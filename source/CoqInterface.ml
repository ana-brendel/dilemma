open Masks
open Serapi
open Sertop

type query_opt = 
  Satisfiable of expr list
  | ProvablyEquilvalent of expr * expr

type query = {
  q : query_opt;
  label : string;
  info : Playground.info;
}

type result = 
  Satisfiability of (expr * bool) list
  | ProvablyEquilvalentResults of (expr * expr) * bool
  | Error of string * query_opt
  
let exec (cmd : Serapi_protocol.cmd) =
  let state = Serapi_protocol.State.make () in
  match Serapi_protocol.exec_cmd state cmd |> fst with
  | ObjList [obj] :: _ -> obj
  | res -> 
    let query = Sertop_ser.sexp_of_cmd cmd |> Sexplib0.Sexp.to_string in
    let ret = List.map (fun r -> Sertop_ser.sexp_of_answer_kind r |> Sexplib0.Sexp.to_string) res |> String.concat "; " in
    raise (Failure ("COMMAND: " ^ query ^ " - RESULT: " ^ ret))
  
let reduce_econstr env sigma =
  let reduction, _ = Redexpr.reduction_of_red_expr env @@ Cbn
    { rBeta = true; rMatch = true; rFix = true; rCofix = true; rZeta = true; rDelta = true; rConst = []; rStrength = Genredexpr.Norm } in
  fun term -> try EConstr.Unsafe.to_constr (snd (reduction env sigma term)) with _ -> EConstr.to_constr sigma term

let reduce_constr env sigma = Base.Fn.compose (reduce_econstr env sigma) EConstr.of_constr

let interp_string env sigma (str : string) (typ : Constr.t) : Constr.t =
  let type_str = Utils.str_of_constr env sigma typ in
  match exec (Parse ({ontop = None; entry=Vernac }, Printf.sprintf "Check (%s : %s)." str type_str)) with
  | CoqAst {v = { expr = VernacSynPure (VernacCheckMayEval (a, b, constr_expr)); control; attrs }; loc = _} ->
    let econstr,_ = Constrintern.interp_constr env sigma constr_expr in reduce_econstr env sigma econstr
  | _ -> raise (Failure "Not able to parse string into Constr.t (in CoqExecution.interp_string)")

let pp_query (q : query) : unit =
  let env, sigma = q.info.env, q.info.sigma in
  let str = fun x -> Utils.str_of_constr env sigma x in
  match q.q with
  | ProvablyEquilvalent (a,b) -> print_endline ("Checks provable equality for: "); print_endline (str a.body ^ " =? " ^ str b.body)
  | Satisfiable exprs -> print_endline ("Satisfiability of: " ^ String.concat ", " (List.map (fun e -> Utils.str_of_constr env sigma e.body) exprs))

let format_satisfiable_query (info : Playground.info) (label : string) (exprs : expr list) : string list = 
  let env, sigma = info.env, info.sigma in
  let str = Utils.str_of_constr_full_via_str env sigma in 
  (* let quickchick_import = "From QuickChick Require Import QuickChick.\nSet Warnings \"-extraction-opaque-accessed,-extraction\"." in
  let file_import = "QCInclude \".\"." in *)
  let test_count = Printf.sprintf "Extract Constant defNumTests => \"%d\"." 15000 in
  (* let test_count = "" in *)
  let lemma_per_expr (i : int) (e : expr) : string * string =
    let parameters = List.map (fun v -> Printf.sprintf "(%s : %s)" (Names.Id.to_string v.id) (str v.typ)) e.variables in
    let lemma = Printf.sprintf "Lemma checking%d %s : %s. Admitted." i (String.concat " " parameters) (str e.body) in
    let check = Printf.sprintf "QuickChick checking%d." i in lemma,check in
  let nat_decidability = "Derive Show for nat. \nDerive Arbitrary for nat. \nInstance Dec_Eq_nat : Dec_Eq nat. \nProof. dec_eq. Qed." in
  let bool_decidability = "Derive Show for bool. \nDerive Arbitrary for bool. \nInstance Dec_Eq_bool : Dec_Eq bool. \nProof. dec_eq. Qed." in
  let strings = List.mapi lemma_per_expr exprs in
  let lemmas, quickchicks = List.split strings in
  [(*quickchick_import;file_import;*)test_count] @ lemmas @ [nat_decidability;bool_decidability] @ quickchicks

let format_provably_equivalent (info : Playground.info) (label : string) a b : string list list = 
  let env, sigma = info.env, info.sigma in
  let str = Utils.str_of_constr_full_via_str env sigma in 
  let vars = String.concat " " (List.map (str_of_variable_w_type env sigma) (a.variables @ b.variables |> Utils.remove_duplicate variable_eq)) in
  let lemma1 = Printf.sprintf "Lemma checking1 %s : %s -> %s." vars (str a.body) (str b.body) in
  let lemma2 = Printf.sprintf "Lemma checking2 %s : %s -> %s." vars (str b.body) (str a.body) in
  [[lemma1; "Proof. simpl. intros MyAssump. apply MyAssump. Qed."; "Check (0)."];
  [lemma1; "Proof. simpl. intros MyAssump. rewrite <- MyAssump. reflexivity. Qed."; "Check (0)."];
  [lemma1; "Proof. simpl. intros MyAssump. rewrite -> MyAssump. reflexivity. Qed."; "Check (0)."];
  [lemma2; "Proof. simpl. intros MyAssump. apply MyAssump. Qed."; "Check (0)."];
  [lemma2; "Proof. simpl. intros MyAssump. rewrite <- MyAssump. reflexivity. Qed."; "Check (0)."];
  [lemma2; "Proof. simpl. intros MyAssump. rewrite -> MyAssump. reflexivity. Qed."; "Check (0)."]]
  
let format_query (query : query) : string list list = 
  match query.q with
  | ProvablyEquilvalent (a,b) -> format_provably_equivalent query.info query.label a b
  | Satisfiable exprs  -> if List.is_empty exprs then [] else [format_satisfiable_query query.info query.label exprs]

let populate_prop (state', goal', assumps') (state_bool, goal_bool, assump_bools, example) =
  let update p b = if b then {p with true_on = example :: p.true_on} else {p with false_on = example :: p.false_on} in
  let state = update state' state_bool in
  let goal = update goal' goal_bool in
  let assumps = List.map2 update assumps' assump_bools in
  (state,goal,assumps)

let process_satisfiable_results env sigma (exprs : expr list) (results' : string list) : result =
  let results_line l = Utils.contains l "+++" || Utils.contains l "***" in
  let results = List.filter results_line results' in
  if (List.length exprs != List.length results) then (raise (Failure "[in CoqInterface.process_satisfiable_results] File did not compile"));
  let parsed = List.combine exprs results in
  let processed = List.map (fun (e,s) -> (e, String.contains s '+')) parsed in Satisfiability processed

let process_provably_equivalent_results a b results = ProvablyEquilvalentResults ((a,b), List.is_empty results |> not)

let process_query_results (query : query) (results : string list) : result =
  match query.q with
  | ProvablyEquilvalent (a,b) -> Utils.break (); process_provably_equivalent_results a b results
  | Satisfiable exprs -> process_satisfiable_results query.info.env query.info.sigma exprs results

let rec handle_provabilty_equivalent pair file one two query = 
  let next o t = handle_provabilty_equivalent pair file o t query in
  let check_file contents =
    let content = String.concat " \n" (query.info.file_formatted @ [""] @ contents) in
    Utils.write_to_file file content; 
    let cmd = Printf.sprintf "cd %s && coqc %s 2>/dev/null" query.info.tmp_dir (query.label ^ ".v") in 
    let results = Utils.run_cmd cmd in Utils.cleanup query.info.tmp_dir query.label; 
    List.is_empty results |> not in
  match one,two with
  | [], [] -> ProvablyEquilvalentResults (pair, false)
  | h :: t, _ -> if check_file h then next [] two else next t (if List.is_empty t then [] else two)
  | [], h :: t -> if check_file h then ProvablyEquilvalentResults (pair, true) else next [] t

let execute (query : query) : result =
  let quickchick_import = "From QuickChick Require Import QuickChick.\nSet Warnings \"-extraction-opaque-accessed,-extraction\".\nQCInclude \".\"." in
  let playground = query.info.tmp_dir ^ "/" ^ query.label ^ ".v" in
  let content' = format_query query in
  match query.q with
  | ProvablyEquilvalent (a,b) -> let one, two = Utils.partition_at_split 3 content' in 
  if 3 = List.length two && 3 = List.length one then handle_provabilty_equivalent (a,b) playground one two query 
  else (List.iter print_endline (List.flatten content'); raise (Failure "Incorrectly formatted content [in CoqInterface.execute]"))
  | _ -> if List.is_empty content' then Satisfiability [] else
    if List.is_empty (List.hd (content')) then Satisfiability [] else
  let content = String.concat " \n" (quickchick_import :: query.info.file_formatted @ [""] @ (List.hd (content'))) in
  Utils.write_to_file playground content;
  let cmd = Printf.sprintf "cd %s && coqc %s 2>/dev/null" query.info.tmp_dir (query.label ^ ".v") in 
  let results = Utils.run_cmd cmd in 
  if (List.is_empty results && (match query.q with | ProvablyEquilvalent _ -> false | _ -> true)) 
    then raise (Failure "Command caused error - empty results, see terminal.");
  let r = process_query_results query results in
  Utils.cleanup query.info.tmp_dir query.label; r
  
(* The addition of "2>/dev/null" in the execution above is intended to suppress the error message: 
     "cp: the -H, -L, and -P options may not be specified with the -r option." which is triggered by QuickChick *)