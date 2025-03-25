open Utils
open Masks
open Coq_extractions

type cmp_kind = GENERALIZED_WEAKENED | GENERALIZED | WEAKENED | AS_IS

let get_atomic (info : Playground.info) (executions : Execution.t list) : (string * string) list =
  let atomics = List.filter (fun (e : Execution.t) -> List.is_empty e.goal.false_on) executions in
  let str (e : Execution.t) = str_of_constr info.env info.sigma in
  List.map (fun (e : Execution.t) -> let s = str e in (s e.goal.expr.body, s e.goal.expr.body)) atomics 

type weakening = {
  original : Constr.t;
  result : Constr.t;
  label : int
}

let weakening_eq w1 w2 = Constr.equal w1.original w2.original && Constr.equal w1.result w2.result

type result = {
  label : int;
  generalizations : int;
  kind : cmp_kind;
  weakening : weakening option;
  synthesized : Constr.t option;
  preconditions : Constr.t list;
  goal : Constr.t;
}

let get_cmp_kind (p : SynthInterface.problem) weakening : cmp_kind =
  match p.case, weakening with
  | VALID_GENERALIZED, _ -> GENERALIZED
  | VALID_UNGENERALIZED, None -> AS_IS
  | VALID_UNGENERALIZED, Some _ -> WEAKENED
  | INVALID_GENERALIZED, _ -> GENERALIZED_WEAKENED
  | _, _ -> raise (Failure "Should not have result from dead end or unstable [in Candidates.cmp_kind_by_exec]")

let get_atomic_results (offset : int) (executions : Execution.t list) : result list =
  let atomics = List.filter (fun (e : Execution.t) -> List.is_empty e.goal.false_on) executions in
  let cmp_kind (e : Execution.t) = match e.case with VALID_UNGENERALIZED -> AS_IS | VALID_GENERALIZED -> GENERALIZED | _ -> raise (Failure "Execution should be valid at this point [in Candidates.cmp_kind_by_exec]") in
  let process (e : Execution.t) = Execution.generalization_count e, e.goal.expr.body, cmp_kind e in
  let pairs = List.map process atomics in
  let weakening = None in let preconditions = [] in
  List.mapi (fun i (generalizations, goal, kind) -> { kind; generalizations; goal; preconditions; weakening; label = i + offset; synthesized = None }) pairs

let get_results_directly (offset : int) (executions : Execution.t list) : result list =
  let weakening = None in
  let cmp_kind (e : Execution.t) = match e.case with VALID_UNGENERALIZED -> AS_IS | VALID_GENERALIZED -> GENERALIZED | _ -> raise (Failure "Execution should be valid at this point [in Candidates.cmp_kind_by_exec]") in
  let process (e : Execution.t) = Execution.generalization_count e, e.goal.expr.body, List.map (fun p -> p.expr.body) e.assumptions, cmp_kind e in
  let is_valid (e : Execution.t) = match e.case with | VALID_GENERALIZED | VALID_UNGENERALIZED -> true | _ -> false in
  let tuples = List.map process (List.filter is_valid executions) in
  List.mapi (fun i (generalizations, goal, preconditions, kind) -> { kind; generalizations; goal; preconditions; weakening; label = i + offset; synthesized = None }) tuples

let result_str_formatted formatted exec env sigma r =
  let str = str_of_constr env sigma in
  let implies_goal = List.fold_right implication_constr r.preconditions r.goal in
  let weakening = match r.weakening with | None -> implies_goal | Some weak -> implication_constr weak.original weak.result in
  if not formatted then str weakening, str implies_goal
  else let to_expr = expr_from_constr env sigma in
    let a_expr, b_expr = to_expr weakening, to_expr implies_goal in
    let make x e = Printf.sprintf "Lemma candidate_%d_%d%s : %s." exec r.label x (format_expr env sigma e) in
    if Constr.equal implies_goal weakening then make "b" b_expr, make "b" b_expr else make "a" a_expr, make "b" b_expr

let result_str (info : Playground.info) r =
  let str = str_of_constr info.env info.sigma in
  let implies_goal = List.fold_right implication_constr r.preconditions r.goal in
  let weakening = match r.weakening with | None -> implies_goal | Some weak -> implication_constr weak.original weak.result in
  let clean s = String.trim s |> Str.global_replace (Str.regexp "\n") " " |> Str.global_replace (Str.regexp "\t") " " in
  clean (str weakening), clean (str implies_goal)

let result_eq r1 r2 = Constr.equal r1.goal r2.goal && List.equal Constr.equal (List.sort Constr.compare r1.preconditions) (List.sort Constr.compare r2.preconditions)

type constructor = {
  exec : int;
  queries : int list;
  proof : Generalize.t;
  case : Execution.case;
  goal : prop;
  assumptions : prop list;
  results : result list
}

let construct_result_str (info : Playground.info) formatted c = List.map (result_str_formatted formatted c.exec info.env info.sigma) c.results

let get_implication_label (c : constructor) (r : result) = Printf.sprintf "implication_%d_%d" c.exec r.label

let equality_option ctor : (Names.variable * Constr.t) option =
  let eq_label mut = Names.Label.equal (Names.Label.make "eq") (Names.MutInd.label mut) in
  let is_var c = match Constr.kind c with Var _ -> true | _ -> false in
  match Constr.kind ctor with
  | App (label,args) -> 
    (match Constr.kind label with
    | Ind ((mut,_),_) when (eq_label mut && Array.length args = 3 && (is_var (Array.get args 1))) -> Some ((Array.get args 1 |> Constr.destVar),ctor)
    | Ind ((mut,_),_) when (eq_label mut && Array.length args = 3 && (is_var (Array.get args 2))) -> Some ((Array.get args 2 |> Constr.destVar),ctor)
    | _ -> None)
  | _ -> None

let filter_eq ctor : bool =
  let eq_label mut = Names.Label.equal (Names.Label.make "eq") (Names.MutInd.label mut) in
  match Constr.kind ctor with
  | App (label,args) -> 
    (match Constr.kind label with
    | Ind ((mut,_),_) when (eq_label mut && Array.length args = 3) -> not (Constr.equal (Array.get args 1) (Array.get args 2))
    | _ -> true)
  | _ -> true

let pull_rewrites generalized_variables (r : result) : result list =
  match r.kind with
  | AS_IS | GENERALIZED | WEAKENED -> []
  | GENERALIZED_WEAKENED -> 
    let equal_to_var = List.filter_map equality_option r.preconditions in
    let simplify_replace v = try [(v,Hashtbl.find generalized_variables v)] with _ -> [] in
    let get_equalities = (fun (v,c) -> if List.is_empty (simplify_replace v) then None else Some (Vars.replace_vars (simplify_replace v) c)) in
    let equalities = List.filter_map get_equalities equal_to_var |> List.filter filter_eq in
    List.map (fun goal -> { r with preconditions = []; goal }) equalities

let results_by_problem (info : Playground.info) gv_equalities (p : SynthInterface.problem) : result list = 
  let get_weakening label result = match p.query.abducted with | None -> None
  | Some og -> if Constr.equal og.expr.body result then None else Some { label; original = og.expr.body; result }  in
  let filter_weakened weakening c = match weakening with Some w -> not (Constr.equal c w.original) | _ -> true in
  let goal = p.goal.expr.body in
  let generalized_terms = List.of_seq (match p.proof.generalized_terms with Some tbl -> Hashtbl.to_seq_values tbl | _ -> Seq.empty) in
  let variables_covered = List.concat_map (fun (e : expr) -> e.variables) generalized_terms |> remove_duplicate variable_eq in
  let check_vars = List.filter_map (fun (e : expr) -> if List.for_all (fun (v : variable) -> List.exists (variable_eq v) variables_covered) e.variables then None else Some e.body) in
  let assumptions = List.filter_map (fun (p : prop) -> match p.kind with Assumption -> Some p.expr | _ -> None) p.assumptions in
  let generalizations = match p.proof.generalized_terms with Some tbl -> Hashtbl.length tbl | _ -> 0 in
  let result_by_candidate ((label,result) : (int * Constr.t)) = 
    if List.mem result gv_equalities then None else
    let weakening = get_weakening label result in
    let preconditions = List.sort Constr.compare (result :: (List.filter (filter_weakened weakening) (check_vars assumptions))) in
    let kind = get_cmp_kind p weakening in
    Some { kind; weakening; preconditions; goal; label = -1; generalizations; synthesized = Some result } 
  in let results = List.filter_map result_by_candidate (List.filter (fun (_,c) -> Constr.equal goal c |> not) p.candidates)
  in match p.proof.generalized_terms with None -> results
  | Some tbl -> let swap_types = Hashtbl.create (Hashtbl.length tbl) in Hashtbl.iter (fun v e -> Hashtbl.add swap_types v.id e.body) tbl;
  results @ (List.concat_map (pull_rewrites swap_types) results)

let match_og_generalization (info : Playground.info) (e : Execution.t) : Constr.t list =
  let make_equality_l (v : variable) (e : expr) = Utils.construct_equal info.env v.typ (Constr.mkVar v.id) e.body in
  let make_equality_r (v : variable) (e : expr) = Utils.construct_equal info.env v.typ e.body (Constr.mkVar v.id) in
  match e.proof.generalized_terms with
  | None -> []
  | Some tbl -> Hashtbl.fold (fun v e acc -> (make_equality_l v e) :: (make_equality_r v e) :: acc ) tbl []

let create_constructors (info : Playground.info) (executions : Execution.t list) (candidates : SynthInterface.problem list) : constructor list =
  let by_label = Hashtbl.create (List.length executions) in
  let safe_add i c = let lst = try Hashtbl.find by_label i with _ -> [] in Hashtbl.replace by_label i (c :: lst) in
  List.iter (fun (p : SynthInterface.problem) -> safe_add p.proof.label p) candidates;
  let create (e : Execution.t) (ps : SynthInterface.problem list) = 
    let gv_equalities = match_og_generalization info e in
    let queries = List.map (fun (p : SynthInterface.problem) -> p.label) ps in
    let results = List.concat_map (results_by_problem info gv_equalities) ps |> remove_duplicate result_eq |> List.mapi (fun label r -> { r with label }) in
    let exec, proof, goal, assumptions, case = e.label, e.proof, e.goal, e.assumptions, e.case in
    { exec; proof; goal; assumptions; results; queries; case } in
  List.filter_map (fun (e : Execution.t) -> try Some (create e (Hashtbl.find by_label e.label)) with _ -> None) executions

let form_implication_prop (info : Playground.info) vars (label : result -> string) (r : result) = 
  let implies_goal = List.fold_right implication_constr r.preconditions r.goal in
  let added = match r.weakening with | None -> [] | Some weak -> [ implication_constr weak.original weak.result ] in
  match conjoin_props (implies_goal :: added) with | None -> None
  | Some impl -> if List.for_all (fun v -> List.exists (Names.Id.equal v.id) vars) (vars_in_constr info.env impl) then Some (label r, impl) else None

let run_validity_driver tmp_dir exec impl_ml (impl : (constructor * (string * Constr.t) list) list) : string list =
  let get_label c = Printf.sprintf "implication_set_%d" c.exec in
  let items labels = List.map (fun (s,_) -> Printf.sprintf "(\"%s\", %s)" s s) labels in
  let impl_lists (c,pairs) = let label = get_label c in 
  (label,Examples.example_set_label c.exec), Printf.sprintf "let %s = [%s]" label (String.concat "; " (items pairs)) in
  let labels, list_definitions = List.map impl_lists impl |> List.split in
  let dependencies = (*(List.map Examples.examples_ml (List.map (fun (c,_) -> c.exec) impl)) @*) [impl_ml] in
  let opens = Evaluator.openning dependencies in
  let constant_defs = [Evaluator.parmap_defs; Evaluator.checking_all; Evaluator.display_list] in 
  let check_each = List.map (fun (label,exs) -> Printf.sprintf "check (List.map snd %s) %s |> display;" exs label) labels in
  let main = Printf.sprintf "let () = print_endline \"running\";\n%s" (String.concat "\n" check_each) in
  let content = opens @ constant_defs @ list_definitions @ [main] |> String.concat "\n\n" in
  let src = Printf.sprintf "CheckingImplValidity%d" exec in
  let fname = ExtractionUtils.join_paths tmp_dir src ^ ".ml" in
  write_to_file fname content; 
  let output = Extractor.run tmp_dir dependencies src in
  List.filter_map (fun l -> let t = String.trim l in if t = "" || t = "running" then None else Some t) (List.tl output)

let prune_by_validity (info : Playground.info) elapsed_time tmp_dir state_info exec example_content file_formatted (constructors : constructor list) : constructor list =
  if List.is_empty constructors then (print_endline (Printf.sprintf "[No Candidates from Execution %d]" exec); []) else 
  (* 1. Create implications - grouped by execution *)
  let fetch_implications_by_constr c = c, List.filter_map (form_implication_prop info (Generalize.get_example_format info c.proof |> fst |> fst) (get_implication_label c)) c.results in
  let implications_by_constr = List.map fetch_implications_by_constr constructors in

  (* 2. Extract to OCaml as boolean functions *)
  print_endline (Printf.sprintf "[Running Extraction for Execution %d]" exec);
  let format_impl con = Formatting.format_prop info.env info.sigma (Generalize.get_example_format info con.proof) in
  let impl_definitions = List.concat_map (fun (c,imps) -> List.map (format_impl c) imps) implications_by_constr in
  let impl_terms = List.concat_map (fun (_,t) -> List.map fst t) implications_by_constr in
  let coq = Formatting.prop_to_bool :: ((List.map snd state_info) @ impl_definitions) |> String.concat "\n" in
  let extras = Some (true, Hashtbl.find example_content exec) in
  if List.is_empty impl_terms then (print_endline (Printf.sprintf "[No Candidates from Execution %d]" exec); []) else
  let impl_ml = Extractor.extract true extras tmp_dir file_formatted (Printf.sprintf "Validity_Check_Impl_%d" exec) coq ((List.map fst state_info) @ impl_terms) in
  print_endline ((Printf.sprintf "[Extraction Complete for Execution %d] Time Elapsed From Start: " exec) ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds");

  (* 3. Evaluate on existing examples -- parallelize by execution *)
  print_endline (Printf.sprintf "[Execution %d] Checking that implications hold under the greater example set..." exec);
  let valid_impl_labels = run_validity_driver tmp_dir exec impl_ml implications_by_constr in
  print_endline (Printf.sprintf "[Execution %d] Finished checking implications!" exec);

  (* 4. Prune/Process *)
  let filter_results (c : constructor) = List.filter (fun r -> List.mem (get_implication_label c r) valid_impl_labels) c.results in
  List.map (fun c -> { c with results = filter_results c}) constructors

let prune_by_assumption (info : Playground.info ) (cache,acc) (constructor : constructor) : ((Constr.t * Constr.t),bool) Hashtbl.t * constructor list = 
  let str = str_of_constr info.env info.sigma in
  let exec_query i aa bb = 
    let a, b = expr_from_constr info.env info.sigma aa, expr_from_constr info.env info.sigma bb in
    let query : CoqInterface.query = { q = CoqInterface.ProvablyEquilvalent (a,b); label = Printf.sprintf "provable_equiv_assumption_%d_%d" constructor.exec i; info} in
    match CoqInterface.execute query with | ProvablyEquilvalentResults (p,r) -> r | _ -> raise (Failure "Unexpected result type (Candidates.prune_by_assumption).") in
  let per_result i (r : result) : result option =
    match r.weakening with | None -> Some r | Some w ->
      let one, two = String.split_on_char '=' (str w.result), String.split_on_char '=' (str w.original) in
      let short_circuit = try String.equal (List.hd one) (List.hd (List.tl two)) && String.equal (List.hd two) (List.hd (List.tl one)) with _ -> false in
      if short_circuit || Constr.equal w.result w.original then None 
      else let pair, flip = (w.result, w.original), (w.original, w.result) in
      let b = try Hashtbl.find cache pair with _ -> (exec_query i w.result w.original) in
      if (Hashtbl.mem cache pair |> not) then (Hashtbl.add cache pair b; Hashtbl.add cache flip b); (if b then None else Some r) 
  in cache, acc @ [{ constructor with results = my_parmapi per_result constructor.results |> List.filter_map (fun x -> x) }]

let prune_by_goal (info : Playground.info) (cache,acc) (constructor : constructor) : ((Constr.t * Constr.t),bool) Hashtbl.t * constructor list = 
  let str = str_of_constr info.env info.sigma in
  let goal, str_goal = constructor.proof.goal, str constructor.proof.goal.expr.body in
  let exec_query i aa b = 
    let a = expr_from_constr info.env info.sigma aa in
    let query : CoqInterface.query = { q = CoqInterface.ProvablyEquilvalent (a,b); label = Printf.sprintf "provable_equiv_goal_%d_%d" constructor.exec i; info} in
    match CoqInterface.execute query with | ProvablyEquilvalentResults (p,r) -> r | _ -> raise (Failure "Unexpected result type (Candidates.prune_by_goal).") in
  let per_result i (r : result) : result option =
    match r.synthesized with | None -> Some r 
    | Some result ->
      let one, two = String.split_on_char '=' (str result), String.split_on_char '=' str_goal in
      let short_circuit = try String.equal (List.hd one) (List.hd (List.tl two)) && String.equal (List.hd two) (List.hd (List.tl one)) with _ -> false in
      if short_circuit || Constr.equal result goal.expr.body then None else 
      let pair, flip = (result, goal.expr.body), (goal.expr.body, result) in
      let b = try Hashtbl.find cache pair with _ -> (exec_query i result goal.expr) in
      if (Hashtbl.mem cache pair |> not) then (Hashtbl.add cache pair b; Hashtbl.add cache flip b); (if b then None else Some r)
  in cache, acc @ [{ constructor with results = my_parmapi per_result constructor.results |> List.filter_map (fun x -> x) }]

let simplify_result (r : result) = 
  let preconditions = remove_duplicate Constr.equal r.preconditions |> List.sort Constr.compare in
  { r with preconditions }

let simplify_constructors (constructors : constructor list) =
  let results_equal (r1 : result) (r2 : result) = List.equal Constr.equal (r1.goal :: r1.preconditions) (r2.goal :: r2.preconditions) in
  let per_constructor c = let results = List.map simplify_result c.results |> remove_duplicate results_equal in { c with results } in
  let filter_from_others acc r = List.exists (List.exists (result_eq r)) (List.map (fun c -> c.results) acc) |> not in
  let folder acc c = let results = List.filter (filter_from_others acc) c.results in { c with results } :: acc in
  List.fold_left folder [] (List.map per_constructor constructors)

let updated_construction (info : Playground.info) elapsed_time state_for_definitions example_content (executions : Execution.t list) (candidates : SynthInterface.problem list) =
  if List.is_empty executions then [] else
  let tmp_dir, file_formatted = info.tmp_dir, info.file_formatted in

  (* 1. Match executions back with synthesis probles *) 
  let constructors = create_constructors info executions candidates |> simplify_constructors in

  (* 2. Prune out if the pairs of lemmas are not valid (via our set of examples) *)
  let divided = List.map (fun (e : Execution.t) -> e.label, List.filter (fun c -> c.exec = e.label) constructors) executions in
  print_endline "Extracting implications to OCaml to check validity consistent with examples...";
  let valid_constructors = my_parmap (fun (e,cs) -> prune_by_validity info elapsed_time tmp_dir state_for_definitions e example_content file_formatted cs) divided in
  print_endline ("[Validity Check Complete] Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds");

  (* 3. Prune out any proposition that is provable equivalent to the one it is weakening *)
  print_endline "\nChecking that the weakening is not trivial...";
  let cache', assumption_pruned_constructors = List.fold_left (prune_by_assumption info) (Hashtbl.create 0,[]) (List.flatten valid_constructors) in
  print_endline ("[Weakening Trivial Check Complete] Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds\n");
  (* 4. Prune out any proposition that is provable equivalent to the goal *)
  print_endline "Checking that the weakening is not provably equivalent to the goal...";
  let cache, goal_pruned_constructors = List.fold_left (prune_by_goal info) (Hashtbl.create 0,[]) assumption_pruned_constructors in
  print_endline ("[Goal Check Complete] Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds\n");

  goal_pruned_constructors |> my_parmap (fun c -> { c with results = remove_duplicate result_eq c.results }) 
 
let constr_cmp c1 c2 : int =
  let n1, n2 = constr_nodes c1, constr_nodes c2 in
  if n1 != n2 then n1 - n2 
  else let h1, h2 = constr_height c1, constr_height c2 in
  if h1 != h2 then h1 - h2 else Constr.compare c1 c2

(* 0 if equal, positive means first is greater (comes second), negative means first is less (comes first) *)
(* TODO these might want to be changed *)
(* let score_by_kind prioritize_rewrites (r : result) : int = 
  match r.kind with 
  | GENERALIZED -> 1 
  | AS_IS -> if prioritize_rewrites then 3 else 2 
  | WEAKENED -> if prioritize_rewrites then 4 else 4 
  | GENERALIZED_WEAKENED -> if prioritize_rewrites then 2 else 3 *)

(* let compare prioritize_rewrites (r1 : result) (r2 : result) : int = 
  if r1.kind != r2.kind then score_by_kind prioritize_rewrites r1 - score_by_kind prioritize_rewrites r2
  else match r1.kind with
  | AS_IS -> 0
  | GENERALIZED when (r1.generalizations != r2.generalizations) -> r2.generalizations - r1.generalizations
  | GENERALIZED_WEAKENED when (r1.generalizations != r2.generalizations) -> r2.generalizations - r1.generalizations
  | GENERALIZED_WEAKENED when (prioritize_rewrites && (List.length r1.preconditions != List.length r2.preconditions)) -> Int.compare (List.length r1.preconditions) (List.length r2.preconditions)
  | GENERALIZED | GENERALIZED_WEAKENED -> constr_nodes r1.goal - constr_nodes r1.goal
  | WEAKENED -> match r1.weakening, r2.weakening with
  | None, _ | _, None -> raise (Failure "Expect there to be a weakening [in Candidates.compare]")
  | Some w1, Some w2 -> let cmp_constrs c1 c2 = constr_nodes c1 - constr_nodes c2 in
    let cmp_og, cmp_weak = cmp_constrs w2.original w1.original, cmp_constrs w1.result w2.result in
    if cmp_og != 0 then cmp_og else cmp_weak *)

let prune_invalid (info : Playground.info) results : result list =
  let gexpr = expr_from_constr info.env info.sigma in
  let make_expr r = 
    let implies_goal = List.fold_right implication_constr r.preconditions r.goal in
    match r.weakening with
    | None -> gexpr implies_goal 
    | Some weak -> 
      match conjoin_props [(implication_constr weak.original weak.result); implies_goal] with
      | Some ctor -> gexpr ctor | _ -> raise (Failure "Should be unreachable [in Candidates.prune_invalid]") in
  let queries' = List.map (fun r -> r, make_expr r) results in
  let queries = List.filter (fun (_,e) -> not (List.is_empty e.variables)) queries' in
  let q = CoqInterface.Satisfiable (List.map snd queries) in
  let query : CoqInterface.query = { q; label = "final_validity_prune"; info} in
  match CoqInterface.execute query with | ProvablyEquilvalentResults _ | Error _ -> raise (Failure "Unexpected query result type [in Candidates.prune_invalid]") 
  | Satisfiability bools -> 
    let pairup = try List.combine queries bools with _ -> raise (Failure "(1) Pairing results back with results issue [in Candidates.prune_invalid]") in
    List.iter (fun ((_,e),(ee,_)) -> if not (Constr.equal e.body ee.body) then raise (Failure "(2) Pairing results back with results issue [in Candidates.prune_invalid]")) pairup;
    List.filter_map (fun ((r,_),(_,b)) -> if b then Some r else None) pairup

let alt_score_by_kind (r : result) : int = 
  match r.kind with 
  | GENERALIZED -> 1 
  | AS_IS -> 2
  | GENERALIZED_WEAKENED when (List.is_empty r.preconditions) -> 3
  | WEAKENED -> 4
  | GENERALIZED_WEAKENED -> 5

(* let rank_length (r1 : result) (r2 : result) : int = 
  let get_size (r : result) =
    let overall = List.fold_left (fun score c -> score + (constr_nodes c)) (constr_nodes r.goal) r.preconditions in
    match r.weakening with None -> overall
    | Some w -> let alt = constr_nodes w.result + constr_nodes w.original in if alt < overall then alt else overall
  in let size_compare = get_size r1 - get_size r2 in
  if size_compare = 0 then (alt_score_by_kind r1 - alt_score_by_kind r2) else size_compare *)

(* let rank_length_alt (r1 : result) (r2 : result) : int = 
  let get_size (r : result) =
    match r.kind with
    | GENERALIZED | GENERALIZED_WEAKENED | AS_IS-> constr_nodes r.goal
    | WEAKENED -> match r.weakening with Some w -> constr_nodes w.result | None -> constr_nodes r.goal 
  in let size_compare = get_size r1 - get_size r2 in
  if size_compare = 0 then (alt_score_by_kind r1 - alt_score_by_kind r2) else size_compare *)

let compare (r1 : result) (r2 : result) : int = 
  let overall (r : result)= List.fold_left (fun score c -> score + (constr_nodes c)) 0 r.preconditions in
  if r1.kind != r2.kind then alt_score_by_kind r1 - alt_score_by_kind r2
  else match r1.kind with
  | AS_IS -> 0
  | GENERALIZED when (constr_nodes r1.goal != constr_nodes r1.goal) -> constr_nodes r1.goal - constr_nodes r2.goal
  | GENERALIZED_WEAKENED when (constr_nodes r1.goal != constr_nodes r1.goal) -> constr_nodes r1.goal - constr_nodes r2.goal
  | GENERALIZED_WEAKENED when (List.length r1.preconditions != List.length r2.preconditions) -> Int.compare (List.length r1.preconditions) (List.length r2.preconditions)
  | GENERALIZED | GENERALIZED_WEAKENED -> overall r1 - overall r2
  | WEAKENED -> match r1.weakening, r2.weakening with
  | None, _ | _, None -> raise (Failure "Expect there to be a weakening [in Candidates.compare]")
  | Some w1, Some w2 when (Constr.equal w1.original w2.original) -> constr_cmp w1.result w2.result 
  | Some w1, Some w2 -> (constr_cmp w1.result w2.result) + (constr_cmp w2.original w1.original)
