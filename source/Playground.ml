open Masks
open Coq_extractions

type info = {
  env : Environ.env;
  sigma : Evd.evar_map;
  dirpath : Names.DirPath.t;
  cwd : string;
  current_proof : string; (* Name of the Proof *)
  libraries : Names.ModPath.t list;
  file_contents : string list; (* Lines from the source file, each line is each command separated by '. ' *)
  file_formatted : string list;
  functions : func list;
  tmp_dir : string
}

type proof = {
  goal : expr;
  assumptions : (variable,expr) Hashtbl.t;
  variables : variable list;
  generalized_terms : (variable,expr) Hashtbl.t option;
}

let proof_eq p1 p2 : bool = 
  expr_eq p1.goal p2.goal &&
  Hashtbl.fold (fun v e acc -> match Hashtbl.find_opt p1.assumptions v with | Some e' -> acc && expr_eq e e' | _ -> false) p2.assumptions true &&
  Hashtbl.fold (fun v e acc -> match Hashtbl.find_opt p2.assumptions v with | Some e' -> acc && expr_eq e e' | _ -> false) p1.assumptions true


type t = { proof : proof; info : info}

let get_content_from_file (dp : Names.DirPath.t) : string * string list =
  let file' = Names.DirPath.to_string dp ^ ".v" in
  let file = (Sys.getcwd ()) ^ "/" ^ file' in
  if (Sys.file_exists file |> not) then raise (Failure "Incorrectly gathering current file Playground.get_content_from_file");
  (Sys.getcwd ()), Utils.read_file file |> Utils.remove_coq_comments |> Utils.split_on_string ". " |> List.map String.trim 

(* Issue with gathering functions is if there a comment before the line parsing gets messed up so should try to make it more resilient *)
let gather_libraries (file_contents : string list) : string list = 
  let filter_func line =
    let check starter = String.starts_with ~prefix:starter line in 
    (check "Require") || (check "Export") || (check "Import") || (check "From") in
  let remove_trailing_period = List.map (fun l -> if (String.ends_with ~suffix:"." l) then Utils.remove_last_char l else l) in
  let lines = List.filter filter_func file_contents |> remove_trailing_period in 
  (List.filter (fun l -> Utils.contains l "LFindToo" |> not) lines)

(* Note, cannot use the From, must have as full path or it will not parse -- can handle later to clean up *)
let mp_gather_libraries (file_contents : string list) : Names.ModPath.t list =
  let strings = gather_libraries file_contents in
  let find_opt' l = List.find_opt (fun line -> Utils.contains line (Names.DirPath.to_string l)) strings in
  List.filter_map (fun l -> match find_opt' l with | Some str -> Some l | _ -> None) (Library.loaded_libraries ())
  |> List.map (fun d -> Names.ModPath.MPfile d)

let format_file (contents : string list) (current : string) : string list =
  let clean_line line = String.split_on_char ' ' line |> List.map String.trim |> String.concat " " in
  let find_proof line = Utils.contains line ("Theorem " ^ current) || Utils.contains line ("Lemma " ^ current) in
  let line = List.find_index find_proof (List.map clean_line contents) in
  match line with
  | None -> raise (Failure "Current proof not correctly found within the source file (in Playground.format_file)")
  | Some index -> 
    let result = Utils.partition_at index contents |> List.map (fun l -> l ^ ".") in
    if (Utils.contains (List.nth contents index) "*)") then result @ ["*)"] else result

let get_assumptions env sigma (hyp_context : EConstr.named_context) : (variable * expr) list =
  let parse = function
  | Context.Named.Declaration.LocalAssum(x, y) -> (Context.(x.binder_name), (EConstr.to_constr sigma y))
  | Context.Named.Declaration.LocalDef(x, _, y) -> (Context.(x.binder_name), (EConstr.to_constr sigma y)) in
  let process (id,body) =
    let expr = if (Constr.is_Type body) then { body; typ = body; variables = [] } else expr_from_constr env sigma body in
    ( {id; typ = expr.body}, expr) in
    List.map parse hyp_context |> List.map process

(* let rec unpack env sigma ctor : unit =
  match Constr.kind ctor with
  | Var id -> ()
  | App (func, args) -> unpack env sigma func; Array.iter (unpack env sigma) args
  | Prod (var,typ,result) -> raise (Failure "Constr kind PROD not handled in Playground.unpack")
  | Lambda (var,typ,body) -> raise (Failure "Constr kind LAMBDA not handled in Playground.unpack")
  | Ind ((mut,i),u) -> print_endline (Names.MutInd.modpath mut |> Names.ModPath.to_string); print_endline (Names.MutInd.label mut |> Names.Label.to_string); print_endline (string_of_int i); print_endline (UVars.Instance.is_empty u |> string_of_bool)
  | Sort _ -> raise (Failure "Constr kind SORT not handled in Playground.unpack")
  | Rel _ -> raise (Failure "Constr kind REL not handled in Playground.unpack")
  | Meta _ -> raise (Failure "Constr kind META not handled in Playground.unpack")
  | Const (c,u) -> print_endline (Names.Constant.to_string c); print_endline (UVars.Instance.is_empty u |> string_of_bool)
  | Construct (((mut,i'),i),u) ->  print_endline (Names.MutInd.modpath mut |> Names.ModPath.to_string); print_endline (Names.MutInd.label mut |> Names.Label.to_string);print_endline (string_of_int i'); print_endline (string_of_int i); print_endline (UVars.Instance.is_empty u |> string_of_bool)
  | LetIn (ids,inp,assignment,expr) -> raise (Failure "Constr kind LETIN not handled in Playground.unpack")
  | Case (info,a,b,arr,c,d,e) -> raise (Failure "Constr kind CASE not handled in Playground.unpack")
  | Evar p -> raise (Failure "Constr kind EVAR not handled in Playground.unpack")
  | Cast (constr,kind,typ) -> raise (Failure "Constr kind CAST not handled in Playground.unpack")
  | Fix fp -> raise (Failure "Constr kind FIX not handled in Playground.unpack")
  | CoFix cfp -> raise (Failure "Constr kind COFIX not handled in Playground.unpack")
  | Proj (proj,_,constr) -> raise (Failure "Constr kind PROJ not handled in Playground.unpack")
  | Int i -> raise (Failure "Constr kind INT not handled in Playground.unpack")
  | Float f -> raise (Failure "Constr kind FLOAT not handled in Playground.unpack")
  | Array (univ,arr,constr,typ) -> raise (Failure "Constr kind ARRAY not handled in Playground.unpack") *)

let fetch_t env sigma (g : Proofview.Goal.t) : proof = 
  (* let nat = Utils.get_nat env in *)
  (* TODO -- update the env to be monomorphized -- right now, can't handle polymorphism *)
  (* let env = Hashtbl.fold (fun (v : variable) _ env' -> Environ.push_named (LocalAssum (Context.annotR v.id, v.typ)) env') generalized_variables env in *)
  let goal = Proofview.Goal.concl g |> EConstr.to_constr sigma |> expr_from_constr env sigma in
  let assumptions' =  Proofview.Goal.hyps g |> get_assumptions env sigma in 
  let variables = List.map fst assumptions' in
  let assumptions = Hashtbl.create (List.length assumptions') in
  List.iter (fun (v,e) -> if (is_prop env e.body) then Hashtbl.add assumptions v e) assumptions';
  { goal; assumptions; variables; generalized_terms = None }

let fetch_info (g : Proofview.Goal.t) : info = 
  let env = Proofview.Goal.env g in 
  let sigma = Proofview.Goal.sigma g in
  let dirpath = Lib.library_dp () in
  let interp = Vernacstate.Interp.freeze_interp_state () in 
  let lemma' = match interp.lemmas with | Some l -> l |> Vernacstate.LemmaStack.get_all_proof_names |> List.map Names.Id.to_string | _ -> [] in
  let current_proof = match lemma' with | l :: [] -> l |_ -> raise (Failure "Name of current lemma not found properly (in ProofContext.fetch_document)") in
  let cwd, file_contents = get_content_from_file dirpath in
  let libraries = mp_gather_libraries file_contents in
  let file_formatted = format_file file_contents current_proof in
  let tmp_dir = Formatting.mkTmp cwd in
  let functions = GatherFunctions.run (Proofview.Goal.env g) (Proofview.Goal.sigma g) tmp_dir libraries file_formatted in
  { env; sigma; dirpath; cwd; current_proof; libraries; file_contents; file_formatted; functions; tmp_dir }

let types_from_proof env (p : proof) : Constr.t list = 
  let ctors = List.map (fun (v : variable) -> v.typ) p.variables |> Utils.remove_duplicate Constr.equal in
  List.filter (fun c -> Constr.is_Type c |> not) ctors |> List.filter (fun c -> Constr.is_Prop (Typeops.infer env c).uj_type |> not)

let fetch (g : Proofview.Goal.t) = let info = fetch_info g in fetch_t info.env info.sigma g, info 

let print (c : t) : unit = 
  let str_constr = Utils.str_of_constr c.info.env c.info.sigma in
  print_endline ("-------------------------------------------- ");
  print_endline ("CURRENT MODULE : " ^ Names.DirPath.to_string c.info.dirpath);
  print_endline ("-------------------------------------------- ");
  print_endline ("-------------------------------------------- ");
  List.iter (fun (v : variable) -> print_endline (Names.Id.to_string v.id ^ " : " ^ str_constr v.typ)) c.proof.variables;
  print_endline ("-------------------------------------------- "); 
  print_endline ("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ ");
  print_endline ("-------------------------------------------- ");
  Hashtbl.iter (fun v b -> print_endline (Names.Id.to_string v.id ^ " : " ^ str_constr b.body)) c.proof.assumptions;
  print_endline ("-------------------------------------------- ");
  print_endline ("GOAL : " ^ str_constr c.proof.goal.body); print_newline ();