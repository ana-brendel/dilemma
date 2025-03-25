open Masks
open Utils
open Prop_synth

let synth_example_cap = 500
let synth_result_cap = 20

type query = {
  positives : example list;
  negatives : example list;
  abducted : prop option
}

(* type Execution.t = {
  label : int;
  proof : Generalize.t;
  case : case;
  goal: prop;
  assumptions: prop list
} *)

type problem = {
  label : int;
  proof : Generalize.t;
  case : Execution.case;
  goal: prop;
  assumptions: prop list;
  query : query;
  types : Constr.t list;
  candidates : (int * Constr.t) list
}

let cap_results (info : Playground.info) (p : problem) : problem =
  let sorted = List.sort (fun r1 r2 -> constr_compare (str_of_constr info.env info.sigma) (snd r1) (snd r2)) p.candidates in
  { p with candidates = partition_at synth_result_cap sorted }

let rec intersect_example_sets (sets : example list list) : example list =
  let eq_example_id (e1 : example) (e2 : example) = e1.label = e2.label in
  match sets with
  | [] -> []
  | [single] -> single
  | next :: rest -> if List.is_empty next then [] else intersection eq_example_id next (intersect_example_sets rest)

let shares_variables (p1 : prop) (p2 : prop) : variable list  = intersection variable_eq p1.expr.variables p2.expr.variables

let invalid_generalized (proof : Generalize.t) (goal : prop) (assumptions : prop list) : query list = 
  let cut = partition_at synth_example_cap in
  let original = List.filter (fun a -> match a.kind with | GenEquality _ -> false | _ -> true) assumptions in
  let true_on_originals = intersect_example_sets (List.map (fun p -> p.true_on) original) in
  let true_on_all = intersect_example_sets (List.map (fun p -> p.true_on) assumptions) in
  let positives = cut (intersect_example_sets [goal.true_on; true_on_all]) in
  let negatives = cut (if (List.is_empty original || List.is_empty true_on_originals) 
    then goal.false_on else intersect_example_sets [true_on_originals; goal.false_on]) in
  [{ positives; negatives; abducted = None}]

(* MAYBE we do disjoint partitioning or group matches here ((TBD)) *)
let groups_to_weaken assumptions =
  let others a = remove_from (fun a1 a2 -> Constr.equal a1.expr.body a2.expr.body) a assumptions in
  List.map (fun a -> a, a.true_on, others a) assumptions

let valid_ungeneralized (proof : Generalize.t) (goal : prop) (assumptions : prop list) : query list = 
  let cut = partition_at synth_example_cap in
  let abduct (assumps,true_on_all,others) =
    let true_on_others = intersect_example_sets (List.map (fun p -> p.true_on) others) in
    let negatives = cut (if (List.is_empty others) then goal.false_on else intersect_example_sets [true_on_others; goal.false_on]) in
    if (List.is_empty negatives) then None
    else let positives = cut true_on_all in if (List.is_empty positives) then None else
    Some { positives; negatives; abducted = Some assumps }
  in List.filter_map abduct (groups_to_weaken assumptions) 

let prepare (info : Playground.info) (execution : Execution.t) : problem list  =
  let proof, goal, assumptions = execution.proof, execution.goal, execution.assumptions in
  let case_handler = match execution.case with
  | VALID_UNGENERALIZED -> valid_ungeneralized
  | INVALID_GENERALIZED -> invalid_generalized
  | _ -> fun _ _ _ -> [] in
  let queries = case_handler proof goal assumptions in
  let gather query = 
    let types' = List.map (fun (v : variable) -> v.typ) execution.proof.variables |> remove_duplicate Constr.equal in
    let types = List.filter (fun t -> try Constr.is_Prop (Typeops.infer info.env t).uj_type |> not with _ -> false) types' in
    { proof; query; types; goal; assumptions; case = execution.case; candidates = []; label = -1; } in
  List.map gather queries

let logging_problems (p : problem) = (p.proof, p.label, p.query.positives, p.query.negatives, p.query.abducted)
let logging_terms (p : problem) = (p.proof, p.label, List.map snd p.candidates) 

  let driver (info : Playground.info) generalized_definitions example_content output_file log elapsed_time (depth : int) (executions : Execution.t list) =
    (* Isolate positive and negative examples for each synthesis problem *)
    print_endline "Preparing synthesis problems for each generalization...";
    (* let context = (List.hd executions).context in *)
    let all_funcs = (List.map (fun (f : func) -> (f.label, f.typ)) info.functions) @ CoqCoreFunctions.constructors info.env @ CoqCoreFunctions.bool_eq_sketches info.env in
    let original_problems = my_parmap (prepare info) executions |> List.flatten |> List.mapi (fun label p -> { p with label }) in 
    List.iter (fun p -> if p.label < 0 then raise (Failure "Incorrect labeling of synthesis problems [in SynthInterface.driver]")) original_problems;
    print_endline ("Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds\n"); 
    let log1 = Log.synthesis_problems info output_file log elapsed_time (List.map logging_problems original_problems) in
  
    (* Enumerate the terms for each synthesis problem (dependent on available variables) *)
    print_endline "Enumerating terms for each synthesis problem..."; 
    let number lst = List.mapi (fun i x -> (i,x)) lst in
    let gvars (p : problem) = match p.proof.generalized_terms with | None -> [] | Some tbl -> Hashtbl.to_seq_keys tbl |> List.of_seq |> List.map (fun v -> v.id) in
    let enum (p : problem) = Enumerate.terms depth info.env info.sigma (List.map (fun v -> (v.id,v.typ)) p.proof.variables) (gvars p)  p.types all_funcs in
    
    (* Here we are only targeting to weaken cases where there is one generalization *)
    let problems = my_parmap (fun p -> { p with candidates = number (enum p) }) original_problems in
    print_endline ("Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds\n"); 
    let log2 = Log.enumerated_terms info output_file log1 elapsed_time (List.map logging_terms problems) in

    (* Construct the synthesis file and extract the information to an OCaml file *)
    print_endline "Extracting relevant information to OCaml..."; 
    print_endline ("Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds\n");

    let get_assumptions (p : problem) = List.mapi (fun i (p : prop) -> (Printf.sprintf "original_assumption_%d" i, p.expr.body)) p.assumptions in
    let get_state_info (p : problem) = ("original_goal",p.goal.expr.body) :: (get_assumptions p) in

    let get_examples (p : problem) b = let es = if b then p.query.positives else p.query.negatives in List.map (fun (e : example) -> e.label) es in
    let prep (p : problem) = (info.env, info.sigma, p.proof.label, p.label, get_state_info p, Hashtbl.find example_content p.proof.label, Generalize.get_example_format info p.proof, get_examples p true, get_examples p false, p.candidates) in
    let no_run, run = List.partition (fun p -> List.is_empty p.candidates && Generalize.runs_synthesis p.proof) problems in
    let prepped = List.map prep run in 

    let format = FormatSynthesis.extract info.tmp_dir generalized_definitions info.file_formatted in
    let synth_obj = my_parmap (fun (env,sigma,exec,label,state_info,tras,ex,pos,neg,cand) -> format env sigma state_info exec label tras ex pos neg cand) prepped in

    print_endline "Extraction complete! Time to run..."; 
    print_endline ("Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds\n");
    let results = Synthesizer.deploy info.tmp_dir synth_obj in

    (* Processing the synthesis results and assigning back to their problems *)
    print_endline "Synthesizer ran, now processing results...";
    let pairs = List.combine results run in 
    List.iter (fun ((i,_),p) -> if i != p.label then raise (Failure "Pairing back up problems failed in SynthInterface.driver")) pairs;
    let update_problems = fun ((_,c),p) -> {p with candidates = List.filter (fun (i,_) -> List.mem i c) p.candidates} in
    let final = List.map update_problems pairs |> List.map (cap_results info) in
    final @ no_run, Log.synthesis_results info output_file log2 elapsed_time (List.map logging_terms final)