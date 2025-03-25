open Utils
open Masks
open Playground

let display str label assumptions goal : string = 
  [ ("Label: " ^ label); ("Assumptions: " ); 
  (Hashtbl.fold (fun _ (e : Masks.expr) acc -> (acc ^ " -- " ^ str e.body ^ "\n")) assumptions "");
  ("----------------------------------");("Goal: " ^ str goal.body)] |> String.concat "\n"

let display_p str label assumptions goal : string = 
  [ ("Label: " ^ label); ("Assumptions: " ); 
  (Hashtbl.fold (fun _ (e : Masks.prop) acc -> (acc ^ " -- " ^ str e.expr.body ^ "\n")) assumptions "");
  ("----------------------------------");("Goal: " ^ str goal.expr.body)] |> String.concat "\n"

let initial (context : Playground.t) : string * string = 
  let breaker = "--------------------------------------------------------------------" in
  let title = "Lemma Synthesis Execution Log and Results" in
  let str = str_of_constr context.info.env context.info.sigma in
  let rec get_file i = 
    let fname = context.info.cwd ^ "/log_for_" ^ context.info.current_proof ^ string_of_int i ^ ".txt" in
    if Sys.file_exists fname then get_file (i + 1) else fname in
  let file = get_file 1 in
  let state = display str "Initial State" context.proof.assumptions context.proof.goal in
  let contents = String.concat "\n" [title;breaker;breaker;"";state] in 
  write_to_file file contents; file, contents

let generalized_variables output_file previous elapsed_time (context : Playground.t) generalized_variables : string = 
  let title = "------------------------------ GENERALIZED VARIABLES ------------------------------" in
  let timer = "Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds\n" in 
  let str = str_of_constr context.info.env context.info.sigma in
  let format v e = Printf.sprintf "%s : %s = %s" (Names.Id.to_string v.id) (str v.typ) (str e.body) in
  let vars = Hashtbl.fold (fun v e acc -> (format v e) :: acc) generalized_variables [] |> List.rev in
  let contents = String.concat "\n" (previous :: "\n" :: title :: timer :: vars) in 
  write_to_file output_file contents; contents

let generalizations info output_file previous elapsed_time (executions : Execution.t list) : string =
  let case_str (case : Execution.case) = ("Case: " ^ match case with | VALID_GENERALIZED -> "Valid and Generalized" | UNSTABLE -> "Not Stable" | DEAD_END -> "Assumptions Not Satisfied"
  | VALID_UNGENERALIZED -> "Valid and Un-Generalized"  | INVALID_GENERALIZED -> "Invalid and Generalized") in
  let title = "------------------------------ GENERALIZATIONS ------------------------------" in
  let note = "  NOTE: The assumptions have been restricted to be only the necessary assumptions." in
  let timer = "Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds\n" in 
  let str (e : Execution.t) = str_of_constr info.env info.sigma in
  let format (e : Execution.t) = display_p (str e) (Printf.sprintf "Generalization #%d" e.label) e.proof.assumptions e.proof.goal ^ "\n" ^ case_str e.case ^ "\n" in
  let gens = List.map format executions in
  let contents = String.concat "\n" (previous :: "\n" :: title :: note :: timer :: gens) in 
  write_to_file output_file contents; contents

let functions info : string = 
  let str = str_of_constr info.env info.sigma in
  let header = " -- functions to consider -- " in
  let format (f : func) = Printf.sprintf "%s : %s" (str f.label) (str f.typ) in
  let funcs = List.map format info.functions in
  header :: funcs |> String.concat "\n"

let format_problem info i ((context, label, positives,negatives,abducted) : Generalize.t * int * example list * example list * prop option) : string = 
  let str = str_of_constr info.env info.sigma in
  let label = Printf.sprintf "Label: %d (%d)" label i in
  (* let format_value ((vr,vl) : (Names.variable * Constr.t)) = Printf.sprintf "%s := %s" (Names.Id.to_string vr) (str vl) in
  let format_example (e : example) = "   [" ^ String.concat "; " (List.map format_value e.values) ^ "]" in *)
  let format title examples = title ^ " " ^ string_of_int (List.length examples) in
    (* let trailing = if List.length examples > 10 then "   etc ...\n" else "" in
    let exs = List.map format_example (partition_at 10 examples) |> String.concat "\n" in
    [title;exs;trailing] |> String.concat "\n" in *)
  let positives = format "Positive Examples:" positives in
  let negatives = format "Negative Examples:" negatives in
  let abducted = match abducted with Some a -> "Abducted Assumption: " ^ (str a.expr.body) | _ -> "Inferring Condition About Generalization" in
  String.concat "\n" [label;abducted;positives; negatives] 

let synthesis_problems info output_file previous elapsed_time problems : string = 
  let title = "------------------------------ SYNTHESIS PROBLEMS ------------------------------" in
  let timer = "Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds\n" in 
  let funcs = if List.is_empty problems then "" else functions info in
  let problem_string = List.mapi (format_problem info) problems |> String.concat "\n\n" in 
  let contents = String.concat "\n" [previous;"\n";title;timer;funcs;"";problem_string] in
  write_to_file output_file contents; contents

let format_terms info i ((_, label, candidates) : Generalize.t * int * Constr.t list) : string = 
  let label = Printf.sprintf "Label: %d (%d)" label i in
  let strings = List.map (str_of_constr info.env info.sigma) candidates in
  let groups = k_sized_partitions 10 strings in
  let lines = List.map (String.concat ", ") groups in
  String.concat "\n" (label :: lines)

let enumerated_terms info output_file previous elapsed_time problems : string = 
  let title = "------------------------------ TERMS CONSIDERED IN SYNTHESIS ------------------------------" in
  let timer = "Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds\n" in 
  let problem_string = List.mapi (format_terms info) problems |> String.concat "\n\n" in 
  let contents = String.concat "\n" [previous;"\n";title;timer;"";problem_string] in
  write_to_file output_file contents; contents

let format_combined info i problem ((context, label, candidates) : Generalize.t * int * Constr.t list) =
  let prob_formatted = format_problem info i problem in
  let strings = List.map (str_of_constr info.env info.sigma) candidates in
  let groups = k_sized_partitions 10 strings in
  let lines = List.map (String.concat ", ") groups in
  String.concat "\n" (prob_formatted :: lines)

let combined_synth_problems info output_file previous elapsed_time problems : string = 
  let title = "------------------------------ COMBINED SYNTHESIS PROBLEMS ------------------------------" in
  let timer = "Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds\n" in 
  let problem_string = List.mapi (fun i p -> format_combined info i (fst p) (snd p)) problems |> String.concat "\n\n" in 
  let contents = String.concat "\n" [previous;"\n";title;timer;"";problem_string] in
  write_to_file output_file contents; contents

let synthesis_results info output_file previous elapsed_time problems : string = 
  let title = "------------------------------ SYNTHESIS RESULTS ------------------------------" in
  let timer = "Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds\n" in 
  let problem_string = List.mapi (format_terms info) problems |> String.concat "\n\n" in 
  let contents = String.concat "\n" [previous;"\n";title;timer;"";problem_string] in
  write_to_file output_file contents; contents

let construction_results output_file previous elapsed_time env sigma synth_results : string = 
  let title = "------------------------------ PROCESSED SYNTHESIS RESULTS ------------------------------" in
  let timer = "Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds\n" in 
  let pstr b x = (if b then " - " else "") ^ str_of_constr env sigma x in
  let lst = Hashtbl.to_seq synth_results |> List.of_seq in
  let problem_string =  List.map (fun (assump, results) -> String.concat "\n" (pstr false assump :: List.map (pstr true) results)) lst in
  let contents = String.concat "\n" [previous;"\n";title;timer;"";(String.concat "\n\n" problem_string)] in
  write_to_file output_file contents; contents

let full_construction_results output_file previous elapsed_time env sigma full_lemmas : string = 
  let title = "------------------------------------ CANDIDATE CONSTRUCTION RESULTS -----------------------------------" in
  let disclaimer = "------------------------------ [ disclaimer: not pruning by provability] ------------------------------" in
  let timer = "Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds\n" in 
  let pairs = List.map (fun (a,b) -> if String.equal a b then b else a ^ "\n" ^ b) full_lemmas in
  let contents = String.concat "\n" [previous;"\n";title;disclaimer;timer;"";(String.concat "\n\n" pairs)] in
  write_to_file output_file contents; contents

let results output_file previous elapsed_time top results : string = 
  let clean s = Str.global_replace (Str.regexp "\n") " " s in
  let cut_off = 5 in
  let format_results = List.mapi (fun i (l,m) -> if String.equal l m then Printf.sprintf "%d. %s\n" (i + 1) (clean l) else Printf.sprintf "%d. %s\n%s\n" (i + 1) (clean l) (clean m)) in
  let all_title = if List.length results > cut_off then "------------------------------ ALL RESULTS ------------------------------" else "" in
  let all_formatted = if List.length results > cut_off then format_results results |> String.concat "\n" else "" in
  let title = "------------------------------ FINAL RESULTS ------------------------------" in
  let timer = "Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds\n" in 
  let count = Printf.sprintf "Number of Result Pairs Returned: %d" (List.length results) in
  let formatted = format_results (partition_at cut_off top) in
  let contents = String.concat "\n" (previous :: "\n" :: all_title :: all_formatted :: "\n" :: title :: timer :: count :: "" :: formatted) in
  write_to_file output_file contents; contents

let contradiction typ output_file previous elapsed_time : unit = 
  let title = "------------------------------ CONTRADICTION ------------------------------" in
  let label = if typ = 0 then "assumptions are unsat" else if typ = 1 then "goal is unsat" else "proof is unstable" in
  let timer = "Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds\n" in 
  let contents = String.concat "\n" [previous;"\n";title;label;timer;"There is a contradiction in your assumptions; target isolating contradiction to complete proof."] in
  write_to_file output_file contents