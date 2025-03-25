open Masks
open Coq_extractions

(* let do_ranking (info : Playground.info) k results (cmp : Candidates.result -> Candidates.result -> int) =
    let results_sorted = List.sort cmp results in Utils.clear_dir info.tmp_dir; 
    let first, second = Utils.partition_at_split 15 results_sorted in
    let valid = Candidates.prune_invalid info first in
    if List.length valid >= 10 then Utils.partition_at 10 valid
    else let valid_2 = Candidates.prune_invalid info second in Utils.partition_at 10 (valid @ valid_2) *)

(* let different_rankings output_file info previous current (results : Candidates.result list) : unit = 
  let clean s = Str.global_replace (Str.regexp "\n") " " s |> Str.global_replace (Str.regexp "\t") " " in
  let format_results = List.mapi (fun i (l,m) -> if String.equal l m then Printf.sprintf "%d. %s\n" (i + 1) (clean l) else Printf.sprintf "%d. %s\n%s\n" (i + 1) (clean l) (clean m)) in
  let r0 = "------------------------------ RANKING (length based 1) ------------------------------" in
  let c0 = List.map (Candidates.result_str info) (do_ranking info 10 results Candidates.rank_length_alt) |> format_results |> String.concat "\n" in
  let r1 = "------------------------------ RANKING (length based 2) ------------------------------" in
  let c1 = List.map (Candidates.result_str info) (do_ranking info 10 results Candidates.rank_length) |> format_results |> String.concat "\n" in
  let r2 = "------------------------------ RANKING (construction) ------------------------------" in
  let c2 = List.map (Candidates.result_str info) (do_ranking info 10 results Candidates.rank_construction_other) |> format_results |> String.concat "\n" in
  let r3 = "------------------------------ RANKING (current) ------------------------------" in
  let c3 = List.map (Candidates.result_str info) (Utils.partition_at 10 current) |> format_results |> String.concat "\n" in 
  let contents = String.concat "\n" [previous;"\n";r0;c0;"";r1;c1;"";r2;c2;"";r3;c3;"";] in
  Utils.write_to_file output_file contents *)

let driver = 
  Proofview.Goal.enter begin fun gl ->
    let initial_time = Unix.gettimeofday() in
    let elapsed_time (t) = (t -. initial_time) |> (fun f -> Float.round (f *. 1000.) /. 1000.) |> string_of_float in

    print_endline "\nSTARTING TO RUN LEMMA SYNTHESIS";
    print_endline ("CORES BEING USED: " ^ string_of_int (Setcore.numcores ()));
    print_endline ("\nGathering proof context and relevant information..."); 
    let original_context, original_info = Playground.fetch gl in
    let context =  ReduceProof.simplify_assumptions original_info original_context in

    print_endline ("Gathered proof context, beginning to analyze...\n"); 
    if Option.has_some context.generalized_terms then raise (Failure "There should be no generalizations yet (1)");
    let output_file, outputs1 = Log.initial { info = original_info; proof = context } in

    let generalized_variables = Generalize.gather original_info original_context in 
    let env = Hashtbl.fold (fun (v : variable) _ env' -> Environ.push_named (LocalAssum (Context.annotR v.id, v.typ)) env') generalized_variables original_info.env in
    let sigma = Evd.from_env env in
    let info = { original_info with env; sigma } in  
    let str = Utils.str_of_constr env sigma in

    print_endline "Checking for contradiction in assumptions...";
    match (ReduceProof.is_contradiction info context) with
    | true -> (print_endline "CONTRADICTION FOUND -- DONE"; Log.contradiction 0 output_file outputs1 elapsed_time; let _ = Utils.run_cmd (Printf.sprintf "rm -r %s" info.tmp_dir) in Proofview.tclUNIT ()) 
    | _ -> print_endline "[NO CONTRADICTION DETECTED IN ASSUMPTIONS!]\n";

    print_endline "Checking for contradiction in assumptions...";
    match (ReduceProof.is_never_true info context) with
    | true -> (print_endline "GOAL IS NEVER SATISFIABLE AND ASSUMPTION MIGHT BE, TARGET CONTRADICTION OR PROOF INVALID -- DONE"; Log.contradiction 1 output_file outputs1 elapsed_time; let _ = Utils.run_cmd (Printf.sprintf "rm -r %s" info.tmp_dir) in  Proofview.tclUNIT ()) 
    | _ -> print_endline "[GOAL IS SATISIABLE!]\n";

    print_endline ("Created variables representing generalized subterms.");
    print_endline ("Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds");
    let outputs2 = Log.generalized_variables output_file outputs1 elapsed_time {info; proof = context} generalized_variables in 

    print_endline ("\nCreating Generalizations..."); 
    if Option.has_some context.generalized_terms then raise (Failure "There should be no generalizations yet (2)");
    let generalizations' = Generalize.create info context generalized_variables in
    let ungen, gen = List.partition (fun (g: Generalize.t) -> match g.generalized_terms with | None -> true | _ -> false) generalizations' in
    let og = if (List.length ungen = 1) then (List.hd ungen) else raise (Failure "[in tactic] Should only be one ungeneralized") in
    print_endline "Reducing original proof context to include only the necesary information...";
    let ungeneralized = ReduceProof.initial_filter info og in 

    match ungeneralized.state with
    | UNSTABLE -> (print_endline "PROOF IS UNSTABLE WITHOUT QUANTIFIED ASSUMPTIONS - need to use a quanitifed assumption and/or find contradiction"; 
    Log.contradiction 2 output_file outputs1 elapsed_time; 
    let _ = Utils.run_cmd (Printf.sprintf "rm -r %s" info.tmp_dir) in  Proofview.tclUNIT ()) 
    | _ -> ();

    let aa = Hashtbl.fold (fun _ (p : prop) acc ->  p.expr.body :: acc) ungeneralized.assumptions [] |> List.mapi (fun i e -> (Printf.sprintf "original_assumption_%d" i, e)) in
    let gvs = Hashtbl.fold (fun (v : variable) (e : expr) acc ->  (Utils.construct_equal env v.typ e.body e.body) :: acc) generalized_variables [] |> List.mapi (fun i e -> (Printf.sprintf "gv_defs_%d" i, e)) in
    let state_info = ("original_goal",ungeneralized.goal.expr.body) :: aa @ gvs in
    let format_state_defs = Formatting.format_prop info.env info.sigma (Generalize.get_example_format info ungeneralized) in
    let state_for_definitions = List.map (fun p -> fst p, format_state_defs p) state_info in 

    print_endline ("Reducing generalizations to include only necessary info...");
    let max_generalization_infer = 2 in
    let generalizations = ungeneralized :: Utils.my_parmap (ReduceProof.filter_assumptions info ungeneralized.assumptions) gen 
      |> List.sort (fun (g1 :Generalize.t) (g2 :Generalize.t) -> Int.compare (g1.label) (g2.label))
      |> Utils.my_parmapi (Generalize.check_validity info) (* doing a final pass to make sure we are correctly resasoning about validity of generlization*)
      |> List.filter (fun (g : Generalize.t) -> match g.state with STABLE -> true | UNSTABLE -> Generalize.generalization_count g <= max_generalization_infer) in
    print_endline ("\nGeneralizations to analyze: " ^ string_of_int (List.length generalizations));
    print_endline ("Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds");

    (* This sections does example generation using the proof state to try to leverage QuickChick heuristics *)
    print_endline ("\nGenerating examples using QuickChick on proof state (in parallel)...");
    let ex_by_state = Examples.examples_by_state info.tmp_dir info.file_formatted str in
    let assumps (g : Generalize.t) = Hashtbl.to_seq_values g.assumptions |> List.of_seq |> List.map (fun e -> e.expr.body) in
    let simplify_gen (g : Generalize.t) = match g.generalized_terms with Some tbl -> List.map (fun (v,e) -> v.id, e.body) (Hashtbl.to_seq tbl |> List.of_seq) | _ -> [] in
    let gen_needed (g : Generalize.t) = List.exists (fun v -> String.starts_with ~prefix:"GenVarEq_" (Names.Id.to_string v.id)) (Hashtbl.to_seq_keys g.assumptions |> List.of_seq) in
    let gen_map (g : Generalize.t) = ex_by_state g.label (assumps g) g.goal.expr.body (gen_needed g) (simplify_gen g) (Generalize.get_example_format info g) in
    let extraction_formatted = Utils.my_parmap gen_map (List.filter Generalize.runs_synthesis generalizations) in 

    print_endline ("Extracting examples to OCaml (in parallel)... ");
    let make_gv_expr_def (v : variable) (e : expr) acc = ("definitions_" ^ Names.Id.to_string v.id, (Utils.construct_equal info.env v.typ e.body e.body)) :: acc in
    let format_gen_terms ((v,e) : (_ * Constr.t)) = Formatting.format_prop info.env info.sigma (Generalize.get_example_format info ungeneralized) (v,e) in
    let generalized_definitions = Hashtbl.fold make_gv_expr_def generalized_variables [] |> List.map (fun p -> (fst p), format_gen_terms p) in
    let example_sets_ml' = Utils.my_parmap (Examples.extract info.tmp_dir info.file_formatted) extraction_formatted in
    let example_sets_ml_definitions = Hashtbl.of_seq (List.to_seq example_sets_ml') in
    print_endline "Examples for each generalization extracted to OCaml";
    print_endline ("Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds");
 
    print_endline ("\nAnalyzing Each Generalization in parallel...");
    let executions = Utils.my_parmap (Execution.analyze info generalized_definitions example_sets_ml_definitions) generalizations |> List.filter_map (fun g -> g)  in
    print_endline "Finished analyzing generalizations:"; 
    List.iter (fun e' -> Execution.display info e'; print_newline ()) executions;
    print_endline ("Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds");

    let outputs3 = Log.generalizations info output_file outputs2 elapsed_time executions in

    (print_endline ("-------------------- SYNTHESIZING --------------------");
    let results, outputs4 = SynthInterface.driver info generalized_definitions example_sets_ml_definitions output_file outputs3 elapsed_time 1 executions in
    print_endline "\nSynthesis complete!";
    print_endline ("Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds");

    print_endline ("\n-------------------- CANDIDATE CONSTRUCTION --------------------"); 
    let processed = Candidates.updated_construction info elapsed_time (state_for_definitions @ generalized_definitions) example_sets_ml_definitions executions results in
    let offset = List.fold_left (fun sum (c: Candidates.constructor) -> sum + List.length c.results) 0 processed in
    let no_weakening = Candidates.get_results_directly offset executions in
    (* let prioritize_rewrites = (Hashtbl.length ungeneralized.assumptions = 0)in *)
    let all_results' = List.sort (Candidates.compare) (no_weakening @ (List.concat_map (fun (c: Candidates.constructor) -> c.results) processed)) in
    let all_results = Utils.remove_duplicate Candidates.result_eq all_results' in
    Utils.clear_dir info.tmp_dir; 
    print_endline "Checking that all lemmas are valid with QuickChick (double check)...";
    let valid = Candidates.prune_invalid info (Utils.partition_at 30 all_results) in
    print_endline ("[QuickChick Check Complete] Time Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds\n");
    let all_lemmas = List.map (Candidates.result_str info) all_results in 
    let lemmas = List.map (Candidates.result_str info) valid in 

    let outputs5 = outputs4 in

    print_endline ("\n-------------------- RESULTS --------------------");
    let _ = Log.results output_file outputs5 elapsed_time lemmas all_lemmas in
    let top5 = Utils.partition_at 5 lemmas in
    List.iter (fun (l,m) -> print_endline (if String.equal l m then l else l ^ "\n" ^ m ); print_newline ()) top5;
    print_endline (Printf.sprintf "Number of Result Pairs Returned (before QuickChick): %d" (List.length all_lemmas));
    print_endline ("\nTime Elapsed From Start: " ^ (Unix.gettimeofday () |> elapsed_time) ^ " seconds");
    let _ = Utils.run_cmd (Printf.sprintf "rm -r %s" info.tmp_dir) in 
    (* different_rankings output_file info final_output valid all_results;
    let _ = Utils.run_cmd (Printf.sprintf "rm -r %s" info.tmp_dir) in  *)
    Proofview.tclUNIT ()) (* Unit Return Type... ends execution. *)
  end