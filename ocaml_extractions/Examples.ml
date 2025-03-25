open ExtractionUtils

let examples_ml exec = Printf.sprintf "Example_Set_%d" exec

let state_examples_ml exec = Printf.sprintf "State_%d" exec
let example_cap_per_type = 20
let overall_example_cap = 9000
let example_label exec id = Printf.sprintf "g%d_example%d" exec id
let example_set_label exec = Printf.sprintf "example_set_%d" exec 

let generator env sigma tmp_dir file_formatted i typ = 
  let typ_string = str_of_constr_full_via_str env sigma typ in
  let prelude = Formatting.prelude file_formatted in
  let generator_code = Formatting.generation_code typ_string in
  let driver = Printf.sprintf "type_generation_%d.v" i in
  let fname = join_paths tmp_dir driver in
  let content = String.concat "\n" (prelude :: "" :: generator_code) in 
  write_to_file ~fname ~content; 
  let results = run_cmd (Printf.sprintf "cd %s && coqc %s" tmp_dir driver) in
  let dedup = remove_duplicate String.equal results in
  let prune = ["QuickChecking generate_for_type";"cp -rL";"+++ Passed";"Time Elapsed:"] in
  let cleaned = List.filter (fun l -> (List.exists (fun prefix -> String.starts_with ~prefix l) prune |> not) && not ("" = String.trim l)) dedup in
  cleanup tmp_dir (Printf.sprintf "type_generation_%d" i);
  (typ, (List.map (fun value -> interp_string env sigma value typ) cleaned))

let format_for_extraction exec example_type_str examples =
  (* example = (int label, (example label str, example content)) *)
  let example_labels = List.map (fun (i,(l,_)) -> i,l) examples in
  let definitions = List.map (Formatting.define_single_example example_type_str) (List.map snd examples) in
  let set_label = example_set_label exec in
  let set_definitions = Formatting.define_example_set example_type_str set_label example_labels in
  let coq_content = (String.concat "\n" definitions) ^ "\nRequire Import String. Open Scope string_scope.\n" ^ set_definitions ^ "\nClose Scope string_scope." in
  let extract_terms = (List.map snd example_labels) @ [set_label] in 
  exec, coq_content, extract_terms

let examples_by_cartesian str examples_by_type label ((vars,str_vars),(types,str_types)) = 
  let fetch typ = try Hashtbl.find examples_by_type typ with _ -> raise (Failure "No examples for type were generated or stored [in Examples.format_for_extraction]") in
  let types_by_var_simple = List.map fetch types |> List.map (partition_at 5) in
  let types_by_var = List.map fetch types |> List.map (partition_at example_cap_per_type) in
  let groups_simple = cartesian types_by_var_simple in 
  let groups = if (List.length groups_simple < overall_example_cap) then cartesian types_by_var else [] in 
  let format_label i = example_label label i in
  let format_ex ex = Printf.sprintf "(%s)" (String.concat "," (List.map str ex)) in
  let cut = partition_at overall_example_cap (groups_simple @ groups) in
  let examples = List.mapi (fun i g -> i, (format_label i, format_ex g)) cut in
  format_for_extraction label str_types examples

let fill_generalized str ((vars,_),(types,_)) (var,expr) generated : string =
  let values = String.split_on_char '&' generated in
  let val_by_var = try List.combine vars values with _ -> raise (Failure "Incorrectly matching up vars and values [in Examples.fill_generalized]") in
  let non_gen = List.filter (fun (v,_) -> Names.Id.equal var v |> not) val_by_var in
  let var_types = List.combine vars types |> List.filter (fun (v,_) -> Names.Id.equal var v |> not) in
  let non_gen_args = String.concat " " (List.map (fun (v,t) -> Printf.sprintf "(%s : %s)" (Names.Id.to_string v) (str t)) var_types) in
  let lambda = Printf.sprintf "((fun %s => %s) %s)" non_gen_args (str expr) (String.concat " " (List.map (fun (_,s) -> "(" ^ s ^ ")") non_gen)) in
  List.map (fun (v,s) -> if Names.Id.equal var v then lambda else s) val_by_var |> String.concat "&"

let needs_generalized vars expr = let vars_in_term = vars_in_constr expr in not (List.exists (fun v -> not (List.mem v vars)) vars_in_term)

(* TODO - if we want to generalize function types, we should add generator code for any function type needed here *)
let examples_by_state tmp_dir file_formatted str exec assumptions goal needs_assump (generalized_terms : (Names.variable * Constr.t) list) (ex_vars,ex_types) =
  let state = List.fold_left (fun acc p -> implication_constr p acc) goal assumptions in
  let prelude = Formatting.prelude file_formatted in
  let generator_code = Formatting.generation_code_by_prop str overall_example_cap (ex_vars,ex_types) (str state) in 
  let driver = Printf.sprintf "state_example_generation_%d.v" exec in
  let fname = join_paths tmp_dir driver in
  let content = String.concat "\n" (prelude :: "" :: generator_code) in 
  write_to_file ~fname ~content; 
  let results = run_cmd (Printf.sprintf "cd %s && coqc %s" tmp_dir driver) in
  let dedup = remove_duplicate String.equal (String.concat " " results |> String.split_on_char '!') |> List.map String.trim in
  let prune = ["QuickChecking generate_for_type";"cp -rL";"+++ Passed";"Time Elapsed:";"*** Failed"] in
  let cap = partition_at (overall_example_cap - 1000) in let first_500 = partition_at 1000 in
  let check = List.filter (fun line -> (contains line "*** Failed" |> not) && List.length (String.split_on_char '&' line) = List.length (fst ex_vars)) in
  let generated = check (List.filter (fun l -> (List.exists (fun prefix -> String.starts_with ~prefix l) prune |> not) && not ("" = String.trim l)) dedup) |> cap in
  let generalized_to_replace = List.filter (fun (_,e) -> needs_generalized (fst ex_vars) e) generalized_terms in
  let filled = List.fold_left (fun exs pair -> my_parmap (fill_generalized str (ex_vars,ex_types) pair) exs) (first_500 generated) generalized_to_replace in
  let examples = if (not needs_assump) || List.is_empty generalized_to_replace then generated else filled @ generated in
  let cleaned = List.map (fun e -> "(" ^ Str.global_replace (Str.regexp "&") "," e ^ ")") examples in
  cleanup tmp_dir (Printf.sprintf "state_example_generation_%d" exec);
  print_endline (Printf.sprintf "\t%d Examples for Execution %d" (List.length cleaned) exec);
  List.mapi (fun i ex -> i, (example_label exec i, ex)) cleaned |> format_for_extraction exec (snd ex_types)

let extract tmp_dir file_formatted (label, coq_content, extract_term) =
  let file = Extractor.extract false None tmp_dir file_formatted (examples_ml label) coq_content extract_term in
  let example_ml_content = List.rev (read_file (join_paths tmp_dir (Printf.sprintf "%s.ml" file))) in
  let examples_defined = cut_at_line_containing "_example0"  example_ml_content in 
  let example_mli_content = List.rev (read_file (join_paths tmp_dir (Printf.sprintf "%s.mli" file))) in
  let examples_defined_mli = cut_at_line_containing "_example0" example_mli_content in
  label, ((String.concat "\n" examples_defined), (String.concat "\n" examples_defined_mli))
  (* label, Extractor.extract tmp_dir file_formatted (examples_ml label) coq_content extract_term *)

(* let examples_for_reduction tmp_dir file_formatted str exec assumptions goal (ex_vars,ex_types) =
  let count = 12000 in
  let state' = List.fold_left (fun acc p -> implication_constr p acc) goal assumptions in
  let state = match disjoin_props [(negate_prop goal);state'] with Some ctor -> ctor | None -> state' in
  let prelude = Formatting.prelude file_formatted in
  let generator_code = Formatting.generation_code_by_prop str count (ex_vars,ex_types) (str state) in 
  let driver = Printf.sprintf "reduction_example_generation_%d.v" exec in
  let fname = join_paths tmp_dir driver in
  let content = String.concat "\n" (prelude :: "" :: generator_code) in 
  write_to_file ~fname ~content; 
  let results = run_cmd (Printf.sprintf "cd %s && coqc %s" tmp_dir driver) in
  let dedup = remove_duplicate String.equal (String.concat " " results |> String.split_on_char '!') |> List.map String.trim in
  let prune = ["QuickChecking generate_for_type";"cp -rL";"+++ Passed";"Time Elapsed:";"*** Failed"] in
  let cap = partition_at count in
  let check = List.filter (fun line -> (contains line "*** Failed" |> not) && List.length (String.split_on_char '&' line) = List.length (fst ex_vars)) in
  let examples = check (List.filter (fun l -> (List.exists (fun prefix -> String.starts_with ~prefix l) prune |> not) && not ("" = String.trim l)) dedup) |> cap in
  let cleaned = List.map (fun e -> "(" ^ Str.global_replace (Str.regexp "&") "," e ^ ")") examples in
  (* cleanup tmp_dir (Printf.sprintf "reduction_example_generation_%d" exec); *)
  print_endline (Printf.sprintf "\t%d Examples for Execution %d" (List.length cleaned) exec);
  List.mapi (fun i ex -> i, (example_label exec i, ex)) cleaned |> format_for_extraction exec (snd ex_types) *)