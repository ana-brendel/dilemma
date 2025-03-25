open SynthUtils
open Coq_extractions

let openning = "open Synthesis_extraction"

let parmap_defs = 
  ["let my_parmap f lst = Parmap.parmap ?keeporder:(Some true) ?init:None ?finalize:None ?ncores:(Some 10) ?chunksize:None f (L lst)";
  "let par_filter_map f lst = my_parmap f lst |> List.filter_map (fun x -> x)"] |> String.concat "\n\n"

let check_candidate = "let check_candidate kind (func : 'd -> dec) (examples : 'd list) =
  if kind then List.for_all func examples else not (List.exists func examples)"

let running = "let run ((positive,negative) : 'c list * 'c list) (candidates : (string * ('c -> dec)) list) =
  let passed_true = par_filter_map (fun (label, func) -> if check_candidate true func positive then Some (label, func) else None) candidates in
  par_filter_map (fun (label, func) -> if check_candidate false func negative then Some label else None) passed_true"

let completing = "let complete i synthesis candidates : unit = 
  let label = string_of_int i in
  let results = run synthesis candidates in
  let results_string = String.concat \";\" results in
  print_endline (label ^ \":\" ^ results_string)"

let format_queries label exs = 
  Printf.sprintf "let synthesis_%d = %s,%s" label (fst exs) (snd exs) 

let format_candidates label candidates =
  let items = List.map (fun c -> Printf.sprintf "(\"%s\", %s)" c c) candidates in
  Printf.sprintf "let candidates_%d = [%s]" label (String.concat "; " items)

let format_driver labels = 
  let completes = List.map (fun i -> Printf.sprintf "complete %d synthesis_%d candidates_%d;" i i i) labels in
  Printf.sprintf "let () = \n%s" (String.concat "\n" completes)

let make_file dir synth candidates queries driver =
  let fname = Printf.sprintf "%s/%s.ml" dir synth in
  let content_list = openning :: [parmap_defs;check_candidate;running;completing;candidates;queries;driver] in
  let content = String.concat "\n\n" content_list in
  write_to_file ~fname ~content

let process_output output =
  let pull_number l = 
    match String.split_on_char ':' l with 
    | i :: t :: _ -> int_of_string i, if t = "" then [] else String.split_on_char ';' t 
    | _ -> raise (Failure "Unexpected result (1) Synthesizer.process_output") in
  let int_from_candidate c =
    match split_on_string "_candidate" c with 
    | [_;n] -> int_of_string n 
    | _ -> raise (Failure "Unexpected result (2) Synthesizer.process_output") in
  List.map pull_number output |> List.map (fun (s,c) -> s, List.map int_from_candidate c) 

let run directory extraction_ml (problems : (int * ((string * string) * string list)) list) =
  let synth = "synthesizer" in 
  let candidates = List.map (fun (label,(_,cans)) -> format_candidates label cans) problems in
  let queries = List.map (fun (label,(exs,_)) -> format_queries label exs) problems in
  let driver = format_driver (List.map fst problems) in
  make_file directory synth (String.concat "\n" candidates) (String.concat "\n" queries) driver;
  let build_cmd = Printf.sprintf "cd %s && ocamlfind ocamlopt -o %s -linkpkg -package parmap %s.ml %s.ml" directory synth extraction_ml synth in
  let build_ocaml = run_cmd build_cmd in
  if List.is_empty build_ocaml |> not then raise (Failure "Error building OCaml extraction in Synthesizer.run")
  else let output = run_cmd (Printf.sprintf "cd %s && ./%s" directory synth) in
  if List.is_empty output then raise (Failure "Error running OCaml synthesizer in Synthesizer.run") 
  else let results = process_output output in
    let _ = run_cmd (Printf.sprintf "rm -r %s" directory) in results

(* **************************************************************************************** *)
(* **************************************************************************************** *)
(* **************************************************************************************** *)

let open_dependencies dependencies = List.map (Printf.sprintf "open %s") dependencies
let candidate_set exec query = Printf.sprintf "candidates_%d_%d" exec query
let get_synthesizer exec = Printf.sprintf "OCaml_Synthesizer_%d" exec

let make_query_set (query : FormatSynthesis.t) : string = 
  let candidates = List.init query.candidate_count (FormatSynthesis.get_candidate_label query.exec query.query) in
  let items = List.map (fun c -> Printf.sprintf "(\"%s\", %s)" c c) candidates in
  Printf.sprintf "let %s = [%s]" (candidate_set query.exec query.query) (String.concat "; " items)

let make_driver (queries : FormatSynthesis.t list) : string =
  let candidates (t : FormatSynthesis.t) = candidate_set t.exec t.query in
  let set kind (t : FormatSynthesis.t) = FormatSynthesis.get_synthesis_set kind t.exec t.query in
  let query (t : FormatSynthesis.t) =  Printf.sprintf "complete %d (%s,%s) %s;" t.query (set true t) (set false t) (candidates t) in
  Printf.sprintf "let () = \n%s" (String.concat "\n" (List.map query queries))

let make_ml_file tmp_dir ml openning definitions query_sets driver =
  let fname = Printf.sprintf "%s/%s.ml" tmp_dir ml in
  let content_list = [openning;parmap_defs;check_candidate;running;completing;definitions;query_sets;driver] in
  let content = String.concat "\n\n" content_list in
  write_to_file ~fname ~content

let process output =
  let pull_number l = 
    match String.split_on_char ':' l with 
    | i :: t :: _ -> int_of_string i, if t = "" then [] else String.split_on_char ';' t 
    | _ -> raise (Failure "Unexpected result (1) Synthesizer.process") in
  let int_from_candidate c =
    match String.split_on_char '_' c with 
    | [_;_;_;n] -> int_of_string n 
    | _ -> raise (Failure "Unexpected result (2) Synthesizer.process") in
  List.map pull_number output |> List.map (fun (s,c) -> s, List.map int_from_candidate c) 

let deploy_per_object tmp_dir (obj : FormatSynthesis.t) : string list =
  let dependencies = [obj.ml_file] in
  let examples, ocaml_defintions = FormatSynthesis.format_t obj in
  let candidate_lists = make_query_set obj in
  let query_sets = make_query_set obj  in
  let driver = make_driver [obj] in
  let ml_file = Printf.sprintf "FullSynthesis_%d_%d" obj.exec obj.query in
  make_ml_file tmp_dir ml_file (open_dependencies dependencies |> String.concat "\n") ocaml_defintions query_sets driver;
  Extractor.run tmp_dir dependencies ml_file 

let deploy tmp_dir synth_objects =
  let outputs = my_parmap (deploy_per_object tmp_dir) synth_objects in
  List.concat_map process outputs

  (* let example_dependencies = List.map (fun (s : FormatSynthesis.t) -> Examples.state_examples_ml s.exec) synth_objects |> remove_duplicate (=) in
  let synth_dependencies = List.map (fun (s : FormatSynthesis.t) -> s.ml_file) synth_objects in 
  let dependencies = example_dependencies @ synth_dependencies in
  let examples, ocaml_defintions = List.map FormatSynthesis.format_t synth_objects |> List.split in
  let candidate_lists = List.map make_query_set synth_objects |> String.concat "\n" in
  let query_sets = List.map make_query_set synth_objects |> String.concat "\n"  in
  let driver = make_driver synth_objects in
  let ml_file = "FullSynthesis" in
  make_ml_file tmp_dir ml_file (open_dependencies dependencies |> String.concat "\n") (String.concat "\n" ocaml_defintions) query_sets driver;
  let output = Extractor.run tmp_dir dependencies ml_file in
  process output *)