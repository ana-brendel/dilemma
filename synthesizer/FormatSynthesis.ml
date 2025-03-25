open Coq_extractions

type t = {
  exec : int;
  query : int; 
  candidate_count : int;
  ml_file : string;
  positives : int list;
  negatives : int list
}

let get_candidate_label exec query label = Printf.sprintf "candidate_%d_%d_%d" exec query label
let get_synthesis_set kind exec query = Printf.sprintf "%s_synthesis_%d_%d" (if kind then "pos" else "neg") exec query

let format_candidates env sigma (vars,types) exec query candidates = 
  let label_candidate i = get_candidate_label exec query i in
  let format pair = Formatting.format_prop env sigma (vars,types) pair in
  let pairs = List.map (fun (i,c) -> label_candidate i, c) candidates in
  List.map fst pairs, List.map format pairs

let extract tmp_dir generalized_definitions file_formatted env sigma state_info exec query extras example_format positives negatives candidates : t = 
  let candidates, candidate_definitions = format_candidates env sigma example_format exec query candidates in
  let state_for_definitions = List.map (Formatting.format_prop env sigma example_format) state_info in
  let coq_content = String.concat "\n" (Formatting.prop_to_bool :: (state_for_definitions @ (List.map snd generalized_definitions) @ candidate_definitions)) in
  let ml_file = Extractor.extract true (Some (true,extras)) tmp_dir file_formatted (Printf.sprintf "Synthesis_def_%d_%d" exec query) coq_content ((List.map fst state_info) @ (List.map fst generalized_definitions) @ candidates) in
  { exec; query; candidate_count = List.length candidates; ml_file; negatives; positives } 

let format_example_set exec query kind examples =
  let label = get_synthesis_set kind exec query in
  let example_labels = List.map (Examples.example_label exec) examples |> String.concat "; " in
  label, Printf.sprintf "let %s = [%s]" label example_labels

let format_t t =
  let positive_label, positive_definition = format_example_set t.exec t.query true t.positives in
  let negative_label, negative_definition = format_example_set t.exec t.query false t.negatives in 
  (t.query, (positive_label, negative_label)), positive_definition ^ "\n" ^ negative_definition