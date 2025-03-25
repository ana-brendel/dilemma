open ExtractionUtils

let openning dependencies = List.map (Printf.sprintf "open %s") dependencies

let example_set_by_exec i = Printf.sprintf "example_set_%d" i

let parmap_defs = 
  ["let my_parmap f lst = Parmap.parmap ?keeporder:(Some true) ?init:None ?finalize:None ?ncores:(Some 10) ?chunksize:None f (L lst)";
  "let par_filter_map f lst = my_parmap f lst |> List.filter_map (fun x -> x)"] |> String.concat "\n\n"

let char_list_to_string = "let char_list_to_string (c : char list) : string = String.of_seq (List.to_seq c)"

let split_for_prop = "let split_for_prop (example_set : ((char list) * 'c) list) (prop_str : string) (prop : 'c -> bool) : unit =
  let trues,falses = List.partition_map (fun (s,c) -> if prop c then Left (char_list_to_string s) else Right (char_list_to_string s)) example_set in
  print_endline \";\"; print_endline prop_str;
  print_endline \"*\"; print_endline (String.concat \",\" trues);
  print_endline \"*\"; print_endline (String.concat \",\" falses)"

let checking_all = "let check (examples : 'c list) (candidates : (string * ('c -> dec)) list) =
  par_filter_map (fun (label, func) -> if List.for_all func examples then Some label else None) candidates"

let display_list = "let display passed = List.iter print_endline passed"

let format_prop_split example_set prop = Printf.sprintf "split_for_prop %s \"%s\" %s" example_set prop prop

let format exec dependencies props = 
  let prop_calls = List.map (format_prop_split (example_set_by_exec exec)) props in
  let driver = Printf.sprintf "let () = %s" (String.concat "; " prop_calls) in
  String.concat "\n" ((openning dependencies) @ ["\n";char_list_to_string;"\n";split_for_prop;"\n";driver])

let process_prop_result result : (string * int list * int list) option = 
  if result = "" then None else
  let split = String.split_on_char '*' result in
  if (List.length split != 3) then (List.iter print_endline split;
    raise (Failure "Processing error in making proposition [in Evaluator.process_prop_result]"))
  else let label, true_strings, false_strings = List.hd split, List.hd (List.tl split), List.hd (List.tl (List.tl split)) in
  let get_ints str = String.split_on_char ',' str |> List.map String.trim |> List.filter_map (fun s -> try Some (int_of_string s) with _ -> None) in
  Some (String.trim label, get_ints true_strings, get_ints false_strings)

let split_examples tmp_dir exec state_ml props = 
  let dependencies = [state_ml] in
  let driver = Printf.sprintf "state_driver_%d" exec in
  let fname = (join_paths tmp_dir driver) ^ ".ml" in
  let content = format exec dependencies props in
  write_to_file ~fname ~content;
  let results = Extractor.run tmp_dir dependencies driver in
  let props_results = String.concat " " results |> String.split_on_char ';' in
  (* cleanup tmp_dir driver; cleanup tmp_dir state_ml; *)
  List.filter_map process_prop_result props_results