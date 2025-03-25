open ExtractionUtils

let imports = ["From QuickChick Require Import QuickChick."; "Set Warnings \"-extraction-opaque-accessed,-extraction\"."; "From Coq Require Export Lists.List.";"Export ListNotations."]
let extrtact_imports = ["From Coq Require Extraction.";"Extraction Language OCaml."]

let make_extraction extraction_file terms = Printf.sprintf "Extraction \"%s.ml\" %s." extraction_file (String.concat " " terms)

let add_extra extras tmp_dir ml_filename =
  match extras with | None -> ()
  | Some (after,(extra_ml,extra_mli)) -> 
    let full = join_paths tmp_dir ml_filename in
    let ml_path, mli_path = full ^ ".ml", full ^ ".mli" in
    let ml_content, mli_content = String.concat "\n" (read_file ml_path |> List.rev), String.concat "\n" (read_file mli_path |> List.rev) in
    let combine a b = if after then a ^ "\n\n" ^ b else b ^ "\n\n" ^ a  in
    write_to_file ~fname:ml_path ~content:(combine ml_content extra_ml); write_to_file ~fname:mli_path ~content:(combine mli_content extra_mli)

let build tmp_dir ml_file =
  let build_ocaml = run_cmd (Printf.sprintf "cd %s && ocamlc -o %s %s.mli %s.ml" tmp_dir ml_file ml_file ml_file) in
  if List.is_empty build_ocaml |> not then raise (Failure "Error building OCaml extraction in Extractor.extract")
  else ml_file

let extract buildb extras tmp_dir file_formatted ml_file coq terms =
  let coq_file = Printf.sprintf "coq_%s" ml_file in
  let extraction = make_extraction ml_file terms in
  let coq_content = String.concat "\n" (imports @ extrtact_imports @ file_formatted @ [coq;"";extraction]) in 
  let coq_extraction = Printf.sprintf "%s/%s.v" tmp_dir coq_file in
  write_to_file ~fname:coq_extraction ~content:coq_content;
  let run_extraction = run_cmd (Printf.sprintf "cd %s && coqc %s.v" tmp_dir coq_file) in
  if List.is_empty run_extraction |> not then raise (Failure "Error extracting Coq to OCaml in ocaml_extractions.Extractor.extract")
  else if (Option.has_some extras) then (add_extra extras tmp_dir ml_file);
  (* cleanup tmp_dir coq_file;  *)
  if (not buildb) then ml_file else (build tmp_dir ml_file)

let run tmp_dir dependencies src = (* requires that a tmp_dir/src.ml file exists *)
  let exec = Printf.sprintf "executable_%s" src in
  let formatted_dependencies = String.concat " " (List.map (fun d -> Printf.sprintf "%s.ml" d) dependencies) in 
  let build_cmd = Printf.sprintf "cd %s && ocamlfind ocamlopt -o %s -linkpkg -package parmap %s %s.ml" tmp_dir exec formatted_dependencies src in
  let build_ocaml = run_cmd build_cmd in
  if List.is_empty build_ocaml |> not then raise (Failure "Error building OCaml extraction in Extractor.run")
  else let output = run_cmd (Printf.sprintf "cd %s && ./%s" tmp_dir exec) in
  if List.is_empty output then raise (Failure "Error running OCaml executable in Extractor.run") 
  else output