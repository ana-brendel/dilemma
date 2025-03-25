open Masks

let query_library (cwd : string) (src : string list) (lib : Names.ModPath.t) : Names.ModPath.t * string list =
  let path = cwd ^ "/library_query.v" in
  let content' = src @ [""; Printf.sprintf "Print %s." (Names.ModPath.to_string lib)] in
  let content = content' |> String.concat "\n" in
  Utils.write_to_file path content;
  let cmd = Printf.sprintf "cd %s && coqc library_query.v" cwd in
  let results = Utils.run_cmd cmd in 
  Utils.cleanup cwd "library_query"; lib, results

let parse_src_lines (results : string list) : string list =
  let results'' = List.map String.trim results |> String.concat " " |> Utils.split_on_string ":= Struct" in
  let results' = match results'' |> List.tl with  | [] -> List.hd results'' | x -> x |> String.concat " " in
  let clean =  String.split_on_char '.' results' |> List.map String.trim in
  let filter l = List.fold_left (fun acc f -> acc || String.starts_with ~prefix:f l) false ["Definition"; "Inductive"; "Fixpoint"] in
  List.filter filter clean 

let type_by_func_name env (lib : Names.ModPath.t option) (names : string list) : (string * Constr.t * Constr.t) list = 
  let with_lib library funcs = 
    let format_ind l = Typeops.infer env (Constr.mkIndU (UVars.in_punivs ((Names.MutInd.make2 library (Names.Label.make l)), 0))) :: [] in
    let format_const l = Typeops.infer env (Constr.mkConstU (UVars.in_punivs (Names.Constant.make2 library (Names.Label.make l)))) :: [] in
    let format_construct_i l i = Typeops.infer env (Constr.mkConstructU (UVars.in_punivs (((Names.MutInd.make2 library (Names.Label.make l)), 0),i))) in
    let format_construct l = List.filter_map (fun i -> try Some (format_construct_i l i) with _ -> None) [0;1;2;3;4] in
    let format l = try format_const l with _ -> try format_ind l with _ -> try format_construct l with _ -> raise (Failure ("Cannot find the type (in GatherFunctions.type_by_func_name) of " ^ l)) in
    let initial = List.map (fun str -> let uj = format str in List.map (fun (uj' : Environ.unsafe_judgment) -> (str, uj'.uj_val, uj'.uj_type)) uj) (List.map String.trim funcs) in
    let sets = (List.filter_map (fun (s,_,t) -> if Constr.is_Set t then Some s else None) (List.flatten initial)) in
    initial @ (List.map (fun str -> List.map (fun (uj' : Environ.unsafe_judgment) -> (str, uj'.uj_val, uj'.uj_type)) (format_construct str)) sets) in
  match lib with | Some l -> with_lib l names |> List.flatten | _ -> []

let definitions env (key : string) : (func list) option =
  let make_mp path = Names.ModPath.MPfile (List.map Names.Id.of_string path |> Names.DirPath.make) in
  let get_func mp = 
    type_by_func_name env (Some mp) (CoqCoreFunctions.to_include mp) |> List.map (fun (_,label,typ) -> {label; typ}) in
  match key with 
  | "Coq.Init.Logic" -> Some (get_func (make_mp ["Logic";"Init";"Coq"]))
  | "Coq.Init.Datatypes" -> Some (get_func (make_mp ["Datatypes";"Init";"Coq"]))
  | "Coq.Lists.List" -> Some (get_func (make_mp ["List";"Lists";"Coq"]))
  | "Coq.Sorting.Permutation" -> Some (get_func (make_mp ["Permutation";"Sorting";"Coq"]))
  | "Coq.Init.Peano" -> Some (get_func (make_mp ["Peano";"Init";"Coq"]))
  | _ -> None

let definitions_via_src env library (src : string list) : Masks.func list =
  let filtered = parse_src_lines src in
  let names = List.filter_map (fun l -> try Some (String.trim l |> String.split_on_char ' ' |> List.tl |> List.hd) with _ -> None) filtered in
  let remove_semi word = String.split_on_char ':' word |> List.hd in
  let results = type_by_func_name env library (List.map remove_semi names) in 
  let get_func (_,label,typ) : Masks.func option = try Some {label; typ} with _ -> None in
  List.filter_map get_func results

let filter_function_by_name env sigma (f : func) : bool =
  let name = Utils.str_of_constr env sigma f.label in
  let typ = Utils.str_of_constr env sigma f.typ in
  let ends_with s = String.ends_with ~suffix:s in
  let starts_with s = String.starts_with ~prefix:s in
  let filter_by_name n = ends_with "_ind" n || ends_with "_sind" n || ends_with "_dec" n || ends_with "_ok" n 
    || ends_with "_error" n || ends_with "_default" n || starts_with "Show" n || starts_with "GenSized" n 
    || starts_with "Shrink" n || starts_with "@Shrink" n || starts_with "@Show" n || starts_with "@show" n  
    || starts_with "@GenSized" n || Utils.contains n "_ind2_" in
  (filter_by_name name || Utils.contains typ "Decidability.Dec_Eq") |> not

let run env sigma (cwd : string) (mods : Names.ModPath.t list) (src : string list) : Masks.func list =
  let common_libraries = ["Coq.Init.Logic";"Coq.Init.Datatypes";"Coq.Init.Peano"] in
  let common = List.filter_map (definitions env) common_libraries |> List.flatten in
  let local = definitions_via_src env (Some (Lib.current_mp ())) src in
  let coq_core = List.filter_map (definitions env) (List.map Names.ModPath.to_string mods) |> List.flatten in
  let others = List.filter (fun m -> match definitions env (Names.ModPath.to_string m) with | None -> true | _ -> false) mods in
  let others_src = List.map (query_library cwd src) others in
  let other_func = List.concat_map (fun (mod',src') -> definitions_via_src env (Some mod') src') others_src in
  common @ coq_core @ local @ other_func |> List.filter (filter_function_by_name env sigma)