let run_cmd command = 
  let channel = Unix.open_process_in command in
  let result = ref ([] : string list) in
  let rec process_aux () = let tmp = input_line channel in result := tmp :: !result; process_aux() in 
  try process_aux () with End_of_file -> let _ = close_in channel in List.rev !result

let clear_dir dir = 
  (if (try Sys.is_directory dir with _ -> false) then let _ = run_cmd (Printf.sprintf "rm -r %s" dir) in ());
  let _ = run_cmd (Printf.sprintf "mkdir %s" dir) in ()

let remove_file fname : unit = if Sys.file_exists fname then (Sys.remove fname) else ()

let write_to_file fname content = 
  remove_file fname; let oc = open_out_gen [Open_wronly; Open_creat; Open_trunc; Open_text] 0o777 fname
  in Printf.fprintf oc "%s" content; close_out oc

let read_file filename =
  let lines = ref [] in
  try
    let chan = open_in filename in
    try
      while true; do lines := input_line chan :: !lines done; !lines
    with End_of_file -> close_in chan; !lines
  with _ -> !lines

let remove_char c s = String.concat "" (String.split_on_char c s)
let remove_first c s = String.concat (String.of_seq (List.to_seq [c])) (String.split_on_char c s)

let remove_prefix prefix s = if (String.starts_with ~prefix s) then (Str.replace_first (Str.regexp prefix) "" s) else s

let remove_duplicate (compare : 'a -> 'a -> bool)  (lst : 'a list) : 'a list = 
  let rec iter accum = function
  | [] -> accum
  | h :: t -> if (List.exists (compare h) accum) then iter accum t else iter (h :: accum) t
  in iter [] lst |> List.rev

let contains_duplicate (compare : 'a -> 'a -> bool)  (lst : 'a list) : bool = 
  let rec iter accum = function
  | [] -> false
  | h :: t -> if (List.exists (compare h) accum) then true else iter (accum @ [h]) t
  in iter [] lst

let contains str substr = let re = Str.regexp_string substr in try ignore (Str.search_forward re str 0); true with Not_found -> false

let split_on_string delim str = let re = Str.regexp_string delim in Str.split re str
let remove_last_char str = if (String.length str <= 1) then "" else String.sub str 0 (String.length str - 1)

let list_contains (eq : 'a -> 'a -> bool) (elem : 'a) : 'a list -> bool = List.exists (fun x -> eq elem x)

let constains_all (eq : 'a -> 'a -> bool) (elems : 'a list) (lst : 'a list) : bool = 
  List.fold_left (fun acc elem -> acc && list_contains eq elem lst) true elems

let str_of_constr env sigma expr = (Pp.string_of_ppcmds (Printer.pr_constr_env env sigma expr))
let str_of_econstr env sigma expr = (Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma expr))

let str_of_constr_full_via_str env sigma expr =
  let get_full_path (func : bool) (env : Environ.env) (sigma : Evd.evar_map) (expr : Constr.t) : string = 
    let modpath, label = 
    try let (name,_) = Constr.destConst expr in Names.Constant.modpath name, Names.Constant.label name
    with _ -> try let ((ind,_),_) = Constr.destInd expr in Names.MutInd.modpath ind, Names.MutInd.label ind   
    with _ -> try let (((construct,_),_),_) = Constr.destConstruct expr in Names.MutInd.modpath construct, Names.MutInd.label construct
    with _ -> raise (Failure ("Fail to get full function path (triggered in Utils.get_func_str_with_mod) : " ^ str_of_constr env sigma expr)) in
    if (Names.ModPath.equal modpath  (Names.ModPath.MPfile (Lib.library_dp ()))) then (Names.Label.to_string label) else
    Printf.sprintf "%s%s.%s" (if func then "@" else "") (Names.ModPath.to_string modpath) (Names.Label.to_string label) in
  (* let replace_token (str : string) (hole : string) (fill : string) : string =
    Str.global_replace (Str.regexp (hole ^ " ")) (fill ^ " ") str |>
    Str.global_replace (Str.regexp (" " ^ hole ^ ")")) (" " ^ fill ^ ")") in *)
  let str_lconstr e'= Pp.string_of_ppcmds (Printer.pr_lconstr_env env sigma e') in
  let rec find_full e : Constr.t list =
  match Constr.kind e with
  | Ind ((_,_),_)  | Const (_,_)  -> [e]
  | App (func, args) -> find_full func @ (Array.map find_full args |> Array.to_list |> List.flatten)
  | Prod (_,typ,body) | Lambda (_,typ,body) | Cast (typ,_,body) -> find_full typ @ find_full body
  | Proj (_,_,constr) -> find_full constr
  | LetIn (ids,inp,assignment,ex) -> find_full inp @ find_full assignment @ find_full ex
  | Array (univ,arr,constr,typ) -> find_full constr @ find_full typ @ (Array.map find_full arr |> Array.to_list |> List.flatten)
  | Case (info,a,arr,b,c,ctor,e) -> find_full ctor @ (Array.map find_full arr |> Array.to_list |> List.flatten)
  | Evar p -> raise (Failure "Constr kind EVAR not handled in Utils.str_of_constr_full_via_str")
  (* | Fix fp -> raise (Failure "Constr kind FIX not handled in Utils.str_of_constr_full_via_str") *)
  | CoFix cfp -> raise (Failure "Constr kind COFIX not handled in Utils.str_of_constr_full_via_str")
  | _ -> [] in
  let get_full e = get_full_path false env sigma e, str_lconstr e in
  let fulls = Hashtbl.create 0 in
  find_full expr |> List.map get_full |> remove_duplicate (fun (_,s1) (_,s2) -> String.equal s1 s2) |> List.iter (fun (fill,hole) -> Hashtbl.add fulls hole fill; Hashtbl.add fulls ("(" ^ hole) ("(" ^fill); Hashtbl.add fulls (")" ^ hole) (")" ^ fill));
  List.map (fun str -> match Hashtbl.find_opt fulls str with | Some swap -> swap | _ -> str) (str_lconstr expr |> Str.global_replace (Str.regexp "\n") " " |> String.split_on_char ' ') |> String.concat " "

(* let format_coqargs_ri (arg : Coqargs.require_injection) : string =
  let ie = match arg.export with | Some Export -> "Export " | Some Import -> "Require Import " | _ -> " " in
  let prefix = match arg.prefix with | Some pf -> "From " ^ pf ^ " " | _ -> "" in
  prefix ^ ie ^ arg.lib ^ "." *)

let rec partition_at (index : int) (lst : 'a list) : 'a list =
  match lst with
  | [] -> []
  | h :: t -> if (index <= 0) then [] else h :: (partition_at (index - 1) t)

let partition_at_split (index : int) (l : 'a list) : 'a list * 'a list =
  let rec helper i lst acc =
  match lst with
  | [] -> acc, []
  | h :: t -> if (i <= 0) then acc, lst else helper (i - 1) t (acc @ [h])
  in helper index l [] 

let my_parmap f lst = Parmap.parmap ?keeporder:(Some true) ?init:None ?finalize:None ?ncores:(Some 10) ?chunksize:None f (L lst)
let my_parmapi f lst = Parmap.parmapi ?keeporder:(Some true) ?init:None ?finalize:None ?ncores:(Some 10) ?chunksize:None f (L lst)

let intersection compare a b = 
  let ma,mi = if (List.length a < List.length b) then b,a else a,b in
  List.filter (fun a' -> list_contains compare a' ma) mi

let select_random (amount : int) (lst : 'a list) : 'a list =
  if (List.length lst <= amount) then lst
  else if (amount <= 0) then []
  else let indices = List.init (amount * 2) (fun _ -> Random.int (List.length lst - 1)) in
  List.map (List.nth lst) indices |> remove_duplicate (=) |> partition_at amount

let random_subset (amount : int) (lst : 'a list) : 'a list =
  if (List.length lst <= amount) then lst
  else if (amount <= 0) then []
  else let indices = List.init (amount * 4) (fun _ -> Random.int (List.length lst - 1)) |> remove_duplicate (=) in
  List.map (List.nth lst) (indices |> partition_at amount)

let random_split (amount : int) (lst : 'a list) : 'a list * 'a list =
  if (List.length lst <= amount) then lst, []
  else if (amount <= 0) then [], lst
  else let indices = List.init (amount * 4) (fun _ -> Random.int (List.length lst - 1)) |> remove_duplicate (=) in
  let chosen = indices |> partition_at amount in
  let left = List.init (List.length lst) (fun x -> x) |> List.filter (fun x -> List.mem x chosen |> not) in
  if (List.length (chosen @ left) != List.length lst) then raise (Failure ("Implementation error in Utils.random_split"));
  List.map (List.nth lst) chosen, List.map (List.nth lst) left

(* Cleans up any file containing the string "name" in its name *)
let cleanup (cwd : string) (name : string) : unit =
  let files = Sys.readdir cwd |> Array.to_list in
  let filter f = contains f name in
  let to_remove = List.filter filter files in
  List.iter remove_file (List.map (fun f -> cwd ^ "/" ^ f) to_remove)

let rec cartesian (l : 'a list list) : 'a list list = 
  match l with
  | [] -> []
  | x :: [] -> List.map (fun e -> [e]) x
  | l1 :: l' -> let r = cartesian l' in List.map (fun e -> List.map (fun p -> e :: p) r) l1 |> List.flatten

let conjoin_props (props : Constr.t list) : Constr.t option =
  let and_mutind = 
    Names.MutInd.make2 
    (Names.MPfile (Names.DirPath.make (List.map Names.Id.of_string ["Logic";"Init";"Coq"])))
    (Names.Label.make "and") in
  let and_constr = Constr.mkIndU (UVars.in_punivs (and_mutind,0)) in
  let rec aux = function
  | [] -> None
  | last :: [] -> Some last
  | curr :: remaining -> 
    match aux remaining with
    | None -> Some curr
    | Some clause -> Some (Constr.mkApp (and_constr,Array.of_list [curr; clause]))
  in aux props

let disjoin_props (props : Constr.t list) : Constr.t option =
  let and_mutind = 
    Names.MutInd.make2 
    (Names.MPfile (Names.DirPath.make (List.map Names.Id.of_string ["Logic";"Init";"Coq"])))
    (Names.Label.make "or") in
  let and_constr = Constr.mkIndU (UVars.in_punivs (and_mutind,0)) in
  let rec aux = function
  | [] -> None
  | last :: [] -> Some last
  | curr :: remaining -> 
    match aux remaining with
    | None -> Some curr
    | Some clause -> Some (Constr.mkApp (and_constr,Array.of_list [curr; clause]))
  in aux props

let negate_prop (ctor : Constr.t) : Constr.t = 
  let mp = (Names.ModPath.MPfile (List.map Names.Id.of_string ["Logic";"Init";"Coq"] |> Names.DirPath.make)) in
  let not_constr = Constr.mkConstU (Names.Constant.make2 mp (Names.Label.make "not"), UVars.Instance.empty) in
  (Constr.mkApp (not_constr, Array.of_list [ctor]))

let implication_constr (pre : Constr.t) (post : Constr.t) : Constr.t = Constr.mkProd (Context.anonR, pre, post)
 
let remove_coq_comments (contents : string list) : string = 
  let characters = List.rev contents |> List.map String.trim |> String.concat " " |> String.to_seq |> List.of_seq in
  let rec eater opens = function
  | [] -> []
  | [c] -> [c]
  | c1 :: c2 :: rest -> 
    match String.of_seq (List.to_seq [c1;c2]) with
    | "(*" -> eater (opens + 1) rest
    | "*)" -> eater (opens - 1) rest
    | _ -> if (opens = 0) then c1 :: eater opens (c2 :: rest) else eater opens (c2 :: rest) 
  in eater 0 characters |> List.to_seq |> String.of_seq

let rec log_base (base : int) (n : int) : int = if n < base then 1 else 1 + log_base base (n / base)

let break () = if true then raise (Failure "BREAK")

let handle_context (ctxt : Constr.rel_declaration) = 
  let parse =  function
  | Context.Rel.Declaration.LocalAssum(x, y) -> (Context.(x.binder_name), y)
  | Context.Rel.Declaration.LocalDef(x, _, y) -> (Context.(x.binder_name), y) in
  parse ctxt |> snd

let remove_from (compare : 't -> 't -> bool) (elem: 't) (lst : 't list) : 't list =
  List.fold_left (fun remaining curr -> if compare elem curr then remaining else remaining @ [curr]) [] lst

let power_set (lst : 'a list) : 'a list list = List.fold_left (fun sets elem -> sets @ (List.map (fun s -> elem :: s) sets)) [[]] lst

let k_sized_partitions (size : int) (lst : 'a list) : 'a list list =
  let rec part acc = function
  | [] -> acc, []
  | h :: t when List.length acc == size -> acc, h :: t
  | h :: t -> part (acc @ [h]) t in
  let rec iter acc = function
  | [] -> acc
  | x -> let m,n = part [] x in iter (acc @ [m]) n in
  iter [] lst

let construct_equal env typ p q = 
  let modpath = Names.ModPath.MPfile (List.map Names.Id.of_string ["Logic";"Init";"Coq"] |> Names.DirPath.make) in
  let eq_prop = (Typeops.infer env (Constr.mkIndU (UVars.in_punivs ((Names.MutInd.make2 modpath (Names.Label.make "eq")), 0)))).uj_val in
  Constr.mkApp (eq_prop, Array.of_list [typ;p;q])

let rec contains_rel ctor = 
  match Constr.kind ctor with
  | Rel _ -> true
  | Proj (_,_,c) -> contains_rel c
  | App (c, cs) -> contains_rel c || Array.fold_left (fun acc c' -> acc || contains_rel c') false cs
  | Prod (_,c1,c2) | Lambda (_,c1,c2) | Cast (c1,_,c2) -> contains_rel c1 || contains_rel c2
  | LetIn (_,c1,c2,c3) -> contains_rel c1 || contains_rel c2 || contains_rel c3
  | Array (_,cs,c1,c2) -> contains_rel c1 || contains_rel c2 || Array.fold_left (fun acc c' -> acc || contains_rel c') false cs
  | Case (info,a,b,arr,c,d,e) -> raise (Failure "Constr kind CASE not handled in SynthUtils.contains_rel")
  | Evar p -> raise (Failure "Constr kind EVAR not handled in SynthUtils.contains_rel")
  | Fix fp -> raise (Failure "Constr kind FIX not handled in SynthUtils.contains_rel")
  | CoFix cfp -> raise (Failure "Constr kind COFIX not handled in SynthUtils.contains_rel")
  | _ -> false

let reduce_econstr env sigma =
  let reduction, _ = Redexpr.reduction_of_red_expr env @@ Cbn
    { rBeta = true; rMatch = true; rFix = true; rCofix = true; rZeta = true; rDelta = true; rConst = []; rStrength = Genredexpr.Norm } in
  fun term -> try EConstr.Unsafe.to_constr (snd (reduction env sigma term)) with _ -> EConstr.to_constr sigma term

let reduce_constr env sigma = Base.Fn.compose (reduce_econstr env sigma) EConstr.of_constr

let get_nat env = let library = Names.ModPath.MPfile (List.map Names.Id.of_string ["Datatypes";"Init";"Coq"] |> Names.DirPath.make) in
  let nat_type = Typeops.infer env (Constr.mkIndU (UVars.in_punivs (Names.MutInd.make2 library (Names.Label.make "nat"), 0))) in
  nat_type.uj_val

let constr_type env sigma (ctor : Constr.t) : Constr.t = 
  try (Typeops.infer env ctor).uj_type with e -> print_endline ("[Utils.constr_type] ERROR ON: " ^ str_of_constr env sigma ctor); raise (e)


let rec constr_nodes ctor : int =
  match Constr.kind ctor with
  | App (func, args) -> Array.fold_left (fun sum a -> sum + constr_nodes a) (constr_nodes func) args
  | Prod (_,a,b) | Lambda (_,a,b) | Cast (a,_,b) -> constr_nodes a + constr_nodes b
  | LetIn (_,inp,a,expr) -> constr_nodes inp + constr_nodes a + constr_nodes expr
  | Case (_,_,arr,((_,a),_),_,b,ayy) -> Array.fold_left (fun sum (_,a) -> sum + constr_nodes a) (Array.fold_left (fun sum a -> sum + constr_nodes a) (constr_nodes a + constr_nodes b) arr) ayy
  | Evar (_,lst) -> SList.Skip.fold (fun sum a -> sum + constr_nodes a) 0 lst
  | Fix ((_,_),(_,b,c)) | CoFix (_,(_,b,c)) -> Array.fold_left (fun sum a -> sum + constr_nodes a) 0 (Array.append b c)
  | Proj (_,_,constr) -> constr_nodes constr
  | Array (_,arr,a,b) -> Array.fold_left (fun sum a -> sum + constr_nodes a) (constr_nodes a + constr_nodes b) arr
  | _ -> 1

let rec constr_height ctor : int =
  let max_lst d l : int = List.fold_left (fun acc elem -> if acc < elem then elem else acc) d l in
  let max_arr d l : int = Array.fold_left (fun acc elem -> if acc < elem then elem else acc) d l in
  match Constr.kind ctor with
  | App (func, args) -> constr_height func + max_arr 0 (Array.map constr_height args)
  | Prod (_,a,b) | Lambda (_,a,b) | Cast (a,_,b) -> 1 + max_lst 0 [constr_height a; constr_height b]
  | LetIn (_,inp,a,expr) -> 1 + max_lst 0 [constr_height inp; constr_height a; constr_height expr]
  | Case (_,_,arr,((_,a),_),_,b,ayy) -> constr_nodes ctor
  | Evar (_,lst) -> 1 + (SList.Skip.fold (fun acc elem -> elem :: acc) [] lst |> List.map constr_height |> max_lst 0)
  | Fix ((_,_),(_,b,c)) | CoFix (_,(_,b,c)) -> 1 + max_arr 0 (Array.map constr_height (Array.append b c))
  | Proj (_,_,constr) -> constr_height constr
  | Array (_,arr,a,b) -> 1 + max_lst 0 [constr_height a; constr_height b; max_arr 0 (Array.map constr_height arr)]
  | _ -> 1

let constr_compare str c1 c2 : int =
  let n1, n2 = constr_nodes c1, constr_nodes c2 in
  if n1 != n2 then n1 - n2 
  else let h1, h2 = constr_height c1, constr_height c2 in
  if h1 != h2 then h1 - h2 else Int.compare (String.length (str c1)) (String.length (str c2)) 

let rec constr_contains (hole : Constr.t) (constr : Constr.t) : bool =
  let contains = constr_contains hole in
  if Constr.equal hole constr then true 
  else match Constr.kind constr with
  | App (func, args) -> contains func || List.exists contains (Array.to_list args)
  | Prod (var,typ,result) -> contains typ || contains result
  | Lambda (var,typ,body) -> contains typ || contains body
  | LetIn (ids,inp,assignment,expr) -> contains inp || contains assignment || contains expr
  | Proj (proj,s,ctor) -> contains ctor
  | Cast (ctor,kind,typ) -> contains ctor || contains typ
  | Array (univ,arr,ctor,typ) -> contains ctor || contains typ || List.exists contains (Array.to_list arr)
  | Evar p -> raise (Failure "Constr kind EVAR not handled in Generalize.constr_contains")
  | CoFix cfp -> raise (Failure "Constr kind COFIX not handled in Generalize.constr_contains")
  | _ -> false

let rec replace_subterm (hole : Constr.t) (fill : Constr.t) (constr : Constr.t) : Constr.t =
  let replace = replace_subterm hole fill in
  if Constr.equal hole constr then fill 
  else match Constr.kind constr with
  | App (func, args) -> Constr.mkApp (replace func,Array.map replace args)
  | Prod (var,typ,result) -> Constr.mkProd (var,replace typ,replace result)
  | Lambda (var,typ,body) -> Constr.mkLambda (var,replace typ,replace body)
  | LetIn (ids,inp,assignment,expr) -> Constr.mkLetIn (ids,replace inp,replace assignment,replace expr)
  | Proj (proj,s,ctor) -> Constr.mkProj (proj,s,replace ctor)
  | Cast (ctor,kind,typ) -> Constr.mkCast (replace ctor,kind,replace typ)
  | Array (univ,arr,ctor,typ) -> Constr.mkArray (univ,Array.map replace arr,replace ctor,replace typ)
  | Evar p -> raise (Failure "Constr kind EVAR not handled in Generalize.replace_subterm")
  | CoFix cfp -> raise (Failure "Constr kind COFIX not handled in Generalize.replace_subterm")
  | _ -> constr