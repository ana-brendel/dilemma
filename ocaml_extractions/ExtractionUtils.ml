open Serapi
open Sertop

let join_paths parent child = Printf.sprintf "%s/%s" parent child

let string_of_constr env sigma ctor = (Pp.string_of_ppcmds (Printer.pr_constr_env env sigma ctor))
let string_of_econstr env sigma ector = (Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma ector))

let break () = if true then raise (Failure "BREAK")

let my_parmap f lst = Parmap.parmap ?keeporder:(Some true) ?init:None ?finalize:None ?ncores:(Some 10) ?chunksize:None f (L lst)
let my_parmapi f lst = Parmap.parmapi ?keeporder:(Some true) ?init:None ?finalize:None ?ncores:(Some 10) ?chunksize:None f (L lst)

let contains str substr = let re = Str.regexp_string substr in try ignore (Str.search_forward re str 0); true with Not_found -> false
let remove_file fname : unit = if Sys.file_exists fname then (Sys.remove fname) else ()

let read_file filename =
  let lines = ref [] in
  try
    let chan = open_in filename in
    try
      while true; do lines := input_line chan :: !lines done; !lines
    with End_of_file -> close_in chan; !lines
  with _ -> !lines

let run_cmd command = 
  let channel = Unix.open_process_in command in
  let result = ref ([] : string list) in
  let rec process_aux () = let tmp = input_line channel in result := tmp :: !result; process_aux() in 
  try process_aux () with End_of_file -> let _ = close_in channel in List.rev !result

let write_to_file ~fname ~content = 
  remove_file fname; let oc = open_out_gen [Open_wronly; Open_creat; Open_trunc; Open_text] 0o777 fname
  in Printf.fprintf oc "%s" content; close_out oc

let remove_duplicate (compare : 'a -> 'a -> bool)  (lst : 'a list) : 'a list = 
  let rec iter accum = function
  | [] -> accum
  | h :: t -> if (List.exists (compare h) accum) then iter accum t else iter (accum @ [h]) t
  in iter [] lst

let cleanup (cwd : string) (name : string) : unit =
  let files = Sys.readdir cwd |> Array.to_list in
  let filter f = contains f name in
  let to_remove = List.filter filter files in
  List.iter remove_file (List.map (fun f -> cwd ^ "/" ^ f) to_remove)

let handle_context (ctxt : Constr.rel_declaration) = 
  let parse =  function
  | Context.Rel.Declaration.LocalAssum(x, y) -> (Context.(x.binder_name), y)
  | Context.Rel.Declaration.LocalDef(x, _, y) -> (Context.(x.binder_name), y) in
  parse ctxt |> snd

let rec cartesian (l : 'a list list) : 'a list list = 
  match l with
  | [] -> []
  | x :: [] -> List.map (fun e -> [e]) x
  | l1 :: l' -> let r = cartesian l' in List.map (fun e -> List.map (fun p -> e :: p) r) l1 |> List.flatten

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

let unique_partition (compare : 'a -> 'a -> bool) (index : int) (lst : 'a list) : 'a list =
  if (List.length lst <= index) then remove_duplicate compare lst 
  else
    let rec partition i acc = function
    | [] -> acc
    | h :: t -> if (i <= 0) then acc else (if (List.exists (compare h) acc) then (partition i acc t) else h :: (partition (i - 1) (h :: acc) t)) in
    partition index [] lst

let hashtbl_safe_add (tbl : ('a,'b list) Hashtbl.t) (key : 'a) (value : 'b list) =
  match Hashtbl.find_opt tbl key with
  | None -> if List.is_empty value then () else Hashtbl.add tbl key value
  | Some lst -> Hashtbl.replace tbl key (lst @ value)

let reduce_econstr env sigma =
  let reduction, _ = Redexpr.reduction_of_red_expr env @@ Cbn
    { rBeta = true; rMatch = true; rFix = true; rCofix = true; rZeta = true; rDelta = true; rConst = []; rStrength = Genredexpr.Norm } in
  fun term -> try EConstr.Unsafe.to_constr (snd (reduction env sigma term)) with _ -> EConstr.to_constr sigma term

let reduce_constr env sigma = Base.Fn.compose (reduce_econstr env sigma) EConstr.of_constr

let exec (cmd : Serapi_protocol.cmd) =
  let state = Serapi_protocol.State.make () in
  match Serapi_protocol.exec_cmd state cmd |> fst with
  | ObjList [obj] :: _ -> obj
  | res -> 
    let query = Sertop_ser.sexp_of_cmd cmd |> Sexplib0.Sexp.to_string in
    let ret = List.map (fun r -> Sertop_ser.sexp_of_answer_kind r |> Sexplib0.Sexp.to_string) res |> String.concat "; " in
    raise (Failure ("COMMAND: " ^ query ^ " - RESULT: " ^ ret))

let interp_string env sigma (str : string) (typ : Constr.t) : Constr.t =
  let type_str = string_of_constr env sigma typ in
  match exec (Parse ({ontop = None; entry=Vernac }, Printf.sprintf "Check (%s : %s)." str type_str)) with
  | CoqAst {v = { expr = VernacSynPure (VernacCheckMayEval (a, b, constr_expr)); control; attrs }; loc = _} ->
    let econstr,_ = Constrintern.interp_constr env sigma constr_expr in reduce_econstr env sigma econstr
  | _ -> raise (Failure "Not able to parse string into Constr.t (in CoqExecution.interp_string)")

let split_into_k (k : int) (lst : 'a list) : 'a list list =
  let div = (List.length lst) / k in
  let size = if div * k = List.length lst then div else div + 1 in
  let rec part acc = function
  | [] -> acc, []
  | h :: t when List.length acc == size -> acc, h :: t
  | h :: t -> part (acc @ [h]) t in
  let rec iter acc = function
  | [] -> acc
  | x -> let m,n = part [] x in iter (acc @ [m]) n in
  iter [] lst

let split_on_string delim str = let re = Str.regexp_string delim in Str.split re str

let str_of_constr_full_via_str env sigma expr =
  let get_full_path (func : bool) (env : Environ.env) (sigma : Evd.evar_map) (expr : Constr.t) : string = 
    let modpath, label = 
    try let (name,_) = Constr.destConst expr in Names.Constant.modpath name, Names.Constant.label name
    with _ -> try let ((ind,_),_) = Constr.destInd expr in Names.MutInd.modpath ind, Names.MutInd.label ind   
    with _ -> try let (((construct,_),_),_) = Constr.destConstruct expr in Names.MutInd.modpath construct, Names.MutInd.label construct
    with _ -> raise (Failure ("Fail to get full function path (triggered in Utils.get_func_str_with_mod) : " ^ string_of_constr env sigma expr)) in
    if (Names.ModPath.equal modpath  (Names.ModPath.MPfile (Lib.library_dp ()))) then (Names.Label.to_string label) else
    Printf.sprintf "%s%s.%s" (if func then "@" else "") (Names.ModPath.to_string modpath) (Names.Label.to_string label) in
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
  | Evar p -> raise (Failure "Constr kind EVAR not handled in ExtractionUtils.str_of_constr_full_via_str")
  (* | Fix fp -> raise (Failure "Constr kind FIX not handled in ExtractionUtils.str_of_constr_full_via_strw") *)
  | CoFix cfp -> raise (Failure "Constr kind COFIX not handled in ExtractionUtils.str_of_constr_full_via_str")
  | _ -> [] in
  let get_full e = get_full_path false env sigma e, str_lconstr e in
  let fulls = Hashtbl.create 0 in
  find_full expr |> List.map get_full |> remove_duplicate (fun (_,s1) (_,s2) -> String.equal s1 s2) |> List.iter (fun (fill,hole) -> Hashtbl.add fulls hole fill; Hashtbl.add fulls ("(" ^ hole) ("(" ^fill); Hashtbl.add fulls (")" ^ hole) (")" ^ fill));
  List.map (fun str -> match Hashtbl.find_opt fulls str with | Some swap -> swap | _ -> str) (str_lconstr expr |> Str.global_replace (Str.regexp "\n") " " |> String.split_on_char ' ') |> String.concat " "

let rec typed_vars_in_constr env (constr : Constr.t) : (Names.Id.t * Constr.t) list =
  let call = typed_vars_in_constr env in
  match Constr.kind constr with
  | Var id -> [(id,(Typeops.infer env constr).uj_type)]
  | App (func, args) -> List.map call (func :: (Array.to_list args)) |> List.flatten
  | Prod (var,typ,result) -> List.map call ([typ; result]) |> List.flatten
  | Lambda (var,typ,body) -> List.map call ([typ; body]) |> List.flatten
  | LetIn (ids,inp,assignment,expr) -> List.map call ([inp; assignment; expr]) |> List.flatten
  | Case (_,_,arr,((_,ctor1),_),invert,ctor2,bran) -> List.map call (ctor1 :: ctor2 :: (Array.to_list arr) @ List.map snd (Array.to_list bran)) |> List.flatten
  | Evar p -> raise (Failure "Constr kind EVAR not handled in Masks.vars_in_constr")
  | Cast (constr,kind,typ) -> raise (Failure "Constr kind CAST not handled in Masks.vars_in_constr")
  | Fix (_,(_,arr1,arr2)) -> List.map call ((Array.to_list arr1) @ (Array.to_list arr2)) |> List.flatten
  | CoFix cfp -> raise (Failure "Constr kind COFIX not handled in Masks.vars_in_constr")
  | Proj (proj,_,constr) -> raise (Failure "Constr kind PROJ not handled in Masks.vars_in_constr")
  | Array (univ,arr,constr,typ) -> raise (Failure "Constr kind ARRAY not handled in Masks.vars_in_constr")
  | _ -> []

let rec vars_in_constr (constr : Constr.t) : Names.Id.t list =
  let call = vars_in_constr in
  match Constr.kind constr with
  | Var id -> [id]
  | App (func, args) -> List.map call (func :: (Array.to_list args)) |> List.flatten
  | Prod (var,typ,result) -> List.map call ([typ; result]) |> List.flatten
  | Lambda (var,typ,body) -> List.map call ([typ; body]) |> List.flatten
  | LetIn (ids,inp,assignment,expr) -> List.map call ([inp; assignment; expr]) |> List.flatten
  | Case (_,_,arr,((_,ctor1),_),invert,ctor2,bran) -> List.map call (ctor1 :: ctor2 :: (Array.to_list arr) @ List.map snd (Array.to_list bran)) |> List.flatten
  | Evar p -> raise (Failure "Constr kind EVAR not handled in Masks.vars_in_constr")
  | Cast (constr,kind,typ) -> raise (Failure "Constr kind CAST not handled in Masks.vars_in_constr")
  | Fix (_,(_,arr1,arr2)) -> List.map call ((Array.to_list arr1) @ (Array.to_list arr2)) |> List.flatten
  | CoFix cfp -> raise (Failure "Constr kind COFIX not handled in Masks.vars_in_constr")
  | Proj (proj,_,constr) -> raise (Failure "Constr kind PROJ not handled in Masks.vars_in_constr")
  | Array (univ,arr,constr,typ) -> raise (Failure "Constr kind ARRAY not handled in Masks.vars_in_constr")
  | _ -> []

let implication_constr (pre : Constr.t) (post : Constr.t) : Constr.t = Constr.mkProd (Context.anonR, pre, post)

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

let remove_first_char str = if (String.length str <= 1) then "" else String.sub str 1 (String.length str)
let remove_last_char str = if (String.length str <= 1) then "" else String.sub str 0 (String.length str - 1)

let rec cut_at_line_containing substr lines =
  match lines with
  | line :: rest when (contains line substr |> not) -> cut_at_line_containing substr rest
  | _ -> lines