
type variable = { id : Names.Id.t; typ : Constr.t }
let variable_eq v1 v2 = Names.Id.equal v1.id v2.id && Constr.equal v1.typ v2.typ
let str_of_variable_w_type (env : Environ.env) (sigma : Evd.evar_map) (v : variable) : string = "(" ^ Names.Id.to_string v.id ^ " : " ^ Utils.str_of_constr env sigma v.typ ^ ")"

type expr = { body : Constr.t; typ : Constr.t; variables : variable list }
let expr_eq e1 e2 = Constr.equal e1.body e2.body && Constr.equal e1.typ e2.typ 
  && List.fold_left2 (fun acc v1 v2 -> acc && variable_eq v1 v2) true e1.variables e2.variables

type candidate = { term : expr; depth : int }
let candidate_eq c1 c2 = expr_eq c1.term c2.term
let candidate_str env sigma can = Utils.str_of_constr env sigma can.term.body ^ " - depth: " ^ string_of_int can.depth

let format_expr env sigma expr = 
  let str_constr = Utils.str_of_constr env sigma in
  match expr.variables with
  | [] -> str_constr expr.body 
  | _ -> Printf.sprintf "forall %s, %s" (String.concat " " (List.map (str_of_variable_w_type env sigma) expr.variables)) (str_constr expr.body)

type func = { label : Constr.t; typ : Constr.t }
let func_eq f1 f2 = Constr.equal f1.label f2.label && Constr.equal f1.typ f2.typ
let func_str env sigma func : string = 
  let str = Utils.str_of_constr env sigma in 
  Printf.sprintf "%s : %s" (str func.label) (str func.typ)

type example = { label : int }

(* type example = { label : int; values : (Names.Id.t * Constr.t) list; generalized_matches : bool }
let example_eq e1 e2 : bool = 
  let h1, h2 = Hashtbl.of_seq (List.to_seq e1.values), Hashtbl.of_seq (List.to_seq e2.values) in
  Hashtbl.fold (fun v e acc -> match Hashtbl.find_opt h1 v with | Some e' -> acc && Constr.equal e e' | _ -> false) h2 true &&
  Hashtbl.fold (fun v e acc -> match Hashtbl.find_opt h2 v with | Some e' -> acc && Constr.equal e e' | _ -> false) h1 true *)

(* type updated_example = { exec : int; label : int }
let updated_example_eq e1 e2 : bool = (e1.exec = e2.exec) && (e1.label = e2.label) *)

(* let example_str env sigma (e : example) : string =
  let label =  ("Example Number: " ^ string_of_int e.label) in
  let vals = List.map (fun (v,e) -> (Names.Id.to_string v ^ " = " ^ Utils.str_of_constr env sigma e)) e.values in
  String.concat "\n" (label::vals) *)

let rec vars_in_constr env (constr : Constr.t) : variable list =
  let call = vars_in_constr env in
  match Constr.kind constr with
  | Var id -> [{id; typ = (Typeops.infer env constr).uj_type }]
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

let is_prop env (constr : Constr.t) : bool = try (Typeops.infer env constr).uj_type |> Constr.is_Prop with _ -> false

let expr_from_constr env sigma (body : Constr.t) : expr = 
  let typ = try (Typeops.infer env body).uj_type with e -> print_endline ("[Masks.expr_from_constr] ERROR ON: " ^ Utils.str_of_constr env sigma body); raise (e) in
  let variables = vars_in_constr env body |> Utils.remove_duplicate variable_eq in
  { body; typ; variables }

let is_quantified_via_str env sigma (expr : expr) = 
  let check str (expr : expr) = Utils.contains (Utils.str_of_constr env sigma expr.body) str in
  check "forall " expr || check "exists " expr

type prop_kind = Assumption | Goal | ProofState | Candidate | ComboHolder | GenEquality of Names.Id.t
type prop = { expr : expr; true_on : example list; false_on : example list; kind : prop_kind }

(* type updated_prop_kind = Assumption | Goal | GenEquality
type updated_prop = { expr : expr; true_on : updated_example list; false_on : updated_example list; kind : updated_prop_kind } *)

let display_prop env sigma p : unit =
  let str = Utils.str_of_constr env sigma in 
  print_endline ("Expr: " ^ str p.expr.body);
  print_endline ("True on: " ^ (List.length p.true_on |> string_of_int));
  print_endline ("False on: " ^ (List.length p.false_on |> string_of_int));