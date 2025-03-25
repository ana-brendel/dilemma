open Utils

type state = STABLE | UNSTABLE 

type t = {
  label : int;
  goal : Masks.prop;
  state : state;
  assumptions : (Masks.variable,Masks.prop) Hashtbl.t;
  variables : Masks.variable list;
  generalized_terms : (Masks.variable,Masks.expr) Hashtbl.t option;
}


let t_of_context label (proof : Playground.proof) : t = 
  let goal : Masks.prop = { expr = proof.goal; true_on = []; false_on = []; kind = Goal } in
  let assumptions : (Masks.variable,Masks.prop) Hashtbl.t = Hashtbl.create (Hashtbl.length proof.assumptions) in
  Hashtbl.iter (fun v expr -> Hashtbl.add assumptions v { expr; true_on = []; false_on = []; kind = Assumption }) proof.assumptions;
  { label; goal; assumptions; variables = proof.variables; generalized_terms = proof.generalized_terms; state = UNSTABLE}

let get_example_format (info : Playground.info)  (t : t) =
  let typ = get_nat info.env in
  let str = Utils.str_of_constr info.env info.sigma in
  let sort_by_var = List.sort (fun v1 v2 -> Names.Id.compare (fst v1) (fst v2)) in
  let mono = List.map (fun (v : Masks.variable) -> if (Constr.isVar v.typ) then { v with typ } else v) t.variables in
  let filtered = List.filter (fun (v : Masks.variable) -> Constr.is_Set v.typ |> not) mono in
  let vars' = sort_by_var (List.map (fun (v : Masks.variable) -> v.id, v.typ) filtered) in
  let vars,types = List.split vars' in
  let str_types = Printf.sprintf "(%s)" (String.concat " * " (List.map (fun v -> str v) types)) in 
  let str_vars = Printf.sprintf "(%s)" (String.concat "," (List.map (fun v -> Names.Id.to_string v) vars)) in 
  (vars,str_vars), (types,str_types)

let display (info : Playground.info) (self : t) : unit =
  [
    ("Label: " ^ string_of_int self.label);
    ("Generalization Count: " ^ string_of_int (match self.generalized_terms with Some tbl -> Hashtbl.length tbl | _ -> 0));
    ("Generalization Destablizes: " ^ string_of_bool (List.exists (fun (v : Masks.variable) -> String.starts_with ~prefix:"GenVarEq_" (Names.Id.to_string v.id)) (Hashtbl.to_seq_keys self.assumptions |> List.of_seq)));
    ("Assumptions: " );
  ] @ 
  (Hashtbl.fold (fun _ (p : Masks.prop) acc -> acc @ [(" -- " ^ Utils.str_of_constr info.env info.sigma p.expr.body)]) self.assumptions [])
  @ [ 
    ("Goal: " ^ Utils.str_of_constr info.env info.sigma self.goal.expr.body);
    ("Example Format: " ^ (let v,t = get_example_format info self in ((snd v) ^ "; " ^ (snd t)))) 
  ] |> String.concat "\n" |> print_endline

let generalization_eq t1 t2 : bool = 
  Masks.expr_eq t1.goal.expr t2.goal.expr &&
  Hashtbl.fold (fun v (e : Masks.prop) acc -> match Hashtbl.find_opt t1.assumptions v with | Some e' -> acc && Masks.expr_eq e.expr e'.expr | _ -> false) t2.assumptions true &&
  Hashtbl.fold (fun v (e : Masks.prop) acc -> match Hashtbl.find_opt t2.assumptions v with | Some e' -> acc && Masks.expr_eq e.expr e'.expr | _ -> false) t1.assumptions true

let rec gather_subterms env sigma level constr : (Constr.t * int) list =
  let no_terms = [] in
  let level_up = gather_subterms env sigma (level + 1) in
  match Constr.kind constr with
  | Var _ | Sort _ | Meta _ | Rel _ | Int _ | Float _ | String _ | Const (_,_) -> no_terms
  | App (func, args) -> (constr, level) :: ((List.map level_up (args |> Array.to_list)) |> List.concat)
  | Prod (var,typ,result) -> (constr, level) :: (level_up typ @ level_up result)
  | Ind ((_,_),_) | Construct (_,_) | Case (_,_,_,_,_,_,_) -> [(constr, level)]
  | Lambda (var,typ,body) -> (*(constr, level) :: (level_up typ @ level_up body) -- for fun var : typ => body *) no_terms
  | LetIn (ids,inp,assignment,expr) -> (constr, level) :: (level_up inp @ level_up assignment @ level_up expr)
  | Proj (proj,_,body) -> (constr, level) :: level_up body
  | Cast (body,kind,typ) -> (constr, level) :: (level_up typ @ level_up body)
  | Array (univ,arr,body,typ) -> (constr, level) :: (((List.map level_up (arr |> Array.to_list)) |> List.concat) @ level_up body @ level_up typ)
  (* | Const (_,_) -> print_endline (str_of_constr env sigma constr); raise (Failure "Constr kind CONST not handled in Generalize.gather_subterms") *)
  (* | Case (info,a,b,arr,c,d,e) -> print_endline (str_of_constr env sigma constr); raise (Failure "Constr kind CASE not handled in Generalize.gather_subterms") *)
  | Evar p -> print_endline (str_of_constr env sigma constr); raise (Failure "Constr kind EVAR not handled in Generalize.gather_subterms")
  | Fix fp -> print_endline (str_of_constr env sigma constr); raise (Failure "Constr kind FIX not handled in Generalize.gather_subterms")
  | CoFix cfp -> print_endline (str_of_constr env sigma constr); raise (Failure "Constr kind COFIX not handled in Generalize.gather_subterms")

let constr_type_outside_assumptions (env : Environ.env) (sigma : Evd.evar_map) (constr : Constr.t) : bool =
  try let typ_constr = snd (Typing.type_of env sigma (EConstr.of_constr constr)) |> EConstr.to_constr sigma in
  match Constr.kind typ_constr with 
  | Sort s when Sorts.is_set s -> false 
  | Sort s when Sorts.is_prop s -> false 
  | _ -> true 
  with _ -> if (contains_rel constr) then false 
  else raise (Failure "[in Generalize.constr_type_outside_assumptions] Cannot get type of subterm")

let gather (info : Playground.info) (proof : Playground.proof) : (Masks.variable,Masks.expr) Hashtbl.t = 
  let min_level = 0 in (* 0 -> the highest level (anything that is a subterm below the whole expression) *)
  let env, sigma = info.env, info.sigma in
  let is_term = constr_type_outside_assumptions env sigma in
  let subterms'' = gather_subterms env sigma 0 proof.goal.body in
  let subterms' = List.filter (fun (c,i) -> i > min_level && is_term c ) subterms'' |> List.map fst |> remove_duplicate (Constr.equal) in
  (* prevents subterms from being prods (function types) *)
  let subterms = List.filter (fun s -> if Constr.isProd (constr_type env sigma s) then false else true) subterms' in
  let generalizations = Hashtbl.create (List.length subterms) in 
  let add i constr =
    let expr = Masks.expr_from_constr env sigma constr in
    let variable : Masks.variable = { id = Names.Id.of_string ("gv" ^ string_of_int i); typ = expr.typ } in
    Hashtbl.add generalizations variable expr in
  List.iteri add subterms; generalizations

let replace_subterm_ env sigma (v : Masks.variable) (term : Masks.expr) (expr : Masks.expr) : Masks.expr =
  let body', typ, variables' = expr.body, expr.typ, expr.variables in
  let fill, hole = Constr.mkVar v.id, term.body in
  let body = replace_subterm hole fill body' in
  Masks.expr_from_constr env sigma body

let replace_subterm_p env sigma (v : Masks.variable) (term : Masks.expr) (prop : Masks.prop) : Masks.prop =
  let body', variables' = prop.expr.body, prop.expr.variables in
  let fill, hole = Constr.mkVar v.id, term.body in
  let body = replace_subterm hole fill body' in
  { prop with expr = Masks.expr_from_constr env sigma body }

let substitute env sigma (proof : t) (v : Masks.variable) (term : Masks.expr) : t = 
  let variables', generalized_terms', assumptions' = proof.variables, proof.generalized_terms, proof.assumptions in
  match Utils.list_contains Masks.variable_eq v variables' with
  | true -> proof | _ -> let generalized_terms = Hashtbl.create 1 in
    let og_generalized_terms = match proof.generalized_terms with Some tbl -> Hashtbl.copy tbl | _ -> Hashtbl.create 0 in
    let update_gvs subterm = replace_subterm_ env sigma v term subterm in
    Hashtbl.iter (fun gv term -> Hashtbl.add generalized_terms gv (update_gvs term)) og_generalized_terms;
    Hashtbl.add generalized_terms v term;
    let goal = replace_subterm_p env sigma v term proof.goal in
    let assumptions = Hashtbl.create (Hashtbl.length assumptions') in
    Hashtbl.iter (fun v' e' -> Hashtbl.add assumptions v' (replace_subterm_p env sigma v term e')) assumptions';
    let gv_equality = construct_equal env v.typ term.body (Constr.mkVar v.id) |> Masks.expr_from_constr env sigma in
    let gv_equality_prop : Masks.prop = { expr = gv_equality; true_on = []; false_on = []; kind = GenEquality v.id } in
    Hashtbl.add assumptions { id = Names.Id.of_string (Printf.sprintf "GenVarEq_%s" (Names.Id.to_string v.id)); typ = Constr.mkProp} gv_equality_prop;
    let variables' = goal.expr.variables @ (Hashtbl.fold (fun _ (e : Masks.prop) acc -> e.expr.variables @ acc) assumptions []) |> remove_duplicate Masks.variable_eq in
    let variables = List.sort (fun (v1 : Masks.variable) (v2 : Masks.variable) -> Names.Id.compare v1.id v2.id) variables' in
  { label = proof.label; goal; assumptions; variables; generalized_terms = Some generalized_terms; state = UNSTABLE }

let check_validity (info : Playground.info) i (proof : t): t  =
  let initial = Hashtbl.to_seq_values proof.assumptions |> List.of_seq |> List.filter (fun (p : Masks.prop) -> match p.kind with | GenEquality _ -> false | _ -> true) in
  let assumptions = List.filter (fun (p : Masks.prop) -> Masks.is_quantified_via_str info.env info.sigma p.expr |> not) initial in
  let implication = List.fold_left (fun impl (pre : Masks.prop) -> implication_constr pre.expr.body impl) proof.goal.expr.body assumptions in
  let exprs = [(Masks.expr_from_constr info.env info.sigma implication)] in
  let label = Printf.sprintf "checking_validity_%d" i in
  let query : CoqInterface.query = { q = CoqInterface.Satisfiable exprs; label; info } in
  match CoqInterface.execute query with 
  | CoqInterface.Satisfiability r when (List.length r = 1) -> if snd (List.hd r) then {proof with state = STABLE} else {proof with state = UNSTABLE}
  | _ -> raise (Failure "[in Generalize.check_validity] Unexpected/incorrect result type.")

let runs_synthesis (self : t) : bool = match self.state, self.generalized_terms with STABLE, Some _ -> false | _ -> true
let generalization_count (self : t) : int = match self.generalized_terms with Some tbl -> Hashtbl.length tbl | _ -> 0

let keep_generalizations (gen : t) : bool =
  let eq_label mut = Names.Label.equal (Names.Label.make "eq") (Names.MutInd.label mut) in
  let is_var c = match Constr.kind c with Var _ -> true | _ -> false in
  let vars_option = match Constr.kind gen.goal.expr.body with
  | App (label,args) -> 
    (match Constr.kind label with
    | Ind ((mut,_),_) when (eq_label mut && Array.length args = 3) -> 
      if ((is_var (Array.get args 1)) && (is_var (Array.get args 2))) then Some ((Array.get args 1),(Array.get args 2)) else None
    | _ -> None)
  | _ -> None in
  match gen.generalized_terms, vars_option with
  | None, _ | _, None-> true (* keep the ungeneralized version *)
  | Some gvs, Some (a,b) -> let gv_ctors = Hashtbl.fold (fun (v : Masks.variable) _ acc -> (Constr.mkVar v.id) :: acc) gvs [] in
    not (List.exists (Constr.equal a) gv_ctors && List.exists (Constr.equal b) gv_ctors)

let create_one (info : Playground.info) original (generalized_variables : (Masks.variable, Masks.expr) Hashtbl.t) : t list =
  let subterm_in (s : Masks.expr) = constr_contains s.body original.goal.expr.body in
  let sub v e acc = if subterm_in e then (substitute info.env info.sigma original v e) :: acc else acc in
  List.filter keep_generalizations (Hashtbl.fold sub generalized_variables [])

let rec icreate cutoff (info : Playground.info) (generalized_variables : (Masks.variable * Masks.expr) list) proof : t list =
  let already_generalized = match proof.generalized_terms with Some gvs -> List.of_seq (Hashtbl.to_seq gvs) | _ -> [] in
  match proof.state with 
  | UNSTABLE when (not (List.is_empty already_generalized)) -> [proof]
  | STABLE when (cutoff <= List.length already_generalized) -> [proof]
  | STABLE | UNSTABLE -> if List.is_empty generalized_variables then [proof]
  else if cutoff <= List.length already_generalized then [proof]
  else let remaining_gens = List.filter (fun (v,_) -> List.exists (Masks.variable_eq v) (List.map fst already_generalized) |> not) generalized_variables in
  let update_gvs subterm = List.fold_left (fun acc (v,e) -> replace_subterm_ info.env info.sigma v e acc) subterm already_generalized in
  let updated_gvs = List.map (fun (v,e) -> v, update_gvs e) remaining_gens in
  let generalizations = create_one info proof (Hashtbl.of_seq (List.to_seq updated_gvs)) |> my_parmapi (check_validity info) in
  proof :: (List.concat_map (icreate cutoff info updated_gvs) generalizations)

(* Removes any generalized variables that very over written *)
let clean_variables (gen : t) : t =
  let map_ids = List.map (fun (v : Masks.variable) -> v.id) in
  let variables = map_ids gen.goal.expr.variables in 
  let assumptions = Hashtbl.create (Hashtbl.length gen.assumptions) in
  let keep_assumption (p : Masks.prop) = match p.kind with GenEquality v -> List.mem v variables | _ -> true in
  Hashtbl.iter (fun v (p : Masks.prop) -> if keep_assumption p then Hashtbl.add assumptions v p) gen.assumptions;
  match gen.generalized_terms with None -> { gen with assumptions }
  | Some tbl -> 
    let all_varibles = Hashtbl.fold (fun _ (p : Masks.prop) acc -> acc @ (map_ids p.expr.variables)) assumptions variables in
    let generalized_terms = Hashtbl.create (Hashtbl.length tbl) in
    Hashtbl.iter (fun (v : Masks.variable) t -> if List.mem v.id all_varibles then Hashtbl.add generalized_terms v t) tbl;
    { gen with assumptions; generalized_terms = Some generalized_terms }

let create info proof generalized_variables = 
  let cutoff = 3 in (* maximum number of generalizations to consider at a time *)
  let checked = check_validity info 100 (t_of_context (-1) proof) in
  let generalizations = icreate cutoff info (List.of_seq (Hashtbl.to_seq generalized_variables)) checked in
  let dedup = remove_duplicate generalization_eq generalizations in 
  (* let final_prune (g : t) = match g.state with STABLE -> true | _ -> generalization_count g <= 1 in *)
  let pruned = List.filter keep_generalizations dedup |> List.map clean_variables in
  List.mapi (fun label gen -> {gen with label}) pruned
