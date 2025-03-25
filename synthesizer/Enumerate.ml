open SynthUtils

(* Impose the invariant that sketches are NOT polymorphic *)
type sketch = {
  id : Constr.t;
  poly : int;
  args : Constr.t list;
  output : Constr.t;
  typ : Constr.t
}

let pull_sketch ((id,typ) : (Constr.t * Constr.t)) : sketch option  = 
  try let args', output = Term.decompose_prod_decls typ in
  let args = List.map handle_context args' |> List.rev in
  let poly = List.filter Constr.is_Type args |> List.length in
  Some { id; poly; args; output; typ } with _ -> None

  let monomorphize_sketch env sigma (types : (Constr.t list) list) sketch : (Constr.t * sketch) list = 
    let rec contains_rel ctor = 
      match Constr.kind ctor with
      | Rel _ -> true
      | Proj (_,_,c) -> contains_rel c
      | App (c, cs) -> contains_rel c || Array.fold_left (fun acc c' -> acc || contains_rel c') false cs
      | Prod (_,c1,c2) | Lambda (_,c1,c2) | Cast (c1,_,c2) -> contains_rel c1 || contains_rel c2
      | LetIn (_,c1,c2,c3) -> contains_rel c1 || contains_rel c2 || contains_rel c3
      | Array (_,cs,c1,c2) -> contains_rel c1 || contains_rel c2 || Array.fold_left (fun acc c' -> acc || contains_rel c') false cs
      | Case (info,a,b,arr,c,d,e) -> raise (Failure "Constr kind CASE not handled in Enumerate.monomorphize_sketch")
      | Evar p -> raise (Failure "Constr kind EVAR not handled in Enumerate.monomorphize_sketch")
      | Fix fp -> raise (Failure "Constr kind FIX not handled in Enumerate.monomorphize_sketch")
      | CoFix cfp -> raise (Failure "Constr kind COFIX not handled in Enumerate.monomorphize_sketch")
      | _ -> false in
    let generate t = 
      try (let args', output' = Term.decompose_prod_decls (Reduction.hnf_prod_applist env sketch.typ t) in
      let args = List.map handle_context args' |> List.rev in
      let poly = List.filter Constr.is_Type args |> List.length in
      if contains_rel output' || List.fold_left (fun acc typ -> acc || contains_rel typ) false t then None
      else 
        let label = Constr.mkApp (sketch.id, Array.of_list t) in
        let typ = (Typeops.infer env label).uj_type in 
        Some (output', { id = label; poly; args; output = output'; typ })) with _ -> None in
    if List.is_empty types then [(sketch.output,sketch)] else List.filter_map generate types

let rec populate_by_type (tbl : (Constr.t, 'a list) Hashtbl.t) (elements : (Constr.t * 'a) list) : unit =
  match elements with
  | [] -> ()
  | (typ,elem) :: rest -> 
    match Hashtbl.find_opt tbl typ with
    | None -> Hashtbl.add tbl typ [elem]; populate_by_type tbl rest
    | Some lst -> Hashtbl.replace tbl typ (elem::lst); populate_by_type tbl rest

let rec is_equal (eq_prop : Constr.t) (ctor : Constr.t) : bool =
  match (Constr.kind ctor) with
  | App (func,_) -> Constr.equal eq_prop func || is_equal eq_prop func
  | _ -> false

let rec get_body (ctor : Constr.t) : Constr.t =
  match Constr.kind ctor with
  | Lambda (_,_,body) -> get_body body
  | _ -> ctor

let rec monomorphize_type_args (types : Constr.t list) : Constr.t list =
  match types with
  | [] -> []
  | h :: tl when Constr.isVar h -> monomorphize_type_args tl (* TODO might want to change to add nat whenever type arg removed *)
  | h :: tl -> h :: monomorphize_type_args tl

let bool_eq_sketches env : sketch list = 
  let modpath = Names.ModPath.MPfile (List.map Names.Id.of_string ["Logic";"Init";"Coq"] |> Names.DirPath.make) in
  let eq_prop = (Typeops.infer env (Constr.mkIndU (UVars.in_punivs ((Names.MutInd.make2 modpath (Names.Label.make "eq")), 0)))).uj_val in
  let library = Names.ModPath.MPfile (List.map Names.Id.of_string ["Datatypes";"Init";"Coq"] |> Names.DirPath.make) in
  let true_construct = Typeops.infer env (Constr.mkConstructU (UVars.in_punivs (((Names.MutInd.make2 library (Names.Label.make "bool")), 0),1))) in
  let label = Constr.mkApp (eq_prop, Array.of_list [true_construct.uj_type;true_construct.uj_val]) in
  let args = [true_construct.uj_type] in
  let poly = 0 in let output = Constr.mkProp in []

let selective_fill env sigma (label : Constr.t) (args : Constr.t list) : Constr.t option =
  let to_str = string_of_constr env sigma in 
  let modpath = Names.ModPath.MPfile (List.map Names.Id.of_string ["Logic";"Init";"Coq"] |> Names.DirPath.make) in
  let eq_prop = (Typeops.infer env (Constr.mkIndU (UVars.in_punivs ((Names.MutInd.make2 modpath (Names.Label.make "eq")), 0)))).uj_val in
  let equal_flag = try Constr.equal (fst (Constr.destApp label)) eq_prop with _ -> false in
  let is_construct c = try Constr.isConstruct (fst (Constr.destApp c)) with _ -> false in
  let get_func c = try (fst (Constr.destApp c)) with _ -> c in
  let length_check = List.length args = 2 in
  if (equal_flag && length_check && Constr.compare (List.nth args 0) (List.nth args 1) <= 0) then None
  else if (equal_flag && length_check && (try Constr.isprop (Typeops.infer env (List.nth args 0)).uj_type with _ -> false)) then None
    (* SHOULD I FILTER OUT CONSTRUCTORS? *)
  (* else if (equal_flag && length_check && is_construct (List.nth args 0) && is_construct (List.nth args 0)) then None *)
  else if (equal_flag && length_check && (Constr.isApp (List.nth args 0) |> not) && (Constr.isApp (List.nth args 1) |> not)) then None
  else if (equal_flag && length_check && Constr.equal (get_func (List.nth args 0)) (get_func (List.nth args 1))) then None
  else if (List.length args > 1 && List.fold_left (fun (b,c) arg -> b && Constr.equal c arg, c) (true,List.hd args) args |> fst) then None
  else Some (Constr.mkApp (label, Array.of_list args))

let fill_in filter env sigma (sketch : sketch) (terms : (Constr.t, Constr.t list) Hashtbl.t) : Constr.t list = 
  let terms = List.filter_map (Hashtbl.find_opt terms) sketch.args in
  if (List.length terms = List.length sketch.args |> not) then []
  else let groups = cartesian terms in
  if filter then List.filter_map (selective_fill env sigma sketch.id) groups
  else List.map (fun args -> Constr.mkApp (sketch.id, Array.of_list args)) groups

let rec levelup filter (env : Environ.env) (sigma : Evd.evar_map) (terms : (Constr.t, Constr.t list) Hashtbl.t) 
  (skeletons : (Constr.t, sketch list) Hashtbl.t) (levels : int) : (Constr.t, Constr.t list) Hashtbl.t =
  if (levels = 0) then terms
  else let new_terms = Hashtbl.copy terms in
  let add_to_existing typ candidates = 
    match Hashtbl.find_opt new_terms typ with 
    | Some existing -> Hashtbl.replace new_terms typ (existing @ candidates |> remove_duplicate Constr.equal) 
    | _ -> Hashtbl.add new_terms typ candidates in
  let fill_in_sketch typ sketches = List.concat_map (fun s -> fill_in filter env sigma s terms) sketches |> remove_duplicate Constr.equal in
  Hashtbl.iter (fun typ sketches -> add_to_existing typ (fill_in_sketch typ sketches)) skeletons; 
  levelup filter env sigma new_terms skeletons (levels - 1) 

let get_initial_terms env sigma skeletons variables : (Constr.t, Constr.t list) Hashtbl.t = 
  let initial = Hashtbl.create 0 in
  let by_type = Hashtbl.create 0 in populate_by_type by_type (skeletons |> List.filter (fun (_,s) -> s.poly = 0));
  populate_by_type initial (List.map (fun (v,t) -> (t, Constr.mkVar v)) variables); 
  let constants = List.filter (fun (_,s) -> List.length s.args = 0) skeletons in
  let results' = levelup false env sigma initial by_type 1 in
  let results = Hashtbl.create (Hashtbl.length results') in
  Hashtbl.iter (Hashtbl.add results) results';
  let safe_add (typ, s) = 
    match Hashtbl.find_opt results typ with
    | None -> Hashtbl.add results typ [s.id]
    | Some lst -> Hashtbl.replace results typ (lst @ [s.id]) in
  List.iter safe_add constants; results

let fetch_skeletons env (functions : (Constr.t * Constr.t) list) = List.filter_map pull_sketch functions @ bool_eq_sketches env
let create_type_groups max_size types = (fun size -> List.init (size + 1) (fun _ -> types) |> cartesian) |> List.init max_size 
let max_poly l = List.fold_left (fun max curr -> if max < curr.poly then curr.poly else max) 0 l
let monomorphize_skeletons env sigma type_groups = List.concat_map (fun skt -> monomorphize_sketch env sigma (List.nth type_groups skt.poly) skt)

let fill_in_props env sigma poly_skeletons_props (terms : (Constr.t, Constr.t list) Hashtbl.t) : Constr.t list =
  let type_groups = [] :: create_type_groups (max_poly poly_skeletons_props) (Hashtbl.to_seq_keys terms |> List.of_seq) in
  let skeletons = monomorphize_skeletons env sigma type_groups poly_skeletons_props in
  let by_type = Hashtbl.create 0 in populate_by_type by_type (skeletons |> List.filter (fun (_,s) -> s.poly = 0));
  let results = levelup true env sigma terms by_type 1 in
  match Hashtbl.find_opt results Constr.mkProp with | Some lst -> lst | _ -> []

let remove_constants env sigma ctor : Constr.t list =
  (* Can implement the constr for True and False to check to avoid strings *)
  let reduced = reduce_constr env sigma in 
  let reduced_string c = string_of_constr env sigma (reduced c) in
  let check c = try ("True" = (reduced_string c) |> not) && ("False" = (reduced_string c) |> not) with _ -> true in
  List.filter check ctor

let includes_generalized env (variables : Names.Id.t list) (ctors : Constr.t list) : Constr.t list = 
  if List.is_empty variables then ctors
  else let contains_some c = 
    let vars = typed_vars_in_constr env c |> List.map fst in
    List.for_all (fun v -> List.mem v vars) variables in List.filter contains_some ctors 

let pull_types t = 
  match Constr.kind t with
  | App (_, args) -> Array.to_list args |> remove_duplicate Constr.equal
  | _ -> []

let terms (_ : int) env sigma variables gvars types' funcs : Constr.t list =
  let str = string_of_constr env sigma in
  (* (0) If there are only polymorphic types, make sure we get the type used there *)
  let types = types' @ (List.concat_map pull_types types') |> remove_duplicate Constr.equal in
  (* (1) Create skeletons that are not polymorphic *)
  let poly_skeletons_no_props, prop_skeletons = fetch_skeletons env funcs |> List.partition (fun skt -> Constr.is_Prop skt.output |> not) in
  let type_groups = [] :: create_type_groups (max_poly (poly_skeletons_no_props @ prop_skeletons)) (monomorphize_type_args types) in
  let skeletons = monomorphize_skeletons env sigma type_groups (poly_skeletons_no_props @ prop_skeletons) in
  (* (2) Gather initial terms - variables or constructors at depth 1 *)
  let intial_terms = get_initial_terms env sigma skeletons variables in
  (* (3) Fill terms into propositions shells *)
  fill_in_props env sigma prop_skeletons intial_terms |> remove_constants env sigma |> remove_duplicate Constr.equal 