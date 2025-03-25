open Masks
open Utils
(* open Coq_extractions *)

(* This will remove assumptions that are implications if there are correct inductive hypothesis *)
let remove_tautologies i info (assumptions : (variable * prop) list) : (variable * prop) list =
  let exprs = List.map (fun (_,p) -> p.expr) assumptions in let label = Printf.sprintf "remove_tautologies_%d" i in
  let query : CoqInterface.query = { q = CoqInterface.Satisfiable exprs; label; info } in
  let results = match CoqInterface.execute query with | CoqInterface.Satisfiability r -> r | _ -> raise (Failure "[in ReduceProof.filter_assumptions] Unexpected/incorrect result type.") in
  if (List.length assumptions != List.length results) then (raise (Failure "[in ReduceProof.filter_assumptions] Error in determining which assumptions are necessary"));
  List.combine assumptions results |> List.filter_map (fun (assump,(_,b)) -> if b then None else Some assump)

let generalize_assumptions (info : Playground.info) terms_to_generalize ((var,prop) : variable * prop) =
  match terms_to_generalize with | None -> (var,prop)
  | Some gvs -> 
    let lst = Hashtbl.to_seq gvs |> List.of_seq |> List.sort (fun (_,e1) (_,e2) -> constr_nodes e1.body - constr_nodes e2.body) in
    let replace expr (v,e) = replace_subterm e.body (Constr.mkVar v.id) expr in
    let expr = List.fold_left replace prop.expr.body lst |> expr_from_constr info.env info. sigma in
    (var, { prop with expr })

let prune_assumptions (proof : Generalize.t) (original_assumptions : (variable, prop) Hashtbl.t)  assumptions : (variable * prop) list =
    match proof.state, proof.generalized_terms with
    | UNSTABLE, _ | _, None -> assumptions
    | STABLE, Some gvs' ->  let gvs = Hashtbl.to_seq_keys gvs' |> List.of_seq |> List.map (fun v -> v.id) in
    let originals = Hashtbl.to_seq_keys original_assumptions |> List.of_seq |> List.map (fun v -> v.id) in
    let filter_func (v,p) = List.exists (Names.Id.equal v.id) originals || List.exists (fun v -> List.exists (fun v' -> Names.Id.equal v v'.id) p.expr.variables) gvs in
    List.filter filter_func assumptions

let score_assumptions (assumptions : ('a * prop) list) : int = List.fold_left (fun score (_,p) -> score + constr_nodes p.expr.body) 0 assumptions 

let filter_assumptions (info : Playground.info) (original_assumptions : (variable, prop) Hashtbl.t) (proof : Generalize.t) : Generalize.t = 
  (* might want to review *)
  let initial = Hashtbl.to_seq proof.assumptions |> List.of_seq in
  let generalized_originals = Hashtbl.to_seq original_assumptions |> List.of_seq |> List.map (generalize_assumptions info proof.generalized_terms) in
  let generalized_equalities,possible_assumptions = List.partition (fun (_,p) -> match p.kind with GenEquality _ -> true | _ -> false) initial in
  let goal, filtered_assumptions' = proof.goal, List.filter (fun x -> Masks.is_quantified_via_str info.env info.sigma (snd x).expr |> not) possible_assumptions in
  let filtered_assumptions = remove_tautologies proof.label info filtered_assumptions' |> (prune_assumptions proof original_assumptions) in
  let generalized_default = generalized_equalities @ generalized_originals in
  let implication a = List.fold_left (fun acc ((_,assump) : (variable * prop)) -> Utils.implication_constr assump.expr.body acc) goal.expr.body a in
  let possible_sets' = Utils.power_set filtered_assumptions |> List.map (List.sort (fun (v1,_) (v2,_) -> Names.Id.compare v1.id v2.id)) in
  let possible_sets = remove_duplicate (List.equal (fun (v1,_) (v2,_) -> Names.Id.equal v1.id v2.id)) possible_sets' in
  let rec check_k k =
    if (List.length filtered_assumptions < k) then generalized_default
    else let groups = List.filter (fun s -> List.length s = k) possible_sets in
    let exprs = List.map implication groups |> List.map (expr_from_constr info.env info.sigma) in
    let label = Printf.sprintf "remove_assumptions_%d" proof.label in
    let query : CoqInterface.query = { q = CoqInterface.Satisfiable exprs; label; info } in
    let results = match CoqInterface.execute query with | CoqInterface.Satisfiability r -> r | _ -> raise (Failure "[in ReduceProof.filter_assumptions] Unexpected/incorrect result type.") in
    if (List.length groups != List.length results) then (raise (Failure "[in ReduceProof.filter_assumptions] Error in determining which assumptions are necessary"));
    let passed = List.combine groups results |> List.filter_map (fun (g,r) -> if snd r then Some g else None) in
    match passed with | [] -> check_k (k+1) | h :: _ -> List.fold_left (fun min curr -> if score_assumptions curr < score_assumptions min then curr else min) h passed in
  let assumptions = Hashtbl.of_seq (List.to_seq (match proof.state with | UNSTABLE -> generalized_default | STABLE -> check_k 0)) in
  let variables =  (proof.goal.expr.variables @ Hashtbl.fold (fun _ e acc -> e.expr.variables @ acc) assumptions []) |> Utils.remove_duplicate variable_eq in
  { proof with goal; assumptions; variables }

let initial_filter (info : Playground.info) (proof : Generalize.t) =
  let initial = Hashtbl.to_seq proof.assumptions |> List.of_seq in
  let goal, filtered_assumptions' = proof.goal, List.filter (fun x -> Masks.is_quantified_via_str info.env info.sigma (snd x).expr |> not) initial in
  let filtered_assumptions = remove_tautologies 0 info filtered_assumptions' in
  let implication a = List.fold_left (fun acc ((_,assump) : (variable * prop)) -> Utils.implication_constr assump.expr.body acc) goal.expr.body a in
  let possible_sets' = Utils.power_set filtered_assumptions |> List.map (List.sort (fun (v1,_) (v2,_) -> Names.Id.compare v1.id v2.id)) in
  let possible_sets = remove_duplicate (List.equal (fun (v1,_) (v2,_) -> Names.Id.equal v1.id v2.id)) possible_sets' in
  let rec check_k k =
    if (List.length filtered_assumptions = k) then filtered_assumptions
    else let groups = List.filter (fun s -> List.length s = k) possible_sets in
    let exprs = List.map implication groups |> List.map (expr_from_constr info.env info.sigma) in
    let label = Printf.sprintf "remove_assumptions_initial" in
    let query : CoqInterface.query = { q = CoqInterface.Satisfiable exprs; label; info } in 
    let results = match CoqInterface.execute query with | CoqInterface.Satisfiability r -> r | _ -> raise (Failure "[in ReduceProof.initial_filter] Unexpected/incorrect result type.") in
    if (List.length groups != List.length results) then (raise (Failure "[in ReduceProof.initial_filter] Error in determining which assumptions are necessary"));
    let passed = List.combine groups results |> List.filter_map (fun (g,r) -> if snd r then Some g else None) in
    match passed with | [] -> check_k (k+1) | h :: _ -> List.fold_left (fun min curr -> if score_assumptions curr < score_assumptions min then curr else min) h passed in
  let assumptions = Hashtbl.of_seq (List.to_seq (check_k 0)) in
  let variables =  (goal.expr.variables @ Hashtbl.fold (fun _ p acc -> p.expr.variables @ acc) assumptions []) |> Utils.remove_duplicate variable_eq in
  { proof with goal; assumptions; variables }

let is_contradiction (info : Playground.info) (proof : Playground.proof) : bool =
  let initial = Hashtbl.to_seq proof.assumptions |> List.of_seq in
  let filtered_assumptions = List.filter (fun x -> Masks.is_quantified_via_str info.env info.sigma (snd x) |> not) initial in
  let assumption_constr = List.map (fun (_,e) -> e.body) filtered_assumptions in
  let conjunction = Utils.conjoin_props assumption_constr in
  match conjunction with
  | None -> false
  | Some conj -> let negation = Utils.negate_prop conj |> expr_from_constr info.env info.sigma in
  let query : CoqInterface.query = { q = CoqInterface.Satisfiable [negation]; label = "initial_contradiction_query"; info } in
  let results = match CoqInterface.execute query with | CoqInterface.Satisfiability r -> r | _ -> raise (Failure "[in ReduceProof.is_contradiction] Unexpected/incorrect result type.") in
  if List.length results != 1 then raise (Failure "Expected exactly one response from query [in ReduceProof.is_contradiction]")
  else snd (List.hd results)

let is_never_true (info : Playground.info) (proof : Playground.proof)  : bool =
  let negation = Utils.negate_prop proof.goal.body |> expr_from_constr info.env info.sigma in
  let query : CoqInterface.query = { q = CoqInterface.Satisfiable [negation]; label = "goal_is_satisfiabl_query"; info } in
  let results = match CoqInterface.execute query with | CoqInterface.Satisfiability r -> r | _ -> raise (Failure "[in ReduceProof.is_contradiction] Unexpected/incorrect result type.") in
  if List.length results != 1 then raise (Failure "Expected exactly one response from query [in ReduceProof.is_contradiction]")
  else snd (List.hd results)

(* Returns rewrite pair if the constr is a variable rewrite *)
let pull_var_rewrite env ctor = (* BUGGY *)
match try Some (Constr.destApp ctor) with _ -> None with 
| None -> None 
| Some (label, args') ->
  let args = try Array.to_list args' |> List.tl |> List.map Constr.destVar with _ -> [] in 
  if List.length args != 2 then None
  else let pair = List.hd args, Constr.mkVar (List.hd (List.tl args)) in
    let modpath = Names.ModPath.MPfile (List.map Names.Id.of_string ["Logic";"Init";"Coq"] |> Names.DirPath.make) in
    let eq_prop = (Typeops.infer env (Constr.mkIndU (UVars.in_punivs ((Names.MutInd.make2 modpath (Names.Label.make "eq")), 0)))).uj_val in
    if try Constr.equal (label) eq_prop with _ -> false then Some pair else None

(* Apply any single variable rewrites in the assumptions to the state to remove redundancy *)
let apply_assumption_rewrites env sigma goal' assumptions' = (* BUGGY *)
let make_expr = expr_from_constr env sigma in
let goal = goal'.body in
let assumptions = List.map (fun (v,e) -> v, e.body) assumptions' in
let equalities = List.filter_map (fun (_,c) -> pull_var_rewrite env c) assumptions in
let remaining = List.filter (fun (_,c) -> match pull_var_rewrite env c with None -> true | _ -> false) assumptions in
if List.is_empty equalities then goal', assumptions'
else let updated_goal = Vars.replace_vars equalities goal in
let updated_assumptions = List.map (fun (v,c) -> v, Vars.replace_vars equalities c) remaining in
make_expr updated_goal, List.map (fun (v,c) -> v, make_expr c) updated_assumptions

let rec is_pair_eq offset str ctor = 
  let pr typ = print_endline (Printf.sprintf "%s%s is %s" offset (str ctor) typ) in
  match Constr.kind ctor with
  | Rel _ -> pr "Rel"
  | Proj (_,_,c) -> pr "Proj"
  | App (c, cs) -> pr "App"; is_pair_eq (offset ^ "  ") str c; Array.iter (is_pair_eq (offset ^ "  + ") str) cs
  | Prod (_,c1,c2) -> pr "Prod"
  | Lambda (_,c1,c2) -> pr "Lambda"
  | Cast (c1,_,c2) -> pr "Cast"
  | LetIn (_,c1,c2,c3) -> pr "LetIn"
  | Array (_,cs,c1,c2) -> pr "Array"
  | Case (info,a,b,arr,c,d,e) -> pr "Case"
  | Evar p -> pr "Evar"
  | Fix fp -> pr "Fix"
  | CoFix cfp -> pr "CoFix"
  | Var v -> print_endline (Printf.sprintf "%s%s is Var" offset (Names.Id.to_string v))
  | Ind ((mut,i),u) -> pr "Ind"
  | Construct ((mut,i),u) -> pr "Construct"
  | _ -> pr "Other"

let destruct_prod ctor = 
  let is_prod mut = Names.Label.equal (Names.Label.make "prod") (Names.MutInd.label mut) in
  match Constr.kind ctor with
  | App (label,args) -> 
    (match Constr.kind label with
    | Ind ((mut,_),_) when (is_prod mut && Array.length args = 2) -> Some (Array.get args 0, Array.get args 1)
    | Construct (((mut,_),_),_) when (is_prod mut && Array.length args = 4) -> Some (Array.get args 2, Array.get args 3)
    | _ -> None)
  | _ -> None

let destruct env ctor =
  let eq_label mut = Names.Label.equal (Names.Label.make "eq") (Names.MutInd.label mut) in
  let and_label mut = Names.Label.equal (Names.Label.make "and") (Names.MutInd.label mut) in
  let mkEqual typ lhs rhs = construct_equal env typ lhs rhs in
  match Constr.kind ctor with
  | App (label,args) -> 
    (match Constr.kind label with
    | Ind ((mut,_),_) when (eq_label mut && Array.length args = 3) -> 
      (match destruct_prod (Array.get args 0), destruct_prod (Array.get args 1), destruct_prod (Array.get args 2) with
      | Some (tx,ty), Some (x1,y1), Some (x2,y2) -> [(mkEqual tx x1 x2);(mkEqual ty y1 y2)] | _ -> [ctor])
    | Ind ((mut,_),_) when (and_label mut && Array.length args = 2) -> Array.to_list args
    | _ -> [ctor])
  | _ -> [ctor]

let rec destruct_until_fixed env ctors =
  let mapped = List.map (fun c -> ([c], (destruct env c))) ctors in
  let results = List.concat_map snd mapped in
  if (List.for_all (fun (l1,l2) -> List.equal Constr.equal l1 l2) mapped) then results 
  else destruct_until_fixed env results

let rewrite_option ctor : bool =
  let eq_label mut = Names.Label.equal (Names.Label.make "eq") (Names.MutInd.label mut) in
  let is_var c = match Constr.kind c with Var _ -> true | _ -> false in
  match Constr.kind ctor with
  | App (label,args) -> 
    (match Constr.kind label with
    | Ind ((mut,_),_) when (eq_label mut && Array.length args = 3 && is_var (Array.get args 1) && is_var (Array.get args 2)) -> true
    | _ -> false)
  | _ -> false

let equality_option ctor : (Names.variable * Constr.t) option =
  let eq_label mut = Names.Label.equal (Names.Label.make "eq") (Names.MutInd.label mut) in
  let is_var c = match Constr.kind c with Var _ -> true | _ -> false in
  match Constr.kind ctor with
  | App (label,args) -> 
    (match Constr.kind label with
    | Ind ((mut,_),_) when (eq_label mut && Array.length args = 3 && (is_var (Array.get args 1))) -> Some ((Array.get args 1 |> Constr.destVar),(Array.get args 2))
    | Ind ((mut,_),_) when (eq_label mut && Array.length args = 3 && (is_var (Array.get args 2))) -> Some ((Array.get args 2 |> Constr.destVar),(Array.get args 1))
    | _ -> None)
  | _ -> None

let get_rewrite_pair ctor =
  match Constr.kind ctor with 
  | App (_,args) when rewrite_option ctor -> Constr.destVar (Array.get args 1), Constr.destVar (Array.get args 2)
  | _ -> raise (Failure "Expects only applicable rewrites [in ReduceProof.get_rewrite_pair]")

let rec transitivity = function
| [] -> []
| (x,y) :: remaining -> 
  match List.find_opt (fun (p,q) -> Names.Id.equal p x || Names.Id.equal q x || Names.Id.equal p y || Names.Id.equal q y) remaining with
  | Some (p,q) when (Names.Id.equal p x) -> transitivity ((y,q) :: (List.filter (fun (a,b) -> not (Names.Id.equal a p && Names.Id.equal b q)) remaining))
  | Some (p,q) when (Names.Id.equal q x) -> transitivity ((y,p) :: (List.filter (fun (a,b) -> not (Names.Id.equal a p && Names.Id.equal b q)) remaining))
  | Some (p,q) when (Names.Id.equal p y) -> transitivity ((x,q) :: (List.filter (fun (a,b) -> not (Names.Id.equal a p && Names.Id.equal b q)) remaining))
  | Some (p,q) when (Names.Id.equal q y) -> transitivity ((x,p) :: (List.filter (fun (a,b) -> not (Names.Id.equal a p && Names.Id.equal b q)) remaining))
  | _ -> (x,y) :: (transitivity remaining)
 
let reduce_rewrites pairs =
  let cmp_set (x1,y1) (x2,y2) = (Names.Id.equal x1 x2 && Names.Id.equal y1 y2) || (Names.Id.equal x1 y2 && Names.Id.equal y1 x2) in
  let dedup = remove_duplicate cmp_set pairs |> List.filter (fun (x,y) -> Names.Id.equal x y |> not) in
  transitivity dedup

let rec gather_equalities equals =
  match equals with
  | [] -> []
  | (v,expr) :: others -> 
    let matches, none_matches = List.partition (fun (v',expr') -> Constr.equal expr expr') others in
    List.map (fun (v',_) -> v,v') matches @ gather_equalities none_matches

let split_for_rewrites ctors =
  let potential_rewrites, remaining = List.partition rewrite_option ctors in
  let equality_candidates = gather_equalities (List.filter_map equality_option remaining) in
  let rewrites = reduce_rewrites (equality_candidates @ List.map get_rewrite_pair potential_rewrites) in
  List.map (fun (v,c) -> v, Constr.mkVar c) rewrites, remaining  

let simplify_assumptions (info : Playground.info) (proof : Playground.proof) : Playground.proof = 
  print_endline ("\nSyntactically simplifying the assumptions..."); 
  if Option.has_some proof.generalized_terms then raise (Failure "No generalized terms expected yet [in ReduceProof.simplify_assumptions]");
  let gexpr = expr_from_constr info.env info.sigma in
  let og_assumptions =  Hashtbl.to_seq_values proof.assumptions |> List.of_seq |> List.map (fun e -> e.body) in
  let og_goal = proof.goal.body in
  let destructed = destruct_until_fixed info.env og_assumptions in
  let rewrites, remaining = split_for_rewrites destructed in
  let assumps = List.map (Vars.replace_vars rewrites) remaining |> remove_duplicate Constr.equal in
  let mk_var i = { id = Names.Id.of_string (Printf.sprintf "Assumption_%d" i); typ = Constr.mkProp} in
  let assumptions = Hashtbl.of_seq (List.to_seq (List.mapi (fun i a -> (mk_var i, gexpr a)) assumps)) in
  let goal = Vars.replace_vars rewrites og_goal |> gexpr in
  let variables = goal.variables @ (Hashtbl.to_seq_values assumptions |> List.of_seq |> List.concat_map (fun e -> e.variables)) |> remove_duplicate variable_eq in 
  { goal; assumptions; generalized_terms = None; variables }