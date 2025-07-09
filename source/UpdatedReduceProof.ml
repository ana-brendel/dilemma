open Masks
open Utils

(** Syntactically simplify assumptions *)
let simplify_assumptions (info : Playground.info) (proof : Playground.proof) : Playground.proof = 
  print_endline ("\nSyntactically simplifying the assumptions..."); 
  if Option.has_some proof.generalized_terms then raise (Failure "No generalized terms expected yet [in UpdatedReduceProof.simplify_assumptions]");
  let gexpr = expr_from_constr info.env info.sigma in
  let og_assumptions =  Hashtbl.to_seq_values proof.assumptions |> List.of_seq |> List.map (fun e -> e.body) in
  let og_goal = proof.goal.body in
  let destructed = ReduceProof.destruct_until_fixed info.env og_assumptions in
  let rewrites, remaining = ReduceProof.split_for_rewrites destructed in
  let assumps = List.map (Vars.replace_vars rewrites) remaining |> remove_duplicate Constr.equal in
  let mk_var i = { id = Names.Id.of_string (Printf.sprintf "Assumption_%d" i); typ = Constr.mkProp} in
  let assumptions = Hashtbl.of_seq (List.to_seq (List.mapi (fun i a -> (mk_var i, gexpr a)) assumps)) in
  let goal = Vars.replace_vars rewrites og_goal |> gexpr in
  let variables = goal.variables @ (Hashtbl.to_seq_values assumptions |> List.of_seq |> List.concat_map (fun e -> e.variables)) |> remove_duplicate variable_eq in 
  { goal; assumptions; generalized_terms = None; variables }

(** Determine if context is provable via contradiction *)
let is_contradiction (info : Playground.info) (proof : Playground.proof) : bool =
  let initial = Hashtbl.to_seq proof.assumptions |> List.of_seq in
  let filtered_assumptions = List.filter (fun x -> Masks.is_quantified_via_str info.env info.sigma (snd x) |> not) initial in
  let assumption_constr = List.map (fun (_,e) -> e.body) filtered_assumptions in
  let conjunction = Utils.conjoin_props assumption_constr in
  match conjunction with
  | None -> false
  | Some conj -> let negation = Utils.negate_prop conj |> expr_from_constr info.env info.sigma in
  let query : CoqInterface.query = { q = CoqInterface.Satisfiable [negation]; label = "initial_contradiction_query"; info } in
  let results = match CoqInterface.execute query with | CoqInterface.Satisfiability r -> r | _ -> raise (Failure "[in UpdatedReduceProof.is_contradiction] Unexpected/incorrect result type.") in
  if List.length results != 1 then raise (Failure "Expected exactly one response from query [in UpdatedReduceProof.is_contradiction]")
  else snd (List.hd results)

(** Determine if context is satisfiable/stable *)
let is_never_true (info : Playground.info) (proof : Playground.proof)  : bool =
  let negation = Utils.negate_prop proof.goal.body |> expr_from_constr info.env info.sigma in
  let query : CoqInterface.query = { q = CoqInterface.Satisfiable [negation]; label = "goal_is_satisfiabl_query"; info } in
  let results = match CoqInterface.execute query with | CoqInterface.Satisfiability r -> r | _ -> raise (Failure "[in UpdatedReduceProof.is_contradiction] Unexpected/incorrect result type.") in
  if List.length results != 1 then raise (Failure "Expected exactly one response from query [in UpdatedReduceProof.is_contradiction]")
  else snd (List.hd results)

(** Simplify results *)
let reduce_constructor (info : Playground.info) i (constructor : Candidates.result) : Candidates.result = 
  match constructor.kind, constructor.synthesized with GENERALIZED, _ | WEAKENED, _ | AS_IS, _ | GENERALIZED_WEAKENED, None -> constructor
  | GENERALIZED_WEAKENED, Some implicant ->
    let implication a = List.fold_left (fun acc (assump : Constr.t) -> Utils.implication_constr assump acc) constructor.goal a in
  let possible_sets = Utils.power_set constructor.preconditions |> List.filter (List.mem implicant) in
  let rec check_k k =
    if (List.length constructor.preconditions <= k) then constructor.preconditions
    else let groups = List.filter (fun s -> List.length s = k) possible_sets in
    let exprs = List.map implication groups |> List.map (expr_from_constr info.env info.sigma) in
    let label = Printf.sprintf "remove_assumptions_for_result_%d" i in
    let query : CoqInterface.query = { q = CoqInterface.Satisfiable exprs; label; info } in
    let results = match CoqInterface.execute query with | CoqInterface.Satisfiability r -> r | _ -> raise (Failure "[in UpdatedReduceProof.reduce_constructors] Unexpected/incorrect result type.") in
    if (List.length groups != List.length results) then (raise (Failure "[in UpdatedReduceProof.reduce_constructors] Error in determining which assumptions are necessary"));
    let passed = List.combine groups results |> List.filter_map (fun (g,r) -> if snd r then Some g else None) in
    match passed with | [] -> check_k (k+1) | h :: _ -> h in
  let preconditions = check_k 0 in { constructor with preconditions }

let score_assumptions (assumptions : Constr.t list) : int = List.fold_left (fun score c -> score + constr_nodes c) 0 assumptions 

(* let rec bin_insert (arr : int array) e = 
  match Array.length arr with
  | 0 -> Array.of_list [e]
  | 1 -> let first = Array.get arr 0 in if first = e then arr else
    if first < e then Array.of_list [first;e] else Array.of_list [e;first] 
  | length -> let middle = Array.get arr (length / 2) in
    if middle = e then arr
    else let lower = Array.sub arr 0 (length / 2) in let upper = Array.sub arr (length / 2) (length / 2) in
    if middle < e then Array.append lower (bin_insert upper e) else Array.append (bin_insert lower e) upper *)

(* let rec bin_find lower upper (arr : int array) e = 
  if lower > upper then false 
  else let mid = lower + ((upper - lower) / 2) in
  let value = Array.get arr mid in
  if value = e then true
  else if value < e then bin_find (mid + 1) upper arr e else bin_find lower (mid - 1) arr e *)

(* let minimal_cover (cover' : int list) (assumptions : Constr.t list) (examples : (Constr.t, int list) Hashtbl.t) default : Constr.t list =
  if List.is_empty cover' then []
  else let cover = List.rev cover' in
  let cover_count = List.length cover in
  let sort_groups l l' = if (List.length l) != (List.length l') then Int.compare (List.length l) (List.length l') else Int.compare (score_assumptions l) (score_assumptions l') in
  let possible_sets = Utils.power_set assumptions |> List.sort sort_groups in
  let rec check sets =
    match sets with
    | [] -> default
    | [] :: remaining -> if cover_count = 0 then [] else check remaining
    | set :: remaining -> 
      (* let example_sets = List.map (fun s -> Hashtbl.find examples s) set in *)
      (* let covered = List.concat example_sets |> Array.of_list in Array.fast_sort Int.compare covered; *)
      (* let covered = List.fold_left (fun acc e -> List.fold_left bin_insert acc e) (List.hd example_sets |> List.rev |> Array.of_list) (List.tl example_sets) in *)
      let covered = Array.make (CoqInterface.reduction_count + 1) false in
      List.iter (fun s -> List.iter (fun e -> Array.set covered e true) s) (List.map (fun s -> Hashtbl.find examples s) set);
      (* let valid = if cover_count <= Array.length covered then List.for_all (bin_find 0 (Array.length covered - 1) covered) cover else false in *)
      let valid = if cover_count <= Array.length covered then List.for_all (Array.get covered) cover else false in
      if valid then set else check remaining in
  check possible_sets  *)

let minimal_cover (cover : int list) (assumptions : Constr.t list) (examples : (Constr.t, bool array) Hashtbl.t) default : Constr.t list =
  if List.is_empty cover then [] (* cover is reverse order *)
  else let sort_groups l l' = if (List.length l) != (List.length l') then Int.compare (List.length l) (List.length l') else Int.compare (score_assumptions l) (score_assumptions l') in
  let possible_sets = Utils.power_set assumptions |> List.sort sort_groups in
  let rec check sets =
    match sets with
    | [] -> default
    | [] :: remaining -> if List.length cover = 0 then [] else check remaining
    | set :: remaining -> let check_if_covered i = List.exists (fun s -> Array.get (Hashtbl.find examples s) i) set in
      if List.for_all check_if_covered cover then set else check remaining in
  check possible_sets 

(** Reduces assumptions for the original proof *)
let initial_filter (info : Playground.info) (proof : Generalize.t) =
  let initial = Hashtbl.to_seq proof.assumptions |> List.of_seq in
  let goal, filtered_assumptions = proof.goal.expr, List.filter (fun x -> Masks.is_quantified_via_str info.env info.sigma (snd x).expr |> not) initial in
  let label = Printf.sprintf "remove_assumptions_initial" in
  let query : CoqInterface.query = { q = CoqInterface.Reduction (List.map (fun (_,p) -> p.expr) filtered_assumptions,goal); label; info } in 
  let assumption_result, false_on_goal = match CoqInterface.execute query with | CoqInterface.ReductionResults (r1,r2) -> r1,r2 | _ -> raise (Failure "[in UpdatedReduceProof.initial_filter] Unexpected/incorrect result type.") in
  (* let false_examples = Hashtbl.create (1 + List.length filtered_assumptions) in
  List.iter (fun (_,p) -> Hashtbl.add false_examples p.expr.body []) filtered_assumptions; Hashtbl.add false_examples goal.body [];
  let process i b e = if not b then Hashtbl.add false_examples e.body (i :: Hashtbl.find false_examples e.body) else () in
  List.iter (fun (i,assumps,(g,b)) -> process i b g; List.iter (fun (e,b) -> process i b e) assumps) result;
  let assumptions_arg = (List.map (fun (_,p) -> p.expr.body) filtered_assumptions) in
  let redcued_assumptions = minimal_cover (Hashtbl.find false_examples goal.body) assumptions_arg false_examples assumptions_arg in *)
  let assumptions_arg = (List.map (fun (_,p) -> p.expr.body) filtered_assumptions) in
  let redcued_assumptions = minimal_cover false_on_goal assumptions_arg assumption_result assumptions_arg in
  let assumptions = List.filter (fun (_,p) -> List.mem p.expr.body redcued_assumptions) filtered_assumptions |> List.to_seq |> Hashtbl.of_seq in
  let variables =  (goal.variables @ Hashtbl.fold (fun _ p acc -> p.expr.variables @ acc) assumptions []) |> Utils.remove_duplicate variable_eq in
  { proof with assumptions; variables }

(** Reduces assumptions for a generalized proof *)
let filter_assumptions (info : Playground.info) (original_assumptions : (variable, prop) Hashtbl.t) (gen : Generalize.t) = 
  let initial = Hashtbl.to_seq gen.assumptions |> List.of_seq in
  let generalized_originals = Hashtbl.to_seq original_assumptions |> List.of_seq |> List.map (ReduceProof.generalize_assumptions info gen.generalized_terms) in
  let generalized_equalities,possible_assumptions = List.partition (fun (_,p) -> match p.kind with GenEquality _ -> true | _ -> false) initial in
  let goal, filtered_assumptions = gen.goal.expr, List.filter (fun x -> Masks.is_quantified_via_str info.env info.sigma (snd x).expr |> not) possible_assumptions in
  (* let filtered_assumptions = ReduceProof.prune_assumptions gen original_assumptions filtered_assumptions' in *)
  let generalized_default = generalized_equalities @ generalized_originals in
  let assumptions = match gen.state with
  | UNSTABLE -> generalized_default |> List.to_seq |> Hashtbl.of_seq
  | STABLE ->
    let label = Printf.sprintf "remove_assumptions_%d" gen.label in
    let query : CoqInterface.query = { q = CoqInterface.Reduction (List.map (fun (_,p) -> p.expr) filtered_assumptions,goal); label; info } in 
    let assumption_result, false_on_goal = match CoqInterface.execute query with | CoqInterface.ReductionResults (r1,r2) -> r1,r2 | _ -> raise (Failure "[in UpdatedReduceProof.initial_filter] Unexpected/incorrect result type.") in
    (* let false_examples = Hashtbl.create (1 + List.length filtered_assumptions) in
    List.iter (fun (_,p) -> Hashtbl.add false_examples p.expr.body []) filtered_assumptions; Hashtbl.add false_examples goal.body [];
    let process i b e = if not b then Hashtbl.add false_examples e.body (i :: Hashtbl.find false_examples e.body) else () in
    List.iter (fun (i,assumps,(g,b)) -> process i b g; List.iter (fun (e,b) -> process i b e) assumps) result;
    let assumptions_arg = (List.map (fun (_,p) -> p.expr.body) filtered_assumptions) in
    let default = List.map (fun (_,p) -> p.expr.body) generalized_default in
    let redcued_assumptions = minimal_cover (Hashtbl.find false_examples goal.body) assumptions_arg false_examples default in *)
    let assumptions_arg = (List.map (fun (_,p) -> p.expr.body) filtered_assumptions) in
    let redcued_assumptions = minimal_cover false_on_goal assumptions_arg assumption_result assumptions_arg in
    List.filter (fun (_,p) -> List.mem p.expr.body redcued_assumptions) (filtered_assumptions @ generalized_equalities) |> List.to_seq |> Hashtbl.of_seq in
  let variables =  (goal.variables @ Hashtbl.fold (fun _ p acc -> p.expr.variables @ acc) assumptions []) |> Utils.remove_duplicate variable_eq in
  { gen with assumptions; variables }
  