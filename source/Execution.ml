open Coq_extractions
open Masks

type case = VALID_GENERALIZED | VALID_UNGENERALIZED | INVALID_GENERALIZED | UNSTABLE | DEAD_END

type t = {
  label : int;
  proof : Generalize.t;
  case : case;
  goal: prop;
  assumptions: prop list
}

let get_context_ml (context : Generalize.t) = Printf.sprintf "State_%d" context.label

let get_execution_ml t = get_context_ml t.proof

let get_examples (e : t) = e.goal.true_on @ e.goal.false_on

let generalization_count self = match self.proof.generalized_terms with Some tbl -> Hashtbl.length tbl | _ -> 0

let display (info : Playground.info) (self : t) : unit =
  let spec (p : prop) = match p.kind with | GenEquality _ -> "[+]" | _ -> "" in
  print_endline ("Label: " ^ string_of_int self.label);
  print_endline ("Generalization Count: " ^ string_of_int (match self.proof.generalized_terms with Some tbl -> Hashtbl.length tbl | _ -> 0));
  print_endline ("Assumptions: " ); (List.iter (fun (p : prop) -> (" -- " ^ spec p ^ Utils.str_of_constr info.env info.sigma p.expr.body) |> print_endline) self.assumptions);
  print_endline ("Goal: " ^ Utils.str_of_constr info.env info.sigma self.goal.expr.body);
  print_endline ("Case: " ^ match self.case with | VALID_GENERALIZED -> "Valid and Generalized" | UNSTABLE -> "Not Stable" | DEAD_END -> "Assumptions Not Satisfied"
  | VALID_UNGENERALIZED -> "Valid and Un-Generalized"  | INVALID_GENERALIZED -> "Invalid and Generalized")

(* ******************************************************************************************* *)
(* ******************************************************************************************* *)
(* ******************************************************************************************* *)
(* ******************************************************************************************* *)

let decide_case generalized (assumptions : prop list) (goal : prop) : case  = 
  let all_examples = goal.true_on @ goal.false_on in
  let get_true_on_all = List.fold_left (fun in_all (a : prop) -> Utils.intersection (fun (e1 : example) e2 -> e1.label = e2.label) in_all a.true_on) all_examples in
  let original_assumptions = List.filter (fun a -> match a.kind with | Assumption -> true | _ -> false) assumptions in
  (* no counterexamples for the goal *)
  if (List.is_empty goal.false_on) then (if generalized then VALID_GENERALIZED else VALID_UNGENERALIZED)
  else let true_on_all_assumptions = get_true_on_all assumptions |> List.map (fun (e : example) -> e.label) in 
  (* assumptions cannot be satisfied or no assumptions *)
  if (List.is_empty assumptions) then UNSTABLE 
  else if (List.is_empty true_on_all_assumptions) then DEAD_END 
  else let true_on_all_og_assumptions = get_true_on_all original_assumptions |> List.map (fun (e : example) -> e.label) in
  (* case 4 if the original assumptions are insufficient *) 
  if (List.exists (fun (e : example) -> List.mem e.label true_on_all_assumptions) goal.false_on) then UNSTABLE 
  (* case 2 if the generalized assumption was necessary *)
  else if (List.exists (fun (e : example) -> List.mem e.label true_on_all_og_assumptions) goal.false_on) then INVALID_GENERALIZED
  else (if generalized then VALID_GENERALIZED else VALID_UNGENERALIZED)

let prop_from_tuple (info : (string, prop) Hashtbl.t) (label_str,trues,falses) : prop =
  let shallow_example label : example = { label; } in
  let prop = Hashtbl.find info label_str in
  let true_on = List.map shallow_example trues in
  let false_on = List.map shallow_example falses in
  { prop with true_on; false_on; }

let get_execution_without_examples generalized (proof : Generalize.t) : t =
  let assumptions = Hashtbl.fold (fun _ p acc -> p :: acc) proof.assumptions [] in
  let case = if generalized then VALID_GENERALIZED else VALID_UNGENERALIZED in
  { label = proof.label; proof; case; goal = proof.goal; assumptions }

let analyze (info : Playground.info) generalized_definitions example_sets_ml (proof : Generalize.t) : t option =
  let generalized = Option.has_some proof.generalized_terms in
  if (List.is_empty proof.variables && proof.generalized_terms = None) then None 
  else if (Generalize.runs_synthesis proof |> not) then Some (get_execution_without_examples generalized proof) else
  let pair = try Hashtbl.find example_sets_ml proof.label with _ -> raise (Failure "Example definitions not found for generalization [in Execution.analyze]") in
  let assumptions = (Hashtbl.to_seq proof.assumptions |> List.of_seq) |> List.filter (fun (_,e) -> Masks.is_quantified_via_str info.env info.sigma e.expr |> not) in
  let format ((v,e) : (_ * prop)) = Formatting.format_prop info.env info.sigma (Generalize.get_example_format info proof) (v,e.expr.body) in
  let proof_info = ("goal", proof.goal) :: (List.map (fun ((v,e) : (variable * prop)) -> ("assump_" ^ Names.Id.to_string v.id, e)) assumptions) in
  let formatted_state =  Formatting.prop_to_bool :: (List.map format proof_info) @ (List.map snd generalized_definitions) |> String.concat "\n" in
  let state_ml = Extractor.extract true (Some (true,pair)) info.tmp_dir info.file_formatted (get_context_ml proof) formatted_state (List.map fst proof_info @ List.map fst generalized_definitions) in
  let prop_info = Evaluator.split_examples info.tmp_dir proof.label state_ml (List.map fst proof_info) in
  let info_tbl = Hashtbl.of_seq (List.to_seq proof_info) in 
  let props = List.map (prop_from_tuple info_tbl) prop_info in
  let goals, assumptions = List.partition (fun (p : prop) -> match p.kind with | Goal -> true | _ -> false) props in
  let goal = match goals with | [g] -> g | _ -> raise (Failure "Error in processing propositions, got more than one or no goal [in Execution.analyze]") in
  let case = decide_case generalized assumptions goal in
  Some { label = proof.label; proof; case; goal; assumptions }