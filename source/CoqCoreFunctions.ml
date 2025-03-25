type included = YES | NO
(* constructors at the bottom *)

let coq_init_logic = [
  ("eq",YES);
  ("not",YES)
]

let coq_init_datatypes = [
  ("fst",NO);
  ("snd",NO);
  ("length",YES);
  ("app",YES)
]

let coq_init_peano = [
  ("le",YES);
  ("lt",YES);
  ("ge", NO);
  ("gt", NO)
]

let coq_lists_list = [
  ("tl",NO);
  ("In",YES);
  ("rev",NO);
  ("existsb",YES);
  ("forallb",YES);
  ("Exists",NO); (* needs decidability *)
  ("Forall",YES);
  ("NoDup",NO); (* needs decidability *)
  ("nodup",YES);
  ("map",YES);
  ("list_prod",NO);
  ("fold_left",NO);
  ("count_occ",NO);
  ("split",NO);
  ("list_max",NO);
  ("ForallPairs",NO); (* needs decidability *)
  ("last",NO);
  ("concat",NO);
  ("filter",NO);
  ("nth",NO); (* 3 args *)
  ("Add",NO) (* 3 args *)
]

let coq_sorting_permutation = [
  ("Permutation",YES);
  ("Permutation_transp",NO)
]

let to_include (mp : Names.ModPath.t) : string list =
  let filter = List.filter_map (fun (str,flag) -> match flag with | YES -> Some str | NO -> None) in
  match Names.ModPath.to_string mp with
  | "Coq.Init.Logic" -> filter coq_init_logic
  | "Coq.Init.Datatypes" -> filter coq_init_datatypes
  | "Coq.Lists.List" -> filter coq_lists_list
  | "Coq.Sorting.Permutation" -> filter coq_sorting_permutation
  | "Coq.Init.Peano" -> filter coq_init_peano
  | _ -> raise (Failure "Calling CoqCoreFunctions.functions_to_include on library not handled.")

let bool_eq_sketches env : (Constr.t * Constr.t) list = 
  let modpath = Names.ModPath.MPfile (List.map Names.Id.of_string ["Logic";"Init";"Coq"] |> Names.DirPath.make) in
  let eq_prop = (Typeops.infer env (Constr.mkIndU (UVars.in_punivs ((Names.MutInd.make2 modpath (Names.Label.make "eq")), 0)))).uj_val in
  let library = Names.ModPath.MPfile (List.map Names.Id.of_string ["Datatypes";"Init";"Coq"] |> Names.DirPath.make) in
  let true_construct = Typeops.infer env (Constr.mkConstructU (UVars.in_punivs (((Names.MutInd.make2 library (Names.Label.make "bool")), 0),1))) in
  let false_construct = Typeops.infer env (Constr.mkConstructU (UVars.in_punivs (((Names.MutInd.make2 library (Names.Label.make "bool")), 0),2))) in
  let _true = Constr.mkApp (eq_prop, Array.of_list [true_construct.uj_type;true_construct.uj_val]) in
  let _false = Constr.mkApp (eq_prop, Array.of_list [false_construct.uj_type;false_construct.uj_val]) in
  let pull_func (c : Constr.t) = let e = Typeops.infer env c in e.uj_val, e.uj_type in
  List.map pull_func [_true;_false]

let constructors env : (Constr.t * Constr.t) list = 
  let datatypes = Names.ModPath.MPfile (List.map Names.Id.of_string ["Datatypes";"Init";"Coq"] |> Names.DirPath.make) in
  let pair =  Typeops.infer env (Constr.mkConstructU (UVars.in_punivs (((Names.MutInd.make2 datatypes (Names.Label.make "prod")), 0),1))) in
  let nil =  Typeops.infer env (Constr.mkConstructU (UVars.in_punivs (((Names.MutInd.make2 datatypes (Names.Label.make "list")), 0),1))) in
  let cons =  Typeops.infer env (Constr.mkConstructU (UVars.in_punivs (((Names.MutInd.make2 datatypes (Names.Label.make "list")), 0),2))) in
  let none =  Typeops.infer env (Constr.mkConstructU (UVars.in_punivs (((Names.MutInd.make2 datatypes (Names.Label.make "option")), 0),1))) in
  let some =  Typeops.infer env (Constr.mkConstructU (UVars.in_punivs (((Names.MutInd.make2 datatypes (Names.Label.make "option")), 0),2))) in
  let pull_func (e : Environ.unsafe_judgment) = e.uj_val, e.uj_type in
  List.map pull_func [nil; pair; cons; none; some]