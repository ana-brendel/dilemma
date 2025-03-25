open ExtractionUtils

let tmp_folder cwd = Printf.sprintf "%s/%s" cwd "lemmafinder_tmp" 

let mkTmp cwd = 
    let dir = tmp_folder cwd in 
    (if (try Sys.is_directory dir with _ -> false) then let _ = run_cmd (Printf.sprintf "rm -r %s" dir) in ());
    let _ = run_cmd (Printf.sprintf "mkdir %s" dir) in dir

let prop_to_bool = "Definition prop_to_bool (P : Prop) {_ : Dec P} := (match (@dec P _) with | left _ => true | right _ => false end)."

let quickchick_imports = [
    "From QuickChick Require Import QuickChick.";
    "Set Warnings \"-extraction-opaque-accessed,-extraction\".";
    "QCInclude \".\". "
]

let nat_typeclass_info = [
    "Derive Show for nat.";
    "Derive Arbitrary for nat."; 
    "Instance Dec_Eq_nat : Dec_Eq nat.";
    "Proof. dec_eq. Qed." 
]

let bool_typeclass_info = [
    "Derive Show for bool."; 
    "Derive Arbitrary for bool."; 
    "Instance Dec_Eq_bool : Dec_Eq bool."; 
    "Proof. dec_eq. Qed." 
]

let prelude file_formatted = 
    let contents = List.filter (fun l -> String.ends_with ~suffix:"LFindToo." l |> not) file_formatted in
    String.concat "\n" (quickchick_imports @ [""] @ nat_typeclass_info @ [""] @ bool_typeclass_info @ [""] @ contents)

let gen_type typ = Printf.sprintf "Definition gen_type := %s." typ

let generation_code typ = [
    gen_type typ; "";
    "Require Import String. Open Scope string_scope.";
    "Parameter print : gen_type -> string -> gen_type.";
    "Lemma generate (g : gen_type) : g = g. Admitted.";
    "Extract Constant print => \"fun n nstr -> print_endline (String.of_seq (List.to_seq nstr)); (n)\". ";
    "Definition generate_for_type (g : gen_type) := let vvar := show g in let lfvar := print g vvar in generate lfvar.";
    "Close Scope string_scope.";
    "QuickChick generate_for_type."
]

let generation_code_by_prop str count ((vars,str_vars),(types,str_types)) prop = 
    if List.is_empty types then [] 
    else let print = Printf.sprintf "Parameter print : %s -> string -> %s." (str (List.hd types)) (str (List.hd types)) in 
    let parameters = List.map2 (fun v t -> Printf.sprintf "(%s : %s)" (Names.Id.to_string v) (str t)) vars types |> String.concat " " in 
    let shows = List.map (fun v -> Printf.sprintf "show %s" (Names.Id.to_string v)) vars |> String.concat " ++ \"&\" ++ " in
    let def_show = Printf.sprintf "Definition our_show %s := \"!\" ++ %s ++ \"!\"." parameters shows in
    [
        Printf.sprintf "Extract Constant defNumTests => \"%d\"." count; ""; "Open Scope string_scope.";
        print; "Extract Constant print => \"fun n nstr -> print_endline (String.of_seq (List.to_seq nstr)); (n)\". ";
        def_show; "Close Scope string_scope."; "";
        Printf.sprintf "Lemma generate %s : %s. Admitted." parameters prop;
        Printf.sprintf "Definition generate_for_type %s :=" parameters;
        Printf.sprintf "let vvar := our_show %s in" (String.concat " " (List.map Names.Id.to_string vars));
        Printf.sprintf "let lfvar := print %s vvar in" (Names.Id.to_string (List.hd vars));
        Printf.sprintf "generate lfvar %s." (String.concat " " (List.map Names.Id.to_string (List.tl vars)));
        "\nQuickChick generate_for_type."
    ]

let define_single_example example_type (label,examples) = 
    Printf.sprintf "Definition %s : (%s) := %s." label example_type examples

let define_example_set example_type label examples = 
    let examples' = List.map (fun (i,l) -> Printf.sprintf "(\"%d\",%s)" i l) examples in
    Printf.sprintf "Definition %s : (list (string * %s)) := [%s]." label example_type (String.concat "; " examples')

let format_prop env sigma example_format (label, ctor) = 
    let candidate = str_of_constr_full_via_str env sigma ctor in
    let (_,example_vars), (_,example_type) = example_format in 
    Printf.sprintf "Definition %s (ex : %s) : bool := match ex with | %s => (prop_to_bool (%s)) end. "
    label example_type example_vars candidate