# Lemma Synthesis Tactic
This repo contains a _Rocq_ tactic (`dilemma`) to perform lemma synthesis, which can be invoked at any point within a _Rocq_ proof. The `dilemma` tactic was created as an implementation of the techniques presented in the follow paper: **TBD link 1**. See bottom of the README for more information pertaining to the OOPSLA submission.

## Installation Instructions (using opam):
If you don't have `opam` installed, you'll need todo that first. (We've specified the versions for each installation in an attempt to minimize errors when version get updated.)
1. `opam update`
1. `opam switch create dilemma ocaml.5.1.1`
1. `opam switch dilemma`
1. `eval $(opam env)`
1. `opam install dune=3.17.2`
1. `opam install conf-gmp=4`
1. `opam install zarith=1.13`
1. `opam install coq=8.20.1`
1. `opam repo add coq-released https://coq.inria.fr/opam/released`
1. `opam update`
1. `opam install coq-quickchick=2.0.5`
1. `opam install parmap=1.2.5`
1. `opam install coq-serapi=8.20.0+0.20.0`
1. `cd .../dilemma`
1. `dune build && dune install`

<details markdown="1">
<summary>Click here to see full list of opam dependencies and their version, in the case there are version issues that occur when using the instructions above
</summary>

* base = v0.17.3
* base-bigarray = base
* base-domains = base
* base-nnp = base
* base-threads = base
* base-unix = base
* cmdliner = 1.3.0
* conf-gmp = 4
* conf-pkg-config = 4
* coq = 8.20.1
* coq-core = 8.20.1
* coq-ext-lib = 0.13.0
* coq-mathcomp-ssreflect = 1.19.0
* coq-quickchick = 2.0.5
* coq-serapi = 8.20.0+0.20.0
* coq-simple-io = 1.11.0
* coq-stdlib = 8.20.1
* coqide-server = 8.20.1
* cppo = 1.8.0
* csexp = 1.5.2
* dune = 3.19.1
* dune-configurator = 3.19.1
* menhir = 20240715
* menhirCST = 20240715
* menhirLib = 20240715
* menhirSdk = 20240715
* num = 1.6
* ocaml = 5.1.1
* ocaml-base-compiler = 5.1.1
* ocaml-compiler-libs = v0.12.4
* ocaml-config = 3
* ocaml-options-vanilla = 1
* ocaml_intrinsics_kernel = v0.17.1
* ocamlbuild = 0.16.1
* ocamlfind = 1.9.8
* parmap = 1.2.5
* parsexp = v0.17.0
* ppx_compare = v0.17.0
* ppx_derivers = 1.2.1
* ppx_deriving = 6.0.3
* ppx_deriving_yojson = 3.9.1
* ppx_hash = v0.17.0
* ppx_import = 1.11.0
* ppx_sexp_conv = v0.17.0
* ppxlib = 0.35.0
* ppxlib_jane = v0.17.0
* sexplib = v0.17.0
* sexplib0 = v0.17.0
* stdlib-shims = 0.3.0
* yojson = 3.0.0
* zarith = 1.13

</details>

## Requirements to Run
`dilemma` uses `QuickChick` as its sampler and checker, so as long as you can invoke the `QuickChick` tactic with any proposition or type available in the file from the same location you are calling `dilemma` from, you should be good to go. Explicitly, this means that all propositions that are available in the file need to be proved decidable, and any type needs to be decidable with respect to its equality, as well as "showable" and have a generator.

For inductive data types, this is can typically be done automatically using tools from the `QuickChick` library. For example, to include the definitions for `nat`:
```
From QuickChick Require Import QuickChick.
...
Derive Show for nat.
Derive Arbitrary for nat.
Instance Dec_Eq_nat : Dec_Eq nat.
Proof. dec_eq. Qed.
```

Note, if the `show` function for the type uses special notation (i.e. not just the constructors), then there might be errors thrown. For example, for the `list` type you would want to define a specific `show` instance (see below) that doesn't use `[]` or `::`:
```
Instance show_list {T} `{_ : Show T} : Show (list T) := 
{| show := 
    let fix aux l :=
      match l with
      | nil => "nil"
      | cons x xs => "cons (" ++ show x ++ ") (" ++ aux xs ++ ")"
      end
    in aux
|}.
```

## How to Use Tactic
1. After completing the installation instructions above, make sure that you can run QuickChick for any types within your proof before the start of the current proof (see requirements above for details).
1. Import the `dilemma` tactic with the line `From Dilemma Require Import Dilemma.`. 
1. At stuck location, use tactics `dilemma. Admitted.`
1. Run `$ coqc your_file.v`.

## How to Run Examples
1. Run `$ cd ../dilemma/examples/common && coq_makefile -f _CoqProject -o Makefile` 
1. Run in the same folder `$ make && make install`. This includes a variety of decidability proofs that are used in the test cases, as well as some definitions. They are included here to avoid overfilling the test files.
1. Then, in the example folder run `coqc` to run that test. For example, `cd ../dilemma/examples && coqc selection_e1.v` will run the test found in that file. 

The expected output (in the command line) from running `$ cd ../dilemma/examples && coqc selection_e1.v` is listed below. There will be a file called `log_for_selection_e11.txt` that also includes results:

```
STARTING TO RUN LEMMA SYNTHESIS
CORES BEING USED: __

Gathering proof context and relevant information...

Syntactically simplifying the assumptions...
Gathered proof context, beginning to analyze...

Checking for contradiction in assumptions...
[NO CONTRADICTION DETECTED IN ASSUMPTIONS!]

Checking for contradiction in assumptions...
[GOAL IS SATISIABLE!]

Created variables representing generalized subterms.
Time Elapsed From Start: __ seconds

Creating Generalizations...
Reducing original proof context to include only the necesary information...
Reducing generalizations to include only necessary info...

Generalizations to analyze: 3
Time Elapsed From Start: __ seconds

Generating examples using QuickChick on proof state (in parallel)...
        __ Examples for Execution 0
        __ Examples for Execution 2
        __ Examples for Execution 1
Extracting examples to OCaml (in parallel)... 
Examples for each generalization extracted to OCaml
Time Elapsed From Start: __ seconds

Analyzing Each Generalization in parallel...
Finished analyzing generalizations:
Label: 0
Generalization Count: 0
Assumptions: 
 -- (select n x = (m, y))
Goal: (length x = length y)
Case: Valid and Un-Generalized

Label: 1
Generalization Count: 1
Assumptions: 
 -- (select n x = (m, y))
 -- [+](length y = gv1)
Goal: (length x = gv1)
Case: Invalid and Generalized

Label: 2
Generalization Count: 1
Assumptions: 
 -- (select n x = (m, y))
 -- [+](length x = gv0)
Goal: (gv0 = length y)
Case: Invalid and Generalized

Time Elapsed From Start: __ seconds
-------------------- SYNTHESIZING --------------------
Preparing synthesis problems for each generalization...
Time Elapsed From Start: __ seconds

Enumerating terms for each synthesis problem...
Time Elapsed From Start: __ seconds

Extracting relevant information to OCaml...
Time Elapsed From Start: __ seconds

Extraction complete! Time to run...
Time Elapsed From Start: __ seconds

Synthesizer ran, now processing results...

Synthesis complete!
Time Elapsed From Start: __ seconds

-------------------- CANDIDATE CONSTRUCTION --------------------
Extracting implications to OCaml to check validity consistent with examples...
[Running Extraction for Execution 0]
[Running Extraction for Execution 1]
[No Candidates from Execution 1]
[Running Extraction for Execution 2]
[Extraction Complete for Execution 0] Time Elapsed From Start: __ seconds
[Execution 0] Checking that implications hold under the greater example set...
[Extraction Complete for Execution 2] Time Elapsed From Start: __ seconds
[Execution 2] Checking that implications hold under the greater example set...
[Execution 0] Finished checking implications!
[Execution 2] Finished checking implications!
[Validity Check Complete] Time Elapsed From Start: __ seconds

Checking that the weakening is not trivial...
[Weakening Trivial Check Complete] Time Elapsed From Start: __ seconds

Checking that the weakening is not provably equivalent to the goal...
[Goal Check Complete] Time Elapsed From Start: __ seconds

Checking that all lemmas are valid with QuickChick (double check)...
[QuickChick Check Complete] Time Elapsed From Start: __ seconds


-------------------- RESULTS --------------------
(select n x = (m, y) -> length x = length y)

(select n x = (m, y) -> Permutation (m :: y) (n :: x))
(Permutation (m :: y) (n :: x) -> length x = length y)

(select n x = (m, y) -> Permutation (n :: x) (m :: y))
(Permutation (n :: x) (m :: y) -> length x = length y)

Number of Result Pairs Returned (before QuickChick): 3

Time Elapsed From Start: __ seconds
```

_Note, underlines (`__`) are used to be place holders for values that are non-deterministic (runtime or number of examples generated, etc). The runtime on my computer for the most recent run was about 70.4 seconds for this example (that is the whole program returned by after 66.4 seconds)._

## Common Issues
- If you get a **Dynlink error** like this when calling dune build (specifically after installing libraries or calling opam update/upgrade): `File "./theories/LFindToo.v", line 1, characters 0-39:
Error:
Dynlink error: error loading shared library: Dynlink.Error (Dynlink.Cannot_open_dll "Failure(\"dlopen({some path}/.opam/default/lib/coq/../coq-core/../dilemma/plugin/lfindtoo.cmxs, 0x000A): symbol not found in flat namespace '_camlSerapi__Serapi_protocol.exec_cmd_5812'\")")`, then you should go the hidden `.opam` folder and delete the folder `/default/lib/dilemma`. Note, in this case the switch is `default` (this is seen in the error and in the folder path you should delete) -- if you followed the instructions above and named the switch `dilemma`, you should see "dilemma" instead of "default"

## OOPSLA 2025 Submission
As mentioned above, `dilemma` was developed as an implementation of the lemma synthesis techniques described in **TBD link 1** (which appears in OOPSLA 2025). The benchmarks which we evaluated `dilemma` on can be found in the following repo: **TBD link benchmark repo**. We've isolated a branch of this repo titled `OOPSLA-2025` which reflects the version of `dilemma` which implements the techniques described in the OOPSLA 2025 paper listed above (in the case of any future updates or additions made to the tool).