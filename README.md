# Lemma Synthesis Tactic
This is the repo I'm working in to develop lemma synthesis tactic for Coq.

## Installation Instructions (as of right now...) using opam:

1. `opam update`
1. `opam switch create dilemma ocaml.5.1.1` (create new switch called lfind)
1. `opam install dune`
1. `opam install coq=8.20.1` (note, if you have issues with installing zarith.1.14 you can install zarith.1.13 prior)
1. `opam repo add coq-released https://coq.inria.fr/opam/released`
1. `opam update`
1. `opam install coq-quickchick=2.0.5`
1. `opam install parmap` (version 1.2.5)
1. `opam install coq-serapi` (version 8.20.0+0.20.0)
1. `cd .../dilemma`
1. `dune build && dune install` (you might want to build twice)

## How to Use Tactic
1. Make sure that you can run QuickChick for any types within your proof before the start of the current proof.
1. At stuck location, use tactics `dilemma. Admitted.`
1. Run `$ coqc your_file.v`.

## How to Run Examples
1. Run `$ cd ../dilemma/examples/common && coq_makefile -f _CoqProject -o Makefile` 
1. Run in the same folder `$ make && make install`. This includes a variety of decidability proofs that are used in the test cases, as well as some definitions. They are included here to avoid overfilling the test files.
1. Then, in the example folder run `coqc` to run that test. For example, `cd ../dilemma/examples && coqc selection_e1.v` will run the test found in that file. 

The expected output (in the command line) from running `$ cd ../dilemma/examples && coqc selection_e1.v` is listed below. There will be a file called `log_for_main1.txt` that also includes results:

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

_Note, underlines (`__`) are used to be place holders for values that are non-deterministic (runtime or number of examples generated). The runtime on my computer for the most recent run was about 70.4 seconds for this example (that is the whole program returned by after 70.4 seconds)._

## Common Issues
- If you get a **Dynlink error** like this when calling dune build (specifically after installing libraries or calling opam update/upgrade): `File "./theories/LFindToo.v", line 1, characters 0-39:
Error:
Dynlink error: error loading shared library: Dynlink.Error (Dynlink.Cannot_open_dll "Failure(\"dlopen({some path}/.opam/default/lib/coq/../coq-core/../dilemma/plugin/lfindtoo.cmxs, 0x000A): symbol not found in flat namespace '_camlSerapi__Serapi_protocol.exec_cmd_5812'\")")`, then you should go the hidden `.opam` folder and delete the folder `/default/lib/dilemma`