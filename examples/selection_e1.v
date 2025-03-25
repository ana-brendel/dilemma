From Dilemma Require Import Dilemma.

Require Import dilemma_testing.Definitions.
Require Import dilemma_testing.Decide.

(* These specify the libraries of functions that should be considered during synthesis that 
    are not defined within the above libraries. *)
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation. 

Theorem main : forall (x y : list nat) (n m : nat), select n x = (m,y) -> length x = length y.
Proof. 
    intros. 
    dilemma.
    Admitted.