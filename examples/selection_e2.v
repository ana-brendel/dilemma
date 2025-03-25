(** * Selection:  Selection Sort *)
(* Some proofs from: https://github.com/kolya-vasiliev/verified-functional-algorithms-2019/blob/master/Selection.v *)

From Dilemma Require Import Dilemma.

Require Import dilemma_testing.Definitions.
From dilemma_testing Require Import Decide.

(* These specify the libraries of functions that should be considered during synthesis that 
    are not defined within the above libraries. *)
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation. 

(* ################################################################# *)

Lemma select_smallest: forall al bl x y, select x al = (y, bl) -> y <=* bl.
Proof. 
    intros al. induction al.
    - intros. inversion H. unfold le_all. apply Forall_nil.
    - intros. unfold select in H. bdestruct (x <=? a).
    -- fold select in H. destruct (select x al) eqn:Q. inversion Q. apply IHal in Q.
    inversion H. rewrite <- H3. unfold le_all. apply Forall_cons. 
    dilemma. Admitted.