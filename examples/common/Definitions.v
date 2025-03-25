Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Export Lists.List.
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Permutation.
Export ListNotations.

Inductive sorted: list nat -> Prop :=
 | sorted_nil: sorted []
 | sorted_1: forall i, sorted [i]
 | sorted_cons: forall i j l, i <= j -> sorted (j :: l) -> sorted (i :: j :: l).

Definition is_a_sorting_algorithm (f: list nat -> list nat) := forall al,
    Permutation al (f al) /\ sorted (f al).

Fixpoint select (x: nat) (l: list nat) : nat * list nat :=
  match l with
  | [] => (x, [])
  | h :: t =>
    if x <=? h
    then let (j, l') := select x t
         in (j, h :: l')
    else let (j, l') := select h t
         in (j, x :: l')
  end.

Fixpoint selsort (l : list nat) (n : nat) : list nat :=
  match l, n with
  | _, O => []  (* ran out of fuel *)
  | [], _ => []
  | x :: r, S n' => let (y, r') := select x r
                  in y :: selsort r' n'
end.

Definition selection_sort (l : list nat) : list nat := selsort l (length l).

Definition le_all x xs := Forall (fun y => x <= y) xs.
Infix "<=*" := le_all (at level 70, no associativity).

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].