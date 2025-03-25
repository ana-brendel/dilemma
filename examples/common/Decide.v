From QuickChick Require Import QuickChick.
From dilemma_testing Require Import Definitions.

Require Import String. Open Scope string.

(* ************************** [ NAT ] *************************** *)
Derive Show for nat.
Derive Arbitrary for nat.
Instance Dec_Eq_nat : Dec_Eq nat.
Proof. dec_eq. Qed.

(* ************************** [ BOOL ] *************************** *)
Derive Show for bool.
Derive Arbitrary for bool.
Instance Dec_Eq_bool : Dec_Eq bool.
Proof. dec_eq. Qed.

(* ************************** [ LIST ] *************************** *)
Instance show_list {T} `{_ : Show T} : Show (list T) := 
{| show := 
    let fix aux l :=
      match l with
      | nil => "nil"
      | cons x xs => "cons (" ++ show x ++ ") (" ++ aux xs ++ ")"
      end
    in aux
|}.
Derive Arbitrary for list.
Instance Dec_Eq_list {T} `{_ : Dec_Eq T}  : Dec_Eq (list T).
Proof. dec_eq. Qed.


(* ************************** [ OPTION ] *************************** *)
Instance show_option {T} `{_ : Show T} : Show (option T) := 
{| show := 
    let fix aux l :=
      match l with
      | None => "None"
      | Some x => "Some (" ++ show x ++ ")"
      end
    in aux
|}.

(* ********************************************************************** *)
(* ************************** [ PERMUTATION ] *************************** *)
(* ********************************************************************** *)

Notation "a :: b"  := (cons a b).
Notation "[]"  := (nil).

Fixpoint inb {T} `{_ : Dec_Eq T} (x : T) (n : list T) : bool :=
match n with
| [] => false
| hd :: tl => if (dec_eq x hd) then true else (inb x tl)
end.

Fixpoint remove {T} `{_ : Dec_Eq T} (x : T) (n : list T) : list T :=
match n with
| [] => []
| hd :: tl => if (dec_eq x hd) then tl else  hd :: (remove x tl)
end.

Fixpoint isPerm {T} `{_ : Dec_Eq T} (n m : list T) : bool :=
match n,m with
| [],[] => true
| [], _ => false
| x :: n', _ => if (inb x m) then (isPerm n' (remove x m)) else false
end.

Lemma remove_result {T} `{_ : Dec_Eq T} (x : T) (n : list T) : inb x n = true -> 
  exists p q, n = app p (x :: q) /\ remove x n = app p q.
Proof. 
intros. induction n.
- simpl in H0. discriminate H0.
- unfold remove. destruct (dec_eq x a). 
+ rewrite <- e. exists []. exists n. simpl. auto.
+ assert (H1: inb x n = true).
* induction n. simpl in H0. destruct (dec_eq x a). rewrite e in n0. contradiction. discriminate H0.
unfold inb in H0. destruct (dec_eq x a). rewrite e in n0. contradiction. fold inb in H0. destruct (dec_eq x a0).
rewrite e. simpl. destruct (dec_eq a0 a0). auto. contradiction. unfold inb. destruct (dec_eq x a0). auto. fold inb. auto.
* fold remove. 
assert (G1: (exists r p q: list T, a :: n = app (app r p) (x :: q) /\ a :: remove x n = (app (app r p) q)) -> 
    (exists p q : list T, a :: n = app p (x :: q) /\ a :: remove x n = (app p q))).
** intros. inversion H2. inversion H3. inversion H4. exists (app x0 x1). exists x2. apply H5.
** apply G1. exists (a :: []). simpl. 
  assert (G2: (exists p q : list T, n = (app p (x :: q)) /\ remove x n = (app p q)) 
          -> (exists p q : list T, a :: n = a :: (app p (x :: q)) /\ a :: remove x n = a :: (app p q))).
*** intros. inversion H2. inversion H3. exists x0. exists x1. destruct H4. split. f_equal. auto. f_equal. auto.
*** simpl. apply G2. apply IHn. apply H1.
Qed.

Lemma if_isPerm_Permutation_eq {T} `{_ : Dec_Eq T} (n m : list T) : isPerm n m = true -> Permutation n m.
Proof.
generalize dependent m. induction n.
- intros. destruct m. apply perm_nil. simpl in H0. discriminate H0.
- induction m.
  * intros. simpl in H0. discriminate H0.
  * intros. unfold isPerm in IHm. unfold isPerm in H0.  
    assert (G : inb a m = true -> forall a0, inb a (a0 :: m) = true).
    ** intros. induction m. simpl in H1. discriminate H1. destruct (dec_eq a a1).
        rewrite e. simpl. destruct (dec_eq a1 a1). reflexivity. contradiction.
        unfold inb. destruct (dec_eq a a1). reflexivity. unfold inb in H1. apply H1.
    ** assert (R: inb a m = true -> exists p q, m = app p (a :: q) /\ remove a m = app p q). apply remove_result. destruct (inb a m).
        -- assert (G1: inb a (a0 :: m) = true).
        + apply G. reflexivity.
        + rewrite G1 in H0. fold isPerm in IHm. fold isPerm in H0. apply IHn in H0.
          destruct (dec_eq a a0).
          ++ rewrite e. apply perm_skip. rewrite e in H0. simpl in H0. destruct (dec_eq a0 a0). apply H0.
              contradiction.
          ++ simpl in H0. destruct (dec_eq a a0). rewrite e in n0. contradiction. 
              assert (G2 : Permutation n (a0 :: remove a m) -> Permutation (a :: n) (a0 :: a :: remove a m)).
              +++ intros. replace (a0 :: a :: remove a m) with (app (a0 :: []) (a :: remove a m)).
                  apply Permutation_cons_app. simpl. auto. simpl. reflexivity.
              +++ assert (RR: exists p q, m = app p (a :: q) /\ remove a m = app p q). apply R; reflexivity.
                  apply G2 in H0. destruct RR. destruct H1. destruct H1. rewrite H2 in H0. rewrite H1.
                  assert (P : Permutation (a0 :: x ++ a :: x0) (a0 :: a :: x ++ x0)).
                  *** apply perm_skip. apply Permutation_sym. apply Permutation_middle.
                  *** apply Permutation_sym in P. apply Permutation_trans with (l' := (app (a0 :: a :: x) x0)). 
                      simpl. apply H0. apply P.
        -- assert (Q: inb a (a0 :: m) = true -> exists p q, (a0 :: m) = app p (a :: q) /\ remove a (a0 :: m) = app p q). apply remove_result. 
          destruct (inb a (a0 :: m)).
          + fold isPerm in H0. apply IHn in H0. 
              assert (G1 : Permutation n (remove a (a0 :: m)) -> Permutation (a :: n) (a :: remove a (a0 :: m))).
              ++ intros. apply perm_skip. apply H0.
              ++ assert (RR: exists p q, (a0 :: m) = app p (a :: q) /\ remove a (a0 :: m) = app p q). apply Q; reflexivity.
                  apply G1 in H0. destruct RR. destruct H1. destruct H1. rewrite H2 in H0. rewrite H1.
                  assert (P : Permutation (a :: x ++ x0) (x ++ a :: x0)). apply Permutation_middle. 
                  apply Permutation_trans with (l' := app (a :: x) x0). auto. auto.
          + discriminate H0.
Qed.

Lemma helper {T} `{_ : Dec_Eq T} (t : T) (x y : list T) : inb t x = false -> remove t (x ++ y) = app x (remove t y).
Proof.
generalize dependent t. induction x.
- intros. simpl. reflexivity.
- intros. unfold remove. simpl. destruct (dec_eq t a). rewrite e in H0. simpl in H0. destruct (dec_eq a a).
  discriminate H0. contradiction. fold remove. f_equal. apply IHx. inversion H0. destruct (dec_eq t a). 
  discriminate H2. reflexivity.
Qed.

Lemma helper2 {T} `{_ : Dec_Eq T} (t : T) (x y : list T) : inb t x = true -> remove t (x ++ y) = app (remove t x) y.
Proof.
generalize dependent t. induction x.
- intros. simpl in H0. discriminate H0.
- intros. simpl. destruct (dec_eq t a). auto. simpl. f_equal. apply IHx. inversion H0. destruct (dec_eq t a). 
  rewrite e in n. contradiction. reflexivity.
Qed.

Lemma isPerm_inb {T} `{_ : Dec_Eq T} (a : T) (n m : list T) : isPerm (a :: n) m = true -> inb a m = true.
Proof. intros. simpl in H0. destruct (inb a m). reflexivity. discriminate H0. Qed.

Lemma isPerm_inb_conv {T} `{_ : Dec_Eq T} (a : T) (n m : list T) : isPerm m (a :: n) = true -> inb a m = true.
Proof.
intros. generalize dependent n. induction m.
+ intros. simpl in H0. discriminate H0.
+ intros. simpl in H0. simpl. destruct (dec_eq a a0).
- reflexivity.
- destruct (dec_eq a0 a).
-- rewrite e in n0. contradiction.
-- destruct (inb a0 n). apply IHm with (n := remove a0 n). auto. discriminate H0.
Qed.

Lemma comm_destruct {T} `{_ : Dec_Eq T} (a : T) (l l' : list T) : isPerm l (a :: l') = true -> isPerm (remove a l) l' = true.
Proof. 
generalize dependent l'. induction l.
- intros. simpl in H0. discriminate H0.
- intros. inversion H0. destruct (dec_eq a0 a).
-- rewrite e. simpl. destruct (dec_eq a a). auto. contradiction.
-- simpl. destruct (dec_eq a a0). rewrite e in n. contradiction. 
  simpl. destruct (inb a0 l'). rewrite H2. auto. reflexivity.
Qed.

Lemma comm_destruct_inv {T} `{_ : Dec_Eq T} (a : T) (l l' : list T) : inb a l = true /\ isPerm (remove a l) l' = true -> isPerm l (a :: l') = true.
Proof.
intros. destruct H0. generalize dependent a. generalize dependent l'. induction l.
- intros. simpl in H0. discriminate H0.
- intros. simpl. simpl in H1. destruct (dec_eq a a0).
* rewrite e in H1. destruct (dec_eq a0 a0). auto. contradiction.
* simpl in H0. destruct (dec_eq a0 a). rewrite e in n. contradiction. simpl in H1. destruct (inb a l').
-- apply IHl. auto. auto.
-- discriminate H1.
Qed.

Lemma isPerm_comm_imp {T} `{_ : Dec_Eq T} (l l' : list T) : isPerm l l' = true -> isPerm l' l = true.
Proof.
intros. generalize dependent l'. induction l.
- destruct l'. auto. intros. simpl in H0. discriminate H0.
- induction l'. intros. simpl in H0. discriminate H0.
destruct (dec_eq a0 a).
-- intros. rewrite e. simpl. rewrite e in H0. simpl in H0. destruct (dec_eq a a). auto. contradiction.
-- intros. assert (A_in: inb a l' = true). apply isPerm_inb in H0. simpl in H0. destruct (dec_eq a a0). rewrite e in n. contradiction. auto.
  assert (A0_in: inb a0 l = true). apply isPerm_inb_conv in H0. simpl in H0. destruct (dec_eq a0 a). rewrite e in n. contradiction. auto.
  apply comm_destruct_inv. split.
  * simpl. destruct (dec_eq a a0). rewrite e in n. contradiction. auto.
  * apply IHl. simpl in H0. simpl. destruct (dec_eq a a0). rewrite e in n. contradiction. rewrite A_in in H0. auto.
Qed.

Theorem contrapositive : forall p q:bool, (p = true -> q = true) ->(q = false -> p = false).
Proof.
intros. destruct p.
- destruct q. discriminate H0. assert (T: true = true). reflexivity. apply H in T. discriminate T.
- reflexivity.
Qed.

Lemma isPerm_comm {T} `{_ : Dec_Eq T} (l l' : list T) : isPerm l l' = isPerm l' l.
Proof. 
assert (G: isPerm l l' = true -> isPerm l' l = true). apply isPerm_comm_imp. 
assert (G': isPerm l l' = false -> isPerm l' l = false). apply contrapositive. apply isPerm_comm_imp. destruct (isPerm l l').
symmetry. apply G. reflexivity. symmetry. apply G'. reflexivity. Qed.

Theorem easy : forall p q r:Prop, (p->q\/r)->(~q/\~r->~p).
Proof. intros. intro. apply H0. destruct H. auto. destruct H0. contradiction. auto.  Qed.

Lemma contrapositive2 : forall p q r: bool, (r = true -> p = true \/ q = true) -> (p = false /\ q = false -> r = false).
Proof. 
intros p q r H0. 
assert (R: (r <> true) <-> (r = false)). split. apply not_true_is_false. unfold not. intros. rewrite H in H1. discriminate H1.
assert (Q: (q <> true) <-> (q = false)). split. apply not_true_is_false. unfold not. intros. rewrite H in H1. discriminate H1.
assert (P: (p <> true) <-> (p = false)). split. apply not_true_is_false. unfold not. intros. rewrite H in H1. discriminate H1.
rewrite <- R. rewrite <- Q. rewrite <- P. apply easy. auto. 
Qed.

Lemma destruct_inb {T} `{_ : Dec_Eq T} (a: T) (x y : list T) : inb a x = true \/ inb a y = true <-> inb a (app x y) = true.
Proof.
split.
- intros. destruct H0. 
* induction x. discriminate H0.
  simpl. simpl in H0. destruct (dec_eq a a0). auto. apply IHx. auto. 
* induction x. simpl. auto. 
  assert (A: inb a (a0 :: x) = true -> remove a ((a0 :: x) ++ y) = app (remove a (a0 :: x)) y). apply helper2. destruct (inb a (a0 :: x)).
  -- assert (A': true = true). auto. apply A in A'. simpl. destruct (dec_eq a a0). auto. auto.
  -- simpl. destruct (dec_eq a a0). auto. auto.
- intros. assert (G: inb a x = false /\ inb a y = false -> inb a (x ++ y) = false). 
  apply contrapositive2.
  + intros. destruct H1. 
  * induction x. simpl. right. auto.
    simpl. simpl in H0. destruct (dec_eq a a0). auto. apply IHx. auto. 
  + destruct (inb a x). auto. destruct (inb a y). auto. assert (G': false = false /\ false = false). split; auto; auto. apply G in G'. 
    rewrite G' in H0. discriminate H0.
Qed.

Lemma destruct_inb_neg {T} `{_ : Dec_Eq T} (a: T) (x y : list T) : inb a x = false /\ inb a y = false <-> inb a (app x y) = false.
Proof. assert (P: inb a x = true \/ inb a y = true <-> inb a (app x y) = true). apply destruct_inb. split. 
- intros. destruct H0. destruct (inb a (x ++ y)). assert (P' : true = true). auto. apply P in P'. destruct P'. rewrite H0 in H2. discriminate.
  rewrite H1 in H2. discriminate H2. auto.
- intros. destruct (inb a x). assert (P' : true = true \/ inb a y = true). left. auto. apply P in P'. rewrite H0 in P'. discriminate P'.
  split. reflexivity. destruct (inb a y). assert (P' : false = true \/ true = true). right. auto. apply P in P'. rewrite P' in H0. discriminate H0.
  reflexivity.
Qed.

Lemma comm_in_app {T} `{_ : Dec_Eq T} (a : T) (y z : list T) : inb a (app y z) = inb a (app z y).
Proof.
assert (P: inb a y = true \/ inb a z = true <-> inb a (app y z) = true). apply destruct_inb.
assert (N: inb a y = false /\ inb a z = false <-> inb a (app y z) = false). apply destruct_inb_neg. 
- destruct (inb a (y ++ z)). 
  * assert (P': true = true). auto. apply P in P'. apply or_comm in P'. apply destruct_inb in P'. symmetry. auto.
  * assert (N': false = false). auto. apply N in N'. apply and_comm in N'. apply destruct_inb_neg in N'. symmetry. auto.
Qed.

Lemma nat_strong_ind: forall (P:nat -> Prop),
P 0 -> (forall n:nat, (forall (m:nat), m <= n -> P m) -> P (S n)) -> forall n, P n.
Proof.
intros P B IHs n. destruct n. exact B. apply IHs. induction n.
intros. replace m with 0. apply B. inversion H. auto. intros. assert (m <= n \/ m = S n) as J. inversion H. right. auto. left. auto.
destruct J as [J|J]. apply IHn. auto. rewrite J. apply IHs. apply IHn.
Qed.

Lemma length_strong_ind: forall (A:Type) (P:list A -> Prop),
P nil -> (forall (n:nat) (k:list A), (forall (l:list A), List.length l <= n -> P l) -> List.length k = S n -> P k) -> forall l, P l.
Proof. 
intros A P B IH. assert (forall (n:nat) (l:list A), List.length l <= n -> P l) as G.
intro n. induction n as [| n IHS] using nat_strong_ind.
  intros. inversion H. destruct l. apply B. simpl in H1. discriminate H1.
  intros. assert (List.length l <= n \/ List.length l = S n) as G. inversion H. right. auto. left. auto.
destruct G as [G|G]. apply IHS with (m:=n); auto. apply IH with (n:=n); try exact G.
  intro k. apply IHS with (m:=n) (l:=k). auto.
  intro l. apply G with (n:= List.length l); auto.
Qed.

Lemma remove_length_less {T} `{_ : Dec_Eq T} (t : T) (x : list T) : List.length (remove t x) <= List.length x.
Proof. 
induction x.
- simpl. auto.
- simpl. destruct (dec_eq t a). auto. simpl. apply le_n_S. auto.
Qed.
Lemma swap_concat {T} `{_ : Dec_Eq T} (x y z : list T) : isPerm x (y ++ z) = true -> isPerm x (z ++ y) = true.
Proof.
generalize dependent y; generalize dependent z. induction x using length_strong_ind.
- intros. destruct y. destruct z. simpl. reflexivity. simpl in H0. discriminate H0. simpl in H0. discriminate H0.
- intros. destruct x.
  -- simpl in H1. discriminate H1.
  -- inversion H1. 
    assert (InBoth : inb t (z ++ y) = true). apply destruct_inb. apply or_comm. apply destruct_inb. auto. apply isPerm_inb in H2. auto.
    simpl. simpl in H2. rewrite InBoth. rewrite comm_in_app in InBoth. rewrite InBoth in H2.
    assert (InY': inb t y = false -> remove t (y ++ z) = app y (remove t z)). apply helper.
    assert (InY: inb t y = true -> remove t (y ++ z) = app (remove t y) z). apply helper2.
    assert (InZ': inb t z = false -> remove t (z ++ y) = app z (remove t y)). apply helper.
    assert (InZ: inb t z = true -> remove t (z ++ y) = app (remove t z) y). apply helper2.
    assert (FormZ : inb t z = true -> exists p q, z = app p (t :: q) /\ remove t z = app p q). apply remove_result. 
    assert (FormY : inb t y = true -> exists p q, y = app p (t :: q) /\ remove t y = app p q). apply remove_result. 
    assert (InBothNeg : inb t y = true \/ inb t z = true). apply destruct_inb. auto.
    destruct (inb t y).
    * assert (InYTrue : true = true). auto. apply InY in InYTrue. destruct (inb t z).
      ** assert (InZTrue : true = true). auto. apply InZ in InZTrue. 
        assert (FormZ' : true = true). auto. apply FormZ in FormZ'. assert (FormY' : true = true). auto. apply FormY in FormY'.
        inversion FormZ'. inversion H3. inversion FormY'. inversion H6. destruct H5. destruct H7.
        rewrite InZTrue. rewrite H7.
        rewrite InYTrue in H2; rewrite H5 in H2. rewrite List.app_assoc.
        apply H0 with (y := t :: x3) (z := app (remove t z) x2). rewrite H4. auto. rewrite List.app_assoc in H2. apply H0 in H2. rewrite H9 in H2. rewrite H8.
        rewrite <- List.app_assoc. rewrite <- List.app_assoc in H2.
        simpl. simpl in H0. assert (TinX : inb t x = true). 
        ++ apply isPerm_inb_conv in H2. auto.
        ++ apply comm_destruct_inv. split. auto. simpl in H2. assert (PreCond: isPerm (remove t x) (app (app x1 x2) (app x3 x0)) = true).
            apply comm_destruct. rewrite <- List.app_assoc. auto. rewrite List.app_assoc.
            apply H0 with (y := (app x1 x2)). rewrite <- H4. apply remove_length_less. auto.
        ++ rewrite H4. auto.
      ** assert (NotInZ : false = false). auto. apply InZ' in NotInZ. rewrite NotInZ. apply H0. rewrite H4. auto. rewrite <- InYTrue. auto.
    * assert (NotInY : false = false). auto. apply InY' in NotInY. destruct (inb t z).
      ** assert (InZTrue : true = true). auto. apply InZ in InZTrue. rewrite InZTrue. apply H0. rewrite H4. auto. rewrite <- NotInY. auto.
      ** destruct InBothNeg. discriminate H3. discriminate H3.
Qed.

Lemma add_to_front_first {T} `{_ : Dec_Eq T} (a: T) (x x1 x2 : list T) : isPerm x (x1 ++ x2) = true -> isPerm (a :: x) (x1 ++ a :: x2) = true.
Proof. intros. apply swap_concat. simpl. destruct dec_eq. apply swap_concat. auto. contradiction. Qed.

Lemma add_to_middle {T} `{_ : Dec_Eq T} (a: T) (y x1 x2 : list T) : isPerm (a :: (x1 ++ x2)) y = true -> isPerm (x1 ++ a :: x2) y = true.
Proof. 
generalize dependent x1. generalize dependent x2. generalize dependent a. induction y.
- intros. apply isPerm_comm_imp; apply isPerm_comm_imp in H0. simpl in H0. discriminate H0.
- intros. apply isPerm_comm_imp; apply isPerm_comm_imp in H0. destruct (dec_eq a a0). 
* rewrite e in H0. assert (Q: inb a x1 = true -> exists p q, x1 = app p (a :: q) /\ remove a x1 = app p q). apply remove_result.
assert (P: inb a x1 = false -> remove a (x1 ++ (a0 :: x2)) = app x1 (remove a (a0 :: x2))). apply helper. simpl.
destruct (inb a x1).
** assert (Q': true = true). reflexivity. apply Q in Q'. inversion Q'. inversion H1. destruct H2. rewrite e. apply add_to_front_first.
  simpl in H0. destruct (dec_eq a0 a0). auto. contradiction.
** assert (P': false = false). reflexivity. apply P in P'. rewrite P'. replace (inb a (x1 ++ a0 :: x2)) with true. 
  rewrite e. simpl. simpl in H0. destruct (dec_eq a0 a0). auto. contradiction.
  rewrite e. symmetry. simpl. apply destruct_inb. right. simpl. destruct (dec_eq a0 a0). auto. contradiction.
* inversion H0. simpl. simpl in H0. destruct (dec_eq a a0). rewrite e in n. contradiction. 
  assert (G: inb a (x1 ++ x2) = true <-> inb a (x1 ++ a0 :: x2) = true).
  split. intros. apply destruct_inb. inversion H1. simpl. destruct (dec_eq a a0). rewrite e in n; contradiction. rewrite H4. apply destruct_inb. auto.
  intros. apply destruct_inb in H1. destruct H1. apply destruct_inb. left; auto. simpl in H1. destruct (dec_eq a a0). rewrite e in n; contradiction.
  apply destruct_inb. right; auto.
  assert (A:  inb a x1 = true \/ inb a x2 = true <-> inb a (app x1 x2) = true). apply destruct_inb.
  destruct (inb a (app x1 x2)).
  -- replace (inb a (x1 ++ a0 :: x2)) with true. rewrite H0. assert (TT: true = true). auto. apply A in TT. 
      assert (I: inb a x1 = true -> exists p q, x1 = app p (a :: q) /\ remove a x1 = app p q). apply remove_result.
      assert (J: inb a x1 = true -> remove a (x1 ++ (a0 :: x2)) = app (remove a x1) (a0 :: x2)). apply helper2.
      assert (K: inb a x1 = true -> remove a (x1 ++ x2) = app (remove a x1) x2). apply helper2.
      assert (L: inb a x1 = false -> remove a (x1 ++ (a0 :: x2)) = app x1 (remove a (a0 :: x2))). apply helper. 
      assert (M: inb a x1 = false -> remove a (x1 ++ x2) = app x1 (remove a x2)). apply helper. destruct (inb a x1).
  --- assert (H1: true = true). auto. apply I in H1.
      assert (H1': true = true). auto. apply J in H1'. assert (H1'': true = true). auto. apply K in H1''.
      inversion H1; inversion H3. destruct H4. 
      rewrite H1'. apply isPerm_comm_imp. apply IHy. apply isPerm_comm_imp. rewrite <- H1''. auto.
  --- assert (L': false = false). auto. apply L in L'. simpl in L'. destruct (dec_eq a a0). rewrite e in n0. contradiction. rewrite L'.
      apply isPerm_comm_imp. apply IHy. assert (M': false = false). auto. apply M in M'. rewrite M' in H0. apply isPerm_comm_imp. auto.
  --- symmetry. apply destruct_inb. simpl. destruct (dec_eq a a0). rewrite e in n0; contradiction. apply A. auto.
  -- discriminate H0.
Qed.

Lemma remove_middle_isPerm {T} `{_ : Dec_Eq T} (a: T) (x x0 x1 x2 : list T) : isPerm (x1 ++ x2) (x ++ x0) = true -> isPerm (x1 ++ a :: x2) (x ++ a :: x0) = true.
Proof. intros. apply add_to_middle. apply add_to_front_first. auto. Qed.

Lemma if_Permutation_isPerm_eq {T} `{_ : Dec_Eq T} (n m : list T) : Permutation n m -> isPerm n m = true.
Proof.
intros. induction H0.
- simpl; reflexivity.
- simpl. destruct (dec_eq x x). auto. contradiction.
- simpl. destruct (dec_eq y x). 
-- rewrite e. simpl. destruct (dec_eq x x). induction l. reflexivity. simpl. destruct (dec_eq a a).
  auto. contradiction. contradiction.
-- destruct (dec_eq y y). simpl. destruct (dec_eq x x). induction l. reflexivity. simpl. destruct (dec_eq a a).
    auto. contradiction. contradiction. contradiction.
- generalize dependent l. generalize dependent l''. induction l'.
-- intros. destruct l. destruct l''. reflexivity. simpl in IHPermutation2. discriminate IHPermutation2. simpl in IHPermutation1. discriminate IHPermutation1.
-- intros. assert (Q: inb a l'' = true -> exists p q, l'' = app p (a :: q) /\ remove a l'' = app p q). apply remove_result.
  assert (R: inb a l = true -> exists p q, l = app p (a :: q) /\ remove a l = app p q). apply remove_result. 
  assert (Q' : inb a l'' = true). apply isPerm_inb with (n := l'). auto. inversion Q'. apply Q in Q'.
  assert (R' : inb a l = true). apply isPerm_inb_conv with (n := l'). auto. apply R in R'.
  inversion Q'. inversion H0. destruct H2. inversion R'. inversion H4. destruct H5.
  apply comm_destruct in IHPermutation1. simpl in IHPermutation2. destruct (inb a l'').
  rewrite H6 in IHPermutation1. rewrite H3 in IHPermutation2.
  rewrite H5 in H0_. rewrite H2 in H0_0.
  apply Permutation_cons_app_inv in H0_0.
  apply Permutation_sym in H0_. apply Permutation_cons_app_inv in H0_. apply Permutation_sym in H0_.
  rewrite H5. rewrite H2. apply remove_middle_isPerm. apply IHl'. auto. auto. auto. auto.
  discriminate H1.
Qed.

Lemma Permutation_isPerm_eq {T} `{_ : Dec_Eq T} (n m : list T) : Permutation n m <-> isPerm n m = true.
Proof. split. apply if_Permutation_isPerm_eq. apply if_isPerm_Permutation_eq. Qed.

Instance Permutation_dec {T} `{_ : Dec_Eq T} (n m : list T) : Dec (Permutation n m).
Proof.
dec_eq. assert (P: Permutation n m <-> isPerm n m = true). apply Permutation_isPerm_eq. destruct (isPerm n m).
- left. apply P. auto.
- right. unfold not. intro. apply P in H0. discriminate H0.
Qed.


(* ************************************************************** *)
(* ************************** [ SORT ] ************************** *)
(* ************************************************************** *)

Fixpoint sorted_bool (l : list nat) : bool :=
  match l with 
  | [] => true
  | a :: l' => 
    match l' with
    | [] => true
    | b :: _ => andb (Nat.leb a b) (sorted_bool l')
  end
end.

Lemma if_sorted_bool_eq (l : list nat) : sorted l -> sorted_bool l = true.
Proof.
  intros. induction l. auto. destruct l. auto.
  unfold sorted_bool. fold sorted_bool. simpl in IHl.
  assert (Q : Nat.leb a n = false -> ~ (le a n)). intros. unfold not. intros. 
    apply leb_correct in H1. rewrite H0 in H1. discriminate H1.
  destruct (Nat.leb a n).
  * rewrite andb_true_l. apply IHl. inversion H. auto.
  * inversion H. assert (Q' : false = false). auto. apply Q in Q'. contradiction.
Qed.

Lemma fi_sorted_bool_eq (l : list nat) : sorted_bool l = true -> sorted l.
Proof.
  intros. induction l.
  - apply sorted_nil.
  - destruct l.
  -- apply sorted_1.
  -- apply sorted_cons. inversion H. 
  assert (Q : Nat.leb a n = true -> (le a n)). apply leb_complete.
  apply Q. destruct (Nat.leb a n). auto. rewrite andb_false_l in H1. discriminate H1.
  apply IHl. inversion H. rewrite H1. symmetry in H1. apply andb_true_eq in H1. destruct H1.
  simpl. auto.
Qed.

Theorem sorted_bool_eq (l : list nat) : sorted_bool l = true <-> sorted l.
Proof. split. apply fi_sorted_bool_eq. apply if_sorted_bool_eq. Qed.

Instance sorted_dec (l : list nat) : Dec (sorted l).
Proof.
  dec_eq. assert (P: sorted_bool l = true <-> sorted l). apply sorted_bool_eq.
  destruct (sorted_bool l). left. apply P. auto. 
  right. unfold not. intros. apply P in H. discriminate H.
Qed.

(* Lemma if_sortedd_sorted_eq (l : list nat) : sortedd l -> sorted l.
Proof.
  induction l.
  * constructor.
  * unfold sortedd in *. intro H. 
    destruct l; constructor.
    + apply (H 0 1). simpl. auto. reflexivity. reflexivity.
    + apply IHl.
      intros. apply (H (S i) (S j)).
      simpl in *. apply lt_n_S in H0. auto. simpl. auto. simpl. auto.
Qed. *)

(* Lemma if_sorted_sortedd_eq (l : list nat) : sorted l -> sortedd l.
Proof.
  intros. unfold sortedd. 
  induction l. destruct i. simpl. intros. discriminate H1. simpl. intros. discriminate H1.
  induction H; intros.
  * simpl in H. destruct i. 
    simpl in H0; discriminate H0.
    simpl in H0; discriminate H0.
  * simpl in H0. destruct i. destruct j.
    inversion H. simpl in H1. destruct j.
    simpl in H1; discriminate H1.
    simpl in H1; discriminate H1.
    simpl in H0. destruct i.
    simpl in H0; discriminate H0.
    simpl in H0; discriminate H0.
  * destruct i,j.
  + inversion H1.
  + apply le_trans with y. simpl in H2. inversion H2. rewrite <- H5. auto.
    destruct j. simpl in H3. inversion H3. rewrite <- H5. auto.
    specialize (IHsorted 0 (S j)). apply IHsorted. apply lt_0_Sn. reflexivity. simpl.
    simpl in H3. auto.
  + inversion H1.
  + simpl in H2. simpl in H3. apply lt_S_n in H1. apply IHsorted with (i:=i) (j:=j).
    auto. auto. auto.
Qed. *)

(* Theorem sorted_eq_sortedd (l : list nat) : sorted l <-> sortedd l.
Proof. split. apply if_sorted_sortedd_eq. apply if_sortedd_sorted_eq. Qed. *)

(* Theorem sortedd_eq_bool (l : list nat) : sortedd l <-> sorted_bool l = true.
Proof. split. 
  intros. apply sorted_bool_eq. apply sorted_eq_sortedd. auto.
  intros. apply sorted_eq_sortedd. apply sorted_bool_eq. auto.
Qed. *)

(* Instance sortedd_dec (l : list nat) : Dec (sortedd l).
Proof.
  dec_eq. assert (P: sortedd l <-> sorted_bool l = true). apply sortedd_eq_bool.
  destruct (sorted_bool l). left. apply P. auto. 
  right. unfold not. intros. apply P in H. discriminate H.
Qed. *)

(* **************************************************************** *)
(* ************************** [ FORALL ] ************************** *)
(* **************************************************************** *)
(* Forall definitions and lemmas at: https://coq.inria.fr/doc/master/stdlib/Coq.Lists.List.html *)
Instance forall_dec {T} `{_ : Dec T} (f : T -> Prop) `{forall (x : T), Dec (f x)} (ls : list T) : (Dec (Forall f ls)).
Proof.
  dec_eq. induction ls.
  - left. apply Forall_nil.
  - destruct IHls.
  + assert (P: {f a} + {~ f a}). apply H0. destruct P.
  ++ left. apply Forall_cons. auto. auto.
  ++ right. unfold not. intros. unfold not in n. apply n. apply Forall_inv in H1. auto.
  + right. unfold not; intros. unfold not in n. apply n. apply Forall_inv_tail in H1. auto.
Qed.

(* ************************************************************* *)
(* ************************** [ <=* ] ************************** *)
(* ************************************************************* *)
Instance leall_dec (x : nat) (ls : list nat) : (Dec (x <=* ls)).
Proof.
  dec_eq. unfold le_all. induction ls.
  - left. apply Forall_nil.
  - pose le_dec. assert (P: {x <= a} + {~ x <= a}). apply s. destruct P.
  + destruct IHls. left. apply Forall_cons. auto. auto. right. 
    unfold not; intros.  apply Forall_inv_tail in H. contradiction.
  + right. unfold not. intros. apply Forall_inv in H. contradiction.
Qed.

Close Scope string.