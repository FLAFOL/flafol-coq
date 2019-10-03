Require Export Coq.Arith.PeanoNat.
Include Coq.Init.Nat.
Require Import Coq.Lists.List.
Import ListNotations.

Definition nat_lt_dec : forall n m : nat, {n < m} + {~ (n < m)}.
  intros n m.
  destruct (n <? m) eqn:e.
  left; apply Nat.ltb_lt; auto.
  right; intro H. assert (true = false) by (transitivity (n <? m); [symmetry; apply Nat.ltb_lt; auto | auto]); discriminate H0.
Defined.

Fixpoint list_max (default : nat) (l : list nat) {struct l}: nat :=
  match l with
  | [] => default
  | x :: xs => max x (list_max default xs)
  end.

Lemma list_max_larger : forall (x default : nat) (l : list nat),
    x = default \/ In x l -> x <= list_max default l.
Proof.
  intros x default l H.
  induction l.
  destruct H; [simpl; rewrite H; reflexivity | inversion H].
  destruct H; [|simpl in H; destruct H].
  - simpl; transitivity (list_max default l);
      [apply IHl; auto| apply Nat.le_max_r].
  - simpl; rewrite H; apply Nat.le_max_l.
  - simpl. transitivity (list_max default l); [apply IHl; auto | apply Nat.le_max_r].
Qed.                        

Fixpoint RemoveZeros (ns : list nat) : list nat :=
  match ns with
  | [] => []
  | n :: ns' => if n =? 0
               then RemoveZeros ns'
               else n :: RemoveZeros ns'
  end.

Lemma InRemoveZeros : forall (ns : list nat) (n : nat), In n (RemoveZeros ns) -> n <> 0 /\ In n ns.
Proof.
  intros ns n H.
  induction ns; simpl in H; [inversion H | destruct (a =? 0) eqn:e].
  specialize (IHns H); destruct IHns; split; [|right]; auto.
  destruct H. pose proof (Nat.eqb_spec a 0); destruct H0; inversion e.
  rewrite <- H; split; [| left]; auto.
  specialize (IHns H); destruct IHns; split; [|right]; auto.
Qed.

Lemma InRemoveZeros' : forall (ns : list nat) (n : nat), n <> 0 -> In n ns -> In n (RemoveZeros ns).
Proof.
  intros ns. induction ns; simpl; intros n ne nInNs.
  inversion nInNs.
  destruct nInNs.
  destruct (a =? 0) eqn:e;
    [exfalso; apply ne; rewrite Nat.eqb_eq in e; rewrite H in e; auto | left; auto].
  destruct (a =? 0); [apply IHns | right; apply IHns]; auto.
Qed.

Lemma RemoveZerosWithoutZerosInv : forall (ns : list nat), ~ In 0 ns -> RemoveZeros ns = ns.
Proof.
  intros ns H. induction ns.
  simpl. auto.
  simpl. destruct (a =? 0) eqn:e.
  rewrite Nat.eqb_eq in e; exfalso; apply H; left; auto.
  apply f_equal. apply IHns. intro Hcontra; apply H; right; auto.
Qed.

Lemma ZeroNotInRemoveZeros : forall (ns : list nat), ~In 0 (RemoveZeros ns).
Proof.
  intros ns; induction ns; simpl; auto.
  destruct (a =? 0) eqn:e ; auto.
  intro Hcontra. apply IHns. destruct Hcontra; auto.
  rewrite Nat.eqb_neq in e. exfalso; apply e; auto.
Qed.

Lemma minus_one_plus_one : forall m n : nat, m <> 0 -> m - 1 = n  -> m = n + 1.
Proof.
  intros m n H H0;
  induction m; [exfalso; apply H; auto|];
  simpl in H0; rewrite Nat.sub_0_r in H0; rewrite H0; rewrite Nat.add_comm; simpl; reflexivity.
Qed.  

Theorem OneLE : forall x, x = 0 \/ 1 <= x.
Proof.
  intros x.
  destruct x. left; auto. right. apply le_n_S.  apply Nat.le_0_l.
Qed.

Theorem OneLES : forall x, 1 <= S x.
Proof.
  intros x. destruct (OneLE (S x)); auto. inversion H.
Qed.


Theorem le_minus_plus : forall n m o, m <= n -> n - m = o -> n = o + m.
Proof.
  induction n; intros m o H H0.
  inversion H. simpl in H0. rewrite Nat.add_0_r. auto.
  destruct m. rewrite Nat.sub_0_r in H0. rewrite Nat.add_0_r. auto.
  simpl in H0. pose proof (le_S_n _ _ H). specialize (IHn m o H1 H0).
  rewrite Nat.add_comm. simpl. apply f_equal. rewrite Nat.add_comm. apply IHn.
Qed.

Theorem ZeroUniqueIdent : forall {a b}, a = a + b -> b = 0.
Proof.
  intros a; induction a; intros b H; simpl.
  simpl in H; symmetry; exact H.
  simpl in H. inversion H. apply IHa; exact H1.
Qed.

Lemma OneUniqueS  :forall {a b}, S a = a + b -> b = 1.
Proof.
  intros a; induction a; intros b H; simpl.
  simpl in H; symmetry; exact H.
  inversion H. apply IHa; exact H1.
Qed.
