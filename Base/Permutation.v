Require Export Coq.Sorting.Permutation.
Require Export Coq.Lists.List.

Import ListNotations. Open Scope list_scope.

Section CountDistinct.
  Variable A : Type.
  Variable Adec : forall (a b : A), {a = b} + {a <> b}.

  Fixpoint CountDistinct' (l : list A) (n : nat) (seen : list A) {struct l}: nat :=
    match l with
    | [] => n
    | (x :: xs) => if (in_dec Adec x seen)
                  then (CountDistinct' xs n seen)
                  else (CountDistinct' xs (n + 1) (x :: seen))
    end.

  Lemma CountDistinct'n : forall (l : list A) (n : nat) (seen : list A),
      CountDistinct' l n seen = (CountDistinct' l 0 seen) + n.
  Proof.
    intros l; induction l; simpl; [reflexivity | intros n seen].
    destruct (in_dec Adec a seen); auto.
    transitivity (CountDistinct' l 0 (a :: seen) + 1 + n).
    transitivity (CountDistinct' l 0 (a :: seen) + (n + 1)); [apply IHl | idtac].
    transitivity (CountDistinct' l 0 (a :: seen) + (1 + n)); 
      [ assert (n + 1 = 1 + n) as H by (apply PeanoNat.Nat.add_comm); rewrite H; reflexivity
      | apply PeanoNat.Nat.add_assoc].
    symmetry; assert (CountDistinct' l 1 (a :: seen) = CountDistinct' l 0 (a :: seen) + 1)
      by (apply IHl);
    rewrite H; reflexivity.
  Qed.

  Lemma SeenPermute : forall (l : list A) (n : nat) (seen seen' : list A),
      Permutation seen seen' -> CountDistinct' l n seen = CountDistinct' l n seen'.
  Proof.
    intros l; induction l as [| x l]; intros n seen seen' Hperm; simpl; auto.
    destruct (in_dec Adec x seen); destruct (in_dec Adec x seen');
      auto; exfalso; apply n0;
        [ apply Permutation_in with (l := seen)
        | apply Permutation_sym in Hperm; apply Permutation_in with (l := seen')];
        auto.
  Qed.
  
  Lemma NotInSeen : forall (l : list A) (n : nat) (seen : list A) (a : A),
      ~ (In a l) -> CountDistinct' l n seen = CountDistinct' l n (a :: seen).
  Proof.
    intros l; induction l as [| x l]; intros n seen a Hin; simpl; auto;
    destruct (Adec a x);
      [ simpl in Hin; exfalso; apply Hin; left; symmetry; auto 
      | destruct (in_dec Adec x seen)].
    - apply IHl; simpl in Hin; intro Hal; apply Hin; right; auto.
    - transitivity (CountDistinct' l (n + 1) (a :: x :: seen));
        [idtac | apply SeenPermute; constructor ];
        apply IHl; simpl in Hin; intro Hal; apply Hin; right; auto.
  Qed.

  Lemma FewerDistinctThanTotal : forall (l seen : list A) (n : nat),
      CountDistinct' l n seen <= length l + n.
  Proof.
    intros l; induction l as [| x l]; simpl; intros seen n; auto.
    destruct (in_dec Adec x seen); [transitivity (length l + n); auto | idtac];
    transitivity (length l + (n + 1));
      [ apply IHl 
      | rewrite PeanoNat.Nat.add_assoc; rewrite PeanoNat.Nat.add_1_r; reflexivity].
  Qed.
  
  Lemma CountLengthSeenNotIn : forall (l seen : list A) (a : A),
      CountDistinct' l 0 seen = length l -> In a seen -> ~ In a l.
  Proof.
    intros l; induction l as [| x l]; simpl; intros seen a Hcd Hlen; auto.
    destruct (in_dec Adec x seen).
    - assert (CountDistinct' l 0 seen <= length l + 0) as Hlt
          by (apply FewerDistinctThanTotal); rewrite PeanoNat.Nat.add_0_r in Hlt;
        rewrite Hcd in Hlt; exfalso; generalize Hlt; apply PeanoNat.Nat.nle_succ_diag_l.
    - intro Hcontra; destruct Hcontra; [apply n; rewrite H; apply Hlen | idtac];
      assert (~In a l)
        as H0
         by (apply IHl with (seen := x :: seen); [idtac | simpl; right; auto];
             apply PeanoNat.Nat.succ_inj;
             rewrite <- PeanoNat.Nat.add_1_r; rewrite <- CountDistinct'n; auto);
        apply H0; auto.
  Qed.

  Definition CountDistinct (l : list A) : nat :=
    CountDistinct' l 0 [].

  Lemma CountDistinctEmpty0 : CountDistinct [] = 0.
  Proof.
    unfold CountDistinct; simpl; reflexivity.
  Qed.

  
  Theorem NoDupAllDistinct : forall (l : list A),
      NoDup l -> CountDistinct l = length l.
  Proof.
    intros l H; induction H; [simpl; apply CountDistinctEmpty0 | idtac];
      unfold CountDistinct; simpl; unfold CountDistinct in IHNoDup;
        rewrite CountDistinct'n.
    rewrite NotInSeen with (a := x) in IHNoDup; [idtac | auto];
      rewrite IHNoDup; rewrite PeanoNat.Nat.add_1_r; reflexivity.
  Qed.

  Theorem CountDistinct'Permute : forall (l l' seen : list A) (n : nat),
      Permutation l l' -> CountDistinct' l n seen = CountDistinct' l' n seen.
  Proof.
    intros l l' seen n HPerm; generalize dependent seen; generalize dependent n;
      induction HPerm; simpl; intros n seen; auto.
    - destruct (in_dec Adec x seen); apply IHHPerm.
    - destruct (in_dec Adec x seen); destruct (in_dec Adec y seen); auto;
        destruct (Adec x y); destruct (Adec y x);
          match goal with
          | [ e : ?a = ?b, n : ?a <> ?b |- _ ] => exfalso; apply n; apply e
          | [ e : ?a = ?b, n : ?b <> ?a |- _ ] => exfalso; apply n; symmetry; apply e
          | [ e : ?a = ?b, e' : ?a = ?b |- _ ] =>
            match e' with
            | e => fail 1
            | _ => clear e'
            end
          | [ e : ?a = ?b, e' : ?b = ?a |- _ ] => clear e'
          | _ => idtac
          end; auto; [rewrite e; auto | apply SeenPermute; constructor].
    - transitivity (CountDistinct' l' n seen); [apply IHHPerm1 | apply IHHPerm2].
  Qed.      

  Lemma CountDistinctPermute : forall (l l' : list A),
      Permutation l l' -> CountDistinct l = CountDistinct l'.
  Proof.
    intros l l' H; unfold CountDistinct; apply CountDistinct'Permute; auto.
  Qed.
  
  Theorem AllDistinctNoDup : forall (l : list A),
      CountDistinct l = length l -> NoDup l.
  Proof.
    intros l; unfold CountDistinct; induction l as [| x l]; simpl; intros H; constructor;
      assert (~ In x l) by
        (rewrite CountDistinct'n in H; rewrite PeanoNat.Nat.add_1_r in H;
         apply CountLengthSeenNotIn with (seen := [x]);
         [apply PeanoNat.Nat.succ_inj; auto | simpl; auto]); auto.
    apply IHl; apply PeanoNat.Nat.succ_inj; auto;
      rewrite <- NotInSeen with (a := x) in H; rewrite CountDistinct'n in H;
        rewrite PeanoNat.Nat.add_1_r in H; auto.
  Qed.

  Lemma NoElemsNil : forall (l : list A), (forall (a : A), ~ In a l) -> l = nil.
  Proof.
    intros l H; destruct l; auto; exfalso; apply (H a); simpl; left; auto.
  Qed.    
  Lemma CountDistinct'AllSeen : forall (l seen : list A) (n : nat),
      (forall a, In a l -> In a seen) -> CountDistinct' l n seen = n.
  Proof.
    intros l; induction l as [| x l]; simpl; intros seen n Hin; auto;
      destruct (in_dec Adec x seen);
      [apply IHl; intros a Hal; apply Hin; auto | exfalso; apply n0; apply Hin; auto].
  Qed.

  Lemma CountDistinct'MoveToSeen : forall (l seen : list A) (a : A) (n : nat),
      In a l -> ~ In a seen ->
      CountDistinct' l n seen = CountDistinct' l (n + 1) (a :: seen).
  Proof.
    intro l; induction l as [| x l]; simpl; intros seen a n HInl HInSeen; auto.
    destruct HInl.
    destruct (in_dec Adec x seen).
    destruct (Adec a x). exfalso; apply HInSeen; rewrite e; auto.
    apply IHl; [destruct HInl; [exfalso; apply n0; symmetry | idtac] | idtac]; auto.
    destruct (Adec a x); [rewrite e; reflexivity | idtac].
    transitivity (CountDistinct' l (n + 1 + 1) (a :: x :: seen)).
    destruct HInl; [exfalso; apply n1 | apply IHl;
                                        [idtac | simpl; intro Hcontra; destruct Hcontra]];
    auto.
    apply SeenPermute; constructor.
  Qed.

  Theorem AllDistinctAsSets' : forall (l l' seen : list A) (n : nat),
      (forall a : A, In a l \/ In a seen <-> In a l') -> CountDistinct' l n seen = CountDistinct' l' n seen.
  Proof.
    intro l; induction l as [| x l]; simpl; intros l' seen n HIn; auto.
    - rewrite CountDistinct'AllSeen;
        [ auto
        | intros; assert (False \/ In a seen) as HIna by (apply HIn; auto);
          destruct HIna as [HFF | HIna]; [destruct HFF | exact HIna]].
    - destruct (in_dec Adec x seen).
      -- apply IHl; intro a; split; intros.
         --- apply HIn. destruct H; [left; right; auto | right; auto].
         --- assert (((x = a) \/ In a l) \/ In a seen) by (apply HIn; auto);
             destruct H0; [destruct H0; [right; rewrite <- H0 | left] | right]; auto.
      -- transitivity (CountDistinct' l' (n + 1) (x :: seen)).
         apply IHl; intro a; split; intro H.
         --- destruct H; apply HIn;
               [left; right | simpl in H; destruct H; [left; left | right]]; auto.
         --- assert ((x = a \/ In a l) \/ In a seen) by (apply HIn; auto);
               destruct H0;
               [destruct H0;
                [right; simpl; left | left]
               | right; simpl; right]; auto.
         --- symmetry; apply CountDistinct'MoveToSeen; auto.
             apply HIn; left; left; reflexivity.
  Qed.

  Theorem AllDistinctAsSets : forall (l l' : list A),
      (forall a : A, In a l <-> In a l') -> CountDistinct l = CountDistinct l'.
  Proof.
    intros l l' HIn; unfold CountDistinct; apply AllDistinctAsSets'.
    intro a; split; intro H.
    destruct H; [apply HIn; auto | simpl in H; destruct H].
    left; apply HIn; auto.
  Qed.    
  
Theorem NoDupEqLength : forall (l l' : list A),
    NoDup l -> (forall a : A, In a l  <-> In a l') -> length l = length l' -> NoDup l'.
Proof.
  intros l l' H H0 H1;
  assert (CountDistinct l = length l) by (apply NoDupAllDistinct; auto);
  assert (CountDistinct l = CountDistinct l') by (apply AllDistinctAsSets; auto);
  apply AllDistinctNoDup;
    transitivity (CountDistinct l); [symmetry | transitivity (length l)]; auto.
Qed.

End CountDistinct.