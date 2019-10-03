Require Import Arith.
Require Export Coq.Lists.List.
Require Import Coq.Logic.JMeq.
Require Import Coq.Classes.Morphisms.
Require Export Coq.Sorting.Permutation.

Import ListNotations. Open Scope list_scope.

Section Forall.

  Variable A : Type.
  Variable P : A -> Prop.

  Theorem map_isFunctorial : forall {A B C : Type} (l : list A) (f1 : B -> C) (f2 : A -> B), map f1 (map f2 l) = map (fun x => f1 (f2 x)) l.
  Proof.
    induction l; simpl; intros; auto.
    f_equal.
    auto.
  Qed.
    
  Theorem map_preservesIn : forall {A B : Type} (l : list A) (f : A -> B) (tb : B), In tb (map f l) -> exists ta, (In ta l) /\ (tb = f ta).
  Proof.
    induction l; simpl; intros; auto.
    - inversion H.
    - destruct H; subst; eauto.
      destruct (IHl f tb H).
      destruct H0.
      subst.
      exists x; eauto.      
  Qed.

  Theorem Forall_append : forall (l1 l2 : list A),
    Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
  Proof.
    intros l1 l2; split; intro H.
    - split; apply Forall_forall; intros x H0;
        rewrite Forall_forall in H; apply H; apply in_or_app; [left | right]; auto.
    - destruct H as [H1 H2]; rewrite Forall_forall in H1; rewrite Forall_forall in H2;
        rewrite Forall_forall; intros x H0; rewrite in_app_iff in H0; destruct H0;
          [apply H1 | apply H2]; auto.
  Qed.

  Definition Forall_inv_car := Forall_inv.
  Theorem Forall_inv_cdr : forall (a : A) (l : list A), Forall P (a :: l) -> Forall P l.
  Proof.
    intros a l H; inversion H; auto.
  Qed.

End Forall.

Fixpoint list_insert {A : Type} (a : A) (n : nat) (l : list A) {struct l} : list A :=
    match n with
    | 0 => a :: l
    | S n' =>
      match l with
      | [] => []
      | x :: l' => x :: (list_insert a n' l')
      end
    end.

Theorem list_insert_nth : forall {A : Type} (a : A) (n : nat) (l : list A),
    nth n (list_insert a n l) a = a.
Proof.
  intros A a n l; generalize n; clear n.
  induction l; intro n; destruct n; simpl; auto.
Qed.

Theorem list_insert_nth_len : forall {A : Type} (x a : A) (n : nat) (l : list A),
    n <= length l -> nth n (list_insert a n l) x = a.
Proof.
  intros A x a n l H; generalize dependent n.
  induction l; intros n H; simpl in H; inversion H; simpl.
  - reflexivity.
  - apply IHl; reflexivity. 
  - destruct n; simpl; [reflexivity | apply IHl; apply Le.le_Sn_le; auto].
Qed.

Theorem mth_list_insert_lt : forall {A : Type} (x a : A) (n m : nat) (l : list A),
    m < n -> nth m (list_insert a n l) x = nth m l x.
Proof.
  intros A x a n m l H.
  generalize dependent m; generalize dependent n; induction l; intros n m H; simpl in H.
  - destruct m; destruct n; simpl; auto; inversion H.
  - destruct n; [inversion H | destruct m; auto; simpl; apply Lt.lt_S_n in H; apply IHl; auto].
Qed.

Theorem mth_list_insert_gt : forall {A : Type} (x a : A) (l : list A) (n m : nat),
    n < m -> nth m (list_insert a n l) x = nth (m - 1) l x.
Proof.
  intros A x a l.
  induction l; intros n m H; simpl in H.
  - destruct m; destruct n; simpl; auto; inversion H; simpl; auto;
      rewrite PeanoNat.Nat.sub_0_r; [reflexivity | destruct m; simpl; reflexivity].
  - destruct n; simpl. repeat (destruct m; inversion H; simpl; auto).
    destruct m; inversion H; simpl.
    -- rewrite H1;
         assert (n = m - 1) by (rewrite <- H1; simpl; rewrite PeanoNat.Nat.sub_0_r; reflexivity);
         rewrite H0 at 2; apply IHl; apply Lt.lt_S_n; auto.
    -- rewrite PeanoNat.Nat.sub_0_r.
       destruct m; simpl. inversion H1.
       assert (m = S m - 1) by (simpl; symmetry; apply PeanoNat.Nat.sub_0_r).
       rewrite H2 at 2. apply IHl. apply Lt.lt_S_n; auto.
Qed.

Program Fixpoint ExceptNth {A : Type} (n : nat) (l : list A) : list A :=
  match l with
  | [] => []
  | (x :: xs) => match n with
                | 0 => xs
                | S n' => x :: ExceptNth n' xs
                end
  end.

Theorem rev_app_to_cons : forall {A : Type} {l : list A} {a : A},
    exists b l', rev l ++ [a] = b :: l'.
Proof.
  intros A l; induction l as [| c l]; intro a.
  - simpl; exists a; exists []; auto.
  - simpl; destruct (IHl c) as [x Hx]; destruct Hx as [l'' Hxl''];
      exists x; exists (l'' ++ [a]); rewrite Hxl''; simpl; auto.
Qed.

Theorem ReverseNil : forall {A : Type} {l : list A}, rev l = [] -> l = [].
Proof.
  intros A l Hl; destruct l;
  [ auto
  | simpl in Hl; exfalso; apply in_nil with (a := a);
    rewrite <- Hl; apply in_or_app; right; simpl; left; auto
  ].
Qed.

Lemma ReverseNilIff : forall {A : Type} {l : list A}, rev l = [] <-> l = [].
Proof.
  intros A l; split; intro H; [apply ReverseNil; auto | rewrite H; auto].
Qed.

Lemma ReverseNilIff' : forall {A : Type} {l : list A}, rev l <> [] <-> l <> [].
Proof.
  intros A l; split; intros H H'; apply H; apply ReverseNilIff; auto.
Qed.

Theorem RevApp : forall {A : Type} (l l' : list A),
    rev (l ++ l') = rev l' ++ rev l.
Proof.
  intros A l; induction l;
    [ intros l'; simpl; rewrite <- app_nil_end; reflexivity
    | intros l'; simpl; rewrite IHl; rewrite app_assoc; reflexivity
    ].
Qed.

Lemma RevConsIsApp : forall {A : Type} (l l' : list A) {a : A},
    rev l = a :: l' -> l = rev l' ++ [a].
Proof.
  intros A l; induction l.
  - intros l' a H; simpl in H; inversion H.
  - simpl; intros l' b H.
    destruct (rev l) as [| c l''] eqn:e.
    simpl in H; inversion H; simpl; rewrite @ReverseNil with (l := l); auto.
    inversion H; simpl in H; rewrite <- H2 in H; simpl; rewrite RevApp; simpl;
      assert (l = rev l'' ++ [b]) by (apply IHl; inversion H; auto).
    rewrite H0. auto.
Qed.

Lemma ForallRev : forall {A : Type} {P : A -> Prop} {l : list A},
    Forall P l -> Forall P (rev l).
Proof.
  intros A P l H.
  induction l; [simpl; apply Forall_nil|].
  pose proof (Forall_inv_car A P _ _ H).
  pose proof (Forall_inv_cdr A P _ _ H).
  simpl; apply Forall_append; split; auto.
Qed.  


Lemma RemoveLastApp1 : forall {A : Type} (l : list A) (a : A),
    removelast (l ++ [a]) = l.
Proof.
  intros A l; induction l as [| b l']; intro a; simpl.
  auto.
  destruct (l' ++ [a]) eqn:e.
  - exfalso; apply in_nil with (a := a); rewrite <- e; apply in_or_app; right; simpl; left; auto.
  - rewrite <- e; rewrite IHl'; reflexivity.
Qed.

Lemma InRemoveLast : forall {A : Type} (l : list A) (a : A),
    In a (removelast l) -> In a l.
Proof.
  intros A l a H.
  induction l; [simpl in H; destruct H | idtac]. 
  simpl in H. destruct l. destruct H. 
  simpl in H; destruct H. simpl; left; auto. 
  simpl; right; fold In.  simpl in IHl. apply IHl; auto.
Qed.

Lemma App1NonEmpty : forall {A : Type} (l : list A) (a : A),
    l ++ [a] <> [].
Proof.
  intros A l a; intro H; apply in_nil with (a := a);
    rewrite <- H; apply in_or_app; right; simpl; auto.
Qed.

Definition InBool : forall {A : Type} (ADec : forall a b : A, {a = b} + {a <> b}), A -> list A -> bool :=
  fun A ADec a l =>
      match (@in_dec A ADec a l) with
      | left _ => true
      | right _ => false
      end.

Theorem InBoolSpec : forall {A : Type} {ADec : forall a b : A, {a = b} + {a <> b}}
                       {a : A} {l : list A},
    InBool ADec a l = true <-> In a l.
Proof.
  intros A ADec a l.
  unfold InBool; (destruct in_dec); split; intro H; auto.
  inversion H.
Qed.

Theorem InBoolSpec' : forall {A : Type} {ADec : forall a b : A, {a = b} + {a <> b}}
                        {a : A} {l : list A},
    InBool ADec a l = false <-> ~ In a l.
Proof.
  intros A ADec a l; split; intro H.
  intro Hcontra. rewrite <- @InBoolSpec with (ADec := ADec) in Hcontra.
  pose proof (eq_trans (eq_sym H) Hcontra); inversion H0.
  destruct (InBool ADec a l) eqn:e.
  exfalso; rewrite InBoolSpec in e; apply H; auto.
  auto.
Qed.

Theorem InBoolSubset : forall {A : Type} {ADec : forall a b : A, {a = b} + {a <> b}}
                         {a : A} {l1 l2 : list A},
    InBool ADec a l1 = true -> (forall b : A, In b l1 -> In b l2) -> InBool ADec a l2 = true.
Proof.
  intros A ADec a l1 l2 H H0.
  rewrite InBoolSpec. rewrite InBoolSpec in H.
  apply H0; auto.
Qed.

Definition InBoolCons : forall {A : Type} {ADec : forall a b : A, {a = b} + {a <> b}}
                       {a b : A} {l : list A},
    InBool ADec a (b :: l) = true -> {a = b} + {InBool ADec a l = true}.
Proof.
  intros A ADec a b l H.
  unfold InBool in H.
  destruct (ADec a b).
  left; auto.
  right.
  destruct (in_dec ADec a (b :: l)); [| inversion H].
  destruct i as [e | i0]; [exfalso; apply n; symmetry; apply e |].
  rewrite InBoolSpec; auto.
Defined.

Lemma InCons: forall {A:Type} {ADec : forall a b : A, {a = b} + {a <> b}} (l:A) m a , In a (l :: m) -> {a = l} + {In a m}.
Proof.
  intros A ADec l m a H.
  eapply InBoolSpec in H.
  eapply InBoolCons in H.
  destruct H; auto.
  right.
  eapply InBoolSpec; eauto.
  Unshelve.
  apply ADec.
Qed.

Program Definition EqNil {A : Type} (l : list A) : {l = []} + {l <> []} :=
  match l with
  | [] => left _
  | _ => right _
  end.

Ltac EqNilDestruct l :=
  let e := fresh "e" in
  let n := fresh "n" in
  match l with
  | [] => destruct (EqNil l) as [e | n];
         [clear e | exfalso; apply n; auto]
  | _ =>
    match goal with
    | [ H : l = [] |- _  ] =>
      destruct (EqNil l) as [e | n];
      [| exfalso; apply n; exact H]
    | [ H : [] = l |- _ ] =>
      destruct (EqNil l) as [e | n];
      [| exfalso; apply n; exact (eq_sym H)]
    | [ H : l <> [] |- _ ] =>
      destruct (EqNil l) as [e | n];
      [ exfalso; apply H; exact e |]
    | [ H : [] <> l |- _ ] =>
      destruct (EqNil l) as [e | n];
      [exfalso; apply H; exact (eq_sym e) |]
    | [ H : l = _ :: _ |- _ ] =>
      destruct (EqNil l) as [e | n];
      [rewrite e in H; inversion H |]
    | [ H : _ :: _ = l |- _ ] =>
      destruct (EqNil l) as [e | n];
      [rewrite e in H; inversion H |]
    | _ => destruct (EqNil l) as [e | n]
    end
  end.

Inductive Path {A : Set} : A -> list A -> Set :=
| Here : forall (a : A) (l : list A), Path a (a :: l)
| There : forall {a : A} (b : A) {l : list A}, Path a l -> Path a (b :: l).

Inductive MaybePath {A : Set} : A -> list A -> Set :=
| IsPath : forall {a : A} {l : list A}, Path a l -> MaybePath a l
| NoPath : forall {a : A} {l : list A}, (Path a l -> False) -> MaybePath a l.

Program Fixpoint FindPath {A : Set} {AEq : forall a b : A, {a = b} + {a <> b}} (a : A) (l : list A) 
  : MaybePath a l :=
  match l with
  | [] => NoPath (fun p => _)
  | b :: l' => match (AEq a b) with
              | left e => eq_rec_r (fun a0 : A => MaybePath a0 (b :: l')) (IsPath (Here b l')) e
              | right n => let m := @FindPath A AEq a l' in
                          match m in (MaybePath y l0) return (y <> b -> MaybePath y (b :: l0)) with
                          | @IsPath _ a0 l0 p => _
                          | @NoPath _ a0 l0 f => _
                          end n
              end
  end.
Next Obligation.
  inversion p.
Defined.
Next Obligation.
  apply IsPath; apply There; auto.
Defined.
Next Obligation.
  apply NoPath. intro p. inversion p.
  - apply H; auto.
  - apply f; auto.
Defined.

Theorem InPathDoubleNeg : forall {A : Set} {AEq : forall a b : A, {a = b} + {a <> b}} (a : A) (l : list A),
    In a l -> (Path a l -> False) -> False.
Proof.
  intros A AEq a l H H0.
  induction l.
  inversion H.
  destruct H.
  rewrite H in H0; apply (H0 (Here a l)).
  apply IHl; auto. 
  intro p. apply H0. apply There; auto.
Qed.

Program Definition InToPath {A :Set} (AEq : forall a b : A, {a = b} + {a <> b}) {a : A} {l : list A} : 
  In a l -> Path a l :=
  fun H => match @FindPath A AEq a l with
        | IsPath pi => pi
        | NoPath npi => _
        end.
Next Obligation.
  apply JMeq_eq in Heq_l; clear Heq_anonymous; rewrite Heq_l in npi.
  exfalso; apply @InPathDoubleNeg with (a := a) (l := l); auto.
Defined.

Fixpoint PathToIndex {A : Set} {a : A} {l : list A} (pi : Path a l) {struct pi} : nat :=
  match pi with
  | Here _ _ => 0
  | There _ pi' => 1 + PathToIndex pi'
  end.

Lemma PathToIndex0_Here : forall {A : Set} {a b : A} {l : list A} (pth : Path a (b :: l)),
    PathToIndex pth = 0 -> a = b /\ JMeq pth (Here a l).
Proof.
  intros A a b l pth H.
  remember (b :: l). destruct pth eqn:e.
  inversion Heql0. split; auto.
  simpl in H. inversion H.
Qed.

Lemma PathToIndexS_There : forall {A : Set} {a : A} {l : list A} (pth : Path a l) (n : nat),
    PathToIndex pth = S n -> exists b l' (pth' : Path a l'), l = b :: l' /\ JMeq pth (@There A a b l' pth').
Proof.
  intros A a l pth n H.
  destruct pth eqn:e. inversion H.
  exists b; exists l; exists p; auto.
Qed.


Program Fixpoint nth_known_correct {A : Type} (n : nat) (l : list A) (n_corr : n < length l) : A :=
  match n with
  | O => match l with
        | [] => _
        | a :: _ => a
        end
  | S m => match l with
          | [] => _
          | _ :: l' => @nth_known_correct A m l' _
          end
  end.
Next Obligation.
  simpl in n_corr; exfalso; eapply PeanoNat.Nat.nlt_0_r; eauto.
Defined.
Next Obligation.
  simpl in n_corr; exfalso; eapply PeanoNat.Nat.nlt_0_r; eauto.
Defined.
Next Obligation.
  simpl in n_corr; apply Lt.lt_S_n; auto.
Defined.

Lemma nth_known_correct_pf_irr : forall {A : Type} (n : nat) (l : list A) (pf pf' : n < length l),
    @nth_known_correct A n l pf = @nth_known_correct A n l pf'.
Proof.
  intros A n l pf pf'.
  generalize dependent n.
  induction l; intros n pf pf'; [simpl in pf; exfalso; eapply PeanoNat.Nat.nlt_0_r; eauto|].
  destruct n; [simpl; reflexivity |].
  simpl. apply IHl.
Qed.

Lemma PathToIndexGivesValidIndex : forall {A : Set} {a : A} {l : list A} (pi : Path a l),
    PathToIndex pi < length l.
Proof.
  intros A a l pi; induction pi; [simpl; apply PeanoNat.Nat.lt_0_succ | simpl; apply Lt.lt_n_S; auto].
Qed.

Lemma ItemAtPathToIndex : forall {A : Set} {a : A} {l : list A} {pi : Path a l},
    @nth_known_correct A (PathToIndex pi) l (PathToIndexGivesValidIndex pi) = a.
Proof.
  intros A a l pi.
  induction pi; simpl; [auto | erewrite nth_known_correct_pf_irr; exact IHpi].
Qed.

Lemma ItemAtPathToIndex' :forall {A : Set} {a : A} {l : list A} {pi : Path a l}
                            (H : PathToIndex pi < length l),
    nth_known_correct (PathToIndex pi) l H = a.
Proof.
  intros A a l pi.
  induction pi; intro H; simpl; simpl in H; [auto| apply IHpi].
Qed.

Program Fixpoint IndexToPath {A : Set} (n : nat) (l : list A) (pf : n < length l) :
  Path (@nth_known_correct A n l pf) l :=
  match n with
  | 0 => match l with
        | [] => _
        | a :: l' => Here a l'
        end
  | S m => match l with
          | [] => _
          | a :: l' => @There _ _ a l' (@IndexToPath _ m l' _)
          end
  end.
Next Obligation.
  simpl in pf; exfalso; eapply PeanoNat.Nat.nlt_0_r; eauto.
Defined.
Next Obligation.
  simpl in pf; exfalso; eapply PeanoNat.Nat.nlt_0_r; eauto.
Defined.
Next Obligation.
  simpl in pf; apply Lt.lt_S_n; auto.
Defined.

Lemma IndexToPathToIndexId : forall {A : Set} (n : nat) (l : list A) (pf : n < length l),
    PathToIndex (@IndexToPath A n l pf) = n.
Proof.
  intros A n l pf.
  generalize dependent n; induction l; intros n pf;
    [simpl in pf; exfalso; eapply PeanoNat.Nat.nlt_0_r; eauto|].
  simpl in pf.  
  destruct n; simpl; [reflexivity |].
  apply f_equal. apply IHl.
Qed.

Lemma PathToIn : forall {A : Set} {a : A} {l : list A}, Path a l -> In a l.
Proof.
  intros A a l H; induction H; [left | right]; auto.
Qed.

Ltac ClearLTZero :=
  match goal with
  | [ H : _ < length [] |- _ ] =>
    exfalso; eapply Nat.nlt_0_r; eauto
  | [ H : _ < 0 |- _ ] =>
    exfalso; eapply Nat.nlt_0_r; eauto
  | _ => idtac
  end.

Definition _add_one_corr_cons : forall {A : Type} i a (l : list A), i < length l -> (i + 1) < length (a :: l).
Proof.
  intros A i a l Hi.
  rewrite Nat.add_comm; simpl.
  apply Lt.lt_n_S; auto.
Qed.
  

Lemma nth_known_correct_cons : forall {A : Type} i a (l : list A) (Hi : i < length l),
    nth_known_correct i l Hi = nth_known_correct (i + 1) (a :: l) (_add_one_corr_cons i a l Hi).
Proof.
  intros A i a l Hi;
    generalize dependent i; generalize dependent a; induction l; intros b i Hi; ClearLTZero; simpl; simpl in Hi; auto.
  destruct i; simpl; auto.
  rewrite IHl with (a := a).
  apply nth_known_correct_pf_irr.
Qed.  

Lemma nth_known_correct_cons' : forall {A : Type} i a (l : list A) (Hi : i < length l) (Hj : i + 1 < length (a :: l)),
    nth_known_correct i l Hi = nth_known_correct (i + 1) (a :: l) Hj.
Proof.
  intros A i a l Hi Hj;
    generalize dependent i; generalize dependent a; induction l; intros b i Hi Hj; ClearLTZero; simpl;
      simpl in Hi; simpl in Hj; auto.
  destruct i; simpl; auto.
Qed.

Lemma nth_known_correct_error : forall {A : Type} i (l : list A) (Hi : i < length l),
    nth_error l i = Some (nth_known_correct i l Hi).
Proof.
  intros A i l Hi.
  generalize dependent i; induction l; intros i Hi; ClearLTZero; simpl.
  destruct i; [simpl; auto|].
  simpl. apply IHl.
Qed.

Lemma nth_error_some_if_known_correct : forall {A : Type} (l : list A) i (Hi : i < length l),
    exists a, nth_error l i = Some a.
Proof.
  intros A l; induction l; intros i Hi; ClearLTZero; simpl; simpl in Hi.
  destruct i; simpl. exists a; auto.
  assert (i < length l) by (apply Lt.lt_S_n; auto). specialize (IHl i H).
  auto.
Qed.

Lemma nth_known_correct_eq : forall {A : Type} i j (l : list A) (Hi : i < length l) (Hj : j < length l),
    i = j -> nth_known_correct i l Hi = nth_known_correct j l Hj.
Proof.
  intros A i j l Hi Hj H.
  assert (nth_error l i = nth_error l j) by (rewrite H; auto).
  pose (nth_error_some_if_known_correct l i Hi) as e;
    destruct e as [a Ha];
    pose proof Ha as Ha';
    rewrite nth_known_correct_error with (Hi0 := Hi) in Ha'; inversion Ha'.
  pose (nth_error_some_if_known_correct l j Hj);
    destruct e as [b Hb];
    pose proof Hb as Hb';
    rewrite nth_known_correct_error with (Hi0 := Hj) in Hb'; inversion Hb'.
  assert (Some a = Some b)
    by (transitivity (nth_error l i); [symmetry; auto | transitivity (nth_error l j); auto]).
  inversion H1. 
  rewrite H2. rewrite H3. auto.
Qed.

Program Fixpoint MoveToFront {A : Type} (AEq : forall a b : A, {a = b} + {a <> b})
        (l : list A) (a : A) : list A :=
  match l with
  | [] => []
  | x :: l' => if AEq a x
              then x :: l'
              else match MoveToFront AEq l' a with
                   | [] => x :: []
                   | y :: l'' =>
                     if AEq y a
                     then y :: x :: l''
                     else l
                   end
  end.

Definition InFront {A : Type} (l : list A) (a : A) : Prop :=
  match l with
  | [] => False
  | x :: _ => a = x
  end.

Lemma MoveToFrontInFront : forall {A : Type} AEq (l : list A) (a : A),
    In a l -> InFront (MoveToFront AEq l a) a.
Proof.
  intros A AEq l a aINl.
  induction l; [inversion aINl|].
  simpl; simpl in aINl. destruct aINl.
  rewrite H; simpl; destruct (AEq a a) as [e | n]; [clear e; simpl | exfalso; apply n]; auto.
  destruct (AEq a a0) as [e | n]; simpl; auto.
  destruct (MoveToFront AEq l a) eqn: e; [destruct (IHl H) | ].
  simpl in IHl; simpl.
  destruct (AEq a1 a). simpl; auto. exfalso; apply n0; symmetry; apply IHl; auto.
Qed.

Lemma MoveToFrontEq : forall {A : Type} AEq (l : list A) (a : A),
    ~In a l -> l = MoveToFront AEq l a.
Proof.
  intros A AEq l; induction l as [| b l']; intros a n; simpl; auto.
  destruct (AEq a b); auto.
  destruct (MoveToFront AEq l' a) eqn:e.
  rewrite (IHl' a); [rewrite e; auto | intro Hcontra; apply n; right; auto].
  destruct (AEq a0 a); auto.
  exfalso; apply n; right;
    rewrite IHl' with (a := a); [ rewrite e; left; auto | intro Hcontra; apply n; right; auto].
Qed.  


Lemma MoveToFrontPermuation : forall {A : Type} AEq (l : list A) (a : A),
    Permutation l (MoveToFront AEq l a).
Proof.
  intros A AEq l a.
  induction l; [simpl; auto|].
  simpl. destruct (AEq a a0); [auto|].
  destruct (MoveToFront AEq l a) eqn:e.
  inversion IHl; auto.
  destruct (AEq a1 a); auto.
  transitivity (a0 :: a1 :: l0); constructor; auto; fail.
Qed.

Lemma MoveToFrontLength : forall {A : Type} AEq (l : list A) (a : A),
    length l = length (MoveToFront AEq l a).
Proof.
  intros A AEq l a; apply Permutation_length; exact (MoveToFrontPermuation AEq l a).
Qed.


Lemma OnlyNNumbersLessThanN : forall (n : nat) (l : list nat),
    (forall m, In m l -> m < n) -> length l > n -> ~ NoDup l.
Proof.
  intros n. induction n; intros l all_below length_above nodup.
  destruct l; simpl in length_above. eapply Gt.gt_irrefl; eauto.
  eapply Nat.nlt_0_r; apply all_below; left; eauto.
  remember (MoveToFront Nat.eq_dec l n).
  pose proof (MoveToFrontPermuation Nat.eq_dec l n).
  rewrite <- Heql0 in H.
  pose proof (Permutation_NoDup H nodup) as nodupl0.
  destruct (ListDec.In_dec Nat.eq_dec n l).
  - assert (InFront l0 n) as nInFrontOfl by (rewrite Heql0; apply MoveToFrontInFront; auto).
    destruct l0; simpl in nInFrontOfl; [inversion nInFrontOfl |].
    apply (IHn l0).
    -- intros m mINl0.
       assert (In m l) as mINl
         by (apply Permutation_in with (l := (n0 :: l0)); [symmetry; auto| right; auto]).
       pose proof (Lt.lt_n_Sm_le m n (all_below m mINl)) as mLEn.
       destruct (Lt.le_lt_or_eq m n mLEn); auto.
       exfalso; inversion nodupl0; apply H3; rewrite <- nInFrontOfl; rewrite <- H0; auto.
    -- assert (length l = length (n0 :: l0)) by (apply Permutation_length; auto);
         rewrite H0 in length_above; simpl in length_above; apply Lt.lt_S_n; auto.
    --inversion nodupl0; auto.
  - apply (IHn l).
    -- intros m H0.
       pose proof (Lt.lt_n_Sm_le m n (all_below m H0)).
       destruct (Lt.le_lt_or_eq m n H1); auto.
       exfalso; apply n0; rewrite <- H2; auto.
    -- apply Gt.gt_trans with (m := S n); auto.
    -- auto.
Qed.

Theorem NoDupFilter : forall {A : Type} (l : list A) (f : A -> bool),
    NoDup l -> NoDup (filter f l).
Proof.
  intros A l f H.
  induction l; simpl; auto.
  destruct (f a).
  constructor. inversion H.
  intro Hcontra; apply H2.
  pose proof (proj1 (filter_In f a l)).
  specialize (H4 Hcontra).
  destruct H4; auto.
  all: apply IHl; inversion H; auto.
Qed.  

Fixpoint FilterLTs (l : list nat) (n : nat) : list nat :=
  match l with
  | [] => []
  | m :: l' =>
    let fltd := FilterLTs l' n in
    if andb (m <? n) (negb (InBool Nat.eq_dec m fltd))
              then m :: fltd
              else fltd
  end.

Theorem FilterLTs_lt : forall (l : list nat) (n m : nat),
    In m (FilterLTs l n) -> m < n.
Proof.
  intros l n m H.
  induction l.
  inversion H.
  simpl in H.
  destruct ((a <? n) && negb (InBool Nat.eq_dec a (FilterLTs l n)))%bool eqn:e.
  apply andb_prop in e; destruct e as [e1 e2].
  assert (a < n) by (rewrite Nat.ltb_lt in e1; auto).
  assert (~ In a (FilterLTs l n)) by (rewrite Bool.negb_true_iff in e2; rewrite InBoolSpec' in e2; auto).
  destruct H; [rewrite <- H; auto | apply IHl; auto].
  apply IHl; auto.
Qed.

Theorem FilterLTs_length1 : forall (l : list nat) (n : nat),
    length (FilterLTs l n) <= length l.
Proof.
  intros l n.
  induction l; simpl; auto.
  destruct (((a <? n) && negb (InBool Nat.eq_dec a (FilterLTs l n)))%bool).
  simpl. apply le_n_S; auto.
  transitivity (length l); auto.
Qed.  

Theorem FilterLTs_NoDup : forall (l : list nat) (n : nat),
    NoDup (FilterLTs l n).
Proof.
  intros l n.
  induction l; simpl; try (constructor; auto; fail); auto.
  destruct ((a <? n) && negb (InBool Nat.eq_dec a (FilterLTs l n)))%bool eqn:e; auto.
  apply andb_prop in e; destruct e as [e1 e2].
  assert (a < n) by (rewrite Nat.ltb_lt in e1; auto).
  assert (~ In a (FilterLTs l n)) by (rewrite Bool.negb_true_iff in e2; rewrite InBoolSpec' in e2; auto).
  constructor; auto.
Qed.

Theorem FilterLTs_in : forall (l : list nat) (n m : nat),
    In m (FilterLTs l n) -> In m l.
Proof.
  intros l n m H.
  induction l. simpl in H; inversion H.
  simpl in H. destruct ((a <? n) && negb (InBool Nat.eq_dec a (FilterLTs l n)))%bool.
  destruct H; [left | right; apply IHl]; auto.
  right; apply IHl; auto.
Qed.

Theorem InFilterLTs : forall (l : list nat) (n m : nat),
    In m l ->  m < n -> In m (FilterLTs l n).
Proof.
  intros l n m H H0; induction l; simpl in H; [inversion H|]; destruct H; simpl;
    destruct ((a <? n) && negb (InBool Nat.eq_dec a (FilterLTs l n)))%bool eqn:e; simpl;
      try (match goal with
           | [ H : ?P |- ?P \/ _ ] => left; auto
           | [ H : ?P, IH : ?P -> ?Q |- _ \/ ?Q] => right; apply IH; auto
           | [ H : ?P, IH : ?P -> ?Q |- ?Q ] => apply IH; auto
           end).
  destruct (Bool.andb_false_elim _ _ e).  
  exfalso; apply Nat.ltb_nlt in e0; apply e0; rewrite H; auto. 
  rewrite Bool.negb_false_iff in e0; rewrite InBoolSpec in e0; rewrite H in e0; auto.
Qed.

Fixpoint AllBelow (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n => AllBelow n ++ [n]
  end.

Theorem InAllBelow : forall (n m : nat),
    m < n <-> In m (AllBelow n).
Proof.
  intros n; induction n; intros m; split; intro H.
  - inversion H.
  - simpl in H; inversion H.
  - simpl; apply in_or_app; apply Lt.lt_n_Sm_le in H; apply Lt.le_lt_or_eq in H; destruct H.
    left; rewrite <- IHn; auto.
    right; rewrite H; left; auto.
  - simpl in H. apply in_app_or in H. destruct H.
    rewrite <- IHn in H; auto.
    destruct H; [rewrite H; auto | inversion H].
Qed.

Theorem AllBelowLength : forall (n : nat),
    length (AllBelow n) = n.
Proof.
  intros n; induction n; simpl; auto.
  rewrite app_length; simpl; rewrite IHn; rewrite Nat.add_comm; simpl; reflexivity.
Qed.  

Program Fixpoint ListDifference {A : Type} (AEq : forall a b : A, {a = b} + {a <> b}) (l1 l2 : list A)
  : list A :=
  match l1 with
  | [] => []
  | a :: l1' => if InBool AEq a l2
               then ListDifference AEq l1' l2
               else a :: ListDifference AEq l1' l2
  end.

Theorem ListDifference_length1 : forall {A : Type} (AEq : forall a b : A, {a = b} + {a <> b}) (l1 l2 : list A),
    length (ListDifference AEq l1 l2) <= length l1.
Proof.
  intros A AEq l1 l2.
  induction l1; simpl; auto.
  destruct (InBool AEq a l2) eqn:e.
  transitivity (length l1); auto.
  simpl; apply le_n_S; auto.
Qed.
  
Theorem SubsetListLength : forall {A : Type} (AEq : forall a b : A, {a = b} + {a <> b}) (l1 l2 : list A),
    (forall a, In a l1 -> In a l2) -> NoDup l1 -> length l1 <= length l2.
Proof.
  intros A AEq l1.
  induction l1; intros l2 H H0.
  - simpl; apply le_0_n.
  - simpl.
    pose proof (MoveToFrontInFront AEq l2 a (H a (or_introl eq_refl))).
    destruct (MoveToFront AEq l2 a) eqn:e; [inversion H1|].
    pose proof (MoveToFrontLength AEq l2 a).
    rewrite e in H2. simpl in H2.
    rewrite H2. apply Le.le_n_S. apply IHl1; [| inversion H0; auto].
    intros a1 H3.
    specialize (H a1 (or_intror H3)).
    apply Permutation_in with (l' := (MoveToFront AEq l2 a)) in H; [| apply MoveToFrontPermuation].
    rewrite e in H; destruct H; auto; inversion H0;
      exfalso; apply H6; simpl in H1; rewrite H1; rewrite H; auto.
Qed.       


Theorem FilterLTs_length2 : forall (l : list nat) (n : nat),
    length (FilterLTs l n) <= n.
Proof.
  intros l n.
  rewrite <- AllBelowLength.
  apply SubsetListLength; [apply Nat.eq_dec| |apply FilterLTs_NoDup].
  intros a H; apply FilterLTs_lt in H; apply InAllBelow; auto.
Qed.
Lemma FilterLTsZero : forall (l : list nat),
    FilterLTs l 0 = [].
Proof.
  intros l; induction l; simpl; auto.
Qed.

Ltac DestructFilterLTs :=
  repeat match goal with
         | [ |- context [if ?b then _ else _] ] =>
           let e := fresh "e" in
           destruct b eqn: e
         | [ H : context [if ?b then _ else _] |- _ ] =>
           let e := fresh "e" in
           destruct b eqn:e
         | [ H1 : ?P |- ?P ] => exact H1
         | [ H1 : ?P, H2 : ~?P |- _ ] => exfalso; apply H2; exact H1
         | [ H : (?a <? ?b) = true |- _ ] =>
           match goal with
           | [ _ : a < b |- _ ] => fail 1
           | _ => assert (a < b) by (rewrite Nat.ltb_lt in H; auto)
           end
         | [ H : (?a <? ?b) = false |- _ ] =>
           match goal with
           | [ _ : ~ a < b |- _ ] => fail 1
           | _ => assert (~ a < b) by (rewrite Nat.ltb_nlt in H; auto)
           end
         | [H : (?a =? ?b) = true |- _ ] =>
           match goal with
           | [_ : a = b |- _ ]=> fail 1
           | _ => assert (a = b) by (rewrite Nat.eqb_eq in H; auto)
           end
         | [H : (?a =? ?b) = false |- _ ] =>
           match goal with
           | [_ : a <> b |- _ ] => fail 1
           | _ => assert (a <> b) by (rewrite Nat.eqb_neq in H; auto)
           end
         | [H : andb ?a ?b = true |- _ ] =>
           match goal with
           | [_ : a = true, _ : b = true |- _ ] => fail 1
           | _ => assert (a = true) by (rewrite Bool.andb_true_iff in H; destruct H; auto);
                 assert (b = true) by (apply Bool.andb_true_iff in H; destruct H; auto)
           end
         | [H : andb ?a ?b = false |- _ ] =>
           match goal with
           | [ _ : a = false |- _ ] => fail 1
           | [ _ : b = false |- _ ] => fail 1
           | _ => let H' := fresh in
                 assert (a = false \/ b = false) as H'
                     by (rewrite Bool.andb_false_iff in H; auto);
                 destruct H'
           end
         | [H : negb ?a = true |- _ ] =>
           match goal with
           | [_ : a = false |- _ ] => fail 1
           | _ => assert (a = false) by (rewrite Bool.negb_true_iff in H; auto)
           end
         | [H : negb ?a = false |- _ ] =>
           match goal with
           | [_ : a = true |- _ ] => fail 1
           | _ => assert (a = true) by (rewrite Bool.negb_false_iff in H; auto)
           end
         | [H : InBool _ ?a ?l = true |- _ ] =>
           match goal with
           | [ _ : In a l |- _ ] => fail 1
           | _ => assert (In a l) by (rewrite InBoolSpec in H; auto)
           end
         | [H : InBool _ ?a ?l = false |- _ ] =>
           match goal with
           | [_ : ~(In a l) |- _ ] => fail 1
           | _ => assert (~In a l) by (rewrite InBoolSpec' in H; auto)
           end
         end.

Lemma FilterLTs_length_NotInZero : forall (l : list nat) (n : nat),
    ~ In 0 l ->
    length (FilterLTs (map (fun x => x - 1) l) n) = length (FilterLTs l (S n)).
Proof.
  intros l; induction l; intros n ni; simpl; auto.
  DestructFilterLTs.
  - simpl. simpl.
    rewrite IHl; auto. intro Hcontra; apply ni; right; auto.
  - exfalso; apply H3; destruct a; [apply Nat.lt_0_succ |].
    simpl in H1; rewrite Nat.sub_0_r in H1; apply Lt.lt_n_S; auto.
  - exfalso. pose proof (FilterLTs_lt _ _ _ H5).
    pose proof (FilterLTs_in _ _ _ H5).
    apply H6. apply InFilterLTs. pose proof (in_map (fun x => x - 1) _ _ H8).
    simpl in H9. auto.
    destruct a; [exfalso; apply ni; left; auto | simpl; rewrite Nat.sub_0_r; apply Lt.lt_S_n; auto].
  - exfalso; apply H3; destruct a.
    exfalso; apply ni; left; auto.
    simpl; rewrite Nat.sub_0_r; apply Lt.lt_S_n; auto.
  - apply FilterLTs_in in H5. apply map_preservesIn in H5.
    destruct H5 as [b Hb]; destruct Hb.
    assert (a = b)
      by (destruct a; [exfalso; apply ni; left; auto |]; destruct b;[exfalso; apply ni; right; auto|];
          simpl in H7; rewrite Nat.sub_0_r in H7; rewrite Nat.sub_0_r in H7; rewrite H7; auto).
    exfalso; apply H6; apply InFilterLTs; [rewrite H8 |]; auto.
  - apply IHl; intro Hcontra; apply ni; right; auto.
  - destruct a; [exfalso; apply ni; left; auto|].
    simpl in H3. rewrite Nat.sub_0_r in H3. apply FilterLTs_lt in H3.
    exfalso; apply H0; apply Lt.lt_n_S; auto.
  - apply IHl; intro Hcontra; apply ni; right; auto.
  - apply IHl; intro Hcontra; apply ni; right; auto.
Qed.


Lemma FilterLTs_remove_zeros : forall (l : list nat) (n : nat),
    FilterLTs (RemoveZeros l) n = RemoveZeros (FilterLTs l n).
Proof.
  intros l n. induction l.
  simpl. auto.
  simpl; DestructFilterLTs; simpl; DestructFilterLTs.
  - rewrite IHl; auto.
  - exfalso. rewrite IHl in H7. apply InRemoveZeros in H7. destruct H7. apply H4; auto.
  - exfalso. apply H7. rewrite IHl. apply InRemoveZeros'; auto.
Qed.

Lemma FilterLTs_length_remove_zeros : forall (l : list nat) (n : nat),
    In 0 l -> length (FilterLTs (RemoveZeros l) n) = length (FilterLTs l n) - 1.
Proof.
  intros l n H.
  rewrite FilterLTs_remove_zeros.
  induction l; simpl; auto.
  simpl; DestructFilterLTs.
  simpl. DestructFilterLTs.
  - rewrite Nat.sub_0_r; rewrite RemoveZerosWithoutZerosInv; [auto | rewrite H5 in H4; auto].
  - simpl. destruct H; [exfalso; apply H5; auto | ]. rewrite IHl; auto. apply Minus.minus_Sn_m.
    clear IHl H3 H1 H4 e e0 H0. induction l; [inversion H | simpl; auto].
    DestructFilterLTs; simpl.
    -- simpl. apply OneLES.
    -- destruct H.
       exfalso; apply H1; rewrite H; destruct n; [inversion H2 | apply Nat.lt_0_succ].
       apply IHl; auto.
    -- destruct (FilterLTs l n); [inversion H3 | simpl; apply OneLES].
  - destruct H; [| apply IHl; auto].
    destruct n; [rewrite FilterLTsZero; simpl; auto
                | exfalso; apply H1; rewrite H; apply Nat.lt_0_succ].
  - destruct H; [apply FilterLTs_in in H2; apply IHl; rewrite <- H; auto |apply IHl; auto].
Qed.

Lemma FilterLTs_length_S_InZero : forall (l : list nat) (n : nat),
    In 0 l ->
    length (FilterLTs (map (fun x => x - 1) (RemoveZeros l)) n) = length (FilterLTs l (S n)) - 1.
Proof.
  intros l n H.
  pose proof (FilterLTs_length_NotInZero (RemoveZeros l) n (ZeroNotInRemoveZeros l)).
  rewrite H0.
  apply FilterLTs_length_remove_zeros; auto.
Qed.

Fixpoint AllBelowMinusZero (n : nat) : list nat :=
  match n with
  | 0 => []
  | 1 => []
  | S n => (AllBelowMinusZero n) ++ [n]
  end.

Lemma InAllBelowMinusZero : forall (n m : nat),
    m < n -> m <> 0 -> In m (AllBelowMinusZero n).
Proof.
  intros n; induction n; intros m H H0.
  inversion H.
  simpl; destruct n.
  destruct m; [exfalso; apply H0; auto | apply Lt.lt_S_n in H; inversion H].
  inversion H; apply in_or_app.
  right; left; auto.
  left. apply IHn; auto.
Qed.

Lemma AllBelowMinusZeroLength : forall (n : nat),
    length (AllBelowMinusZero n) = n - 1.
Proof.
  intros n; induction n; simpl; auto.
  destruct n. simpl. auto.
  rewrite app_length; rewrite IHn; simpl; rewrite Nat.sub_0_r; rewrite Nat.add_comm; simpl; auto.
Qed.

Lemma FilterLTs_everything : forall (l : list nat) (n : nat),
    length (FilterLTs l (S n)) = (S n) -> In 0 (FilterLTs l (S n)).
Proof.
  intros l n H.
  destruct (ListDec.In_dec Nat.eq_dec 0 (FilterLTs l (S n))); auto.
  assert (forall x, In x (FilterLTs l (S n)) -> In x (AllBelowMinusZero (S n))).
  intros x H0. pose proof (FilterLTs_in _ _ _ H0). pose proof (FilterLTs_lt _ _ _ H0).
  apply InAllBelowMinusZero; auto.
  intro Hcontra; apply n0; apply InFilterLTs; [rewrite <- Hcontra; auto | apply Nat.lt_0_succ].
  assert (NoDup (FilterLTs l (S n))) by apply FilterLTs_NoDup.
  pose proof (SubsetListLength Nat.eq_dec _ _ H0 H1).
  rewrite AllBelowMinusZeroLength in H2. simpl in H2. rewrite Nat.sub_0_r in H2.
  rewrite H in H2. exfalso; eapply Nat.nle_succ_diag_l; eauto.
Qed.


Fixpoint nub {A : Type} (ADec : forall a b : A, {a = b} + {a <> b}) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => if InBool ADec x xs
              then nub ADec xs
              else x :: (nub ADec xs)
  end.

Lemma nub_In : forall {A : Type} ADec (l : list A) (a : A),
    In a l <-> In a (nub ADec l).
Proof.
  intros A ADec l a.
  induction l. simpl; split; auto.
  simpl. destruct (InBool ADec a0 l) eqn:e.
  split; intro H; auto.
  destruct H; [rewrite H in e; rewrite InBoolSpec in e|]; apply IHl; auto.
  right; apply IHl; auto.
  simpl. split; intro H.
  all: destruct H; [left; auto| right; apply IHl; auto].
Qed.

Lemma nub_count_occ_01 : forall {A : Type} ADec (l : list A) (a : A),
    count_occ ADec (nub ADec l) a = 1 \/ count_occ ADec (nub ADec l) a = 0.
Proof.
  intros A ADec l a.
  induction l; simpl. right; auto.
  destruct (InBool ADec a0 l) eqn:e; auto.
  simpl. destruct (ADec a0 a); auto.
  assert (~ In a0 (nub ADec l))
    by (intro H; rewrite InBoolSpec' in e; apply e; rewrite nub_In; exact H).
  left; rewrite e0 in H; pose proof (proj1 (count_occ_not_In ADec (nub ADec l) a) H);
    rewrite H0; auto.
Qed.
  
Lemma nub_count_occ: forall {A : Type} ADec (l : list A) (a : A),
    In a l <-> count_occ ADec (nub ADec l) a = 1.
Proof.
  intros A ADec l a; split; intro H.
  - destruct (nub_count_occ_01 ADec l a); auto; exfalso.
    rewrite (nub_In ADec) in H.
    pose proof ((proj1 (count_occ_In ADec (nub ADec l) a)) H).
    rewrite H0 in H1; inversion H1.
  - rewrite (nub_In ADec); rewrite (count_occ_In ADec); rewrite H; auto.
Qed.  
  
Program Fixpoint WithoutPath {A : Set}
        {a : A} (l : list A) (p : Path a l) {struct p}: list A :=
  match p with
  | Here _ l => l
  | There b pth' => b :: (WithoutPath _ pth')
  end.

Inductive PathToSamePlace {A : Set} : forall (l1 l2 : list A) (a b : A),
    Path a l1 -> Path b l2 -> Prop :=
| BothHere : forall (l : list A) (a : A), PathToSamePlace (a :: l) (a :: l) a a (Here a l) (Here a l)
| BothThere : forall (l1 l2 : list A) (a b c : A) (p1 : Path b l1) (p2 : Path c l2),
    PathToSamePlace l1 l2 b c p1 p2 -> PathToSamePlace (a :: l1) (a :: l2) b c (There a p1) (There a p2).

Lemma PathToSamePlaceSameA : forall {A : Set} (l1 l2 : list A) (a b : A)
                               (p1 : Path a l1) (p2 : Path b l2),
    PathToSamePlace l1 l2 a b p1 p2 -> a = b.
Proof.
  intros A l1 l2 a b p1 p2 H.
  induction H; auto.
Qed.
  
Lemma PathToSamePlaceSameL : forall {A : Set} (l1 l2 : list A) (a b : A)
                               (p1 : Path a l1) (p2 : Path b l2),
    PathToSamePlace l1 l2 a b p1 p2 -> l1 = l2.
Proof.
  intros A l1 l2 a b p1 p2 H.
  induction H; auto.
  rewrite IHPathToSamePlace; auto.
Qed.

Lemma PathToSamePlaceRefl : forall {A : Set} (l : list A) (a : A) (p : Path a l),
    PathToSamePlace l l a a p p.
Proof.
  intros A l a p.
  induction p; try (constructor; auto; fail).
Qed.

Lemma PathToSamePlaceIndexEq : forall {A : Set} (l1 l2 : list A) (a b : A)
                                 (p1 : Path a l1) (p2 : Path b l2),
    PathToSamePlace l1 l2 a b p1 p2 -> PathToIndex p1 = PathToIndex p2.
Proof.
  intros A l1 l2 a b p1 p2 ptsp.
  induction ptsp; simpl; auto.
Qed.

Lemma PathToIndexEqToSamePlace : forall {A : Set} (l : list A) (a b : A)
                                 (p1 : Path a l) (p2 : Path b l),
    PathToIndex p1 = PathToIndex p2 -> PathToSamePlace l l a b p1 p2.
Proof.
  intros A l a b p1 p2 indexEq.
  induction p1 eqn:e; simpl in *.
  - destruct (PathToIndex0_Here p2 (eq_sym indexEq)).
    generalize dependent p2. rewrite H. intros p2 indexEq H0.
    apply JMeq_eq in H0. rewrite H0. constructor.
  - remember (PathToIndexS_There p2 (PathToIndex p) (eq_sym indexEq)).
    clear Heqe0. destruct e0 as [b1 e0]; destruct e0 as [l' e0]; destruct e0 as [pth' H];
                   destruct H as [e1 e2].
    inversion e1. clear e1. generalize dependent p2.
    rewrite H0. generalize dependent pth'. rewrite <- H1.
    intros pth' p2 indexEq e2.
    apply JMeq_eq in e2. rewrite e2. constructor.
    apply IHp with (p1 := p). reflexivity. rewrite e2 in indexEq. simpl in indexEq.
    inversion indexEq; auto.
Qed.

Lemma PathToSamePlaceRecursive :
  forall {A : Set} (l l' : list A) (a b c d : A)  (p1 : Path a l) (p2 : Path b l')
    (Adec : forall a b : A, {a = b} + {a <> b}),
    PathToSamePlace (c :: l) (d :: l') a b (There c p1) (There d p2) ->
    PathToSamePlace l l' a b p1 p2.
Proof.
  intros A l l' a b c d p1 p2 Adec p3.
  inversion p3.
  apply Eqdep_dec.inj_pair2_eq_dec in H6; auto.
  apply Eqdep_dec.inj_pair2_eq_dec in H6; [| apply list_eq_dec; auto].
  apply Eqdep_dec.inj_pair2_eq_dec in H7; auto.
  apply Eqdep_dec.inj_pair2_eq_dec in H7; [| apply list_eq_dec; auto].
  rewrite <- H6. rewrite <- H7. exact H5.
Qed.
  
Program Fixpoint PathToSamePlaceDec
  {A : Set} {l1 l2 : list A} {a b : A} (p1 : Path a l1) (p2 : Path b l2) (Adec : forall x y : A, {x = y} + {x <> y})
  : {PathToSamePlace l1 l2 a b p1 p2} + {~ PathToSamePlace l1 l2 a b p1 p2} :=
  match p1 with
  | Here x l1' => match p2 with
                 | Here y l2' =>
                   match Adec x y with
                   | left e => 
                     match list_eq_dec Adec l1' l2' with
                     | left e => left _
                     | right n => right _
                     end
                   | right n => right _
                   end
                 | There _ _ => right _
                 end
  | There x p1' => match p2 with
                | Here _ _ => right _
                | There y p2' =>
                  match (Adec x y) with
                  | left e => 
                    match (PathToSamePlaceDec p1' p2' Adec) with
                    | left e' => left _
                    | right n => right _
                    end
                  | right n => right _
                  end
                                        
                  end
  end.
Next Obligation.
  constructor.
Defined.
Next Obligation.
  intro H; apply n. apply PathToSamePlaceSameL in H.
  inversion H; auto.
Defined.
Next Obligation.
  intro H; apply n. eapply PathToSamePlaceSameA; exact H.
Defined.
Next Obligation.
  intro H; inversion H.
Defined.
Next Obligation.
  intro H; inversion H.
Defined.
Next Obligation.
  constructor; auto.
Defined.
Next Obligation.
  intro H. apply PathToSamePlaceRecursive in H; auto.
Defined.
Next Obligation.
  intro H. apply PathToSamePlaceSameL in H. inversion H. apply n; auto.
Defined.

  Lemma withoutLiftPath : forall {A : Set} (l : list A) (a b : A) (pth : Path a l), Path b (WithoutPath l pth) -> Path b l. 
  Proof.
    induction pth; simpl; intros.
    apply There; auto.
    inversion H; subst.
    apply Here.
    apply There; auto.
  Qed.

  Program Fixpoint RemoveIndex {A : Set} (l : list A) (n : nat) (corr : n < length l) : list A :=
    match n with
    | 0 => match l with
          | [] => _
          | _ :: l' => l'
          end
    | S m => match l with
            | [] => _
            | a :: l' => a :: (RemoveIndex l' m _)
            end
    end.
  Next Obligation.
    exfalso; inversion corr.
  Defined.
  Next Obligation.
    exfalso; inversion corr.
  Defined.
  Next Obligation.
    simpl in corr; apply Lt.lt_S_n; auto.
  Defined.

  Definition Reindex (n m : nat) : nat :=
    if n <? m
    then m - 1
    else m.

  Fixpoint RemoveIndex' {A : Set} (l : list A) (n : nat) : list A :=
    match l with
    | [] => []
    | a :: l' => match n with
               | 0 => l'
               | S m => a :: (RemoveIndex' l' m)
               end
    end.

  Theorem RemoveIndexWhenCorr : forall {A : Set} (l : list A) (n : nat) (corr : n < length l),
      RemoveIndex l n corr = RemoveIndex' l n.
  Proof.
    intros A l n corr.
    generalize dependent n.
    induction l; intros. inversion corr.
    destruct n. simpl. reflexivity.
    simpl. rewrite IHl. reflexivity.
  Qed.

  Theorem RemoveIndex'Nil : forall {A : Set} (n : nat),
      @RemoveIndex' A [] n = [].
  Proof.
    auto.
  Qed.    
  
  Theorem RemoveIndexNil : forall (A : Set) (n : nat) (corr : n < 0),
      @RemoveIndex A [] n corr = [].
  Proof.
    intros A n corr.
    inversion corr.
  Qed.

  Theorem Reindex'_correct_m_lt : forall {A : Set} (l : list A) (n m : nat),
      m < n -> nth_error l m = nth_error (RemoveIndex' l n) (Reindex n m).
  Proof.
    intros A l n m H.
    unfold Reindex. destruct (n <? m) eqn: n_lt_m.
    apply Nat.ltb_lt in n_lt_m.
    exfalso. eapply Nat.lt_asymm; [exact H | exact n_lt_m].
    apply Nat.ltb_nlt in n_lt_m.
    generalize dependent m. generalize dependent n.
    induction l; intros n m H n_lt_m.
    - simpl. reflexivity.
    - simpl. destruct n. inversion H.
      destruct m. simpl. reflexivity.
      simpl; apply IHl;
        [apply Lt.lt_S_n; exact H| intro H'; apply n_lt_m; apply Lt.lt_n_S; exact H'].
  Qed.      

Program Fixpoint RepathWithoutPath {A : Set} {a1 a2 : A}
        {l : list A} (p1 : Path a1 l) (p2 : Path a2 l)
  (n : ~ PathToSamePlace l l a1 a2 p1 p2) : Path a2 (WithoutPath l p1) :=
  match p1 with
  | Here b l =>
    match p2 with
    | Here _ _ => _
    | There c pth' => pth'
    end
  | There b pth' =>
    match p2 with
    | Here _ l' => Here a2 (WithoutPath l' pth')
    | There c pth'' => There b (RepathWithoutPath pth' pth'' _)
    end
  end.
Next Obligation.
  exfalso; apply n; clear n.
  apply JMeq_eq in Heq_l0.
  apply JMeq_eq in Heq_l.
  pose proof (eq_trans Heq_l0 (eq_sym Heq_l)) as e.
  inversion e.
  assert (PathToIndex p1 = 0)
  by (clear Heq_p2 Heq_l p2 H1 e H0 a2;
      generalize dependent p1;
      rewrite <- Heq_l0; intros p1 Heq_p1; apply JMeq_eq in Heq_p1;
      rewrite <- Heq_p1; simpl; reflexivity).
  assert (PathToIndex p2 = 0)
    by (clear Heq_p1 Heq_l0 p1 H1 e H0 a1 H;
        generalize dependent p2;
        rewrite <- Heq_l;
        intros p2 Heq_p2; apply JMeq_eq in Heq_p2;
        rewrite <- Heq_p2; simpl; reflexivity).
  apply PathToIndexEqToSamePlace; rewrite H; rewrite H2; reflexivity.
Defined.
Next Obligation.
  apply JMeq_eq in Heq_l0.
  apply JMeq_eq in Heq_l.
  pose (eq_trans Heq_l0 (eq_sym Heq_l)).
  inversion e; auto.
Defined.
Next Obligation.
  apply JMeq_eq in Heq_l0.
  apply JMeq_eq in Heq_l.
  pose (eq_trans Heq_l0 (eq_sym Heq_l)).
  inversion e; auto.
Defined.
Next Obligation.
  unfold eq_rect; simpl.
  destruct (RepathWithoutPath_obligation_3 A a1 a2 l p1 p2 a1 b wildcard'0 pth' eq_refl
                                            Heq_l0 Heq_p1 a2 l' eq_refl Heq_l Heq_p2).
  apply JMeq_eq in Heq_l0. apply JMeq_eq in Heq_l.
  pose proof (eq_trans Heq_l0 (eq_sym Heq_l)) as e.
  inversion e. reflexivity.
Defined.
Next Obligation.
  apply JMeq_eq in Heq_l0. apply JMeq_eq in Heq_l.
  pose proof (eq_trans Heq_l0 (eq_sym Heq_l)) as e. inversion e; reflexivity.
Defined.
Next Obligation.
  destruct (RepathWithoutPath_obligation_6 A a1 a2 l p1 p2 a1 b wildcard'2 pth' eq_refl
                                           Heq_l0 Heq_p1 a2 c wildcard'0 pth'' eq_refl Heq_l Heq_p2).
  simpl.
  assert (PathToIndex p2 = S (PathToIndex pth''))
    by (clear Heq_p1 Heq_l0 n b p1 pth';
        generalize dependent p2; apply JMeq_eq in Heq_l; rewrite <- Heq_l;
        intros p2 Heq_p2; apply JMeq_eq in Heq_p2; rewrite <- Heq_p2; simpl; reflexivity).
  assert (PathToIndex p1 = S (PathToIndex pth'))
    by (clear Heq_p2 Heq_l n c p2 pth'' H;
        generalize dependent p1; apply JMeq_eq in Heq_l0; rewrite <- Heq_l0;
        intros p1 Heq_p1; apply JMeq_eq in Heq_p1; rewrite <- Heq_p1; simpl; reflexivity).
  intro Hsame. apply PathToSamePlaceIndexEq in Hsame.
  apply n. apply PathToIndexEqToSamePlace.
  transitivity (S (PathToIndex pth')); auto.
  rewrite Hsame. symmetry; auto.
Defined.

Lemma PathToFront : forall {A : Set} {a : A} {l : list A} (pth : Path a l),
    Permutation l (a :: WithoutPath l pth).
Proof.
  intros A a l pth.
  induction pth; simpl. apply Permutation_refl.
  apply perm_trans with (l' := b :: a :: WithoutPath l pth);
    [apply perm_skip; auto | apply perm_swap].
Qed.
  
Lemma combine_nil_l : forall {A : Type} {B : Type} (l : list B), @combine A B [] l = [].
Proof.
  intros A B l; reflexivity.
Qed.
Lemma combine_nil_r : forall {A : Type} {B : Type} (l : list A), @combine A B l [] = [].
Proof.
  intros A B l; induction l; reflexivity.
Qed.
