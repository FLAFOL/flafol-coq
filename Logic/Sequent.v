Require Export Term. (* We use it enough below to just go ahead and import it directly. *)
Require Export Formula.

Require Import Base.Lists.
Require Import Base.Arith.
Require Import Base.Permutation.
Require Import Tactics.FormulaEquality.
Require Import Tactics.TermEquality.
Require Import Tactics.WellFormedFormulaNoProofs.
Require Import Tactics.TermHasSortNoFormulas.
Require Import Program.Wf.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Logic.JMeq.


Set Bullet Behavior "Strict Subproofs".


Module Type Sequent (G : GroundInfo) (GTerm : Term G) (GFormula : Formula G GTerm)
       (TE : TermEquality G GTerm) (FE : FormulaEquality G GTerm GFormula TE)
       (THS : TermHasSort'' G GTerm TE)
       (WFF : WellFormedFormula' G GTerm TE THS GFormula FE).
  Import G. Import GTerm. Import GFormula. Import ListNotations.
  Import THS. Import WFF.

  Open Scope term_scope. Open Scope formula_scope. Open Scope list_scope.
  Open Scope nat_scope.
  
  (*
    We go ahead and define modes, modalities, PCs, beliefs, and contexts below.
    These are all simple definitions based on the term and formula definitions.
    However, it's convinient to have them.
   *)


  Inductive Modality : Set :=
  | g : flafolTerm -> Modality
  | sim : Modality -> flafolTerm -> flafolTerm -> Modality.
  Notation "m ⋅ p ⟨ l ⟩" := (sim m p l) (at level 20).
  Notation "⟨ l ⟩" := (g l) (at level 20).
  Inductive ProperModality : Modality -> Prop :=
  | gProper : forall lab : flafolTerm,
      ⊢s lab ::: Label -> ProperModality (⟨lab⟩)
  | simProper : forall (m : Modality) (p lab : flafolTerm),
      ProperModality m -> ⊢s p ::: Principal -> ⊢s lab ::: Label ->
      ProperModality (m ⋅ p⟨lab⟩).
  Fixpoint ProperModality' (m : Modality) : Prop :=
      match m with
      | ⟨l⟩ => ⊢s l ::: Label
      | m' ⋅ p⟨l⟩ => ⊢s p ::: Principal /\ ⊢s l ::: Label
                        /\ ProperModality' m'
      end.
  Lemma ProperModalitySingular : forall m, ProperModality m <-> ProperModality' m.
  Proof.
    intros m; split; intro H; induction m;
      try (inversion H; simpl; auto; fail);
      try (simpl in H; constructor; auto; fail);
    simpl in H; destruct H as [H1 H2]; destruct H2 as [H2 H3]; 
      try (constructor; auto; fail).
  Qed.

  Lemma ConsProperModality : forall (p lab: flafolTerm) (m : Modality),
      ProperModality (m ⋅ p⟨lab⟩) -> ⊢s p ::: Principal /\ ⊢s lab ::: Label /\ ProperModality m.
  Proof.
    intros p lab m H.
    inversion H; split; [| split]; auto.
  Qed.

  Reserved Infix "∈FVM" (at level 40).
  Inductive FreeInModality : var -> Modality -> Prop :=
    freeInGLabel : forall (x : var) (l pc : flafolTerm), x ∈FVT l -> x ∈FVM (⟨l⟩)
  | freeInSimulator : forall (x : var) (m : Modality) (p l: flafolTerm),
      x ∈FVM m -> x ∈FVM (m ⋅ p⟨l⟩)
  | freeInSimPrincipal : forall (x : var) (m : Modality) (p l: flafolTerm),
      x ∈FVT p -> x ∈FVM (m ⋅ p⟨l⟩)
  | freeInSimLabel : forall (x : var) (m : Modality) (p l : flafolTerm),
      x ∈FVT l -> x ∈FVM (m ⋅ p⟨l⟩)
  where "x ∈FVM m" := (FreeInModality x m).
  Notation "x ∉FVM m" := (~ FreeInModality x m) (at level 40).
  Lemma NotFVMSim : forall (m : Modality) (p l: flafolTerm) (x : var),
      x ∉FVM m -> x ∉FVT p -> x ∉FVT l -> x ∉FVM (m ⋅ p⟨l⟩).
  Proof.
    intro m; destruct m as [l2 | m' q l2]; intros p l1 x Hm Hp Hl.
    all: intro Hc; inversion Hc; [apply Hm | apply Hp | apply Hl ]; auto.
  Qed.

  Lemma NotFVMSimInversion : forall (m : Modality) (p l : flafolTerm) (x : var),
      x ∉FVM (m ⋅ p⟨l⟩) -> x ∉FVM m /\ x ∉FVT p /\ x ∉FVT l.
  Proof.
    intros m p l x H.
    split; [| split]; intro H'; apply H; try (constructor; auto; fail).
  Qed.
  Fixpoint varsInModality (m : Modality) : list var :=
    match m with
    | g l => (varsInTerm l)
    | m' ⋅ p⟨l⟩ => (varsInModality m') ++ (varsInTerm p) ++ (varsInTerm l)
    end.
  Lemma FreeVarsInModality : forall (x : var) (m : Modality),
      x ∈FVM m <-> In x (varsInModality m).
  Proof.
    intros x m; revert x; induction m; intro x; split; intro H;
      match goal with
      | [ H : ?x ∈FVM ?m |- _ ] => inversion H
      | _ => idtac
      end.
    - simpl. apply varsInTermFVT; auto.
    - simpl in H. apply freeInGLabel; eauto.
      apply varsInTermFVT; auto.
    - simpl; apply in_or_app; left; apply IHm; auto.
    - simpl; apply in_or_app; right; apply in_or_app; left; apply varsInTermFVT; auto.
    - simpl; apply in_or_app; right; apply in_or_app; right;
        apply varsInTermFVT; auto.
    - simpl in H. apply in_app_or in H; destruct H;
                    try (constructor; apply IHm; auto; fail).
      apply in_app_or in H; destruct H; try (constructor; apply varsInTermFVT; auto; fail).
  Qed.
  Definition freshInModality (m : Modality) (sigma : sort) : var :=
    freshVar (varsInModality m) sigma.
  Lemma freshInModalityOfSort : forall (m : Modality) (sigma : sort),
      VarSort (freshInModality m sigma) = sigma.
  Proof.
    intros; unfold freshInModality; apply freshVarSameSort; auto.
  Qed.
  Lemma freshInModalityIsFresh : forall (m : Modality) (sigma : sort),
      (freshInModality m sigma) ∉FVM m.
  Proof.
    intros m sigma; induction m; intros H;
      inversion H; subst; unfold freshInModality in H2; simpl in H2;
    [apply varsInTermFVT in H2 |
       apply FreeVarsInModality in H2 | apply varsInTermFVT in H2
       | apply varsInTermFVT in H2]. eapply freshVarNotIn; eauto.    
    all: try lazymatch goal with
      | [ H : In (freshVar (?l1 ++ ?l2) ?rho) ?l1 |- False ] =>
        apply freshVarNotIn with (sigma := rho) (vs := l1 ++ l2);
          apply in_or_app; left; auto
      | [ H : In (freshVar (?l1 ++ ?l2) ?rho) ?l2 |- False ] =>
        apply freshVarNotIn with (sigma := rho) (vs := l1 ++ l2);
          apply in_or_app; right; auto
      | [ H : In (freshVar (?l1 ++ ?l2 ++ ?l3) ?rho) ?l1 |- False ] =>
        apply freshVarNotIn with (sigma := rho) (vs := l1 ++ l2 ++ l3);
          apply in_or_app; left; auto
      | [ H : In (freshVar (?l1 ++ ?l2 ++ ?l3) ?rho) ?l2 |- False ] =>
        apply freshVarNotIn with (sigma := rho) (vs := l1 ++ l2 ++ l3);
          apply in_or_app; right; apply in_or_app; left; auto
      | [ H : In (freshVar (?l1 ++ ?l2 ++ ?l3) ?rho) ?l3 |- False ] =>
        apply freshVarNotIn with (sigma := rho) (vs := l1 ++ l2 ++ l3);
          apply in_or_app; right; apply in_or_app; right; auto
      end.
  Qed.

  Definition FreeInModalityDec (x : var) (m : Modality) : {x ∈FVM m} + {x ∉FVM m}.
    induction m as [l | m' IHm p l].
    destruct (freeInTermDec x l); [left; constructor; auto; fail | ].
    right; intro Hc; inversion Hc; apply n; auto.
    destruct IHm; [left; constructor; auto; fail|].
    destruct (freeInTermDec x p); [left; constructor; auto; fail |].
    destruct (freeInTermDec x l); [left; constructor; auto; fail |].
    right; intro Hc; inversion Hc; [apply n | apply n0 | apply n1 ]; auto.
  Defined.
  
  Definition ModalityEqDec : forall m1 m2 : Modality, {m1 = m2} + {m1 <> m2}.
    decide equality; auto with eq_dec.
  Defined.
  Hint Resolve ModalityEqDec : eq_dec.
  Definition InnermostLabel (m : Modality) : flafolTerm :=
    match m with
    | ⟨lab⟩ => lab
    | _ ⋅ _ ⟨lab⟩ => lab
    end.
  Lemma InnermostLabelProper : forall (m : Modality),
      ProperModality m -> ⊢s (InnermostLabel m) ::: Label.
  Proof.
    intros m H; inversion H; auto.
  Qed.

  Inductive PathToPrinInModality : Modality -> flafolTerm -> Set :=
  | hereSimP : forall (m : Modality) (p lab : flafolTerm),
      PathToPrinInModality (m ⋅ p⟨lab⟩) p
  | thereP : forall (m : Modality) (p q lab : flafolTerm),
      PathToPrinInModality m p -> PathToPrinInModality (m ⋅ q⟨lab⟩) p.

  Inductive PathToLabelInModality : Modality -> flafolTerm -> Set :=
  | hereGLab : forall lab : flafolTerm, PathToLabelInModality (⟨lab⟩) lab
  | hereSimLab : forall (m : Modality) (p lab : flafolTerm),
      PathToLabelInModality (m ⋅ p⟨lab⟩) lab
  | thereLab : forall (m : Modality) (p lab lab' : flafolTerm),
      PathToLabelInModality m lab -> PathToLabelInModality (m ⋅ p⟨lab'⟩) lab.

  Inductive PathToDoubleInModality : Modality -> Set :=
  | hereDouble : forall m p l,  PathToDoubleInModality (m ⋅ p⟨l⟩ ⋅ p⟨l⟩)
  | thereDouble : forall m p l,
      PathToDoubleInModality m -> PathToDoubleInModality (m ⋅ p⟨l⟩).
  
  Program Fixpoint ReplacePrinInModality
          {m : Modality} {p : flafolTerm} (pth : PathToPrinInModality m p) (q : flafolTerm) : Modality :=
    match pth with
    | hereSimP m _ lab => m ⋅ q⟨lab⟩
    | thereP m _ r lab pth' => (ReplacePrinInModality pth' q) ⋅ r ⟨lab⟩
    end.

  Program Fixpoint ReplaceLabelInModality
          (m : Modality) (lab lab' : flafolTerm) (pi : PathToLabelInModality m lab)
    : Modality :=
    match pi with
    | hereGLab _ => ⟨lab'⟩
    | hereSimLab m' p _ => m' ⋅ p⟨lab'⟩
    | thereLab m' p _ lab'' rho => (ReplaceLabelInModality m' lab lab' rho) ⋅ p⟨lab''⟩
    end.


  Program Fixpoint CollapseDoubleInModality
          {m : Modality} (pth : PathToDoubleInModality m) : Modality :=
    match pth with
    | hereDouble m p l => m ⋅ p⟨l⟩
    | thereDouble m p l pth' => (CollapseDoubleInModality pth') ⋅ p⟨l⟩
    end.


  
  Theorem ReplacePrinInModalityProper : forall (m : Modality) (p q : flafolTerm) (pth : PathToPrinInModality m p),
      ProperModality m -> ⊢s q ::: Principal ->
      ProperModality (ReplacePrinInModality pth q).
  Proof.
    intros m p q pth H H0.
    induction pth; simpl; inversion H; constructor; auto.
  Qed.

  Theorem ReplacePrinInModalityProper' : forall (m : Modality) (p q : flafolTerm)
                                           (pth : PathToPrinInModality m p),
       ⊢s p ::: Principal ->
       ProperModality (ReplacePrinInModality pth q) ->
       ProperModality m.
  Proof.
    intros m p q pth H H0.
    induction pth; simpl in *; inversion H0; constructor; auto.
  Qed.
  
  Theorem ReplaceLabelInModalityProper : forall (m : Modality) (l l' : flafolTerm)
                                        (pth : PathToLabelInModality m l),
      ProperModality m -> ⊢s l' ::: Label ->
      ProperModality (ReplaceLabelInModality m l l' pth).
  Proof.
    intros m l l' pth H H0.
    induction pth; simpl; inversion H; constructor; auto.
  Qed.
  
  Theorem ReplaceLabelInModalityProper' : forall (m : Modality) (l l' : flafolTerm)
                                        (pth : PathToLabelInModality m l),
      ProperModality (ReplaceLabelInModality m l l' pth) -> ⊢s l ::: Label ->
      ProperModality m.
  Proof.
    intros m l l' pth H lsort. induction pth; simpl in *;
    [| inversion H | inversion H]; constructor; auto.
  Qed.

  Theorem CollapseDoubleProper : forall (m : Modality) (pth : PathToDoubleInModality m),
      ProperModality m -> ProperModality (CollapseDoubleInModality pth).
  Proof.
    intros m pth H.
    induction pth; simpl.
    inversion H; inversion H3; constructor; auto; fail.
    inversion H; constructor; auto.
  Qed.

  Theorem CollapseDoubleProper' : forall (m : Modality) (pth : PathToDoubleInModality m),
      ProperModality (CollapseDoubleInModality pth) -> ProperModality m.
  Proof.
    intros m pth H.
    induction pth; simpl in *.
    inversion H; constructor; auto.
    inversion H; constructor; auto.
  Qed.


  Program Fixpoint ModalityBeforePrin
          {m : Modality} {p : flafolTerm} (pth : PathToPrinInModality m p) : Modality :=
    match pth with
    | hereSimP m _ lab => m
    | thereP m _ q lab pth' => ModalityBeforePrin pth'
    end.

  Program Fixpoint LabelAtPrin
          {m : Modality} {p : flafolTerm} (pth : PathToPrinInModality m p) : flafolTerm :=
    match pth with
    | hereSimP _ _ lab => lab
    | thereP m _ _ _ pth' => LabelAtPrin pth'
    end.

  Definition ModalityResidual : Set := list (flafolTerm * flafolTerm).

  Definition ProperModalityResidual : ModalityResidual -> Prop :=
    fun m => forall p l , In (p, l) m ->
                    ⊢s p ::: Principal /\ ⊢s l ::: Label.

  Theorem ProperModalityResidualApp : forall (m m' : ModalityResidual),
      ProperModalityResidual m -> ProperModalityResidual m' ->
      ProperModalityResidual (m ++ m').
  Proof.
    intros m m' H H0.
    induction m; auto.
    simpl. unfold ProperModalityResidual. intros p l H1.
    simpl in H1. destruct H1.
    apply H. left; auto.
    apply in_app_or in H1; destruct H1.
    apply H; right; auto.
    apply H0; auto.
  Qed.

  Theorem ProperModalityResidualCons : forall (m : ModalityResidual) (p l : flafolTerm),
      ⊢s p ::: Principal -> ⊢s l ::: Label -> ProperModalityResidual m
      -> ProperModalityResidual ((p, l) :: m).
  Proof.
    intros m p l H H0 H1.
    unfold ProperModalityResidual; intros.
    inversion H2; [| apply H1; auto].
    inversion H3. rewrite <- H5; rewrite <- H6.
    split; auto.
  Qed.

  Theorem ProperModalityResidualConsInv : forall (m : ModalityResidual) (p l : flafolTerm),
      ProperModalityResidual ((p, l) :: m) ->
      ⊢s p ::: Principal /\ ⊢s l ::: Label /\ ProperModalityResidual m.
  Proof.
    intros m p l H; unfold ProperModalityResidual in H; split; [| split; [| split]];
    try (specialize (H p l (or_introl eq_refl));
         repeat match goal with
                | [ H : _ /\ _ |- _ ] => destruct H
                end; auto; fail).
    all: specialize (H p0 l0 (or_intror H0)); apply H.
  Qed.
  
  Reserved Infix "∈FVMR" (at level 40).
  Inductive freeInModalityResidual : var -> ModalityResidual -> Prop :=
  | FreeInHerePMR : forall (x : var) (p l : flafolTerm) (m : ModalityResidual),
      x ∈FVT p -> x ∈FVMR ((p, l) :: m)
  | FreeInHereLMR : forall (x : var) (p l : flafolTerm) (m : ModalityResidual),
      x ∈FVT l -> x ∈FVMR ((p, l) :: m)
  | FreeOverThereMR : forall (x : var) (p l : flafolTerm) (m : ModalityResidual),
      x ∈FVMR m -> x ∈FVMR ((p, l) :: m)
  where "x ∈FVMR m" := (freeInModalityResidual x m).

  
  Program Fixpoint ModalityAfterPrin
          {m : Modality} {p : flafolTerm} (pth : PathToPrinInModality m p)
    : ModalityResidual :=
    match pth with
    | hereSimP m _ _ => []
    | thereP m _ q lab pth' => ModalityAfterPrin pth' ++ [(q, lab)]
    end.

  Theorem ModalityAfterPrinProper : forall {m : Modality} {p : flafolTerm}
                                      (pth : PathToPrinInModality m p),
      ProperModality m -> ProperModalityResidual (ModalityAfterPrin pth).
  Proof.
    intros m p pth; induction pth; intro pmod; simpl; auto.
    unfold ProperModalityResidual; intros p0 l H; inversion H.
    inversion pmod.
    apply ProperModalityResidualApp. apply IHpth; auto.
    unfold ProperModalityResidual. intros p1 l H5.
    destruct H5; inversion H5. split.  rewrite <- H7; auto. rewrite <- H8; auto.
  Qed.


  Program Fixpoint ModalityCombine
          (m : Modality) (m' : ModalityResidual) : Modality :=
    match m' with
    | [] => m
    | p :: m' => match p with
               | (q, lab) => ModalityCombine (m ⋅ q⟨lab⟩) m'
               end
    end.

  Lemma ModalityCombineApp1 : forall (m : Modality) (m' : ModalityResidual)
                               (p lab : flafolTerm),
      ModalityCombine m (m' ++ [(p, lab)]) = (ModalityCombine m m') ⋅ p⟨lab⟩.
  Proof.
    intros m m' p lab; generalize dependent m.
    induction m'; intros m; simpl; auto.
    destruct a; apply IHm'.
  Qed.

    Lemma ModalityCombineApp : forall m0 m1 m, ModalityCombine (ModalityCombine m m0) m1 = ModalityCombine m (m0 ++ m1).
  Proof.
    induction m0; intros; auto.
    simpl.
    destruct a.
    rewrite IHm0.
    reflexivity.
  Qed.

  Lemma ModalityResidualAppProper : forall m0 m1, ProperModalityResidual m0 -> ProperModalityResidual m1 -> ProperModalityResidual (m0 ++ m1).
  Proof.
    induction m0; simpl; auto.
    intros.
    destruct a.
    intro.
    intros.
    simpl in H1.
    destruct H1.
    apply H.
    left; auto.
    pose proof (IHm0 m1).
    revert H1.
    apply IHm0; auto.
    intro.
    intros.
    apply H.
    right; auto.
  Qed.

  Lemma ModalityCombineFuse : forall (m : Modality) (m' m'' : ModalityResidual),
      ModalityCombine (ModalityCombine m m') m'' = ModalityCombine m (m' ++ m'').
  Proof.
    intros m m' m''.
    generalize dependent m.
    induction m'; intro m; simpl. reflexivity.
    destruct a.
    rewrite IHm'. reflexivity.
  Qed.

  Fixpoint PathToLabelInModalityCombine {m : Modality} {l : flafolTerm}
           (pth : PathToLabelInModality m l) (mr : ModalityResidual) :
    PathToLabelInModality (ModalityCombine m mr) l :=
    match mr with
    | [] => pth
    | pr :: mr' => match pr with
                 | (p, l') => PathToLabelInModalityCombine (thereLab m p l l' pth) mr'
                 end
    end.

  
  Fixpoint ModalityBottomsOut (m : Modality) (l : flafolTerm) : bool :=
    match m with
    | ⟨l'⟩ => if termEqDec l l' then true else false
    | m' ⋅ _⟨_⟩ => ModalityBottomsOut m' l
    end.

  Fixpoint FullModalityResidual (m : Modality) : ModalityResidual :=
    match m with
    | ⟨_⟩ => []
    | m' ⋅ p⟨l⟩ =>  FullModalityResidual m' ++ [(p, l)]
    end.

  Theorem FullModalityResidualCombine : forall (m : Modality) (mr : ModalityResidual),
      FullModalityResidual (ModalityCombine m mr) = FullModalityResidual m ++ mr.
  Proof.
    intros m mr; revert m; induction mr; intro m.
    simpl; rewrite app_nil_r; reflexivity.
    simpl. destruct a as [p l].
    specialize (IHmr (m ⋅ p⟨l⟩)). simpl in IHmr.
    rewrite <- app_assoc in IHmr. simpl in IHmr. exact IHmr.
  Qed.

  Theorem FullModalityResidualProper : forall (m : Modality),
      ProperModality m -> ProperModalityResidual (FullModalityResidual m).
  Proof.
    intro m; induction m as [l | m IHm p l]; intro H.
    simpl; unfold ProperModalityResidual; intros p l' H0; inversion H0.
    simpl. inversion H.
    unfold ProperModalityResidual. intros p1 l0 H6.
    apply in_app_or in H6. destruct H6.
    apply IHm; auto.
    destruct H6; inversion H6.
    rewrite <- H8. rewrite <- H9. split; auto.
  Qed.


  Theorem ModalityBottomsOut_spec : forall (m : Modality) (l : flafolTerm),
      ModalityBottomsOut m l = true -> m = ModalityCombine (⟨l⟩) (FullModalityResidual m).
  Proof.
    intros m; induction m as [l | m' p l]; intros l' H.
    simpl in H. destruct (termEqDec l' l). rewrite e. simpl. reflexivity.
    inversion H.
    simpl. rewrite ModalityCombineApp1. simpl.
    rewrite <- p; auto.
  Qed.

  Lemma ModalityBottomsOutCombination : forall (mr : ModalityResidual) (m : Modality)
                                          (l : flafolTerm),
      ModalityBottomsOut (ModalityCombine m mr) l = ModalityBottomsOut m l.
  Proof.
    intro mr; induction mr as [| pr mr']; [|destruct pr as [p l']]; intros m l.
    simpl; reflexivity.
    simpl. specialize (IHmr' (m ⋅ p⟨l'⟩) l). simpl in IHmr'. auto.
  Qed.
  
  Fixpoint ModalityExtension (m1 m2 : Modality) : option ModalityResidual :=
    match m1 with
    | ⟨l1⟩ => if ModalityBottomsOut m2 l1 then Some (FullModalityResidual m2) else None
    | m1' ⋅ p1⟨l1⟩ =>
      match ModalityExtension m1' m2 with
      | Some mr =>
        match mr with
        | [] => None
        | pr :: mr' => match pr with
                     | (p2, l2) => if termEqDec p1 p2
                                  then if termEqDec l1 l2
                                       then Some mr'
                                       else None
                                  else None
                     end
        end
      | None => None
      end
    end.

  Theorem ModalityExtension_spec : forall (m1 m2 : Modality) (mr : ModalityResidual),
      ModalityExtension m1 m2 = Some mr -> m2 = ModalityCombine m1 mr.
  Proof.
    intro m1; induction m1 as [l | m1' IHm1 p1 l1]; intros m2 mr H;
      simpl in *.
    destruct (ModalityBottomsOut m2 l) eqn:e.
    inversion H. apply ModalityBottomsOut_spec; auto.
    inversion H.
    destruct (ModalityExtension m1' m2) eqn:e; [| inversion H].
    destruct m; [inversion H|].
    destruct p as [p2 l2]; destruct (termEqDec p1 p2); destruct (termEqDec l1 l2);
      try (inversion H; fail).
    specialize (IHm1 m2 ((p2, l2) :: m) e). simpl in IHm1.
    inversion H. rewrite H1 in IHm1; rewrite e0; rewrite e1; auto.
  Qed.

  Theorem ModalityExtensionOfCombination : forall (m : Modality) (mr : ModalityResidual),
      ModalityExtension m (ModalityCombine m mr) = Some mr.
  Proof.
    intro m; induction m as [l | m' IHm p l]; intro mr.
    simpl. rewrite ModalityBottomsOutCombination. simpl.
    destruct (termEqDec l l) as [e | n]; [clear e | exfalso; apply n; reflexivity].
    rewrite FullModalityResidualCombine. simpl. reflexivity.
    simpl.
    assert (ModalityCombine (m' ⋅ p⟨l⟩) mr = ModalityCombine m' ((p, l) :: mr))
      by (simpl; reflexivity).
    rewrite H. rewrite IHm.
    destruct (termEqDec p p) as [_|n]; [|exfalso; apply n; reflexivity].
    destruct (termEqDec l l) as [_|n]; [|exfalso; apply n; reflexivity].
    reflexivity.
  Qed.


    

  
  Lemma ModalityExtension_same : forall m : Modality,
      ModalityExtension m m = Some [].
  Proof.
    intros m.
    assert (m = ModalityCombine m []) by auto.
    rewrite H at 2. apply ModalityExtensionOfCombination.
  Qed.

  Theorem ModalityExtension_sim : forall (m1 m2 : Modality) (mr : ModalityResidual)
                                    (p l : flafolTerm),
      ModalityExtension (m1 ⋅ p⟨l⟩) m2 = Some mr -> ModalityExtension m1 m2 = Some ((p,l) :: mr).
  Proof.
    intros m1 m2 mr p l H.
    simpl in H. destruct (ModalityExtension m1 m2) eqn:e; [| inversion H].
    destruct m; [inversion H|].
    destruct p0 as [p2 l2]. destruct (termEqDec p p2); [| inversion H].
    destruct (termEqDec l l2); [| inversion H].
    inversion H. rewrite e0. rewrite e1. reflexivity.
  Qed.

  Theorem ModalityExtensionCombined : forall (m1 m2 : Modality) (mr1 mr2 : ModalityResidual),
      ModalityExtension (ModalityCombine m1 mr1) m2 = Some mr2 ->
      ModalityExtension m1 m2  = Some (mr1 ++ mr2).
  Proof.
    intros m1 m2 mr1; revert m1 m2; induction mr1; intros m1 m2 mr2 H; simpl in *.
    auto.
    destruct a as [p l].
    apply IHmr1 in H.
    rewrite ModalityExtension_sim with (p := p) (l := l) (mr := mr1 ++ mr2). reflexivity.
    exact H.
  Qed.
  
  Lemma ModalityCombineToGround : forall (m : Modality) (mr : ModalityResidual) (l : flafolTerm),
      ModalityCombine m mr = ⟨l⟩ -> m = ⟨l⟩ /\ mr = [].
  Proof.
    intros m mr; revert m; induction mr; intros m l H; [simpl in H; split; auto|]. 
    simpl in H.  destruct a. apply IHmr in H.
    destruct H. inversion H.
  Qed.


  Lemma ModalityExtensionComplete : forall (m1 m2 : Modality),
      ModalityExtension m1 m2 = None -> forall mr : ModalityResidual,
        ModalityCombine m1 mr <> m2.
  Proof.
    intros m1 m2 H mr. intro H0. rewrite <- H0 in H.
    rewrite ModalityExtensionOfCombination in H. inversion H.
  Qed.

  Lemma ModalityExtensionExtendedNone : forall (m1 m2 : Modality) (mr : ModalityResidual),
      ModalityExtension m1 m2 = None -> ModalityExtension (ModalityCombine m1 mr) m2 = None.
  Proof.
    intros m1 m2 mr H.
    pose proof (ModalityExtensionComplete _ _ H).
    destruct (ModalityExtension (ModalityCombine m1 mr) m2) eqn:e; auto.
    pose proof (ModalityExtension_spec _ _ _ e).
    specialize (H0 (mr ++ m)).
    exfalso; apply H0. rewrite <- ModalityCombineApp.
    auto.
  Qed.

  Theorem ModalityExtensionProper : forall (m1 m2 : Modality) (mr : ModalityResidual),
      ProperModality m2 -> ModalityExtension m1 m2 = Some mr ->
      ProperModalityResidual mr.
  Proof.
    intros m1; induction m1 as [l | m1 IHm1 p l]; intros m2 mr H H0.
    - simpl in H0;
        destruct (ModalityBottomsOut m2 l); inversion H0;
          apply FullModalityResidualProper; auto.
    - simpl in H0.
      destruct (ModalityExtension m1 m2) eqn:e; [| inversion H0].
      destruct m; [inversion H0|]. destruct p0 as [p2 l2].
      destruct (termEqDec p p2); [|inversion H0];
        destruct (termEqDec l l2); [| inversion H0].
      specialize (IHm1 m2 ((p2, l2) :: m) H e).
      inversion H0. rewrite H2 in IHm1.
      apply ProperModalityResidualConsInv in IHm1.
      destruct IHm1 as [H1 H3]; destruct H3; auto.
  Qed.
  
  Fixpoint ModalitySize (m : Modality) : nat :=
    match m with
    | ⟨_⟩ => 1
    | m' ⋅ _⟨_⟩ => S (ModalitySize m')
    end.

  Theorem ModalityCombineSizeInv : forall m mr,
      ModalitySize (ModalityCombine m mr) = ModalitySize m + length mr.
  Proof.
    intros m mr. revert m.
    induction mr; intro m.
    simpl. symmetry; apply PeanoNat.Nat.add_0_r.
    simpl. destruct a.  rewrite IHmr. simpl.
    symmetry. rewrite PeanoNat.Nat.add_comm at 1. rewrite plus_Sn_m.
    rewrite PeanoNat.Nat.add_comm. reflexivity.
  Qed.
  Theorem ModalityCombineIdentUnique : forall m mr, m = ModalityCombine m mr -> mr = [].
  Proof.
    intros m mr H.
    pose proof (eq_trans (f_equal ModalitySize H) (ModalityCombineSizeInv m mr)).
    pose proof (ZeroUniqueIdent H0).
    apply length_zero_iff_nil. exact H1.
  Qed.

  Lemma ModalityCombineOnlySim : forall m mr p l,
      m ⋅ p⟨l⟩ = ModalityCombine m mr -> mr = [(p, l)].
  Proof.
    intros m mr p l H.
    pose proof (eq_trans (f_equal ModalitySize H) (ModalityCombineSizeInv m mr)).
    simpl in H0. apply OneUniqueS in H0.
    destruct mr. simpl in H0. inversion H0.
    simpl in H0. inversion H0. rewrite length_zero_iff_nil in H2.
    rewrite H2 in H. simpl in H. destruct p0. inversion H.
    rewrite H2. reflexivity.
  Qed.


  Lemma ModalityCombineGenericInj : forall (m1 m2 : Modality) (mr1 mr2 : ModalityResidual),
      ModalityCombine m1 mr1 = ModalityCombine m2 mr2 ->
      length mr1 = length mr2 ->
      m1 = m2 /\ mr1 = mr2.
  Proof.
    intros m1 m2 mr1.
    revert m1 m2. induction mr1 as [| a mr1];
    intros m1 m2 mr2 H H0;
    [pose proof (eq_trans (eq_sym (ModalityCombineSizeInv m1 []))
                         (eq_trans (f_equal ModalitySize H)
                                   (ModalityCombineSizeInv m2 mr2)))
     | pose proof (eq_trans (eq_sym (ModalityCombineSizeInv m1 (a :: mr1)))
                         (eq_trans (f_equal ModalitySize H)
                                   (ModalityCombineSizeInv m2 mr2)))];
    rewrite H0 in H1;
    assert (ModalitySize m1 = ModalitySize m2)
      by (remember (ModalitySize m1) as n1; remember (ModalitySize m2) as n2;
          remember (length mr2) as m; clear m1 m2 mr2 H Heqm Heqn1 Heqn2 H0; try (clear mr1);
          induction m;
          [repeat (rewrite PeanoNat.Nat.add_0_r in H1); exact H1 
          | repeat rewrite <- plus_n_Sm in H1; inversion H1; apply IHm; exact H0]).
    - symmetry in H0; rewrite length_zero_iff_nil in H0; rewrite H0 in H.
      simpl in H. split; auto.
    - destruct mr2; simpl in H0; [inversion H0|].
      simpl in H. destruct p as [q l2]. destruct a as [p l1].
      inversion H0.
      specialize (IHmr1 (m1 ⋅ p⟨l1⟩) (m2 ⋅ q⟨l2⟩) mr2 H H4).
      destruct IHmr1. inversion H3.
      split; auto. rewrite H5. reflexivity.
  Qed.
  
  Lemma ModalityCombineInj2 : forall (m : Modality) (mr1 mr2 : ModalityResidual),
      ModalityCombine m mr1 = ModalityCombine m mr2 -> mr1 = mr2.
  Proof.
    intros m mr1 mr2 H.
    assert (length mr1 = length mr2)
      by (pose proof (eq_trans (eq_sym (ModalityCombineSizeInv m mr1))
                               (eq_trans (f_equal ModalitySize H)
                                         (ModalityCombineSizeInv m mr2)));
          remember (ModalitySize m) as n;
          clear m Heqn H; remember (length mr1) as m1; remember (length mr2) as m2;
          clear mr1 Heqm1 mr2 Heqm2;
          induction n; simpl in H0; [exact H0 |inversion H0; apply IHn; exact H1]).
    pose proof (ModalityCombineGenericInj m m mr1 mr2 H H0).
    destruct H1; auto.
  Qed.

  
  Lemma ModalityCombineProper : forall (m : Modality) (m' : ModalityResidual),
      ProperModality m ->
      ProperModalityResidual m' ->
      ProperModality (ModalityCombine m m').
  Proof.
    intros m m'.
    generalize dependent m; induction m'; intros m H H0. simpl; auto.
    simpl in *. destruct a.
    apply IHm'.
    specialize (H0 f f0). constructor; auto; apply H0; left; auto.
    intros p l0 H1. apply H0; right; auto.
  Qed.

  Theorem ModalityRestitchPrin : forall (m : Modality) (p : flafolTerm)
                               (pth : PathToPrinInModality m p),
      m = ModalityCombine ((ModalityBeforePrin pth) ⋅ p⟨LabelAtPrin pth⟩) (ModalityAfterPrin pth).
  Proof.
    intros m p pth.
    induction pth; simpl; auto.
    rewrite ModalityCombineApp1.
    rewrite <- IHpth. auto.
  Qed.

  Theorem ModalityRestitchReplacePrin : forall {m : Modality} {p : flafolTerm}
                                          (pth : PathToPrinInModality m p) (q : flafolTerm),
      ReplacePrinInModality pth q =
      ModalityCombine ((ModalityBeforePrin pth) ⋅ q⟨(LabelAtPrin pth)⟩)
                      (ModalityAfterPrin pth).
  Proof.
    intros m p pth; induction pth; simpl; intros r; auto.
    rewrite IHpth. rewrite <- ModalityCombineApp. simpl. reflexivity.
  Qed.

  Fixpoint ModalityResidualSays (m : ModalityResidual) (phi : flafolFormula) : flafolFormula :=
    match m with
    | [] => phi
    | t :: m' => let (p, l) := t in
               p □ ⟨l⟩ (ModalityResidualSays m' phi)
    end.

  Theorem ModalityResidualSaysWF : forall (m : ModalityResidual) (phi : flafolFormula),
      ⊢wff phi -> ProperModalityResidual m -> ⊢wff (ModalityResidualSays m phi).
  Proof.
    intros m; induction m; intros phi phi_wf m_proper; simpl; auto.
    destruct a.
    apply ProperModalityResidualConsInv in m_proper.
    repeat match goal with
           | [ H : _ /\ _ |- _ ] => destruct H
           end.
    constructor; auto.
  Qed.

  Fixpoint ModalityAfterGround (m : Modality) : ModalityResidual :=
    match m with
    | ⟨l⟩ => []
    | m ⋅ p⟨l⟩ => (ModalityAfterGround m) ++ [(p, l)]
    end.

  Fixpoint GroundLabel (m : Modality) : flafolTerm :=
    match m with
    | ⟨l⟩ => l
    | m ⋅ _⟨_⟩ => GroundLabel m
    end.

  Theorem ModalityGroundPlusAfter : forall (m : Modality),
      m = ModalityCombine (⟨GroundLabel m⟩) (ModalityAfterGround m).
  Proof.
    intros m; induction m; simpl; auto.
    rewrite ModalityCombineApp1. rewrite IHm at 1. reflexivity.
  Qed.

  Theorem ModalityAfterGroundProper : forall (m : Modality),
      ProperModality m -> ProperModalityResidual (ModalityAfterGround m).
  Proof.
    intros m; induction m; intro pmod; simpl in *.
    unfold ProperModalityResidual; intros p l Hc; inversion Hc.
    unfold ProperModalityResidual in *.
    intros p l H.
    apply ConsProperModality in pmod;
      repeat match goal with
             | [ H : _ /\ _ |- _ ] => destruct H
             end.
    apply in_app_or in H.
    destruct H; [apply IHm | ]; auto.
    destruct H; inversion H.
    rewrite <- H5; rewrite <- H4; split; auto.
  Qed.

  Theorem GroundLabelProper : forall (m : Modality),
      ProperModality m -> ⊢s GroundLabel m ::: Label.
  Proof.
    intro m; induction m as [l | m' IHm p l] ; intro pmod; simpl in *.
    inversion pmod; auto.
    apply IHm; apply ConsProperModality in pmod; auto.
    destruct pmod as [_ H]; destruct H as [_ H]; auto.
  Qed.

  Definition ModalitySays (m : Modality) (phi : flafolFormula) :=
    ModalityResidualSays (ModalityAfterGround m) phi.

  Theorem ModalitySaysWF : forall (m : Modality) (phi : flafolFormula),
      ProperModality m -> ⊢wff phi -> ⊢wff (ModalitySays m phi).
  Proof.
    intros m phi pmod phi_wf.
    unfold ModalitySays.
    apply ModalityResidualSaysWF; auto.
    apply ModalityAfterGroundProper; auto.
  Qed.
    
  Program Fixpoint ModalityBeforeLabel {m : Modality} {l : flafolTerm}
          (pth : PathToLabelInModality m l) : option Modality :=
    match pth with
    | hereGLab _ => None 
    | hereSimLab m _ _ => Some m
    | thereLab m p _ _ pth' => ModalityBeforeLabel pth'
    end.

  Program Fixpoint PrincipalAtLabel {m : Modality} {l : flafolTerm}
          (pth : PathToLabelInModality m l) : option flafolTerm :=
    match pth with
    | hereGLab _ => None
    | hereSimLab m p _ => Some p
    | thereLab _ _ _ _ pth' => PrincipalAtLabel pth'
    end.

  Program Fixpoint ModalityAfterLabel {m : Modality} {l : flafolTerm}
          (pth : PathToLabelInModality m l) : ModalityResidual :=
    match pth with
    | hereGLab _ => []
    | hereSimLab _ _ _ => []
    | thereLab _ p _ lab' pth' => (ModalityAfterLabel pth') ++ [(p, lab')]
    end.

  
  Theorem ModalityAfterLabelProper : forall {m l} (pth : PathToLabelInModality m l),
      ProperModality m -> ProperModalityResidual (ModalityAfterLabel pth).
  Proof.
    intros m l pth H. induction pth; simpl in *.
    unfold ProperModalityResidual; intros p l H0; inversion H0.
    unfold ProperModalityResidual; intros q l H0; inversion H0.
    inversion H. specialize (IHpth H3).
    apply ProperModalityResidualApp; auto.
    unfold ProperModalityResidual. intros p1 l H6.
    destruct H6; inversion H6. split; [rewrite <- H8 | rewrite <- H9]; auto.
  Qed.

  Theorem ModalityRestitchLabel :
    forall {m l} (pth : PathToLabelInModality m l) (p : flafolTerm) (m' : Modality),
      PrincipalAtLabel pth = Some p ->
      ModalityBeforeLabel pth = Some m' ->
      m = ModalityCombine (m' ⋅ p⟨l⟩) (ModalityAfterLabel pth).
  Proof.
    intros m l pth.
    induction pth; simpl; auto; intros p0 m' H H0;
      inversion H; inversion H0.
    reflexivity.
    rewrite ModalityCombineApp1; rewrite <- IHpth; auto.
  Qed.

  Theorem NilPrincipalModalityLabel :
    forall {m l} (pth : PathToLabelInModality m l),
      PrincipalAtLabel pth = None <-> ModalityBeforeLabel pth = None.
  Proof.
    intros m l pth; split; intro H;
      induction pth; simpl in *; auto; inversion H.
  Qed.

  Theorem ModalityRestitchLabelNil :
    forall {m l} (pth : PathToLabelInModality m l),
      PrincipalAtLabel pth = None ->
      m = ModalityCombine (⟨l⟩) (ModalityAfterLabel pth).
  Proof.
    intros m l pth; induction pth; simpl; auto; intros H; inversion H.
    rewrite ModalityCombineApp1; rewrite <- IHpth; auto.
  Qed.

  Theorem ModalityRestitchReplaceLabel :
    forall {m l1 l2} (pth : PathToLabelInModality m l1) (p : flafolTerm) (m' : Modality),
      PrincipalAtLabel pth = Some p ->
      ModalityBeforeLabel pth = Some m' ->
      ReplaceLabelInModality m l1 l2 pth =
      ModalityCombine (m' ⋅ p⟨l2⟩) (ModalityAfterLabel pth).
  Proof.
    intros m l1 l2 pth; induction pth; simpl; auto; intros q m' H H0;
      inversion H; inversion H0.
    reflexivity.
    rewrite ModalityCombineApp1; rewrite <- IHpth; auto.
  Qed.

  Theorem ModalityRestitchReplaceLabelNil :
    forall {m l1 l2} (pth : PathToLabelInModality m l1),
      PrincipalAtLabel pth = None ->
      ReplaceLabelInModality m l1 l2 pth = ModalityCombine (⟨l2⟩) (ModalityAfterLabel pth).
  Proof.
    intros m l1 l2 pth; induction pth; simpl; auto; intros H; inversion H.
    rewrite ModalityCombineApp1; rewrite <- IHpth; auto.
  Qed.
  
  Fixpoint PathToLabelInModalityRepath
           {m l1} (pth : PathToLabelInModality m l1) (l2 : flafolTerm)
    : PathToLabelInModality (ReplaceLabelInModality m l1 l2 pth) l2 :=
    match pth with
    | hereGLab _ => hereGLab l2
    | hereSimLab m p _ => hereSimLab m p l2
    | thereLab m p _ l' pth' => thereLab _ p l2 l' (PathToLabelInModalityRepath pth' l2)
    end.

  Theorem PTLIMRepathSameBefore :
    forall {m l1} (pth : PathToLabelInModality m l1) (l2 : flafolTerm),
      ModalityBeforeLabel (PathToLabelInModalityRepath pth l2) = ModalityBeforeLabel pth.
  Proof.
    intros m l1 pth l2.
    induction pth; simpl; auto.
  Qed.

  Theorem PTLIMRepathSameAfter :
    forall {m l1} (pth : PathToLabelInModality m l1) (l2 : flafolTerm),
      ModalityAfterLabel (PathToLabelInModalityRepath pth l2) = ModalityAfterLabel pth.
  Proof.
    intros m l1 pth l2.
    induction pth; simpl; [| | rewrite IHpth]; reflexivity.
  Qed.

  Theorem PTLIMRepathSamePrin : 
    forall {m l1} (pth : PathToLabelInModality m l1) (l2 : flafolTerm),
      PrincipalAtLabel (PathToLabelInModalityRepath pth l2) = PrincipalAtLabel pth.
  Proof.
    intros m l1 pth l2.
    induction pth; simpl; [| | rewrite IHpth]; reflexivity.
  Qed.
  
  Program Fixpoint ModalityBeforeDouble {m : Modality} (pth : PathToDoubleInModality m) :=
    match pth with
    | hereDouble m p l => m
    | thereDouble m p l pth' => ModalityBeforeDouble pth'
    end.

  Program Fixpoint ModalityAfterDouble {m : Modality} (pth : PathToDoubleInModality m)
    : ModalityResidual :=
    match pth with
    | hereDouble m p l => []
    | thereDouble m p l pth' => (ModalityAfterDouble pth') ++ [(p, l)]
    end.

  Program Fixpoint PrincipalAtDouble {m : Modality} (pth : PathToDoubleInModality m)
    : flafolTerm :=
    match pth with
    | hereDouble m p l => p
    | thereDouble m p l pth' => PrincipalAtDouble pth'
    end.

  Program Fixpoint LabelAtDouble {m : Modality} (pth : PathToDoubleInModality m)
    : flafolTerm :=
    match pth with
    | hereDouble m p l => l
    | thereDouble m p l pth' => LabelAtDouble pth'
    end.

  Theorem ModalityRestitchDouble :
    forall {m : Modality} (pth : PathToDoubleInModality m),
      let p := PrincipalAtDouble pth in
      let l := LabelAtDouble pth in
      m = ModalityCombine ((ModalityBeforeDouble pth) ⋅ p⟨l⟩ ⋅ p ⟨l⟩)
                          (ModalityAfterDouble pth).
  Proof.
    intros m pth p l.
    unfold p. unfold l. clear p l.
    induction pth; simpl in *. reflexivity.
    rewrite ModalityCombineApp1. rewrite <- IHpth. reflexivity.
  Qed.

  Theorem ModalityRestitchCollapsedDouble :
    forall {m : Modality} (pth : PathToDoubleInModality m),
      let p := PrincipalAtDouble pth in
      let l := LabelAtDouble pth in
      (CollapseDoubleInModality pth) = ModalityCombine ((ModalityBeforeDouble pth) ⋅ p⟨l⟩)
                                                       (ModalityAfterDouble pth).
  Proof.
    intros m pth p l.
    unfold p. unfold l. clear p l.
    induction pth; simpl; auto.
    rewrite IHpth. rewrite ModalityCombineApp1. reflexivity.
  Qed.
  
  Definition FwdModality {m : Modality} {p : flafolTerm} (pth : PathToPrinInModality m p)
             (q : flafolTerm) :=
    (ModalityBeforePrin pth) ⋅ q⟨LabelAtPrin pth⟩.

  Theorem RestitchFwdModality :
    forall {m : Modality} {p : flafolTerm} (pth : PathToPrinInModality m p) (q : flafolTerm),
      FwdModality pth q = (ModalityBeforePrin pth) ⋅ q⟨LabelAtPrin pth⟩.
  Proof.
    intros m p pth; induction pth; intro r; simpl; auto.
  Qed.

  Theorem RestitchModalityFwdModality : 
    forall {m : Modality} {p : flafolTerm} (pth : PathToPrinInModality m p),
      m = ModalityCombine (FwdModality pth p) (ModalityAfterPrin pth).
  Proof.
    intros m p pth.
    rewrite ModalityRestitchPrin with (pth := pth) at 1.
    rewrite RestitchFwdModality. reflexivity.
  Qed.                            

  Theorem ModalityRestitchReplacePrinFwdModality :
    forall {m : Modality} {p : flafolTerm} (pth : PathToPrinInModality m p) (q : flafolTerm),
      ReplacePrinInModality pth q
      = ModalityCombine (FwdModality pth q) (ModalityAfterPrin pth).
  Proof.
    intros m p pth q.
    rewrite ModalityRestitchReplacePrin. rewrite RestitchFwdModality.
    reflexivity.
  Qed.

  Program Fixpoint VarModality {m : Modality} {l : flafolTerm}
          (pth : PathToLabelInModality m l) (l' : flafolTerm) :=
    match ModalityBeforeLabel pth with
    | None => ⟨l'⟩
    | Some m' => match PrincipalAtLabel pth with
                | None => _
                | Some p => m' ⋅ p⟨l'⟩
                end
    end.

  Theorem RestitchVarModality : forall {m l1 l2} (pth : PathToLabelInModality m l1)
                                  (p : flafolTerm) (m' : Modality),
      PrincipalAtLabel pth = Some p ->
      ModalityBeforeLabel pth = Some m' ->
      VarModality pth l2 = m' ⋅ p⟨l2⟩.
  Proof.
    intros m l1 l2 pth; induction pth; intros q m' H H0; simpl in *; auto.
    inversion H. inversion H. inversion H0. reflexivity.
    rewrite H0. rewrite H. reflexivity.
  Qed.

  Theorem RestitchVarModalityNil : forall {m l1 l2} (pth : PathToLabelInModality m l1),
      PrincipalAtLabel pth = None ->
      VarModality pth l2 = ⟨l2⟩.
  Proof.
    intros m l1 l2 pth; induction pth; intro H; simpl in *; auto.
    inversion H.
    pose proof H. rewrite NilPrincipalModalityLabel in H0.
    rewrite H0. reflexivity.
  Qed.

  Theorem RestitchModalityVarModality : forall {m l1} (pth : PathToLabelInModality m l1),
      m = ModalityCombine (VarModality pth l1) (ModalityAfterLabel pth).
  Proof.
    intros m l1 pth.
    induction pth; simpl; try reflexivity.
    destruct (ModalityBeforeLabel pth) eqn:e.
    destruct (PrincipalAtLabel pth) eqn:e'.
    rewrite <- ModalityCombineApp.
    rewrite <- RestitchVarModality with (pth0 := pth) (p0 := f) (m' := m0); auto.
    rewrite <- IHpth. simpl. reflexivity.
    rewrite NilPrincipalModalityLabel in e'.
    pose proof (eq_trans (eq_sym e) e'). inversion H.
    rewrite <- NilPrincipalModalityLabel in e.
    rewrite <- RestitchVarModalityNil with (pth0 := pth); auto.
    rewrite <- ModalityCombineApp. rewrite <- IHpth. simpl. reflexivity.
  Qed.

  Theorem RestitchReplaceLabelVarModality : forall {m l1 l2} (pth : PathToLabelInModality m l1),
      (ReplaceLabelInModality m l1 l2 pth) = ModalityCombine (VarModality pth l2) (ModalityAfterLabel pth).
  Proof.
    intros m l1 l2 pth.
    destruct (PrincipalAtLabel pth) as [p|] eqn:e1;
      destruct (ModalityBeforeLabel pth) eqn:e2.
    - rewrite RestitchVarModality with (p0 := p) (m' := m0); auto.
      rewrite ModalityRestitchReplaceLabel with (p0 := p) (m' := m0); auto.
    - rewrite <- NilPrincipalModalityLabel in e2.
      pose proof (eq_trans (eq_sym e1) e2) as H; inversion H.
    - rewrite NilPrincipalModalityLabel in e1.
      pose proof (eq_trans (eq_sym e1) e2) as H; inversion H.      
    - rewrite RestitchVarModalityNil; auto.
      rewrite ModalityRestitchReplaceLabelNil; auto.
  Qed.

    Theorem ModalityBeforeLabelProper : forall {m : Modality} {l : flafolTerm}
                                        (pth : PathToLabelInModality m l) (m0 : Modality),
      ModalityBeforeLabel pth = Some m0 -> ProperModality m -> ProperModality m0.
  Proof.
    intros m l pth; induction pth; intros m0 e pmod; simpl in *.
    inversion e.
    inversion e; inversion pmod. rewrite <- H0; auto.
    inversion pmod. apply IHpth; auto.
  Qed.

  Theorem PrincipalAtLabelProper : forall{m : Modality} {l : flafolTerm}
                                    (pth : PathToLabelInModality m l) (p : flafolTerm),
      PrincipalAtLabel pth = Some p -> ProperModality m -> ⊢s p ::: Principal.
  Proof.
    intros m l pth; induction pth; intros q e pmod; simpl in *.
    inversion e.
    inversion e; inversion pmod; rewrite <- H0; auto.
    inversion pmod; apply IHpth; auto.
  Qed.
  
  Theorem VarModalityProper : forall {m : Modality} {l1 : flafolTerm} (l2 : flafolTerm)
                                (pth : PathToLabelInModality m l1),
      ProperModality m -> ⊢s l2 ::: Label -> ProperModality (VarModality pth l2).
  Proof.
    intros m l1 l2 pth. revert l2. induction pth; intros l2 pmod l2sort; simpl.
    constructor; auto.
    inversion pmod; constructor; auto.
    inversion pmod.
    destruct (ModalityBeforeLabel pth) eqn:e.
    destruct (PrincipalAtLabel pth) eqn:e'.
    constructor; auto. apply ModalityBeforeLabelProper with (pth0 := pth); auto.
    apply PrincipalAtLabelProper with (pth0 := pth); auto.
    unfold VarModality_obligation_1;
      apply ModalityBeforeLabelProper with (pth0 := pth); auto.
    constructor; auto.
  Qed.

  Theorem VarModalityCombine : forall {m : Modality} {l : flafolTerm}
                                 (pth : PathToLabelInModality m l) (l2 : flafolTerm)
                                 (mr : ModalityResidual),
      VarModality pth l2 = VarModality (PathToLabelInModalityCombine pth mr) l2.
  Proof.
    intros m l pth l2 mr.
    revert m l pth l2. induction mr; intros m l pth l2; simpl. reflexivity.
    destruct a.
    rewrite <- IHmr. simpl.
    destruct (ModalityBeforeLabel pth) eqn:e;
      destruct (PrincipalAtLabel pth) eqn:e'.
    rename f1 into p. rewrite RestitchVarModality with (p0 := p) (m' := m0); auto.
    rewrite NilPrincipalModalityLabel in e'.
    pose proof (eq_trans (eq_sym e') e). inversion H.
    rewrite <- NilPrincipalModalityLabel in e.
    pose proof (eq_trans (eq_sym e') e). inversion H.
    rewrite RestitchVarModalityNil; auto.
  Qed.    


  Fixpoint substModality (m : Modality) (y : var) (trm : flafolTerm) :=
    match m with
    | ⟨l⟩ => ⟨ l t[y ↦ trm]⟩
    | m' ⋅ p⟨l⟩ => (substModality m' y trm) ⋅ (p t[y↦trm])⟨l t[y↦trm]⟩
    end.
  Notation "m mod[ x ↦ t ]" := (substModality m x t) (at level 40).

  Definition ModalityResSubst (m' : ModalityResidual) (x : var) (t : flafolTerm) :=
    map (fun arg => match arg with (p,l) => (p t[x ↦ t], l t[x ↦ t]) end) m'.

  Lemma ModalityCombineSubst : forall m' m x t, ((ModalityCombine m m') mod[x ↦ t]) = ModalityCombine (m mod[x ↦ t]) (ModalityResSubst m' x t).
  Proof.
    induction m'; simpl; auto.
    destruct a.
    intros.
    apply IHm'.
  Qed.
  
  Theorem substModalityNotFreeEq : forall (m : Modality) (x : var) (t : flafolTerm),
      x ∉FVM m -> m mod[ x ↦ t] = m.
  Proof.
    intros m x t H.
    induction m as [lab | m IH p lab].
    simpl. repeat rewrite substTermNonFreeEqual; auto.
    intro H'; apply H; constructor; auto; fail.
    simpl. apply NotFVMSimInversion in H; destruct H; destruct H0.
    repeat (rewrite substTermNonFreeEqual; auto).
    rewrite (IH H); reflexivity.
  Qed.

  Lemma ProperModSubst : forall (m : Modality) (x : var) (t : flafolTerm),
       ⊢s t ::: (VarSort x) -> ProperModality m -> ProperModality (m mod[x ↦ t]).
  Proof.
    induction m; simpl; intros.
    - inversion H0; subst.
      constructor; apply substTermSortPreserving; auto.
    - inversion H0; subst.
      constructor; auto; apply substTermSortPreserving; auto.
  Qed.

  Lemma fvsubstModality : forall y' y m t, y' ∉FVM m -> y' ∉FVT t -> y' ∉FVM (m mod[ y ↦ t]).
  Proof.
    induction m; simpl; intros; auto.
    - intro h.
      inversion h; subst.
      revert H3.
      apply fvsubstTerm; auto.
      intro h1.
      apply H.
      constructor; auto.
    - intro h.
      inversion h; subst.
      revert H3.
      apply IHm; auto.
      intro.
      apply H.
      constructor; auto.
      revert H3.
      apply fvsubstTerm; auto.
      intro; apply H; try (econstructor; eauto; fail).
      revert H3.
      apply fvsubstTerm; auto.
      intro; apply H; try (econstructor; eauto; fail).
  Qed.

  Lemma NotFreeInModalitySubstEq : forall m x t, x ∉FVM m -> m mod[x ↦ t] = m.
  Proof.
    intros m; induction m as [l | m' IHm p l]; intros x t H.
    destruct (freeInTermDec x l);
      try (exfalso; apply H; constructor; auto; fail).
    simpl; repeat (rewrite substTermNonFreeEqual; auto).
    destruct (freeInTermDec x p);
      destruct (freeInTermDec x l);
      try (exfalso; apply H; constructor; auto; fail).
    simpl; repeat (rewrite substTermNonFreeEqual; auto).
    rewrite IHm; auto.
    intro H0; apply H; constructor; auto; fail.
  Qed.
  
  Theorem InnermostLabelSubst : forall (m : Modality) (x : var) (t : flafolTerm),
      InnermostLabel (m mod[x ↦ t]) = (InnermostLabel m) t[x ↦ t].
  Proof.
    intros m; induction m; intros x t; simpl; reflexivity.
  Qed.

  Program Fixpoint PathToDoubleSubst {m : Modality} (pth : PathToDoubleInModality m) (x : var) (t : flafolTerm) : PathToDoubleInModality (m mod[x ↦ t]) :=
    match pth with
    | hereDouble m' p' l' => hereDouble ((m' mod[x ↦ t])) (p' t[x ↦ t]) (l' t[x ↦ t])
    | thereDouble m' p' l' pth => thereDouble (m' mod[x ↦ t]) (p' t[x ↦ t]) (l' t[x ↦ t]) (PathToDoubleSubst pth x t)
    end.

  Program Fixpoint PathToLabelSubst {m : Modality} {l : flafolTerm}
          (pth : PathToLabelInModality m l) (x : var) (t : flafolTerm) :
    PathToLabelInModality (m mod[x ↦ t]) (l t[x ↦ t]) :=
    match pth with
    | hereGLab lab => hereGLab (lab t[x ↦ t])
    | hereSimLab m p lab =>
      hereSimLab (m mod[x ↦ t]) (p t[x ↦ t]) (lab t[x ↦ t])
    | thereLab m p l l' pth' =>
      thereLab (m mod[x ↦ t]) (p t[x ↦ t]) (l t[x ↦ t]) (l' t[x ↦ t])
               (PathToLabelSubst pth' x t)
    end.

  Program Fixpoint PathToPrinSubst {m : Modality} {p : flafolTerm}
          (pth : PathToPrinInModality m p) (x : var) (t : flafolTerm) :
    PathToPrinInModality (m mod[x ↦ t]) (p t[x ↦ t]) :=
    match pth with
    | hereSimP m p l =>
      hereSimP (m mod[x ↦ t]) (p t[x ↦ t]) (l t[x ↦ t])
    | thereP m p q l pth' =>
      thereP (m mod[x ↦ t]) (p t[x ↦ t]) (q t[x ↦ t]) (l t[x ↦ t])
             (PathToPrinSubst pth' x t)
    end.
  
  Lemma ModalityBeforeLabelSubst :
    forall (m : Modality) (l : flafolTerm) (x : var) (t : flafolTerm)
      (pth : PathToLabelInModality m l),
      match ModalityBeforeLabel pth with
      | Some m' => ModalityBeforeLabel (PathToLabelSubst pth x t) = Some (m' mod[x ↦ t])
      | None => ModalityBeforeLabel (PathToLabelSubst pth x t) = None
      end.
  Proof.
    intros m l x t pth; induction pth; simpl; auto.
  Qed.

  Lemma ModalityBeforePrinSubst :
    forall (m : Modality) (p : flafolTerm) (x : var) (t : flafolTerm)
      (pth : PathToPrinInModality m p),
      ModalityBeforePrin (PathToPrinSubst pth x t)
      = (ModalityBeforePrin pth) mod[x ↦ t].
  Proof.
    intros m p x t pth; induction pth; simpl; auto.
  Qed.

  Lemma PrincipalAtLabelSubst :
    forall (m : Modality) (l : flafolTerm) (x : var) (t : flafolTerm)
      (pth : PathToLabelInModality m l),
      match PrincipalAtLabel pth with
      | Some p => PrincipalAtLabel (PathToLabelSubst pth x t) = Some (p t[x ↦ t])
      | None => PrincipalAtLabel (PathToLabelSubst pth x t) = None
      end.
  Proof.
    intros m pc x t pth; induction pth; simpl; auto.
  Qed.

  Lemma DoubleSubst :
    forall (m : Modality) (x : var) (t : flafolTerm)
      (pth : PathToDoubleInModality m),
      CollapseDoubleInModality pth mod[x ↦ t] = CollapseDoubleInModality (PathToDoubleSubst pth x t).
  Proof.
    induction pth; simpl; intros; auto.
    rewrite IHpth; auto.    
  Qed.

  Lemma ProperModalityResSubst : forall m' y t, ⊢s t ::: (VarSort y) -> ProperModalityResidual m' -> ProperModalityResidual (ModalityResSubst m' y t).
  Proof.
    induction m'; simpl; intros; auto.
    destruct a.
    apply ProperModalityResidualConsInv in H0.
    destruct H0 as [h1 [h2 h3]].
    apply ProperModalityResidualCons; auto.
    all : apply substTermSortPreserving; auto.
  Qed.                                                                                       
                         
  Lemma LabelAtPrinSubst :
    forall (m : Modality) (p : flafolTerm) (x : var) (t : flafolTerm)
      (pth : PathToPrinInModality m p),
      LabelAtPrin pth t[x ↦ t] = LabelAtPrin (PathToPrinSubst pth x t).
  Proof.
    intros m p x t pth; induction pth; simpl; auto.
  Qed.

  Lemma ModalityBeforeLabel_PrinAtLabel_Some1 : forall (m m' : Modality) (l : flafolTerm)
                                                  (pth : PathToLabelInModality m l),
      ModalityBeforeLabel pth = Some m' -> exists p, PrincipalAtLabel pth = Some p.
  Proof.
    intros m m' l pth H.
    induction pth; simpl in *; auto.
    - inversion H.
    - exists p; auto.
  Qed.

  Lemma ModalityBeforeLabel_PrinAtLabel_None1 : forall (m : Modality) (l : flafolTerm)
                                                  (pth : PathToLabelInModality m l),
      ModalityBeforeLabel pth = None -> PrincipalAtLabel pth = None.
  Proof.
    intros m l pth H; induction pth; simpl in *; auto.
    inversion H.
  Qed.
  
  Theorem VarModalitySubst : forall (m : Modality) (l1 l2: flafolTerm) (x : var) (t : flafolTerm)
                               (pth : PathToLabelInModality m l1),
      (VarModality pth l2) mod[x ↦ t] = VarModality (PathToLabelSubst pth x t) (l2 t[x ↦ t]).
  Proof.
    intros m l1 l2 x t pth.
    induction pth; auto; simpl.
    pose proof (ModalityBeforeLabelSubst m lab x t pth).
    pose proof (PrincipalAtLabelSubst m lab x t pth).
    destruct (ModalityBeforeLabel pth) eqn:e.
    pose proof (ModalityBeforeLabel_PrinAtLabel_Some1 m m0 lab pth e).
    destruct H1 as [q Hq].
    rewrite Hq in H0. rewrite Hq; rewrite H; rewrite H0.
    auto.
    pose proof (ModalityBeforeLabel_PrinAtLabel_None1 m lab pth e).
    rewrite H1 in H0. rewrite H0. rewrite H; auto.
  Qed.

  Theorem FwdModalitySubst : forall (m : Modality) (p q : flafolTerm) (x : var) (t : flafolTerm)
                               (pth : PathToPrinInModality m p),
      (FwdModality pth q) mod[x ↦ t] = FwdModality (PathToPrinSubst pth x t) (q t[x ↦ t]).
  Proof.
    intros m p q x t pth; induction pth; simpl; auto.
  Qed.

  Theorem ReplaceLabelInModalitySubst :
    forall (m : Modality) (l l' : flafolTerm) (x : var) (t : flafolTerm)
      (pth : PathToLabelInModality m l),
      (ReplaceLabelInModality m l l' pth) mod[x ↦ t] =
      ReplaceLabelInModality (m mod[x ↦ t]) (l t[x ↦ t]) (l' t[x ↦ t]) (PathToLabelSubst pth x t).
  Proof.
    intros m l l' x t pth; induction pth; simpl; auto.
    rewrite IHpth. auto.
  Qed.

  Theorem ReplacePrinInModalitySubst :
    forall (m : Modality) (p q : flafolTerm) (x : var) (t : flafolTerm)
      (pth : PathToPrinInModality m p),
      (ReplacePrinInModality pth q) mod[x ↦ t] =
      ReplacePrinInModality (PathToPrinSubst pth x t) (q t[x ↦ t]).
  Proof.
    intros m p q x t pth; induction pth; simpl; auto.
    rewrite IHpth; auto.
  Qed.

  Program Fixpoint open_modality_rec (n : nat) (m : Modality) (t : flafolTerm) : Modality :=
    match m with
    | ⟨l⟩ => ⟨open_term_rec n l t⟩
    | m' ⋅ p⟨l⟩ => (open_modality_rec n m' t) ⋅ (open_term_rec n p t) ⟨open_term_rec n l t⟩
    end.

  Inductive lc_modality : Modality -> Prop :=
  | G_lc : forall l : flafolTerm, lc_term l -> lc_modality (⟨l⟩)
  | sim_lc : forall (m : Modality) (p l : flafolTerm),
      lc_modality m -> lc_term p -> lc_term l -> lc_modality (m ⋅ p⟨l⟩).
                                                                       
  Lemma open_modality_commute_rec : forall m t1 t2 n1 n2,
      n1 =? n2 = false -> lc_term t1 -> lc_term t2 ->
      open_modality_rec n2 (open_modality_rec n1 m t1) t2
      = open_modality_rec n1 (open_modality_rec n2 m t2) t1.
  Proof.
    intros m t1 t2 n1 n2 H H0 H1.
    induction m; simpl.
    repeat rewrite (open_term_commute_rec _ _ _ n1 n2); auto.
    repeat rewrite (open_term_commute_rec _ _ _ n1 n2); auto.
    rewrite IHm.
    auto.
  Qed.



  Inductive Belief : Set :=
    mkBelief : flafolFormula -> Modality -> Belief.
  Notation "phi @ m" := (mkBelief phi m) (at level 24).
  Definition ProperBelief (b : Belief) : Prop :=
    match b with
    | phi @ m => ProperModality m /\ ⊢wff phi
    end.
  Lemma ProperBeliefM : forall (m : Modality) (phi : flafolFormula),
      ProperBelief (phi @ m) -> ProperModality m.
  Proof.
    intros m phi H; inversion H; auto.
  Qed.
  Lemma ProperBeliefPhi : forall (m : Modality) (phi : flafolFormula),
      ProperBelief (phi @ m) -> ⊢wff phi.
  Proof.
    intros m phi H; apply H.
  Qed.
  Inductive freeInBelief : var -> Belief -> Prop :=
    freeInMB : forall (x : var) (m : Modality) (phi : flafolFormula),
      x ∈FVM m -> freeInBelief x (phi @ m)
  | freeInPhiB : forall (x : var) (m : Modality) (phi : flafolFormula),
      x ∈FVF phi -> freeInBelief x (phi @ m).
  Infix "∈FVB" := freeInBelief (at level 40) : proof_scope.
  Notation "x ∉FVB b" := (~ freeInBelief x b) (at level 40) : proof_scope.
  Open Scope proof_scope.
  Lemma NotInFVB : forall m phi x,
      x ∉FVM m -> x ∉FVF phi -> x ∉FVB (phi @ m).
  Proof.
    intros m phi x H H0 Hcontra.
    inversion Hcontra; [apply H | apply H0]; auto.
  Qed.

  Lemma NotInFVBInversion : forall m phi x,
      x ∉FVB (phi @ m) -> x ∉FVM m /\ x ∉FVF phi.
  Proof.
    intros m phi x H.
    split; intro Hcontra; apply H; try (constructor; auto; fail).
  Qed.
  Fixpoint varsInBelief (b : Belief) : list var :=
    match b with
    | (phi @ m) => (varsInModality m) ++ (varsInFormula phi)
    end.
  Lemma freeVarsInBelief : forall (x : var) (b : Belief),
      x ∈FVB b -> In x (varsInBelief b).
  Proof.
    intros x b H.
    destruct b; simpl; apply in_or_app; inversion H;
      [left; apply FreeVarsInModality; auto | right; apply FreeVarsInFormula; auto].
  Qed.    
  Definition freshInBelief (b : Belief) (sigma : sort) : var :=
    freshVar (varsInBelief b) sigma.
  Lemma freshInBeliefOfSort : forall (b : Belief) (sigma : sort),
      VarSort (freshInBelief b sigma) = sigma.
  Proof.
    intros b sigma; unfold freshInBelief; apply freshVarSameSort.
  Qed.
  Lemma freshInBeliefIsFresh : forall(b : Belief) (sigma : sort),
      (freshInBelief b sigma) ∉FVB b.
  Proof.
    intros b sigma. unfold freshInBelief; destruct b; simpl.
    intro H; apply freeVarsInBelief in H; simpl in H.
    eapply freshVarNotIn; eauto.
  Qed.
  Definition BeliefEqDec : forall b b' : Belief, {b = b'} + {b <> b'}.
    decide equality; [apply ModalityEqDec | apply formulaEqDec].
  Defined.
  Definition substBelief (b : Belief) (x : var) (t : flafolTerm) :=
    match b with
    | phi @ m => (phi f[x ↦ t]) @ (m mod[x ↦ t])
    end.
  Notation "b bel[ x ↦ t ]" := (substBelief b x t) (at level 40).
  Lemma fvsubstBelief : forall y' y b t, y' ∉FVT t -> y' ∉FVB b -> y' ∉FVB (b bel[y ↦ t]).
  Proof.
    intros y' y b t H H0.
    destruct b as [phi m].
    apply NotInFVBInversion in H0; destruct H0.
    simpl; apply NotInFVB. apply fvsubstModality; auto. apply fvsubstFormula; auto.
  Qed.

  

  Definition Context : Set := list Belief.
  Definition ProperContext : Context -> Prop := Forall ProperBelief.

  Definition freeInContext : var -> Context -> Prop := fun x : var => Exists (freeInBelief x).
  Infix "∈FVC" := freeInContext (at level 40) : proof_scope.
  Notation "x ∉FVC Gamma" := (~ freeInContext x Gamma) (at level 40) : proof_scope.
  Lemma NotInFVCConsInversion : forall (b : Belief) (Gamma : Context) (x : var),
      x ∉FVC (b :: Gamma) -> x ∉FVB b /\ x ∉FVC Gamma.
  Proof.
    intros b Gamma x H.
    split; intro Hcontra; apply H.
    unfold freeInContext; apply Exists_cons; left; auto.
    unfold freeInContext; apply Exists_cons; right; auto.
  Qed.

  Lemma NotInFVCCons : forall (b : Belief) (Gamma : Context) (x : var),
      x ∉FVB b -> x ∉FVC Gamma -> x ∉FVC (b :: Gamma).
  Proof.
    intros b Gamma x H H0.
    intro Hcontra; apply Exists_cons in Hcontra;
      destruct Hcontra; [apply H | apply H0]; auto.
  Qed.
  Definition varsInContext : Context -> list var :=
    flat_map varsInBelief.
  Theorem freeVarsInContext : forall (x : var) (Gamma : Context),
      x ∈FVC Gamma -> In x (varsInContext Gamma).
  Proof.
    intros x Gamma; revert x; induction Gamma; intros x H;
      inversion H; simpl; apply in_or_app;
        [left; apply freeVarsInBelief | right; apply IHGamma]; auto.
  Qed.
  Definition freshInContext (Gamma : Context) (sigma : sort) :=
    freshVar (varsInContext Gamma) sigma.
  Lemma freshInContextOfSort : forall (Gamma : Context) (sigma : sort),
      VarSort (freshInContext Gamma sigma) = sigma.
  Proof.
    intros Gamma sigma; unfold freshInContext; apply freshVarSameSort.
  Qed.
  Lemma freshInContextIsFresh : forall (Gamma : Context) (sigma : sort),
      (freshInContext Gamma sigma) ∉FVC Gamma.
  Proof.
    intros Gamma sigma H.
    apply freeVarsInContext in H.
    unfold freshInContext in H. eapply freshVarNotIn; eauto.
  Qed.

  Lemma fvcApp : forall G1 G2 y, y ∉FVC (G1 ++ G2) -> y ∉FVC G1 /\ y ∉FVC G2.
  Proof.
    induction G1; simpl; intros; auto.
    split; auto.
    intro.
    inversion H0.
    apply NotInFVCConsInversion in H.
    destruct H.
    destruct (IHG1 _ _ H0).
    split; auto.
    apply NotInFVCCons; auto.
  Qed.
    
  Lemma ProperContextIff : forall (Gamma Delta : Context),
      (forall b : Belief, In b Gamma <-> In b Delta) -> ProperContext Gamma -> ProperContext Delta.
  Proof.
    intros Gamma Delta Hin; unfold ProperContext;
      repeat (rewrite Forall_forall); intros Hproper b Hb;
        apply Hproper; auto; apply <- Hin; auto.
  Qed.
  Hint Resolve ProperContextIff.
  Definition ContextEqDec : forall Gamma Delta : Context, {Gamma = Delta} + {Gamma <> Delta}.
    apply list_eq_dec; apply BeliefEqDec.
  Defined.
  Theorem ProperContextApp : forall (Gamma Delta : Context),
      ProperContext (Gamma ++ Delta) -> ProperContext Gamma /\ ProperContext Delta.
  Proof.
    unfold ProperContext; intros Gamma Delta H; rewrite ->Forall_forall in H; split;
      rewrite Forall_forall; intros b Hin; apply H;
        apply in_or_app; [left | right]; auto.
  Qed.
  Theorem AppProperContext : forall (Gamma Delta : Context),
      ProperContext Gamma -> ProperContext Delta -> ProperContext (Gamma ++ Delta).
  Proof.
    unfold ProperContext; intros Gamma Delta HGamma HDelta; rewrite Forall_forall;
      rewrite ->Forall_forall in HGamma; rewrite ->Forall_forall in HDelta;
        intros b Hin; apply in_app_or in Hin; destruct Hin;
          [apply HGamma | apply HDelta]; auto.
  Qed.
  Theorem ProperContextFirst : forall (b : Belief) (Gamma : Context),
      ProperContext (b :: Gamma) -> ProperBelief b.
  Proof.
    unfold ProperContext; intros b Gamma Hproper; rewrite ->Forall_forall in Hproper;
      apply Hproper; simpl; left; auto.
  Qed.
  Theorem ProperContextRemoveFirst : forall (b : Belief) (Gamma : Context),
      ProperContext (b :: Gamma) -> ProperContext Gamma.
  Proof.
    unfold ProperContext; intros b Gamma Hproper; rewrite ->Forall_forall in Hproper;
      rewrite Forall_forall; intros b' Hin; apply Hproper; simpl; right; auto.
  Qed.
  
  Lemma ProperContextWithoutPath : forall (Gamma : Context) (b : Belief) (pth : Path b Gamma),
      ProperContext Gamma -> ProperContext (WithoutPath Gamma pth).
  Proof.
    intros Gamma b pth H.
    unfold ProperContext in *. rewrite Forall_forall in *.
    intros b' b'_in_Gamma. apply InToPath in b'_in_Gamma; [| exact BeliefEqDec].
    apply withoutLiftPath in b'_in_Gamma. apply PathToIn in b'_in_Gamma.
    apply H; auto.
  Qed.


  Definition substContext (Gamma : Context) (y : var) (t : flafolTerm) :=
    map (fun b : Belief => b bel[y ↦ t]) Gamma.
  Notation "G c[ x ↦ t ]" := (substContext G x t) (at level 40).

  Theorem substContextNonFreeEq : forall (Gamma : Context) (x : var) (t : flafolTerm),
      x ∉FVC Gamma -> Gamma c[x ↦ t] = Gamma.
  Proof.
    intros Gamma x t H.
    induction Gamma as [| b Delta]; [simpl; reflexivity|].
    simpl. destruct b as [phi m]; simpl.
    apply NotInFVCConsInversion in H; destruct H.
    apply NotInFVBInversion in H; destruct H.
    rewrite substModalityNotFreeEq; auto.
    rewrite (IHDelta H0).
    rewrite notFreeInFormulaSubstEq; auto.
  Qed.

  Lemma BeliefInProperContextIsProper : forall (b : Belief) (Gamma : Context),
                        ProperContext Gamma -> In b Gamma -> ProperBelief b.
  Proof.
    intros b Gamma H H0.
    unfold ProperContext in H; rewrite ->Forall_forall in H.
    specialize (H b H0); auto.
  Qed.

  Lemma ProperContextCons : forall (b : Belief) (Gamma : Context),
      ProperBelief b -> ProperContext Gamma -> ProperContext (b :: Gamma).
  Proof.
    intros b Gamma H H0.
    unfold ProperContext in H0; unfold ProperContext.
    rewrite ->Forall_forall in H0; rewrite Forall_forall.
    intros x H1; destruct H1 as [H1 | Hin]; [rewrite <- H1; auto | apply H0; auto].
  Qed.

  Lemma ConsProperContext : forall (b : Belief) (Gamma : Context),
      ProperContext (b :: Gamma) -> ProperBelief b /\ ProperContext Gamma.
  Proof.
    intros b Gamma H;
      unfold ProperContext in H; rewrite ->Forall_forall in H; split.
    - apply H; left; auto.
    - unfold ProperContext; rewrite Forall_forall; intros x H0; apply H; right; auto.
  Qed.

  Lemma ProperContextSubst : forall (G:Context) (x : var) (t : flafolTerm),
      lc_term t -> ⊢s t ::: (VarSort x) -> ProperContext G -> ProperContext (G c[x ↦ t]).
  Proof.
    induction G; simpl; intros; try solve [constructor].
    destruct a as [phi m].
    inversion H1; subst; inversion H4; subst.
    apply ProperContextCons.
    constructor.
    apply ProperModSubst; auto.
    apply WellFormedSubst; auto.
    apply IHG; auto.
  Qed.
  
  Definition freshInSequent (Gamma : Context) (b : Belief) (sigma : sort) : var :=
    freshVar ((varsInContext Gamma) ++ (varsInBelief b)) sigma.
  Lemma freshInSequentOfSort :
    forall (Gamma : Context) (b : Belief) (sigma : sort),
      VarSort (freshInSequent Gamma b sigma) = sigma.
  Proof.
    intros Gamma b sigma; unfold freshInSequent; apply freshVarSameSort.
  Qed.
  Lemma freshInSequentIsFresh :
    forall (Gamma : Context) (b : Belief) (sigma : sort),
      ((freshInSequent Gamma b sigma) ∉FVC Gamma) /\ ((freshInSequent Gamma b sigma) ∉FVB b).
  Proof.
    intros Gamma b sigma; split;
      intro H; unfold freshInSequent in H;
        [ apply freeVarsInContext in H | apply freeVarsInBelief in H];
        match goal with
        | [ H : In (freshVar (?l1 ++ ?l2) sigma) ?l1 |- False ] =>
          apply freshVarNotIn with (sigma := sigma) (vs := l1 ++ l2);
            apply in_or_app; left; auto
        | [ H : In (freshVar (?l1 ++ ?l2) sigma) ?l2 |- False ] =>
          apply freshVarNotIn with (sigma := sigma) (vs := l1 ++ l2);
            apply in_or_app; right; auto
        end.
  Qed.

  Inductive proofTerm : Set :=
  | axiomTerm : proofTerm     
  | TTRTerm : proofTerm
  | FFLTerm : proofTerm
  | AndLTerm : proofTerm -> proofTerm
  | AndRTerm : proofTerm -> proofTerm -> proofTerm
  | OrLTerm : proofTerm -> proofTerm -> proofTerm
  | OrR1Term : proofTerm -> proofTerm
  | OrR2Term : proofTerm -> proofTerm
  | ImpLTerm : proofTerm -> proofTerm -> proofTerm
  | ImpRTerm : proofTerm -> proofTerm
  | forallLTerm : proofTerm -> proofTerm
  | forallRTerm : proofTerm -> proofTerm
  | existsLTerm : proofTerm -> proofTerm
  | existsRTerm : proofTerm -> proofTerm
  | flowsToReflTerm : proofTerm
  | flowsToTransRTerm : proofTerm -> proofTerm -> proofTerm
  | saysRTerm : proofTerm -> proofTerm
  | saysLTerm : proofTerm -> proofTerm
  | modalityExpandRTerm : proofTerm -> proofTerm
  | modalityCollapseRTerm : proofTerm -> proofTerm
  | modalityExpandLTerm : proofTerm -> proofTerm
  | modalityCollapseLTerm : proofTerm -> proofTerm
  | RVarianceTerm : proofTerm -> proofTerm -> proofTerm
  | LVarianceTerm : proofTerm -> proofTerm -> proofTerm
  | FwdRTerm : proofTerm -> proofTerm -> proofTerm -> proofTerm
  | FwdLTerm : proofTerm -> proofTerm -> proofTerm -> proofTerm
  | CRVarianceTerm : proofTerm -> proofTerm -> proofTerm
  | CWVarianceTerm : proofTerm -> proofTerm -> proofTerm.  
  
  (*
    The proof system.
   *)
  
  Reserved Notation "Gamma ⊢ t ::: b" (at level 25).
  Inductive typing : Context -> proofTerm -> Belief -> Set :=
  | axiomr : forall (Gamma : Context) (b : Belief),
      ProperContext Gamma -> Path b Gamma -> Gamma ⊢ axiomTerm ::: b
  | TTRr :
      forall (Gamma : Context) (m : Modality),
        ProperContext Gamma -> ProperModality m ->
        Gamma ⊢ TTRTerm ::: (TT @ m)
  | FFLr :
      forall (Gamma : Context) (phi : flafolFormula) (m : Modality) (m' : ModalityResidual),
        ProperContext Gamma -> ⊢wff phi -> ProperModality m -> Path (FF @ m) Gamma ->
        ProperModalityResidual m' ->
        Gamma ⊢ FFLTerm ::: (phi @ ModalityCombine m m')
  | AndLr :
      forall (Gamma : Context) (phi psi : flafolFormula) (m : Modality) (b : Belief) (pth : Path  (phi & psi @ m) Gamma) (e : proofTerm), (phi @ m :: psi @ m :: Gamma) ⊢ e ::: b ->
        Gamma ⊢ (AndLTerm e) ::: b
  | AndRr :
      forall (Gamma : Context) (phi psi : flafolFormula) (m : Modality) (e1 e2 : proofTerm),
        Gamma ⊢ e1 ::: (phi @ m) -> Gamma ⊢ e2 ::: (psi @ m) ->
        Gamma ⊢ (AndRTerm e1 e2) ::: phi & psi @ m
  | OrLr :
      forall (Gamma : Context)
        (phi psi : flafolFormula) (m : Modality) (b : Belief)
        (pth : Path  (phi ⊕ psi @ m) Gamma) (e1 e2 : proofTerm),
        (phi @ m :: Gamma) ⊢ e1 ::: b ->
        (psi @ m :: Gamma) ⊢ e2 ::: b ->
        Gamma ⊢ (OrLTerm e1 e2) ::: b
  | OrR1r :
      forall (Gamma : Context) (phi psi : flafolFormula) (m : Modality) (e : proofTerm),
        Gamma ⊢ e ::: (phi @ m) -> ⊢wff psi ->
        Gamma ⊢ (OrR1Term e) ::: (phi ⊕ psi @ m)
  | OrR2r :
      forall (Gamma : Context) (phi psi : flafolFormula) (m : Modality) (e : proofTerm),
        Gamma ⊢ e ::: (psi @ m) -> ⊢wff phi ->
        Gamma ⊢ (OrR2Term e) ::: (phi ⊕ psi @ m)
  | ImpLr :
      forall (Gamma : Context) (phi psi : flafolFormula) (m : Modality) (l : flafolTerm) (b : Belief) (pth : Path  (phi ==⟨l⟩> psi @ m) Gamma) (e1 e2 : proofTerm), 
        Gamma ⊢ e1 ::: (phi @ ⟨l⟩) -> (psi @ m :: Gamma) ⊢ e2 ::: b -> 
        Gamma ⊢ (ImpLTerm e1 e2) ::: b
  | ImpRr :
      forall (Gamma : Context) (phi psi : flafolFormula) (m' : Modality) (l : flafolTerm) (e : proofTerm),
         (phi @ ⟨ l ⟩ :: Gamma) ⊢ e ::: (psi @ m') ->
        Gamma ⊢ (ImpRTerm e) ::: (phi ==⟨l⟩> psi @ m')
  | forallLr :
      forall (Gamma : Context) (sigma : sort) (phi : flafolFormula) (t : flafolTerm) (m : Modality)
        (b : Belief) (pth : Path (∀ sigma; phi @ m) Gamma) (e : proofTerm),
        lc_term t -> ⊢s t ::: sigma ->
        (open_formula phi t @ m :: Gamma) ⊢ e ::: b ->
        Gamma ⊢ (forallLTerm e) ::: b
  | forallRr :
      forall (Gamma : Context) (sigma : sort) (y : var) (phi : flafolFormula) (m : Modality) (e : proofTerm),
        VarSort y = sigma -> y ∉FVC Gamma -> y ∉FVF phi -> y ∉FVM m ->
        Gamma ⊢ e ::: ((open_formula phi (varTerm y)) @ m) ->
        Gamma ⊢ (forallRTerm e) ::: (∀ sigma; phi @ m)
  | existsLr :
      forall (Gamma : Context) (sigma : sort) (y : var) (phi : flafolFormula) (m : Modality) (b : Belief) (pth : Path  (∃ sigma; phi @ m) Gamma) (e : proofTerm),
        VarSort y = sigma ->  y ∉FVC (Gamma) -> y ∉FVB b -> 
        (open_formula phi (varTerm y) @ m :: Gamma) ⊢ e ::: b ->
        Gamma ⊢ (existsLTerm e) ::: b
  | existsRr :
      forall (Gamma : Context) (sigma : sort) (t : flafolTerm) (phi : flafolFormula) (m : Modality) (e : proofTerm),
        lc_term t -> ⊢s t ::: sigma -> Gamma ⊢ e ::: ((open_formula phi t) @ m) ->
        Gamma ⊢ (existsRTerm e) ::: (∃ sigma; phi @ m)
  | flowsToReflr :
      forall (Gamma : Context) (lab : flafolTerm) (m : Modality),
        ProperContext Gamma -> ⊢s lab ::: Label -> ProperModality m ->
        Gamma ⊢ flowsToReflTerm ::: (lab ⊑ lab @ m)
  | flowsToTransRr :
      forall (Gamma : Context)(lab1 lab2 lab3 : flafolTerm) (m : Modality) (e1 e2 : proofTerm),
        Gamma ⊢ e1 ::: (lab1 ⊑ lab2 @ m) -> Gamma ⊢ e2 ::: (lab2 ⊑ lab3 @ m) ->
        Gamma ⊢ (flowsToTransRTerm e1 e2) ::: (lab1 ⊑ lab3 @ m)
  | saysRr :
      forall (Gamma : Context) (p lab : flafolTerm) (phi : flafolFormula) (m : Modality) (e : proofTerm),
        Gamma ⊢ e ::: phi @ (m ⋅ p⟨lab⟩) ->
        Gamma ⊢ (saysRTerm e) ::: (p □ ⟨lab⟩ phi @ m)
  | saysLr :
      forall (Gamma : Context) (p lab : flafolTerm) (phi : flafolFormula) (m : Modality)
        (b : Belief) (pth : Path  (p □ ⟨ lab ⟩ phi @ m) Gamma) (e : proofTerm), ((phi @ m ⋅ p⟨lab⟩) :: Gamma) ⊢ e ::: b -> Gamma ⊢ (saysLTerm e) ::: b
  | modalityExpandRr :
      forall (Gamma : Context) (phi : flafolFormula) (m : Modality) (pth : PathToDoubleInModality m) (e : proofTerm),
        Gamma ⊢ e ::: (phi @ (CollapseDoubleInModality pth)) -> 
        Gamma ⊢ (modalityExpandRTerm e) ::: (phi @ m)
  | modalityCollapseRr :
      forall (Gamma : Context) (phi : flafolFormula) (m : Modality) (pth : PathToDoubleInModality m) (e : proofTerm),
        Gamma ⊢ e ::: (phi @ m) -> 
        Gamma ⊢ (modalityCollapseRTerm e) ::: (phi @ (CollapseDoubleInModality pth))
  | modalityExpandLr :
      forall (Gamma : Context) (phi : flafolFormula) (m : Modality) (pth : PathToDoubleInModality m)
        (b : Belief) (pth' : Path (phi @ (CollapseDoubleInModality pth)) Gamma) (e : proofTerm), (phi @ m :: Gamma) ⊢ e ::: b ->
        Gamma ⊢ (modalityExpandLTerm e) ::: b
  | modalityCollapseLr :
      forall (Gamma : Context) (phi : flafolFormula) (m : Modality) (pth : PathToDoubleInModality m)
        (b : Belief) (pth' : Path (phi @ m) Gamma) (e : proofTerm), (phi @ (CollapseDoubleInModality pth) :: Gamma) ⊢ e ::: b ->
        Gamma ⊢ (modalityCollapseLTerm e) ::: b
  | RVariancer :
      forall (Gamma : Context) (lab1 lab2 : flafolTerm) (phi : flafolFormula) (m : Modality)
        (pi : PathToLabelInModality m lab1) (e1 e2 : proofTerm),
        Gamma ⊢ e1 ::: (phi @ m) ->
        Gamma ⊢ e2 ::: (lab1 ⊑ lab2 @ (VarModality pi lab2)) ->
        Gamma ⊢ (RVarianceTerm e1 e2) ::: (phi @ (ReplaceLabelInModality m lab1 lab2 pi))
  | LVariancer :
      forall (Gamma : Context) (lab1 lab2 : flafolTerm) (phi : flafolFormula) (m : Modality)
        (pi : PathToLabelInModality m lab1) (b : Belief) (pth : Path  (phi @ m) Gamma) (e1 e2 : proofTerm),
        (phi @ ReplaceLabelInModality m lab1 lab2 pi :: Gamma) ⊢ e1 ::: b ->
        Gamma ⊢ e2 ::: (lab1 ⊑ lab2 @ (VarModality pi lab2)) ->
        Gamma ⊢ (LVarianceTerm e1 e2) ::: b
  | FwdRr :
      forall (Gamma : Context) (phi : flafolFormula) (m : Modality)
        (p q : flafolTerm) (pth : PathToPrinInModality m p) (e1 e2 e3 : proofTerm),
        Gamma ⊢ e1 ::: (phi @ m) ->
        Gamma ⊢ e2 ::: ((canRead q (LabelAtPrin pth)) @ (FwdModality pth p)) ->
        Gamma ⊢ e3 ::: ((canWrite p (LabelAtPrin pth)) @ (FwdModality pth q)) ->
        Gamma ⊢ (FwdRTerm e1 e2 e3) ::: (phi @ (ReplacePrinInModality pth q))
  | FwdLr :
      forall (Gamma : Context) (phi : flafolFormula) (m : Modality)
        (p q : flafolTerm) (pth : PathToPrinInModality m q) (b : Belief) (pth' : Path (phi @ m) Gamma)
        (e1 e2 e3 : proofTerm),
        (phi @ ReplacePrinInModality pth p :: Gamma) ⊢ e1 ::: b ->
        Gamma ⊢ e2 ::: ((canWrite q (LabelAtPrin pth)) @ (FwdModality pth p)) ->
        Gamma ⊢ e3 ::: ((canRead p (LabelAtPrin pth)) @ (FwdModality pth q)) ->
        Gamma ⊢ (FwdLTerm e1 e2 e3) ::: b
  | CRVariancer :
      forall (Gamma : Context) (p lab1 lab2 : flafolTerm) (m : Modality) (e1 e2 : proofTerm),
        Gamma ⊢ e1 ::: ((canRead p lab2) @ m) -> Gamma ⊢ e2 ::: ((lab1 ⊑ lab2) @ m) ->
        Gamma ⊢ (CRVarianceTerm e1 e2) ::: ((canRead p lab1) @ m)
  | CWVariancer :
      forall (Gamma : Context) (p lab1 lab2 : flafolTerm) (m : Modality) (e1 e2 : proofTerm),
        Gamma ⊢ e1 ::: ((canWrite p lab1) @ m) -> Gamma ⊢ e2 ::: ((lab1 ⊑ lab2) @ m) ->
        Gamma ⊢ (CWVarianceTerm e1 e2) ::: ((canWrite p lab2) @ m)
  where "Gamma ⊢ t ::: b" := (typing Gamma t b).


  Reserved Notation "Gamma ⊢ b" (at level 25).
  Inductive proof : Context -> Belief -> Set :=
  | axiom : forall (Gamma : Context) (b : Belief),
      ProperContext Gamma -> Path b Gamma -> Gamma ⊢ b
  | TTR :
      forall (Gamma : Context) (m : Modality),
        ProperContext Gamma -> ProperModality m ->
        Gamma ⊢ TT @ m
  | FFL :
      forall (Gamma : Context) (phi : flafolFormula) (m : Modality) (m' : ModalityResidual),
        ProperContext Gamma -> ⊢wff phi -> ProperModality m -> Path (FF @ m) Gamma ->
        ProperModalityResidual m' ->
        Gamma ⊢ phi @ ModalityCombine m m'
  | AndL :
      forall (Gamma : Context) (phi psi : flafolFormula) (m : Modality) (b : Belief) (pth : Path  (phi & psi @ m) Gamma), (phi @ m :: psi @ m :: Gamma) ⊢ b ->
        Gamma ⊢ b
  | AndR :
      forall (Gamma : Context) (phi psi : flafolFormula) (m : Modality),
        Gamma ⊢ phi @ m -> Gamma ⊢ psi @ m ->
        Gamma ⊢ phi & psi @ m
  | OrL :
      forall (Gamma : Context)
        (phi psi : flafolFormula) (m : Modality) (b : Belief)
        (pth : Path  (phi ⊕ psi @ m) Gamma),
        (phi @ m :: Gamma) ⊢ b ->
        (psi @ m :: Gamma) ⊢ b ->
        Gamma ⊢ b
  | OrR1 :
      forall (Gamma : Context) (phi psi : flafolFormula) (m : Modality),
        Gamma ⊢ phi @ m -> ⊢wff psi ->
        Gamma ⊢ phi ⊕ psi @ m
  | OrR2 :
      forall (Gamma : Context) (phi psi : flafolFormula) (m : Modality),
        Gamma ⊢ psi @ m -> ⊢wff phi ->
        Gamma ⊢ phi ⊕ psi @ m
  | ImpL :
      forall (Gamma : Context) (phi psi : flafolFormula) (m : Modality) (l : flafolTerm) (b : Belief) (pth : Path  (phi ==⟨l⟩> psi @ m) Gamma), 
        Gamma ⊢ phi @ ⟨l⟩ -> (psi @ m :: Gamma) ⊢ b ->
        Gamma ⊢ b
  | ImpR :
      forall (Gamma : Context) (phi psi : flafolFormula) (m' : Modality) (l : flafolTerm),
         (phi @ ⟨ l ⟩ :: Gamma) ⊢ psi @ m' ->
        Gamma ⊢ phi ==⟨l⟩> psi @ m'
  | forallL :
      forall (Gamma : Context) (sigma : sort) (phi : flafolFormula) (t : flafolTerm) (m : Modality)
        (b : Belief) (pth : Path (∀ sigma; phi @ m) Gamma),
        lc_term t -> ⊢s t ::: sigma ->
        (open_formula phi t @ m :: Gamma) ⊢ b ->
        Gamma ⊢ b
  | forallR :
      forall (Gamma : Context) (sigma : sort) (y : var) (phi : flafolFormula) (m : Modality),
        VarSort y = sigma -> y ∉FVC Gamma -> y ∉FVF phi -> y ∉FVM m ->
        Gamma ⊢ (open_formula phi (varTerm y)) @ m ->
        Gamma ⊢ ∀ sigma; phi @ m
  | existsL :
      forall (Gamma : Context) (sigma : sort) (y : var) (phi : flafolFormula) (m : Modality) (b : Belief) (pth : Path  (∃ sigma; phi @ m) Gamma),
        VarSort y = sigma ->  y ∉FVC (Gamma) -> y ∉FVB b -> 
        (open_formula phi (varTerm y) @ m :: Gamma) ⊢ b ->
        Gamma ⊢ b
  | existsR :
      forall (Gamma : Context) (sigma : sort) (t : flafolTerm) (phi : flafolFormula) (m : Modality),
        lc_term t -> ⊢s t ::: sigma -> Gamma ⊢ (open_formula phi t) @ m ->
        Gamma ⊢ ∃ sigma; phi @ m
  | flowsToRefl :
      forall (Gamma : Context) (lab : flafolTerm) (m : Modality),
        ProperContext Gamma -> ⊢s lab ::: Label -> ProperModality m ->
        Gamma ⊢ lab ⊑ lab @ m
  | flowsToTransR :
      forall (Gamma : Context)(lab1 lab2 lab3 : flafolTerm) (m : Modality),
        Gamma ⊢ lab1 ⊑ lab2 @ m -> Gamma ⊢ lab2 ⊑ lab3 @ m ->
        Gamma ⊢ lab1 ⊑ lab3 @ m
  | saysR :
      forall (Gamma : Context) (p lab : flafolTerm) (phi : flafolFormula) (m : Modality),
        Gamma ⊢ phi @ (m ⋅ p⟨lab⟩) ->
        Gamma ⊢ p □ ⟨lab⟩ phi @ m
  | saysL :
      forall (Gamma : Context) (p lab : flafolTerm) (phi : flafolFormula) (m : Modality)
        (b : Belief) (pth : Path  (p □ ⟨ lab ⟩ phi @ m) Gamma), ((phi @ m ⋅ p⟨lab⟩) :: Gamma) ⊢ b -> Gamma ⊢ b
  | modalityExpandR :
      forall (Gamma : Context) (phi : flafolFormula) (m : Modality) (pth : PathToDoubleInModality m),
        Gamma ⊢ phi @ (CollapseDoubleInModality pth) -> 
        Gamma ⊢ phi @ m
  | modalityCollapseR :
      forall (Gamma : Context) (phi : flafolFormula) (m : Modality) (pth : PathToDoubleInModality m),
        Gamma ⊢ phi @ m -> 
        Gamma ⊢ phi @ (CollapseDoubleInModality pth)
 | modalityExpandL :
      forall (Gamma : Context) (phi : flafolFormula) (m : Modality) (pth : PathToDoubleInModality m)
        (b : Belief) (pth' : Path (phi @ (CollapseDoubleInModality pth)) Gamma), (phi @ m :: Gamma) ⊢ b -> Gamma ⊢ b
   | modalityCollapseL :
      forall (Gamma : Context) (phi : flafolFormula) (m : Modality) (pth : PathToDoubleInModality m)
        (b : Belief) (pth' : Path (phi @ m) Gamma), (phi @ (CollapseDoubleInModality pth) :: Gamma) ⊢ b ->
        Gamma ⊢ b
  | RVariance :
      forall (Gamma : Context) (lab1 lab2 : flafolTerm) (phi : flafolFormula) (m : Modality)
        (pi : PathToLabelInModality m lab1),
        Gamma ⊢ phi @ m ->
        Gamma ⊢ lab1 ⊑ lab2 @ (VarModality pi lab2) ->
        Gamma ⊢ phi @ (ReplaceLabelInModality m lab1 lab2 pi)
  | LVariance :
      forall (Gamma : Context) (lab1 lab2 : flafolTerm) (phi : flafolFormula) (m : Modality)
        (pi : PathToLabelInModality m lab1) (b : Belief) (pth : Path  (phi @ m) Gamma),
        (phi @ ReplaceLabelInModality m lab1 lab2 pi :: Gamma) ⊢ b ->
        Gamma ⊢ lab1 ⊑ lab2 @ (VarModality pi lab2) ->
        Gamma ⊢ b
  | FwdR :
      forall (Gamma : Context) (phi : flafolFormula) (m : Modality)
        (p q : flafolTerm) (pth : PathToPrinInModality m p),
        Gamma ⊢ phi @ m ->
        Gamma ⊢ (canRead q (LabelAtPrin pth)) @ (FwdModality pth p) ->
        Gamma ⊢ (canWrite p (LabelAtPrin pth)) @ (FwdModality pth q) ->
        Gamma ⊢ phi @ (ReplacePrinInModality pth q)
  | FwdL :
      forall (Gamma : Context) (phi : flafolFormula) (m : Modality)
        (p q : flafolTerm) (pth : PathToPrinInModality m q) (b : Belief) (pth' : Path (phi @ m) Gamma),
        (phi @ ReplacePrinInModality pth p :: Gamma) ⊢ b ->
        Gamma ⊢ (canWrite q (LabelAtPrin pth)) @ (FwdModality pth p) ->
        Gamma ⊢ (canRead p (LabelAtPrin pth)) @ (FwdModality pth q) ->
        Gamma ⊢ b
  | CRVariance :
      forall (Gamma : Context) (p lab1 lab2 : flafolTerm) (m : Modality),
        Gamma ⊢ (canRead p lab2) @ m -> Gamma ⊢ (lab1 ⊑ lab2) @ m ->
        Gamma ⊢ (canRead p lab1) @ m
  | CWVariance :
      forall (Gamma : Context) (p lab1 lab2 : flafolTerm) (m : Modality),
        Gamma ⊢ (canWrite p lab1) @ m -> Gamma ⊢ (lab1 ⊑ lab2) @ m ->
        Gamma ⊢ (canWrite p lab2) @ m
              where "Gamma ⊢ b" := (proof Gamma b).

  Lemma TypingToProof : forall t G b, typing G t b -> G ⊢ b.
  Proof.
    induction t; simpl; intros G0 b0 h0; inversion h0; subst; try (econstructor; eauto; fail).
  Defined.
  
  Lemma ProofToTyping : forall G b, G ⊢ b -> @sigT proofTerm (fun t => typing G t b).
  Proof.
    induction 1; simpl; repeat (match goal with
                                |[h : sigT _ |- _] => destruct h
                                end); try solve [eexists; econstructor; eauto; fail].
  Defined.
                    
  Fixpoint term_size (t : proofTerm) : nat :=
    match t with
    | axiomTerm => 1
    | TTRTerm => 1
    | FFLTerm => 1
    | AndLTerm pf1 => S (term_size (pf1))
    | AndRTerm pf1 pf2 => S (max (term_size pf1) (term_size pf2))                        
    | OrLTerm pf1 pf2 => S (max (term_size pf1) (term_size pf2))
    | OrR1Term pf1 => S (term_size pf1)
    | OrR2Term pf1 => S (term_size pf1)
    | ImpLTerm pf1 pf2 => S (max (term_size pf1) (term_size pf2))
    | ImpRTerm pf1 => S (term_size pf1)
    | forallLTerm pf1 => S (term_size pf1)
    | forallRTerm pf1 => S (term_size pf1)
    | existsLTerm pf1 => S (term_size pf1)
    | existsRTerm pf1 => S (term_size pf1)
    | flowsToReflTerm => 1
    | flowsToTransRTerm pf1 pf2 => S (max (term_size pf1) (term_size pf2))
    | saysRTerm pf1 => S (term_size pf1)
    | saysLTerm pf1 => S (term_size pf1)
    | modalityExpandRTerm pf1 => S (term_size pf1)
    | modalityCollapseRTerm pf1 => S (term_size pf1)
    | modalityExpandLTerm pf1 => S (term_size pf1)
    | modalityCollapseLTerm pf1 => S (term_size pf1)
    | RVarianceTerm pf1 pf2 => S (max (term_size pf1) (term_size pf2))
    | LVarianceTerm pf1 pf2 => S (max (term_size pf1) (term_size pf2))
    | FwdRTerm pf1 pf2 pf3 => S (list_max (term_size pf1) [term_size pf2; term_size pf3])
    | FwdLTerm pf1 pf2 pf3 => S (list_max (term_size pf1) [term_size pf2; term_size pf3])
    | CRVarianceTerm pf1 pf2 => S (max (term_size pf1) (term_size pf2))
    | CWVarianceTerm pf1 pf2 => S (max (term_size pf1) (term_size pf2))
    end.

  
  Program Fixpoint proof_size {Gamma : Context} {b : Belief}
          (pf : Gamma ⊢ b) {struct pf}: nat :=
    match pf with
    | axiom _ _ _ _ => 1
    | TTR _ _ _ _ => 1
    | FFL _ _ _ _ _ _ _ _ _ => 1
    | AndL _ _ _ _ _ _ pf1 => S (proof_size pf1)
    | AndR _ _ _ _ pf1 pf2 => S (max (proof_size pf1) (proof_size pf2))
    | OrL _ _ _ _ _ _ pf1 pf2 =>
      S (max (proof_size pf1) (proof_size pf2))
    | OrR1 _ _ _ _ pf1 _ => S (proof_size pf1)
    | OrR2 _ _ _ _ pf1 _ => S (proof_size pf1)
    | ImpL _ _ _ _ _ _ pth pf1 pf2 =>
      S (max (proof_size pf1) (proof_size pf2))
    | ImpR _ _ _ _ _ pf1 => S (proof_size pf1)
    | forallL _ _ _ _ _ _ _ _ _ pf1 => S (proof_size pf1)
    | forallR _ _ _ _ _ _ _ _ _ pf1 => S (proof_size pf1)
    | existsL _ _ _ _ _ _ _ _ _ _ pf1 => S (proof_size pf1)
    | existsR _ _ _ _ _ _ _ pf1 => S (proof_size pf1)
    | flowsToRefl _ _ _ _ _ _ => 1
    | flowsToTransR _ _ _ _ _ pf1 pf2 =>
      S (max (proof_size pf1) (proof_size pf2))
    | saysR _ _ _ _ _ pf1 => S (proof_size pf1)
    | saysL _ _ _ _ _ _ _ pf1 => S (proof_size pf1)
    | modalityExpandR _ _ _ _ pf1 => S (proof_size pf1)
    | modalityCollapseR _ _ _ _ pf1 => S (proof_size pf1)
    | modalityExpandL _ _ _ _ _ _ pf1 => S (proof_size pf1)
    | modalityCollapseL _ _ _ _ _ _ pf1 => S (proof_size pf1)
    | RVariance _ _ _ _ _ _ pf1 pf2 =>
      S (max (proof_size pf1) (proof_size pf2))
    | LVariance _ _ _ _ _ _ _ pth pf1 pf2 =>
      S (max (proof_size pf1) (proof_size pf2))
    | FwdR _ _ _ _ _ _ pf1 pf2 pf3 =>
      S (list_max (proof_size pf1) [proof_size pf2; proof_size pf3])
    | FwdL _ _ _ _ _ _ _ _ pf1 pf2 pf3 =>
      S (list_max (proof_size pf1) [proof_size pf2; proof_size pf3])
    | CRVariance _ _ _ _ _ pf1 pf2 =>
      S (max (proof_size pf1) (proof_size pf2))
    | CWVariance _ _ _ _ _ pf1 pf2 =>
      S (max (proof_size pf1) (proof_size pf2))
    end.

  Lemma proof_size_JMeq : forall Gamma Delta b1 b2 (pf1 : Gamma ⊢ b1) (pf2 : Delta ⊢ b2),
      Gamma = Delta -> b1 = b2 -> JMeq pf1 pf2 -> proof_size pf1 = proof_size pf2.
  Proof.
    intros Gamma Delta b1 b2 pf1 pf2 H H0.
    Set Printing All.
    generalize dependent pf2.
    destruct H. destruct H0.
    Unset Printing All.
    intros pf2 H.
    apply JMeq_eq in H.
    rewrite H. reflexivity.
  Qed.

  Lemma proof_size_JMeq_lt1 : forall {n} {Gamma Delta} {b1 b2} {pf1 : Gamma ⊢ b1} {pf2 : Delta ⊢ b2},

      JMeq pf1 pf2 -> Gamma = Delta -> b1 = b2 ->n < proof_size pf1 -> n < proof_size pf2.
  Proof.
    intros n Gamma Delta b1 b2 pf1 pf2 H e1 e2 H0.
    rewrite <- (proof_size_JMeq Gamma Delta b1 b2 pf1 pf2 e1 e2 H).
    exact H0.
  Qed.

  Lemma proof_size_JMeq_lt2 : forall {n} {Gamma Delta} {b1 b2} {pf1 : Gamma ⊢ b1} {pf2 : Delta ⊢ b2},
      JMeq pf1 pf2 -> Gamma = Delta -> b1 = b2 -> n < proof_size pf2 -> n < proof_size pf1.
  Proof.
    intros n Gamma Delta b1 b2 pf1 pf2 H e1 e2 H0.
    rewrite (proof_size_JMeq Gamma Delta b1 b2 pf1 pf2 e1 e2 H).
    exact H0.
  Qed.
  
                        
  Ltac provenWFSequent :=
    repeat match goal with
           | [ x : ?P |- ?P ] => exact x
           | [ |- ?P /\ ?Q ] => split
           | [ H : ?P /\ ?Q |- _ ] => destruct H
           | [ H : InBool ?ADec ?a ?l = true |- _ ] =>
             match goal with
             | [ _ : In a l |- _ ] => fail 1
             | _ => pose proof ((proj1 InBoolSpec) H)
             end
           | [ H : Path ?a ?l |- _ ] =>
             match goal with
             | [ _ : In a l |- _ ] => fail 1
             | _ => pose proof (PathToIn H)
             end
           | [ H : ProperBelief (?phi @ ?m) |- _ ] =>
             unfold ProperBelief in H; simpl in H; destruct H
           | [ H : ProperContext (?Delta ++ ?Gamma) |- _ ] => apply ProperContextApp in H
           | [ H : ProperContext (?b :: ?Gamma) |- _ ] => apply ConsProperContext in H
           | [ inG : In ?b ?Gamma, pctxt : ProperContext ?Gamma |- ProperBelief ?b ] =>
             apply (BeliefInProperContextIsProper b Gamma pctxt inG)
           | [ inG : In (?phi @ ?m) ?Gamma, pctxt : ProperContext ?Gamma |- ProperModality ?m ] =>
             apply (BeliefInProperContextIsProper (phi @ m) Gamma pctxt inG)
           | [ inG : In (?phi @ ?m) ?Gamma, pctxt : ProperContext ?Gamma |- ⊢wff ?phi ] =>
             apply (BeliefInProperContextIsProper (phi @ m) Gamma pctxt inG)
           | [ |- ⊢wff ?phi ] => FindWellFormedFormula'
           | [ |- ProperContext (?Delta ++ ?Gamma) ] => apply AppProperContext
           | [ pctxt : ProperContext ?Gamma |- ProperContext (?b :: ?Gamma) ] =>
             apply (fun pf => ProperContextCons b Gamma pf pctxt)
           | [ |- ProperBelief (?phi @ ?m) ] => simpl
           | [ x : var, H : forall y : var, _ |- _ ] =>
             pose proof (H x)
           end.
  (*
    The proof system enforces well-formedness on everything.
   *)
  Lemma provenWFSequent : forall {Gamma : Context} {b : Belief},
      Gamma ⊢ b -> ProperContext Gamma /\ ProperBelief b.
  Proof.
    intros; induction H; try (timeout 20 provenWFSequent).
    - apply ModalityCombineProper; auto.
    - apply impliesWF; auto.
      all: inversion H0; auto.
    - apply forallWF with (L := y :: varsInFormula phi); eauto.
      intros x H4 H5.
      eapply WFopen_formula_rec with (t1 := varTerm y); eauto.
      rewrite <-e.
      constructor.
    - eapply existsWF with (L := []); intros; eauto.
      eapply WFopen_formula_rec with (t1 := t); eauto.
    - inversion H6; inversion H5; FindWellFormedFormula'.
    - inversion H1; auto.
    - inversion H1; constructor; auto; fail.
    - apply CollapseDoubleProper' with (pth := pth); auto.
    - clear H.
      induction pth; simpl; auto.
      inversion H1; subst; auto.
      inversion H1; subst.
      constructor; auto.
    - apply ReplaceLabelInModalityProper; auto.
      inversion H5; auto.
    - apply ReplacePrinInModalityProper; auto.
      inversion H9; auto.
    - inversion H5; inversion H6; FindWellFormedFormula'.
    - inversion H5; inversion H6; FindWellFormedFormula'.
  Qed.

  Definition provenProperContext : forall {Gamma : Context} {b : Belief},
      Gamma ⊢ b -> ProperContext Gamma :=
    fun Gamma b pf => proj1 (provenWFSequent pf).

  Definition provenProperBelief : forall {Gamma : Context} {b : Belief},
      Gamma ⊢ b -> ProperBelief b :=
    fun Gamma b pf => proj2 (provenWFSequent pf).

  Lemma provenProperContextTyping : forall {Gamma : Context} {b : Belief} {t : proofTerm},
      typing Gamma t b -> ProperContext Gamma.
  Proof.
    intros G b t h0.
    apply TypingToProof in h0.
    eapply provenProperContext; eauto.
  Qed.

  Lemma provenProperBeliefTyping : forall {Gamma : Context} {b : Belief} {t : proofTerm},
      typing Gamma t b -> ProperBelief b.
  Proof.
    intros G b t h0.
    apply TypingToProof in h0.
    eapply provenProperBelief; eauto.
  Qed.

  
  Theorem InContextNotFree : forall (Gamma : Context) (b : Belief) (x : var),
      x ∉FVC Gamma -> In b Gamma -> x ∉FVB b.
  Proof.
    intros Gamma b x Hx Hb Hfvb; apply Hx. unfold freeInContext.
    rewrite Exists_exists; exists b; split; auto.
  Qed.
         
  Program Fixpoint before_belief (b : Belief) (E : Context) {struct E} : Context :=
    match E with
    | [] => []
    | b' :: E' => match BeliefEqDec b' b with
                 | left _ => []
                 | right _ => b' :: (before_belief b E')
                 end
    end.

  Program Fixpoint after_belief (b : Belief) (E : Context) {struct E} : Context :=
    match E with
    | [] => []
    | b' :: E' => match BeliefEqDec b' b with
                 | left _ => E'
                 | right _ => after_belief b E'
                 end
    end.

  Lemma splitE : forall (b : Belief) (E : Context), In b E -> E = (before_belief b E) ++ b :: (after_belief b E).
  Proof.
    intros b E.
    induction E.
    - intro; exfalso; apply in_nil with (a := b); auto.
    - intro. simpl. destruct (BeliefEqDec a b) as [e | n]; [rewrite e; simpl; auto | idtac];
                      simpl; rewrite ->IHE at 1; auto;
                        simpl in H; destruct H; [exfalso; apply n | idtac]; auto.
  Qed.

  Lemma before_belief_proper : forall (b : Belief) (E : Context), ProperContext E -> ProperContext (before_belief b E).
  Proof.
    intros b E H;
      induction E; simpl; auto;
        destruct (BeliefEqDec a b);
        [ unfold ProperContext; apply Forall_nil
        | unfold ProperContext; apply Forall_cons;
          [ apply Forall_inv_car with (l := E); auto
          | apply IHE; apply Forall_inv_cdr with (a := a); auto]].
  Qed.

  Lemma after_belief_proper : forall (b : Belief) (E : Context), ProperContext E -> ProperContext (after_belief b E).
  Proof.
    intros b E H.
    induction E; simpl; auto.
    destruct (BeliefEqDec a b);
      [ apply Forall_inv_cdr with (a := a); auto
      | apply IHE; apply Forall_inv_cdr with (a := a); auto].
  Qed.
  Theorem ProperSubcontext1 : forall (Gamma Delta : Context) (b : Belief),
      ProperContext (b :: Gamma) -> ProperContext Delta -> ProperContext (b :: Delta).
  Proof.
    intros Gamma Delta b H H0.
    apply Forall_inv_car in H.
    apply Forall_cons; auto.
  Qed.

  Theorem ProperSubcontext2 : forall (Gamma Delta : Context) (b1 b2 : Belief),
      ProperContext (b1 :: b2 :: Gamma) -> ProperContext Delta -> ProperContext (b1 :: b2 :: Delta).
  Proof.
    intros Gamma Delta b1 b2 H H0.
    pose proof H.
    apply Forall_inv_car in H.
    apply Forall_inv_cdr in H1.
    apply Forall_cons; [auto | eapply ProperSubcontext1; auto; exact H1].
  Qed.

  Theorem ProperSubcontext3 : forall (Gamma Delta : Context) (b1 b2 b3 : Belief),
      ProperContext (b1 :: b2 :: b3 :: Gamma) -> ProperContext Delta ->
      ProperContext (b1 :: b2 :: b3 :: Delta).
  Proof.
    intros Gamma Delta b1 b2 b3 H H0.
    pose proof H.
    apply Forall_inv_car in H.
    apply Forall_inv_cdr in H1.
    apply Forall_cons; [auto | eapply ProperSubcontext2; auto; exact H1].
  Qed.

    
  Theorem SubcontextWithExtra1 : forall (Gamma Delta : Context) (b1 : Belief),
      (forall b, In b Gamma -> In b Delta) -> forall b, In b (b1 :: Gamma) -> In b (b1 :: Delta).
  Proof.
    intros Gamma Delta b1 H b H0.
    destruct H0; [left; auto | right; apply H; auto].
  Qed.

  Theorem SubcontextWithExtra2 : forall (Gamma Delta : Context) (b1 b2 : Belief),
      (forall b, In b Gamma -> In b Delta) -> forall b, In b (b1 :: b2 :: Gamma) -> In b (b1 :: b2 :: Delta).
  Proof.
    intros Gamma Delta b1 b2 H b H0.
    destruct H0; [left; auto | right; apply SubcontextWithExtra1 with (Gamma := Gamma); auto].
  Qed.
  Theorem SubcontextWithExtra3 : forall (Gamma Delta : Context) (b1 b2 b3 : Belief),
      (forall b, In b Gamma -> In b Delta) -> forall b, In b (b1 :: b2 :: b3 :: Gamma) -> In b (b1 :: b2 :: b3 :: Delta).
  Proof.
    intros Gamma Delta b1 b2 b3 H b H0.
    destruct H0; [left; auto | right; apply SubcontextWithExtra2 with (Gamma := Gamma); auto].
  Qed.
  

  Lemma split_forall : forall (Gamma Delta E : Context) (b : Belief),
      (forall b', In b' (Delta ++ b :: Gamma) -> In b' E) ->
      forall l b', In b' (Delta ++ l ++ b :: Gamma) -> In b' ((before_belief b E) ++ (l ++ b :: (after_belief b E))).
  Proof.
    intros Gamma Delta E b H l b' H0.
    rewrite ->(splitE b E) in H; [idtac | apply H; apply in_or_app; right; left; auto].
    apply in_app_or in H0; destruct H0; [idtac | apply in_app_or in H0; destruct H0; [idtac | destruct H0]].
    - assert (In b' (before_belief b E ++ b :: after_belief b E)) by (apply H; apply in_or_app; left; auto).
      apply in_app_or in H1; destruct H1; [apply in_or_app; left; auto | idtac].
      apply in_or_app; right; apply in_or_app; right; auto.
    - apply in_or_app; right; apply in_or_app; left; auto.
    - apply in_or_app; right; apply in_or_app; right; left; auto.
    - assert (In b' (before_belief b E ++ b :: after_belief b E)) by (apply H; apply in_or_app; right; right; auto).
      apply in_app_or in H1; destruct H1; [apply in_or_app; left; auto | idtac].
      apply in_or_app; right; apply in_or_app; right; auto.
  Qed.

  Lemma split_proper : forall (E l : Context) (b : Belief),
      In b E -> ProperContext E -> ProperContext l ->
      ProperContext ((before_belief b E) ++ (l ++ (b :: (after_belief b E)))).
  Proof.
    intros E l b H H0 H1.
    unfold ProperContext.
    apply Forall_append; split; [fold ProperContext; apply before_belief_proper; auto | idtac].
    apply Forall_append; split; [auto | idtac].
    apply Forall_cons; [idtac | apply after_belief_proper; auto].
    unfold ProperContext in H0; rewrite ->Forall_forall in H0. apply H0; auto.
  Qed.

  Lemma FreshWithMore : forall (Gamma Delta : Context) (y : var),
      (forall b : Belief, In b Gamma -> In b Delta) -> y ∉FVC Delta -> y ∉FVC Gamma.
  Proof.
    intros Gamma Delta y Hsub Hin Hcontra; apply Hin.
    unfold freeInContext; unfold freeInContext in Hcontra.
    rewrite Exists_exists; rewrite ->Exists_exists in Hcontra.
    destruct Hcontra as [x Hx]; destruct Hx.
    exists x; split; auto.
  Qed.


  

  Lemma replacesubst: forall m lab1 lab2 y t pi, {pi'| ReplaceLabelInModality m lab1 lab2 pi mod[ y ↦ t] = ReplaceLabelInModality (m mod[y ↦ t]) (lab1 t[y ↦ t]) (lab2 t[y ↦ t]) pi'}.
    induction pi; simpl; intros; auto.
    - unshelve eexists.
      constructor.
      reflexivity.
    - unshelve eexists.
      constructor.
      reflexivity.
    - destruct IHpi.
      unshelve eexists.
      constructor.
      apply x.
      simpl.
      rewrite e.
      reflexivity.
  Defined.


  Lemma max_inj1 : forall m n p, p <= n -> p <= (max n m).
  Proof.
    intros m n p H.
    etransitivity; eauto.
    apply PeanoNat.Nat.le_max_l.
  Qed.
  Lemma max_inj2 : forall m n p, p <= m -> p <= (max n m).
  Proof.
    intros m n p H.
    etransitivity; eauto.
    apply PeanoNat.Nat.le_max_r.
  Qed.

  Lemma proof_size_eq0: forall Gamma t1 pc m (x1 : Gamma ⊢ t1 ⊑ pc @ m) t2 (p : t2=t1),
      proof_size (eq_rec_r (fun f : flafolTerm => Gamma ⊢ f ⊑ pc @ m) x1 p) = proof_size x1.
  Proof.
    intros Gamma t1 pc m x1 t2 p.
    destruct p.
    reflexivity.
  Qed.
  
  Lemma proof_size_eq1: forall Gamma y t pc m x1,
        proof_size (eq_rec_r (fun f : flafolTerm => (Gamma c[ y ↦ t]) ⊢ f ⊑ (pc t[ y ↦ t]) @ (m mod[ y ↦ t])) x1 (InnermostLabelSubst m y t)) = proof_size x1.
  Proof.
    intros Gamma y t pc m x1.
    destruct (InnermostLabelSubst m y t).
    reflexivity.
  Qed.

  Lemma proof_size_eq11: forall Gamma phi pc1 pc2 m (x1 : Gamma ⊢ phi @ m) (p : pc1=pc2),
      proof_size (eq_rec _ (fun pc : flafolTerm => Gamma ⊢ phi @ m) x1 pc2 p) = proof_size x1.
  Proof.
    intros Gamma phi pc1 pc2 m x1 p.
    destruct p.
    reflexivity.
  Qed.

  Lemma proof_size_eq12: forall Gamma phi phi' pc1 pc2 m m' (x1 : ((phi' @ m) :: Gamma) ⊢ phi @ m') (p : pc1 = pc2),
      proof_size (eq_rec _ (fun pc : flafolTerm => ((phi' @ m) :: Gamma) ⊢ phi @ m') x1 pc2 p) = proof_size x1.
  Proof.
    destruct p.
    reflexivity.
  Qed.  

  Lemma proof_size_eq13: forall Gamma phi phi' pc1 pc2 m m' (x1 : ((phi' @ m) :: Gamma) ⊢ phi @ m') (p : pc1 = pc2),
      proof_size (eq_rec _ (fun pc : flafolTerm => ((phi' @ m) :: Gamma) ⊢ phi @ m') x1 pc2 p) = proof_size x1.
  Proof.
    destruct p.
    reflexivity.
  Qed.  
  Lemma proof_size_eq21: forall G1 G2 b (x1 : G1 ⊢ b) (p : G1=G2),
      proof_size (eq_rec _ (fun Gamma : Context => Gamma ⊢ b) x1 G2 p) = proof_size x1.
  Proof.
    intros G1 G2 b pf p.
    destruct p. 
    reflexivity.
  Qed.

  Lemma proof_size_eq22: forall G1 G2 b b' (x1 : (b :: G1) ⊢ b') (p : G1 = G2),
      proof_size (eq_rec _ (fun G : Context => (b :: G) ⊢ b') x1 G2 p) = proof_size x1.
  Proof.
    intros G1 G2 b b' x1 p.
    destruct p.
    reflexivity.
  Qed.  
  
  Lemma proof_size_eq2: forall G1 G2 b (x1 : G1 ⊢ b) (p : G2=G1),
      proof_size (eq_rec_r (fun Gamma : Context => Gamma ⊢ b) x1 p) = proof_size x1.
  Proof.
    intros G1 G2 b x1 p.
    destruct p.
    reflexivity.
  Qed.

  Lemma proof_size_eq3: forall Gamma phi1 phi2 m (x1 : Gamma ⊢ phi1 @ m) (p : phi2 = phi1),
      proof_size (eq_rec_r (fun phi : flafolFormula => Gamma ⊢ phi @ m) x1 p) = proof_size x1.
  Proof.
    intros Gamma phi1 phi2 m x1 p.
    destruct p.
    reflexivity.
  Qed.  

  Lemma proof_size_eq31: forall Gamma phi1 phi2 m (x1 : Gamma ⊢ phi1 @ m) (p : phi1 = phi2),
      proof_size (eq_rec _ (fun phi : flafolFormula => Gamma ⊢ phi @ m) x1 phi2 p) = proof_size x1.
  Proof.
    intros Gamma phi1 phi2 m x1 p.
    destruct p.
    reflexivity.
  Qed.

   Lemma proof_size_eq32: forall Gamma phi phi1 phi2 m m' (x1 : ((phi1 @ m) :: Gamma) ⊢ phi @ m') (p : phi1 = phi2),
      proof_size (eq_rec _ (fun f : flafolFormula => ((f @ m) :: Gamma) ⊢ phi @ m') x1 phi2 p) = proof_size x1.
  Proof.
    intros Gamma phi phi1 phi2 m m' x1 p.
    destruct p.
    reflexivity.
  Qed.  

  Lemma proof_size_eq4: forall Gamma phi  m1 m2 (x1 : Gamma ⊢ phi @ m1) (p : m2 = m1),
      proof_size (eq_rec_r (fun m : Modality => Gamma ⊢ phi @ m) x1 p) = proof_size x1.
  Proof.
    intros Gamma phi m1 m2 x1 p.
    destruct p.
    reflexivity.
  Qed.

  Lemma proof_size_eq41: forall Gamma phi m1 m2 (x1 : Gamma ⊢ phi @ m1) (p : m1 = m2),
      proof_size (eq_rec _ (fun m : Modality => Gamma ⊢ phi @ m) x1 m2 p) = proof_size x1.
  Proof.
    intros Gamma phi m1 m2 x1 p.
    destruct p.
    reflexivity.
  Qed.

  Lemma proof_size_eq42: forall Gamma phi m1 m2 b (x1 : (phi @ m1 :: Gamma) ⊢ b) (p : m1 = m2),
      proof_size (eq_rec _ (fun m : Modality => (phi @ m :: Gamma) ⊢ b) x1 m2 p) = proof_size x1.
  Proof.
    intros Gamma phi m1 m2 b x1 p.
    destruct p.
    reflexivity.
  Qed.

  
  Lemma fvsubstContext : forall y' y Gamma t, y' ∉FVT t -> y' ∉FVC Gamma -> y' ∉FVC (Gamma c[ y ↦ t]).
  Proof.
    intros y' y Gamma t H H0.
    induction Gamma; simpl; auto.
    apply NotInFVCConsInversion in H0; destruct H0.
    apply NotInFVCCons. apply fvsubstBelief; auto. apply IHGamma; auto.
  Qed.

  Lemma substFormulaNonFreeEqual : forall (f : flafolFormula) (x : var) (t : flafolTerm), x ∉FVF f -> f f[ x ↦ t] = f.
  Proof.
    induction f; simpl; intros; eauto.
    - repeat rewrite substTermNonFreeEqual; auto.
      all: intro; apply H.
      all: econstructor; eauto; fail.
    - f_equal.
      induction l; simpl; auto.
      rewrite substTermNonFreeEqual.
      rewrite IHl; auto.
      all: intro; apply H.
      inversion H0; subst.
      apply freeInRel with (t := t0); simpl; auto.
      apply freeInRel with (t := a); simpl; auto.
    - rewrite substTermNonFreeEqual.
      rewrite substTermNonFreeEqual; auto.
      all: intro; apply H; econstructor; eauto; fail.
    - rewrite substTermNonFreeEqual.
      rewrite substTermNonFreeEqual; auto.
      all: intro; apply H; econstructor; eauto; fail.
    - rewrite IHf1.
      rewrite IHf2; auto.
      all: intro; apply H; econstructor; eauto; fail.
    - rewrite IHf1.
      rewrite IHf2; auto.
      all: intro; apply H; econstructor; eauto; fail.
    - rewrite IHf1.
      rewrite substTermNonFreeEqual.
      rewrite IHf2.
      reflexivity.
      all: intro; apply H; econstructor; eauto; fail.
    - rewrite IHf; auto.
      intro; apply H.
      constructor; auto.
    - rewrite IHf; auto.
      intro; apply H.
      constructor; auto.
    - rewrite IHf.
      rewrite substTermNonFreeEqual.
      rewrite substTermNonFreeEqual.
      reflexivity.
      all: intro; apply H; econstructor; eauto; fail.
  Qed.      

  Program Fixpoint PathSubst {Gamma : Context} {b : Belief} (x : var) (t : flafolTerm)
          (pth : Path b Gamma) : Path (b bel[x ↦ t]) (Gamma c[x ↦ t]) :=
    match pth with
    | Here _ _ => Here _ _
    | There _ pth'  => There _ (PathSubst x t pth')
    end.
  Notation "p pth[ x ↦ t ]" := (PathSubst x t p) (at level 40).
  
  (* There has to be a better/more automated way. *)
  (*    Sadly, reasoning about equality *sucks*. *)
  Ltac substPf' :=
    simpl;
    repeat match goal with
           | [ |- ?a = ?a ] => reflexivity
           | [H : JMeq _ ?pf |- proof_size ?pf1 < proof_size ?pf] =>
             apply JMeq_eq in H; rewrite <- H; simpl; auto
           | [ H : ?y ∉FVC ?Gamma |- context[?Gamma c[ ?y ↦ ?t]] ] =>
             rewrite substContextNonFreeEq; auto
           | [ H : ?y ∉FVM ?m |- context[?m mod[ ?y ↦ ?t]] ] =>
             rewrite NotFreeInModalitySubstEq; auto
           | [ |- freshVar (varsInContext ?Gamma ++ _) _ ∉FVC ?Gamma ] =>
             let H := fresh in
             intro H; apply freeVarsInContext in H
           | [ |- freshVar (_ ++ _++ varsInFormula ?phi ++ _) _ ∉FVF ?phi ] =>
             let H := fresh in
             intro H; apply FreeVarsInFormula in H
           | [ |- freshVar (_ ++ varsInModality ?m ++ _) _ ∉FVM ?m ] =>
             let H := fresh in
             intro H; apply FreeVarsInModality in H
           | [ H : In (freshVar ?l ?sort) ?l' |- False ] =>
             apply freshVarNotIn with (sigma := sort) (vs := l)
           | [ H : In ?x ?l1 |- In ?x (?l1 ++ _) ] =>
             apply in_or_app; left; exact H
           | [ H : In ?x ?l2 |- In ?x (_ ++ ?l2 ++ _) ] =>
             apply in_or_app; right; apply in_or_app; left ; exact H
           | [ H : In ?x ?l3 |- In ?x (_ ++ _ ++ ?l3 ++ _) ] =>
             apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact H
           | [ H : In ?x ?l4 |- In ?x (_ ++ _ ++ _ ++ _ ++ ?l4) ] =>
             apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact H
           | [ |- S _ = S _] => apply f_equal
           | |- context[match ?e with eq_refl => _ end] => destruct e
           | [ |- context[proof_size (proj1_sig (?f ?Gamma ?b ?x ?t ?pf' ?tsort ?lct ?sz))] ] =>
             let H := fresh in
             pose proof (proj2_sig (f Gamma b x t pf' tsort lct sz)) as H;
             rewrite <- H at 1;
             auto; fail
           | [ |- ?a < S(max ?b ?c) ] => apply Lt.le_lt_n_Sm
           | [ |- ?a <= max ?a ?b ] => apply Nat.le_max_l
           | [ |- ?b <= max ?a ?b ] => apply Nat.le_max_r
           | [ |- ?a <= max ?b ?c ] => transitivity ?c
           | [ |- context[eq_rect]] => unfold eq_rect; simpl
           | [ |- context[eq_ind_r]] => unfold eq_ind_r; simpl
           | [ |- context[eq_ind]] => unfold eq_ind; simpl
           | [ |- context[proof_size (proj1_sig (?f ?Gamma ?b ?y ?t ?pf1 ?tsort ?lct ?sz))]] =>
             let H := fresh in
             pose proof (proj2_sig (f Gamma b y t pf1 tsort lct sz)) as H;
             simpl in H; rewrite H; auto

           end.
  
  Definition substT : proofTerm -> var -> flafolTerm -> proofTerm := fun p v t => p.
  
  Lemma substTyping : forall {e G b y t}, typing G e b -> lc_term t -> ⊢s t ::: (VarSort y) -> typing (G c[y ↦ t]) (substT e y t) (b bel[y ↦ t]).
  Proof.
    induction e; simpl; intros; inversion H; subst; unfold substT in *; eauto.
    - apply axiomr.
      apply ProperContextSubst; auto.
      apply PathSubst; auto.
    - apply TTRr.
      apply ProperContextSubst; auto.
      apply ProperModSubst; auto.      
    - simpl.
      rewrite ModalityCombineSubst.
      apply FFLr.
      apply ProperContextSubst; auto.
      apply WellFormedSubst; auto.
      apply ProperModSubst; auto.      
      apply (PathSubst y t H5).
      apply ProperModalityResSubst; auto.
    - eapply AndLr.
      eapply (PathSubst y t pth).
      fold substFormula.
      apply (IHe (phi @ m :: psi @ m :: G)); auto.
    - eapply AndRr; fold substFormula.
      eapply IHe1 with (b := phi @ m); auto.
      eapply IHe2 with (b := psi @ m); auto.
    - eapply OrLr.
      eapply (PathSubst y t pth).
      1, 2 : fold substFormula.
      apply (IHe1 (phi @ m :: G)); auto.
      apply (IHe2 (psi @ m :: G)); auto.
    - apply OrR1r; fold substFormula.
      eapply IHe with (b := phi @ m); auto.
      apply WellFormedSubst; auto.
    - apply OrR2r; fold substFormula.
      eapply IHe with (b := psi @ m); auto.
      apply WellFormedSubst; auto.
    - eapply ImpLr.
      eapply (PathSubst y t pth).
      all : fold substFormula.
      eapply IHe1 with (b := phi @  ⟨ l ⟩); auto.
      apply (IHe2 (psi @ m :: G)); auto.
    - apply ImpRr; fold substFormula.
      eapply (IHe (phi @  ⟨ l ⟩ :: G)) with (b := psi @ m'); auto.
    - eapply forallLr with (t := t0 t[y ↦ t]).
      eapply (PathSubst y t pth).
      apply lc_term_subst; auto.
      apply substTermSortPreserving; auto.
      fold substFormula.
      rewrite <-open_formula_subst; auto.
      pose proof (IHe ((open_formula phi t0) @ m :: G) b y t).
      simpl in H2.
      apply H2; auto.
    - pose ((freshVar (y0 :: y :: ((varsInContext G) ++ (varsInTerm t) ++ (varsInFormula phi) ++ (varsInModality m))) (VarSort y0))) as y'.
      assert (VarSort y' = VarSort y0) by apply freshVarSameSort.
      assert (typing G e (open_formula phi (varTerm y') @ m)).
      + rewrite <-substContextNonFreeEq with (Gamma := G) (x := y0) (t := varTerm y'); auto.
        rewrite <-(substModalityNotFreeEq m y0 (varTerm y')); auto.
        assert (open_formula phi (varTerm y') = open_formula phi (varTerm y0) f[ y0 ↦ varTerm y']).
        * rewrite open_formula_subst; auto.
          rewrite substFormulaNonFreeEqual; auto.
          2: constructor.
          simpl.
          destruct (varEqDec y0 y0); congruence.
        * rewrite H3.
          pose proof (IHe _ _ y0 (varTerm y') H8).
          simpl in H7.
          apply H7.
          constructor.
          rewrite <-H2.
          apply varS.
      + pose (freshVarNotIn (y0 :: y :: ((varsInContext G) ++ (varsInTerm t) ++ (varsInFormula phi) ++ (varsInModality m))) (VarSort y0)).
        apply forallRr with (y := y'); auto.
        * apply fvsubstContext.
          all: intro; apply n; simpl; repeat right.
          apply in_or_app; right.
          all: apply in_or_app; left.
          apply varsInTermFVT; auto.
          apply freeVarsInContext; auto.
        * apply fvsubstFormula.
          all: intro; apply n; simpl; repeat right.
          apply in_or_app; right.
          all: apply in_or_app; right.
          all: apply in_or_app; left.
          apply FreeVarsInFormula; auto.
          apply varsInTermFVT; auto.
        * apply fvsubstModality.
          all: intro; apply n; simpl; repeat right.
          all: apply in_or_app; right.
          apply in_or_app; right.
          apply in_or_app; right.
          apply FreeVarsInModality; auto.
          apply in_or_app; left.
          apply varsInTermFVT; auto.
        * fold substFormula.
          pose proof (IHe _ _ y t H3).
          simpl in H7.
          assert (open_formula (phi f[ y ↦ t]) (varTerm y') = open_formula phi (varTerm y') f[ y ↦ t]).
          -- rewrite open_formula_subst; auto.
             simpl.
             destruct (varEqDec y y'); auto.
             apply False_ind.
             apply (freshVarNotIn (y0 :: y :: ((varsInContext G) ++ (varsInTerm t) ++ (varsInFormula phi) ++ (varsInModality m))) (VarSort y0)).
             simpl.
             right; left; auto.
          -- rewrite H9; auto.
    - destruct b.
      pose ((freshVar (y0 :: y :: ((varsInContext ((phi @ m) :: G)) ++ (varsInTerm t) ++ (varsInFormula phi) ++ varsInFormula f ++ varsInModality m0)) (VarSort y0))) as y'.
      pose proof (IHe _ _ y0 (varTerm y') H7).

      assert ((typing ((open_formula phi (varTerm y') @ m) :: G) e (f @ m0))).
      + rewrite <-substContextNonFreeEq with (Gamma := G) (x := y0) (t := varTerm y'); auto.
        rewrite <-(substModalityNotFreeEq m0 y0 (varTerm y')); auto.
        rewrite <-(substFormulaNonFreeEqual f y0 (varTerm y')); auto.
        rewrite <-(substModalityNotFreeEq m y0 (varTerm y')); auto.
        3, 4: intro; apply H5; (repeat econstructor; eauto; fail).
        assert (open_formula phi (varTerm y') = open_formula phi (varTerm y0) f[ y0 ↦ varTerm y']).
        rewrite open_formula_subst; auto.
        2: constructor.
        simpl.
        destruct (varEqDec y0 y0); auto; try congruence.
        rewrite substFormulaNonFreeEqual; auto.
        1, 3 : intro h; apply H4; apply Exists_exists; exists (∃ VarSort y0; phi @ m).
        1, 2 : split; try apply PathToIn; auto.
        econstructor; econstructor; eauto; fail.
        econstructor; eauto; fail.
        rewrite H3.
        apply H2; auto.
        constructor.
        erewrite <-freshVarSameSort. constructor.
      + assert (VarSort y' = VarSort y0) by apply freshVarSameSort.
        pose (freshVarNotIn (y0
                               :: y
                               :: varsInContext ((phi @ m) :: G) ++
                               varsInTerm t ++ varsInFormula phi ++ varsInFormula f ++ varsInModality m0) (VarSort y0)) as ini.
        eapply existsLr with (y := y'); eauto.
        apply (PathSubst y t pth).
        * apply fvsubstContext.
          all: intro; apply ini; simpl; repeat right.
          apply in_or_app; right.
          apply in_or_app; left.
          apply varsInTermFVT; auto.
          apply in_or_app; left.
          apply in_or_app; right.
          apply freeVarsInContext; auto.
        * apply fvsubstBelief.
          all: intro; apply ini; simpl; repeat right.
          apply in_or_app; right.
          apply in_or_app; left.
          apply varsInTermFVT; auto.
          inversion H8; subst.
          all: apply in_or_app; right.
          all: apply in_or_app; right.
          all: apply in_or_app; right.
          apply in_or_app; right.
          apply FreeVarsInModality; auto.
          apply in_or_app; left.
          apply FreeVarsInFormula; auto.
        * fold substFormula.
          pose proof (IHe _ _ y t H3).
          assert (open_formula (phi f[ y ↦ t]) (varTerm y') = open_formula phi (varTerm y') f[ y ↦ t]).
          -- rewrite open_formula_subst; auto.
             simpl.
             destruct (varEqDec y y'); auto.
             apply False_ind.
             apply ini.
             simpl.
             right; left; auto.
          -- rewrite H9.
             apply H8; auto.
    - apply existsRr with (t := t0 t[y ↦ t]); auto.
      apply lc_term_subst; auto.
      apply substTermSortPreserving; auto.
      fold substFormula.
      rewrite <- open_formula_subst; auto.
      pose proof (IHe G ((open_formula phi t0) @ m) y t).
      simpl in H2.
      auto.
    - apply flowsToReflr; auto.
      apply ProperContextSubst; auto.
      apply substTermSortPreserving; auto.
      apply ProperModSubst; auto.
    - eapply flowsToTransRr; fold substFormula.
      eapply IHe1 with (b := lab1 ⊑ lab2 @ m); auto.
      eapply IHe2 with (b := lab2 ⊑ lab3 @ m); auto.
    - eapply saysRr; fold substFormula.
      eapply IHe with (b :=  phi @ m ⋅ p ⟨ lab ⟩); auto.
    - eapply saysLr.
      eapply (PathSubst y t pth).
      fold substFormula.
      apply (IHe (phi @ m ⋅ p ⟨ lab ⟩ :: G)); auto.
    - pose proof (IHe _ _ y t H4).
      simpl in H2.
      rewrite DoubleSubst in H2.      
      eapply modalityExpandRr; auto.
    - simpl.
      rewrite DoubleSubst.
      apply modalityCollapseRr.
      apply IHe with (b := phi @ m); auto.
    - eapply modalityExpandLr with (phi := phi f[y ↦ t]) (pth := (PathToDoubleSubst pth y t)).
      rewrite <-DoubleSubst.
      eapply (PathSubst y t pth').
      apply (IHe (phi @ m :: G)); auto.
    - pose proof (IHe _ _ y t H4).
      simpl in H2.
      rewrite DoubleSubst in H2.      
      eapply modalityCollapseLr; auto.
      eapply (PathSubst y t pth').
    - simpl.
      rewrite ReplaceLabelInModalitySubst.
      apply RVariancer.
      apply IHe1 with (b := phi @ m); auto.
      pose proof (IHe2 _ _ y t H7) as h0.
      simpl in h0.
      rewrite <-VarModalitySubst.
      auto.
    - eapply LVariancer with (phi := phi f[y ↦ t]) (m := m mod[y ↦ t]) (lab1 := lab1 t[ y ↦ t]) (lab2 := lab2 t[ y ↦ t]).
      eapply (PathSubst y t pth).
      pose proof (IHe1 _ _ y t H5) as h0.
      simpl in h0.
      rewrite ReplaceLabelInModalitySubst in h0.
      eauto.
      pose proof (IHe2 _ _ y t H7) as h0.
      simpl in h0.
      pose proof (VarModalitySubst m lab1 lab2 y t pi).
      rewrite <-VarModalitySubst.
      auto.
    - simpl.
      rewrite ReplacePrinInModalitySubst.
      apply FwdRr.
      apply IHe1 with (b := phi @ m); auto.
      + pose proof (IHe2 _ _ y t H8) as h0.
        rewrite <-FwdModalitySubst.
        rewrite <-LabelAtPrinSubst.
        auto.
      + pose proof (IHe3 _ _ y t H9) as h0.
        rewrite <-FwdModalitySubst.
        rewrite <-LabelAtPrinSubst.
        auto.
    - eapply FwdLr with (phi := phi f[y ↦ t]) (m := m mod[y ↦ t]) (p := p t[ y ↦ t]) (q := q t[ y ↦ t]).
      eapply (PathSubst y t pth').
      pose proof (IHe1 _ _ y t H6) as h0.
      simpl in h0.
      rewrite ReplacePrinInModalitySubst in h0.
      eauto.
      + pose proof (IHe2 _ _ y t H8) as h0.
        rewrite <- FwdModalitySubst.
        rewrite <-LabelAtPrinSubst.
        auto.
      + pose proof (IHe3 _ _ y t H9) as h0.
        rewrite <- FwdModalitySubst.
        rewrite <-LabelAtPrinSubst.
        auto.
    - apply CRVariancer with (lab2 := lab2 t[y ↦ t]).
      apply IHe1 with (b := canRead p lab2 @ m); auto.
      apply IHe2 with (b := lab1 ⊑ lab2 @ m); auto.
    - apply CWVariancer with (lab1 := lab1 t[y ↦ t]).
      apply IHe1 with (b := canWrite p lab1 @ m); auto.
      apply IHe2 with (b := lab1 ⊑ lab2 @ m); auto.
  Qed.

  Lemma substPf : forall Γ b y t, Γ ⊢ b -> ⊢s t ::: (VarSort y) -> lc_term t ->
                             (Γ c[y ↦ t]) ⊢ (b bel[y ↦ t]).
  Proof.
    intros.
    apply ProofToTyping in H.
    destruct H.
    apply TypingToProof with (t := x).
    apply substTyping; auto.
  Qed.

  
  Lemma open_with_fresherRT1 : forall Gamma phi m y y' t (h : typing Gamma t (open_formula phi (varTerm y) @ m)), VarSort y = VarSort y' -> y ∉FVC Gamma -> y ∉FVF phi -> y ∉FVM m -> typing Gamma t (open_formula phi (varTerm y') @ m).
  Proof.
    intros Gamma phi m y y' pf H H0 H2 H3 H4.
    assert (open_formula phi (varTerm y') = open_formula phi (varTerm y) f[ y ↦ varTerm y']).
    rewrite open_formula_subst; simpl; auto.
    rewrite substFormulaNonFreeEqual; auto.
    destruct (varEqDec y y); try congruence; auto.
    constructor.
    rewrite <-substContextNonFreeEq with (Gamma := Gamma) (x := y) (t := varTerm y'); auto.
    rewrite <-substModalityNotFreeEq with (m := m) (x := y) (t := varTerm y'); auto.
    rewrite H1.
    apply @substTyping with (b := open_formula phi (varTerm y) @ m); auto.
    constructor.
    rewrite H0; constructor.
  Qed.
  
  Lemma open_with_fresherRT : forall Gamma phi m y y' t (h : typing Gamma t (open_formula phi (varTerm y) @ m)), VarSort y = VarSort y' -> y ∉FVC Gamma -> y ∉FVF phi -> y ∉FVM m -> sigT (fun t'  => typing Gamma t' (open_formula phi (varTerm y') @ m)).
  Proof.
    intros.
    exists t.
    eapply open_with_fresherRT1; eauto.
  Qed.    

  Lemma open_with_fresherRTS : forall Gamma phi m y y' t (h : typing Gamma t (open_formula phi (varTerm y) @ m)), VarSort y = VarSort y' -> y ∉FVC Gamma -> y ∉FVF phi -> y ∉FVM m -> sigT (fun t'  => prod (typing Gamma t' (open_formula phi (varTerm y') @ m)) (term_size t = term_size t')).
  Proof.
    intros.
    exists t.
    split; [eapply open_with_fresherRT1; eauto | auto].
  Qed.
  
  Lemma open_with_fresherLT1 : forall Gamma phi psi m m' y y' t (h : typing ((open_formula phi (varTerm y)) @ m :: Gamma) t (psi @ m')), Path (∃ VarSort y; phi @ m) Gamma -> VarSort y = VarSort y' -> y ∉FVC Gamma -> y ∉FVF psi -> y ∉FVM m' -> typing ((open_formula phi (varTerm y')) @ m :: Gamma) t (psi @ m').
  Proof.
    intros Gamma phi psi m m' y y' pf h H H0 H1 H2 H3.
    assert (open_formula phi (varTerm y') = open_formula phi (varTerm y) f[ y ↦ varTerm y']).
    rewrite open_formula_subst; simpl; auto.
    rewrite substFormulaNonFreeEqual; auto.
    destruct (varEqDec y y); try congruence; auto.
    intro.
    apply H1.
    unfold freeInContext.
    apply Exists_exists.
    exists (∃ VarSort y; phi @ m).
    split.
    apply PathToIn; auto.
    econstructor; econstructor; eauto; fail.
    constructor.
    rewrite <-substContextNonFreeEq with (Gamma := Gamma) (x := y) (t := varTerm y'); auto.
    rewrite <-substModalityNotFreeEq with (m := m') (x := y) (t := varTerm y'); auto.
    rewrite <-substModalityNotFreeEq with (m := m) (x := y) (t := varTerm y'); auto.
    rewrite <-substFormulaNonFreeEqual with (f := psi) (x := y) (t := varTerm y'); auto.
    rewrite H4.
    apply @substTyping with (b := psi @ m') (G := open_formula phi (varTerm y) @ m :: Gamma); auto.
    constructor.
    rewrite H0; constructor.
    intro; apply H1.
    apply Exists_exists.
    exists (∃ VarSort y; phi @ m).
    split.
    apply PathToIn; auto.
    econstructor; eauto; fail.
  Qed.

  Lemma open_with_fresherLT : forall Gamma phi psi m m' y y' t (h : typing ((open_formula phi (varTerm y)) @ m :: Gamma) t (psi @ m')), Path (∃ VarSort y; phi @ m) Gamma -> VarSort y = VarSort y' ->  y ∉FVC Gamma -> y ∉FVF psi -> y ∉FVM m' -> sigT (fun t' => typing ((open_formula phi (varTerm y')) @ m :: Gamma) t' (psi @ m')).
  Proof.
    intros.
    exists t.
    eapply open_with_fresherLT1; eauto.
  Qed.

  Lemma open_with_fresherLT' : forall Gamma phi b m y y' t (h : typing ((open_formula phi (varTerm y)) @ m :: Gamma) t b), Path (∃ VarSort y; phi @ m) Gamma -> VarSort y = VarSort y' -> y ∉FVC Gamma ->  y ∉FVB b -> sigT (fun t' => typing ((open_formula phi (varTerm y')) @ m :: Gamma) t' b).
  Proof.
    intros.
    destruct b.
    exists t.
    eapply open_with_fresherLT1; eauto.
    all : intro.
    all : apply H2.
    all : econstructor; eauto; fail.
  Qed.

  Lemma open_with_fresherLTS : forall Gamma phi psi m m' y y' t (h : typing ((open_formula phi (varTerm y)) @ m :: Gamma) t (psi @ m')), Path (∃ VarSort y; phi @ m) Gamma -> VarSort y = VarSort y' -> y ∉FVC Gamma -> y ∉FVF psi -> y ∉FVM m' -> sigT (fun t' => prod (typing ((open_formula phi (varTerm y')) @ m :: Gamma) t' (psi @ m')) (term_size t = term_size t')).
  Proof.
    intros.
    exists t; split; auto.
    eapply open_with_fresherLT1; eauto.
  Qed.
    
  Lemma open_with_fresherLTS' : forall Gamma phi b m y y' t (h : typing ((open_formula phi (varTerm y)) @ m :: Gamma) t b), Path (∃ VarSort y; phi @ m) Gamma -> VarSort y = VarSort y' -> y ∉FVC Gamma ->  y ∉FVB b -> sigT (fun t' => prod (typing ((open_formula phi (varTerm y')) @ m :: Gamma) t' b) (term_size t = term_size t')).
  Proof.
    intros.
    destruct b.
    exists t; split; auto.
    eapply open_with_fresherLT1; eauto.
    all : intro.
    all : apply H2.
    all : econstructor; eauto; fail.
  Qed.
  
  Hint Resolve InBoolSubset.
  Hint Resolve ProperSubcontext1.
  Hint Resolve ProperSubcontext2.
  Hint Resolve ProperSubcontext3.
  Hint Resolve provenProperContext.
  Hint Resolve SubcontextWithExtra1.
  Hint Resolve SubcontextWithExtra2.
  Hint Resolve SubcontextWithExtra3.
  Hint Resolve freshInSequentIsFresh.
  Hint Resolve freshInSequentOfSort.
 Lemma InCons: forall (l:Belief) m a , In a (l :: m) -> {a = l} + {In a m}.
  Proof.
    intros l m a H.
    eapply InBoolSpec in H.
    eapply InBoolCons in H.
    destruct H; auto.
    right.
    eapply InBoolSpec; eauto.
    Unshelve.
    apply BeliefEqDec.
  Qed.

  Ltac destructProd :=
    match goal with
    | [h : prod _ _ |- _] => destruct h
    end.
  
  Ltac destr_In :=
    match goal with
    | [H1 : In _ (?x :: ?G) |- _] => apply InCons in H1;
                                   destruct H1; [idtac| destr_In]
    | _ => idtac
    end.

    Lemma PathSplit : forall {A : Set} {a : A} l1 l2, Path a l1 + Path a l2 -> Path a (l1 ++ l2).
  Proof.
    induction l1; simpl; intros; eauto.
    - destruct H; auto.
      inversion p.
    - destruct H.
      inversion p; subst.
      apply Here.
      all : apply There; auto.
  Qed.    


  Lemma SplitPath {A : Set} {a : A} (l1 l2 : list A) (pth : Path a (l1 ++ l2)) : (Path a l1) + (Path a l2).
  Proof.
    induction l1; simpl in *; auto.
    inversion pth; subst; auto.
    left; constructor.
    destruct (IHl1 H1); auto.
    left; econstructor; eauto; fail.    
  Qed.        
    
  Lemma ExchangePath : forall {A : Set} L1 {L2 L3} {b : A}, Path b (L1 ++ L2 ++ L3) -> Path b (L2 ++ L1 ++ L3).
  Proof.
    intros A L1 L2.
    revert L1.
    induction L2; simpl; auto.
    intros.
    apply SplitPath in H.
    destruct H.
    apply PathSplit with (l1 := a :: L2).
    right.
    apply PathSplit.
    left; auto.
    inversion p; subst.
    apply Here.
    apply There.
    apply SplitPath in H1.
    destruct H1.
    apply PathSplit with (l1 := L2); tauto.
    apply PathSplit.
    right.
    apply PathSplit.
    right; auto.
  Qed.

  Lemma ExchangeProper : forall L1 {L2 L3}, ProperContext (L1 ++ L2 ++ L3) -> ProperContext (L2 ++ L1 ++ L3).
  Proof.
    induction L1; auto.
    intros.
    inversion H; subst.
    pose proof (IHL1 _ _ H3).
    apply AppProperContext.
    pose proof (ProperContextApp).
    edestruct H1.
    apply H0; auto.
    auto.
    constructor; auto.
    apply ProperContextApp in H0.
    apply H0.
  Qed.
  
  Ltac solveSubPath := intro; simpl;
                     repeat (match goal with
                             | [|- prod (Path _ ?G1 -> Path _ ?G2) (Path _ ?G2 -> Path _ ?G1)] => split
                             | [|- Path _ (?a :: ?b :: ?c :: _ ++ _ ) -> Path _ (_ ++ (?a :: ?b :: ?c :: _))] => apply (ExchangePath [a; b; c])
                             | [|- Path _ (_ ++ (?a :: ?b :: ?c :: _)) -> Path _ (?a :: ?b :: ?c :: _ ++ _ )] => apply @ExchangePath with (L2 := [a; b; c])
                             | [|- Path _ (?a :: ?b :: _ ++ _ ) -> Path _ (_ ++ (?a :: ?b :: _))] => apply (ExchangePath [a; b])
                             | [|- Path _ (_ ++ (?a :: ?b :: _)) -> Path _ (?a :: ?b :: _ ++ _ )] => apply @ExchangePath with (L2 := [a; b])
                             | [|- Path _ (?a :: _ ++ _ ) -> Path _ (_ ++ (?a :: _))] => apply (ExchangePath [a])
                             | [|- Path _ (_ ++ (?a ::  _)) -> Path _ (?a :: _ ++ _ )] => apply @ExchangePath with (L2 := [a])
                             | [|- (Path _ ?G1 -> Path _ ?G2)] => let h := fresh in
                                                               intro h; apply PathToIn in h; apply (InToPath BeliefEqDec); simpl; destr_In; eauto
                             end).

  Ltac fttIH := try (match goal with 
                     | [IH1 : forall _ _ _ _ _ _, typing _ ?t1 _ -> _, h1 : typing _ ?t1 _, IH2 : forall _ _ _ _ _ _, typing _ ?t2 _ -> _, h2 : typing _ ?t2 _, IH3 : forall _ _ _ _ _ _, typing _ ?t3 _ -> _, h3 : typing _ ?t3 _ |- _] => edestruct IH1 with (1 := h1); eauto; edestruct IH2 with (1 := h2); eauto; edestruct IH3 with (1 := h3); eauto
                     | [IH1 : forall _ b1 _ _ _ _, typing _ ?t1 b1 -> _, h1 : typing _ ?t1 ?b, IH2 : forall _ b2 _ _ _ _, typing _ ?t2 b2 -> _, h2 : typing _ ?t2 ?b' |- _] => edestruct IH1 with (b1 := b) (1 := h1); eauto; edestruct IH2 with (b2 := b') (1 := h2); eauto
                     | [IH1 : forall _ b1 _ _ _ _, typing _ ?t1 b1 -> _, h1 : typing _ ?t1 ?b |- _] => edestruct IH1 with (b1 := b) (1 := h1) ; eauto
                     end; eexists; econstructor; eauto; fail).

  Ltac solvePrope := match goal with
                     | [h : typing ?G _ _ |- ProperContext ?G] => apply (provenProperContextTyping h)
                     | [h : typing (?a :: ?b :: ?c :: _ ++ ?G) _ _  |- ProperContext (?a :: ?b :: ?c :: ?G)] => apply provenProperContextTyping in h; apply ExchangeProper with (L1 := [a; b; c]) in h; destruct (ProperContextApp _ _ h); auto 
                     | [h : typing (?a :: ?b :: _ ++ ?G) _ _  |- ProperContext (?a :: ?b :: ?G)] => apply provenProperContextTyping in h; apply ExchangeProper with (L1 := [a;b]) in h; destruct (ProperContextApp _ _ h); auto 
                     | [h : typing (?a :: _ ++ ?G) _ _  |- ProperContext (?a :: ?G)] => apply provenProperContextTyping in h; apply ExchangeProper with (L1 := [a]) in h; destruct (ProperContextApp _ _ h); auto
                     end.

  
  Definition weak (t : proofTerm) (G : Context) : proofTerm := t.
  
  Definition WeakeningTyping : forall {t G1 G2 b}, typing G1 t b -> ProperContext G2 -> (forall {b'}, Path b' G1 -> Path b' G2) -> typing G2 (weak t G2) b.
  Proof.
    unfold weak.
    induction t; simpl; intros; inversion H; subst;
      try (match goal with
           |[h : Path _ _ |- _] => pose proof (H1 _ h)
           end); try solve [econstructor; eauto; fail].
    - eapply AndLr; eauto.
      eapply IHt; eauto.
      apply provenProperContextTyping in H4.
      inversion H4; subst; auto.
      inversion H7; subst.
      repeat (constructor; auto).
      intros.
      inversion H3; subst.
      apply Here.
      inversion H7; subst.
      apply There; apply Here.
      repeat apply There; auto.
    - eapply OrLr; eauto.
      eapply IHt1; eauto.
      apply provenProperContextTyping in H5.
      inversion H5; subst; auto.
      repeat (constructor; auto).
      intros.
      inversion H3; subst.
      apply Here.
      repeat apply There; auto.
      eapply IHt2; eauto.
      apply provenProperContextTyping in H7.
      inversion H7; subst; auto.
      repeat (constructor; auto).
      intros.
      inversion H3; subst.
      apply Here.
      repeat apply There; auto.
    - eapply ImpLr; eauto.
      eapply IHt2; eauto.
      apply provenProperContextTyping in H7.
      inversion H7; subst; auto.
      repeat (constructor; auto).
      intros.
      inversion H3; subst.
      apply Here.
      repeat apply There; auto.
    - eapply ImpRr; eauto.
      eapply IHt; eauto.
      apply provenProperContextTyping in H4.
      inversion H4; subst; auto.
      repeat (constructor; auto).
      intros.
      inversion H2; subst.
      apply Here.
      repeat apply There; auto.
    - eapply forallLr; eauto.
      eapply IHt; eauto.
      apply provenProperContextTyping in H6.
      inversion H6; subst; auto.
      repeat (constructor; auto).
      intros.
      inversion H5; subst.
      apply Here.
      repeat apply There; auto.
    - eapply forallRr with (y := (freshInSequent G2 (phi @ m) (VarSort y))); try apply freshInSequentIsFresh; auto.
      1, 2: intro; eapply freshInSequentIsFresh with (b := phi @ m); econstructor; eauto; fail.
      pose (open_with_fresherRT1 _ _ _ _ (freshInSequent G2 (phi @ m) (VarSort y)) t H8); auto.
      eapply IHt; eauto.
    - eapply existsLr with (y := (freshInSequent G2 b (VarSort y))); try apply freshInSequentIsFresh; eauto.
      destruct b.
      pose (open_with_fresherLT1 _ _ _ _ _ _ (freshInSequent G2 (f @ m0) (VarSort y)) t H7); auto.
      eapply IHt. apply t0; eauto.
      1,2 : intro; apply H5; econstructor; eauto; fail.
      clear t0; apply provenProperContextTyping in H7.
      inversion H7; subst; auto.
      repeat (constructor; auto).
      inversion H8; subst; auto.
      inversion H8; subst.
      eapply WFopen_formula_rec; eauto.
      constructor.
      erewrite <- freshInSequentOfSort.
      constructor.
      intros.
      inversion H3; subst.
      apply Here.
      repeat apply There; auto.
    - eapply saysLr; eauto.
      eapply IHt; eauto.
      apply provenProperContextTyping in H4.
      inversion H4; subst; auto.
      repeat (constructor; auto).
      intros.
      inversion H3; subst.
      apply Here.
      repeat apply There; auto.
    - eapply modalityExpandLr; eauto.
      eapply IHt; eauto.
      apply provenProperContextTyping in H4.
      inversion H4; subst; auto.
      repeat (constructor; auto).
      intros.
      inversion H3; subst.
      apply Here.
      repeat apply There; auto.
    - eapply modalityCollapseLr with (pth := pth); eauto.
      eapply IHt; eauto.
      apply provenProperContextTyping in H4.
      inversion H4; subst; auto.
      repeat (constructor; auto).
      intros.
      inversion H3; subst.
      apply Here.
      repeat apply There; auto.
    - eapply LVariancer; eauto.
      eapply IHt1; eauto.
      apply provenProperContextTyping in H5.
      inversion H5; subst; auto.
      repeat (constructor; auto).
      intros.
      inversion H3; subst.
      apply Here.
      repeat apply There; auto.
    - eapply FwdLr; eauto.
      eapply IHt1; eauto.
      apply provenProperContextTyping in H6.
      inversion H6; subst; auto.
      repeat (constructor; auto).
      intros.
      inversion H3; subst.
      apply Here.
      repeat apply There; auto.
  Defined.
    

  Lemma WeakeningTypingSize  : forall t G, term_size (weak t G) = term_size t.
    unfold weak; auto.
  Defined.

  Lemma Weakening
          {Gamma : Context} {b : Belief}
          (pf : Gamma ⊢ b) (Delta : Context) (DeltaProper : ProperContext Delta)
          (GammaSubDelta : forall {b'}, Path b' Gamma -> Path b' Delta)
    : Delta ⊢ b.
  Proof.
    apply ProofToTyping in pf.
    destruct pf.
    apply TypingToProof with (t := x).
    eapply WeakeningTyping; eauto.
  Defined.


  Program Definition ProofToTypingSizeConc : Type :=
    forall {Gamma : Context} {b : Belief} (pf : Gamma ⊢ b), _ = proof_size pf.
  Next Obligation.
    destruct (ProofToTyping Gamma b pf).
    exact (term_size x).
  Defined.
  Lemma ProofToTypingSize : ProofToTypingSizeConc.
  Proof.
    unfold ProofToTypingSizeConc.
    intros Gamma b pf.
    unfold ProofToTypingSizeConc_obligation_1; simpl.
    induction pf; simpl; auto;
      repeat (match goal with
              | [ |- context[ProofToTyping _ _ ?pf] ]=> destruct (ProofToTyping _ _ pf); simpl; auto
              end).
  Qed.

  Lemma TypingToProofSize : forall (t : proofTerm) (Gamma : Context) (b : Belief)
                              (ty : typing Gamma t b),
      term_size t = proof_size (TypingToProof t Gamma b ty).
  Proof.
    intros t Gamma b ty.
    induction ty; simpl; auto.
    all: unfold eq_rec_r; simpl; unfold eq_rec; unfold eq_rect; simpl;
      destruct e0; simpl; rewrite IHty; auto.
  Qed.

  Lemma WeakeningSize : forall {Gamma : Context} {b : Belief} (pf : Gamma ⊢ b) (Delta : Context)
                          (DeltaProper : ProperContext Delta)
                          (GammaSubDelta : forall {b' : Belief}, Path b' Gamma -> Path b' Delta),
      proof_size pf = proof_size (Weakening pf Delta DeltaProper (fun b' pth => GammaSubDelta pth)).
  Proof.
    intros Gamma b pf Delta DeltaProper GammaSubDelta.
    unfold Weakening. symmetry.
    pose proof (ProofToTypingSize Gamma b pf). simpl in H. unfold ProofToTypingSizeConc_obligation_1 in H.
    destruct (ProofToTyping Gamma b pf).
    rewrite <- TypingToProofSize; auto.
  Qed.
  
  Program Definition Weakening' {Gamma : Context} {b : Belief}
          (pf : Gamma ⊢ b)
          (Delta : Context) (pctxt_Delta : ProperContext Delta)
          (sub : forall b' : Belief, In b' Gamma -> In b' Delta) :=
    Weakening pf Delta pctxt_Delta (fun b p => (InToPath BeliefEqDec (sub b (PathToIn p)))).

  Lemma Weakening'Size : forall {Gamma : Context} {b : Belief} (pf : Gamma ⊢ b) (Delta : Context)
                           (pctxt_Delta : ProperContext Delta)
                           (sub : forall b' : Belief, In b' Gamma -> In b' Delta),
      proof_size pf = proof_size (Weakening' pf Delta pctxt_Delta sub).
  Proof.
    intros Gamma b pf Delta pctxt_Delta sub.
    unfold Weakening'. apply WeakeningSize.
  Qed.
  
  Lemma ContextIff : forall (Gamma Delta : Context) (b : Belief),
      (forall b, In b Gamma <-> In b Delta) -> Gamma ⊢ b -> Delta ⊢ b.
  Proof.
    intros Gamma Delta b H H0.
    eapply Weakening'; eauto.
    apply H.
  Qed.

  Theorem Exchange : forall t G1 G2 b, typing G1 t b -> (forall b, prod (Path b G1 -> Path b G2) (Path b G2 -> Path b G1) ) -> typing G2 t b. 
  Proof.
    induction t; simpl; intros; assert (forall b, Path b G1 -> Path b G2) by (apply H0; auto); inversion H; subst; try (econstructor; eauto; fail); try constructor; auto.    
    - eapply ProperContextIff; eauto.
      intro.
      split.
      intro.
      apply InToPath in H4.
      2 : apply BeliefEqDec.
      apply PathToIn; auto.
      intro.
      apply InToPath in H4.
      2 : apply BeliefEqDec.
      apply PathToIn; apply H0; auto.
    - eapply ProperContextIff; eauto.
      intro.
      split.
      intro.
      apply InToPath in H4.
      2 : apply BeliefEqDec.
      apply PathToIn; auto.
      intro.
      apply InToPath in H4.
      2 : apply BeliefEqDec.
      apply PathToIn; apply H0; auto.
    - eapply ProperContextIff; eauto.
      intro.
      split.
      intro.
      apply InToPath in H7.
      2 : apply BeliefEqDec.
      apply PathToIn; auto.
      intro.
      apply InToPath in H7.
      2 : apply BeliefEqDec.
      apply PathToIn; apply H0; auto.
    - econstructor; eauto.
      eapply IHt; eauto.
      intros; split; intro.
      all : inversion H2; subst.
      1, 3 : apply Here.
      all : inversion H6; subst.
      1, 3 : apply There; apply Here.
      all : repeat apply There; apply H0; auto.
    - econstructor; eauto.
      2 : eapply IHt2; eauto.
      eapply IHt1; eauto.
      all : intro b0; split; intro h.
      all : inversion h; subst.
      1, 3, 5, 7 : apply Here.
      all : repeat apply There; apply H0; auto.
    - econstructor; eauto.
      eapply IHt2; eauto.
      intros; split; intro h.
      all : inversion h; subst.
      1, 3 : apply Here.
      all : apply There; apply H0; auto.
    - eapply IHt; eauto.
      intros; split; intro h.
      all : inversion h; subst.
      1, 3 : apply Here.
      all : apply There; apply H0; auto.
    - econstructor; eauto.      
      eapply IHt; eauto.
      intros; split; intro h.
      all : inversion h; subst.
      1, 3 : apply Here.
      all : apply There; apply H0; auto.
    - apply forallRr with (y := y); auto.
      eapply FreshWithMore.
      2: eauto.
      intros.
      apply InToPath in H2.
      2 : apply BeliefEqDec.
      apply PathToIn; apply H0; auto.
      eapply IHt; eauto.
    - eapply existsLr with (y := y); eauto.
      { eapply FreshWithMore.
        2: eauto.
        intros.
        apply InToPath in H2.
        2 : apply BeliefEqDec.
        apply PathToIn.
        apply H0; auto. }
      eapply IHt; eauto.
      intros; split; intro h.
      all : inversion h; subst.
      1, 3 : apply Here.
      all : apply There; apply H0; auto.
    - eapply ProperContextIff; eauto.
      intro.
      split.
      intro.
      apply InToPath in H5.
      2 : apply BeliefEqDec.
      apply PathToIn; auto.
      intro.
      apply InToPath in H5.
      2 : apply BeliefEqDec.
      apply PathToIn; apply H0; auto.
    - econstructor; eauto.      
      eapply IHt; eauto.
      intros; split; intro h.
      all : inversion h; subst.
      1, 3 : apply Here.
      all : apply There; apply H0; auto.
    - econstructor; eauto.      
      eapply IHt; eauto.
      intros; split; intro h.
      all : inversion h; subst.
      1, 3 : apply Here.
      all : apply There; apply H0; auto.
    - econstructor; eauto.      
      eapply IHt; eauto.
      intros; split; intro h.
      all : inversion h; subst.
      1, 3 : apply Here.
      all : apply There; apply H0; auto.
    - econstructor; eauto.      
      eapply IHt1; eauto.
      intros; split; intro h.
      all : inversion h; subst.
      1, 3 : apply Here.
      all : apply There; apply H0; auto.
    - econstructor; eauto.      
      eapply IHt1; eauto.
      intros; split; intro h.
      all : inversion h; subst.
      1, 3 : apply Here.
      all : apply There; apply H0; auto.
  Qed.
  
  Lemma ExchangeSeq : forall (Gamma Delta : Context) (phi psi : flafolFormula) (m1 m2 : Modality) (b : Belief),
      (Gamma ++ (phi @ m1 :: psi @ m2 :: Delta)) ⊢ b ->
      (Gamma ++ (psi @ m2 :: phi @ m1 :: Delta)) ⊢ b.
  Proof.
    intros Gamma Delta phi psi m1 m2 b H.
    apply ContextIff with (Gamma := Gamma ++ phi @ m1 :: psi @ m2 :: Delta).
    intro b'; split; intro Hin; apply in_app_or in Hin; destruct Hin as [Hin | Hin];
      apply in_or_app; [left | right | left | right]; auto; simpl;
        simpl in Hin; destruct Hin as [Heq | Hin];
          repeat match goal with
                 | [ Hin : ?phi \/ ?psi |- _ ] => destruct Hin
                 | [ Heq : ?b = ?b' |- ?b = ?b' \/ _ ] => left; exact Heq
                 | _ => right
                 end; auto.
    exact H.
  Qed.

  Lemma Rearrange : forall (Gamma Delta : Context) (b : Belief),
      Permutation Gamma Delta -> Gamma ⊢ b -> Delta ⊢ b.
  Proof.
    intros Gamma Delta b H.
    apply ContextIff with (Gamma := Gamma).
    intro b'; split; apply Permutation_in; auto; apply Permutation_sym; auto.
  Qed.

  Lemma Weakening1 : forall (Gamma : Context) (phi : flafolFormula) (m : Modality) (b : Belief),
      ⊢wff phi -> ProperModality m -> Gamma ⊢ b -> (phi @ m :: Gamma) ⊢ b.
  Proof.
    intros Gamma phi m b phi_wf pmod pf.
    eapply Weakening.
    exact pf.
    apply Forall_cons; [constructor; auto; fail | exact (provenProperContext pf)].
    intros b' H; apply There; auto.
  Qed.

  Lemma Contraction : forall (Gamma : Context) (phi : flafolFormula) (m : Modality) (b : Belief),
      (phi @ m :: phi @ m :: Gamma) ⊢ b -> (phi @ m :: Gamma) ⊢ b.
  Proof.
    intros Gamma phi m b pf.
    eapply Weakening.
    exact pf.
    pose proof (provenProperContext pf) as pctxt.
    apply Forall_cons; [apply Forall_inv_car in pctxt
                       | apply Forall_inv_cdr in pctxt; apply Forall_inv_cdr in pctxt];
    exact pctxt.
    intros b' pth. inversion pth. apply Here. exact H1.
  Qed.

  Definition ExFalso : forall (Gamma : Context) (m : Modality) (phi : flafolFormula),
      ProperContext Gamma -> ProperModality m -> ⊢wff phi -> Path (FF @ m) Gamma -> Gamma ⊢ phi @ m.
  Proof.
    intros Gamma m phi pctxt pmod phi_wf pth.
    apply FFL with (m' := []); auto.
    simpl. intros p l H. inversion H.
  Defined.

  Lemma PathToEq: forall phi m' M C, Path (phi @ m') (map (fun m : Modality => C @ m) M) -> phi = C.
  Proof.
    intros phi m' M C H.
    induction M; simpl in *; inversion H; subst; auto.
  Qed.  
  Lemma flowsToTransL' : forall {t Gamma b lab1 lab2 lab3} {M : list Modality}, typing ((map (fun m => lab1 ⊑ lab3 @ m) M) ++ Gamma) t b -> (forall m, Path (lab1 ⊑ lab3 @ m) (map (fun m => lab1 ⊑ lab3 @ m) M) -> (Gamma ⊢ (lab1 ⊑ lab2 @ m)) * (Gamma ⊢ (lab2 ⊑ lab3 @ m))) -> sigT (fun t' => typing Gamma t' b).
  Proof.
    induction t; simpl; intros; inversion H; subst.
    - destruct (SplitPath _ _ H2).
      + destruct b.
        pose proof (PathToEq _ _ _ _ p); subst.
        pose proof (H0 m p).
        apply ProofToTyping.
        apply flowsToTransR with (lab2 := lab2); tauto.
      + eexists; econstructor; eauto.
        eapply ProperContextApp; eauto.
    - eexists.
      eapply TTRr; auto.
      eapply ProperContextApp; eauto.
    - destruct (SplitPath _ _ H4).
      pose proof (PathToEq _ _ _ _ p).
      inversion H6.
      eexists.
      eapply FFLr; auto.
      eapply ProperContextApp; eauto.
    - destruct (SplitPath _ _ pth).
      { apply PathToEq in p; congruence.
      }
      edestruct IHt with (lab1 := lab1) (lab2 := lab2) (lab3 := lab3) (Gamma :=phi @ m :: psi @ m :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      intros.
      split; eapply Weakening.
      1, 4 : eapply H0; eauto.
      2, 4 : solveSubPath.
      1, 2: solvePrope.
      eexists; econstructor; eauto; fail.
    - fttIH.
    - destruct (SplitPath _ _ pth).
      { apply PathToEq in p; congruence. }
      edestruct IHt1 with (lab1 := lab1) (lab2 := lab2) (lab3 := lab3) (Gamma :=phi @ m :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      intros.
      split; eapply Weakening.
      1, 4 : eapply H0; eauto.
      2, 4 : solveSubPath.
      1, 2: solvePrope.
      edestruct IHt2 with (lab1 := lab1) (lab2 := lab2) (lab3 := lab3) (Gamma := psi @ m :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      intros.
      split; eapply Weakening.
      1, 4 : eapply H0; eauto.
      2, 4 : solveSubPath.
      1, 2: solvePrope.
      eexists; econstructor; eauto; fail.
    - fttIH.
    - fttIH.
    - destruct (SplitPath _ _ pth).
      { apply PathToEq in p; congruence. }
      edestruct IHt2 with (lab1 := lab1) (lab2 := lab2) (lab3 := lab3) (Gamma :=psi @ m :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      intros.
      split; eapply Weakening.
      1, 4 : eapply H0; eauto.
      2, 4 : solveSubPath.
      1, 2: solvePrope.
      edestruct IHt1 with (lab1 := lab1) (lab2 := lab2) (lab3 := lab3); eauto.
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (lab1 := lab1) (lab2 := lab2) (lab3 := lab3) (Gamma := phi @ ⟨ l ⟩ :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      intros.
      split; eapply Weakening.
      1, 4 : eapply H0; eauto.
      2, 4 : solveSubPath.
      1, 2: solvePrope.
      eexists; econstructor; eauto; fail.
    - destruct (SplitPath _ _ pth).
      { apply PathToEq in p; congruence.
      }
      edestruct IHt with (lab1 := lab1) (lab2 := lab2) (lab3 := lab3) (Gamma :=open_formula phi t0 @ m :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      intros.
      split; eapply Weakening.
      1, 4 : eapply H0; eauto.
      2, 4 : solveSubPath.
      1, 2: solvePrope.
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (1 := H7); eauto.      
      eexists.
      eapply forallRr with (y := y); eauto.
      intro.
      apply H3.
      {
        clear dependent t.
        clear lab2 t0 H0 H3 H4 H5 phi m x.
        induction M; simpl; auto.
        econstructor; eauto; fail.
      }
    - destruct (SplitPath _ _ pth).
      { apply PathToEq in p; congruence.
      }
      edestruct IHt with (lab1 := lab1) (lab2 := lab2) (lab3 := lab3) (Gamma :=open_formula phi (varTerm y) @ m :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      intros.
      split; eapply Weakening.
      1, 4 : eapply H0; eauto.
      2, 4 : solveSubPath.
      1, 2: solvePrope.
      pose (freshInSequent (open_formula phi (varTerm y) @ m :: Gamma) b (VarSort y)) as y'.
      destruct (open_with_fresherLT' _ _ _ _ y y'  x t0); auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      eapply fvcApp; eauto.
      eexists.
      eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
      unfold y'.
      destruct (freshInSequentIsFresh (open_formula phi (varTerm y) @ m :: Gamma) b (VarSort y)) as [fv1 fv2].
      intro; apply fv1; econstructor; eauto; fail.      
    - fttIH.
    - eexists.
      eapply flowsToReflr; auto.
      eapply ProperContextApp; eauto.
    - fttIH.
    - fttIH.
    - destruct (SplitPath _ _ pth).
      { apply PathToEq in p0; congruence.
      }
      edestruct IHt with (lab1 := lab1) (lab2 := lab2) (lab3 := lab3) (Gamma := phi @ m ⋅ p ⟨ lab ⟩ :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      intros.
      split; eapply Weakening.
      1, 4 : eapply H0; eauto.
      2, 4 : solveSubPath.
      1, 2 : solvePrope.
      eexists; econstructor; eauto; fail.
    - fttIH.
    - fttIH.
    - destruct (SplitPath _ _ pth').
      + pose proof (PathToEq _ _ _ _ p).
        subst.
        eapply IHt with (M := m :: M) (lab2 := lab2).
        simpl.
        eauto.
        intros m0 H1.
        inversion H1; subst; eauto.
        split; eapply modalityExpandR with (pth := pth); eauto.
        1, 2 : apply H0; eauto.
      + edestruct IHt with (lab1 := lab1) (lab2 := lab2) (lab3 := lab3) (Gamma := (phi @ m :: Gamma)).
        eapply Exchange; eauto.
        solveSubPath.
        intros.
        split; eapply Weakening.
        1, 4 : eapply H0; eauto.
        2, 4 : solveSubPath.
        1, 2: solvePrope.
        eexists; econstructor; eauto; fail.
    - destruct (SplitPath _ _ pth').
      + pose proof (PathToEq _ _ _ _ p).
        subst.
        eapply IHt with (M := (CollapseDoubleInModality pth) :: M) (lab2 := lab2).
        simpl.
        eauto.
        intros m0 H1.
        inversion H1; subst; eauto.
        split; eapply modalityCollapseR with (pth := pth); eauto.
        1, 2 : apply H0; eauto.
      + edestruct IHt with (lab1 := lab1) (lab2 := lab2) (lab3 := lab3) (Gamma := (phi @ (CollapseDoubleInModality pth) :: Gamma)).
        eapply Exchange; eauto.
        solveSubPath.
        intros.
        split; eapply Weakening.
        1, 4 : eapply H0; eauto.
        2, 4 : solveSubPath.
        1, 2 : solvePrope.
        eexists; econstructor; eauto; fail.
    - fttIH.
    - destruct (SplitPath _ _ pth).
      + pose proof (PathToEq _ _ _ _ p).
        subst.
        eapply IHt1 with (M := (ReplaceLabelInModality m lab0 lab4 pi) :: M) (lab2 := lab2).
        simpl.
        eauto.
        intros m0 H1.
        inversion H1; subst; eauto.
        edestruct (IHt2) with (1 := H6); eauto.
        split; eapply RVariance.
        2, 4 : eapply TypingToProof; eauto.
        1, 2 : apply H0; auto.
      + edestruct (IHt2) with (1 := H6); eauto.
        edestruct (IHt1) with (lab1 := lab1) (lab2 := lab2) (lab3 := lab3) (Gamma := (phi @ ReplaceLabelInModality m lab0 lab4 pi :: Gamma)).
        eapply Exchange; eauto.
        solveSubPath.
        intros.
        split; eapply Weakening.
        1, 4 : eapply H0; eauto.
        2, 4 : solveSubPath.
        1, 2 : solvePrope.
        eexists.
        eapply LVariancer; eauto.
    - fttIH.
    - destruct (SplitPath _ _ pth').
      + pose proof (PathToEq _ _ _ _ p0).
        subst.
        eapply IHt1 with (M := (ReplacePrinInModality pth p) :: M) (lab2 := lab2).
        simpl.
        eauto.
        intros m0 H1.
        inversion H1; subst; eauto.
        edestruct (IHt2) with (1 := H7); eauto.
        edestruct (IHt3) with (1 := H8); eauto.
        split; eapply FwdR.
        2, 3, 5, 6 : eapply TypingToProof; eauto.
        1, 2 : apply H0; auto.
      + edestruct (IHt2) with (1 := H7); eauto.
        edestruct (IHt3) with (1 := H8); eauto.
        edestruct (IHt1) with (lab1 := lab1) (lab2 := lab2) (lab3 := lab3) (Gamma := (phi @ ReplacePrinInModality pth p :: Gamma)).
        eapply Exchange; eauto.
        solveSubPath.
        intros.
        split; eapply Weakening.
        1, 4 : eapply H0; eauto.
        2, 4 : solveSubPath.
        1, 2 : solvePrope.
        eexists.
        eapply FwdLr; eauto.
    - fttIH.
    - fttIH.
  Qed.
  
  Lemma flowsToTransLr : forall {t Gamma b lab1 lab2 lab3} {m : Modality}, typing ((lab1 ⊑ lab3 @ m) :: Gamma) t b -> Path (lab1 ⊑ lab2 @ m) Gamma -> Path (lab2 ⊑ lab3 @ m) Gamma -> sigT (fun t' => typing Gamma t' b).
  Proof.
    intros.
    eapply @flowsToTransL' with (M := [m]).
    simpl.
    eauto.
    intros m0 H2.
    inversion H2; subst; try congruence.
    2 : inversion H5.
    split; eapply axiom; eauto.
    1, 2 : apply provenProperContextTyping in H; inversion H; subst; auto.
  Qed.
  
  Lemma CRVarianceL' : forall {t Gamma b p lab1 lab2} {M : list Modality}, typing ((map (fun m => canRead p lab1 @ m) M) ++ Gamma) t b -> (forall m, Path (canRead p lab1 @ m) (map (fun m => canRead p lab1 @ m) M) -> (Gamma ⊢ canRead p lab2 @ m)) -> (forall m, Path (canRead p lab1 @ m) (map (fun m => canRead p lab1 @ m) M) -> Gamma ⊢ (lab1 ⊑ lab2 @ m)) -> sigT (fun t' => typing Gamma t' b).
  Proof.
    induction t; simpl; intros; inversion H; subst.
    - destruct (SplitPath _ _ H3).
      + destruct b.
        pose proof (PathToEq _ _ _ _ p0); subst.
        pose proof (H0 m p0).
        apply ProofToTyping.
        eapply CRVariance; eauto.        
      + eexists; econstructor; eauto.
        eapply ProperContextApp; eauto.
    - eexists.
      eapply TTRr; auto.
      eapply ProperContextApp; eauto.
    - destruct (SplitPath _ _ H5).
      pose proof (PathToEq _ _ _ _ p0).
      inversion H7.
      eexists.
      eapply FFLr; auto.
      eapply ProperContextApp; eauto.
    - destruct (SplitPath _ _ pth).
      { apply PathToEq in p0; congruence.
      }
      edestruct IHt with (lab1 := lab1) (lab2 := lab2) (Gamma := phi @ m :: psi @ m :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      1, 2 : intros.
      1, 2 : eapply Weakening.
      1, 4 : eauto.
      2, 4 : solveSubPath.
      1, 2 : solvePrope.
      eexists; econstructor; eauto; fail.
    - fttIH.
    - destruct (SplitPath _ _ pth).
      { apply PathToEq in p0; congruence.
      }
      edestruct IHt1 with (lab1 := lab1) (lab2 := lab2) (Gamma :=phi @ m :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      1, 2 : intros.
      1, 2 : eapply Weakening.
      1, 4 : eauto.
      2, 4 : solveSubPath.
      1, 2 : solvePrope.
      edestruct IHt2 with (lab1 := lab1) (lab2 := lab2) (Gamma := psi @ m :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      1, 2 : intros.
      1, 2 : eapply Weakening.
      1, 4 : eauto.
      2, 4 : solveSubPath.
      1, 2 : solvePrope.
      eexists; econstructor; eauto; fail.
    - fttIH.
    - fttIH.
    - destruct (SplitPath _ _ pth).
      { apply PathToEq in p0; congruence.
      }
      edestruct IHt2 with (lab1 := lab1) (lab2 := lab2) (Gamma :=psi @ m :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      1, 2 : intros.
      1, 2 : eapply Weakening.
      1, 4 : eauto.
      2, 4 : solveSubPath.
      1, 2 : solvePrope.
      edestruct IHt1 with (lab1 := lab1) (lab2 := lab2); eauto.
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (lab1 := lab1) (lab2 := lab2) (Gamma := phi @ ⟨ l ⟩ :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      intros.
      1, 2 : intros.
      1, 2 : eapply Weakening.
      1, 4 : eauto.
      2, 4 : solveSubPath.
      1, 2 : solvePrope.
      eexists; econstructor; eauto; fail.
    - destruct (SplitPath _ _ pth).
      { apply PathToEq in p0; congruence.
      }
      edestruct IHt with (lab1 := lab1) (lab2 := lab2) (Gamma :=open_formula phi t0 @ m :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      1, 2 : intros.
      1, 2 : eapply Weakening.
      1, 4 : eauto.
      2, 4 : solveSubPath.
      1, 2 : solvePrope.
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (1 := H8); eauto.      
      eexists.
      eapply forallRr with (y := y); eauto.
      intro.
      apply H4.
      {
        clear dependent t.
        clear lab2 t0 H0 H1 H4 H5 H6 phi m x.
        induction M; simpl; auto.
        econstructor; eauto; fail.
      }
    - destruct (SplitPath _ _ pth).
      { apply PathToEq in p0; congruence.
      }
      edestruct IHt with (lab1 := lab1) (lab2 := lab2) (Gamma :=open_formula phi (varTerm y) @ m :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      1, 2 : intros.
      1, 2 : eapply Weakening.
      1, 4 : eauto.
      2, 4 : solveSubPath.
      1, 2 : solvePrope.
      pose (freshInSequent (open_formula phi (varTerm y) @ m :: Gamma) b (VarSort y)) as y'.
      destruct (open_with_fresherLT' _ _ _ _ y y'  x t0); auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      eapply fvcApp; eauto.
      eexists.
      eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
      unfold y'.
      destruct (freshInSequentIsFresh (open_formula phi (varTerm y) @ m :: Gamma) b (VarSort y)) as [fv1 fv2].
      intro; apply fv1; econstructor; eauto; fail.      
    - fttIH.
    - eexists.
      eapply flowsToReflr; auto.
      eapply ProperContextApp; eauto.
    - fttIH.
    - fttIH.
    - destruct (SplitPath _ _ pth).
      { apply PathToEq in p1; congruence.
      }
      edestruct IHt with (lab1 := lab1) (lab2 := lab2) (Gamma := phi @ m ⋅ p0 ⟨ lab ⟩ :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      1, 2 : intros.
      1, 2 : eapply Weakening.
      1, 4 : eauto.
      2, 4 : solveSubPath.
      1, 2 : solvePrope.
      eexists; econstructor; eauto; fail.
    - fttIH.
    - fttIH.
    - destruct (SplitPath _ _ pth').
      + pose proof (PathToEq _ _ _ _ p0).
        subst.
        eapply IHt with (M := m :: M) (lab2 := lab2).
        simpl.
        eauto.
        all : intros m0 h1.
        all : inversion h1; subst; eauto.
        all : eapply modalityExpandR.
        all : eauto.
      + edestruct IHt with (lab1 := lab1) (lab2 := lab2) (Gamma := (phi @ m :: Gamma)).
        eapply Exchange; eauto.
        solveSubPath.
        1, 2 : intros.
        1, 2 : eapply Weakening.
        1, 4 : eauto.
        2, 4 : solveSubPath.
        1, 2 : solvePrope.
        eexists.
        eapply modalityExpandLr with (pth := pth); eauto.
    - destruct (SplitPath _ _ pth').
      + pose proof (PathToEq _ _ _ _ p0).
        subst.
        eapply IHt with (M := (CollapseDoubleInModality pth) :: M) (lab2 := lab2).
        simpl.
        eauto.
        all : intros m0 h1.
        all : inversion h1; subst; eauto.
        all : eapply modalityCollapseR.
        all : eauto.
      + edestruct IHt with (lab1 := lab1) (lab2 := lab2) (Gamma := (phi @ (CollapseDoubleInModality pth) :: Gamma)).
        eapply Exchange; eauto.
        solveSubPath.
        1, 2 : intros.
        1, 2 : eapply Weakening.
        1, 4 : eauto.
        2, 4 : solveSubPath.
        1, 2 : solvePrope.
        eexists.
        eapply modalityCollapseLr with (pth := pth); eauto.
    - fttIH.
    - destruct (SplitPath _ _ pth).
      + pose proof (PathToEq _ _ _ _ p0).
        subst.
        edestruct (IHt2) with (1 := H7); eauto.
        eapply IHt1 with (M := (ReplaceLabelInModality m lab0 lab3 pi) :: M) (lab2 := lab2).
        simpl.
        eauto.
        all : intros m0 h1.
        all : inversion h1; subst; eauto.
        all : eapply RVariance.
        2, 4 : eapply TypingToProof; eauto.
        all : eauto.
      + edestruct (IHt2) with (1 := H7); eauto.
        edestruct (IHt1) with (lab1 := lab1) (lab2 := lab2) (Gamma := (phi @ ReplaceLabelInModality m lab0 lab3 pi :: Gamma)).
        eapply Exchange; eauto.
        solveSubPath.
        1, 2 : intros.
        1, 2 : eapply Weakening.
        1, 4 : eauto.
        2, 4 : solveSubPath.
        1, 2 : solvePrope.
        eexists.
        eapply LVariancer; eauto.
    - fttIH.
    - destruct (SplitPath _ _ pth').
      + pose proof (PathToEq _ _ _ _ p1).
        subst.
        edestruct (IHt2) with (1 := H8); eauto.
        edestruct (IHt3) with (1 := H9); eauto.
        eapply IHt1 with (M := (ReplacePrinInModality pth p0) :: M) (lab2 := lab2).
        simpl.
        eauto.
        all : intros m0 h1.
        all : inversion h1; subst; eauto.
        all : eapply FwdR; auto.
        all : eapply TypingToProof; eauto.
      + edestruct (IHt2) with (1 := H8); eauto.
        edestruct (IHt3) with (1 := H9); eauto.
        edestruct (IHt1) with (lab1 := lab1) (lab2 := lab2) (Gamma := (phi @ ReplacePrinInModality pth p0 :: Gamma)).
        eapply Exchange; eauto.
        solveSubPath.
        1, 2 : intros.
        1, 2 : eapply Weakening.
        1, 4 : eauto.
        2, 4 : solveSubPath.
        1, 2 : solvePrope.
        eexists.
        eapply FwdLr; eauto.
    - fttIH.
    - fttIH.
  Qed.

  Lemma CRVarianceLr : forall {t Gamma b p lab1 lab2} {m : Modality}, typing ((canRead p lab1 @ m) :: Gamma) t b -> Path (canRead p lab2 @ m) Gamma -> Gamma ⊢ (lab1 ⊑ lab2 @ m) -> sigT (fun t' => typing Gamma t' b).
  Proof.
    intros.
    eapply @CRVarianceL' with (M := [m]); eauto.
    simpl.
    eauto.
    all : intros m0 H2.
    all : inversion H2; subst.
    2, 4 : inversion H5.
    eapply axiom; eauto.
    auto.
  Qed.

  
    Lemma CWVarianceL' : forall {t Gamma b p lab1 lab2} {M : list Modality}, typing ((map (fun m => canWrite p lab1 @ m) M) ++ Gamma) t b -> (forall m, Path (canWrite p lab1 @ m) (map (fun m => canWrite p lab1 @ m) M) -> (Gamma ⊢ canWrite p lab2 @ m)) -> (forall m, Path (canWrite p lab1 @ m) (map (fun m => canWrite p lab1 @ m) M) -> Gamma ⊢ (lab2 ⊑ lab1 @ m)) -> sigT (fun t' => typing Gamma t' b).
  Proof.
    induction t; simpl; intros; inversion H; subst.
    - destruct (SplitPath _ _ H3).
      + destruct b.
        pose proof (PathToEq _ _ _ _ p0); subst.
        pose proof (H0 m p0).
        apply ProofToTyping.
        eapply CWVariance; eauto.        
      + eexists; econstructor; eauto.
        eapply ProperContextApp; eauto.
    - eexists.
      eapply TTRr; auto.
      eapply ProperContextApp; eauto.
    - destruct (SplitPath _ _ H5).
      pose proof (PathToEq _ _ _ _ p0).
      inversion H7.
      eexists.
      eapply FFLr; auto.
      eapply ProperContextApp; eauto.
    - destruct (SplitPath _ _ pth).
      { apply PathToEq in p0; congruence.
      }
      edestruct IHt with (lab1 := lab1) (lab2 := lab2) (Gamma := phi @ m :: psi @ m :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      1, 2 : intros.
      1, 2 : eapply Weakening.
      1, 4 : eauto.
      2, 4 : solveSubPath.
      1, 2 : solvePrope.
      eexists; econstructor; eauto; fail.
    - fttIH.
    - destruct (SplitPath _ _ pth).
      { apply PathToEq in p0; congruence.
      }
      edestruct IHt1 with (lab1 := lab1) (lab2 := lab2) (Gamma :=phi @ m :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      1, 2 : intros.
      1, 2 : eapply Weakening.
      1, 4 : eauto.
      2, 4 : solveSubPath.
      1, 2 : solvePrope.
      edestruct IHt2 with (lab1 := lab1) (lab2 := lab2) (Gamma := psi @ m :: Gamma) (M := M) (p := p).
      eapply Exchange; eauto.
      solveSubPath.
      1, 2 : intros.
      1, 2 : eapply Weakening.
      1, 4 : eauto.
      2, 4 : solveSubPath.
      1, 2 : solvePrope.
      eexists; econstructor; eauto; fail.
    - fttIH.
    - fttIH.
    - destruct (SplitPath _ _ pth).
      { apply PathToEq in p0; congruence.
      }
      edestruct IHt2 with (lab1 := lab1) (lab2 := lab2) (Gamma :=psi @ m :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      1, 2 : intros.
      1, 2 : eapply Weakening.
      1, 4 : eauto.
      2, 4 : solveSubPath.
      1, 2 : solvePrope.
      edestruct IHt1 with (lab1 := lab1) (lab2 := lab2); eauto.
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (lab1 := lab1) (lab2 := lab2) (Gamma := phi @ ⟨ l ⟩ :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      intros.
      1, 2 : intros.
      1, 2 : eapply Weakening.
      1, 4 : eauto.
      2, 4 : solveSubPath.
      1, 2 : solvePrope.
      eexists; econstructor; eauto; fail.
    - destruct (SplitPath _ _ pth).
      { apply PathToEq in p0; congruence.
      }
      edestruct IHt with (lab1 := lab1) (lab2 := lab2) (Gamma :=open_formula phi t0 @ m :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      1, 2 : intros.
      1, 2 : eapply Weakening.
      1, 4 : eauto.
      2, 4 : solveSubPath.
      1, 2 : solvePrope.
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (1 := H8); eauto.      
      eexists.
      eapply forallRr with (y := y); eauto.
      intro.
      apply H4.
      {
        clear dependent t.
        clear lab2 t0 H0 H1 H4 H5 H6 phi m x.
        induction M; simpl; auto.
        econstructor; eauto; fail.
      }
    - destruct (SplitPath _ _ pth).
      { apply PathToEq in p0; congruence.
      }
      edestruct IHt with (lab1 := lab1) (lab2 := lab2) (Gamma :=open_formula phi (varTerm y) @ m :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      1, 2 : intros.
      1, 2 : eapply Weakening.
      1, 4 : eauto.
      2, 4 : solveSubPath.
      1, 2 : solvePrope.
      pose (freshInSequent (open_formula phi (varTerm y) @ m :: Gamma) b (VarSort y)) as y'.
      destruct (open_with_fresherLT' _ _ _ _ y y'  x t0); auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      eapply fvcApp; eauto.
      eexists.
      eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
      unfold y'.
      destruct (freshInSequentIsFresh (open_formula phi (varTerm y) @ m :: Gamma) b (VarSort y)) as [fv1 fv2].
      intro; apply fv1; econstructor; eauto; fail.      
    - fttIH.
    - eexists.
      eapply flowsToReflr; auto.
      eapply ProperContextApp; eauto.
    - fttIH.
    - fttIH.
    - destruct (SplitPath _ _ pth).
      { apply PathToEq in p1; congruence.
      }
      edestruct IHt with (lab1 := lab1) (lab2 := lab2) (Gamma := phi @ m ⋅ p0 ⟨ lab ⟩ :: Gamma).
      eapply Exchange; eauto.
      solveSubPath.
      1, 2 : intros.
      1, 2 : eapply Weakening.
      1, 4 : eauto.
      2, 4 : solveSubPath.
      1, 2 : solvePrope.
      eexists; econstructor; eauto; fail.
    - fttIH.
    - fttIH.
    - destruct (SplitPath _ _ pth').
      + pose proof (PathToEq _ _ _ _ p0).
        subst.
        eapply IHt with (M := m :: M) (lab2 := lab2).
        simpl.
        eauto.
        all : intros m0 h1.
        all : inversion h1; subst; eauto.
        all : eapply modalityExpandR.
        all : eauto.
      + edestruct IHt with (lab1 := lab1) (lab2 := lab2) (Gamma := (phi @ m :: Gamma)).
        eapply Exchange; eauto.
        solveSubPath.
        1, 2 : intros.
        1, 2 : eapply Weakening.
        1, 4 : eauto.
        2, 4 : solveSubPath.
        1, 2 : solvePrope.
        eexists.
        eapply modalityExpandLr with (pth := pth); eauto.
    - destruct (SplitPath _ _ pth').
      + pose proof (PathToEq _ _ _ _ p0).
        subst.
        eapply IHt with (M := (CollapseDoubleInModality pth) :: M) (lab2 := lab2).
        simpl.
        eauto.
        all : intros m0 h1.
        all : inversion h1; subst; eauto.
        all : eapply modalityCollapseR.
        all : eauto.
      + edestruct IHt with (lab1 := lab1) (lab2 := lab2) (Gamma := (phi @ (CollapseDoubleInModality pth) :: Gamma)).
        eapply Exchange; eauto.
        solveSubPath.
        1, 2 : intros.
        1, 2 : eapply Weakening.
        1, 4 : eauto.
        2, 4 : solveSubPath.
        1, 2 : solvePrope.
        eexists.
        eapply modalityCollapseLr with (pth := pth); eauto.
    - fttIH.
    - destruct (SplitPath _ _ pth).
      + pose proof (PathToEq _ _ _ _ p0).
        subst.
        edestruct (IHt2) with (1 := H7); eauto.
        eapply IHt1 with (M := (ReplaceLabelInModality m lab0 lab3 pi) :: M) (lab2 := lab2).
        simpl.
        eauto.
        all : intros m0 h1.
        all : inversion h1; subst; eauto.
        all : eapply RVariance.
        2, 4 : eapply TypingToProof; eauto.
        all : eauto.
      + edestruct (IHt2) with (1 := H7); eauto.
        edestruct (IHt1) with (lab1 := lab1) (lab2 := lab2) (Gamma := (phi @ ReplaceLabelInModality m lab0 lab3 pi :: Gamma)).
        eapply Exchange; eauto.
        solveSubPath.
        1, 2 : intros.
        1, 2 : eapply Weakening.
        1, 4 : eauto.
        2, 4 : solveSubPath.
        1, 2 : solvePrope.
        eexists.
        eapply LVariancer; eauto.
    - fttIH.
    - destruct (SplitPath _ _ pth').
      + pose proof (PathToEq _ _ _ _ p1).
        subst.
        edestruct (IHt2) with (1 := H8); eauto.
        edestruct (IHt3) with (1 := H9); eauto.
        eapply IHt1 with (M := (ReplacePrinInModality pth p0) :: M) (lab2 := lab2).
        simpl.
        eauto.
        all : intros m0 h1.
        all : inversion h1; subst; eauto.
        all : eapply FwdR; auto.
        all : eapply TypingToProof; eauto.
      + edestruct (IHt2) with (1 := H8); eauto.
        edestruct (IHt3) with (1 := H9); eauto.
        edestruct (IHt1) with (lab1 := lab1) (lab2 := lab2) (Gamma := (phi @ ReplacePrinInModality pth p0 :: Gamma)).
        eapply Exchange; eauto.
        solveSubPath.
        1, 2 : intros.
        1, 2 : eapply Weakening.
        1, 4 : eauto.
        2, 4 : solveSubPath.
        1, 2 : solvePrope.
        eexists.
        eapply FwdLr; eauto.
    - fttIH.
    - fttIH.
  Qed.
  
  Lemma CWVarianceLr : forall {t Gamma b p lab1 lab2} {m : Modality}, typing ((canWrite p lab1 @ m) :: Gamma) t b -> Path (canWrite p lab2 @ m) Gamma -> Gamma ⊢ (lab2 ⊑ lab1 @ m) -> sigT (fun t' => typing Gamma t' b).
  Proof.
    intros.
    eapply @CWVarianceL' with (M := [m]); eauto.
    simpl.
    eauto.
    all : intros m0 H2.
    all : inversion H2; subst.
    2, 4 : inversion H5.
    eapply axiom; eauto.
    auto.
  Qed.
    
End Sequent.    
