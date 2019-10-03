Require Export Sequent.
Require Export SignedSubformula.

Require Import Base.Lists.
Require Import Base.Arith.
Require Import Base.Permutation.
Require Import Tactics.FormulaEquality.
Require Import Tactics.TermEquality.
Require Import Tactics.WellFormedFormulaNoProofs.
Require Import Tactics.TermHasSortNoFormulas.
Require Import Program.Wf.
Require Import Coq.Arith.Wf_nat.

Set Bullet Behavior "Strict Subproofs".


Module Type CompatibleSupercontext (G : GroundInfo) (GTerm : Term G) (GFormula : Formula G GTerm)
       (TE : TermEquality G GTerm) (FE : FormulaEquality G GTerm GFormula TE)
       (SS : SignedSubformula G GTerm GFormula TE FE)
       (THS : TermHasSort'' G GTerm TE)
       (WFF : WellFormedFormula' G GTerm TE THS GFormula FE)
       (S : Sequent G GTerm GFormula TE FE THS WFF).
  Import G. Import GTerm. Import GFormula. Import ListNotations.
  Import THS. Import WFF. Import S. Import SS.

  Open Scope term_scope. Open Scope formula_scope. Open Scope list_scope. Open Scope proof_scope.


  Reserved Notation "Delta ≪ Gamma ⊢csc b" (at level 50).


  Inductive CompatibleSupercontext : Context -> Context -> Belief -> Prop :=
  | CSCRefl : forall Gamma b, Gamma ≪ Gamma ⊢csc b
  | CSCUnion : forall Delta E Gamma b,
      Delta ≪ Gamma ⊢csc b -> E ≪ Gamma ⊢csc b ->
      (Delta ++ E) ≪ Gamma ⊢csc b
  | CSCPermutation : forall Delta1 Delta2 Gamma1 Gamma2 b,
      Permutation Delta1 Delta2 -> Permutation Gamma1 Gamma2 ->
      Delta1 ≪ Gamma1 ⊢csc b -> Delta2 ≪ Gamma2 ⊢csc b
  (* The following two constructors are provable from the rest, up to some technicalities.
     Technically, we need to have a different -- but equivalent -- presentation of CSC for the second, and the first is only provable up to alpha-equivalence.
     Here we axiomatize them, so that we don't have to build up the framework of alpha-equivalence.
   *)
  | CSCAtomic : forall Delta Gamma phi m b,
      AtomicFormula phi -> ⊢wff phi -> ProperModality m ->
      Delta ≪ Gamma ⊢csc (phi @ m) ->
      Delta ≪ Gamma ⊢csc b
  | CSCWeakening : forall Delta Gamma b1 b2,
      Delta ≪ Gamma ⊢csc b1 ->
      (b2 :: Delta) ≪ (b2 :: Gamma) ⊢csc b1
  | CSCAndL : forall Delta Gamma b phi psi m,
      Path (phi & psi @ m) Gamma ->
      Delta ≪ (phi @ m :: psi @ m :: Gamma) ⊢csc b ->
      Delta ≪ Gamma ⊢csc b
  | CSCAndR1 : forall Delta Gamma phi psi m,
      Delta ≪ Gamma ⊢csc phi @ m ->
      Delta ≪ Gamma ⊢csc phi & psi @ m
  | CSCAndR2 : forall Delta Gamma phi psi m,
      Delta ≪ Gamma ⊢csc psi @ m ->
      Delta ≪ Gamma ⊢csc phi & psi @ m
  | CSCOrL1 : forall Delta Gamma b phi psi m,
      Path (phi ⊕ psi @ m) Gamma ->
      Delta ≪ (phi @ m :: Gamma) ⊢csc b ->
      Delta ≪ Gamma ⊢csc b
  | CSCOrL2 : forall Delta Gamma b phi psi m,
      Path (phi ⊕ psi @ m) Gamma ->
      Delta ≪ (psi @ m :: Gamma) ⊢csc b ->
      Delta ≪ Gamma ⊢csc b
  | CSCOrR1 : forall Delta Gamma phi psi m,
      Delta ≪ Gamma ⊢csc phi @ m ->
      Delta ≪ Gamma ⊢csc phi ⊕ psi @ m
  | CSCOrR2 : forall Delta Gamma phi psi m,
      Delta ≪ Gamma ⊢csc psi @ m ->
      Delta ≪ Gamma ⊢csc phi ⊕ psi @ m
  | CSCImpL1 : forall Delta Gamma b phi l psi m,
      Path (phi ==⟨ l ⟩> psi @ m) Gamma ->
      Delta ≪ (psi @ m :: Gamma) ⊢csc b ->
      Delta ≪ Gamma ⊢csc b
  | CSCImpL2 : forall Delta Gamma b phi l psi m,
      Path (phi ==⟨ l ⟩> psi @ m) Gamma ->
      Delta ≪ Gamma ⊢csc phi @ ⟨l⟩ ->
      Delta ≪ Gamma ⊢csc b
  | CSCImpR : forall Delta Gamma phi l psi m,
      Delta ≪ (phi @ ⟨ l ⟩ :: Gamma) ⊢csc (psi @ m) ->
      Delta ≪ Gamma ⊢csc (phi ==⟨l⟩> psi @ m)
  | CSCForallL : forall Delta Gamma sigma phi t m b,
      Path (∀ sigma; phi @ m) Gamma ->
      lc_term t -> ⊢s t ::: sigma ->
      Delta ≪ (open_formula phi t @ m :: Gamma) ⊢csc b ->
      Delta ≪ Gamma ⊢csc b
  | CSCForallR : forall Delta Gamma sigma y phi m,
      VarSort y = sigma -> y ∉FVC Gamma -> y ∉FVF phi -> y ∉FVM m ->
      Delta ≪ Gamma ⊢csc (open_formula phi (varTerm y)) @ m ->
      Delta ≪ Gamma ⊢csc ∀ sigma; phi @ m
  | CSCExistsL : forall Delta Gamma sigma phi y m b,
      Path (∃ sigma; phi @ m) Gamma ->
      VarSort y = sigma -> y ∉FVC Gamma -> y ∉FVB b ->
      Delta ≪ (open_formula phi (varTerm y) @ m :: Gamma) ⊢csc b ->
      Delta ≪ Gamma ⊢csc b
  | CSCExistsR : forall Delta Gamma sigma t phi m,
      lc_term t -> ⊢s t ::: sigma ->
      Delta ≪ Gamma ⊢csc open_formula phi t @ m ->
      Delta ≪ Gamma ⊢csc ∃ sigma; phi @ m
  | CSCsaysL : forall Delta Gamma p l phi m b,
      Path (p □ ⟨l⟩ phi @ m) Gamma ->
      Delta ≪ (phi @ m ⋅ p⟨l⟩ :: Gamma) ⊢csc b ->
      Delta ≪ Gamma ⊢csc b
  | CSCsaysR : forall Delta Gamma p l phi m,
      Delta ≪ Gamma ⊢csc phi @ m ⋅ p⟨l⟩ ->
      Delta ≪ Gamma ⊢csc p □ ⟨l⟩ phi @ m
  | CSCMER : forall Delta Gamma phi m (pth : PathToDoubleInModality m),
      Delta ≪ Gamma ⊢csc phi @ (CollapseDoubleInModality pth) ->
      Delta ≪ Gamma ⊢csc phi @ m
  | CSCMEL : forall Delta Gamma phi m (pth : PathToDoubleInModality m) b,
      Path (phi @ (CollapseDoubleInModality pth)) Gamma ->
      Delta ≪ (phi @ m :: Gamma) ⊢csc b ->
      Delta ≪ Gamma ⊢csc b
  | CSCMCR : forall Delta Gamma phi m (pth : PathToDoubleInModality m),
      Delta ≪ Gamma ⊢csc phi @ m ->
      Delta ≪ Gamma ⊢csc phi @ (CollapseDoubleInModality pth)
  | CSCMCL : forall Delta Gamma phi m (pth : PathToDoubleInModality m) b,
      Path (phi @ m) Gamma ->
      Delta ≪ (phi @ (CollapseDoubleInModality pth) :: Gamma) ⊢csc b ->
      Delta ≪ Gamma ⊢csc b
  | CSCRVariance : forall Delta Gamma l1 l2 phi m (pth : PathToLabelInModality m l1),
      Gamma ⊢ l1 ⊑ l2 @ (VarModality pth l2) ->
      Delta ≪ Gamma ⊢csc phi @ m ->
      Delta ≪ Gamma ⊢csc phi @ (ReplaceLabelInModality m l1 l2 pth)
  | CSCLVariance : forall Delta Gamma l1 l2 phi m (pth : PathToLabelInModality m l1) b,
      Path (phi @ m) Gamma ->
      Gamma ⊢ l1 ⊑ l2 @ (VarModality pth l2) ->
      Delta ≪ (phi @ ReplaceLabelInModality m l1 l2 pth :: Gamma) ⊢csc b ->
      Delta ≪ Gamma ⊢csc b
  | CSCFwdR : forall Delta Gamma phi m p q (pth : PathToPrinInModality m p),
      Gamma ⊢ (canRead q (LabelAtPrin pth)) @ (FwdModality pth p) ->
      Gamma ⊢ (canWrite p (LabelAtPrin pth)) @ (FwdModality pth q) ->
      Delta ≪ Gamma ⊢csc phi @ m ->
      Delta ≪ Gamma ⊢csc phi @ (ReplacePrinInModality pth q)
  | CSCFwdL : forall Delta Gamma phi m p q
                (pth : PathToPrinInModality m q) b,
      Path (phi @ m) Gamma ->
      Gamma ⊢ (canWrite q (LabelAtPrin pth)) @ (FwdModality pth p) ->
      Gamma ⊢ (canRead p (LabelAtPrin pth)) @ (FwdModality pth q) ->
      Delta ≪ (phi @ ReplacePrinInModality pth p :: Gamma) ⊢csc b ->
      Delta ≪ Gamma ⊢csc b
  where "Delta ≪ Gamma ⊢csc b" := (CompatibleSupercontext Delta Gamma b).
                           
  Definition CSCPermL :
    forall Delta1 Delta2 Gamma b,
      Delta1 ≪ Gamma ⊢csc b -> Permutation Delta1 Delta2 -> Delta2 ≪ Gamma ⊢csc b :=
    fun Delta1 Delta2 Gamma b Δcsc perm =>
      CSCPermutation Delta1 Delta2 Gamma Gamma b perm (Permutation_refl Gamma) Δcsc.
  Definition CSCPermR :
    forall Delta Gamma1 Gamma2 b,
      Delta ≪ Gamma1 ⊢csc b -> Permutation Gamma1 Gamma2 -> Delta ≪ Gamma2 ⊢csc b :=
    fun Delta Gamma1 Gamma2 b Δcsc perm =>
      CSCPermutation Delta Delta Gamma1 Gamma2 b (Permutation_refl Delta) perm Δcsc.
                               
  Open Scope bool_scope.

  Definition ContextEqBool : Context -> Context -> bool :=
    fun Gamma Delta => if ContextEqDec Gamma Delta then true else false.

  Infix "=ctxt=" := ContextEqBool (at level 20).

  Lemma ContextEqBoolRefl : forall Gamma, Gamma =ctxt= Gamma = true.
  Proof.
    intros Gamma.
    unfold ContextEqBool. destruct (ContextEqDec Gamma Gamma); auto.
  Qed.

  Lemma ContextEqBoolEqual : forall {Gamma Delta}, Gamma =ctxt= Delta = true -> Gamma = Delta.
  Proof.
    intros Gamma Delta H.
    unfold ContextEqBool in H. destruct (ContextEqDec Gamma Delta); auto.
    inversion H.
  Qed.
  
  Fixpoint ContextAppearsInProof {Gamma : Context} {b : Belief} (Delta : Context) (pf : Gamma ⊢ b) : bool :=
    match pf with
    | axiom Gamma _ _ _ => Gamma =ctxt= Delta
    | TTR Gamma _ _ _ => Gamma =ctxt= Delta
    | FFL Gamma _ _ _ _ _ _ _ _ => Gamma =ctxt= Delta
    | AndL Gamma _ _ _ _ _ pf1 => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1
    | AndR Gamma _ _ _ pf1 pf2 => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1 || ContextAppearsInProof Delta pf2
    | OrL Gamma _ _ _ _ _ pf1 pf2 => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1 || ContextAppearsInProof Delta pf2
    | OrR1 Gamma _ _ _ pf1 _ => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1
    | OrR2 Gamma _ _ _ pf1 _ => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1
    | ImpL Gamma _ _ _ _ _ _ pf1 pf2 => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1 || ContextAppearsInProof Delta pf2
    | ImpR Gamma _ _ _ _ pf1 => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1
    | forallL Gamma _ _ _ _ _ _ _ _ pf1 => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1
    | forallR Gamma _ _ _ _ _ _ _ _ pf1 => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1
    | existsL Gamma _ _ _ _ _ _ _ _ _ pf1 => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1
    | existsR Gamma _ _ _ _ _ _ pf1 => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1
    | flowsToRefl Gamma _ _ _ _ _ => Gamma =ctxt= Delta
    | flowsToTransR Gamma _ _ _ _ pf1 pf2 => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1 || ContextAppearsInProof Delta pf2
    | saysR Gamma _ _ _ _ pf1 => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1
    | saysL Gamma _ _ _ _ _ _ pf1 => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1
    | modalityExpandR Gamma _ _ _ pf1 => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1
    | modalityCollapseR Gamma _ _ _ pf1 => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1
    | modalityExpandL Gamma _ _ _ _ _ pf1 => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1
    | modalityCollapseL Gamma _ _ _ _ _ pf1 => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1
    | RVariance Gamma _ _ _ _ _ pf1 pf2 => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1 || ContextAppearsInProof Delta pf2
    | LVariance Gamma _ _ _ _ _ _ _ pf1 pf2 => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1 || ContextAppearsInProof Delta pf2
    | FwdR Gamma _ _ _ _ _ pf1 pf2 pf3 =>
      Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1 || ContextAppearsInProof Delta pf2 || ContextAppearsInProof Delta pf3
    | FwdL Gamma _ _ _ _ _ _ _ pf1 pf2 pf3 => 
      Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1 || ContextAppearsInProof Delta pf2 || ContextAppearsInProof Delta pf3
    | CRVariance Gamma _ _ _ _ pf1 pf2 => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1 || ContextAppearsInProof Delta pf2
    | CWVariance Gamma _ _ _ _ pf1 pf2 => Gamma =ctxt= Delta || ContextAppearsInProof Delta pf1 || ContextAppearsInProof Delta pf2
    end.

  Lemma ContextAppearsHere : forall {Gamma : Context} {b : Belief} (pf : Gamma ⊢ b), ContextAppearsInProof Gamma pf = true.
  Proof.
    intros Gamma b pf.
    induction pf; simpl; try (rewrite ContextEqBoolRefl; simpl; auto).
  Qed.

  Hint Constructors CompatibleSupercontext.
  Theorem CompatibleSupercontextProperty : forall {Gamma : Context} {b : Belief} (Delta : Context) (pf : Gamma ⊢ b),
      ContextAppearsInProof Delta pf = true -> Delta ≪ Gamma ⊢csc b.
  Proof.
    intros Gamma b Delta pf H.
    induction pf; simpl in *;
      repeat match goal with
             | [ H : ?Delta ≪ ?Gamma ⊢csc ?l1 ⊑ ?l2 @ ?m |- ?Delta ≪ ?Gamma ⊢csc _ ] =>
               apply CSCAtomic with (phi := l1 ⊑ l2) (m := m); [constructor | exact H]
             | [ H : _ || _ = true |- _ ] =>
               apply Bool.orb_prop in H; destruct H
             | [ H : Gamma =ctxt= Delta = true |- _ ] =>
               match goal with
               | [ _ : Gamma = Delta |- _ ] => fail 1
               | _ => pose proof (ContextEqBoolEqual H)
               end
             | [e : ?Gamma = ?Delta |- ?Delta ≪ ?Gamma ⊢csc ?b ] => rewrite e; apply CSCRefl
             | [e : ?Delta = ?Gamma |- ?Delta ≪ ?Gamma ⊢csc ?b ] => rewrite e; apply CSCRefl
             | [ H1 : ?P, H2 : ?P -> _ |- _ ] => specialize (H2 H1)
             end; auto.
    7: apply CSCForallR with (y := y); auto. 
    8: apply CSCExistsR with (t := t); auto.
    all: eauto.
    all: eapply CSCAtomic; eauto.
    all: try (constructor; auto;
              match goal with
              | [H : ContextAppearsInProof ?Delta ?pf = true |- _ ] =>
                clear H; apply provenProperBelief in pf; simpl in pf; destruct pf;
                match goal with
                | [H' : ⊢wff _ |- _ ] => inversion H'; auto
                end
              end; fail).
    all: try (match goal with
              | [H : ContextAppearsInProof _ ?pf = true |- _ ] =>
                clear H; apply provenProperBelief in pf; simpl in pf; destruct pf; auto
              end).
  Qed.

  Theorem CompatibleSupercontextProper : forall (Delta Gamma : Context) (b : Belief),
      ProperContext Gamma -> ProperBelief b -> Delta ≪ Gamma ⊢csc b -> ProperContext Delta.
  Proof.
    intros Delta Gamma b H H0 H1.
    induction H1; auto.
    - apply AppProperContext;
      [apply IHCompatibleSupercontext1 | apply IHCompatibleSupercontext2]; auto.
    - apply ProperContextIff with (Gamma := Delta1).
      intros b0. split. intro Hd1. apply Permutation_in with (l := Delta1); auto.
      intro Hd2; apply Permutation_in with(l := Delta2); auto.
      symmetry; auto.
      apply IHCompatibleSupercontext; auto.
      apply ProperContextIff with (Gamma := Gamma2); auto.
      intro b0; split; intro; eapply Permutation_in; [symmetry| | |]; eauto.
    - apply IHCompatibleSupercontext; auto.
      simpl; split; auto.
    - apply ProperContextCons; auto.
      apply ConsProperContext in H; destruct H; auto.
      apply IHCompatibleSupercontext; auto.
      apply ConsProperContext in H; destruct H; auto.
    - apply IHCompatibleSupercontext; auto.
      assert (ProperBelief (phi & psi @ m))
      by (apply BeliefInProperContextIsProper with (Gamma := Gamma); auto;
          apply PathToIn; auto).
      simpl in H3. destruct H3. inversion H4.
      apply ProperContextCons; [| apply ProperContextCons]; simpl; [split|split|]; auto.
    - apply IHCompatibleSupercontext; auto.
      destruct H0; simpl; split; auto. inversion H2; auto.
    - apply IHCompatibleSupercontext; auto.
      destruct H0; simpl; split; auto. inversion H2; auto.
    - apply IHCompatibleSupercontext; auto.
      apply ProperContextCons; auto.
      apply PathToIn in H1. apply BeliefInProperContextIsProper in H1; auto.
      inversion H1. inversion H4. split; auto.
    - apply IHCompatibleSupercontext; auto.
      apply ProperContextCons; auto.
      apply PathToIn in H1. apply BeliefInProperContextIsProper in H1; auto.
      inversion H1. inversion H4. split; auto.
    - apply IHCompatibleSupercontext; auto.
      inversion H0. inversion H3. split; auto.
    - apply IHCompatibleSupercontext; auto.
      inversion H0. inversion H3. split; auto.
    - apply IHCompatibleSupercontext; auto.
      apply ProperContextCons; auto.
      apply PathToIn in H1. apply BeliefInProperContextIsProper in H1; auto.
      inversion H1. inversion H4. split; auto.
    - apply IHCompatibleSupercontext; auto.
      apply PathToIn in H1. apply BeliefInProperContextIsProper in H1; auto.
      inversion H1. inversion H4. split; auto. constructor; auto.
    - inversion H0; inversion H3. apply IHCompatibleSupercontext.
           apply ProperContextCons; auto.
      all: split; auto. constructor; auto.
    - apply IHCompatibleSupercontext; auto.
      apply PathToIn in H1. apply BeliefInProperContextIsProper in H1; auto.
      inversion H1. inversion H6.
      pose (x := freshVar (L ++ varsInFormula phi) sigma).
      assert (~ In x L) as HxL
        by (intro Hx; apply freshVarNotIn with (vs := L ++ varsInFormula phi) (sigma := sigma);
            apply in_or_app; left; fold x; auto).
      assert (⊢s varTerm x ::: sigma) as x_term_sort
          by (unfold x;
              rewrite <- freshVarSameSort with (vs := L ++ varsInFormula phi) (sigma := sigma) at 2;
              apply varS).
      specialize (H8 x HxL x_term_sort).
      apply WellFormedSubst with (t := t) (x := x) in H8; auto.
      rewrite open_formula_subst in H8; auto.
      rewrite notFreeInFormulaSubstEq in H8; auto.
      simpl in H8.
      destruct (varEqDec x x) as [e|n]; [clear e| exfalso; apply n; reflexivity].
      apply ProperContextCons; [split|]; auto.
      intro fvf; apply FreeVarsInFormula in fvf.
      apply freshVarNotIn with (vs := L ++ varsInFormula phi) (sigma := sigma).
      fold x. apply in_or_app; right; auto.
      unfold x. rewrite freshVarSameSort; auto.
    - apply IHCompatibleSupercontext; auto.
      inversion H0. inversion H7.
      pose (x := freshVar (L ++ varsInFormula phi) sigma).
      assert (~ In x L) as HxL
        by (intro Hx; apply freshVarNotIn with (vs := L ++ varsInFormula phi) (sigma := sigma);
            apply in_or_app; left; fold x; auto).
      assert (⊢s varTerm x ::: sigma) as x_term_sort
          by (unfold x;
              rewrite <- freshVarSameSort with (vs := L ++ varsInFormula phi) (sigma := sigma) at 2;
              apply varS).
      specialize (H9 x HxL x_term_sort).
      apply WellFormedSubst with (t := varTerm y) (x := x) in H9; auto.
      rewrite open_formula_subst in H9; auto.
      rewrite notFreeInFormulaSubstEq in H9; auto.
      simpl in H9.
      destruct (varEqDec x x) as [e|n]; [clear e| exfalso; apply n; reflexivity].
      split; auto.
      intro fvf; apply FreeVarsInFormula in fvf.
      apply freshVarNotIn with (vs := L ++ varsInFormula phi) (sigma := sigma).
      fold x. apply in_or_app; right; auto. constructor; auto. constructor; auto.
      unfold x. rewrite freshVarSameSort; auto. rewrite <- H1. constructor.
    - apply IHCompatibleSupercontext; auto.
      apply PathToIn in H1. apply BeliefInProperContextIsProper in H1; auto.
      inversion H1. inversion H7.
      pose (x := freshVar (L ++ varsInFormula phi) sigma).
      assert (~ In x L) as HxL
        by (intro Hx; apply freshVarNotIn with (vs := L ++ varsInFormula phi) (sigma := sigma);
            apply in_or_app; left; fold x; auto).
      assert (⊢s varTerm x ::: sigma) as x_term_sort
          by (unfold x;
              rewrite <- freshVarSameSort with (vs := L ++ varsInFormula phi) (sigma := sigma) at 2;
              apply varS).
      specialize (H9 x HxL x_term_sort).
      apply WellFormedSubst with (t := varTerm y) (x := x) in H9; auto.
      rewrite open_formula_subst in H9; auto.
      rewrite notFreeInFormulaSubstEq in H9; auto.
      simpl in H9.
      destruct (varEqDec x x) as [e|n]; [clear e| exfalso; apply n; reflexivity].
      apply ProperContextCons; [split|]; auto.
      intro fvf; apply FreeVarsInFormula in fvf.
      apply freshVarNotIn with (vs := L ++ varsInFormula phi) (sigma := sigma).
      fold x. apply in_or_app; right; auto. constructor; auto. constructor; auto.
      unfold x. rewrite freshVarSameSort; auto. rewrite <- H2. constructor.
    - apply IHCompatibleSupercontext; auto.
      inversion H0. inversion H5.
      pose (x := freshVar (L ++ varsInFormula phi) sigma).
      assert (~ In x L) as HxL
        by (intro Hx; apply freshVarNotIn with (vs := L ++ varsInFormula phi) (sigma := sigma);
            apply in_or_app; left; fold x; auto).
      assert (⊢s varTerm x ::: sigma) as x_term_sort
          by (unfold x;
              rewrite <- freshVarSameSort with (vs := L ++ varsInFormula phi) (sigma := sigma) at 2;
              apply varS).
      specialize (H7 x HxL x_term_sort).
      apply WellFormedSubst with (t := t) (x := x) in H7; auto.
      rewrite open_formula_subst in H7; auto.
      rewrite notFreeInFormulaSubstEq in H7; auto.
      simpl in H7.
      destruct (varEqDec x x) as [e|n]; [clear e| exfalso; apply n; reflexivity].
      split; auto.
      intro fvf; apply FreeVarsInFormula in fvf.
      apply freshVarNotIn with (vs := L ++ varsInFormula phi) (sigma := sigma).
      fold x. apply in_or_app; right; auto. 
      unfold x. rewrite freshVarSameSort; auto. 
    - apply IHCompatibleSupercontext; auto.
      apply ProperContextCons; auto.
      apply PathToIn in H1; apply BeliefInProperContextIsProper in H1; auto.
      destruct H1. inversion H3. split; auto. constructor; auto.
    - apply IHCompatibleSupercontext; auto.
      destruct H0. inversion H2. split; auto. constructor; auto.
    - apply IHCompatibleSupercontext; auto.
      inversion H0; split; auto. apply CollapseDoubleProper; auto.
    - apply PathToIn in H1. apply BeliefInProperContextIsProper in H1; auto.
      destruct H1. apply IHCompatibleSupercontext; auto.
      apply ProperContextCons; auto. split; auto.
      apply CollapseDoubleProper' with (pth := pth); auto.
    - apply IHCompatibleSupercontext; auto.
      inversion H0; split; auto. apply CollapseDoubleProper' with (pth := pth); auto.
    - apply PathToIn in H1. apply BeliefInProperContextIsProper in H1; auto.
      destruct H1. apply IHCompatibleSupercontext; auto.
      apply ProperContextCons; auto. split; auto.
      apply CollapseDoubleProper; auto.
    - apply IHCompatibleSupercontext; auto. destruct H0; split; auto.
      apply ReplaceLabelInModalityProper' with (l := l1) (l' := l2) (pth := pth); auto.
      apply provenProperBelief in H1. destruct H1. inversion H4; auto.
    - apply IHCompatibleSupercontext; auto; apply ProperContextCons; auto.
      apply PathToIn in H1. apply BeliefInProperContextIsProper in H1; auto.
      destruct H1. split; auto. apply ReplaceLabelInModalityProper; auto.
      apply provenProperBelief in H2; destruct H2. inversion H5; auto.
    - apply IHCompatibleSupercontext; auto.
      destruct H0; split; auto.
      apply ReplacePrinInModalityProper' with (pth := pth) (q := q); auto.
      apply provenProperBelief in H2. destruct H2. inversion H5; auto.
    - apply IHCompatibleSupercontext; auto. apply ProperContextCons; auto.
      apply PathToIn in H1; apply BeliefInProperContextIsProper in H1; auto.
      destruct H1; split; auto.
      apply ReplacePrinInModalityProper; auto.
      apply provenProperBelief in H3. destruct H3. inversion H6; auto.
  Qed.

  Lemma CompatibleSupercontextSuper : forall {Delta Gamma : Context} {b : Belief},
      Delta ≪ Gamma ⊢csc b -> forall b', In b' Gamma -> In b' Delta.
  Proof.
    intros Delta Gamma b H.
    induction H; intros b' b'Γ; auto;
      try (destruct b'Γ; [left; auto | right; apply IHCompatibleSupercontext; auto]; fail);
      try (apply IHCompatibleSupercontext; right; auto; fail).
    - apply in_or_app; left; apply IHCompatibleSupercontext1; auto.
    - apply Permutation_in with (l := Delta1); auto.
      apply IHCompatibleSupercontext; auto.
      apply Permutation_in with (l := Gamma2); auto.
      symmetry; auto.
    - apply IHCompatibleSupercontext. right; right; auto.
  Qed.
End CompatibleSupercontext.