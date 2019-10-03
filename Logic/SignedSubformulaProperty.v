Require Export Term.
Require Export Formula.
Require Export Sequent.
Require Export SignedSubformula.

Require Import Base.Lists.
Require Import Base.Permutation.
Require Export Tactics.Equality.
Require Export Tactics.FormulaEquality.
Require Import Tactics.TermEquality.
Require Import Tactics.WellFormedFormulaNoProofs.
Require Import Tactics.TermHasSortNoFormulas.

Import ListNotations.
Module Type SignedSubformulaProperty (G : GroundInfo) (GTerm : Term G) (GFormula : Formula G GTerm)
       (TE : TermEquality G GTerm) (FE : FormulaEquality G GTerm GFormula TE) (THS : TermHasSort'' G GTerm TE) (WFF : WellFormedFormula' G GTerm TE THS GFormula FE) (SSF : SignedSubformula G GTerm GFormula TE FE) (SEQ : Sequent G GTerm GFormula TE FE THS WFF).

  Import G. Import GTerm. Import GFormula. Import TE. Import FE. Import ListNotations.
  Import SSF. Import THS. Import WFF. Import SEQ.

  Open Scope term_scope. Open Scope formula_scope. Open Scope list_scope.
  Fixpoint FormulaAppearsInContext (phi : flafolFormula) (Gamma : Context) : bool :=
    match Gamma with
    | [] => false
    | (b :: Delta) => match b with
                | (psi @ m) => if formulaEqDec phi psi
                            then true
                            else FormulaAppearsInContext phi Delta
                end
    end.

  Lemma PathToAppears : forall {phi : flafolFormula} {m : Modality} {Gamma : Context},
      Path (phi @ m) Gamma -> FormulaAppearsInContext phi Gamma = true.
  Proof.
    intros phi m Gamma H.
    remember (phi @ m). induction H.
    rewrite Heqb. simpl; auto. destruct (formulaEqDec phi phi); [auto | exfalso; apply n; auto].
    specialize (IHPath Heqb). simpl. destruct b. destruct (formulaEqDec phi f); auto.
  Qed.

  Fixpoint FormulaAppearsNegInProof {Gamma : Context} {b : Belief} (phi : flafolFormula) (pf : Gamma ⊢ b) : bool :=
    match pf with
    | axiom Gamma _ _ _ => FormulaAppearsInContext phi Gamma
    | TTR Gamma _ _ _ => FormulaAppearsInContext phi Gamma
    | FFL Gamma _ _ _ _ _ _ _ _ => FormulaAppearsInContext phi Gamma
    | AndL _ _ _ _ _ _ pf1 => FormulaAppearsNegInProof phi pf1
    | AndR _ _ _ _ pf1 pf2 => orb (FormulaAppearsNegInProof phi pf1) (FormulaAppearsNegInProof phi pf2)
    | OrL _ _ _ _ _ _ pf1 pf2 => orb (FormulaAppearsNegInProof phi pf1) (FormulaAppearsNegInProof phi pf2)
    | OrR1 _ _ _ _ pf1 _ => FormulaAppearsNegInProof phi pf1
    | OrR2 _ _ _ _ pf1 _ => FormulaAppearsNegInProof phi pf1
    | ImpL _ _ _ _ _ _ _ _ pf1 => FormulaAppearsNegInProof phi pf1
    | ImpR _ _ _ _ _ pf1 => FormulaAppearsNegInProof phi pf1
    | forallL _ _ _ _ _ _ _ _ _ pf1 => FormulaAppearsNegInProof phi pf1
    | forallR _ _ _ _ _ _ _ _ _ pf1 => FormulaAppearsNegInProof phi pf1
    | existsL _ _ _ _ _ _ _ _ _ _ pf1 => FormulaAppearsNegInProof phi pf1
    | existsR _ _ _ _ _ _ _ pf1 => FormulaAppearsNegInProof phi pf1
    | flowsToRefl Gamma _ _ _ _ _ => FormulaAppearsInContext phi Gamma
    | flowsToTransR _ _ _ _ _ pf1 pf2 => orb (FormulaAppearsNegInProof phi pf1) (FormulaAppearsNegInProof phi pf2)
    | saysR _ _ _ _ _ pf1 => FormulaAppearsNegInProof phi pf1
    | saysL _ _ _ _ _ _ _ pf1 => FormulaAppearsNegInProof phi pf1
    | modalityExpandR _ _ _ _ pf1 => FormulaAppearsNegInProof phi pf1
    | modalityCollapseR _ _ _ _ pf1 => FormulaAppearsNegInProof phi pf1
    | modalityExpandL _ _ _ _ _ _ pf1 => FormulaAppearsNegInProof phi pf1
    | modalityCollapseL _ _ _ _ _ _ pf1 => FormulaAppearsNegInProof phi pf1
    | RVariance _ _ _ _ _ _ pf1 pf2 => orb (FormulaAppearsNegInProof phi pf1) (FormulaAppearsNegInProof phi pf2)
    | LVariance _ _ _ _ _ _ _ _ pf1 pf2 => orb (FormulaAppearsNegInProof phi pf1) (FormulaAppearsNegInProof phi pf2)
    | FwdR _ _ _ _ _ _ pf1 pf2 pf3 =>
      orb (FormulaAppearsNegInProof phi pf1) (orb (FormulaAppearsNegInProof phi pf2) (FormulaAppearsNegInProof phi pf3))
    | FwdL _ _ _ _ _ _ _ _ pf1 pf2 pf3 =>
      orb (FormulaAppearsNegInProof phi pf1) (orb (FormulaAppearsNegInProof phi pf2) (FormulaAppearsNegInProof phi pf3))
    | CRVariance _ _ _ _ _ pf1 pf2 => orb (FormulaAppearsNegInProof phi pf1) (FormulaAppearsNegInProof phi pf2)
    | CWVariance _ _ _ _ _ pf1 pf2 => orb (FormulaAppearsNegInProof phi pf1) (FormulaAppearsNegInProof phi pf2)
    end.

  Fixpoint FormulaAppearsPosInProof {Gamma : Context} {b : Belief} (phi : flafolFormula) (pf : Gamma ⊢ b) : bool :=
    match b with
    | psi @ _ => if formulaEqDec phi psi then true else
                  match pf with
                  | axiom _ _ _ _ => false
                  | TTR _ _ _ _ => false
                  | FFL _ _ _ _ _ _ _ _ _ => false
                  | AndL _ _ _ _ _ _ pf1 => FormulaAppearsPosInProof phi pf1
                  | AndR _ _ _ _ pf1 pf2 => orb (FormulaAppearsPosInProof phi pf1) (FormulaAppearsPosInProof phi pf2)
                  | OrL _ _ _ _ _ _ pf1 pf2 => orb (FormulaAppearsPosInProof phi pf1) (FormulaAppearsPosInProof phi pf2)
                  | OrR1 _ _ _ _ pf1 _ => FormulaAppearsPosInProof phi pf1
                  | OrR2 _ _ _ _ pf1 _ => FormulaAppearsPosInProof phi pf1
                  | ImpL _ _ _ _ _ _ _ _ pf1 => FormulaAppearsPosInProof phi pf1
                  | ImpR _ _ _ _ _ pf1 => FormulaAppearsPosInProof phi pf1
                  | forallL _ _ _ _ _ _ _ _ _ pf1 => FormulaAppearsPosInProof phi pf1
                  | forallR _ _ _ _ _ _ _ _ _ pf1 => FormulaAppearsPosInProof phi pf1
                  | existsL _ _ _ _ _ _ _ _ _ _ pf1 => FormulaAppearsPosInProof phi pf1
                  | existsR _ _ _ _ _ _ _ pf1 => FormulaAppearsPosInProof phi pf1
                  | flowsToRefl Gamma _ _ _ _ _ => false
                  | flowsToTransR _ _ _ _ _ pf1 pf2 => orb (FormulaAppearsPosInProof phi pf1) (FormulaAppearsPosInProof phi pf2)
                  | saysR _ _ _ _ _ pf1 => FormulaAppearsPosInProof phi pf1
                  | saysL _ _ _ _ _ _ _ pf1 => FormulaAppearsPosInProof phi pf1
                  | modalityExpandR _ _ _ _ pf1 => FormulaAppearsPosInProof phi pf1
                  | modalityCollapseR _ _ _ _ pf1 => FormulaAppearsPosInProof phi pf1
                  | modalityExpandL _ _ _ _ _ _ pf1 => FormulaAppearsPosInProof phi pf1
                  | modalityCollapseL _ _ _ _ _ _ pf1 => FormulaAppearsPosInProof phi pf1
                  | RVariance _ _ _ _ _ _ pf1 pf2 => orb (FormulaAppearsPosInProof phi pf1) (FormulaAppearsPosInProof phi pf2)
                  | LVariance _ _ _ _ _ _ _ _ pf1 pf2 => orb (FormulaAppearsPosInProof phi pf1) (FormulaAppearsPosInProof phi pf2)
                  | FwdR _ _ _ _ _ _ pf1 pf2 pf3 =>
                    orb (FormulaAppearsPosInProof phi pf1) (orb (FormulaAppearsPosInProof phi pf2) (FormulaAppearsPosInProof phi pf3))
                  | FwdL _ _ _ _ _ _ _ _ pf1 pf2 pf3 =>
                    orb (FormulaAppearsPosInProof phi pf1) (orb (FormulaAppearsPosInProof phi pf2) (FormulaAppearsPosInProof phi pf3))
                  | CRVariance _ _ _ _ _ pf1 pf2 => orb (FormulaAppearsPosInProof phi pf1) (FormulaAppearsPosInProof phi pf2)
                  | CWVariance _ _ _ _ _ pf1 pf2 => orb (FormulaAppearsPosInProof phi pf1) (FormulaAppearsPosInProof phi pf2)
                  end
    end.

  
  Lemma FormulaAppearsNegHere : forall (Gamma : Context) {b : Belief} (phi : flafolFormula) (pf : Gamma ⊢ b),
      FormulaAppearsInContext phi Gamma = true -> FormulaAppearsNegInProof phi pf = true.
  Proof.
    intros Gamma b phi pf H.
    induction pf; simpl in *; auto;
    repeat match goal with
           | [H : context[if ?b then _ else _] |- _ ] => destruct b; auto
           | [H1 : ?P, H2 : ?P -> _ |- _ ] => specialize (H2 H1)
           end; rewrite IHpf1; auto.
  Qed.

  Lemma FormulaAppearsPosHere : forall {Gamma : Context} (phi : flafolFormula) {m : Modality} (pf : Gamma ⊢ phi @ m),
      FormulaAppearsPosInProof phi pf = true.
  Proof.
    intros Gamma phi m pf; remember (phi @ m).
    induction pf; simpl; try (destruct b); inversion Heqb.
    all: repeat match goal with
                | [ |- context[formulaEqDec ?phi ?phi] ] =>
                  let e := fresh "e" in
                  let n := fresh "n" in
                  destruct (formulaEqDec phi phi) as [e | n] ; [| exfalso; apply n; reflexivity]
                | [ H : ?phi = ?psi |- context[formulaEqDec ?phi ?psi] ] =>
                  let e := fresh "e" in
                  let n := fresh "n" in
                  destruct (formulaEqDec phi psi) as [e | n] ; [| exfalso; apply n; rewrite H; reflexivity]
                | [ H : ?psi = ?phi |- context[formulaEqDec ?phi ?psi] ] =>
                  let e := fresh "e" in
                  let n := fresh "n" in
                  destruct (formulaEqDec phi psi) as [e | n] ; [| exfalso; apply n; rewrite H; reflexivity]
                end; auto.
  Qed.

  Definition FormulaOfBelief : Belief -> flafolFormula :=
    fun b => match b with
          | phi @ _ => phi
          end.
  
  Hint Constructors SignedSubformulaOf.
  Theorem LeftSignedSubformulaProperty : forall (Gamma : Context) {b : Belief} (phi : flafolFormula) (pf : Gamma ⊢ b),
      FormulaAppearsNegInProof phi pf = true ->
      (exists chi, FormulaAppearsInContext chi Gamma = true /\ (phi s: Neg) ≤s (chi s: Neg)) \/ (phi s: Neg) ≤s (FormulaOfBelief b s: Pos).
  Proof.
    intros Gamma b phi pf H.
    induction pf; simpl in *; try (left; exists phi; split; auto; fail);
      repeat match goal with
             | [H1 : ?b1 = ?b2, H2 : ?b1 = ?b2 -> _ |- _ ] => specialize (H2 H1)
             | [ H : (orb ?b1 ?b2) = true |- _ ] => apply Bool.orb_prop in H; destruct H
             end; auto; try (destruct IHpf; [left | right]; auto; eapply SSTrans; eauto; fail);
        try (destruct IHpf1; [left | right]; auto; eapply SSTrans; eauto; fail);
        try (destruct IHpf2; [left | right]; auto; eapply SSTrans; eauto; fail).
    - destruct IHpf; [left | right; auto]. destruct H0; destruct H0.
      destruct (formulaEqDec x phi0).
      exists (phi0 & psi); split; [apply (PathToAppears pth) | rewrite e in H1; apply SSTrans with (psi := (phi0, Neg)); auto].
      destruct (formulaEqDec x psi).
      exists (phi0 & psi); split; [apply (PathToAppears pth) | rewrite e in H1; apply SSTrans with (psi := (psi, Neg)); auto].
      exists x; split; auto.
    - clear IHpf2. destruct IHpf1; [left | right; auto].
      destruct H0; destruct H0; destruct (formulaEqDec x phi0).
      exists (phi0 ⊕ psi); split; [apply (PathToAppears pth) | rewrite e in H1; eapply SSTrans; eauto].
      exists x; split; auto.
    - clear IHpf1. destruct IHpf2; [left | right; auto].
      destruct H0; destruct H0; destruct (formulaEqDec x psi).
      exists (phi0 ⊕ psi); split; [apply (PathToAppears pth) | rewrite e in H1; eapply SSTrans; eauto].
      exists x; split; auto.
    - clear IHpf1. destruct IHpf2; [left | right; auto].
      destruct H0; destruct (formulaEqDec x psi); destruct H0.
      exists (phi0 ==⟨ l ⟩> psi); split; [apply (PathToAppears pth) | rewrite e in H1; eapply SSTrans; eauto].
      exists x; split; auto.
    - destruct IHpf; [destruct H0| right; auto]. destruct (formulaEqDec x phi0); destruct H0; [clear H0|].
      rewrite e in H1; right; pose proof (SSImpL phi0 psi l Pos); simpl in H0; eapply SSTrans; eauto.
      left; exists x; split; auto.
      eapply SSTrans; eauto.
    - destruct IHpf; [left | right]; auto. 
      destruct H0; destruct H0. destruct (formulaEqDec x (open_formula phi0 t)).
      exists (∀ sigma; phi0); split. apply (PathToAppears pth). rewrite e in H1; eapply SSTrans; eauto.
      exists x; split; auto.
    - destruct IHpf; [left | right; auto]. destruct H0; destruct H0; destruct (formulaEqDec x (open_formula phi0 (varTerm y))).
      exists (∃ sigma; phi0); split. apply (PathToAppears pth). rewrite e0 in H1; eapply SSTrans; eauto.
      exists x; split; auto.
    - destruct IHpf1; [left; auto|].
      pose proof (FlowsToOnlySub lab1 lab2 (phi, Neg) Pos H0).
      inversion H1.
    - destruct IHpf2; [left; auto|].
      pose proof (FlowsToOnlySub lab2 lab3 (phi, Neg) Pos H0).
      inversion H1.
    - destruct IHpf; [left; auto|].
      right; eapply SSTrans; eauto.
      apply SaysInner;
      pose proof (provenProperBelief pf);
      destruct H1;
      inversion H1; auto.
    - destruct IHpf; [left | right; auto].
      destruct H0; destruct H0; destruct (formulaEqDec x phi0).
      exists (p □ ⟨ lab ⟩ phi0); split. apply (PathToAppears pth). rewrite e in H1; eapply SSTrans; eauto.
      pose proof (provenProperContext pf). apply ConsProperContext in H2. destruct H2.
      inversion H2. inversion H4.
      apply SaysInner; auto.
      exists x; split; auto.
    - destruct IHpf; [ left | right; auto].
      destruct H0; destruct H0; destruct (formulaEqDec x phi0).
      exists x; split; auto; rewrite e; apply (PathToAppears pth').
      exists x; split; auto.
    - destruct IHpf; [left | right; auto].
      destruct H0; destruct H0; destruct (formulaEqDec x phi0).
      exists x; split; auto; rewrite e; apply (PathToAppears pth').
      exists x; split; auto.
    - destruct IHpf2; [left; auto |].
      pose proof (FlowsToOnlySub lab1 lab2 (phi, Neg) Pos H0). inversion H1.
    - destruct IHpf1; [left | right; auto].
      destruct H0; destruct H0; destruct (formulaEqDec x phi0).
      exists x; split; auto; rewrite e; apply (PathToAppears pth).
      exists x; split; auto.
    - destruct IHpf2; auto.
      pose proof (FlowsToOnlySub lab1 lab2 (phi, Neg) Pos H0). inversion H1.
    - destruct IHpf2; auto. 
      pose proof (CanROnlySub q _ _ _ H0). inversion H1.
    - destruct IHpf3; auto. 
      pose proof (CanWOnlySub p _ _ _ H0). inversion H1.
    - destruct IHpf1; [left | right; auto].
      destruct H0; destruct H0; destruct (formulaEqDec x phi0).
      exists x; split; auto; rewrite e; apply (PathToAppears pth').
      exists x; split; auto.
    - destruct IHpf2; auto. 
      pose proof (CanWOnlySub _ _ _ _ H0). inversion H1.
    - destruct IHpf3; auto. 
      pose proof (CanROnlySub _ _ _ _ H0). inversion H1.
    - destruct IHpf1; auto.
      pose proof (CanROnlySub _ _ _ _ H0). inversion H1.
    - destruct IHpf2; auto.
      pose proof (FlowsToOnlySub lab1 lab2 (phi, Neg) Pos H0). inversion H1.
    - destruct IHpf1; auto.
      pose proof (CanWOnlySub _ _ _ _ H0). inversion H1.
    - destruct IHpf2; auto.
      pose proof (FlowsToOnlySub lab1 lab2 (phi, Neg) Pos H0). inversion H1.
  Qed.

  End SignedSubformulaProperty.