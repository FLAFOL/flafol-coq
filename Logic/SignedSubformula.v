Require Export Term.
Require Export Formula.

Require Import Base.Lists.
Require Import Base.Permutation.
Require Export Tactics.Equality.
Require Export Tactics.FormulaEquality.
Require Import Tactics.TermEquality.
Require Import Tactics.WellFormedFormulaNoProofs.
Require Import Tactics.TermHasSortNoFormulas.

Import ListNotations.
Module Type SignedSubformula (G : GroundInfo) (GTerm : Term G) (GFormula : Formula G GTerm)
       (TE : TermEquality G GTerm) (FE : FormulaEquality G GTerm GFormula TE).

  Import G. Import GTerm. Import GFormula. Import TE. Import FE. Import ListNotations.

  Open Scope term_scope. Open Scope formula_scope. Open Scope list_scope.


  Inductive Sign : Set :=
    Pos
  | Neg.

  Definition negate : Sign -> Sign :=
    fun g => match g with
          | Pos => Neg
          | Neg => Pos
          end.

  Definition SignedFormula := (flafolFormula * Sign)%type.

  Notation "phi s: g" := ((phi, g ) : SignedFormula) (at level 35).
  Reserved Infix "≤s" (at level 40).

  Inductive SignedSubformulaOf : SignedFormula -> SignedFormula -> Prop :=
  | SSRefl : forall phi : SignedFormula, phi ≤s phi
  | SSTrans : forall phi psi chi : SignedFormula, phi ≤s psi -> psi ≤s chi -> phi ≤s chi
  | SSOrL : forall (phi psi : flafolFormula) (g : Sign),
      (phi s: g) ≤s (phi ⊕ psi s: g)
  | SSOrR : forall (phi psi : flafolFormula) (g : Sign),
      (psi s: g) ≤s (phi ⊕ psi s: g)
  | SSAndL : forall (phi psi : flafolFormula) (g : Sign),
      (phi s: g) ≤s (phi & psi s: g)
  | SSAndR : forall (phi psi : flafolFormula) (g : Sign),
      (psi s: g) ≤s (phi & psi s: g)
  | SSImpL : forall (phi psi : flafolFormula) (l : flafolTerm) (g : Sign),
      (phi s: negate g) ≤s (phi ==⟨ l ⟩> psi s: g)
  | SSImpR : forall (phi psi : flafolFormula) (l : flafolTerm) (g : Sign),
      (psi s: g) ≤s (phi ==⟨ l ⟩> psi s: g)
  | SSForallNeg : forall (phi : flafolFormula) (s : G.sort) (t : flafolTerm),
      ⊢s t ::: s -> (open_formula phi t s: Neg) ≤s (∀ s; phi s: Neg)
  | SSForallPos : forall (phi : flafolFormula) (s : G.sort) (x : var),
      VarSort x = s ->
      (open_formula phi (varTerm x) s: Pos) ≤s (∀ s; phi s: Pos)
  | SSExistsPos : forall (phi : flafolFormula) (s : G.sort) (t : flafolTerm),
      ⊢s t ::: s -> (open_formula phi t s: Pos) ≤s (∃ s; phi s: Pos)
  | SSExistsNeg : forall (phi : flafolFormula) (y : var) (s : G.sort),
      VarSort y = s ->
      (open_formula phi (varTerm y) s: Neg) ≤s (∃ s; phi s: Neg)
  | SaysInner : forall (phi : flafolFormula) (g : Sign) (p lab : flafolTerm),
      ⊢s p ::: Principal -> ⊢s lab ::: Label ->
      (phi s: g) ≤s (p □ ⟨ lab ⟩ phi s: g)
  where "phi ≤s psi" := (SignedSubformulaOf phi psi).


  Lemma FlowsToOnlySub : forall (t u : flafolTerm) (phi : SignedFormula) (g : Sign),
      phi ≤s (t ⊑ u s: g) -> phi = (t ⊑ u s: g).
  Proof.
    intros t u phi g.
    generalize (eq_refl (t ⊑ u s: g)). generalize (t ⊑ u s: g) at 1 3 4.
    intros s H H0.
    induction H0; auto; try (inversion H; auto; fail).
    rewrite <- IHSignedSubformulaOf2; auto. rewrite <- IHSignedSubformulaOf1; auto.
    rewrite IHSignedSubformulaOf2; auto.
  Qed.

  Lemma CanROnlySub : forall(p l : flafolTerm) (phi : SignedFormula) (g : Sign),
      phi ≤s (canRead p l s: g) -> phi = (canRead p l s: g).
  Proof.
    intros p l phi g.
    generalize (eq_refl (canRead p l s: g)). generalize (canRead p l s: g) at 1 3 4.
    intros s H H0.
    induction H0; auto; try (inversion H; auto; fail).
    rewrite <- IHSignedSubformulaOf2; auto. rewrite <- IHSignedSubformulaOf1; auto.
    rewrite IHSignedSubformulaOf2; auto.
  Qed.

  Lemma CanWOnlySub : forall(p l : flafolTerm) (phi : SignedFormula) (g : Sign),
      phi ≤s (canWrite p l s: g) -> phi = (canWrite p l s: g).
  Proof.
    intros p l phi g.
    generalize (eq_refl (canWrite p l s: g)). generalize (canWrite p l s: g) at 1 3 4.
    intros s H H0.
    induction H0; auto; try (inversion H; auto; fail).
    rewrite <- IHSignedSubformulaOf2; auto. rewrite <- IHSignedSubformulaOf1; auto.
    rewrite IHSignedSubformulaOf2; auto.
  Qed.

    


  Ltac FindEqualSign := idtac.
  Ltac FindEqualSign' l :=
    match goal with
    | [ H : ?P |- ?P ] => exact H
    | [ H : Pos = Neg |- _ ] => inversion H
    | [ H : Neg = Pos |- _ ] => inversion H
    | [ e : ?g = ?g' |- ?g' = ?g ] => exact (eq_sym e)
    | [ e : ?g = ?g' |- ?g = ?g''] =>
      NotInList g' l; transitivity g'; [exact e | FindEqualSign' constr:(g' :: l)]
    end.
  Ltac FindEqualSign ::= FindEqualSign' constr:(@nil Sign).

  Lemma UnifySignedFormula : forall g g' phi psi, phi = psi -> g = g' -> (phi s: g) = (psi s: g').
  Proof.
    intros g g' phi psi H H0; rewrite H; rewrite H0; reflexivity.
  Qed.
  Ltac FindEqualSignedFormula := idtac.
  Ltac FindEqualSignedFormula' l := 
    match goal with
    | [ H : ?P |- ?P ] => exact H
    | [ e : ?phi = ?psi |- ?psi = ?phi ] => exact (eq_sym e)
    | [ |- (?phi s: ?g) = (?psi s: ?g') ] => apply UnifySignedFormula;
                                       [ FindFormulaEquality | FindEqualSign]
    | [ e : ?phi = ?psi |- ?phi = ?chi ] =>
      NotInList psi l; transitivity psi; [exact e | FindEqualSignedFormula' constr:(psi :: l)]
    end.
  Ltac FindEqualSignedFormula ::= FindEqualSignedFormula' constr:(@nil SignedFormula).

  Lemma UnifySubformula : forall phi psi : SignedFormula, phi = psi -> phi ≤s psi.
  Proof.
    intros phi psi H; rewrite H; apply SSRefl.
  Qed.

  Lemma UnifyGSSImpL : forall phi psi l g g',
      g' = negate g -> (phi s: g') ≤s (phi ==⟨ l ⟩> psi s: g).
  Proof.
    intros phi psi l g g' H; rewrite H; apply SSImpL.
  Qed.
  
  Ltac FindSignedSubformula := idtac.
  Ltac FindSignedSubformula' l :=
    match goal with
    | [ H : ?P |- ?P ] => exact H
    | [ |- ?phi ≤s ?phi ] => apply SSRefl
    | [ |- ?phi ≤s ?psi ] =>
      apply UnifySubformula; FindEqualSignedFormula
    | [ H: ?phi ≤s ?psi  |- ?phi ≤s ?chi ] =>
      NotInList psi l; apply (SSTrans phi psi chi); [exact H | FindSignedSubformula' constr:(psi :: l)]
    | [ |- (?phi, ?g) ≤s (?phi ⊕ _, ?g) ] =>
      apply SSOrL
    | [ |- (?phi, ?g) ≤s (_ ⊕ ?phi, ?g) ] =>
      apply SSOrR
    | [ |- (?phi, ?g) ≤s (?phi & _, ?g) ] =>
      apply SSAndL
    | [ |- (?phi, ?g) ≤s (_ & ?phi, ?g) ] =>
      apply SSAndR
    | [ |- (?phi, ?g') ≤s (?phi ==⟨ _ ⟩> _, ?g)] =>
        apply UnifyGSSImpL; simpl; FindEqualSign
    | [ |- ?phi ≤s _ ==⟨ _ ⟩> ?phi ] =>
      apply SSImpR
    | [ |- ?p □ ⟨?lab⟩ ?phi ≤s ?p □ ⟨?lab⟩ ?psi ] =>
      apply SaysInner; [auto | auto | FindSignedSubformula]
    end.
  Ltac FindSignedSubformula ::= FindSignedSubformula' constr:(@nil SignedFormula).


  
End SignedSubformula.