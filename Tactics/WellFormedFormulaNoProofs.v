Require Export Formula.
Require Import Term.
Require Import Equality.
Require Import TermEquality.
Require Import FormulaEquality.
Require Import TermHasSortNoFormulas.
Require Import Coq.Lists.List.

Import ListNotations.
Module Type WellFormedFormula'(G : GroundInfo)(GT : Term G) (TE : TermEquality G GT)
       (THS : TermHasSort'' G GT TE) (GF : Formula G GT) (FE : FormulaEquality G GT GF TE).
  Import G. Import GT. Import TE. Import THS. Import GF. Import FE.

  Lemma UnifyWFF : forall (phi psi : flafolFormula),
      phi = psi -> ⊢wff phi -> ⊢wff psi.
  Proof.
    intros phi psi H H0; rewrite <- H; auto.
  Qed.

  Ltac FindWellFormedFormula' :=
    match goal with
    | [ wff : ⊢wff ?phi |- ⊢wff ?phi ] => exact wff
    | [ wff: ⊢wff (?phi f[ ?x ↦ ?t ]) |- ⊢wff ?phi ] =>
      apply (fun pf => WellFormedConstructor phi x t pf wff); FindTermHasSort''
    | [ |- ⊢wff TT ] => exact TTWF
    | [ |- ⊢wff FF ] => exact FFWF
    | [ |- ⊢wff (?ℓ1 ⊑ ?ℓ2) ] =>
      apply (flowstoWF ℓ1 ℓ2); [FindTermHasSort'' | FindTermHasSort'']
    | [ |- ⊢wff (canRead ?p ?ℓ) ] =>
      apply (canReadWF p ℓ); [FindTermHasSort'' | FindTermHasSort'']
    | [ |- ⊢wff (canWrite ?p ?ℓ) ] =>
      apply (canWriteWF p ℓ); [FindTermHasSort'' | FindTermHasSort'']
    | [ |- ⊢wff (?p □ ⟨ ?ℓ ⟩ ?phi) ] =>
      apply (saysWF p ℓ phi); [FindTermHasSort'' | FindTermHasSort'' |
                               FindWellFormedFormula']
    | [ |- ⊢wff (rel ?R ?args) ] =>
      apply (RelWF R args); FindArgsHaveSorts''
    | [ |- ⊢wff (?phi & ?psi) ] =>
      apply (andWF phi psi); [FindWellFormedFormula' | FindWellFormedFormula']
    | [ |- ⊢wff (?phi ⊕ ?psi) ] =>
      apply (orWF phi psi); [FindWellFormedFormula' | FindWellFormedFormula']
    | [ |- ⊢wff (?phi ==⟨?l⟩> ?psi) ] =>
      apply (impliesWF phi psi l); [FindWellFormedFormula' | FindTermHasSort'' | FindWellFormedFormula']
    | [ |- ⊢wff (∀ ?s; ?phi) ] =>
      eapply (forallWF phi); FindWellFormedFormula'
    | [ |- ⊢wff (∃ ?s; ?phi) ] =>
      eapply (existsWF phi); FindWellFormedFormula'
    | [ wff' : ⊢wff ?phi |- ⊢wff ?psi ] =>
      apply (UnifyWFF phi psi); [FindFormulaEquality | FindWellFormedFormula']
    end.

  Module FindWFF'Tests.

    Lemma FindWFF'Test1 : forall (phi : flafolFormula), ⊢wff phi -> ⊢wff phi.
    Proof.
      intros. FindWellFormedFormula'.
    Qed.

    Lemma FindWFF'Test2 : ⊢wff TT.
    Proof.
      FindWellFormedFormula'.
    Qed.

    Lemma FindWFF'Test3  : ⊢wff FF.
    Proof.
      FindWellFormedFormula'.
    Qed.

    Lemma FindWFF'Test4 : forall (label1 label2 : flafolTerm),
        ⊢s label1 ::: Label -> ⊢s label2 ::: Label ->
        ⊢wff (label1 ⊑ label2).
    Proof.
      intros. FindWellFormedFormula'.
    Qed.

    Lemma FindWFF'Test5 : forall (p label : flafolTerm) (phi : flafolFormula),
        ⊢s p ::: Principal -> ⊢s label ::: Label -> ⊢wff phi ->
        ⊢wff (p □ ⟨ label ⟩ phi).
    Proof.
      intros; FindWellFormedFormula'.
    Qed.

    Lemma FindWFF'Test6 : forall (R : relSym) (t1 t2 : flafolTerm) (sigma rho : sort),
        relTypes R = [sigma; rho] -> ⊢s t1 ::: sigma -> ⊢s t2 ::: rho ->
        ⊢wff (rel R [t1; t2]).
    Proof.
      intros. FindWellFormedFormula'.
    Qed.

    Lemma FindWFF'Test7 : forall (phi psi : flafolFormula),
        ⊢wff phi -> ⊢wff psi -> ⊢wff (phi & psi).
    Proof.
      intros. FindWellFormedFormula'.
    Qed.
    Lemma FindWFF'Test8 : forall (phi psi : flafolFormula),
        ⊢wff phi -> ⊢wff psi -> ⊢wff (phi ⊕ psi).
    Proof.
      intros. FindWellFormedFormula'.
    Qed.
    Lemma FindWFF'Test9 : forall (phi psi : flafolFormula) (l : flafolTerm),
        ⊢wff phi -> ⊢wff psi -> ⊢s l ::: Label -> ⊢wff (phi ==⟨l⟩> psi).
    Proof.
      intros. FindWellFormedFormula'.
    Qed.

    Lemma FindWFF'Test12 : forall (phi psi : flafolFormula),
        ⊢wff phi -> phi = psi -> ⊢wff psi.
    Proof.
      intros. FindWellFormedFormula'.
    Qed.
  End FindWFF'Tests.
  End WellFormedFormula'.
      