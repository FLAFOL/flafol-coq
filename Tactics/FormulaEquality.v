Require Export Tactics.TermEquality.
Require Export Logic.Formula.
Require Import Tactics.Equality.
Require Import Coq.Lists.List.

Import ListNotations.
Module Type FormulaEquality(G : GroundInfo)(GT : Term G)(GF : Formula G GT)(TE : TermEquality G GT).
  Import G. Import GT. Import GF. Import TE.

  Lemma UnifyFlowsTo : forall {t1 u1 t2 u2 : flafolTerm},
      t1 = t2 -> u1 = u2 -> flowsto t1 u1 = flowsto t2 u2.
  Proof.
    intros; rewrite H; rewrite H0; auto.
  Qed.

  Lemma UnifyRel : forall {R1 R2 : relSym} {args1 args2 : list flafolTerm},
      R1 = R2 -> args1 = args2 -> rel R1 args1 = rel R2 args2.
  Proof.
    intros; rewrite H; rewrite H0; auto.
  Qed.

  Lemma UnifyAnd : forall {phi1 psi1 phi2 psi2 : flafolFormula},
      phi1 = phi2 -> psi1 = psi2 -> and phi1 psi1 = and phi2 psi2.
  Proof.
    intros; rewrite H; rewrite H0; auto.
  Qed.

  Lemma UnifyOr : forall {phi1 psi1 phi2 psi2 : flafolFormula},
      phi1 =phi2 -> psi1 = psi2 -> or phi1 psi1 = or phi2 psi2.
  Proof.
    intros phi1 psi1 phi2 psi2 H H0; rewrite H; rewrite H0; auto.
  Qed.

  Lemma UnifyImplies : forall {phi1 psi1 phi2 psi2 : flafolFormula} {l1 l2 : flafolTerm},
      phi1 =phi2 -> psi1 = psi2 -> l1 = l2 ->
      phi1 ==⟨l1⟩> psi1 = phi2 ==⟨l2⟩> psi2.
  Proof.
    intros phi1 psi1 phi2 psi2 l1 l2 H H0 H1;
      rewrite H; rewrite H0; rewrite H1; auto.
  Qed.

  Lemma UnifyForall : forall {s : G.sort} {phi psi : flafolFormula},
      phi = psi -> flafolForall s phi = flafolForall s psi.
  Proof.
    intros s phi psi H0; rewrite H0; auto.
  Qed.

  Lemma UnifyExists : forall {s : G.sort} {phi psi : flafolFormula},
      phi = psi -> flafolExists s phi = flafolExists s psi.
  Proof.
    intros s phi psi H0; rewrite H0; auto.
  Qed.

  Lemma UnifySays : forall {p q ell ell' : flafolTerm} {phi psi : flafolFormula},
      p = q -> ell = ell' -> phi = psi  -> says p ell phi = says q ell' psi.
  Proof.
    intros p q ell ell' phi psi H H0 H1; rewrite H; rewrite H0; rewrite H1; auto.
  Qed.

  Lemma UnifyCanRead : forall {p q ell ell' : flafolTerm},
      p = q -> ell = ell' -> canRead p ell = canRead q ell'.
  Proof.
    intros p q ell ell' H H0; rewrite H; rewrite H0; auto.
  Qed.

  Lemma UnifyCanWrite : forall {p q ell ell' : flafolTerm},
      p = q -> ell = ell' -> canWrite p ell = canWrite q ell'.
  Proof.
    intros p q ell ell' H H0; rewrite H; rewrite H0; auto.
  Qed.

  Ltac FindFormulaEquality := idtac.
  Ltac FindFormulaEquality' l :=
    match goal with
    | [ |- ?phi = ?phi ] => reflexivity
    | [ e : ?phi = ?psi |- ?phi = ?psi ] => exact e
    | [ e : ?psi = ?phi |- ?phi = ?psi ] => exact (eq_sym e)
    | [ e : ?phi = ?chi |- ?phi = ?psi ] =>
      NotInList chi l; transitivity chi; [exact e | FindFormulaEquality' constr:(chi :: l)]
    | [ e : ?chi = ?phi |- ?phi = ?psi ] =>
      NotInList chi l; transitivity chi;
      [exact (eq_sym e) | FindFormulaEquality' constr:(chi :: l)]
    | [ |- (?t1 ⊑ ?u1) = (?t2 ⊑ ?u2) ] =>
      apply UnifyFlowsTo; [FindTermEquality | FindTermEquality]
    | [ |- (rel ?R1 ?args1) = (rel ?R2 ?args2) ] =>
      apply UnifyRel; [FindEquality | FindArgsEquality]
    | [ |- (?phi1 & ?psi1) = (?phi2 & ?psi2) ] =>
      apply UnifyAnd; [FindFormulaEquality | FindFormulaEquality]
    | [ |- (?phi1 ⊕ ?psi1) = (?phi2 ⊕ ?psi2) ] =>
      apply UnifyOr; [FindFormulaEquality | FindFormulaEquality]
    | [ |- (?phi1 ==⟨?l1⟩> ?psi1) = (?phi2 ==⟨?l2⟩> ?psi2) ] =>
      apply UnifyImplies; [FindFormulaEquality | FindTermEquality | FindTermEquality]
    | [ |- (∀ ?s; ?phi) = (∀ ?s'; ?psi) ] =>
      apply UnifyForall; [FindEquality | FindFormulaEquality]
    | [ |- (∃ ?s; ?phi) = (∃ ?s'; ?psi) ] =>
      apply UnifyExists; [FindEquality | FindFormulaEquality]
    | [ |- (says ?p ?ℓ ?phi) = (says ?q ?ℓ' ?psi) ] =>
      apply UnifySays; [FindTermEquality | FindTermEquality | FindFormulaEquality]
    | [ |- (canRead ?p ?ℓ) = (canRead ?q ?ℓ') ] =>
      apply UnifyCanRead; [FindTermEquality | FindTermEquality ]
    | [ |- (canWrite ?p ?ℓ) = (canWrite ?q ?ℓ') ] =>
      apply UnifyCanWrite; [FindTermEquality | FindTermEquality ]
    end.

  Ltac FindFormulaEquality ::= FindFormulaEquality' constr:(@nil flafolFormula).

  Module FormulaEqualityTests.
    Lemma FormulaEqualityTest1 : forall (phi : flafolFormula), phi = phi.
    Proof.
      intros; FindFormulaEquality.  
    Qed.

    Lemma FormulaEqualityTest2 : forall (phi u : flafolFormula), phi = u -> u = phi.
    Proof.
      intros phi u H; FindFormulaEquality.
    Qed.

    Lemma FormulaEqualityTest3 : forall (phi psi chi : flafolFormula), phi = psi -> psi = chi -> phi = chi. 
    Proof.
      intros phi psi chi H H0; FindFormulaEquality.
    Qed.

    Lemma FormulaEqualityTest4 : forall (phi psi chi upsilon : flafolFormula), phi = psi -> phi = chi -> chi = upsilon -> phi = upsilon.
    Proof.
      intros; FindFormulaEquality.
    Qed.

    Lemma FormulaEqualityTest5 : forall (phi psi chi upsilon : flafolFormula), phi = upsilon -> phi = psi -> upsilon = chi -> phi = chi.
    Proof.
      intros; FindFormulaEquality.
    Qed.

    Lemma FormulaEqualityTest6 : forall (phi psi chi upsilon : flafolFormula), upsilon = phi -> phi = psi -> chi = upsilon -> phi = chi.
    Proof.
      intros; FindFormulaEquality.
    Qed.

    Lemma FormulaEqualityTest7 : forall (t1 t2 u1 u2 : flafolTerm),
        t1 = t2 -> u1 = u2 -> t1 ⊑ u1 = t2 ⊑ u2.
    Proof.
      intros; FindFormulaEquality.
    Qed.

    Lemma FormulaEqualityTest8 : forall (R1 R2 : relSym) (t1 t2 u1 u2 : flafolTerm),
        R1 = R2 -> t1 = t2 -> u1 = u2 -> rel R1 [t1; u1] = rel R2 [t2; u2].
    Proof.
      intros; FindFormulaEquality.
    Qed.

    Lemma FormulaEqualityTest9 : forall (phi psi chi upsilon : flafolFormula),
        phi = psi -> chi = upsilon -> phi & chi = psi & upsilon.
    Proof.
      intros; FindFormulaEquality.
    Qed.
    
  End FormulaEqualityTests.    

End FormulaEquality.
