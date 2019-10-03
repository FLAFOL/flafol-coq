Require Export Term.
Require Export Formula.
Require Export SignedSubformula.
Require Export Sequent.

Require Import Base.Lists.
Require Import Base.Permutation.
Require Import Tactics.FormulaEquality.
Require Import Tactics.TermEquality.
Require Import Tactics.WellFormedFormulaNoProofs.
Require Import Tactics.TermHasSortNoFormulas.

Module Type Consistency (G : GroundInfo) (GTerm : Term G) (GFormula : Formula G GTerm)
       (TE : TermEquality G GTerm) (FE : FormulaEquality G GTerm GFormula TE)
       (SSFormula : SignedSubformula G GTerm GFormula TE FE)
       (THS : TermHasSort'' G GTerm TE)
       (WFF : WellFormedFormula' G GTerm TE THS GFormula FE)
       (PF : Sequent G GTerm GFormula TE FE THS WFF).
  Import G. Import GTerm. Import GFormula. Import SSFormula. Import PF.
  Import ListNotations. Import THS. Import WFF. 


  Inductive Falsy : flafolFormula -> Prop :=
    falseFalsy : Falsy FF
  | saysFalsy : forall p labl phi, Falsy phi -> Falsy (p □ ⟨ labl ⟩ phi).

  Hint Constructors Falsy.
  
  Theorem FalsySubst' : forall (x : var) (t : flafolTerm) (phi : flafolFormula),
      Falsy phi -> Falsy (phi f[x ↦ t]).
  Proof.
    intros x t phi H; induction phi; inversion H; simpl; constructor; auto.
  Qed.

  Theorem FalsySubst'' : forall (x : var) (t : flafolTerm) (phi : flafolFormula),
      Falsy (phi f[x ↦ t]) -> Falsy phi.
  Proof.
    intros x t phi H; induction phi; inversion H; simpl; try (constructor; auto).
    all: destruct (varEqDec x v); inversion H1.
    all: inversion H0.
  Qed.

  Theorem FalsySubst : forall (x : var) (t : flafolTerm) (phi : flafolFormula),
      Falsy phi <-> Falsy (phi f[ x ↦ t]).
  Proof.
    intros x t phi; split; [apply FalsySubst' | apply FalsySubst''].
  Qed.
  
  Open Scope formula_scope. Open Scope proof_scope.

  Ltac PositiveConsistency :=
    repeat match goal with
           | [ H : @InBool Belief BeliefEqDec ?a ?l = true |- _ ] =>
             match goal with
             | [_ : In ?a ?l |- _ ] => fail 1
             | _ => pose proof ((proj1 InBoolSpec) H)
             end
           | [ H :In ?a ?l |- _ ] =>
             match goal with
             | [ _ : InBool BeliefEqDec ?a ?l = true |- _ ] => fail 1
             | _ => pose proof ((proj2 InBoolSpec) H)
             end
           | [ H : _ ⊢[ _ ] (_ ⊑ _) @ _ |- _ ] => clear H
           | [ H : _ ⊢[ _ ] (canRead _ _) @ _ |- _ ] => clear H
           | [ H : _ ⊢[ _ ] (canWrite _ _) @ _ |- _ ] => clear H
           | [ IH : (forall (m0 : Modality) (phi0 psi0 : flafolFormula),
                        Path (phi0 @ m0) ?Gamma = true -> (psi0 s: Neg) ≤s (phi0 s: Neg) -> ~ Falsy psi0) ->
                    Falsy ?chi -> False,
                    H : ?Gamma ⊢[ _ ] ?chi @ _
               |- False] =>
             apply IH; auto
           | [ H : In _ (?Delta ++ ?Gamma) |- _ ] => apply in_app_or in H; destruct H
           | [ H : In _ (_ :: _) |- _ ] => destruct H
           | [ H0 : (forall (m0 : Modality) (phi0 psi0: flafolFormula),
                        Path (phi0 @ m0) (?Delta ++ _ :: ?Gamma) ->
                        (psi0, Neg) ≤s (phi0, Neg) -> ~ Falsy psi0),
                    H1 : Path (?phi1 @?m1) ?Delta,
                         H2 : (?psi1, Neg) ≤s (?phi1, Neg)
               |- ~ Falsy ?psi1 ] => 
             apply (H0 m1 phi1); [apply in_or_app; left | ]; auto
           | [ H0 : (forall (m0 : Modality) (phi0 psi0 : flafolFormula),
                        Path (phi0 @ m0) (?Delta ++ _ :: ?Gamma) ->
                        (psi0, Neg) ≤s (phi0, Neg) -> ~ Falsy psi0),
                    H1 : Path (?phi1 @ ?m1) ?Gamma,
                         H2 : (?psi1, Neg) ≤s (?phi1, Neg)
               |- ~ Falsy ?psi1 ] =>
             apply (H0 m1 phi1); [apply in_or_app; right; right | ]; auto
           | [ H0 : (forall (m0 : Modality) (phi0 psi0 : flafolFormula),
                        Path (phi0 @ m0) (?Delta ++ ((?f ?phi ?psi) @ ?m) :: ?Gamma) ->
                        (psi0, Neg) ≤s (phi0, Neg) -> ~ Falsy psi0),
                    H1 : (?phi @ ?m) = (?phi1 @ ?m1),
                         H2 : (?psi1, Neg) ≤s (?phi1, Neg)
               |- ~ Falsy ?psi1] =>
             let H3 := fresh "H" in
             let H4 := fresh "H" in
             assert (m = m1) as H3 by (inversion H1; auto);
             assert (phi = phi1) as H4 by (inversion H1; auto);
             apply (H0 m (f phi psi)); [apply in_or_app; right; left; auto | ];
             apply SSTrans with (psi := phi s: Neg);
             [rewrite H4; auto | constructor]
           | [ H0 : (forall (m0 : Modality) (phi0 psi0 : flafolFormula),
                        Path (phi0 @ m0) (?Delta ++ ((?f ?phi ?psi) @ ?m) :: ?Gamma) ->
                        (psi0, Neg) ≤s (phi0, Neg) -> ~ Falsy psi0),
                    H1 : (?psi @ ?m) = (?phi1 @ ?m1),
                         H2 : (?psi1, Neg) ≤s (?phi1, Neg)
               |- ~ Falsy ?psi1] =>
             let H3 := fresh "H" in
             let H4 := fresh "H" in
             assert (m = m1) as H3 by (inversion H1; auto);
             assert (psi = phi1) as H4 by (inversion H1; auto);
             apply (H0 m (f phi psi)); [apply in_or_app; right; left; auto | ];
             apply SSTrans with (psi := psi s: Neg);
             [rewrite H4; auto | constructor]
           | [ H0 : (forall (m0 : Modality) (phi0 psi0: flafolFormula),
                        Path (phi0 @ m0) (?Delta ++ ((?f ?phi ?psi) @ ?m) :: ?Gamma) ->
                        (psi0, Neg) ≤s (phi0, Neg) -> ~ Falsy psi0),
                    H1 : ((?f ?phi ?psi) @ ?m ) = (?phi1 @ ?m1),
                         H2 : (?psi0, Neg) ≤s (?phi1, Neg)
               |- ~ Falsy ?psi1] =>
             let H3 := fresh "H" in
             let H4 := fresh "H" in
             assert (m = m1) as H3 by (inversion H1; auto);
             assert (f phi psi = phi1) as H4 by (inversion H1; auto);
             apply (H0 m (f phi psi)); [apply in_or_app; right; left; auto | ];
             rewrite H4; auto
           | [ H0 : (forall (m0 : Modality) (phi0 psi0: flafolFormula) pc,
                        Path (phi0 @ m0) (?Delta ++ ((?f ?x ?phi) @ ?m) :: ?Gamma) ->
                        (psi0, Neg) ≤s (phi0, Neg) -> ~ Falsy psi0),
                    H1 : (?phi @ ?m) = (?phi1 @ ?m1),
                         H2 : (?psi0, Neg) ≤s (?phi1, Neg)
               |- ~ Falsy ?psi1] =>
             let H3 := fresh "H" in
             let H4 := fresh "H" in
             assert (m = m1) as H3 by (inversion H1; auto);
             assert (phi = phi1) as H4 by (inversion H1; auto);
             apply (H0 m (f x phi)); [apply in_or_app; right; left; auto | ];
             apply SSTrans with (psi := phi s: Neg);
             [rewrite H4; auto | constructor]; auto
           | [ H0 : (forall (m0 : Modality) (phi0 psi0: flafolFormula),
                        Path (phi0 @ m0) (?Delta ++ ((?f ?x ?phi) @ ?m) :: ?Gamma) ->
                        (psi0, Neg) ≤s (phi0, Neg) -> ~ Falsy psi0),
                    H1 : ((?phi f[?x ↦ ?t]) @ ?m) = (?phi1 @ ?m1),
                         H2 : (?psi0, Neg) ≤s (?phi1, Neg)
               |- ~ Falsy ?psi1] =>
             let H3 := fresh "H" in
             let H4 := fresh "H" in
             assert (m = m1) as H3 by (inversion H1; auto);
             assert (phi f[x ↦ t] = phi1) as H4 by (inversion H1; auto);
             apply (H0 m (f x phi)); [apply in_or_app; right; left; auto | ];
             apply SSTrans with (psi := (phi f[x ↦ t]) s: Neg);
             [rewrite H4; auto | constructor]; auto
           | [ |- forall _, _ ] => intro
           end.

  Hint Constructors SignedSubformulaOf.

  Definition phiBelief (b : Belief) : flafolFormula :=
    match b with
    | mkBelief phi m => phi
    end.



  Theorem PositiveConsistency' : forall {Gamma : Context} {b : Belief},
      (forall m phi, Path (phi @ m) Gamma -> ~((FF s: Neg) ≤s (phi s: Neg))) -> Gamma ⊢ b -> (phiBelief b <> FF).
  Proof.
    intros Gamma b H pf.
    induction pf; subst; auto; try (simpl; discriminate).
    all: try (repeat match goal with
                     | [ H : (forall (m : Modality) (phi : flafolFormula), Path (phi @ m) ?Gamma -> ~ (FF, Neg) ≤s (phi, Neg)), p : Path (?phi @ ?m) ?Gamma |- ~ (FF, Neg) ≤s (?phi, Neg) ] => apply (H m phi p) 
                     | [ H : ?P -> ?Q |- ?Q ] => apply H; intros
                     | [ H : Path ?b1 (_ :: ?Gamma) |- _] => apply PathToIn in H; destruct H
                     | [ H : In ?b ?Gamma |- _ ] => apply (InToPath BeliefEqDec) in H
                     | [ H : ?phi @ ?m1 = ?psi @ ?m2 |- _ ] =>
                       match goal with
                       | [ _ : phi = psi, _ : m1 = m2 |- _ ] => fail 1
                       | _ => inversion H
                       end
                     end) .
    - destruct b. intro. simpl in H0. apply (H m f p0).
      rewrite H0; auto.
    - exfalso; apply (H m FF p1); auto.
    - intro Hphi0. apply (H m (phi & psi) pth).
      inversion H0; eapply SSTrans; eauto. 
    - intro Hphi0; apply (H m (phi & psi) pth).
      inversion H0; eapply SSTrans; eauto.
    - intro Hphi0; apply (H m (phi ⊕ psi) pth).
      inversion H0; eapply SSTrans; eauto.
    - intro H1; apply (H m (phi ==⟨ l ⟩> psi) pth).
      inversion H2; eapply SSTrans; eauto.
    - intro Hphi0; apply (H m (∀ sigma; phi) pth).
      eapply SSTrans; eauto.
    - intro Hphi0; apply (H m (∃ VarSort y; phi) pth).
      eapply SSTrans; eauto.
    - intro Hphi0; apply (H m (p □ ⟨ lab ⟩ phi) pth).
      pose proof (provenProperContext pf).
      apply ConsProperContext in H1.
      destruct H1.
      inversion H1. inversion H5.
      inversion H2; eapply SSTrans; eauto.
    - rewrite <- H2. apply H with (m := CollapseDoubleInModality pth); auto.
    - rewrite <- H2. apply H with (m := m); auto.
    - rewrite <- H2. apply H with (m := m); auto.
    - rewrite <- H2; apply H with (m := m); auto.
  Qed.

  Theorem PositiveConsistency : forall (Gamma : Context) (m : Modality),
      (forall m' phi, Path (phi @ m') Gamma -> ~ ((FF s: Neg) ≤s (phi s: Neg))) ->
      Gamma ⊢ FF @ m -> False.
  Proof.
    intros Gamma m H H0.
    eapply @PositiveConsistency' with (b := FF @ m); eauto.
  Qed.
  
  Theorem Consistency : forall m, [] ⊢ FF @ m -> False.
  Proof.
    intros m H; eapply PositiveConsistency; eauto.
    intros m' phi H0; inversion H0.
  Qed.

End Consistency.