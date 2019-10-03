Require Import Sequent.
Require Export Term. (* We use it enough below to just go ahead and import it directly. *)
Require Export Formula.
Require Export Cut.

Require Import Base.Lists.
Require Import Base.Permutation.
Require Import Base.Option.
Require Import Tactics.FormulaEquality.
Require Import Tactics.TermEquality.
Require Import Tactics.WellFormedFormulaNoProofs.
Require Import Tactics.TermHasSortNoFormulas.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.Wellfounded.Inclusion.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Wf.
Require Import Coq.Arith.Wf_nat.

Open Scope string_scope.

Module Type Speaksfor (G : GroundInfo) (GTerm : Term G) (GFormula : Formula G GTerm)
       (TE : TermEquality G GTerm) (FE : FormulaEquality G GTerm GFormula TE)
       (THS : TermHasSort'' G GTerm TE)
       (WFF : WellFormedFormula' G GTerm TE THS GFormula FE) (SEQ : Sequent G GTerm GFormula TE FE THS WFF)
       (CT : CutTact G GTerm GFormula TE FE THS WFF SEQ) (NF : NormalForm G GTerm GFormula TE FE THS WFF SEQ CT)
       (C : Cut G GTerm GFormula TE FE THS WFF SEQ CT NF).
  Import G. Import GTerm. Import GFormula. Import ListNotations.
  Import THS. Import WFF. Import SEQ. Import C.

  Reserved Notation "Gamma ⊢sf g1 ⇛ g2" (at level 25).
  Inductive speaksfor : Context -> Modality -> Modality -> Set :=
  | ReflSF : forall Gamma g, ProperContext Gamma -> ProperModality g -> Gamma ⊢sf g ⇛ g
  | ExtSF : forall Gamma g1 g2 p l,
      ⊢s p ::: Principal -> ⊢s l ::: Label ->
      Gamma ⊢sf g1 ⇛ g2 -> Gamma ⊢sf g1 ⋅ p⟨l⟩ ⇛ g2 ⋅ p⟨l⟩
  | SelfLSF : forall Gamma g p l,
      ProperContext Gamma -> ProperModality g -> ⊢s p ::: Principal -> ⊢s l ::: Label ->
      Gamma ⊢sf g ⋅ p⟨l⟩ ⇛ g ⋅ p⟨l⟩ ⋅ p⟨l⟩
  | SelfRSF : forall Gamma g p l,
      ProperContext Gamma -> ProperModality g -> ⊢s p ::: Principal -> ⊢s l ::: Label ->
      Gamma ⊢sf g ⋅ p⟨l⟩ ⋅ p⟨l⟩ ⇛ g ⋅ p⟨l⟩
  | VarSF0 : forall Gamma l l',
      Gamma ⊢ l ⊑ l' @ ⟨l'⟩ -> Gamma ⊢sf ⟨l⟩ ⇛ ⟨l'⟩
  | VarSF : forall Gamma g p l l',
      Gamma ⊢ l ⊑ l' @ g ⋅ p⟨l'⟩ -> Gamma ⊢sf g ⋅ p⟨l⟩ ⇛ g ⋅ p⟨l'⟩
  | FwdSF : forall Gamma g p q l,
      Gamma ⊢ canRead q l @ g ⋅ p⟨l⟩ -> Gamma ⊢ canWrite p l @ g ⋅ q⟨l⟩ ->
      Gamma ⊢sf g ⋅ p⟨l⟩ ⇛ g ⋅ q⟨l⟩
  | TransSF : forall Gamma g1 g2 g3,
      Gamma ⊢sf g1 ⇛ g2 -> Gamma ⊢sf g2 ⇛ g3 -> Gamma ⊢sf g1 ⇛ g3
  where "Gamma ⊢sf g1 ⇛ g2" := (speaksfor Gamma g1 g2).

  Lemma sf_proper : forall (Gamma : Context) (g1 g2 : Modality),
      Gamma ⊢sf g1 ⇛ g2 -> ProperContext Gamma /\ ProperModality g1 /\ ProperModality g2.
  Proof.
    intros Gamma g1 g2 H.
    induction H;
      repeat match goal with
             | [ |- _ /\ _ ] => split
             | [ H : ?P |- ?P ] => exact H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ |- ProperModality (_ ⋅ _⟨_⟩)] => apply simProper
             | [ H : ?Gamma ⊢ _ |- _ ] =>
               match goal with
               | [ _ : ProperContext Gamma |- _] => fail 1
               | _ => assert (ProperContext Gamma) by (apply (provenProperContext H))
               end
             | [ H : _ ⊢ ?b |- _ ] =>
               match goal with
               | [ _ : ProperBelief b |- _ ] => fail 1
               | _ => assert (ProperBelief b) by (apply (provenProperBelief H))
               end
             | [ H : ProperBelief (?phi @ ?m) |- _ ] =>
               match goal with
               | [_ : ⊢wff phi |- _] => fail 1
               | _ => assert (⊢wff phi) by (apply (@ProperBeliefPhi m phi H))
               end
             | [ H : ProperBelief (?phi @ ?m) |- _ ] =>
               match goal with
               | [_ : ProperModality m |- _] => fail 1
               | _ => assert (ProperModality m) by (apply (@ProperBeliefM m phi H))
               end
             | [ H : ProperModality (?g ⋅ ?p ⟨ ?l ⟩) |- _ ] =>
               match goal with
               | [ _ : ProperModality g, _ : ⊢s p ::: Principal, _ : ⊢s l ::: Label |- _ ] =>
                 fail 1
               | _ =>
                 let H1 := fresh in
                 let H2 := fresh in
                 remember (@ConsProperModality p l g H) as H1;
                   destruct H1 as [H1 H2]; destruct H2
               end
             end.
    inversion H0; inversion H4; constructor; auto.
    inversion H1; auto.
  Qed.

  Definition ElimSF : forall (Gamma : Context) (phi : flafolFormula) (g1 g2 : Modality),
      Gamma ⊢ phi @ g1 -> Gamma ⊢sf g1 ⇛ g2 -> Gamma ⊢ phi @ g2.
  Proof.
    intros Gamma phi g1 g2 H H0.
    generalize dependent phi.
    induction H0; intros.
    - auto.
    - apply SaysR_inversion; apply IHspeaksfor; apply saysR; auto.
    - remember (hereDouble g0 p l).
      apply modalityExpandR with (pth := p2). rewrite Heqp2. simpl. auto.
    - remember (hereDouble g0 p l).
      assert (g0 ⋅ p⟨l⟩ = CollapseDoubleInModality p2)
        by (rewrite Heqp2; simpl; reflexivity).
      rewrite H0. apply modalityCollapseR; auto.
    - assert (⟨l'⟩ = ReplaceLabelInModality (⟨l⟩) l l' (hereGLab l)) by auto.
      rewrite H0; apply RVariance; auto.
    - remember (hereSimLab g0 p l).
      assert (g0 ⋅ p⟨l'⟩ = ReplaceLabelInModality (g0 ⋅ p⟨l⟩) l l' p1)
        by (rewrite Heqp1; simpl; reflexivity).
      rewrite H0. apply RVariance; auto.
      rewrite Heqp1. simpl. auto.
    - remember (hereSimP g0 p l).
      assert (g0 ⋅ q⟨l⟩ = ReplacePrinInModality p2 q)
        by (rewrite Heqp2; simpl; reflexivity).
      rewrite H0. apply FwdR; auto; rewrite Heqp2; unfold FwdModality; simpl; auto.
    - apply IHspeaksfor2. apply IHspeaksfor1. auto.
  Defined.

  Definition SFWeak : forall {Gamma Delta : Context} {g1 g2 : Modality},
      ProperContext Delta -> Gamma ⊢sf g1 ⇛ g2 ->
      (forall b : Belief, Path b Gamma -> Path b Delta) ->
      Delta ⊢sf g1 ⇛ g2.
  Proof.
    intros Gamma Delta g1 g2 pctxtΔ H H0.
    generalize dependent Delta. induction H; intros Delta pctxtΔ ΓΔ;
                              try (constructor; auto; fail).
    - apply VarSF0. apply Weakening with (Delta0 := Delta) in p; auto.
    - apply VarSF. apply Weakening with (Delta0 := Delta) in p0; auto.
    - apply FwdSF.
      apply Weakening with (Delta0 := Delta) in p0; auto. 
      apply Weakening with (Delta0 := Delta) in p1; auto.
    - apply TransSF with (g2 := g2); auto.
  Defined.

  Definition SFModalityExt : forall {Gamma : Context} {m1 m2 : Modality} {mr : ModalityResidual},
      Gamma ⊢sf m1 ⇛ m2 -> ProperModalityResidual mr ->
      Gamma ⊢sf (ModalityCombine m1 mr) ⇛ (ModalityCombine m2 mr).
  Proof.
    intros Gamma m1 m2 mr H H0. generalize dependent m2. revert Gamma m1.

    induction mr; intros Gamma m1 m2 H; [simpl; exact H|].
    destruct a as [p l]. simpl in *.
    apply ProperModalityResidualConsInv in H0. destruct H0 as [H0 H1]; destruct H1.
    apply IHmr; auto.
    apply ExtSF; auto.
  Defined.
    
  Definition SFCollapseDouble : forall {Gamma : Context} {m : Modality}
                               (pth : PathToDoubleInModality m),
      ProperContext Gamma -> ProperModality m ->
      Gamma ⊢sf m ⇛ (CollapseDoubleInModality pth).
  Proof.
    intros Gamma m pth; revert Gamma.
    induction pth; intros Gamma pctxt pmod.
    simpl. apply SelfRSF; auto; inversion pmod; auto.
    inversion H2; auto.
    simpl. apply ExtSF; [| | apply IHpth]; inversion pmod; auto.
  Defined.

  Definition SFExpandDouble : forall {Gamma : Context} {m : Modality}
                                (pth : PathToDoubleInModality m),
      ProperContext Gamma -> ProperModality m ->
      Gamma ⊢sf (CollapseDoubleInModality pth) ⇛ m.
  Proof.
    intros Gamma m pth; revert Gamma. induction pth; intros Gamma pctxt pmod.
    simpl. apply SelfLSF; auto; inversion pmod; auto.
    inversion H2; auto.
    simpl. apply ExtSF; [| | apply IHpth]; inversion pmod; auto.
  Defined.

  Definition SFReplaceLabel : forall {Gamma : Context} {m : Modality} {l1 l2 : flafolTerm}
                                (pth : PathToLabelInModality m l1),
      ProperModality m ->
      Gamma ⊢ l1 ⊑ l2 @ (VarModality pth l2) ->
      Gamma ⊢sf m ⇛ ReplaceLabelInModality m l1 l2 pth.
  Proof.
    intros Gamma m l1 l2 pth H H0.
    destruct (PrincipalAtLabel pth) eqn:e.
    - rename f into p.
      destruct (ModalityBeforeLabel pth) eqn:e1;
        [| apply NilPrincipalModalityLabel in e1;
           pose proof (eq_trans (eq_sym e1) e) as H1; inversion H1].
      erewrite ModalityRestitchLabel at 1; eauto.
      erewrite ModalityRestitchReplaceLabel; eauto.
      apply SFModalityExt.
      erewrite RestitchVarModality with (p0 := p) (m' := m0) in H0; auto.
      apply VarSF; auto.
      apply ModalityAfterLabelProper; auto.
    - assert (ModalityBeforeLabel pth = None) as e0
          by (rewrite NilPrincipalModalityLabel in e; exact e).
      erewrite ModalityRestitchLabelNil at 1; eauto.
      erewrite ModalityRestitchReplaceLabelNil; eauto.
      apply SFModalityExt.
      rewrite RestitchVarModalityNil in H0; auto.
      apply VarSF0; auto.
      apply ModalityAfterLabelProper; auto.
  Defined.

  Definition SFReplacePrin : forall {Gamma : Context} {m : Modality} {p q : flafolTerm}
                               (pth : PathToPrinInModality m p),
      ProperModality m ->
      Gamma ⊢ canRead q (LabelAtPrin pth) @ FwdModality pth p ->
      Gamma ⊢ canWrite p (LabelAtPrin pth) @ FwdModality pth q ->
      Gamma ⊢sf m ⇛ ReplacePrinInModality pth q.
  Proof.
    intros Gamma m p q pth H H0 H1.
    rewrite ModalityRestitchPrin with (pth := pth) at 1.
    rewrite ModalityRestitchReplacePrin. apply SFModalityExt.
    apply FwdSF; auto.
    apply ModalityAfterPrinProper; auto.
  Defined.
  
  Inductive G_evidence : flafolFormula -> Modality -> Modality -> Set :=
  | TT_ev : forall (m : Modality), G_evidence TT m m
  | FF_ev : forall (m : Modality), G_evidence FF m m
  | varF_ev : forall (m : Modality) (X : formulaVar), G_evidence (varFormula X) m m
  | flowsto_ev : forall (m : Modality) (l1 l2 : flafolTerm), G_evidence (l1 ⊑ l2) m m
  | rel_ev : forall (m : Modality) (R : relSym) (args : list flafolTerm),
      G_evidence (rel R args) m m
  | canR_ev : forall (m : Modality) (p l : flafolTerm), G_evidence (canRead p l) m m
  | canW_ev : forall (m : Modality) (p l : flafolTerm), G_evidence (canWrite p l) m m
  | and_ev1 : forall (m1 m2 : Modality) (phi psi : flafolFormula),
      G_evidence phi m1 m2 -> G_evidence (phi & psi) m1 m2
  | and_ev2 : forall (m1 m2 : Modality) (phi psi : flafolFormula),
      G_evidence psi m1 m2 -> G_evidence (phi & psi) m1 m2
  | or_ev1 : forall (m1 m2 : Modality) (phi psi : flafolFormula),
      G_evidence phi m1 m2 -> G_evidence (phi ⊕ psi) m1 m2
  | or_ev2 : forall (m1 m2 : Modality) (phi psi : flafolFormula),
      G_evidence psi m1 m2 -> G_evidence (phi ⊕ psi) m1 m2
  | impl_ev : forall (m1 m2 : Modality) (phi psi : flafolFormula) (l : flafolTerm),
      G_evidence psi m1 m2 -> G_evidence (phi ==⟨l⟩> psi) m1 m2
  | fa_ev : forall (sigma : sort) (phi : flafolFormula) (t : flafolTerm) (x : var) (m1 m2 : Modality),
      VarSort x = sigma -> x ∉FVF phi -> x ∉FVT t -> x ∉FVM m1 -> ⊢s t ::: sigma -> lc_term t ->
      G_evidence (open_formula phi (varTerm x)) m1 m2 ->
      G_evidence (∀ sigma; phi) m1 (m2 mod[x ↦ t])
  | ex_ev : forall (sigma : sort) (phi : flafolFormula) (t : flafolTerm) (x : var) (m1 m2 : Modality),
      VarSort x = sigma -> x ∉FVF phi -> x ∉FVT t -> x ∉FVM m1 -> ⊢s t ::: sigma -> lc_term t ->
      G_evidence (open_formula phi (varTerm x)) m1 m2 ->
      G_evidence (∃ sigma; phi) m1 (m2 mod[x ↦ t])
  | says_ev : forall (m1 m2 : Modality) (p l : flafolTerm) (phi : flafolFormula),
      G_evidence phi (m1 ⋅ p⟨l⟩) m2 -> G_evidence (p □⟨l⟩ phi) m1 m2.


  Fixpoint G' (fuel : nat) (phi : flafolFormula) (m1 : Modality) (m2 : Modality) : Prop :=
    match fuel with
    | O => False
    | S remaining => 
      match phi with
      | TT => m1 = m2
      | FF => m1 = m2
      | varFormula x => m1 = m2
      | flowsto l1 l2 => m1 = m2
      | rel R args => m1 = m2
      | canRead p l => m1 = m2
      | canWrite p l => m1 = m2
      | and psi chi => G' remaining psi m1 m2 \/ G' remaining chi m1 m2
      | or psi chi => G' remaining psi m1 m2 \/ G' remaining chi m1 m2
      | psi ==⟨l⟩> chi => G' remaining chi m1 m2
      | flafolForall sigma psi =>
        exists t : flafolTerm, ⊢s t ::: sigma /\ lc_term t /\ G' remaining (open_formula psi t) m1 m2
      | flafolExists sigma psi =>
        exists t : flafolTerm, ⊢s t ::: sigma /\ lc_term t /\ G' remaining (open_formula psi t) m1 m2
      | says p l psi => G' remaining psi (m1 ⋅ p⟨l⟩) m2
      end
    end.

  Theorem G'_more_fuel_better : forall (phi : flafolFormula) (m1 m2 : Modality) (fuel1 fuel2 : nat),
      fuel1 < fuel2 -> G' fuel1 phi m1 m2 -> G' fuel2 phi m1 m2.
  Proof.
    intros phi m1 m2 fuel1.
    generalize phi m1 m2. clear phi m1 m2.
    induction fuel1; intros.
    inversion H0.
    destruct fuel2; [inversion H|]. simpl in *. destruct phi; auto.
    - destruct H0; [left | right]; apply IHfuel1; auto; apply Lt.lt_S_n; auto.
    - destruct H0; [left | right]; apply IHfuel1; auto; apply Lt.lt_S_n; auto.
    - apply IHfuel1; auto; apply Lt.lt_S_n; auto.
    - destruct H0 as [t Ht]; destruct Ht as [tsort Ht]; destruct Ht as [lc_t Ht];
        exists t; split; [|split]; auto; apply IHfuel1; auto; apply Lt.lt_S_n; auto.
    - destruct H0 as [t Ht]; destruct Ht as [tsort Ht]; destruct Ht as [lc_t Ht];
        exists t; split; [| split]; auto; apply IHfuel1; auto; apply Lt.lt_S_n; auto.
    - apply IHfuel1; auto; apply Lt.lt_S_n; auto.
  Qed.

  Theorem G'_at_least_as_much_fuel : forall (phi : flafolFormula) (m1 m2 : Modality) (fuel1 fuel2 : nat),
      fuel1 <= fuel2 -> G' fuel1 phi m1 m2 -> G' fuel2 phi m1 m2.
  Proof.
    intros phi m1 m2 fuel1 fuel2 H H0.
    destruct (Compare_dec.le_lt_eq_dec fuel1 fuel2 H).
    apply G'_more_fuel_better with (fuel1 := fuel1); auto.
    rewrite <- e; auto.
  Qed.

  Theorem G'_size_is_enough : forall (phi : flafolFormula) (m1 m2 : Modality),
      (exists fuel : nat, G' fuel phi m1 m2) -> G' (formula_size phi) phi m1 m2.
  Proof.
    intros phi; induction phi using OpeningInduction; intros.
    all: try (destruct H as [fuel HG]; destruct fuel as [|remaining]; [inversion HG; fail|]); simpl in *; try (auto; fail).
    - apply IHphi; exists remaining; auto.
    - destruct HG;
        [ left; apply G'_at_least_as_much_fuel with (fuel1 := formula_size phi1)
        | right; apply G'_at_least_as_much_fuel with (fuel1 := formula_size phi2)].
      -- apply PeanoNat.Nat.le_max_l.
      -- apply IHphi1; exists remaining; auto.
      -- apply PeanoNat.Nat.le_max_r.
      -- apply IHphi2; exists remaining; auto.
    - destruct HG;
        [ left; apply G'_at_least_as_much_fuel with (fuel1 := formula_size phi1)
        | right; apply G'_at_least_as_much_fuel with (fuel1 := formula_size phi2)].
      -- apply PeanoNat.Nat.le_max_l.
      -- apply IHphi1; exists remaining; auto.
      -- apply PeanoNat.Nat.le_max_r.
      -- apply IHphi2; exists remaining; auto.
    - apply G'_at_least_as_much_fuel with (fuel1 := formula_size phi2).
      apply PeanoNat.Nat.le_max_r.
      apply IHphi2; exists remaining; auto.
    - destruct H0 as [fuel HG]; destruct fuel as [|remaining]; [inversion HG |]; simpl in *.
      destruct HG as [t HG]; destruct HG as [tsort HG]; destruct HG as [lc_t HG].
      exists t; split; [|split]; auto. rewrite <- OpenFormulaSize with (t := t). apply H; auto.
      exists remaining; auto.
    - destruct H0 as [fuel HG]; destruct fuel as [|remaining]; [inversion HG |]; simpl in *.
      destruct HG as [t HG]; destruct HG as [tsort HG]; destruct HG as [lc_t HG].
      exists t; split; [|split]; auto. rewrite <- OpenFormulaSize with (t := t). apply H; auto.
      exists remaining; auto.
  Qed.
  Theorem G'_Proper : forall (phi : flafolFormula) (m1 m2 : Modality)( fuel : nat),
      ⊢wff phi -> ProperModality m1 -> G' fuel phi m1 m2 -> ProperModality m2.
  Proof.
    intro phi; induction phi using OpeningInduction; intros m1 m2 fuel well_formed pmod HG'.
    all: destruct fuel as [| remaining]; [inversion HG'|]; simpl in *.
    all: try (rewrite <- HG'; auto; fail).
    - apply IHphi with (m1 := m1 ⋅ p⟨lab⟩) (fuel := remaining); auto.
      inversion well_formed; auto.
      constructor; inversion well_formed; auto.
    - destruct HG'; [apply IHphi1 with (m1 := m1) (fuel := remaining)
                    | apply IHphi2 with (m1 := m1) (fuel := remaining)];
      inversion well_formed; auto.
    - destruct HG'; [apply IHphi1 with (m1 := m1) (fuel := remaining)
                    | apply IHphi2 with (m1 := m1) (fuel := remaining)];
      inversion well_formed; auto.
    - eapply IHphi2; inversion well_formed; eauto.
    - destruct HG' as [t HG']; destruct HG' as [tsort HG']; destruct HG' as [lc_t HG'].
      eapply H; eauto. inversion well_formed.
      specialize (H1 (freshVar (L ++ varsInFormula phi) sigma)).
      assert (~ In (freshVar (L ++ varsInFormula phi) sigma) L).
      intro Hcontra. apply freshVarNotIn with (vs := L ++ varsInFormula phi) (sigma := sigma).
      apply in_or_app; left; auto.
      specialize (H1 H3); clear H3.
      assert (⊢s varTerm (freshVar (L ++ varsInFormula phi) sigma) ::: sigma).
      erewrite <- freshVarSameSort. eapply varS.
      specialize (H1 H3); clear H3.
      remember (freshVar (L ++ varsInFormula phi) sigma) as x.
      assert (phi = phi f[x ↦ t])
      by (symmetry; apply notFreeInFormulaSubstEq;
          intro Hxϕ; apply freshVarNotIn with (vs := L ++ varsInFormula phi) (sigma := sigma);
          rewrite <- Heqx; apply in_or_app; right; apply FreeVarsInFormula; auto).
      assert (t = (varTerm x) t[x ↦ t])
        by (simpl; destruct (varEqDec x x) as [e | n]; [ | exfalso; apply n]; reflexivity).
      rewrite H3. rewrite H4 at 2. rewrite <- OpenFormulaSubstAll; auto.
      apply WellFormedSubst; auto. rewrite Heqx. rewrite freshVarSameSort. auto.
    - destruct HG' as [t HG']; destruct HG' as [tsort HG']; destruct HG' as [lc_t HG'].
      eapply H; eauto. inversion well_formed.
      specialize (H1 (freshVar (L ++ varsInFormula phi) sigma)).
      assert (~ In (freshVar (L ++ varsInFormula phi) sigma) L).
      intro Hcontra. apply freshVarNotIn with (vs := L ++ varsInFormula phi) (sigma := sigma).
      apply in_or_app; left; auto.
      specialize (H1 H3); clear H3.
      assert (⊢s varTerm (freshVar (L ++ varsInFormula phi) sigma) ::: sigma).
      erewrite <- freshVarSameSort. eapply varS.
      specialize (H1 H3); clear H3.
      remember (freshVar (L ++ varsInFormula phi) sigma) as x.
      assert (phi = phi f[x ↦ t])
      by (symmetry; apply notFreeInFormulaSubstEq;
          intro Hxϕ; apply freshVarNotIn with (vs := L ++ varsInFormula phi) (sigma := sigma);
          rewrite <- Heqx; apply in_or_app; right; apply FreeVarsInFormula; auto).
      assert (t = (varTerm x) t[x ↦ t])
        by (simpl; destruct (varEqDec x x) as [e | n]; [ | exfalso; apply n]; reflexivity).
      rewrite H3. rewrite H4 at 2. rewrite <- OpenFormulaSubstAll; auto.
      apply WellFormedSubst; auto. rewrite Heqx. rewrite freshVarSameSort. auto.
  Qed.

  Theorem G'_atomic : forall (fuel : nat) (phi : flafolFormula) (m m' : Modality),
      AtomicFormula phi -> G' fuel phi m m' -> m = m'.
  Proof.
    intros fuel phi m m' H H0.
    induction phi; destruct fuel; try (inversion H; fail); simpl in H0; try (inversion H0; fail); auto.
  Qed.

  Theorem G'_creates_extensions : forall (fuel : nat) (phi : flafolFormula) (m m' : Modality),
      G' fuel phi m m' -> option_defined (ModalityExtension m m').
  Proof.
    intros fuel phi m1 m2 H. destruct fuel; [inversion H|].
    generalize dependent m2; revert m1.
    induction phi using OpeningInduction; intros m1 m2 G'φ; simpl in G'φ;
    match goal with
    | [ H : ?m1 = ?m2 |- option_defined (ModalityExtension ?m1 ?m2) ] =>
      rewrite H; rewrite ModalityExtension_same; constructor
    | _ => idtac
    end.
    - assert (fuel < S fuel) by auto.
      pose proof (G'_more_fuel_better _ _ _ _ (S fuel) H G'φ).
      specialize (IHphi (m1 ⋅ p⟨lab⟩) m2 H0).
      destruct (ModalityExtension (m1 ⋅ p⟨lab⟩) m2) eqn:e; [clear IHphi |inversion IHphi].
      apply ModalityExtension_sim in e. rewrite e. constructor.
    - destruct G'φ as [H | H]; [apply IHphi1 | apply IHphi2];
        apply G'_more_fuel_better with (fuel2 := S fuel) in H; auto.
    - destruct G'φ as [H | H]; [apply IHphi1 | apply IHphi2];
        apply G'_more_fuel_better with (fuel2 := S fuel) in H; auto.
    - apply IHphi2.      
      apply G'_more_fuel_better with (fuel2 := S fuel) in G'φ; auto.
    - destruct G'φ as [t H']; destruct H' as [tsort H']; destruct H' as [lct G'φ].
      apply (H t tsort). apply G'_more_fuel_better with (fuel1 := fuel); auto.
    - destruct G'φ as [t H']; destruct H' as [tsort H']; destruct H' as [lct G'φ].
      apply (H t tsort). apply G'_more_fuel_better with (fuel1 := fuel); auto.
  Qed.

  Theorem G'_creates_extensions_neg : forall (fuel : nat) (phi : flafolFormula) (m m' : Modality),
      G' fuel phi m m' -> ModalityExtension m m' <> None.
  Proof.
    intros fuel phi m m' H Hcontra.
    pose proof (G'_creates_extensions fuel phi m m' H).
    inversion H0. pose proof (eq_trans H2 Hcontra). inversion H1.
  Qed.

  Definition ExtensionOfG' {fuel : nat} {phi : flafolFormula} {m m' : Modality}
             (G'_phi : G' fuel phi m m') : ModalityResidual.
    destruct (ModalityExtension m m') eqn:e. exact m0.
    exfalso; eapply G'_creates_extensions_neg; [exact G'_phi | exact e].
  Defined.
  Lemma G'_combine : forall (fuel : nat) (phi : flafolFormula) (m : Modality)
                           (mr1 mr2 : ModalityResidual),
      G' fuel phi (ModalityCombine m mr1) (ModalityCombine m mr2) ->
      exists mr', mr2 = mr1 ++ mr'.
  Proof.
    intros fuel phi; revert fuel; induction phi using OpeningInduction;
      intros fuel m mr1 mr2 Hsim; destruct fuel; try (inversion Hsim; fail).
    all: try (simpl in Hsim; exists []; rewrite app_nil_r;
              symmetry; apply ModalityCombineInj2 with (m := m); exact Hsim).
    - simpl in Hsim.
      specialize (IHphi fuel m (mr1 ++ [(p, lab)]) mr2).
      assert (ModalityCombine m mr1 ⋅ p⟨lab⟩ = ModalityCombine m (mr1 ++ [(p,lab)]))
        by (rewrite <-  ModalityCombineApp; simpl; reflexivity).
      rewrite H in Hsim. specialize (IHphi Hsim).
      destruct IHphi as [mr' Hmr'].
      exists ((p, lab) :: mr'). rewrite <- app_assoc in Hmr'. simpl in Hmr'. exact Hmr'.
    - destruct Hsim; [apply IHphi1 in H | apply IHphi2 in H]; exact H.
    - destruct Hsim; [apply IHphi1 in H | apply IHphi2 in H]; exact H.
    - apply IHphi2 in Hsim; exact Hsim.
    - simpl in Hsim. destruct Hsim as [t Ht]; destruct Ht as [tsort Ht];
                       destruct Ht as [lct Hsim].
      eapply H; eauto.
    - simpl in Hsim. destruct Hsim as [t Ht]; destruct Ht as [tsort Ht];
                       destruct Ht as [lct Hsim].
      eapply H; eauto.
  Qed.
  
  Lemma G'_replace_base : forall (fuel : nat) (phi : flafolFormula)
                            (m1 m2 : Modality) (mr : ModalityResidual),
      G' fuel phi m1 (ModalityCombine m1 mr) ->
      G' fuel phi m2 (ModalityCombine m2 mr).
  Proof.
    intros fuel phi; revert fuel; induction phi using OpeningInduction;
      intros fuel m1 m2 mr Hm1; destruct fuel; try (inversion Hm1; fail).
    all: try (simpl in Hm1; apply ModalityCombineIdentUnique in Hm1;
           rewrite Hm1; simpl; reflexivity).
    - simpl in Hm1. simpl.
      assert (G' fuel phi (ModalityCombine m1 [(p, lab)]) (ModalityCombine m1 mr))
        by (simpl; exact Hm1).
      apply G'_combine in H. destruct H as [mr' H].
      rewrite H. simpl. apply IHphi with (m1 := m1 ⋅ p⟨lab⟩).
      rewrite H in Hm1. simpl in Hm1. exact Hm1.
    - simpl in Hm1; destruct Hm1 as [H | H];
        [left ; apply IHphi1 with (m1 := m1)| right; apply IHphi2 with (m1 := m1)]; exact H.
    - simpl in Hm1; destruct Hm1 as [H | H];
        [left ; apply IHphi1 with (m1 := m1)| right; apply IHphi2 with (m1 := m1)]; exact H.
    - simpl in Hm1; simpl. apply IHphi2 with (m1 := m1); exact Hm1.
    - simpl in Hm1. simpl.
      destruct Hm1 as [t H1]; destruct H1 as [tsort H1]; destruct H1 as [lct Hm1].
      exists t; split; [|split]; auto. apply H with (m1 := m1); auto.
    - simpl in Hm1. simpl.
      destruct Hm1 as [t H1]; destruct H1 as [tsort H1]; destruct H1 as [lct Hm1].
      exists t; split; [|split]; auto. apply H with (m1 := m1); auto.
  Qed.

  Lemma __G'_collapse_double1 : forall (fuel : nat) (phi : flafolFormula) (m : Modality)
                                 (mr : ModalityResidual)
                                 (pth : PathToDoubleInModality m),
      G' fuel phi (CollapseDoubleInModality pth) (ModalityCombine (CollapseDoubleInModality pth) mr) ->
      G' fuel phi m (ModalityCombine m mr).
  Proof.
    intros fuel phi m mr pth H.
    apply G'_replace_base with (m1 := CollapseDoubleInModality pth); exact H.
  Qed.

  Lemma __G'_collapse_double2 : forall (fuel : nat) (phi : flafolFormula) (m : Modality)
                                  (mr : ModalityResidual)
                                  (pth : PathToDoubleInModality m),
      G' fuel phi m (ModalityCombine m mr) ->
      G' fuel phi (CollapseDoubleInModality pth) (ModalityCombine (CollapseDoubleInModality pth) mr).
  Proof.
    intros fuel phi m mr pth H.
    apply G'_replace_base with (m1 := m); exact H.
  Qed.
    
  
  Lemma G'_collapse_double1 : forall (fuel : nat) (phi : flafolFormula) (m m' : Modality)
                                (pth : PathToDoubleInModality m),
      G' fuel phi (CollapseDoubleInModality pth) m' ->
      match ModalityExtension (CollapseDoubleInModality pth) m' with
      | Some mr => G' fuel phi m (ModalityCombine m mr)
      | None => False
      end.
  Proof.
    intros fuel phi m m' pth G'_phi.
    destruct (ModalityExtension (CollapseDoubleInModality pth) m') eqn:e.
    pose proof (ModalityExtension_spec (CollapseDoubleInModality pth) m' m0 e).
    rewrite H in G'_phi. apply __G'_collapse_double1 with (pth := pth); exact G'_phi.
    apply G'_creates_extensions_neg with (fuel := fuel) (phi := phi) in e.
    destruct e.
    exact G'_phi.
  Qed.

  Lemma G'_collapse_double2 : forall (fuel : nat) (phi : flafolFormula) (m m' : Modality)
                                (pth : PathToDoubleInModality m),
      G' fuel phi m m' ->
      match ModalityExtension m m' with
      | Some mr => G' fuel phi (CollapseDoubleInModality pth)
                       (ModalityCombine (CollapseDoubleInModality pth) mr)
      | None => False
      end.
  Proof.
    intros fuel phi m m' pth G'_phi.
    destruct (ModalityExtension m m') eqn:e.
    pose proof (ModalityExtension_spec m m' m0 e).
    apply __G'_collapse_double2. rewrite <- H. exact G'_phi.
    apply G'_creates_extensions_neg with (fuel := fuel) (phi := phi) in e; auto.
  Qed.
  
  Fixpoint G'_choice (fuel : nat) (phi : flafolFormula) (m : Modality) : option Modality :=
    match fuel with
    | 0 => None
    | S rem => match phi with
            | A & B => G'_choice rem A m
            | A ⊕ B => G'_choice rem A m
            | A ==⟨_⟩> B => G'_choice rem B m
            | ∀ sigma; A =>
                let x := freshVar (varsInFormula phi ++ varsInModality m) sigma in
                G'_choice rem (open_formula A (varTerm x)) m
            | ∃ sigma; A =>
              let x := freshVar (varsInFormula phi ++ varsInModality m) sigma in
              G'_choice rem (open_formula A (varTerm x)) m
            | p □ ⟨ l ⟩ A => G'_choice rem A (m ⋅ p⟨l⟩)
            | _ => Some m
            end
      end.

  Fixpoint G'_choice_residual (fuel : nat) (phi : flafolFormula) (m : Modality) : option ModalityResidual :=
    match fuel with
    | 0 => None
    | S rem => match phi with
              | A & B => G'_choice_residual rem A m
              | A ⊕ B => G'_choice_residual rem A m
              | _ ==⟨_⟩> B => G'_choice_residual rem B m
              | flafolForall sigma A =>
                let x := freshVar (varsInFormula phi ++ varsInModality m) sigma in
                G'_choice_residual rem (open_formula A (varTerm x)) m
              | flafolExists sigma A =>
                let x := freshVar (varsInFormula phi ++ varsInModality m) sigma in
                G'_choice_residual rem (open_formula A (varTerm x)) m
              | says p l A =>
                match (G'_choice_residual rem A (m ⋅ p⟨l⟩)) with
                | None => None
                | Some mr => Some ((p, l) :: mr)
                end
              | _ => Some []
              end
    end.
                
  Lemma option_defined_bool_spec : forall {A : Type} (oa : option A), option_defined_bool oa = true <-> option_defined oa.
  Proof.
    intros A oa.
    split; intro H. destruct oa; simpl in H; [constructor | inversion H].
    inversion H; simpl; auto.
  Qed.
  Lemma option_defined_bool_spec' : forall {A : Type} (oa : option A), option_defined_bool oa = false <-> ~ option_defined oa.
  Proof.
    intros A oa.
    split; intro H.
    intro H'; inversion H'; rewrite <- H0 in H; simpl in H; inversion H.
    destruct oa; simpl in *; auto.
    exfalso; apply H; constructor.
  Qed.

  Theorem G'_choice_more_fuel_better : forall (fuel1 fuel2 : nat) (phi : flafolFormula) (m : Modality),
      fuel1 <= fuel2 -> option_defined (G'_choice fuel1 phi m) ->
      option_defined (G'_choice fuel2 phi m).
  Proof.
    intros fuel1 fuel2 phi m H H0.
    destruct (Compare_dec.le_lt_eq_dec fuel1 fuel2 H); [|rewrite <- e; auto].
    clear H. generalize dependent H0. generalize dependent m. generalize dependent phi.
    generalize dependent fuel2.
    induction fuel1 as [| rem]; intros fuel2 lt_fuel2 phi m defined_fuel1;
      simpl in *; [inversion defined_fuel1 |].
    destruct fuel2 as [| rem2]; [inversion lt_fuel2 |]; simpl.
    destruct phi; auto.
    all: auto; apply IHrem; [apply Lt.lt_S_n|]; auto.
  Qed.

  Theorem G'_choice_formula_size_enough : forall (phi : flafolFormula) (m : Modality),
      option_defined (G'_choice (formula_size phi) phi m).
  Proof.
    intros phi; induction phi using OpeningInduction; intro m; simpl; try (constructor; fail).
    - apply IHphi; auto.
    - apply G'_choice_more_fuel_better with (fuel1 := formula_size phi1);
      [apply PeanoNat.Nat.le_max_l | apply IHphi1].
    - apply G'_choice_more_fuel_better with (fuel1 := formula_size phi1);
      [apply PeanoNat.Nat.le_max_l | apply IHphi1].
    - apply G'_choice_more_fuel_better with (fuel1 := formula_size phi2);
      [apply PeanoNat.Nat.le_max_r | apply IHphi2].
    - remember (freshVar (varsInFormula phi ++ varsInModality m) sigma) as x.
      assert (sigma = VarSort x) by (rewrite Heqx; symmetry; apply freshVarSameSort).
      assert (⊢s varTerm x ::: sigma) by (rewrite H0; constructor).
      clear H0.
      specialize (H (varTerm x) H1 m).
      rewrite OpenFormulaSize in H. exact H.
    - remember (freshVar (varsInFormula phi ++ varsInModality m) sigma) as x.
      assert (sigma = VarSort x) by (rewrite Heqx; symmetry; apply freshVarSameSort).
      assert (⊢s varTerm x ::: sigma) by (rewrite H0; constructor).
      clear H0.
      specialize (H (varTerm x) H1 m).
      rewrite OpenFormulaSize in H. exact H.
  Qed.

  Lemma G'_choice_formula_size_enough_neg : forall {phi : flafolFormula} {m : Modality},
      G'_choice (formula_size phi) phi m <> None.
  Proof.
    intros phi m H.
    remember (G'_choice_formula_size_enough phi m).
    inversion o. assert (Some a = None). etransitivity; eauto. inversion H0.
  Qed.
    
  Theorem G'_choice_proper : forall (fuel : nat) (phi : flafolFormula) (m m' : Modality),
      ⊢wff phi -> ProperModality m -> G'_choice fuel phi m = Some m' ->
      ProperModality m'.
  Proof.
    intro fuel; induction fuel as [| remaining]; intros phi m m' wff_φ pmod gchoice;
      [inversion gchoice|].
    simpl in gchoice. destruct phi.
    all: try (inversion gchoice; rewrite <- H0; auto; fail).
    all: try (eapply IHremaining; auto; [| | exact gchoice]; auto; inversion wff_φ; auto; fail).
    - eapply IHremaining; auto; [| | exact gchoice]; auto; inversion wff_φ; auto.
      remember (varTerm (freshVar (varsInFormula (∀ s; phi) ++ varsInModality m) s)) as t.
      remember (freshVar (L ++ varsInFormula phi) s) as x.
      specialize (H0 x).
      assert (~ In x L) by
          (rewrite Heqx; intro Hcontra;
           apply freshVarNotIn with (vs := L ++ varsInFormula phi) (sigma := s);
           apply in_or_app; left; auto).
      specialize (H0 H2); clear H2.
      assert (⊢s varTerm x ::: s).
      rewrite Heqx. rewrite <- freshVarSameSort with (vs := L ++ varsInFormula phi) (sigma := s) at 2.
      apply varS.
      specialize (H0 H2); clear H2.
      assert (phi = phi f[x ↦ t])
      by (symmetry; apply notFreeInFormulaSubstEq;
          intro Hcontra; apply FreeVarsInFormula in Hcontra;
          apply freshVarNotIn with (vs := L ++ varsInFormula phi) (sigma := s);
          apply in_or_app; right; rewrite <- Heqx; auto).
      rewrite H2.
      assert (t = (varTerm x) t[x ↦ t])
        by (simpl; destruct (varEqDec x x) as [e | n];
            [reflexivity | exfalso; apply n; reflexivity]).
      rewrite H3 at 2.
      assert (lc_term t) by (rewrite Heqt; constructor).
      rewrite <- OpenFormulaSubstAll; auto.
      apply WellFormedSubst with (x := x) (t := t); auto.
      rewrite Heqt. rewrite Heqx. rewrite freshVarSameSort.
      rewrite <- freshVarSameSort with (vs := varsInFormula (∀ s; phi) ++ varsInModality m).
      constructor.
    - eapply IHremaining; auto; [| | exact gchoice]; auto; inversion wff_φ; auto.
      remember (varTerm (freshVar (varsInFormula (∃ s; phi) ++ varsInModality m) s)) as t.
      remember (freshVar (L ++ varsInFormula phi) s) as x.
      specialize (H0 x).
      assert (~ In x L) by
          (rewrite Heqx; intro Hcontra;
           apply freshVarNotIn with (vs := L ++ varsInFormula phi) (sigma := s);
           apply in_or_app; left; auto).
      specialize (H0 H2); clear H2.
      assert (⊢s varTerm x ::: s).
      rewrite Heqx. rewrite <- freshVarSameSort with (vs := L ++ varsInFormula phi) (sigma := s) at 2.
      apply varS.
      specialize (H0 H2); clear H2.
      assert (phi = phi f[x ↦ t])
        by (symmetry; apply notFreeInFormulaSubstEq;
            intro Hcontra; apply FreeVarsInFormula in Hcontra;
            apply freshVarNotIn with (vs := L ++ varsInFormula phi) (sigma := s);
            apply in_or_app; right; rewrite <- Heqx; auto).
      rewrite H2.
      assert (t = (varTerm x) t[x ↦ t])
        by (simpl; destruct (varEqDec x x) as [e | n];
            [reflexivity | exfalso; apply n; reflexivity]).
      rewrite H3 at 2.
      assert (lc_term t) by (rewrite Heqt; constructor).
      rewrite <- OpenFormulaSubstAll; auto.
      apply WellFormedSubst with (x := x) (t := t); auto.
      rewrite Heqt. rewrite Heqx. rewrite freshVarSameSort.
      rewrite <- freshVarSameSort with (vs := varsInFormula (∃ s; phi) ++ varsInModality m).
      constructor.
    - eapply IHremaining; [ | | exact gchoice]; inversion wff_φ; auto.
      constructor; auto.
  Qed.

  Theorem G'_choice_spec : forall (fuel : nat) (phi : flafolFormula) (m1 m2 : Modality),
      G'_choice fuel phi m1 = Some m2 -> G' fuel phi m1 m2.
  Proof.
    intros fuel.
    induction fuel as [| remaining]; intros phi m1 m2 H; [inversion H|].
    simpl in *. destruct phi; try (inversion H; auto; fail).
    - remember (varTerm (freshVar (varsInFormula (∀ s; phi) ++ varsInModality m1) s)) as t.
      exists t; split; [| split]; auto.
      -- rewrite <- (freshVarSameSort (varsInFormula (∀ s; phi) ++ varsInModality m1) s).
         rewrite Heqt. constructor.
      -- rewrite Heqt. constructor.
    - remember (varTerm (freshVar (varsInFormula (∃ s; phi) ++ varsInModality m1) s)) as t.
      exists t; split; [| split]; auto.
      -- rewrite <- (freshVarSameSort (varsInFormula (∃ s; phi) ++ varsInModality m1) s).
         rewrite Heqt. constructor.
      -- rewrite Heqt. constructor.
  Qed.         

  Theorem G'_choice_residual_spec : forall (phi : flafolFormula) (fuel : nat) (m1 : Modality)
                                      (mr : ModalityResidual),
      G'_choice_residual fuel phi m1 = Some mr ->
      G'_choice fuel phi m1 = Some (ModalityCombine m1 mr).
  Proof.
    intros phi; induction phi using OpeningInduction;
        intros fuel m1 m2 G'm2; destruct fuel as [| remaining]; inversion G'm2; auto.
    - simpl in G'm2. destruct (G'_choice_residual remaining phi (m1 ⋅ p⟨lab⟩)) eqn:e;
      simpl; inversion G'm2; simpl. apply IHphi; auto.
    - simpl in G'm2. simpl. apply IHphi1; auto.
    - simpl in G'm2. simpl. apply IHphi1; auto.
    - simpl in G'm2. simpl. apply IHphi2; auto.
    - simpl. apply H; auto.
      erewrite <- freshVarSameSort. apply varS.
    - simpl. apply H; auto.
      erewrite <- freshVarSameSort. apply varS.
  Qed.

      
  Theorem G'_extension : forall (fuel : nat) (phi : flafolFormula) (m1 m2 : Modality),
      G' fuel phi m1 m2 -> exists mr, m2 = ModalityCombine m1 mr.
  Proof.
    induction fuel as [|remaining]; intros phi m1 m2 H; [inversion H|].
    destruct phi; simpl in *.
    all: try (exists []; simpl; auto; fail).
    - destruct H; eapply IHremaining; eauto.
    - destruct H; eapply IHremaining; eauto.
    - eapply IHremaining; eauto.
    - destruct H as [t H]; destruct H as [t_sort H]; destruct H as [lc_t H].
      eapply IHremaining; eauto.
    - destruct H as [t H]; destruct H as [t_sort H]; destruct H as [lc_t H].
      eapply IHremaining; eauto.
    - specialize (IHremaining phi (m1 ⋅ f⟨f0⟩) m2 H); destruct IHremaining as [mr IHremaining].
      exists ((f, f0) :: mr). simpl. exact IHremaining.
  Qed.

  Theorem G'_choice_extension : forall (fuel : nat) (phi : flafolFormula) (m1 m2 : Modality),
      G'_choice fuel phi m1 = Some m2 -> exists mr, m2 = ModalityCombine m1 mr.
  Proof.
    intros fuel phi m1 m2 H.
    eapply G'_extension; eapply G'_choice_spec; eauto.
  Qed.

  Theorem G'_choice_residual_more_fuel_better : forall (fuel1 fuel2 : nat) (phi : flafolFormula)
                                                  (m : Modality) (mr : ModalityResidual),
      fuel1 <= fuel2 -> G'_choice_residual fuel1 phi m = Some mr ->
      G'_choice_residual fuel2 phi m = Some mr.
  Proof.
    intros fuel1. induction fuel1; intros fuel2 phi m mr fuel_lt G1.
    simpl in G1; inversion G1.
    destruct phi.
    all: try (simpl in G1; inversion G1; inversion fuel_lt; simpl; auto; fail).
    all: try (inversion fuel_lt; simpl; simpl in G1; apply IHfuel1; auto;
              apply Le.le_Sn_le; auto; fail).
    inversion fuel_lt; simpl; simpl in G1.
    destruct (G'_choice_residual fuel1 phi (m ⋅ f⟨f0⟩)); auto.
    destruct (G'_choice_residual fuel1 phi (m ⋅ f⟨f0⟩)) eqn:e; auto; [| inversion G1].
    apply IHfuel1 with (fuel2 := m0) in e. rewrite e. auto.
    apply Le.le_Sn_le; auto.
  Qed.

  Theorem G'_choice_residual_formula_size_enough : forall (phi : flafolFormula) (m : Modality),
      option_defined (G'_choice_residual (formula_size phi) phi m).
  Proof.
    intros phi; induction phi using OpeningInduction; intro m;
      try (simpl; constructor; auto; fail).
    - simpl. specialize (IHphi (m ⋅ p⟨lab⟩)). inversion IHphi.
      constructor.
    - simpl.
      specialize (IHphi1 m). inversion IHphi1.
      rewrite G'_choice_residual_more_fuel_better with (fuel1 := formula_size phi1) (mr := a);
        auto; [constructor | apply PeanoNat.Nat.le_max_l].
    - simpl.
      specialize (IHphi1 m). inversion IHphi1.
      rewrite G'_choice_residual_more_fuel_better with (fuel1 := formula_size phi1) (mr := a);
        auto; [constructor | apply PeanoNat.Nat.le_max_l].
    - simpl.
      specialize (IHphi2 m). inversion IHphi2.
      rewrite G'_choice_residual_more_fuel_better with (fuel1 := formula_size phi2) (mr := a);
        auto; [constructor | apply PeanoNat.Nat.le_max_r].
    - simpl.
      remember (varTerm (freshVar (varsInFormula phi ++ varsInModality m) sigma)) as t.
      assert (⊢s t ::: sigma) by (rewrite Heqt; erewrite <- freshVarSameSort; apply varS).
      specialize (H t H0 m). clear H0 Heqt.
      rewrite OpenFormulaSize in H. exact H.
    - simpl.
      remember (varTerm (freshVar (varsInFormula phi ++ varsInModality m) sigma)) as t.
      assert (⊢s t ::: sigma) by (rewrite Heqt; erewrite <- freshVarSameSort; apply varS).
      specialize (H t H0 m). clear H0 Heqt.
      rewrite OpenFormulaSize in H. exact H.
  Qed.

  Lemma G'_choice_residual_formula_size_enough_neg : forall (phi : flafolFormula) (m : Modality),
      G'_choice_residual (formula_size phi) phi m <> None.
  Proof.
    intros phi m.
    intro H. pose proof (G'_choice_residual_formula_size_enough phi m).
    inversion H0. pose proof (eq_trans H2 H). inversion H1.
  Qed.

  Fixpoint CollapseOtherModality {m : Modality}
           (pth : PathToDoubleInModality m) (m' : Modality) : option Modality :=
    match pth with
    | hereDouble m p l =>
      match m' with
      | ⟨_⟩ => None
      | m'' ⋅ p'⟨l'⟩ =>
        if termEqDec p p'
        then if termEqDec l l'
             then Some m''
             else None
        else None
      end
    | thereDouble m p l pth' =>
      match m' with
      | ⟨_⟩ => None
      | m'' ⋅ p'⟨l'⟩ => if termEqDec p p'
                       then if termEqDec l l'
                            then match (CollapseOtherModality pth' m'') with
                                 | Some m''' => Some (m''' ⋅ p⟨l⟩)
                                 | None => None
                                 end
                            else None
                       else None
      end
    end.

  Lemma CollapseSameModality : forall (m : Modality) (pth : PathToDoubleInModality m),
      CollapseOtherModality pth m = Some (CollapseDoubleInModality pth).
  Proof.
    intros m pth.
    induction pth; simpl.
    destruct (termEqDec p p) as [_ | n]; [| exfalso; apply n; reflexivity].
    destruct (termEqDec l l) as [_ | n]; [| exfalso; apply n; reflexivity].
    reflexivity.
    destruct (termEqDec p p) as [_ | n]; [| exfalso; apply n; reflexivity].
    destruct (termEqDec l l) as [_ | n]; [| exfalso; apply n; reflexivity].
    rewrite IHpth. reflexivity.
  Qed.

  Fixpoint ExtendPathToDouble {m : Modality} (pth : PathToDoubleInModality m)
           (mr : ModalityResidual) : PathToDoubleInModality (ModalityCombine m mr) :=
    match mr with
    | [] => pth
    | a :: mr' => match a with
                  (p, l) =>
                  ExtendPathToDouble (thereDouble _ p l pth) mr'
                end
    end.

  Lemma CollapseExtendedPathToDouble : forall {m : Modality} (pth : PathToDoubleInModality m)
                                         (mr : ModalityResidual),
      CollapseDoubleInModality (ExtendPathToDouble pth mr)
      = ModalityCombine (CollapseDoubleInModality pth) mr.
  Proof.
    intros m pth mr. generalize dependent m.
    simpl. induction mr; intros m pth. simpl; reflexivity. simpl. destruct a as [p l].
    rewrite IHmr. simpl. reflexivity.
  Qed.

  Definition G_choice (b : Belief) : Modality :=
    match b with
    | phi @ m => match G'_choice (formula_size phi) phi m with
              | Some m' => m'
              | None => ⟨varTerm (freshVar [] Label)⟩ (* bogus! *)
              end
    end.

  Definition G_choice_residual (b : Belief) : ModalityResidual :=
    match b with
    | phi @ m => match G'_choice_residual (formula_size phi) phi m with
                | Some m' => m'
                | None => [] (* bogus! *)
                end
    end.
  
  Definition G (b : Belief) : Modality -> Prop :=
    fun m => match b with
          | phi @ m' => G' (formula_size phi) phi m' m
          end.

  Theorem G_proper : forall (b : Belief) (m : Modality), ProperBelief b -> G b m -> ProperModality m.
  Proof.
    intros b m H H0.
    unfold G in H0. destruct b. inversion H.
    eapply G'_Proper. exact H2. exact H1. exact H0.
  Qed.

  Theorem G_atomic : forall (phi : flafolFormula) (m m' : Modality),
      AtomicFormula phi -> G (phi @ m) m' -> m = m'.
  Proof.
    intros phi m m' H H'.
    unfold G in *. apply G'_atomic in H'; auto.
  Qed.
  
  Theorem G_choice_spec : forall (b : Belief), G b (G_choice b).
  Proof.
    unfold G; unfold G_choice.
    destruct b.
    destruct (G'_choice (formula_size f) f m) eqn:e.
    apply G'_choice_spec; auto.
    apply G'_choice_formula_size_enough_neg in e; inversion e.
  Qed.

  Theorem G_choice_proper : forall (b : Belief), ProperBelief b -> ProperModality (G_choice b).
  Proof.
    intros b pbel; unfold G; destruct b; unfold G_choice.
    inversion pbel.
    destruct (G'_choice (formula_size f) f m) eqn:e.
    eapply G'_choice_proper; [exact H0 | exact H| exact e].
    constructor.
    rewrite <- freshVarSameSort with (vs := []) (sigma := Label) at 2; constructor.
  Qed.

  Theorem G_extension : forall phi m1 m2, G (phi @ m1) m2 -> exists mr, m2 = ModalityCombine m1 mr.
  Proof.
    intros phi m1 m2 H.
    unfold G in H; apply G'_extension in H; exact H.
  Qed.

  Theorem G_choice_extension : forall phi m1, exists mr, (G_choice (phi @ m1)) = ModalityCombine m1 mr.
  Proof.
    intros phi m1.
    eapply G_extension; eapply G_choice_spec.
  Qed.

  Theorem G_choice_residual_spec : forall phi m1,
      G_choice (phi @ m1) = ModalityCombine m1 (G_choice_residual (phi @ m1)).
  Proof.
    intros phi m1.
    unfold G_choice; unfold G_choice_residual.
    pose proof (G'_choice_formula_size_enough phi m1).
    inversion H. pose proof (G'_choice_residual_formula_size_enough phi m1).
    inversion H0.
    pose proof (G'_choice_residual_spec phi (formula_size phi) m1 a0 (eq_sym H3)).
    pose proof (eq_trans H1 H2). inversion H4. reflexivity.
  Qed.
  
  Reserved Notation "Gamma ⊢inf m1 ⇛ m2" (at level 25).
  Inductive canInfluence : Context -> Modality -> Modality -> Set :=
  | SFCI : forall (Gamma : Context) (m1 m2 : Modality),
      Gamma ⊢sf m1 ⇛ m2 -> Gamma ⊢inf m1 ⇛ m2
  | ExtCS : forall (Gamma : Context) (m1 m2 : Modality) (p l : flafolTerm),
      ⊢s p ::: Principal -> ⊢s l ::: Label ->
      Gamma ⊢inf m1 ⇛ m2 -> Gamma ⊢inf m1 ⋅ p⟨l⟩ ⇛ m2 ⋅ p⟨l⟩
  | TransCI : forall (Gamma : Context) (m1 m2 m3 : Modality),
      Gamma ⊢inf m1 ⇛ m2 -> Gamma ⊢inf m2 ⇛ m3 -> Gamma ⊢inf m1 ⇛ m3
  | ImpCI : forall (Gamma : Context) (phi psi : flafolFormula) (l : flafolTerm)
              (m m1 m2 : Modality),
      ProperContext Gamma -> Path (phi ==⟨l⟩> psi @ m) Gamma ->
      G (phi @ ⟨l⟩) m1 -> G(psi @ m) m2 -> Gamma ⊢inf m1 ⇛ m2
  where "Gamma ⊢inf m1 ⇛ m2" := (canInfluence Gamma m1 m2).

  Lemma reflCI : forall (Gamma : Context) (m : Modality),
      ProperContext Gamma -> ProperModality m -> Gamma ⊢inf m ⇛ m.
  Proof.
    intros Gamma m pctxt pmod. apply SFCI. apply ReflSF; auto.
  Qed.

  Lemma canInfluenceProper : forall (Gamma : Context) (m1 m2 : Modality),
      Gamma ⊢inf m1 ⇛ m2 -> ProperContext Gamma /\ ProperModality m1 /\ ProperModality m2.
  Proof.
    intros Gamma m1 m2 H.
    induction H;
      repeat match goal with
      | [ H : ?P |- ?P ] => exact H
      | [ H : _ /\ _ |- _ ] => destruct H
      | [ |- _ /\ _ ] => split
      | [ H : ?Gamma ⊢sf ?m1 ⇛ ?m2  |- _ ] =>
        match goal with
        | [ _ : ProperContext Gamma, _ : ProperModality m1, _ : ProperModality m2 |- _ ] =>
          fail 1
        | _ => let H1 := fresh in
              let H2 := fresh in
              remember (sf_proper _ _ _ H) as H1; destruct H1 as [H1 H2]; destruct H2
        end
      | [ |- ProperModality (_ ⋅ _⟨_⟩) ] => constructor; auto
      | [ H : G ?b' ?m |- ProperModality ?m ] => apply G_proper with (b := b'); auto
             end.
    all: assert (ProperBelief (phi ==⟨l⟩> psi @ m)) as H
      by (apply BeliefInProperContextIsProper with (Gamma := Gamma); [|apply PathToIn]; auto);
      inversion H; inversion H1; repeat (constructor; auto).
  Qed.    

  Lemma ExtCIResidual : forall (Gamma : Context) (m1 m2 : Modality) (r : ModalityResidual),
      ProperModalityResidual r -> Gamma ⊢inf m1 ⇛ m2 -> Gamma ⊢inf (ModalityCombine m1 r) ⇛ (ModalityCombine m2 r).
  Proof.
    intros Gamma m1 m2 r H H0.
    generalize dependent m2; generalize dependent m1; generalize dependent Gamma. 
    induction r; intros; simpl; auto.
    destruct a as [p l].
    apply IHr. apply ProperModalityResidualConsInv in H.
    destruct H as [psort H]; destruct H as [lsort pmr]; auto.
    apply ExtCS; auto; apply ProperModalityResidualConsInv in H; destruct H as [H H']; destruct H'; auto.
  Qed.

  Theorem CIWeakening : forall (Gamma Delta : Context) (m1 m2 : Modality),
      ProperContext Delta -> (forall b, Path b Gamma -> Path b Delta) -> Gamma ⊢inf m1 ⇛ m2 -> Delta ⊢inf m1 ⇛ m2.
  Proof.
    intros Gamma Delta m1 m2 pctxtΔ H H0.
    induction H0; try (constructor; auto; fail).
    - apply SFCI; apply @SFWeak with (Gamma := Gamma); auto.
    - apply TransCI with (m2 := m2).
      apply IHcanInfluence1; auto.
      apply IHcanInfluence2; auto.
    - apply ImpCI with (phi := phi) (psi := psi) (l := l) (m := m); auto.
  Qed.

  
End Speaksfor.