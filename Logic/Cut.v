Require Import Sequent.
Require Export Term. (* We use it enough below to just go ahead and import it directly. *)
Require Export Formula.
Require Export NormalForm.

Require Import Base.Lists.
Require Import Base.Permutation.
Require Export Tactics.CutTact.
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

Require Import Coq.Strings.String.
Open Scope string_scope.

Module Type Cut (G : GroundInfo) (GTerm : Term G) (GFormula : Formula G GTerm)
       (TE : TermEquality G GTerm) (FE : FormulaEquality G GTerm GFormula TE)
       (THS : TermHasSort'' G GTerm TE)
       (WFF : WellFormedFormula' G GTerm TE THS GFormula FE) (SEQ : Sequent G GTerm GFormula TE FE THS WFF)
       (CT : CutTact G GTerm GFormula TE FE THS WFF SEQ) (NF : NormalForm G GTerm GFormula TE FE THS WFF SEQ CT).
  Import G. Import GTerm. Import GFormula. Import ListNotations.
  Import THS. Import WFF. Import SEQ. Import NF. Import CT.

  Ltac Cut_ltac1 :=
    repeat match goal with
           | [ H1 : NormalForm' ?pf ?b, H2 : JMeq ?pf' ?pf |- _ ] =>
             apply (NormalForm'_JMeq2 H2) in H1; auto; simpl in H1
           | [ H : True |- _ ] => clear H
           | [ H : False |- _ ] => inversion H
           | [ H : ?Gamma ⊢ _ |- ProperContext ?Gamma ] =>
             exact (provenProperContext H)
           end.
  
  
  Lemma liftExpColPath : forall mr m (pth : PathToDoubleInModality m), sigT (fun pi' : PathToDoubleInModality (ModalityCombine m mr) => ModalityCombine (CollapseDoubleInModality pth) mr = CollapseDoubleInModality pi').
  Proof.
    induction mr; simpl; intros.
    - exists pth; auto.
    - destruct a.
      edestruct (IHmr (m ⋅ f ⟨ f0 ⟩) (thereDouble m f f0 pth)).
      eauto.
  Qed.


  Lemma liftVarPath : forall mr m lab1 lab2 (pth : PathToLabelInModality m lab1), sigT (fun pi' : PathToLabelInModality (ModalityCombine m mr) lab1 => prod (ModalityCombine (ReplaceLabelInModality m lab1 lab2 pth) mr = ReplaceLabelInModality (ModalityCombine m mr) lab1 lab2 pi') (VarModality pth lab2 = VarModality pi' lab2)).
  Proof.
    induction mr; simpl; intros.
    - exists pth; auto.
    - destruct a.
      destruct (IHmr (m ⋅ f ⟨ f0 ⟩) lab1 lab2 (thereLab m f lab1 f0 pth)).
      destruct p.
      exists x.
      split; auto.
      simpl in e0.
      destruct pth; auto.
  Qed.

  Lemma liftFwdPath : forall mr m p q (pth : PathToPrinInModality m p), sigT (fun pi' : PathToPrinInModality (ModalityCombine m mr) p => prod (ModalityCombine (ReplacePrinInModality pth q) mr = ReplacePrinInModality pi' q) (prod (prod (LabelAtPrin pth = LabelAtPrin pi') (FwdModality pth q = FwdModality pi' q)) (FwdModality pth p = FwdModality pi' p))).
  Proof.
    induction mr; simpl; intros.
    - exists pth; auto.
    - destruct a.
      destruct (IHmr (m ⋅ f ⟨ f0 ⟩) p q (thereP m p f f0 pth)).
      repeat destructProd.
      exists x.
      split; auto.
  Qed.

  Definition PFFR_inv := fun t => forall {Gamma : Context} {m : Modality} {C : flafolFormula} {mr : ModalityResidual} (pf : typing Gamma t (FF @ m)) (mr_proper : ProperModalityResidual mr) (C_wf : ⊢wff C), sigT (fun t' => typing Gamma t' (C @ (ModalityCombine m mr))).

    
  Lemma FFR_inversion : forall {t : proofTerm} {Gamma : Context} {m : Modality} {C : flafolFormula} {mr : ModalityResidual} (pf : typing Gamma t (FF @ m)) (mr_proper : ProperModalityResidual mr) (C_wf : ⊢wff C), sigT (fun t' => typing Gamma t' (C @ (ModalityCombine m mr))).
  Proof.
    apply (@Fix _ (fun x1 x2 => term_size x1 < term_size x2) (well_founded_ltof _ _) PFFR_inv); eauto.
    unfold PFFR_inv.
    intros t IHt.
    destruct t; intros; inversion pf; subst.
    - eexists.
      apply FFLr; auto.
      apply TypingToProof in pf.
      apply provenWFSequent in pf.
      destruct pf.
      inversion H2; auto.
    - rewrite ModalityCombineApp.
      eexists.
      apply FFLr; auto.
      apply ModalityResidualAppProper; auto.
    - edestruct IHt with (2 := H1); eauto.
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (2 := H2); try solve [simpl; solveCutRel]; eauto.
      edestruct IHt with (2 := H4); try solve [simpl; solveCutRel]; eauto.
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (2 := H4); try solve [simpl; solveCutRel]; eauto.
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (2 := H3); try solve [simpl; solveCutRel]; eauto.
      eexists; econstructor; eauto; fail.
    - pose (freshInSequent (open_formula phi (varTerm y) @ m :: (C @ ModalityCombine m mr) :: Gamma) (FF @ m) (VarSort y)) as y'.
      destruct (open_with_fresherLTS' _ _ _ _ y y'  t H4) as [t' [T eq]]; auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      edestruct IHt with (2 := T); eauto.
      simpl; rewrite eq; auto.
      eexists.
      eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
      unfold y'.
      all : destruct (freshInSequentIsFresh (open_formula phi (varTerm y) @ m :: (C @ ModalityCombine m mr ):: Gamma) (FF @ m) (VarSort y)) as [fv1 fv2].
      intro; apply fv1; econstructor; eauto; fail.      
      intro.
      apply fv1.
      econstructor; eauto; fail.
    - edestruct IHt with (2 := H1); eauto.
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (2 := H2); eauto.
      edestruct (liftExpColPath mr _ pth).
      eexists.
      eapply modalityExpandRr.      
      rewrite e in t0.
      eauto.
    - edestruct IHt with (2 := H2); eauto.
      edestruct (liftExpColPath mr _ pth).      
      rewrite e.
      eexists.
      apply modalityCollapseRr; eauto.
    - edestruct IHt with (2 := H1); eauto.
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (2 := H1); eauto.
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (2 := H3); try solve [simpl; solveCutRel]; eauto.
      edestruct (liftVarPath mr m0 lab1 lab2 pi).
      destruct p.
      rewrite e.
      eexists.
      apply RVariancer.
      eauto.
      rewrite <-e0; eauto.
    - edestruct IHt with (2 := H2); try solve [simpl; solveCutRel]; eauto.
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (2 := H4); try solve [simpl; solveCutRel]; eauto.
      edestruct (liftFwdPath mr m0 p q pth).
      repeat destructProd.
      rewrite e.
      eexists.
      apply FwdRr; eauto.
      rewrite <-e0.
      rewrite <-e1.
      eauto.
      rewrite <-e1.
      rewrite <-e2.
      eauto.      
    - edestruct IHt with (2 := H3); try solve [simpl; solveCutRel]; eauto.
      eexists; econstructor; eauto; fail.
  Qed.
    
    
  
  Lemma SplitPath {A : Set} {a : A} (l1 l2 : list A) (pth : Path a (l1 ++ l2)) : (Path a l1) + (Path a l2).
  Proof.
    induction l1; simpl in *; auto.
    inversion pth; subst; auto.
    left; constructor.
    destruct (IHl1 H1); auto.
    left; econstructor; eauto; fail.    
  Qed.    

  Lemma PathToEq: forall phi m' M C, Path (phi @ m') (map (fun m : Modality => C @ m) M) -> phi = C.
  Proof.
    intros phi m' M C H.
    induction M; simpl in *; inversion H; subst; auto.
  Qed.
    
  Obligation Tactic := 
    match goal with
    | [|- proof_size _ <= proof_size _] => Normalize
    | _ =>
    try (match goal with
         | [H : _ = ?l1 ++ ?l2 |- _] => pose proof H
         end); try (timeout 1 Tactics.program_simpl);
      try (match goal with
           | [H : ProperContext (?G1 ++ ?G2) |- ProperContext ?G1] => apply (ProperContextApp G1 G2); auto 
           | [H : ProperContext (?G1 ++ ?G2) |- ProperContext ?G2] => apply (ProperContextApp G1 G2); auto 
           end);
      try (match goal with
           | [H : JMeq _ _ , H0 : NormalForm' _ _ |- _] =>
             apply JMeq_eq in H; rewrite <- H in H0; simpl in H0
           end);
      try (match goal with
           | [H : False|- _] => inversion H
           end); auto; Normalize;
        try (match goal with
             | [H : Path _ (_ ++ _)|- _] => subst; apply SplitPath in H
             end); intros
    end.      

  Obligation Tactic := intros; subst; simpl in *;
                         try (match goal with
                              | [h : Empty_set |- _] => inversion h
                              | [h : typing (_ ++ _) _ _ |- _] => inversion h; subst
                              end).


  
  Program Fixpoint Cut_h1MCR {Gamma : Context} {phi : Belief} {C : flafolFormula} {M : list Modality} (t : proofTerm) (h1 : typing ((map (fun m => C @ m) M) ++ Gamma) t phi) (h2 : forall b, Path b (map (fun m => C @ m) M) -> Gamma ⊢ b) (h3 : NormalFormTerm' t false) {measure (term_size t)} : sigT (fun t : proofTerm => typing Gamma t phi) :=
      match t with
      | axiomTerm => _
      | TTRTerm => _
      | FFLTerm => _
      | AndLTerm e'1 => _
      | AndRTerm e'1 e'2 => _
      | OrLTerm pf1 pf2 => _
      | OrR1Term pf1 => _
      | OrR2Term pf1 => _
      | ImpLTerm pf1 pf2 => _
      | ImpRTerm pf1 => _
      | forallLTerm pf1 => _
      | forallRTerm pf1 => _
      | existsLTerm pf1 => _
      | existsRTerm pf1 => _
      | flowsToReflTerm => _
      | flowsToTransRTerm pf1 pf2 => _
      | saysRTerm pf1 => _
      | saysLTerm pf1 => _
      | modalityExpandRTerm pf1 => _
      | modalityCollapseRTerm pf1 => _
      | modalityExpandLTerm pf1 => _
      | modalityCollapseLTerm pf1 => _
      | RVarianceTerm pf1 pf2 => _
      | LVarianceTerm pf1 pf2 => _
      | FwdRTerm pf1 pf2 pf3 => _
      | FwdLTerm pf1 pf2 pf3 => _
      | CRVarianceTerm pf1 pf2 => _
      | CWVarianceTerm pf1 pf2 => _
      end.
  Next Obligation.
    destruct (SplitPath (map (fun m : Modality => C @ m) M) Gamma H0); eauto.
    pose proof (h2 _ p).
    apply ProofToTyping; auto.
    eexists.
    econstructor; eauto.    
    eapply ProperContextApp; eauto.
  Defined.
  Next Obligation.
    eexists.
    apply TTRr; auto.
    eapply ProperContextApp; eauto.
  Defined.
  Next Obligation.
    destruct (SplitPath (map (fun m : Modality => C @ m) M) Gamma H2); eauto.
    + pose proof (h2 _ p).
      apply ProofToTyping in H4.
      destruct H4.      
      eapply FFR_inversion; eauto.
    + eexists.
      apply FFLr; auto.
      eapply ProperContextApp; eauto.
  Defined.
  Next Obligation.
    eexists.
    apply flowsToReflr; auto.
    eapply ProperContextApp; eauto.
  Defined.
  Next Obligation.
    destruct (Cut_h1MCR _ _ _ _ pf1 H2); eauto.
    apply h3.
    solveCutRel.
    destruct (Cut_h1MCR _ _ _ _ pf2 H4); eauto.
    apply h3.
    solveCutRel.
    eexists.
    econstructor; eauto; fail.
  Defined.
  Next Obligation.
    destruct (Cut_h1MCR _ _ _ _ pf1 H1); eauto.
    eexists.
    eapply modalityExpandRr; eauto.
  Defined.
  Next Obligation.
    destruct (Cut_h1MCR _ _ _ _ pf1 H1); eauto.
    eexists.
    eapply modalityCollapseRr; eauto.
  Defined.
  Next Obligation.
    - destruct (SplitPath (map (fun m : Modality => C @ m) M) Gamma pth'); eauto.
      assert (forall b : Belief, Path b ((C @ m) :: (map (fun m : Modality => C @ m) M)) -> Gamma ⊢ b).
      + intros.
        inversion H; subst; auto.
        rewrite <-(PathToEq phi0 (CollapseDoubleInModality pth) M C); auto.
        eapply modalityExpandR; eauto.
      + pose proof (Cut_h1MCR Gamma phi C (m :: M)).
        simpl in H0.
        rewrite (PathToEq phi0 (CollapseDoubleInModality pth) M C) in H1; auto.
        pose proof (H0 pf1 H1); clear H0; auto.
      + destruct (Cut_h1MCR (phi0 @ m :: Gamma) phi C M pf1); auto.
        eapply Exchange; eauto.
        solveSubPath.
        intros.
        eapply Weakening; eauto.
        solveProper.
        solveSubPath.
        eexists.
        eapply modalityExpandLr with (pth := pth); eauto.
  Defined.
  Next Obligation.
    - destruct (SplitPath (map (fun m : Modality => C @ m) M) Gamma pth'); eauto.
      assert (forall b : Belief, Path b ((C @ CollapseDoubleInModality pth) :: (map (fun m : Modality => C @ m) M)) -> Gamma ⊢ b).
      + intros.
        inversion H; subst; auto.
        rewrite <-(PathToEq phi0 m M C); auto.
        eapply modalityCollapseR; eauto.
      + pose proof (Cut_h1MCR Gamma phi C ((CollapseDoubleInModality pth) :: M)).
        simpl in H0.
        rewrite (PathToEq phi0 m M C) in H1; auto.
        pose proof (H0 pf1 H1); clear H0; auto.
      + destruct (Cut_h1MCR (phi0 @ CollapseDoubleInModality pth :: Gamma) phi C M pf1); auto.
        eapply Exchange; eauto.
        solveSubPath.
        intros.
        eapply Weakening; eauto.
        solveProper.
        solveSubPath.
        eexists.
        eapply modalityCollapseLr with (pth := pth); eauto.
  Defined.
  Next Obligation.
    destruct h3.
    destruct (Cut_h1MCR _ _ _ _ pf1 H2); eauto.
    apply le_n_S; solve_max_le.
    destruct (Cut_h1MCR _ _ _ _ pf2 H4); eauto.
    apply le_n_S; solve_max_le.
    eexists.
    eapply RVariancer; eauto.
  Defined.
  Next Obligation.
    destruct h3.
    destruct (SplitPath (map (fun m : Modality => C @ m) M) Gamma pth); eauto.
    - destruct (Cut_h1MCR Gamma (lab1 ⊑ lab2 @ VarModality pi lab2) C M pf2); auto.
      apply le_n_S; solve_max_le.
      assert (forall b : Belief, Path b ((C @ ReplaceLabelInModality m lab1 lab2 pi) :: (map (fun m : Modality => C @ m) M)) -> Gamma ⊢ b).
      + intros.
        inversion H; subst; auto.
        apply RVariance; auto.
        apply h2.
        rewrite (PathToEq phi0 m M C) in p; auto.
        eapply TypingToProof; eauto.
      + pose proof (Cut_h1MCR Gamma phi C ((ReplaceLabelInModality m lab1 lab2 pi) :: M)).
        simpl in H0.
        rewrite (PathToEq phi0 m M C) in H2; auto.
        pose proof (H0 pf1 H2); clear H0; apply H1; auto.
        apply le_n_S; solve_max_le.
    - destruct (Cut_h1MCR (phi0 @ ReplaceLabelInModality m lab1 lab2 pi :: Gamma) phi C M pf1); auto.
      eapply Exchange; eauto.
      solveSubPath.
      intros.
      eapply Weakening; eauto.
      solveProper.
      solveSubPath.
      apply le_n_S; solve_max_le.
      destruct (Cut_h1MCR _ _ _ _ pf2 H4); auto.
      apply le_n_S; solve_max_le.
      eexists.
      eapply LVariancer; eauto.
  Defined.
  Next Obligation.
    repeat (match goal with
            | [h: _ * _ |- _] => destruct h
            end).
    destruct (Cut_h1MCR _ _ _ _ pf1 H3); eauto.
    apply le_n_S; solve_max_le.
    destruct (Cut_h1MCR _ _ _ _ pf2 H5); eauto.
    apply le_n_S; solve_max_le.
    destruct (Cut_h1MCR _ _ _ _ pf3 H6); eauto.
    apply le_n_S; solve_max_le.
    eexists.
    eapply FwdRr; eauto.
  Defined.
  Next Obligation.
    repeat (match goal with
            | [h: _ * _ |- _] => destruct h
            end).
    destruct (SplitPath (map (fun m : Modality => C @ m) M) Gamma pth'); eauto.
    - destruct (Cut_h1MCR Gamma (canWrite q (LabelAtPrin pth) @ FwdModality pth p) C M pf2); auto.
      apply le_n_S; solve_max_le.
      destruct (Cut_h1MCR Gamma (canRead p (LabelAtPrin pth) @ FwdModality pth q) C M pf3); auto.
      apply le_n_S; solve_max_le.
      assert (forall b : Belief, Path b ((C @ ReplacePrinInModality pth p) :: (map (fun m : Modality => C @ m) M)) -> Gamma ⊢ b).
      + intros.
        inversion H; subst; auto.
        apply FwdR; auto.
        apply h2.
        rewrite (PathToEq phi0 m M C) in p0; auto.
        all: eapply TypingToProof; eauto.
      + pose proof (Cut_h1MCR Gamma phi C ((ReplacePrinInModality pth p) :: M)).
        simpl in H0.
        rewrite (PathToEq phi0 m M C) in H3; auto.
        pose proof (H0 pf1 H3); clear H0; apply H1; auto.
        apply le_n_S; solve_max_le.
    - destruct (Cut_h1MCR (phi0 @ ReplacePrinInModality pth p :: Gamma) phi C M pf1); auto.
      eapply Exchange; eauto.
      solveSubPath.
      intros.
      eapply Weakening; eauto.
      solveProper.
      solveSubPath.
      apply le_n_S; solve_max_le.
      destruct (Cut_h1MCR _ _ _ _ pf2 H5); auto.
      apply le_n_S; solve_max_le.
      destruct (Cut_h1MCR _ _ _ _ pf3 H6); auto.
      apply le_n_S; solve_max_le.
      eexists.
      eapply FwdLr; eauto.
  Defined.
  Next Obligation.
    destruct (Cut_h1MCR _ _ _ _ pf1 H2); eauto.
    apply h3.
    solveCutRel.
    destruct (Cut_h1MCR _ _ _ _ pf2 H4); eauto.
    apply h3.
    solveCutRel.
    eexists.
    econstructor; eauto; fail.
  Defined.
  Next Obligation.
    destruct (Cut_h1MCR _ _ _ _ pf1 H2); eauto.
    apply h3.
    solveCutRel.
    destruct (Cut_h1MCR _ _ _ _ pf2 H4); eauto.
    apply h3.
    solveCutRel.
    eexists.
    econstructor; eauto; fail.
  Defined.    
  Next Obligation.
    unfold MR.
    apply well_founded_ltof.
  Defined.
    
  Obligation Tactic :=
    Tactics.program_simpl;
      timeout 5 (simpl in *; Normalize; Cut_ltac1; simpl in *; Normalize; Cut_ltac1;
                    auto; simpl in *; auto;
                      (try unfold eq_rect in *);
                         (try unfold eq_ind_r in * );
                            (try unfold eq_ind in * );
                               simpl;repeat match goal with
                                            | [ |- context[match ?e with eq_refl => _ end] ] =>
                                              destruct e; simpl
                                            end; auto).

    
  Program Fixpoint AndR_inversion
          {Gamma : Context} {C1 C2 : flafolFormula} {m : Modality}
          (pf : Gamma ⊢ C1 & C2 @ m) {struct pf}
    : (Gamma ⊢ C1 @ m) * (Gamma ⊢ C2 @ m) :=
    match pf with
    | axiom _ _ pctxt pth =>
      (AndL Gamma C1 C2 m (C1 @ m) _ (axiom _ (C1 @ m) _ (Here _ _)),
       AndL Gamma C1 C2 m (C2 @ m) _ (axiom _ (C2 @ m) _ (There _ (Here _ _))))
    | TTR _ m pctxt pmod => _
    | FFL _ _ m' m'' pctxt phi_wf pmod pth pmod' =>
      (FFL Gamma C1 m' m'' pctxt _ pmod pth pmod',
       FFL Gamma C2 m' m'' pctxt _ pmod pth pmod')
    | AndL _ phi psi m' _ pth pf1 =>
      let (pf11, pf12) := AndR_inversion pf1 in
      (AndL Gamma phi psi m' (C1 @ m) pth pf11,
       AndL Gamma phi psi m' (C2 @ m) pth pf12)
    | AndR _ _ _ _ pf1 pf2 => (pf1, pf2)
    | OrL _ phi psi m' _ pth pf1 pf2 =>
      let (pf11, pf12) := AndR_inversion pf1 in
      let (pf21, pf22) := AndR_inversion pf2 in
      (OrL Gamma phi psi m' (C1 @ m) pth pf11 pf21,
       OrL Gamma phi psi m' (C2 @ m) pth pf12 pf22)
    | OrR1 _ phi psi m pf1 psi_wf => _
    | OrR2 _ phi psi m pf1 phi_wf => _
    | ImpL _ phi psi m' l _ pth pf1 pf2 =>
      let (pf21, pf22) := AndR_inversion pf2 in
      (ImpL Gamma phi psi m' l (C1 @ m) pth pf1 pf21,
       ImpL Gamma phi psi m' l (C2 @ m) pth pf1 pf22)
    | ImpR _ phi psi m l pf1 => _
    | forallL _ sigma phi t m' _ lct tsort pth pf1 =>
      let (pf11, pf12) := AndR_inversion pf1 in
      (forallL Gamma sigma phi t m' (C1 @ m) lct tsort pth pf11,
       forallL Gamma sigma phi t m' (C2 @ m) lct tsort pth pf12)
    | forallR _ sigma y phi m' ysort yctxt yconc ym pf1 => _
    | existsL _ sigma y phi m' _ pth ysort yctxt yb pf1 =>
      let (pf11, pf12) := AndR_inversion pf1 in
      (existsL Gamma sigma y phi m' (C1 @ m) pth ysort yctxt _ pf11,
       existsL Gamma sigma y phi m' (C2 @ m) pth ysort yctxt _ pf12)
    | existsR _ sigma t phi m' lct tsort pf1 => _
    | flowsToRefl _ l m' pctxt lLabel pmod => _
    | flowsToTransR _ l1 l2 l3 m' pf1 pf2 => _
    | saysR _ p l phi m' pf1 => _
    | saysL _ p l phi m' _ pth pf1 =>
      let (pf11, pf12) := AndR_inversion pf1 in
      (saysL Gamma p l phi m' (C1 @ m) pth pf11,
       saysL Gamma p l phi m' (C2 @ m) pth pf12)
    | modalityExpandR _ _ m' pth pf1 =>
      let (pf11, pf12) := AndR_inversion pf1 in
      (modalityExpandR Gamma C1 m' pth pf11,
       modalityExpandR Gamma C2 m' pth pf12)
    | modalityCollapseR _ _ m' pth pf1 =>
      let (pf11, pf12) := AndR_inversion pf1 in
      (modalityCollapseR Gamma C1 m' pth pf11,
       modalityCollapseR Gamma C2 m' pth pf12)
    | modalityExpandL _ phi m' pth1 _ pth2 pf1 =>
      let (pf11, pf12) := AndR_inversion pf1 in
      (modalityExpandL Gamma phi m' pth1 (C1 @ m) pth2 pf11,
       modalityExpandL Gamma phi m' pth1 (C2 @ m) pth2 pf12)
    | modalityCollapseL _ phi m' pth1 _ pth2 pf1 =>
      let (pf11, pf12) := AndR_inversion pf1 in
      (modalityCollapseL Gamma phi m' pth1 (C1 @ m) pth2 pf11,
       modalityCollapseL Gamma phi m' pth1 (C2 @ m) pth2 pf12)
    | RVariance _ l1 l2 _ m' pi pf1 pf2 =>
      let (pf11, pf12) := AndR_inversion pf1 in
      (RVariance Gamma l1 l2 C1 m' pi pf11 pf2,
       RVariance Gamma l1 l2 C2 m' pi pf12 pf2)
    | LVariance _ l1 l2 phi m' pi _ pth pf1 pf2 =>
      let (pf11, pf12) := AndR_inversion pf1 in
      (LVariance Gamma l1 l2 phi m' pi (C1 @ m) pth pf11 pf2,
       LVariance Gamma l1 l2 phi m' pi (C2 @ m) pth pf12 pf2)
    | FwdR _ _ m' p q pth pf1 pf2 pf3 =>
      let (pf11, pf12) := AndR_inversion pf1 in
      (FwdR Gamma C1 m' p q pth pf11 pf2 pf3,
       FwdR Gamma C2 m' p q pth pf12 pf2 pf3)
    | FwdL _ phi m' p q pth1 _ pth2 pf1 pf2 pf3 =>
      let (pf11, pf12) := AndR_inversion pf1 in
      (FwdL Gamma phi m' p q pth1 (C1 @ m) pth2 pf11 pf2 pf3,
       FwdL Gamma phi m' p q pth1 (C2 @ m) pth2 pf12 pf2 pf3)
    | CRVariance _ p l1 l2 m pf1 pf2 => _
    | CWVariance _ p l1 l2 m pf1 pf2 => _
    end.
  
  Next Obligation.
    pose proof (provenProperBelief pf) as H; inversion H.
    inversion H1.
    apply Forall_cons; [constructor; auto; fail|].
    apply Forall_cons; [constructor; auto; fail| auto].
  Defined.
  Next Obligation.
    pose proof (provenProperBelief pf) as H; inversion H.
    inversion H1.
    apply Forall_cons; [constructor; auto; fail|].
    apply Forall_cons; [constructor; auto; fail| auto].
  Defined.
  Next Obligation.
    inversion phi_wf; auto.
  Defined.
  Next Obligation.
    inversion phi_wf; auto.
  Defined.
  Next Obligation.  
    intro Hc. apply yb. inversion Hc. constructor; auto; fail.
    constructor; constructor; auto; fail.
  Defined.
  Next Obligation.
    intro Hc. apply yb. inversion Hc. constructor; auto; fail.
    constructor; constructor; auto; fail.
  Defined.

  Lemma AndR_inversion_typing : forall t G phi psi m, typing G t (phi & psi @ m) -> (sigT (fun t' => typing G t' (phi @ m))) * (sigT (fun t' => typing G t' (psi @ m))).
  Proof.
    intros t G phi psi m H.
    apply TypingToProof in H.
    apply AndR_inversion in H.
    destruct H.
    apply ProofToTyping in p.
    apply ProofToTyping in p0; auto.
  Defined.
    

  Program Definition _TTL_inversion_helper1 (Gamma : Context) (b1 b : Belief)
          (pth : Path b Gamma) : Path b (b1 :: Gamma) :=
    There b1 pth.
  Program Definition _TTL_inversion_helper2 (Gamma : Context) (b1 b2 b : Belief)
          (pth : Path b Gamma) : Path b (b1 :: b2 :: Gamma) :=
    There b1 (There b2 pth).

  Program Fixpoint RemoveTrues (Gamma : Context) : Context :=
    match Gamma with
    | [] => []
    | b :: Delta => match b with
              | (phi @ _) =>
                match phi with
                | TT => RemoveTrues Delta
                | _ => b :: RemoveTrues Delta
                end
              end
    end.

  Theorem RemoveTruesSubset : forall Gamma b, In b (RemoveTrues Gamma) -> In b Gamma.
  Proof.
    intros Gamma b H.
    induction Gamma.
    inversion H.
    simpl in H; destruct a as [phi m]; destruct phi;
      try (destruct H; [rewrite H; left; auto | right; apply IHGamma; auto]).
    right; apply IHGamma; auto.
  Qed.

  Theorem RemoveTruesInNotTrue : forall Gamma m phi, In (phi @ m) Gamma -> phi <> TT ->
                                          In (phi @ m) (RemoveTrues Gamma).
  Proof.
    intros Gamma m phi H H0.
    induction Gamma; [inversion H |].
    simpl. destruct a as [psi m']; destruct psi.
    all: destruct H; [try(left; auto) | try(right; apply IHGamma; auto)].
    exfalso; inversion H; apply H0; auto.
    apply IHGamma; auto.
  Qed.

  Theorem RemoveTruesProper : forall {Gamma}, ProperContext Gamma -> ProperContext (RemoveTrues Gamma).
  Proof.
    unfold ProperContext; intros Gamma H.
    induction Gamma.
    simpl; apply Forall_nil.
    simpl. destruct a as [phi m].
    destruct phi.
    all: try (let H1 := fresh in
              let H2 := fresh in
              pose proof (Forall_inv_car _ _ _ _ H) as H1;
              pose proof (Forall_inv_cdr _ _ _ _ H) as H2;
              apply Forall_cons; [exact H1| apply IHGamma; exact H2]).
    pose proof (Forall_inv_cdr _ _ _ _ H) as H1; apply IHGamma; auto.
  Qed.

  Theorem NFVCRemoveTrues : forall {x Gamma}, x ∉FVC Gamma -> x ∉FVC (RemoveTrues Gamma).
  Proof.
    intros x Gamma H.
    intro Hc; apply H; clear H.
    induction Gamma; auto.
    destruct a as [phi m].
    unfold freeInContext in Hc.
    rewrite Exists_exists in Hc.
    destruct Hc as [b Hb]; destruct Hb as [bInRTs xInFVBb].
    simpl in bInRTs. destruct phi.
    apply Exists_cons_tl. rewrite Exists_exists.
    exists b; split; auto.
    apply RemoveTruesSubset; auto.
    all: unfold freeInContext; rewrite Exists_exists; exists b; split; auto;
      destruct bInRTs; [left; auto | right; apply RemoveTruesSubset; auto].
  Qed.   


  Program Definition RemoveTruesRepath :
    forall {m phi Gamma}, TT <> phi -> Path (phi @ m) Gamma -> Path (phi @ m) (RemoveTrues Gamma) :=
    fun m phi Gamma n pth => InToPath BeliefEqDec 
                                (RemoveTruesInNotTrue Gamma m phi (PathToIn pth) (fun e => n (eq_sym e))).

  Ltac TTL_inversion_In_helper :=
    repeat match goal with
                      | [H : ?P |- ?P ] => exact H
                      | [H : In ?b (match ?psi as _ return _ with
                                    | _ => _
                                    end _) |- _ ] => destruct psi
                      | [H : In ?b (?x :: ?xs) |- _ ] => destruct H
                      | [H : ?x = ?b |- ?x = ?b \/ _ ] => left; exact H
                      | [H : ?b = ?x |- ?x = ?b \/ _ ] => left; symmetry; exact H
                      | [ |- _ \/ _ ] => right
                      | [H : In ?b (RemoveTrues ?Gamma) |- In ?b ?Gamma ] => apply RemoveTruesSubset
                      end.
  Ltac TTL_inversion_ProperContext_helper :=
    repeat match goal with
                      | [H :?P |- ?P] => exact H
                      | [H : ProperContext ?Gamma |- ProperContext (RemoveTrues ?Gamma) ] =>
                        apply RemoveTruesProper; exact H
                      | [H : Forall ProperBelief ?Gamma |- _ ] =>
                        match goal with
                        | [ _ : ProperContext Gamma |- _ ] => fail 1
                        | _ =>
                          assert (ProperContext Gamma) by (unfold ProperContext; exact H)
                        end
                      | [ |- Forall ProperBelief _ ] => fold ProperContext
                      | [H : ?Gamma ⊢ _ |- _] =>
                        match goal with
                        | [_ : ProperContext Gamma |- _ ] => fail 1
                        | _ =>
                          pose proof (provenProperContext H)
                        end
                      | [H : ProperContext (?b :: ?Gamma) |- _ ] =>
                        match goal with
                        | [_ : ProperBelief b, _ : ProperContext Gamma |- _ ] => fail 1
                        | [_ : ProperBelief b, _ : Forall ProperBelief Gamma |- _ ] => fail 1
                        | _ =>
                          let H1 := fresh in
                          pose (H1 := H);
                          unfold ProperContext in H1;
                          pose proof (Forall_inv_car _ _ _ _ H1);
                          pose proof (Forall_inv_cdr _ _ _ _ H1);
                          clear H1
                        end
                      | [H : ProperBelief ?b |- ProperContext (?b :: ?Gamma) ] =>
                        apply Forall_cons; [exact H|]
                      end.
  Ltac TTL_inversion_eq_helper :=
    repeat match goal with
           | [ |- context[match ?phi as _ return _ with
                         | _ => _
                         end _] ] => destruct phi
           | [ |- ?a = ?a ] => reflexivity
           | [ H : ?a <> ?a |- _] => exfalso; apply H; reflexivity
           | [ H : ?a = ?b |- _] => inversion H; fail
           | [ H : JMeq _ _ |- _ ] => clear H
           end.

  Obligation Tactic := Tactics.program_simpl;
                        try (TTL_inversion_In_helper; fail);
                        try (TTL_inversion_ProperContext_helper; fail);
                        try (TTL_inversion_eq_helper; fail).

  Program Fixpoint TTL_inversion1 {Gamma : Context} {b : Belief} (pf : Gamma ⊢ b)
    : (RemoveTrues Gamma) ⊢ b :=
    match pf with
    | axiom _ _ pctxt pth =>
      match b with
      | (phi @ m) => match phi with
                  | TT => TTR _ m (RemoveTruesProper pctxt) _
                  | _ => axiom _ b (RemoveTruesProper pctxt) (RemoveTruesRepath _ pth)
                  end
      end
    | TTR _ m pctxt pmod =>
      TTR _ m (RemoveTruesProper pctxt) pmod
    | FFL _ phi m m' pctxt phi_wf pmod pth pmod' =>
      FFL _ phi m m' (RemoveTruesProper pctxt) phi_wf pmod (RemoveTruesRepath _ pth) pmod'
    | AndL _ phi psi m _ pth pf1 =>
      match phi with
      | TT => match psi with
             | TT => (* Both might be true, but TT & TT is not TT *)
               AndL _ TT TT m b (RemoveTruesRepath _ pth) 
                   (Weakening (TTL_inversion1 pf1) (TT @ m :: TT @ m :: (RemoveTrues Gamma))
                               _ _)
             | _ => AndL _ TT psi m b (RemoveTruesRepath _ pth)
                        (Weakening (TTL_inversion1 pf1) (TT @ m :: psi @ m :: (RemoveTrues Gamma))
                                   _ _)
             end
      | _ => match psi with
            | TT => AndL _ phi TT m b (RemoveTruesRepath _ pth)
                        (Weakening (TTL_inversion1 pf1) (phi @ m :: TT @ m :: (RemoveTrues Gamma))
                                   _ _)
            | _ => AndL _ phi psi m b (RemoveTruesRepath _ pth) (TTL_inversion1 pf1)
            end
      end
    | AndR _ phi psi m pf1 pf2 =>
      AndR _ phi psi m (TTL_inversion1 pf1) (TTL_inversion1 pf2)
    | OrL _ phi psi m _ pth pf1 pf2 =>
      OrL _ phi psi m b (RemoveTruesRepath _ pth)
          (match phi with
           | TT =>
             Weakening (TTL_inversion1 pf1) (TT @ m :: RemoveTrues Gamma) _
                       (fun b pth => There (TT @ m) pth)
           | _ => TTL_inversion1 pf1
           end)
          (match psi with
           | TT =>
             Weakening (TTL_inversion1 pf2) (TT @ m :: RemoveTrues Gamma) _
                       (fun b pth => There (TT @ m) pth)
           | _ => TTL_inversion1 pf2
           end)
    | OrR1 _ phi psi m pf1 psi_wf =>
      OrR1 _ phi psi m (TTL_inversion1 pf1) psi_wf
    | OrR2 _ phi psi m pf1 phi_wf =>
      OrR2 _ phi psi m (TTL_inversion1 pf1) phi_wf
    | ImpL _ phi psi m l _ pth pf1 pf2 =>
      ImpL _ phi psi m l b (RemoveTruesRepath _ pth)
           (TTL_inversion1 pf1)
           (match psi with
            | TT =>
              Weakening (TTL_inversion1 pf2) (TT @ m :: RemoveTrues Gamma) _
                        (fun b pth => There (TT @ m) pth)
            | _ =>
              TTL_inversion1 pf2
            end)
    | ImpR _ phi psi m l pf1 =>
      ImpR _ phi psi m l
           (match phi with
            | TT =>
              Weakening (TTL_inversion1 pf1) (TT @ ⟨l⟩ :: RemoveTrues Gamma) _
                        (fun b pth => There (TT @ ⟨l⟩) pth)
            | _ => TTL_inversion1 pf1
            end)
    | forallL _ sigma phi t m _ pth lct tsort pf1 =>
      forallL _ sigma phi t m b (RemoveTruesRepath _ pth) lct tsort
              (match (open_formula phi t) with
               | TT => Weakening (TTL_inversion1 pf1) (TT @ m :: RemoveTrues Gamma) _
                                (fun b pth => There (TT @ m) pth)
               | _ => TTL_inversion1 pf1
               end)
    | forallR _ sigma y phi m ysort yctxt yconc ym pf1 =>
      forallR _ sigma y phi m ysort (NFVCRemoveTrues yctxt) yconc ym (TTL_inversion1 pf1)
    | existsL _ sigma y phi m _ pth ysort yctxt yb pf1 =>
      existsL _ sigma y phi m b (RemoveTruesRepath _ pth) ysort _ yb
              (match (open_formula phi (varTerm y)) with
               | TT => Weakening (TTL_inversion1 pf1) (TT@ m :: RemoveTrues Gamma) _
                                (fun b pth => There (TT @ m) pth)
               | _ => TTL_inversion1 pf1
               end)
    | existsR _ sigma t phi m lct tsort pf1 =>
      existsR _ sigma t phi m lct tsort (TTL_inversion1 pf1)
    | flowsToRefl _ l m pctxt lLabel pmod =>
      flowsToRefl _ l m _ lLabel pmod
    | flowsToTransR _ l1 l2 l3 m pf1 pf2 =>
      flowsToTransR _ l1 l2 l3 m (TTL_inversion1 pf1) (TTL_inversion1 pf2)
    | saysR _ p l phi m pf1 =>
      saysR _ p l phi m (TTL_inversion1 pf1)
    | saysL _ p l phi m _ pth pf1 =>
      saysL _ p l phi m _ (RemoveTruesRepath _ pth)
            (match phi with
             | TT => Weakening (TTL_inversion1 pf1) (TT @ m ⋅ p⟨l⟩ :: RemoveTrues Gamma) _
                              (fun b pth => There (TT @ m ⋅ p⟨l⟩) pth)
             | _ => TTL_inversion1 pf1
             end)
    | modalityExpandR _ phi m pth pf1 =>
      modalityExpandR _ phi m pth (TTL_inversion1 pf1)
    | modalityCollapseR _ phi m pth pf1 =>
      modalityCollapseR _ phi m pth (TTL_inversion1 pf1)
    | modalityExpandL _ phi m pth1 _ pth2 pf1 =>
      match phi with
      | TT => TTL_inversion1 pf1
      | _ => modalityExpandL _ phi m pth1 b (RemoveTruesRepath _ pth2) (TTL_inversion1 pf1)
      end
    | modalityCollapseL _ phi m pth1 _ pth2 pf1 =>
      match phi with
      | TT => TTL_inversion1 pf1
      | _ => modalityCollapseL _ phi m pth1 b (RemoveTruesRepath _ pth2) (TTL_inversion1 pf1)
      end
    | RVariance _ l1 l2 phi m pi pf1 pf2 =>
      RVariance _ l1 l2 phi m pi (TTL_inversion1 pf1) (TTL_inversion1 pf2)
    | LVariance _ l1 l2 phi m pi _ pth pf1 pf2 =>
      match phi with
      | TT => TTL_inversion1 pf1
      | _ => LVariance _ l1 l2 phi m pi b (RemoveTruesRepath _ pth) (TTL_inversion1 pf1) (TTL_inversion1 pf2)
      end
    | FwdR _ phi m p q pth pf1 pf2 pf3 =>
      FwdR _ phi m p q pth
           (TTL_inversion1 pf1) (TTL_inversion1 pf2) (TTL_inversion1 pf3)
    | FwdL _ phi m p q pth1 _ pth2 pf1 pf2 pf3 =>
      match phi with
      | TT => TTL_inversion1 pf1
      | _ => FwdL _ phi m p q pth1 b (RemoveTruesRepath _ pth2)
           (TTL_inversion1 pf1) (TTL_inversion1 pf2) (TTL_inversion1 pf3)
      end
    | CRVariance _ p l1 l2 m pf1 pf2 =>
      CRVariance _ p l1 l2 m (TTL_inversion1 pf1) (TTL_inversion1 pf2)
    | CWVariance Gamma p l1 l2 m pf1 pf2 =>
      CWVariance _ p l1 l2 m (TTL_inversion1 pf1) (TTL_inversion1 pf2)
    end.
  Next Obligation.
    pose proof (provenProperBelief pf); inversion H; auto.
  Defined.
  Next Obligation.
    exact (There _ (There _ H)).
  Defined.
  Next Obligation.
    destruct psi; try (exfalso; apply H; reflexivity; fail);
      exact (There _ H0).
  Defined.
  Next Obligation.
    destruct phi; try (exfalso; apply H; reflexivity; fail).
    all: inversion H0; [exact (Here _ _) | exact (There _ (There _ H3))].
  Defined.
  Next Obligation.
    apply Forall_cons; [| apply RemoveTruesProper; exact (provenProperContext pf)].
    constructor. pose proof (provenProperContext pf1). inversion H; subst. inversion H2; auto.
    FindWellFormedFormula'.
  Defined.
  Next Obligation.
    intro Hc. apply yctxt.
    unfold freeInContext in *. rewrite Exists_exists in *.
    destruct Hc as [b' Hb']; destruct Hb' as [b'In yInb'].
    exists b'; split; auto. apply RemoveTruesSubset; auto.
  Defined.
  Next Obligation.
    apply Forall_cons.
    pose proof (provenProperContext pf1). apply Forall_inv_car in H.
    inversion H.
    constructor; auto; FindWellFormedFormula'; fail.
    apply RemoveTruesProper. exact (provenProperContext pf).
  Defined.

  Program Definition TTL_inversion
          {Gamma : Context} {m : Modality} {b : Belief}
          (pf : (TT @ m :: Gamma) ⊢ b) : Gamma ⊢ b :=
    Weakening (TTL_inversion1 pf) Gamma _ _.
  Next Obligation.
    apply (InToPath BeliefEqDec).
    apply RemoveTruesSubset. apply PathToIn. exact H.
  Defined.

  Lemma flowsToRefl_inversion' : forall t M G b lab, typing ((map (fun m => lab ⊑ lab @ m) M) ++ G) t b -> sigT (fun t' => typing G t' b). 
  Proof.
    induction t; simpl; intros; inversion H; subst.
    all : try match goal with
              |[h : Path (_ @ _) (_ ++ _) |- _] => destruct (SplitPath _ _ h) as [h0 | h0]; [try apply PathToEq in h0; try congruence | ]
              end.    
    - apply SplitPath in H1.
      destruct H1.
      destruct b.
      apply PathToEq in p.
      subst.
      eexists.
      apply flowsToReflr.
      eapply ProperContextApp; eauto.
      1, 2: apply TypingToProof in H.
      1, 2: apply provenWFSequent in H.
      1, 2: destruct H as [h1 h2]; inversion h2; auto.
      inversion H1; auto.
      eexists.
      apply axiomr; auto.
      eapply ProperContextApp; eauto.
    - eexists.
      eapply TTRr; auto.
      eapply ProperContextApp; eauto.
    - eexists.
      eapply FFLr; eauto.
      eapply ProperContextApp; eauto.
    - assert (typing (map (fun m : Modality => lab ⊑ lab @ m) M ++ phi @ m :: psi @ m :: G) t b).
      eapply Exchange; eauto.
      solveSubPath.
      edestruct IHt with (1 := H0).
      eexists; econstructor; eauto; fail.
    - edestruct IHt1 with (1 := H3).
      edestruct IHt2 with (1 := H5).
      eexists; econstructor; eauto; fail.
    - assert (typing (map (fun m : Modality => lab ⊑ lab @ m) M ++ phi @ m :: G) t1 b).
      eapply Exchange; eauto.
      solveSubPath.
      assert (typing (map (fun m : Modality => lab ⊑ lab @ m) M ++ psi @ m :: G) t2 b).
      eapply Exchange; eauto.
      solveSubPath.
      edestruct IHt1 with (1 := H0).
      edestruct IHt2 with (1 := H1).
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (1 := H1).
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (1 := H1).
      eexists; econstructor; eauto; fail.
    - assert (typing (map (fun m : Modality => lab ⊑ lab @ m) M ++ psi @ m :: G) t2 b).
      eapply Exchange; eauto.
      solveSubPath.
      edestruct IHt1 with (1 := H3).
      edestruct IHt2 with (1 := H0).
      eexists; econstructor; eauto; fail.
    - assert (typing (map (fun m : Modality => lab ⊑ lab @ m) M ++ phi @ ⟨ l ⟩ :: G) t (psi @ m')).
      eapply Exchange; eauto.
      solveSubPath.
      edestruct IHt with (1 := H0).
      eexists; econstructor; eauto; fail.
    - assert (typing (map (fun m : Modality => lab ⊑ lab @ m) M ++ open_formula phi t0 @ m :: G) t b).
      eapply Exchange; eauto.
      solveSubPath.
      edestruct IHt with (1 := H0).
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (1 := H6).
      eexists; eapply forallRr with (y := y); eauto.
      intro.
      apply H2.
      clear H6 H H2.
      induction M; simpl; auto.
      apply Exists_cons_tl; eauto.
    - assert (typing (map (fun m : Modality => lab ⊑ lab @ m) M ++ open_formula phi (varTerm y) @ m :: G) t b).
      eapply Exchange; eauto.
      solveSubPath.
      edestruct IHt with (1 := H0).
      eexists; eapply existsLr with (y := y); eauto.
      intro; apply H2.
      clear pth H5 H0 H2 H.
      induction M; simpl; auto.
      econstructor; eauto; fail.
    - edestruct IHt with (1 := H4).
      eexists; econstructor; eauto; fail.
    - eexists.
      eapply flowsToReflr; eauto.
      eapply ProperContextApp; eauto.
    - edestruct IHt1 with (1 := H3).
      edestruct IHt2 with (1 := H5).
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (1 := H2).
      eexists; econstructor; eauto; fail.
    - assert (typing (map (fun m : Modality => lab ⊑ lab @ m) M ++ phi @ m ⋅ p ⟨ lab0 ⟩ :: G) t b).
      eapply Exchange; eauto.
      solveSubPath.
      edestruct IHt with (1 := H0).
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (1 := H2).
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (1 := H2).
      eexists; econstructor; eauto; fail.
    - subst.      
      edestruct IHt with (1 := H2) (M := m :: M) (lab := lab) (G := G) (b := b).
      eexists.
      apply t0.
    - assert (typing (map (fun m : Modality => lab ⊑ lab @ m) M ++ phi @ m :: G) t b).
      eapply Exchange; eauto.
      solveSubPath.
      edestruct IHt with (1 := H0).
      eexists; econstructor; eauto; fail.
    - subst.      
      edestruct IHt with (1 := H2) (M := (CollapseDoubleInModality pth) :: M) (lab := lab) (G := G) (b := b).
      eexists.
      apply t0.
    - assert (typing (map (fun m : Modality => lab ⊑ lab @ m) M ++ phi @ (CollapseDoubleInModality pth) :: G) t b).
      eapply Exchange; eauto.
      solveSubPath.
      edestruct IHt with (1 := H0).
      eexists; econstructor; eauto; fail.
    - edestruct IHt1 with (1 := H3).
      edestruct IHt2 with (1 := H5).
      eexists; econstructor; eauto; fail.
    - subst.
      edestruct IHt1 with (1 := H3) (M := (ReplaceLabelInModality m lab1 lab2 pi) :: M) (lab := lab) (G := G) (b := b).
      eexists.
      apply t.
    - assert (typing (map (fun m : Modality => lab ⊑ lab @ m) M ++ phi @ (ReplaceLabelInModality m lab1 lab2 pi) :: G) t1 b).
      eapply Exchange; eauto.
      solveSubPath.
      edestruct IHt1 with (1 := H0).
      edestruct IHt2 with (1 := H5).
      eexists; econstructor; eauto; fail.
    - edestruct IHt1 with (1 := H4).
      edestruct IHt2 with (1 := H6).
      edestruct IHt3 with (1 := H7).
      eexists; econstructor; eauto; fail.
    - subst.
      edestruct IHt1 with (1 := H4) (M := ( ReplacePrinInModality pth p) :: M) (lab := lab) (G := G) (b := b).
      eexists.
      apply t.
    - assert (typing (map (fun m : Modality => lab ⊑ lab @ m) M ++ phi @ ( ReplacePrinInModality pth p) :: G) t1 b).
      eapply Exchange; eauto.
      solveSubPath.
      edestruct IHt1 with (1 := H0).
      edestruct IHt2 with (1 := H6).
      edestruct IHt3 with (1 := H7).
      eexists; econstructor; eauto; fail.
    - edestruct IHt1 with (1 := H3).
      edestruct IHt2 with (1 := H5).
      eexists; econstructor; eauto; fail.
    - edestruct IHt1 with (1 := H3).
      edestruct IHt2 with (1 := H5).
      eexists; econstructor; eauto; fail.
  Qed.

  Corollary flowsToRefl_inversion : forall {t m G b lab}, typing (lab ⊑ lab @ m :: G) t b -> sigT (fun t' => typing G t' b). 
  Proof.
    intros.
    eapply flowsToRefl_inversion' with (M := [m]).
    simpl; eauto.
  Defined.  


  Lemma ColExpFV : forall m (pth : PathToDoubleInModality m) y phi, y ∈FVB phi @ CollapseDoubleInModality pth <-> y ∈FVB phi @ m.
  Proof.
    induction pth; simpl; intros.
    - split; intro h.
      + inversion h; subst.
        constructor.
        inversion H1; subst; auto; econstructor; eauto; fail.
        econstructor; eauto; fail.
      + inversion h; subst.
        constructor.
        inversion H1; subst; auto; try (econstructor; eauto; fail).
        econstructor; eauto; fail.
    - destruct (IHpth y phi).
      split; intro h.
      + inversion h; subst.
        inversion H3; subst.
        4 : econstructor; eauto; fail.
        pose proof (H (freeInMB y _ phi H4)).
        2, 3 : constructor.
        2, 3 : try (econstructor; eauto; fail).
        inversion H1; subst.
        constructor.
        all : econstructor; eauto; fail.
      + inversion h; subst; auto.
        inversion H3; subst.
        pose proof (H0 (freeInMB y _ phi H4)).
        inversion H1; subst.
        1, 3, 4 : constructor.
        all : econstructor; eauto; fail.
  Qed.
        
  
  Definition PFI := fun t => forall {Gamma : Context} {sigma : sort} {phi : flafolFormula} 
                              {m : Modality} (pf : typing Gamma t (∀ sigma; phi @ m)), sigT (fun y =>
      prod ((VarSort y = sigma)) (prod (y ∉FVC Gamma) (prod ( y ∉FVB (phi@m)) (sigT (fun t' => typing Gamma t' (open_formula phi (varTerm y) @ m)))))). 
    
  Lemma forallR_inversion : forall {t : proofTerm} {Gamma : Context} {sigma : sort} {phi : flafolFormula} 
                              {m : Modality} (pf : typing Gamma t (∀ sigma; phi @ m)), sigT (fun y =>
      prod ((VarSort y = sigma)) (prod (y ∉FVC Gamma) (prod ( y ∉FVB (phi@m)) (sigT (fun t' => typing Gamma t' (open_formula phi (varTerm y) @ m)))))). 
  Proof.
    pose proof (@Fix _ (fun x1 x2 => term_size x1 < term_size x2) (well_founded_ltof _ _) PFI).
    apply H.
    clear H.
    unfold PFI in *.
    intros t IHt.
    destruct t; simpl in *; intros; inversion pf; subst.
    - pose (freshInSequent Gamma (phi @ m) sigma) as y'.
      exists y'.
      repeat split.
      all : try apply freshInSequentIsFresh; auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      eexists.
      eapply forallLr with (t := varTerm y'); eauto. constructor. 
      unfold y'.
      unfold freshInSequent.
      erewrite <- freshVarSameSort.
      constructor.
      eapply axiomr.
      constructor; auto.
      InstantiateProper.
      inversion H2; subst.
      pose (freshVar L sigma) as x.
      pose proof (H4 x).
      assert (⊢s varTerm x ::: sigma) by (unfold x; erewrite <- freshVarSameSort; econstructor).
      eapply WFopen_formula_rec with (t1 := varTerm x) (s := sigma); auto.      
      unfold y'; erewrite <- freshVarSameSort; econstructor.
      apply H3; auto.
      apply freshVarNotIn.
      apply Here.
    - pose (freshInSequent Gamma (phi @ ModalityCombine m0 m') sigma) as y'.
      exists y'.
      repeat split.
      all : try apply freshInSequentIsFresh; auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      eexists.
      eapply FFLr; auto.
      inversion H2; subst.
      pose (freshVar L sigma) as x.
      pose proof (H0 x).
      assert (⊢s varTerm x ::: sigma) by (unfold x; erewrite <- freshVarSameSort; econstructor).
      eapply WFopen_formula_rec with (t1 := varTerm x) (s := sigma); auto.      
      unfold y'; erewrite <- freshVarSameSort; econstructor.
      apply H; auto.
      apply freshVarNotIn.
    - edestruct (IHt t) with (2 := H1) as [y' [eq [ni1 [n2 [t' T']]]]]; auto.
      exists y'.
      repeat split; auto.
      eapply FreshWithMore.
      2: eauto.
      intros.
      simpl; auto.
      eexists; econstructor; eauto; fail.
    - edestruct (IHt t1) with (2 := H2) as [y' [eq [ni1 [n2 [t' T']]]]]; auto.
      simpl; solveCutRel.
      edestruct (IHt t2) with (2 := H4) as [y'' [eq' [ni1' [n2' [t'' T'']]]]]; auto.
      simpl; solveCutRel.
      exists y'.
      repeat split; auto.
      eapply FreshWithMore.
      2: eauto.
      intros.
      simpl; auto.
      assert (sigT (fun t1 => typing (psi @ m0 :: Gamma) t1 (open_formula phi (varTerm y') @ m))).
      eapply open_with_fresherRT; eauto.
      etransitivity; eauto.
      1, 2 : intro; apply n2'.      
      1, 2 : econstructor; eauto; fail.
      destruct H.
      eexists; econstructor; eauto; fail.
    - edestruct (IHt t2) with (2 := H4) as [y'' [eq' [ni1' [n2' [t'' T'']]]]]; auto.
      simpl; solveCutRel.
      exists y''.
      repeat split; auto.
      eapply FreshWithMore.
      2: eauto.
      intros.
      simpl; auto.
      eexists; econstructor; eauto; fail.
    - edestruct (IHt t) with (2 := H3) as [y'' [eq' [ni1' [n2' [t'' T'']]]]]; auto.
      exists y''.
      repeat split; auto.
      eapply FreshWithMore.
      2: eauto.
      intros.
      simpl; auto.
      eexists; econstructor; eauto; fail.
    - exists y.
      repeat split; auto.
      intro.
      inversion H; subst; auto.
      eauto.
    - pose (freshInSequent Gamma (∀ sigma; phi @ m) (VarSort y)) as y2.
      assert (sigT (fun t1 => prod (typing ((open_formula phi0 (varTerm y2) @ m0 :: Gamma)) t1 (∀ sigma; phi @ m)) (term_size t = term_size t1))).
      eapply open_with_fresherLTS'; eauto.
      unfold y2; rewrite freshInSequentOfSort; auto.
      destruct H as [t' [H4' eq]].
      edestruct (IHt t') with (2 := H4') as [y'' [eq' [ni1' [n2' [t'' T'']]]]]; auto.
      rewrite eq; auto.
      pose (freshVar (y2 :: varsInContext (open_formula phi (varTerm y2) @ m :: Gamma) ++ varsInBelief (open_formula phi (varTerm y'') @ m) ++ varsInBelief (phi @ m)) (VarSort y'')) as y3.
      assert (sigT (fun t1 => typing ((open_formula phi0 (varTerm y2) @ m0 :: Gamma)) t1 ( open_formula phi (varTerm y3) @ m))).
      eapply open_with_fresherRT; eauto.
      unfold y3; rewrite freshVarSameSort; auto.
      1, 2 : intro; apply n2'; econstructor; eauto; fail.
      destruct H.
      exists y3.
      repeat split; auto.
      unfold y3; rewrite freshVarSameSort; auto.
      1, 2 : assert ((In y3 (y2 :: varsInContext (open_formula phi (varTerm y2) @ m :: Gamma) ++
                           varsInBelief (open_formula phi (varTerm y'') @ m) ++ varsInBelief (phi @ m))) -> False) by (unfold y3; apply freshVarNotIn); intro; apply H.
      { simpl.
        right.
        apply PathToIn.
        apply PathSplit.
        left.
        apply PathSplit.
        right.
        apply InToPath.
        apply varEqDec.
        apply freeVarsInContext; auto. }
      { simpl.
        right.
        apply PathToIn.
        apply PathSplit.
        right.
        apply PathSplit.
        right.
        apply InToPath.
        apply varEqDec.
        apply freeVarsInBelief in H0; auto. }
      eexists.
      eapply existsLr with (y := y2); eauto.
      unfold y2; rewrite freshInSequentOfSort; auto.
      apply freshInSequentIsFresh.
      intro.
      inversion H; subst.
      destruct (freshInSequentIsFresh Gamma (∀ VarSort y''; phi @ m) (VarSort y)).
      apply H3.
      constructor; auto.      
      revert H5.
      apply openFVF.
      intro.
      inversion H0; subst.
      assert ((In y3 (y2 :: varsInContext (open_formula phi (varTerm y2) @ m :: Gamma) ++
                           varsInBelief (open_formula phi (varTerm y'') @ m) ++ varsInBelief (phi @ m))) -> False) by (unfold y3; apply freshVarNotIn).
      apply H3.
      simpl; auto.
      destruct (freshInSequentIsFresh Gamma (∀ VarSort y''; phi @ m) (VarSort y)).
      intro.
      apply H3.
      econstructor; econstructor; simpl; eauto; fail.
    - edestruct (IHt t) with (2 := H1) as [y'' [eq' [ni1' [n2' [t'' T'']]]]]; auto.
      exists y''.
      repeat split; auto.
      eapply FreshWithMore.
      2: eauto.
      intros.
      simpl; auto.
      eexists; econstructor; eauto; fail.
    - edestruct (IHt t) with (2 := H2) as [y'' [eq' [ni1' [n2' [t'' T'']]]]]; auto.
      exists y''.
      repeat split; auto.
      intro.
      apply n2'.
      apply ColExpFV; auto.
      eexists; econstructor; eauto; fail.
    - edestruct (IHt t) with (2 := H2) as [y'' [eq' [ni1' [n2' [t'' T'']]]]]; auto.
      exists y''.
      repeat split; auto.
      intro.
      apply n2'.
      eapply ColExpFV; eauto.
      eexists; econstructor; eauto; fail.
    - edestruct (IHt t) with (2 := H1) as [y'' [eq' [ni1' [n2' [t'' T'']]]]]; auto.
      exists y''.
      repeat split; auto.
      eapply FreshWithMore.
      2: eauto.
      intros.
      simpl; auto.
      eexists; econstructor; eauto; fail.
    - edestruct (IHt t) with (2 := H1) as [y'' [eq' [ni1' [n2' [t'' T'']]]]]; auto.
      exists y''.
      repeat split; auto.
      eapply FreshWithMore.
      2: eauto.
      intros.
      simpl; auto.
      eexists; econstructor; eauto; fail.
    - edestruct (IHt t1) with (2 := H3) as [y'' [eq' [ni1' [n2' [t'' T'']]]]]; auto.
      simpl; solveCutRel.
      pose (freshInSequent (phi @ ReplaceLabelInModality m0 lab1 lab2 pi :: Gamma) (open_formula phi (varTerm y'') @ m0) sigma) as y2.
      assert (sigT (fun t1 => typing Gamma t1 (open_formula phi (varTerm y2) @ m0))).
      eapply open_with_fresherRT; eauto.
      unfold y2; rewrite freshInSequentOfSort; auto.
      1, 2 : intro; apply n2'.
      1, 2 : econstructor; eauto; fail.
      destruct (freshInSequentIsFresh (phi @ ReplaceLabelInModality m0 lab1 lab2 pi :: Gamma) (open_formula phi (varTerm y'') @ m0) sigma).
      destruct H.
      exists y2.
      repeat split; auto.
      unfold y2; rewrite freshInSequentOfSort; auto.
      1, 2 : intro; apply H0.
      1, 2 : econstructor; eauto; fail.
      eexists; econstructor; eauto; fail.
    - edestruct (IHt t1) with (2 := H2) as [y'' [eq' [ni1' [n2' [t'' T'']]]]]; auto.
      simpl; solveCutRel.
      exists y''.
      repeat split; auto.
      eapply FreshWithMore.
      2: eauto.
      intros.
      simpl; auto.
      eexists; econstructor; eauto; fail.
    - edestruct (IHt t1) with (2 := H4) as [y'' [eq' [ni1' [n2' [t'' T'']]]]]; auto.
      simpl; solveCutRel.
      pose (freshInSequent (phi @ ReplacePrinInModality pth q :: Gamma) (open_formula phi (varTerm y'') @ m0) sigma) as y2.
      assert (sigT (fun t1 => typing Gamma t1 (open_formula phi (varTerm y2) @ m0))).
      eapply open_with_fresherRT; eauto.
      unfold y2; rewrite freshInSequentOfSort; auto.
      1, 2 : intro; apply n2'.
      1, 2 : econstructor; eauto; fail.
      destruct (freshInSequentIsFresh (phi @ ReplacePrinInModality pth q :: Gamma) (open_formula phi (varTerm y'') @ m0) sigma).
      destruct H.
      exists y2.
      repeat split; auto.
      unfold y2; rewrite freshInSequentOfSort; auto.
      1, 2 : intro; apply H0.
      1, 2 : econstructor; eauto; fail.
      eexists; econstructor; eauto; fail.
    - edestruct (IHt t1) with (2 := H3) as [y'' [eq' [ni1' [n2' [t'' T'']]]]]; auto.
      simpl; solveCutRel.
      exists y''.
      repeat split; auto.
      eapply FreshWithMore.
      2: eauto.
      intros.
      simpl; auto.
      eexists; econstructor; eauto; fail.
  Qed.
    
  
  Lemma ImpR_inversion {Gamma : Context} {l : flafolTerm} {phi psi : flafolFormula} {m : Modality} {t : proofTerm} (pf : typing Gamma t (phi ==⟨ l ⟩> psi @ m)) : sigT (fun t' : proofTerm => typing ((phi @ ⟨ l ⟩) :: Gamma) t' (psi @ m)).
  Proof.
    revert Gamma l phi psi m pf.
    induction t; simpl; intros; inversion pf; subst; eauto.
    - eexists.
      eapply ImpLr.
      apply There; eauto.
      apply axiomr; eauto.
      constructor; auto.
      InstantiateProper; auto; inversion H2; auto.
      apply Here.
      apply axiomr; eauto.
      constructor.
      InstantiateProper; auto; inversion H2; auto.
      constructor; auto.
      InstantiateProper; auto; inversion H2; auto.      
      apply Here.      
    - eexists.
      apply FFLr; auto.
      constructor; auto.
      inversion H2; subst.
      repeat constructor; auto.
      inversion H2; auto.
      apply There; auto.
    - destruct (IHt _ _ _ _ _ H1).
      eexists.
      eapply AndLr.
      apply There; eauto.
      eapply (Exchange x); eauto; try solve [solveSubPath].
    - destruct (IHt1 _ _ _ _ _ H2).
      destruct (IHt2 _ _ _ _ _ H4).
      eexists.
      eapply OrLr.
      apply There; eauto.
      eapply (Exchange x); eauto; try solve [solveSubPath].
      eapply (Exchange x0); eauto; try solve [solveSubPath].
    - destruct (IHt2 _ _ _ _ _ H4).
      eexists.
      eapply ImpLr; eauto.
      apply There; eauto.
      eapply WeakeningTyping; eauto; try solve [solveSubPath].
      repeat solveProper.
      eapply (Exchange x); eauto; try solve [solveSubPath].
    - destruct (IHt _ _ _ _ _ H3).
      eexists.
      eapply forallLr; eauto.
      apply There; eauto.
      eapply (Exchange x); eauto; try solve [solveSubPath].
    - destruct (IHt _ _ _ _ _ H4).
      eexists.
      eapply existsLr.
      apply There; eauto.
      reflexivity.
      intro.
      inversion H; subst; auto.
      inversion H3; subst.
      apply H2.
      inversion H6; subst.
      apply freeInPhiB.
      apply freeInImpLabel; auto.
      apply H2.
      apply freeInPhiB.
      apply freeInImpL; auto.
      intro.
      apply H2.
      inversion H; subst.
      econstructor; eauto; fail.
      econstructor; econstructor; eauto; fail.
      eapply (Exchange x); eauto; try solve [solveSubPath].
    - destruct (IHt _ _ _ _ _ H1).
      eexists.
      eapply saysLr.
      apply There; eauto.
      eapply (Exchange x); eauto; try solve [solveSubPath].
    - destruct (IHt _ _ _ _ _ H2).
      eexists.
      eapply modalityExpandRr; eauto.
    - destruct (IHt _ _ _ _ _ H2).
      eexists.
      eapply modalityCollapseRr; eauto.
    - destruct (IHt _ _ _ _ _ H1).
      eexists.
      eapply modalityExpandLr; eauto.
      apply There; eauto.
      eapply (Exchange x); eauto; try solve [solveSubPath].
    - destruct (IHt _ _ _ _ _ H1).
      eexists.
      eapply modalityCollapseLr; eauto.
      apply There; eauto.
      eapply (Exchange x); eauto; try solve [solveSubPath].
    - destruct (IHt1 _ _ _ _ _ H3).
      eexists.
      eapply RVariancer; eauto.
      eapply WeakeningTyping; eauto; try solve [solveSubPath].
      solveProper.
    - destruct (IHt1 _ _ _ _ _ H2).
      eexists.
      eapply LVariancer; eauto.
      apply There; eauto.
      eapply (Exchange x); eauto; try solve [solveSubPath].
      eapply WeakeningTyping; eauto; try solve [solveSubPath].
      repeat solveProper.
    - destruct (IHt1 _ _ _ _ _ H4).
      eexists.
      apply FwdRr; eauto.
      all: eapply WeakeningTyping; eauto; try solve [solveSubPath].
      all: solveProper.
    - destruct (IHt1 _ _ _ _ _ H3).
      eexists.
      eapply FwdLr; eauto.
      apply There; eauto.
      eapply (Exchange x); eauto; try solve [solveSubPath].
      all: eapply WeakeningTyping; eauto; try solve [solveSubPath].
      all: repeat solveProper.
  Qed.
   
  Lemma SaysR_inversion_typing : forall (t : proofTerm) {Gamma : Context} {p l : flafolTerm} {C : flafolFormula} {m : Modality} (pf : typing Gamma t (p □ ⟨l⟩ C @ m)), sigT (fun t' => typing Gamma t' (C @ m ⋅ p⟨l⟩)).
  Proof.
    induction t; simpl; intros; inversion pf; subst; eauto.
    all : try match goal with
              | [IH : forall _ _ _ _ _, typing _ ?t _ -> _, h : typing _ ?t _ |- _] => destruct IH with (1 := h); eexists; econstructor; eauto; fail
              end.
    - eexists.
      eapply saysLr; eauto.
      apply axiomr; auto.
      constructor; auto.
      InstantiateProper; try inversion H2; auto.
      apply Here.
    - eexists.
      assert (ModalityCombine m0 m' ⋅ p ⟨ l ⟩ = ModalityCombine m0 (m' ++ [(p, l)])) .
      clear H6 H5 pf H3.
      revert m0.
      induction m'; simpl; intros; eauto.
      destruct a.
      eauto.
      rewrite H.
      eapply FFLr; eauto.
      inversion H2; auto.
      apply ModalityResidualAppProper; simpl; auto.
      constructor; inversion H0.
      1, 3 : inversion H2; inversion H4; subst; auto.
      all : inversion H4.
     - edestruct IHt1 with (1 := H2).
      edestruct IHt2 with (1 := H4).
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (1 := H4).
      eexists.
      eapply existsLr with (y := y); eauto.
      intro.
      apply H2.
      inversion H; subst.
      inversion H5; subst.
      all : try (econstructor; econstructor; eauto; fail).
      econstructor; eauto; fail.
    - edestruct IHt with (1 := H2).
      eexists.
      apply modalityExpandRr with (pth := thereDouble m p l pth); eauto.
    - edestruct IHt with (1 := H2).
      eexists.
      apply modalityCollapseRr with (pth := thereDouble m0 p l pth); eauto.
    - edestruct IHt1 with (1 := H3).
      eexists.
      eapply RVariancer with (pi := thereLab m0 p lab1 l pi); eauto.
      assert (VarModality (thereLab m0 p lab1 l pi) lab2 = VarModality pi lab2).
      destruct pi; simpl in *; auto.
      rewrite H; eauto.
    - edestruct IHt1 with (1 := H4).
      eexists.      
      eapply FwdRr with (pth := thereP m0 p0 p l pth); eauto.
  Qed.
      
  Lemma substPreservesSize : forall f1 x t, formula_size (f1 f[x ↦ t]) = formula_size f1.
  Proof.
    induction f1; intros; simpl; eauto.
  Qed.
  
  Definition fs {A B C} (x : A * B * C) : A := 
    match x with
    | (x1, x2, x3) => x1
    end.

  Definition sn {A B C} (x : A * B * C) : B := 
    match x with
    | (x1, x2, x3) => x2
    end.

  Definition th {A B C} (x : A * B * C) : C := 
    match x with
    | (x1, x2, x3) => x3
    end.
 
  Definition liftBelief (x : flafolFormula * Modality * ModalityResidual) :=
    match x with
    | (x1, x2, x3) => x1 @ (ModalityCombine x2 x3)        
    end.
  
  Definition PFF := fun t => forall Gamma b M, (typing ((map liftBelief M) ++ Gamma) t b) -> (forall m, Path m M -> Path (FF @ (sn m)) Gamma) -> sigT (fun t' => typing Gamma t' b).

  Lemma liftBeliefPath : forall {M phi m}, Path (phi @ m) (map liftBelief M) -> sigT (fun m1 => sigT (fun m2 => m = ModalityCombine m1 m2)).
  Proof.
    unfold liftBelief.
    induction M; simpl; intros.
    inversion H.
    destruct a as [[x1 x2] x3].
    inversion H; subst; eauto.
  Qed.
  
  Lemma ModalityCombineCons : forall m1' m1 p lab, ModalityCombine m1 (m1' ++ [(p, lab)]) = ModalityCombine m1 m1' ⋅ p ⟨ lab ⟩.
  Proof.
    induction m1'; simpl; auto.
    destruct a.
    intros.
    rewrite IHm1'.
    auto.
  Qed.    
  
                                 
  Lemma ModColPthinv : forall m1' m1 m (pth : PathToDoubleInModality m), CollapseDoubleInModality pth = ModalityCombine m1 m1' -> (sigT (fun m2 => sigT (fun pi' : PathToDoubleInModality m2 => prod (m = ModalityCombine m2 m1') (m1 = CollapseDoubleInModality pi')))) + (sigT (fun m' => m = ModalityCombine m1 m')).
  Proof.
    induction m1'; simpl; intros.
    - left.
      exists m, pth.
      split; auto.      
    - destruct a.
      destruct (IHm1' (m1 ⋅ f ⟨ f0 ⟩) m pth H).
      * destruct s as [m2 [pi' [e1 e2]]].
        rewrite e1.
        destruct pi'.
        simpl in e2.
        inversion e2; subst.
        right.
        exists ((p,l) :: (p,l) :: m1').
        auto.
        simpl in e2.
        inversion e2; subst.
        left.
        exists m0.
        exists pi'.
        split; auto.
      * destruct s.
        right.
        rewrite e.        
        exists ((f,f0) :: x).
        reflexivity.    
  Qed.
    
  Lemma ModExpPthinv : forall m1' m1 m (pth : PathToDoubleInModality m), m = ModalityCombine m1 m1' -> (sigT (fun pi' : PathToDoubleInModality m => sigT (fun m'' => CollapseDoubleInModality pth = (ModalityCombine (CollapseDoubleInModality pi') m'')))) + (sigT (fun m' => CollapseDoubleInModality pth = ModalityCombine m1 m')).
  Proof.
    induction m1'; simpl.
    - intros.
      left.
      exists pth, []; reflexivity.
    - intros.
      destruct a.
      destruct (IHm1' (m1 ⋅ f ⟨ f0 ⟩) m pth H).
      + destruct s.
        destruct s.
        left.
        rewrite e.
        exists x.
        exists x0.
        reflexivity.
      + destruct s.
        right.
        rewrite e.
        exists ((f,f0) :: x).
        reflexivity.      
  Qed.

  Lemma LVariancePthinv : forall m1' m1 m lab1 lab2 (pi : PathToLabelInModality m lab1), m = ModalityCombine m1 m1' -> (sigT (fun pi' : PathToLabelInModality m1 lab1 => prod (ReplaceLabelInModality m lab1 lab2 pi = (ModalityCombine (ReplaceLabelInModality m1 lab1 lab2 pi') m1')) (VarModality pi lab2 = VarModality pi' lab2))) + (sigT (fun m' => ReplaceLabelInModality m lab1 lab2 pi = ModalityCombine m1 m')).
  Proof.    
    induction m1'; simpl.
    - intros.
      left.
      rewrite <-H; auto.
      exists pi; split; reflexivity.
    - intros.
      destruct a.
      destruct (IHm1' (m1 ⋅ f ⟨ f0 ⟩) m lab1 lab2 pi H).
      + destruct s.
        destruct p.
        remember (m1 ⋅ f ⟨ f0 ⟩).
        pose x.
        destruct x.
        inversion Heqm0.
        subst.
        rewrite e.
        simpl.
        inversion Heqm0; subst.
        { right.
          exists ((f, lab2) :: m1').
          reflexivity.
        }
        inversion Heqm0; subst.
        left.
        exists x.
        rewrite e.
        split.
        reflexivity.
        rewrite e0.
        clear IHm1' e Heqm0 p e0 pi.
        simpl.
        induction x; simpl; auto.
      + destruct s.
        right.
        rewrite e.
        exists ((f, f0) :: x).
        reflexivity.
  Qed.

  Lemma FwdLPthinv : forall m1' m1 m p q (pth : PathToPrinInModality m q), m = ModalityCombine m1 m1' -> (sigT (fun pi' : PathToPrinInModality m1 q => prod (prod (ReplacePrinInModality pth p = (ModalityCombine (ReplacePrinInModality pi' p) m1')) (FwdModality pth p = FwdModality pi' p)) (prod (FwdModality pth q = FwdModality pi' q) ((LabelAtPrin pth) = (LabelAtPrin pi'))))) + (sigT (fun m' => ReplacePrinInModality pth p = ModalityCombine m1 m')).
  Proof.    
    induction m1'; simpl.
    - intros.
      left.
      rewrite <-H; auto.
      exists pth; split; split; reflexivity.
    - intros.
      destruct a.
      destruct (IHm1' (m1 ⋅ f ⟨ f0 ⟩) m p q pth H).
      + destruct s.
        repeat destructProd.
        remember (m1 ⋅ f ⟨ f0 ⟩).
        pose x.
        destruct x.
        subst.
        rewrite e1.
        inversion Heqm0; subst.
        { right.
          exists ((p, f0) :: m1').
          reflexivity.
        }
        inversion Heqm0; subst.
        left.
        exists x.
        rewrite e1.
        split.
        { split.
          reflexivity.
          rewrite e2.
          clear IHm1' e Heqm0 p0 e0 e1 e2 pth.
          simpl.
          induction x; simpl; auto. }
        { split.
          rewrite e.
          clear IHm1' e Heqm0 p0 e0 e1 e2 pth.
          induction x; simpl; auto.
          rewrite e0.
          clear IHm1' e Heqm0 p0 e0 e1 e2 pth.
          induction x; simpl; auto. }
      + destruct s.
        right.
        rewrite e.
        exists ((f, f0) :: x).
        reflexivity.
  Qed.
  
  Definition mapBelief (x : flafolFormula * Modality) :=
    match x with
    | (x1, x2) => x1 @ x2      
    end.

  Lemma ModProperApp : forall m1' m1 m, m = ModalityCombine m1 m1' -> ProperModality m -> ProperModality m1 /\ ProperModalityResidual m1'.
  Proof.
    induction m1'; simpl; intros; auto.
    split.
    rewrite <-H; auto.
    constructor; inversion H1.
    destruct a.
    destruct (IHm1' _ _ H); auto.
    split.
    inversion H1; auto.
    intro.
    intros.
    inversion H3; subst; auto.
    inversion H4; subst.
    inversion H1; auto.
  Qed.

    
  Lemma ProperModResApp : forall m m', ProperModalityResidual m -> ProperModalityResidual m' -> ProperModalityResidual (m ++ m').
    induction m; simpl; auto.
    intros.
    intro.
    intros.
    inversion H1; subst.
    unfold ProperModalityResidual in *.
    apply H.
    simpl; auto.
    eapply IHm; eauto.
    intro.
    intros.
    eapply H.
    simpl; auto.
  Qed.    
    

  Lemma FFL_inversion' : forall t Gamma b M (h : typing ((map mapBelief M) ++ Gamma) t b), (forall f m, Path (f @ m) (map mapBelief M) -> (sigT (fun m1 => sigT (fun m1' => prod (m = ModalityCombine m1 m1') (Gamma ⊢ (FF @ m1)))))) -> sigT (fun t' => typing Gamma t' b).
  Proof.
    induction t; simpl; intros; inversion h; subst.
    - destruct (SplitPath _ _ H1).
      + destruct b.
        destruct (H _ _ p) as [m2 [m2' [h1 h2]]].
        rewrite h1.
        apply ProofToTyping in h2.
        destruct h2.
        eapply FFR_inversion; eauto.
        eapply ModProperApp; eauto.
        all : apply PathToIn in H1.
        all : destruct (BeliefInProperContextIsProper _ _ H0 H1); auto. 
      + eexists; econstructor; eauto.
        eapply ProperContextApp; eauto.
    - eexists.
      apply TTRr; auto.
      eapply ProperContextApp; eauto.
    - destruct (SplitPath _ _ H3).
      + destruct (H _ _ p) as [m2 [m2' [h1 h2]]].
        rewrite h1.
        rewrite ModalityCombineApp.
        apply ProofToTyping in h2.
        destruct h2.
        eapply FFR_inversion; eauto.
        apply ProperModResApp; auto.
        eapply ModProperApp; eauto.
      + eexists.
        apply FFLr; eauto.
        eapply ProperContextApp; eauto.
    - destruct (SplitPath _ _ pth).
      + destruct (H _ _ p) as [m2 [m2' [h1 h2]]].
        eapply IHt with (M := (phi, m) :: (psi, m) :: M); auto.
        intros.
        inversion H0; subst.
        exists m2, m2'.        
        split; auto.
        inversion H4; subst; eauto.
      + assert (typing (map mapBelief M ++ phi @ m :: psi @ m :: Gamma) t b).
        eapply Exchange; eauto.
        solveSubPath.
        edestruct IHt with (1 := H0).
        intros.
        destruct (H _ _ H1) as [m1 [m1' []]].
        exists m1, m1'.
        split; auto.
        eapply Weakening; eauto; try solve [solveProper | solveSubPath].
        eexists.
        eapply AndLr; eauto.
    - edestruct IHt1 with (1 := H3); auto.
      edestruct IHt2 with (1 := H5); auto.
      eexists; econstructor; eauto; fail.
    - destruct (SplitPath _ _ pth).
      + destruct (H _ _ p) as [m2 [m2' [h1 h2]]].
        eapply IHt1 with (M := (phi, m) :: M); auto.
        intros.
        inversion H0; subst; eauto.
      + assert (typing (map mapBelief M ++ phi @ m :: Gamma) t1 b).
        eapply Exchange; eauto.
        solveSubPath.
        assert (typing (map mapBelief M ++ psi @ m :: Gamma) t2 b).
        eapply Exchange; eauto.
        solveSubPath.
        edestruct IHt1 with (1 := H0); auto.
        intros.
        destruct (H _ _ H2) as [m1 [m1' []]].
        exists m1, m1'.
        split; auto.
        eapply Weakening; eauto; try solve [solveProper | solveSubPath].
        edestruct IHt2 with (1 := H1).
        intros.
        destruct (H _ _ H2) as [m1 [m1' []]].
        exists m1, m1'.
        split; auto.
        eapply Weakening; eauto; try solve [solveProper | solveSubPath].
        eexists; econstructor; eauto; fail.
    - edestruct IHt with (1 := H1); auto.
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (1 := H1); auto.
      eexists; econstructor; eauto; fail.
    - destruct (SplitPath _ _ pth).
      + destruct (H _ _ p) as [m2 [m2' [h1 h2]]].
        eapply IHt2 with (M := (psi, m) :: M); auto.
        intros.
        inversion H0; subst; eauto.
      + assert (typing (map mapBelief M ++ psi @ m :: Gamma) t2 b).
        eapply Exchange; eauto.
        solveSubPath.
        edestruct IHt1 with (1 := H3); auto.
        edestruct IHt2 with (1 := H0).
        intros.
        destruct (H _ _ H1) as [m1 [m1' []]].
        exists m1, m1'.
        split; auto.
        eapply Weakening; eauto; try solve [solveProper | solveSubPath].
        eexists; econstructor; eauto; fail.
    - assert (typing (map mapBelief M ++ phi @ ⟨l⟩ :: Gamma) t (psi @ m')).
      eapply Exchange; eauto.
      solveSubPath.
      edestruct IHt with (1 := H0); auto.
      intros.
      destruct (H _ _ H1) as [m1 [m1' []]].
      exists m1, m1'.
      split; auto.
      eapply Weakening; eauto; try solve [solveProper | solveSubPath].
      eexists; econstructor; eauto; fail.
    - destruct (SplitPath _ _ pth).
      + destruct (H _ _ p) as [m2 [m2' [h1 h2]]].
        eapply IHt with (M := (open_formula phi t0, m) :: M); auto.
        intros.
        inversion H0; subst; eauto.
      + assert (typing (map mapBelief M ++ open_formula phi t0 @ m :: Gamma) t b).
        eapply Exchange; eauto.
        solveSubPath.
        edestruct IHt with (1 := H0).
        intros.
        destruct (H _ _ H3) as [m1 [m1' []]].
        exists m1, m1'.
        split; auto.
        eapply Weakening; eauto; try solve [solveProper | solveSubPath].
        eexists; econstructor; eauto; fail.
    - edestruct IHt with (1 := H6); auto.
      eexists.
      eapply forallRr with (y := y); eauto.
      clear IHt H H3 H4 h H6 phi t0 x t.
      intro.
      apply H2.
      clear H2.
      induction M; simpl; auto.
      apply Exists_cons_tl; auto.
    - destruct (SplitPath _ _ pth).
      + destruct (H _ _ p) as [m2 [m2' [h1 h2]]].
        eapply IHt with (M := (open_formula phi (varTerm y), m) :: M); auto.
        intros.
        inversion H0; subst; eauto.
      + assert (typing (map mapBelief M ++ open_formula phi (varTerm y) @ m :: Gamma) t b).
        eapply Exchange; eauto.
        solveSubPath.
        edestruct IHt with (1 := H0).
        intros.
        destruct (H _ _ H1) as [m1 [m1' []]].
        exists m1, m1'.
        split; auto.
        eapply Weakening; eauto; try solve [solveProper | solveSubPath].
        eexists.
        eapply existsLr with (y := y); eauto.
        intro.
        apply H2.
        clear IHt H H3 H5 b t0 x t h H0 H2 pth.
        induction M; simpl; auto.
        apply Exists_cons_tl; auto.
    - edestruct IHt with (1 := H4); auto.
      eexists; econstructor; eauto; fail.
    - eexists.
      apply flowsToReflr; auto.
      eapply ProperContextApp; eauto.
    - edestruct IHt1 with (1 := H3); auto.
      edestruct IHt2 with (1 := H5); auto.
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (1 := H2); auto.
      eexists; econstructor; eauto; fail.
    - destruct (SplitPath _ _ pth).
      + destruct (H _ _ p0) as [m2 [m2' [h1 h2]]].
        eapply IHt with (M := (phi, m ⋅ p ⟨ lab ⟩) :: M); auto.
        simpl.
        intros.
        inversion H0; subst; eauto.
        exists m2, (m2' ++ [(p, lab)]).        
        split; eauto.
        repeat rewrite ModalityCombineCons; auto.
      + assert (typing (map mapBelief M ++ phi @ m ⋅ p ⟨ lab ⟩ :: Gamma) t b).
        eapply Exchange; eauto.
        solveSubPath.
        edestruct IHt with (1 := H0).
        intros.
        destruct (H _ _ H1) as [m1 [m1' []]].
        exists m1, m1'.
        split; auto.
        eapply Weakening; eauto; try solve [solveProper | solveSubPath].
        eexists; econstructor; eauto; fail.
    - edestruct IHt with (1 := H2); auto.
      eexists; econstructor; eauto; fail.
    - edestruct IHt with (1 := H2); auto.
      eexists; econstructor; eauto; fail.
    - destruct (SplitPath _ _ pth').
      + destruct (H _ _ p) as [m1 [m1' [h1 h2]]].
        destruct (ModColPthinv _ _ _ _ h1).
        * destruct s as [m2 [pi' [e1 e2]]].
          rewrite e1 in H2.
          edestruct IHt with (M := (phi, ModalityCombine m2 m1') :: M); simpl; eauto.
          intros f m0 H0.
          inversion H0; subst; eauto.
          exists m2, m1'.
          split; auto.
          apply modalityExpandR with (pth := pi'); auto.
        * destruct s.
          rewrite e in H2.
          edestruct IHt with (1 := H2) (M := (phi, ModalityCombine m1 x) :: M) (Gamma := Gamma) (b := b).
          intros.
          inversion H0; subst; eauto.
          eauto.
      + assert (typing (map mapBelief M ++ phi @ m :: Gamma) t b).
        eapply Exchange; eauto.
        solveSubPath.
        edestruct IHt with (1 := H0).
        intros.
        destruct (H _ _ H1) as [m1 [m1' []]].
        exists m1, m1'.
        split; auto.
        eapply Weakening; eauto; try solve [solveProper | solveSubPath].
        eexists; econstructor; eauto; fail.
    - destruct (SplitPath _ _ pth').
      + destruct (H _ _ p) as [m2 [m2' [h1 h2]]].
        destruct (ModExpPthinv _ _ _ pth h1).
        * destruct s as [pi [m'' e]].
          rewrite e in H2.
          edestruct IHt with (M := (phi, ModalityCombine (CollapseDoubleInModality pi) m'') :: M); simpl; eauto.
          intros f m0 H0.
          inversion H0; subst; eauto.
          exists (CollapseDoubleInModality pi), m''.
          split; auto.
          apply modalityCollapseR.
          apply ProofToTyping in h2.
          destruct h2.
          edestruct (@FFR_inversion) with (1 := t0) (C := FF) (mr := m2'); auto.
          apply PathToIn in pth'.
          apply provenProperContextTyping in H2.
          inversion H2; subst.          
          destruct (BeliefInProperContextIsProper _ _ H5 pth'); auto. 
          eapply ModProperApp with (m := ModalityCombine m2 m2'); eauto.
          constructor.
          eapply TypingToProof; eauto.
        * destruct s.
          rewrite e in H2.
          edestruct IHt with (M := (phi, ModalityCombine m2 x) :: M) (Gamma := Gamma) (b := b); simpl; eauto.
          intros.
          inversion H0; subst; eauto.
      + assert (typing (map mapBelief M ++ (phi @ CollapseDoubleInModality pth) :: Gamma) t b).
        eapply Exchange; eauto.
        solveSubPath.
        edestruct IHt with (1 := H0).
        intros.
        destruct (H _ _ H1) as [m1 [m1' []]].
        exists m1, m1'.
        split; auto.
        eapply Weakening; eauto; try solve [solveProper | solveSubPath].
        eexists; econstructor; eauto; fail.
    - edestruct IHt1 with (1 := H3); auto.
      edestruct IHt2 with (1 := H5); auto.
      eexists; econstructor; eauto; fail.
    - destruct (SplitPath _ _ pth).
      + destruct (H _ _ p) as [m2 [m2' [h1 h2]]].
        destruct (LVariancePthinv _ _ _ _ lab2 pi h1).
        * edestruct IHt2 with (1 := H5); auto.
          destruct s.
          destruct p0.
          rewrite e in H3.
          edestruct IHt1 with (1 := H3) (M := (phi, ModalityCombine (ReplaceLabelInModality m2 lab1 lab2 x0) m2') :: M); eauto.
          intros f m0 H0.
          inversion H0; subst; eauto.
          exists (ReplaceLabelInModality m2 lab1 lab2 x0), m2'.
          split; auto.
          apply RVariance; auto.
          rewrite e0 in t.
          eapply TypingToProof; eauto.
        * destruct s.
          rewrite e in H3.
          edestruct IHt1 with (1 := H3) (M := (phi, ModalityCombine m2 x) :: M) (Gamma := Gamma) (b := b).
          intros.
          inversion H0; subst; eauto.
          eauto.
      + assert (typing (map mapBelief M ++ (phi @ ReplaceLabelInModality m lab1 lab2 pi) :: Gamma) t1 b).
        eapply Exchange; eauto.
        solveSubPath.
        edestruct IHt1 with (1 := H0).
        intros.
        destruct (H _ _ H1) as [m1 [m1' []]].
        exists m1, m1'.
        split; auto.
        eapply Weakening; eauto; try solve [solveProper | solveSubPath].
        edestruct IHt2 with (1 := H5); auto.
        eexists; econstructor; eauto; fail.
    - edestruct IHt1 with (1 := H4); auto.
      edestruct IHt2 with (1 := H6); auto.
      edestruct IHt3 with (1 := H7); auto.
      eexists; econstructor; eauto; fail.
    - destruct (SplitPath _ _ pth').
      + destruct (H _ _ p0) as [m2 [m2' [h1 h2]]].
        destruct (FwdLPthinv _ _ _ p q pth h1).
        * edestruct IHt2 with (1 := H6); auto.
          edestruct IHt3 with (1 := H7); auto.
          destruct s.
          repeat destructProd.
          rewrite e1 in H4.
          edestruct IHt1 with (1 := H4) (M := (phi, ModalityCombine (ReplacePrinInModality x1 p) m2') :: M); eauto.
          intros f m0 H0.
          inversion H0; subst; eauto.
          exists (ReplacePrinInModality x1 p), m2'.
          split; auto.
          apply FwdR; auto.
          rewrite e0 in t0.
          rewrite e in t0.
          eapply TypingToProof; eauto.
          rewrite e0 in t.
          rewrite e2 in t.
          eapply TypingToProof; eauto.
        * destruct s.
          rewrite e in H4.
          edestruct IHt1 with (1 := H4) (M := (phi, ModalityCombine m2 x) :: M) (Gamma := Gamma) (b := b).
          intros.
          inversion H0; subst; eauto.
          eauto.
      + assert (typing (map mapBelief M ++ (phi @ReplacePrinInModality pth p) :: Gamma) t1 b).
        eapply Exchange; eauto.
        solveSubPath.
        edestruct IHt1 with (1 := H0).
        intros.
        destruct (H _ _ H1) as [m1 [m1' []]].
        exists m1, m1'.
        split; auto.
        eapply Weakening; eauto; try solve [solveProper | solveSubPath].
        edestruct IHt2 with (1 := H6); auto.
        edestruct IHt3 with (1 := H7); auto.
        eexists; econstructor; eauto; fail.
    - edestruct IHt1 with (1 := H3); auto.
      edestruct IHt2 with (1 := H5); auto.
      eexists; econstructor; eauto; fail.
    - edestruct IHt1 with (1 := H3); auto.
      edestruct IHt2 with (1 := H5); auto.
      eexists; econstructor; eauto; fail.
  Qed.

  Lemma FFL_inversion : forall t Gamma b f m m'(h : typing ((f @ ModalityCombine m m') :: Gamma) t b), Path (FF @ m) Gamma -> sigT (fun t' => typing Gamma t' b).
  Proof.
    intros.
    eapply FFL_inversion' with (M := [(f, ModalityCombine m m')]); simpl; eauto.
    intros.
    inversion H0; subst; simpl; eauto.
    exists m, m'.
    split; auto.
    apply axiom; auto.
    apply provenProperContextTyping in h.
    inversion h; auto.
    inversion H3.    
  Qed.

 Ltac solveProper :=
   match goal with
   | [h : typing ?G _ _ |- ProperContext ?G] => apply (provenProperContextTyping h)
   | [h : typing ?G _ _ |- Forall ProperBelief ?G] => apply (provenProperContextTyping h)
   | [h : typing (?a :: ?b :: ?c :: _ ++ ?G) _ _  |- ProperContext (?a :: ?b :: ?c :: ?G)] => apply provenProperContextTyping in h; apply ExchangeProper with (L1 := [a; b; c]) in h; destruct (ProperContextApp _ _ h); auto 
   | [h : typing (?a :: ?b :: _ ++ ?G) _ _  |- ProperContext (?a :: ?b :: ?G)] => apply provenProperContextTyping in h; apply ExchangeProper with (L1 := [a;b]) in h; destruct (ProperContextApp _ _ h); auto 
   | [h : typing (?a :: _ ++ ?G) _ _  |- ProperContext (?a :: ?G)] => apply provenProperContextTyping in h; apply ExchangeProper with (L1 := [a]) in h; destruct (ProperContextApp _ _ h); auto
   | [h : Forall ProperBelief (?a :: _) |- Forall ProperBelief (?a :: _)] => inversion h; subst; constructor; auto 
   | [h : ProperContext (?a :: _) |- Forall ProperBelief (?a :: _)] => inversion h; subst; constructor; auto 
   | [h : Forall ProperBelief (?a :: _) |- ProperContext (?a :: _)] => inversion h; subst; constructor; auto 
   | [h : ProperContext (?a :: _) |- ProperContext (?a :: _)] => inversion h; subst; constructor; auto 

                                                                                                  
   | [h : Forall ProperBelief (_:: ?a :: _) |- Forall ProperBelief (?a :: _)] => inversion h; subst
   | [h : ProperContext (_ :: ?a :: _) |- Forall ProperBelief (?a :: _)] => inversion h; subst
   | [h : Forall ProperBelief (_ :: ?a :: _) |- ProperContext (?a :: _)] => inversion h; subst
   | [h : ProperContext (_ :: ?a :: _) |- ProperContext (?a :: _)] => inversion h; subst
   | [h : typing (_ :: ?a :: _) _ _ |- Forall ProperBelief (?a :: _)] => apply provenProperContextTyping in h; inversion h; subst
   | [h : typing (_ :: ?a :: _) _ _ |- ProperContext (?a :: _)] => apply provenProperContextTyping in h; inversion h; subst
 
   | [h : typing _ _ ?a |- Forall ProperBelief (?a :: _)] => pose proof (provenProperBeliefTyping h); constructor; auto
   | [h : typing _ _ ?a |- ProperContext (?a :: _)] => pose proof (provenProperBeliefTyping h); constructor; auto
                                                                                                  
   | [h : typing (?a :: _) _ _ |- Forall ProperBelief (?a :: _)] => apply provenProperContextTyping in h; inversion h; subst; constructor; auto
   | [h : typing (?a :: _) _ _ |- ProperContext (?a :: _)] => apply provenProperContextTyping in h; inversion h; subst; constructor; auto
   end.                                                     

  
  Definition Ph2MCR := fun t1 : proofTerm => forall {Gamma : Context} {phi b : Belief} {t2 : proofTerm} (h2 : typing Gamma t1 b) (h0 : NormalFormTerm' t1 false) (h1 : typing (b :: Gamma) t2 phi ), sigT (fun t' => typing Gamma t' phi).    

  Lemma Cut_h2MCR : forall {t1 : proofTerm} {Gamma : Context} {phi b : Belief} {t2 : proofTerm} (h2 : typing Gamma t1 b) (h0 : NormalFormTerm' t1 false) (h1 : typing (b :: Gamma) t2 phi ), sigT (fun t' => typing Gamma t' phi).
  Proof.    
    pose proof (@Fix _ (fun x1 x2 => term_size x1 < term_size x2) (well_founded_ltof _ _) Ph2MCR).
    apply H.
    clear H.
    unfold Ph2MCR in *.
    intros x IH Gamma phi b t2 h2 h0 h1.
    destruct x; simpl in *; try solve [inversion h0]; intros; inversion h2; subst; repeat destructProd.
    - eexists.
      eapply WeakeningTyping; eauto.
      intros b' H1.
      inversion H1; auto.
    - apply TypingToProof in h1.
      apply ProofToTyping.
      eapply TTL_inversion; eauto.      
    - clear IH h2.
      eapply FFL_inversion; eauto.
    - eapply flowsToRefl_inversion; eauto.
    - assert (sigT (fun t => typing (lab1 ⊑ lab2 @ m :: lab2 ⊑ lab3 @ m :: Gamma) t phi)).
      eapply flowsToTransLr.
      eapply WeakeningTyping.
      apply h1.
      2 : solveSubPath.
      repeat solveProper.
      apply Here.
      apply There; apply Here.
      destruct H.
      edestruct IH.
      4 : eauto.
      2 : solveTyping.
      rewrite WeakeningTypingSize; solveCutRel.
      solveNFT.
      edestruct (IH x2); solveCutRel; eauto.
    - edestruct IH; auto.
      apply H1.
      eapply modalityExpandLr.
      apply Here.
      eapply (WeakeningTyping h1); eauto.
      repeat solveProper.
      solveSubPath.
      eauto.
    - edestruct IH; auto.
      apply H1.
      eapply modalityCollapseLr.
      apply Here.
      eapply (WeakeningTyping h1); eauto.
      2 : solveSubPath.
      repeat solveProper.
      eauto.
    - edestruct IH; auto.
      eauto.
      eapply WeakeningTyping.
      apply h1.
      2 : solveSubPath.
      repeat solveProper.
      eexists.
      eapply modalityExpandLr.
      eauto.
      eauto.
    - edestruct IH; auto.
      eauto.
      eapply WeakeningTyping.
      apply h1.
      2 : solveSubPath.
      repeat solveProper.
      eexists.
      eapply modalityCollapseLr.
      eauto.
      eauto.
    - eapply (IH x1) with (phi := phi); solveCutRel; eauto.
      eapply LVariancer with (lab1 := lab1) (lab2 := lab2) (pi := pi); [apply Here | |].
      eapply WeakeningTyping; eauto.
      2 : solveSubPath.
      repeat solveProper.
      eapply WeakeningTyping; eauto.
      2 : solveSubPath.
      repeat solveProper.
    - edestruct (IH x1) with (phi := phi); eauto; solveCutRel.
      eapply WeakeningTyping; eauto.
      2 : solveSubPath.
      repeat solveProper.
      eexists.      
      eapply LVariancer; eauto.
    - eapply (IH x1) with (phi := phi); eauto; solveCutRel.
      eapply FwdLr; try (apply Here); eapply WeakeningTyping; eauto; try solve [solveSubPath].
      all : repeat solveProper.
    - edestruct (IH x1) with (phi := phi); eauto; solveCutRel.
      eapply WeakeningTyping; eauto.
      2 : solveSubPath.
      repeat solveProper.
      eexists.
      eapply FwdLr; eauto.
    - assert (sigT (fun t => typing (canRead p lab2 @ m :: Gamma) t phi)).
      eapply CRVarianceLr.
      eapply WeakeningTyping.
      apply h1.
      2 : solveSubPath.
      repeat solveProper.
      apply Here.
      eapply TypingToProof.
      eapply WeakeningTyping; eauto.
      2 : solveSubPath.
      repeat solveProper.
      destruct H.
      edestruct IH.
      4 : eauto.
      2 : solveTyping.
      rewrite WeakeningTypingSize; solveCutRel.
      solveNFT.
      eauto.
    - assert (sigT (fun t => typing (canWrite p lab1 @ m :: Gamma) t phi)).
      eapply CWVarianceLr.
      eapply WeakeningTyping.
      apply h1.
      2 : solveSubPath.
      repeat solveProper.
      apply Here.
      eapply TypingToProof.
      eapply WeakeningTyping; eauto.
      2 : solveSubPath.
      repeat solveProper.
      destruct H.
      edestruct IH.
      4 : eauto.
      2 : solveTyping.
      rewrite WeakeningTypingSize; solveCutRel.
      solveNFT.
      eauto.
  Qed.
      
  Definition cut_rel : (nat * nat * nat) -> (nat * nat * nat) -> Prop :=
    fun t1 t2 => match t1, t2 with
              | (x1,y1,z1), (x2,y2,z2) =>
                x1 < x2 \/ (x1 = x2 /\ y1 < y2)
                \/ (x1 = x2 /\ y1 = y2 /\ z1 < z2)
              end.

  Fixpoint modality_size (m : Modality) : nat :=
    match m with
    | g _ => 1
    | sim m' _ _ => 1 + (modality_size m')
    end.
  
  Definition belief_size (b : Belief) : nat :=
    match b with
    | phi @ m => formula_size phi + modality_size m
    end.

  Theorem Cut_MCR1 {Gamma : Context} {phi : Belief} {C : flafolFormula} {m : Modality} (t1 t2 : proofTerm) (h1 : typing ((C @ m) :: Gamma) t1 phi) (nft1 : NormalFormTerm' t1 false) (h2 : typing Gamma t2 (C @ m)) (nft2 : NormalFormTerm' t2 true) : sigT (fun t : proofTerm => typing Gamma t phi).
  Proof.
    eapply @Cut_h1MCR with (M := [m]); simpl; eauto.
    intros.
    inversion H; subst; auto.
    eapply TypingToProof; eauto.
    inversion H2.
  Qed.
    
  Ltac destructProd :=
    match goal with
    | [h : prod _ _ |- _] => destruct h
    end.    

  Ltac proveTyping :=
    match goal with
    | [ |- typing _ (?f _) _] => constructor; eauto
    | [y : var |- var] => exact y
    end.

  Ltac proveFalse :=
    match goal with
    | [h : context [not (_ = _)] |- False] => eapply h; reflexivity
    end.

  Ltac PathInv :=
    match goal with
    | [h: Path _ (_ :: _) |- _] => inversion h; subst
    end.
  
  Ltac invertTypingNFT:=
    lazymatch goal with
    | [h1 : typing _ (?f _) _, h2 : NormalFormTerm' (?f _) _ |- _] => inversion h1; simpl in h2; subst
    end.

  Obligation Tactic := intros.

  Definition aux_rel : (nat * nat) -> (nat * nat) -> Prop :=
    fun t1 t2 => match t1, t2 with
              | (x1,y1), (x2,y2) =>
                x1 < x2 \/ (x1 = x2 /\ y1 < y2)
              end.

  Lemma prodltImpCutRel : forall n1 n2 n3 n1' n2' n3', cut_rel (n1, n2, n3) (n1', n2', n3') -> (lexprod (nat*nat) (fun _ => nat) aux_rel (fun _ x1 x2 => lt x1 x2) (existT (fun _ => nat) (n1, n2) n3) (existT (fun _ => nat) (n1', n2') n3')).
  Proof.
    unfold cut_rel.
    inversion 1; subst.
    apply left_lex; auto.
    unfold aux_rel.
    left; auto.
    destruct H0.
    apply left_lex; auto.
    unfold aux_rel.
    right; auto.
    destruct H0.
    destruct H1.
    rewrite H0.
    rewrite H1.
    apply right_lex; auto.
  Qed.

  Lemma wffLexprod : well_founded (lexprod (nat*nat) (fun _ => nat) aux_rel (fun _ x1 x2 => lt x1 x2)).
  Proof.
    apply wf_lexprod.
    apply wffCutRel.
    intros.
    apply lt_wf.    
  Qed.

  Definition liftToLexProd {A : Set} {B : Set} (ltA : A -> A -> Prop) (ltB : B -> B -> Prop) :=
    fun x1 x2 : (A * B) => lexprod A (fun _ => B) ltA (fun _ x1 x2 => ltB x1 x2) (existT (fun _ => B) (fst x1) (snd x1)) (existT (fun _ => B) (fst x2) (snd x2)).
      
  Lemma wffCutRel : well_founded cut_rel.
  Proof.
    eapply wf_incl with (R2 := liftToLexProd aux_rel lt).
    intro.
    intros.
    destruct x, y.
    destruct p, p0.
    unfold liftToLexProd.
    apply prodltImpCutRel; auto.
    unfold liftToLexProd.
    apply wf_inverse_image.
    apply wffLexprod.
  Qed.

 Definition Cutrel : (flafolFormula * proofTerm * proofTerm) -> (flafolFormula * proofTerm * proofTerm) -> Prop :=
   fun t1 t2 => match t1, t2 with
             | (x1,y1,z1), (x2,y2,z2) => cut_rel (formula_size x1, term_size y1, term_size z1) (formula_size x2, term_size y2, term_size z2)

             end.

 Definition rel' : (flafolFormula * proofTerm * proofTerm) -> (flafolFormula * proofTerm * proofTerm) -> Prop :=
   fun x1 x2 => cut_rel (formula_size (fst (fst x1)), (term_size (snd (fst x1))), term_size (snd x1)) (formula_size (fst (fst x2)), (term_size (snd (fst x2))), term_size (snd x2)).
 
 Theorem WfRel' : well_founded rel'.
 Proof.
   unfold rel'.
   apply wf_inverse_image.
   apply wffCutRel.
 Qed.

 (*The dictionary order is well-founded*)
 Theorem WfCutrel : well_founded Cutrel.
 Proof.
   unfold Cutrel.
   eapply wf_incl with (R2 := rel').
   intro.
   intros.
   unfold rel'.
   destruct x, y.
   destruct p, p1.
   simpl; auto.
   apply WfRel'.
 Qed.
 
 Definition PCut := fun (x : flafolFormula * proofTerm * proofTerm) => forall {Gamma : Context} {D : flafolFormula} {m m' : Modality} (h1 : typing (((fs x) @ m) :: Gamma) (th x) (D @ m')) (nft1 : NormalFormTerm' (th x) true) (h2 : typing Gamma (sn x) ((fs x) @ m)) (nft2 : NormalFormTerm' (sn x) true), sigT (fun t' : proofTerm => typing Gamma t' (D @ m')).
   
 Lemma open_with_fresherRT : forall Gamma phi m y trm t (h : typing Gamma t (open_formula phi (varTerm y) @ m)), ⊢s trm ::: (VarSort y) -> y ∉FVC Gamma -> y ∉FVB (phi @ m) -> sigT (fun t'  => typing Gamma t' (open_formula phi trm @ m)).
 Proof.
   intros.
   eexists t.
   assert (open_formula phi trm = open_formula phi (varTerm y) f[ y ↦ trm]).
   rewrite open_formula_subst; simpl; auto.
   rewrite substFormulaNonFreeEqual; auto.
   destruct (varEqDec y y); try congruence; auto.
   intro.
   apply H1.
   econstructor; eauto; fail.
   eapply hasSort_lc; eauto.
   rewrite <-substContextNonFreeEq with (Gamma := Gamma) (x := y) (t := trm); auto.
   rewrite <-substModalityNotFreeEq with (m := m) (x := y) (t := trm); auto.
   rewrite H2.
   apply @substTyping with (b := open_formula phi (varTerm y) @ m); auto.
   eapply hasSort_lc; eauto.
   intro.
   apply H1.
   econstructor; eauto; fail.
 Qed.

 Lemma open_with_fresherLT : forall Gamma phi psi m m' y trm t (h : typing ((open_formula phi (varTerm y)) @ m :: Gamma) t (psi @ m')) bol, NormalFormTerm' t bol -> Path (∃ VarSort y; phi @ m) Gamma -> ⊢s trm ::: (VarSort y) ->  y ∉FVC Gamma -> (y ∉FVB psi @ m') -> sigT (fun t' => prod (typing ((open_formula phi trm) @ m :: Gamma) t' (psi @ m')) (prod (term_size t = term_size t') (NormalFormTerm' t' bol))).
 Proof.
   intros Gamma phi psi m m' y trm t h bol H H0 H1 H2 H3.
   exists t; split; auto.
   assert (open_formula phi trm = open_formula phi (varTerm y) f[ y ↦ trm]).
   rewrite open_formula_subst; simpl; auto.
   rewrite substFormulaNonFreeEqual; auto.
   destruct (varEqDec y y); try congruence; auto.
   intro.
   apply H2.
   unfold freeInContext.
   apply Exists_exists.
   exists (∃ VarSort y; phi @ m).
   split.
   apply PathToIn; auto.
   econstructor; econstructor; eauto; fail.
   eapply hasSort_lc; eauto.
   rewrite <-substContextNonFreeEq with (Gamma := Gamma) (x := y) (t := trm); auto.
   rewrite <-substModalityNotFreeEq with (m := m') (x := y) (t := trm); auto.
   rewrite <-substModalityNotFreeEq with (m := m) (x := y) (t := trm); auto.
   rewrite <-substFormulaNonFreeEqual with (f := psi) (x := y) (t := trm); auto.
   rewrite H4.
   apply @substTyping with (b := psi @ m') (G := open_formula phi (varTerm y) @ m :: Gamma); auto.
   eapply hasSort_lc; eauto.
   intro.
   apply H3; econstructor; eauto; fail.
   intro; apply H2.
   apply Exists_exists.
   exists (∃ VarSort y; phi @ m).
   split.
   apply PathToIn; auto.
   econstructor; eauto; fail.
   intro.
   apply H3; econstructor; eauto; fail.
 Qed.
 
   
 Theorem Cut : forall (x : flafolFormula * proofTerm * proofTerm) {Gamma : Context} {D : flafolFormula} {m m' : Modality} (h1 : typing (((fs x) @ m) :: Gamma) (th x) (D @ m')) (nft1 : NormalFormTerm' (th x) true) (h2 : typing Gamma (sn x) ((fs x) @ m)) (nft2 : NormalFormTerm' (sn x) true), sigT (fun t' : proofTerm => typing Gamma t' (D @ m')).
  Proof.
    assert (well_founded Cutrel) by (apply WfCutrel).
    pose proof (@Fix _ _ H PCut).
    apply H0.
    intros.
    assert (forall x1 x2 x3, Cutrel (x1, x2, x3) x -> PCut (x1, x2, x3)).
    intros; eauto.
    clear H1.
    clear H H0.
    destruct x as [[C t2] t1].
    unfold PCut in *.
    simpl in H2.
    assert (forall (Gamma : Context) (x1 D : flafolFormula) (m m' : Modality) (x3 x2 : proofTerm)
              (h1 : typing (x1 @ m :: Gamma) x3 (D @ m'))
              (nft1 : NormalFormTerm' x3 true)
              (h2 : typing Gamma x2 (x1 @ m)) (nft2 : NormalFormTerm' x2 true), (Cutrel (x1, x2, x3) (C, t2, t1)) -> sigT (fun t' : proofTerm => typing Gamma t' (D @ m'))) as Cut.
    eauto.
    clear H2.
    simpl in *.
    intros Gamma D m m' h1 nft1 h2 nft2.
    destruct t1; try solve [eapply (Cut_MCR1 _ t2 h1 nft1 h2 nft2); auto]; inversion h1; subst; simpl in *; repeat destructProd; try PathInv.
    - edestruct (@Cut _ _ D _ m' t1 (weak t2 (phi @ m :: psi @ m :: Gamma)) (Exchange _ _ (phi & psi @ m :: phi @ m :: psi @ m :: Gamma) _ H1 ltac:(solveSubPath)) nft1).
      eapply WeakeningTyping; eauto; try solve [solveSubPath | repeat solveProper].
      solveNFT.
      repeat rewrite WeakeningTypingSize; simpl; solveCutRel.
      apply AndR_inversion_typing in h2.
      destruct h2 as [[t3 T3] [t4 T4]].
      destruct (NormalizeTyping t) as [x' [t' h2]].      
      destruct (NormalizeTyping T3) as [t3' [T3' nft3]].      
      edestruct (@Cut _ _ D _ m' x' (weak t3' (psi @ m :: Gamma)) t' h2).
      eapply WeakeningTyping; eauto; try solve [solveSubPath | repeat solveProper].
      solveNFT.
      simpl; solveCutRel.
      destruct (NormalizeTyping t0) as [x'' [t'' h3]].      
      destruct (NormalizeTyping T4) as [t4' [T4' nft4]].      
      edestruct (@Cut _ _ D _ m' x'' t4' t'' h3); eauto.
      simpl; solveCutRel.      
    - edestruct (@Cut _ _ D _ m' t1 (weak t2 (phi @ m0 :: psi @ m0 :: Gamma)) (Exchange _ _ (C @ m :: phi @ m0 :: psi @ m0 :: Gamma) _ H1 ltac:(solveSubPath)) nft1 ).
      eapply WeakeningTyping; eauto; try solve [solveSubPath | repeat solveProper].
      solveNFT.
      repeat rewrite WeakeningTypingSize; simpl; solveCutRel.
      eexists.
      eapply AndLr; eauto.
    - edestruct Cut.
      apply H3.
      all: eauto.
      solveCutRel.
      edestruct Cut.
      apply H5.
      all: eauto.
      solveCutRel.
      eexists; econstructor; eauto; fail.
    - destruct t2; inversion h2; subst; simpl in *; repeat destructProd; try solve [eapply (Cut_h2MCR) with (1 := h2) (3 := h1); simpl; auto].
      + edestruct Cut with (x2 := t2) (3 := H1); auto.
        eapply (WeakeningTyping h1); try solveSubPath.
        repeat solveProper.
        solveNFT.
        eexists; econstructor; eauto; fail.
      + edestruct Cut with (x2 := t2_1) (3 := H3); simpl; auto.
        eapply (WeakeningTyping h1); try solveSubPath.
        repeat solveProper.
        solveNFT.
        solveCutRel.
        edestruct Cut with (x2 := t2_2) (3 := H6); simpl; auto.
        eapply (WeakeningTyping h1); try solveSubPath.
        repeat solveProper.
        solveNFT.
        solveCutRel.
        eexists; econstructor; eauto; fail.
      + edestruct (@Cut _ _ D _ m' t1_1 (weak (OrR1Term t2) (phi @ m :: Gamma)) (Exchange _ _ (phi ⊕ psi @ m :: phi @ m :: Gamma) _ H2 ltac:(solveSubPath)) n).
        solveTyping.
        solveNFT.
        repeat rewrite WeakeningTypingSize; simpl; solveCutRel.
        destruct (NormalizeTyping t) as [x' [t' h3]].      
        edestruct Cut with (x2 := t2) (3 := H5); simpl; auto.
        eauto.
        unfold NormalFormTerm in h3; auto.
        solveCutRel.
        eauto.
      + edestruct (@Cut _ _ D _ m' t1_2 (weak (OrR2Term t2) (psi @ m :: Gamma)) (Exchange _ _ (phi ⊕ psi @ m :: psi @ m :: Gamma) _ H4 ltac:(solveSubPath)) n0).
        solveTyping.
        solveNFT.
        repeat rewrite WeakeningTypingSize; simpl; solveCutRel.
        destruct (NormalizeTyping t) as [x' [t' h3]].      
        edestruct Cut with (x2 := t2) (3 := H5); simpl; auto.
        eauto.
        unfold NormalFormTerm in h3; auto.
        solveCutRel.
        eauto.
      + edestruct Cut with (x2 := t2_2) (3 := H6); auto.
        eapply (WeakeningTyping h1); try solveSubPath.
        repeat solveProper.
        solveNFT.
        repeat rewrite WeakeningTypingSize; simpl; solveCutRel.
        eexists; econstructor; eauto; fail.
      + edestruct Cut with (x2 := t2) (3 := H5); auto.
        eapply (WeakeningTyping h1); try solveSubPath.
        repeat solveProper.
        solveNFT.
        eexists; econstructor; eauto; fail.
      + pose (freshInSequent (open_formula phi (varTerm y) @ m :: ( phi ⊕ psi @ m) :: Gamma) (D @ m') (VarSort y)) as y'.
        destruct (open_with_fresherLT'' _ _ _ _ y y' t2 H6 _ nft2) as [t' [T [nft' eq]]]; auto.
        unfold y'.
        rewrite freshInSequentOfSort; auto.
        edestruct Cut with (x2 := t') (3 := T); auto.
        3 : simpl; rewrite eq; solveCutRel.
        eapply (WeakeningTyping h1); try solveSubPath.
        repeat solveProper.
        solveNFT.
        eexists.
        eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
        unfold y'.
        all : destruct (freshInSequentIsFresh (open_formula phi (varTerm y) @ m :: ( phi ⊕ psi @ m) :: Gamma) (D @ m') (VarSort y)) as [fv1 fv2].
        eapply FreshWithMore.
        2: eauto.
        intros.
        simpl; auto.
      + edestruct Cut with (x2 := t2) (3 := H1); auto.
        eapply (WeakeningTyping h1); try solveSubPath.
        repeat solveProper.
        solveNFT.
        eexists; econstructor; eauto; fail.
    - edestruct Cut with (x1 := C) (Gamma := phi @ m0 :: Gamma) (m := m); auto.
      apply (Exchange _ _ _ _ H2).
      solveSubPath.
      auto.
      eapply (WeakeningTyping h2); try solveSubPath.
      repeat solveProper.
      solveNFT.
      repeat rewrite WeakeningTypingSize; simpl; solveCutRel.
      edestruct Cut with (x1 := C) (Gamma := psi @ m0 :: Gamma) (m := m); auto.
      apply (Exchange _ _ _ _ H4).
      solveSubPath.
      auto.
      eapply (WeakeningTyping h2); try solveSubPath.
      repeat solveProper.
      solveNFT.
      repeat rewrite WeakeningTypingSize; simpl; solveCutRel.
      eexists; econstructor; eauto; fail.
    - edestruct Cut with (1 := H3); eauto.
      solveCutRel.
      eexists; econstructor; eauto; fail.
    - edestruct Cut with (1 := H3); eauto.
      solveCutRel.
      eexists; econstructor; eauto; fail.
    - edestruct (@Cut _ _ D _ m' t1_2 (weak t2 (psi @ m :: Gamma)) (Exchange _ _ (phi ==⟨ l ⟩> psi @ m :: psi @ m :: Gamma) _ H4 ltac:(solveSubPath)) n0).
      eapply WeakeningTyping; eauto; try solve [solveSubPath].
      repeat solveProper.
      solveNFT.
      repeat rewrite WeakeningTypingSize; simpl; solveCutRel.
      edestruct (@Cut _ _ phi _ (⟨ l ⟩) t1_1 t2 H2 n h2 nft2).
      simpl; solveCutRel.
      apply ImpR_inversion in h2.
      destruct h2 as [t3 T3].
      destruct (NormalizeTyping T3) as [t3' [T3' nft3]].      
      destruct (NormalizeTyping t0) as [x0' [t0' nfx0']].
      edestruct (@Cut _ _ psi _ m t3' x0' T3' nft3 t0' nfx0').
      simpl; solveCutRel.
      destruct (NormalizeTyping t) as [x' [t' h2]].      
      destruct (NormalizeTyping t1) as [x1' [t1' nfx1']].      
      edestruct (@Cut _ _ D _ m' x' x1' t' h2 t1' nfx1'); eauto.
      simpl; solveCutRel.
    - edestruct (@Cut _ _ D _ m' t1_2 (weak t2 (psi @ m0 :: Gamma)) (Exchange _ _ (C @ m :: psi @ m0 :: Gamma) _ H4 ltac:(solveSubPath)) n0 ).
      eapply WeakeningTyping; eauto; try solve [solveSubPath].
      repeat solveProper.
      solveNFT.
      repeat rewrite WeakeningTypingSize; simpl; solveCutRel.
      edestruct (@Cut _ _ phi _ (⟨l⟩) t1_1 t2 H2 n h2 nft2).
      simpl; solveCutRel.
      eexists.
      eapply ImpLr; eauto.
    - assert (typing (C @ m :: phi @ ⟨ l ⟩ :: Gamma) t1 (psi @ m')).
      eapply Exchange; eauto; solveSubPath.
      edestruct Cut with (1 := H); auto.
      solveTyping.
      solveNFT.
      repeat rewrite WeakeningTypingSize; simpl; solveCutRel.
      eexists; econstructor; eauto; fail.
    - edestruct (@Cut _ _ D _ m' t1 (weak t2 (open_formula phi t @ m :: Gamma)) (Exchange _ _ ( ∀ sigma; phi @ m :: open_formula phi t @ m :: Gamma) _ H3 ltac:(solveSubPath)) nft1).
      eapply WeakeningTyping; eauto; try solve [solveSubPath].
      repeat solveProper.
      solveNFT.
      repeat rewrite WeakeningTypingSize; simpl; solveCutRel.
      edestruct (forallR_inversion h2) as [y' [n1 [n2 [n3 [t' T']]]]].
      assert (sigT (fun t' : proofTerm => typing Gamma t' ((open_formula phi t) @ m))).
      eapply open_with_fresherRT; eauto.
      rewrite n1; auto.
      destruct H as [t4 T4].
      destruct (NormalizeTyping T4) as [t3' [T3' nft3]].      
      destruct (NormalizeTyping t0) as [x0' [t0' nfx0']].
      edestruct (@Cut _ (open_formula phi t) _ _ _ x0' t3' t0' nfx0' T3' nft3).
      simpl; solveCutRel.
      rewrite OpenFormulaSize; auto.
      eauto.
    - edestruct (@Cut _ _ D _ m' t1 (weak t2 (open_formula phi t @ m0 :: Gamma)) (Exchange _ _ (C @ m :: open_formula phi t @ m0 :: Gamma) _ H3 ltac:(solveSubPath)) nft1).
      eapply WeakeningTyping; eauto; try solve [solveSubPath].
      repeat solveProper.
      solveNFT.
      repeat rewrite WeakeningTypingSize; simpl; solveCutRel.
      eexists.
      econstructor; eauto; fail.
    - edestruct Cut with (1 := H7); eauto.
      solveCutRel.
      exists (forallRTerm x).
      eapply forallRr with (y := y); eauto 2.
      intro h.
      apply H3.
      econstructor; eauto; fail.
    - destruct t2; inversion h2; subst; simpl in *; repeat destructProd; try solve [eapply (Cut_h2MCR) with (1 := h2) (3 := h1); simpl; auto].
      + edestruct Cut with (x2 := t2) (3 := H3); auto.
        eapply (WeakeningTyping h1); try solveSubPath.
        repeat solveProper.
        solveNFT.
        eexists; econstructor; eauto; fail.
      + edestruct Cut with (x2 := t2_1) (3 := H5); simpl; auto.
        eapply (WeakeningTyping h1); try solveSubPath.
        repeat solveProper.
        solveNFT.
        solveCutRel.
        edestruct Cut with (x2 := t2_2) (3 := H7); simpl; auto.
        eapply (WeakeningTyping h1); try solveSubPath.
        repeat solveProper.
        solveNFT.
        solveCutRel.
        eexists; econstructor; eauto; fail.
      + edestruct Cut with (x2 := t2_2) (3 := H7); auto.
        eapply (WeakeningTyping h1); try solveSubPath.
        repeat solveProper.
        solveNFT.
        repeat rewrite WeakeningTypingSize; simpl; solveCutRel.
        eexists; econstructor; eauto; fail.
      + edestruct Cut with (x2 := t2) (3 := H6); auto.
        eapply (WeakeningTyping h1); try solveSubPath.
        repeat solveProper.
        solveNFT.
        eexists; econstructor; eauto; fail.
      + pose (freshInSequent (open_formula phi (varTerm y0) @ m0 :: (∃ VarSort y; phi @ m) :: Gamma) (D @ m') (VarSort y0)) as y'.
        destruct (open_with_fresherLT'' _ _ _ _ y0 y' t2 H7 _ nft2) as [t' [T [nft' eq]]]; auto.
        unfold y'.
        rewrite freshInSequentOfSort; auto.
        edestruct Cut with (x2 := t') (3 := T); auto.
        3 : simpl; rewrite eq; solveCutRel.
        eapply (WeakeningTyping h1); try solveSubPath.
        repeat solveProper.
        solveNFT.
        eexists.
        eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
        unfold y'.
        destruct (freshInSequentIsFresh (open_formula phi (varTerm y0) @ m0 :: (∃ VarSort y; phi @ m) :: Gamma) (D @ m') (VarSort y0)) as [fv1 fv2].
        eapply FreshWithMore.
        2: eauto.
        intros.
        simpl; auto.
      + assert (sigT (fun t' => prod (typing (open_formula phi t @ m :: ∃ VarSort y; phi @ m ::  Gamma) t' (D @ m')) (prod (term_size t1 = term_size t') (NormalFormTerm' t' true)))).
        eapply open_with_fresherLT; eauto;
          try (apply freshInSequentIsFresh; auto); try (rewrite freshInSequentOfSort; auto).
        destruct H as [t1' [H4' [eq nft1']]].        
        edestruct (@Cut _ _ D _ m' t1' (weak (existsRTerm t2) ((open_formula phi t @ m :: Gamma))) (Exchange _ _ (∃ VarSort y; phi @ m :: open_formula phi t @ m :: Gamma) _ H4' ltac:(solveSubPath)) nft1').
        eapply WeakeningTyping; eauto; try solve [solveSubPath].
        repeat solveProper.
        solveNFT.
        repeat rewrite WeakeningTypingSize; rewrite eq; simpl; solveCutRel.
        (*prove by subst*)
        destruct (NormalizeTyping t0) as [x' [t' h3]].
        edestruct Cut with (x2 := t2) (3 := H9); simpl; auto.
        eauto.
        unfold NormalFormTerm in h3; auto.
        solveCutRel.
        rewrite OpenFormulaSize; eauto.
        eauto.
      + edestruct Cut with (x2 := t2) (3 := H3); auto.
        eapply (WeakeningTyping h1); try solveSubPath.
        repeat solveProper.
        solveNFT.
        eexists; econstructor; eauto; fail.
    - edestruct Cut with (x1 := C) (Gamma := open_formula phi (varTerm y) @ m0 :: Gamma) (m := m); auto.
      apply (Exchange _ _ _ _ H4).
      solveSubPath.
      auto.
      eapply (WeakeningTyping h2); try solveSubPath.
      repeat solveProper.
      solveNFT.
      repeat rewrite WeakeningTypingSize; simpl; solveCutRel.
      eexists.
      eapply existsLr with (y := y); eauto.
      intro.
      apply H1.
      inversion H; subst.
      all : apply Exists_cons_tl; auto.
    - edestruct (@Cut _ _ (open_formula phi t) _ m' t1 t2 H5 nft1 h2 nft2).
      simpl; solveCutRel.
      exists (existsRTerm x).
      eapply existsRr; eauto 2.
    - edestruct (@Cut _ _ phi _ (m' ⋅ p ⟨ lab ⟩) t1 t2 H2 nft1 h2 nft2).
      simpl; solveCutRel.
      exists (saysRTerm x).
      constructor; auto.
    - edestruct (@Cut _ _ D _ m' t1 (weak t2 (phi @ (m ⋅ p ⟨ lab ⟩) :: Gamma)) (Exchange _ _ (p □ ⟨ lab ⟩ phi @ m :: phi @ m ⋅ p ⟨ lab ⟩ :: Gamma) _ H1 ltac:(solveSubPath)) nft1).
      eapply WeakeningTyping; eauto; try solve [solveSubPath].
      repeat solveProper.
      solveNFT.
      repeat rewrite WeakeningTypingSize; simpl; solveCutRel.
      apply SaysR_inversion_typing in h2.
      destruct h2 as [t3 T3].
      destruct (NormalizeTyping t) as [x' [t' h2]].      
      destruct (NormalizeTyping T3) as [t3' [T3' nft3]].      
      edestruct (@Cut _ _ D _ m' x' t3' t' h2); eauto.
    - edestruct (@Cut _ _ D _ m' t1 (weak t2 (phi @ m0 ⋅ p ⟨ lab ⟩ :: Gamma)) (Exchange _ _ (C @ m :: phi @ m0 ⋅ p ⟨ lab ⟩ :: Gamma) _ H1 ltac:(solveSubPath)) nft1 ).
      eapply WeakeningTyping; eauto; try solve [solveSubPath].
      repeat solveProper.
      solveNFT.
      repeat rewrite WeakeningTypingSize; simpl; solveCutRel.
      eexists.
      eapply saysLr; eauto.
  Qed.

  Theorem SaysR_inversion {Gamma : Context} {phi : flafolFormula} {m : Modality} {p l : flafolTerm} (pf : Gamma ⊢ p □⟨l⟩ phi @ m) : Gamma ⊢ phi @ m ⋅ p⟨l⟩.
  Proof.
    remember (ProofToTyping _ _ pf) as t.
    destruct t as [t Ht].
    remember (@SaysR_inversion_typing t Gamma p l phi m Ht).
    destruct s as [t' Ht'].
    clear Heqs.
    apply TypingToProof in Ht'. exact Ht'.
  Qed.

End Cut.