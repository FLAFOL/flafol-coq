Require Export Term.
Require Export Formula.
Require Export Sequent.

Require Import Base.Lists.
Require Import Base.Permutation.
Require Import Tactics.FormulaEquality.
Require Import Tactics.TermEquality.
Require Import Tactics.WellFormedFormulaNoProofs.
Require Import Tactics.TermHasSortNoFormulas.
Require Import Tactics.CutTact.
Require Import Coq.Program.Wf.

Module Type Simulation (G : GroundInfo) (GTerm : Term G)
       (GFormula : Formula G GTerm)
       (TE : TermEquality G GTerm) (FE : FormulaEquality G GTerm GFormula TE)
       (THS : TermHasSort'' G GTerm TE)
       (WFF : WellFormedFormula' G GTerm TE THS GFormula FE)
       (PF : Sequent G GTerm GFormula TE FE THS WFF).
  Import G. Import GTerm. Import GFormula. Import PF.
  Import ListNotations. Import THS. Import WFF. 


  Fixpoint impSays (phi : flafolFormula) (p lab : flafolTerm) :=
    match phi with
      flowsto _ _ => phi
    | varFormula _ => phi
    | GFormula.rel s l =>phi 
    | TT => TT
    | FF => FF
    | and f1 f2 => and (impSays f1 p lab) (impSays f2 p lab)
    | or f1 f2 => or (impSays f1 p lab) (impSays f2 p lab)
    | implies f1 l f2 => (p □ ⟨ l ⟩ (impSays f1 p lab)) ==⟨ lab ⟩> (impSays f2 p lab)
    | flafolForall sigma f => flafolForall sigma (impSays f p lab)
    | flafolExists sigma f => flafolExists sigma (impSays f p lab)
    | says p' l1 f => says p' l1 (impSays f p lab)
    | canRead _ _ => phi
    | canWrite _ _ => phi
    end.
  
  Fixpoint InFrontOfModality (p lab : flafolTerm) (m : Modality) :=
    match m with
    | g lab' => (g lab) ⋅ p ⟨lab'⟩
    | m' ⋅ q ⟨lab'⟩ => (InFrontOfModality p lab m') ⋅ q ⟨lab'⟩
    end.
  
  Notation "⟨ p , lab ⟩ ⋅ m" := (InFrontOfModality p lab m) (at level 30).
  
  Definition impSaysInFrontMod (b : Belief) (p lab : flafolTerm) :=
    let (phi, m) := b in
    (impSays phi p lab) @ (⟨ p , lab ⟩ ⋅ m).

  Notation "b ☉ p ⟨ lab ⟩" := (impSaysInFrontMod b p lab) (at level 21). 

  Lemma PathTensor : forall G b p lab, Path b G -> Path (b ☉ p ⟨ lab ⟩) (map (fun b' => b' ☉ p ⟨ lab ⟩) G).
  Proof.
    induction G; intros; inversion H; simpl; subst.
    apply Here.
    apply There; eauto.    
  Qed.

  Lemma InFrontProper : forall m p lab,
      ProperModality m -> ⊢s p ::: Principal -> ⊢s lab ::: Label ->
      ProperModality (⟨p, lab⟩ ⋅ m).
  Proof.
    intros m p lab H H0 H1.
    induction m; simpl.
    inversion H; apply simProper; eauto; constructor; auto.
    inversion H; apply simProper; eauto.
  Qed.

  Lemma openFormulaImpSays : forall phi n p lab t, lc_term lab -> lc_term p -> open_formula_rec n (impSays phi p lab) t = impSays (open_formula_rec n phi t) p lab.
  Proof.
    induction phi; simpl; intros; eauto; repeat (f_equal; auto).
    1, 2 : apply OpenRecLCTerm; auto.
  Qed.
  
  Lemma wffSim : forall phi lab p, ⊢wff phi -> ⊢s lab ::: Label -> ⊢s p ::: Principal -> ⊢wff (impSays phi p lab).
  Proof.
    induction phi using ClosedFormulaInduction; simpl; intros; eauto; try inversion H; subst; try (econstructor; eauto; fail).
    - apply impliesWF; auto.
      apply saysWF; auto.
    - inversion H0; subst.
      apply forallWF with (L := L0 ++ L); intros.
      rewrite openFormulaImpSays with (n := 0).
      apply H; auto.
      intro; apply H3.
      apply in_or_app; auto.
      apply H4; auto.
      intro; apply H3.
      apply in_or_app; auto.
      all : eapply hasSort_lc; eauto.
    - inversion H0; subst.
      apply existsWF with (L := L0 ++ L); intros.
      rewrite openFormulaImpSays with (n := 0).
      apply H; auto.
      intro; apply H3.
      apply in_or_app; auto.
      apply H4; auto.
      intro; apply H3.
      apply in_or_app; auto.
      all : eapply hasSort_lc; eauto.
  Qed.

  Lemma ModalityCombineSim: forall m' m p lab,  ⟨ p, lab ⟩ ⋅ ModalityCombine m m' = ModalityCombine (⟨ p, lab ⟩ ⋅ m) m'.
  Proof.
    induction m'; auto.
    destruct a.
    intros.
    - assert (ModalityCombine m ((f, f0) :: m') = ModalityCombine (m ⋅ f ⟨ f0 ⟩) m') as eq by reflexivity.
      rewrite eq.
      rewrite IHm'.
      auto.
  Qed.

  
  Fixpoint ExtendPathToDouble (m : Modality) (p lab : flafolTerm) (pth : PathToDoubleInModality m) : PathToDoubleInModality (⟨p, lab⟩ ⋅ m).
  Proof.
    case pth; simpl; intros.
    - apply hereDouble.
    - apply thereDouble.
      apply ExtendPathToDouble; auto.    
  Defined.

  Lemma ReplaceExtendedDouble : forall m pth p lab, CollapseDoubleInModality (ExtendPathToDouble m p lab pth) = (⟨ p, lab ⟩ ⋅ CollapseDoubleInModality pth).
  Proof.
    induction pth; simpl; intros; auto.
    rewrite IHpth; auto.    
  Qed.
    
  
  Program Fixpoint ExtendPathToLabel (m : Modality) (p lab lab' : flafolTerm)
          (pi : PathToLabelInModality m lab') : PathToLabelInModality (⟨p, lab⟩ ⋅ m) lab' :=
    match pi with
    | hereGLab lab' => hereSimLab (g lab) p lab'
    | hereSimLab m' q _ => hereSimLab (⟨p, lab⟩ ⋅ m') q lab'
    | thereLab m' q _ lab'' rho => thereLab _ _ _ _ (ExtendPathToLabel m' p lab lab' rho)
    end.
  
  Lemma ReplaceExtendedPath : forall (m : Modality) (p lab lab1 lab2 : flafolTerm)
                                (pi : PathToLabelInModality m lab1),
      ⟨p, lab⟩ ⋅ (ReplaceLabelInModality m lab1 lab2 pi)
      = ReplaceLabelInModality (⟨p, lab⟩ ⋅ m) lab1 lab2 (ExtendPathToLabel m p lab lab1 pi).
  Proof.
    intros m p lab lab1 lab2 pi.
    induction pi; cbn; auto; rewrite IHpi; auto.
  Qed.  

  Lemma ExtendedPathVarM : forall (m : Modality) (lab1 : flafolTerm) (pi : PathToLabelInModality m lab1) (p lab lab2 : flafolTerm), VarModality (ExtendPathToLabel m p lab lab1 pi) lab2 = (⟨ p, lab ⟩ ⋅ VarModality pi lab2).
  Proof.
    intros m lab1 pi p lab lab2.
    induction pi; intros; auto.
    destruct pi; simpl; auto.
  Qed.

  Lemma ProperContextSim : forall (G : Context) (p lab : flafolTerm), ⊢s p ::: Principal -> ⊢s lab ::: Label -> ProperContext G ->  ProperContext (map (fun b' : Belief => b' ☉ p ⟨ lab ⟩) G).
  Proof.
    induction G; simpl; intros; auto.
    inversion H1; subst.
    apply Forall_cons; auto.
    2 : apply IHG; auto.
    destruct a.
    inversion H4; subst.
    constructor.
    apply InFrontProper; auto.
    apply wffSim; auto.
  Qed.

  Fixpoint ExtendPathToPrin (m : Modality) (p' p lab : flafolTerm) (pth : PathToPrinInModality m p') : PathToPrinInModality (⟨p, lab⟩ ⋅ m) p'.
  Proof.
    case pth; simpl; intros.
    - apply hereSimP.
    - apply thereP.
      apply ExtendPathToPrin; auto.    
  Defined.

  Lemma ReplaceExtendedPrin : forall m p1 p2 pth p lab, ReplacePrinInModality (ExtendPathToPrin m p1 p lab pth) p2 = (⟨ p, lab ⟩ ⋅ ReplacePrinInModality pth p2).
  Proof.
    induction pth; simpl; intros; auto.
    rewrite IHpth; auto.
  Qed.

  Lemma FwdM : forall m p0 q pth p lab, FwdModality (ExtendPathToPrin m p0 p lab pth) q = (⟨ p, lab ⟩ ⋅ ModalityBeforePrin pth) ⋅ q ⟨ LabelAtPrin pth ⟩.
  Proof.
    intros m p0 q pth p lab.
    induction pth; intros; auto.
  Qed.

 Lemma ReplaceLabelPrin : forall m p0 pth p lab, LabelAtPrin (ExtendPathToPrin m p0 p lab pth) = LabelAtPrin pth.
 Proof.
   induction pth; simpl; intros; auto.   
 Qed.
   
 Hint Resolve InFrontProper.

 
  
  Theorem Simulation : forall t G b p lab, typing G t b -> ⊢s p ::: Principal -> ⊢s lab ::: Label -> sigT (fun t' => typing (map (fun b' => b' ☉ p ⟨ lab ⟩) G) t' (b ☉ p ⟨ lab ⟩)).
  Proof.
    induction t; simpl; intros; inversion H; subst; simpl in *;
      try (match goal with
           | [h : Path _ _, h1 : ⊢s ?p ::: Principal, h2 : ⊢s ?lab ::: Label |- _] => pose proof h; apply PathTensor with (p := p) (lab := lab) in h
           end);
      (match goal with
       | [h1 : typing _ ?t1 _, IH1 : forall _ _ _ _, typing _ ?t1 _-> _, h2 : typing _ ?t2 _, IH2 : forall _ _ _ _, typing _ ?t2 _-> _ |- _] => edestruct IH1 with (1 := h1); eauto; edestruct IH2 with (1 := h2); eauto
       | [h : typing _ ?t _, IH : forall _ _ _ _, typing _ ?t _-> _ |- _] => edestruct IH with (1 := h); eauto
       | _ => idtac
       end); try (eexists; econstructor; eauto; fail).
    - eexists.
      apply axiomr; auto.
      apply ProperContextSim; auto.
    - eexists.
      apply TTRr; eauto.
      apply ProperContextSim; auto.
    - eexists.
      rewrite ModalityCombineSim.
      apply FFLr; auto.
      apply ProperContextSim; auto.
      apply wffSim; auto.
    - eexists.
      apply OrR1r; eauto.
      apply wffSim; auto.
    - eexists.
      apply OrR2r; eauto.
      apply wffSim; auto.
    - eexists.
      eapply ImpLr; eauto.
      fold impSays.
      simpl in t.
      apply saysRr; eauto.
    - eexists.
      simpl in t0.      
      apply ImpRr.
      eapply saysLr.
      apply Here.
      simpl in t0.
      eapply WeakeningTyping; eauto.
      apply provenProperContextTyping in t0.
      inversion t0; subst.
      repeat apply Forall_cons; auto.
      constructor; auto.
      constructor; auto.
      inversion H5.
      inversion H2; subst.      
      constructor; auto.
      solveSubPath.      
    - eexists.
      eapply forallLr with (t := t0); eauto.
      fold impSays.
      simpl in t1.
      rewrite openFormulaImpSays with (n := 0); eauto.
      eauto.
      all : eapply hasSort_lc; eauto.
    - clear t0 x.
      pose (freshInSequent (map (fun b' : Belief => b' ☉ p ⟨ lab ⟩) G) (impSays phi p lab @ (⟨ p, lab ⟩ ⋅ m)) (VarSort y)) as y'.      
      apply open_with_fresherRT1 with (y' := y') in H8; try (symmetry; apply freshInSequentOfSort); auto.
      edestruct IHt with (1 := H8); eauto.
      eexists.
      apply forallRr with (y := y'); try (apply freshInSequentIsFresh; auto); try (apply freshInSequentOfSort; auto).
      1, 2: pose proof (freshInSequentIsFresh (map (fun b' : Belief => b' ☉ p ⟨ lab ⟩) G) (impSays phi p lab @ (⟨ p, lab ⟩ ⋅ m)) (VarSort y)).
      1, 2: destruct H2.
      1, 2: intro; apply H3.
      1, 2: try (econstructor; eauto; fail).
      simpl in t0.
      rewrite openFormulaImpSays with (n := 0); eauto.
      all : eapply hasSort_lc; eauto.
    - clear t0 x.
      pose (freshInSequent (map (fun b' : Belief => b' ☉ p ⟨ lab ⟩) G) (b ☉ p ⟨ lab ⟩) (VarSort y)) as y'.
      destruct b.
      apply open_with_fresherLT1 with (y' := y') in H7; try (symmetry; apply freshInSequentOfSort); auto.
      edestruct IHt with (1 := H7); eauto.
      eexists.
      eapply existsLr with (y := y'); try (apply freshInSequentIsFresh; auto); try (apply freshInSequentOfSort; auto); eauto.
      fold impSays.
      simpl in t0.
      rewrite openFormulaImpSays with (n := 0); eauto.
      1, 2 : eapply hasSort_lc; eauto.
      all : intro; apply H5; try (econstructor; eauto; fail).
    - eexists.
      eapply existsRr with (t := t0); eauto.
      simpl in t1.
      rewrite openFormulaImpSays with (n := 0); eauto.
      all : eapply hasSort_lc; eauto.
    - eexists.
      apply flowsToReflr; auto.
      apply ProperContextSim; auto.
    - simpl in t0.
      eexists.
      apply modalityExpandRr with (pth := ExtendPathToDouble m p lab pth).
      rewrite ReplaceExtendedDouble; eauto.
    - rewrite <-ReplaceExtendedDouble; eauto.
      eexists.
      apply modalityCollapseRr; eauto.
    - simpl in t0.
      eexists.
      simpl in pth'.
      eapply modalityExpandLr with (pth := ExtendPathToDouble m p lab pth); eauto.
      rewrite ReplaceExtendedDouble; auto. 
    - eexists.
      eapply modalityCollapseLr with (pth := ExtendPathToDouble m p lab pth); eauto.
      rewrite ReplaceExtendedDouble; eauto.      
    - eexists.
      rewrite ReplaceExtendedPath.
      apply RVariancer; eauto.
      rewrite ExtendedPathVarM.
      eauto.
    - eexists.
      eapply LVariancer with (lab1 := lab1) (lab2 := lab2) (pi := (ExtendPathToLabel m p lab lab1 pi)); eauto.
      simpl in t.
      rewrite <-ReplaceExtendedPath; eauto.
      simpl in t0.
      rewrite ExtendedPathVarM; eauto.
    - edestruct IHt1 with (1 := H6); eauto.
      eexists.
      rewrite <-ReplaceExtendedPrin.
      simpl in *.
      apply FwdRr; eauto.
      rewrite FwdM.
      rewrite ReplaceLabelPrin; eauto.
      rewrite FwdM; eauto.
      rewrite ReplaceLabelPrin; eauto.
    - edestruct IHt1 with (1 := H6); eauto.
      simpl in *.
      eexists.
      eapply FwdLr with (pth := (ExtendPathToPrin m q p lab pth)) (p := p0); eauto.
      rewrite ReplaceExtendedPrin; eauto.      
      rewrite FwdM.
      rewrite ReplaceLabelPrin; eauto.
      rewrite FwdM; eauto.
      rewrite ReplaceLabelPrin; eauto.
  Qed.
End Simulation.