Require Import Sequent.
Require Export Term. (* We use it enough below to just go ahead and import it directly. *)
Require Export Formula.

Require Import Base.Lists.
Require Import Tactics.CutTact.
Require Import Base.Permutation.
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

Module Type NormalForm (G : GroundInfo) (GTerm : Term G) (GFormula : Formula G GTerm)
       (TE : TermEquality G GTerm) (FE : FormulaEquality G GTerm GFormula TE)
       (THS : TermHasSort'' G GTerm TE)
       (WFF : WellFormedFormula' G GTerm TE THS GFormula FE) (SEQ : Sequent G GTerm GFormula TE FE THS WFF) (CT : CutTact G GTerm GFormula TE FE THS WFF SEQ).
  Import G. Import GTerm. Import GFormula. Import ListNotations.
  Import THS. Import WFF. Import SEQ. Import CT.

  Fixpoint NormalForm' {Gamma : Context} {b : Belief} (pf : Gamma ⊢ b) (Mode2 : bool) : Prop :=
    match pf with
    | axiom _ _ pctxt pth => True
    | TTR _ m pctxt pmod => True
    | FFL _ phi m m' pctxt phi_wf pmod pth pmod' => True
    | AndL _ phi psi m _ pth pf1 =>
      if Mode2
      then NormalForm' pf1 true
      else False
    | AndR _ phi psi m pf1 pf2 =>
      if Mode2
      then NormalForm' pf1 true /\ NormalForm' pf2 true
      else False
    | OrL _ phi psi m _ pth pf1 pf2 =>
      if Mode2
      then NormalForm' pf1 true /\ NormalForm' pf2 true
      else False
    | OrR1 _ phi psi m pf1 psi_wf =>
      if Mode2
      then NormalForm' pf1 true
      else False
    | OrR2 _ phi psi m pf1 phi_wf =>
      if Mode2
      then NormalForm' pf1 true
      else False
    | ImpL _ phi psi m l _ pth pf1 pf2 =>
      if Mode2
      then NormalForm' pf1 true /\ NormalForm' pf2 true
      else False
    | ImpR _ phi psi m' l pf1 => 
      if Mode2
      then NormalForm' pf1 true
      else False
    | forallL _ sigma phi t m _ lct tsort pth pf1 =>
      if Mode2
      then NormalForm' pf1 true
      else False
    | forallR _ sigma y phi m ysort yctxt yconc ym pf1 =>
      if Mode2
      then NormalForm' pf1 true
      else False
    | existsL _ sigma y phi m _ ysort yctxt yconc pth pf1 =>
      if Mode2
      then NormalForm' pf1 true
      else False
    | existsR _ sigma t phi m lct tsort pf1 =>
      if Mode2
      then NormalForm' pf1 true
      else False
    | flowsToRefl _ lab m pctxt labLabel pmod => True
    | flowsToTransR _ lab1 lab2 lab3 m pf1 pf2 =>
      if Mode2
      then NormalForm' pf1 true /\ NormalForm' pf2 true
      else False
    | saysR _ p lab phi m pf1 =>
      if Mode2
      then NormalForm' pf1 true
      else False
    | saysL _ p lab phi m _ pth pf1 =>
      if Mode2
      then NormalForm' pf1 true
      else False
    | modalityExpandR Gamma phi m pth pf1 =>
      NormalForm' pf1 false
    | modalityCollapseR Gamma phi m pth pf1 =>
      NormalForm' pf1 false
    | modalityExpandL _ phi m pth _ pth2 pf1 =>
      NormalForm' pf1 false
    | modalityCollapseL _ phi m pth _ pth2 pf1 =>
      NormalForm' pf1 false
    | RVariance _ lab1 lab2 phi m pi pf1 pf2 =>
      NormalForm' pf1 false /\ NormalForm' pf2 false
    | LVariance _ lab1 lab2 phi m pi _ pth pf1 pf2 =>
      NormalForm' pf1 false /\ NormalForm' pf2 false
    | FwdR _ phi m p q pth pf1 pf2 pf3 =>
      NormalForm' pf1 false /\ NormalForm' pf2 false /\ NormalForm' pf3 false
    | FwdL Gamma phi m p q pth b _ pf1 pf2 pf3 =>
      NormalForm' pf1 false /\ NormalForm' pf2 false /\ NormalForm' pf3 false
    | CRVariance _ p lab1 lab2 m pf1 pf2 =>
      if Mode2
      then NormalForm' pf1 true /\ NormalForm' pf2 true
      else False
    | CWVariance _ p lab1 lab2 m pf1 pf2 =>
      if Mode2
      then NormalForm' pf1 true /\ NormalForm' pf2 true
      else False
    end.

  Theorem Mode1_implies_Mode2 : forall {Gamma : Context} {b : Belief} (pf : Gamma ⊢ b) (Mode2 : bool),
      NormalForm' pf false -> NormalForm' pf true.
  Proof.
    intros Gamma b pf Mode2 H.
    induction pf; simpl in *; 
      match goal with
      | [ H : False |- _ ] => inversion H
      | _ => idtac
      end; auto.
  Qed.

  Theorem NormalForm'_JMeq : forall {Gamma Delta : Context} {b1 b2 : Belief} (pf1 : Gamma ⊢ b1) (pf2 : Delta ⊢ b2) (Mode2 : bool), Gamma = Delta -> b1 = b2 -> JMeq pf1 pf2 -> NormalForm' pf1 Mode2 <-> NormalForm' pf2 Mode2.
  Proof.
    intros Gamma Delta b1 b2 pf1 pf2 Mode2 H H0 H1.
    generalize dependent pf2. destruct H. destruct H0. intros pf2 H1.
    apply JMeq_eq in H1. rewrite H1. reflexivity.
  Qed.

  Theorem NormalForm'_JMeq1 : forall {Gamma Delta : Context} {b1 b2 : Belief}
                                {pf1 : Gamma ⊢ b1} {pf2 : Delta ⊢ b2}
                                {Mode2 : bool},
      JMeq pf1 pf2 -> Gamma = Delta -> b1 = b2 -> NormalForm' pf1 Mode2 -> NormalForm' pf2 Mode2.
  Proof.
    intros Gamma Delta b1 b2 pf1 pf2 Mode2 e3 e1 e2 H.
    rewrite <- (NormalForm'_JMeq pf1 pf2 Mode2 e1 e2 e3).
    exact H.
  Qed.
  
  Theorem NormalForm'_JMeq2 : forall {Gamma Delta : Context} {b1 b2 : Belief}
                                {pf1 : Gamma ⊢ b1} {pf2 : Delta ⊢ b2}
                                {Mode2 : bool},
      JMeq pf1 pf2 -> Gamma = Delta -> b1 = b2 -> NormalForm' pf2 Mode2 -> NormalForm' pf1 Mode2.
  Proof.
    intros Gamma Delta b1 b2 pf1 pf2 Mode2 e3 e1 e2 H.
    rewrite (NormalForm'_JMeq pf1 pf2 Mode2 e1 e2 e3).
    exact H.
  Qed.

  Definition NormalForm {Gamma : Context} {b : Belief} (pf : Gamma ⊢ b) :=
    NormalForm' pf true.

  Lemma NormalForm'_eq1 : forall G1 G2 phi m b (x1 : G1 ⊢ phi @ m) (p : G1=G2),
       NormalForm' x1 b -> NormalForm' (eq_rect _ (fun G : Context => G ⊢ phi @ m) x1 G2 p) b.
  Proof.
    intros G1 G2 phi m b x1 p H.
    destruct p; auto.
  Qed.    

  Lemma NormalForm'_eq2 : forall Gamma b1 b2 b (x1 : Gamma ⊢ b1) (p : b1=b2),
       NormalForm' x1 b -> NormalForm' (eq_rect _ (fun B : Belief => Gamma ⊢ B) x1 b2 p) b.
  Proof.
    intros Gamma b1 b2 b x1 p H.
    destruct p; auto.
  Qed.    
  Ltac Normalize' :=
    repeat match goal with
           | [ |- True ] => exact I
           | [ H : False |- _ ] => inversion H
           | [ |- ?a = ?a] => reflexivity
           | [ H : ?P |- ?P ] => exact H
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : if ?b then _ else _ |- _ ] => destruct b
           | [ |- context[if ?b then _ else _]] => destruct b
           | [ H : JMeq ?pf' ?pf |- _ < proof_size ?pf ] =>
             apply (proof_size_JMeq_lt1 H); auto
           | [ H : NormalForm _ |- _] => unfold NormalForm in H; simpl in H; auto
           | [ |- _ /\ _ ] => split
           | [ H : JMeq ?pf' ?pf |- NormalForm' ?pf ?b ] =>
               match type of pf with
               | ?Gamma ⊢ ?b1 => match type of pf' with
                            | ?Delta ⊢ ?b2 => match goal with
                                         | [ H3 : Gamma = Delta, H4 : b1 = b2 |- _ ] =>
                                           rewrite <- (NormalForm'_JMeq pf' pf b H3 H4 H);
                                           simpl; auto
                                         | _ => assert (Gamma = Delta /\ b1 = b2)
                                         end
                            end
               end
           | [ |- NormalForm _ ] => unfold NormalForm; simpl; auto
           | [|- NormalForm' (proj1_sig (?f ?Delta ?D ?mod ?path ?pf' ?len)) _] =>
             let H := fresh in
             pose proof (proj2_sig (f Delta D mod path pf' len)) as H;
             simpl in H; apply H
           | [ |- context[eq_ind_r] ] => unfold eq_ind_r
           | [ |- context[eq_ind] ] => unfold eq_ind
           | [ |- context[eq_rect] ] => unfold eq_rect
           | [ |- context[match ?e with | eq_refl => _ end] ] => destruct e; simpl
           | [ |- context[match ?H with | conj _ _ => _ end] ] => destruct H; simpl
           | [ H1 : NormalForm' ?pf ?b, H2 : JMeq (_ ?pf1 _ _) ?pf |- NormalForm' ?pf1 ?b ] =>
             apply (NormalForm'_JMeq2 H2) in H1; simpl in H1; auto
           | [ H1 : NormalForm' ?pf ?b, H2 : JMeq (_ ?pf1 _) ?pf |- NormalForm' ?pf1 ?b ] =>
             apply (NormalForm'_JMeq2 H2) in H1; simpl in H1; auto
           | [ H1 : NormalForm' ?pf ?b, H2 : JMeq (_ ?pf1) ?pf |- NormalForm' ?pf1 ?b ] =>
             apply (NormalForm'_JMeq2 H2) in H1; simpl in H1; auto
           | [ H : JMeq (_ ?pf1) ?pf |- proof_size ?pf1 < proof_size ?pf  ] =>
             apply JMeq_eq in H; rewrite <- H; simpl; auto
           | [ H : JMeq (_ ?pf1 _) ?pf |- proof_size ?pf1 < proof_size ?pf  ] =>
             apply JMeq_eq in H; rewrite <- H; simpl; auto
           | [ H : JMeq (_ ?pf1 _ _) ?pf |- proof_size ?pf1 < proof_size ?pf  ] =>
             apply JMeq_eq in H; rewrite <- H; simpl; auto
           | [ H : JMeq (_ ?pf1 _ _ _) ?pf |- proof_size ?pf1 < proof_size ?pf  ] =>
             apply JMeq_eq in H; rewrite <- H; simpl; auto
           | [ H : JMeq (_ ?pf1 _ _ _ _) ?pf |- proof_size ?pf1 < proof_size ?pf  ] =>
             apply JMeq_eq in H; rewrite <- H; simpl; auto
           | [ H : JMeq (_ ?pf1 _ _ _ _ _) ?pf |- proof_size ?pf1 < proof_size ?pf  ] =>
             apply JMeq_eq in H; rewrite <- H; simpl; auto
           | [ |- ?a < S ?b ] => apply PeanoNat.Nat.lt_succ_r
           | [ |- ?a <= Arith.max ?a _ ] => apply PeanoNat.Nat.le_max_l
           | [ |- ?a <= Arith.max _ ?b] => apply PeanoNat.Nat.le_max_r
           | [ |- ?a <= Arith.max _ (Arith.max ?a ?b) ] =>
             transitivity (Arith.max a b)
           | [ |- ?a <= Arith.max _ (Arith.max ?b ?a) ] =>
             transitivity (Arith.max b a)
           end.

  
  Ltac Normalize :=
    repeat match goal with
           | [ |- True ] => exact I
           | [ H : False |- _ ] => inversion H
           | [ |- ?a = ?a] => reflexivity
           | [ H : ?P |- ?P ] => exact H
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : if ?b then _ else _ |- _ ] => destruct b
           | [ |- context[if ?b then _ else _]] => destruct b
           | [ |- proof_size _ < proof_size _] => Normalize'
           | [ H : JMeq ?pf' ?pf |- _ < proof_size ?pf ] =>
             apply (proof_size_JMeq_lt1 H); auto
           | [ H : NormalForm _ |- _] => unfold NormalForm in H; simpl in H; auto
           | [ |- _ /\ _ ] => split
           | [ H : JMeq ?pf' ?pf |- NormalForm' ?pf ?b ] =>
               match type of pf with
               | ?Gamma ⊢ ?b1 => match type of pf' with
                            | ?Delta ⊢ ?b2 => match goal with
                                         | [ H3 : Gamma = Delta, H4 : b1 = b2 |- _ ] =>
                                           rewrite <- (NormalForm'_JMeq pf' pf b H3 H4 H);
                                           simpl; auto
                                         | _ => assert (Gamma = Delta /\ b1 = b2)
                                         end
                            end
               end
           | [ |- NormalForm _ ] => unfold NormalForm; simpl; auto
           | [|- NormalForm' (proj1_sig (?f ?Delta ?D ?mod ?path ?pf' ?len)) _] =>
             let H := fresh in
             pose proof (proj2_sig (f Delta D mod path pf' len)) as H;
             simpl in H; apply H
           | [|- NormalForm' (proj1_sig ?h) _] => destruct h
           | [ |- NormalForm' (eq_rect _ (fun x => x ⊢ _) _ _ _) _ ] => apply NormalForm'_eq1; simpl; Normalize
           | [ |- NormalForm' (eq_rect _ (fun x => _ ⊢ x) _ _ _) _ ] => apply NormalForm'_eq2; simpl; Normalize
           | [ |- context[match ?e with | eq_refl => _ end] ] => destruct e; simpl
           | [ |- context[match ?H with | conj _ _ => _ end] ] => destruct H; simpl
           | [ H1 : NormalForm' ?pf ?b, H2 : JMeq (_ ?pf1 _ _) ?pf |- NormalForm' ?pf1 ?b ] =>
             apply (NormalForm'_JMeq2 H2) in H1; simpl in H1; auto
           | [ H1 : NormalForm' ?pf ?b, H2 : JMeq (_ ?pf1 _) ?pf |- NormalForm' ?pf1 ?b ] =>
             apply (NormalForm'_JMeq2 H2) in H1; simpl in H1; auto
           | [ H1 : NormalForm' ?pf ?b, H2 : JMeq (_ ?pf1) ?pf |- NormalForm' ?pf1 ?b ] =>
             apply (NormalForm'_JMeq2 H2) in H1; simpl in H1; auto
           | [ H : JMeq (_ ?pf1) ?pf |- proof_size ?pf1 < proof_size ?pf  ] =>
             apply JMeq_eq in H; rewrite <- H; simpl; auto
           | [ H : JMeq (_ ?pf1 _) ?pf |- proof_size ?pf1 < proof_size ?pf  ] =>
             apply JMeq_eq in H; rewrite <- H; simpl; auto
           | [ H : JMeq (_ ?pf1 _ _) ?pf |- proof_size ?pf1 < proof_size ?pf  ] =>
             apply JMeq_eq in H; rewrite <- H; simpl; auto
           | [ H : JMeq (_ ?pf1 _ _ _) ?pf |- proof_size ?pf1 < proof_size ?pf  ] =>
             apply JMeq_eq in H; rewrite <- H; simpl; auto
           | [ H : JMeq (_ ?pf1 _ _ _ _) ?pf |- proof_size ?pf1 < proof_size ?pf  ] =>
             apply JMeq_eq in H; rewrite <- H; simpl; auto
           | [ H : JMeq (_ ?pf1 _ _ _ _ _) ?pf |- proof_size ?pf1 < proof_size ?pf  ] =>
             apply JMeq_eq in H; rewrite <- H; simpl; auto
           | [ |- ?a < S ?b ] => apply PeanoNat.Nat.lt_succ_r
           | [ |- ?a <= Arith.max ?a _ ] => apply PeanoNat.Nat.le_max_l
           | [ |- ?a <= Arith.max _ ?b] => apply PeanoNat.Nat.le_max_r
           | [ |- ?a <= Arith.max _ (Arith.max ?a ?b) ] =>
             transitivity (Arith.max a b)
           | [ |- ?a <= Arith.max _ (Arith.max ?b ?a) ] =>
             transitivity (Arith.max b a)
           end.
  
  
  Fixpoint NormalFormTerm' (e : proofTerm) (Mode2 : bool) : Set :=
    match e with
    | axiomTerm => unit
    | TTRTerm => unit
    | FFLTerm => unit
    | AndLTerm e1 =>
      if Mode2
      then NormalFormTerm' e1 true
      else Empty_set
    | AndRTerm e1 e2 =>
      if Mode2
      then NormalFormTerm' e1 true * NormalFormTerm' e2 true
      else Empty_set
    | OrLTerm pf1 pf2 =>
      if Mode2
      then NormalFormTerm' pf1 true * NormalFormTerm' pf2 true
      else Empty_set
    | OrR1Term pf1 =>
      if Mode2
      then NormalFormTerm' pf1 true
      else Empty_set
    | OrR2Term pf1 =>
      if Mode2
      then NormalFormTerm' pf1 true
      else Empty_set
    | ImpLTerm pf1 pf2 =>
      if Mode2
      then NormalFormTerm' pf1 true * NormalFormTerm' pf2 true
      else Empty_set
    | ImpRTerm pf1 => 
      if Mode2
      then NormalFormTerm' pf1 true
      else Empty_set
    | forallLTerm pf1 =>
      if Mode2
      then NormalFormTerm' pf1 true
      else Empty_set
    | forallRTerm pf1 =>
      if Mode2
      then NormalFormTerm' pf1 true
      else Empty_set
    | existsLTerm pf1 =>
      if Mode2
      then NormalFormTerm' pf1 true
      else Empty_set
    | existsRTerm pf1 =>
      if Mode2
      then NormalFormTerm' pf1 true
      else Empty_set
    | flowsToReflTerm => unit
    | flowsToTransRTerm pf1 pf2 =>
      NormalFormTerm' pf1 false * NormalFormTerm' pf2 false
    | saysRTerm pf1 =>
      if Mode2
      then NormalFormTerm' pf1 true
      else Empty_set
    | saysLTerm pf1 =>
      if Mode2
      then NormalFormTerm' pf1 true
      else Empty_set
    | modalityExpandRTerm pf1 =>
      NormalFormTerm' pf1 false
    | modalityCollapseRTerm pf1 =>
      NormalFormTerm' pf1 false
    | modalityExpandLTerm pf1 =>
      NormalFormTerm' pf1 false
    | modalityCollapseLTerm pf1 =>
      NormalFormTerm' pf1 false
    | RVarianceTerm pf1 pf2 =>
      NormalFormTerm' pf1 false * NormalFormTerm' pf2 false
    | LVarianceTerm pf1 pf2 =>
      NormalFormTerm' pf1 false * NormalFormTerm' pf2 false
    | FwdRTerm pf1 pf2 pf3 =>
      NormalFormTerm' pf1 false * NormalFormTerm' pf2 false * NormalFormTerm' pf3 false
    | FwdLTerm pf1 pf2 pf3 =>
      NormalFormTerm' pf1 false * NormalFormTerm' pf2 false * NormalFormTerm' pf3 false
    | CRVarianceTerm pf1 pf2 =>
      NormalFormTerm' pf1 false * NormalFormTerm' pf2 false
    | CWVarianceTerm pf1 pf2 =>
      NormalFormTerm' pf1 false * NormalFormTerm' pf2 false
    end.
  
  Definition NormalFormTerm (e : proofTerm) := NormalFormTerm' e true.

  Lemma nfFtoT : forall t, NormalFormTerm' t false -> NormalFormTerm' t true.
  Proof.
    induction t; simpl; intros; eauto.
    all: try match goal with
         | [h : Empty_set |- _] => inversion h
         end.
  Qed.  

  Lemma weakNFT : forall {G t b}, NormalFormTerm' t b -> NormalFormTerm' (weak t G) b.
  Proof.
    unfold weak; auto.
  Qed.    

  Lemma open_with_fresherRTS' : forall Gamma phi m y y' t (h : typing Gamma t (open_formula phi (varTerm y) @ m)) bol, NormalFormTerm' t bol -> VarSort y = VarSort y' -> y ∉FVC Gamma -> y ∉FVF phi -> y ∉FVM m -> sigT (fun t'  => prod (typing Gamma t' (open_formula phi (varTerm y') @ m)) (prod (NormalFormTerm' t' bol) (term_size t = term_size t'))).
  Proof.
    intros.
    exists t.
    split; [eapply open_with_fresherRT1; eauto | auto].
  Qed.
  
  Lemma open_with_fresherLT'' : forall Gamma phi b m y y' t (h : typing ((open_formula phi (varTerm y)) @ m :: Gamma) t b) bol, NormalFormTerm' t bol -> Path (∃ VarSort y; phi @ m) Gamma -> VarSort y = VarSort y' -> y ∉FVC Gamma ->  y ∉FVB b -> sigT (fun t' => prod (typing ((open_formula phi (varTerm y')) @ m :: Gamma) t' b) (prod (NormalFormTerm' t' bol) (term_size t = term_size t'))).
  Proof.
    intros.
    destruct b.
    exists t.    
    split; [eapply open_with_fresherLT1; eauto | auto].
    all : intro.
    all : apply H3.
    all : econstructor; eauto; fail.
  Qed.
    
  Ltac solveNFT := simpl; match goal with
                   | [|- NormalFormTerm _ * _] => simpl; split; solveNFT
                   | [|- _ * NormalFormTerm' _ _] => simpl; split; solveNFT
                   | [|- NormalFormTerm' _ _ * _] => simpl; split; solveNFT
                   | [|- NormalFormTerm' (weak _ _) _] => simpl; apply weakNFT; auto
                   | _ => auto
                   end.

  Ltac simplNFProofs :=
    try
      match goal with
      | [IH1 : NormalFormTerm' ?e1 ?b1 -> _ , h1 : NormalFormTerm' ?e1 ?b1, IH2 : NormalFormTerm' ?e2 ?b2 -> _ , h2 : NormalFormTerm' ?e2 ?b2 |- _] => edestruct (IH1 h1) as [x1 []]; eauto; try solve [solveProper | repeat apply There; eauto]; edestruct (IH2 h2) as [x2 []]; eauto; try solve [solveProper | repeat apply There; eauto]; eexists; split; [econstructor; eauto; fail | simpl; tauto]
      | [IH : NormalFormTerm' ?e ?b -> _ , h : NormalFormTerm' ?e ?b |- _] => edestruct (IH h) as [x []]; eauto; try solve [solveProper | repeat apply There; eauto]; eexists; split; [econstructor; eauto; fail | simpl; tauto]
      end.

  Ltac solveTyping := match goal with
                      | [h : typing _ ?e _ |- typing _ ?e _] => exact h; fail
                      | [h : typing _ _ ?b |- typing _ _ ?b] => eapply WeakeningTyping; eauto;
                                                              try (match goal with [|- forall b, Path b _ -> Path b _] => try solve [solveSubPath]; fail end); try solve [repeat solveProper]
                      end.

  Ltac sndInduction e2 h2 Gamma H := generalize dependent Gamma; induction e2; intros; inversion h2; subst; pose proof H; simpl in *; eauto; repeat destructProd; try solve [eexists; split; [eapply flowsToTransRr; eauto| simpl; tauto]]; try solve [simplNFProofs].

  Definition projectTermTyping : forall {G t b}, typing G t b -> proofTerm := fun G t b h => t.


  Lemma NFmodalityExpandR : forall {e1 : proofTerm} (h0 : NormalFormTerm' e1 true) {Gamma : Context} {C : flafolFormula} {m : Modality} (ptdim : PathToDoubleInModality m) (h1 : typing Gamma e1 (C @ CollapseDoubleInModality ptdim)), @sigT proofTerm (fun e' => prod (typing Gamma e' (C @ m)) (NormalFormTerm' e' true)).
  Proof.
    induction e1; simpl; intros; inversion h1; subst; try solve [eexists; split; [eapply modalityExpandRr; eauto| simpl; auto]]; repeat destructProd; try solve [simplNFProofs].
    - edestruct (IHe1 h0) as [x' []]; eauto.
      eexists; split.
      eapply forallRr with (y := y); eauto.
      { clear IHe1 e1 h0 Gamma phi h1 H3 H5 H7 x' t n. 
        induction ptdim; simpl in *.
        apply NotFVMSimInversion in H6;
          repeat match goal with
                 | [H : _ /\ _ |- _ ] => destruct H
                 end;
          apply NotFVMSim; auto.
        apply NotFVMSim; auto.
        apply NotFVMSimInversion in H6.
        repeat match goal with
               | [H : _ /\ _ |- _ ] => destruct H
               end;
          apply NotFVMSim; auto.
      }
      simpl; auto.
    - edestruct (IHe1 h0) as [x' []]; eauto.
      eexists; split.
      eapply existsLr with (y := y); eauto.
      { clear IHe1 e1 h0 m0 pth Gamma phi h1 H1 H4 x' t n.
        apply NotInFVBInversion in H2. destruct H2 as [ym yC]; apply NotInFVB; auto; clear C yC.
        induction ptdim; simpl in ym.
        apply NotFVMSimInversion in ym;
          repeat match goal with
                 | [H : _ /\ _ |- _ ] => destruct H
                 end;
          apply NotFVMSim; auto.
        apply NotFVMSim; auto.
        apply NotFVMSimInversion in ym.
        repeat match goal with
               | [H : _ /\ _ |- _ ] => destruct H
               end;
          apply NotFVMSim; auto. }
      simpl; auto.
    - edestruct (IHe1 h0) with (ptdim := (thereDouble _ p lab ptdim)) as [x' []]; eauto.
      eexists; split.
      econstructor; eauto; fail.
      simpl; auto.
  Defined.

  Lemma NFmodalityCollapseR : forall {e1 : proofTerm} (h0 : NormalFormTerm' e1 true) {Gamma : Context} {C : flafolFormula} {m : Modality} (ptdim : PathToDoubleInModality m) (h1 : typing Gamma e1 (C @ m)), @sigT proofTerm (fun e' => prod (typing Gamma e' (C @ CollapseDoubleInModality ptdim)) (NormalFormTerm' e' true)).
  Proof.
    induction e1; simpl; intros; inversion h1; subst.
    9 : destruct h0.
    9 : edestruct (IHe1_2 n0) with (1 := H4) (ptdim := ptdim).
    9 : destruct p.
    9 : eexists; split; [eapply ImpLr; eauto | simpl; auto].
    all : try solve [eexists; split; [eapply modalityCollapseRr; eauto| simpl; auto]]; repeat destructProd; try solve [simplNFProofs].
    - edestruct (IHe1 h0) as [x' []]; eauto.
      eexists; split.
      eapply forallRr with (y := y); eauto.
      { clear IHe1 e1 h0 Gamma phi h1 H3 H5 H7 x' t n. 
        induction ptdim; simpl in *.
        apply NotFVMSimInversion in H6;
          repeat match goal with
                 | [H : _ /\ _ |- _ ] => destruct H
                 end;
          apply NotFVMSim; auto.
        intro.
        apply H.
        constructor; auto.
        apply NotFVMSimInversion in H6.
        repeat match goal with
               | [H : _ /\ _ |- _ ] => destruct H
               end;
          apply NotFVMSim; auto.
      }
      simpl; auto.
    - edestruct (IHe1 h0) as [x' []]; eauto.
      eexists; split.
      eapply existsLr with (y := y); eauto.
      { clear IHe1 e1 h0 m0 pth Gamma phi h1 H1 H4 x' t n.
        apply NotInFVBInversion in H2. destruct H2 as [ym yC]; apply NotInFVB; auto; clear C yC.
        induction ptdim; simpl in ym.
        apply NotFVMSimInversion in ym;
          repeat match goal with
                 | [H : _ /\ _ |- _ ] => destruct H
                 end;
          apply NotFVMSim; auto.
        eapply NotFVMSimInversion; eauto.
        apply NotFVMSimInversion in ym.
        repeat match goal with
               | [H : _ /\ _ |- _ ] => destruct H
               end;
          apply NotFVMSim; auto. }
      simpl; auto.
    - edestruct (IHe1 h0) with (ptdim := (thereDouble _ p lab ptdim)) as [x' []]; eauto.
      eexists; split.
      econstructor; eauto; fail.
      simpl; auto.
  Defined.

  Definition cut_rel : (nat * nat) -> (nat * nat) -> Prop :=
    fun t1 t2 => match t1, t2 with
              | (x1,y1), (x2,y2) =>
                x1 < x2 \/ (x1 = x2 /\ y1 < y2)
              end.

  Lemma prodltImpCutRel : forall n1 n2 n1' n2', cut_rel (n1, n2) (n1', n2') -> (lexprod nat (fun _ => nat) lt (fun _ x1 x2 => lt x1 x2) (existT (fun _ => nat) n1 n2) (existT (fun _ => nat) n1' n2')).
  Proof.
    unfold cut_rel.
    inversion 1; subst.
    apply left_lex; auto.
    destruct H0.
    rewrite H0.
    apply right_lex.
    auto.
  Qed.

  Lemma wffLexprod : well_founded (lexprod nat (fun _ => nat) lt (fun _ x1 x2 => lt x1 x2)).
  Proof.
    apply wf_lexprod.
    apply lt_wf.
    intros.
    apply lt_wf.    
  Qed.

  Definition liftToLexProd {A : Set} {B : Set} (ltA : A -> A -> Prop) (ltB : B -> B -> Prop) :=
    fun x1 x2 : (A * B) => lexprod A (fun _ => B) ltA (fun _ x1 x2 => ltB x1 x2) (existT (fun _ => B) (fst x1) (snd x1)) (existT (fun _ => B) (fst x2) (snd x2)).
      
  Lemma wffCutRel : well_founded cut_rel.
  Proof.
    eapply wf_incl with (R2 := liftToLexProd lt lt).
    intro.
    intros.
    destruct x, y.
    unfold liftToLexProd.
    apply prodltImpCutRel; auto.
    unfold liftToLexProd.
    apply wf_inverse_image.
    apply wffLexprod.
  Qed.
  
  Definition rel : (flafolFormula * proofTerm) -> (flafolFormula * proofTerm) -> Prop :=
    fun x1 x2 => match x1, x2 with
                | (f1, t1), (f2, t2) => cut_rel (formula_size f1, term_size t1) (formula_size f2, term_size t2)
              end.

   Definition rel' : (flafolFormula * proofTerm) -> (flafolFormula * proofTerm) -> Prop :=
    fun x1 x2 => cut_rel (formula_size (fst x1), term_size (snd x1)) (formula_size (fst x2), term_size (snd x2)).
  
  Theorem WfRel' : well_founded rel'.
  Proof.
    unfold rel'.
    apply wf_inverse_image.
    apply wffCutRel.
  Qed.
  
  Theorem WfRel : well_founded rel.
  Proof.
    unfold rel.
    eapply wf_incl with (R2 := rel').
    intro.
    intros.
    unfold rel'.
    destruct x, y.
    simpl; auto.
    apply WfRel'.
  Qed.
  
  
  Definition PMEL := fun (x : flafolFormula * proofTerm) => forall {Gamma : Context} {m : Modality} (pth : PathToDoubleInModality m) (b : Belief) (pth0 : Path ((fst x) @ CollapseDoubleInModality pth) Gamma)  (h0 : NormalFormTerm (snd x))  (h1 : typing ((fst x) @ m :: Gamma) (snd x) b), @sigT proofTerm (fun e' => prod (typing Gamma e' b) (NormalFormTerm e')).

  Ltac InstantiateProper := match goal with
          | [pth : Path _ ?G, h : ProperContext ?G |- ProperBelief _] => apply PathToIn in pth; let H := fresh "h" in pose proof (BeliefInProperContextIsProper _ _ h pth) as H; inversion H; subst; repeat constructor; auto
          | [pth : Path _ ?G, h : Forall ProperBelief ?G |- ProperBelief _] => apply PathToIn in pth; let H := fresh "h" in pose proof (BeliefInProperContextIsProper _ _ h pth) as H; inversion H; subst; repeat constructor; auto
          end.

  
  Lemma NFModalityExpandL : forall (x : flafolFormula * proofTerm) {Gamma : Context} {m : Modality} (pth : PathToDoubleInModality m) (b : Belief) (pth0 : Path ((fst x) @ CollapseDoubleInModality pth) Gamma)  (h0 : NormalFormTerm (snd x))  (h1 : typing ((fst x) @ m :: Gamma) (snd x) b), @sigT proofTerm (fun e' => prod (typing Gamma e' b) (NormalFormTerm e')).
  Proof.
    assert (well_founded rel) by (apply WfRel).
    pose proof (@Fix _ rel H PMEL).
    clear H.
    apply H0.
    clear H0.
    unfold PMEL in *.
    intros x IHe1 Gamma m pth b pth0 h0 h1.
    destruct x as [phi e1].
    unfold NormalFormTerm in *.
    simpl in *.
    destruct e1; inversion h1; subst; simpl in h0; try solve [eexists; split; [eapply modalityExpandLr; eauto| simpl; auto]]; repeat destructProd.
    - inversion pth1; subst.
      + edestruct (IHe1 (phi0 & psi, e1)) with (Gamma := (phi0 @ m :: psi @ m :: Gamma)); simpl; auto.
        repeat apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        edestruct (IHe1 (phi0, weak x (phi0 @ m :: psi @ m :: phi0 @ CollapseDoubleInModality pth :: Gamma))) with (Gamma0 := (psi @ m :: phi0 @ CollapseDoubleInModality pth :: Gamma)); simpl; auto.
        solveCutRel.
        apply There; apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H0; auto. }
        solveSubPath.
        destruct p.
        edestruct (IHe1 (psi, weak x0 (psi @ m :: phi0 @ CollapseDoubleInModality pth :: psi @ CollapseDoubleInModality pth :: Gamma))) with (Gamma0 := (phi0 @ CollapseDoubleInModality pth :: psi @ CollapseDoubleInModality pth :: Gamma)); simpl; auto.
        solveCutRel.
        apply There; apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H0; auto. }
        solveSubPath.
        destruct p.
        eexists; split.
        eapply AndLr; eauto.
        simpl; auto.
      + edestruct (IHe1 (phi, e1)) with (Gamma := phi0 @ m0 :: psi @ m0 :: Gamma) ; simpl; auto.
        repeat apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        eexists; split.
        eapply AndLr; eauto.
        simpl; auto.
    - edestruct (IHe1 (phi, e1_1)) with (Gamma := Gamma) ; simpl; eauto.
      solveCutRel.
      edestruct (IHe1 (phi, e1_2)) with (Gamma := Gamma) ; simpl; eauto.
      solveCutRel.
      destruct p.
      destruct p0.
      eexists; split.
      eapply AndRr; eauto.
      simpl; auto.
    - inversion pth1; subst.
      + edestruct (IHe1 (phi0 ⊕ psi, e1_1)) with (Gamma := (phi0 @ m :: Gamma)); simpl; auto.
        solveCutRel.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        edestruct (IHe1 (phi0 ⊕ psi, e1_2)) with (Gamma := (psi @ m :: Gamma)); simpl; auto.
        solveCutRel.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        edestruct (IHe1 (psi, weak x0 (psi @ m :: psi @ CollapseDoubleInModality pth :: Gamma))) with (Gamma0 := (psi @ CollapseDoubleInModality pth :: Gamma)); simpl; auto.
        solveCutRel.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H0; auto. }
        solveSubPath.
        destruct p.
        edestruct (IHe1 (phi0, weak x (phi0 @ m :: phi0 @ CollapseDoubleInModality pth :: Gamma))) with (Gamma0 := (phi0 @ CollapseDoubleInModality pth :: Gamma)); simpl; auto.
        solveCutRel.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H0; auto. }
        solveSubPath.
        destruct p.
        eexists; split.
        eapply OrLr; eauto.
        simpl; auto.
      + edestruct (IHe1 (phi, e1_1)) with (Gamma := phi0 @ m0 :: Gamma); simpl; auto.
        solveCutRel.
        repeat (apply There); eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        edestruct (IHe1 (phi, e1_2)) with (Gamma := psi @ m0 :: Gamma); simpl; auto.
        solveCutRel.
        repeat (apply There); eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        eexists; split.
        eapply OrLr; eauto.
        simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (Gamma := Gamma) ; simpl; eauto.
      destruct p.
      eexists; split.
      eapply OrR1r; eauto.
      simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (Gamma := Gamma) ; simpl; eauto.
      destruct p.
      eexists; split.
      eapply OrR2r; eauto.
      simpl; auto.
    - inversion pth1; subst.
      + edestruct (IHe1 (phi0 ==⟨ l ⟩> psi, e1_2)) with (Gamma := (psi @ m :: Gamma)); simpl; auto.
        solveCutRel.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        edestruct (IHe1 (phi0 ==⟨ l ⟩> psi, e1_1)) with (Gamma := Gamma); simpl; eauto.
        solveCutRel.
        destruct p.
        edestruct (IHe1 (psi, weak x (psi @ m :: psi @ CollapseDoubleInModality pth :: Gamma))) with (Gamma0 := (psi @ CollapseDoubleInModality pth :: Gamma)); simpl; auto.
        solveCutRel.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H0; auto. }
        solveSubPath.
        destruct p.
        eexists; split.
        eapply ImpLr; eauto.
        simpl; auto.
      + edestruct (IHe1 (phi, e1_2)) with (Gamma := (psi @ m0 :: Gamma)); simpl; auto.
        solveCutRel.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        edestruct (IHe1 (phi, e1_1)) with (Gamma := (Gamma)); simpl; eauto.
        solveCutRel.
        destruct p.
        eexists; split.
        eapply ImpLr; eauto.
        simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (Gamma := phi0 @ ⟨ l ⟩ :: Gamma); simpl; auto.
      apply There; eauto.
      eapply Exchange; eauto.
      solveSubPath.
      destruct p.
      eexists; split.
      eapply ImpRr; eauto.
      simpl; auto.
    - inversion pth1; subst.
      + edestruct (IHe1 (∀ sigma; phi0, e1)) with (Gamma := (open_formula phi0 t @ m) :: Gamma); simpl; auto.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        edestruct (IHe1 (open_formula phi0 t, weak x (open_formula phi0 t @ m :: open_formula phi0 t @ CollapseDoubleInModality pth :: Gamma))) with (Gamma0 := (open_formula phi0 t @ CollapseDoubleInModality pth) :: Gamma); simpl; auto.
        solveCutRel.
        rewrite OpenFormulaSize; auto.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H4; auto.
        }
        solveSubPath.
        destruct p.
        eexists; split.
        eapply forallLr; eauto.
        simpl; auto.
      + edestruct (IHe1 (phi, e1)) with (Gamma := (open_formula phi0 t @ m0 :: Gamma)); simpl; auto.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        eexists; split.
        eapply forallLr; eauto.
        simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (Gamma := Gamma); simpl; eauto.
      destruct p.
      eexists; split.
      eapply forallRr with (y := y); eauto.
      intro.
      apply H1.
      econstructor; eauto; fail.
      simpl; auto.
    - inversion pth1; subst.
      + edestruct (IHe1 (∃ VarSort y; phi0, e1)) with (Gamma := (open_formula phi0 (varTerm y) @ m) :: Gamma); simpl; auto.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        edestruct (IHe1 (open_formula phi0 (varTerm y), weak x (open_formula phi0 (varTerm y) @ m :: open_formula phi0 (varTerm y) @ CollapseDoubleInModality pth :: Gamma))) with (Gamma0 := (open_formula phi0 (varTerm y) @ CollapseDoubleInModality pth) :: Gamma); simpl; auto.
        solveCutRel.
        rewrite OpenFormulaSize; auto.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H3; auto. }
        solveSubPath.
        destruct p.
        pose (freshInSequent (open_formula phi0 (varTerm y) @ m :: Gamma) b (VarSort y)) as y'.
        edestruct (open_with_fresherLT'' _ _ _ _ y y'  x0 t0) as [xx [xx1 [nftx ]]]; eauto.
        unfold y'.
        rewrite freshInSequentOfSort; auto.
        eapply NotInFVCConsInversion; eauto.
        eexists; split.
        eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
        unfold y'.
        destruct (freshInSequentIsFresh (open_formula phi0 (varTerm y) @ m :: Gamma) b (VarSort y)) as [fv1 fv2].
        intro; apply fv1; econstructor; eauto; fail.      
        simpl; auto.
      + edestruct (IHe1 (phi, e1)) with (Gamma := (open_formula phi0 (varTerm y) @ m0 :: Gamma)); simpl; auto.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        eexists; split.
        eapply existsLr with (y := y); eauto.
        intro.
        inversion H; subst; apply H1; econstructor; eauto; fail.
        simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (Gamma := Gamma); simpl; eauto.
      destruct p.
      eexists; split.
      eapply existsRr; eauto.
      simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (Gamma := Gamma); simpl; eauto.
      destruct p0.
      eexists; split.
      eapply saysRr; eauto.
      simpl; auto.
    - inversion pth1; subst.
      + edestruct (IHe1 (p □ ⟨ lab ⟩ phi0, e1)) with (Gamma := (phi0 @ m ⋅ p ⟨ lab ⟩ :: Gamma)); simpl; auto.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p0.
        edestruct (IHe1 (phi0, weak x (phi0 @ m ⋅ p ⟨ lab ⟩ :: phi0 @ CollapseDoubleInModality pth ⋅ p ⟨ lab ⟩ :: Gamma))) with (Gamma0 := (phi0 @ CollapseDoubleInModality pth ⋅ p ⟨ lab ⟩ :: Gamma)) (pth0 := (thereDouble _ p lab pth)); simpl; auto.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          all : inversion H0; auto. }
        solveSubPath.
        destruct p0.
        eexists; split.
        eapply saysLr; eauto.
        simpl; auto.
      + edestruct (IHe1 (phi, e1)) with (Gamma := phi0 @ m0 ⋅ p ⟨ lab ⟩ :: Gamma); simpl; auto.
        repeat (apply There); eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p0.
        eexists; split.
        eapply saysLr; eauto.
        simpl; auto.
  Qed.

  
  Definition PMCL := fun (x : flafolFormula * proofTerm) => forall {Gamma : Context} {m : Modality} (pth : PathToDoubleInModality m) (b : Belief) (pth0 : Path ((fst x) @ m) Gamma)  (h0 : NormalFormTerm (snd x))  (h1 : typing ((fst x) @ CollapseDoubleInModality pth :: Gamma) (snd x) b), @sigT proofTerm (fun e' => prod (typing Gamma e' b) (NormalFormTerm e')).

  Lemma NFModalityCollapseL : forall (x : flafolFormula * proofTerm) {Gamma : Context} {m : Modality} (pth : PathToDoubleInModality m) (b : Belief) (pth0 : Path ((fst x) @ m) Gamma)  (h0 : NormalFormTerm (snd x))  (h1 : typing ((fst x) @ CollapseDoubleInModality pth :: Gamma) (snd x) b), @sigT proofTerm (fun e' => prod (typing Gamma e' b) (NormalFormTerm e')).
  Proof.
    assert (well_founded rel) by (apply WfRel).
    pose proof (@Fix _ rel H PMCL).
    clear H.
    apply H0.
    clear H0.
    unfold PMCL in *.
    intros x IHe1 Gamma m pth b pth0 h0 h1.
    destruct x as [phi e1].
    unfold NormalFormTerm in *.
    simpl in *.
    destruct e1; inversion h1; subst; simpl in h0; try solve [eexists; split; [eapply modalityCollapseLr; eauto| simpl; auto]]; repeat destructProd.
    - inversion pth1; subst.
      + edestruct (IHe1 (phi0 & psi, e1)) with (Gamma := (phi0 @ CollapseDoubleInModality pth
                                                               :: psi @ CollapseDoubleInModality pth :: Gamma)); simpl; auto.
        repeat apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        edestruct (IHe1 (phi0, weak x (phi0 @ CollapseDoubleInModality pth :: psi @ CollapseDoubleInModality pth :: phi0 @ m :: Gamma))) with (Gamma0 := (psi @ CollapseDoubleInModality pth :: phi0 @ m :: Gamma)); simpl; auto.
        solveCutRel.
        apply There; apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H0; auto. }
        solveSubPath.
        destruct p.
        edestruct (IHe1 (psi, weak x0 (psi @ CollapseDoubleInModality pth :: phi0 @ m :: psi @ m :: Gamma))) with (Gamma0 := (phi0 @ m :: psi @ m :: Gamma)); simpl; auto.
        solveCutRel.
        apply There; apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H0; auto. }
        solveSubPath.
        destruct p.
        eexists; split.
        eapply AndLr; eauto.
        simpl; auto.
      + edestruct (IHe1 (phi, e1)) with (Gamma := phi0 @ m0 :: psi @ m0 :: Gamma) ; simpl; auto.
        repeat apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        eexists; split.
        eapply AndLr; eauto.
        simpl; auto.
    - edestruct (IHe1 (phi, e1_1)) with (Gamma := Gamma) ; simpl; eauto.
      solveCutRel.
      edestruct (IHe1 (phi, e1_2)) with (Gamma := Gamma) ; simpl; eauto.
      solveCutRel.
      destruct p.
      destruct p0.
      eexists; split.
      eapply AndRr; eauto.
      simpl; auto.
    - inversion pth1; subst.
      + edestruct (IHe1 (phi0 ⊕ psi, e1_1)) with (Gamma := (phi0 @ CollapseDoubleInModality pth :: Gamma)); simpl; auto.
        solveCutRel.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        edestruct (IHe1 (phi0 ⊕ psi, e1_2)) with (Gamma := (psi @ CollapseDoubleInModality pth :: Gamma)); simpl; auto.
        solveCutRel.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        edestruct (IHe1 (psi, weak x0 (psi @ CollapseDoubleInModality pth :: psi @ m :: Gamma))) with (Gamma0 := (psi @ m :: Gamma)); simpl; auto.
        solveCutRel.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H0; auto. }
        solveSubPath.
        destruct p.
        edestruct (IHe1 (phi0, weak x (phi0 @ CollapseDoubleInModality pth :: phi0 @ m :: Gamma))) with (Gamma0 := (phi0 @ m :: Gamma)); simpl; auto.
        solveCutRel.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H0; auto. }
        solveSubPath.
        destruct p.
        eexists; split.
        eapply OrLr; eauto.
        simpl; auto.
      + edestruct (IHe1 (phi, e1_1)) with (Gamma := phi0 @ m0 :: Gamma); simpl; auto.
        solveCutRel.
        repeat (apply There); eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        edestruct (IHe1 (phi, e1_2)) with (Gamma := psi @ m0 :: Gamma); simpl; auto.
        solveCutRel.
        repeat (apply There); eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        eexists; split.
        eapply OrLr; eauto.
        simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (Gamma := Gamma) ; simpl; eauto.
      destruct p.
      eexists; split.
      eapply OrR1r; eauto.
      simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (Gamma := Gamma) ; simpl; eauto.
      destruct p.
      eexists; split.
      eapply OrR2r; eauto.
      simpl; auto.
    - inversion pth1; subst.
      + edestruct (IHe1 (phi0 ==⟨ l ⟩> psi, e1_2)) with (Gamma := (psi @ CollapseDoubleInModality pth :: Gamma)); simpl; auto.
        solveCutRel.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        edestruct (IHe1 (phi0 ==⟨ l ⟩> psi, e1_1)) with (Gamma := Gamma); simpl; eauto.
        solveCutRel.
        destruct p.
        edestruct (IHe1 (psi, weak x (psi @ CollapseDoubleInModality pth :: psi @ m :: Gamma))) with (Gamma0 := (psi @ m :: Gamma)); simpl; auto.
        solveCutRel.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H0; auto. }
        solveSubPath.
        destruct p.
        eexists; split.
        eapply ImpLr; eauto.
        simpl; auto.
      + edestruct (IHe1 (phi, e1_2)) with (Gamma := (psi @ m0 :: Gamma)); simpl; auto.
        solveCutRel.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        edestruct (IHe1 (phi, e1_1)) with (Gamma := (Gamma)); simpl; eauto.
        solveCutRel.
        destruct p.
        eexists; split.
        eapply ImpLr; eauto.
        simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (Gamma := phi0 @ ⟨ l ⟩ :: Gamma); simpl; auto.
      apply There; eauto.
      eapply Exchange; eauto.
      solveSubPath.
      destruct p.
      eexists; split.
      eapply ImpRr; eauto.
      simpl; auto.
    - inversion pth1; subst.
      + edestruct (IHe1 (∀ sigma; phi0, e1)) with (Gamma := (open_formula phi0 t @ CollapseDoubleInModality pth) :: Gamma); simpl; auto.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        edestruct (IHe1 (open_formula phi0 t, weak x (open_formula phi0 t @ CollapseDoubleInModality pth :: open_formula phi0 t @ m :: Gamma))) with (Gamma0 := (open_formula phi0 t @ m) :: Gamma); simpl; auto.
        solveCutRel.
        rewrite OpenFormulaSize; auto.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H4; auto. }
        solveSubPath.
        destruct p.
        eexists; split.
        eapply forallLr; eauto.
        simpl; auto.
      + edestruct (IHe1 (phi, e1)) with (Gamma := (open_formula phi0 t @ m0 :: Gamma)); simpl; auto.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        eexists; split.
        eapply forallLr; eauto.
        simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (Gamma := Gamma); simpl; eauto.
      destruct p.
      eexists; split.
      eapply forallRr with (y := y); eauto.
      intro.
      apply H1.
      econstructor; eauto; fail.
      simpl; auto.
    - inversion pth1; subst.
      + edestruct (IHe1 (∃ VarSort y; phi0, e1)) with (Gamma := (open_formula phi0 (varTerm y) @ CollapseDoubleInModality pth) :: Gamma); simpl; auto.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        edestruct (IHe1 (open_formula phi0 (varTerm y), weak x (open_formula phi0 (varTerm y) @ CollapseDoubleInModality pth :: open_formula phi0 (varTerm y) @ m :: Gamma))) with (Gamma0 := (open_formula phi0 (varTerm y) @ m) :: Gamma); simpl; auto.
        solveCutRel.
        rewrite OpenFormulaSize; auto.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H3; auto. }
        solveSubPath.
        destruct p.
        pose (freshInSequent (open_formula phi0 (varTerm y) @ m :: Gamma) b (VarSort y)) as y'.
        edestruct (open_with_fresherLT'' _ _ _ _ y y'  x0 t0) as [xx [xx1 [nftx ]]]; eauto.
        unfold y'.
        rewrite freshInSequentOfSort; auto.
        eapply NotInFVCConsInversion; eauto.
        eexists; split.
        eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
        unfold y'.
        destruct (freshInSequentIsFresh (open_formula phi0 (varTerm y) @ m :: Gamma) b (VarSort y)) as [fv1 fv2].
        intro; apply fv1; econstructor; eauto; fail.      
        simpl; auto.
      + edestruct (IHe1 (phi, e1)) with (Gamma := (open_formula phi0 (varTerm y) @ m0 :: Gamma)); simpl; auto.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p.
        eexists; split.
        eapply existsLr with (y := y); eauto.
        intro.
        inversion H; subst; apply H1; econstructor; eauto; fail.
        simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (Gamma := Gamma); simpl; eauto.
      destruct p.
      eexists; split.
      eapply existsRr; eauto.
      simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (Gamma := Gamma); simpl; eauto.
      destruct p0.
      eexists; split.
      eapply saysRr; eauto.
      simpl; auto.
    - inversion pth1; subst.
      + edestruct (IHe1 (p □ ⟨ lab ⟩ phi0, e1)) with (Gamma := (phi0 @ CollapseDoubleInModality pth ⋅ p ⟨ lab ⟩ :: Gamma)); simpl; auto.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p0.
        edestruct (IHe1 (phi0, weak x (phi0 @ CollapseDoubleInModality pth ⋅ p ⟨ lab ⟩ :: phi0 @ m ⋅ p ⟨ lab ⟩ :: Gamma))) with (Gamma0 := (phi0 @ m ⋅ p ⟨ lab ⟩ :: Gamma)) (pth0 := (thereDouble _ p lab pth)); simpl; auto.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          all : inversion H0; auto. }
        solveSubPath.
        destruct p0.
        eexists; split.
        eapply saysLr; eauto.
        simpl; auto.
      + edestruct (IHe1 (phi, e1)) with (Gamma := phi0 @ m0 ⋅ p ⟨ lab ⟩ :: Gamma); simpl; auto.
        repeat (apply There); eauto.
        eapply Exchange; eauto.
        solveSubPath.
        destruct p0.
        eexists; split.
        eapply saysLr; eauto.
        simpl; auto.
  Qed.
  
  Definition PNFFTT1 := fun e1 =>  forall (h0 : NormalFormTerm' e1 true) (e2 : proofTerm) (Gamma : Context) (lab1 lab2 lab3 : flafolTerm) (m : Modality) (h1 : typing Gamma e1 (lab1 ⊑ lab2 @ m)) (h2 : typing Gamma e2 (lab2 ⊑ lab3 @ m)) (h3 : NormalFormTerm' e2 false), sigT (fun e : proofTerm => prod (typing Gamma e (lab1 ⊑ lab3 @ m)) (NormalFormTerm' e true)).

  
  Lemma NFFlowsToTransR1 : forall (e1 : proofTerm) (h0 : NormalFormTerm' e1 true) (e2 : proofTerm) (Gamma : Context) (lab1 lab2 lab3 : flafolTerm) (m : Modality) (h1 : typing Gamma e1 (lab1 ⊑ lab2 @ m)) (h2 : typing Gamma e2 (lab2 ⊑ lab3 @ m)) (h3 : NormalFormTerm' e2 false), sigT (fun e : proofTerm => prod (typing Gamma e (lab1 ⊑ lab3 @ m)) (NormalFormTerm' e true)).
  Proof.
    apply (@Fix _ (fun x1 x2 => term_size x1 < term_size x2) (well_founded_ltof _ _) PNFFTT1).
    unfold PNFFTT1 in *.
    intros e1 IHe1.
    destruct e1; simpl; intros; inversion h1; subst; repeat destructProd; try solve [eexists; split; [eapply flowsToTransRr; eauto| simpl; tauto]]; try solve [simplNFProofs].
    all : try try match goal with
                  | [h1 : NormalFormTerm' ?e1 ?b1, H1 : typing _ ?e1 _, h2 : NormalFormTerm' ?e2 ?b2, H2 : typing _ ?e2 _ |- _]  => edestruct (IHe1 e1 ltac:(simpl; solveCutRel) h1) with (1 := H1) as [x1 []]; try solve [eapply WeakeningTyping; eauto; try solve [solveProper | solveSubPath]; fail | solveNFT]; edestruct (IHe1 e2 ltac:(simpl; solveCutRel) h2) with (1 := H2) as [x2 []]; try solve [eapply WeakeningTyping; eauto; try solve [solveProper | solveSubPath]; fail | solveNFT]; eexists; split; [econstructor; eauto; fail | simpl; tauto]; fail
                  | [h : NormalFormTerm' ?e ?b, h1 : typing _ ?e _ |- _]  => edestruct (IHe1 e ltac:(simpl; solveCutRel) h) with (1 := h1) as [x []]; try solve [eapply WeakeningTyping; eauto; try solve [solveProper | solveSubPath]; fail | solveNFT]; eexists; split; [econstructor; eauto; fail | simpl; tauto]; fail
                  end.    
    - pose (freshInSequent (open_formula phi (varTerm y) @ m :: (lab1 ⊑ lab3 @ m) :: Gamma) (lab1 ⊑ lab2 @ m) (VarSort y)) as y'.
      destruct (open_with_fresherLT'' _ _ _ _ y y' e1 H4 _ h0) as [t' [T [nft eq]]]; auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      edestruct (IHe1 t') with (3 := T) (lab3 := lab3) as [x []]; auto.
      simpl; rewrite eq; auto.
      solveTyping.
      solveNFT.
      eexists; split.
      eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
      unfold y'.
      all : destruct (freshInSequentIsFresh (open_formula phi (varTerm y) @ m :: (lab1 ⊑ lab3 @ m):: Gamma) (lab1 ⊑ lab2 @ m) (VarSort y)) as [fv1 fv2].
      eapply FreshWithMore. 2: eauto.
      intros.
      simpl; auto.
      intro.
      apply fv1.
      apply Exists_cons_tl.
      apply Exists_cons_hd; auto.
      simpl; auto.
    - eexists; split.
      eapply flowsToTransRr.
      apply h1.
      eauto.
      simpl; auto.
    - exists (flowsToTransRTerm (flowsToTransRTerm e1_1 e1_2) e2).
      split; simpl; auto.
      econstructor; eauto.      
  Qed.
    
  
  Definition PNFFTT := fun e2 =>  forall (h3 : NormalFormTerm' e2 true) (e1 : proofTerm) (h0 : NormalFormTerm' e1 true) (Gamma : Context) (lab1 lab2 lab3 : flafolTerm) (m : Modality) (h2 : typing Gamma e2 (lab2 ⊑ lab3 @ m)) (h1 : typing Gamma e1 (lab1 ⊑ lab2 @ m)), sigT (fun e : proofTerm => prod (typing Gamma e (lab1 ⊑ lab3 @ m)) (NormalFormTerm' e true)).

  
  Lemma NFFlowsToTransR : forall (e2 : proofTerm) (h3 : NormalFormTerm' e2 true) (e1 : proofTerm) (h0 : NormalFormTerm' e1 true) (Gamma : Context) (lab1 lab2 lab3 : flafolTerm) (m : Modality) (h2 : typing Gamma e2 (lab2 ⊑ lab3 @ m)) (h1 : typing Gamma e1 (lab1 ⊑ lab2 @ m)), sigT (fun e : proofTerm => prod (typing Gamma e (lab1 ⊑ lab3 @ m)) (NormalFormTerm' e true)).
  Proof.
    apply (@Fix _ (fun x1 x2 => term_size x1 < term_size x2) (well_founded_ltof _ _) PNFFTT).
    unfold PNFFTT in *.
    intros e2 IHe1.
    destruct e2; simpl; intros; inversion h2; subst; repeat destructProd; try solve [eexists; split; [eapply flowsToTransRr; eauto| simpl; tauto]]; try solve [simplNFProofs].
    all : try solve [eapply NFFlowsToTransR1; eauto; simpl; auto].
    all : try lazymatch goal with
              | [h : NormalFormTerm' ?e ?b, h1 : typing _ ?e _ |- _]  => edestruct (IHe1 e ltac:(simpl; solveCutRel) h) with (2 := h1) as [x []]; try solve [eapply WeakeningTyping; eauto; try solve [solveProper | solveSubPath]; fail]; try solve [solveNFT]; eexists; split; [econstructor; eauto; fail | simpl; tauto]; fail
              end.
    - edestruct (IHe1 e2_1 ltac:(simpl; solveCutRel) n) with (2 := H2) (lab1 := lab1) as [x []].
      2 : solveTyping.
      solveNFT.
      edestruct (IHe1 e2_2 ltac:(simpl; solveCutRel) n0) with (2 := H4) (lab1 := lab1) as [x' []].
      2 : solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - pose (freshInSequent (open_formula phi (varTerm y) @ m :: (lab1 ⊑ lab3 @ m) :: Gamma) (lab2 ⊑ lab3 @ m) (VarSort y)) as y'.
      destruct (open_with_fresherLT'' _ _ _ _ y y' e2 H4 _ h3) as [t' [T [nft eq]]]; auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      edestruct (IHe1 t') with (4 := T) (lab1 := lab1) as [x []]; auto.
      simpl; rewrite eq; auto.
      2 : solveTyping.
      solveNFT.
      eexists; split.
      eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
      all : destruct (freshInSequentIsFresh (open_formula phi (varTerm y) @ m :: (lab1 ⊑ lab3 @ m):: Gamma) (lab2 ⊑ lab3 @ m) (VarSort y)) as [fv1 fv2].
      eapply FreshWithMore. 2: eauto.
      intros.
      simpl; auto.
      intro.
      apply fv1.
      apply Exists_cons_tl.
      apply Exists_cons_hd; auto.
      simpl; auto.
  Qed.


  Definition PCRV1 := fun e1 => forall (h0 : NormalFormTerm' e1 true) (e2 : proofTerm) (Gamma : Context) (p lab1 lab2 : flafolTerm) (m : Modality) (h1 : typing Gamma e1 (canRead p lab2 @ m)) (h2 : typing Gamma e2 (lab1 ⊑ lab2 @ m)) (h3 : NormalFormTerm' e2 false), sigT (fun e => prod (typing Gamma e (canRead p lab1 @ m)) (NormalFormTerm' e true)).

  
  Lemma NFCRVariance1 : forall (e1 : proofTerm) (h0 : NormalFormTerm' e1 true) (e2 : proofTerm) (Gamma : Context) (p lab1 lab2 : flafolTerm) (m : Modality) (h1 : typing Gamma e1 (canRead p lab2 @ m)) (h2 : typing Gamma e2 (lab1 ⊑ lab2 @ m)) (h3 : NormalFormTerm' e2 false), sigT (fun e => prod (typing Gamma e (canRead p lab1 @ m)) (NormalFormTerm' e true)).
  Proof.
    apply (@Fix _ (fun x1 x2 => term_size x1 < term_size x2) (well_founded_ltof _ _) PCRV1).
    unfold PCRV1 in *.
    intros e1 IHe1.
    destruct e1; simpl; intros; inversion h1; subst; repeat destructProd; try solve [eexists; split; [eapply CRVariancer; eauto| simpl; tauto]]; try solve [simplNFProofs].
    all : try lazymatch goal with
              | [h : NormalFormTerm' ?e ?b, h1 : typing _ ?e _ |- _]  => edestruct (IHe1 e ltac:(simpl; solveCutRel) h) with (1 := h1) as [x []]; try solve [eapply WeakeningTyping; eauto; try solve [solveProper | solveSubPath]; fail]; try solve [solveNFT]; eexists; split; [econstructor; eauto; fail | simpl; tauto]; fail
              end.
    - edestruct (IHe1 e1_1 ltac:(simpl; solveCutRel) n) with (1 := H2)  (lab1 := lab1) as [x []].
      solveTyping.
      solveNFT.
      edestruct (IHe1 e1_2 ltac:(simpl; solveCutRel) n0) with (1 := H4)  (lab1 := lab1) as [x' []].
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - pose (freshInSequent (open_formula phi (varTerm y) @ m :: (canRead p lab1 @ m) :: Gamma) (canRead p lab2 @ m) (VarSort y)) as y'.
      destruct (open_with_fresherLT'' _ _ _ _ y y' e1 H4 _ h0) as [t' [T [nft eq]]]; auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      edestruct (IHe1 t') with (3 := T) (lab1 := lab1) as [x []]; auto.
      simpl; rewrite eq; auto.
      solveTyping.
      solveNFT.
      eexists; split.
      eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
      unfold y'.
      all : destruct (freshInSequentIsFresh (open_formula phi (varTerm y) @ m :: (canRead p lab1 @ m) :: Gamma) (canRead p lab2 @ m) (VarSort y)) as [fv1 fv2].
      eapply FreshWithMore. 2: eauto.
      intros.
      simpl; auto.
      intro.
      apply fv1.
      apply Exists_cons_tl.
      apply Exists_cons_hd; auto.
      simpl; auto.
    - eexists; split.
      eapply CRVariancer; eauto.
      eapply flowsToTransRr; eauto.
      simpl; auto.  
  Qed.
  
  Definition PCRV := fun e2 => forall (h3 : NormalFormTerm' e2 true) (e1 : proofTerm) (Gamma : Context) (p lab1 lab2 : flafolTerm) (m : Modality) (h2 : typing Gamma e2 (lab1 ⊑ lab2 @ m)) (h1 : typing Gamma e1 (canRead p lab2 @ m)) (h0 : NormalFormTerm' e1 true), sigT (fun e => prod (typing Gamma e (canRead p lab1 @ m)) (NormalFormTerm' e true)).

  Lemma NFCRVariance : forall e2 (h3 : NormalFormTerm' e2 true) (e1 : proofTerm) (Gamma : Context) (p lab1 lab2 : flafolTerm) (m : Modality) (h2 : typing Gamma e2 (lab1 ⊑ lab2 @ m)) (h1 : typing Gamma e1 (canRead p lab2 @ m)) (h0 : NormalFormTerm' e1 true) , sigT (fun e => prod (typing Gamma e (canRead p lab1 @ m)) (NormalFormTerm' e true)).
  Proof.
    apply (@Fix _ (fun x1 x2 => term_size x1 < term_size x2) (well_founded_ltof _ _) PCRV).
    unfold PCRV in *.
    intros e2 IHe2.
    destruct e2; simpl; intros; inversion h2; subst; repeat destructProd; try solve [eexists; split; [eapply CRVariance; eauto| simpl; tauto]]; try solve [simplNFProofs].
    all : try solve [eapply NFCRVariance1; eauto; simpl; auto].
    all : try lazymatch goal with
              | [h : NormalFormTerm' ?e ?b, h1 : typing _ ?e _ |- _]  => edestruct (IHe2 e ltac:(simpl; solveCutRel) h) with (1 := h1) as [x []]; try solve [eapply WeakeningTyping; eauto; try solve [solveProper | solveSubPath]; fail]; try solve [solveNFT]; eexists; split; [econstructor; eauto; fail | simpl; tauto]; fail
              end.
    - edestruct (IHe2 e2_1 ltac:(simpl; solveCutRel) n) with (1 := H2) (p := p) (lab2 := lab2) as [x []].
      solveTyping.
      solveNFT.
      edestruct (IHe2 e2_2 ltac:(simpl; solveCutRel) n0) with (1 := H4) (p := p) as [x' []].
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - pose (freshInSequent (open_formula phi (varTerm y) @ m :: (canRead p lab1 @ m) :: Gamma) (canRead p lab2 @ m) (VarSort y)) as y'.
      destruct (open_with_fresherLT'' _ _ _ _ y y' e2 H4 _ h3) as [t' [T [nft eq]]]; auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      edestruct (IHe2 t') with (3 := T) (p := p) (lab1 := lab1) as [x []]; auto.
      simpl; rewrite eq; auto.
      solveTyping.
      solveNFT.
      eexists; split.
      eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
      unfold y'.
      all : destruct (freshInSequentIsFresh (open_formula phi (varTerm y) @ m :: (canRead p lab1 @ m) :: Gamma) (canRead p lab2 @ m) (VarSort y)) as [fv1 fv2].
      eapply FreshWithMore. 2: eauto.
      intros.
      simpl; auto.
      intro.
      apply fv1.
      apply Exists_cons_tl.
      apply Exists_cons_hd; auto.
      simpl; auto.
  Qed.  

  Definition PCWV1 := fun e1 => forall (h0 : NormalFormTerm' e1 true) (e2 : proofTerm) (Gamma : Context) (p lab1 lab2 : flafolTerm) (m : Modality) (h1 : typing Gamma e1 (canWrite p lab1 @ m)) (h2 : typing Gamma e2 (lab1 ⊑ lab2 @ m)) (h3 : NormalFormTerm' e2 false), sigT (fun e => prod (typing Gamma e (canWrite p lab2 @ m)) (NormalFormTerm' e true)).

  
  Lemma NFCWVariance1 : forall (e1 : proofTerm) (h0 : NormalFormTerm' e1 true) (e2 : proofTerm) (Gamma : Context) (p lab1 lab2 : flafolTerm) (m : Modality) (h1 : typing Gamma e1 (canWrite p lab1 @ m)) (h2 : typing Gamma e2 (lab1 ⊑ lab2 @ m)) (h3 : NormalFormTerm' e2 false), sigT (fun e => prod (typing Gamma e (canWrite p lab2 @ m)) (NormalFormTerm' e true)).
  Proof.
    apply (@Fix _ (fun x1 x2 => term_size x1 < term_size x2) (well_founded_ltof _ _) PCWV1).
    unfold PCWV1 in *.
    intros e1 IHe1.
    destruct e1; simpl; intros; inversion h1; subst; repeat destructProd; try solve [eexists; split; [eapply CWVariancer; eauto| simpl; tauto]]; try solve [simplNFProofs].
    all : try lazymatch goal with
              | [h : NormalFormTerm' ?e ?b, h1 : typing _ ?e _ |- _]  => edestruct (IHe1 e ltac:(simpl; solveCutRel) h) with (1 := h1) as [x []]; try solve [eapply WeakeningTyping; eauto; try solve [solveProper | solveSubPath]; fail]; try solve [solveNFT]; eexists; split; [econstructor; eauto; fail | simpl; tauto]; fail
              end.
    - edestruct (IHe1 e1_1 ltac:(simpl; solveCutRel) n) with (1 := H2)  (lab2 := lab2) as [x []].
      solveTyping.
      solveNFT.
      edestruct (IHe1 e1_2 ltac:(simpl; solveCutRel) n0) with (1 := H4)  (lab2 := lab2) as [x' []].
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - pose (freshInSequent (open_formula phi (varTerm y) @ m :: (canWrite p lab2 @ m) :: Gamma) (canWrite p lab1 @ m) (VarSort y)) as y'.
      destruct (open_with_fresherLT'' _ _ _ _ y y' e1 H4 _ h0) as [t' [T [nft eq]]]; auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      edestruct (IHe1 t') with (3 := T) (lab2 := lab2) as [x []]; auto.
      simpl; rewrite eq; auto.
      solveTyping.
      solveNFT.
      eexists; split.
      eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
      unfold y'.
      all : destruct (freshInSequentIsFresh (open_formula phi (varTerm y) @ m :: (canWrite p lab2 @ m) :: Gamma) (canWrite p lab1 @ m) (VarSort y)) as [fv1 fv2].
      eapply FreshWithMore. 2: eauto.
      intros.
      simpl; auto.
      intro.
      apply fv1.
      apply Exists_cons_tl.
      apply Exists_cons_hd; auto.
      simpl; auto.
    - eexists; split.
      eapply CWVariancer; eauto.
      eapply flowsToTransRr; eauto.
      simpl; auto.  
  Qed.

  Definition PCWV := fun e2 => forall (h3 : NormalFormTerm' e2 true) (e1 : proofTerm) (Gamma : Context) (p lab1 lab2 : flafolTerm) (m : Modality) (h2 : typing Gamma e2 (lab1 ⊑ lab2 @ m)) (h1 : typing Gamma e1 (canWrite p lab1 @ m)) (h0 : NormalFormTerm' e1 true), sigT (fun e => prod (typing Gamma e (canWrite p lab2 @ m)) (NormalFormTerm' e true)).

  Lemma NFCWVariance : forall e2 (h3 : NormalFormTerm' e2 true) (e1 : proofTerm) (Gamma : Context) (p lab1 lab2 : flafolTerm) (m : Modality) (h2 : typing Gamma e2 (lab1 ⊑ lab2 @ m)) (h1 : typing Gamma e1 (canWrite p lab1 @ m)) (h0 : NormalFormTerm' e1 true), sigT (fun e => prod (typing Gamma e (canWrite p lab2 @ m)) (NormalFormTerm' e true)).
  Proof.
    apply (@Fix _ (fun x1 x2 => term_size x1 < term_size x2) (well_founded_ltof _ _) PCWV).
    unfold PCWV in *.
    intros e2 IHe2.
    destruct e2; simpl; intros; inversion h2; subst; repeat destructProd.
    all : try solve [eapply NFCWVariance1; eauto; simpl; auto].
    all : try lazymatch goal with
              | [h : NormalFormTerm' ?e ?b, h1 : typing _ ?e _ |- _]  => edestruct (IHe2 e ltac:(simpl; solveCutRel) h) with (1 := h1) as [x []]; try solve [eapply WeakeningTyping; eauto; try solve [solveProper | solveSubPath]; fail]; try solve [solveNFT]; eexists; split; [econstructor; eauto; fail | simpl; tauto]; fail
              end.
    - edestruct (IHe2 e2_1 ltac:(simpl; solveCutRel) n) with (1 := H2) (p := p) (lab2 := lab2) as [x []].
      solveTyping.
      solveNFT.
      edestruct (IHe2 e2_2 ltac:(simpl; solveCutRel) n0) with (1 := H4) (p := p) as [x' []].
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - pose (freshInSequent (open_formula phi (varTerm y) @ m :: (canWrite p lab2 @ m) :: Gamma) (canWrite p lab1 @ m) (VarSort y)) as y'.
      destruct (open_with_fresherLT'' _ _ _ _ y y' e2 H4 _ h3) as [t' [T [nft eq]]]; auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      edestruct (IHe2 t') with (3 := T) (p := p) (lab1 := lab1) as [x []]; auto.
      simpl; rewrite eq; auto.
      solveTyping.
      solveNFT.
      eexists; split.
      eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
      unfold y'.
      all : destruct (freshInSequentIsFresh (open_formula phi (varTerm y) @ m :: (canWrite p lab2 @ m) :: Gamma) (canWrite p lab1 @ m) (VarSort y)) as [fv1 fv2].
      eapply FreshWithMore. 2: eauto.
      intros.
      simpl; auto.
      intro.
      apply fv1.
      apply Exists_cons_tl.
      apply Exists_cons_hd; auto.
      simpl; auto.
  Qed.  

  Definition PNFRV1 := fun e1 => forall {Gamma : Context} {lab1 lab2 : flafolTerm} {phi : flafolFormula} {m : Modality} (pi : PathToLabelInModality m lab1) (h0 : NormalFormTerm e1)  (h1 : typing Gamma e1 (phi @ m)) (e2 : proofTerm) (h2: typing Gamma e2 (lab1 ⊑ lab2 @ VarModality pi lab2)) (h3 : NormalFormTerm' e2 false),  @sigT proofTerm (fun e' => prod (typing Gamma e' (phi @ ReplaceLabelInModality m lab1 lab2 pi)) (NormalFormTerm e')).
  
  Lemma NFRVariance1 : forall (e1 : proofTerm) {Gamma : Context} {lab1 lab2 : flafolTerm} {phi : flafolFormula} {m : Modality} (pi : PathToLabelInModality m lab1) (h0 : NormalFormTerm e1)  (h1 : typing Gamma e1 (phi @ m)) (e2 : proofTerm) (h2: typing Gamma e2 (lab1 ⊑ lab2 @ VarModality pi lab2)) (h3 : NormalFormTerm' e2 false),  @sigT proofTerm (fun e' => prod (typing Gamma e' (phi @ ReplaceLabelInModality m lab1 lab2 pi)) (NormalFormTerm e')).
  Proof.
    apply (@Fix _ (fun x1 x2 => term_size x1 < term_size x2) (well_founded_ltof _ _) PNFRV1).
    unfold PNFRV1 in *.
    intros e1 IHe1.
    unfold NormalFormTerm in *.
    destruct e1; simpl; intros; inversion h1; subst; try solve [eexists; split; [eapply RVariancer; eauto| simpl; auto]].
    - edestruct (IHe1 e1) with (lab1 := lab1) (lab2 := lab2) (pi := pi) as [x []].
      auto.
      auto.
      eauto.
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - destruct h0.
      edestruct (IHe1 e1_1); eauto; try solve [simpl; solveCutRel].
      edestruct (IHe1 e1_2); eauto; try solve [simpl; solveCutRel].
      destruct p, p0.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - destruct h0.
      edestruct (IHe1 e1_1) with (lab1 := lab1) (lab2 := lab2) (pi := pi).
      simpl; solveCutRel.
      auto.
      eauto.
      solveTyping.
      solveNFT.
      edestruct (IHe1 e1_2) with (lab1 := lab1) (lab2 := lab2) (pi := pi).
      simpl; solveCutRel.
      auto.
      eauto.
      solveTyping.
      solveNFT.
      destruct p, p0.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - edestruct (IHe1 e1); eauto.
      destruct p.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - edestruct (IHe1 e1); eauto.
      destruct p.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - destruct h0.
      edestruct (IHe1 e1_2) with (lab1 := lab1) (lab2 := lab2) (pi := pi).
      simpl; solveCutRel.
      auto.
      eauto.
      solveTyping.
      solveNFT.
      destruct p.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - edestruct (IHe1 e1) with (lab1 := lab1) (lab2 := lab2) (pi := pi).
      simpl; solveCutRel.
      auto.
      eauto.
      solveTyping.
      solveNFT.
      destruct p.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - edestruct IHe1 with (lab1 := lab1) (lab2 := lab2) (pi := pi).
      simpl; solveCutRel.
      auto.
      eauto.
      solveTyping.
      solveNFT.
      destruct p.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - pose (freshInSequent ((phi0 @ ReplaceLabelInModality m lab1 lab2 pi) :: Gamma) (phi0 @ m) (VarSort y)) as y'.
      destruct (open_with_fresherRTS' _ _ _ y y' e1 H7 _ h0) as [t' [T [nft eq]]]; auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      edestruct (IHe1 t') with (3 := T) (lab1 := lab1) (lab2 := lab2) (pi := pi) as [x []]; auto.
      simpl; rewrite eq; auto.
      solveTyping.
      solveNFT.
      eexists; split.
      eapply forallRr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
      all : destruct (freshInSequentIsFresh ((phi0 @ ReplaceLabelInModality m lab1 lab2 pi) :: Gamma) (phi0 @ m) (VarSort y)) as [fv1 fv2].
      eapply FreshWithMore. 2: eauto.
      intros.
      simpl; auto.
      intro.
      apply fv2.
      econstructor; eauto; fail.
      intro.
      apply fv1.
      apply Exists_cons_hd.
      econstructor; eauto; fail.
      simpl; auto.
    - pose (freshInSequent (open_formula phi0 (varTerm y) @ m :: (phi @ ReplaceLabelInModality m lab1 lab2 pi) :: Gamma) (phi @ m) (VarSort y)) as y'.
      destruct (open_with_fresherLT'' _ _ _ _ y y' e1 H4 _ h0) as [t' [T [nft eq]]]; auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      edestruct (IHe1 t') with (3 := T) (lab1 := lab1) (lab2 := lab2) (pi := pi) as [x []]; auto.
      simpl; rewrite eq; auto.
      solveTyping.
      solveNFT.
      eexists; split.
      eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
      all : destruct (freshInSequentIsFresh (open_formula phi0 (varTerm y) @ m :: (phi @ ReplaceLabelInModality m lab1 lab2 pi) :: Gamma) (phi @ m) (VarSort y)) as [fv1 fv2].
      eapply FreshWithMore. 2: eauto.
      intros.
      simpl; auto.
      intro.
      apply fv1.
      apply Exists_cons_tl.
      apply Exists_cons_hd; auto.
      simpl; auto.
    - edestruct (IHe1 e1); eauto.
      destruct p.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - edestruct IHe1 with (lab1 := lab1) (lab2 := lab2) (pi := thereLab m p _ lab pi); eauto.
      simpl; solveCutRel.
      destruct pi; simpl in *; auto.
      destruct p0.
      eexists; split.
      eapply saysRr; simpl in *; eauto.
      simpl; auto. 
    - edestruct (IHe1 e1) with (lab1 := lab1) (lab2 := lab2) (pi := pi).
      simpl; solveCutRel.
      auto.
      eauto.
      solveTyping.
      solveNFT.
      destruct p0.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
  Qed.

  Definition PNFRV := fun e2 => forall (h3 : NormalFormTerm' e2 true) {Gamma : Context} {lab1 lab2 : flafolTerm} {phi : flafolFormula} {m : Modality} (pi : PathToLabelInModality m lab1) (h2: typing Gamma e2 (lab1 ⊑ lab2 @ VarModality pi lab2)) (e1 : proofTerm) (h1 : typing Gamma e1 (phi @ m)) (h0 : NormalFormTerm' e1 true), @sigT proofTerm (fun e' => prod (typing Gamma e' (phi @ ReplaceLabelInModality m lab1 lab2 pi)) (NormalFormTerm e')).
  
  Lemma NFRVariance : forall (e2 : proofTerm) (h3 : NormalFormTerm' e2 true) {Gamma : Context} {lab1 lab2 : flafolTerm} {phi : flafolFormula} {m : Modality} (pi : PathToLabelInModality m lab1) (h2: typing Gamma e2 (lab1 ⊑ lab2 @ VarModality pi lab2)) (e1 : proofTerm) (h1 : typing Gamma e1 (phi @ m)) (h0 : NormalFormTerm' e1 true), @sigT proofTerm (fun e' => prod (typing Gamma e' (phi @ ReplaceLabelInModality m lab1 lab2 pi)) (NormalFormTerm e')).
  Proof.
    apply (@Fix _ (fun x1 x2 => term_size x1 < term_size x2) (well_founded_ltof _ _) PNFRV).
    unfold PNFRV in *.
    intros e2 IHe2.
    unfold NormalFormTerm in *.
    destruct e2; simpl; intros; inversion h2; subst; try solve [eexists; split; [eapply RVariancer; eauto| simpl; auto]]; repeat destructProd.
    all : try solve [eapply NFRVariance1; eauto; simpl; auto].
    all : try lazymatch goal with
              | [h : NormalFormTerm' ?e ?b, h1 : typing _ ?e _ |- _]  => edestruct (IHe2 e ltac:(simpl; solveCutRel) h) with (1 := h1) (lab1 := lab1) (pi := pi) (lab2 := lab2) (phi := phi) as [x []]; try solve [solveTyping]; try solve [solveNFT]; eexists; split; [econstructor; eauto; fail | simpl; tauto]; fail 
              end.
    - edestruct (IHe2 e2_1) with (lab1 := lab1) (lab2 := lab2) (pi := pi) (phi := phi).
      simpl; solveCutRel.
      auto.
      eauto.
      solveTyping.
      solveNFT. 
      edestruct (IHe2 e2_2) with (lab1 := lab1) (lab2 := lab2) (pi := pi) (phi := phi).
      simpl; solveCutRel.
      auto.
      eauto.
      solveTyping.
      solveNFT.
      destruct p, p0.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - pose (freshInSequent (open_formula phi0 (varTerm y) @ m :: (phi @ ReplaceLabelInModality m lab1 lab2 pi) :: Gamma) (phi @ m) (VarSort y)) as y'.
      destruct (open_with_fresherLT'' _ _ _ _ y y' e2 H4 _ h3) as [t' [T [nft eq]]]; auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      edestruct (IHe2 t') with (3 := T) (lab1 := lab1) (lab2 := lab2) (pi := pi) (phi := phi) as [x []]; auto.
      simpl; rewrite eq; auto.
      solveTyping.
      solveNFT.
      eexists; split.
      eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
      all : destruct (freshInSequentIsFresh (open_formula phi0 (varTerm y) @ m :: (phi @ ReplaceLabelInModality m lab1 lab2 pi) :: Gamma) (phi @ m) (VarSort y)) as [fv1 fv2].
      eapply FreshWithMore. 2: eauto.
      intros.
      simpl; auto.
      intro.
      apply fv1.
      apply Exists_cons_tl.
      apply Exists_cons_hd; auto.
      simpl; auto.
  Qed.

  Lemma SplitPath {A : Set} {a : A} (l1 l2 : list A) (pth : Path a (l1 ++ l2)) : (Path a l1) + (Path a l2).
  Proof.
    induction l1; simpl in *; auto.
    inversion pth; subst; auto.
    left; constructor.
    destruct (IHl1 H1); auto.
    left; econstructor; eauto; fail.    
  Qed.    

  Lemma PathToEq: forall {m m' C phi}, Path (phi @ m) (map (fun f : flafolFormula => f @ m') C) -> m = m'.
  Proof.
    intros m m' C phi H.
    induction C; simpl in *; inversion H; subst; auto.
  Qed.  

  Definition PLV1 := fun (x : flafolFormula * proofTerm) => forall {Gamma : Context} {lab1 lab2 : flafolTerm} {m : Modality} (pi : PathToLabelInModality m lab1) (b : Belief) (pth : Path ((fst x) @ m) Gamma)  (h0 : NormalFormTerm (snd x))  (h1 : typing ((fst x) @ ReplaceLabelInModality m lab1 lab2 pi :: Gamma) (snd x) b) (e2 : proofTerm) (h2: typing Gamma e2 (lab1 ⊑ lab2 @ VarModality pi lab2)) (h3 : NormalFormTerm' e2 false), @sigT proofTerm (fun e' => prod (typing Gamma e' b) (NormalFormTerm e')).

  Lemma NFLVariance1 : forall (x : flafolFormula * proofTerm) {Gamma : Context} {lab1 lab2 : flafolTerm} {m : Modality} (pi : PathToLabelInModality m lab1) (b : Belief) (pth : Path ((fst x) @ m) Gamma)  (h0 : NormalFormTerm (snd x))  (h1 : typing ((fst x) @ ReplaceLabelInModality m lab1 lab2 pi :: Gamma) (snd x) b) (e2 : proofTerm) (h2: typing Gamma e2 (lab1 ⊑ lab2 @ VarModality pi lab2)) (h3 : NormalFormTerm' e2 false), @sigT proofTerm (fun e' => prod (typing Gamma e' b) (NormalFormTerm e')).
  Proof.
    assert (well_founded rel) by (apply WfRel).
    pose proof (@Fix _ rel H PLV1).
    clear H.
    apply H0.
    clear H0.
    unfold PLV1 in *.
    intros x IHe1 Gamma lab1 lab2 m pi b pth h0 h1 e2 h2 h3.
    destruct x as [phi e1].
    unfold NormalFormTerm in *.
    simpl in *.
    destruct e1; inversion h1; subst; simpl in h0; try solve [eexists; split; [eapply LVariancer; eauto| simpl; auto]]; repeat destructProd.
    - inversion pth0; subst.
      + edestruct (IHe1 (phi0 & psi, e1)) with (Gamma := (phi0 @ ReplaceLabelInModality m lab1 lab2 pi
                                                               :: psi @ ReplaceLabelInModality m lab1 lab2 pi :: Gamma)); simpl; auto.
        repeat apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p.
        edestruct (IHe1 (phi0, weak x (phi0 @ ReplaceLabelInModality m lab1 lab2 pi :: psi @ ReplaceLabelInModality m lab1 lab2 pi :: phi0 @ m :: Gamma))) with (Gamma0 := (psi @ ReplaceLabelInModality m lab1 lab2 pi :: phi0 @ m :: Gamma)) (lab3 := lab1) (lab4 := lab2) (pi0 := pi); simpl; auto.
        solveCutRel.
        apply There; apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H0; auto. }
        solveSubPath.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H0; auto. }
        solveSubPath.
        solveNFT.
        destruct p.
        edestruct (IHe1 (psi, weak x0 (psi @ ReplaceLabelInModality m lab1 lab2 pi :: phi0 @ m :: psi @ m :: Gamma))) with (Gamma0 := (phi0 @ m :: psi @ m :: Gamma)) (lab3 := lab1) (lab4 := lab2) (pi0 := pi); simpl; auto.
        solveCutRel.
        apply There; apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H0; auto. }
        solveSubPath.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H0; auto. }
        solveSubPath.
        solveNFT.
        destruct p.
        eexists; split.
        eapply AndLr; eauto.
        simpl; auto.
      + edestruct (IHe1 (phi, e1)) with (lab1 := lab1) (lab2 := lab2) (pi := pi) (Gamma := phi0 @ m0 :: psi @ m0 :: Gamma) ; simpl; auto.
        repeat (apply There); eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p.
        eexists; split.
        eapply AndLr; eauto.
        simpl; auto.
    - edestruct (IHe1 (phi, e1_1)) with (lab1 := lab1) (lab2 := lab2) (pi := pi) (Gamma := Gamma) ; simpl; eauto.
      solveCutRel.
      edestruct (IHe1 (phi, e1_2)) with (lab1 := lab1) (lab2 := lab2) (pi := pi) (Gamma := Gamma) ; simpl; eauto.
      solveCutRel.
      destruct p.
      destruct p0.
      eexists; split.
      eapply AndRr; eauto.
      simpl; auto.
    - inversion pth0; subst.
      + edestruct (IHe1 (phi0 ⊕ psi, e1_1)) with (Gamma := (phi0 @ ReplaceLabelInModality m lab1 lab2 pi :: Gamma)); simpl; auto.
        solveCutRel.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p.
        edestruct (IHe1 (phi0 ⊕ psi, e1_2)) with (Gamma := (psi @ ReplaceLabelInModality m lab1 lab2 pi :: Gamma)); simpl; auto.
        solveCutRel.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p.
        edestruct (IHe1 (psi, weak x0 (psi @ ReplaceLabelInModality m lab1 lab2 pi :: psi @ m :: Gamma))) with (Gamma0 := (psi @ m :: Gamma)) (lab3 := lab1) (lab4 := lab2) (pi0 := pi); simpl; auto.
        solveCutRel.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H0; auto. }
        solveSubPath.
        eapply WeakeningTyping; eauto.
        { apply provenProperContextTyping in h2.
          constructor; auto.
          InstantiateProper.
          inversion H0; auto. }
        solveSubPath.
        solveNFT.
        destruct p.
        edestruct (IHe1 (phi0, weak x (phi0 @ ReplaceLabelInModality m lab1 lab2 pi :: phi0 @ m :: Gamma))) with (Gamma0 := (phi0 @ m :: Gamma)) (lab3 := lab1) (lab4 := lab2) (pi0 := pi); simpl; auto.
        solveCutRel.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { apply provenProperContextTyping in h2.
          constructor; auto.
          InstantiateProper.
          apply provenProperContextTyping in t0.
          inversion t0; subst.
          inversion H5; auto.
          inversion H0; auto.
          constructor; auto.
          InstantiateProper.
          inversion H0; auto. }        
        solveSubPath.
        eapply WeakeningTyping; eauto.
        { apply provenProperContextTyping in h2.
          constructor; auto.
          InstantiateProper.
          apply provenProperContextTyping in t0.
          inversion t0; subst.
          inversion H5; auto.
          inversion H0; auto. }
        solveSubPath.
        solveNFT.
        destruct p.
        eexists; split.
        eapply OrLr; eauto.
        simpl; auto.
      + edestruct (IHe1 (phi, e1_1)) with (lab1 := lab1) (lab2 := lab2) (pi := pi) (Gamma := phi0 @ m0 :: Gamma); simpl; auto.
        solveCutRel.
        repeat (apply There); eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p.
        edestruct (IHe1 (phi, e1_2)) with (lab1 := lab1) (lab2 := lab2) (pi := pi) (Gamma := psi @ m0 :: Gamma); simpl; auto.
        solveCutRel.
        repeat (apply There); eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p.
        eexists; split.
        eapply OrLr; eauto.
        simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (lab1 := lab1) (lab2 := lab2) (pi := pi) (Gamma := Gamma) ; simpl; eauto.
      destruct p.
      eexists; split.
      eapply OrR1r; eauto.
      simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (lab1 := lab1) (lab2 := lab2) (pi := pi) (Gamma := Gamma) ; simpl; eauto.
      destruct p.
      eexists; split.
      eapply OrR2r; eauto.
      simpl; auto.
    - inversion pth0; subst.
      + edestruct (IHe1 (phi0 ==⟨ l ⟩> psi, e1_2)) with (Gamma := (psi @ ReplaceLabelInModality m lab1 lab2 pi :: Gamma)); simpl; auto.
        solveCutRel.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p.
        edestruct (IHe1 (phi0 ==⟨ l ⟩> psi, e1_1)) with (Gamma := Gamma); simpl; eauto.
        solveCutRel.
        destruct p.
        edestruct (IHe1 (psi, weak x (psi @ ReplaceLabelInModality m lab1 lab2 pi :: psi @ m :: Gamma))) with (Gamma0 := (psi @ m :: Gamma)); simpl; auto.
        solveCutRel.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H0; auto. }
        solveSubPath.
        eapply WeakeningTyping; eauto.
        { apply provenProperContextTyping in h2.
          constructor; auto.
          InstantiateProper.
          inversion H0; auto. }
        solveSubPath.
        solveNFT.
        destruct p.
        eexists; split.
        eapply ImpLr; eauto.
        simpl; auto.
      + edestruct (IHe1 (phi, e1_2)) with (Gamma := (psi @ m0 :: Gamma)); simpl; auto.
        solveCutRel.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p.
        edestruct (IHe1 (phi, e1_1)) with (Gamma := (Gamma)); simpl; eauto.
        solveCutRel.
        destruct p.
        eexists; split.
        eapply ImpLr; eauto.
        simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (Gamma := phi0 @ ⟨ l ⟩ :: Gamma); simpl; auto.
      apply There; eauto.
      eapply Exchange; eauto.
      solveSubPath.
      eapply WeakeningTyping; eauto.
      repeat solveProper.
      solveSubPath.
      solveNFT.
      destruct p.
      eexists; split.
      eapply ImpRr; eauto.
      simpl; auto.
    - inversion pth0; subst.
      + edestruct (IHe1 (∀ sigma; phi0, e1)) with (Gamma := (open_formula phi0 t @ ReplaceLabelInModality m lab1 lab2 pi) :: Gamma); simpl; auto.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p.
        edestruct (IHe1 (open_formula phi0 t, weak x (open_formula phi0 t @ ReplaceLabelInModality m lab1 lab2 pi :: open_formula phi0 t @ m :: Gamma))) with (Gamma0 := (open_formula phi0 t @ m) :: Gamma); simpl; auto.
        solveCutRel.
        rewrite OpenFormulaSize; auto.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H4; auto. }
        solveSubPath.
        eapply WeakeningTyping; eauto.
        { apply provenProperContextTyping in h2.
          constructor; auto.
          InstantiateProper.
          apply provenProperContextTyping in H3.
          inversion H3.
          inversion H6; auto. }
        solveSubPath.
        solveNFT.
        destruct p.
        eexists; split.
        eapply forallLr; eauto.
        simpl; auto.
      + edestruct (IHe1 (phi, e1)) with (Gamma := (open_formula phi0 t @ m0 :: Gamma)); simpl; auto.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p.
        eexists; split.
        eapply forallLr; eauto.
        simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (Gamma := Gamma); simpl; eauto.
      destruct p.
      eexists; split.
      eapply forallRr with (y := y); eauto.
      intro.
      apply H1.
      econstructor; eauto; fail.
      simpl; auto.
    - inversion pth0; subst.
      + edestruct (IHe1 (∃ VarSort y; phi0, e1)) with (Gamma := (open_formula phi0 (varTerm y) @ ReplaceLabelInModality m lab1 lab2 pi) :: Gamma); simpl; auto.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p.
        edestruct (IHe1 (open_formula phi0 (varTerm y), weak x (open_formula phi0 (varTerm y) @ ReplaceLabelInModality m lab1 lab2 pi :: open_formula phi0 (varTerm y) @ m :: Gamma))) with (Gamma0 := (open_formula phi0 (varTerm y) @ m) :: Gamma); simpl; auto.
        solveCutRel.
        rewrite OpenFormulaSize; auto.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          all : inversion H3; auto. }
        solveSubPath.
        eapply WeakeningTyping; eauto; try solve [repeat solveProper | solveSubPath].
        { apply provenProperContextTyping in h2.
          constructor; auto.
          all : InstantiateProper.
          apply provenProperContextTyping in H4.
          all : inversion H4; auto.
          inversion H6; auto. }
        solveNFT.
        destruct p.
        eexists; split.
        eapply existsLr with (y := y); eauto.
        intro.
        inversion H; subst.
        * apply H1.
          apply Exists_cons_tl.
          apply Exists_cons_hd; auto.          
        * apply H1; econstructor; eauto; fail.          
        * simpl; auto.
      + edestruct (IHe1 (phi, e1)) with (Gamma := (open_formula phi0 (varTerm y) @ m0 :: Gamma)); simpl; auto.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p.
        eexists; split.
        eapply existsLr with (y := y); eauto.
        intro.
        inversion H; subst; apply H1; econstructor; eauto; fail.
        simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (Gamma := Gamma); simpl; eauto.
      destruct p.
      eexists; split.
      eapply existsRr; eauto.
      simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (Gamma := Gamma); simpl; eauto.
      destruct p0.
      eexists; split.
      eapply saysRr; eauto.
      simpl; auto.
    - inversion pth0; subst.
      + edestruct (IHe1 (p □ ⟨ lab ⟩ phi0, e1)) with (Gamma := (phi0 @ ReplaceLabelInModality m lab1 lab2 pi ⋅ p ⟨ lab ⟩ :: Gamma)); simpl; auto.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p0.
        edestruct (IHe1 (phi0, weak x (phi0 @ ReplaceLabelInModality m lab1 lab2 pi ⋅ p ⟨ lab ⟩ :: phi0 @ m ⋅ p ⟨ lab ⟩ :: Gamma))) with (Gamma0 := (phi0 @ m ⋅ p ⟨ lab ⟩ :: Gamma)) (lab3 := lab1) (lab4 := lab2) (pi0 := thereLab m p lab1 lab pi); simpl; auto.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto; try solve [repeat solveProper | solveSubPath].
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          all : inversion H0; auto. }
        { destruct pi; simpl in *.
          eapply WeakeningTyping; eauto; try solve [repeat solveProper | solveSubPath].
          { apply provenProperContextTyping in h2.
            constructor; auto.
            InstantiateProper.
            all : inversion H0; auto.
            inversion H; auto. }
          eapply WeakeningTyping; eauto; try solve [repeat solveProper | solveSubPath].
          { apply provenProperContextTyping in h2.
            constructor; auto.
            InstantiateProper.
            all : inversion H0; auto.
            all : inversion H; auto. }
          eapply WeakeningTyping; eauto; try solve [repeat solveProper | solveSubPath].
          { apply provenProperContextTyping in h2.
            constructor; auto.
            InstantiateProper.
            all : inversion H0; auto.
            all : inversion H; auto. }          
        }
        solveNFT.
        destruct p0.
        eexists; split.
        eapply saysLr; eauto.
        simpl; auto.
      + edestruct (IHe1 (phi, e1)) with (lab1 := lab1) (lab2 := lab2) (pi := pi) (Gamma := phi0 @ m0 ⋅ p ⟨ lab ⟩ :: Gamma); simpl; auto.
        repeat (apply There); eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p0.
        eexists; split.
        eapply saysLr; eauto.
        simpl; auto.
  Qed.

  Lemma NFLVariance' : forall (e1 : proofTerm) (phi : flafolFormula) {Gamma : Context} {lab1 lab2 : flafolTerm} {m : Modality} (pi : PathToLabelInModality m lab1) (b : Belief) (pth : Path (phi @ m) Gamma)  (h0 : NormalFormTerm e1)  (h1 : typing (phi @ ReplaceLabelInModality m lab1 lab2 pi :: Gamma) e1 b) (e2 : proofTerm) (h2: typing Gamma e2 (lab1 ⊑ lab2 @ VarModality pi lab2)) (h3 : NormalFormTerm' e2 false), @sigT proofTerm (fun e' => prod (typing Gamma e' b) (NormalFormTerm e')).
  Proof.
    intros.
    eapply NFLVariance1 with (x := (phi, e1)); eauto.
  Qed.
  
  Definition PLV := fun (e2 : proofTerm) => forall (h3 : NormalFormTerm' e2 true) {Gamma : Context} {lab1 lab2 : flafolTerm} {m : Modality} {phi : flafolFormula} (pi : PathToLabelInModality m lab1) (b : Belief) (pth : Path (phi @ m) Gamma) (h2: typing Gamma e2 (lab1 ⊑ lab2 @ VarModality pi lab2)) (e1 : proofTerm) (h0 : NormalFormTerm e1)  (h1 : typing (phi @ ReplaceLabelInModality m lab1 lab2 pi :: Gamma) e1 b), @sigT proofTerm (fun e' => prod (typing Gamma e' b) (NormalFormTerm e')).

  Lemma NFLVariance : forall (e2 : proofTerm) (h3 : NormalFormTerm' e2 true) {Gamma : Context} {lab1 lab2 : flafolTerm} {m : Modality} {phi : flafolFormula} (pi : PathToLabelInModality m lab1) (b : Belief) (pth : Path (phi @ m) Gamma) (h2: typing Gamma e2 (lab1 ⊑ lab2 @ VarModality pi lab2)) (e1 : proofTerm) (h0 : NormalFormTerm e1)  (h1 : typing (phi @ ReplaceLabelInModality m lab1 lab2 pi :: Gamma) e1 b), @sigT proofTerm (fun e' => prod (typing Gamma e' b) (NormalFormTerm e')).
  Proof.
    apply (@Fix _ (fun x1 x2 => term_size x1 < term_size x2) (well_founded_ltof _ _) PLV).
    unfold PLV in *.
    intros e2 IHe2.
    unfold NormalFormTerm in *.
    destruct e2; simpl; intros; inversion h2; subst; try solve [eexists; split; [eapply LVariancer; eauto| simpl; auto]]; repeat destructProd.
    all : try solve [eapply NFLVariance' with (e1 := e1) (phi := phi); eauto; simpl; auto].
    all : try lazymatch goal with
          | [h : NormalFormTerm' ?e true, h1 : typing _ ?e _ |- _]  => edestruct (IHe2 e ltac:(simpl; solveCutRel) h) with (b := b) (2 := h1) (lab1 := lab1) (pi := pi) (lab2 := lab2) (phi := phi) as [x []]; try solve [solveTyping]; try solve [solveNFT | repeat apply There; auto]; eexists; split; [econstructor; eauto; fail | simpl; tauto]; fail
          end.
    - edestruct (IHe2 e2_1 ltac:(simpl; solveCutRel) n) with (b := b) (2 :=H2) (lab1 := lab1) (pi := pi) (lab2 := lab2) (phi := phi) as [x []]; try solve [solveTyping]; try solve [solveNFT | repeat apply There; auto].
      edestruct (IHe2 e2_2 ltac:(simpl; solveCutRel) n0) with (b := b) (2 :=H4) (lab1 := lab1) (pi := pi) (lab2 := lab2) (phi := phi) as [x' []]; try solve [clear t; solveTyping]; try solve [solveNFT | repeat apply There; auto].
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - pose (freshInSequent (open_formula phi0 (varTerm y) @ m :: (phi @ ReplaceLabelInModality m lab1 lab2 pi) :: Gamma) b (VarSort y)) as y'.
      destruct (open_with_fresherLT'' _ _ _ _ y y' e2 H4 _ h3) as [t' [T [nft eq]]]; auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      edestruct (IHe2 t') with (4 := T) (lab1 := lab1) (lab2 := lab2) (pi := pi) (phi := phi) (b := b) as [x []]; auto.
      simpl; rewrite eq; auto.
      apply There; auto.
      2 : solveTyping.
      solveNFT.
      eexists; split.
      eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
      all : destruct (freshInSequentIsFresh (open_formula phi0 (varTerm y) @ m :: (phi @ ReplaceLabelInModality m lab1 lab2 pi) :: Gamma) b (VarSort y)) as [fv1 fv2].
      eapply FreshWithMore. 2: eauto.
      intros.
      simpl; auto.
      simpl; auto.
  Qed.        
    
  Ltac destruct_NFProd := repeat match goal with
                                 | [h : _ * NormalFormTerm' _ _ |- _ ] => destruct h
                                 end.

  Ltac solIH := try solve [solveTyping| solveNFT | solveProper | repeat apply There; eauto].

  Definition PFwdR1 := fun e1 => forall {Gamma : Context} {phi : flafolFormula} {m : Modality} {p q : flafolTerm} (pth : PathToPrinInModality m p) (h0 : NormalFormTerm e1)  (h1 : typing Gamma e1 (phi @ m)) (e2 : proofTerm) (h2 : typing Gamma e2 ((canRead q (LabelAtPrin pth)) @ (FwdModality pth p))) (h3 : NormalFormTerm' e2 false) (e3 : proofTerm) (h4 : typing Gamma e3 ((canWrite p (LabelAtPrin pth)) @ (FwdModality pth q))) (h5 : NormalFormTerm' e3 false), @sigT proofTerm (fun e' => prod (typing Gamma e' (phi @ ReplacePrinInModality pth q)) (NormalFormTerm e')).

  
  Lemma NFFwdR1 : forall (e1 : proofTerm) {Gamma : Context} {phi : flafolFormula} {m : Modality} {p q : flafolTerm} (pth : PathToPrinInModality m p) (h0 : NormalFormTerm e1)  (h1 : typing Gamma e1 (phi @ m)) (e2 : proofTerm) (h2 : typing Gamma e2 ((canRead q (LabelAtPrin pth)) @ (FwdModality pth p))) (h3 : NormalFormTerm' e2 false) (e3 : proofTerm) (h4 : typing Gamma e3 ((canWrite p (LabelAtPrin pth)) @ (FwdModality pth q))) (h5 : NormalFormTerm' e3 false), @sigT proofTerm (fun e' => prod (typing Gamma e' (phi @ ReplacePrinInModality pth q)) (NormalFormTerm e')).
 Proof.
   unfold NormalFormTerm.
   apply (@Fix _ (fun x1 x2 => term_size x1 < term_size x2) (well_founded_ltof _ _) PFwdR1).
   unfold PFwdR1 in *.
   intros e1 IHe1.
   unfold NormalFormTerm in *.
   destruct e1; simpl; intros; inversion h1; subst; repeat destructProd; try solve [eexists; split; [eapply FwdRr; eauto| simpl; repeat split; auto]].
    - edestruct (IHe1 e1) with (p := p) (q := q) (pth := pth); auto.
      eauto.
      1, 3 : eapply WeakeningTyping; eauto.
      all: try solve [solveSubPath | repeat solveProper | solveNFT].
      destruct p0.
      eexists; split.
      eapply AndLr; eauto.
      simpl; auto.
    - edestruct (IHe1 e1_1); eauto.
      simpl; solveCutRel.
      edestruct (IHe1 e1_2); eauto.
      simpl; solveCutRel.
      destruct p0, p1.
      eexists; split.
      apply AndRr; eauto.
      simpl; auto.
    - edestruct (IHe1 e1_1) with (p := p) (q := q) (pth := pth); auto.
      simpl; solveCutRel.
      eauto.
      1, 3 : eapply WeakeningTyping; eauto.
      all: try solve [solveSubPath | repeat solveProper | solveNFT].
      edestruct (IHe1 e1_2) with (p := p) (q := q) (pth := pth); auto.
      simpl; solveCutRel.
      eauto.
      1, 3 : eapply WeakeningTyping; eauto.
      all: try solve [solveSubPath | repeat solveProper | solveNFT].
      destruct p1, p0.
      eexists; split.
      eapply OrLr; eauto.
      simpl; auto.
    - edestruct IHe1; eauto.
      simpl; solveCutRel.
      destruct p0.
      eexists; split.
      apply OrR1r; eauto.
      simpl; auto.
    - edestruct IHe1; eauto.
      simpl; solveCutRel.
      destruct p0.
      eexists; split.
      apply OrR2r; eauto.
      simpl; auto.
    - edestruct (IHe1 e1_2) with (p := p) (q := q) (pth := pth); auto.
      simpl; solveCutRel.
      eauto.
      1, 3 : eapply WeakeningTyping; eauto.
      all: try solve [solveSubPath | repeat solveProper | solveNFT].
      destruct p0.
      eexists; split.
      eapply ImpLr; eauto.
      simpl; auto.
    - edestruct (IHe1 e1) with (p := p) (q := q) (pth := pth); auto.
      simpl; solveCutRel.
      eauto.
      1, 3 : eapply WeakeningTyping; eauto.
      all: try solve [solveSubPath | repeat solveProper | solveNFT].
      destruct p0.
      eexists; split.
      eapply ImpRr; eauto.
      simpl; auto.
    - edestruct (IHe1 e1) with (p := p) (q := q) (pth := pth); auto.
      eauto.
      1, 3 : eapply WeakeningTyping; eauto.
      all: try solve [solveSubPath].
      all: try solve [solveSubPath | repeat solveProper | solveNFT].
      destruct p0.
      eexists; split.
      eapply forallLr; eauto.
      simpl; auto.
    - pose (freshInSequent ((phi0 @  ReplacePrinInModality pth q) :: Gamma) (phi0 @ m) (VarSort y)) as y'.
      destruct (open_with_fresherRTS' _ _ _ y y' e1 H7 _ h0) as [t' [T [nft eq]]]; auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      edestruct (IHe1 t') with (3 := T) (p := p) (q := q) (pth := pth) as [x []]; auto.
      simpl; rewrite eq; auto.
      eauto.
      auto.
      eauto.
      auto.
      eexists; split.
      eapply forallRr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
      all : destruct (freshInSequentIsFresh ((phi0 @  ReplacePrinInModality pth q) :: Gamma) (phi0 @ m) (VarSort y)) as [fv1 fv2].
      eapply FreshWithMore. 2: eauto.
      intros.
      simpl; auto.
      intro.
      apply fv2.
      econstructor; eauto; fail.
      intro.
      apply fv1.
      apply Exists_cons_hd.
      econstructor; eauto; fail.
      simpl; auto.
    - pose (freshInSequent (open_formula phi0 (varTerm y) @ m :: (phi @ ReplacePrinInModality pth q) :: Gamma) (phi @ m) (VarSort y)) as y'.
      destruct (open_with_fresherLT'' _ _ _ _ y y' e1 H4 _ h0) as [t' [T [nft eq]]]; auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      edestruct (IHe1 t') with (3 := T) (p := p) (q := q) (pth := pth) as [x []]; auto.
      simpl; rewrite eq; auto.
      solveTyping.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split.
      eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
      all : destruct (freshInSequentIsFresh (open_formula phi0 (varTerm y) @ m :: (phi @ ReplacePrinInModality pth q) :: Gamma) (phi @ m) (VarSort y)) as [fv1 fv2].
      eapply FreshWithMore. 2: eauto.
      intros.
      simpl; auto.
      intro.
      apply fv1.
      apply Exists_cons_tl.
      apply Exists_cons_hd; auto.
      simpl; auto.
    - edestruct (IHe1 e1) with (p := p) (q := q) (pth := pth); eauto; destruct p0; eexists; split.
      eapply existsRr; eauto.
      simpl; auto.
    - edestruct (IHe1 e1) with (p := p) (q := q) (pth := thereP m _ p0 lab pth); eauto.
      destruct p1.
      eexists; split.
      eapply saysRr; simpl in *; eauto.
      simpl; auto. 
    - edestruct (IHe1 e1) with (p := p) (q := q) (pth := pth). auto.
      auto.
      eauto.
      1, 3 : eapply WeakeningTyping; eauto.
      all: try solve [solveSubPath | repeat solveProper | solveNFT].
      destruct p1.
      eexists; split.
      eapply saysLr; eauto.
      simpl; auto.
 Qed.

  Definition PFwdR2 := fun e2 => forall {Gamma : Context} {phi : flafolFormula} {m : Modality} {p q : flafolTerm} (pth : PathToPrinInModality m p) (h2 : typing Gamma e2 ((canRead q (LabelAtPrin pth)) @ (FwdModality pth p))) (h3 : NormalFormTerm' e2 true) (e1 : proofTerm) (h1 : typing Gamma e1 (phi @ m)) (h0 : NormalFormTerm e1)  (e3 : proofTerm) (h4 : typing Gamma e3 ((canWrite p (LabelAtPrin pth)) @ (FwdModality pth q))) (h5 : NormalFormTerm' e3 false), @sigT proofTerm (fun e' => prod (typing Gamma e' (phi @ ReplacePrinInModality pth q)) (NormalFormTerm e')).

 
  Lemma NFFwdR2 : forall (e2 : proofTerm) {Gamma : Context} {phi : flafolFormula} {m : Modality} {p q : flafolTerm} (pth : PathToPrinInModality m p) (h2 : typing Gamma e2 ((canRead q (LabelAtPrin pth)) @ (FwdModality pth p))) (h3 : NormalFormTerm' e2 true) (e1 : proofTerm) (h1 : typing Gamma e1 (phi @ m)) (h0 : NormalFormTerm e1)  (e3 : proofTerm) (h4 : typing Gamma e3 ((canWrite p (LabelAtPrin pth)) @ (FwdModality pth q))) (h5 : NormalFormTerm' e3 false), @sigT proofTerm (fun e' => prod (typing Gamma e' (phi @ ReplacePrinInModality pth q)) (NormalFormTerm e')).
 Proof.
   apply (@Fix _ (fun x1 x2 => term_size x1 < term_size x2) (well_founded_ltof _ _) PFwdR2).
   unfold PFwdR2 in *.
   unfold NormalFormTerm in *.
   intros e2 IHe2.
   destruct e2; intros; inversion h2; subst; try solve [eexists; split; [eapply FwdRr; eauto| simpl; auto]]; repeat destructProd; unfold NormalFormTerm.
   all : try solve [eapply NFFwdR1 with (e1 := e1) (e3 := e3); eauto].
    - edestruct IHe2 with (2 := H1) (phi := phi) as [x []]; auto.
      solveTyping.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - simpl in h3; repeat destructProd.
      edestruct (IHe2 e2_1) with (2 := H2) (phi := phi) as [x []]; auto.
      simpl; solveCutRel.
      solveTyping.
      solveNFT.
      solveTyping.
      solveNFT.
      edestruct (IHe2 e2_2) with (2 := H4) (phi := phi) as [x' []]; auto.
      simpl; solveCutRel.
      eapply WeakeningTyping.
      apply h1.
      repeat solveProper.
      solveSubPath.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - simpl in h3; repeat destructProd.
      edestruct (IHe2 e2_2) with (2 := H4) (phi := phi) as [x' []]; auto.
      simpl; solveCutRel.
      solveTyping.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - simpl in h3; repeat destructProd.
      edestruct IHe2 with (2 := H3) (phi := phi) as [x' []]; auto.
      repeat apply There; eauto.
      solveTyping.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - simpl in h3.
      pose (freshInSequent (open_formula phi0 (varTerm y) @ m :: (phi @ ReplacePrinInModality pth q) :: Gamma) (phi @ m) (VarSort y)) as y'.
      destruct (open_with_fresherLT'' _ _ _ _ y y' e2 H4 _ h3) as [t' [T [nft eq]]]; auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      edestruct (IHe2 t') with (2 := T) (p := p) (q := q) (pth := pth) (phi := phi) as [x []]; auto.
      simpl; rewrite eq; auto.
      solveTyping.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split.
      eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
      all : destruct (freshInSequentIsFresh (open_formula phi0 (varTerm y) @ m :: (phi @ ReplacePrinInModality pth q) :: Gamma) (phi @ m) (VarSort y)) as [fv1 fv2].
      eapply FreshWithMore. 2: eauto.
      intros.
      simpl; auto.
      intro.
      apply fv1.
      apply Exists_cons_tl.
      apply Exists_cons_hd; auto.
      simpl; auto.
    - simpl in h3; repeat destructProd.
      edestruct IHe2 with (2 := H1) (phi := phi) as [x' []]; auto.
      solveTyping.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
 Qed.

 Definition PFwdR := fun e3 => forall (e1 : proofTerm) (e2 : proofTerm) {Gamma : Context} {phi : flafolFormula} {m : Modality} {p q : flafolTerm} (pth : PathToPrinInModality m p) (h1 : typing Gamma e1 (phi @ m))  (h0 : NormalFormTerm' e1 true) (h2 : typing Gamma e2 ((canRead q (LabelAtPrin pth)) @ (FwdModality pth p))) (h4 : typing Gamma e3 ((canWrite p (LabelAtPrin pth)) @ (FwdModality pth q))) (h3 : NormalFormTerm' e2 true) (h5 : NormalFormTerm' e3 true) , @sigT proofTerm (fun e' => prod (typing Gamma e' (phi @ ReplacePrinInModality pth q)) (NormalFormTerm' e' true)).
 
  Lemma NFFwdR : forall (e3 : proofTerm) (e1 : proofTerm) (e2 : proofTerm) {Gamma : Context} {phi : flafolFormula} {m : Modality} {p q : flafolTerm} (pth : PathToPrinInModality m p) (h1 : typing Gamma e1 (phi @ m))  (h0 : NormalFormTerm' e1 true) (h2 : typing Gamma e2 ((canRead q (LabelAtPrin pth)) @ (FwdModality pth p))) (h4 : typing Gamma e3 ((canWrite p (LabelAtPrin pth)) @ (FwdModality pth q))) (h3 : NormalFormTerm' e2 true) (h5 : NormalFormTerm' e3 true) , @sigT proofTerm (fun e' => prod (typing Gamma e' (phi @ ReplacePrinInModality pth q)) (NormalFormTerm' e' true)).
  Proof.
   apply (@Fix _ (fun x1 x2 => term_size x1 < term_size x2) (well_founded_ltof _ _) PFwdR).
   unfold PFwdR in *.
   unfold NormalFormTerm in *.
   intros e3 IHe3.
   destruct e3; intros; inversion h4; subst; try solve [eexists; split; [eapply FwdRr; eauto| simpl; auto]]; repeat destructProd; unfold NormalFormTerm.
   all : try solve [eapply NFFwdR2 with (e1 := e1) (e2 := e2); eauto].
    - edestruct IHe3 with (5 := H1) (phi := phi) as [x []]; auto.
      solveTyping.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - simpl in h5; repeat destructProd.
      edestruct (IHe3 e3_1) with (5 := H2) (phi := phi) as [x []]; auto.
      simpl; solveCutRel.
      solveTyping.
      solveNFT.
      solveTyping.
      solveNFT.
      edestruct (IHe3 e3_2) with (5 := H4) (phi := phi) as [x' []]; auto.
      simpl; solveCutRel.
      eapply WeakeningTyping.
      apply h1.
      repeat solveProper.
      solveSubPath.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - simpl in h5; repeat destructProd.
      edestruct (IHe3 e3_2) with (5 := H4) (phi := phi) as [x' []]; auto.
      simpl; solveCutRel.
      solveTyping.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - simpl in h5; repeat destructProd.
      edestruct IHe3 with (5 := H3) (phi := phi) as [x' []]; auto.
      solveTyping.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - simpl in h5.
      pose (freshInSequent (open_formula phi0 (varTerm y) @ m :: (phi @ ReplacePrinInModality pth q) :: Gamma) (phi @ m) (VarSort y)) as y'.
      destruct (open_with_fresherLT'' _ _ _ _ y y' e3 H4 _ h5) as [t' [T [nft eq]]]; auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      edestruct (IHe3 t') with (5 := T) (p := p) (q := q) (pth := pth) (phi := phi) as [x []]; auto.
      simpl; rewrite eq; auto.
      solveTyping.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split.
      eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
      all : destruct (freshInSequentIsFresh (open_formula phi0 (varTerm y) @ m :: (phi @ ReplacePrinInModality pth q) :: Gamma) (phi @ m) (VarSort y)) as [fv1 fv2].
      eapply FreshWithMore. 2: eauto.
      intros.
      simpl; auto.
      intro.
      apply fv1.
      apply Exists_cons_tl.
      apply Exists_cons_hd; auto.
      simpl; auto.
    - simpl in h5; repeat destructProd.
      edestruct IHe3 with (5 := H1) (phi := phi) as [x' []]; auto.
      solveTyping.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
  Qed.
      
  Definition PFWDL := fun (x : flafolFormula * proofTerm) => forall {Gamma : Context} {p q : flafolTerm} {m : Modality} (pi : PathToPrinInModality m q) (b : Belief) (pth : Path ((fst x) @ m) Gamma) (h0 : NormalFormTerm (snd x)) (h1 : typing ((fst x) @ ReplacePrinInModality pi p :: Gamma) (snd x) b) (e2 : proofTerm) (h2 : typing Gamma e2 (canWrite q (LabelAtPrin pi) @ FwdModality pi p)) (h3 : NormalFormTerm' e2 false) (e3 : proofTerm) (h4 : typing Gamma e3 (canRead p (LabelAtPrin pi) @ FwdModality pi q)) (h5 : NormalFormTerm' e3 false), @sigT proofTerm (fun e' => prod (typing Gamma e' b) (NormalFormTerm e')).
  
  Lemma NFFwdL1 : forall (x : flafolFormula * proofTerm) {Gamma : Context} {p q : flafolTerm} {m : Modality} (pi : PathToPrinInModality m q) (b : Belief) (pth : Path ((fst x) @ m) Gamma) (h0 : NormalFormTerm (snd x)) (h1 : typing ((fst x) @ ReplacePrinInModality pi p :: Gamma) (snd x) b) (e2 : proofTerm) (h2 : typing Gamma e2 (canWrite q (LabelAtPrin pi) @ FwdModality pi p)) (h3 : NormalFormTerm' e2 false) (e3 : proofTerm) (h4 : typing Gamma e3 (canRead p (LabelAtPrin pi) @ FwdModality pi q)) (h5 : NormalFormTerm' e3 false), @sigT proofTerm (fun e' => prod (typing Gamma e' b) (NormalFormTerm e')).
  Proof.
    assert (well_founded rel) by (apply WfRel).
    pose proof (@Fix _ rel H PFWDL).
    clear H.
    apply H0.
    clear H0.
    unfold PFWDL in *.
    intros x IHe1 Gamma p q m pi b pth h0 h1 e2 h2 h3 e3 h4 h5.
    destruct x as [phi e1].
    unfold NormalFormTerm in *.
    simpl in *.
    destruct e1; inversion h1; subst; simpl in h0; try solve [eexists; split; [eapply FwdLr; eauto| simpl; auto]]; repeat destructProd.
    - inversion pth0; subst.
      + edestruct (IHe1 (phi0 & psi, e1)) with (Gamma := (phi0 @ ReplacePrinInModality pi p
                                                               :: psi @ ReplacePrinInModality pi p :: Gamma)); simpl; auto.
        repeat apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        solveTyping.
        solveNFT.
        destruct p0.
        edestruct (IHe1 (phi0, weak x (phi0 @ ReplacePrinInModality pi p :: psi @ReplacePrinInModality pi p :: phi0 @ m :: Gamma))) with (Gamma0 := (psi @ReplacePrinInModality pi p :: phi0 @ m :: Gamma)) (pi0 := pi); simpl; auto.
        solveCutRel.
        apply There; apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          all : inversion H0; auto. }
        solveSubPath.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          all : inversion H0; auto. }
        solveSubPath.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          all : inversion H0; auto. }
        solveSubPath.
        solveNFT.
        destruct p0.
        edestruct (IHe1 (psi, weak x0 (psi @ ReplacePrinInModality pi p :: phi0 @ m :: psi @ m :: Gamma))) with (Gamma0 := (phi0 @ m :: psi @ m :: Gamma)) (pi0 := pi); simpl; auto.
        solveCutRel.
        apply There; apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          all : inversion H0; auto. }
        solveSubPath.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          all : inversion H0; auto. }
        solveSubPath.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          all : inversion H0; auto. }
        solveSubPath.
        solveNFT.
        destruct p0.
        eexists; split.
        eapply AndLr; eauto.
        simpl; auto.
      + edestruct (IHe1 (phi, e1)) with (pi := pi) (Gamma := phi0 @ m0 :: psi @ m0 :: Gamma) ; simpl; auto.
        repeat (apply There); eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p0.
        eexists; split.
        eapply AndLr; eauto.
        simpl; auto.
    - edestruct (IHe1 (phi, e1_1)) with (pi := pi) (Gamma := Gamma) ; simpl; eauto.
      solveCutRel.
      edestruct (IHe1 (phi, e1_2)) with (pi := pi) (Gamma := Gamma) ; simpl; eauto.
      solveCutRel.
      destruct p0.
      destruct p1.
      eexists; split.
      eapply AndRr; eauto.
      simpl; auto.
    - inversion pth0; subst.
      + edestruct (IHe1 (phi0 ⊕ psi, e1_1)) with (Gamma := (phi0 @ ReplacePrinInModality pi p :: Gamma)); simpl; auto.
        solveCutRel.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p0.
        edestruct (IHe1 (phi0 ⊕ psi, e1_2)) with (Gamma := (psi @ ReplacePrinInModality pi p :: Gamma)); simpl; auto.
        solveCutRel.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p0.
        edestruct (IHe1 (psi, weak x0 (psi @ ReplacePrinInModality pi p :: psi @ m :: Gamma))) with (Gamma0 := (psi @ m :: Gamma)) (pi0 := pi); simpl; auto.
        solveCutRel.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          all : inversion H0; auto. }
        solveSubPath.
        eapply WeakeningTyping; eauto.
        {apply provenProperContextTyping in h2.
          constructor; auto.
          InstantiateProper.
          all : inversion H0; auto. }
        solveSubPath.
        solveNFT.
        eapply WeakeningTyping; eauto.
        {apply provenProperContextTyping in h2.
          constructor; auto.
          InstantiateProper.
          all : inversion H0; auto. }
        solveSubPath.
        solveNFT.
        destruct p0.
        edestruct (IHe1 (phi0, weak x (phi0 @ ReplacePrinInModality pi p :: phi0 @ m :: Gamma))) with (Gamma0 := (phi0 @ m :: Gamma)) (pi0 := pi); simpl; auto.
        solveCutRel.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          all : inversion H0; auto. }
        solveSubPath.
        eapply WeakeningTyping; eauto.
        {apply provenProperContextTyping in h2.
          constructor; auto.
          InstantiateProper.
          all : inversion H0; auto. }
        solveSubPath.
        solveNFT.
        eapply WeakeningTyping; eauto.
        {apply provenProperContextTyping in h2.
          constructor; auto.
          InstantiateProper.
          all : inversion H0; auto. }
        solveSubPath.
        solveNFT.
        destruct p0.
        eexists; split.
        eapply OrLr; eauto.
        simpl; auto.
      + edestruct (IHe1 (phi, e1_1)) with (pi := pi) (Gamma := phi0 @ m0 :: Gamma); simpl; auto.
        solveCutRel.
        repeat (apply There); eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p0.
        edestruct (IHe1 (phi, e1_2)) with (pi := pi) (Gamma := psi @ m0 :: Gamma); simpl; auto.
        solveCutRel.
        repeat (apply There); eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p0.
        eexists; split.
        eapply OrLr; eauto.
        simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (pi := pi) (Gamma := Gamma) ; simpl; eauto.
      destruct p0.
      eexists; split.
      eapply OrR1r; eauto.
      simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (pi := pi) (Gamma := Gamma) ; simpl; eauto.
      destruct p0.
      eexists; split.
      eapply OrR2r; eauto.
      simpl; auto.
    - inversion pth0; subst.
      + edestruct (IHe1 (phi0 ==⟨ l ⟩> psi, e1_2)) with (Gamma := (psi @ ReplacePrinInModality pi p :: Gamma)); simpl; auto.
        solveCutRel.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p0.
        edestruct (IHe1 (phi0 ==⟨ l ⟩> psi, e1_1)) with (Gamma := Gamma); simpl; eauto.
        solveCutRel.
        destruct p0.
        edestruct (IHe1 (psi, weak x (psi @ ReplacePrinInModality pi p :: psi @ m :: Gamma))) with (Gamma0 := (psi @ m :: Gamma)); simpl; auto.
        solveCutRel.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          all : inversion H0; auto. }
        solveSubPath.
        eapply WeakeningTyping; eauto.
        {apply provenProperContextTyping in h2.
          constructor; auto.
          InstantiateProper.
          all : inversion H0; auto. }
        solveSubPath.
        solveNFT.
        eapply WeakeningTyping; eauto.
        {apply provenProperContextTyping in h2.
          constructor; auto.
          InstantiateProper.
          all : inversion H0; auto. }
        solveSubPath.
        solveNFT.
        destruct p0.
        eexists; split.
        eapply ImpLr; eauto.
        simpl; auto.
      + edestruct (IHe1 (phi, e1_2)) with (Gamma := (psi @ m0 :: Gamma)); simpl; auto.
        solveCutRel.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p0.
        edestruct (IHe1 (phi, e1_1)) with (Gamma := (Gamma)); simpl; eauto.
        solveCutRel.
        destruct p0.
        eexists; split.
        eapply ImpLr; eauto.
        simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (Gamma := phi0 @ ⟨ l ⟩ :: Gamma); simpl; auto.
      apply There; eauto.
      eapply Exchange; eauto.
      solveSubPath.
      eapply WeakeningTyping; eauto.
      repeat solveProper.
      solveSubPath.
      solveNFT.
      eapply WeakeningTyping; eauto.
      repeat solveProper.
      solveSubPath.
      solveNFT.
      destruct p0.
      eexists; split.
      eapply ImpRr; eauto.
      simpl; auto.
    - inversion pth0; subst.
      + edestruct (IHe1 (∀ sigma; phi0, e1)) with (Gamma := (open_formula phi0 t @ ReplacePrinInModality pi p) :: Gamma); simpl; auto.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p0.
        edestruct (IHe1 (open_formula phi0 t, weak x (open_formula phi0 t @ ReplacePrinInModality pi p :: open_formula phi0 t @ m :: Gamma))) with (Gamma0 := (open_formula phi0 t @ m) :: Gamma); simpl; auto.
        solveCutRel.
        rewrite OpenFormulaSize; auto.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion t0; auto.
          inversion H8; auto. }
        solveSubPath.
        eapply WeakeningTyping; eauto.
        {apply provenProperContextTyping in h2.
          constructor; auto.          
          InstantiateProper.
          apply provenProperContextTyping in t0.
          inversion t0.
          inversion H6; auto. }
        solveSubPath.
        solveNFT.
        eapply WeakeningTyping; eauto.
        {apply provenProperContextTyping in h2.
          constructor; auto.          
          InstantiateProper.
          apply provenProperContextTyping in t0.
          inversion t0.
          inversion H6; auto. }
        solveSubPath.
        solveNFT.
        destruct p0.
        eexists; split.
        eapply forallLr; eauto.
        simpl; auto.
      + edestruct (IHe1 (phi, e1)) with (Gamma := (open_formula phi0 t @ m0 :: Gamma)); simpl; auto.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p0.
        eexists; split.
        eapply forallLr; eauto.
        simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (Gamma := Gamma); simpl; eauto.
      destruct p0.
      eexists; split.
      eapply forallRr with (y := y); eauto.
      intro.
      apply H1.
      econstructor; eauto; fail.
      simpl; auto.
    - inversion pth0; subst.
      + edestruct (IHe1 (∃ VarSort y; phi0, e1)) with (Gamma := (open_formula phi0 (varTerm y) @ ReplacePrinInModality pi p) :: Gamma); simpl; auto.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p0.
        edestruct (IHe1 (open_formula phi0 (varTerm y), weak x (open_formula phi0 (varTerm y) @ ReplacePrinInModality pi p :: open_formula phi0 (varTerm y) @ m :: Gamma))) with (Gamma0 := (open_formula phi0 (varTerm y) @ m) :: Gamma); simpl; auto.
        solveCutRel.
        rewrite OpenFormulaSize; auto.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          inversion H3; auto. }
        repeat solveProper.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        {apply provenProperContextTyping in h2.
          constructor; auto.          
          InstantiateProper.
          apply provenProperContextTyping in t.
          inversion t; auto.
          inversion H6; auto. }
        solveSubPath.
        solveNFT.
        eapply WeakeningTyping; eauto.
        {apply provenProperContextTyping in h2.
          constructor; auto.          
          InstantiateProper.
          apply provenProperContextTyping in t.
          inversion t; auto.
          inversion H6; auto. }
        solveSubPath.
        solveNFT.
        destruct p0.
        eexists; split.
        eapply existsLr with (y := y); eauto.
        intro.
        inversion H; subst.
        * apply H1.
          apply Exists_cons_tl.
          apply Exists_cons_hd; auto.          
        * apply H1; econstructor; eauto; fail.
        * simpl; auto.
      + edestruct (IHe1 (phi, e1)) with (Gamma := (open_formula phi0 (varTerm y) @ m0 :: Gamma)); simpl; auto.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p0.
        eexists; split.
        eapply existsLr with (y := y); eauto.
        intro.
        inversion H; subst; apply H1; econstructor; eauto; fail.
        simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (Gamma := Gamma); simpl; eauto.
      destruct p0.
      eexists; split.
      eapply existsRr; eauto.
      simpl; auto.
    - edestruct (IHe1 (phi, e1)) with (Gamma := Gamma); simpl; eauto.
      destruct p1.
      eexists; split.
      eapply saysRr; eauto.
      simpl; auto.
    - inversion pth0; subst.
      + edestruct (IHe1 (p0 □ ⟨ lab ⟩ phi0, e1)) with (Gamma := (phi0 @ ReplacePrinInModality pi p ⋅ p0 ⟨ lab ⟩ :: Gamma)); simpl; auto.
        apply There; eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p1.
        edestruct (IHe1 (phi0, weak x (phi0 @ ReplacePrinInModality pi p ⋅ p0 ⟨ lab ⟩ :: phi0 @ m ⋅ p0 ⟨ lab ⟩ :: Gamma))) with (Gamma0 := (phi0 @ m ⋅ p0 ⟨ lab ⟩ :: Gamma))  (pi0 := thereP m q p0 lab pi); simpl; auto.
        apply Here.
        solveNFT.
        eapply WeakeningTyping; eauto.
        { repeat solveProper.
          constructor; auto.
          InstantiateProper.
          all : inversion H0; auto. } 
        solveSubPath.
        { destruct pi; simpl in *.
          eapply WeakeningTyping; eauto.
          { apply provenProperContextTyping in h2.
            constructor; auto.
            InstantiateProper.
            all : inversion H; auto.
            all : inversion H0; auto. }
          solveSubPath.
          eapply WeakeningTyping; eauto.
          { apply provenProperContextTyping in h2.
            constructor; auto.
            InstantiateProper.
            all : inversion H; auto.
            all : inversion H0; auto. }
          solveSubPath. }
        solveNFT.
        { destruct pi; simpl in *.
          eapply WeakeningTyping; eauto.
          { apply provenProperContextTyping in h2.
            constructor; auto.
            InstantiateProper.
            all : inversion H; auto.
            all : inversion H0; auto. }
          solveSubPath.
          eapply WeakeningTyping; eauto.
          { apply provenProperContextTyping in h2.
            constructor; auto.
            InstantiateProper.
            all : inversion H; auto.
            all : inversion H0; auto. }
          solveSubPath. }
        solveNFT.
        destruct p1.
        eexists; split.
        eapply saysLr; eauto.
        simpl; auto.
      + edestruct (IHe1 (phi, e1)) with (Gamma := phi0 @ m0 ⋅ p0 ⟨ lab ⟩ :: Gamma); simpl; auto.
        repeat (apply There); eauto.
        eapply Exchange; eauto.
        solveSubPath.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        eapply WeakeningTyping; eauto.
        repeat solveProper.
        solveSubPath.
        solveNFT.
        destruct p1.
        eexists; split.
        eapply saysLr; eauto.
        simpl; auto.
  Qed.

  Lemma NFFwdL' : forall (phi : flafolFormula) (e1 : proofTerm) {Gamma : Context} {p q : flafolTerm} {m : Modality} (pi : PathToPrinInModality m q) (b : Belief) (pth : Path (phi @ m) Gamma) (h0 : NormalFormTerm e1) (h1 : typing (phi @ ReplacePrinInModality pi p :: Gamma) e1 b) (e2 : proofTerm) (h2 : typing Gamma e2 (canWrite q (LabelAtPrin pi) @ FwdModality pi p)) (h3 : NormalFormTerm' e2 false) (e3 : proofTerm) (h4 : typing Gamma e3 (canRead p (LabelAtPrin pi) @ FwdModality pi q)) (h5 : NormalFormTerm' e3 false), @sigT proofTerm (fun e' => prod (typing Gamma e' b) (NormalFormTerm e')).
  Proof.
    intros.
    eapply NFFwdL1 with (x := (phi, e1)); eauto.
  Qed.    

  Definition PFwdL2 := fun e2 => forall (phi : flafolFormula) (t1 : proofTerm) {Gamma : Context} {p q : flafolTerm} {m : Modality} (pi : PathToPrinInModality m q) (b : Belief) (pth : Path (phi @ m) Gamma) (h1 : typing (phi @ ReplacePrinInModality pi p :: Gamma) t1 b) (h0 : NormalFormTerm t1) (h2 : typing Gamma e2 (canWrite q (LabelAtPrin pi) @ FwdModality pi p)) (h3 : NormalFormTerm' e2 true) (e3 : proofTerm) (h4 : typing Gamma e3 (canRead p (LabelAtPrin pi) @ FwdModality pi q)) (h5 : NormalFormTerm' e3 false), @sigT proofTerm (fun e' => prod (typing Gamma e' b) (NormalFormTerm e')).
  
  Lemma NFFwdL2 : forall (e2 : proofTerm) (phi : flafolFormula) (t1 : proofTerm) {Gamma : Context} {p q : flafolTerm} {m : Modality} (pi : PathToPrinInModality m q) (b : Belief) (pth : Path (phi @ m) Gamma) (h1 : typing (phi @ ReplacePrinInModality pi p :: Gamma) t1 b) (h0 : NormalFormTerm t1) (h2 : typing Gamma e2 (canWrite q (LabelAtPrin pi) @ FwdModality pi p)) (h3 : NormalFormTerm' e2 true) (e3 : proofTerm) (h4 : typing Gamma e3 (canRead p (LabelAtPrin pi) @ FwdModality pi q)) (h5 : NormalFormTerm' e3 false), @sigT proofTerm (fun e' => prod (typing Gamma e' b) (NormalFormTerm e')).
  Proof.
    apply (@Fix _ (fun x1 x2 => term_size x1 < term_size x2) (well_founded_ltof _ _) PFwdL2).
    unfold PFwdL2 in *.
    intros e2 IHe2.
    unfold NormalFormTerm in *.
    destruct e2; intros; inversion h2; subst; try solve [eexists; split; [eapply FwdLr; eauto| simpl; auto]]; repeat destructProd; unfold NormalFormTerm.
    all : try solve [eapply NFFwdL' with (e1 := t1) (e3 := e3); try solve [apply pth]; eauto].
    - edestruct IHe2 with (5 := H1) (b := b) as [x []]; auto.
      repeat apply There; auto.
      eauto.
      solveTyping.
      unfold NormalFormTerm in *.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - simpl in h3; repeat destructProd.
      edestruct IHe2 with (5 := H2) (b := b) as [x []]; auto.
      simpl; solveCutRel.
      repeat apply There; eauto.
      solveTyping.
      unfold NormalFormTerm in *.
      solveNFT.
      solveTyping.
      solveNFT.
      edestruct (IHe2 e2_2) with (5 := H4) (b := b) as [x' []]; auto.
      simpl; solveCutRel.
      repeat apply There; eauto.
      eapply WeakeningTyping.
      apply h1.
      repeat solveProper.
      solveSubPath.
      unfold NormalFormTerm in *.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - simpl in h3; repeat destructProd.
      edestruct (IHe2 e2_2) with (5 := H4) (b := b) as [x' []]; auto.
      simpl; solveCutRel.
      repeat apply There; eauto.
      solveTyping.
      unfold NormalFormTerm in *.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - simpl in h3; repeat destructProd.
      edestruct IHe2 with (5 := H3) (b := b) as [x' []]; auto.
      repeat apply There; eauto.
      solveTyping.
      unfold NormalFormTerm in *.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - simpl in h3.
      pose (freshInSequent (open_formula phi0 (varTerm y) @ m0 :: (phi @ ReplacePrinInModality pi p) :: Gamma) b (VarSort y)) as y'.
      destruct (open_with_fresherLT'' _ _ _ _ y y' e2 H4 _ h3) as [t' [T [nft eq]]]; auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      edestruct (IHe2 t') with (5 := T) (p := p) (q := q) (pi := pi) (phi := phi) (b := b) as [x []]; auto.
      simpl; rewrite eq; auto.
      apply There; auto.
      solveTyping.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split.
      eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
      all : destruct (freshInSequentIsFresh (open_formula phi0 (varTerm y) @ m0 :: (phi @ ReplacePrinInModality pi p) :: Gamma) b (VarSort y)) as [fv1 fv2].
      eapply FreshWithMore. 2: eauto.
      intros.
      simpl; auto.
      simpl; auto.
    - simpl in h3; repeat destructProd.
      edestruct IHe2 with (5 := H1) (b := b) as [x' []]; auto.
      repeat apply There; eauto.
      solveTyping.
      unfold NormalFormTerm in *.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
  Qed.

  Definition PFwdL := fun (e3 : proofTerm) => forall (phi : flafolFormula) (t1 : proofTerm) {Gamma : Context} {p q : flafolTerm} {m : Modality} (pi : PathToPrinInModality m q) (b : Belief) (pth : Path (phi @ m) Gamma) (h4 : typing Gamma e3 (canRead p (LabelAtPrin pi) @ FwdModality pi q)) (h5 : NormalFormTerm' e3 true) (h1 : typing (phi @ ReplacePrinInModality pi p :: Gamma) t1 b) (h0 : NormalFormTerm t1) (e2 : proofTerm) (h2 : typing Gamma e2 (canWrite q (LabelAtPrin pi) @ FwdModality pi p)) (h3 : NormalFormTerm' e2 true) (e3 : proofTerm), @sigT proofTerm (fun e' => prod (typing Gamma e' b) (NormalFormTerm e')).

  
  Lemma NFFwdL : forall (e3 : proofTerm) (phi : flafolFormula) (t1 : proofTerm) {Gamma : Context} {p q : flafolTerm} {m : Modality} (pi : PathToPrinInModality m q) (b : Belief) (pth : Path (phi @ m) Gamma) (h4 : typing Gamma e3 (canRead p (LabelAtPrin pi) @ FwdModality pi q)) (h5 : NormalFormTerm' e3 true) (h1 : typing (phi @ ReplacePrinInModality pi p :: Gamma) t1 b) (h0 : NormalFormTerm t1) (e2 : proofTerm) (h2 : typing Gamma e2 (canWrite q (LabelAtPrin pi) @ FwdModality pi p)) (h3 : NormalFormTerm' e2 true) (e3 : proofTerm), @sigT proofTerm (fun e' => prod (typing Gamma e' b) (NormalFormTerm e')).
  Proof.
    apply (@Fix _ (fun x1 x2 => term_size x1 < term_size x2) (well_founded_ltof _ _) PFwdL).
    unfold PFwdL in *.
    intros e3 IHe3.
    unfold NormalFormTerm in *.
    destruct e3; intros; inversion h4; subst; try solve [eexists; split; [eapply FwdLr; eauto| simpl; auto]]; repeat destructProd; unfold NormalFormTerm.
    all : try solve [eapply NFFwdL2 with (t1 := t1) (e2 := e2); try solve [apply pth]; eauto].
    - edestruct IHe3 with (3 := H1) (b := b) (phi := phi) as [x []]; auto.
      repeat apply There; auto.
      solveTyping.
      unfold NormalFormTerm in *.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - simpl in h5; repeat destructProd.
      edestruct (IHe3 e3_1) with (3 := H2) (b := b) (phi := phi) as [x []]; auto.
      simpl; solveCutRel.
      repeat apply There; eauto.
      solveTyping.
      unfold NormalFormTerm in *.
      solveNFT.
      solveTyping.
      solveNFT.
      edestruct (IHe3 e3_2) with (3 := H4) (b := b) (phi := phi) as [x' []]; auto.
      simpl; solveCutRel.
      repeat apply There; eauto.
      eapply WeakeningTyping.
      apply h1.
      repeat solveProper.
      solveSubPath.
      unfold NormalFormTerm in *.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - simpl in h5; repeat destructProd.
      edestruct (IHe3 e3_2) with (3 := H4) (b := b) (phi := phi) as [x' []]; auto.
      simpl; solveCutRel.
      repeat apply There; eauto.
      solveTyping.
      unfold NormalFormTerm in *.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - simpl in h5; repeat destructProd.
      edestruct IHe3 with (3 := H3) (b := b) (phi := phi) as [x' []]; auto.
      repeat apply There; eauto.
      solveTyping.
      unfold NormalFormTerm in *.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
    - simpl in h5.
      pose (freshInSequent (open_formula phi0 (varTerm y) @ m0 :: (phi @ ReplacePrinInModality pi p) :: Gamma) b (VarSort y)) as y'.
      destruct (open_with_fresherLT'' _ _ _ _ y y' e3 H4 _ h5) as [t' [T [nft eq]]]; auto.
      unfold y'.
      rewrite freshInSequentOfSort; auto.
      edestruct (IHe3 t') with (3 := T) (p := p) (q := q) (pi := pi) (phi := phi) (b := b) as [x []]; auto.
      simpl; rewrite eq; auto.
      apply There; auto.
      solveTyping.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split.
      eapply existsLr with (y := y'); eauto; try (eapply freshInSequentIsFresh; eauto); try (apply freshInSequentOfSort; auto).
      all : destruct (freshInSequentIsFresh (open_formula phi0 (varTerm y) @ m0 :: (phi @ ReplacePrinInModality pi p) :: Gamma) b (VarSort y)) as [fv1 fv2].
      eapply FreshWithMore. 2: eauto.
      intros.
      simpl; auto.
      simpl; auto.
    - simpl in h5; repeat destructProd.
      edestruct IHe3 with (3 := H1) (b := b) (phi := phi) as [x' []]; auto.
      repeat apply There; eauto.
      solveTyping.
      unfold NormalFormTerm in *.
      solveNFT.
      solveTyping.
      solveNFT.
      eexists; split; [econstructor; eauto; fail | simpl; auto].
  Qed.
    
  
  Theorem NormalizeTyping {t : proofTerm} {Gamma : Context} {b : Belief} (pf : typing Gamma t b) : @sigT proofTerm (fun e' => prod (typing Gamma e' b) (NormalFormTerm e')).
  Proof.
    revert Gamma b pf.
    unfold NormalFormTerm.
    induction t; intros; inversion pf; repeat destructProd; subst; try solve [eexists; split; [eauto; fail | simpl; tauto]].
    all: try solve [match goal with
         | [h1 : typing _ ?t1 _, h2 : forall _ _, typing _ ?t1 _ -> _, h3 : typing _ ?t2 _, h4 : forall _ _, typing _ ?t2 _ -> _, h5 : typing _ ?t3 _, h6 : forall _ _, typing _ ?t3 _ -> _ |- _] => destruct (h2 _ _ h1) as [x1 [pf1 nft1]]; destruct (h4 _ _ h3) as [x2 [pf2 nft2]]; destruct (h6 _ _ h5) as [x3 [pf3 nft3]]
         | [h1 : typing _ ?t1 _, h2 : forall _ _, typing _ ?t1 _ -> _, h3 : typing _ ?t2 _, h4 : forall _ _, typing _ ?t2 _ -> _ |- _] => destruct (h2 _ _ h1) as [x1 [pf1 nft1]]; destruct (h4 _ _ h3) as [x2 [pf2 nft2]]
         | [h1 : typing _ ?t _, h2 : forall _ _, typing _ ?t _ -> _ |- _] => destruct (h2 _ _ h1) as [x1 [pf1 nft1]]
         end; eexists; split; simpl; try solve [econstructor; eauto; fail | tauto]].
    - destruct (IHt _ _ H5) as [x1 [pf1 nft1]].
      eexists; split.
      eapply forallRr with (y := y); eauto.
      simpl; auto.
    - destruct (IHt _ _ H4) as [x1 [pf1 nft1]].
      eexists; split.
      eapply existsLr with (y := y); eauto.
      simpl; auto.
    - destruct (IHt1 _ _ H2) as [x1 []].
      destruct (IHt2 _ _ H4) as [x2 []].
      eapply NFFlowsToTransR.
      eauto.
      apply n.
      eauto.
      eauto.
    - destruct (IHt _ _ H1) as [x1 [pf1 nft1]].
      eapply NFmodalityExpandR; eauto.
    - destruct (IHt _ _ H1) as [x1 [pf1 nft1]].
      eapply NFmodalityCollapseR; eauto.
    - destruct (IHt _ _ H1) as [x1 [pf1 nft1]].
      eapply NFModalityExpandL with (x := (phi, x1)); eauto.
    - destruct (IHt _ _ H1) as [x1 [pf1 nft1]].
      eapply NFModalityCollapseL with (x := (phi, x1)); eauto.
    - destruct (IHt1 _ _ H2) as [x1 [pf1 nft1]].
      destruct (IHt2 _ _ H4) as [x2 [pf2 nft2]].
      eapply NFRVariance.
      apply nft2.
      eauto.
      apply pf1.
      eauto.
    - destruct (IHt1 _ _ H2) as [x1 [pf1 nft1]].
      destruct (IHt2 _ _ H4) as [x2 [pf2 nft2]].
      eapply NFLVariance with (e2 := x2) (e1 := x1); simpl; eauto.
    - destruct (IHt1 _ _ H3) as [x1 [pf1 nft1]].
      destruct (IHt2 _ _ H5) as [x2 [pf2 nft2]].
      destruct (IHt3 _ _ H6) as [x3 [pf3 nft3]].
      eapply NFFwdR; simpl; auto.
      eauto.
      apply nft1.
      eauto.
      eauto.
      all : auto.
    - destruct (IHt1 _ _ H3) as [x1 [pf1 nft1]].
      destruct (IHt2 _ _ H5) as [x2 [pf2 nft2]].
      destruct (IHt3 _ _ H6) as [x3 [pf3 nft3]].
      eapply NFFwdL; simpl; auto.
      apply pth'.
      apply pf3.
      auto.
      2 : apply nft1.
      auto.
      eauto.
      auto.
    - destruct (IHt1 _ _ H2) as [x1 [pf1 nft1]].
      destruct (IHt2 _ _ H4) as [x2 [pf2 nft2]].
      eapply (NFCRVariance _ nft2); eauto.
    - destruct (IHt1 _ _ H2) as [x1 [pf1 nft1]].
      destruct (IHt2 _ _ H4) as [x2 [pf2 nft2]].
      eapply (NFCWVariance _ nft2); eauto.
  Qed.
  
End NormalForm.