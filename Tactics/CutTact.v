Require Import Arith.
Require Import Base.Lists.
Require Import Logic.Sequent.
Require Export Formula.
Require Import Term.
Require Import Equality.
Require Import TermEquality.
Require Import FormulaEquality.
Require Import TermHasSortNoFormulas.
Require Import WellFormedFormulaNoProofs.
Require Import TermHasSortNoFormulas.


Module Type CutTact (G : GroundInfo) (GTerm : Term G) (GFormula : Formula G GTerm)
       (TE : TermEquality G GTerm) (FE : FormulaEquality G GTerm GFormula TE)
       (THS : TermHasSort'' G GTerm TE)
       (WFF : WellFormedFormula' G GTerm TE THS GFormula FE) (SEQ : Sequent G GTerm GFormula TE FE THS WFF).
  Import G. Import GTerm. Import GFormula. Import ListNotations.
  Import THS. Import WFF. Import SEQ.
  
  Lemma max_inj1 : forall m n p, p <= n -> p <= (max n m).
  Proof.
    intros m n p H.
    etransitivity; eauto.
    apply PeanoNat.Nat.le_max_l.
  Qed.
  Lemma max_inj2 : forall m n p, p <= m -> p <= (max n m).
  Proof.
    intros m n p H.
    etransitivity; eauto.
    apply PeanoNat.Nat.le_max_r.
  Qed.

  Ltac solve_max_le := (repeat match goal with
                               | |- ?A <= max ?A _ => apply max_inj1
                               | |- ?A <= max ?B _ => apply max_inj2
                               end); try apply max_inj1; reflexivity.

  Lemma InCons: forall (l:Belief) m a , In a (l :: m) -> {a = l} + {In a m}.
  Proof.
    intros l m a H.
    eapply InBoolSpec in H.
    eapply InBoolCons in H.
    destruct H; auto.
    right.
    eapply InBoolSpec; eauto.
    Unshelve.
    apply BeliefEqDec.
  Qed.

  Ltac destructProd :=
    match goal with
    | [h : prod _ _ |- _] => destruct h
    end.
  
  Ltac destr_In :=
    match goal with
    | [H1 : In _ (?x :: ?G) |- _] => apply InCons in H1;
                                   destruct H1; [idtac| destr_In]
    | _ => idtac
    end.

  Ltac solveSubPath := intro; simpl;
                     repeat (match goal with
                             | [|- prod (Path _ ?G1 -> Path _ ?G2) (Path _ ?G2 -> Path _ ?G1)] => split
                             | [|- Path _ (?a :: ?b :: ?c :: _ ++ _ ) -> Path _ (_ ++ (?a :: ?b :: ?c :: _))] => apply (ExchangePath [a; b; c])
                             | [|- Path _ (_ ++ (?a :: ?b :: ?c :: _)) -> Path _ (?a :: ?b :: ?c :: _ ++ _ )] => apply @ExchangePath with (L2 := [a; b; c])
                             | [|- Path _ (?a :: ?b :: _ ++ _ ) -> Path _ (_ ++ (?a :: ?b :: _))] => apply (ExchangePath [a; b])
                             | [|- Path _ (_ ++ (?a :: ?b :: _)) -> Path _ (?a :: ?b :: _ ++ _ )] => apply @ExchangePath with (L2 := [a; b])
                             | [|- Path _ (?a :: _ ++ _ ) -> Path _ (_ ++ (?a :: _))] => apply (ExchangePath [a])
                             | [|- Path _ (_ ++ (?a ::  _)) -> Path _ (?a :: _ ++ _ )] => apply @ExchangePath with (L2 := [a])
                             | [|- (Path _ ?G1 -> Path _ ?G2)] => let h := fresh in
                                                               intro h; apply PathToIn in h; apply (InToPath BeliefEqDec); simpl; destr_In; eauto
                             end).
  
 Ltac solveCutRel :=
    match goal with
    | |- ((?A < ?A) \/ _) => right; solveCutRel
    | |- ((?A = ?A) /\ (?B < ?B)) \/ _ => right; solveCutRel
    | |- _ => try left; repeat split; auto; try apply le_n_S; try solve [solve_max_le]
    end.

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
 
                                                                                                  
   | [h : typing (?a :: _) _ _ |- Forall ProperBelief (?a :: _)] => apply provenProperContextTyping in h; inversion h; subst; constructor; auto
   | [h : typing (?a :: _) _ _ |- ProperContext (?a :: _)] => apply provenProperContextTyping in h; inversion h; subst; constructor; auto
   end.                                                     

End CutTact.