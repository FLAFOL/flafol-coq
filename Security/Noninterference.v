Require Export Sequent.
Require Export Speaksfor.
Require Export CompatibleSupercontext.

Require Import Base.Lists.
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

Module Type Noninterference (G : GroundInfo) (GTerm : Term G) (GFormula : Formula G GTerm)
       (TE : TermEquality G GTerm) (FE : FormulaEquality G GTerm GFormula TE)
       (THS : TermHasSort'' G GTerm TE)
       (WFF : WellFormedFormula' G GTerm TE THS GFormula FE) (SEQ : Sequent G GTerm GFormula TE FE THS WFF)
       (CT : CutTact G GTerm GFormula TE FE THS WFF SEQ) (NF : NormalForm G GTerm GFormula TE FE THS WFF SEQ CT)
       (C : Cut G GTerm GFormula TE FE THS WFF SEQ CT NF)
       (SF : Speaksfor G GTerm GFormula TE FE THS WFF SEQ CT NF C)
       (SS : SignedSubformula G GTerm GFormula TE FE)
       (CSC : CompatibleSupercontext G GTerm GFormula TE FE SS THS WFF SEQ).
  Import G. Import GTerm. Import GFormula. Import ListNotations.
  Import THS. Import WFF. Import SEQ. Import SF. Import SS. Import CSC.

  Theorem RelabelPathToLabelCombine :
    forall {m : Modality} {l : flafolTerm} (pth : PathToLabelInModality m l) (mr : ModalityResidual) (l2 : flafolTerm),
      ReplaceLabelInModality (ModalityCombine m mr) l l2 (PathToLabelInModalityCombine pth mr)
      = ModalityCombine (ReplaceLabelInModality m l l2 pth) mr.
  Proof.
    intros m l pth mr; revert m l pth.
    induction mr; intros m l pth l2; simpl. reflexivity.
    simpl. destruct a as [q l3]. rewrite IHmr. simpl.
    reflexivity.
  Qed.

  Inductive NI_ret : Context -> Belief -> Belief -> Set :=
  | inflnc : forall {Gamma : Context} {b1 b2 : Belief}
               (Delta : Context) (m1 m2 : Modality) (mr : ModalityResidual),
      Delta ≪ Gamma ⊢csc b2 ->
      G b1 m1 -> G b2 m2 -> Delta ⊢inf (ModalityCombine m1 mr) ⇛ m2 -> NI_ret Gamma b1 b2.
                                                                                
  Hint Resolve ProperContextWithoutPath.
  Hint Resolve PeanoNat.Nat.le_max_l. Hint Resolve PeanoNat.Nat.le_max_r.
  
  Program Fixpoint Noninterference' (Gamma : Context) (b1 b2 : Belief) (pth : Path b1 Gamma)
          (pf : Gamma ⊢ b2) {measure (proof_size pf)} :
    {pf' : (WithoutPath Gamma pth) ⊢ b2 | proof_size pf' <= proof_size pf} +
    NI_ret Gamma b1 b2 :=
    match pf with
    | axiom _ _ pctxt pth' =>
      match (PathToSamePlaceDec pth pth' BeliefEqDec) with
      | left ptsp =>
        inr (inflnc Gamma (G_choice b1) (G_choice b2) [] _ (G_choice_spec b1) (G_choice_spec b2) _)
      | right n =>
        inl (axiom (WithoutPath Gamma pth) b2
                   (ProperContextWithoutPath Gamma b1 pth pctxt)
                   (RepathWithoutPath pth pth' _))
      end
    | TTR Gamma m pctxt pmod =>
      inl (TTR (WithoutPath Gamma pth) m (ProperContextWithoutPath Gamma b1 pth pctxt) pmod)
    | FFL _ phi m mr pctxt wffφ pmod pth_to_ff pmr =>
      match (PathToSamePlaceDec pth pth_to_ff BeliefEqDec) with
      | left ptsp =>
        inr (inflnc Gamma (G_choice b1) (G_choice (phi @ ModalityCombine m mr))
                    (mr ++ (G_choice_residual (phi @ ModalityCombine m mr)))
                    _ (G_choice_spec b1) _ _)
      | right n =>
        inl (FFL (WithoutPath Gamma pth) phi m mr
                 (ProperContextWithoutPath Gamma b1 pth pctxt)
                 wffφ pmod
                 (RepathWithoutPath pth pth_to_ff _) pmr)
      end
    | AndL _ phi psi m _ pth_to_and pf1 =>
      match (PathToSamePlaceDec pth pth_to_and BeliefEqDec) with
      | left ptsp =>
        match (Noninterference' _ b1 b2 (There (phi @ m) (There (psi @ m) pth)) pf1) with
        | inl pf2 =>
          match (Noninterference' _ (phi @ m) b2 (Here (phi @ m) (psi @ m :: _)) pf2) with
          | inl pf3 =>
            match (Noninterference' _ (psi @ m) b2 (Here (psi @ m) _) pf3) with
            | inl pf4 => inl pf4
            | inr infl =>
              match infl with
              | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
                inr (inflnc (phi @ m :: b1 :: Delta) m1 m2 mr _ _ _ _)
              end
            end
          | inr infl =>
            match infl with
            | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
              inr (inflnc (b1 :: Delta) m1 m2 mr _ _ _ _)
            end
          end
        | inr infl =>
          match infl with
          | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
            inr (inflnc Delta m1 m2 mr _ Gm1 Gm2 i)
          end
        end
      | right n =>
        match (Noninterference' _ b1 b2 (There (phi @ m) (There (psi @ m) pth)) pf1) with
        | inl pf2 => inl (AndL _ phi psi m b2 (RepathWithoutPath pth pth_to_and _) pf2)
        | inr infl =>
          match infl with
          | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i => inr (inflnc Delta m1 m2 mr _ Gm1 Gm2 i)
          end
        end
      end
    | AndR _ phi psi m pf1 pf2 =>
      match (Noninterference' Gamma b1 (phi @ m) pth pf1) with
      | inl pf1' =>
        match (Noninterference' Gamma b1 (psi @ m) pth pf2) with
        | inl pf2' => inl (AndR _ phi psi m pf1' pf2')
        | inr ret =>
          match ret with
          | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i => inr (inflnc Delta m1 m2 mr _ _ _ _)
          end
        end
      | inr ret =>
        match ret with
        | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i => inr (inflnc Delta m1 m2 mr _ _ _ _)
        end
      end
    | OrL _ phi psi m _ pth_to_or pf1 pf2 =>
      match (PathToSamePlaceDec pth pth_to_or BeliefEqDec) with
      | left ptsp =>
        match (Noninterference' (phi @ m :: Gamma) _ _ (Here (phi @ m) Gamma) pf1) with
        | inl pf1' =>
          match (Noninterference' Gamma _ _ pth pf1') with
          | inl pf1'' => inl pf1''
          | inr ret => inr ret
          end
        | inr ret => match ret with
                    | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
                      inr (inflnc Delta m1 m2 mr _ _ Gm2 i)
                    end
        end
      | right n =>
        match (Noninterference' _ b1 b2 (There (phi @ m) pth) pf1) with
        | inl pf1' => match (Noninterference' _ b1 b2 (There (psi @ m) pth) pf2) with
                     | inl pf2' => inl (OrL (WithoutPath Gamma pth)
                                           phi psi m b2 (RepathWithoutPath pth pth_to_or _) pf1' pf2') 
                     | inr ret =>
                       match ret with
                       | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
                         inr (inflnc Delta m1 m2 mr _ Gm1 Gm2 i)
                       end
                     end
        | inr ret =>
          match ret with
          | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
            inr (inflnc Delta m1 m2 mr (CSCOrL1 Delta Gamma _ phi psi m pth_to_or Δcsc) Gm1 Gm2 i)
          end
        end
      end
    | OrR1 _ phi psi m pf1 wff_ψ =>
      match (Noninterference' Gamma b1 (phi @ m) pth pf1) with
      | inl pf1' => inl (OrR1 _ phi psi m pf1' wff_ψ)
      | inr ret =>
        match ret with
        | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
          inr (inflnc Delta m1 m2 mr _ Gm1 _ i)
        end
      end
    | OrR2 _ phi psi m pf1 wff_φ => 
      match (Noninterference' Gamma b1 (psi @ m) pth pf1) with
      | inl pf1' => inl (OrR2 _ phi psi m pf1' wff_φ)
      | inr ret =>
        match ret with
        | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
          inr (inflnc Delta m1 m2 mr _ Gm1 _ i)
        end
      end
    | ImpL _ phi psi m l b pth_to_impl pf1 pf2 =>
      match (PathToSamePlaceDec pth pth_to_impl BeliefEqDec) with
      | left ptsp =>
        match (Noninterference' (psi @ m :: Gamma) (psi @ m) b2 (Here (psi @ m) Gamma) pf2) with
        | inl pf2' =>
          match (Noninterference' Gamma b1 b2 pth pf2') with
          | inl pf2'' => inl pf2''
          | inr ret => match ret with
                      | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
                        inr (inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i)
                      end
          end
        | inr ret => match ret with
                    | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
                      inr (inflnc Delta m1 m2 mr (CSCImpL1 Delta Gamma b2 phi l psi m pth Δcsc) _ _ _)
                    end
        end
      | right n =>
        match (Noninterference' (psi @ m :: Gamma) b1 b2 (There (psi @ m) pth) pf2) with
        | inl pf2' =>
          match (Noninterference' Gamma b1 (phi @ ⟨l⟩) pth pf1) with
          | inl pf1' =>
            inl (ImpL (WithoutPath Gamma pth) phi psi m l b _ pf1' pf2')
          | inr ret =>
            match (Noninterference' (psi @ m :: (WithoutPath Gamma pth)) (psi @ m) b2 (Here (psi @ m) (WithoutPath Gamma pth)) pf2') with
                   | inl pf2'' => inl (Weakening pf2'' (WithoutPath Gamma pth) _ _)
                   | inr ret2 => 
                     match ret with
                     | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
                       match ret2 with
                       | inflnc E m1' m2' mr' Ecsc Gm1' Gm2' i' =>
                         inr (inflnc (Delta ++ (b1 :: E)) m1 m2' (mr ++ mr') _ _ _ _)
                       end
                     end
            end
          end
        | inr ret => match ret with
                    | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
                      inr (inflnc Delta m1 m2 mr _ _ _ _)
                    end
        end
      end
    | ImpR _ phi psi m' l pf1 =>
      match (Noninterference' (phi @ ⟨l⟩ :: Gamma) b1 (psi @ m') (There (phi @ ⟨l⟩) pth) pf1) with
      | inl pf1' => inl (ImpR (WithoutPath Gamma pth) phi psi m' l pf1')
      | inr ret => match ret with
                  | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
                    inr (inflnc Delta m1 m2 mr (CSCImpR Delta Gamma phi l psi m' Δcsc) Gm1 _ i)
                  end
      end
    | forallL _ sigma phi t m b pth_to_fa lct tsort pf1 =>
      match PathToSamePlaceDec pth pth_to_fa BeliefEqDec with
      | left ptsp =>
        let pth_to_open := Here (open_formula phi t @ m) Gamma in
        match (Noninterference' _ (open_formula phi t @ m) b2 pth_to_open pf1) with
        | inl pf1' =>
          match (Noninterference' Gamma b1 b2 pth pf1') with
          | inl pf1'' => inl pf1''
          | inr ret => match ret with
                      | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
                        inr (inflnc Delta m1 m2 mr _ _ Gm2 _)
                      end
          end
        | inr ret => match ret with
                    | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
                      let Δcsc' :=CSCForallL Delta Gamma sigma phi t m b pth_to_fa lct tsort Δcsc in 
                      inr (inflnc Delta m1 m2 mr Δcsc' _ _ _)
                    end
        end
      | right n =>
        match (Noninterference' _ b1 b2 (There (open_formula phi t @ m) pth) pf1) with
        | inl pf1' =>
          let pth_to_fa' := RepathWithoutPath pth pth_to_fa _ in
          inl (forallL (WithoutPath Gamma pth) sigma phi t m b pth_to_fa' lct tsort pf1')
        | inr ret => match ret with
                    | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
                      let Δcsc' :=CSCForallL Delta Gamma sigma phi t m b pth_to_fa lct tsort Δcsc in 
                      inr (inflnc Delta m1 m2 mr Δcsc' _ _ _)
                    end
        end
      end
    | forallR _ sigma y phi m ysort yfvc yfvf yfvm pf1 =>
      match (Noninterference' Gamma b1 (open_formula phi (varTerm y) @ m) pth pf1) with
      | inl pf1' => inl (forallR (WithoutPath Gamma pth) sigma y phi m ysort _ yfvf yfvm pf1')
      | inr ret =>
        match ret with
        | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
          let Δcsc' := CSCForallR Delta Gamma sigma y phi m ysort yfvc yfvf yfvm Δcsc in
          inr (inflnc Delta m1 m2 mr Δcsc' Gm1 _ i)
        end
      end
    | existsL _ sigma y phi m b pth_to_ex ysort yfvc yfvb pf1 =>
      match PathToSamePlaceDec pth pth_to_ex BeliefEqDec with
      | left ptsp =>
        let pth_to_open := Here (open_formula phi (varTerm y) @ m) Gamma in
        match (Noninterference' _ (open_formula phi (varTerm y) @ m) b2 pth_to_open pf1) with
        | inl pf1' =>
          match (Noninterference' Gamma b1 b2 pth pf1') with
          | inl pf1'' => inl pf1''
          | inr ret => match ret with
                      | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
                        inr (inflnc Delta m1 m2 mr _ _ Gm2 _)
                      end
          end
        | inr ret => match ret with
                    | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
                      let Δcsc' := CSCExistsL Delta Gamma sigma phi y m b pth_to_ex ysort yfvc yfvb Δcsc in
                      inr (inflnc Delta m1 m2 mr Δcsc' _ _ _)
                    end
        end
      | right n =>
        let pth_to_open := There (open_formula phi (varTerm y) @ m) pth in
        match (Noninterference' _ b1 b2 pth_to_open pf1) with
        | inl pf1' =>
          let pth_to_ex' := RepathWithoutPath pth pth_to_ex _ in
          inl (existsL (WithoutPath Gamma pth) sigma y phi m b pth_to_ex' ysort _ yfvb pf1')
        | inr ret => match ret with
                    | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
                      let Δcsc' := CSCExistsL Delta Gamma sigma phi y m b pth_to_ex ysort yfvc yfvb Δcsc in
                      inr (inflnc Delta m1 m2 mr Δcsc' _ _ _)
                    end
        end

      end
    | existsR _ sigma t phi m lct tsort pf1 =>
      match Noninterference' Gamma b1 (open_formula phi t @ m) pth pf1 with
      | inl pf1' =>
        inl (existsR (WithoutPath Gamma pth) sigma t phi m lct tsort pf1')
      | inr ret => 
        match ret with
        | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
          let Δcsc' := CSCExistsR Delta Gamma sigma t phi m lct tsort Δcsc in
          inr (inflnc Delta m1 m2 mr Δcsc' Gm1 _ i)
        end
      end
    | flowsToRefl _ l m pctxt lsort pmod =>
      let pctxt' := ProperContextWithoutPath Gamma b1 pth pctxt in
      inl (flowsToRefl (WithoutPath Gamma pth) l m pctxt' lsort pmod)
    | flowsToTransR _ l1 l2 l3 m pf1 pf2 =>
      match (Noninterference' Gamma b1 (l1 ⊑ l2 @ m) pth pf1) with
      | inl pf1' =>
        match (Noninterference' Gamma b1 (l2 ⊑ l3 @ m) pth pf2) with
        | inl pf2' => inl (flowsToTransR (WithoutPath Gamma pth) l1 l2 l3 m pf1' pf2')
        | inr ret =>
          match ret with
          | inflnc Delta m1 m2 mr Δcsc' Gm1 Gm2 i =>
            inr (inflnc Delta m1 m2 mr _ Gm1 _ i)
          end
        end
      | inr ret =>
        match ret with
        | inflnc Delta m1 m2 mr Δcsc' Gm1 Gm2 i =>
          inr (inflnc Delta m1 m2 mr _ Gm1 _ i)
        end
      end
    | saysR _ p l phi m pf1 =>
      match Noninterference' Gamma b1 (phi @ m ⋅ p⟨l⟩) pth pf1 with
      | inl pf1' => inl (saysR (WithoutPath Gamma pth) p l phi m pf1')
      | inr ret =>
        match ret with
        | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
          inr (inflnc Delta m1 m2 mr (CSCsaysR Delta Gamma p l phi m Δcsc) Gm1 _ _)
        end
      end
    | saysL _ p l phi m _ pth_to_says pf1 =>
      match PathToSamePlaceDec pth pth_to_says BeliefEqDec with
      | left ptsp =>
        let b1' := phi @ m ⋅ p⟨l⟩ in
        match Noninterference' (b1' :: Gamma) b1' b2 (Here b1' Gamma) pf1 with
        | inl pf1' =>
          match Noninterference' Gamma b1 b2 pth pf1' with
          | inl pf1' => inl pf1'
          | inr ret =>
            match ret with
            | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
              inr (inflnc Delta m1 m2 mr _ _ _ _)
            end
          end
        | inr ret =>
          match ret with
          | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
            inr (inflnc Delta m1 m2 mr _ _ _ _)
          end
        end
      | right n =>
        let b1' := phi @ m⋅p⟨l⟩ in
        match Noninterference' (b1' :: Gamma) b1 b2 (There b1' pth) pf1 with
        | inl pf1' =>
          inl (saysL (WithoutPath Gamma pth) p l phi m b2 (RepathWithoutPath pth pth_to_says _) pf1')
        | inr ret => match ret with
                    | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
                      let Δcsc' := CSCsaysL Delta Gamma p l phi m b2 pth_to_says Δcsc in
                      inr (inflnc Delta m1 m2 mr Δcsc' Gm1 _ _)
                    end
        end
      end
    | modalityExpandR _ phi m pth_to_dbl pf1 =>
      match Noninterference' Gamma b1 (phi @ CollapseDoubleInModality pth_to_dbl) pth pf1 with
      | inl pf1' =>
        inl (modalityExpandR (WithoutPath Gamma pth) phi m pth_to_dbl pf1')
      | inr ret =>
        match ret with
        | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
          match ModalityExtension (CollapseDoubleInModality pth_to_dbl) m2 with
          | Some mr2 =>
            let m2' := ModalityCombine m mr2 in
            inr (inflnc Delta m1 m2' mr _ _ _ _)
          | None => _
          end
        end
      end
    | modalityCollapseR _ phi m pth_to_dbl pf1 =>
      match Noninterference' Gamma b1 (phi @ m) pth pf1 with
      | inl pf1' =>
        inl (modalityCollapseR (WithoutPath Gamma pth) phi m pth_to_dbl pf1')
      | inr ret =>
        match ret with
        | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
          match ModalityExtension m m2 with
          | Some mr2 =>
            let m2' := ModalityCombine (CollapseDoubleInModality pth_to_dbl) mr2 in
            inr (inflnc Delta m1 m2' mr _ _ _ _)
          | None => _
          end
        end
      end
    | modalityExpandL _ phi m pth_to_dbl _ pth_to_clpsd pf1 =>
      match PathToSamePlaceDec pth pth_to_clpsd BeliefEqDec with
      | left ptsp =>
        match Noninterference' ((phi @ m) :: Gamma) (phi @ m) b2 (Here (phi @ m) Gamma) pf1 with
        | inl pf1' => match Noninterference' Gamma b1 b2 pth pf1' with
                     | inl pf1'' => inl pf1''
                     | inr ret =>
                       match ret with
                       | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
                         inr _
                       end
                     end
        | inr ret =>
          match ret with
          | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
            match  ModalityExtension m m1 with
            | Some mr1 =>
              let m1' := ModalityCombine (CollapseDoubleInModality pth_to_dbl) mr1 in
              let Δcsc' := CSCMEL Delta Gamma phi m pth_to_dbl b2 pth_to_clpsd Δcsc in
              inr (inflnc Delta m1' m2 mr Δcsc' _ _ _)
            | None => _
            end
          end
        end
      | right n =>
        match Noninterference' (phi @ m :: Gamma) b1 b2 (There (phi @ m) pth) pf1 with
        | inl pf1' =>
          let pth_to_clpsd' := RepathWithoutPath pth pth_to_clpsd _ in  
          inl (modalityExpandL (WithoutPath Gamma pth) phi m pth_to_dbl b2 pth_to_clpsd' pf1')
        | inr ret =>
          match ret with
          | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
            let Δcsc' := CSCMEL Delta Gamma phi m pth_to_dbl b2 pth_to_clpsd Δcsc in
            inr (inflnc Delta m1 m2 mr Δcsc' _ _ _)
          end
        end
      end
    | modalityCollapseL _ phi m pth_to_dbl b pth_to_expnd pf1 =>
      match PathToSamePlaceDec pth pth_to_expnd BeliefEqDec with
      | left ptsp =>
        let b1' := phi @ CollapseDoubleInModality pth_to_dbl in
        match Noninterference' (b1' :: Gamma) b1' b2 (Here b1' Gamma) pf1 with
        | inl pf1' => match Noninterference' Gamma b1 b2 pth pf1' with
                     | inl pf1'' => inl pf1''
                     | inr ret =>
                       match ret with
                       | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
                         inr _
                       end
                     end
        | inr ret =>
          match ret with
          | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
            match  ModalityExtension (CollapseDoubleInModality pth_to_dbl) m1 with
            | Some mr1 =>
              let m1' := ModalityCombine m mr1 in
              let Δcsc' := CSCMCL Delta Gamma phi m pth_to_dbl b2 pth_to_expnd Δcsc in
              inr (inflnc Delta m1' m2 mr Δcsc' _ _ _)
            | None => _
            end
          end
        end
      | right n =>
        let b1' := phi @ CollapseDoubleInModality pth_to_dbl in
        match Noninterference' (b1' :: Gamma) b1 b2 (There b1' pth) pf1 with
        | inl pf1' =>
          let pth_to_expnd' := RepathWithoutPath pth pth_to_expnd _ in  
          inl (modalityCollapseL (WithoutPath Gamma pth) phi m pth_to_dbl b2 pth_to_expnd' pf1')
        | inr ret =>
          match ret with
          | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
            let Δcsc' := CSCMCL Delta Gamma phi m pth_to_dbl b2 pth_to_expnd Δcsc in
            inr (inflnc Delta m1 m2 mr Δcsc' _ _ _)
          end
        end
      end
    | RVariance _ l1 l2 phi m pth_to_lbl pf1 pf2 =>
      match Noninterference' Gamma b1 (l1 ⊑ l2 @ VarModality pth_to_lbl l2) pth pf2 with
      | inl pf2' =>
        match Noninterference' Gamma b1 (phi @ m) pth pf1 with
        | inl pf1' => inl (RVariance (WithoutPath Gamma pth) l1 l2 phi m pth_to_lbl pf1' pf2')
        | inr ret =>
          match ret with
          | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
            match ModalityExtension m m2 with
            | Some mr2 =>
              let m2' := ModalityCombine (ReplaceLabelInModality m l1 l2 pth_to_lbl) mr2 in
              inr (inflnc Delta m1 m2' mr _ _ _ _)
            | None => _
            end
          end
        end
      | inr ret =>
        match ret with
        | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
          let m3 := G_choice (phi @ ReplaceLabelInModality m l1 l2 pth_to_lbl) in
          match ModalityExtension (VarModality pth_to_lbl l2) m3 with
          | Some mr' =>
            let mr2 := mr ++ mr' in
            inr (inflnc Delta m1 m3 mr2 _ _ _ _)
          | None => _
          end
        end
      end
    | LVariance _ l1 l2 phi m pth_to_lbl _ pth_to_vary pf1 pf2 =>
      match PathToSamePlaceDec pth pth_to_vary BeliefEqDec with
      | left ptsp =>
        let b := phi @ ReplaceLabelInModality m l1 l2 pth_to_lbl in
        match Noninterference' (b :: Gamma) b1 b2 (There b pth) pf1 with
        | inl pf1' =>
          match Noninterference' (b :: WithoutPath Gamma pth) b b2 (Here b (WithoutPath Gamma pth)) pf1' with
          | inl pf1'' => inl pf1''
          | inr ret => match ret with
                      | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
                        match ModalityExtension (VarModality pth_to_lbl l2) m1 with
                        | Some mr' =>
                          let m1' := ModalityCombine (VarModality pth_to_lbl l1) mr' in
                          inr (inflnc (b1 :: Delta) m1' m2 mr _ _ _ _)
                        | None => _
                        end
                      end
          end
        | inr ret => match ret with
                      | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
                        inr (inflnc Delta m1 m2 mr _ _ _ _)
                    end
        end
      | right n =>
        let b := phi @ ReplaceLabelInModality m l1 l2 pth_to_lbl in
        match Noninterference' (b :: Gamma) b1 b2 (There b pth) pf1 with
        | inl pf1' =>
          match Noninterference' Gamma b1 (l1 ⊑ l2 @ VarModality pth_to_lbl l2) pth pf2 with
          | inl pf2' =>
            let npth := RepathWithoutPath pth pth_to_vary _ in
            inl (LVariance (WithoutPath Gamma pth) l1 l2 phi m pth_to_lbl _ npth pf1' pf2')
          | inr ret2 =>
            match ret2 with
            | inflnc Δ1 m11 m12 mr1 Δcsc1 Gm11 Gm12 i1 =>                     
              let Γ' := WithoutPath Gamma pth in
              let pth' := RepathWithoutPath pth pth_to_vary _ in
              match Noninterference' (b :: Γ') b b2 (Here b Γ') pf1' with
              | inl pf1'' => inl pf1''
              | inr ret =>
                match ret with
                | inflnc Δ2 m21 m22 mr2 Δcsc2 Gm21 Gm22 i2 =>
                  match ModalityExtension (VarModality pth_to_lbl l2) m21 with
                  | Some mr3 =>
                    inr (inflnc (b1 :: (Δ1 ++ Δ2)) m11 m22 (mr1 ++ mr3 ++ mr2) _ _ _ _)
                  | None => _
                  end
                end
              end
            end
          end
        | inr ret =>
          match ret with
          | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
            inr (inflnc Delta m1 m2 mr _ _ _ _)
          end
        end
      end
    | FwdR _ phi m p q pth_to_p pf1 pf2 pf3 =>
      match Noninterference' _ b1 _ pth pf1 with
      | inl pf1' =>
        match Noninterference' _ b1 _ pth pf2 with
        | inl pf2' =>
          match Noninterference' _ b1 _ pth pf3 with
          | inl pf3' => inl (FwdR (WithoutPath Gamma pth) phi m p q pth_to_p pf1' pf2' pf3')
          | inr ret =>
            match ret with
            | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
              let m3 := G_choice (phi @ ReplacePrinInModality pth_to_p q) in
              match ModalityExtension (FwdModality pth_to_p q) m3 with
              | Some mr' =>
                let mr2 := mr ++ mr' in
                inr (inflnc Delta m1 m3 mr2 _ _ _ _)
              | None => _
              end
            end
          end
        | inr ret =>
            match ret with
            | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i => 
              let m3 := G_choice (phi @ ReplacePrinInModality pth_to_p q) in
              match ModalityExtension (ReplacePrinInModality pth_to_p q) m3 with
              | Some mr' =>
                let mr2 := mr ++ (ModalityAfterPrin pth_to_p) ++ mr' in
                inr (inflnc Delta m1 m3 mr2 _ _ _ _)
              | None => _
              end  
            end
        end
      | inr ret =>
        match ret with
        | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
          match ModalityExtension m m2 with
          | Some mr2 =>
            let m2' := ModalityCombine (ReplacePrinInModality pth_to_p q) mr2 in
            inr (inflnc Delta m1 m2' mr _ _ _ _)
          | None => _
          end

        end
      end
    | FwdL _ phi m p q pth_to_q _ pth_to_fwd pf1 pf2 pf3 => 
      match PathToSamePlaceDec pth pth_to_fwd BeliefEqDec with
      | left ptsp =>
        let b1' := phi @ ReplacePrinInModality pth_to_q p in
        match Noninterference' (b1' :: Gamma) b1' b2 (Here b1' Gamma) pf1 with
        | inl pf1' =>
          match Noninterference' Gamma b1 b2 pth pf1' with
          | inl pf1'' => inl pf1''
          | inr ret =>
            match ret with
            | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
              inr (inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i)
            end
          end
        | inr ret =>
          match ret with
          | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
            match ModalityExtension (ReplacePrinInModality pth_to_q p) m1 with
            | Some mr1 =>
              let m1' := ModalityCombine (ReplacePrinInModality pth_to_q q) mr1 in
              inr (inflnc Delta m1' m2 mr _ _ _ _)
            | None => _
            end
          end
        end
      | right n =>
        let b := phi @ ReplacePrinInModality pth_to_q p in
        match Noninterference' (b :: Gamma) b1 b2 (There b pth) pf1 with
        | inl pf1' =>
          match Noninterference' Gamma b1 _ pth pf2 with
          | inl pf2' =>
            match Noninterference' Gamma b1 _ pth pf3 with
            | inl pf3' =>
              let pth_to_fwd' := RepathWithoutPath pth pth_to_fwd _ in
              inl (FwdL (WithoutPath Gamma pth) phi m p q pth_to_q b2 pth_to_fwd' pf1' pf2' pf3')
            | inr ret1 =>
            match ret1 with
            | inflnc Δ1 m11 m12 mr1 Δcsc1 Gm11 Gm12 i1 =>
              let Γ' := WithoutPath Gamma pth in
              match Noninterference' (b :: Γ') b b2 (Here b Γ') pf1' with
              | inl pf1'' => inl pf1''
              | inr ret2 =>
                match ret2 with
                | inflnc Δ2 m21 m22 mr2 Δcsc2 Gm21 Gm22 i2 =>
                  match ModalityExtension (ReplacePrinInModality pth_to_q p) m21 with
                  | Some mr2' =>
                    let new_mr := mr1 ++ (ModalityAfterPrin pth_to_q) ++ mr2' ++ mr2 in
                    inr (inflnc (b1 :: Δ1 ++ Δ2) m11 m22 new_mr _ _ _ _)
                  | None => _
                  end
                end
            end
            end
            end
          | inr ret1 =>
            match ret1 with
            | inflnc Δ1 m11 m12 mr1 Δcsc1 Gm11 Gm12 i1 =>
              let Γ' := WithoutPath Gamma pth in
              match Noninterference' (b :: Γ') b b2 (Here b Γ') pf1' with
              | inl pf1'' => inl pf1''
              | inr ret2 =>
                match ret2 with
                | inflnc Δ2 m21 m22 mr2 Δcsc2 Gm21 Gm22 i2 =>
                  match ModalityExtension (ReplacePrinInModality pth_to_q p) m21 with
                  | Some mr2' =>
                    let new_mr := mr1 ++ (ModalityAfterPrin pth_to_q) ++ mr2' ++ mr2 in
                    inr (inflnc (b1 :: Δ1 ++ Δ2) m11 m22 new_mr _ _ _ _)
                  | None => _
                  end
                end
            end
            end
          end
        | inr ret =>
          match ret with
          | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
            inr (inflnc Delta m1 m2 mr _ _ _ _)
          end
        end
      end
    | CRVariance _ p l1 l2 m pf1 pf2 =>
      match Noninterference' _ _ _ pth pf1 with
      | inl pf1' =>
        match Noninterference' _ _ _ pth pf2 with
        | inl pf2' => inl (CRVariance (WithoutPath Gamma pth) p l1 l2 m pf1' pf2')
        | inr ret =>
          match ret with
          | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
            let (pmod, wff_ft) := provenProperBelief pf2 in
            let Δcsc' := CSCAtomic _ _ (l1 ⊑ l2) m _ (flowsToAtomic l1 l2) wff_ft pmod Δcsc in
            inr (inflnc Delta m1 m2 mr Δcsc' _ _ _)
          end
        end
      | inr ret =>
        match ret with
        | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
          let (pmod, wff_ft) := provenProperBelief pf1 in
          let Δcsc' := CSCAtomic _ _ (canRead p l2) m _ (canRAtomic p l2) wff_ft pmod Δcsc in

          inr (inflnc Delta m1 m2 mr Δcsc' _ _ _)
        end
      end
    | CWVariance _ p l1 l2 m pf1 pf2 => 
      match Noninterference' _ _ _ pth pf1 with
      | inl pf1' =>
        match Noninterference' _ _ _ pth pf2 with
        | inl pf2' => inl (CWVariance (WithoutPath Gamma pth) p l1 l2 m pf1' pf2')
        | inr ret =>
          match ret with
          | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
            let (pmod, wff_ft) := provenProperBelief pf2 in
            let Δcsc' := CSCAtomic _ _ (l1 ⊑ l2) m _ (flowsToAtomic l1 l2) wff_ft pmod Δcsc in
            inr (inflnc Delta m1 _ mr Δcsc' _ _ _)
          end
        end
      | inr ret =>
        match ret with
        | inflnc Delta m1 m2 mr Δcsc Gm1 Gm2 i =>
          let (pmod, wff_ft) := provenProperBelief pf1 in
          let Δcsc' := CSCAtomic _ _ (canWrite p l1) m _ (canWAtomic p l1) wff_ft pmod Δcsc in


          inr (inflnc Delta m1 m2 mr Δcsc' _ _ _)
        end
      end
    end.
  Next Obligation.
    clear Heq_anonymous. apply PathToSamePlaceSameA in ptsp.
    rewrite ptsp. constructor; constructor; auto.
    apply G_choice_proper. apply BeliefInProperContextIsProper with(Gamma := Gamma); auto.
    apply PathToIn; auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl. reflexivity.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl. reflexivity.
  Defined.
  Next Obligation.
    destruct (G'_choice (formula_size phi) phi (ModalityCombine m mr)) eqn:e.
    apply G'_choice_spec; auto.
    apply G'_choice_formula_size_enough_neg in e. inversion e.
  Defined.
  Next Obligation.
    destruct (G'_choice (formula_size phi) phi (ModalityCombine m mr)) eqn:e;
      [|apply G'_choice_formula_size_enough_neg in e; inversion e].
    destruct (G'_choice_residual (formula_size phi) phi (ModalityCombine m mr)) eqn:e'.
    pose proof (G'_choice_residual_spec phi (formula_size phi) (ModalityCombine m mr) m1 e').
    pose proof (eq_trans (eq_sym e) H). inversion H0.
    rewrite ModalityCombineApp. constructor.
    pose proof (PathToSamePlaceSameA _ _ _ _ _ _ ptsp).
    rewrite H1. simpl.
    constructor; auto.
    rewrite <- ModalityCombineApp. rewrite <- H2.
    apply G'_choice_proper
                   with (phi := phi) (fuel := formula_size phi) (m := (ModalityCombine m mr)); auto.
    apply ModalityCombineProper; auto.
    apply G'_choice_residual_formula_size_enough_neg in e'. inversion e'.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl. reflexivity.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl. apply PeanoNat.Nat.lt_succ_diag_r.
  Defined.
  Next Obligation.
    unfold eq_rect in H. simpl in H.
    apply Lt.lt_le_S.
    apply PeanoNat.Nat.le_lt_trans with (m := proof_size pf1); auto.
    clear Heq_anonymous. apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply PeanoNat.Nat.lt_succ_diag_r.
  Defined.
  Next Obligation.
    unfold eq_rect in H0. simpl in H0.
    apply PeanoNat.Nat.le_lt_trans with (m := proof_size pf2); auto.
    apply PeanoNat.Nat.le_lt_trans with (m := proof_size pf1); auto.
    clear Heq_anonymous Heq_anonymous1. apply JMeq_eq in Heq_pf.
    rewrite <- Heq_pf. simpl. apply PeanoNat.Nat.lt_succ_diag_r.
  Defined.
  Next Obligation.
    fold (WithoutPath Gamma pth) in pf4.
    transitivity (proof_size pf3); auto.
    transitivity (proof_size pf2); auto.
    transitivity (proof_size pf1); auto.
    clear Heq_anonymous Heq_anonymous0 Heq_anonymous1 Heq_anonymous2 H1.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl. apply PeanoNat.Nat.lt_le_incl.
    apply PeanoNat.Nat.lt_succ_diag_r.
  Defined.
  Next Obligation.
    apply CSCAndL with (phi := phi) (psi := psi) (m := m); auto.
    apply CSCWeakening.
    fold (WithoutPath Gamma pth) in Δcsc.
    apply CSCPermR with (Gamma1 := b1 :: WithoutPath (psi @ m :: Gamma) (There (psi @ m) pth)).
    simpl. apply CSCWeakening. exact Δcsc.
    symmetry. apply PathToFront.
  Defined.
  Next Obligation.
    clear Heq_anonymous3 Heq_anonymous2 Heq_anonymous1 H0 Heq_anonymous4.
    apply PathToSamePlaceSameA in ptsp.
    rewrite ptsp. simpl. right. apply G'_at_least_as_much_fuel with (fuel1 := formula_size psi); auto.
  Defined.
  Next Obligation.
    pose proof (provenProperContext pf1).
    apply ConsProperContext in H1; destruct H1 as [H1 H2]; auto;
      apply ConsProperContext in H2; destruct H2 as [H2 H3].
    fold (WithoutPath Gamma pth) in *.
    unfold eq_rect in H0; simpl in H0.
    clear Heq_anonymous1 Heq_anonymous2 Heq_anonymous3 Heq_anonymous4.
    apply CIWeakening with (Gamma := Delta); [| intros b H4; apply There|]; auto.
    apply ProperContextCons; [|apply ProperContextCons]; auto.
    - apply PathToSamePlaceSameA in ptsp. rewrite ptsp.
      pose proof (PathToIn pth_to_and).
      apply BeliefInProperContextIsProper in H4; auto.
    - clear Heq_infl. apply CompatibleSupercontextProper in Δcsc; auto.
      apply ProperContextCons; auto. clear Heq_pf H0; apply provenProperBelief in pf1; auto.
    - apply There; auto.
  Defined.
  Next Obligation.
    fold (WithoutPath Gamma pth) in *.
    apply CSCAndL with (phi := phi) (psi := psi) (m := m); auto.
    apply CSCPermR with (Gamma1 := b1 :: WithoutPath (phi @ m :: psi @ m :: Gamma) (There _ (There _ pth))).
    simpl. apply CSCWeakening. exact Δcsc.
    symmetry; apply PathToFront.
  Defined.
  Next Obligation.
    fold (WithoutPath Gamma pth) in *.
    clear Heq_anonymous1 Heq_anonymous2 Heq_anonymous3 H.
    apply PathToSamePlaceSameA in ptsp. rewrite ptsp. simpl.
    left. apply G'_at_least_as_much_fuel with (fuel1 := formula_size phi); auto.
  Defined.
  Next Obligation.
    pose proof (provenProperContext pf1).
    apply ConsProperContext in H0; destruct H0. apply ConsProperContext in H1; destruct H1.
    apply CIWeakening with (Gamma := Delta); auto.
    apply ProperContextCons.
    pose proof (PathToSamePlaceSameA _ _ _ _ _ _ ptsp).
    rewrite H3.
    pose proof (PathToIn pth_to_and).
    apply BeliefInProperContextIsProper in H4; auto.
    fold (WithoutPath Gamma pth) in *.
    clear Heq_infl; apply CompatibleSupercontextProper in Δcsc; auto.
    repeat (apply ProperContextCons; auto).
    eapply provenProperBelief; eauto.
    intros b H3. apply There; auto.
  Defined.
  Next Obligation.
    clear Heq_infl; apply CSCAndL in Δcsc; auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl; apply PeanoNat.Nat.lt_succ_diag_r.
  Defined.
  Next Obligation.
    unfold eq_rect in H; simpl in H.
    apply Lt.lt_le_S. apply PeanoNat.Nat.le_lt_trans with (m := proof_size pf1); auto.
    clear Heq_anonymous. apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply PeanoNat.Nat.lt_succ_diag_r.
  Defined.
  Next Obligation.
    clear Heq_infl. apply CSCAndL in Δcsc; auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf.
    rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. auto.
  Defined.
  Next Obligation.
    clear Heq_anonymous. unfold eq_rect in H. simpl in H.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. auto.
  Defined.
  Next Obligation.
    clear Heq_anonymous.
    unfold eq_rect in *. simpl in *. clear Heq_anonymous0.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Le.le_n_S. apply PeanoNat.Nat.max_lub.
    transitivity (proof_size pf1); auto.
    transitivity (proof_size pf2); auto.
  Defined.
  Next Obligation.
    right; apply G'_at_least_as_much_fuel with (fuel1 := formula_size psi); auto.
  Defined.
  Next Obligation.
    left; apply G'_at_least_as_much_fuel with (fuel1 := formula_size phi); auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. apply PeanoNat.Nat.le_max_l.
  Defined.
  Next Obligation.
    unfold eq_rect in H; simpl in H; auto.
    clear Heq_anonymous. apply JMeq_eq in Heq_pf. rewrite <- Heq_pf.
    simpl. apply Lt.le_lt_n_Sm. etransitivity; eauto.
  Defined.
  Next Obligation.
    unfold eq_rect in H0; simpl in H0.
    clear Heq_anonymous Heq_anonymous0 Heq_anonymous1.
    etransitivity; eauto.
    transitivity (proof_size pf1); auto.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply le_S; auto.
  Defined.
  Next Obligation.
    clear Heq_ret.
    apply CSCOrL1 with (psi := psi) in Δcsc; auto.
  Defined.
  Next Obligation.
    pose proof (PathToSamePlaceSameA _ _ _ _ _ _ ptsp).
    rewrite H. simpl. left.
    apply G'_at_least_as_much_fuel with (fuel1 := formula_size phi); auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. apply PeanoNat.Nat.le_max_l.
  Defined.
  Next Obligation.
    clear Heq_anonymous; unfold eq_rect in *; simpl in *.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. apply PeanoNat.Nat.le_max_r.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *.
    clear Heq_anonymous1 Heq_anonymous0 Heq_anonymous.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf; simpl.
    apply Le.le_n_S. apply PeanoNat.Nat.max_lub;
                       etransitivity; eauto.
  Defined.
  Next Obligation.
    clear Heq_ret;
      apply CSCOrL2 with (phi := phi)in Δcsc; auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf; simpl.
    apply PeanoNat.Nat.lt_succ_diag_r.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *.
    clear Heq_anonymous. apply JMeq_eq in Heq_pf. rewrite <- Heq_pf; simpl.
    apply Le.le_n_S; auto.
  Defined.
  Next Obligation.
    left. apply G'_at_least_as_much_fuel with (fuel1 := formula_size phi); auto.
  Defined.
  Next Obligation.
   apply JMeq_eq in Heq_pf. rewrite <- Heq_pf; simpl.
    apply PeanoNat.Nat.lt_succ_diag_r.
  Defined. 
  Next Obligation.
    unfold eq_rect in *; simpl in *.
    clear Heq_anonymous. apply JMeq_eq in Heq_pf. rewrite <- Heq_pf; simpl.
    apply Le.le_n_S; auto.
  Defined.
  Next Obligation.
    right; apply G'_at_least_as_much_fuel with (fuel1 := formula_size psi); auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf; simpl.
    apply Lt.le_lt_n_Sm. apply PeanoNat.Nat.le_max_r.
  Defined.
  Next Obligation.
    clear Heq_anonymous. unfold eq_rect in *; simpl in *.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. etransitivity; eauto.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *.
    clear Heq_anonymous1 Heq_anonymous Heq_anonymous0. 
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply le_S. etransitivity; eauto. transitivity (proof_size pf2); eauto.
  Defined.
  Next Obligation.
    clear Heq_anonymous2 Heq_anonymous1. apply PathToSamePlaceSameA in ptsp; auto.
  Defined.
  Next Obligation.
    clear Heq_anonymous2 Heq_anonymous1. apply PathToSamePlaceSameA in ptsp; auto.
    rewrite ptsp. simpl. apply G'_at_least_as_much_fuel with (fuel1 := formula_size psi); auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Lt.le_lt_n_Sm. apply PeanoNat.Nat.le_max_r.
  Defined.
  Next Obligation.
    clear Heq_anonymous H.  apply JMeq_eq in Heq_pf.
    rewrite <- Heq_pf. simpl. apply Lt.le_lt_n_Sm; auto.
  Defined.
  Next Obligation.
    apply RepathWithoutPath with (p2 := pth_to_impl); auto.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *.
    clear Heq_anonymous1 Heq_anonymous.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Le.le_n_S. apply PeanoNat.Nat.max_lub; etransitivity; eauto.
  Defined.    
  Next Obligation.
    unfold eq_rect in *; simpl in *.
    clear Heq_anonymous Heq_anonymous1 Heq_anonymous0.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Lt.le_lt_n_Sm. etransitivity; eauto.
  Defined.
  Next Obligation.
    eapply provenProperContext; eauto.
  Defined.
  Next Obligation.
    rewrite <- WeakeningSize.
    clear Heq_anonymous Heq_anonymous2 Heq_anonymous1.
    unfold eq_rect in *; simpl in *.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf; simpl.
    apply PeanoNat.Nat.le_le_succ_r. etransitivity; eauto.
    etransitivity; eauto.
  Defined.
  Next Obligation.
    clear Heq_ret Heq_ret2.
    apply CSCWeakening with (b2 := b1) in Ecsc; auto.
    apply CSCPermR with (Gamma2 := psi @ m :: Gamma) in Ecsc; auto.
    apply CSCImpL1 with (phi := phi) (l := l) in Ecsc; auto.
    apply CSCImpL2 with (psi := psi) (b := b2) (m := m) in Δcsc; auto.
    transitivity (psi @ m :: b1 :: WithoutPath Gamma pth).
    constructor; fail.
    apply perm_skip. symmetry; apply PathToFront.
  Defined.
  Next Obligation.
    clear Heq_ret Heq_ret2.
    assert (ProperModalityResidual mr')
      by (pose proof (canInfluenceProper _ _ _ i'); destruct H0; destruct H1;
          apply C.ModProperApp with (m1' := mr') (m1 := m1') in H1;
          [destruct H1; auto | reflexivity]).
    apply ExtCIResidual with (r := mr') in i; auto.
    assert (ProperContext (Delta ++ b1 :: E))
    by (apply AppProperContext;
        [pose proof (canInfluenceProper _ _ _ i); destruct H1; auto 
        | apply ProperContextCons;
          [apply BeliefInProperContextIsProper with (Gamma := Gamma);
           [exact (provenProperContext pf)
           |apply PathToIn; auto]
          | eapply canInfluenceProper; eauto]]).
    assert (Path (phi ==⟨l⟩> psi @ m) (Delta ++ b1 :: E))
    by (apply InToPath; [exact BeliefEqDec|];
        apply in_or_app; left;
        apply @CompatibleSupercontextSuper with (b := phi @ ⟨l⟩) (Gamma := Gamma); auto;
        apply PathToIn; auto).
    pose (i'' := ImpCI (Delta ++ b1 :: E) phi psi l m m2 m1' H1 H2 Gm2 Gm1').
    apply ExtCIResidual with (r := mr') in i''; auto.
    apply CIWeakening with (Delta := Delta ++ b1 :: E) in i.
    pose (i''' := TransCI _ _ _ _ i i'').
    apply CIWeakening with (Delta := Delta ++ b1 :: E) in i'.
    pose (i'''' := TransCI _ _ _ _ i''' i').
    rewrite ModalityCombineApp in i''''; auto.
    auto.
    intros b H3. apply InToPath; [exact BeliefEqDec|]. apply in_or_app; right. right.
    apply PathToIn in H3; auto.
    auto.
    intros b H3. apply InToPath; [exact BeliefEqDec|]. apply in_or_app; left.
    apply PathToIn in H3; auto.
  Defined.
  Next Obligation.
    clear Heq_ret. apply CSCImpL1 with (phi := phi) (l := l) in Δcsc; auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf.
    simpl. apply PeanoNat.Nat.lt_succ_diag_r.
  Defined.
  Next Obligation.
    unfold eq_rect in H; simpl in H. clear Heq_anonymous.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Le.le_n_S; auto.
  Defined.
  Next Obligation.
    apply G'_at_least_as_much_fuel with (fuel1 := formula_size psi); auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Le.le_n_S; auto.
  Defined.
  Next Obligation.
    clear Heq_anonymous. unfold eq_rect in *; simpl in *.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Le.le_n_S; auto.
  Defined.
  Next Obligation.
    clear Heq_anonymous Heq_anonymous1. unfold eq_rect in *; simpl in *.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    etransitivity; eauto.
  Defined.
  Next Obligation.
    clear Heq_anonymous1 Heq_anonymous2.
    apply PathToSamePlaceSameA in ptsp. rewrite ptsp. simpl.
    exists t; split; [| split]; auto.
    rewrite <- OpenFormulaSize with (t := t); auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply PeanoNat.Nat.lt_succ_diag_r.
  Defined.
  Next Obligation.
    clear Heq_anonymous. unfold eq_rect in *; simpl in *.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Le.le_n_S; auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply PeanoNat.Nat.lt_succ_diag_r.
  Defined.
  Next Obligation.
    intro yfree. apply yfvc. unfold freeInContext in yfree.
    apply Exists_exists in yfree.
    destruct yfree as [b yfree]; destruct yfree as [xin yfree].
    apply Exists_exists. exists b; split; auto.
    apply PathToIn. apply InToPath in xin; [| exact BeliefEqDec].
    eapply withoutLiftPath; eauto.
  Defined.
  Next Obligation.
    clear Heq_anonymous; unfold eq_rect in *; simpl in *.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Le.le_n_S; auto.
  Defined.
  Next Obligation.
    exists (varTerm y); split; [|split]; try constructor.
    rewrite <- OpenFormulaSize with (t := varTerm y); auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply PeanoNat.Nat.lt_succ_diag_r.
  Defined.
  Next Obligation.
    clear Heq_anonymous. unfold eq_rect in *; simpl in *.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Le.le_n_S; auto.
  Defined.
  Next Obligation.
    clear Heq_anonymous Heq_anonymous1. unfold eq_rect in *; simpl in *.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    etransitivity; eauto.
  Defined.
  Next Obligation.
    clear Heq_anonymous1 Heq_anonymous2.
    apply PathToSamePlaceSameA in ptsp. rewrite ptsp. simpl.
    exists (varTerm y); split; [| split]; auto; try (constructor).
    rewrite <- OpenFormulaSize with (t := varTerm y); auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply PeanoNat.Nat.lt_succ_diag_r.
  Defined.
  Next Obligation.
    intro yfree. apply yfvc. unfold freeInContext in yfree.
    apply Exists_exists in yfree.
    destruct yfree as [b yfree]; destruct yfree as [xin yfree].
    apply Exists_exists. exists b; split; auto.
    apply PathToIn. apply InToPath in xin; [| exact BeliefEqDec].
    eapply withoutLiftPath; eauto.
  Defined.
  Next Obligation.
    clear Heq_anonymous; unfold eq_rect in *; simpl in *.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Le.le_n_S; auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply PeanoNat.Nat.lt_succ_diag_r.
  Defined.
  Next Obligation.
    clear Heq_anonymous; unfold eq_rect in *; simpl in *.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Le.le_n_S; auto.
  Defined.
  Next Obligation.
    exists t; split; [|split]; auto.
    rewrite <- OpenFormulaSize with (t := t); auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl; reflexivity.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Lt.le_lt_n_Sm. auto.
  Defined.
  Next Obligation.
    clear Heq_anonymous H.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Lt.le_lt_n_Sm. auto.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *.
    clear Heq_anonymous Heq_anonymous0.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Le.le_n_S. apply PeanoNat.Nat.max_lub; etransitivity; eauto.
  Defined.
  Next Obligation.
    pose proof (provenProperBelief pf2). destruct H0.
    apply CSCAtomic with (phi := l2 ⊑ l3) (m := m); auto. constructor.
  Defined.
  Next Obligation.
    pose proof (provenProperBelief pf1). destruct H.
    apply CSCAtomic with (phi := l1 ⊑ l2) (m := m); auto. constructor.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Lt.le_lt_n_Sm. auto.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Le.le_n_S; auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Lt.le_lt_n_Sm. auto.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Le.le_n_S; auto.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous Heq_anonymous1.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    etransitivity; eauto.
  Defined.
  Next Obligation.
    eapply CSCsaysL; eauto.
  Defined.
  Next Obligation.
    clear Heq_anonymous0 Heq_anonymous1. apply PathToSamePlaceSameA in ptsp. rewrite ptsp.
    simpl; auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Lt.le_lt_n_Sm. auto.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Le.le_n_S; auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Lt.le_lt_n_Sm. auto.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Le.le_n_S; auto.
  Defined.
  Next Obligation.
    apply CSCMER with (pth := pth_to_dbl); auto.
  Defined.
  Next Obligation.
    pose proof (ModalityExtension_spec _ _ _ (eq_sym Heq_anonymous)).
    clear Heq_ret. rewrite H in Gm2.
    eapply G'_replace_base; exact Gm2.
  Defined.
  Next Obligation.
    pose proof (ModalityExtension_spec _ _ _ (eq_sym Heq_anonymous)).
    pose proof (canInfluenceProper _ _ _ i). destruct H0.
    pose proof (provenProperBelief pf). destruct H2.
    pose proof (SFExpandDouble pth_to_dbl H0 H2).
    apply @SFModalityExt with (mr := mr2) in H4.
    rewrite <- H in H4.
    apply TransCI with (m2 := m2); auto. apply SFCI; auto.
    symmetry in Heq_anonymous. apply ModalityExtensionProper in Heq_anonymous; auto.
    destruct H1; auto.
  Defined.
  Next Obligation.
    symmetry in Heq_anonymous. apply G'_creates_extensions_neg with (fuel := formula_size phi) (phi := phi) in Heq_anonymous.
    inversion Heq_anonymous.
    auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply PeanoNat.Nat.lt_succ_diag_r.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Le.le_n_S; auto.
  Defined.
  Next Obligation.
    pose proof (ModalityExtension_spec _ _ _ (eq_sym Heq_anonymous)).
    clear Heq_ret; rewrite H in Gm2.
    apply G'_replace_base with (m1 := m); exact Gm2.
  Defined.
  Next Obligation.
    pose proof (ModalityExtension_spec _ _ _ (eq_sym Heq_anonymous)).
    pose proof (canInfluenceProper _ _ _ i). destruct H0.
    pose proof (provenProperBelief pf). destruct H2.
    apply CollapseDoubleProper' in H2.
    pose proof (SFCollapseDouble pth_to_dbl H0 H2).
    apply @SFModalityExt with (mr := mr2) in H4.
    rewrite <- H in H4. apply SFCI in H4. apply TransCI with (m2 := m2); auto.
    symmetry in Heq_anonymous; apply ModalityExtensionProper in Heq_anonymous; auto.
    destruct H1; auto.
  Defined.
  Next Obligation.
    symmetry in Heq_anonymous. eapply G'_creates_extensions_neg in Heq_anonymous.
    inversion Heq_anonymous.
    exact Gm2.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply PeanoNat.Nat.lt_succ_diag_r.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Le.le_n_S; auto.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous.
    clear Heq_anonymous0 Heq_anonymous1.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    etransitivity; eauto.
  Defined.
  Next Obligation.
    pose proof (ModalityExtension_spec _ _ _ (eq_sym Heq_anonymous)).
    clear Heq_ret; rewrite H in Gm1.
    pose proof (PathToSamePlaceSameA _ _ _ _ _ _ ptsp).
    rewrite H0.
    apply G'_replace_base with (m1 := m); exact Gm1.
  Defined.
  Next Obligation.
    pose proof (ModalityExtension_spec _ _ _ (eq_sym Heq_anonymous)).
    pose proof (canInfluenceProper _ _ _ i). destruct H0; destruct H1.
    pose proof (BeliefInProperContextIsProper b1 Gamma (provenProperContext pf) (PathToIn pth)).
    pose proof (PathToSamePlaceSameA _ _ _ _ _ _ ptsp).
    rewrite H4 in H3. clear H4. destruct H3.
    apply CollapseDoubleProper' in H3.
    pose proof (SFExpandDouble pth_to_dbl H0 H3).
    apply @SFModalityExt with (mr := mr1) in H5.
    apply SFCI in H5. apply TransCI with (m2 := ModalityCombine m1 mr); auto.
    apply ExtCIResidual with (r := mr) in H5; auto.
    rewrite <- H in H5. exact H5.
    pose proof (C.ModProperApp mr m1 (ModalityCombine m1 mr) eq_refl H1).
    destruct H6.
    exact H7.
    symmetry in Heq_anonymous.
    apply ModalityExtensionProper with (m1 := m) (m2 := m1); auto.
    apply G_proper with (b := phi @ m); auto.
    pose proof (provenProperContext pf1).
    apply ConsProperContext in H6; destruct H6; auto.
  Defined.
  Next Obligation.
    symmetry in Heq_anonymous. eapply G'_creates_extensions_neg in Heq_anonymous;
                                 eauto.
    destruct Heq_anonymous.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply PeanoNat.Nat.lt_succ_diag_r.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Le.le_n_S; auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply PeanoNat.Nat.lt_succ_diag_r.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Le.le_n_S; auto.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous Heq_anonymous0 Heq_anonymous1.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    etransitivity; eauto.
  Defined.
  Next Obligation.
    pose proof (ModalityExtension_spec _ _ _ (eq_sym Heq_anonymous)).
    clear Heq_ret; rewrite H in Gm1.
    pose proof (PathToSamePlaceSameA _ _ _ _ _ _ ptsp).
    rewrite H0.
    apply G'_replace_base with (m1 := CollapseDoubleInModality pth_to_dbl); exact Gm1.
  Defined.
  Next Obligation.
    pose proof (ModalityExtension_spec _ _ _ (eq_sym Heq_anonymous)).
    pose proof (canInfluenceProper _ _ _ i). destruct H0; destruct H1.
    pose proof (BeliefInProperContextIsProper b1 Gamma (provenProperContext pf) (PathToIn pth)).
    pose proof (PathToSamePlaceSameA _ _ _ _ _ _ ptsp).
    rewrite H4 in H3. clear H4. destruct H3.
    pose proof (SFCollapseDouble pth_to_dbl H0 H3).
    apply @SFModalityExt with (mr := mr1) in H5.
    apply SFCI in H5. apply TransCI with (m2 := ModalityCombine m1 mr); auto.
    apply ExtCIResidual with (r := mr) in H5; auto.
    rewrite <- H in H5. exact H5.
    pose proof (C.ModProperApp mr m1 (ModalityCombine m1 mr) eq_refl H1).
    destruct H6.
    exact H7.
    symmetry in Heq_anonymous.
    apply ModalityExtensionProper with (m1 := CollapseDoubleInModality pth_to_dbl) (m2 := m1); auto.
    apply G_proper with (b := phi @ CollapseDoubleInModality pth_to_dbl); auto.
    pose proof (provenProperContext pf1).
    apply ConsProperContext in H6; destruct H6; auto.
  Defined.
  Next Obligation.
    symmetry in Heq_anonymous; eapply G'_creates_extensions_neg in Heq_anonymous;
      eauto.
    destruct Heq_anonymous.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply PeanoNat.Nat.lt_succ_diag_r.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Le.le_n_S; auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. apply PeanoNat.Nat.le_max_r.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. apply PeanoNat.Nat.le_max_l.
  Defined. 
  Next Obligation.
    clear Heq_anonymous.
    unfold eq_rect in *. simpl in *. clear Heq_anonymous0.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Le.le_n_S. apply PeanoNat.Nat.max_lub.
    transitivity (proof_size pf1); auto.
    transitivity (proof_size pf2); auto.
  Defined.
  Next Obligation.
    apply G'_replace_base with (m1 := m).
    pose proof (ModalityExtension_spec m m2 mr2 (eq_sym Heq_anonymous)).
    rewrite <- H0. exact Gm2.
  Defined.
  Next Obligation.
    apply TransCI with (m2 := m2); auto.
    pose proof (ModalityExtension_spec _ _ _ (eq_sym Heq_anonymous)).
    rewrite H0. apply ExtCIResidual.
    pose proof (canInfluenceProper _ _ _ i).
    destruct H1 as [H1 H2]; destruct H2.
    apply (ModalityExtensionProper _ _ _ H3 (eq_sym Heq_anonymous)).
    apply SFCI. apply SFReplaceLabel.
    pose (provenProperBelief pf). destruct p.
    eapply ReplaceLabelInModalityProper'; eauto.
    pose (provenProperBelief pf2). destruct p.
    inversion H4; auto.
    pose proof (Weakening pf2 Delta).
    pose proof (canInfluenceProper _ _ _ i). destruct H2.
    specialize (H1 H2).
    apply H1. intros b' H4.
    apply (InToPath BeliefEqDec). eapply CompatibleSupercontextSuper; [exact Δcsc|].
    apply PathToIn; auto.
  Defined.
  Next Obligation.
    symmetry in Heq_anonymous; eapply G'_creates_extensions_neg in Heq_anonymous;
      eauto.
    destruct Heq_anonymous.
  Defined.
  Next Obligation.
    pose proof (provenProperBelief pf2).
    destruct H.
    apply CSCAtomic with (phi := l1 ⊑ l2) (m := VarModality pth_to_lbl l2);
      auto.
    constructor.
  Defined.    
  Next Obligation.
    destruct (G'_choice (formula_size phi) phi (ReplaceLabelInModality m l1 l2 pth_to_lbl))
             eqn:e; [| exfalso; eapply G'_choice_formula_size_enough_neg; eauto].
    apply G'_choice_spec; auto.
  Defined.
  Next Obligation.
    destruct (G'_choice (formula_size phi) phi (ReplaceLabelInModality m l1 l2 pth_to_lbl))
             eqn:e; [| exfalso; eapply G'_choice_formula_size_enough_neg; eauto].
    clear Heq_ret. apply G'_atomic in Gm2; [| constructor].
    rewrite <- Gm2 in i.
    pose proof (ModalityExtension_spec _ _ _ (eq_sym Heq_anonymous)).
    rewrite H.
    rewrite <- ModalityCombineApp. apply ExtCIResidual; auto.
    apply ModalityExtensionProper with (m1 := VarModality pth_to_lbl l2) (m2 := m0); auto.
    pose proof (provenProperBelief pf). destruct H0.
    eapply G'_choice_proper; eauto.
  Defined.
  Next Obligation.
    exfalso.
    destruct (G'_choice (formula_size phi) phi (ReplaceLabelInModality m l1 l2 pth_to_lbl))
             eqn:e; [| exfalso; eapply G'_choice_formula_size_enough_neg; eauto].
    destruct (PrincipalAtLabel pth_to_lbl) eqn:e0;
      [rename f into p | pose proof ((proj1 (NilPrincipalModalityLabel pth_to_lbl)) e0)].
    - destruct (ModalityBeforeLabel pth_to_lbl) eqn:e1;
        [| pose proof ((proj2 (NilPrincipalModalityLabel pth_to_lbl)) e1) as e2;
           pose proof (eq_trans (eq_sym e0) e2) as e3; inversion e3].
      rewrite ModalityRestitchReplaceLabel with (p0 := p) (m' := m3) in e; auto.
      rewrite RestitchVarModality with (p0 := p) (m' := m3) in Heq_anonymous; auto.
      assert (ModalityExtension (ModalityCombine (m3 ⋅ p⟨l2⟩) (ModalityAfterLabel pth_to_lbl)) m0 <> None) by
      (apply G'_creates_extensions_neg with (phi := phi) (fuel := formula_size phi);
       apply G'_choice_spec; auto).
      apply H; apply ModalityExtensionExtendedNone; auto.
    - rewrite ModalityRestitchReplaceLabelNil in e; auto.
      rewrite RestitchVarModalityNil in Heq_anonymous; auto.
      assert (ModalityExtension (ModalityCombine (⟨l2⟩) (ModalityAfterLabel pth_to_lbl)) m0 <> None) by
      (apply G'_creates_extensions_neg with (phi := phi) (fuel := formula_size phi);
       apply G'_choice_spec; auto).
      apply H0. apply ModalityExtensionExtendedNone; auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. apply PeanoNat.Nat.le_max_l.
  Defined. 
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. etransitivity; eauto.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *.
    clear Heq_anonymous Heq_anonymous0 Heq_anonymous1.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    transitivity (proof_size pf1); auto.
    transitivity (proof_size pf1'); auto.
  Defined.
  Next Obligation.
    apply CSCLVariance with (l1 := l1) (l2 := l2) (phi := phi) (m := m) (pth := pth_to_lbl); auto.
    apply CSCPermR with (Gamma1 := b1 :: phi @ ReplaceLabelInModality m l1 l2 pth_to_lbl :: WithoutPath Gamma pth).
    apply CSCWeakening. exact Δcsc.
    symmetry; apply (PathToFront (There _ pth)).
  Defined.
  Next Obligation.
    clear Heq_ret.
    rewrite RestitchReplaceLabelVarModality in Gm1.
    pose proof (PathToSamePlaceSameA _ _ _ _ _ _ ptsp).
    rewrite H0.
    rewrite RestitchModalityVarModality with (pth0 := pth_to_lbl) at 1.
    pose proof (ModalityExtension_spec _  _ _ (eq_sym Heq_anonymous)).
    rewrite H1 in Gm1.
    destruct (ModalityExtension (ModalityCombine (VarModality pth_to_lbl l2) (ModalityAfterLabel pth_to_lbl)) m1) eqn:e.
    pose proof (ModalityExtension_spec _ _ _ e).
    rewrite ModalityCombineApp in H2.
    pose proof (ModalityCombineInj2 _ _ _ (eq_trans (eq_sym H1) H2)).
    rewrite H3. rewrite <- ModalityCombineApp.
    rewrite H3 in Gm1. rewrite <- ModalityCombineApp in Gm1.
    apply G'_replace_base with (m1 := ModalityCombine (VarModality pth_to_lbl l2) (ModalityAfterLabel pth_to_lbl)); auto.
    rewrite <- H1 in Gm1. exfalso; eapply G'_creates_extensions_neg; eauto.
  Defined.

  
  Next Obligation.
    destruct (PrincipalAtLabel pth_to_lbl) eqn:e.
    - rename f into p.
      destruct (ModalityBeforeLabel pth_to_lbl) eqn:e'.
      pose (pth_to_lbl' := PathToLabelInModalityCombine (PathToLabelInModalityCombine (hereSimLab m0 p l1) mr') mr).
      pose proof (eq_refl (ReplaceLabelInModality _ _ l2 pth_to_lbl')).
      unfold pth_to_lbl' in H0 at 1.
      rewrite RelabelPathToLabelCombine in H0 at 1.
      rewrite RelabelPathToLabelCombine in H0 at 1.
      simpl in H0.
      pose proof (ModalityExtension_spec _ _ _ (eq_sym Heq_anonymous)).
      rewrite <- RestitchVarModality with (pth0 := pth_to_lbl) in H0; auto.
      rewrite <- H1 in H0.
      apply TransCI with (m2 := (ModalityCombine m1 mr)).
      rewrite H0. apply SFCI.
      rewrite RestitchVarModality with (p0 := p) (m' := m0) (pth0 := pth_to_lbl); auto.
      apply SFReplaceLabel.
      apply ModalityCombineProper. apply ModalityCombineProper.
      rewrite <- RestitchVarModality with (pth0 := pth_to_lbl); auto.
      apply VarModalityProper.
      pose proof (BeliefInProperContextIsProper (phi @ m) Gamma (provenProperContext pf2) (PathToIn pth_to_vary)).
      destruct H2; auto.
      pose proof (provenProperBelief pf2). inversion H2. inversion H4. auto.
      apply ModalityExtensionProper with (m1 := VarModality pth_to_lbl l2) (m2 := m1).
      pose proof (canInfluenceProper _ _ _ i). destruct H2; destruct H3.
      apply (C.ModProperApp mr m1 (ModalityCombine m1 mr) (eq_refl (ModalityCombine m1 mr)) H3).
      symmetry; auto.
      pose proof (canInfluenceProper _ _ _ i). destruct H2; destruct H3; auto.
      apply (C.ModProperApp mr m1 (ModalityCombine m1 mr) (eq_refl (ModalityCombine m1 mr)) H3).
      apply @Weakening with (Gamma := Gamma); auto.
      unfold pth_to_lbl'. rewrite <- VarModalityCombine. rewrite <- VarModalityCombine.
      simpl. rewrite <- RestitchVarModality with (pth0 := pth_to_lbl); auto.
      apply ProperContextCons.
      apply BeliefInProperContextIsProper with (Gamma := Gamma).
      exact (provenProperContext pf2).
      apply PathToIn. auto.
      apply (canInfluenceProper _ _ _ i).
      intros b' H2. apply InToPath; [exact BeliefEqDec |].
      apply PathToIn in H2.
      pose proof (CompatibleSupercontextSuper Δcsc).
      apply Permutation_in with (l' := (b1 :: WithoutPath Gamma pth)) in H2.
      destruct H2. left; auto. 
      right; apply H3. right; auto.
      apply PathToFront.
      apply CIWeakening with (Gamma := Delta).
      apply ProperContextCons.
      apply BeliefInProperContextIsProper with (Gamma := Gamma).
      exact (provenProperContext pf2).
      apply PathToIn. auto.
      apply (canInfluenceProper _ _ _ i).
      intros b H2; right; auto.
      exact i.
      rewrite <- NilPrincipalModalityLabel in e'.
      pose proof (eq_trans (eq_sym e) e'). inversion H0.
    - pose (pth_to_lbl' := PathToLabelInModalityCombine (PathToLabelInModalityCombine
                                                          (hereGLab l1) mr') mr).
      pose proof (eq_refl (ReplaceLabelInModality _ _ l2 pth_to_lbl')).
      unfold pth_to_lbl' in H0 at 1.
      rewrite RelabelPathToLabelCombine in H0 at 1.
      rewrite RelabelPathToLabelCombine in H0 at 1.
      simpl in H0.
      pose proof (ModalityExtension_spec _ _ _ (eq_sym Heq_anonymous)).
      rewrite <- RestitchVarModalityNil with (pth0 := pth_to_lbl) in H0; auto.
      rewrite <- H1 in H0.
      apply TransCI with (m2 := (ModalityCombine m1 mr)).
      rewrite H0. apply SFCI.
      rewrite RestitchVarModalityNil; auto.
      apply SFReplaceLabel.
      apply ModalityCombineProper. apply ModalityCombineProper.
      constructor. pose proof (provenProperBelief pf2). destruct H2. inversion H3; auto.
      apply ModalityExtensionProper with (m1 := VarModality pth_to_lbl l2) (m2 := m1).
      pose proof (canInfluenceProper _ _ _ i). destruct H2; destruct H3.
      apply (C.ModProperApp mr m1 (ModalityCombine m1 mr) (eq_refl (ModalityCombine m1 mr)) H3).
      auto.
      pose proof (canInfluenceProper _ _ _ i). destruct H2; destruct H3; auto.
      apply (C.ModProperApp mr m1 (ModalityCombine m1 mr) (eq_refl (ModalityCombine m1 mr)) H3).
      apply @Weakening with (Gamma := Gamma); auto.
      unfold pth_to_lbl'. rewrite <- VarModalityCombine. rewrite <- VarModalityCombine.
      simpl. rewrite <- RestitchVarModalityNil with (pth0 := pth_to_lbl); auto.
      apply ProperContextCons.
      apply BeliefInProperContextIsProper with (Gamma := Gamma).
      exact (provenProperContext pf2).
      apply PathToIn. auto.
      apply (canInfluenceProper _ _ _ i).
      intros b' H2. apply InToPath; [exact BeliefEqDec |].
      apply PathToIn in H2.
      pose proof (CompatibleSupercontextSuper Δcsc).
      apply Permutation_in with (l' := (b1 :: WithoutPath Gamma pth)) in H2.
      destruct H2. left; auto. 
      right; apply H3. right; auto.
      apply PathToFront.
      apply CIWeakening with (Gamma := Delta).
      apply ProperContextCons.
      apply BeliefInProperContextIsProper with (Gamma := Gamma).
      exact (provenProperContext pf2).
      apply PathToIn. auto.
      apply (canInfluenceProper _ _ _ i).
      intros b H2; right; auto.
      exact i.
  Defined.
  Next Obligation.
    clear Heq_ret.
    rewrite RestitchReplaceLabelVarModality in Gm1.
    pose proof (ModalityExtensionExtendedNone _ _ (ModalityAfterLabel pth_to_lbl)
                                              (eq_sym Heq_anonymous)).
    exfalso; eapply G'_creates_extensions_neg; eauto.
  Defined.
  Next Obligation.
    eapply CSCLVariance; eauto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. apply PeanoNat.Nat.le_max_l.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. apply PeanoNat.Nat.le_max_r.
  Defined.
  Next Obligation.
    clear Heq_anonymous.
    unfold eq_rect in *. simpl in *. clear Heq_anonymous0 Heq_anonymous1.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Le.le_n_S. apply PeanoNat.Nat.max_lub.
    transitivity (proof_size pf1); auto.
    transitivity (proof_size pf2); auto.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear  Heq_anonymous0 Heq_anonymous1 Heq_anonymous2.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. etransitivity; eauto.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous.
    pose proof Heq_pf as e_pf.
    apply JMeq_eq in e_pf. rewrite <- e_pf at 1. simpl.
    transitivity (proof_size pf1); [transitivity (proof_size pf1')|]; auto.
  Defined.
  Next Obligation.
    apply CSCPermL with (Delta1 := Δ1 ++ (b1 :: Δ2)).
    apply CSCUnion.
    pose proof (provenProperBelief pf2). destruct H0.
    apply CSCAtomic with (phi := l1 ⊑ l2) (m := VarModality pth_to_lbl l2);
      [constructor | exact H1 | exact H0 | exact Δcsc1].
    apply CSCPermR with (Gamma1 := b1 :: WithoutPath Gamma pth).
    eapply CSCLVariance with (phi := phi) (m := m); eauto.
    apply There. apply RepathWithoutPath with (p2 := pth_to_vary); auto.
    apply Rearrange with (Gamma := Gamma); auto.
    apply PathToFront. exact pf2.
    apply CSCPermR with (Gamma1 := b1 :: phi @ ReplaceLabelInModality m l1 l2 pth_to_lbl :: WithoutPath Gamma pth).
    apply CSCWeakening. exact Δcsc2.
    constructor.
    symmetry; apply PathToFront.
    symmetry; apply Permutation_middle.
  Defined.
  Next Obligation.
    pose proof (G'_atomic (formula_size (l1 ⊑ l2)) (l1 ⊑ l2) (VarModality pth_to_lbl l2)
                          m12 (flowsToAtomic l1 l2) Gm12).
    pose proof (i1).
    rewrite <- H0 in H1.
    pose proof i2.
    pose proof (ModalityExtension_spec _ _ _ (eq_sym Heq_anonymous)).
    rewrite H3 in H2.
    apply ExtCIResidual with (r := mr3 ++ mr2) in H1.
    rewrite ModalityCombineApp in H1.
    assert (ProperContext (b1 :: Δ1 ++ Δ2)).
    apply ProperContextCons. apply BeliefInProperContextIsProper with (Gamma := Gamma).
    apply (provenProperContext pf2). apply PathToIn; auto.
    apply AppProperContext. apply (canInfluenceProper _ _ _ i1).
    apply (canInfluenceProper _ _ _ i2).
    apply CIWeakening with (Delta := b1 :: Δ1 ++ Δ2) in H1; auto; 
    [| intros b H5; apply There;
       apply InToPath; [exact BeliefEqDec|]; apply in_or_app; left;
     apply PathToIn; exact H5].
    eapply TransCI; [exact H1 |].
    rewrite ModalityCombineApp in H2.
    apply CIWeakening with (Delta := b1 :: Δ1 ++ Δ2) in H2; auto;
      intros b H5; apply There;
       apply InToPath; [exact BeliefEqDec|]; apply in_or_app; right;
         apply PathToIn; exact H5.
    apply ProperModalityResidualApp.
    - eapply ModalityExtensionProper; eauto.
      eapply G_proper; eauto.
      pose proof (provenProperContext pf1).
      apply ConsProperContext in H4; destruct H4; auto.
    - pose proof (canInfluenceProper _ _ _ i2).
      destruct H4; destruct H5.
      apply C.ModProperApp with (m1 := m21) (m1' := mr2) in H5.
      destruct H5; auto. reflexivity.
  Defined.
  Next Obligation.
    destruct (PrincipalAtLabel pth_to_lbl) eqn:e;
      [rename f into p|];
      destruct (ModalityBeforeLabel pth_to_lbl) eqn:e'.
    - rewrite RestitchVarModality with (p0 := p) (m' := m0) in Heq_anonymous; auto.
      clear Heq_ret.
      rewrite ModalityRestitchReplaceLabel with (p0 := p) (m' := m0) in Gm21; auto.
      destruct (ModalityExtension (ModalityCombine (m0 ⋅ p⟨l2⟩) (ModalityAfterLabel pth_to_lbl)) m21) eqn:e2.
      pose proof (ModalityExtensionExtendedNone _ _ (ModalityAfterLabel pth_to_lbl) (eq_sym Heq_anonymous)).
      pose proof (eq_trans (eq_sym e2) H0). inversion H1.
      apply G'_creates_extensions_neg in Gm21. exfalso; apply Gm21; auto.
    - rewrite <- NilPrincipalModalityLabel in e'.
      pose proof (eq_trans (eq_sym e) e'). inversion H0.
    - rewrite NilPrincipalModalityLabel in e.
      pose proof (eq_trans (eq_sym e') e). inversion H0.
    - clear Heq_ret; rewrite ModalityRestitchReplaceLabelNil in Gm21; auto.
      rewrite RestitchVarModalityNil in Heq_anonymous; auto.
      destruct (ModalityExtension (ModalityCombine (⟨l2⟩) (ModalityAfterLabel pth_to_lbl)) m21) eqn:e2.
      pose proof (ModalityExtensionExtendedNone _ _ (ModalityAfterLabel pth_to_lbl) (eq_sym Heq_anonymous)).
      pose proof (eq_trans (eq_sym e2) H0). inversion H1.
      apply G'_creates_extensions_neg in Gm21. exfalso; apply Gm21; auto.
  Defined.
  Next Obligation.
    eapply CSCLVariance; eauto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. etransitivity; auto.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. apply PeanoNat.Nat.le_max_l.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous Heq_anonymous0.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. transitivity (Arith.max (proof_size pf3) (proof_size pf1)).
    apply PeanoNat.Nat.le_max_l. apply PeanoNat.Nat.le_max_r.
  Defined.
  Next Obligation.
    clear Heq_anonymous.
    unfold eq_rect in *. simpl in *. clear Heq_anonymous0 Heq_anonymous1.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Le.le_n_S. apply PeanoNat.Nat.max_lub.
    transitivity (proof_size pf2); auto.
    transitivity (Arith.max (proof_size pf3) (proof_size pf1)); auto.
    apply PeanoNat.Nat.max_lub; etransitivity; eauto.
  Defined.
  Next Obligation.
    pose proof (provenProperBelief pf3).
    destruct H1.
    apply CSCAtomic with (phi := canWrite p (LabelAtPrin pth_to_p))
                         (m := FwdModality pth_to_p q); auto.
    constructor.
  Defined.
  Next Obligation.
    destruct (G'_choice (formula_size phi) phi (ReplacePrinInModality pth_to_p q)) eqn:e1.
    apply G'_choice_spec; auto.
    exfalso; eapply G'_choice_formula_size_enough_neg; eauto.
  Defined.
  Next Obligation.
    destruct (G'_choice (formula_size phi) phi (ReplacePrinInModality pth_to_p q)) eqn:e1;
      [| exfalso; eapply G'_choice_formula_size_enough_neg; eauto].
    destruct (ModalityExtension (ModalityBeforePrin pth_to_p) m0) eqn:e2;
      [| inversion Heq_anonymous].
    destruct m3; [inversion Heq_anonymous |].
    destruct p0. rename f into q'. rename f0 into l2.
    destruct (termEqDec q q'); [| inversion Heq_anonymous];
      destruct (termEqDec (LabelAtPrin pth_to_p) l2); [| inversion Heq_anonymous].
    pose proof (ModalityExtension_spec _ _ _ e2) as e3. rewrite e3; simpl.
    inversion Heq_anonymous. rewrite <- ModalityCombineApp.
    apply ExtCIResidual.
    pose proof (provenProperBelief pf1); destruct H1.
    pose proof (provenProperBelief pf2); destruct H4.
    inversion H5.
    pose proof (ReplacePrinInModalityProper _ _ q pth_to_p H1 H8).
    pose proof (G'_choice_proper _ _ _ _ H3 H10 e1).
    pose proof (ModalityExtensionProper _ _ _ H11 e2).
    apply ProperModalityResidualConsInv in H12; apply H12.
    rewrite <- e0. rewrite <- RestitchFwdModality.
    clear Heq_ret. apply G_atomic in Gm2. rewrite <- e. rewrite Gm2; auto.
    constructor.
  Defined.
  Next Obligation.
    destruct (G'_choice (formula_size phi) phi (ReplacePrinInModality pth_to_p q)) eqn:e1;
      [| exfalso; eapply G'_choice_formula_size_enough_neg; eauto].
    destruct (ModalityExtension (ModalityBeforePrin pth_to_p) m0) eqn:e2.
    destruct m3.
    rewrite ModalityRestitchReplacePrin in e1.
    pose proof (G'_choice_spec _ _ _ _ e1).
    destruct (ModalityExtension (ModalityCombine (ModalityBeforePrin pth_to_p ⋅ q ⟨ LabelAtPrin pth_to_p ⟩) (ModalityAfterPrin pth_to_p)) m0) eqn:e3;
      [|exfalso; eapply G'_creates_extensions_neg; eauto].
    assert (ModalityCombine (ModalityBeforePrin pth_to_p ⋅ q⟨LabelAtPrin pth_to_p⟩)
                            (ModalityAfterPrin pth_to_p) =
            ModalityCombine (ModalityBeforePrin pth_to_p)
                            ((q, LabelAtPrin pth_to_p) ::  ModalityAfterPrin pth_to_p))
           by auto.
    rewrite H2 in e3. apply ModalityExtensionCombined in e3.
    pose proof (eq_trans (eq_sym e2) e3). inversion H3.
    destruct (ModalityExtension (ModalityCombine (ModalityBeforePrin pth_to_p ⋅ q ⟨ LabelAtPrin pth_to_p ⟩) (ModalityAfterPrin pth_to_p)) m0) eqn:e3.
    - assert (ModalityCombine (ModalityBeforePrin pth_to_p ⋅ q⟨LabelAtPrin pth_to_p⟩)
                              (ModalityAfterPrin pth_to_p) =
              ModalityCombine (ModalityBeforePrin pth_to_p)
                              ((q, LabelAtPrin pth_to_p) ::  ModalityAfterPrin pth_to_p))
        by auto.
      rewrite H1 in e3. apply ModalityExtensionCombined in e3.
      pose proof (eq_trans (eq_sym e2) e3). inversion H2.
      destruct p0 as [p2 l2].
      destruct (termEqDec q p2). destruct (termEqDec (LabelAtPrin pth_to_p) l2).
      inversion Heq_anonymous.
      inversion H4. exfalso; apply n; auto. inversion H4; exfalso; apply n; auto.
    - rewrite <- ModalityRestitchReplacePrin in e3.
      exfalso; eapply (G'_creates_extensions_neg _ _ (ReplacePrinInModality pth_to_p q) m0).
      apply G'_choice_spec; eauto. exact e3.
    -
      apply ModalityExtensionExtendedNone with (mr := (q, LabelAtPrin pth_to_p) :: ModalityAfterPrin pth_to_p) in e2.
      simpl in e2. rewrite <- ModalityRestitchReplacePrin in e2.
      apply G'_choice_spec in e1.
      exfalso; eapply (G'_creates_extensions_neg (formula_size phi) phi _ _ e1 e2); eauto.
  Defined.
    Next Obligation.
    pose proof (provenProperBelief pf2).
    destruct H0.
    apply CSCAtomic with (phi := canRead q (LabelAtPrin pth_to_p))
                         (m := FwdModality pth_to_p p); auto.
    constructor.
  Defined.
  Next Obligation.
    destruct (G'_choice (formula_size phi) phi (ReplacePrinInModality pth_to_p q)) eqn:e1.
    apply G'_choice_spec; auto.
    exfalso; eapply G'_choice_formula_size_enough_neg; eauto.
  Defined.
  Next Obligation.
    destruct (G'_choice (formula_size phi) phi (ReplacePrinInModality pth_to_p q)) eqn:e1;
      [| exfalso; eapply G'_choice_formula_size_enough_neg; eauto].
    rewrite <- ModalityCombineApp.
    pose proof (ModalityExtension_spec _ _ _ (eq_sym Heq_anonymous)).
    rewrite H0.
    apply TransCI with (m2 := ModalityCombine m mr').
    pose proof (ModalityRestitchPrin m p pth_to_p).
    rewrite H1 at 2. rewrite <- ModalityCombineApp.
    apply ExtCIResidual; [| apply ExtCIResidual]; auto.
    apply ModalityExtensionProper with (m1 := ReplacePrinInModality pth_to_p q) (m2 := m0);
      auto.
    eapply G'_choice_proper; eauto.
    pose proof (provenProperBelief pf1). destruct H2. exact H3.
    apply ReplacePrinInModalityProper.
    pose proof (provenProperBelief pf1); destruct H2; auto.
    pose proof (provenProperBelief pf2); destruct H2. inversion H3; auto.
    apply ModalityAfterPrinProper. pose proof (provenProperBelief pf1); destruct H2; auto.
    rewrite <- RestitchFwdModality. clear Heq_ret; apply G_atomic in Gm2. rewrite <- Gm2 in i.
    exact i.
    constructor.
    apply ExtCIResidual.
    apply ModalityExtensionProper with (m1 := ReplacePrinInModality pth_to_p q) (m2 := m0);
      auto.
    eapply G'_choice_proper; eauto.
    pose proof (provenProperBelief pf1). destruct H1. exact H2.
    apply ReplacePrinInModalityProper.
    pose proof (provenProperBelief pf1); destruct H1; auto.
    pose proof (provenProperBelief pf2); destruct H1. inversion H2; auto.
    apply SFCI.
    apply SFReplacePrin. pose proof (provenProperBelief pf1); destruct H1; auto.
    apply @Weakening with (Gamma := Gamma); auto. apply (canInfluenceProper _ _ _ i).
    pose proof (CompatibleSupercontextSuper Δcsc).
    intros b' H2. apply PathToIn in H2. apply H1 in H2. apply InToPath; [exact BeliefEqDec|].
    exact H2.
    apply @Weakening with (Gamma := Gamma); auto. apply (canInfluenceProper _ _ _ i).
    pose proof (CompatibleSupercontextSuper Δcsc).
    intros b' H2. apply PathToIn in H2. apply H1 in H2. apply InToPath; [exact BeliefEqDec|].
    exact H2.
  Defined.

  Next Obligation.
    destruct (G'_choice (formula_size phi) phi (ReplacePrinInModality pth_to_p q)) eqn:e1;
      [| exfalso; eapply G'_choice_formula_size_enough_neg; eauto].
    exfalso; eapply G'_creates_extensions_neg.
    apply G'_choice_spec in e1. exact e1. auto.
  Defined.
  Next Obligation.
    rewrite ModalityRestitchReplacePrin.
    pose proof (ModalityExtension_spec _ _ _ (eq_sym Heq_anonymous)).
    clear Heq_ret; rewrite H in Gm2.
    rewrite ModalityRestitchPrin with (pth := pth_to_p) in Gm2.
    apply G'_replace_base with
                       (m1 := ModalityCombine (ModalityBeforePrin pth_to_p ⋅ p ⟨LabelAtPrin pth_to_p⟩)
                                             (ModalityAfterPrin pth_to_p)).
    exact Gm2.
  Defined.
  Next Obligation.
    apply TransCI with (m2 := m2); auto.
    pose proof (ModalityExtension_spec _ _ _ (eq_sym Heq_anonymous)).
    rewrite H. apply ExtCIResidual.
    apply ModalityExtensionProper with (m1 := m) (m2 := m2).
    apply (canInfluenceProper _ _ _ i).
    exact (eq_sym Heq_anonymous).
    apply SFCI. apply SFReplacePrin.
    pose proof (provenProperBelief pf1); destruct H0; auto.
    all: apply @Weakening with (Gamma := Gamma); auto; [apply (canInfluenceProper _ _ _ i)|
    intros b' H0; apply InToPath; [exact BeliefEqDec|];
    apply (CompatibleSupercontextSuper Δcsc); apply PathToIn; auto].
  Defined.    
  Next Obligation.
    exfalso; eapply G'_creates_extensions_neg; [exact Gm2 | auto].
  Defined.    
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. etransitivity; eauto. 
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. repeat (etransitivity; eauto).
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous Heq_anonymous0 Heq_anonymous1.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    repeat (etransitivity; eauto).
  Defined.
  Next Obligation.
    eapply CSCFwdL; eauto.
  Defined.
  Next Obligation.
    pose proof (PathToSamePlaceSameA _ _ _ _ _ _ ptsp) as H; rewrite H.
    rewrite ModalityRestitchReplacePrin.
    rewrite ModalityRestitchPrin with (pth := pth_to_q) at 1.
    clear Heq_ret; rewrite ModalityRestitchReplacePrin in Gm1.
    rewrite ModalityRestitchReplacePrin in Heq_anonymous.
    pose proof (ModalityExtension_spec _ _ _ (eq_sym Heq_anonymous)).
    rewrite H0 in Gm1.
    eapply G'_replace_base; eauto.
  Defined.
  Next Obligation.
    apply TransCI with (m2 := ModalityCombine m1 mr); auto.
    apply ExtCIResidual.
    pose proof (canInfluenceProper _ _ _ i) as H;
      destruct H as [H H0]; destruct H0;
        eapply C.ModProperApp with (m := ModalityCombine m1 mr) (m1' := mr) (m1 := m1) in H0;
        [destruct H0; auto | reflexivity].
    pose proof(ModalityExtension_spec _ _ _ (eq_sym Heq_anonymous)).
    rewrite H.
    apply ExtCIResidual.
    apply ModalityExtensionProper with (m1 := ReplacePrinInModality pth_to_q p) (m2 := m1).
    pose proof (canInfluenceProper _ _ _ i) as H0;
      destruct H0 as [H1 H2]; destruct H2;
        eapply C.ModProperApp with (m := ModalityCombine m1 mr) (m1' := mr) (m1 := m1) in H0;
        [destruct H0; auto | reflexivity].
    symmetry; exact Heq_anonymous.
    apply SFCI.
    rewrite ModalityRestitchReplacePrin at 1.
    rewrite <- ModalityRestitchPrin at 1.
    assert (ProperContext Delta) by (apply (canInfluenceProper _ _ _ i)).
    assert (forall b, Path b Gamma -> Path b Delta).
    pose proof (CompatibleSupercontextSuper Δcsc).
    intros b H2. apply InToPath; [exact BeliefEqDec|]. apply H1.
    right; apply PathToIn; auto.
    apply SFReplacePrin; auto.
    pose proof (provenProperContext pf2).
    pose proof (BeliefInProperContextIsProper (phi @ m) Gamma H2 (PathToIn pth_to_fwd)).
    destruct H3; auto.
    apply @Weakening with (Gamma := Gamma); auto.
    apply @Weakening with (Gamma := Gamma); auto.
  Defined.
  Next Obligation.
    exfalso. eapply G'_creates_extensions_neg; [exact Gm1| symmetry; exact Heq_anonymous].
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. etransitivity; eauto.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. apply PeanoNat.Nat.le_max_l.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous1 Heq_anonymous.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm.
    transitivity (Arith.max (proof_size pf3) (proof_size pf1)); auto.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous Heq_anonymous1 Heq_anonymous2.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply le_n_S. apply PeanoNat.Nat.max_lub.
    etransitivity; eauto.
    apply PeanoNat.Nat.max_lub; etransitivity; eauto;
      transitivity (Arith.max (proof_size pf3) (proof_size pf1)); auto.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous1 Heq_anonymous2 Heq_anonymous3. 
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm.
    transitivity (Arith.max (proof_size pf3) (proof_size pf1)); auto.
    etransitivity; eauto.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous Heq_anonymous1 Heq_anonymous2 Heq_anonymous3. 
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    transitivity (Arith.max (proof_size pf3) (proof_size pf1)); auto.
    transitivity (proof_size pf1); auto. transitivity (proof_size pf1'); auto.
  Defined.
  Next Obligation.
    clear H0 H Heq_anonymous Heq_anonymous0 Heq_anonymous1 Heq_anonymous2 Heq_anonymous3 Heq_anonymous5.
    pose proof (provenProperBelief pf3) as H0; destruct H0 as [H0 H1].
    pose proof (CSCAtomic Δ1 Gamma _ _ b2 (canRAtomic p (LabelAtPrin pth_to_q)) H1 H0 Δcsc1).
    pose proof (CSCWeakening _ _ _ b1 Δcsc2).
    apply CSCPermR with (Gamma2 := phi @ ReplacePrinInModality pth_to_q p :: Gamma) in H2.
    eapply CSCFwdL in H2; eauto.
    apply CSCPermL with (Delta1 := Δ1 ++ (b1 :: Δ2)).
    apply CSCUnion; auto.
    symmetry; apply Permutation_middle.
    transitivity (phi @ ReplacePrinInModality pth_to_q p :: b1 :: WithoutPath Gamma pth).
    apply perm_swap.
    apply perm_skip. symmetry. apply PathToFront.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *;
      clear Heq_anonymous0 Heq_anonymous1 Heq_anonymous2 Heq_anonymous3 Heq_anonymous5
            Heq_ret1 Heq_ret2.
    assert (ProperContext (b1 :: Δ1 ++ Δ2))
      by (apply ProperContextCons;
          [apply BeliefInProperContextIsProper with (Gamma := Gamma);
           [exact (provenProperContext pf2) | exact (PathToIn pth)]
          | apply AppProperContext; eapply canInfluenceProper; eauto]).
    apply TransCI with (m2 := ModalityCombine m21 mr2).
    - pose proof (ModalityExtension_spec _ _ _ (eq_sym Heq_anonymous)).
      rewrite H2. rewrite ModalityCombineApp.
      rewrite app_assoc.
      rewrite <- ModalityCombineApp with (m0 := mr1 ++ ModalityAfterPrin pth_to_q)
                                        (m1 := mr2' ++ mr2).
      apply ExtCIResidual.
      -- apply ProperModalityResidualApp.
         apply ModalityExtensionProper with (m1 := ReplacePrinInModality pth_to_q p) (m2 := m21); [| symmetry; apply Heq_anonymous].
         fold (G (phi @ (ReplacePrinInModality pth_to_q p)) m21) in Gm21.
         apply G_proper in Gm21; auto.
         eapply BeliefInProperContextIsProper. apply (provenProperContext pf1).
         left; reflexivity.
         pose proof (canInfluenceProper _ _ _ i2).
         destruct H3. destruct H4.
         apply C.ModProperApp with (m1' := mr2) (m1 := m21) in H4; [| reflexivity].
         destruct H4; auto.
      -- apply TransCI with (m2 := ReplacePrinInModality pth_to_q q).
         --- rewrite ModalityRestitchReplacePrin. rewrite <- ModalityCombineApp.
             apply ExtCIResidual. apply ModalityAfterPrinProper.
             pose proof (BeliefInProperContextIsProper (phi @ m) Gamma (provenProperContext pf2)
                                                       (PathToIn pth_to_fwd)).
             destruct H3; auto.
             rewrite <- RestitchFwdModality.
             rewrite Gm12. apply CIWeakening with (Gamma := Δ1); auto.
             intros b H3. apply InToPath; [exact BeliefEqDec|]. right.
             apply in_or_app. left. apply PathToIn. exact H3.
         --- rewrite ModalityRestitchReplacePrin. rewrite <- ModalityRestitchPrin.
             apply SFCI. apply SFReplacePrin; auto.
             apply (BeliefInProperContextIsProper (phi @ m) Gamma (provenProperContext pf2)
                                                  (PathToIn pth_to_fwd)).
             apply @Weakening with (Gamma := Gamma); auto.
             intros b' H3. apply There. apply InToPath; [exact BeliefEqDec|].
             apply in_or_app; left. eapply CompatibleSupercontextSuper; [exact Δcsc1|].
             apply PathToIn; auto.
             apply @Weakening with (Gamma := Gamma); auto.
             intros b' H3. apply There. apply InToPath; [exact BeliefEqDec|].
             apply in_or_app; left. eapply CompatibleSupercontextSuper; [exact Δcsc1|].
             apply PathToIn; auto.
    - apply CIWeakening with (Gamma := Δ2); auto.
      intros b H2. apply InToPath; [exact BeliefEqDec|].
      right. apply in_or_app; right. apply PathToIn; auto.
  Defined.
  Next Obligation.
    exfalso; eapply G'_creates_extensions_neg; [apply Gm21 | symmetry; exact Heq_anonymous].
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous1 Heq_anonymous2.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm.
    transitivity (proof_size pf1); auto.
    etransitivity; eauto.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous Heq_anonymous1 Heq_anonymous2.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    repeat (etransitivity; eauto).
  Defined.
  Next Obligation.
    pose proof (provenProperBelief pf2) as H0; destruct H0 as [H0 H1].
    pose proof (CSCAtomic Δ1 Gamma _ _ b2 (canWAtomic q (LabelAtPrin pth_to_q)) H1 H0 Δcsc1).
    pose proof (CSCWeakening _ _ _ b1 Δcsc2).
    apply CSCPermR with (Gamma2 := phi @ ReplacePrinInModality pth_to_q p :: Gamma) in H3.
    eapply CSCFwdL in H3; eauto.
    apply CSCPermL with (Delta1 := Δ1 ++ (b1 :: Δ2)).
    apply CSCUnion; auto.
    symmetry; apply Permutation_middle.
    transitivity (phi @ ReplacePrinInModality pth_to_q p :: b1 :: WithoutPath Gamma pth).
    apply perm_swap.
    apply perm_skip. symmetry. apply PathToFront.
  Defined.
  Next Obligation.
    apply TransCI with (m2 := ModalityCombine m21 mr2).
    - pose proof (ModalityExtension_spec _ _ _ (eq_sym Heq_anonymous)).
      rewrite H0. rewrite ModalityCombineApp.
      rewrite app_assoc.
      rewrite <- ModalityCombineApp with (m0 := mr1 ++ ModalityAfterPrin pth_to_q)
                                        (m1 := mr2' ++ mr2).
      apply ExtCIResidual.
      -- apply ProperModalityResidualApp.
         apply ModalityExtensionProper with (m1 := ReplacePrinInModality pth_to_q p) (m2 := m21); [| symmetry; apply Heq_anonymous].
         clear Heq_ret2. apply G_proper in Gm21; auto.
         eapply BeliefInProperContextIsProper. apply (provenProperContext pf1).
         left; reflexivity.
         pose proof (canInfluenceProper _ _ _ i2).
         destruct H1. destruct H2.
         apply C.ModProperApp with (m1' := mr2) (m1 := m21) in H2; [| reflexivity].
         destruct H2; auto.
      -- rewrite ModalityRestitchReplacePrin.
         rewrite <- ModalityCombineApp.
         apply ExtCIResidual. apply ModalityAfterPrinProper.
         pose proof (BeliefInProperContextIsProper (phi @ m) Gamma (provenProperContext pf)
                                                   (PathToIn pth_to_fwd)).
         destruct H1; auto.
         rewrite <- RestitchFwdModality.
         clear Heq_ret1 Heq_anonymous4 Heq_anonymous2 Heq_anonymous1.
         apply G_atomic in Gm12; [|constructor]. rewrite Gm12.
         apply CIWeakening with (Gamma := Δ1).
         apply ProperContextCons. apply BeliefInProperContextIsProper with (Gamma := Gamma).
         apply (provenProperContext pf). apply PathToIn. auto.
         apply AppProperContext; eapply canInfluenceProper; eauto.
         intros b H1. apply There. apply PathSplit. left. exact H1.
         exact i1.
    - apply CIWeakening with (Gamma := Δ2).
      apply ProperContextCons. apply BeliefInProperContextIsProper with (Gamma := Gamma).
      apply (provenProperContext pf). apply PathToIn. auto.
      apply AppProperContext; eapply canInfluenceProper; eauto.
      intros b H1. apply There. apply PathSplit. right; exact H1.
      exact i2.
  Defined.            
  Next Obligation.
    exfalso; eapply G'_creates_extensions_neg; [exact Gm21 | symmetry; exact Heq_anonymous].
  Defined.
  Next Obligation.
    eapply CSCFwdL; eauto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. apply PeanoNat.Nat.le_max_l.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. apply PeanoNat.Nat.le_max_r.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous.
    clear Heq_anonymous0.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Le.le_n_S. apply PeanoNat.Nat.max_lub.
    transitivity (proof_size pf1); auto.
    transitivity (proof_size pf2); auto.
  Defined.
  Next Obligation.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. apply PeanoNat.Nat.le_max_l.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous.
    apply JMeq_eq in Heq_pf. rewrite <- Heq_pf. simpl.
    apply Lt.le_lt_n_Sm. apply PeanoNat.Nat.le_max_r.
  Defined.
  Next Obligation.
    unfold eq_rect in *; simpl in *. clear Heq_anonymous.
    clear Heq_anonymous0.
    apply JMeq_eq in Heq_pf; rewrite <- Heq_pf; simpl.
    apply Le.le_n_S. apply PeanoNat.Nat.max_lub.
    transitivity (proof_size pf1); auto.
    transitivity (proof_size pf2); auto.
  Defined.
    
  Theorem Noninterference : forall (Gamma : Context) (b1 b2 : Belief) (pth : Path b1 Gamma),
      Gamma ⊢ b2 ->
      ((WithoutPath Gamma pth) ⊢ b2 +
       sigT2 (fun Delta : Context => Delta ≪ Gamma ⊢csc b2)
             (fun Delta : Context =>
                sigT2 (fun m1 : Modality => G b1 m1)
                      (fun m1 : Modality =>
                         sigT2 (fun m2 => G b2 m2)
                               (fun m2 =>
                                  sigT (fun m1' : ModalityResidual =>
                                          Delta ⊢inf (ModalityCombine m1 m1') ⇛ m2))))).
  Proof.
    intros Gamma b1 b2 pth H.
    pose proof (Noninterference' Gamma b1 b2 pth H).
    destruct H0; [left | right]; auto.
    destruct s; auto.
    destruct n. exists Delta; auto. exists m1; auto. exists m2; auto. exists mr; auto.
  Qed.
  
End Noninterference.