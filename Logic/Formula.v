Require Export Term.
Require Import Base.Lists.
Require Import Tactics.TermEquality.
Require Import Tactics.TermHasSortNoFormulas.

Require Import Coq.Program.Wf.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.

Module Type Formula (G : GroundInfo) (GTerm : Term G).
  Import G.
  Import GTerm.

  Open Scope term_scope.

  Inductive flafolFormula : Set :=
    TT : flafolFormula
  | FF : flafolFormula
  | varFormula : formulaVar -> flafolFormula
  | flowsto : flafolTerm -> flafolTerm -> flafolFormula
  | rel : forall R : G.relSym, list flafolTerm -> flafolFormula
  | canRead : flafolTerm -> flafolTerm -> flafolFormula
  | canWrite : flafolTerm -> flafolTerm -> flafolFormula
  | and : flafolFormula -> flafolFormula -> flafolFormula
  | or : flafolFormula -> flafolFormula -> flafolFormula
  | implies : flafolFormula -> flafolTerm -> flafolFormula -> flafolFormula
  | flafolForall : G.sort -> flafolFormula -> flafolFormula
  | flafolExists : G.sort -> flafolFormula -> flafolFormula
  | says : flafolTerm -> flafolTerm -> flafolFormula -> flafolFormula.

  Notation "l ⊑ l'" := (flowsto l l') (at level 19) : formula_scope.
  (* This notation comes from modal logic. *)
  Notation "p □ ⟨ ℓ ⟩ phi" := (says p ℓ phi) (at level 20) : formula_scope.
  Infix "&" := and (at level 21) : formula_scope.
  Infix "⊕" := or (at level 21) : formula_scope.
  Notation "phi ==⟨ l ⟩> psi" := (implies phi l psi) (at level 22) : formula_scope.
  Notation "∀ s ; phi" := (flafolForall s phi) (at level 23) : formula_scope.
  Notation "∃ s ; phi" := (flafolExists s phi) (at level 23) : formula_scope.

  Open Scope formula_scope.

  Hint Resolve list_eq_dec termEqDec sortEqDec varEqDec relSymEqDec formulaVarEqDec: eq_dec.
  Definition formulaEqDec : forall phi psi : flafolFormula, {phi = psi} + {phi <> psi}.
    decide equality; auto with eq_dec.
  Defined.
  
  Hint Resolve formulaEqDec : eq_dec.
  Fixpoint open_formula_rec (n : nat) (phi : flafolFormula) (t : flafolTerm) : flafolFormula :=
    match phi with
    | varFormula X => phi
    | TT => phi
    | FF => phi
    | ℓ₁ ⊑ ℓ₂ => (open_term_rec n ℓ₁ t) ⊑ (open_term_rec n ℓ₂ t)
    | canRead p ℓ => canRead (open_term_rec n p t) (open_term_rec n ℓ t)
    | canWrite p ℓ => canWrite (open_term_rec n p t) (open_term_rec n ℓ t)
    | p □ ⟨ℓ⟩ psi =>
      let p' := (open_term_rec n p t) in
      let ℓ' := (open_term_rec n ℓ t) in
      p' □ ⟨ ℓ'⟩ (open_formula_rec n psi t)
    | rel R args => rel R (map (fun t' => open_term_rec n t' t) args)
    | psi & chi => (open_formula_rec n psi t) & (open_formula_rec n chi t)
    | psi ⊕ chi => (open_formula_rec n psi t) ⊕ (open_formula_rec n chi t)
    | psi ==⟨l⟩> chi => (open_formula_rec n psi t) ==⟨open_term_rec n l t⟩> (open_formula_rec n chi t)
    | ∀ s; psi => ∀ s; (open_formula_rec (S n) psi t)
    | ∃ s; psi => ∃ s; (open_formula_rec (S n) psi t)       
    end.


  Fixpoint formula_size (f : flafolFormula) : nat :=
    match f with
      flowsto _ _ => 1
    | varFormula _ => 1
    | rel s l => 1
    | TT => 1
    | FF => 1
    | and f1 f2 => 1 + max (formula_size f1) (formula_size f2)
    | or f1 f2 => 1 + max (formula_size f1) (formula_size f2)
    | implies f1 _ f2 => 1 + max (formula_size f1) (formula_size f2)
    | flafolForall x f => 1 + (formula_size f)
    | flafolExists x f => 1 + (formula_size f)
    | says p l1 f => 1 + (formula_size f)
    | canRead _ _ => 1
    | canWrite _ _ => 1
    end.


   Definition open_formula (phi : flafolFormula) (t : flafolTerm) : flafolFormula :=
     open_formula_rec 0 phi t.

   Inductive lc_formula : flafolFormula -> Prop :=
     lcVF : forall X : formulaVar, lc_formula (varFormula X)
   | lcTT : lc_formula TT
   | lcFF : lc_formula FF
   | lcFlowsTo : forall lab1 lab2, lc_term lab1 -> lc_term lab2 -> lc_formula (lab1 ⊑ lab2)
   | lcCanRead : forall p lab, lc_term p -> lc_term lab -> lc_formula (canRead p lab)
   | lcCanWrite : forall p lab, lc_term p -> lc_term lab -> lc_formula (canWrite p lab)
   | lcSays : forall p lab phi, lc_term p -> lc_term lab ->  lc_formula phi ->
                            lc_formula (p □ ⟨ lab ⟩ phi)
   | lcRel : forall R args, (forall t, In t args -> lc_term t) -> lc_formula (rel R args)
   | lcAnd : forall phi psi, lc_formula phi -> lc_formula psi -> lc_formula (phi & psi)
   | lcOr : forall phi psi, lc_formula phi -> lc_formula psi -> lc_formula (phi ⊕ psi)
   | lcImp : forall phi l psi, lc_formula phi -> lc_term l -> lc_formula psi
                      -> lc_formula (phi ==⟨l⟩> psi)
   | lcForall : forall phi sigma L, (forall x, ~ (In x L) -> ⊢s varTerm x ::: sigma ->
                               lc_formula (open_formula phi (varTerm x)))
                         -> lc_formula (∀ sigma; phi)
   | lcExists : forall phi sigma L, (forall x, ~ (In x L) -> ⊢s varTerm x ::: sigma ->
                               lc_formula (open_formula phi (varTerm x)))
                         -> lc_formula (∃ sigma; phi).

   Lemma open_formula_commute_rec : forall phi t1 t2 n1 n2, beq_nat n1 n2 = false -> lc_term t1 -> lc_term t2 -> open_formula_rec n2 (open_formula_rec n1 phi t1) t2 = open_formula_rec n1 (open_formula_rec n2 phi t2) t1.
     
     induction phi; simpl; intros; subst; try (econstructor; eauto; fail).
     - rewrite open_term_commute_rec; auto.
       f_equal.
       rewrite open_term_commute_rec; auto.
     - repeat rewrite map_isFunctorial.
       f_equal.
       induction l; simpl; auto.
       rewrite open_term_commute_rec; auto.
       rewrite IHl; auto.
     - rewrite open_term_commute_rec; auto.
       f_equal.
       rewrite open_term_commute_rec; auto.
     - rewrite open_term_commute_rec; auto.
       f_equal.
       rewrite open_term_commute_rec; auto.
     - rewrite IHphi1; auto.
       rewrite IHphi2; auto.
     - rewrite IHphi1; auto.
       rewrite IHphi2; auto.
     - f_equal; auto; apply open_term_commute_rec; auto.
     - rewrite IHphi; auto.
     - rewrite IHphi; auto.
     - rewrite open_term_commute_rec; auto.
       f_equal.
       rewrite open_term_commute_rec; auto.
       apply IHphi; auto.      
   Qed.
   
    Lemma OpenFormulaSize' : forall phi t n, formula_size (open_formula_rec n phi t) = formula_size phi.
    Proof.
      intros phi; induction phi; intros t n; simpl; auto.
    Qed.
    Lemma OpenFormulaSize : forall phi t, formula_size (open_formula phi t) = formula_size phi.
    Proof.
      intros phi t; unfold open_formula; apply OpenFormulaSize'.
    Qed.
   Inductive freeInFormula : var -> flafolFormula -> Prop :=
   | freeInFlowsto1  :forall (x : var) (ℓ₁ ℓ₂ : flafolTerm),
       x ∈FVT ℓ₁ -> freeInFormula x (ℓ₁ ⊑ ℓ₂)
   | freeInFlowsto2 : forall (x : var) (ℓ₁ ℓ₂ : flafolTerm),
       x ∈FVT ℓ₂ -> freeInFormula x (ℓ₁ ⊑ ℓ₂)
   | freeInCanWriteP : forall (x : var) (p ℓ : flafolTerm),
       x ∈FVT p -> freeInFormula x (canWrite p ℓ)
   | freeInCanWriteL : forall (x : var) (p ℓ : flafolTerm),
       x ∈FVT ℓ -> freeInFormula x (canWrite p ℓ)
   | freeInCanReadP : forall (x : var) (p ℓ : flafolTerm),
       x ∈FVT p -> freeInFormula x (canRead p ℓ)
   | freeInCanReadL : forall (x : var) (p ℓ : flafolTerm),
       x ∈FVT ℓ -> freeInFormula x (canRead p ℓ)
   | freeInSaysP : forall (x : var) (p ℓ : flafolTerm) (phi : flafolFormula),
       x ∈FVT p -> freeInFormula x (p □ ⟨ ℓ ⟩ phi)
   | freeInSaysL : forall (x : var) (p ℓ : flafolTerm) (phi : flafolFormula),
       x ∈FVT ℓ -> freeInFormula x (p □ ⟨ ℓ ⟩ phi)
   | freeInSaysF : forall (x : var) (p ℓ : flafolTerm) (phi : flafolFormula),
       freeInFormula x phi -> freeInFormula x (p □ ⟨ ℓ ⟩ phi)
   | freeInRel : forall (x : var) (R : relSym) (args : list flafolTerm) (t : flafolTerm),
       In t args -> x ∈FVT t -> freeInFormula x (rel R args)
   | freeInAndL : forall (x : var) (phi psi : flafolFormula),
       freeInFormula x phi -> freeInFormula x (phi & psi)
   | freeInAndR : forall (x : var) (phi psi : flafolFormula),
       freeInFormula x psi -> freeInFormula x (phi & psi)
   | freeInOrL : forall (x : var) (phi psi : flafolFormula),
       freeInFormula x phi -> freeInFormula x (phi ⊕ psi)
   | freeInOrR : forall (x : var) (phi psi : flafolFormula),
       freeInFormula x psi -> freeInFormula x (phi ⊕ psi)
   | freeInImpL : forall (x : var) (phi psi : flafolFormula) (l : flafolTerm),
       freeInFormula x phi -> freeInFormula x (phi ==⟨l⟩> psi)
   | freeInImpLabel : forall (x : var) (phi psi : flafolFormula) (l : flafolTerm),
       x ∈FVT l -> freeInFormula x (phi ==⟨l⟩> psi)
   | freeInImpR : forall (x : var) (phi psi : flafolFormula) (l : flafolTerm),
       freeInFormula x psi -> freeInFormula x (phi ==⟨l⟩> psi)
   | freeInForall : forall (x : var) (s : G.sort) (phi : flafolFormula),
       freeInFormula x phi -> freeInFormula x (∀ s; phi)
   | freeInExists : forall (x : var) (s : G.sort) (phi : flafolFormula),
       freeInFormula x phi -> freeInFormula x (∃ s; phi).

   Infix "∈FVF" := freeInFormula (at level 40) : formula_scope.
   Notation "x ∉FVF t" := (~ freeInFormula x t) (at level 40) : formula_scope.
   Import ListNotations.
   Fixpoint varsInFormula (phi : flafolFormula) : list var :=
     match phi with
     | varFormula _ => []
     | TT => []
     | FF => []
     | lab1 ⊑ lab2 => (varsInTerm lab1) ++ (varsInTerm lab2)
     | canRead p lab => (varsInTerm p) ++ (varsInTerm lab)
     | canWrite p lab => (varsInTerm p) ++ (varsInTerm lab)
     | p □ ⟨lab⟩ phi => (varsInTerm p) ++ (varsInTerm lab) ++
                                        (varsInFormula phi)
     | rel _ args => flat_map varsInTerm args
     | psi & chi => (varsInFormula psi) ++ (varsInFormula chi)
     | psi ⊕ chi => (varsInFormula psi) ++ (varsInFormula chi)
     | psi ==⟨l⟩> chi => (varsInFormula psi) ++ (varsInTerm l) ++ (varsInFormula chi)
     | flafolForall s psi => varsInFormula psi
     | flafolExists s psi => varsInFormula psi
     end.

    Obligation Tactic := Tactics.program_simpl; simpl; try (match goal with
      | [ |- ?a < S (Nat.max ?a ?b) ] =>
        apply PeanoNat.Nat.lt_succ_r; apply PeanoNat.Nat.le_max_l
      | [ |- ?b < S (Nat.max ?a ?b) ] =>
        apply PeanoNat.Nat.lt_succ_r; apply PeanoNat.Nat.le_max_r
      end).

    Program Fixpoint ClosedFormulaInduction (P : flafolFormula -> Type)
            (varCase : forall X, P (varFormula X))
            (trueCase : P TT)
            (falseCase : P FF)
            (flowsCase : forall lab1 lab2, P (lab1 ⊑ lab2))
            (canReadCase : forall p lab, P (canRead p lab))
            (canWriteCase : forall p lab, P (canWrite p lab))
            (saysCase : forall p lab phi, P phi -> P (p □ ⟨ lab ⟩ phi))
            (relCase : forall R args, P (rel R args))
            (andCase : forall phi psi, P phi -> P psi -> P (phi & psi))
            (orCase : forall phi psi, P phi -> P psi -> P (phi ⊕ psi))
            (impCase : forall phi l psi, P phi -> P psi -> P (phi ==⟨l⟩> psi))
            (forallCase : forall sigma psi L, (forall x, (~ In x L) -> ⊢s varTerm x ::: sigma ->
                                         P (open_formula psi (varTerm x)))
                                 -> P (∀ sigma; psi))
            (existsCase : forall sigma psi L, (forall x, (~ In x L) -> ⊢s varTerm x ::: sigma ->
                                         P (open_formula psi (varTerm x)))
                                 -> P (∃ sigma; psi))
            (phi : flafolFormula) { measure (formula_size phi) }
     : P phi :=
      let rec := ClosedFormulaInduction _ _ _ _ _ _ _ _ _ _ _ _ _ _ in
     match phi with
     | varFormula X => varCase X
     | TT => trueCase
     | FF => falseCase
     | lab1 ⊑ lab2 => flowsCase lab1 lab2
     | canRead p lab => canReadCase p lab
     | canWrite p lab => canWriteCase p lab
     | p □ ⟨lab⟩ psi => saysCase p lab psi (rec psi _)
     | rel R args => relCase R args
     | psi & chi => andCase psi chi (rec psi _) (rec chi _)
     | psi ⊕ chi => orCase psi chi (rec psi _) (rec chi _)
     | psi ==⟨l⟩> chi => impCase psi l chi (rec psi _) (rec chi _)
     | ∀ sigma; psi => forallCase sigma psi (varsInFormula psi) (fun x i H => rec (open_formula psi (varTerm x)) _)
     | ∃ sigma; psi => existsCase sigma psi (varsInFormula psi) (fun x i H => rec (open_formula psi (varTerm x)) _)
     end.
   Next Obligation.
     rewrite OpenFormulaSize; apply PeanoNat.Nat.lt_succ_diag_r.
   Defined.
   Next Obligation.
     rewrite OpenFormulaSize; apply PeanoNat.Nat.lt_succ_diag_r.
   Defined.
   (* 
     This is the equivalent of a type system.
     Essentially, this makes sure that all of constituant terms are of the correct type.
   *)
   Inductive wellFormedFormula : flafolFormula -> Prop :=
     varWF : forall X : formulaVar, wellFormedFormula (varFormula X)
   | TTWF : wellFormedFormula TT
   | FFWF : wellFormedFormula FF
   | flowstoWF : forall (ℓ₁ ℓ₂ : flafolTerm),
       ⊢s ℓ₁ ::: Label -> ⊢s ℓ₂ ::: Label ->
       wellFormedFormula (ℓ₁ ⊑ ℓ₂)
   | canReadWF : forall (p ℓ : flafolTerm),
       ⊢s p ::: Principal -> ⊢s ℓ ::: Label ->
       wellFormedFormula (canRead p ℓ)
   | canWriteWF: forall (p ℓ : flafolTerm),
       ⊢s p ::: Principal -> ⊢s ℓ ::: Label ->
       wellFormedFormula (canWrite p ℓ)
   | saysWF : forall (p ℓ : flafolTerm) (phi : flafolFormula),
       ⊢s p ::: Principal -> ⊢s ℓ ::: Label ->
       wellFormedFormula phi ->
       wellFormedFormula (p □ ⟨ ℓ ⟩ phi)
   | RelWF : forall (R : relSym) (args : list flafolTerm),
       hasSorts args (relTypes R) -> wellFormedFormula (rel R args)
   | andWF : forall phi psi : flafolFormula,
       wellFormedFormula phi -> wellFormedFormula psi -> wellFormedFormula (phi & psi)
   | orWF : forall phi psi : flafolFormula,
       wellFormedFormula phi -> wellFormedFormula psi -> wellFormedFormula (phi ⊕ psi)
   | impliesWF : forall (phi psi : flafolFormula) (l : flafolTerm), 
       wellFormedFormula phi -> ⊢s l ::: Label -> wellFormedFormula psi ->
       wellFormedFormula (phi ==⟨l⟩> psi)
   | forallWF : forall (sigma : G.sort) (phi : flafolFormula) (L : list var),
       (forall x, ~(In x L) -> ⊢s (varTerm x) ::: sigma -> wellFormedFormula (open_formula phi (varTerm x)))
       -> wellFormedFormula (∀ sigma; phi)
   | existsWF : forall (sigma : G.sort) (phi : flafolFormula) (L : list var),
       (forall x, ~(In x L) -> ⊢s (varTerm x) ::: sigma -> wellFormedFormula (open_formula phi (varTerm x)))
       -> wellFormedFormula (∃ sigma; phi).

   Notation "⊢wff" := wellFormedFormula : formula_scope.

   Definition freeInFormulaDec : forall (x : var) (phi : flafolFormula), {x ∈FVF phi} + {x ∉FVF phi}.
   Proof.
     intros x phi.
     induction phi; try (right; intro H; inversion H; auto; fail).
     all: repeat match goal with
                 | [ X : var, Phi : flafolFormula |- _ ] =>
                   match goal with
                   | [ _ : X ∈FVF Phi |- {X ∈FVF ∀ ?s; Phi} + {X ∉FVF ∀ ?s; Phi} ] =>
                     let E := fresh "e" in
                     let N := fresh "n" in
                     destruct (varEqDec X V) as [E | N];
                       [ right; intro H; inversion H; auto; fail
                       | left; constructor; auto; fail]
                   | [ _ : X ∈FVF Phi |- {X ∈FVF ∃ ?s; Phi} + {X ∉FVF ∃ ?s; Phi} ] =>
                     let E := fresh "e" in
                     let N := fresh "n" in
                     destruct (varEqDec X V) as [E | N];
                       [ right; intro H; inversion H; auto; fail
                       | left; constructor; auto; fail]
                   | [ _ : X ∈FVF Phi |- _ ] =>
                     left; try (constructor; auto; fail)
                   | [ _ : X ∉FVF Phi |- _ ] => fail 1
                   | [ IH : {X ∈FVF Phi} + {X ∉FVF Phi} |- _ ] => destruct IH
                   end
                 | [ X : var, T : flafolTerm |- _ ] =>
                   match goal with
                   | [ _ : X ∈FVT T |- {X ∈FVF _} + {X ∉FVF _} ] => left; try (constructor; auto; fail)
                   | [ _ : X ∉FVT T |- _ ] => fail 1
                   | [ |- {X ∈FVF _} + {X ∉FVF _} ] => destruct(freeInTermDec X T)
                   end
                 end;
       try (right; intro H; inversion H; auto; fail).
     destruct (freeInTermListDec x l); [left | right].
     destruct e as [t H]; destruct H as [HIn HFVT]; apply freeInRel with (t := t); auto.
     intro H; inversion H; unfold not in n; apply n with (t := t); auto.     
   Qed.

   Theorem FreeVarsInFormula : forall (x : var) (phi : flafolFormula),
       x ∈FVF phi -> In x (varsInFormula phi).
   Proof.
     intros x phi; revert x; induction phi; intros x H; simpl; auto;
       repeat match goal with
       | [ |- False ] => inversion H
       | [ |- In ?x (?l1 ++ ?l2) ] => apply in_or_app
       end; try (inversion H; auto; fail).
     - inversion H; [left |right]; apply varsInTermFVT; auto.
     - inversion H; apply varsInTermFVT'; exists t; auto.
     - inversion H; [left | right]; apply varsInTermFVT; auto.
     - inversion H; [left | right]; apply varsInTermFVT; auto.
     - inversion H; [left; apply IHphi1; auto | |];
         right; apply in_or_app; [left; auto; apply varsInTermFVT; auto |].
       right; auto; apply varsInTermFVT; auto.
     - inversion H; [left; auto; apply varsInTermFVT; auto | |];
         right; apply in_or_app; [left; auto; apply varsInTermFVT; auto | ];
           right; auto; apply varsInTermFVT; auto.
   Qed.
   
   Definition freshInFormula (phi : flafolFormula) (sigma : sort) :=
     freshVar (varsInFormula phi) sigma.

   Lemma freshInFormulaOfSort : forall (phi : flafolFormula) (sigma : sort),
       VarSort (freshInFormula phi sigma) = sigma.
   Proof.
     intros phi sigma; unfold freshInFormula; apply freshVarSameSort.
   Qed.

   Lemma freshInFormulaIsFresh : forall (phi : flafolFormula) (sigma : sort),
       (freshInFormula phi sigma) ∉FVF phi.
   Proof.
     intros phi sigma; unfold freshInFormula; intro H;
       apply FreeVarsInFormula in H; eapply freshVarNotIn; eauto.
   Qed.

   (* NOTE: We're substituting _term_ variables, not _formula_ variables *)
   Fixpoint substFormula (phi : flafolFormula) (x : var) (t : flafolTerm) :=
     match phi with
     | varFormula _ => phi
     | TT => phi
     | FF => phi
     | ℓ₁ ⊑ ℓ₂ => (ℓ₁ t[x ↦ t]) ⊑ (ℓ₂ t[x ↦ t])
     | canRead p ℓ => canRead (p t[x ↦ t]) (ℓ t[x ↦ t])
     | canWrite p ℓ => canWrite (p t[x ↦ t]) (ℓ t[x ↦ t])
     | p □ ⟨ ℓ ⟩ psi =>
       let p' :=  p t[x ↦ t] in
       let ℓ' := ℓ t[x ↦ t] in
       p' □ ⟨ ℓ' ⟩ (substFormula psi x t)
     | rel R args => rel R (map (fun t' => t' t[ x ↦ t ]) args)
     | psi & chi => (substFormula psi x t) & (substFormula chi x t)
     | psi ⊕ chi => (substFormula psi x t) ⊕ (substFormula chi x t)
     | psi ==⟨l⟩> chi => (substFormula psi x t) ==⟨l t[x↦ t]⟩> (substFormula chi x t)
     | ∀ s; psi => ∀ s; substFormula psi x t
     | ∃ s; psi => ∃ s; substFormula psi x t
     end.
                                           
    Notation "phi f[ x ↦ t ]" := (substFormula phi x t) (at level 40).
    Theorem notFreeInFormulaSubstEq : forall (phi : flafolFormula) (x : var) (t : flafolTerm),
        x ∉FVF phi -> phi f[ x ↦ t ] = phi.
    Proof.
      intros phi x t HFVF. generalize dependent t.
      induction phi; simpl; auto; intros t.
      all: try (repeat match goal with
                       | [ H : ?T t[ _ ↦ _ ] = ?T |- _ ] => rewrite H
                       | [ H : ?Phi f[ _ ↦ _ ] = ?Phi |- _ ] => rewrite H
                       | [ T : flafolTerm |- _ ] =>
                         match goal with
                         | [ H : T t[ _ ↦ _ ] = T |- _ ] => fail 1
                         | [ |- context[substTerm ?T ?X ?U]] => 
                           assert (T t[ X ↦ U ] = T)
                             by (apply substTermNonFreeEqual;
                                 let H := fresh "H" in
                                 intro H; apply HFVF; constructor; auto; fail)
                         end
                       | [ IH : ?X ∉FVF ?Phi -> forall t, ?Phi f[ ?X ↦ t ] = ?Phi |- _ ] =>
                         match goal with
                         | [ _ : Phi f[ X ↦ _ ] = Phi |- _ ] => fail 1
                         | [ |- context[ Phi f[ X ↦ ?T ] ]] => assert (Phi f[X ↦ T ] = Phi)
                             by (apply IH;
                                 let H := fresh "H" in
                                 intro H; apply HFVF; constructor; auto; fail)
                         end
                       end); auto. 
      rewrite mapSubstTermNonFreeEqual; [reflexivity | idtac].
      intros t' HIn HFVT. apply HFVF; apply freeInRel with (t := t'); auto.
    Qed.

    Lemma OpenFormulaRecSubst : forall phi x s t n,
        x ∉FVT s ->
        lc_term t ->
        open_formula_rec n (phi f[x↦t]) s
        = (open_formula_rec n phi s) f[x ↦ t].
    Proof.
      intros phi; induction phi; intros x u t n Hxs Ht;
        unfold open_formula.
      all: simpl; repeat rewrite OpenTermRecSubst; auto.
      all: try (rewrite IHphi1; auto; rewrite IHphi2; auto; fail).
      - apply f_equal;
          induction l; simpl; auto; rewrite OpenTermRecSubst; auto; rewrite IHl; auto.
      - rewrite IHphi; auto.
      - rewrite IHphi; auto.
      - rewrite IHphi; auto.
    Qed.

    Lemma OpenFormulaSubst : forall phi x s t,
        x ∉FVT s -> lc_term t -> open_formula (phi f[x ↦ t]) s = (open_formula phi s) f[x ↦ t].
    Proof.
      intros phi x s t H H0.
      unfold open_formula. apply OpenFormulaRecSubst; auto.
    Qed.

    Obligation Tactic := Tactics.program_simpl;
                          try (inversion Hphi; auto; constructor; auto; try (eapply substTermSortPreservingInv; eauto 2; fail);
                                 match goal with (* Inductive cases *)
                                 | [ IHphi : forall (x : var) (t : flafolTerm), lc_term t -> ⊢s t ::: VarSort x -> ⊢wff (?phi f[x ↦ t]) -> ⊢wff ?phi, tsort : ⊢s ?t ::: VarSort ?x |- ⊢wff ?phi ] => apply IHphi with (x := x) (t := t); auto
                                 | _ => idtac
                                 end; fail).
    Program Fixpoint WellFormedConstructor (phi : flafolFormula) (x : var) (t : flafolTerm)
             (tlc : lc_term t) (tsort : ⊢s t ::: (VarSort x)) (Hphi : ⊢wff (phi f[x ↦ t]))
      {measure (formula_size phi)} : ⊢wff phi :=
      match phi with
      | varFormula _ => Hphi
      | TT => Hphi
      | FF => Hphi
      | ℓ₁ ⊑ ℓ₂ => _
      | canRead p ℓ => _
      | canWrite p ℓ => _
      | p □ ⟨ ℓ ⟩ psi => _
      | rel R args => _
      | psi & chi => _
      | psi ⊕ chi => _
      | psi ==⟨l⟩> chi => _
      | ∀ s; psi => _
      | ∃ s; psi => _
      end.
  Next Obligation.
    inversion Hphi.
    apply saysWF; try (apply substTermSortPreservingInv with (x := x) (t₂ := t); auto).
    apply (WellFormedConstructor psi x t tlc tsort H4).
    simpl; auto.
  Defined.
  Next Obligation.
    inversion Hphi; auto; constructor; auto.
    apply substTermSortPreservingMapInv with (x := x) (t₂ := t); auto.
  Defined.
  Next Obligation.
    inversion Hphi; apply andWF.
    apply (WellFormedConstructor psi x t tlc tsort H1);
      simpl; auto; rewrite PeanoNat.Nat.lt_succ_r; apply PeanoNat.Nat.le_max_l.
    apply (WellFormedConstructor chi x t tlc tsort H2);
      simpl; auto; rewrite PeanoNat.Nat.lt_succ_r; apply PeanoNat.Nat.le_max_r.
  Defined.
  Next Obligation.
    inversion Hphi; apply orWF.
    apply (WellFormedConstructor psi x t tlc tsort H1);
      simpl; auto; rewrite PeanoNat.Nat.lt_succ_r; apply PeanoNat.Nat.le_max_l.
    apply (WellFormedConstructor chi x t tlc tsort H2);
      simpl; auto; rewrite PeanoNat.Nat.lt_succ_r; apply PeanoNat.Nat.le_max_r.
  Defined.
  Next Obligation.
    inversion Hphi; apply impliesWF; auto.
    apply (WellFormedConstructor psi x t tlc tsort H2);
      simpl; auto; rewrite PeanoNat.Nat.lt_succ_r; apply PeanoNat.Nat.le_max_l.
    eapply substTermSortPreservingInv; eauto.
    apply (WellFormedConstructor chi x t tlc tsort H4);
      simpl; auto; rewrite PeanoNat.Nat.lt_succ_r; apply PeanoNat.Nat.le_max_r.
  Defined.
  Next Obligation.
    inversion Hphi.
    apply forallWF with (L := x :: L ++ (varsInFormula psi)).
    intros x0 H2 H3.
    apply WellFormedConstructor with (x := x) (t := t); auto.
    unfold open_formula; rewrite <- OpenFormulaRecSubst; auto.
    unfold open_formula in H0; apply H0; auto.
    intro Hcontra; apply H2; right; apply in_or_app; left; auto.
    intro Hcontra; inversion Hcontra; apply H2; left; auto.
    simpl; rewrite OpenFormulaSize; auto.
  Defined.
  Next Obligation.
    inversion Hphi.
    apply existsWF with (L := x :: L ++ (varsInFormula psi)).
    intros x0 H2 H3.
    apply WellFormedConstructor with (x := x) (t := t); auto.
    unfold open_formula; rewrite <- OpenFormulaRecSubst; auto.
    unfold open_formula in H0; apply H0; auto.
    intro Hcontra; apply H2; right; apply in_or_app; left; auto.
    intro Hcontra; inversion Hcontra; apply H2; left; auto.
    simpl; rewrite OpenFormulaSize; auto.
  Defined.

  Obligation Tactic := Tactics.program_simpl;
                        try (apply substTermSortPreserving);
                        try (inversion Hphi; auto;
                               try (constructor;
                                      try (apply substTermSortPreserving); 
                                      auto; fail); fail).
  Program Fixpoint WellFormedSubst (phi : flafolFormula) (x : var) (t : flafolTerm)
          (tclosed : lc_term t) (tsort : ⊢s t ::: (VarSort x)) (Hphi : ⊢wff phi)
    {measure (formula_size phi)} : ⊢wff (phi f[x↦ t]) :=
    match phi with
    | varFormula _ => Hphi
    | TT => Hphi
    | FF => Hphi
    | ℓ₁ ⊑ ℓ₂ => _
    | canRead p ℓ => _
    | canWrite p ℓ => _
    | p □ ⟨ ℓ ⟩ psi => saysWF _ _ _ _ _ (WellFormedSubst psi _ _ _ _ _)
    | rel R args => _
    | psi & chi => andWF _ _ (WellFormedSubst psi _ _ _ _ _) (WellFormedSubst chi _ _ _ _ _)
    | psi ⊕ chi => orWF _ _  (WellFormedSubst psi _ _ _ _ _) (WellFormedSubst chi _ _ _ _ _)
    | psi ==⟨l⟩> chi => _
    | ∀ s; psi => _
    | ∃ s; psi => _
    end.

  Next Obligation.
    inversion Hphi; apply RelWF; apply substTermSortPreservingMap; auto.
  Defined.
  Next Obligation.
    simpl; auto; rewrite PeanoNat.Nat.lt_succ_r; apply PeanoNat.Nat.le_max_l.
  Defined.
  Next Obligation.
    simpl; auto; rewrite PeanoNat.Nat.lt_succ_r; apply PeanoNat.Nat.le_max_r.
  Defined.
  Next Obligation.
    simpl; auto; rewrite PeanoNat.Nat.lt_succ_r; apply PeanoNat.Nat.le_max_l.
  Defined.
  Next Obligation.
    simpl; auto; rewrite PeanoNat.Nat.lt_succ_r; apply PeanoNat.Nat.le_max_r.
  Defined.
  Next Obligation.
    inversion Hphi.
    pose proof (WellFormedSubst psi x t tclosed tsort H2).
    pose proof (WellFormedSubst chi x t tclosed tsort H4).
    pose proof (substTermSortPreserving l x t Label H3 tsort).
    constructor; auto; [apply H5 | apply H6]; simpl;
    apply Lt.le_lt_n_Sm; [apply Nat.le_max_l | apply Nat.le_max_r].
  Defined.    

  Next Obligation.
    inversion Hphi.
    apply forallWF with (L := x :: L ++ (varsInFormula psi)).
    intros x0 H2 H3.
    unfold open_formula; rewrite OpenFormulaRecSubst; auto.
    apply WellFormedSubst; auto.
    unfold open_formula in H0; apply H0; auto.
    intro Hcontra; apply H2; right; apply in_or_app; left; auto.
    simpl; rewrite OpenFormulaSize; auto.
    intro Hcontra; apply H2; left; inversion Hcontra; auto.
  Defined.
  Next Obligation.
    inversion Hphi.
    apply existsWF with (L := x :: L ++ (varsInFormula psi)).
    intros x0 H2 H3.
    unfold open_formula; rewrite OpenFormulaRecSubst; auto.
    apply WellFormedSubst; auto.
    unfold open_formula in H0; apply H0; auto.
    intro Hcontra; apply H2; right; apply in_or_app; left; auto.
    simpl; rewrite OpenFormulaSize; auto.
    intro Hcontra; apply H2; left; inversion Hcontra; auto.
  Defined.

  Lemma FormulaSubstId : forall (phi : flafolFormula) (x : var),
      phi f[x ↦ varTerm x] = phi.
  Proof.
    induction phi; intros x; simpl; auto; repeat rewrite TermSubstId; auto;
      try (rewrite IHphi; auto; fail);
      try (rewrite IHphi1; rewrite IHphi2; auto; fail).
    - rewrite TermsSubstId; auto.
  Qed.

  Lemma SubstTTInversion : forall (phi : flafolFormula) (t : flafolTerm) (x : var),
      phi f[x ↦ t] = TT -> phi = TT.
  Proof.
    intros phi t x H.
    induction phi; try (inversion H; fail); auto.
    all: simpl in H; destruct (varEqDec x v); inversion H.
  Qed.
  Hint Resolve SubstTTInversion : substInversion.
  Hint Rewrite SubstTTInversion : substInversion.

  Lemma SubstFFInversion : forall (phi : flafolFormula) (t : flafolTerm) (x : var),
      phi f[x ↦ t] = FF -> phi = FF.
  Proof.
    intros phi t x H.
    induction phi; try (inversion H; fail); auto.
    all: simpl in H; destruct (varEqDec x v); inversion H.
  Qed.
  Hint Resolve SubstFFInversion : substInversion.
  Hint Rewrite SubstFFInversion : substInversion.

  Lemma SubstRelInversion : forall (phi : flafolFormula) (t : flafolTerm) (x : var)
                              (R : relSym) (args : list flafolTerm),
      phi f[x ↦ t] = rel R args -> exists args', phi = rel R args'.
  Proof.
    intros phi t x R args H.
    induction phi; try (inversion H; fail); auto.
    exists l; inversion H; auto.
    all: simpl in H; destruct (varEqDec x v); inversion H.
  Qed.
  Hint Resolve SubstRelInversion : substInversion.
  Hint Rewrite SubstRelInversion : substInversion.

  Lemma SubstAndInversion : forall (phi psi chi : flafolFormula) (t : flafolTerm) (x : var),
      phi f[x ↦ t] = psi & chi -> exists psi' chi', phi = psi' & chi'.
  Proof.
    intros phi psi chi t x H.
    induction phi; try (inversion H; fail); auto.
    exists phi1; exists phi2; inversion H; auto.
    all: simpl in H; destruct (varEqDec x v); inversion H.
  Qed.
  Hint Resolve SubstAndInversion : substInversion.
  Hint Rewrite SubstAndInversion : substInversion.

  Lemma SubstOrInversion : forall (phi psi chi : flafolFormula) (t : flafolTerm) (x : var),
      phi f[x ↦ t] = psi ⊕ chi -> exists psi' chi', phi = psi' ⊕ chi'.
  Proof.
    intros phi psi chi t x H.
    induction phi; try (inversion H; fail); auto.
    exists phi1; exists phi2; inversion H; auto.
    all: simpl in H; destruct (varEqDec x v); inversion H.
  Qed.
  Hint Resolve SubstOrInversion : substInversion.
  Hint Rewrite SubstOrInversion : substInversion.    

  Lemma SubstImpInversion : forall (phi psi chi : flafolFormula) (l t : flafolTerm) (x : var),
      phi f[x ↦ t] = psi ==⟨l⟩> chi -> exists psi' chi' l', phi = psi' ==⟨l'⟩> chi'.
  Proof.
    intros phi psi chi l t x H.
    destruct phi; try (inversion H; fail); auto.
    exists phi1; exists phi2; exists f; inversion H; auto.
  Qed.
  Hint Resolve SubstImpInversion : substInversion.
  Hint Rewrite SubstImpInversion : substInversion.    

  Lemma SubstFlowsToInversion : forall (phi : flafolFormula) (t u v : flafolTerm) (x : var),
      phi f[x ↦ t] = u ⊑ v -> exists w w', phi = w ⊑ w'.
  Proof.
    intros phi t u v x H.
    induction phi; try (inversion H; fail); auto.
    exists f; exists f0; inversion H; auto.
    all: simpl in H; destruct (varEqDec x v0); inversion H.
  Qed.
  Hint Resolve SubstFlowsToInversion : substInversion.
  Hint Rewrite SubstFlowsToInversion : substInversion.

  Lemma SubstForallInversion : forall (phi psi : flafolFormula) (s : G.sort) (t : flafolTerm) (x : var),
      phi f[x ↦ t] = ∀ s; psi -> exists chi, phi = flafolForall s chi.
  Proof.
    intros phi psi s t x H.
    induction phi; try (inversion H; fail); auto.
    inversion H; subst.
    exists phi; auto.
  Qed.
  Hint Resolve SubstForallInversion : substInversion.
  Hint Rewrite SubstForallInversion : substInversion.

  Lemma SubstExistsInversion : forall (phi psi : flafolFormula) (s : G.sort) (t : flafolTerm) (x : var),
      phi f[x ↦ t] = ∃ s; psi -> exists chi, phi = flafolExists s chi.
  Proof.
    intros phi psi s t x H.
    induction phi; try (inversion H; fail); auto.
    inversion H; subst.
    exists phi; auto.
  Qed.
  Hint Resolve SubstExistsInversion : substInversion.
  Hint Rewrite SubstExistsInversion : substInversion.

  Lemma SubstSaysInversion : forall (phi psi : flafolFormula) (p lab t : flafolTerm) (x : var),
      phi f[x ↦ t] = p □ ⟨lab⟩ psi -> exists q lab' chi, phi = q □ ⟨lab'⟩ chi.
  Proof.
    intros phi psi p lab t x H.
    induction phi; try (inversion H; fail); auto.
    exists f ; exists f0; exists phi; reflexivity.
  Qed.
  Hint Resolve SubstSaysInversion : substInversion.
  Hint Rewrite SubstSaysInversion : substInversion.

  Lemma SubstCanReadInversion : forall (phi : flafolFormula) (p lab t : flafolTerm) (x : var),
      phi f[x ↦ t] = canRead p lab -> exists q lab', phi = canRead q lab'.
  Proof.
    intros phi p lab t x H.
    induction phi; try (inversion H; fail); auto.
    exists f ; exists f0; inversion H; auto.
  Qed.
  Hint Resolve SubstCanReadInversion : substInversion.
  Hint Rewrite SubstCanReadInversion : substInversion.

  Lemma SubstCanWriteInversion : forall (phi : flafolFormula) (p lab t : flafolTerm) (x : var),
      phi f[x ↦ t] = canWrite p lab -> exists q lab', phi = canWrite q lab'.
  Proof.
    intros phi p lab t x H.
    induction phi; try (inversion H; fail); auto.
    exists f ; exists f0; inversion H; auto.
  Qed.
  Hint Resolve SubstCanWriteInversion : substInversion.
  Hint Rewrite SubstCanWriteInversion : substInversion.

  Ltac InvertSubst H H' :=
    match type of H with
    | ?phi f[?x ↦ ?t] = TT =>
      pose proof (SubstTTInversion phi t x H) as H'
    | TT = ?phi f[?x ↦ ?t] =>
      pose proof (SubstTTInversion phi t x (eq_sym H)) as H'
    | ?phi f[?x ↦ ?t] = FF =>
      pose proof (SubstFFInversion phi t x H) as H'
    | FF = ?phi f[?x ↦ ?t] =>
      pose proof (SubstFFInversion phi t x (eq_sym H)) as H'
    | ?phi f[?x ↦ ?t] = ?lab1 ⊑ ?lab2 =>
      pose proof (SubstFlowsToInversion phi lab1 lab2 t x H) as H'
    | ?lab1 ⊑ ?lab2 = ?phi f[?x ↦ ?t] =>
      pose proof (SubstFlowsToInversion phi lab1 lab2 t x (eq_sym H)) as H'
    | ?phi f[?x ↦ ?t] = rel ?R ?args =>
      pose proof (SubstRelInversion phi t x R args H) as H' 
    | rel ?R ?args = ?phi f[?x ↦ ?t] =>
      pose proof (SubstRelInversion phi t x R args (eq_sym H)) as H'
    | ?phi f[?x ↦ ?t] = ?psi & ?chi =>
      pose proof (SubstAndInversion phi psi chi t x H) as H'
    | ?psi & ?chi = ?phi f[?x ↦ ?t] =>
      pose proof (SubstAndInversion phi psi chi t x (eq_sym H)) as H'
    | ?phi f[?x ↦ ?t] = ?psi ⊕ ?chi =>
      pose proof (SubstOrInversion phi psi chi t x H) as H'
    | ?psi ⊕ ?chi = ?phi f[?x ↦ ?t] =>
      pose proof (SubstOrInversion phi psi chi t x (eq_sym H)) as H'
    | ?phi f[?x ↦ ?t] = ?psi ==⟨?l⟩> ?chi =>
      pose proof (SubstImpInversion phi psi chi l t x H) as H'
    | ?psi ==⟨?l⟩> ?chi = ?phi f[?x ↦ ?t] =>
      pose proof (SubstImpInversion phi psi chi l t x (eq_sym H)) as H'
    | ?phi f[?x ↦ ?t] = flafolForall ?s ?psi =>
      pose proof (SubstForallInversion phi psi s t x H) as H'
    | flafolForall ?s ?psi = ?phi f[?x ↦ ?t] =>
      pose proof (SubstForallInversion phi psi s t x (eq_sym H)) as H'
    | ?phi f[?x ↦ ?t] = flafolExists ?s ?psi =>
      pose proof (SubstExistsInversion phi psi s t x H) as H'
    | flafolExists ?s ?psi = ?phi f[?x ↦ ?t] =>
      pose proof (SubstExistsInversion phi psi s t x (eq_sym H)) as H'
    | ?phi f[?x ↦ ?t] = ?p □ ⟨?lab⟩ ?psi =>
      pose proof (SubstSaysInversion phi psi p lab t x H) as H'
    | ?p □ ⟨?lab⟩ ?psi = ?phi f[?x ↦ ?t] =>
      pose proof (SubstExistsInversion phi psi p lab t x (eq_sym H)) as H'
    | ?phi f[?x ↦ ?t] = canRead ?p ?lab =>
      pose proof (SubstCanReadInversion phi p lab t x H) as H'
    | canRead ?p ?lab = ?phi f[?x ↦ ?t] =>
      pose proof (SubstCanReadInversion phi p lab t x H) as H'
    | ?phi f[?x ↦ ?t] = canWrite ?p ?lab =>
      pose proof (SubstCanWriteInversion phi p lab t x H) as H'
    | canWrite ?p ?lab = ?phi f[?x ↦ ?t] =>
      pose proof (SubstCanWriteInversion phi p lab t x H) as H'
    end.

  Theorem RepeatedSubstFormula : forall (phi : flafolFormula) (x y : var) (t : flafolTerm),
      y ∉FVF phi -> (phi f[x ↦ varTerm y]) f[y ↦ t] = phi f[x ↦ t].
  Proof.
    intros phi x y t H.
    Hint Resolve RepeatedSubstTerm.
    induction phi; simpl; eauto;
      repeat (rewrite RepeatedSubstTerm); auto.
    all: try (intro Hcontra; apply H; try (constructor; auto; fail)).
    - apply f_equal.
      induction l; simpl; [auto|].
      rewrite RepeatedSubstTerm; [apply f_equal|].
      apply IHl.
      intro Hcontra; apply H; inversion Hcontra; apply freeInRel with (t := t0); [right |]; auto.
      intro Hcontra; apply H; apply freeInRel with (t := a); [left |]; auto.
    - rewrite <- IHphi1; [rewrite <- IHphi2; auto |];
        intro Hcontra; apply H; constructor; auto; fail.
    - rewrite <- IHphi1; [rewrite <- IHphi2; auto |];
        intro Hcontra; apply H; constructor; auto; fail.
    - rewrite <- IHphi1; [rewrite <- IHphi2; auto |];
        intro Hcontra; apply H; constructor; auto; fail.
    - rewrite IHphi; auto.
      intro Hcontra; apply H.
      apply freeInForall; auto.
    - rewrite IHphi; auto.
      intro Hcontra; apply H.
      apply freeInExists; auto.
    - rewrite <- IHphi; auto.
      intro Hcontra; apply H; constructor; auto; fail.
  Qed.

   (*
     This is a helper piece of Ltac for wffDec.
     It checks whether t has sort sigma.
     If it does not, and we are checking that some formula is well-formed,
     then t must be a constituent of phi and so phi must not be well-formed.
    *)
   Ltac checkWFFDec t sigma :=
     match goal with
     | [ Ht : ~ ⊢s t ::: sigma |- {⊢wff ?phi} + {~ ⊢wff ?phi} ] =>
       let H := fresh "H" in
       right; intro H; inversion H; unfold not in Ht; apply Ht; auto
     | [ Ht : ⊢s t ::: sigma |- _ ] => fail 1
     | _ => destruct (hasSortDec' t sigma)
     end.

   Hint Resolve WellSortedLocallyClosed : WFFLC.
   Theorem WFFLC : forall phi, ⊢wff phi -> lc_formula phi.
   Proof.
     intros phi H.
     induction phi using ClosedFormulaInduction; 
       try (inversion H; econstructor; eauto with WFFLC; fail).
     - inversion H; apply lcRel; intros t H3; clear H H0 H2.
       generalize dependent (relTypes R).
       induction args; [inversion H3|].
       intros sigmas H1; inversion H1.
       destruct H3. rewrite H3 in H2; eauto with WFFLC.
       apply IHargs with (l := types'); auto.
     - inversion H; apply lcForall with (L := L ++ L0 ++ varsInFormula phi).
       intros x H4 H5.
       apply H0; auto.
       -- intro Hcontra; apply H4; apply in_or_app; left; auto.
       -- apply H2; auto;
            intro Hcontra; apply H4; apply in_or_app; right; apply in_or_app; left; auto.
     - inversion H; apply lcExists with (L := L ++ L0 ++ varsInFormula phi).
       intros x H4 H5.
       apply H0; auto.
       -- intro Hcontra; apply H4; apply in_or_app; left; auto.
       -- apply H2; auto;
            intro Hcontra; apply H4; apply in_or_app; right; apply in_or_app; left; auto.
   Qed.

     Ltac WFopen_term_rec := match goal with
                         | [H : ⊢s open_term_rec ?n ?t ?t1' ::: ?sigma |- ⊢s open_term_rec ?n ?t ?t2 ::: ?sigma] =>
                           eapply  WFopen_term_rec with (t1 := t1'); eauto
                         end.
  Lemma WFopen_formula_rec : forall phi t1 t2 s n, ⊢s t1 ::: s -> ⊢s t2 ::: s -> ⊢wff (open_formula_rec n phi t1) -> ⊢wff (open_formula_rec n phi t2).
  Proof.
    induction phi using ClosedFormulaInduction; simpl; intros; inversion H1; subst; try (econstructor; eauto; fail);
      try (constructor; try WFopen_term_rec; eauto; fail).
    - constructor.
      eapply WFhasSorts with (t1 := t1); eauto.
    - inversion H2; subst.
      apply forallWF with (L := L ++ L0).
      intros.
      unfold open_formula.
      rewrite open_formula_commute_rec.
      eapply H with (t1 := t1); eauto.
      intro.
      apply H3.
      apply in_or_app; auto.
      unfold open_formula in *.
      rewrite open_formula_commute_rec; auto.
      apply H4; auto.
      intro.
      apply H3.
      apply in_or_app; auto.
      all: try constructor.
      eapply hasSort_lc; eauto.
    - inversion H2; subst.
      apply forallWF with (L := L ++ L0).
      intros.
      unfold open_formula.
      rewrite open_formula_commute_rec.
      eapply H with (t1 := t1); eauto.
      intro.
      apply H4.
      apply in_or_app; auto.
      unfold open_formula in *.
      rewrite open_formula_commute_rec; auto.
      apply H5; auto.
      intro.
      apply H4.
      apply in_or_app; auto.
      eapply hasSort_lc; eauto.
      eapply hasSort_lc; eauto.
      simpl; reflexivity.
      eapply hasSort_lc; eauto.
      eapply hasSort_lc; eauto.
    - inversion H2; subst.
      apply existsWF with (L := L ++ L0).
      intros.
      unfold open_formula.
      rewrite open_formula_commute_rec.
      eapply H with (t1 := t1); eauto.
      intro.
      apply H3.
      apply in_or_app; auto.
      unfold open_formula in *.
      rewrite open_formula_commute_rec; auto.
      apply H4; auto.
      intro.
      apply H3.
      apply in_or_app; auto.
      all: try constructor.
      eapply hasSort_lc; eauto.
    - inversion H2; subst.
      apply existsWF with (L := L ++ L0).
      intros.
      unfold open_formula.
      rewrite open_formula_commute_rec.
      eapply H with (t1 := t1); eauto.
      intro.
      apply H4.
      apply in_or_app; auto.
      unfold open_formula in *.
      rewrite open_formula_commute_rec; auto.
      apply H5; auto.
      intro.
      apply H4.
      apply in_or_app; auto.
      all: try (eapply hasSort_lc; eauto; fail).
      simpl; auto.
  Qed.


  Lemma fvsubstFormula : forall y' y f t, y' ∉FVF f -> y' ∉FVT t -> y' ∉FVF (f f[ y ↦ t]).
  Proof.
    intros y' y f.
    revert y' y.
    induction f; intros; simpl; auto.
    - intro.
      inversion H1; subst.
      + revert H4.       
        apply fvsubstTerm; auto.
        intro.
        apply H.
        econstructor; eauto.
      + revert H4.       
        apply fvsubstTerm; auto.
        intro.
        apply H.
        econstructor; eauto; fail.
    - intro.
      inversion H1; subst.
      destruct (map_preservesIn _ _ _ H5) as [t1 [h0 h1]]. 
      revert H6.
      subst.
      apply fvsubstTerm; auto.
      intro.
      apply H.
      econstructor; eauto.
    - intro.
      inversion H1; subst.      
      1,2: revert H4; apply fvsubstTerm; auto.
      1,2: intro; apply H; econstructor; eauto; fail.
    - intro.
      inversion H1; subst.      
      1,2: revert H4; apply fvsubstTerm; auto.
      1,2: intro; apply H; econstructor; eauto; fail.      
    - intro.
      inversion H1; subst; revert H4; eauto.
      apply IHf1; auto.
      intro.
      apply H.
      econstructor; eauto; fail.
      apply IHf2; auto.
      intro.
      apply H.
      econstructor; eauto; fail.
    - intro.
      inversion H1; subst; revert H4; eauto.
      apply IHf1; auto.
      intro.
      apply H.
      econstructor; eauto; fail.
      apply IHf2; auto.
      intro.
      apply H.
      econstructor; eauto; fail.
    - intro.
      inversion H1; subst; revert H4; eauto.
      apply IHf1; auto.
      intro.
      apply H.
      econstructor; eauto; fail.
      apply fvsubstTerm; auto.
      intro; apply H; econstructor; eauto; fail.
      apply IHf2; auto.
      intro.
      apply H.
      econstructor; eauto; fail.
    - intro.
      inversion H1; subst.
      revert H4.
      apply IHf; auto.
      intro; apply H.
      econstructor; eauto; fail.
    - intro.
      inversion H1; subst.
      revert H4.
      apply IHf; auto.
      intro; apply H.
      econstructor; eauto; fail.
    - intro.
      inversion H1; subst.
      1,2: revert H4; apply fvsubstTerm; auto.
      1,2: intro; apply H; econstructor; eauto; fail.
      revert H4.
      apply IHf; auto.
      intro; apply H.
      econstructor; eauto; fail.
  Qed.

  Lemma openFVF : forall phi y t n, y ∉FVT t -> y ∉FVF phi  -> y ∉FVF open_formula_rec n phi t.
  Proof.
    induction phi; simpl; intros; eauto.
    - intro.
      inversion H1; subst.
      + revert H4.       
        apply openFVT; auto.
        intro.
        apply H0.
        econstructor; eauto.
      + revert H4.       
        apply openFVT; auto.
        intro.
        apply H0.
        econstructor; eauto; fail.
    - intro.
      inversion H1; subst.
      destruct (map_preservesIn _ _ _ H5) as [t1 [h0 h1]]. 
      revert H6.
      subst.
      apply openFVT; auto.
      intro.
      apply H0.
      econstructor; eauto.
    - intro.
      inversion H1; subst.      
      1,2: revert H4; apply openFVT; auto.
      1,2: intro; apply H0; econstructor; eauto; fail.
    - intro.
      inversion H1; subst.      
      1,2: revert H4; apply openFVT; auto.
      1,2: intro; apply H0; econstructor; eauto; fail.      
    - intro.
      inversion H1; subst; revert H4; eauto.
      apply IHphi1; auto.
      intro.
      apply H0.
      econstructor; eauto; fail.
      apply IHphi2; auto.
      intro.
      apply H0.
      econstructor; eauto; fail.
    - intro.
      inversion H1; subst; revert H4; eauto.
      apply IHphi1; auto.
      intro.
      apply H0.
      econstructor; eauto; fail.
      apply IHphi2; auto.
      intro.
      apply H0.
      econstructor; eauto; fail.
    - intro.
      inversion H1; subst; revert H4; eauto.
      apply IHphi1; auto.
      intro.
      apply H0.
      econstructor; eauto; fail.
      apply openFVT; auto.
      intro; apply H0; econstructor; eauto; fail.
      apply IHphi2; auto.
      intro.
      apply H0.
      econstructor; eauto; fail.
    - intro.
      inversion H1; subst.
      revert H4.
      apply IHphi; auto.
      intro; apply H0.
      econstructor; eauto; fail.
    - intro.
      inversion H1; subst.
      revert H4.
      apply IHphi; auto.
      intro; apply H0.
      econstructor; eauto; fail.
    - intro.
      inversion H1; subst.
      1,2: revert H4; apply openFVT; auto.
      1,2: intro; apply H0; econstructor; eauto; fail.
      revert H4.
      apply IHphi; auto.
      intro; apply H0.
      econstructor; eauto; fail.      
  Qed.

  
  Lemma OpenFormulaSubstRecAll : forall phi u x t n,
      lc_term t ->
      open_formula_rec n phi u f[x ↦ t] = open_formula_rec n (phi f[x ↦ t]) (u t[x ↦ t]).
  Proof.
    intros phi; induction phi; intros u x t n lct; simpl; auto;
      try (repeat rewrite OpenTermSubstRecAll; auto).
    - apply f_equal. repeat rewrite map_map.
      induction l; simpl; auto. rewrite OpenTermSubstRecAll; auto. apply f_equal. apply IHl.
    - rewrite IHphi1; [rewrite IHphi2|]; auto. 
    - rewrite IHphi1; [rewrite IHphi2|]; auto.
    - rewrite IHphi1; [rewrite IHphi2|]; auto.
    - apply f_equal; rewrite IHphi; auto.
    - apply f_equal; rewrite IHphi; auto.
    - rewrite IHphi; auto.
  Qed.
      
  Lemma OpenFormulaSubstAll : forall phi u x t,
      lc_term t ->
      open_formula phi u f[x ↦ t] = open_formula (phi f[x ↦ t]) (u t[x ↦ t]).
  Proof.
    intros phi u x t H.
    unfold open_formula. apply OpenFormulaSubstRecAll; auto.
  Qed.

    Lemma open_formula_subst_rec : forall phi x t2 t3 n, lc_term t3 -> (open_formula_rec n phi t2) f[x ↦ t3] = open_formula_rec n (phi f[x ↦ t3]) (t2 t[x ↦ t3]).
  Proof.
    induction phi; intros; simpl; auto.
    all: try solve [rewrite IHphi1; auto; rewrite IHphi2; auto].
    - repeat rewrite open_term_subst_rec; auto.
    - induction l; simpl.
      unfold open_formula; simpl; auto.
      f_equal.
      f_equal.
      rewrite open_term_subst_rec; auto.
      inversion IHl; auto.
    - f_equal; auto; apply open_term_subst_rec; auto.
    - f_equal; auto; apply open_term_subst_rec; auto.
    - f_equal.
      apply IHphi1; auto.
      apply open_term_subst_rec; auto.
      apply IHphi2; auto.
    - f_equal.
      rewrite IHphi; auto.
    - f_equal.
      rewrite IHphi; auto.
    - repeat rewrite open_term_subst_rec; auto.
      f_equal.
      rewrite IHphi; auto.
  Qed.  
  Lemma open_formula_subst : forall phi x t2 t3,  lc_term t3 -> (open_formula phi t2) f[x ↦ t3] = open_formula (phi f[x ↦ t3]) (t2 t[x ↦ t3]).
  Proof.
    intros.
    apply open_formula_subst_rec; assumption.
  Qed.

  Obligation Tactic := Tactics.program_simpl; simpl; try (match goal with
      | [ |- ?a < S (Nat.max ?a ?b) ] =>
        apply PeanoNat.Nat.lt_succ_r; apply PeanoNat.Nat.le_max_l
      | [ |- ?b < S (Nat.max ?a ?b) ] =>
        apply PeanoNat.Nat.lt_succ_r; apply PeanoNat.Nat.le_max_r
      end).
  Program Fixpoint OpeningInduction (P : flafolFormula -> Type)
          (varCase : forall X, P (varFormula X))
          (trueCase : P TT)
          (falseCase : P FF)
          (flowsCase : forall lab1 lab2, P (lab1 ⊑ lab2))
          (canReadCase : forall p lab, P (canRead p lab))
          (canWriteCase : forall p lab, P (canWrite p lab))
          (saysCase : forall p lab phi, P phi -> P (p □ ⟨ lab ⟩ phi))
          (relCase : forall R args, P (rel R args))
          (andCase : forall phi psi, P phi -> P psi -> P (phi & psi))
          (orCase : forall phi psi, P phi -> P psi -> P (phi ⊕ psi))
          (impCase : forall phi l psi, P phi -> P psi -> P (phi ==⟨l⟩> psi))
          (forallCase : forall sigma psi, (forall t, ⊢s t ::: sigma ->
                                     P (open_formula psi t))
                               -> P (∀ sigma; psi))
          (existsCase : forall sigma psi, (forall t, ⊢s t ::: sigma ->
                                     P (open_formula psi t))
                               -> P (∃ sigma; psi))
          (phi : flafolFormula) { measure (formula_size phi) }
    : P phi :=
    let rec := OpeningInduction _ _ _ _ _ _ _ _ _ _ _ _ _ _ in
    match phi with
    | varFormula X => varCase X
    | TT => trueCase
    | FF => falseCase
    | lab1 ⊑ lab2 => flowsCase lab1 lab2
    | canRead p lab => canReadCase p lab
    | canWrite p lab => canWriteCase p lab
    | p □ ⟨lab⟩ psi => saysCase p lab psi (rec psi _)
    | rel R args => relCase R args
    | psi & chi => andCase psi chi (rec psi _) (rec chi _)
    | psi ⊕ chi => orCase psi chi (rec psi _) (rec chi _)
    | psi ==⟨l⟩> chi => impCase psi l chi (rec psi _) (rec chi _)
    | ∀ sigma; psi => forallCase sigma psi (fun t H => rec (open_formula psi t) _)
    | ∃ sigma; psi => existsCase sigma psi (fun t H => rec (open_formula psi t) _)
   end.
   Next Obligation.
     rewrite OpenFormulaSize; apply PeanoNat.Nat.lt_succ_diag_r.
   Defined.
   Next Obligation.
     rewrite OpenFormulaSize; apply PeanoNat.Nat.lt_succ_diag_r.
   Defined.

  Inductive AtomicFormula : flafolFormula -> Prop :=
  | TTAtomic : AtomicFormula TT
  | FFAtomic : AtomicFormula FF
  | varFAtomic : forall X : formulaVar, AtomicFormula (varFormula X)
  | relAtomic : forall (R : relSym) (args : list flafolTerm),
      AtomicFormula (rel R args)
  | canRAtomic : forall p l, AtomicFormula (canRead p l)
  | canWAtomic : forall p l, AtomicFormula (canWrite p l)
  | flowsToAtomic : forall l1 l2, AtomicFormula (l1 ⊑ l2).
   
End Formula.