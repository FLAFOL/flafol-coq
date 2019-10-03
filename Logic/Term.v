Require Import Base.Lists.
Require Import Coq.Program.Tactics.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListDec.
Require Import Coq.Arith.PeanoNat.
Require Coq.Vectors.Fin.

Require Import Coq.Arith.EqNat.
Local Open Scope nat_scope.

Module Type GroundInfo.

  (*
    This module contains the information that needs to be shared among terms, formulas, etc.
    In particular, it contains the equivalent of the sets of sorts, variables, function symbols, relation symbols, and ground terms.
    In some sense, this is the knob that a user of FLAFOL can twiddle.
   *)
  
  Parameter sort : Set.
  Parameter Principal Label : sort.

  Parameter sortEqDec : forall sigma rho : sort, {sigma = rho} + {sigma <> rho}.

  Parameter var : Set.
  Parameter varEqDec : forall x y : var, {x = y} + {x <> y}.

  Parameter VarSort : var -> sort. (* There's a set of variables for every sort. *)
  (* There's an infinite number of variables in each sort. 
     This demands a new variable, fresh wrt the list, of the given sort. *)
  Parameter freshVar : list var -> sort -> var.

  Axiom freshVarNotIn : forall (vs : list var) (sigma : sort), ~ In (freshVar vs sigma) vs.
  Axiom freshVarSameSort : forall (vs : list var)(sigma : sort),
      VarSort (freshVar vs sigma) = sigma.

  Parameter formulaVar : Set.
  Parameter formulaVarEqDec : forall X Y : formulaVar, {X = Y} + {X <> Y}.
  Parameter freshFormulaVar : list formulaVar -> formulaVar.
  Axiom freshFormulaVarNotIn : forall (vs : list formulaVar), ~ In (freshFormulaVar vs) vs.

  Parameter funSym : Set. (* There are function symbols, each with an arity and a function type. *)
  Parameter funInputTypes : forall f : funSym, list sort.
  Parameter funOutputType : funSym -> sort.
  Axiom funSymEqDec : forall f f' : funSym, {f = f'} + {f <> f'}.

  Parameter relSym : Set. (* Similarly, there are relations, each with an arity and a relation type. *)
  Parameter relTypes : forall R : relSym, list sort.
  Axiom relSymEqDec : forall R S : relSym, {R = S} + {R <> S}.

End GroundInfo.

Module Type Term (G : GroundInfo).
  Import G.


  Inductive flafolTerm : Set :=
    varTerm : G.var -> flafolTerm
  | varTerm_b : nat -> flafolTerm
  | funTerm : forall f : G.funSym, list flafolTerm -> flafolTerm.

  (*
    Because we have a list of flafolTerm as an argument to a constructor, we need the induction principal to take that into account.
   *)
  Fixpoint flafolTerm_rect_nest
           (P : flafolTerm -> Type)
           (Q : list flafolTerm -> Type)
           (vT : forall x : G.var, P (varTerm x))
           (bT : forall n : nat, P (varTerm_b n))
           (fT: forall (f : G.funSym) (args : list flafolTerm),
               Q args -> P (funTerm f args))
           (nilQ : Q nil)
           (consQ : forall (t : flafolTerm) (l : list flafolTerm),
               P t -> Q l -> Q (cons t l))
           (t : flafolTerm)
    : P t :=
    match t with
    | varTerm x => vT x
    | varTerm_b n => bT n
    | funTerm f args => fT f args (list_rect Q nilQ
                                            (fun u r =>
                                               consQ u r
                                                     (flafolTerm_rect_nest P Q vT bT fT
                                                                           nilQ consQ u)) args)
    end.
  Fixpoint flafolTerm_rect_nest_prop
           (P : flafolTerm -> Prop)
           (Q : list flafolTerm -> Prop)
           (vT : forall x : G.var, P (varTerm x))
           (bT : forall n : nat, P (varTerm_b n))
           (fT: forall (f : G.funSym) (args : list flafolTerm),
               Q args -> P (funTerm f args))
           (nilQ : Q nil)
           (consQ : forall (t : flafolTerm) (l : list flafolTerm),
               P t -> Q l -> Q (cons t l))
           (t : flafolTerm)
    : P t :=
    match t with
    | varTerm x => vT x
    | varTerm_b n => bT n
    | funTerm f args => fT f args (list_rect Q nilQ
                                            (fun u r =>
                                               consQ u r
                                                     (flafolTerm_rect_nest P Q vT bT fT
                                                                           nilQ consQ u)) args)
    end.

  
  (*locally closed term, ie. terms with no varTerm_b*)
  Inductive lc_term : flafolTerm -> Prop :=
  | lc_VarTerm : forall x, lc_term (varTerm x)
  | lc_funTerm: forall f l, (forall t, In t l -> lc_term t) -> lc_term (funTerm f l).

  Definition BoundVarsNotLC : forall n, ~ lc_term (varTerm_b n).
  Proof.
    intros n Hcontra; inversion Hcontra.
  Defined.
  
  Definition termEqDec : forall (t u : flafolTerm), {t = u} + {t <> u}.
    intros t.
    induction t using flafolTerm_rect_nest with (Q := (fun l => forall l', {l = l'} + {l <> l'})).
    all: intros;
    match goal with
    | [ u : flafolTerm |- _] =>
      let H := fresh "H" in
      destruct u; try (right; intro H; inversion H; auto; fail)
    | _ => idtac
    end.
    all: try match goal with
        | [|- {?F ?X = ?F ?Y} + {?F ?X <> ?F ?Y} ] => (* Since variables and ground types have decidable equality, 
                                                      we can decide on the equality of the injections. *)
          let e := fresh "e" in
          let n := fresh "n" in
          let H := fresh "H" in
          match F with
          | varTerm => destruct (G.varEqDec X Y) as [e | n]
          end;
            [left; rewrite e; auto | right; intro H; inversion H; apply n; auto]
        | [IH : forall u : flafolTerm, {?T = u} + {?T <> u} |- {_ ?T = _ ?U} + {_ ?T <> _ ?U} ] => (* Take care of the inductive case. *)
          let e := fresh "e" in
          let n := fresh "n" in
          destruct (IH U) as [e | n];
            [left; rewrite e; auto
            | right; intros e; inversion e; apply n; auto]
             end.
    destruct (eq_nat_dec n n0).
    left; auto.
    right; intros.
    injection; intros; auto.
    (* At this point, we have the "equality of the underlying thing" in the context. *)
    (* To take care of function application, we first check the argument list,
       then we look at the function symbols. Only if they both agree are they equal. *)
     destruct (IHt l) as [e | n]; [idtac | right; intros e; inversion e; apply n; auto]; 
       destruct (G.funSymEqDec f f0) as [e' | n];
       [ left; rewrite e; rewrite e'; auto | right; intro e'; inversion e'; apply n; auto].
     (* Now we have decidablity on terms taken care of, if we have it for lists of terms. *)
     (* Checking whether a list is nil is trivial. *)
     destruct l'; [left; auto | right; discriminate].
     (* If the lhs is not nil, then the rhs cannot be. *)
     all: destruct l'; [right; discriminate | idtac].
     (* Finally, we just apply the IHs to both parts of the cons cells. *)
     all: match goal with
          | [|- {_ = (cons ?U ?L)} + {_ <> (cons ?U ?L)} ] =>
            let e1 := fresh "e" in
            let n1 := fresh "n" in
            let e2 := fresh "e" in
            let n2 := fresh "n" in
            let H' := fresh "H" in
            destruct (IHt U) as [e1 | n1]; [idtac | right; intro H'; inversion H'; apply n1; auto];
              destruct (IHt0 L) as [e2 | n2]; [idtac | right; intro H'; inversion H'; apply n2; auto];
                left; rewrite e1; rewrite e2; auto
          end.
  Defined.

  Import ListNotations.
  Program Fixpoint termEqBool (t u : flafolTerm) {struct t}: bool :=
    match t with
    | varTerm_b n => match u with
                    | varTerm_b m => match eq_nat_decide n m with
                                  | left _ => true
                                  | right _ => false
                                  end
                    | _ => false
                    end
    | varTerm x => match u with
                  | varTerm y => match varEqDec x y with
                                | left _ => true
                                | right _ => false
                                end
                  | _ => false
                  end
    | funTerm f args => match u with
                       | funTerm g args' =>
                         match funSymEqDec f g with
                         | right _ => false
                         | left _ => andb (Nat.eqb (length args) (length args'))
                                         (forallb (fun p => match p with (f, x) => f x end) (combine (map termEqBool args) args'))
                         end
                       | _ => false
                       end
    end.


  Theorem termEqBoolSpec : forall t u, t = u <-> termEqBool t u = true.
  Proof.
    intros t.
    induction t using flafolTerm_rect_nest
      with (Q := fun ts => forall us, ts = us <->
                             andb (Nat.eqb (length ts) (length us))
                                  (forallb
                                     (fun p => match p as p' return p' = p -> bool with
                                              (f, x) => fun _ => f x end eq_refl)
                                     (combine (map termEqBool ts) us)) = true).
    intro u; destruct u; simpl; split; intro; try (inversion H; fail).
    destruct (varEqDec x v); auto; inversion H; exfalso; apply n; auto.
    destruct (varEqDec x v); auto; [rewrite e; auto | inversion H].
    intro u; destruct u; simpl; split; intro; try (inversion H; fail).
    destruct (eq_nat_decide n n0); auto; inversion H; exfalso; apply n1; auto. apply eq_eq_nat; auto.
    destruct (eq_nat_decide n n0); try congruence. f_equal. apply eq_nat_eq; auto.
    intro u; destruct u; simpl; split; intro; try (inversion H; fail).
    destruct (funSymEqDec f f0); [ | inversion H; auto].
    inversion H.
    specialize (IHt l).
    destruct IHt.
    rewrite <- H2 at 1 3.
    apply H0; auto.
    destruct (funSymEqDec f f0); [| inversion H].
    specialize (IHt l).
    destruct IHt.
    specialize (H1 H).
    rewrite e; rewrite H1; auto.
    intros us; split; intro H.
    rewrite <- H; simpl; auto.
    apply andb_prop in H; destruct H.
    simpl in H; destruct us; simpl in H; try (inversion H; fail); auto.
    intros us; split; intro H.
    rewrite <- H; simpl; auto.
    rewrite PeanoNat.Nat.eqb_refl; simpl.
    specialize (IHt t); destruct IHt; specialize (H0 eq_refl); rewrite H0.
    specialize (IHt0 l); destruct IHt0. specialize (H2 eq_refl).
    apply andb_prop in H2; destruct H2.
    apply H4.
    apply andb_prop in H; destruct H.
    destruct us as [|u us]; try (simpl in H; inversion H; fail).
    simpl in H0; simpl in H.
    apply andb_prop in H0; destruct H0.
    rewrite <- IHt in H0.
    specialize (IHt0 us); destruct IHt0.
    rewrite H in H3; simpl in H3. specialize (H3 H1).
    rewrite H3; rewrite H0. auto.
  Qed.

  Corollary termEqBoolSpec' : forall t u, t <> u <-> termEqBool t u = false.
  Proof.
    intros t u; split; intro H.
    destruct (termEqBool t u) eqn: e; auto;
      rewrite <- termEqBoolSpec in e; exfalso; apply H; auto.
    intro Hcontra. rewrite termEqBoolSpec in Hcontra. pose proof (eq_trans (eq_sym H) Hcontra). inversion H0.
  Qed.
  
  (* Think of this as a type system for terms. 
     In the paper, terms have a single sort based on how they're built.
     Here, it's easier to do this: define all terms, and then give a type system.
     This makes it so that 
     (a) we can easily build a term of some unknown sort, and
     (b) we can build terms without needing to show that it's of some particular sort.
   *)
  Inductive hasSort : flafolTerm -> G.sort -> Prop :=
    varS : forall (x : G.var), hasSort (varTerm x) (G.VarSort x)
  | funS : forall (f : G.funSym) (args : list flafolTerm),
      hasSorts args (G.funInputTypes f) -> hasSort (funTerm f args) (G.funOutputType f)
  with
  hasSorts : list flafolTerm -> list G.sort -> Prop :=
  | nilNilS : hasSorts nil nil
  | consConsS : forall (t : flafolTerm) (sigma : G.sort) (args' : list flafolTerm) (types' : list G.sort),
      hasSort t sigma -> hasSorts args' types' -> hasSorts (t :: args') (sigma :: types').

  Scheme hasSortIndNest := Induction for hasSort Sort Prop
    with hasSortsIndNest := Induction for hasSorts Sort Prop.
  Combined Scheme hasSortssMutInd from hasSortIndNest, hasSortsIndNest.

  Notation "⊢s t ::: sigma" := (hasSort t sigma) (at level 40) : term_scope.
  Open Scope term_scope.

  Theorem sortsUnique : forall (t : flafolTerm) (sigma rho : G.sort),
      ⊢s t ::: sigma -> ⊢s t ::: rho -> sigma = rho.
  Proof.
    intros t sigma rho Hsigma Hrho.
    destruct t;
      inversion Hsigma; inversion Hrho; auto.
  Qed.

  Lemma hasSortsIn : forall args sigma t, In t args -> hasSorts args sigma -> exists s, ⊢s t ::: s.
  Proof.
    induction args; simpl; intros; auto.
    inversion H.
    destruct H; subst.
    all: inversion H0; subst; eauto.
  Qed.  

  
  Lemma hasSort_lc : forall t s, ⊢s t ::: s -> lc_term t.
  Proof.
    induction t using flafolTerm_rect_nest_prop with (Q := fun l => forall s x, In x l -> ⊢s x ::: s -> lc_term x); simpl; intros; try solve [constructor].
    - inversion H.
    - constructor.
      intros t H0.
      inversion H; subst.
      destruct (hasSortsIn args (funInputTypes f) t); eauto.
    - inversion H.
    - destruct H; subst; eauto.      
  Qed.
  Fixpoint open_term_rec (n : nat) (t₁ : flafolTerm) (t₂ : flafolTerm) : flafolTerm :=
    match t₁ with
    | varTerm_b n2 => if beq_nat n n2
                     then t₂
                     else t₁
    | funTerm f args => funTerm f (map (fun t => open_term_rec n t t₂) args)
    | _ => t₁
    end.

  Lemma WFopen_term_rec : forall t t1 t2 s1 s n, ⊢s t1 ::: s -> ⊢s t2 ::: s -> ⊢s (open_term_rec n t t1) ::: s1 -> ⊢s (open_term_rec n t t2) ::: s1.
  Proof.
     induction t using flafolTerm_rect_nest_prop with (Q := fun l => forall t1 t2 s n sigmas,  ⊢s t1 ::: s -> ⊢s t2 ::: s -> hasSorts (map (fun x => open_term_rec n x t1) l) sigmas -> hasSorts (map (fun x => open_term_rec n x t2) l) sigmas); simpl; intros; auto.
     - destruct (n0 =? n); auto.
       erewrite sortsUnique; eauto.
     - inversion H1; subst.
       constructor; auto.
       eapply IHt with (t1 := t1); eauto.
     - inversion H1; subst.
       constructor; eauto.
  Qed.

  Lemma WFhasSorts : forall l t1 t2 s n sigmas,  ⊢s t1 ::: s -> ⊢s t2 ::: s -> hasSorts (map (fun x => open_term_rec n x t1) l) sigmas -> hasSorts (map (fun x => open_term_rec n x t2) l) sigmas.
  Proof.
    induction l; simpl; intros; auto.
    inversion H1; subst.
    constructor; auto.
    eapply WFopen_term_rec with (t1:=t1); eauto.
    eapply IHl with (t1 := t1); eauto.    
  Qed.  


  (* 
     The following section says that we can infer when a term is in some particular sort. 
     
     We first provide a way to determine which sort a term _might_ have.
     If that term is well-typed, then it is in that sort.
   *)
  Section TypeInference.
    Program Definition possibleSort : forall (t : flafolTerm), lc_term t -> G.sort :=
      fun t lct => match t with
                  varTerm x => G.VarSort x
                | varTerm_b i => match (BoundVarsNotLC i lct) with end
                | funTerm f _ => G.funOutputType f
                end.

    Theorem possibleSortPossible : forall (t : flafolTerm) (sigma : G.sort) (lct : lc_term t),
        ⊢s t ::: sigma -> ⊢s t ::: (possibleSort t lct).
    Proof.
      intros t sigma lct Hsigma;
        destruct t; simpl; inversion Hsigma;
          match goal with
            [ H : ⊢s ?F ?T ::: ?S, H1 : ?S' = ?S |- ⊢s ?F ?T ::: ?S' ] =>
            rewrite H1; auto
          end.
    Qed.

    Theorem possibleSortOnlyPossible : forall (t : flafolTerm) (lct : lc_term t) (sigma : G.sort),
        ⊢s t ::: sigma -> sigma = (possibleSort t lct).
    Proof.
      exact (fun t lct sigma pf => sortsUnique t sigma (possibleSort t lct) pf (possibleSortPossible t sigma lct pf)).
    Qed.
  End TypeInference.

  (*
    This section says that type checking is decidable.
    This combines with the type inference of the last section nicely.
   *)
  Section TypeChecking.
    Definition hasSortDec' : forall (t : flafolTerm) (sigma : sort), {⊢s t ::: sigma} + {~ ⊢s t ::: sigma}.
      intros t; induction t using flafolTerm_rect_nest
                  with (Q := fun ℓ => forall sigmas : list sort, {hasSorts ℓ sigmas} + {~ hasSorts ℓ sigmas});
      simpl; intros sigma;
        match goal with
        | [ |- {⊢s varTerm_b ?n ::: ?sigma} + {~ ⊢s varTerm_b ?n ::: ?sigma} ] =>
          let H := fresh "Hcontra" in
          right; intro H; inversion H
        | [ |- {⊢s ?T ::: ?sigma} + {~ ⊢s ?T ::: ?sigma} ] =>
          destruct (G.sortEqDec sigma (match T with
                                   | varTerm x => G.VarSort x
                                   | varTerm_b _ => Principal (* Dummy value, should never matter. *)
                                   | funTerm f _ => G.funOutputType f
                                   end)); [rewrite e | right; intro H; inversion H; apply n; auto]
        | _ => idtac
        end; try (left; constructor; auto; fail).
      - destruct (IHt (G.funInputTypes f)); [left; constructor; auto | right; intro H; inversion H; auto].
      - destruct sigma; [left; constructor | right; intro H; inversion H; auto].
      - destruct sigma; [right; intro H; inversion H; auto | idtac].
        destruct (IHt s); [idtac | right; intro H; inversion H; auto].
        destruct (IHt0 sigma); [idtac | right; intro H; inversion H; auto].
        left; constructor; auto.
    Qed.

    Definition hasSortsDec : forall (ℓ : list flafolTerm) (sigmas : list sort),
        {hasSorts ℓ sigmas} + {~ hasSorts ℓ sigmas}.
      intros ℓ.
      induction ℓ.
      intros sigmas; destruct sigmas; [left; constructor | right; intros H; inversion H; auto].
      intros sigmas; destruct sigmas; [right; intros H; inversion H; auto | idtac].
      destruct (hasSortDec' a s); [idtac | right; intros H; inversion H; auto].
      destruct (IHℓ sigmas); [idtac | right; intros H; inversion H; auto].
      left; constructor; auto.
    Defined.    

    Definition hasSortDec : forall (t : flafolTerm) (lct : lc_term t), {⊢s t ::: (possibleSort t lct)} + {forall sigma : G.sort, ~ ⊢s t ::: sigma}.
      intros t lct.
      destruct (hasSortDec' t (possibleSort t lct)); [left; auto | right; intros sigma H; apply n].
      apply possibleSortPossible with (sigma := sigma); auto.
    Defined.
  End TypeChecking.

  (* 
     This section defines the free variables of some term. 
     The free variable set for a term is recursive.
     (In fact, it's finite, but we do not prove that here.)
   *)
  Section FreeVariables.
    Inductive freeInTerm : G.var -> flafolTerm -> Prop :=
      freeInVar : forall (x : G.var), freeInTerm x (varTerm x)
    | freeInFun : forall (x : G.var) (f : G.funSym) (args : list flafolTerm),
        forall (t : flafolTerm), In t args -> freeInTerm x t -> freeInTerm x (funTerm f args).
    
    Notation "x ∈FVT y" := (freeInTerm x y) (at level 40) : term_scope.
    Notation "x ∉FVT y" := (~ freeInTerm x y) (at level 40) : term_scope.

    Definition freeInTermDec : forall (x : G.var) (t : flafolTerm),
        {x ∈FVT t} + {x ∉FVT t}.
      intros x t.
      induction t using flafolTerm_rect_nest
        with (Q := fun ℓ => {exists t' : flafolTerm, In t' ℓ /\ x ∈FVT t'} + {forall t' : flafolTerm, In t' ℓ -> x ∉FVT t'}); (* Try the dumb things that often work. *)
        try (left; constructor; auto; fail); try (right; intro H; inversion H; fail);
          try (destruct IHt;
               [left; constructor; auto | right; intro H; inversion H; auto];
               fail).
      - destruct (G.varEqDec x x0);
          [left; rewrite e; constructor; auto | right; intro H; inversion H; apply n; auto].
      - destruct IHt as [e | n];
          [left; destruct e as [t' H]; destruct H as [Hin HFVT];
           apply freeInFun with (t := t'); auto
          | right].
        intro H; inversion H. unfold not in n; apply n with (t' := t); auto.
      - right; intros t' H; inversion H.
      - destruct IHt; [left; exists t; split; simpl; auto | idtac].
        destruct IHt0 as [H | H];
          [left; destruct H as [t' H]; destruct H; exists t'; simpl; split; auto | idtac].
        right; intros t' H' H''; simpl in H'; destruct H' as [H' | H'];
          [apply n; rewrite H'; auto | apply H with (t' := t'); auto].
    Defined.    

    Definition freeInTermListDec : forall (x : G.var) (ℓ : list flafolTerm),
        {exists t, In t ℓ /\ x ∈FVT t} + {forall t, In t ℓ -> x ∉FVT t}.
      intros x ℓ.
      induction ℓ.
      right; simpl; intros t H; inversion H.
      destruct IHℓ.
      - left; destruct e as [t H]; destruct H as [HIn HFVT].
        exists t; simpl; auto.
      - destruct (freeInTermDec x a).
        -- left; exists a; simpl; auto.
        -- right; intros t H; simpl in H; destruct H; auto. rewrite <- H; auto.
    Qed.
  End FreeVariables.
  Notation "x ∈FVT y" := (freeInTerm x y) (at level 40) : term_scope.
  Notation "x ∉FVT y" := (~ freeInTerm x y) (at level 40) : term_scope.

  (* 
     Substitution is important for defining the quantifiers. 
     This section defines substitution and proves some important results, like
     - Substition preserves sorts
     - Substituting a non-free variable is idempotent
   *)
  Section SafeSubstitution.
  Fixpoint substTerm (t₁ : flafolTerm) (x : G.var) (t₂ : flafolTerm) : flafolTerm :=
    match t₁ with
    | varTerm y => if G.varEqDec x y
                  then t₂
                  else t₁
    | funTerm f args => funTerm f (map (fun t => substTerm t x t₂) args)
    | _ => t₁
    end.
  Notation "t t[ x ↦ t' ]" := (substTerm t x t') (at level 39) : term_scope.

  (* Notation "t t[ x ↦ t' ]" := (substTerm t x t') (at level 39) : term_scope. *)

  Definition open_term (t1 : flafolTerm) (t2 : flafolTerm) : flafolTerm := open_term_rec 0 t1 t2.

  Lemma OpenRecLCTerm : forall t s n, lc_term t -> open_term_rec n t s = t.
  Proof.
    induction t using flafolTerm_rect_nest
      with (Q := fun ts => forall s n, (forall t, In t ts -> lc_term t) -> (map (fun t => open_term_rec n t s) ts) = ts).
    intros s n H. simpl; auto.
    intros s n0 H. inversion H.
    intros s n H. simpl.
    inversion H. rewrite IHt; auto.
    auto.
    intros s n H. simpl. rewrite IHt; auto. rewrite IHt0; auto.
    intros t0 Ht0; apply H; auto. right; auto.
    apply H; left; auto.
  Qed.

  Lemma open_term_commute_rec : forall t t1 t2 n1 n2, Nat.eqb n1 n2 = false -> lc_term t1 -> lc_term t2 -> open_term_rec n2 (open_term_rec n1 t t1) t2 = open_term_rec n1 (open_term_rec n2 t t2) t1.
    intros t. 
    induction t using flafolTerm_rect_nest_prop with (Q := fun l => forall t1 t2 n1 n2 x, Nat.eqb n1 n2 = false -> In x l -> lc_term t1 -> lc_term t2 -> open_term_rec n2 (open_term_rec n1 x t1) t2 = open_term_rec n1 (open_term_rec n2 x t2) t1); simpl; intros; auto.
    - destruct (Nat.eq_dec n1 n); simpl.      
      + rewrite e.
        destruct (Nat.eq_dec n2 n); simpl.      
        * rewrite e in H.
          rewrite e0 in H.
          rewrite <-beq_nat_refl in H.
          inversion H.
        * pose proof ((proj2 (Nat.eqb_neq _ _)) n0).
          rewrite H2.
          simpl.
          rewrite <-beq_nat_refl.
          rewrite OpenRecLCTerm; auto.
      + pose proof ((proj2 (Nat.eqb_neq _ _)) n0).
        rewrite H2.
        simpl.
        destruct (Nat.eq_dec n2 n); simpl.      
        * rewrite e.
          rewrite <-beq_nat_refl.
          rewrite OpenRecLCTerm; auto.
        * pose proof ((proj2 (Nat.eqb_neq _ _)) n3).
          rewrite H3.
          simpl.
          rewrite H2; auto.
    - f_equal.
      repeat rewrite map_isFunctorial.
      induction args; simpl; auto.
      rewrite IHt; simpl; auto.
      f_equal.
      apply IHargs; auto.
      intros.
      apply IHt; simpl; auto.
    - inversion H0.
    - case H0; simpl; auto.
      intro.
      subst; auto.      
  Qed.

  
  Theorem substTermSortPreserving : forall (t₁ : flafolTerm) (x : G.var) (t₂ : flafolTerm) (sigma : G.sort),
      ⊢s t₁ ::: sigma -> ⊢s t₂ ::: (G.VarSort x) -> ⊢s t₁ t[ x ↦ t₂ ] ::: sigma.
  Proof.  
    intros t₁;
      induction t₁ using flafolTerm_rect_nest
        with (Q := fun ℓ => forall (x : G.var) (t₂ : flafolTerm) (pf : ⊢s t₂ ::: G.VarSort x),
                      forall sigmas : list G.sort, hasSorts ℓ sigmas -> hasSorts (map (fun t => substTerm t x t₂) ℓ) sigmas);
        intros; simpl; auto; try (inversion H; constructor; apply IHt₁; auto; fail).
    - destruct (G.varEqDec x0 x); [inversion H; rewrite H1; rewrite e in H0; rewrite H1 in H0; auto | auto].
    - inversion H; constructor; [apply IHt₁; auto | idtac].
      apply IHt₁0; auto.
  Qed.

  Theorem substTermSortPreservingMap : forall (ℓ : list flafolTerm) (x : var)
                                         (t₂ : flafolTerm) (sigmas : list sort),
      ⊢s t₂ ::: (G.VarSort x) ->
      hasSorts ℓ sigmas ->
      hasSorts (map (fun t => substTerm t x t₂) ℓ) sigmas.
  Proof.
    intros ℓ x t₂ sigmas H H0.
    revert H0. revert sigmas.
    induction ℓ; intros; inversion H0.
    simpl; apply nilNilS.
    assert (hasSorts (map (fun t => t t[ x ↦ t₂ ]) ℓ) types') by (apply IHℓ; auto).
    apply consConsS.
    apply substTermSortPreserving; auto.
    unfold map in H6. apply H6.
  Qed.    

  Theorem substTermSortPreservingInv : forall (t₁ : flafolTerm) (x : G.var) (t₂ : flafolTerm) (sigma : G.sort),
      ⊢s t₂ ::: (G.VarSort x) -> ⊢s t₁ t[ x ↦ t₂ ] ::: sigma -> ⊢s t₁ ::: sigma.
  Proof.
    intros t₁;
    induction t₁ using flafolTerm_rect_nest
      with (Q := fun ℓ => forall (x : var)  (t₂ : flafolTerm) (pf : ⊢s t₂ ::: VarSort x),
                    forall sigmas : list sort,
                      hasSorts (map (fun t => substTerm t x t₂) ℓ) sigmas ->
                      hasSorts ℓ sigmas);
    intros; simpl; auto; try (inversion H; constructor; apply IHt₁; auto; fail);
      try (simpl in H0; inversion H0; constructor; apply IHt₁ with (x := x) (t₂ := t₂); auto).
    - simpl in H0; destruct (varEqDec x0 x); [idtac | auto];
        assert (sigma = VarSort x0) by (apply sortsUnique with (t := t₂); auto);
        rewrite H1; rewrite e; constructor.
    - inversion H. constructor.
      -- apply IHt₁ with (x := x) (t₂ := t₂); auto.
      -- apply IHt₁0 with (x := x) (t₂ := t₂); auto.
  Qed.

  Theorem substTermSortPreservingMapInv : forall (ℓ : list flafolTerm) (x : var)
                                            (t₂ : flafolTerm) (sigmas : list sort),
      ⊢s t₂ ::: (VarSort x) ->
      hasSorts (map (fun t => substTerm t x t₂) ℓ) sigmas ->
      hasSorts ℓ sigmas.
  Proof.
    intros ℓ; induction ℓ; intros x t₂ sigmas H1 H2; simpl in H2; inversion H2; constructor.
    apply substTermSortPreservingInv with (x := x) (t₂ := t₂); auto.
    apply IHℓ with (x := x) (t₂ := t₂); auto.
  Qed.

  Theorem substTermNonFreeEqual : forall (t₁ : flafolTerm)(x : G.var) (t₂ : flafolTerm),
      x ∉FVT t₁ -> t₁ t[ x ↦ t₂ ] = t₁.
  Proof.
    intros t₁ x t₂ H.
    induction t₁ using flafolTerm_rect_nest
      with (Q := fun ℓ => (forall t, In t ℓ -> x ∉FVT t) -> map (fun t => t t[x ↦ t₂]) ℓ = ℓ);
      simpl; auto;
      try (rewrite IHt₁; [reflexivity | idtac]; intro H'; apply H; constructor; auto; fail).
    - destruct (G.varEqDec x x0); auto. exfalso; apply H; rewrite e; constructor.
    - rewrite IHt₁; [reflexivity | idtac].
      intros t HIn HFVT.
      apply H. apply freeInFun with (t := t); auto.
    - rewrite IHt₁; [rewrite IHt₁0; [reflexivity | intros t H0] | idtac]; apply H; simpl; auto.
  Qed.

  Lemma mapSubstTermNonFreeEqual : forall (ℓ : list flafolTerm) (x : G.var) (t₂ : flafolTerm),
      (forall t, In t ℓ -> x ∉FVT t) -> map (fun t => t t[ x ↦ t₂ ]) ℓ = ℓ.
  Proof.
    intros ℓ; induction ℓ; intros.
    simpl; reflexivity.
    simpl. rewrite substTermNonFreeEqual; [idtac | apply H; simpl; auto].
    rewrite IHℓ; [reflexivity | idtac].
    intros t H0; apply H; simpl; auto.
  Qed.
  End SafeSubstitution.
  Notation "t t[ x ↦ t' ]" := (substTerm t x t') (at level 39) : term_scope.

  (* This section defines a function which ensures a variable is fresh in a term.
     I.e. that it is _not_ free in that term.
     It does this by returning a variable that is (supposed to be) non-free in that term.

     N.B.: THIS IS BROKEN.
     With the current implementation, you cannot prove that the variable you get back is in fact non-free.
     I should fix this, perhaps by using finiteness of free variables.
   *)
  
  Section Freshening.

    Import ListNotations.
    Fixpoint varsInTerm (t : flafolTerm) : list var :=
      match t with
      | varTerm x => [x]
      | varTerm_b n => []
      | funTerm _ args => flat_map varsInTerm args
      end.

    Lemma varsInTermFVT : forall (t : flafolTerm) (x : var),
        x ∈FVT t <-> In x (varsInTerm t).
    Proof.
      intros t; induction t using flafolTerm_rect_nest
                 with (Q := fun l => forall y,
                               (exists u, In u l /\ y ∈FVT u) <-> In y (flat_map varsInTerm l));
      [intro y | intro x | intro x | intro y | intro y]; simpl.
      - split; intro H; [inversion H; left; auto |];
          destruct H; [rewrite H; constructor | destruct H].
      - split; intro H; inversion H.
      - split; intro H.
        -- inversion H; apply IHt; exists t; split; auto.
        -- pose proof ((proj2 (IHt x)) H).
           destruct H0 as [u Hu]; destruct Hu;
             econstructor; eauto.
      - split; intro; destruct H.
        destruct H as [H H0]; destruct H.
      - split; intro H.
        -- apply in_or_app.
           destruct H as [u Hu]; destruct Hu.
           destruct H; [left; apply IHt; rewrite H; auto
                       | right; apply IHt0; exists u; split; auto].
        -- apply in_app_or in H; destruct H.
           exists t; split; auto. apply IHt; auto.
           pose proof ((proj2 (IHt0 y)) H).
           destruct H0 as [u Hu]; destruct Hu; exists u; split; auto.
    Qed.           
    
    Lemma varsInTermFVT' : forall (ts : list flafolTerm) (x : var),
        (exists t, In t ts /\ x ∈FVT t) <-> In x (flat_map varsInTerm ts).
    Proof.
      intro ts; induction ts; intro x; split; intro H.
      - destruct H as [t Ht]; destruct Ht as [Hcontra H]; inversion Hcontra.
      - simpl in H; inversion H.
      - simpl in H; simpl; destruct H as [t Ht]; destruct Ht as [Hin Hfvt].
        destruct Hin; apply in_or_app; [left | right]; auto.
        rewrite H; apply varsInTermFVT; auto.
        apply IHts; exists t; auto.
      - simpl in H; simpl. apply in_app_or in H; destruct H.
        exists a; split; [left; auto | apply varsInTermFVT; auto].
        pose proof ((proj2 (IHts x)) H).
        destruct H0 as [t Ht]; destruct Ht; exists t; auto.
    Qed.
    
    Definition freshInTerm (t : flafolTerm) (sigma : sort): var :=
      freshVar (varsInTerm t) (sigma : sort).

    Theorem freshInTermSameSort : forall (t : flafolTerm) (sigma : sort),
        VarSort (freshInTerm t sigma) = sigma.
    Proof.
      intros; unfold freshInTerm; apply freshVarSameSort.
    Qed.

    Theorem freshInTermIsFresh : forall (t : flafolTerm) (sigma : sort),
        (freshInTerm t sigma) ∉FVT t.
    Proof.
      intros t sigma.
      unfold freshInTerm. intro H.
      apply varsInTermFVT in H.
      eapply freshVarNotIn; eauto.
    Qed.
  End Freshening.

  Lemma TermSubstId : forall (x : var) (t : flafolTerm),
      t t[x ↦ varTerm x] = t.
  Proof.
    intros x t. generalize x. clear x.
    induction t using flafolTerm_rect_nest
      with (Q := fun l => forall x : var, map (fun u => u t[x ↦ varTerm x]) l = l);
      intro y; simpl; auto.
    - destruct (varEqDec y x); [rewrite e | idtac]; auto.
    - rewrite IHt; auto.
    - rewrite IHt; rewrite IHt0; auto.
  Qed.      

  Lemma TermsSubstId : forall (x : var) (l : list flafolTerm),
      map (fun t => t t[x ↦ varTerm x]) l = l.
  Proof.
    intros x l.
    induction l; simpl; auto.
    rewrite TermSubstId. rewrite IHl. auto.
  Qed.

  Theorem SubstWellSorted : forall (t u : flafolTerm) (x : var) (sigma : sort),
      ⊢s t ::: sigma -> ⊢s u ::: (VarSort x) -> ⊢s t t[ x ↦ u ] ::: sigma.
  Proof.
    intros t.
    induction t using flafolTerm_rect_nest
      with (Q := fun l => forall (v : flafolTerm) (y : var) (sigmas : list sort),
                    ⊢s v ::: (VarSort y) ->
                    hasSorts l sigmas ->
                    hasSorts (map (fun w => w t[y ↦ v]) l) sigmas);
      intros; auto.
    - simpl; destruct (varEqDec x0 x); auto.
      rewrite <- e in H; inversion H; auto.
    - simpl; inversion H; apply funS; apply IHt; auto.
    - simpl. inversion H0. apply consConsS; auto.
  Qed.

  Theorem SubstWellSorted' : forall (ts : list flafolTerm) (u : flafolTerm) (x : var)
                               (sigmas : list sort),
      hasSorts ts sigmas -> ⊢s u ::: (VarSort x) -> hasSorts (map (fun t => t t[x ↦ u]) ts) sigmas.
  Proof.
    intros ts.
    induction ts; intros; simpl; auto.
    inversion H; apply consConsS; [apply SubstWellSorted|]; auto.
  Qed.

  Theorem WellSortedSubst : forall (t u : flafolTerm) (x : var) (sigma : sort),
      ⊢s u ::: (VarSort x) -> ⊢s (t t[x ↦ u]) ::: sigma -> ⊢s t ::: sigma.
  Proof.
    intro t; induction t using flafolTerm_rect_nest
               with (Q := fun ts => forall u x sigmas,
                             ⊢s u ::: (VarSort x) ->
                             hasSorts (map (fun t => t t[x ↦ u]) ts) sigmas ->
                             hasSorts ts sigmas);
    [intros u y sigma Hu Ht | intros u x sigma Hu Ht | intros u x sigma Hu Ht
     | intros u x sigmas Hu Hts | intros u x sigmas Hu Hts].
    - simpl in Ht. destruct (varEqDec y x); auto.
      rewrite <- (sortsUnique _ _ _ Hu Ht); rewrite e; constructor.
    - simpl in Ht; auto.
    - simpl in Ht. inversion Ht.
      constructor; auto. eapply IHt; eauto.
    - simpl in Hts; auto.
    - simpl in Hts. inversion Hts.
      constructor; auto.
      eapply IHt; eauto.
      eapply IHt0; eauto.
  Qed.  

  Theorem WellSortedSubsts : forall (ts : list flafolTerm) (u : flafolTerm) (x : var) (sigmas : list sort),
      ⊢s u ::: (VarSort x) -> hasSorts (map (fun t => (t t[x ↦ u])) ts) sigmas
      -> hasSorts ts sigmas.
  Proof.
    intros ts; induction ts; intros.
    simpl in H0; auto.
    simpl in H0. inversion H0; econstructor; eauto.
    eapply WellSortedSubst; eauto.
  Qed.  

  Theorem RepeatedSubstTerm : forall (t : flafolTerm) (x y : var) (u : flafolTerm),
      y ∉FVT t -> ((t t[x ↦ varTerm y]) t[y ↦ u]) = (t t[x ↦ u]).
  Proof.
    intros t; induction t using flafolTerm_rect_nest
                with (Q := fun ts => forall x y u,
                               (forall t, In t ts -> y ∉FVT t) ->
                               map (fun t => t t[y ↦ u]) (map (fun t => t t[x ↦ varTerm y]) ts) =
                               map (fun t => (t t[x ↦ u])) ts);
    intros; auto.
    - simpl. destruct (varEqDec x0 x).
      simpl. destruct (varEqDec y y) as [e' | n]; [ auto | exfalso; apply n; auto].
      simpl. destruct (varEqDec y x); auto.
      exfalso; apply H. rewrite e; constructor; auto.
    - simpl; rewrite IHt; auto.
      intros t H0 H1. apply H.
      apply freeInFun with (t := t); auto.
    - simpl; rewrite IHt; [rewrite IHt0 |]; auto.
      intros t0 H0. apply H. simpl; right; auto.
      apply H; simpl; left; auto.
  Qed.
  
  Lemma FreeInSubstTFreeInSomeTerm : forall x t u, x ∈FVT (t t[x ↦ u]) -> x ∈FVT t \/ x ∈FVT u.
  Proof.
    intros x t; generalize dependent x.
    induction t using flafolTerm_rect_nest
      with (Q := fun ts => forall x u t, In t (map (fun t => t t[x ↦ u]) ts) -> x ∈FVT t -> x ∈FVT u \/ exists t', In t' ts /\ x ∈FVT t'); intros.
    simpl in H; destruct (varEqDec x0 x); [right | left]; auto.
    simpl in H; left; auto.
    simpl in H. inversion H.
    specialize (IHt x u t H3 H4).
    destruct IHt; [right; auto | ]. destruct H5; destruct H5. left; try (econstructor; eauto; fail).
    simpl in H; inversion H.
    simpl in H; destruct H.
    rewrite <- H in H0; specialize (IHt x u H0); destruct IHt.
    right; exists t; split; [simpl; left; auto | auto].
    left; auto.
    specialize (IHt0 x u t0 H H0).
    destruct IHt0; [left; auto|].
    destruct H1 as [t' H1]; destruct H1.
    right; exists t'; split; auto. simpl; right; auto.
  Qed.    

  Lemma NotFreeInTermsNotFreeInSubst : forall x t u, x ∉FVT t -> x ∉FVT u -> x ∉FVT (t t[x ↦ u]).
  Proof.
    intros x t u H H0 Hcontra.
    apply FreeInSubstTFreeInSomeTerm in Hcontra; destruct Hcontra; [apply H| apply H0]; auto.
  Qed.

  Lemma SubstitutedFree : forall t x u,  x ∈FVT (t t[x ↦ u]) -> x ∈FVT u.
  Proof.
    intro t; induction t using flafolTerm_rect_nest
               with (Q := fun ts => forall x u t,
                             In t (map (fun t => t t[x ↦ u]) ts) ->
                             x ∈FVT t -> x ∈FVT u).
    - intros x0 u H; simpl in H; destruct (varEqDec x0 x); auto; inversion H; exfalso; apply n; auto.
    - intros x u H; inversion H.
    - intros x u H; inversion H; apply IHt with (t := t); auto.
    - intros x u t H H0; inversion H.
    - intros x u t0 H H0; destruct H.
      apply IHt; auto; rewrite H; auto.
      apply IHt0 with (t := t0); auto.
  Qed.

  Lemma OpenTermRecSubst : forall t x s u n,
      x ∉FVT s -> lc_term u ->
      open_term_rec n (t t[x↦u]) s = (open_term_rec n t s) t[x↦ u].
  Proof.
    intro t; induction t using flafolTerm_rect_nest
               with (Q := fun ts => forall x s u n,
                             x ∉FVT s ->
                             lc_term u ->
                             (map (fun t : flafolTerm => open_term_rec n t s)
                                  (map (fun t : flafolTerm => t t[ x ↦ u]) ts))
                             = (map (fun t : flafolTerm => t t[ x ↦ u])
                                    (map (fun t : flafolTerm => open_term_rec n t s) ts)));
    intros; simpl.
    - destruct (varEqDec x0 x); auto; apply OpenRecLCTerm; auto.
    - destruct (PeanoNat.Nat.eqb n0 n); auto; rewrite substTermNonFreeEqual; auto.
    - apply f_equal; apply IHt; auto.
    - auto.
    - rewrite IHt; auto; apply f_equal; rewrite IHt0; auto.
  Qed.

  Theorem WellSortedLocallyClosed : forall t sigma, ⊢s t ::: sigma -> lc_term t.
  Proof.
    intros t; induction t using flafolTerm_rect_nest
                with (Q := fun ts => forall sigmas, hasSorts ts sigmas -> forall t, In t ts -> lc_term t);
    intros sigma H; inversion H; try (constructor; auto; fail).
    - constructor; apply IHt with (sigmas := funInputTypes f); auto.
    - intros t H0; inversion H0.
    - intros t1 H5. destruct H5. rewrite <- H5; apply IHt with (sigma := sigma0); auto.
      apply IHt0 with (sigmas := types'); auto.
  Qed.

  Theorem OpenTermRecForOneOpenForAllSortn : forall (t : flafolTerm) (y : var) (L : list var)
                                               (sigma rho : sort) (n : nat),
       (~ In y L) -> ⊢s varTerm y ::: sigma -> ⊢s (open_term_rec n t (varTerm y)) ::: rho
       -> forall x : var, (~ In x L) -> ⊢s varTerm x ::: sigma -> (⊢s (open_term_rec n t (varTerm x)) ::: rho).
  Proof.
    intro t; induction t using flafolTerm_rect_nest
               with (Q := fun ts => forall y L sigma rhos n,
                             (~ In y L) -> ⊢s varTerm y ::: sigma ->
                             hasSorts (map (fun t => open_term_rec n t (varTerm y)) ts) rhos ->
                             forall x, (~ In x L) -> ⊢s varTerm x ::: sigma ->
                                  hasSorts (map (fun t => open_term_rec n t (varTerm x)) ts) rhos);
    intros; try (simpl; simpl in H1; auto).
    - destruct (PeanoNat.Nat.eqb n0 n); [erewrite sortsUnique; eauto | auto].
    - inversion H1. apply funS.
      apply IHt with (y := y) (L := L) (sigma := sigma) (rhos := funInputTypes f) (n := n); auto.
    - inversion H1. apply consConsS.
      eapply IHt; eauto.
      eapply IHt0; eauto.
  Qed.  



  Lemma fvsubstTerm : forall y' y t1 t2, y' ∉FVT t1 -> y' ∉FVT t2 -> y' ∉FVT (t1 t[ y ↦ t2]).
  Proof.
    intros y' y t1.
    revert y' y.
    induction t1 using flafolTerm_rect_nest_prop with (Q := fun l => forall y y' t' t1, In t1 l -> y' ∉FVT t1 -> y' ∉FVT t' -> y' ∉FVT (t1 t[ y ↦ t'])); simpl; intros; auto.
    - destruct (varEqDec y x); auto.
    - intro h.
      inversion h; subst.
      destruct (map_preservesIn _ _ _ H4) as [ta [h1 h2]].
      revert H5.
      rewrite h2.
      apply IHt1; auto.
      intro h0.
      apply H.
      econstructor; eauto.
    - destruct H; subst; auto.
  Qed.

  Lemma openFVT : forall t1 t2 y n, y ∉FVT t1 -> y ∉FVT t2  -> y ∉FVT open_term_rec n t1 t2.
  Proof.
    induction t1 using flafolTerm_rect_nest_prop with (Q := fun l => forall y' n t' t2, In t' l -> y' ∉FVT t' -> y' ∉FVT t2 -> y' ∉FVT open_term_rec n t' t2); simpl; intros; auto.
    - destruct (PeanoNat.Nat.eqb n0 n); auto. 
    - intro h.
      inversion h; subst.
      destruct (map_preservesIn _ _ _ H4) as [ta [h1 h2]].
      revert H5.
      rewrite h2.
      apply IHt1; auto.
      intro h0.
      apply H.
      econstructor; eauto.
    - destruct H; subst; auto.
  Qed.

  
  Lemma OpenTermSubstRecAll : forall t1 t2 x u n,
      lc_term u ->
      open_term_rec n t1 t2 t[x ↦ u] = open_term_rec n (t1 t[x ↦ u]) (t2 t[x ↦ u]).
  Proof.
    intros t1;
      induction t1 using flafolTerm_rect_nest
        with (Q := fun l => forall t2 x u n, lc_term u -> map (fun t => open_term_rec n t t2 t[x ↦ u]) l = map (fun t => open_term_rec n (t t[x ↦ u]) (t2 t[x ↦ u])) l); intros t2 y u n' lcu; simpl.
    - destruct (varEqDec).  unfold open_term. symmetry; apply OpenRecLCTerm; auto.
      unfold open_term. simpl. auto.
    - unfold open_term. simpl. destruct (n' =? n); auto.
    - rewrite map_map. unfold open_term. simpl.
      rewrite map_map. apply f_equal.
      apply IHt1; auto.
    - reflexivity.
    -rewrite IHt1; auto. apply f_equal. apply IHt0; auto.
  Qed.

  Lemma OpenTermSubstAll : forall t1 t2 x u,
      lc_term u ->
      open_term t1 t2 t[x ↦ u] = open_term (t1 t[x ↦ u]) (t2 t[x ↦ u]).
  Proof.
    intros t1 t2 x u H.
    unfold open_term. apply OpenTermSubstRecAll; auto.
  Qed.

  Lemma lc_open_id : forall t1 t2 n, lc_term t1 -> open_term_rec n t1 t2 = t1.
  Proof.
    intros t1 t2 n H.
    revert t2 n.
    induction t1 using flafolTerm_rect_nest_prop with (Q := fun l => forall t2 n, (forall x, In x l -> lc_term x) -> map (fun t => open_term_rec n t t2) l = l); simpl; intros; auto.
    - inversion H.
    - rewrite IHt1; auto.
      inversion H; subst; auto.      
    - rewrite IHt1; auto.
      f_equal; auto.
  Qed.    
  
  Lemma open_term_subst_rec : forall t1 x t2 t3 n, lc_term t3 -> (open_term_rec n t1 t2) t[x ↦ t3] = open_term_rec n (t1 t[x ↦ t3]) (t2 t[x ↦ t3]).
  Proof.
    induction t1 using flafolTerm_rect_nest_prop with (Q := fun l => forall x n t2 t3, lc_term t3 -> map (fun t => (open_term_rec n t t2) t[x ↦ t3] ) l = map (fun t => open_term_rec n (t t[x ↦ t3]) (t2 t[x ↦ t3])) l); simpl; intros; auto.
    - destruct (varEqDec x0 x); simpl; auto.
      rewrite lc_open_id; auto.
    - destruct (n0 =? n); auto.
    - f_equal.
      rewrite map_isFunctorial.
      rewrite map_isFunctorial.
      rewrite IHt1; auto.
    - rewrite IHt1; auto.
      f_equal.
      auto.
  Qed.  
  
  Lemma lc_term_subst : forall t1 y t2, lc_term t1 -> lc_term t2 -> lc_term (t1 t[y ↦ t2]).
  Proof.
    induction t1 using flafolTerm_rect_nest with (Q := fun l => forall y t2, (forall x, In x l -> lc_term x) -> lc_term t2 -> forall x, In x (map (fun t => t t[ y ↦ t2]) l) -> lc_term x); intros; simpl; auto.
    - destruct (varEqDec y x); auto.
    - inversion H; subst.
      constructor.
      intros t H1.
      eapply IHt1; auto.
      apply H0.
      apply H1.
    - eapply InCons in H1.
      simpl in H.
      destruct H1; subst; auto.
      apply IHt0 with (y := y) (t2 := t2); auto.
      Unshelve.
      apply termEqDec.
  Qed.

End Term.
