Require Export Term.
Require Import Equality.
Require Import TermEquality.
Require Import Coq.Lists.List.

Import ListNotations.
Module Type TermHasSort''(G : GroundInfo)(GT : Term G) (TE : TermEquality G GT).
  Import G. Import GT. Import TE.


  Ltac FindSortEquality' l :=
    match goal with
    | [ |- ?sigma = ?sigma ] => reflexivity
    | [ e : ?sigma = ?rho |- ?sigma = ?rho ] => exact e
    | [ e : ?rho = ?sigma |- ?sigma = ?rho ] => exact (eq_sym e)
    | [ e : ?sigma = ?rho |- ?sigma = ?tau ] =>
      NotInList rho l; transitivity rho; [exact e | FindSortEquality' constr:(rho :: l)]
    | [ e : ?rho = ?sigma |- ?sigma = ?tau ] =>
      NotInList rho l; transitivity rho; [exact (eq_sym e) | FindSortEquality' constr:(rho :: l)]
    | [ t1 : ⊢s ?t ::: ?sigma, t2 : ⊢s ?t ::: ?rho |- ?sigma = ?rho ] =>
      apply (sortsUnique t sigma rho t1 t2)
    | [ t1 : ⊢s ?t ::: ?sigma |- ?sigma = (possibleSort ?t) ] =>
      apply (sortsUnique t sigma (possibleSort t) t1 (possibleSortPossible t sigma t1))
    | [ t1 : ⊢s ?t ::: ?sigma |- (possibleSort ?t) = ?sigma] =>
      apply (sortsUnique t sigma (possibleSort t) t1 (possibleSortPossible t sigma t1))
    end.

  Ltac FindSortEquality := FindSortEquality' constr:(@nil sort).

  Lemma UnifyCons : forall {A : Type} (x y : A) (xs ys : list A),
      x = y -> xs = ys -> (x :: xs) = (y :: ys).
  Proof.
    intros A x y xs ys H H0; rewrite H; rewrite H0; auto.
  Qed.

  Ltac FindListEquality' A l tac :=
    match goal with
    | [ |- ?xs = ?xs ] => reflexivity
    | [ e : ?xs = ?ys |- ?xs = ?ys ] => exact e
    | [ e : ?ys = ?xs |- ?xs = ?ys ] => exact (eq_sym e)
    | [ e : ?xs = ?zs |- ?xs = ?ys ] =>
      NotInList zs l; transitivity zs; [exact e | FindListEquality' constr:(A) constr:(zs :: l) ltac:(tac)]
    | [ e : ?zs = ?xs |- ?xs = ?ys ] =>
      NotInList zs l; transitivity zs;
      [exact (eq_sym e) | FindSortEquality' constr:(zs :: l)]
    | [|- (?x :: ?xs) = (?y :: ?ys) ] =>
      apply (@UnifyCons A x y xs ys); [tac | FindListEquality' constr:(A) constr:(@nil A) ltac:(tac)]
    end.

  Ltac FindListEquality A tac :=
    FindListEquality' constr:(A) constr:(@nil A) ltac:(tac).

  Ltac FindInputTypeEquality := FindListEquality constr:(sort) ltac:(FindSortEquality).

  Lemma UnifySorts : forall (t : flafolTerm) (sigma rho : sort),
      ⊢s t ::: sigma -> sigma = rho -> ⊢s t ::: rho.
  Proof.
    intros t sigma rho H H0; rewrite <- H0; exact H.
  Qed.

  Lemma UnifySorts' : forall (t u : flafolTerm) (sigma rho : sort),
      ⊢s t ::: sigma -> t = u -> sigma = rho -> ⊢s u ::: rho.
  Proof.
    intros t u sigma rho H H0 H1; rewrite <- H0; rewrite <- H1; auto.
  Qed.
  Lemma UnifyVarSorts : forall (x : var) (sigma : sort),
      sigma = VarSort x -> hasSort (varTerm x) sigma.
  Proof.
    intros x sigma H; rewrite H; constructor.
  Qed.

  Lemma UnifyOutputSorts : forall (f : funSym) (args : list flafolTerm) (sigma : sort),
      sigma = funOutputType f -> hasSorts args (funInputTypes f) -> hasSort (funTerm f args) sigma.
  Proof.
    intros f args sigma H H0; rewrite H; constructor; auto.
  Qed.

  Lemma UnifyHasSorts : forall (args1 args2 : list flafolTerm) (sigmas rhos : list sort),
      args1 = args2 -> sigmas = rhos -> 
      hasSorts args1 sigmas -> hasSorts args2 rhos.
  Proof.
    intros args1 args2 sigmas rhos H H0 H1; rewrite <- H; rewrite <- H0; auto.
  Qed.
  Ltac FindArgsHaveSorts'' := idtac.
  Ltac FindTermHasSort'' :=
    match goal with
    | [ ths : ⊢s ?t ::: ?sigma |- ⊢s ?t ::: ?sigma] => exact ths
    | [ ths : ⊢s ?t ::: ?sigma |- ⊢s ?t ::: (possibleSort ?t ?lct) ] =>
      apply (possibleSortPossible t sigma lct ths)
    | [ ths : ⊢s ?t ::: ?sigma |- ⊢s ?t ::: ?rho] =>
      apply (UnifySorts t sigma rho ths); FindSortEquality
    | [ ths : ⊢s ?t ::: ?sigma |- ⊢s ?u ::: ?rho] =>
      apply (UnifySorts' t u sigma rho ths); [FindTermEquality | FindSortEquality]
    | [ |- ⊢s (varTerm ?x) ::: (VarSort ?x) ] => exact (varS x)
    | [ |- ⊢s (varTerm ?x) ::: ?sigma ] =>
      apply (UnifyVarSorts x sigma); FindSortEquality
    | [ |- ⊢s (funTerm ?f ?args) ::: (funOutputType ?f) ] =>
      apply (funS f args); FindArgsHaveSorts''
    | [ |- ⊢s (funTerm ?f ?args) ::: ?sigma ] =>
      apply (UnifyOutputSorts f args); [FindArgsHaveSorts'' | FindSortEquality]
    | [ _ : context[varTerm ?x] |- ⊢s ?t ::: ?sigma ] =>
      apply (UnifySorts' (varTerm x) t (VarSort x) sigma (varS x));
      [FindTermEquality | FindSortEquality]
    | [ _ : context[funTerm ?f ?args] |- ⊢s ?t ::: ?sigma ] =>
      apply (UnifySorts' (funTerm f args) t (funOutputType f) sigma);
      [apply (funS f args); FindArgsHaveSorts'' | FindTermEquality | FindSortEquality]
    end.

  Ltac FindArgsHaveSorts'' ::=
    match goal with
    | [ ahs : hasSorts ?l ?l' |- hasSorts ?l ?l' ] => exact ahs
    | [ |- hasSorts nil nil ] => exact nilNilS
    | [ |- hasSorts (?t :: ?args) (?sigma :: ?sorts) ] =>
      apply (consConsS t sigma args sorts); [FindTermHasSort'' | FindArgsHaveSorts'']
    | [ _ : context[?sigma :: ?sigmas] |- hasSorts (?x :: ?xs) ?rhos ] =>
      apply (UnifyHasSorts (x :: xs) (x :: xs) (sigma :: sigmas) rhos eq_refl);
      [ FindInputTypeEquality | FindArgsHaveSorts'']
    end.

  Module TermHasSortNoFormulasTests.
    Lemma TermHasSortNFTest1 : forall (t : flafolTerm) (sigma : sort),
      ⊢s t ::: sigma -> ⊢s t ::: sigma.
    Proof.
      intros. FindTermHasSort''.
    Qed.

    Lemma TermHasSortNFTest2 : forall (t : flafolTerm) (lct : lc_term t) (sigma : sort),
        ⊢s t ::: sigma -> ⊢s t ::: (possibleSort t lct).
    Proof.
      intros. FindTermHasSort''.
    Qed.

    Lemma TermHasSortNFTest3 : forall (t : flafolTerm) (sigma rho : sort),
        sigma = rho -> ⊢s t ::: sigma -> ⊢s t ::: rho.
    Proof.
      intros. FindTermHasSort''.
    Qed.

    Lemma TermHasSortNFTest4 : forall (x : var), ⊢s (varTerm x) ::: (VarSort x).
    Proof.
      intros. FindTermHasSort''.
    Qed.

    Lemma TermHasSortNFTest5 : forall (x : var) (sigma : sort),
        sigma = VarSort x -> ⊢s (varTerm x) ::: sigma.
    Proof.
      intros. FindTermHasSort''.
    Qed.
    Lemma TermHasSortNFTest6 : forall (x : var) (sigma : sort) (t : flafolTerm),
        sigma = VarSort x -> t = varTerm x -> ⊢s t ::: sigma.
    Proof.
      intros.
      FindTermHasSort''.
    Qed.
    Lemma TermHasSortNFTest10 : forall (f : funSym) (t1 t2 : flafolTerm) (sigma1 sigma2 : sort),
        ⊢s t1 ::: sigma1 -> ⊢s t2 ::: sigma2 -> funInputTypes f = [sigma1; sigma2] ->
        ⊢s funTerm f [t1; t2] ::: (funOutputType f).
    Proof.
      intros. FindTermHasSort''.
    Qed.

    Lemma TermHasSortNFTexst11 : forall (f : funSym) (t1 t2 u : flafolTerm) (sigma1 sigma2 rho : sort),
        ⊢s t1 ::: sigma1 -> ⊢s t2 ::: sigma2 -> funInputTypes f = [sigma1; sigma2] ->
        u = funTerm f [t1; t2] -> rho = funOutputType f ->
        ⊢s u ::: rho.
    Proof.
      intros. FindTermHasSort''.
    Qed.
  End TermHasSortNoFormulasTests.
End TermHasSort''.