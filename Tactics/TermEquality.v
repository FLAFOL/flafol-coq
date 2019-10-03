Require Export Term.
Require Import Equality.
Require Import Coq.Lists.List.

Import ListNotations.
Module Type TermEquality(G : GroundInfo)(GT : Term G).
  Import G. Import GT.

  Lemma UnifyFunTerms : forall {f f' : funSym} {l l' : list flafolTerm}, f = f' -> l = l' -> funTerm f l = funTerm f' l'.
  Proof.
    intros f f' l l' H H0; rewrite H; rewrite H0; reflexivity.
  Qed.

  Lemma UnifyCons : forall {A : Type} {a b : A} {l l' : list A},
      a = b -> l = l' -> (a :: l) = (b :: l').
  Proof.
    intros A a b l l' H H0; rewrite H; rewrite H0; reflexivity.
  Qed.

  Ltac FindArgsEquality := idtac.
  Ltac FindTermEquality' l :=
    match goal with
    | [ |- ?t = ?t ] => reflexivity
    | [ e : ?t = ?u |- ?t = ?u ] => exact e
    | [ e : ?u = ?t |- ?t = ?u ] => exact (eq_sym e)
    | [ e : ?x = ?z |- ?x = ?y ] =>
      NotInList z l; transitivity z; [exact e | FindTermEquality' constr:(z :: l)]
    | [ e : ?z = ?x |- ?x = ?y ] =>
      NotInList z l; transitivity z;
      [exact (eq_sym e) | FindTermEquality' constr:(z :: l)]
    | [ |- (funTerm ?f1 ?l1) = (funTerm ?f2 ?l2) ] =>
      apply UnifyFunTerms; [FindEquality | FindArgsEquality ]
    end.

  Ltac FindTermEquality := FindTermEquality' constr:(@nil flafolTerm).

  Ltac FindArgsEquality ::=
    match goal with
    | [ |- [] = [] ] => reflexivity
    | [ |- (?t :: ?l1) = (?u :: ?l2)] => apply UnifyCons;
                                       [FindTermEquality
                                       | FindArgsEquality]
    end.

  Module TermEqualityTests.
    Lemma TermEqualityTest1 : forall (t : flafolTerm), t = t.
    Proof.
      intros; FindTermEquality.  
    Qed.

    Lemma TermEqualityTest2 : forall (t u : flafolTerm), t = u -> u = t.
    Proof.
      intros t u H; FindTermEquality.
    Qed.

    Lemma TermEqualityTest3 : forall (t u v : flafolTerm), t = u -> u = v -> t = v. 
    Proof.
      intros t u v H H0; FindTermEquality.
    Qed.

    Lemma TermEqualityTest4 : forall (t u v w : flafolTerm), t = u -> t = v -> v = w -> t = w.
    Proof.
      intros; FindTermEquality.
    Qed.

    Lemma TermEqualityTest5 : forall (t u v w : flafolTerm), t = w -> t = u -> w = v -> t = v.
    Proof.
      intros; FindTermEquality.
    Qed.

    Lemma TermEqualityTest6 : forall (t u v w : flafolTerm), w = t -> t = u -> v = w -> t = v.
    Proof.
      intros; FindTermEquality.
    Qed.

    Lemma TermEqualityTest8 : forall (f1 f2 : funSym) (t1 t2 u1 u2 : flafolTerm),
        f1 = f2 -> t1 = t2 -> u1 = u2 -> funTerm f1 [t1; u1] = funTerm f2 [t2; u2].
    Proof.
      intros f1 f2 t1 t2 u1 u2 H H0 H1.
      Fail FindEquality.
      FindTermEquality.
    Qed.        
  End TermEqualityTests.    
End TermEquality.