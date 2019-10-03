Require Import Coq.Lists.List.
Import ListNotations.
Ltac NotInList a l :=
  match l with
  | nil => idtac
  | a :: _ => fail 1
  | _ :: ?l' => NotInList a l'
  end.

Ltac FindEquality' l :=
  match goal with
  | [ |- ?x = ?x ] => reflexivity
  | [ e : ?x = ?y |- ?x = ?y ] => exact e
  | [ e : ?y = ?x |- ?x = ?y ] => exact (eq_sym e)
  | [ e : ?x = ?z |- ?x = ?y ] =>
    NotInList z l; transitivity z; [exact e | FindEquality' constr:(z :: l)]
  | [ e : ?z = ?x |- ?x = ?y ] =>
    NotInList z l; transitivity z; [exact (eq_sym e) | FindEquality' constr:(z :: l)]
  end.

Ltac FindEquality :=
  match goal with
  | [ |- ?x = ?y ] => let typ := type of x in
                    FindEquality' constr:(@nil typ)
  end.

Module FindEqualityTests.
Lemma FindEqualityTest1 : forall {A : Type} (x : A), x = x.
Proof.
  intros; FindEquality.
Qed.

Lemma FindEqualityTest2 : forall {A : Type} (x y : A), x = y -> y = x.
Proof.
  intros A x y H; FindEquality.
Qed.

Lemma FindEqualityTest3 : forall {A : Type} (x y z : A), x = y -> y = z -> x = z. 
Proof.
  intros A x y z Hxy Hyz; FindEquality.
Qed.

Lemma FindEqualityTest4 : forall {A : Type} (a b c d : A), a = b -> a = c -> c = d -> a = d.
Proof.
  intros. FindEquality.
Qed.

Lemma FindEqualityTest5 : forall {A : Type} (a b c d : A), a = d -> a = b -> d = c -> a = c.
Proof.
  intros; FindEquality.
Qed.

Lemma FindEqualityTest6 : forall {A : Type} (a b c d : A), d = a -> a = b -> c = d -> a = c.
Proof.
  intros; FindEquality.
Qed.
End FindEqualityTests.