
Inductive Either : Type -> Type -> Type :=
| Left : forall {A B : Type}, A -> Either A B
| Right : forall {A B : Type}, B -> Either A B.