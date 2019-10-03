  Inductive option_defined {A : Type} : option A -> Prop :=
  | defnd : forall (a : A), option_defined (Some a).

  Definition option_defined_bool : forall {A : Type}, option A -> bool :=
    fun A oa => match oa with
             | None => false
             | Some _ => true
             end.
