Require Import Relation_Definitions Program.Basics.
Require Export SetoidClass Setoid.

Generalizable Variables A B C R S X Y Z equ f g h.

Class Posetoid (A: Type) :=
{
  leq: relation A;
  posetoid_preorder :> PreOrder leq
}.

Notation "x ≤ y" := (leq x y) (at level 70) : type_scope.
Notation "x ≥ y" := (leq y x) (at level 70, only parsing) : type_scope.


Module Posetoid.

  Section Instances.
    Context `(posetoid: Posetoid A).

    Definition eq: relation A := relation_conjunction leq (flip leq).

    Global Instance equivalence: Equivalence eq | 2.
    Proof.
      split; repeat destruct 1.
      - split; reflexivity.
      - split; assumption.
      - split; etransitivity; eassumption.
    Qed.

    Global Instance partial_order: PartialOrder eq leq.
    Proof. apply (reflexivity (R := relation_equivalence)). Qed.
    
    Global Instance setoid: Setoid A | 2 := Build_Setoid equivalence.
  End Instances.

End Posetoid.