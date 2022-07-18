From Coq.Relations Require Import Relation_Definitions.
From Coq.Program Require Import Basics.
From Coq.Classes Require Export RelationClasses Morphisms SetoidClass.

Generalizable Variables A B C R S X Y Z equ f g h.

Class Posetoid (A: Type) :=
{
  leq: relation A;
  posetoid_preorder :> PreOrder leq
}.

Notation "x <= y" := (leq x y): type_scope.
Notation "x >= y" := (leq y x) (only parsing): type_scope.


Module Posetoid.

  Section Instances.
    Context `(posetoid: Posetoid A).

    Definition eq: relation A := relation_conjunction leq (flip leq).

    Global Instance equivalence: Equivalence eq.
    Proof.
      split; repeat destruct 1.
      - split; reflexivity.
      - split; assumption.
      - split; etransitivity; eassumption.
    Qed.

    Global Instance partial_order: PartialOrder eq leq := ltac:(easy).
    
    Global Instance setoid: Setoid A | 10 := Build_Setoid equivalence.
  End Instances.

End Posetoid.
