From Coq.Relations Require Import Relation_Definitions.
From Coq.Program Require Import Basics.

From Coq.Classes Require Export RelationClasses Morphisms SetoidClass.

Generalizable All Variables.


Class StrictOrderedSetoid `(Setoid A) :=
{
  less: relation A;
  order_compatibility :> Proper (equiv ==> equiv ==> iff) less;
  StrictOrderedSetoid_StrictOrder :> StrictOrder less;
}.

Notation "x < y" := (less x y): type_scope.
Notation "x > y" := (less y x) (only parsing): type_scope.

Section BasicProperties.

  Context `(StrictOrderedSetoid A).
  
  Lemma setoid_irreflexivity: forall x x': A, x == x' -> ~(x < x').
  Proof.
    intros x x' E L.
    rewrite <- E in L.
    contradict L. apply irreflexivity.
  Qed.
  
  Lemma setoid_irreflexivity_contra: forall x x': A, x < x' -> x =/= x'.
  Proof.
    firstorder using setoid_irreflexivity.
  Qed.

End BasicProperties.


Section Covariance_Contravariance.

  Section GeneralDefinition.

    Context `{R: relation A} `{R': relation A'}.

    Class Covariant (f: A -> A'): Prop :=
      covariance: Proper (R ++> R') f.

    Class Contravariant (f: A -> A'): Prop :=
      contravariance: Proper (R --> R') f.

  End GeneralDefinition.

  Arguments Covariant {_} _ {_} _ _.
  Arguments Contravariant {_} _ {_} _ _.

  Instance contra_domain_flip `(Contravariant A R A' R' f):
    Covariant (flip R) R' f
    := contravariance.

  Instance contra_codomain_flip `(Contravariant A R A' R' f):
    Covariant R (flip R') f
    := fun x y => contravariance y x.


  Section Equivalences.
    Context `{Equivalence A equ} `{Equivalence A' equ'}.
    
    Global Instance equiv_contra_co `(Contravariant A equ A' equ' f):
      Covariant equ equ' f
      := fun x y E => contravariance x y (symmetry E).

    Global Instance equiv_co_contra `(Covariant A equ A' equ' f):
      Contravariant equ equ' f
      := fun x y E => covariance x y (symmetry E).
  End Equivalences.

  Section StrictOrders.
    Context `{StrictOrder A R} `{StrictOrder A' R'}.
    Context `(Covariant _ R _ R' f).

    Lemma covariant_inv: forall x x': A, R' (f x) (f x') -> ~(R x' x).
    Proof.
      intros x x' rel' rel.
      apply covariance in rel.
      apply (asymmetry rel rel').
    Qed.
    


  End StrictOrders.
  
  Lemma strict_covariant_quasi_injectivity `(StrictCovariant f):
      forall x x': A, f x == f x' -> ~(x < x').
  Proof.
    intros x x' E L.
    apply (proper_prf   f) in L.
    contradict L. now apply setoid_irreflexivity.
  Qed.
  
  Corollary strict_covariant_quasi_injectivity_2 `(StrictCovariant f):
      forall x x': A, f x == f x' -> ~(x' < x).
  Proof.
    intros x x' E. setoid_symmetry in E.
    exact (strict_covariant_quasi_injectivity H3 _ _ E).
  Qed.

  Definition strict_downward_closed `(StrictCovariant f) :=
    forall y: B,
      (exists x: A, f x == y) ->
        forall y': B, y' < y -> exists x': A, f x' == y'.
  
  Definition strict_upward_closed `(StrictCovariant f) :=
    forall y: B,
      (exists x: A, f x == y) ->
        forall y': B, y < y' -> exists x': A, f x' == y'.

End Covariance_Contravariance.
