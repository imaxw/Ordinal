Require Import
  Coq.Relations.Relation_Definitions
  Coq.Classes.RelationClasses
  Coq.Logic.StrictProp.

Generalizable Variables A B P Q R equal domain.

Set Implicit Arguments.


Class WellFounded `(R: relation A) :=
  wf: well_founded R.

Class WeaklyExtensional `(equivalence: Equivalence domain equal)
                   (R: relation domain) :=
  weak_extensionality: forall x y, (R x y <-> R y x) -> equal x y.
    
Arguments WeaklyExtensional {domain} equal {equivalence} R.

Class WellOrder `(equivalence: Equivalence domain equal)
                 (R: relation domain) :=
{
  WellOrder_WellFounded :> WellFounded R;
  WellOrder_Transitive :> Transitive R;
  WellOrder_WeakExtensional :> WeaklyExtensional equal R
}.

Arguments WellOrder {domain} equal {equivalence} R.


Section Induction_Principles.

  Context `{Rwf: WellFounded A R}.

  Definition wf_rect := well_founded_induction_type Rwf.
  Definition wf_rec := well_founded_induction Rwf.
  Definition wf_ind := well_founded_ind Rwf.

  Definition wf_sind (P: A -> SProp) :=
    fun ih a => Acc_sind P (fun x _ => ih x) (Rwf a).

  Definition wf_recursive (B: Type):
      (forall x : A, (forall y : A, R y x -> B) -> B) -> A -> B
    := well_founded_induction_type Rwf (fun _ => B).
  
  Lemma infinite_descent (P: A -> Prop):
      (forall x: A, P x -> exists2 z, R z x & P z) ->
      forall a: A, ~ P a.
  Proof.
    intros DH a. induction a as [x IH] using wf_ind.
    intro H.
    specialize (DH x H) as [z H1 H2].
    exact (IH z H1 H2).
  Qed.
  
  Lemma infinite_descent_S (P: A -> SProp):
      (forall x: A, P x -> Squash (exists2 z, R z x & Box (P z))) ->
      forall a: A, P a -> sEmpty.
  Proof.
    intros DH a. induction a as [x IH] using wf_sind.
    intro H.
    specialize (DH x H) as [[y H1 [H2]]].
    exact (IH y H1 H2).
  Qed.

  Definition infinite_descent_T (P: A -> Type):
      (forall x: A, P x -> {z & R z x & P z}) ->
      forall a: A, notT (P a)
    := fun DH =>
        wf_rect _
          (fun a IH H =>
            let (z, H1, H2) := (DH a H) in IH z H1 H2).

End Induction_Principles.


Section Double_Induction_Principles.

  Context `{Rwf: WellFounded A R}.
  Context `{Rwf': WellFounded A' R'}.

  Definition wf_double_rect (P: A -> A' -> Type):
      (forall x y,
        (forall x' y', R x' x -> R' y' y -> P x' y') ->
        P x y) ->
      forall a b, P a b.
  Proof.
    induction a using wf_rect; firstorder.
  Defined.

  Definition wf_double_sind (P: A -> A' -> SProp):
      (forall x y,
        (forall x' y', R x' x -> R' y' y -> P x' y') ->
        P x y) ->
      forall a b, P a b.
  Proof.
    induction a using wf_sind; firstorder.
  Defined.

  Definition wf_double_rec (P: A -> A' -> Set) := wf_double_rect P.
  Definition wf_double_ind (P: A -> A' -> Prop) := wf_double_rect P.

  Definition wf_double_recursive (B: Type):
      (forall x y,
        (forall x' y', R x' x -> R' y' y -> B) -> B) ->
      A -> A' -> B
    := wf_double_rect (fun _ _ => B).

End Double_Induction_Principles.

  

Section Derived_Instances.

  Context `{Rwf: WellFounded A R}.
  Context `{Rwf': WellFounded A' R'}.

  #[local] Infix "≺" := R (at level 70).
  #[local] Infix "⊀" := (complement R) (at level 70).
  #[local] Infix "≺'" := R' (at level 70).

(** Every well-founded relation is irreflexive. We give
    this instance low-ish priority because for many such
    relations there will already exist a more direct proof
    of that fact. *)
  #[export]
  Instance wf_irrefl: Irreflexive R | 5.
  Proof.
    intro x. induction x as [x IH] using wf_ind.
    exact (fun H => IH x H H).
  Qed.

End Derived_Instances.
