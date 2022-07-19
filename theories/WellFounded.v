Require Import
  Coq.Relations.Relation_Definitions
  Coq.Relations.Relation_Operators
  Coq.Classes.RelationClasses
  Coq.Logic.StrictProp.

Generalizable Variables A B P Q R equal.

Set Implicit Arguments.


Class WellFounded `(R: relation A) :=
  wf: well_founded R.

Class WeaklyExtensional `(equivalence: Equivalence A equal)
                   (R: relation A) :=
  weak_extensionality: forall x y, (forall t, R t x <-> R t y) -> equal x y.
    
Arguments WeaklyExtensional {A} equal {equivalence} R.

Class WellOrder `(equivalence: Equivalence A equal)
                 (R: relation A) :=
{
  WellOrder_WellFounded :> WellFounded R;
  WellOrder_Transitive :> Transitive R;
  WellOrder_WeakExtensional :> WeaklyExtensional equal R
}.

Arguments WellOrder {A} equal {equivalence} R.

(** Every well-founded relation is irreflexive. We give
    this instance low priority because for many such
    relations there will already exist a more direct proof
    of that fact. *)
#[export]
Instance wf_irrefl `{WellFounded A R}: Irreflexive R | 4.
Proof.
  intro x. induction x as [x IH] using (well_founded_ind H).
  exact (fun H => IH x H H).
Qed.


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


Section Strong_Extensionality.
  Require Import Morphisms.
  
  Context `{equivalence: Equivalence A equal}.
  Variable R: relation A.
  #[local] Infix "==" := equal (at level 70).
  #[local] Infix "<" := R (at level 70).

  Class Bisimulation (E: relation A): Prop :=
    bisimilarity: forall x y, E x y ->
      (forall a, a < x -> exists2 b, b < y & E a b)
      /\
      (forall b, b < y -> exists2 a, a < x & E a b).
    
  Class StronglyExtensional: Prop :=
    strong_extensionality: forall (E: relation A) (bisim: Bisimulation E),
      subrelation E equal.

  Let bisimilar x y := forall t, t < x <-> t < y.
  #[local] Infix "~" := bisimilar (at level 70).

  #[local] Instance bisim: Bisimulation bisimilar.
  Proof using equivalence.
    firstorder.
  Qed.

  #[local] Instance bisim_equivalence: Equivalence bisimilar.
  Proof.
    split; autounfold; unfold bisimilar; firstorder.
  Qed.

  #[global]
  Instance we_from_se {Rse: StronglyExtensional}: WeaklyExtensional equal R.
  Proof.
    exact (strong_extensionality bisim).
  Qed.

  #[global]
  Instance wf_we_is_se {Rwf: WellFounded R} {Rwe: WeaklyExtensional equal R}:
    StronglyExtensional.
  Proof.
  Abort.

End Strong_Extensionality.


#[global] Instance nat_wo: WellOrder eq lt.
Proof.
  split.
  Require Import Arith_base.
  - exact lt_wf.
  - exact lt_trans.
  - intros m n H.
    destruct (lt_eq_lt_dec n m) as [[L|E]|G]; [exfalso | auto | exfalso].
    + specialize (proj1 (H _) L). apply irreflexivity.
    + specialize (proj2 (H _) G). apply irreflexivity.
Qed.

