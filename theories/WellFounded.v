Require Import
  Coq.Relations.Relation_Definitions
  Coq.Program.Basics
  Coq.Classes.Morphisms
  Coq.Logic.StrictProp.

Require Coq.Setoids.Setoid.

Local Open Scope signature_scope.

Generalizable Variables A P R equal.

Set Implicit Arguments.

Existing Class well_founded.

Class WeaklyExtensional `(equivalence: Equivalence A equal)
                         (R: relation A) :=
  weak_extensionality: forall x y, (forall t, R t x <-> R t y) -> equal x y.
    
Arguments WeaklyExtensional {A} equal {equivalence} R.

Class WellOrder `(equivalence: Equivalence A equal)
                 (R: relation A) :=
{
  WellOrder_Compat :> Proper (equal ==> equal ==> iff) R;
  WellOrder_WellFounded :> well_founded R;
  WellOrder_Transitive :> Transitive R;
  WellOrder_WeakExtensional :> WeaklyExtensional equal R
}.

Arguments WellOrder {A} equal {equivalence} R.


Section Induction_Principles.

  Context `{Rwf: well_founded A R}.

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

  Context `{Rwf: well_founded A R}.
  Context `{Rwf': well_founded A' R'}.

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

  (** A well-founded relation is necessarily irreflexive. (We give
      this instance low priority because for many such relations
      there will already exist a simpler proof of irreflexivity.) *)
  Global Instance wf_irrefl `{well_founded A R}: Irreflexive R | 4.
  Proof.
    intro x. induction x as [x IH] using (well_founded_ind H).
    exact (fun H => IH x H H).
  Qed.


  Global Instance wo_proper `{WellOrder A equal R}:
    Proper (equal ==> equal ==> impl) R.
  Proof.
    (* I don't even know if this is true. *)
  Abort.

End Derived_Instances.


Section Strong_Extensionality.

  Context `{equivalence: Equivalence A equal}.
  Variable R: relation A.
  Local Infix "==" := equal (at level 70).
  Local Infix "<" := R (at level 70).

  Class Bisimulation (E: relation A): Prop :=
    bisimilarity: forall x y, E x y ->
      (forall a, a < x -> exists2 b, b < y & E a b)
      /\
      (forall b, b < y -> exists2 a, a < x & E a b).
    
  Class Extensional: Prop :=
    extensionality: forall (E: relation A) (bisim: Bisimulation E),
      subrelation E equal.

  Let bisimilar x y := forall t, t < x <-> t < y.
  Local Infix "~" := bisimilar (at level 70).

  Local Instance bisim: Bisimulation bisimilar.
  Proof using equivalence.
    firstorder.
  Qed.

  Local Instance bisim_equivalence: Equivalence bisimilar.
  Proof.
    split; autounfold; unfold bisimilar; firstorder.
  Qed.

  Global Instance we_from_se {Rext: Extensional}: WeaklyExtensional equal R.
  Proof.
    exact (extensionality bisim).
  Qed.

  Global Instance wf_we_is_se {Rprop: Proper (equal ==> equal ==> iff) R}
                              {Rwf: well_founded R}
                              {Rwe: WeaklyExtensional equal R}:
    Extensional.
  Proof.
    intros E bisim.
    intros x y.
    induction x, y as [x y IH] using (wf_double_ind (R' := R)).
    intro H. apply bisim in H.
    apply weak_extensionality. split; intro L.
    - destruct (proj1 H t L) as [u L' e].
      specialize (IH t u L L' e).
      now rewrite -> IH.
    - destruct (proj2 H t L) as [u L' e].
      specialize (IH u t L' L e).
      now rewrite <- IH.
  Qed.

End Strong_Extensionality.

Arguments Extensional {_} _ _.


Global Instance nat_wo: WellOrder eq lt.
Proof.
  split.
  Require Import Arith_base.
  - solve_proper.
  - exact lt_wf.
  - exact lt_trans.
  - intros m n H.
    destruct (lt_eq_lt_dec n m) as [[L|E]|G]; [exfalso | auto | exfalso].
    + specialize (proj1 (H _) L). apply irreflexivity.
    + specialize (proj2 (H _) G). apply irreflexivity.
Qed.
