Require Import Relations Morphisms Setoid.

Local Open Scope signature_scope.

Generalizable All Variables.

Set Implicit Arguments.

Existing Class well_founded.
Arguments well_founded_induction_type {_ _ _}.
Arguments well_founded_induction {_ _ _}.
Arguments well_founded_ind {_ _ _}.
Arguments Fix {_ _ _}.

Global Instance wf_irrefl `{well_founded A R}: Irreflexive R | 4.
Proof.
  intro x. induction x as [x IH] using well_founded_ind.
  exact (fun H => IH x H H).
Qed.

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


Definition well_founded_induction_S `{Rwf: well_founded A R} :=
  fun (P: A -> SProp) ih a => Acc_sind P (fun x _ => ih x) (Rwf a).


Section Infinite_Descent.

  Context `{Rwf: well_founded A R}.
  
  Lemma infinite_descent (P: A -> Prop):
      (forall x: A, P x -> exists2 z, R z x & P z) ->
      forall a: A, ~ P a.
  Proof.
    intros DH a. induction a as [x IH] using well_founded_ind.
    intro H.
    specialize (DH x H) as [z H1 H2].
    exact (IH z H1 H2).
  Qed.

  Definition infinite_descent_type (P: A -> Type):
      (forall x: A, P x -> {z & R z x & P z}) ->
      forall a: A, notT (P a)
    := fun DH =>
        well_founded_induction_type _
          (fun a IH H =>
            let (z, H1, H2) := (DH a H) in IH z H1 H2).

End Infinite_Descent.


Section Double_Induction_Principles.

  Context `{Rwf: well_founded A R}.
  Context `{Rwf': well_founded A' R'}.

  Definition wf_double_rect (P: A -> A' -> Type):
      (forall x y,
        (forall x' y', R x' x -> R' y' y -> P x' y') ->
        P x y) ->
      forall a b, P a b.
  Proof.
    induction a using well_founded_induction_type; firstorder.
  Defined.

  Definition wf_double_sind (P: A -> A' -> SProp):
      (forall x y,
        (forall x' y', R x' x -> R' y' y -> P x' y') ->
        P x y) ->
      forall a b, P a b.
  Proof.
    induction a using well_founded_induction_S; firstorder.
  Defined.

  Definition wf_double_rec (P: A -> A' -> Set) := wf_double_rect P.
  Definition wf_double_ind (P: A -> A' -> Prop) := wf_double_rect P.

End Double_Induction_Principles.


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
    extensionality: forall `(Bisimulation E), subrelation E equal.

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

Arguments Bisimulation {_} _ _.
Arguments Extensional {_} _ _.


Section Simulation.

  Context `{woA: WellOrder A eqA ltA}.
  Context `{woB: WellOrder B eqB ltB}.

  Class Simulation (f: A -> B) : Prop :=
  {
    Simulation_proper :> Proper (ltA ==> ltB) f;
    Simulation_lt_to_eq : forall t x, ltB t (f x) -> exists2 y, ltA y x & eqB t (f y)
  }.

  (*Lemma Simulation_Bisimulation `(Simulation f): Bisimulation ltA (fun a a' => eqB (f a) (f a')).
  Proof.
    destruct H as [pf hf].
    intros a a' Eq1.
    split.
    revert a' Eq1.
    induction a as [a IH] using well_founded_ind.
    - intros a' Eq1 x Lt1.
      specialize (hf (f x) a (pf _ _ Lt1)).
      destruct hf as [y Lt2 Eq2].
      specialize (IH x Lt1 y Eq2).
      exists y.
      + 
  Qed.*)

  Lemma Simulation_unique `(simf : Simulation f) `(simg : Simulation g) :
  pointwise_relation _ eqB f g.
  Proof.
  Abort.



End Simulation.


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
