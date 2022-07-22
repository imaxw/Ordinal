From Ordinal Require Import CommonHeader Base.
From Coq.Arith Require Import PeanoNat.
From Coq.Vectors Require Fin.

Generalizable Variables n w P.

Section Finiteness.
  Import Ord.
  Open Scope equiv_scope.

  (* This is in Type instead of Prop because we want to eliminate it
     to extract a witness *)
  Inductive FiniteT: t → Type :=
  | finite_zero: FiniteT zero
  | finite_succ w: FiniteT w → FiniteT (succ w)
  | finite_eq w w': w == w' → FiniteT w → FiniteT w'.

  (* Uninformative variant, if you really want it *)
  Variant Is_Finite: Ord → Prop := finite_witness w: FiniteT w → Is_Finite w.

  Class Finite (w: Ord):= finiteness: FiniteT w.

  #[export] Instance finite_proper: Proper (eq ==> iff) Is_Finite.
  Proof.
    repeat intro; split; destruct 1; constructor.
    - exact (finite_eq H X).
    - symmetry in H; exact (finite_eq H X).
  Qed.

  Section FromNatUniqueness.
    Context `(f: Nat.t -> Ord.t).
    Hypothesis f0: f Nat.zero == Ord.zero.
    Hypothesis fS: forall n, f (Nat.succ n) == Ord.succ (f n).

    Theorem from_nat_uniqueness: f == from_nat.
    Proof.
      intro n; now_show (f n == from_nat n).
      induction n.
      - trivial.
      - rewrite -> fS; now apply succ_compat.
    Qed.
  End FromNatUniqueness.

  Instance nat_Finite (n: nat): Finite (from_nat n).
  Proof.
    induction n.
    - exact finite_zero.
    - simpl. apply finite_succ, IHn.
  Defined.

  Instance nat_eq_Finite w n (EQ: from_nat n == w): Finite w.
  Proof.
    apply (finite_eq EQ), nat_Finite.
  Defined.

  Definition to_nat `(Finite w): {n:nat | w == from_nat n}.
  Proof.
    induction H as [| w H [n IH] | w w' EQ H [n IH]].
    - exists Nat.zero. reflexivity.
    - exists (Nat.succ n). apply succ_compat, IH.
    - exists n. rewrite <- EQ; assumption.
  Defined.

  Lemma Finite_ind `(Proper _ (Ord.eq ==> iff) P):
      P zero → (∀ w, P w → P (succ w)) →  ∀ `(Finite w), P w.
  Proof.
    intros H0 IH w F. induction F.
    - exact H0.
    - exact (IH w IHF).
    - rewrite <- e; exact IHF.
  Qed.

  Theorem ω_not_finite: notT (Finite (ssup from_nat)).
  Proof.
    intro H; apply to_nat in H. destruct H as [n [H _]].
    induction n.
    - specialize (H 0%nat) as [devil _]. contradiction.
    - rewrite <- le_lt in H.
      specialize (H (Nat.succ n)).
      contradict H; apply irreflexivity.
  Qed.

End Finiteness.

(*
Module FinOrd.
  Import Ord.
  #[local] Notation Fin := Fin.t.

  Local Lemma Fin0_empty: ¬inhabited (Fin 0).
  Proof λ inh, let (x) := inh in Fin.case0 _ x.

  Definition from_Fin (n:nat): Fin n -> t.
    induction n as [| n IH].
    - exact (Fin.case0 _).
    - intro x. simple inversion x.
      + exact (ssup IH).
      + exact (eq_rect _ (λ n, Fin n → t) IH _ (eq_add_S _ _ (eq_sym H0))).
  Defined.

  Property Fin_0_0: ssup (@from_Fin 0) == 0.
  Proof.
    apply zero_empty, Fin0_empty.
  Qed.

  Property Fin_S_S: ∀ n,
      ssup (@from_Fin (Nat.succ n)) == succ (ssup (@from_Fin n)).
  Proof.
    intro n. apply succ_unique.
    - now_show (ssup (@from_Fin n) < ssup (@from_Fin (Nat.succ n))).
      exists Fin.F1.
      change (from_Fin Fin.F1) with (ssup (@from_Fin n)).
      apply strict_sup_greater.
    - intros y H; apply le_lt_reduce.
      now_show (∀ x: Fin.t (Nat.succ n), from_Fin x < y).
      intro x. induction x.
      + (* F1 case *) assumption.
      + (* FS case *)
        simpl.
        transitivity (ssup (@from_Fin n)).
        * apply strict_sup_greater.
        * exact H.
  Qed.

  Theorem Fin_ordinality: ∀ n:nat, ssup (@from_Fin n) == finite n.
  Proof.
    apply finite_uniqueness; [exact Fin_0_0 | exact Fin_S_S].
  Qed.

  Definition Fin_preimage {n:nat}:
      ∀ (w:Ord) (H: w < n), {x: Fin n | from_Fin x == w}.
  induction n.
  - intros; contradict H. apply zero_not_less.
  - intros. change (w < succ n) in H.
    apply le_lt_succ in H.
    apply succ_inj in H. . simpl in H. succ_inj in H.
    *)


