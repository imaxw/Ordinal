From Coq Require Import Logic.StrictProp.

(** Libraries that are used in multiple other files *)
From Coq Require Export
  Structures.Equalities
  Structures.Orders
  Classes.RelationClasses
  Classes.Morphisms
  Classes.Equivalence
  Classes.SetoidClass
  Setoids.Setoid
  Program.Basics
  Program.Combinators
  Unicode.Utf8.

Generalizable All Variables.

#[export] Set Implicit Arguments.
#[export] Set Default Goal Selector "all".

#[export] Instance pointwise_setoid `(Setoid A) (domain: Type):
  Setoid (domain → A) := Build_Setoid _.

#[export] Existing Instance proper_sym_impl_iff.

(** Some convenience notations *)
Notation "•" := tt: type_scope.
Notation "⊤" := True : type_scope.
Notation "⊥" := False : type_scope.
Notation "∅" := Empty_set : type_scope.
Infix "×" := prod (at level 40, no associativity) : type_scope.
  
Notation "∃! x .. y , P" :=
    (ex (unique (fun x => .. (ex (unique (fun y => P))) ..)))
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∃! x .. y ']' ,  '/' P ']'") : type_scope.

Notation "∄ x .. y , P" :=
  (not (ex (fun x => .. (ex (fun y => P) ) ..)))
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∄ x .. y ']' ,  '/' P ']'") : type_scope.

Notation "∃2 x , P & Q" := (ex2 (fun x => P) (fun x => Q))
  (at level 200, right associativity,
  format "'[ ' '[ ' ∃2  x ']' ,  '/' P  '&'  Q ']'") : type_scope.
  
Notation "∃2! x , P & Q" := (ex2 (unique (fun x => P) (fun x => Q)))
  (at level 200, right associativity,
  format "'[ ' '[ ' ∃2!  x ']' ,  '/' P  '&'  Q ']'") : type_scope.

Tactic Notation "∃" constr(x) := exists x.


Fixpoint iter_prod (A: Type) (n: nat): Type :=
  match n with
  | 0 => unit
  | 1 => A
  | S n => (A ^ n) × A
  end
where "A ^ n" := (iter_prod A n): type_scope.

  
Section Logic.

  Context [A B: Type]. 
  Variables L R: A → B → Prop.
  Variable P: Prop.
  
  Lemma all_ex_conj_left:
    (∀ x, ∃ y, L x y ∧ R x y) → (∀ x, ∃ y, L x y).
  Proof. firstorder. Qed.
  
  Lemma all_ex2_conj_left:
    (∀ x, ∃2 y, L x y & R x y) → (∀ x, ∃ y, L x y).
  Proof. firstorder. Qed.
  
  Lemma all_ex_conj_right:
    (∀ x, ∃ y, L x y ∧ R x y) → (∀ x, ∃ y, R x y).
  Proof. firstorder. Qed.
  
  Lemma all_ex2_conj_right:
    (∀ x, ∃2 y, L x y & R x y) → (∀ x, ∃ y, R x y).
  Proof. firstorder. Qed.

  Lemma ex_all_conj_left: (∃ x, ∀ y, L x y ∧ R x y) → (∃ x, ∀ y, L x y).
  Proof. firstorder. Qed.

  Lemma ex_all_conj_right: (∃ x, ∀ y, L x y ∧ R x y) → (∃ x, ∀ y, R x y).
  Proof. firstorder. Qed.
    
  Lemma empty_notT: ¬inhabited A → notT A.
  Proof λ H a, H (inhabits a).

End Logic.

Section Maps.

  Variables A B C C1 C2 D D1 D2: Type.

  Definition vacuous: ∅ → C := ltac:(tauto).
  Definition const: C → D → C := ltac:(tauto).
  Definition fprod: (D → C1) → (D → C2) → D → (C1 × C2) := ltac:(tauto).
  Definition fsum: (D1 → C) → (D2 → C) → D1 + D2 → C := ltac:(tauto).

  Property fpair_fst: ∀f g, ∀ x, fst (fprod f g x) = f x. trivial. Qed.
  Property fpair_snd: ∀ f g, ∀ x, snd (fprod f g x) = g x. trivial. Qed.
  Property fsum_inl: ∀ f g, ∀ x, fsum f g (inl x) = f x. trivial. Qed.
  Property fsum_inr: ∀ f g, ∀ x, fsum f g (inr x) = g x. trivial. Qed.

  Definition prod_assocL: A × (B × C) -> (A × B) × C := ltac:(tauto).
  Definition prod_assocR: (A × B) × C -> A × (B × C) := ltac:(tauto).
  Definition sum_assocL: A + (B + C) -> (A + B) + C := ltac:(tauto).
  Definition sum_assocR: (A + B) + C → A + (B + C) := ltac:(tauto).

End Maps.

Notation "⟨ ⟩" := (const tt) (format "⟨ ⟩"). 
Notation "⟨ f ⟩" := f (only parsing).
Notation "⟨ f , g , .. , h ⟩" := (fprod .. (fprod f g) .. h).
Notation "[ ]" := (@vacuous _) (format "[ ]").
Notation "[ f ]" := f (only parsing).
Notation "[ f , g , .. , h ]" := (fsum .. (fsum f g) .. h). 


Section ExistentialApplication.

  Variables (A B: Type) (pB: Prop).
  Variables P Q: A -> Prop.
  Variables sP sQ: A -> SProp.
  Variables tP tQ: A -> Type.
  
  Definition ex_apply (f: forall x:A, P x -> pB) (a: ex P) :=
    let (x, p) := a in f x p.

  Definition ex2_apply (f: forall x:A, P x -> Q x -> pB) (a: ex2 P Q) :=
   let (x, p, q) := a in f x p q.

  Definition sig_apply (f: forall x, P x -> B) (a: sig P) :=
    let (x, p) := a in f x p.

  Definition sig2_apply (f: forall x:A, P x -> Q x -> pB) (a: ex2 P Q) :=
    let (x, p, q) := a in f x p q.

  Definition sigT_apply (f: forall x, tP x -> B) (a: sigT tP) :=
    let (x, p) := a in f x p.

  Definition sigT2_apply (f: forall x, tP x -> tQ x -> B) (a: sigT2 tP tQ) :=
    let (x, p, q) := a in f x p q.

  Definition Ssig_apply (f: forall x, sP x -> B) (a: Ssig sP) :=
    f (Spr1 a) (Spr2 a).

End ExistentialApplication.

Definition unit_all_intro (P: unit -> Type): P • → ∀ x, P x.
Proof. intros; now destruct x. Defined.

Definition unit_spec (P: unit → Type): ∀ x: unit, P x → P •.
Proof. destruct x; tauto. Qed.

Ltac elim_quantifiers :=
  match goal with
  | [|- forall _ : Empty_set, _] => let a := fresh "x" in
                                    intro a; destruct a
  | [|- exists _ : Empty_set, _] => exfalso
  | [|- exists _ : unit, _] => exists tt
  | [|- forall _ : unit, _] => let a := fresh "x" in
                               intro a; destruct a
  | [H : exists _ : Empty_set, _ |- _] => let a := fresh "x" in
                                          destruct H as (a, H);
                                          destruct a
  | [H : forall _ : Empty_set, _ |- _] => clear H
  | [H : exists _ : unit, _ |- _] => let a := fresh "x" in
                                     destruct H as (a, H);
                                     destruct a
  | [H : forall _ : unit, _ |- _] => specialize (H tt)
  end.


Create HintDb relations.
#[export] Hint Immediate Equivalence_Reflexive: relations.
#[export] Hint Unfold complement: relations.
#[export] Hint Unfold flip: relations.
#[export] Hint Unfold relation_conjunction: relations.
#[export] Hint Unfold relation_disjunction: relations.
#[export] Hint Unfold Reflexive: relations.
#[export] Hint Unfold Irreflexive: relations.
#[export] Hint Unfold Symmetric: relations.
#[export] Hint Unfold Asymmetric: relations.
#[export] Hint Unfold Antisymmetric: relations.
#[export] Hint Unfold Transitive: relations.
#[export] Hint Unfold Proper: relations.
#[export] Hint Unfold respectful: relations.
#[export] Hint Unfold impl: relations.
#[export] Hint Unfold iff: relations.
#[export] Hint Unfold impl: relations.
#[export] Hint Unfold iff: relations.
#[export] Hint Unfold pointwise_equivalence: relations.
#[export] Hint Unfold relation_equivalence: relations.

Create HintDb ordinal.

Declare Scope Ord_scope.
Delimit Scope Ord_scope with Ω.
