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

(** Some convenience notations *)
Notation "⊤" := True : type_scope.
Notation "⊥" := False : type_scope.
Notation "∅" := Empty_set : type_scope.
Infix "×" := prod (at level 40, no associativity) : type_scope.
  
Notation "∃! x .. y , P" :=
  (ex (unique (fun x => .. (ex (unique (fun y => P))) ..)))
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∃! x .. y ']' ,  '/' P ']'") : type_scope.

Notation "∃2 x , P & Q" := (ex2 (fun x => P) (fun x => Q))
  (at level 200, x binder, right associativity,
  format "'[ ' '[ ' ∃2  x ']' ,  '/' P  '&'  Q ']'") : type_scope.
  
Notation "∃2! x , P & Q" := (ex2 (unique (fun x => P) (fun x => Q)))
  (at level 200, x binder, right associativity,
  format "'[ ' '[ ' ∃2!  x ']' ,  '/' P  '&'  Q ']'") : type_scope.

Fixpoint iter_prod (A: Type) (n: nat): Type :=
  match n with
  | 0 => unit
  | 1 => A
  | S n => (A ^ n) × A
  end
where "A ^ n" := (iter_prod A n): type_scope.

  
Section Logic.
  
  Lemma all_ex_conj_left [A B] (L R: A → B → Prop):
    (∀ x, ∃ y, L x y ∧ R x y) → (∀ x, ∃ y, L x y).
  Proof. firstorder. Qed.
  
  Lemma all_ex2_conj_left [A B] (L R: A → B → Prop):
    (∀ x, ∃2 y, L x y & R x y) → (∀ x, ∃ y, L x y).
  Proof. firstorder. Qed.
  
  Lemma all_ex_conj_right [A B] (L R: A → B → Prop):
    (∀ x, ∃ y, L x y ∧ R x y) → (∀ x, ∃ y, R x y).
  Proof. firstorder. Qed.
  
  Lemma all_ex2_conj_right [A B] (L R: A → B → Prop):
    (∀ x, ∃2 y, L x y & R x y) → (∀ x, ∃ y, R x y).
  Proof. firstorder. Qed.

  Lemma ex_all_conj_left [A B] (L R: A → B → Prop):
    (∃ x, ∀ y, L x y ∧ R x y) → (∃ x, ∀ y, L x y).
  Proof. firstorder. Qed.

  Lemma ex_all_conj_right [A B] (L R: A → B → Prop):
    (∃ x, ∀ y, L x y ∧ R x y) → (∃ x, ∀ y, R x y).
  Proof. firstorder. Qed.
    
  Lemma empty_notT [A]: ¬inhabited A → notT A.
  Proof λ H a, H (inhabits a).

  Lemma ex_empty [P] [Q]: (∃ x: ∅, Q x) → P.
  Proof. intro H; exfalso; destruct H as [[]]. Defined.

  Lemma ex_unit [P]: (∃ x: unit, P x) → P tt.
  Proof. destruct 1 as [[]]; assumption. Qed.

End Logic.


Section Maps.

  Variables A B C C1 C2 D D1 D2: Type.

  Definition empty_map: ∅ → C := ltac:(tauto).
  Definition const: C → D → C := ltac:(tauto).
  Definition fprod: (D → C1) → (D → C2) → D → (C1 × C2) := λ f g x, (f x, g x).
  Definition fsum: (D1 → C) → (D2 → C) → (D1 + D2) → C := sum_rect (λ _, C).

  Property fpair_fst: ∀f g, ∀ x, fst (fprod f g x) = f x. trivial. Qed.
  Property fpair_snd: ∀ f g, ∀ x, snd (fprod f g x) = g x. trivial. Qed.
  Property fsum_inl: ∀ f g, ∀ x, fsum f g (inl x) = f x. trivial. Qed.
  Property fsum_inr: ∀ f g, ∀ x, fsum f g (inr x) = g x. trivial. Qed.

  Definition prod_assocL: A × (B × C) -> (A × B) × C := ltac:(tauto).
  Definition prod_assocR: (A × B) × C -> A × (B × C) := ltac:(tauto).
  Definition sum_assocL: A + (B + C) -> (A + B) + C := ltac:(tauto).
  Definition sum_assocR: (A + B) + C → A + (B + C) := ltac:(tauto).

End Maps.
Arguments empty_map {C}.
#[export] Hint Unfold const: core.
#[export] Hint Unfold empty_map: core.

Notation "⟨ ⟩" := (const tt) (format "⟨ ⟩"). 
Notation "⟨ f ⟩" := f (only parsing).
Notation "⟨ f , g , .. , h ⟩" := (fprod .. (fprod f g) .. h).
Notation "[ ]" := (@empty_map _) (format "[ ]").
Notation "[ f ]" := f (only parsing).
Notation "[ f , g , .. , h ]" := (fsum .. (fsum f g) .. h). 


Section Existential_Application.

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

End Existential_Application.

Ltac elim_quantifiers :=
  repeat match goal with
  | [|- forall _ : Empty_set, _] => intros []
  | [|- exists _ : Empty_set, _] => exfalso
  | [|- exists _ : unit, _] => exists tt
  | [|- forall _ : unit, _] => intros []
  | [H: exists _ : Empty_set, _ |- _] => destruct H as [[]]
  | [H: forall _ : Empty_set, _ |- _] => clear H
  | [H: exists _ : unit, _ |- _] => destruct H as [[] H]
  | [H: forall _ : unit, _ |- _] => specialize (H tt)
  end.

Section Minimality_and_Maximality.

  Class Minimal `(P: A → Prop) `{preo: PreOrder A R} (a: A) : Prop :=
  {
    minimal_property: P a;
    minimality: ∀ x: A, P x → R a x
  }.

  Class Maximal `(P: A → Prop) `{preo: PreOrder A R}  (a: A): Prop :=
  {
    maximal_property: P a;
    maximality: ∀ x: A, P x → R x a
  }.

  Lemma Minimal_unique `(min: Minimal A P R a)
        `{equivalence: Equivalence A equ} `{po: PartialOrder A equ R}:
    ∀ x: A, Minimal P x → equ x a.
  Proof.
    destruct min, 1; auto using antisymmetry.
  Qed.

  Lemma Maximal_unique `(max: Maximal A P R a)
        `{equivalence: Equivalence A equ} {po: PartialOrder equ R}:
    ∀ x: A, Maximal P x → equ x a.
  Proof.
    destruct max, 1; auto using antisymmetry.
  Qed.

End Minimality_and_Maximality.


Section MoreMorphisms.

  Local Open Scope signature_scope.

  #[export] Existing Instance proper_sym_impl_iff.

  #[export]
  Instance sym_lift `(Symmetric A R) `(Symmetric A' R'): Symmetric (R ==> R').
  Proof.
    unfold Symmetric, respectful; auto.
  Qed.

End MoreMorphisms.


Create HintDb rels.
#[export] Hint Immediate Equivalence_Reflexive: rels.
#[export] Hint Immediate PreOrder_Reflexive: rels.
#[export] Hint Immediate StrictOrder_Irreflexive: rels.
#[export] Hint Unfold complement: rels.
#[export] Hint Unfold flip: rels.
#[export] Hint Unfold relation_conjunction: rels.
#[export] Hint Unfold relation_disjunction: rels.
#[export] Hint Unfold pointwise_relation: rels.
#[export] Hint Unfold Reflexive: rels.
#[export] Hint Unfold Irreflexive: rels.
#[export] Hint Unfold Symmetric: rels.
#[export] Hint Unfold Asymmetric: rels.
#[export] Hint Unfold Antisymmetric: rels.
#[export] Hint Unfold Transitive: rels.
#[export] Hint Unfold Proper: rels.
#[export] Hint Unfold respectful: rels.
#[export] Hint Unfold impl: rels.
#[export] Hint Unfold iff: rels.
#[export] Hint Unfold predicate_equivalence: rels.
#[export] Hint Unfold predicate_implication: rels.
#[export] Hint Unfold pointwise_equivalence: rels.
#[export] Hint Unfold relation_equivalence: rels.

Create HintDb ord.
#[export] Hint Constructors Minimal: ord.
#[export] Hint Constructors Maximal: ord.
#[export] Hint Constructors unit: Ord.

Declare Scope Ord_scope.
Delimit Scope Ord_scope with Ω.
