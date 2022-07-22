From Coq Require Import Logic.StrictProp.

(** Libraries that are used in multiple other files *)
From Coq Require Export
  Structures.Equalities
  Structures.Orders
  Classes.RelationClasses
  Classes.Morphisms
  Classes.Equivalence
  Classes.SetoidClass
  Program.Basics
  Program.Combinators
  Unicode.Utf8.

Generalizable All Variables.

#[export] Set Implicit Arguments.
#[export] Set Default Goal Selector "all".
#[export] Unset Intuition Negation Unfolding.

Arguments ex_intro [_ _] _ _.
Arguments ex_intro2 [_ _ _] _ _ _.

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

Definition dcompose `(f: ∀ x: A, B x → C) (g: ∀ x :A, B x) := 
  λ x, f x (g x).
Infix "•" := dcompose (at level 40, left associativity): type_scope.
  

Section Double_Quantifier_Projections.

  Variables A B: Type.
  Variables P Q: A → B → Prop.
  Variable f: ∀ (x: A) (y: B), P x y → Q x y.

  Definition all_ex (ae: ∀ x, ∃ y, P x y): ∀ x, ∃ y, Q x y
    := λ x, let (y, p) := ae x in ex_intro y (f p).

  Definition ex_all (ea: ∃ x, ∀ y, P x y): ∃ x, ∀ y, Q x y
    := let (x, a) := ea in ex_intro x (λ y, f (a y)).
  
  Definition all_all (aa: ∀ x y, P x y): ∀ x y, Q x y
    := λ x y, f (aa x y).

  Definition ex_ex (ee: ∃ x y, P x y): ∃ x y, Q x y
    := let (x, e) := ee in let (y, p) := e in ex_intro x (ex_intro y (f p)).

End Double_Quantifier_Projections.

Arguments all_ex [_ _ _ _] _ _.
Arguments ex_all [_ _ _ _] _ _.
Arguments all_all [_ _ _ _] _ _.
Arguments ex_ex [_ _ _ _] _ _.
Print Implicit all_ex.

    
Lemma empty_notT A: ¬inhabited A → notT A.
Proof λ H a, H (inhabits a).

Lemma ex_empty [P] [Q]: (∃ x: ∅, Q x) → P.
Proof. intro H; exfalso; destruct H as [[]]. Defined.

Lemma ex_unit [P]: (∃ x: unit, P x) → P tt.
Proof. destruct 1 as [[]]; assumption. Qed.


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

  Local Coercion sig_of_sig2: sig2 >-> sig.
  Local Coercion sigT_of_sigT2: sigT2 >-> sigT.
  Local Coercion ex_of_ex2: ex2 >-> ex.

  Variables (A B: Type) (pB: Prop).
  Variables P Q: A -> Prop.
  Variables sP sQ: A -> SProp.
  Variables tP tQ: A -> Type.
  
  Definition ex_apply (f: forall x:A, P x -> pB) (a: ex P) :=
    let (x, p) := a in f x p.

  Definition ex2_apply (f: forall x:A, P x -> Q x -> pB) (a: ex2 P Q) :=
   let (x, p, q) := a in f x p q.

  Definition sig_apply (f: forall x, P x -> B) (a: sig P) :=
    f (proj1_sig a) (proj2_sig a).

  Definition sig2_apply (f: forall x:A, P x -> Q x -> B) (a: sig2 P Q) :=
    f (proj1_sig a) (proj2_sig a) (proj3_sig a).

  Definition sigT_apply (f: forall x, tP x -> B) (a: sigT tP) :=
    f (projT1 a) (projT2 a).

  Definition sigT2_apply (f: forall x, tP x -> tQ x -> B) (a: sigT2 tP tQ) :=
    f (projT1 a) (projT2 a) (projT3 a).

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


Section MoreMorphisms.

  Local Open Scope signature_scope.

  #[export] Existing Instance proper_sym_impl_iff.

  #[export]
  Instance sym_lift `(Symmetric A R) `(Symmetric A' R'): Symmetric (R ==> R').
  Proof.
    unfold Symmetric, respectful; auto.
  Qed.

End MoreMorphisms.


Definition rfcompose `(R: relation A) `(f: D → A): relation D :=
  λ x y, R (f x) (f y).

Inductive rcompose `(R: A → B → Type) `(S: B → C → Type): A → C → Type :=
| rcompose_by a b c: R a b → S b c → rcompose R S a c.

Infix "≪" := rfcompose (at level 30, no associativity): type_scope.
Infix "~" := rcompose (at level 30, no associativity): type_scope.


(** We'll be working with a number of flipped, conjoined, etc. 
  relations and these unfolds will make life easier. *)
#[export] Hint Unfold flip: core.
#[export] Hint Unfold complement: core.
#[export] Hint Unfold relation_conjunction: core.
#[export] Hint Unfold relation_disjunction: core.
#[export] Hint Unfold pointwise_relation: core.
#[export] Hint Unfold Reflexive: core.
#[export] Hint Unfold Irreflexive: core.
#[export] Hint Unfold Symmetric: core.
#[export] Hint Unfold Asymmetric: core.
#[export] Hint Unfold Antisymmetric: core.
#[export] Hint Unfold Transitive: core.
#[export] Hint Unfold Proper: core.
#[export] Hint Unfold respectful: core.
#[export] Hint Unfold impl: core.
#[export] Hint Unfold predicate_equivalence: core.
#[export] Hint Unfold predicate_implication: core.
#[export] Hint Unfold pointwise_equivalence: core.
#[export] Hint Unfold relation_equivalence: core.

Declare Scope Ord_scope.
Delimit Scope Ord_scope with Ω.

Create HintDb ord.
