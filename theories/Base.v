From Ordinal Require Import CommonHeader WellFounded Notations.

Require Import PeanoNat.

Generalizable Variables A B C R X Y Z.

(** Definition of the ordered setoid of ordinal numbers, together with
    proofs that it is indeed an ordered setoid under the given relations.
    That is:
    - Ord.eq (==) is an equivalence relation;
    - Ord.lt (<) is an ==-compatible strict ordering relation;
    - Ord.le (<=) is a partial ordering relation w.r.t. ==;
    - < is a subrelation of <=.

    In the course of doing this, we also prove:
    - < is well-founded and so transfinite induction is valid;
    - < and <= are co-transitive; and
    - the constructor for Ord is ==-compatible and <=-covariant.

    Some desirable properties (such as totality) require excluded middle,
    and are deferred to the OrdClassical module.

    Implementation note:
    A rather more elegant mutually recursive definition of < and <= is
    possible, and was originally to be used here:
    - sup⁺ f <= y when, for all a:A, f(a) < y; 
    - x < sup⁺ g when, for some b:B, x <= g(b). 
       However, Coq does not accept these as fixpoint definitions since
    they descend on different parameters. It does accept them as
    inductive definitions, but this would require them to be redefined
    inside the Ord module, which causes annoying notational issues.
    We have instead included proofs of the above properties for our
    definitions, as lemmata le_lt and lt_le respectively.
*)


(** An ordinal is represented by the image of a (possibly empty) function
    with codomain the ordinals. Conceptually it 'is' the least ordinal
    greater than every element of the function's range. *)

Inductive Ord: Type := strict_sup `(f: A → Ord).
#[global] Bind Scope Ord_scope with Ord.

Notation "sup⁺" := strict_sup.


Module Ord <: EqLtLe' <: StrOrder.
  Open Scope Ord_scope.

  Definition t := Ord.
  #[global] Bind Scope Ord_scope with t.

  Definition π₁ (w: Ord): Type :=
    match w with @strict_sup A f => A end.
  
  Definition π₂ (w: Ord): π₁ w → Ord :=
    match w with @strict_sup A f => f end.

  Fixpoint le x y: Prop :=
    match x, y with
    | sup⁺ f, sup⁺ g => ∀ a, ∃ b, f a ≤ g b
    end
  where "x ≤ y" := (le x y): Ord_scope.

  Fixpoint lt x y: Prop :=
    match x, y with
    | sup⁺ f, sup⁺ g => ∃ b, ∀ a, f a < g b
    end
  where "x < y" := (lt x y): Ord_scope.

  Definition eq x y := le x y ∧ le y x.
  Global Notation "x == y" := (eq x y): Ord_scope.
  Global Notation "x =/= y" := (¬ x == y): Ord_scope.

  Definition apart x y := (lt x y ∨ lt y x).
  Global Notation "x ≶ y" := (apart x y): Ord_scope.

  Global Notation "x > y" := (y < x) (only parsing): Ord_scope.
  Global Notation "x ≥ y" := (y ≤ x) (only parsing): Ord_scope.
  
  Global Notation "x == y == z" := (x == y ∧ y == z): Ord_scope.
  Global Notation "x < y < z" := (x < y ∧ y < z): Ord_scope.
  Global Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z): Ord_scope.
  Global Notation "x ≤ y < z" := (x ≤ y ∧ y < z): Ord_scope.
  Global Notation "x < y ≤ z" := (x < y ∧ y ≤ z): Ord_scope.
  Global Notation "x < y == z" := (x ≤ y ∧ y == z): Ord_scope.
  Global Notation "x == y < z" := (x == y ∧ y < z): Ord_scope.
  Global Notation "x < y == z" := (x < y ∧ y == z): Ord_scope.
  Global Notation "x == y < z" := (x == y ∧ y < z): Ord_scope.
  Global Notation "x ≤ y == z" := (x ≤ y ∧ y == z): Ord_scope.
  Global Notation "x == y ≤ z" := (x == y ∧ y ≤ z): Ord_scope.

  
  Section Reduction_Lemmata.

    Context (w: t) `(f: A -> t) `(g: B -> t).

    Lemma le_le: (∀ a, ∃ b, f a ≤ g b) ↔ sup⁺ f ≤ sup⁺ g.
    Proof reflexivity _.

    Lemma lt_lt: (∀ a, ∃ b, f a ≤ g b) ↔ sup⁺ f ≤ sup⁺ g.
    Proof reflexivity _.

    Lemma le_lt: (∀ a, f a < w) ↔ sup⁺ f ≤ w.
    Proof using w A f.
      revert A f; induction w as [A' f' IH].
      split.
        intros Hyp a; specialize (Hyp a).
        set (xx := f a) in *; destruct xx.
        destruct Hyp; eexists; apply IH; eassumption.
      Qed.

    Lemma lt_le: (∃ a, w ≤ f a) ↔ (w < sup⁺ f).
    Proof.
      revert A f; induction w as [A' f' IH].
      split.
        intros [a H]; exists a.
        set (xx := f a) in *; destruct xx.
        intro; apply IH, H.
      Qed.

    Lemma eq_le:
      (∀a, ∃b, f a ≤ g b) → (∀b, ∃a, g b ≤ f a) → (sup⁺ f == sup⁺ g)%Ω.
    Proof. easy. Qed.

    Lemma eq_eq:
      (∀a, ∃b, f a == g b) → (∀b, ∃a, g b == f a) → (sup⁺ f == sup⁺ g)%Ω.
    Proof.
      intros H1 H2.
      pose proof (H1' := all_ex_conj_left _ _ H1); simpl in H1'.
      pose proof (H2' := all_ex_conj_left _ _ H2); simpl in H2'.
      apply eq_le; assumption.
      Qed.

  End Reduction_Lemmata.


  Section Order_Properties.

    #[export]
    Instance lt_sub_le: subrelation lt le.
    Proof.
      red; fix ϕ 1. intros [] [] []; eexists; eauto.
    Qed.

    #[export]
    Instance lt_irrefl: Irreflexive lt.
    Proof.
      intro x; induction x. firstorder.
    Qed.

    #[export]
    Instance lt_trans: Transitive lt.
    Proof.
      unfold Transitive; fix ϕ 1.
      intros [] [] [] [] [].
      eexists; eauto.
    Qed.
    Arguments lt_trans [_ _ _] _ _.

    #[export]
    Instance le_refl: Reflexive le.
    Proof.
      intro x; induction x. firstorder.
    Qed.

    #[export]
    Instance le_trans: Transitive le.
    Proof.
      unfold Transitive; fix ϕ 1.
      intros [A f] [B g] [C h]; simpl; intros H₁ H₂.
      intro a;
        specialize (H₁ a) as [b H₁];
        specialize (H₂ b) as [c H₂];
        exists c.
      eauto.
    Qed.
    Arguments le_trans [_ _ _] _ _.

    #[export]
    Instance eq_refl: Reflexive eq.
    Proof λ o, conj (le_refl o) (le_refl o).

    #[export]
    Instance eq_sym: Symmetric eq.
    Proof λ o o', proj1 (and_comm (o ≤ o') (o ≥ o')).
    Arguments eq_sym [_ _] _.

    #[export]
    Instance eq_trans: Transitive eq.
    Proof λ x y z E₁ E₂,
            let (LE₁, GE₁) := E₁ in
            let (LE₂, GE₂) := E₂ in
            conj (le_trans LE₁ LE₂) (le_trans GE₂ GE₁).
    Arguments eq_trans [_ _ _] _ _.

    #[export]
    Instance lt_strorder: StrictOrder lt := Build_StrictOrder _ _ _.

    #[export]
    Instance eq_equiv: Equivalence eq := Build_Equivalence _ _ _ _.

    #[export]
    Instance le_preorder: PreOrder le := Build_PreOrder _ _ _.

    #[export]
    Instance le_partorder: PartialOrder eq le := reflexivity _.

    #[export]
    Instance lt_wf: WellFounded lt.
    Proof.
      intro x. enough (∀ (y: Ord) (H: y ≤ x), Acc lt y).
      { apply H; reflexivity. }
      induction x as [A f IH], y as [B g].
      intro; constructor; intros z H'.
      apply lt_le in H'. destruct H' as [b H'].
      specialize (H b) as [a H].
      apply (IH a). transitivity (g b); assumption.
    Qed.

    Fixpoint lt_le_trans [x y z]: x < y -> y ≤ z -> x < z.
    Proof.
      destruct x as [A f], y as [B g], z as [C h].
      intros [b H₁] H₂; specialize (H₂ b) as [c H₂].
      eexists; eauto.
    Qed.
  
    Fixpoint le_lt_trans [x y z]: x ≤ y -> y < z -> x < z.
    Proof.
      destruct x as [A f], y as [B g], z as [C h].
      intros H₁ [c H₂]; exists c.
      firstorder.
    Qed.

    #[export]
    Instance lt_le_compat: Proper (le --> le ++> impl) lt.
    Proof.
      repeat intro.
      eapply le_lt_trans, lt_le_trans; eassumption.
    Qed.

    #[export]
    Instance lt_compat: Proper (eq ==> eq ==> iff) lt.
    Proof.
      repeat intro.
      split; destruct H, H0; intro.
      eapply le_lt_trans, lt_le_trans; eassumption.
    Qed.

    #[export]
    Instance le_compat: Proper (eq ==> eq ==> iff) le.
    Proof.
      firstorder using le_preorder.
    Qed.

    #[export]
    Instance apart_irrefl: Irreflexive apart.
    Proof λ x H, or_ind (lt_irrefl x) (lt_irrefl x) H.

    #[export]
    Instance apart_sym: Symmetric apart.
    Proof λ x y, or_ind (λ Lxy, or_intror Lxy) (λ Lyx, or_introl Lyx).

    #[export]
    Instance setoid: Setoid Ord := Build_Setoid _.
  
  End Order_Properties.
    

  Section Strict_Sup_Properties.

    Variable A: Type.

    #[export]
    Instance strict_sup_le_covariant:
      Proper (pointwise_relation A le ==> le) strict_sup.
    Proof λ f g H a, ex_intro _ a (H a).

    #[export]
    Instance strict_sup_compat:
      Proper (pointwise_relation A eq ==> eq) (@strict_sup A).
    Proof.
      firstorder.
    Qed.
  
    Property strict_sup_property (f: A → t):
      ∀ a, f a < sup⁺ f.
    Proof.
      intros; apply lt_le; now eexists.
    Qed.
  
    Property strict_sup_minimality (f: A → t):
      ∀ o: Ord, (∀ a, f a < o) → sup⁺ f ≤ o.
    Proof.
      intro; apply le_lt.
    Qed.

  End Strict_Sup_Properties.

  Section Zero.

    Definition empty_map (e: Empty_set): Ord := match e with end.
  
    Definition zero: Ord := sup⁺ empty_map.
    Notation "0" := zero: Ord_scope.

    Property zero_le: ∀ x: Ord, 0 ≤ x.
    Proof λ x, strict_sup_minimality empty_map x (Empty_set_rect _).

    Property zero_unique: ∀ z: Ord, (∀ x, z ≤ x) -> z == 0.
    Proof λ z H, conj (H 0) (zero_le z).
  
    Property le_0_is_0 w: w ≤ zero -> w == 0.
    Proof λ H, conj H (zero_le w).
  
    Property zero_not_lt: ∀ w, ¬(w  < 0).
    Proof.
      intros [] []; contradiction.
    Qed.

    Property zero_empty [A] (f: A → t):
      sup⁺ f == 0 ↔ ¬inhabited A.
    Proof.
      split.
      - intros [H _] [a].
        destruct (H a); contradiction.
      - intro H. apply empty_notT in H. apply le_0_is_0.
        intro a; contradiction.
      Qed.

    Property positive_inhabited [A] (f: A → t):
      sup⁺ f > 0 ↔ inhabited A.
    Proof.
      split; intros [a].
      - auto.
      - exists a; intros [].
    Qed.

    Property nonzero_nonempty [A] (f: A -> t):
      sup⁺ f =/= zero ↔ ¬¬inhabited A.
    Proof.
      split. intros H H'.
      apply (zero_empty f) in H'.
      contradiction.
    Qed.

  End Zero.


  Section Successor.
    (** The successor operation and its basic properties. *)

    Definition succ (x: t): t := sup⁺ (λ _: unit, x).

    #[export]
    Instance succ_lt_covariant: Proper (lt ++> lt) succ.
    Proof.
      repeat intro; simpl; repeat elim_quantifiers.
      assumption.
    Qed.

    #[export]
    Instance succ_le_covariant: Proper (le ==> le) succ.
    Proof.
      repeat intro; simpl; repeat elim_quantifiers.
      assumption.
    Qed.

    #[export]
    Instance succ_compat: Proper (eq ==> eq) succ.
    Proof.
      repeat intro; destruct H; split.
      simpl in *; repeat elim_quantifiers.
      assumption.
    Qed.

    Property lt_succ: forall x, x < succ x.
    Proof.
      intro; apply lt_le; exists tt; reflexivity.
    Qed.

    Property succ_minimality: forall x y, x < y → succ x ≤ y.
    Proof.
      intros; apply le_lt; intro; assumption.
    Qed.
    
    Property succ_le_iff_lt: forall x y, succ x ≤ y ↔ x < y.
    Proof.
      intros; split.
      - intro; apply le_lt in H; [assumption | exact tt].
      - apply succ_minimality.
    Qed.

    Property le_iff_lt_succ: forall x y, x ≤ y ↔ x < succ y.
    Proof.
      intros; split; intro.
      - apply lt_le; exists tt; assumption.
      - apply lt_le in H; destruct H as [_ H]; assumption.
    Qed.

    Property succ_unique x s:
      x < s → (∀ y, x < y → s ≤ y) → s == succ x.
    Proof.
      firstorder using lt_succ, succ_minimality.
    Qed.

    Property succ_lt_inv: ∀ x y, succ x < succ y → x < y.
    Proof.
      intros; now apply succ_le_iff_lt, le_iff_lt_succ.
    Qed.

    Property succ_le_inv: ∀ x y, succ x ≤ succ y → x ≤ y.
    Proof.
      intros; now apply le_iff_lt_succ, succ_le_iff_lt.
    Qed.

    Property succ_inj: ∀ x y, succ x == succ y → x == y.
    Proof.
      intros x y [H1 H2]; split; now apply succ_le_inv.
    Qed.
  
  End Successor.

  Notation 𝐒 := Ord.succ.


  Section Ordinality.
    (** Mapping of other sets with well-founded relations into the ordinals *)
    
    Context `{WellFounded A R}.

    Definition inj: A → Ord :=
      wf_recursive
        (λ (a: A) (ih: ∀ x: A, R x a → Ord),
          let f: {x | R x a} → Ord := sig_apply ih
            in sup⁺ f).

    Global Instance inj_covariant: Proper (R ==> lt) inj.
    Proof.
      (* Not sure how to prove this *)
    Abort.
  End Ordinality.


  Section From_Nat.
    (** Mapping of the natural numbers into the finite ordinals. *)

    Fixpoint from_nat (n:nat): Ord :=
      match n with
      | O => zero
      | S n' => 𝐒 (from_nat n')
      end.

    #[export]
    Instance from_nat_compat: Proper (Logic.eq ==> eq) from_nat := _.

    #[export]
    Instance from_nat_lt_covariant: Proper (Peano.lt ==> lt) from_nat.
    Proof.
      intros m n Hyp; induction n.
      - contradict Hyp; auto with arith.
      - inversion_clear Hyp; simpl.
        + apply lt_succ.
        + rewrite <- lt_succ. now apply IHn.
    Qed.

    #[export]
    Instance from_nat_le_covariant: Proper (Peano.le ==> le) from_nat.
    Proof.
      intros m n Hyp; induction n.
      inversion_clear Hyp; try reflexivity.
      cbn. rewrite <- lt_succ. apply IHn, H.
    Qed.
    
    Property from_nat_le_inv m n: from_nat m ≤ from_nat n → m <= n.
    Proof.
      induction m, n as [n | m | m n IH] using nat_double_ind.
      simpl; intro H; repeat elim_quantifiers.
      auto with arith.
    Qed.
    
    Property from_nat_inj m n: from_nat m == from_nat n → m = n.
      intros [H₁ H₂].
      apply from_nat_le_inv in H₁, H₂.
      auto with arith. 
    Qed.

  End From_Nat.

  
  Section Join.

    Variable I: Type.

    Let Join_map (w: I → Ord): { i: I & π₁ (w i) } → Ord :=
      λ x, π₂ (w (projT1 x)) (projT2 x).
    
    Definition Join (w: I → Ord) := sup⁺ (Join_map w).

    Property Join_ge (w: I → Ord): ∀ i, w i ≤ Join w.
    Proof.
      intro i. destruct (w i) eqn: E.
      intro a.
      change (π₁ (sup⁺ f)) in a.
      exists (existT _ i (eq_rect _ _ a _ (symmetry E))).
      subst Join_map; simpl; rewrite -> E. reflexivity.
    Qed.

    Property Join_minimal (w: I → Ord):
      ∀ j: Ord, (∀ i: I, w i ≤ j) → Join w ≤ j.
    Proof.
      intros j H; destruct j eqn: E.
      apply le_lt. intro a.
      destruct a as (i, x). subst Join_map; simpl.
      specialize (H i).
      eapply lt_le_trans. 2: exact H.
      destruct (w i); apply strict_sup_property.
    Qed.

  End Join.

  Notation "⋀ { w | i : I }" := (Join (λ i: I, w)) : Ord_scope.

End Ord.

Global Instance: RewriteRelation Ord.lt := {}.
Global Instance: RewriteRelation Ord.le := {}.
Global Instance: RewriteRelation Ord.eq := {}.
