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
Print Ord.


#[global] Notation "sup⁺" := strict_sup: Ord_scope.


Module Ord <: EqLtLe' <: StrOrder.
  Open Scope Ord_scope.

  Definition t := Ord.
  #[global] Bind Scope Ord_scope with t.

  Definition src (w: Ord): Type :=
    match w with @strict_sup A f => A end.
  
  Definition src_map (w: Ord): src w → Ord :=
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
  #[global] Notation "x == y" := (eq x y): Ord_scope.
  #[global] Notation "x =/= y" := (¬ x == y): Ord_scope.

  Definition apart x y := (lt x y ∨ lt y x).
  #[global] Notation "x ≶ y" := (apart x y): Ord_scope.

  #[global] Notation "x > y" := (y < x) (only parsing): Ord_scope.
  #[global] Notation "x ≥ y" := (y ≤ x) (only parsing): Ord_scope.
  
  #[global] Notation "x == y == z" := (x == y ∧ y == z): Ord_scope.
  #[global] Notation "x < y < z" := (x < y ∧ y < z): Ord_scope.
  #[global] Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z): Ord_scope.
  #[global] Notation "x ≤ y < z" := (x ≤ y ∧ y < z): Ord_scope.
  #[global] Notation "x < y ≤ z" := (x < y ∧ y ≤ z): Ord_scope.
  #[global] Notation "x < y == z" := (x ≤ y ∧ y == z): Ord_scope.
  #[global] Notation "x == y < z" := (x == y ∧ y < z): Ord_scope.
  #[global] Notation "x < y == z" := (x < y ∧ y == z): Ord_scope.
  #[global] Notation "x == y < z" := (x == y ∧ y < z): Ord_scope.
  #[global] Notation "x ≤ y == z" := (x ≤ y ∧ y == z): Ord_scope.
  #[global] Notation "x == y ≤ z" := (x == y ∧ y ≤ z): Ord_scope.

  
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

    Fixpoint lt_le_trans [x y z]: x < y -> y ≤ z -> x < z.
    Proof.
      destruct x, y, z.
      intros [b H₁] H₂; specialize (H₂ b) as [c H₂].
      exists c; eauto.
    Qed.
  
    Fixpoint le_lt_trans [x y z]: x ≤ y -> y < z -> x < z.
    Proof.
      destruct x, y, z.
      intros H₁ [c H₂].
      exists c; firstorder.
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
    Proof. solve_proper. Qed.

    #[export]
    Instance apart_irrefl: Irreflexive apart.
    Proof λ x H, or_ind (lt_irrefl x) (lt_irrefl x) H.

    #[export]
    Instance apart_sym: Symmetric apart.
    Proof λ x y, or_ind (λ Lxy, or_intror Lxy) (λ Lyx, or_introl Lyx).

    #[export]
    Instance apart_proper: Proper (eq ==> eq ==> iff) apart.
    Proof.
      intros x y E x' y' E'.
      split; intro.
      destruct H; [left | right].
      try now rewrite <- E, <- E'.
      try now rewrite -> E, -> E'.
    Qed.

    #[export]
    Instance setoid: Setoid Ord := Build_Setoid _.
  
  End Order_Properties.
    

  Section Strict_Sup_Properties.

    Variable A: Type.

    #[export]
    Instance strict_sup_le_covariant: Proper (pointwise_relation A le ==> le) sup⁺.
    Proof. firstorder. Qed.

    #[export]
    Instance strict_sup_compat: Proper (pointwise_relation A eq ==> eq) sup⁺.
    Proof. firstorder. Qed.
  
    Property strict_sup_property (f: A → Ord):
        Minimal (λ o: Ord, ∀ a, f a < o) (sup⁺ f).
    Proof.
      split.
      - intros; apply lt_le; now eexists.
      - intro; apply le_lt.
    Qed.
    
    Lemma compose_le:
      ∀ B (f: A → B) (g: B → Ord), sup⁺ (g ∘ f) ≤ sup⁺ g.
    Proof.
      intros until a; now exists (f a).
    Qed.

  End Strict_Sup_Properties.


  Section More_Order_Properties.

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

    #[export]
    Instance lt_we: WeaklyExtensional eq lt.
    Proof.
      intros x y H; split.
      induction x as [A f IH], y as [B g]. simpl.
      - intro a. apply lt_le.
        destruct (strict_sup_property f).
        exact (proj1 (H (f a)) (minimal_property a)).
      - intro b. apply lt_le.
        destruct (strict_sup_property g).
        exact (proj2 (H (g b)) (minimal_property b)).
    Qed.

    #[export]
    Instance lt_wo: WellOrder eq lt := Build_WellOrder _ _ _.

  End More_Order_Properties.


  Section Propriety.

    #[local] Open Scope signature_scope.


    Variable Q: ∀ A, (A → Ord) → Prop.
    Let P (o: Ord) := Q (src_map o).

    Hypothesis proper: Proper (eq ==> iff) P.

    #[export]
    Instance proper_is_pointwise_proper A:
      Proper (pointwise_relation A eq ==> iff) (@Q A).
    Proof.
      intros x y H.
      now apply strict_sup_compat, proper in H.
    Qed.

    Theorem source_irrelevance (o: Ord):
    ∀ A (f: A → Ord), sup⁺ f == o → Q f → P o.
    Proof.
      intros A f Eq. now rewrite <- Eq.
    Qed.

    Theorem source_irrelevance_inv (o: Ord):
    P o → ∀ A (f: A → Ord), sup⁺ f == o → Q f.
    Proof.
      intros H A f Eq. now rewrite <- Eq in H.
    Qed.

  End Propriety.


  Section Zero.

    Definition zero: Ord := sup⁺ empty_map.

    Property zero_le: ∀ x: Ord, zero ≤ x.
    Proof.
      intro; apply le_lt; tauto.
    Qed.

    #[export] Instance zero_minimal: Minimal (const ⊤) zero.
    Proof.
      split; auto using zero_le.
    Qed.

    Definition zero_unique z: (∀ x, z ≤ x) -> z == zero.
    Proof.
      firstorder using zero_minimal.
    Qed.
  
    Property le_zero_is_zero w: w ≤ zero -> w == zero.
    Proof λ H, conj H (zero_le w).
  
    Property nlt_zero: ∀ w, ¬(w  < zero).
    Proof.
      intros [] []; contradiction.
    Qed.

    Property zero_empty [A] (f: A → t):
      sup⁺ f == zero ↔ ¬inhabited A.
    Proof.
      split.
      - intros [H _] [a].
        destruct (H a); contradiction.
      - intro H. apply empty_notT in H.
        apply le_zero_is_zero.
        intro a; contradiction.
      Qed.

    Property positive_inhabited [A] (f: A → t):
      sup⁺ f > zero ↔ inhabited A.
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

  #[global] Notation "0" := zero: Ord_scope.


  Section Successor.
    (** The successor operation and its basic properties. *)

    Definition succ (o: Ord): Ord := sup⁺ (λ _:unit, o).

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

    #[export]
    Instance succ_property (o: Ord): Minimal (lt o) (succ o).
    Proof.
      split.
      - apply lt_le; exists tt; reflexivity.
      - intros; apply le_lt; intro; assumption.
    Qed.

    Definition succ_unique (o: Ord) := Minimal_unique (succ_property o).
    
    Property succ_le_iff_lt: forall x y, succ x ≤ y ↔ x < y.
    Proof.
      intros; split.
      - intro; apply le_lt in H; [assumption | constructor].
      - apply succ_property.
    Qed.

    Property le_iff_lt_succ: forall x y, x ≤ y ↔ x < succ y.
    Proof.
      intros; split; intro H.
      - apply -> lt_le; repeat constructor; assumption.
      - apply <- lt_le in H; destruct H; assumption.
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
      destruct 1; split; now apply succ_le_inv.
    Qed.
  
  End Successor.

  #[global] Notation "'S'" := Ord.succ: Ord_scope.


  Section Limit_and_Successor_Ordinals.
    
    Definition Is_successor (o: Ord) :=  ∃ p: Ord, S p == o.

    Definition Is_limit (o: Ord) := ∀ p: Ord, S p =/= o.

    #[export]
    Instance: Proper (eq ==> iff) Is_successor.
    Proof.
      intros x y E; split.
      intros [p H]. exists p. rewrite H.
      2: symmetry.
      exact E.
    Qed.

    #[export]
    Instance: Proper (eq ==> iff) Is_limit.
    Proof.
      split. unfold Is_limit. intros.
      1: rewrite <- H. 2: rewrite -> H.
      apply H0.
    Qed.

    (** Constructively we cannot prove every ordinal is either a
     successor or a limit ordinal, but we can prove the following. *)

    Fact limit_nand_successor (o: Ord): ¬(Is_limit o ∧ Is_successor o).
    Proof. firstorder. Qed.

    Fact nn_limit_or_successor (o: Ord): ¬¬(Is_limit o ∨ Is_successor o).
    Proof. firstorder. Qed.

    Fact not_successor_is_limit (o: Ord): ¬Is_successor o → Is_limit o.
    Proof. firstorder. Qed.

    (** An ordinal is a successor just if every map into the ordinals
    specifying it has a maximal element. *)

    Lemma successor_iff_max (o: Ord):
      Is_successor o ↔ ∀ I (w: I → Ord),
        sup⁺ w == o → ∃ i: I, ∀ i': I, w i ≥ w i'.
    Proof.
      split.
      - intros [o' s] I w Eq.
        rewrite <- Eq in s; clear Eq o.
        specialize (proj1 s tt) as [i s1];
        specialize (proj2 s i) as [[] s2];
        pose proof (Eq' := conj s1 s2: o' == w i); clear s1 s2.
        rewrite -> Eq' in s; clear Eq' o'.
        exists i.
        destruct s as [s1 s2]; simpl in *; elim_quantifiers.
        intro i'; specialize (s2 i') as [[] s2]. assumption.
      - intros; destruct o.
        specialize (H A f (reflexivity _)) as [a H].
        unfold Is_successor.
        exists (f a). split; simpl; elim_quantifiers.
        + exists a; reflexivity.
        + intro; exists tt; apply H.
    Qed.
  
  End Limit_and_Successor_Ordinals.
      


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
      (* Not sure how to prove this! *)
    Abort.
    
  End Ordinality.


  Section From_Nat.
    (** Mapping of the natural numbers into the finite ordinals. *)

    Definition from_nat (n: Nat.t): Ord := Nat.iter n S 0.

    #[export]
    Instance from_nat_compat: Proper (Logic.eq ==> eq) from_nat := _.

    #[export]
    Instance from_nat_lt_covariant: Proper (Peano.lt ==> lt) from_nat.
    Proof.
      intros m n Hyp; induction n.
      - contradict Hyp; auto with arith.
      - inversion_clear Hyp; simpl.
        + apply succ_property.
        + rewrite <- (succ_property _).(minimal_property).
          auto.
    Qed.

    #[export]
    Instance from_nat_le_covariant: Proper (Peano.le ==> le) from_nat.
    Proof.
      intros m n Hyp.
      induction m, n as [n | m | m n IH] using nat_double_ind.
      - (* 0, n *) apply zero_le.
      - (* S m, 0 *) contradict Hyp; auto with arith.
      - (* S m, S n *)
        simpl; repeat elim_quantifiers.
        apply IH. auto with arith.
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

  
  Section Indexed_Join.

    Section Def.
      Context {I: Type}.
      Variable w: I → Ord.

      Definition Is_supremum (j: Ord) := ∀ i: I, w i ≤ j.
      Hint Unfold Is_supremum: ord.

      Let J: Type := {i & src (w i)}.
      Let ϕ: J → Ord := λ x, let (i, x) := x in src_map (w i) x.

      Definition Join: Ord := sup⁺ ϕ.

      Let Φ := λ j, ∀ i, w i ≤ j.
      Local Hint Unfold Φ: core.

      #[export]
      Instance Join_property: Minimal Is_supremum Join.
      Proof.
        split.
        - intro i; now_show (w i ≤ Join).
          destruct (w i) eqn: E.
          intro a.
          change (src (sup⁺ f)) in a.
          exists (existT _ i (eq_rect _ _ a _ (symmetry E))).
          subst ϕ; simpl; rewrite -> E. reflexivity.
        - intros j H; now_show (Join ≤ j).
          destruct j eqn: E.
          apply le_lt. now_show (∀ a, ϕ a < sup⁺ f).
          intros (i, x).
          eapply lt_le_trans. 2: exact (H i).
          subst ϕ; simpl.
          destruct (w i). apply strict_sup_property.
      Qed.

      Definition Join_unique := Minimal_unique Join_property.

      Corollary Join_max (i: I): Is_supremum (w i) → Join == w i.
      Proof.
        split; now apply Join_property.
      Qed.
    End Def.

    #[export]
    Instance Join_compat {I}: Proper (pointwise_relation I eq ==> eq) Join.
    Proof.
      autounfold with rels. intros w w' H.
      apply Join_unique.
      split; unfold Is_supremum.
      - intro i; specialize (H i). rewrite <- H. apply Join_property. 
      - intros x H'. setoid_rewrite <- H in H'.
        now apply Join_property.
    Qed.

  End Indexed_Join.

  #[global] Notation "⋀ { w | i : I }" := (Join (λ i: I, w)) : Ord_scope.


  Section Meet.

    (*Variable I: Type.
    Variable w: I → Ord.

    Let M: Type := ∀ i: I, src (w i).*)

  End Meet.

End Ord.

#[export] Instance Ord_lt_rewrite: RewriteRelation Ord.lt := {}.
#[export] Instance Ord_le_rewrite: RewriteRelation Ord.le := {}.
#[export] Instance Ord_eq_rewrite: RewriteRelation Ord.eq := {}.

