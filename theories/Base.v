(** Definition of the ordered setoid of ordinal numbers, together with
    proofs that it is indeed an ordered setoid under the given relations.
    That is:
    - Ord.eq (==) is an equivalence relation;
    - Ord.lt (<) is an ==-compatible strict ordering relation;
    - Ord.le (≤) is a partial ordering relation w.r.t. ==;
    - < is a subrelation of ≤.

    Some desirable properties (such as totality) require excluded middle,
    and are deferred to the OrdClassical module.

    Implementation note:
    A rather more elegant mutually recursive definition of < and ≤ is
    possible, and was originally to be used here:
    - ssup f ≤ y when, for all a:A, f(a) < y; 
    - x < ssup g when, for some b:B, x ≤ g(b). 
      However, Coq does not accept these as fixpoint definitions since
    they descend on different parameters. It does accept them as
    inductive definitions, but this would require them to be redefined
    inside the Ord module, which causes annoying notational issues.
    We have instead included proofs of the above properties for our
    definitions, as lemmata le_lt and lt_le respectively.
*)

From Ordinal Require Import CommonHeader WellOrderClass Notations.

Require Arith_base.

Generalizable All Variables.


(** An ordinal is represented by the image of a (possibly empty) function
    with codomain the ordinals. Conceptually it 'is' the least ordinal
    greater than every element of the function's range. *)

Inductive Ord := ssup `(x: A → Ord).

Module Ord <: EqLtLe' <: StrOrder.

  Definition t := Ord.

  Definition src (o: Ord) := let (A, _) := o in A.
  
  Definition src_map (o: Ord) : src o → Ord :=
    match o with ssup f => f end.

  Fixpoint le o o': Prop :=
    ∀ a: src o, ∃ a': src o',le (src_map o a) (src_map o' a').

  Fixpoint lt o o': Prop :=
    ∃ a': src o', ∀ a: src o, lt (src_map o a) (src_map o' a').

  Definition ge := flip le.
  Definition gt := flip lt.
  Definition eq := relation_conjunction le ge.

  #[export] Hint Unfold ge gt relation_conjunction flip: core.

  Include EqLtLeNotation.
  Infix "≤" := le.
  Infix "≥" := ge.
  Notation "x =/= y" := (x ~= y).
  
  Section Reduction_Lemmata.

    Lemma le_le `(x: A → Ord) `(y: B → Ord):
      (∀ a, ∃ b, x a ≤ y b) ↔ ssup x ≤ ssup y.
    Proof. reflexivity. Qed.

    Lemma lt_lt `(x: A → Ord) `(y: B → Ord):
      (∃ b, ∀ a, x a < y b) ↔ ssup x < ssup y.
    Proof. reflexivity. Qed.

    Fixpoint le_lt (o: Ord): ∀ [A] (x: A → Ord), (∀ a, x a < o) ↔ ssup x ≤ o.
    Proof.
      destruct o as [A' x'].
      split.
      intros hyp a; specialize (hyp a).
      simpl in a, hyp |- *. destruct (x a).
      destruct hyp as [a' hyp]. exists a'.
      apply le_lt. auto.
    Qed.

    Fixpoint lt_le (o: Ord): ∀ [A] (x: A → Ord), (∃ a, o ≤ x a) ↔ o < ssup x.
    Proof.
      destruct o as [A' x'].
      split.
      intros [a hyp]. exists a.
      simpl in hyp |- *. destruct (x a).
      intro. apply lt_le, hyp.
    Qed.

    Lemma eq_le `(x: A → Ord) `(y: B → Ord):
      (∀ a, ∃ b, x a ≤ y b) → (∀ b, ∃ a, y b ≤ x a) → (ssup x == ssup y)%Ω.
    Proof @conj _ _.

    Lemma eq_eq `(x: A → Ord) `(y: B → Ord):
      (∀ a, ∃ b, x a == y b) → (∀ b, ∃ a, y b == x a) → (ssup x == ssup y)%Ω.
    Proof. firstorder. Qed.

  End Reduction_Lemmata.


  Section Order_Properties.

    Open Scope equiv_scope.

    #[export] Instance lt_sub_le: subrelation lt le.
    Proof.
      unfold subrelation; fix Fix 1.
      destruct x, y, 1; eexists; eauto.
    Qed.

    #[export] Instance eq_sub_le: subrelation eq le.
    Proof λ x y H, proj1 H.

    #[export] Instance le_preorder: PreOrder le.
    Proof.
      split; autounfold.
      fix Fix 1.
      - destruct x; intro a; now exists a.
      - destruct x, y, z; intros H1 H2 a.
        edestruct H1, H2. eauto.
    Qed.

    #[export] Instance ge_preorder: PreOrder ge | 2 :=
      flip_PreOrder _.

    #[export] Instance lt_strorder: StrictOrder lt.
    Proof.
      split; autounfold.
      fix Fix 1.
      - destruct x, 1; firstorder.
      - destruct x, y, z, 1, 1.
        eexists; eauto.
    Qed.

    #[export] Instance gt_strorder: StrictOrder gt | 2 :=
      flip_StrictOrder _.

    #[export] Instance eq_equiv: Equivalence eq.
    Proof.
      firstorder using le_preorder.
    Qed.

    #[export] Instance le_partial_order: PartialOrder eq le.
    Proof.
      now_show (eq === relation_conjunction le (flip le)).
      reflexivity.
    Qed.

    #[export] Instance ge_partial_order: PartialOrder eq ge | 2 :=
      PartialOrder_inverse _.

    #[export] Instance lt_le_compat: Proper (le --> le ++> impl) lt.
    Proof.
      autounfold. fix Fix 1.
      intros [A x] [B y] Le [A' x'] [B' y'] Le'.
      unfold flip; simpl in *.
      intros (a', Lt). specialize (Le' a') as (b', Le').
      exists b'. intro b. specialize (Le b) as (a, Le).
      specialize (Lt a).
      eapply Fix; eassumption.
    Qed.
    
    #[export] Instance lt_compat: Proper (eq ==> eq ==> iff) lt.
    Proof.
      apply (proper_sym_impl_iff_2 _ _).
      firstorder using lt_le_compat.
    Qed.

    #[export] Instance lt_wf: well_founded lt.
    Proof.
      intro x. enough (∀ (y: Ord) (H: y ≤ x), Acc lt y).
      { apply H; reflexivity. }
      induction x as [A f IH], y as [B g].
      intro; constructor; intros z H'.
      apply lt_le in H'. destruct H' as [b H'].
      specialize (H b) as [a H].
      apply (IH a). etransitivity; eassumption.
    Qed.

    #[export] Instance lt_ext: Extensional eq lt.
    Proof.
      enough (WeaklyExtensional eq lt) by exact _.
      intros x y H; split.
      induction x as [A f IH], y as [B g]. simpl.
      intro x. apply lt_le, H, le_lt; reflexivity.
    Qed.

    #[export] Instance lt_wo: WellOrder eq lt := { }.

    #[export] Instance pointwise_eq_sub_le [A]:
    subrelation (pointwise_relation A eq) (pointwise_relation A le) := _.

    #[export] Instance pointwise_lt_sub_le [A]:
    subrelation (pointwise_relation A lt) (pointwise_relation A le) := _.
    
    #[export] Instance unary_covariant_is_proper (op: Ord → Ord):
      Proper (le ==> le) op → Proper (eq ==> eq) op.
    Proof. firstorder. Qed.

    #[export] Instance binop_covariant_proper (op: Ord → Ord → Ord):
      Proper (le ==> le ==> le) op → Proper (eq ==> eq ==> eq) op.
    Proof. firstorder. Qed.

    #[export] Instance pointwise_covariant_is_proper [A] (op: (A → Ord) → Ord):
      Proper (pointwise_relation A le ==> le) op →
      Proper (pointwise_relation A eq ==> eq) op.
    Proof.
      intros covariant x y E. pose proof (E' := symmetry E).
      apply pointwise_eq_sub_le in E, E'.
      split; auto.
    Qed.

  End Order_Properties.
    

  Section Strict_Supremum.

    Variable A: Type.

    #[export]
    Instance ssup_covariance: Proper (pointwise_relation A le ++> le) ssup.
    Proof. firstorder. Qed.

    #[export]
    Instance ssup_compat: Proper (pointwise_relation A eq ==> eq) ssup := _.

    Property ssup_gt (x: A → Ord): ∀ a, x a < ssup x.
    Proof.
      apply le_lt; reflexivity.
    Qed.
  
    Property ssup_minimal (x: A → Ord): ∀ s, (∀ a: A, x a < s) ↔ ssup x ≤ s.
    Proof.
      intro; apply le_lt.
    Qed.

    Property ssup_ge (x: A → Ord): ∀ a, x a ≤ ssup x.
    Proof.
      intro; apply lt_sub_le, ssup_gt.
    Qed.
    
    Lemma compose_le `(x: B → Ord) (f: A → B): ssup (x ∘ f) ≤ ssup x.
    Proof.
      intro a; exists (f a). reflexivity.
    Qed.

  End Strict_Supremum.


  Section Propriety.

    Variable Q: ∀ A, (A → Ord) → Prop.
    Let P (o: Ord) := Q (src_map o).

    Hypothesis proper: Proper (eq ==> iff) P.

    #[export]
    Instance proper_is_pointwise_proper A:
      Proper (pointwise_relation A eq ==> iff) (@Q A).
    Proof.
      intros x y H.
      now apply ssup_compat, proper in H.
    Qed.

    Theorem source_irrelevance (o: Ord):
      ∀ A (f: A → Ord), ssup f == o → Q f → P o.
    Proof.
      intros A f Eq. now rewrite <- Eq.
    Qed.

    Theorem source_irrelevance_inv (o: Ord):
      P o → ∀ A (f: A → Ord), ssup f == o → Q f.
    Proof.
      intros H A f Eq. now rewrite <- Eq in H.
    Qed.

  End Propriety.


  Section Zero.

    Definition zero: Ord := ssup (Empty_set_rect _).

    Property zero_le: ∀ x: Ord, zero ≤ x.
    Proof λ x, Empty_set_ind _.

    Definition zero_unique z: (∀ x, z ≤ x) -> z == zero.
    Proof λ h, conj (h zero) (zero_le z).
  
    Property le_zero_is_zero x: x ≤ zero -> x == zero.
    Proof λ h, conj h (zero_le x).
  
    Property nlt_zero: ∀ w, ¬(w  < zero).
    Proof.
      intros [] []; contradiction.
    Qed.

    Definition lt_zero_exfalso {P: Ord -> Type} w: w < zero → P w :=
      λ h, False_rect (P w) (nlt_zero w h).

    Property ssup_empty_is_zero w: ¬inhabited (src w) ↔ w == zero.
    Proof.
      destruct w as (A, x); simpl. split.
      - intro N. apply le_zero_is_zero, le_lt.
        intro a; now contradict N.
      - intros [H _] [a]. now destruct (H a).
    Qed.

    Property ssup_inhabited_is_positive w: inhabited (src w) ↔ w > zero.
    Proof.
      split; intros [a].
      - exists a; intros [].
      - auto.
    Qed.

    Property ssup_nonempty_is_nonzero w: ¬¬inhabited (src w) ↔ w ~= zero.
    Proof.
      split. intros H H'.
      apply (ssup_empty_is_zero w) in H'.
      contradiction.
    Qed.

  End Zero.

  #[export] Hint Resolve zero_le: ord.
  #[export] Hint Resolve zero_unique: ord.
  #[export] Hint Resolve le_zero_is_zero: ord.
  #[export] Hint Resolve nlt_zero: ord.
  #[export] Hint Resolve <- ssup_empty_is_zero: ord.
  #[export] Hint Resolve <- ssup_inhabited_is_positive: ord.
  #[export] Hint Resolve <- ssup_nonempty_is_nonzero: ord.


  Section Successor.
    (** The successor operation and its basic properties. *)

    Definition succ (o: Ord): Ord := ssup (λ _:unit, o).

    #[export]
    Instance succ_strict_covariance: Proper (lt ++> lt) succ.
    Proof.
      repeat intro; simpl; repeat elim_quantifiers.
      assumption.
    Qed.

    #[export]
    Instance succ_covariance: Proper (le ==> le) succ.
    Proof.
      unfold succ; solve_proper.
    Qed.

    #[export]
    Instance succ_compat: Proper (eq ==> eq) succ := _.

    Property succ_gt o: o < succ o.
    Proof.
      apply -> lt_le. exists tt; reflexivity.
    Qed.

    Property succ_minimality o: ∀ s, o < s ↔ succ o ≤ s.
    Proof.
      split; intros.
      - apply -> le_lt; auto.
      - apply <- le_lt in H; auto using tt.
    Qed.

    Property succ_ge o: o ≤ succ o.
    Proof.
      apply lt_sub_le, succ_gt.
    Qed.

    Property le_iff_lt_succ x y: x ≤ y ↔ x < succ y.
    Proof.
      intros; split; intro H.
      - apply -> lt_le; repeat constructor; assumption.
      - apply <- lt_le in H; destruct H; assumption.
    Qed.

    Property succ_lt_inv x y: succ x < succ y → x < y.
    Proof.
      intros; now apply succ_minimality, le_iff_lt_succ.
    Qed.

    Property succ_le_inv: ∀ x y, succ x ≤ succ y → x ≤ y.
    Proof.
      intros; now apply le_iff_lt_succ, succ_minimality.
    Qed.

    Property succ_inj: ∀ x y, succ x == succ y → x == y.
    Proof.
      destruct 1; split; now apply succ_le_inv.
    Qed.
  
  End Successor.

  #[export] Hint Resolve -> succ_minimality: ord.
  #[export] Hint Rewrite <- succ_gt: ord.
  #[export] Hint Rewrite <- succ_minimality: ord.


  Section Limit_and_Successor_Ordinals.
    
    Definition Is_successor (o: Ord) := ∃ p, succ p == o.

    Definition Is_limit (o: Ord) := ∀ p, p < o → succ p < o.

    #[export]
    Instance: Proper (eq ==> iff) Is_successor.
    Proof.
      unfold Is_successor; solve_proper.
    Qed.

    #[export]
    Instance: Proper (eq ==> iff) Is_limit.
    Proof.
      unfold Is_limit; solve_proper.
    Qed.

    (** Constructively we cannot prove every ordinal is either a
     successor or a limit ordinal, but we can prove the following. *)

    Fact limit_nand_successor (o: Ord): ¬(Is_limit o ∧ Is_successor o).
    Proof.
      intros [H [p H']]. rewrite <- H' in H. clear dependent o.
      pose proof (H'' := succ_gt p).
      specialize (H p H''). contradict H. apply irreflexivity.
    Qed.

    Fact not_successor_is_limit (o: Ord) : ¬Is_successor o → Is_limit o.
    Proof.
      intros H p L.
      assert (Hp: succ p =/= o) by firstorder.
      give_up.
    Abort.
    (* Is this even true constructively? *)
      

    (** An ordinal is a successor iff every map into the ordinals
    specifying it has a maximal element, iff any map does so. *)

    Lemma successor_max (o: Ord):
      Is_successor o →
      ∀ `(x: A → Ord), ssup x == o → ∃ μ: A, ∀ a: A, x μ ≥ x a.
    Proof.
      intros [o' s] I x Eq.
      rewrite <- Eq in s; clear dependent o.
      specialize (proj1 s tt) as [i s1];
      specialize (proj2 s i) as [[] s2];
      pose proof (Eq' := conj s1 s2: o' == x i); clear s1 s2.
      rewrite -> Eq' in s.
      exists i. firstorder.
    Qed.

    Lemma max_successor (o: Ord) `(x: A → Ord) (Eq: ssup x == o):
      (∃ μ: A, ∀ a: A, x μ ≥ x a) → Is_successor o.
    Proof.
      intros [μ M]. exists (x μ).
      rewrite <- Eq; clear dependent o.
      split.
      - intros []; exists μ; reflexivity.
      - intro a; exists tt; apply M.
    Qed.
  
  End Limit_and_Successor_Ordinals.


  Section From_WF.
    (** Mapping of other sets with well-founded relations into the ordinals *)
    
    Context `{Rwf: well_founded A R}.
    Local Infix "≺" := R (at level 70).

    Let fwf (a: A) (ih: ∀ x: A, x ≺ a → Ord): Ord :=
        @ssup {y | y ≺ a} (sig_apply ih).

    Definition from_wf := Fix _ fwf : A → Ord.

    Local Lemma fwf_ext (a: A) (f g: ∀ y, y ≺ a → Ord) :
      (∀ (y:A) (p: y ≺ a), f y p == g y p) -> fwf f == fwf g.
    Proof.
      intro H. apply eq_eq.
      intro y; exists y. destruct y.
      2: symmetry.
      apply H.
    Qed.

    Local Lemma fwf_inv (x: A):
      ∀ (r s: Acc R x), Fix_F _ fwf r == Fix_F _ fwf s.
    Proof.
      induction (Rwf x); intros.
      rewrite <-! Fix_F_eq.
      apply fwf_ext.
      auto.
    Qed.
    
    Property from_wf_eq a:
      from_wf a == ssup (λ y: {y | y ≺ a}, from_wf (proj1_sig y)).
    Proof.
      change (ssup _) with (fwf (λ y (_: y ≺ a), from_wf y)).
      unfold from_wf, Fix. rewrite <- Fix_F_eq.
      apply fwf_ext. intros. apply fwf_inv.
    Qed.

    Global Instance from_wf_strict_covariance: Proper (R ==> lt) from_wf.
    Proof.
      intros x y p. rewrite -> (from_wf_eq y).
      exact (ssup_gt _ (exist _ x p)).
    Qed.

    Context `{equivA: Equivalence A eqA}.
    Context {R_compat: Proper (eqA ==> eqA ==> iff) R}.
    Local Infix "≃" := eqA (at level 70).

    Global Instance from_wf_compat: Proper (eqA ==> eq) from_wf.
    Proof.
      intros x y e. rewrite ->! from_wf_eq.
      apply eq_eq.
      intros [z r].
      pose (r' := r).
      apply (R_compat (reflexivity z) e) in r'.
      exists (exist _ z r'). reflexivity.
    Qed.

    Context {Rtrans: Transitive R}.

    Property from_wf_inv_covariance: ∀ x y, from_wf x < from_wf y → x ≺ y.
    Proof.
      intros x y Lt. induction y as [y IH] using well_founded_ind.
      rewrite -> (from_wf_eq y) in Lt.
      apply lt_le in Lt as [[y' r] Le]. cbn in Le.
      refine (transitivity _ r).
      specialize (IH y' r).
      apply IH.
      (* doesn't seem to quite work... *)
      change (from_wf x ≤ from_wf y') in Le.
      now_show (from_wf x < from_wf y').
    Abort.

    Hypothesis Rwext: WeaklyExtensional eqA R.

    Property from_wf_inj: ∀ x y, from_wf x == from_wf y → x ≃ y.
    Proof.
      induction y as [y IH] using well_founded_ind. intro Eq.
      apply weak_extensionality. intro t; split.
    Abort.
      
  End From_WF.


  Section From_Nat.
    (** Mapping of the natural numbers into the finite ordinals. We could
    just use from_wf, but we instead define a simpler function and then
    show that it is equivalent. *)

    Definition from_nat (n: nat): Ord := Nat.iter n succ zero.

    Local Lemma from_wf_nat_covariance:
      Proper (Peano.le ==> le) (from_wf (R := Peano.lt)).
    Proof.
      intros m n h.
      apply Arith.Compare_dec.le_lt_eq_dec in h; destruct h.
      - apply lt_sub_le, from_wf_strict_covariance. assumption.
      - destruct e. reflexivity.
    Qed.

    Lemma from_wf_0: from_wf 0 == zero.
    Proof.
      rewrite -> from_wf_eq.
      apply ssup_empty_is_zero. intros [[x lt]].
      inversion lt.
    Qed.

    Lemma from_wf_S (n: nat): from_wf (S n) == succ (from_wf n).
    Proof.
      unfold succ. rewrite -> from_wf_eq. simpl.
      apply eq_le.
      - intros [m l]. exists tt. simpl.
        apply from_wf_nat_covariance; auto with arith.
      - intro. assert (l: (n < S n)%nat) by auto.
        now exists (exist _ n l).
    Qed.

    Proposition from_wf_is_from_nat:
      pointwise_relation _ eq (from_wf (R := Peano.lt)) from_nat.
    Proof.
      intro n; induction n.
      - apply from_wf_0.
      - simpl. rewrite <- IHn. apply from_wf_S.
    Qed.

    Lemma from_nat_src (n: nat): (0 < n)%nat → unit = src (from_nat n) :> Type.
    Proof.
      intro H. rewrite <- (Arith.PeanoNat.Nat.succ_pred_pos _ H). reflexivity.
    Qed.

    Lemma from_nat_src_0 (n: nat): ∅ = src (from_nat 0) :> Type.
    Proof.
      reflexivity.
    Qed.

    #[export]
    Instance from_nat_compat: Proper (Logic.eq ==> eq) from_nat := _.

    #[export]
    Instance from_nat_strict_covariace: Proper (Peano.lt ==> lt) from_nat.
    Proof.
      repeat intro.
      rewrite <- from_wf_is_from_nat.
      apply from_wf_strict_covariance, H.
    Qed.

    #[export]
    Instance from_nat_covariance: Proper (Peano.le ==> le) from_nat.
    Proof.
      intros m n m_le_n.
      induction m, n as [n | m | m n IH] using nat_double_ind.
      - (* 0, n *) apply zero_le.
      - (* S m, 0 *) exfalso. inversion m_le_n.
      - (* S m, S n *)
        simpl; repeat elim_quantifiers.
        apply IH. auto with arith.
    Qed.
    
    Property from_nat_le_inv m n: from_nat m ≤ from_nat n → (m <= n)%nat.
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
  

  Section Supremum.
    (** The supremum, or join, of an indexed family of ordinals.
        Conceptually we join all their sources into a sigma-type and
        take the strict supremum of the corresponding join of their
        source maps.
        *)

    Open Scope equiv_scope.

    Section Def.

      Context `(x: A → Ord).

      Let J: Type := { a: A & src (x a) }.

      Let Jmap: J → Ord := λ j, let (a, b) := j in src_map (x a) b.

      Definition sup: Ord := ssup Jmap.

      Property sup_ge: ∀ a: A, x a ≤ sup.
      Proof.
        intro a. destruct (x a) as [B y] eqn: E.
        intro b.
        exists (existT _ a (eq_rect _ _ b _ (symmetry E))).
        unfold sup; simpl. rewrite -> E. reflexivity.
      Qed.

      Property sup_minimality: ∀ s, (forall a, x a ≤ s) → sup ≤ s.
      Proof.
        intros s H. destruct s eqn: E.
        apply le_lt.
        intros [a b]. rewrite <- (H a).
        simpl. destruct (x a). apply ssup_gt.
      Qed.

      Property sup_uniqueness:
      ∀ s, (∀ a, x a ≤ s) → (∀ s', (∀ a, x a ≤ s') → s ≤ s') → sup == s.
      Proof.
        split.
        - apply sup_minimality; auto.
        - apply H0, sup_ge.
      Qed.

      Property sup_maximum: ∀ a:A, (∀ b:A, x b ≤ x a) → x a == sup.
      Proof.
        intros. split.
        - apply sup_ge.
        - apply sup_minimality; assumption.
      Qed.

    End Def.

    #[export]
    Instance sup_covariance {A}: Proper (pointwise_relation A le ==> le) sup.
    Proof λ x y H,
          sup_minimality x (sup y) (transitivity H (sup_ge y)).

    #[export]
    Instance sup_compat {A}: Proper (pointwise_relation A eq ==> eq) sup := _.

    Property sup_le_ssup [A]: pointwise_relation _ le (@sup A) (@ssup A).
    Proof.
      intro x. apply sup_minimality, ssup_ge.
    Qed.

    Proposition ssup_is_sup_succ [A] (x: A → Ord): ssup x == sup (succ ∘ x).
    Proof.
      split; simpl.
      - intro a; exists (existT _ a tt). reflexivity.
      - intros [a []]; exists a. reflexivity.
    Qed.

    Proposition succ_sup [A] (x: A → Ord): sup x < ssup x ↔ succ (sup x) == ssup x.
    Proof.
      split.
      + split.
        - apply le_lt; trivial.
        - cbn. intro a; exists tt; apply sup_ge.
      + intro H; rewrite <- H; apply succ_gt.
    Qed.

    Proposition sup_empty_is_zero [A] (x: A → Ord): ¬inhabited A → sup x == zero.
    Proof.
      intro N; apply le_zero_is_zero.
      intros [a]; now contradict N.
    Qed.

    Remark sup_const_le x [A]: sup (const x : A → Ord) ≤ x.
    Proof.
      apply sup_minimality; reflexivity.
    Qed.

    Remark sup_const_eq x [A]: inhabited A → sup (const x : A → Ord) == x.
    Proof.
      split. 1: apply sup_const_le.
      destruct H as [a].
      change x with (const x a) at 2. apply sup_ge.
    Qed.

  End Supremum.


  Section Pairwise_Maximum.

    Definition max (x y: Ord): Ord := ssup (sum_rect _ (src_map x) (src_map y)).
    Local Notation "[ f , g ]" := (sum_rect _ f g).

    Property max_ge x y: x ≤ max x y ∧ y ≤ max x y.
    Proof.
      destruct x, y. split. intro a.
      1: exists (inl a). 2: exists (inr a).
      reflexivity.
    Qed.

    Definition max_ge_L x y := proj1 (max_ge x y): x ≤ max x y.
    Definition max_ge_R x y := proj2 (max_ge x y): y ≤ max x y.

    Property max_minimality x y: ∀ z, x ≤ z → y ≤ z → max x y ≤ z.
    Proof.
      destruct x, y, z; simpl.
      intros H1 H2 p. destruct p as [a | a].
      1: destruct (H1 a). 2: destruct (H2 a).
      eexists; eassumption.
    Qed.

    Corollary max_uniqueness x y: ∀ m,
      x ≤ m → y ≤ m → (∀ z, x ≤ z → y ≤ z → m ≤ z) → max x y == m.
    Proof.
      split.
      - apply max_minimality; assumption.
      - apply H1; apply max_ge.
    Qed.

    Proposition max_is_sup x y: max x y == sup (λ b:bool, if b then x else y).
    Proof.
      split.
      - apply max_minimality. 
        + exact (sup_ge _ true).
        + exact (sup_ge _ false).
      - apply sup_minimality.
        intro b; case b. apply max_ge.
    Qed.
  
    #[export]
    Instance max_covariance: Proper (le ++> le ++> le) max.
    Proof.
      intros [A f] [B g] Le [A' f'] [B' g'] Le'.
      intro x; destruct x as [a | a].
      - destruct (Le a) as [x]; now exists (inl x).
      - destruct (Le' a) as [x]; now exists (inr x).
    Qed.

    #[export]
    Instance max_compat: Proper (eq ==> eq ==> eq) max := _.

    Property max_idempotence x: max x x == x.
    Proof.
      destruct x as [A f]; apply eq_eq.
      - intros [a | a]; now exists a.
      - intro a; now exists (inl a).
    Qed.

    Property max_sym x y: max x y == max y x.
    Proof.
      apply eq_eq. intros [a | a].
      1, 3: exists (inr a). 3, 4: exists (inl a).
      reflexivity.
    Qed.

    Property max_eq_L x y: x ≥ y ↔ max x y == x.
    Proof.
      split.
      - split.
        + rewrite <- H; apply max_idempotence.
        + apply max_ge.
      - intro H; rewrite <- H; apply max_ge.
    Qed.

    Property max_eq_R x y: x ≤ y ↔ max x y == y.
    Proof.
      rewrite max_sym. apply max_eq_L.
    Qed.
  
  End Pairwise_Maximum.


  Section Pairwise_Minimum.
    
    Fixpoint min (x y: Ord): Ord :=
      ssup (λ p: src x × src y, min (src_map x (fst p)) (src_map y (snd p))).

    Fixpoint min_le (x y: Ord): min x y ≤ x ∧ min x y ≤ y.
    Proof.
      destruct x, y; split; intros [a b].
      1: exists a. 2: exists b.
      apply min_le.
    Qed.

    Definition min_le_L x y := proj1 (min_le x y) : min x y ≤ x.
    Definition min_le_R x y := proj2 (min_le x y) : min x y ≤ y.

    Fixpoint min_maximality x y: ∀ z, z ≤ x → z ≤ y → z ≤ min x y.
    Proof.
      destruct x as [A x], y as [B y], z as [C z]. cbn.
      intros H1 H2 c.
      specialize (H1 c) as [a H1]; specialize (H2 c) as [b H2].
      exists (a, b). now_show (z c ≤ min (x a) (y b)).
      now apply min_maximality.
    Qed.

    Corollary min_uniqueness x y: ∀ m,
      m ≤ x → m ≤ y → (∀ z, z ≤ x → z ≤ y → z ≤ m) → min x y == m.
    Proof.
      split.
      - apply H1; apply min_le.
      - apply min_maximality; assumption.
    Qed.
  
    #[export]
    Instance min_covariance: Proper (le ++> le ++> le) min.
    Proof.
      intros [A f] [B g] Le [A' f'] [B' g'] Le'. simpl.
      intros (a, a').
      specialize (Le a) as (b, Le); fold le in Le.
      specialize (Le' a') as (b', Le'); fold le in Le'.
      exists (b, b'); cbn in *.
      apply min_maximality.
      1: rewrite <- Le. 2: rewrite <- Le'.
      apply min_le.
    Qed.

    #[export]
    Instance min_compat: Proper (eq ==> eq ==> eq) min := _.
  
  End Pairwise_Minimum.

End Ord.

#[global] Bind Scope Ord_scope with Ord Ord.t.

#[global] Infix "≤" := Ord.le: Ord_scope.
#[global] Infix "≥" := Ord.ge: Ord_scope.
#[global] Infix "<" := Ord.lt: Ord_scope.
#[global] Infix ">" := Ord.gt: Ord_scope.
#[global] Infix "==" := Ord.eq: Ord_scope.
#[global] Notation "x =/= y" := (not (Ord.eq x y)): Ord_scope.

#[global] Notation "x == y == z" := (and (Ord.eq x y) (Ord.eq y z)): Ord_scope.
#[global] Notation "x < y < z" := (and (Ord.lt x y) (Ord.lt y z)): Ord_scope.
#[global] Notation "x ≤ y ≤ z" := (and (Ord.le x y) (Ord.le y z)): Ord_scope.
#[global] Notation "x ≤ y < z" := (and (Ord.le x y) (Ord.lt y z)): Ord_scope.
#[global] Notation "x < y ≤ z" := (and (Ord.lt x y) (Ord.le y z)): Ord_scope.
#[global] Notation "x < y == z" := (and (Ord.lt x y) (Ord.eq y z)): Ord_scope.
#[global] Notation "x == y < z" := (and (Ord.eq x y) (Ord.lt y z)): Ord_scope.
#[global] Notation "x ≤ y == z" := (and (Ord.le x y) (Ord.eq y z)): Ord_scope.
#[global] Notation "x == y ≤ z" := (and (Ord.eq x y) (Ord.le y z)): Ord_scope.

#[export] Instance Ord_eq_rewrite: RewriteRelation Ord.eq | 0 := {}.
#[export] Instance Ord_lt_rewrite: RewriteRelation Ord.lt | 1 := {}.
#[export] Instance Ord_le_rewrite: RewriteRelation Ord.le | 1 := {}.
#[export] Instance Ord_gt_rewrite: RewriteRelation Ord.lt | 2 := {}.
#[export] Instance Ord_ge_rewrite: RewriteRelation Ord.ge | 2 := {}.
