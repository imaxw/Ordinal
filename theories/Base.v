From Ordinal Require Import
  CommonHeader
  WellFounded
  Notations.

Require Import Arith_base.

Generalizable Variables A B C I J K R X Y Z eqA.


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
    - ssup f <= y when, for all a:A, f(a) < y; 
    - x < ssup g when, for some b:B, x <= g(b). 
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

Inductive Ord: Type := ssup `(x: A → Ord).
Bind Scope Ord_scope with Ord.

Module Ord <: EqLtLe' <: StrOrder.

  Open Scope Ord_scope.

  Definition t := Ord.

  Definition src (w: Ord): Type :=
    match w with @ssup A f => A end.
  
  Definition src_map (w: Ord): src w → Ord :=
    match w with @ssup A f => f end.

  Definition rect := Ord_rect.
  Definition rec := Ord_rec.
  Definition ind := Ord_ind.
  Definition sind := Ord_sind.

  Fixpoint le o o': Prop :=
    ∀ a: src o, ∃ a': src o', le (src_map o a) (src_map o' a').
    (*match o, o' with
    | ssup x, ssup y => ∀ a, ∃ b, le (x a) (y b)
    end.*)

  Fixpoint lt o o': Prop :=
    ∃ a': src o', ∀ a: src o, lt (src_map o a) (src_map o' a').
    (*match o, o' with
    | ssup x, ssup y => ∃ b, ∀ a, lt (x a) (y b)
    end.*)

  Definition eq o o': Prop := le o o' ∧ le o' o.
  Definition ge o o': Prop := le o' o.
  Definition gt o o': Prop := lt o' o.

  #[export] Hint Unfold ge: core.
  #[export] Hint Unfold gt: core.

  #[global] Infix "≤" := le: Ord_scope.
  #[global] Infix "≥" := ge: Ord_scope.
  #[global] Infix "<" := lt: Ord_scope.
  #[global] Infix ">" := gt (only parsing): Ord_scope.
  #[global] Infix "==" := eq: Ord_scope.
  #[global] Notation "x =/= y" := (not (eq x y)): Ord_scope.

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

    Lemma le_le `(x: A → Ord) `(y: B → Ord):
      (∀ a, ∃ b, x a ≤ y b) ↔ ssup x ≤ ssup y.
    Proof. reflexivity. Qed.

    Lemma lt_lt `(x: A → Ord) `(y: B → Ord):
      (∀ a, ∃ b, x a ≤ y b) ↔ ssup x ≤ ssup y.
    Proof. reflexivity. Qed.

    Lemma le_lt (o: Ord): ∀ [A] (x: A → Ord), (∀ a, x a < o) ↔ ssup x ≤ o.
    Proof.
      induction o as [A' x' IH].
      split.
      intros hyp a; specialize (hyp a).
      simpl in a, hyp |- *. destruct (x a) as [C z].
      destruct hyp as [a' hyp]. exists a'.
      apply IH; auto.
    Qed.

    Lemma lt_le (o: Ord): ∀ [A] (x: A → Ord), (∃ a, o ≤ x a) ↔ o < ssup x.
    Proof.
      induction o as [A' f' IH].
      split.
      intros [a H]. exists a.
      simpl in H |- *; destruct (x a).
      intro. apply IH, H.
    Qed.

    Lemma eq_le `(x: A → Ord) `(y: B → Ord):
      (∀ a, ∃ b, x a ≤ y b) → (∀ b, ∃ a, y b ≤ x a) → eq (ssup x) (ssup y).
    Proof @conj _ _.

    Lemma eq_eq `(x: A → Ord) `(y: B → Ord):
      (∀ a, ∃ b, x a == y b) → (∀ b, ∃ a, y b == x a) → eq (ssup x) (ssup y).
    Proof. firstorder. Qed.

  End Reduction_Lemmata.


  Section Order_Properties.

    Open Scope equiv_scope.

    #[export] Instance lt_sub_le: subrelation lt le.
    Proof.
      unfold subrelation; fix Fix 1.
      destruct x, y, 1; eexists; eauto.
    Qed.

    #[export] Instance le_preorder: PreOrder le.
    Proof.
      split; autounfold.
      fix Fix 1.
      - destruct x; intro a; now exists a.
      - destruct x, y, z; intros H1 H2 a.
        edestruct H1, H2. eauto.
    Qed.

    #[export] Instance lt_strorder: StrictOrder lt.
    Proof.
      split; autounfold.
      fix Fix 1.
      - destruct x, 1; firstorder.
      - destruct x, y, z, 1, 1.
        eexists; eauto.
    Qed.

    #[export] Instance eq_equiv: Equivalence eq.
    Proof.
      firstorder using le_preorder.
    Qed.

    #[export] Instance le_partial_order: PartialOrder eq le.
    Proof.
      now_show (eq === relation_conjunction le (flip le)).
      reflexivity.
    Qed.

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

    #[export] Instance setoid: Setoid Ord := { }.

  End Order_Properties.
    

  Section Strict_Supremum.

    Variable A: Type.

    #[export]
    Instance ssup_covariance:
      Proper (pointwise_relation A le ++> le) ssup.
    Proof. firstorder. Qed.

    #[export]
    Instance ssup_compat:
      Proper (pointwise_relation A eq ==> eq) ssup.
    Proof. firstorder. Qed.

    Property lt_ssup (x: A → Ord): ∀ a, x a < ssup x.
    Proof.
      apply le_lt; reflexivity.
    Qed.
  
    Property ssup_minimal (x: A → Ord): ∀ s, (∀ a: A, x a < s) ↔ ssup x ≤ s.
    Proof.
      intro; apply le_lt.
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

    Property zero_empty w: w == zero ↔ ¬inhabited (src w).
    Proof.
      destruct w as (A, x); simpl. split.
      - intros [H _] [a]. now destruct (H a).
      - intro N. apply le_zero_is_zero, le_lt.
        intro a; now contradict N.
    Qed.

    Property positive_inhabited w: w > zero ↔ inhabited (src w).
    Proof.
      split; intros [a].
      - auto.
      - exists a; intros [].
    Qed.

    Property nonzero_nonempty w: w =/= zero ↔ ¬¬inhabited (src w).
    Proof.
      split. intros H H'.
      apply (zero_empty w) in H'.
      contradiction.
    Qed.

  End Zero.

  #[export] Hint Resolve zero_le: ord.
  #[export] Hint Resolve zero_unique: ord.
  #[export] Hint Resolve le_zero_is_zero: ord.
  #[export] Hint Resolve nlt_zero: ord.
  #[export] Hint Resolve <- zero_empty: ord.
  #[export] Hint Resolve <- positive_inhabited: ord.
  #[export] Hint Resolve <- nonzero_nonempty: ord.


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
    Instance succ_compat: Proper (eq ==> eq) succ.
    Proof.
      unfold succ; solve_proper.
    Qed.

    Property lt_succ o:  o < succ o.
    Proof.
      apply -> lt_le. exists tt; reflexivity.
    Qed.

    Property succ_minimality o: ∀ s, o < s ↔ succ o ≤ s.
    Proof.
      split; intros.
      - apply -> le_lt; auto.
      - apply <- le_lt in H; auto using tt.
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

  #[export] Hint Resolve lt_succ: ord.
  #[export] Hint Resolve -> succ_minimality: ord.
  #[export] Hint Resolve -> le_iff_lt_succ: ord.
  #[export] Hint Rewrite <- lt_succ: ord.
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
      pose proof (H'' := lt_succ p).
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
    
    Variable A: Type.
    Variable R: relation A.
    Context {Rwf: well_founded R}.
    Local Infix "≺" := R (at level 70).

    Let fwf (a: A) (ih: ∀ x: A, x ≺ a → Ord): Ord :=
        @ssup {y | y ≺ a} (sig_apply ih).

    Definition from_wf := Fix Rwf _ fwf : A → Ord.

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
      exact (lt_ssup _ (exist _ x p)).
    Qed.

    Context `{equivA: Equivalence A eqA}.
    Context {R_compat: Proper (eqA ==> eqA ==> iff) R}.
    Local Infix "=" := eqA: type_scope.

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
      intros x y Lt. induction y as [y IH] using wf_ind.
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

    Property from_wf_inj: ∀ x y, from_wf x == from_wf y → x = y.
    Proof.
      induction y as [y IH] using wf_ind. intro Eq.
      apply weak_extensionality. intro t; split.
    Abort.
      
  End From_WF.


  Section From_Nat.
    (** Mapping of the natural numbers into the finite ordinals. *)
    Local Open Scope signature_scope.

    #[export] Instance from_wf_nat_covariance:
      Proper (Peano.le ==> le) (from_wf (R := Peano.lt)).
    Proof.
      intros m n h.
      apply le_lt_eq_dec in h; destruct h.
      - apply lt_sub_le, from_wf_strict_covariance. assumption.
      - destruct e. reflexivity.
    Qed.

    Lemma from_wf_0: from_wf 0 == zero.
    Proof.
      rewrite -> from_wf_eq.
      apply zero_empty. intros [[x lt]].
      contradict lt. auto with arith.
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

    Definition from_nat (n: nat): Ord := Nat.iter n succ zero.

    Proposition from_wf_is_from_nat:
      pointwise_relation _ eq (from_wf (R := Peano.lt)) from_nat.
    Proof.
      intro n; induction n.
      - apply from_wf_0.
      - simpl. rewrite <- IHn. apply from_wf_S.
    Qed.

    Lemma from_nat_src (n: nat): (0 < n)%nat → unit = src (from_nat n) :> Type.
    Proof.
      intro H. rewrite <- (Nat.succ_pred_pos _ H). reflexivity.
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
    
    Property from_nat_le_inv m n: (from_nat m ≤ from_nat n)%nat → m <= n.
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

    Section Def.
      Context {I: Type}.
      Variable x: I → Ord.

      Let Smap (j: {i:I & src (x i)}) : Ord :=
        let (i, a) := j in src_map (x i) a.

      Definition sup: Ord := ssup Smap.

      Property sup_property: ∀ i: I, x i ≤ sup.
      Proof.
        intro i. destruct (x i) as [A f] eqn: E.
        intro a.
        exists (existT _ i (eq_rect _ _ a _ (symmetry E))).
        simpl. rewrite -> E. reflexivity.
      Qed.

      Property sup_minimality: ∀ s, (forall i, x i ≤ s) → sup ≤ s.
        intros s H. destruct s eqn: E.
        apply le_lt.
        intros [i a]. rewrite <- (H i).
        simpl. destruct (x i). apply lt_ssup.
      Qed.

    End Def.

    #[export]
    Instance sup_compat {I}: Proper (pointwise_relation I eq ==> eq) sup.
    Proof.
      autounfold. intros o o' H.
      split. apply sup_minimality. intro i.
      1: rewrite -> (H i).
      2: rewrite <- (H i).
      apply sup_property.
    Qed.

  End Supremum.


  Section Max.

    Definition max x y: Ord := ssup (sum_rect _ (src_map x) (src_map y)).

    Property max_ge_L x y: x ≤ max x y.
    Proof.
      destruct x, y.
      intro a; eexists (inl a). reflexivity.
    Qed.

    Property max_ge_R x y: y ≤ max x y.
    Proof.
      destruct x, y.
      intro a; exists (inr a). reflexivity.
    Qed.

    Definition max_ge x y := conj (max_ge_L x y) (max_ge_R x y).

    Property max_minimality x y: ∀ z, x ≤ z → y ≤ z → max x y ≤ z.
    Proof.
      destruct x, y, z; simpl.
      intros H1 H2 p. destruct p as [a | a].
      1: destruct (H1 a). 2: destruct (H2 a).
      eexists; eassumption.
    Qed.

    Let bmap (x y: Ord) (b: bool) := if b then x else y.

    Corollary max_is_sup: ∀ x y, max x y == sup (bmap x y).
    Proof.
      split.
      - apply max_minimality.
        pose (S := sup_property (bmap x y)).
        + exact (S true).
        + exact (S false).
      - apply sup_minimality.
        destruct i; simpl; apply max_ge.
    Qed.
  
    #[export] Instance max_covariance: Proper (le ++> le ++> le) max.
    Proof.
      intros [A f] [B g] Le [A' f'] [B' g'] Le'.
      intro x; destruct x as [a | a].
      - destruct (Le a) as [x]; now exists (inl x).
      - destruct (Le' a) as [x]; now exists (inr x).
    Qed.

    #[export] Instance max_compat: Proper (eq ==> eq ==> eq) max.
    Proof.
      do 2 destruct 1; split; now apply max_covariance.
    Qed.

    #[export] Instance max_strict_covariance: Proper (lt ++> lt ++> lt) max.
    Proof.
    Abort.
  
  End Max.

End Ord.

#[export] Instance Ord_lt_rewrite: RewriteRelation Ord.lt := {}.
#[export] Instance Ord_le_rewrite: RewriteRelation Ord.le := {}.
#[export] Instance Ord_eq_rewrite: RewriteRelation Ord.eq := {}.
