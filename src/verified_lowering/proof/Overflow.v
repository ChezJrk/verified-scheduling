From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Zdiv.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import micromega.Zify.

Import ListNotations.

From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics
     Zexpr Bexpr Array.

Open Scope string_scope.

Lemma result_state_compat_restore : forall ec st st' h p x,
    ~ p \in dom ec ->
    result_state_compat ec st h ->
    st $+ (p, x) $<= st' ->
    result_state_compat ec (restore st st') h.
Proof.
  intros.
  unfold result_state_compat in *.
  firstorder; subst.
  cases (x0 ==v p); subst.
  - apply lookup_Some_dom in H2. propositional.
  - pose proof H2. apply H0 in H2. clear H0. invs. clear H4.
    specialize (H0 s). firstorder.
    erewrite lookup_restore.
    eapply includes_lookup with (m:=st $+ (p,x)).
    rewrite lookup_add_ne. auto. auto. auto.
    eapply lookup_Some_dom. eassumption.
Qed.

Lemma subset_add_restore {X} : forall (st st' : fmap var X) p x,
    st $+ (p, x) $<= st' ->
    p \in dom st ->
          restore st st' = st $+ (p,x).
Proof.
  intros.
  apply fmap_ext. intros.
  cases (k ==v p); subst.
  - rewrite lookup_add_eq.
    rewrite lookup_restore.
    eapply add_includes_lookup. eassumption. propositional. auto.
  - rewrite lookup_add_ne by auto.
    cases (st $? k).
    + rewrite lookup_restore.
      eapply includes_lookup. 2: eassumption.
      rewrite lookup_add_ne. auto. auto.
      eapply lookup_Some_dom. eassumption.
    + pose proof Heq. apply lookup_None_dom in Heq.
      unfold restore.
      apply lookup_restrict_false. auto.
Qed.

Lemma restore_id {X} : forall (st st' : fmap var X),
    st $<= st' ->
    restore st st' = st.
Proof.
  intros. unfold restore.
  apply fmap_ext. intros.
  cases (st $? k).
  - rewrite lookup_restrict_true.
    eapply includes_lookup; try eassumption.
    eapply lookup_Some_dom. eassumption.
  - apply lookup_restrict_false.
    apply lookup_None_dom. assumption.
Qed.

Inductive is_permutation {X} : list X -> list X -> Prop :=
| NilPermute : is_permutation [] []
| ConsPermuteMatch : forall x xs1 xs2,
    is_permutation xs1 xs2 ->
    is_permutation (x::xs1) (x::xs2)
| ConsPermuteSwap : forall x y xs1 xs2,
    is_permutation xs1 xs2 ->
    is_permutation (x::y::xs1) (y::x::xs2).  

Lemma size_from_shape_list_permutation : forall l1 l2,
    is_permutation l1 l2 ->
    size_from_shape_list l1 = size_from_shape_list l2.
Proof.
  induct 1; simplify.
  - auto.
  - cases xs1; cases xs2; try now invert H; auto.
    simpl in *. repeat rewrite Z.mul_1_l in *.
    repeat rewrite (Z.mul_comm x).
    repeat rewrite fold_left_mul_assoc.
    lia.
  - rewrite Z.mul_comm.
    cases xs1; cases xs2; simpl in *; try lia; try now invert H; auto.
    repeat rewrite Z.mul_1_l in *.
    replace (y*x*z)%Z with (z*(y*x))%Z by lia.
    replace (y*x*z0)%Z with (z0*(y*x))%Z by lia.
    repeat rewrite fold_left_mul_assoc.
    lia.
Qed.

Theorem result_state_compat_mono_stack : forall ec st h' r p,
    result_state_compat ec st h' ->
    result_state_compat (ec $+ (p, S r)) (st $+ (p, r)) h'.
Proof.
  unfold result_state_compat.
  firstorder.
  - cases (p ==v x); subst.
    + rewrite lookup_add_eq in * by auto.
      equality.
    + rewrite lookup_add_ne in * by auto.
      apply H in H0. propositional.
      auto.
  - cases (p ==v x); subst.
    + rewrite lookup_add_eq in * by auto.
      equality.
    + rewrite lookup_add_ne in * by auto.
      apply H in H0. propositional. auto.
Qed.

Lemma stack_heap_separate_add_stack : forall st h x v,
    stack_heap_separate st h ->
    h $? x = None ->
    stack_heap_separate (st $+ (x,v)) h.
Proof.
  intros.
  unfold stack_heap_separate in *.
  firstorder.
  - cases (x ==v x0); subst.
    + auto.
    + rewrite lookup_add_ne in * by auto.
      apply H in H2. auto.
  - cases (x ==v x0); subst.
    + rewrite lookup_add_eq in * by auto.
      rewrite H0 in H2. discriminate.
    + rewrite lookup_add_ne in * by auto.
      apply H1 in H2. auto.
Qed.

Lemma stack_heap_separate_add_heap : forall st h x v,
    stack_heap_separate st h ->
    st $? x = None ->
    stack_heap_separate st (h $+ (x,v)).
Proof.
  intros.
  unfold stack_heap_separate in *.
  firstorder.
  - cases (x ==v x0); subst.
    + rewrite H0 in H2. discriminate.
    + rewrite lookup_add_ne in * by auto.
      apply H in H2. auto.
  - cases (x ==v x0); subst.
    + auto.
    + rewrite lookup_add_ne in * by auto.
      apply H1 in H2. auto.
Qed.

Theorem stack_heap_separate_alloc : forall st h p esh sta ha,
    stack_heap_separate st h ->
    ~ p \in dom st \cup dom h ->            
            alloc_stack_heap esh p st h = (sta,ha) ->
            stack_heap_separate sta ha.
Proof.
  intros.
  destruct esh; simpl in *; invert H1.
  - eapply stack_heap_separate_add_stack. auto.
    destruct (ha $? p) eqn:e; eauto.
    apply lookup_Some_dom in e. sets.
  - unfold alloc_array_in_heap.
    eapply stack_heap_separate_add_heap. auto.
    destruct (sta $? p) eqn:e; eauto.
    apply lookup_Some_dom in e. sets.
Qed.

Theorem alloc_stack_heap_separate : forall st h p sta ha l,
    stack_heap_separate st h ->
    st $? p = None ->
    h $? p = None ->    
    alloc_stack_heap l p st h = (sta, ha) ->
    stack_heap_separate sta ha.
Proof.
  intros. destruct l; simpl in *.
  - unfold stack_heap_separate in *.
    invert H2.
    firstorder.
    + cases (x ==v p); subst; eauto.
      erewrite lookup_add_ne in * by auto.
      eauto.
    + cases (x ==v p); subst.
      * rewrite H1 in H3. discriminate.
      * erewrite lookup_add_ne in * by auto. eauto.
  - invert H2.
    unfold stack_heap_separate in *.
    firstorder.
    + cases (x ==v p); subst.
      * rewrite H0 in H3. discriminate.
      * unfold alloc_array_in_heap.
        simpl. rewrite Nat.add_0_r.
        destruct (fold_left mul l n).
        -- erewrite lookup_add_ne in * by auto.
           eapply H in H3. auto.
        -- erewrite lookup_add_ne in * by auto. eauto.
    + cases (x ==v p); subst.
      * auto.
      * unfold alloc_array_in_heap in *.
        simpl in *. rewrite Nat.add_0_r in *.
        destruct (fold_left mul l n).
        -- erewrite lookup_add_ne in * by auto.
           apply H2 in H3. auto.
        -- erewrite lookup_add_ne in * by auto.
           eauto.
Qed.

Theorem not_stack_heap_not_in_context : forall p st ha ec,
    ~ p \in dom st \cup dom ha ->
            result_state_compat ec st ha ->
            ec $? p = None.
Proof.
  intros.
  unfold result_state_compat in *.
  cases (ec $? p); auto.
  pose proof Heq.
  apply H0 in Heq. clear H0.
  propositional.
  cases r.
  - specialize (H0 z). propositional.
    apply lookup_Some_dom in H3. sets.
  - specialize (H2 v). propositional. cases H3.
    propositional.
    apply lookup_Some_dom in H3. sets.
Qed.

Theorem result_state_compat_add_stack : forall ec st h x r,
    ~x \in dom ec ->
           result_state_compat ec st h ->
           result_state_compat ec (st $+ (x, r)) h.
Proof.
  intros.
  unfold result_state_compat in *.
  firstorder. pose proof H1.
  apply H0 in H1. clear H0. propositional.
  apply H0 in H2.
  cases (x ==v x0).
  - subst. apply lookup_Some_dom in H3. sets.
  - rewrite lookup_add_ne by auto. auto.
Qed.

Theorem result_state_compat_add_heap : forall ec st h x r,
    ~x \in dom ec ->
           result_state_compat ec st h ->
           result_state_compat ec st (h $+ (x,r)).
Proof.
  intros.
  unfold result_state_compat in *.  
  firstorder; subst.
  cases (x0 ==v x); subst.
  - apply lookup_Some_dom in H1. propositional.
  - rewrite lookup_add_ne in * by auto.
    eapply H0 in H1. clear H0. invs. clear H0.
    specialize (H2 l). propositional.
Qed.

Theorem dom_alloc : forall sta ha st h p eshz,
    alloc_stack_heap (map Z.to_nat eshz) p st h = (sta, ha) ->
    dom sta \cup dom ha = constant [p] \cup dom st \cup dom h.
Proof.
  intros.
  destruct eshz; simpl in *; invert H.
  - simpl.
    f_equal.
    rewrite dom_add. auto.
  - unfold alloc_array_in_heap.
    simpl.
    repeat rewrite dom_add.
    sets.
Qed.

Theorem alloc_stack_id : forall l p st st'',
    alloc_stack l p st $<= st'' ->
    alloc_stack l p st'' = st''.
Proof.
  destruct l; intros; simpl in *; auto.
  apply add_id.
  eapply add_includes_lookup.
  eassumption.
Qed.

Theorem alloc_heap_id : forall l p st st'',
    alloc_heap l p st $<= st'' ->
    alloc_heap l p st'' = st''.
Proof.
  destruct l; intros; simpl in *; auto.
  apply add_id.
  unfold alloc_array_in_heap in H.
  eapply add_includes_lookup.
  eassumption.
Qed.

