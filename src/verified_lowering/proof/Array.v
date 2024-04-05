From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Coq Require Import ZArith.Zdiv.
From Coq Require Import ZArith.Int.
From Coq Require Import ZArith.Znat.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.

Set Warnings "-deprecate-hint-without-locality,-deprecated".
Import ListNotations.

From ATL Require Import Map Sets FrapWithoutSets Div Tactics.
From Lower Require Import ListMisc Range Constant.

Open Scope string_scope.

Definition array := fmap Z R.
Definition heap := fmap string array.

Definition lookup_total (h : heap) p : array :=
  match h $? p with
  | Some arr => arr
  | None => $0
  end.
Infix "$!" := lookup_total (at level 50, no associativity).


Lemma map_add_swap {X} : forall v1 v2 r1 r2 (ec : fmap var X),
    v1 <> v2 ->
    (ec $+ (v1, r1) $+ (v2,r2)) =
    (ec $+ (v2, r2) $+ (v1,r1)).
Proof.
  intros.
  maps_equal.
Qed.

Fixpoint alloc_array n m :=
  match n with
  | O => m
  | Datatypes.S n' => (alloc_array n' m) $+ (Z.of_nat n', 0%R)
  end.

(* TODO : fix this definition for adding two maps together *)
Definition array_add (arr1 arr2 : array) : array :=
  merge (fun v1 v2 => match v1 with
                      | Some r1 => match v2 with
                                   | Some r2 => Some (r1 + r2)%R
                                   | None => v1
                                   end
                      | None => v2
                      end) arr1 arr2.

Lemma array_add_empty_r : forall arr1,
    array_add arr1 $0 = arr1.
Proof.
  intros. unfold array_add.
  rewrite merge_empty2.
  reflexivity.
  intros.
  cases x; auto.
Qed.

Lemma array_add_comm : forall arr1 arr2,
    array_add arr1 arr2 = array_add arr2 arr1.
Proof.
  intros.
  unfold array_add.
  apply fmap_ext. intros.
  repeat rewrite lookup_merge.
  cases (arr1 $? k); cases (arr2 $? k); f_equal; ring.
Qed.

Lemma array_add_empty_l : forall arr1,
    array_add $0 arr1 = arr1.
Proof.
  intros. rewrite array_add_comm. apply array_add_empty_r.
Qed.

Lemma includes_remove_add : forall B (c v : fmap string B) x n,
  c $<= v ->
  c $- x $<= v $+ (x, n).
Proof.
  simplify; apply includes_intro; simplify.
  cases (x ==v k); subst; simplify; try equality.
  eauto using includes_lookup.
Qed.

Lemma includes_add_new {B} : forall (v : fmap string B) (p : string) n,
    v $? p = None ->
    v $<= v $+ (p,n).
Proof.
  intros.
  apply includes_intro.
  intros.
  cases (k ==v p); subst.
  - rewrite H in H0. discriminate.
  - rewrite lookup_add_ne by auto. auto.
Qed.

Lemma None_dom_lookup : forall K V (m : fmap K V) k,
    ~ k \in dom m -> m $? k = None.
Proof.
  intros.
  cases (m $? k).
  - apply lookup_Some_dom in Heq.
    firstorder.
  - auto.
Qed.

Theorem map_add_subset_eq {X} : forall (st st' : fmap string X) p r,
    ~ p \in dom st ->
            st $+ (p, r) $<= st' ->
            st $<= st'.
Proof.
  intros.
  pose proof (None_dom_lookup _ _ _ _ H).
  eapply includes_intro. intros.
  cases (k ==v p); subst.
  - rewrite H1 in H2. discriminate.
  - eapply includes_lookup.
    2: eassumption.
    erewrite lookup_add_ne by auto. auto.
Qed.

Theorem add_includes_lookup {X} : forall (st st'' : fmap string X) p v,
    st $+ (p, v) $<= st'' ->
    st'' $? p = Some v.
Proof.
  intros.
  eapply includes_lookup; try eassumption.
  rewrite lookup_add_eq; auto.
Qed.

Theorem add_id {X} : forall (st : fmap string X) p v,
    st $? p = Some v ->
    st $+ (p,v) = st.
Proof.
  intros.
  apply fmap_ext; intros.
  cases (k ==v p); subst; 
    try rewrite lookup_add_eq by auto;
    try rewrite lookup_add_ne by auto;
    auto.
Qed.  

Theorem add_arr_id {X} : forall (st : fmap Z X) p v,
    st $? p = Some v ->
    st $+ (p,v) = st.
Proof.
  intros.
  apply fmap_ext; intros.
  assert (k = p \/ k <> p) by lia. cases H0; subst;
    try rewrite lookup_add_eq by auto;
    try rewrite lookup_add_ne by auto;
    auto.
Qed.  

Lemma add_overwrite {X} : forall (m : fmap string X) x a b,
    m $+ (x,a) $+ (x,b) = m $+ (x,b).
Proof.
  intros. sets.
Qed.

Lemma add_array_overwrite {X} : forall (m : fmap Z X) x a b,
    m $+ (x,a) $+ (x,b) = m $+ (x,b).
Proof.
  intros. sets.
Qed.

Theorem add_remove_id {X} : forall x (h : fmap string X) v,
    ~ x \in dom h ->
    h = h $+ (x, v) $- x.
Proof.
  intros. apply fmap_ext. intros.
  cases (k ==v x); subst.
  - rewrite lookup_remove_eq.
    apply None_dom_lookup. auto. auto.
  - rewrite lookup_remove_ne; auto.
    rewrite lookup_add_ne by auto. auto.
Qed.

Theorem dom_lookup_Some {K X} : forall (h : fmap K X) x,
    x \in dom h ->
          exists s, h $? x = Some s.
Proof.
  intros.
  cases (h $? x).
  eexists. equality.
  apply lookup_None_dom in Heq.
  propositional.
Qed.

Lemma array_add_singleton : forall offset old r0 nval r1,
    nval $? offset = Some old ->
    (r1 = r0 + old)%R ->
    array_add nval ($0 $+ (offset, r0)) = nval $+ (offset, r1).
Proof.
  intros.
  apply fmap_ext. intros.
  assert (k = offset \/ k <> offset) by lia. cases H1.
  -- subst. rewrite lookup_add_eq by auto.
     unfold array_add.
     rewrite lookup_merge. rewrite H. rewrite lookup_add_eq by auto.
     rewrite Rplus_comm. auto.
  -- rewrite lookup_add_ne by auto.
     unfold array_add. rewrite lookup_merge.
     rewrite lookup_add_ne by auto. rewrite lookup_empty.
     cases (nval $? k); auto.
Qed.

Lemma union_empty_r {X} : forall (m : set X),
    m \cup constant nil = m.
Proof. sets. Qed.

#[export] Hint Resolve includes_refl array_add_singleton : core.
#[export] Hint Resolve add_arr_id add_id union_empty_r : core.
#[export] Hint Extern 4 (_ = constant nil) => sets : core.
#[export] Hint Extern 4 (_ \subseteq _) => sets : core.

Lemma cap_empty_monotone {X} : forall (s1 s2 s3 : set X),
  s1 \subseteq s2 ->
  s2 \cap s3 = constant [] ->
  s1 \cap s3 = constant [].
Proof. intros. sets. Qed.

Ltac reduce_sets H :=
        match type of H with
        | (_ \cup _) \cap _ = constant nil => rewrite cap_distr in H;
                                              apply cup_empty in H;
                                              let new := fresh "H" in
                                              destruct H as [ H new ];
                                              reduce_sets H;
                                              reduce_sets new
        | _ \cap (_ \cup _) = constant nil => rewrite intersection_comm in H;
                                              rewrite cap_distr in H;
                                              apply cup_empty in H;
                                              let new := fresh "H" in
                                              destruct H as [ H new ];
                                              reduce_sets H;
                                              reduce_sets new
        | _ => idtac
        end.

Lemma includes_trans {X Y} : forall (m1 m2 m3 : fmap X Y),
    m1 $<= m2 ->
    m2 $<= m3 ->
    m1 $<= m3.
Proof.
  intros.
  apply includes_intro. intros.
  eapply includes_lookup in H1. 2: eassumption.
  eapply includes_lookup in H1. 2: eassumption.
  auto.
Qed.  

Lemma subset_cup_monotone {X} : forall (s1 s2 s3 s4 : set X),
    s1 \subseteq s3 ->
    s2 \subseteq s4 ->
    s1 \cup s2 \subseteq s3 \cup s4.
Proof. sets. Qed.

Lemma list_app_middle {X} : forall (l zs : list X) z,
    (l ++ z :: zs = (l ++ [z]) ++ zs)%list.
Proof. induct l; intros; simpl; equality. Qed.

Lemma dom_restrict {Y} : forall P (m : fmap var Y),
    dom (restrict P m) = (dom m \cap P).
Proof.
  intros.
  apply sets_equal. propositional.
  - replace ((dom m \cap P) x) with (x \in (dom m \cap P))
      by equality.
    replace ((dom (restrict P m)) x) with (x \in dom (restrict P m)) in H
        by equality.
    eapply dom_lookup_Some in H. invert H.
    pose proof H0.
    apply lookup_restrict_true_fwd in H.
    pose proof H.
    eapply lookup_restrict_true with (m:=m) in H.
    assert (m $? x = Some x0) by equality.
    apply lookup_Some_dom in H2. sets.
  - replace ((dom m \cap P) x) with (x \in (dom m \cap P)) in *
      by equality.
    replace ((dom (restrict P m)) x) with (x \in dom (restrict P m))
      by equality.
    assert (x \in dom m) by sets.
    assert (P x) by sets.
    eapply dom_lookup_Some in H0. invert H0.
    eapply lookup_Some_dom with (v:=x0).
    eapply lookup_restrict_true in H1.
    rewrite <- H2. apply H1.
Qed.
Lemma subset_cap_empty {X} : forall (x s s' : set X),
  s \cap s' = constant nil ->
  x \subseteq s' ->
  x \cap s = constant nil.
Proof. sets. Qed.

Lemma array_add_assoc : forall arr1 arr2 arr3,
    array_add arr1 (array_add arr2 arr3) =
      array_add (array_add arr1 arr2) arr3.
Proof.
  intros. unfold array_add.
  apply fmap_ext. intros.
  repeat rewrite lookup_merge.
  cases (arr1 $? k); cases (arr2 $? k); cases (arr3 $? k);
    f_equal; try ring.
Qed.

Lemma add_comm {X Y} : forall k1 k2 r1 r2 (arr : fmap X Y),
    k1 <> k2 ->
    arr $+ (k1,r1) $+ (k2,r2) = arr $+ (k2,r2) $+ (k1,r1).
Proof. sets. Qed.

Lemma array_add_add_singleton : forall arr1 arr2 k r1 r2,
    array_add (arr1 $+ (k,r1)) (arr2 $+ (k,r2)) =
      array_add arr1 arr2 $+ (k,(r1+r2)%R).
Proof.
  intros. unfold array_add.
  apply fmap_ext. intros.
  repeat rewrite lookup_merge.
  assert (k = k0 \/ k <> k0) by lia.
  cases H; subst;
    repeat rewrite lookup_add_eq by auto;
    repeat rewrite lookup_add_ne by auto.
  - reflexivity.
  - rewrite lookup_merge. reflexivity.
Qed.

Local Hint Resolve includes_add_new None_dom_lookup.

Lemma array_add_l : forall a b c,
    a = c ->
    array_add a b = array_add c b.
Proof. auto. Qed.

Lemma array_add_r : forall a b c,
    a = c ->
    array_add b a = array_add b c.
Proof. auto. Qed.

Lemma array_add_singleton_collapse : forall k1 val1 arr,
    ~ k1 \in dom arr ->
             array_add arr ($0 $+ (k1,val1)) = arr $+ (k1,val1).
Proof.
  unfold array_add. intros.
  rewrite merge_add2.
  rewrite None_dom_lookup by auto.
  rewrite merge_empty2. reflexivity.
  intros. cases x; auto.
  intros. cases x; discriminate.
  rewrite dom_empty. sets.
Qed.

Lemma dom_array_add : forall a b,
    dom (array_add a b) = dom a \cup dom b.
Proof.
  intros. unfold array_add.
  apply sets_equal. propositional.
  - eapply dom_lookup_Some in H.
    invert H.
    rewrite lookup_merge in H0.
    cases (a $? x); cases (b $? x).
    + eapply lookup_Some_dom in Heq. sets.
    + eapply lookup_Some_dom in Heq. sets.
    + eapply lookup_Some_dom in Heq0. sets.
    + discriminate.
  - cases (a $? x); cases (b $? x).
    + eapply lookup_Some_dom.
      rewrite lookup_merge.
      rewrite Heq, Heq0. reflexivity.
    + eapply lookup_Some_dom.
      rewrite lookup_merge.
      rewrite Heq, Heq0. reflexivity.
    + eapply lookup_Some_dom.
      rewrite lookup_merge.
      rewrite Heq, Heq0. reflexivity.
    + eapply lookup_None_dom in Heq.
      eapply lookup_None_dom in Heq0.
      sets.
Qed.

Lemma dom_fold_left_array_add :
  forall (domain : list (list Z)) f g acc,
    dom (fold_left (fun arr index => array_add arr ($0 $+ (f index, g index)))
                   domain acc) =
      constant (map f domain) \cup dom acc.
Proof.
  induct domain; intros.
  - simpl. sets.
  - simpl. rewrite IHdomain. rewrite dom_array_add.
    rewrite dom_add. rewrite dom_empty.
    sets.
Qed.    

Lemma lookup_array_add_l : forall a b k,
    k \in dom a ->
          dom a \cap dom b = constant [] ->
          array_add a b $? k = a $? k.
Proof.
  intros.
  unfold array_add.
  rewrite lookup_merge.
  cases (a $? k).
  + cases (b $? k).
    * eapply lookup_Some_dom in Heq.
      eapply lookup_Some_dom in Heq0.
      sets.
    * reflexivity.
  + eapply lookup_None_dom in Heq. sets.
Qed.

Lemma lookup_array_add_r : forall a b k,
    k \in dom b ->
          dom a \cap dom b = constant [] ->
          array_add a b $? k = b $? k.
Proof.
  intros.
  unfold array_add.
  rewrite lookup_merge.
  cases (a $? k).
  + cases (b $? k).
    * eapply lookup_Some_dom in Heq.
      eapply lookup_Some_dom in Heq0.
      sets.
    * eapply lookup_None_dom in Heq0. sets.
  + reflexivity.
Qed.

Lemma lookup_total_add_ne : forall k k' m x,
    k <> k' -> (m $+ (k,x)) $! k' = m $! k'.
Proof.
  unfold lookup_total.
  intros. rewrite lookup_add_ne by auto.
  reflexivity.
Qed.

Lemma lookup_total_add_eq : forall k m x,
    (m $+ (k,x)) $! k = x.
Proof.
  unfold lookup_total.
  intros. rewrite lookup_add_eq by auto.
  reflexivity.
Qed.

Lemma array_add_remove : forall arr1 arr2 k,
    array_add arr1 arr2 $- k =
      array_add (arr1 $- k) (arr2 $- k).
Proof.
  intros. eapply fmap_ext. intros.
  assert (k = k0 \/ k <> k0) by lia. propositional.
  - subst. rewrite lookup_remove_eq by auto.
    unfold array_add.
    rewrite lookup_merge.
    rewrite lookup_remove_eq by auto.
    rewrite lookup_remove_eq by auto.
    reflexivity.
  - rewrite lookup_remove_ne by auto.
    unfold array_add.
    rewrite lookup_merge.
    rewrite lookup_merge.
    rewrite lookup_remove_ne by auto.
    rewrite lookup_remove_ne by auto.
    reflexivity.
Qed.

Lemma add_remove_comm {X Y} : forall arr (k1 k2 : X) (x : Y),
    (forall (k k' : X), k = k' \/ k <> k') ->
    k1 <> k2 ->
    arr $+ (k1,x) $- k2 = arr $- k2 $+ (k1,x).
Proof.
  intros.
  apply fmap_ext. intros.
  pose proof (H k k2). propositional.
  - subst. rewrite lookup_remove_eq by auto.
    rewrite lookup_add_ne by auto.
    rewrite lookup_remove_eq by auto.
    reflexivity.
  - rewrite lookup_remove_ne by auto.
    pose proof (H k k1). propositional.
    + subst. rewrite lookup_add_eq by auto.
      rewrite lookup_add_eq by auto.
      reflexivity.
    + rewrite lookup_add_ne by auto.
      rewrite lookup_add_ne by auto.
      rewrite lookup_remove_ne by auto.
      reflexivity.
Qed.  

Lemma add_remove {Y} : forall k (arr : fmap string Y) x,
    arr $+ (k,x) $- k = arr $- k.
Proof.
  intros. eapply fmap_ext. intros.
  cases (k ==v k0).
  - subst. repeat rewrite lookup_remove_eq by auto. reflexivity.
  - repeat rewrite lookup_remove_ne by auto.
    rewrite lookup_add_ne by auto.
    reflexivity.
Qed.  

Lemma array_add_add_assoc : forall arr1 arr2 k x,
    ~ k \in dom arr2 ->
    array_add (arr1 $+ (k,x)) arr2 = array_add arr1 arr2 $+ (k,x).
Proof.
  intros.
  unfold array_add.
  eapply fmap_ext. intros.
  rewrite lookup_merge.
  assert (k = k0 \/ k <> k0) by lia. invert H0.
  - repeat rewrite lookup_add_eq by auto.
    eapply None_dom_lookup in H. rewrite H. reflexivity.
  - repeat rewrite lookup_add_ne by auto.
    rewrite lookup_merge.
    eapply None_dom_lookup in H. 
    cases (arr1 $? k0); cases (arr2 $? k0); auto.
Qed.

Lemma map_decompose_singleton : forall m (k : Z) (x : R),
    m $? k = Some x ->
    m = (m $- k) $+ (k, x).
Proof.
  intros. eapply fmap_ext. intros.
  assert (k = k0 \/ k <> k0) by lia.
  propositional.
  - subst. rewrite lookup_add_eq by auto. auto.
  - rewrite lookup_add_ne by auto.
    rewrite lookup_remove_ne by auto. reflexivity.
Qed.  

Lemma array_add_add : forall arr1 arr2 k x1 x2,
    array_add (arr1 $+ (k,x1)) (arr2 $+ (k,x2)) =
      array_add arr1 arr2 $+ (k,(x1+x2)%R).
Proof.
  intros. eapply fmap_ext. unfold array_add. intros.
  repeat rewrite lookup_merge.
  assert (k = k0 \/ k <> k0) by lia. propositional.
  - subst. repeat rewrite lookup_add_eq by auto. reflexivity.
  - repeat rewrite lookup_add_ne by auto.
    rewrite lookup_merge. reflexivity.
Qed.    

Lemma remove_add_overwrite {Y} : forall (m : fmap Z Y) k x,
    m $- k $+ (k,x) = m $+ (k,x).
Proof.
  intros. eapply fmap_ext. intros.
  assert (k = k0 \/ k <> k0) by lia. propositional.
  - subst. repeat rewrite lookup_add_eq by auto.
    reflexivity.
  - repeat rewrite lookup_add_ne by auto.
    rewrite lookup_remove_ne by auto.
    reflexivity.
Qed.

Ltac invs :=
  repeat
    match goal with
    | H : _ /\ _ |- _ => invert H
    | H : exists _, _ |- _ => invert H
    | H : _ = (_,_) |- _ => invert1 H
    | H : Some _ = Some _ |- _ => invert H
  end.

Lemma array_add_alloc_array : forall n arr,
    dom arr = constant (map Z.of_nat (nat_range n)) ->
    arr = array_add (alloc_array n $0) arr.
Proof.
  induct n; intros.
  - rewrite array_add_empty_l. reflexivity.
  - unfold nat_range in *.
    rewrite succ_nat_range_rec_app_end in *.
    simpl. posnats.
    rewrite map_app in *.
    rewrite <- union_constant in *.    
    simpl map in H at 2. rewrite add_0_r in *. posnats.
    assert (Z.of_nat n \in dom arr). sets. rewrite H. sets.
    eapply dom_lookup_Some in H0. invs.
    erewrite map_decompose_singleton with (m:=arr) (k:= Z.of_nat n) at 2.
    2: eassumption.
    rewrite array_add_add.
    rewrite <- IHn.
    rewrite remove_add_overwrite.
    rewrite add_arr_id. reflexivity.
    rewrite H1. f_equal. ring.
    rewrite dom_remove. rewrite H.
    sets.
    eapply in_map_iff in H0. invs.
    eapply in_map_iff in H2. invs.
    eapply range_nat_range_rec in H6. lia.
    clear H0. posnats.
    eapply in_map_iff in H2. invs.
    eapply range_nat_range_rec in H3. lia.
Qed.

Lemma dom_alloc_array : forall n,
    dom (alloc_array n $0) = constant (zrange 0 (Z.of_nat ( n))).
Proof.
  induct n; unfold zrange in *; intros.
  - simpl. rewrite dom_empty. reflexivity.
  - rewrite Z.sub_0_r in *. rewrite Nat2Z.id in *.
    rewrite succ_zrange'_app_end.
    simpl.
    rewrite dom_add. rewrite IHn. rewrite <- union_constant.
    sets.
Qed.

Definition alloc_array_in_heap l (h : heap) p :=
  let n := match l with
           | [] => O
           | _ => fold_left Nat.mul l 1
           end in
  h $+ (p,alloc_array n $0).

Lemma remove_id {Y} : forall (h : fmap var Y) x,
    ~ x \in dom h ->
            h $- x = h.
Proof.
  intros. apply fmap_ext. intros.
  cases (x ==v k). subst. rewrite lookup_remove_eq; auto.
  rewrite None_dom_lookup; auto.
  rewrite lookup_remove_ne by auto. auto.
Qed.

Lemma lookup_alloc_array : forall n k,
    (alloc_array n $0) $? k = None \/ (alloc_array n $0) $? k = Some 0%R.
Proof.
  induct n; intros.
  - simpl. rewrite lookup_empty. auto.
  - simpl.
    assert (k = Z.of_nat n \/ k <> Z.of_nat n)%Z by lia. invert H.
    + rewrite lookup_add_eq by auto. propositional.
    + rewrite lookup_add_ne by auto. eauto.
Qed.

Lemma lookup_array_add_weak_l : forall a1 a2 k,
    ~ k \in dom a2 ->
            (array_add a1 a2) $? k = a1 $? k.
Proof.
  unfold array_add. intros. rewrite lookup_merge.
  cases (a2 $? k). eapply lookup_Some_dom in Heq. sets.
  cases (a1 $? k); eauto.
Qed.

