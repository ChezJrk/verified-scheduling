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
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Open Scope list_scope.

From ATL Require Import Sets FrapWithoutSets.
From Lower Require Import ListMisc.

Lemma constant_cons {X} : forall (x:X) xs,
    constant (x::xs) = constant [x] \cup constant xs.
Proof. sets. Qed.

Lemma constant_filter_or {X} : forall f g (l : list X),
    constant (filter (fun x => f x || g x) l) =
      constant (filter f l) \cup constant (filter g l).
Proof.
  induct l; intros.
  - simpl. sets.
  - simpl. cases (f a); cases (g a); simpl;
      try rewrite constant_cons; try rewrite IHl; sets.
Qed.

Lemma constant_in_bool_list_Z_filter_eq : forall d2 a,
    in_bool_list_Z d2 a = true ->
    constant (filter (eq_list_Z a) d2) = constant [a].
Proof.
  induction d2; intros.
  - simpl in *. discriminate.
  - simpl in *.
    eapply orb_true_iff in H.
    cases (eq_list_Z a0 a).
    + rewrite constant_cons.
      cases (in_bool_list_Z d2 a).
      * eapply eq_list_Z_eq in Heq. subst.
        rewrite IHd2. sets. auto.
      * eapply eq_list_Z_eq in Heq. subst.
        rewrite not_in_bool_list_Z_filter_empty by auto. sets.
    + invert H. rewrite eq_list_Z_comm in Heq. rewrite Heq in H0.
      discriminate.
      eauto.
Qed.

Lemma constant_in_bool_Z_filter_eq : forall d2 z,
          in_bool_Z d2 z = true ->
          constant (filter (Z.eqb z) d2) = constant [z].
Proof.
  induction d2; intros.
  - invert H.
  - simpl in *.
    eapply orb_true_iff in H. invert H.
    + rewrite Z.eqb_sym in H0. rewrite H0.
      eapply Z.eqb_eq in H0. subst.
      rewrite constant_cons.
      cases (in_bool_Z d2 a).
      * rewrite IHd2 by auto. sets.
      * rewrite not_in_bool_Z_filter_empty by auto.
        sets.
    + cases (z =? a)%Z.
      * rewrite constant_cons.
        rewrite IHd2 by auto.
        eapply Z.eqb_eq in Heq. subst. sets.
      * eauto.
Qed.

Lemma cap_distr {X : Type} : forall (a b c : set X),
    (a \cup b) \cap c = (a \cap c) \cup (b \cap c).
Proof.
  sets.
Qed.

Lemma cup_empty {X : Type} : forall (a b : set X),
    a \cup b = constant nil <->
    a = constant nil /\ b = constant nil.
Proof.
  intros.
  split; sets.
Qed.

Lemma constant_cap_empty {X : Type} : forall x (a : set X),
    constant [x] \cap a = constant nil <->
    ~ x \in a.
Proof.
  intros. sets.
Qed.

Lemma cap_id {X} : forall (x : set X),
    x \cap x = x.
Proof. sets. Qed.

Lemma cup_id {X} : forall (x : set X),
    x \cup x = x.
Proof. sets. Qed.

Lemma cap_empty_r {X} : forall (s : set X),
    s \cap constant [] = constant [].
Proof. sets. Qed.

Lemma cap_empty_l {X} : forall (s : set X),
    constant [] \cap s = constant [].
Proof. sets. Qed.
Lemma cup_cap_id {X} : forall (l1 l2 : list X),
    constant l1 \cup (constant l2 \cap constant l1) = constant l1.
Proof. intros. sets. Qed.

Lemma cup_distr {X} : forall (x y z : set X),
    (x \cap y) \cup z = (x \cup z) \cap (y \cup z).
Proof. sets. Qed.

Lemma cap_empty_exclusion {X} : forall p1 p2,
    p1 \cap p2 = constant [] <->
    forall (x : X), (x \in p1 -> ~ x \in p2) /\ (x \in p2 -> ~ x \in p1).
Proof.
  propositional; sets. specialize (H x). invert H. propositional.
Qed.

Lemma cup_empty_l {X} : forall (s : set X),
    constant nil \cup s = s.
Proof. sets. Qed.

Lemma cup_empty_r {X} : forall (s : set X),
    s \cup constant nil = s.
Proof. sets. Qed.

Lemma consant_cap_singleton_in_bool_Z : forall d2 a,
  in_bool_Z d2 a = true ->
  constant d2 \cap constant [a] = constant [a].
Proof.
  induction d2; intros.
  - sets.
  - rewrite constant_cons. simpl in *.
    eapply orb_true_iff in H. invert H.
    + eapply Z.eqb_eq in H0. rewrite H0. sets.
    + eapply IHd2 in H0. rewrite cap_distr.
      rewrite H0.
      sets.
Qed.

Lemma constant_cap_singleton_not_in_bool_Z : forall d2 a,
    in_bool_Z d2 a = false ->
    constant d2 \cap constant [a] = constant [].
Proof.
  induction d2; intros.
  - sets.
  - rewrite constant_cons.
    simpl in *. eapply orb_false_iff in H.
    invert H. eapply Z.eqb_neq in H0.
    eapply IHd2 in H1. sets.
Qed.

Lemma constant_filter_eq_cup : forall x l,
    (constant [x] \cup constant (filter (eq_list_Z x) l)) =
      constant [x].
Proof.
  induct l; intros.
  - simpl. sets.
  - simpl. cases (eq_list_Z x ).
    + simpl. eapply eq_list_Z_eq in Heq. subst.
      rewrite (constant_cons _ (filter _ _)).
      rewrite <- union_assoc. rewrite cup_id. auto.
    + auto.
Qed.

Lemma constant_cap_filter_Z : forall (d1 d2 : list Z),
    constant d1 \cap constant d2 =
      constant (filter (fun x => in_bool_Z d1 x) d2).
Proof.
  induction d1; intros; cases d2.
  - simpl. sets.
  - simpl. rewrite filter_false_empty. sets.
  - simpl. sets.
  - simpl. cases (a =? z)%Z.
    + simpl. eapply Z.eqb_eq in Heq. subst.
      rewrite constant_cons.
      rewrite (constant_cons z d2).
      rewrite (constant_cons _ (filter _ _)).
      rewrite constant_filter_or.
      rewrite cap_distr.
      repeat rewrite (intersection_comm _ (_ \cup _)).
      rewrite cap_distr.
      repeat rewrite (intersection_comm _ (_ \cup _)).
      rewrite cap_distr.
      rewrite cap_id. rewrite cup_cap_id.
      rewrite <- union_assoc.
      rewrite (intersection_comm (constant [z])).
      rewrite cup_cap_id. rewrite intersection_comm.
      rewrite IHd1.
      cases (in_bool_Z d2 z).
      * rewrite constant_in_bool_Z_filter_eq by auto. sets.
      * rewrite not_in_bool_Z_filter_empty by auto. sets.
    + simpl. cases (in_bool_Z d1 z).
      * rewrite constant_cons.
        rewrite (constant_cons z d2).
        rewrite (constant_cons _ (filter _ _)).
        rewrite constant_filter_or.
        rewrite cap_distr.
        repeat rewrite (intersection_comm _ (_ \cup _)).
        rewrite cap_distr.
        repeat rewrite (intersection_comm _ (_ \cup _)).
        rewrite cap_distr.
        eapply Z.eqb_neq in Heq.
        replace (constant [z] \cap constant [a])
          with (constant (@nil Z)) by sets.
        rewrite cup_empty_l.
        rewrite (intersection_comm (constant [z])).
        rewrite IHd1.
        simpl. rewrite Heq0.
        cases (in_bool_Z d2 a).
        -- rewrite constant_in_bool_Z_filter_eq by auto.
           replace (constant d2 \cap constant [a]) with
             (constant [a])
             by (rewrite consant_cap_singleton_in_bool_Z; auto).
           rewrite intersection_comm. rewrite IHd1. sets.
        -- rewrite not_in_bool_Z_filter_empty by auto.
           replace (constant d2 \cap constant [a])
             with (constant (@nil Z))
             by (rewrite constant_cap_singleton_not_in_bool_Z; auto).
           rewrite intersection_comm. rewrite IHd1.
           sets.
      * rewrite constant_cons.
        rewrite (constant_cons z d2).
        rewrite constant_filter_or.
        rewrite cap_distr.
        repeat rewrite (intersection_comm _ (_ \cup _)).
        rewrite cap_distr.
        repeat rewrite (intersection_comm _ (_ \cup _)).
        rewrite cap_distr.
        replace (constant [z] \cap constant d1)
          with (constant (@nil Z)).
        2: { rewrite intersection_comm;
             rewrite constant_cap_singleton_not_in_bool_Z; auto. }
        rewrite cup_empty_l.
        eapply Z.eqb_neq in Heq.
        replace (constant [z] \cap constant [a])
          with (constant (@nil Z)) by sets.
        rewrite cup_empty_l.
        rewrite (intersection_comm _ (constant d1)).
        rewrite IHd1.
        cases (in_bool_Z d2 a).
        -- replace (constant d2 \cap constant [a])
             with (constant [a])
             by (rewrite consant_cap_singleton_in_bool_Z; auto).
           rewrite constant_in_bool_Z_filter_eq by auto.
           sets.
        -- rewrite not_in_bool_Z_filter_empty by auto.
           replace (constant d2 \cap constant [a]) with
             (constant (@nil Z))
             by (rewrite constant_cap_singleton_not_in_bool_Z; auto).
           sets.
Qed.

Lemma subseteq_transitivity {X} : forall (s1 s2 s3 : set X),
    s1 \subseteq s2 ->
    s2 \subseteq s3 ->
    s1 \subseteq s3.
Proof.
  intros. sets.
Qed.

Lemma subseteq_cup_l {X} : forall (a b c : set X),
    a \subseteq b ->
    a \subseteq b \cup c.
Proof. intros. sets. Qed.

Lemma constant_cup_remove {X} :
  forall l (x : X)
         (H: (forall x y : X, {x = y} + {x <> y})),
    x \in constant l ->
          no_dup l ->
          constant l = constant [x] \cup constant (List.remove H x l).
Proof.
  induct l; intros.
  - sets.
  - rewrite constant_cons in *.
    simpl.
    cases (H x a).
    + subst. invert H1.
      rewrite notin_remove by auto.
      auto.
    + invert H1. rewrite (constant_cons _ (List.remove _ _ _)).
      assert (x \in constant l). sets.
      erewrite IHl by eassumption.
      rewrite <- union_assoc.
      rewrite (union_comm (constant [a])).
      rewrite <- union_assoc.
      reflexivity.
Qed.      

Lemma constant_cup_subseteq_eliminate {X} : forall (a : X) l1 l2,
    no_dup l1 ->
    no_dup l2 ->
    ~ a \in constant l1 ->
    ~ a \in constant l2 ->
    constant [a] \cup constant l1 \subseteq constant [a] \cup constant l2 ->
    constant l1 \subseteq constant l2.
Proof.
  intros.
  eapply subseteq_In.
  rewrite subseteq_In in H3.
  intros.
  specialize (H3 x).
  assert (x \in constant [a] \cup constant l1) by sets. propositional.
  assert (x <> a). sets.
  sets.
Qed.

Lemma not_In_remove {X} : forall (a : X) x l H,
    no_dup l ->
    ~ a \in constant l ->
    ~ a \in constant (List.remove H x l).
Proof.
  induct l; intros.
  - sets.
  - simpl.
    invert H0.
    rewrite constant_cons in H1.
    assert (a <> a0) by sets.
    assert (~ a \in constant l) by sets.
    cases (H x a0).
    + subst. eauto.
    + rewrite constant_cons.
      assert (~ a \in constant (List.remove H x l)).
      eauto. sets.
Qed.    

Lemma no_dup_remove {X} : forall (x : X) l H,
    no_dup l ->
    no_dup (List.remove H x l).
Proof.
  induct l; intros.
  - simpl. auto.
  - simpl.
    cases (H x a).
    + invert H0. eauto.
    + econstructor. invert H0. eauto.
      invert H0.
      eapply not_In_remove. auto.
      rewrite <- In_iff_in. auto.
Qed.      

Lemma length_remove {X} : forall X0 l1 (a : X),
    a \in constant l1 ->
    no_dup l1 ->
    Datatypes.S (length (List.remove X0 a l1)) = length l1.
Proof.
  induct l1; intros.
  - sets.
  - rewrite constant_cons in H. simpl.
    cases (X0 a0 a).
    + subst. invert H0.
      rewrite notin_remove by auto. reflexivity.
    + simpl.
      invert H0.
      assert (a0 \in constant l1) by sets.
      eapply IHl1 in H0.
      rewrite H0. reflexivity. auto.
Qed.

Lemma constant_subseteq_length {X} : forall (l2 l1 : list X),
    no_dup l1 ->
    no_dup l2 ->
    constant l1 \subseteq constant l2 ->
    (forall x y : X, {x = y} + {x <> y}) ->
    length l1 <= length l2.
Proof.
  induct l2; intros.
  - cases l1. reflexivity. simpl in *. rewrite constant_cons in H1. sets.
    exfalso. eapply H1. left. left. reflexivity.
  - invert H0. rewrite constant_cons in H1.
    pose proof (in_dec X0). specialize (X1 a l1).
    invert X1.
    + apply In_iff_in in H0. erewrite (constant_cup_remove l1 _ X0) in H1.
      2: eassumption. 2: eassumption.
      eapply constant_cup_subseteq_eliminate in H1.
      3: auto.
      4: unfold not; intros; apply H5; eapply In_iff_in; auto.
      3: { unfold not. intros. eapply In_iff_in in H2. eapply remove_In.
           apply H2. }
      2: { eapply no_dup_remove. auto. }
      simpl.
      eapply IHl2 in H1; auto.
      2: { eapply no_dup_remove. auto. }
      cases l1. sets. simpl in *. invert H.
      cases (X0 a x).
      * subst. rewrite notin_remove in H1 by auto. lia.
      * simpl in *. rewrite length_remove in H1. 2: sets. 2: auto.
        lia.
    + eapply IHl2 in H; auto.
      2: { rewrite subseteq_In in H1.
           eapply subseteq_In. intros.
           assert (a <> x). sets.
           eapply H1 in H2.
           sets. }
      simpl. lia.
Qed.

Lemma constant_singleton_filter_neg_eq : forall l2 a,
  constant [a] \cup constant (filter (fun x : var => negb (a =? x)) l2) =
    constant [a] \cup constant l2.
Proof.
  induct l2; intros.
  - simpl. reflexivity.
  - simpl. cases (a0 =? a).
    + simpl.
      eapply String.eqb_eq in Heq. subst.
      rewrite IHl2. sets.
    + simpl.
      eapply String.eqb_neq in Heq.
      rewrite (constant_cons a). symmetry.
      rewrite (constant_cons a). symmetry.
      repeat rewrite <- union_assoc.
      rewrite (union_comm (constant [a0])).
      repeat rewrite union_assoc.
      f_equal. rewrite IHl2. reflexivity.
Qed.

Lemma cap_monotone_contra {X} : forall (x y z : set X),
      x \cap z = constant [] ->
      y \subseteq z ->
      x \cap y = constant [].
Proof. intros. sets. Qed.

