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
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Open Scope list_scope.

From ATL Require Import Sets FrapWithoutSets.
From Lower Require Import ListMisc.

Fixpoint zrange' lo range :=
  match range with
  | Datatypes.S n => lo::(zrange' (lo+1)%Z n)
  | _ => []
  end.

Definition zrange lo hi := zrange' lo (Z.to_nat (hi-lo)%Z).

Fixpoint nat_range_rec k x :=
  match k with
  | 0 => []
  | Datatypes.S n => x::(nat_range_rec n (x+1))
  end.

Definition nat_range k := nat_range_rec k 0.

Lemma map_zrange'_shift_1 {X} : forall k lo (f : Z -> X),
    map f (zrange' (lo+1)%Z k) =
      map (fun x => f (x+1)%Z) (zrange' lo k).
Proof.
  induct k; intros.
  - reflexivity.
  - simpl in *. f_equal. auto.
Qed.

Lemma map_zrange'_shift_lo {X} : forall k lo (f : Z -> X),
    map f (zrange' lo k) =
      map (fun x => f (x+lo)%Z) (zrange' 0%Z k).
Proof.
  induct k; intros.
  - reflexivity.
  - simpl in *. f_equal.
    rewrite IHk. replace 1%Z with (0+1)%Z by lia.
    rewrite map_zrange'_shift_1.
    simpl. f_equal.
    apply functional_extensionality. intros. f_equal. lia.
Qed.

Lemma not_in_zrange' : forall a k' k,
    (k' < k)%Z ->
    ~ In k' (zrange' k a).
Proof.
  induct a; intros.
  - simpl. firstorder.
  - simpl. unfold not in *. intros.
    inversion H0. lia.
    eapply IHa. 2: eassumption. lia.
Qed.    

Lemma no_dup_zrange' : forall a k,
    no_dup (zrange' k a).
Proof.
  induct a.
  - constructor.
  - intros. simpl. constructor. eauto.
    eapply not_in_zrange'. lia.
Qed.

Lemma in_zrange'_lower_bound : forall a k' k,
    In k' (zrange' k a) ->
    (k <= k')%Z.
Proof.
  induct a; intros.
  - simpl in *. firstorder.
  - simpl in *. invert H. lia.
    eapply IHa in H0. lia.
Qed.

Lemma in_zrange'_upper_bound : forall a k' k,
    In k' (zrange' k a) ->
    (k' < k + (Z.of_nat a))%Z.
Proof.
  induct a; intros.
  - simpl in *. firstorder.
  - simpl in *. invert H. lia.
    eapply IHa in H0. lia.
Qed.    

Lemma in_zrange' : forall a k x,
    (k <= x < k + (Z.of_nat a))%Z ->
    In x (zrange' k a).
Proof.
  induct a; intros.
  - simpl in *. lia.
  - simpl in *.
    assert (k = x \/ k <> x) by lia. propositional.
    right. eapply IHa.
    lia.
Qed.

Lemma succ_zrange'_app_end : forall n k,
    zrange' k (Datatypes.S n) = (zrange' k n ++ [(Z.of_nat n + k)%Z])%list.
Proof.
  induct n; intros.
  - reflexivity.
  - simpl zrange' in *.
    rewrite IHn.
    rewrite app_comm_cons. f_equal.
    f_equal. lia.
Qed.

Lemma succ_nat_range_rec_app_end : forall n k,
    nat_range_rec (Datatypes.S n) k = ((nat_range_rec n k) ++  [n+k])%list.
Proof.
  induct n; intros.
  - reflexivity.
  - simpl in *. f_equal.
    rewrite IHn. f_equal. f_equal. lia.
Qed.

Lemma map_nat_range_rec_extensionality {X} : forall n k (f g : nat -> X),
    (forall x, k <= x < n + k-> f x = g x) ->
    map f (nat_range_rec n k) = map g (nat_range_rec n k).
Proof.
  induct n; intros.
  - reflexivity.
  - simpl. f_equal. eapply H. lia.
    eapply IHn. intros. eapply H. lia.
Qed.

Lemma map_nat_range_extensionality {X} : forall n (f g : nat -> X),
    (forall x, 0 <= x < n -> f x = g x) ->
    map f (nat_range n) = map g (nat_range n).
Proof.
  intros. eapply map_nat_range_rec_extensionality. intros.
  eapply H. lia.
Qed.

Lemma length_zrange' : forall a k,
    length (zrange' k a) = a.
Proof.
  induct a; intros.
  - reflexivity.
  - simpl. rewrite IHa. auto.
Qed.

Lemma length_nat_range_rec : forall n k,
    length (nat_range_rec n k) = n.
Proof.
  induct n; intros.
  - reflexivity.
  - simpl. rewrite IHn. lia.
Qed.

Lemma no_dup_map2_cons_concat : forall a l,
    no_dup l ->
    no_dup
      (map2 cons
            (concat
               (map (fun k : Z => repeat k (Datatypes.length l))
                    (zrange' 0 a))) (concat (repeat l a))).
Proof.
  induct a; intros.
  - simpl in *. econstructor.
  - rewrite succ_zrange'_app_end.
    rewrite succ_repeat_app_end.
    rewrite map_app. rewrite Z.add_0_r.
    repeat rewrite concat_app.
    rewrite map2_app.
    2: { erewrite length_concat.
         erewrite length_concat.
         rewrite repeat_length.
         rewrite map_length.
         rewrite length_zrange'. reflexivity.
         eapply Forall_repeat. reflexivity.
         eapply Forall_map.
         eapply Forall_forall. intros.
         rewrite repeat_length. reflexivity. }
    eapply no_dup_app.
    auto. simpl. repeat rewrite app_nil_r.
    eapply no_dup_map2_cons_l2. auto.
    simpl. repeat rewrite app_nil_r.
    rewrite map2_cons_repeat by reflexivity.
    eapply Forall_map.
    eapply Forall_impl with (P:= fun x => True). intros.
    unfold not. intros.
    eapply not_In_cons_l1 in H1.
    eapply in_concat in H1. invert H1. invert H2.
    eapply in_map_iff in H1. invert H1.
    invert H2.
    eapply repeat_spec in H3. subst.
    eapply in_zrange'_upper_bound in H4. lia.
    eapply Forall_forall. propositional.
Qed.

Lemma range_nat_range_rec : forall k n x,
  In x (nat_range_rec k n) ->
  n <= x < n + k.
Proof.
  induct k; intros.
  - simpl in *. propositional.
  - simpl in *. propositional.
    + lia.
    + subst. lia.
    + eapply IHk in H0. lia.
    + eapply IHk in H0. lia.
Qed.

Lemma zrange'_nat_range_rec : forall n k,
    (0 <= k)%Z ->
    zrange' k n  = map Z.of_nat (nat_range_rec n (Z.to_nat k)).
Proof.
  induct n; intros.
  - reflexivity.
  - simpl. f_equal. lia.
    replace (Z.to_nat k + 1) with (Z.to_nat (k+1))%Z by lia.
    eapply IHn. lia.
Qed.

Lemma zrange'_app : forall n m k,
    (zrange' k n ++ zrange' (k+Z.of_nat n) m)%list =
      zrange' k (n + m).
Proof.
  induct n; intros.
  - simpl. rewrite Z.add_0_r. reflexivity.
  - simpl. f_equal. rewrite <- IHn.
    f_equal. f_equal. lia.
Qed.

Lemma eq_zrange'_nat_range_rec : forall x y,
    x = y ->
    zrange' 0 x = map Z.of_nat (nat_range_rec y 0).
Proof.
  induct x; propositional; subst.
  - reflexivity.
  - rewrite succ_zrange'_app_end.
    rewrite succ_nat_range_rec_app_end. rewrite add_0_r.
    rewrite Z.add_0_r.
    rewrite IHx. rewrite map_app. simpl. reflexivity.
Qed.

Lemma eq_zrange_nat_range : forall x y,
  x = y ->
  zrange 0 x = map Z.of_nat (nat_range (Z.to_nat y)).
Proof.
  unfold zrange. unfold nat_range. intros.
  rewrite Z.sub_0_r.
  eapply eq_zrange'_nat_range_rec. lia.
Qed.

Lemma In_zrange' : forall n x k,
    In x (zrange' k n) <->
    (k <= x < Z.of_nat n + k)%Z.
Proof.
  induct n; intros; split; intros.
  - invert H.
  - simpl in *. lia.
  - simpl in *|-. invert H.
    + lia.
    + eapply IHn in H0. lia.
  - rewrite succ_zrange'_app_end.
    eapply in_or_app. simpl.
    assert ((Z.of_nat n + k)%Z = x \/ (Z.of_nat n + k)%Z <> x)%Z by lia.
    invert H0.
    + propositional.
    + left. eapply IHn. lia.
Qed.

Lemma In_zrange : forall x n,
    In x (zrange 0 n) <->
    (0 <= x < n)%Z.
Proof.
  unfold zrange. intros. rewrite Z.sub_0_r in *.
  split; intros.
  eapply In_zrange' in H. lia.
  eapply In_zrange'. lia.
Qed.

Lemma In_nat_range_rec :
  forall n k x,
    In x (nat_range_rec n k) <->
      k <= x < n + k.
Proof.
  induct n; intros; split; intros.
  - invert H.
  - lia.
  - rewrite succ_nat_range_rec_app_end in *.
    eapply in_app_or in H.
    simpl in *. invert H.
    + eapply IHn in H0. lia.
    + invert H0. 2: contradiction.
      lia.
  - rewrite succ_nat_range_rec_app_end in *.
    eapply in_or_app. simpl.
    assert (n + k = x \/ n + k <> x) by lia. invert H0.
    + propositional.
    + left. eapply IHn. lia.
Qed.
  
Lemma In_nat_range :
  forall k x,
    In x (nat_range k) <->
      x < k.
Proof.
  unfold nat_range.
  intros. split; intros.
  eapply In_nat_range_rec in H. lia.
  eapply In_nat_range_rec. lia.
Qed.  

Lemma map_nat_range_rec_shift {X} : forall n k (f : nat -> X),
    map f (nat_range_rec n k) =
      map (fun x => f (x+k)) (nat_range n).
Proof.
  induct n; intros.
  - reflexivity.
  - simpl. f_equal. rewrite IHn. rewrite IHn.
    f_equal. eapply functional_extensionality. intros. f_equal. lia.
Qed.

Lemma skipn_rev_nat_range_rec : forall n k c,    
    skipn c (rev (nat_range_rec n k)) = rev (nat_range_rec (n-c) k).
Proof.
  induct n; intros.
  - simpl. rewrite skipn_nil. reflexivity.
  - cases c.
    + rewrite sub_0_r. reflexivity.
    + rewrite succ_nat_range_rec_app_end.
      rewrite rev_app_distr. simpl.
      eauto.
Qed.

Lemma firstn_nat_range_rec : forall n k c,
    firstn c (nat_range_rec n k) =
      nat_range_rec (min c n) k.
Proof.
  induct n; intros.
  - simpl. rewrite firstn_nil. rewrite min_0_r. reflexivity.
  - simpl. cases c.
    + simpl. rewrite min_0_l. reflexivity.
    + simpl. rewrite <- succ_min_distr.
      simpl. f_equal. eauto.
Qed.

Lemma skipn_nat_range_rec : forall n k c,
    skipn c (nat_range_rec n k) =
      nat_range_rec (n-c) (k+c).
Proof.
  induct n; intros.
  - simpl. rewrite skipn_nil. reflexivity.
  - simpl. cases c.
    + simpl. rewrite add_0_r. reflexivity.
    + simpl. rewrite IHn. f_equal. lia.
Qed.

Lemma skipn_nat_range : forall n c,
    skipn c (nat_range n) =
      nat_range_rec (n-c) c.
Proof.
  unfold nat_range. intros. rewrite skipn_nat_range_rec. reflexivity.
Qed.

Lemma firstn_nat_range : forall n c,
    firstn c (nat_range n) =
      nat_range (min c n).
Proof.
  unfold nat_range. intros. rewrite firstn_nat_range_rec. reflexivity.
Qed.

Lemma firstn_add {X} : forall a b (l : list X),
    firstn (a+b) l = (firstn a l ++ (firstn b (skipn a l)))%list.
Proof.
  induct a; intros.
  - simpl. reflexivity.
  - cases l. simpl. rewrite firstn_nil. reflexivity.
    simpl. f_equal.
    eauto.
Qed.

Lemma firstn_rev_nat_range_rec : forall n k c,
    firstn k (rev (nat_range_rec n c)) =
      rev (nat_range_rec (min k n) (c+(n-k))).
Proof.
  induct n; intros.
  - simpl. rewrite min_0_r. rewrite firstn_nil. reflexivity.
  - cases k. rewrite min_0_l. reflexivity.
    rewrite <- succ_min_distr. simpl sub.
    rewrite succ_nat_range_rec_app_end.
    rewrite rev_app_distr. simpl firstn at 1.
    rewrite succ_nat_range_rec_app_end.
    rewrite rev_app_distr. simpl rev at 2. simpl app at 1.
    assert (k <= n \/ n < k) by lia. invert H.
    + rewrite min_l by lia. f_equal. lia.
      rewrite IHn. rewrite min_l by lia. reflexivity.
    + rewrite min_r by lia. replace (n - k) with 0 by lia.
      f_equal. lia. rewrite add_0_r.
      rewrite IHn. rewrite min_r by lia. f_equal. f_equal. lia.
Qed.

Lemma nth_error_nat_range_rec : forall n k x,
    x < n ->
    nth_error (nat_range_rec n k) x = Some (k+x).
Proof.
  induct n; intros.
  - lia.
  - simpl. cases x. simpl. f_equal. lia.
    simpl. rewrite IHn by lia. f_equal. lia.
Qed.

