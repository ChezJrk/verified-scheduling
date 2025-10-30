From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import ZArith.Zdiv.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import Logic.FunctionalExtensionality.

Set Warnings "-deprecate-hint-without-locality,-deprecated".
Import ListNotations.

From ATL Require Import FrapWithoutSets Div Tactics.
From Lower Require Import Array ListMisc Constant Range Result Zexpr.

(* Generates all possible multidimensional indices into shape sh *)
Fixpoint mesh_grid sh : list (list Z) :=
  match sh with
  | [] => [[]]
  | x::xs => let rest := mesh_grid xs in
             let new_range := concat
                                (map (fun k => repeat k (length rest))
                                     (zrange 0%Z x)) in             
             map2 List.cons new_range (concat (repeat rest (Z.to_nat x)))
  end.

Lemma no_dup_mesh_grid : forall sh,
    no_dup (mesh_grid sh).
Proof.
  induct sh.
  - simpl. constructor. constructor. firstorder.
  - simpl. unfold zrange. rewrite Z.sub_0_r.
    eapply no_dup_map2_cons_concat. auto.
Qed.

Lemma not_In_empty_mesh_grid : forall r0,
    ~ In [] (mesh_grid (result_shape_Z (V r0))).
Proof.
  unfold result_shape_Z.
  simpl. intros. cases r0.
  - propositional.
  - propositional.
    simpl in *. eapply not_In_empty_map2_cons. eassumption.
Qed.

Lemma mesh_grid_nonneg : forall sh x xs,
    In (x::xs) (mesh_grid sh) ->
    (0 <= x)%Z.
Proof.
  induct sh; propositional.
  - simpl in *. firstorder. discriminate.
  - simpl in *. eapply not_In_cons_l1 in H.
    eapply in_concat in H. firstorder.
    eapply in_map_iff in H. firstorder. subst.
    eapply repeat_spec in H0. subst.
    unfold zrange in *.
    eapply in_zrange'_lower_bound in H1.
    lia.
Qed.

Lemma in_mesh_grid_cons :
  forall k x,
    (0 <= x < Z.of_nat k)%Z ->
    forall x0 xs,
      (In x0 (mesh_grid xs) <->
      In (x::x0) (mesh_grid (Z.of_nat k::xs))).
Proof.
  simpl.
  induct k; intros; propositional.
  - lia.
  - lia.
  - unfold zrange. rewrite Z.sub_0_r.
    rewrite Nat2Z.id.
    rewrite succ_zrange'_app_end. rewrite Z.add_0_r.
    rewrite map_app. rewrite concat_app.
    rewrite succ_repeat_app_end.
    rewrite concat_app.
    rewrite map2_app.
    2:{ erewrite length_concat. rewrite length_map.
        rewrite length_zrange'.
        all: cycle 1.
        eapply Forall_map.
        eapply Forall_forall. intros.
        rewrite repeat_length. reflexivity.
        erewrite length_concat. rewrite repeat_length.
        reflexivity. eapply Forall_repeat. reflexivity. }
    eapply in_or_app.
    assert (x = Z.of_nat k \/ x < Z.of_nat k)%Z by lia. invert H2.
    + right. simpl. rewrite app_nil_r.
      rewrite map2_cons_repeat. rewrite app_nil_r.
      eapply in_map. auto.
      rewrite app_nil_r. reflexivity.
    + left. unfold zrange in IHk. rewrite Z.sub_0_r in IHk.
      rewrite Nat2Z.id in IHk.
      eapply IHk. lia. auto.
  - unfold zrange in *. rewrite Z.sub_0_r in *.
    rewrite Nat2Z.id in *.
    rewrite succ_zrange'_app_end in H. rewrite Z.add_0_r in H.
    rewrite map_app in H. rewrite concat_app in H.
    rewrite succ_repeat_app_end in H.
    rewrite concat_app in H.
    rewrite map2_app in H.
    2:{ erewrite length_concat. rewrite length_map.
        rewrite length_zrange'.
        all: cycle 1.
        eapply Forall_map.
        eapply Forall_forall. intros.
        rewrite repeat_length. reflexivity.
        erewrite length_concat. rewrite repeat_length.
        reflexivity. eapply Forall_repeat. reflexivity. }
    eapply in_app_or in H. 
    assert (x = Z.of_nat k \/ x < Z.of_nat k)%Z by lia. invert H2; invert H.
    + eapply not_In_cons_l1 in H2.
      eapply in_concat in H2.
      firstorder. 
      eapply in_map_iff in H.
      firstorder. subst.
      eapply repeat_spec in H2. subst.
      eapply in_zrange'_upper_bound in H3. lia.
    + simpl in *. repeat rewrite app_nil_r in *.
      rewrite map2_cons_repeat in H2 by reflexivity.
      eapply in_map_iff in H2.
      firstorder. invert H. auto.
    + eapply IHk;try eassumption. lia.
    + eapply not_In_cons_l2 in H2.
      eapply in_concat in H2.      
      firstorder. subst. auto.
Qed.

Lemma in_mesh_grid_cons_ :
  forall k x x0 xs,
    (0 <= x < Z.of_nat k)%Z /\
      In x0 (mesh_grid xs) <->
      In (x::x0) (mesh_grid (Z.of_nat k::xs)).
Proof.
  induct k; propositional.  
  - lia.
  - simpl in *. propositional.
  - simpl in *. propositional.
  - simpl in *. propositional.
  - simpl in *. posnats.
    rewrite succ_repeat_app_end.
    rewrite concat_app. simpl. rewrite app_nil_r. posnats.
    unfold zrange. rewrite Z.sub_0_r. rewrite Nat2Z.id.
    rewrite succ_zrange'_app_end. rewrite Z.add_0_r.
    rewrite map_app. rewrite concat_app.
    unfold zrange in IHk.
    rewrite Z.sub_0_r in IHk. setoid_rewrite Nat2Z.id in IHk.
    rewrite map2_app.
    2: { erewrite length_concat.
         rewrite length_map. rewrite length_zrange'.
         erewrite length_concat. rewrite repeat_length.
         reflexivity.
         eapply Forall_repeat. reflexivity.
         eapply Forall_map.
         eapply Forall_forall. intros. rewrite repeat_length.
         reflexivity. }
    eapply in_or_app.
    assert (x = Z.of_nat k \/ x < Z.of_nat k)%Z by lia. invert H0.
    right. simpl. rewrite app_nil_r.
    rewrite map2_cons_repeat.
    eapply In_cons_map_cons. propositional. reflexivity.
    left. eapply IHk. propositional.
  - eapply mesh_grid_nonneg. eassumption.
  - simpl in H.
    eapply not_In_cons_l1 in H.
    eapply in_concat in H. firstorder.
    eapply in_map_iff in H. firstorder. subst. 
    eapply repeat_spec in H0. subst.
    unfold zrange in H1.
    eapply in_zrange'_upper_bound in H1. lia.
  - simpl. simpl in H.
    eapply not_In_cons_l2 in H.
    eapply in_concat in H. firstorder.
    eapply repeat_spec in H. subst.
    auto.
Qed.

Lemma in_mesh_grid_cons__ :
  forall k x x0 xs,
    (0 <= x < k)%Z /\
      In x0 (mesh_grid xs) <->
      In (x::x0) (mesh_grid (k::xs)).
Proof.
  intros. cases k.
  - simpl. propositional. lia.
  - replace (Z.pos p) with (Z.of_nat (Z.to_nat (Z.pos p))) by lia.
    eapply in_mesh_grid_cons_.
  - simpl. propositional. lia.
Qed.

Lemma in_cons_mesh_grid_result_shape_Z_cons : forall l r r0 x0 x,
  result_has_shape (V (r :: r0)) l ->
  In x0 (mesh_grid (result_shape_Z r)) ->
  (0 <= x < Z.of_nat (length (r::r0)))%Z ->
  In (x :: x0) (mesh_grid (result_shape_Z (V (r :: r0)))).
Proof.
  intros. invert H.
  pose proof in_mesh_grid_cons. simpl in *.
  posnats. setoid_rewrite Nat2Z.id in H.
  eapply H. lia. unfold result_shape_Z in H0. auto.
Qed.

Lemma in_mesh_grid_result_shape_Z_cons : forall r r0 l z x0,
  result_has_shape (V (r :: r0)) l ->
  In (z :: x0) (mesh_grid (result_shape_Z (V r0))) ->
  In ((z + 1)%Z :: x0) (mesh_grid (result_shape_Z (V (r :: r0)))).
Proof.
  intros. invert H.
  pose proof in_mesh_grid_cons. simpl in *.
  unfold result_shape_Z in H0. simpl in H0.
  cases r0; simpl in *. propositional.
  posnats. setoid_rewrite Nat2Z.id in H.
  eapply H; clear H.
  - eapply not_In_cons_l1 in H0.
    eapply in_concat in H0. firstorder. 
    eapply in_map_iff in H. firstorder. subst.
    eapply repeat_spec in H0. subst.
    unfold zrange in H1.
    pose proof (in_zrange'_lower_bound _ _ _ H1).
    simpl in *. lia. 
    eapply in_map_iff in H. firstorder. subst.
    eapply repeat_spec in H0. subst.
    pose proof (in_zrange'_upper_bound _ _ _ H1).
    lia.
  - eapply not_In_cons_l2 in H0.
    eapply in_concat in H0. firstorder. subst. invert H6.
    eapply result_has_shape_result_shape_nat in H4. rewrite H4.
    eapply result_has_shape_result_shape_nat in H2. rewrite H2 in *. auto.
    eapply repeat_spec in H. subst.
    eapply result_has_shape_result_shape_nat in H4. 
    invert H6. eapply result_has_shape_result_shape_nat in H2.
    rewrite H2 in *.
    rewrite H4 in *. auto.
Qed.

Lemma length_mesh_grid_indices :
  forall l idx,
    In idx (mesh_grid (map Z.of_nat l)) ->
    length l = length idx.
Proof.
  induct l; intros.
  - simpl in H. propositional. subst. reflexivity.
  - simpl map in *.
    cases idx.
    simpl in H. eapply not_In_empty_map2_cons in H. propositional.
    eapply in_mesh_grid_cons_ in H. firstorder.
    simpl. f_equal. eauto.
Qed.

Lemma length_mesh_grid_indices_Z :
  forall l idx,
    In idx (mesh_grid l) ->
    length l = length idx.
Proof.
  induct l; intros.
  - simpl in H. propositional. subst. reflexivity.
  - simpl map in *.
    cases idx.
    simpl in H. eapply not_In_empty_map2_cons in H. propositional.
    eapply in_mesh_grid_cons__ in H. firstorder.
    simpl. f_equal. eauto.
Qed.

Lemma empty_not_in_mesh_grid : forall r0,
    ~ In [] (mesh_grid (result_shape_Z (V r0))).
Proof.
  unfold result_shape_Z. simpl. unfold not.
  intros. cases r0. invert H.
  simpl in *.
  eapply not_In_empty_map2_cons. eassumption.
Qed.

Lemma result_lookup_Z_gen_pad : forall l x,
    In x (mesh_grid (map Z.of_nat l)) ->
    result_lookup_Z x (gen_pad l) = SX.
Proof.
  induct l; intros.
  - simpl in *. propositional. invert H0. reflexivity.
  - cases x. simpl in *. eapply not_In_empty_map2_cons in H.
    propositional.
    simpl. pose proof H. simpl map in H.
    eapply in_mesh_grid_cons_ in H. propositional.
    rewrite nth_error_repeat by lia. eauto.
    cases z; eauto.
    lia.
Qed.

Lemma length_mesh_grid : forall sh,
    (Forall (fun x => 0 < x)%Z sh) ->
    length (mesh_grid sh) = Z.to_nat (fold_left Z.mul sh 1%Z).
Proof.
  induct sh; intros.
  - simpl. lia.
  - invert H. simpl.
    rewrite length_map2.
    erewrite length_concat.
    2: { eapply Forall_map. eapply Forall_forall. intros.
         rewrite repeat_length. reflexivity. }
    rewrite length_map. unfold zrange.
    rewrite length_zrange'.
    rewrite Z.sub_0_r.
    erewrite length_concat.
    2: { eapply Forall_repeat. reflexivity. }
    rewrite repeat_length. rewrite min_id.
    rewrite fold_left_mul_assoc. rewrite IHsh. lia. auto.
Qed.    

Lemma mesh_grid_shape_pos : forall sh args,
  In args (mesh_grid sh) ->
  Forall (fun z2 : Z => (0 < z2)%Z) sh.
Proof.
  induct sh; intros.
  - auto.
  - cases args. eapply not_In_empty_map2_cons in H. propositional.
    eapply in_mesh_grid_cons__ in H. invert H.
    econstructor. lia.
    eauto.
Qed.

Lemma mesh_grid_shape_nonneg : forall sh args,
  In args (mesh_grid sh) ->
  Forall (fun z2 : Z => (0 <= z2)%Z) sh.
Proof.
  induct sh; intros.
  - auto.
  - cases args. eapply not_In_empty_map2_cons in H. propositional.
    eapply in_mesh_grid_cons__ in H. invert H.
    econstructor. lia.
    eauto.
Qed.

Lemma flatten_sh_nonneg : forall sh args,
    In args (mesh_grid sh) ->
    (0 <= flatten sh args)%Z.
Proof.
  induct sh; intros.
  - simpl in *. propositional. subst. simpl. lia.
  - cases args. eapply not_In_empty_map2_cons in H. propositional.
    eapply in_mesh_grid_cons__ in H. invert H.
    cases sh. simpl in *. propositional. subst. simpl. lia.
    cases args. eapply not_In_empty_map2_cons in H1. propositional.
    eapply in_mesh_grid_cons__ in H1. invert H1.
    simpl.
    eapply Z.add_nonneg_nonneg.
    + eapply Z.mul_nonneg_nonneg. lia.
      eapply fold_left_mul_nonneg.
      eapply mesh_grid_shape_nonneg. eassumption. lia.
    + eapply IHsh.
      erewrite <- in_mesh_grid_cons__. auto.
Qed.

Lemma flatten_cons_cons : forall x xs y ys z z0,
  (y * fold_left Z.mul xs z + flatten (z :: xs) (z0 :: ys))%Z =
    flatten (x :: z :: xs) (y :: z0 :: ys).
Proof.
  reflexivity.
Qed.

Lemma in_range_in_flatten : forall sh x,
  (0 <= x)%Z ->
  (x < fold_left Z.mul sh 1)%Z ->
  (Forall (fun x => 0 <= x)%Z sh) ->
  In x (map (flatten sh) (mesh_grid sh)).
Proof.
  induct sh; intros.
  - simpl in *. lia.
  - simpl in * |-. rewrite fold_left_mul_assoc in *.
    pose proof (Z_div_mod x (fold_left Z.mul sh 1%Z)).
    assert (fold_left Z.mul sh 1 > 0)%Z.    
    invert H1. lia.
    eapply H2 in H3. clear H2.
    destruct (Z.div_eucl x (fold_left Z.mul sh 1%Z)) eqn:ee.
    invert H3.
    specialize (IHsh z0).
    propositional. invert H1. propositional.
    eapply in_map_iff in H1.
    invert H1. invert H4.
    rewrite Z.mul_comm.
    cases sh.
    + simpl in *. propositional. subst.
      rewrite <- repeat_to_concat.
      rewrite map_map2.
      unfold flatten in *. rewrite Z.add_0_r.
      rewrite map2_repeat2.
      rewrite map_id.
      eapply in_concat. eexists [z]. split.
      eapply in_map with (f:= fun x => [x]).
      unfold zrange.
      eapply in_zrange'. lia.
      rewrite Z.mul_1_r.
      simpl. propositional.
      erewrite length_concat.
      2: { eapply Forall_map. simpl. eapply Forall_forall. intros.
           reflexivity. }
      rewrite length_map. unfold zrange.
      rewrite length_zrange'. lia.
    + cases x. eapply not_In_empty_map2_cons in H5. propositional.
      replace (z * fold_left Z.mul (z0 :: sh) 1)%Z with
        (z * fold_left Z.mul (sh) z0)%Z.
      2: { simpl. f_equal. f_equal. lia. }
      erewrite flatten_cons_cons with (x:=a).
      assert (a = 0 \/ 0 < a)%Z by lia. invert H1.
      { simpl in *. rewrite Z.mul_0_r in *. lia. }
      eapply in_map_iff. eexists.
      split. reflexivity.
      erewrite <- in_mesh_grid_cons__. split; auto.
      assert (0 <= z)%Z.
      eapply div_eucl_pos. 3: apply H.
      eapply mesh_grid_shape_pos in H5.
      eapply fold_left_mul_pos. auto. lia.
      auto. 
      propositional.
      eapply div_eucl_bound in H0. auto. auto.
      auto.
Qed.

(* Lemma in_mesh_grid_flatten_in_range_nat *)

Lemma in_mesh_grid_flatten_in_range : forall sh x0,
    (Forall (fun x => 0 <= x)%Z sh) ->
    In x0 (mesh_grid sh) ->
    In (flatten sh x0) (zrange 0 (fold_left Z.mul sh 1%Z)).
Proof.
  induct sh; intros.
  - simpl in *. propositional. subst. simpl. propositional.
  - cases x0.
    eapply not_In_empty_map2_cons in H0. propositional.
    cases sh.
    + pose proof H0.
      eapply not_In_cons_l2 in H0.
      rewrite <- repeat_to_concat in H0.
      eapply repeat_spec in H0. subst.
      eapply in_mesh_grid_cons__ in H1. invs.
      simpl.
      unfold zrange.
      eapply in_zrange'.
      lia.
    + eapply in_mesh_grid_cons__ in H0. invs.
      cases x0.
      eapply not_In_empty_map2_cons in H2. propositional.
      pose proof H2.
      eapply in_mesh_grid_cons__ in H2. invs.
      simpl.
      rewrite Z.mul_1_l.
      rewrite (Z.mul_comm a).
      rewrite fold_left_mul_assoc.
      eapply IHsh in H1.
      unfold zrange in H1.
      rewrite Z.sub_0_r in H1.
      simpl in H1.
      rewrite Z.mul_1_l in H1.
      pose proof (in_zrange'_lower_bound _ _ _ H1).
      pose proof (in_zrange'_upper_bound _ _ _ H1).
      eapply in_zrange'.
      rewrite Z.sub_0_r. rewrite Z.add_0_l.
      invert H. 
      rewrite Z2Nat.id.
      2: { eapply Z.mul_nonneg_nonneg.
           eapply fold_left_mul_nonneg. invert H11. auto.
           invert H11. auto. auto. }
      rewrite (Z.mul_comm _ a).
      split.
      * eapply Z.add_nonneg_nonneg.
        eapply Z.mul_nonneg_nonneg. auto.
        eapply fold_left_mul_nonneg.
        invert H11. auto. invert H11. auto.
        eapply flatten_sh_nonneg.
        erewrite <- in_mesh_grid_cons__.
        auto.
      * eapply mul_add_lt.
        auto. auto.
        eapply flatten_sh_nonneg.
        erewrite <- in_mesh_grid_cons__.
        auto.
        lia.
      * invert H. auto.
Qed.

Lemma constant_map_flatten_zrange : forall l,
  constant
    (map (flatten l) (mesh_grid l)) \subseteq
    constant (zrange 0 (fold_left Z.mul l 1%Z)).
Proof.
  induct l; intros.
  - simpl. unfold zrange. sets.
  - apply subseteq_In. intros.
    rewrite subseteq_In in IHl.
    eapply In_iff_in in H.
    eapply in_map_iff in H. invs.
    rewrite <- In_iff_in.
    cases x0. eapply not_In_empty_map2_cons in H1. propositional.
    eapply in_mesh_grid_flatten_in_range.
    eapply mesh_grid_shape_nonneg. eassumption.
    auto.
Qed.

Lemma in_mesh_grid_args_flatten_bounds : forall sh args1 z1,
  In args1 (mesh_grid (z1 :: sh)) ->
  (0 <= flatten (z1 :: sh) args1 < fold_left Z.mul sh z1)%Z \/
    (fold_left Z.mul sh z1 < flatten (z1 :: sh) args1 <= 0)%Z.
Proof.
  induct sh; intros.
  - simpl in *.
    cases args1. eapply not_In_empty_map2_cons in H. propositional.
    pose proof H.
    eapply not_In_cons_l2 in H.
    eapply not_In_cons_l1 in H0.
    rewrite <- repeat_to_concat in H.
    eapply repeat_spec in H. subst. simpl.
    unfold zrange in *.
    rewrite Z.sub_0_r in H0.
    eapply in_concat in H0.
    invs.
    eapply in_map_iff in H0. invs.
    invert H1.
    pose proof (in_zrange'_lower_bound _ _ _ H2).
    pose proof (in_zrange'_upper_bound _ _ _ H2).
    lia.
    simpl in *. propositional.
  - cases args1. simpl in *.
    eapply not_In_empty_map2_cons in H. propositional.
    simpl in *.
    pose proof (not_In_cons_l1 _ _ _ _ H).
    pose proof (not_In_cons_l2 _ _ _ _ H). clear H.
    pose proof IHsh.
    eapply in_concat in H1.
    invs.
    eapply repeat_spec in H1. subst.
    eapply H in H3. clear H. clear IHsh.
    eapply in_concat in H0.
    invs.
    eapply in_map_iff in H0. invs.
    eapply repeat_spec in H1. subst.
    unfold zrange in H2.
    pose proof (in_zrange'_lower_bound _ _ _ H2).
    pose proof (in_zrange'_upper_bound _ _ _ H2).
    clear H2.
    invert H3.
    + cases z1; try lia.
      left.
      rewrite (Z.mul_comm (Z.pos p)).
      rewrite fold_left_mul_assoc.
      assert (x0 < Z.pos p)%Z by lia. clear H0.
      split.
      eapply Z.add_nonneg_nonneg.
      eapply Z.mul_nonneg_nonneg. lia. lia. lia.
      rewrite (Z.mul_comm _ (Z.pos p)).
      eapply mul_add_lt.
      lia. lia. lia. lia.
    + cases z1; try lia.
      right.
      split.
      rewrite (Z.mul_comm (Z.pos p)).
      rewrite fold_left_mul_assoc.
      rewrite (Z.mul_comm _ (Z.pos p)).
      assert (forall x y, -x < -y -> y < x)%Z.
      intros. lia. eapply H2.
      rewrite Z.opp_add_distr.
      rewrite Zopp_mult_distr_r.
      rewrite Zopp_mult_distr_r.
      rewrite Z.add_opp_r.
      eapply mul_add_lt. lia. lia. lia. lia.
      assert (forall x y, -x <= -y -> y <= x)%Z.
      lia. eapply H2.
      simpl. rewrite Z.opp_add_distr.
      rewrite Zopp_mult_distr_r.
      assert (flatten (a::sh) args1 = 0 \/ flatten (a::sh) args1 <> 0)%Z
        by lia. invert H3.
      * rewrite H4.
        lia.
      * eapply auxiliary.Zle_mult_approx. lia. lia. lia.
Qed.

Lemma exists_0_empty_mesh_grid : forall l,
    Exists (fun x => x = 0)%Z l ->
    mesh_grid l = [].
Proof.
  induct l; intros.
  - invert H.
  - invert H.
    + reflexivity.
    + simpl. rewrite IHl by auto.
      rewrite concat_repeat_empty.
      simpl. rewrite map_constant_repeat.
      rewrite concat_repeat_empty.
      reflexivity.
Qed.      

Lemma mesh_grid_cons : forall x xs,
    mesh_grid (x::xs) =
      map2 cons (concat
                   (map (fun k => repeat k (length (mesh_grid xs)))
                        (zrange 0 x)))
           (concat (repeat (mesh_grid xs) (Z.to_nat x))).
Proof. reflexivity. Qed.

Lemma mesh_grid_app : forall n m xs,
    (0 <= m)%Z ->
    (0 <= n)%Z ->
    mesh_grid (n+m::xs)%Z = (mesh_grid (n::xs) ++
                                       (map
                                          (fun l => match l with
                                                    | i::is => (i+n::is)%Z
                                                    | _ => l
                                                    end)
                                          (mesh_grid (m::xs))))%list.
Proof.
  intros.
  rewrite mesh_grid_cons.
  rewrite (mesh_grid_cons n).
  rewrite (mesh_grid_cons m).
  rewrite map_map2.
  rewrite map2_f_l1 with (f:=fun a => (a+n)%Z).
  rewrite concat_map. rewrite map_map.
  replace 
    (fun x : Z =>
            map (fun a0 : Z => (a0 + n)%Z)
                (repeat x (Datatypes.length (mesh_grid xs)))) with
      (fun x : Z =>
         (repeat (x+n)%Z (Datatypes.length (mesh_grid xs)))) .
    2: { eapply functional_extensionality. intros.
         rewrite map_repeat. reflexivity. }
    rewrite <- map_map
      with (g:=(fun x => repeat x (length (mesh_grid xs))))
           (f:=fun x =>(x+n)%Z).
    unfold zrange. repeat rewrite Z.sub_0_r.
    rewrite <- map_zrange'_shift_lo with (f:=fun x=>x).
    rewrite Z2Nat.inj_add by lia.
    rewrite <- zrange'_app.
    rewrite Z2Nat.id by lia.
    rewrite repeat_app.
    rewrite Z.add_0_l. rewrite concat_app. rewrite map_app.
    rewrite concat_app.
    rewrite map2_app.
    all: cycle 1.
    erewrite length_concat.
    2: { eapply Forall_map. eapply Forall_forall. intros.
         rewrite repeat_length. reflexivity. }
    erewrite length_concat.
    2: { eapply Forall_forall. intros.
         eapply repeat_spec in H1. subst. reflexivity. }
    rewrite length_map. rewrite length_zrange'.
    rewrite repeat_length. lia.
    rewrite map_id. reflexivity.
Qed.    

Lemma result_lookup_Z_concat_l : forall x x1 xs r1 r2 x2,
    result_has_shape (V r1) (x1 :: xs) ->
    result_has_shape (V r2) (x2 :: xs) ->
    In x (mesh_grid (Z.of_nat x1 :: map Z.of_nat xs)) ->
    result_lookup_Z x (V r1) = result_lookup_Z x (V (r1 ++ r2)).
Proof.
  intros.
  cases x. eapply not_In_empty_map2_cons in H1. propositional.
  simpl.
  eapply in_mesh_grid_cons__ in H1. invs.
  rewrite nth_error_app1.
  2: erewrite result_has_shape_length; try eassumption; lia.
  reflexivity.
Qed.

Lemma result_lookup_Z_concat_r : forall x x1 xs r1 r2 x2,
    result_has_shape (V r1) (x1 :: xs) ->
    result_has_shape (V r2) (x2 :: xs) ->
    In x (mesh_grid (Z.of_nat x2 :: map Z.of_nat xs)) ->
    result_lookup_Z x (V r2) =
      result_lookup_Z match x with
                      | z::xs => ((z + Z.of_nat x1)%Z :: xs)
                      | _ => x
                      end (V (r1 ++ r2)).
Proof.
  intros.
  cases x. eapply not_In_empty_map2_cons in H1. propositional.
  simpl.
  eapply in_mesh_grid_cons__ in H1. invs.
  rewrite nth_error_app2.
  2: erewrite result_has_shape_length; try eassumption; lia.
  erewrite result_has_shape_length; try eassumption.
  replace (Z.to_nat (z + Z.of_nat x1)%Z - x1) with (Z.to_nat z) by lia.
  cases z; try lia.
  - simpl. cases (Z.of_nat x1); try lia.
    + cases r2; eauto.
    + eauto.
  - cases (Z.pos p + Z.of_nat x1)%Z; try lia.
    eauto.
Qed.

Lemma in_mesh_grid_cons_filter_until_0 : forall sh idx,
    In idx (mesh_grid (map Z.of_nat sh)) <->
    In idx (mesh_grid (map Z.of_nat (filter_until sh 0))).
Proof.
  induct sh; propositional.
  - simpl map in *.
    cases idx. eapply not_In_empty_map2_cons in H. propositional.
    eapply in_mesh_grid_cons__ in H. invs.
    cases (a =? 0)%nat. eapply Nat.eqb_eq in Heq. lia.
    simpl map.
    erewrite <- in_mesh_grid_cons__. propositional. eapply IHsh. auto.
  - simpl map in *.
    cases (a =? 0)%nat.
    eapply Nat.eqb_eq in Heq. subst. simpl in *. propositional.
    simpl map in *.
    cases idx. eapply not_In_empty_map2_cons in H. propositional.
    eapply in_mesh_grid_cons__ in H. invs.
    erewrite <- in_mesh_grid_cons__. propositional.
    eapply IHsh. auto.
Qed.

Ltac decomp_goal_index :=
  match goal with
  | |- In _ (mesh_grid (map Z.of_nat (filter_until ?sh 0))) =>
      erewrite <- in_mesh_grid_cons_filter_until_0; simpl map
  | |- In (?x::?xs) (mesh_grid (_::_)) =>
      erewrite <- in_mesh_grid_cons__
  end.

Ltac decomp_index :=
  match goal with
  | H : In (?idx::?idxs) (mesh_grid (?x::?xs)) |- _ =>
      eapply in_mesh_grid_cons__ in H; invert H
  | H : In [] (mesh_grid (?x::?xs)) |- _ =>
      eapply not_In_empty_map2_cons in H; contradiction
  | H : In ?idx (mesh_grid (?x::?xs)) |- _ =>
      cases idx
  | H : In _ (mesh_grid (map Z.of_nat (filter_until _ 0))) |- _ =>
      eapply in_mesh_grid_cons_filter_until_0 in H;
      simpl map in H
  | H : In _ (filter (fun x => negb _) _) |- _ =>
      eapply filter_In in H; invert H
  end.

Lemma constant_map_flatten_zrange_exists_0 : forall l,
    Exists (fun x => x = 0)%Z l ->
    constant
      (map (flatten l) (mesh_grid l)) =
      constant (zrange 0 (fold_left Z.mul l 1%Z)).
Proof.
  intros. erewrite exists_0_empty_mesh_grid by eassumption.
  simpl. erewrite fold_left_Zmul_exists_0 by eassumption.
  unfold zrange. reflexivity.
Qed.

Lemma constant_map_flatten_zrange_gt_0 : forall l,
    Forall (fun x => 0 < x)%Z l ->
    constant
      (map (flatten l) (mesh_grid l)) =
      constant (zrange 0 (fold_left Z.mul l 1%Z)).
Proof.
  intros. apply sets_equal.  
  induct l; intros; split; intros.
  - simpl in *. auto.
  - simpl in *. auto.
  - eapply In_iff_in in H0.
    eapply in_map_iff in H0. invs.
    eapply In_iff_in.
    rewrite <- In_iff_in.
    decomp_index. decomp_index.
    eapply in_mesh_grid_flatten_in_range.
    eapply mesh_grid_shape_nonneg. eassumption.
    auto.
  - eapply In_iff_in in H0.    
    eapply In_iff_in. erewrite <- In_iff_in.
    eapply in_map_iff.
    simpl zrange in *.
    rewrite fold_left_mul_assoc in H0.
    eapply In_zrange in H0.

    cases (Z.div_eucl x (fold_left Z.mul l 1%Z)).
    pose proof (Z_div_mod x (fold_left Z.mul l 1%Z)).
    assert (fold_left Z.mul l 1 > 0)%Z.
    { assert (0 < fold_left Z.mul l 1)%Z.
      eapply fold_left_mul_pos. invert H. auto. lia. lia. }
    propositional.
    rewrite Heq in *. invert H0.
    eapply In_zrange in H5.
    eapply IHl in H5.
    eapply In_iff_in in H5.
    eapply in_map_iff in H5. invert H5. invert H0.
    eexists (z::x).
    split. all: cycle 1.
    erewrite <- in_mesh_grid_cons__. split.
    assert (0 <= z)%Z.
    { pose proof (in_mesh_grid_flatten_in_range l x).
      assert (Forall (fun x : Z => (0 <= x)%Z) l).
      eapply Forall_impl.
      2: { invert H. eapply H8. }
      simpl. lia.
      propositional.
      eapply In_zrange in H0.
      eapply div_eucl_pos in H3. 2: lia. 2: lia. lia. }
    eapply div_eucl_bound in H4. lia. lia.
    pose proof (in_mesh_grid_flatten_in_range l x).
    assert (Forall (fun x : Z => (0 <= x)%Z) l).
    eapply Forall_impl.
    2: { invert H. eapply H9. }
    simpl. lia. apply H1 in H6. 
    eapply In_zrange in H6. auto.
    auto. invert H. auto.
    invert H. auto.
    cases l.
    + simpl in *. propositional. subst. simpl. lia.
    + decomp_index. decomp_index. simpl.
      rewrite Z.mul_1_l. lia.
Qed.

Lemma constant_map_flatten_zrange_nonneg : forall l,
    Forall (fun x => 0 <= x)%Z l ->
    constant
      (map (flatten l) (mesh_grid l)) =
      constant (zrange 0 (fold_left Z.mul l 1%Z)).
Proof.
  intros.
  eapply forall_nonneg_exists_zero_or_forall_pos_Z in H.
  invert H.
  - eapply constant_map_flatten_zrange_gt_0. eauto.
  - eapply constant_map_flatten_zrange_exists_0. eauto.
Qed.

Lemma not_in_mesh_grid_or : forall a args2 z sh,
    ~ In (a :: args2) (mesh_grid (z :: sh)) ->
    ~ (0 <= a < z)%Z \/ ~ In args2 (mesh_grid sh).
Proof.
  intros.
  setoid_rewrite <- in_mesh_grid_cons__ in H.
  eapply Classical_Prop.not_and_or in H. propositional.
Qed.

Fixpoint all_args_in_bounds evaled_index_list :=
  match evaled_index_list with
  | Some (val,limit)::xs => andb (andb (0 <=? val)%Z (val <? limit)%Z)
                                 (all_args_in_bounds xs)
  | [] => true
  | _ => false
  end.

Lemma in_mesh_grid_all_args_in_bounds : forall args2 sh,
  In args2 (mesh_grid sh) ->
  all_args_in_bounds (map Some (combine args2 sh)) = true.
Proof.
  induct args2; intros.
  - simpl. auto.
  - cases sh. simpl in H. propositional.
    decomp_index. simpl.
    replace (0 <=? a)%Z with true.
    2: { symmetry. eapply Z.leb_le. lia. }
    replace (a <? z)%Z with true.
    2: { symmetry. eapply Z.ltb_lt. lia. }
    simpl. eauto.
Qed.

Lemma not_in_mesh_grid_all_args_in_bounds : forall args2 sh,
    ~ In args2 (mesh_grid sh) ->
    length args2 = length sh ->
    all_args_in_bounds (map Some (combine args2 sh)) = false.
Proof.
  induct args2; intros; cases sh; simpl length in *; try lia.
  - simpl in *. propositional.
  - unfold not in *. simpl.
    eapply not_in_mesh_grid_or in H. invert H.
    + propositional.
      cases ((0 <=? a)%Z && (a <? z)%Z). simpl.
      eapply andb_prop in Heq. invs.
      eapply Z.ltb_lt in H2. eapply Z.leb_le in H1. propositional.
      reflexivity.
    + rewrite IHargs2; eauto. rewrite andb_false_r. reflexivity.
Qed.    
  
Lemma mesh_grid_filter_until :
  forall sh,
    mesh_grid (map Z.of_nat (filter_until sh 0)) =
      mesh_grid (map Z.of_nat sh).
Proof.
  intros. pose proof (list_nat_nonneg sh).
  invert H.
  erewrite exists_0_empty_mesh_grid.
  2: { eapply exists_0_map_of_nat. 
       eapply exists_0_filter_until_0.
       eauto. }
  erewrite exists_0_empty_mesh_grid.
  2: { eapply exists_0_map_of_nat. 
       eauto. }
  reflexivity.
  erewrite filter_until_0_id by auto. reflexivity.
Qed.

Lemma mesh_grid_map_Nat2Z_id : forall sh,
    mesh_grid (map Z.of_nat (map Z.to_nat sh)) = mesh_grid sh.
Proof.
  induct sh; intros.
  - simpl. reflexivity.
  - simpl map.
    cases a.
    + reflexivity.
    + posnats.
      rewrite Z2Nat.id by lia.
      simpl. rewrite IHsh. reflexivity.
    + reflexivity.
Qed.

Definition is_None {X} (x : option X) :=
  match x with
  | None => true
  | _ => false
  end.

Lemma filter_pad_r_empty : forall k l0 x,
    (0 <= k) ->
    filter
      (fun x1 : list Z =>
         negb
           (is_None
              (result_lookup_Z_option
                 x1
                 (V (x ++ gen_pad_list (k :: l0))))))
      (map
         (fun l : list Z =>
            match l with
            | [] => l
            | i :: is => (i + Z.of_nat (length x))%Z :: is
            end)
         (mesh_grid
            (Z.of_nat k
               :: map Z.of_nat
               (filter_until l0 0)))) = [].
Proof.
  intros.
  eapply filter_empty.
  eapply Forall_forall. intros.
  eapply in_map_iff in H0. invs.
  repeat decomp_index.
  eapply negb_false_iff.
  unfold is_None.
  simpl.
  rewrite nth_error_app2.
  2: lia.
  rewrite nth_error_repeat by lia.
  rewrite result_lookup_Z_option_gen_pad.
  cases (z + Z.of_nat (Datatypes.length x))%Z; try lia.
Qed.

Lemma filter_pad_r_mesh_grid : forall m x l0 k,
    result_has_shape (V (gen_pad_list (k :: l0) ++ x)) (m :: l0) ->
    (0 <= k) ->
    filter
          (fun x1 : list Z =>
           negb
             (is_None
                (result_lookup_Z_option x1
                   (V
                      (x ++
                         gen_pad_list (k :: l0))))))
      (mesh_grid
         (map Z.of_nat
              (filter_until
                 (m :: l0) 0))) =
        (filter (fun x0 => negb (is_None (result_lookup_Z_option x0 (V x))))
                (mesh_grid
                   (map Z.of_nat
                        (filter_until (m - k :: l0) 0)))).
Proof.
  intros.
  simpl in H.
  repeat rewrite map_cons.

  pose proof (result_has_shape_length _ _ _ H).
  rewrite length_app in H1.
  rewrite repeat_length in H1.

  cases m.
  - reflexivity.
  - rewrite filter_until_0_cons by lia.
    rewrite <- H1.
    replace (k + length x - k) with (length x) by lia.
    rewrite map_cons at 1.
    rewrite Nat2Z.inj_add by lia.
    rewrite Z.add_comm.
    rewrite mesh_grid_app by lia.
    rewrite filter_app.
    (* replace m with *)
    (*   (k + m - k) *)
    (*   by lia. *)
    rewrite filter_pad_r_empty.
    simpl map. cases x. simpl. auto. simpl map. simpl length. posnats.
    rewrite app_nil_r.
    eapply filter_ext_in.
    2: lia. intros.
    repeat decomp_index.
    f_equal. f_equal.
    simpl.
    rewrite app_comm_cons.
    rewrite nth_error_app1.
    auto. simpl in *. lia.
Qed.

Lemma filter_pad_l_empty : forall k l0 x,
    filter
      (fun x0 =>
         negb
           (is_None
              (result_lookup_Z_option
                 x0
                 (V
                    (gen_pad_list
                       (k :: l0) ++
                       x)))))
      (mesh_grid
         (Z.of_nat k
                   :: map Z.of_nat
                   (filter_until
                      l0 0))) = [].
Proof.
  intros.
  eapply filter_empty.
  eapply Forall_forall. intros.
  repeat decomp_index.
  eapply negb_false_iff.
  unfold is_None.
  simpl.
  rewrite nth_error_app1.
  2: rewrite repeat_length; lia.
  rewrite nth_error_repeat by lia.
  rewrite result_lookup_Z_option_gen_pad.
  cases z; auto.
Qed.

Lemma filter_pad_l_mesh_grid : forall m x l0 k,
    result_has_shape
      (V (gen_pad_list
            (Z.to_nat k :: l0) ++ x))
      (m :: l0) ->
    (0 <= k)%Z ->
    filter
      (fun x0 =>
         negb
           (is_None
              (result_lookup_Z_option
                 x0
                 (V (gen_pad_list
                       (Z.to_nat k :: l0) ++ x)))))
      (mesh_grid
         (map Z.of_nat
              (filter_until (m :: l0) 0))) =
      map
        (fun l1 =>
           match l1 with
           | [] => l1
           | x1 :: xs => (x1 + k)%Z :: xs
           end)
        (filter (fun x0 => negb (is_None (result_lookup_Z_option x0 (V x))))
                (mesh_grid
                   (map Z.of_nat
                        (filter_until (m - Z.to_nat k :: l0) 0)))).
Proof.
  intros.
  simpl in H.
  repeat rewrite map_cons.

  pose proof (result_has_shape_length _ _ _ H).
  rewrite length_app in H1.
  rewrite repeat_length in H1.

  cases m.
  - reflexivity.
  - rewrite filter_until_0_cons by lia.
    rewrite <- H1.
    replace (Z.to_nat k + length x - Z.to_nat k) with (length x) by lia.
    rewrite map_cons at 1.
    rewrite Nat2Z.inj_add by lia.
    rewrite mesh_grid_app by lia.
    rewrite filter_app.
    replace (Datatypes.S m) with
      (Z.to_nat k + (Datatypes.S m - Z.to_nat k))
      by lia.
    rewrite filter_pad_l_empty.
    rewrite app_nil_l.
    rewrite filter_map.
    rewrite Z2Nat.id by lia.
    f_equal.
    cases x. reflexivity.
    simpl length. rewrite filter_until_0_cons by lia.
    eapply filter_ext_in. intros.
    rewrite map_cons in *.
    repeat decomp_index.
    f_equal. f_equal.
    rewrite result_lookup_Z_option_concat_l by lia. auto.
Qed.
Lemma result_lookup_Z_option_empty_vector : forall x,
    result_lookup_Z_option x (V []) = None.
Proof.
  induct x; simpl; eauto. rewrite nth_error_empty.
  cases a; auto.
Qed.

Lemma filter_gen_pad_empty : forall l0 sh,
    filter
      (fun x0 =>
         negb (is_None (result_lookup_Z_option x0 (V (gen_pad_list l0)))))
      sh = [].
Proof.
  intros.
  eapply filter_empty.
  eapply Forall_forall. intros.
  eapply negb_false_iff.
  unfold is_None.
  cases l0. simpl.
  rewrite result_lookup_Z_option_empty_vector. auto.
  replace (V (gen_pad_list (n::l0))) with (gen_pad (n::l0)).
  rewrite result_lookup_Z_option_gen_pad. auto.
  reflexivity.
Qed.

Lemma nth_error_flatten : forall l n m xs z z0,
    (0 <= z)%Z ->
    (z < Z.of_nat n)%Z ->
    (0 <= z0)%Z ->
    (z0 < Z.of_nat m)%Z ->
    result_has_shape (V l) (n::m::xs) ->
    nth_error (flatten_result l) (Z.to_nat (z * Z.of_nat m + z0)%Z) =
      match nth_error l (Z.to_nat z) with
      | Some (V v) => nth_error v (Z.to_nat z0)
      | _ => None
      end.
 Proof.
  induct l; intros.
  - invert H3. simpl in *. lia.
  - invert H3. cases a. invert H9.
    assert (z = 0 \/ 0 < z)%Z by lia. invert H3.
    + simpl. rewrite nth_error_app1.
      2: erewrite result_has_shape_length by eassumption; lia.
      reflexivity.
    + simpl.
      assert (m <= Z.to_nat z * m).
      replace m with (1*m) at 1 by lia.
      eapply mul_le_mono_r. lia.
      rewrite nth_error_app2.
      2: { erewrite result_has_shape_length by eassumption.
           rewrite Z2Nat.inj_add by lia.
           rewrite Z2Nat.inj_mul by lia.
           rewrite Nat2Z.id.
           lia. }
      erewrite result_has_shape_length by eassumption.
      rewrite Z2Nat.inj_add by lia.
      rewrite Z2Nat.inj_mul by lia.
      rewrite Nat2Z.id.
      rewrite add_sub_swap by lia.
      cases (Z.to_nat z). lia.
      simpl. replace (m + n * m - m + Z.to_nat z0) with
        (n * m + Z.to_nat z0) by lia.
      replace n with (Z.to_nat (Z.of_nat n)) by lia.
      replace m with (Z.to_nat (Z.of_nat m)) by lia.
      rewrite <- Z2Nat.inj_mul by lia.
      rewrite <- Z2Nat.inj_add by lia.
      rewrite Nat2Z.id.
      cases l. rewrite nth_error_empty. simpl. rewrite nth_error_empty. auto.
      erewrite IHl. 4: eassumption.
      rewrite Nat2Z.id. auto. lia.
      3: { econstructor. reflexivity. invert H10. eassumption.
           invert H10. auto. }
      simpl in *. lia. lia.
Qed.

Lemma result_lookup_Z_option_flatten : forall l n m xs z z0 x,
    (0 <= z)%Z ->
    (z < Z.of_nat n)%Z ->
    In x (mesh_grid (map Z.of_nat xs)) ->
    (0 <= z0)%Z ->
    (z0 < Z.of_nat m)%Z ->
    result_has_shape (V l) (n::m::xs) ->
    result_lookup_Z_option ((z * Z.of_nat m + z0)%Z :: x)
                           (V (flatten_result l)) =
      result_lookup_Z_option (z :: z0 :: x) (V l).
Proof.
  simpl. intros. erewrite nth_error_flatten; try eassumption.
  cases ((z * Z.of_nat m + z0)%Z); try lia.
  - cases (nth_error l (Z.to_nat z)).
    + eapply result_has_shape_forall in H4.
      eapply nth_error_In in Heq0.
      eapply Forall_forall in H4.
      2: eassumption. cases r. invert H4.
      cases z; cases z0; try lia; auto.
    + cases z; auto.
  - cases (nth_error l (Z.to_nat z)).
    + eapply result_has_shape_forall in H4.
      eapply nth_error_In in Heq0.
      eapply Forall_forall in H4.
      2: eassumption. cases r. invert H4.
      cases z; cases z0; try lia; auto.
    + cases z; auto.
Qed.

Lemma filter_fun_pad_r : forall l k l0,
  (fun x : list Z =>
        negb
          (is_None
             (result_lookup_Z_option x
                (V
                   (l ++
                      repeat
                      (gen_pad l0) k))))) =
    (fun x : list Z =>
        negb
          (is_None
             (result_lookup_Z_option x
                                     (V l)))).
Proof.
  intros. eapply functional_extensionality. intros.
  cases x. reflexivity.
  assert (0 <= z \/ z < 0)%Z by lia.
  invert H.
  2: { cases z; try lia. reflexivity. }
  assert (z < Z.of_nat (length l) \/ Z.of_nat (length l) <= z)%Z by lia.
  invert H.
  2: { simpl.
       cases z; try lia.
       - rewrite nth_error_app2 by lia.
         assert (length l <= Z.to_nat 0) by lia.
         eapply nth_error_None in H. rewrite H. simpl.
         cases ((repeat (gen_pad l0) k)).
         + auto. 
         + cases k. invert Heq. invert Heq.
           rewrite result_lookup_Z_option_gen_pad. reflexivity.
       - rewrite nth_error_app2 by lia.
         assert (length l <= Z.to_nat (Z.pos p)) by lia.
         eapply nth_error_None in H. rewrite H. simpl.
         cases (nth_error
           (repeat (gen_pad l0) k)
           (Pos.to_nat p - Datatypes.length l)).
         + pose proof Heq.
           eapply nth_error_Some in Heq.
           rewrite repeat_length in *.
           rewrite nth_error_repeat in H2 by lia.
           invs.
           rewrite result_lookup_Z_option_gen_pad. reflexivity.
         + auto. }
  simpl.
  cases z; try lia.
  - rewrite nth_error_app1. auto. lia.
  - rewrite nth_error_app1. auto. lia.
Qed.  

Lemma result_lookup_Z_option_None : forall x2 r,
    result_has_shape r (result_shape_nat r) ->
    ~ In x2
      (filter
         (fun x => negb (is_None (result_lookup_Z_option x r)))
         (mesh_grid (result_shape_Z r))) ->
    result_lookup_Z_option x2 r = None.
Proof.
  induct x2; intros.
  - simpl in *. propositional. cases r; auto.
    simpl in *. cases z; simpl in *; propositional.
  - simpl in *.
    cases a; auto.
    + erewrite filter_In in *. 
      unfold result_shape_Z in *. simpl map in *.
      cases r; auto.
      simpl map in *.
      cases v. simpl. auto.
      simpl map in *.
      rewrite <- in_mesh_grid_cons__ in H0. posnats.
      eapply Classical_Prop.not_and_or in H0.
      simpl. invert H0.
      * eapply Classical_Prop.not_and_or in H1. invert H1. lia.
        eapply IHx2. invert H. eauto. 
        unfold not. intros. apply H0.
        eapply filter_In in H1. propositional.
      * eapply IHx2. invert H. eauto.
        unfold not. intros.
        eapply filter_In in H0. propositional.
    + cases r; auto.
      unfold result_shape_Z in *. simpl map in *.
      cases v. rewrite nth_error_empty. auto.
      simpl map in *.
      erewrite filter_In in *. 
      rewrite <- in_mesh_grid_cons__ in H0. posnats.
      eapply Classical_Prop.not_and_or in H0.
      simpl. invert H0.
      * eapply Classical_Prop.not_and_or in H1.
        simpl. invert H1.
        -- cases (nth_error (r :: v) (Pos.to_nat p)).
           eapply nth_error_Some in Heq. simpl length in *. lia.
           auto.
        -- cases (nth_error (r :: v) (Pos.to_nat p)); auto.
           eapply IHx2.
           eapply nth_error_In in Heq.
           eapply Forall_forall
             with (P:= fun r =>
                         result_has_shape r (result_shape_nat r)) in Heq.
           2: { invert H. econstructor.
                apply H7.
                erewrite result_has_shape_result_shape_nat in H8 by eauto.
                eapply result_has_shape_result_shape_nat in H7.
                eapply Forall_impl.
                2: eassumption. intros.
                eapply result_has_shape_self. apply H. }
                eauto.
           unfold not. intros.
           apply H0.
           eapply filter_In in H1. propositional.
           invert H.
           cases (Pos.to_nat p); try lia. simpl in Heq.
           eapply nth_error_In in Heq.
           eapply Forall_forall in Heq.
           2: eassumption. simpl in *.
           erewrite result_has_shape_result_shape_nat in H2 by eauto.
           erewrite result_has_shape_result_shape_nat by eauto.
           eauto.
      * cases (nth_error (r :: v) (Pos.to_nat p)); auto.
        eapply IHx2. invert H.
        cases (Pos.to_nat p); try lia. simpl in Heq.
        eapply nth_error_In in Heq.
        eapply Forall_forall in Heq.
        2: eassumption. simpl in Heq. eauto.
        eapply result_has_shape_self. eauto.
        unfold not. intros.
        eapply filter_In in H0. propositional.
        simpl in H1.
        cases (Pos.to_nat p); try lia. simpl is_None in H1.
        simpl in Heq. rewrite Heq in *.
        eauto.
Qed.

Lemma result_lookup_Z_option_split : forall l k n z args1 sh,
    In args1 (mesh_grid (map Z.of_nat sh)) ->
    (0 <= z)%Z ->
    (z < Z.of_nat n)%Z ->
    0 < k ->
    result_has_shape (V l) (n::sh) ->
    result_lookup_Z_option
      ((z / Z.of_nat k)%Z :: (z mod Z.of_nat k)%Z :: args1)
      (V (split_result k l)) =
      result_lookup_Z_option (z :: args1) (V l).
Proof.
  intros. simpl.
  cases (z / Z.of_nat k)%Z.
  3: { pose proof (Z.div_pos z (Z.of_nat k)). lia. }
  2: { cases (z mod Z.of_nat k)%Z.
       3: { pose proof (mod_nonneg (Z.of_nat k) z). lia. }
       2: { cases z.
            3: lia.
            2: { rewrite <- Heq,<-Heq0.
                 rewrite Z2Nat.inj_div by lia. rewrite Z2Nat.inj_mod by lia.
                 pose proof (nth_error_split_result l k
                                                    (Z.to_nat (Z.pos p1))).
                 rewrite <- H4.
                 2: { lia. }
                 2: { erewrite result_has_shape_length by eauto. lia. }
                 repeat rewrite Nat2Z.id.
                 cases (nth_error (split_result k l) (Z.to_nat (Z.pos p1)/k)).
                 cases r; auto. auto. }
            repeat rewrite Z.mod_0_l in * by lia. lia. }
       pose proof (nth_error_split_result l k (Z.to_nat z)).
       rewrite <- H4.
       rewrite <- Heq.
       rewrite Z2Nat.inj_div by lia.
       rewrite Nat2Z.id.
       cases (nth_error (split_result k l) (Z.to_nat z / k)).
       { cases z; cases r; auto. simpl Z.to_nat.
         rewrite mod_0_l by lia. reflexivity.
         rewrite <- (Z2Nat.id (_ mod _)%Z) in Heq0 by lia.
         rewrite Z2Nat.inj_mod in Heq0.
         rewrite Nat2Z.id in Heq0.
         replace (Z.to_nat (Z.pos p0) mod k) with 0 by lia. reflexivity.
         lia. lia. lia. }
       cases z; auto. lia. erewrite result_has_shape_length by eauto. lia. }
  cases z; try lia.
  cases l. rewrite nth_error_empty. unfold split_result. simpl.
  rewrite div_ceil_n_0. simpl. auto. lia.
  pose proof (nth_error_split_result (r::l) k (Z.to_nat 0)).
  rewrite <- H4. simpl Z.to_nat.
  rewrite mod_0_l by lia. rewrite Z.mod_0_l by lia.
  rewrite div_0_l by lia.
  cases (nth_error (split_result k (r::l)) 0); eauto. cases r0; eauto. lia.
  simpl. lia.
  cases l. rewrite nth_error_empty. unfold split_result. simpl.
  rewrite div_ceil_n_0. simpl. auto. lia.
  pose proof (nth_error_split_result (r::l) k (Z.to_nat (Z.pos p))).
  rewrite <- H4.
  2:{ lia. }
  2: { erewrite result_has_shape_length. 2: eassumption. lia. }
  replace (Z.to_nat (Z.pos p) / k) with 0.
  2: { rewrite <- Nat2Z.id.
       eapply Nat2Z.inj_iff.
       rewrite Nat2Z.inj_div by lia.
       rewrite Z2Nat.inj_div by lia.
       rewrite Nat2Z.inj_div by lia.
       rewrite (Nat2Z.id k ) by lia.
       rewrite Nat2Z.id. rewrite Z2Nat.id by lia. lia. }
  simpl Z.to_nat.
  cases (nth_error (split_result k (r :: l)) 0).
  - posnats.
    replace (Pos.to_nat p mod k) with
      (Z.to_nat  (Z.pos p mod Z.of_nat k)%Z).
    cases (Z.pos p mod Z.of_nat k)%Z.
    3: { pose proof (mod_nonneg (Z.of_nat k) (Z.pos p) ). lia. }
    cases r0; auto.
    cases r0; auto.
    rewrite Z2Nat.inj_mod by lia. simpl. rewrite Nat2Z.id. lia.
  - reflexivity.
Qed.  

Lemma result_lookup_Z_option_split_true : forall z z0 x0 l k m sh,
  negb
          (is_None
             (result_lookup_Z_option (z :: z0 :: x0)
                (V (split_result (Z.to_nat k) l)))) =
        true ->
  (0 <= z < m // k)%Z ->
  (0 <= z0 < k)%Z ->
  (0 <= m)%Z ->
  In x0
     (mesh_grid (map Z.of_nat sh)) ->
  result_has_shape (V l) (Z.to_nat m::sh) ->
  (z * k + z0 < m)%Z.
Proof.
  intros. 
  erewrite <- result_lookup_Z_option_flatten in H; eauto; try lia.
  4: { eapply result_has_shape_split_result. lia. eauto. }
  2: { erewrite <- Z2Nat_div_distr by lia. rewrite Z2Nat.id by lia. lia. }
  2: { lia. }
  erewrite flatten_result_split_result in H.
  2: { eapply forall_result_has_shape.
       eapply result_has_shape_forall; eauto. eauto. }
  2 : lia.
  rewrite Z2Nat.id in * by lia.
  simpl in H.
  cases (z * k + z0)%Z.
  3: { lia. }
  { cases l. rewrite nth_error_app2 in *. 2: simpl; lia.
    simpl in H. rewrite mod_0_l in * by lia. rewrite sub_0_r in * by lia.
    rewrite mod_same in * by lia. simpl in *. discriminate.
    invert H4. lia. }
  pose proof H4. eapply result_has_shape_length in H4.
  assert (Z.pos p < m \/ m <= Z.pos p)%Z by lia. invert H6. auto.
  rewrite nth_error_app2 in H.
  2: { lia. }
  cases (nth_error
               (repeat (gen_pad sh)
                  ((Z.to_nat k -
                    Datatypes.length l mod Z.to_nat k)
                   mod Z.to_nat k))
               (Z.to_nat (Z.pos p) - Datatypes.length l)).
  - pose proof Heq0.
    eapply nth_error_Some in H6. rewrite nth_error_repeat in Heq0.
    invert Heq0.
    rewrite result_lookup_Z_option_gen_pad in *. simpl in *. discriminate.
    rewrite repeat_length in *. lia.
  - discriminate.
Qed.  

