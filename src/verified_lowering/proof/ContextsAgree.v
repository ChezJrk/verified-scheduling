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
From Stdlib Require Import Logic.FunctionalExtensionality.

Set Warnings "-deprecate-hint-without-locality,-deprecated".
Import ListNotations.

From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.
From Lower Require Import Zexpr Bexpr Array Range Sexpr Result ListMisc Meshgrid VarGeneration
     Injective Constant InterpretReindexer ResultToArrayDelta.

Open Scope string_scope.

Definition contexts_agree
           (ec : expr_context) (st : stack) (h : heap) sh :=
  forall x,
    (forall v, ec $? x = Some (V v) ->
               exists l,
                 sh $? x = Some l /\
                   Forall (fun x => vars_of_Zexpr x = []) l /\
                   result_has_shape
                     (V v)
                     (map Z.to_nat (map (eval_Zexpr_Z_total $0) l)) /\
                   (Forall (fun x => 0 <= x)%Z
                           (map (eval_Zexpr_Z_total $0) l)) /\
               exists arr,
                 h $? x = Some arr /\
                   array_add
                     (alloc_array
                        (Z.to_nat
                           (fold_left
                              Z.mul
                              (map Z.of_nat
                                   (filter_until
                                      (map Z.to_nat
                                           (map (eval_Zexpr_Z_total $0) l)
                                      ) 0)) 1%Z)) $0)
                     (tensor_to_array_delta
                        (partial_interpret_reindexer
                           (fun l => l)
                           (map Z.of_nat
                                (filter_until
                                   (map Z.to_nat
                                        (map (eval_Zexpr_Z_total $0) l)) 0)) $0)
                        (V v)) = arr) /\
      (forall s, ec $? x = Some (S s) -> sh $? x = Some [] /\
                                           st $? x = Some (match s with
                                                           | SS r => r
                                                           | SX => 0%R
                                                           end)).

Lemma eval_get_eval_Zexprlist : forall l v rs r,
    eval_get v rs l r ->
    exists lz, eval_Zexprlist v l lz.
Proof.
  induct 1; invs.
  - eexists. econstructor. eauto. eauto.
  - eexists. eauto.
Qed.

Arguments flatten : simpl nomatch.
Lemma eval_get_lookup_result_Z : forall l v rs r,
    eval_get v rs l r ->
    forall x0,
      eval_Zexprlist v l x0 ->
      r = result_lookup_Z x0 (V rs).
Proof.
  induct 1; intros.
  - invert H3. simpl.
    eq_eval_Z. rewrite H1.
    cases z; try lia; eauto.
  - invert H2. invert H8. eq_eval_Z. simpl. rewrite H1.
    cases z; try lia; eauto.
Qed.

Lemma eval_get_In_meshgrid : forall l v rs r,
    eval_get v rs l r ->
    result_has_shape (V rs) (result_shape_nat (V rs)) ->
    forall x0,
      eval_Zexprlist v l x0 ->
      In x0 (mesh_grid (result_shape_Z (V rs))).
Proof.
  induct 1; intros.
  - invert H4. cases l. simpl in *.
    cases (Z.to_nat i); invert H1.
    unfold result_shape_Z. simpl map. posnats.
    erewrite <- in_mesh_grid_cons__.
    split. eq_eval_Z.
    eapply nth_error_Some in H1. simpl in *. lia.
    unfold result_shape_Z in IHeval_get.
    simpl in H3. invert H3. clear H9.
    eapply nth_error_In in H1.
    simpl in H1. invert H1.
    + eauto.
    + eapply Forall_forall in H12. 2: eapply H3.
      pose proof (result_has_shape_result_shape_nat _ _ H12).
      erewrite result_has_shape_result_shape_nat by eassumption.
      rewrite <- H1.
      eapply result_has_shape_self in H12. eauto.
  - invert H3. invert H9. unfold result_shape_Z. simpl.
    cases l. cases (Z.to_nat i); invert H1.
    invert H2. clear H8.
    pose proof (nth_error_Some _ _ _ H1).
    eapply nth_error_In in H1. simpl in H1. invert H1.
    + simpl map. posnats.
      erewrite <- in_mesh_grid_cons. simpl. propositional.
      simpl in *. posnats. eq_eval_Z. lia.
    + eapply Forall_forall in H10. 2: eapply H3.
      eapply result_has_shape_result_shape_nat in H10.
      erewrite result_has_shape_result_shape_nat by eassumption.
      rewrite <- H10. simpl map. eq_eval_Z.
      erewrite <- in_mesh_grid_cons__. simpl in *.
      propositional. lia.
Qed.

Lemma eval_Sexpr_eval_Sstmt : forall sh (v : valuation) ec s r,
    eval_Sexpr sh v ec s r ->
    forall st h r0,
      contexts_agree ec st h sh ->
      eval_Sstmt v st h (lowerS s sh) r0 ->
      match r with
      | SS s => s
      | SX => 0%R
      end = r0.
Proof.
  induct 1; intros; simpl in *; try invert1 H2; try f_equal; eauto.
  - eapply H1 in H. invs. rewrite H3 in H7. invert H7. cases r; auto.
  - rewrite H0 in *.
    invert H4.
    rewrite map_fst_combine in H8 by auto.
    rewrite map_snd_combine in H8 by auto.
    unfold contexts_agree in *.
    specialize (H3 x). invert H3. clear H5.
    eapply H4 in H.
    clear H4. invs.
    
    (* REVISIT *)
    assert (Some
         (array_add
            (alloc_array
               (Z.to_nat
                  (fold_left Z.mul (map Z.of_nat (filter_until (map Z.to_nat (map (eval_Zexpr_Z_total $0) x0)) 0))
                     1%Z)) $0)
            (tensor_to_array_delta
               (partial_interpret_reindexer (fun l : list (Zexpr * Zexpr) => l)
                  (map Z.of_nat (filter_until (map Z.to_nat (map (eval_Zexpr_Z_total $0) x0)) 0)) $0) 
               (V rs))) = Some l0).
    rewrite <- H9. eauto.
    invert H6.
    rewrite H0 in *. invert H.
    pose proof H2. eapply eval_get_eval_Zexprlist in H2. invs.
    eapply eval_Zexpr_Z_eval_Zexpr in H8.
    erewrite eval_Zexpr_Z_flatten_index_flatten in H8; eauto.
    2: { eapply forall_no_vars_eval_Zexpr_Z_total. eauto. }
    invert H8.

    pose proof H.
    eapply eval_get_lookup_result_Z in H2; eauto. subst.

    erewrite <- result_has_shape_result_shape_Z in H14 by eauto.
    rewrite
      tensor_to_array_delta_partial_interpret_reindexer_flatten
      in H14.
    unfold array_add in *.
    rewrite lookup_merge in *.
    erewrite result_has_shape_result_shape_Z in H14 by eauto.
    pose proof H5.
    eapply forall_nonneg_exists_zero_or_forall_pos_Z in H5.
    invert H5.
    + rewrite filter_until_0_id in H14.
      2: { eapply Forall_map.
           eapply Forall_impl. 2: apply H8. simpl. intros. lia. }
      rewrite Z2Natid_list in * by auto.
      
      rewrite result_lookup_Z_tensor_to_array_delta in *.
      eapply eval_get_In_meshgrid in H; eauto.
      erewrite result_has_shape_result_shape_Z in H; eauto.
      repeat decomp_index.
      rewrite mesh_grid_map_Nat2Z_id in *.
      cases rs.
      { invert H4. cases x0. simpl in *. discriminate.
        invert H5. rewrite map_cons in *. 
        repeat decomp_index. lia. }
      invert H4. simpl in *. cases x0. simpl in *. discriminate.
      simpl map in *. invert H11.
      eapply in_mesh_grid_args_flatten_bounds in H.
      invert H.
      2: { invert H2. eapply fold_left_mul_nonneg in H11.
           2: apply H13.
           lia. }
      cases (alloc_array
            (Z.to_nat
               (fold_left Z.mul
                  (eval_Zexpr_Z_total $0 z :: map (eval_Zexpr_Z_total $0) x0) 1%Z))
            $0 $?
          flatten (eval_Zexpr_Z_total $0 z :: map (eval_Zexpr_Z_total $0) x0) x1).
      * pose proof (lookup_alloc_array
                      (Z.to_nat
               (fold_left Z.mul
                  (eval_Zexpr_Z_total $0 z :: map (eval_Zexpr_Z_total $0) x0) 1%Z))
                      (flatten (eval_Zexpr_Z_total $0 z :: map (eval_Zexpr_Z_total $0) x0) x1)).
        invert H. rewrite H10 in *. discriminate.
        rewrite H10 in *. invs.
        cases (result_lookup_Z_option x1 (V (r :: rs))). invs.
        rewrite Rplus_0_l.
        eapply result_lookup_Z_option_result_lookup_Z in Heq. rewrite Heq.
        auto.
        invs.
        eapply result_lookup_Z_option_result_lookup_Z_None in Heq.
        cases (result_lookup_Z x1 (V (r :: rs))); eauto.
      * eapply result_lookup_Z_option_result_lookup_Z in H14. rewrite H14.
        auto.
      * eapply result_has_shape_self; eauto.
      * eapply result_has_shape_self; eauto.
      * eapply eval_get_In_meshgrid. eauto.
        eapply result_has_shape_self; eauto.
        eauto.
      * unfold injective. intros. invs.
        eapply injective_flatten; eauto.
        erewrite result_has_shape_result_shape_Z by eauto.
        rewrite filter_until_0_id.
      2: { eapply Forall_map.
           eapply Forall_impl. 2: apply H8. simpl. intros. lia. }
      rewrite Z2Natid_list in * by auto.
      auto.
    + eapply eval_get_In_meshgrid in H; eauto.
      erewrite result_has_shape_result_shape_Z in H; eauto.
      erewrite exists_0_empty_mesh_grid in H.
      simpl in *. propositional.
      eapply exists_0_map_Z_of_nat.
      eapply exists_0_filter_until_0.
      eapply Exists_map.
      eapply Exists_impl. 2: eapply H8.
      simpl. intros. subst. lia.
      eapply result_has_shape_self; eauto.
  - eapply IHeval_Sexpr1 in H5; eauto.
    eapply IHeval_Sexpr2 in H9; eauto.
    cases r1; cases r2; subst; simpl; auto. 
  - eapply IHeval_Sexpr1 in H5; eauto.
    eapply IHeval_Sexpr2 in H9; eauto.
    cases r1; cases r2; subst; simpl; auto. 
  - invert H3.
    eapply IHeval_Sexpr1 in H6; eauto.
    eapply IHeval_Sexpr2 in H10; eauto.
    cases r1; cases r2; subst; simpl; auto.
  - eapply IHeval_Sexpr1 in H5; eauto.
    eapply IHeval_Sexpr2 in H9; eauto.
    cases r1; cases r2; subst; simpl; auto.
  - invert H0. eauto.
Qed.

Lemma contexts_agree_add_heap : forall ec st h sh a val p,
    contexts_agree ec st h sh ->
    h $? p = Some a ->
    ~ p \in dom sh ->
    ~ p \in dom ec ->
    contexts_agree ec st (h $+ (p,array_add a val)) sh.
Proof.
  unfold contexts_agree. propositional.
  - eapply H in H3. invs. clear H.    
    cases (x ==v p). subst. eapply lookup_Some_dom in H3. sets.
    rewrite lookup_add_ne by auto.
    eexists. split.
    eassumption. split. eassumption. split. eassumption.
    split. eassumption.
    eexists. split. eassumption. reflexivity.
  - eapply H in H3. propositional.
  - eapply H in H3. propositional.
Qed.

Lemma contexts_agree_alloc_array_in_heap :
  forall ec st h sh x l,
    contexts_agree ec st h sh ->
    ec $? x = None ->
    contexts_agree ec st (alloc_array_in_heap l h x) sh.
Proof.
  unfold contexts_agree. propositional.
  - cases (x ==v x0). subst. rewrite H0 in *. discriminate.
    eapply H in H1.
    invs.
    eexists.
    split. eassumption.
    split. eassumption.
    split. eassumption.
    split. eassumption.    
    eexists. unfold alloc_array_in_heap.
    rewrite lookup_add_ne by auto.
    split. eassumption. reflexivity.
  - eapply H. eauto.
  - eapply H. eauto.
Qed.    

Lemma contexts_agree_add_in_stack :
  forall ec st h sh p val a,
    contexts_agree ec st h sh ->
    st $? p = Some a ->
          ~ p \in dom sh ->
       ~ p \in dom ec ->
          contexts_agree ec (st $+ (p, val)) h sh.
Proof.
  unfold contexts_agree. propositional.
  - eapply H. auto.
  - cases (x ==v p).
    + subst. eapply H. eauto. 
    + subst. eapply H. eauto. 
  - cases (x ==v p).
    + subst. rewrite lookup_add_eq by auto.
      eapply lookup_Some_dom in H3. sets.
    + rewrite lookup_add_ne by auto.
      eapply H. auto.
Qed.

Lemma contexts_agree_alloc_stack : forall ec st x val h sh,
    contexts_agree ec st h sh ->
    ec $? x = None ->
    contexts_agree ec (st $+ (x, val)) h sh.
Proof.
  unfold contexts_agree. propositional.
  - eapply H. eauto. 
  - cases (x ==v x0). subst. rewrite H1 in *. discriminate.
    eapply H. eauto.
  - cases (x ==v x0). subst. rewrite H1 in *. discriminate.
    rewrite lookup_add_ne by auto.
    eapply H. auto.
Qed.

Lemma contexts_agree_let_bind1_scalar :
  forall ec st h sh x r,
  contexts_agree ec st h sh ->
  contexts_agree (ec $+ (x, S r)) (st $+ (x, (match r with
                                                | SS r' => r'
                                                | SX => 0%R
                                                end))) h (sh $+ (x, [])).
Proof.
  unfold contexts_agree. propositional.
  - cases (x ==v x0).
    + subst. repeat rewrite lookup_add_eq in * by auto. invs.
    + rewrite lookup_add_ne in * by auto. eapply H in H0.
      eauto.
  - cases (x ==v x0).
    + subst. rewrite lookup_add_eq in * by auto. invs. auto.
    + rewrite lookup_add_ne in * by auto.
      eapply H. eauto.
  - cases (x ==v x0).
    + subst. rewrite lookup_add_eq in * by auto. invs. auto.
    + rewrite lookup_add_ne in * by auto.
      eapply H. auto.
Qed.

Lemma contexts_agree_add_alloc_heap :
  forall ec st h sh x nz z esh1 l1,
  contexts_agree ec st h sh ->
  ec $? x = None ->
  result_has_shape (V l1)
                   (map Z.to_nat (map (eval_Zexpr_Z_total $0) (z :: esh1))) ->
  Forall (fun x : Z => (0 <= x)%Z) (map (eval_Zexpr_Z_total $0) (z :: esh1))->
  Forall (fun x : Zexpr => vars_of_Zexpr x = []) (z :: esh1) ->
  fold_left Z.mul
            (map Z.of_nat
                 (filter_until
                    (map Z.to_nat
                         (map (eval_Zexpr_Z_total $0) (z :: esh1))) 0))
            1%Z = nz ->  
  contexts_agree (ec $+ (x, V l1)) st (h $+ (x,
          array_add (alloc_array (Z.to_nat nz) $0)
                    (tensor_to_array_delta
                       (partial_interpret_reindexer
                          (fun l : list (Zexpr * Zexpr) => l)
                          (map Z.of_nat
                               (filter_until
                                  (map Z.to_nat
                                       (map (eval_Zexpr_Z_total $0)
                                            (z :: esh1))) 0)) $0)
                       (V l1)))) (sh $+ (x, z :: esh1)).
Proof.
  unfold contexts_agree. propositional.
  - cases (x ==v x0).
    + subst. rewrite lookup_add_eq in * by auto.
      invs. 
      eexists.
      split. reflexivity.
      split. eauto.
      split. eauto.
      split. eassumption.
      eexists. rewrite lookup_add_eq by auto.
      split. reflexivity.
      f_equal.
    + rewrite lookup_add_ne in * by auto.
      eapply H in H5. clear H. invs.
      eexists.
      split. eassumption.
      split. eassumption.
      split. eassumption.
      split. eassumption.
      eexists. rewrite lookup_add_ne by auto. split.
      eassumption. reflexivity.
  - cases (x ==v x0).
    + subst. rewrite lookup_add_eq in * by auto.
      invert H5.
    + rewrite lookup_add_ne in * by auto.
      eapply H. eauto.
  - cases (x ==v x0).
    + subst. rewrite lookup_add_eq in * by auto.
      invert H5.
    + rewrite lookup_add_ne in * by auto.
      eapply H. eauto.
Qed.

Lemma contexts_agree_result_has_shape :
  forall ec st h sh,
  contexts_agree ec st h sh ->
  (forall (x0 : var) (r0 : result) (size0 : list Zexpr),
      sh $? x0 = Some size0 ->
      ec $? x0 = Some r0 ->
      result_has_shape r0
                       (map Z.to_nat (map (eval_Zexpr_Z_total $0) size0))).
Proof.
  unfold contexts_agree. intros. specialize (H x0).
  invs.
  cases r0.
  - eapply H3 in H1. propositional. rewrite H in *. invs. econstructor.
  - eapply H2 in H1; clear H2. invs. rewrite H1 in *. invs.
    eauto.
Qed.    

