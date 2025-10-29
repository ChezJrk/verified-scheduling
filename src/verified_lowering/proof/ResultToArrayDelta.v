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
From Lower Require Import ATLDeep Zexpr Bexpr Array Range Sexpr Result ListMisc
  Meshgrid VarGeneration Injective Constant InterpretReindexer
  WellFormedEnvironment ATLDeep.

Open Scope string_scope.

Local Hint Resolve
      eval_Zexprlist_includes_valuation includes_add_new None_dom_lookup.

Lemma option_eq_dec {X} :
  (forall (a b :X), {a = b} + {a <> b }) ->
  forall (x y : option X),
    {x  = y} + {x <> y}.
Proof.
  intros.
  cases x; cases y.
  - specialize (X0 x x0). invert X0.
    auto. right. unfold not. intros. invert H0. propositional.
  - right. inversion 1.
  - right. inversion 1.
  - auto.
Qed.

Definition tensor_to_array_delta_by_indices
           (reindexer : list Z -> option Z) r indices : array :=
  fold_left (fun arr index =>
               match reindexer index, result_lookup_Z_option index r with
               | Some z,Some val => array_add
                             arr
                             ($0 $+ (z,val))
               | _,_ => arr
               end)
            indices $0.

Definition tensor_to_array_delta reindexer r :=
  let shape := result_shape_Z r in
  let indices := mesh_grid shape in
  let indices := filter (fun x => negb (is_None (result_lookup_Z_option x r)))
                        indices in
  tensor_to_array_delta_by_indices reindexer r indices.

Lemma partial_fold_left_array_add_accum_assoc :
  forall domain val k f (v : array) r,
    no_dup domain ->
    partial_injective f domain ->
    ~ k \in dom v ->
            (Forall (fun x => match f x with
                              | Some val => ~ val \in dom v
                              | _ => True
                              end) domain) ->
            Forall (fun index => match f index with
                                 | Some val => val <> k
                                 | _ => True
                                 end) domain ->
            fold_left
              (fun (arr : array) (index0 : list Z) =>
                 match f index0,result_lookup_Z_option index0 r  with
                 | Some z,Some val => array_add arr ($0 $+ (z, val))
                 | _,_ => arr
                 end) domain (v $+ (k, val)) =
              (fold_left
                 (fun (arr : array) (index0 : list Z) =>
                    match f index0,result_lookup_Z_option index0 r with
                    | Some z,Some val => array_add arr ($0 $+ (z, val))
                    | _,_ => arr
                    end) domain
                 v) $+ (k, val).
Proof.
  induct domain; intros.
  - reflexivity.
  - simpl in *.
    invert H2. invert H3.
    cases (f a); cases (result_lookup_Z_option a r).
    + repeat rewrite array_add_singleton_collapse.
      * rewrite add_comm.
        2: { auto. }
        rewrite IHdomain.
        -- reflexivity.
        -- invert H. auto.
        -- eapply partial_injective_cons; eauto.
        -- rewrite dom_add. sets.
        -- rewrite dom_add.
           eapply Forall_impl_weak.
           2: eassumption.
           intros. simpl in *.
           cases (f x); auto.
           assert (forall l l' : list Z, {l = l'} + {l <> l'}).
           apply list_eq_dec. apply Z.eq_dec.
           specialize (H4 x a). invert H4.
           ++ rewrite Heq in Heq1. invert Heq1.
              invert H. propositional.
           ++ eapply Forall_forall in H7. 2: apply H2.
              rewrite Heq1 in *. sets.
              eapply H9.
              rewrite <- Heq1 in Heq. pose proof Heq.
              eapply H0 in Heq. simpl in *.
              propositional.

              subst. auto.

              rewrite H10 in H4. rewrite <- H4 in *. discriminate.

              simpl. propositional.

              simpl. propositional.
        -- eauto.
      * auto.
      * rewrite dom_add. sets.
    + rewrite IHdomain; eauto.
      invert H. auto.
      eapply partial_injective_cons; eauto.      
    + rewrite IHdomain; eauto.
      invert H. eauto.
      eapply partial_injective_cons; eauto.      
    + rewrite IHdomain; eauto.
      invert H. eauto.
      eapply partial_injective_cons; eauto.
Qed.

Lemma partial_dom_fold_left_array_add :
  forall (domain : list (list Z)) f acc r,
    partial_injective f domain ->
    dom (fold_left (fun arr index =>
                      match f index,result_lookup_Z_option index r with
                      | Some z,Some val => array_add arr ($0 $+ (z, val))
                      | _,_ => arr
                      end)
                   domain acc) =
      (constant
         (extract_Some
            (map
               f (filter
                    (fun x =>
                       negb (is_None (result_lookup_Z_option x r)))
                    domain))))
        \cup dom acc.
Proof.
  induct domain; intros.
  - simpl. sets.
  - simpl. rewrite IHdomain.
    cases (f a); cases (result_lookup_Z_option a r).
    + rewrite dom_array_add.
      rewrite dom_add. rewrite dom_empty. rewrite cup_empty_r.
      simpl. rewrite Heq.
      symmetry. rewrite constant_cons. symmetry. sets.
    + reflexivity.
    + simpl. rewrite Heq. reflexivity.
    + reflexivity.
    + eapply partial_injective_cons; eauto.
Qed.

Lemma partial_lookup_fold_left_array_add : forall domain index r f k,
    partial_injective f domain ->
    no_dup domain ->
    In index domain ->
    f index = Some k ->
    fold_left
      (fun (arr : array) (index0 : list Z) =>
         match f index0,result_lookup_Z_option index0 r with
         | Some z,Some val => array_add arr ($0 $+ (z, val))
         | _,_ => arr
         end) domain
      $0 $? k = result_lookup_Z_option index r.
Proof.
  induct domain; intros; simpl in *; propositional; subst.
  - rewrite H2.
    pose proof H as Htmp.
    cases (result_lookup_Z_option index r).
    + rewrite array_add_empty_l.
      rewrite partial_fold_left_array_add_accum_assoc; eauto.
      rewrite lookup_add_eq by auto. reflexivity.
      invert H0. auto.
      eapply partial_injective_cons; eauto.
      rewrite dom_empty. auto.
      rewrite dom_empty.
      eapply Forall_forall. intros. sets.
      cases (f x); propositional.
      eapply Forall_forall. intros.
      cases (f x); auto.
      unfold not. intros.
      subst. pose proof Heq. rewrite <- H2 in Heq0.
      pose proof Heq0.
      eapply Htmp in Heq0. simpl in Heq0.
      propositional. subst. invert H0. propositional.
      rewrite H5 in *. rewrite <- H4 in *. discriminate.
      simpl. propositional.
      simpl. propositional.
    + rewrite None_dom_lookup. auto.
      rewrite partial_dom_fold_left_array_add.
      rewrite dom_empty. rewrite cup_empty_r.
      unfold not. intros. eapply In_iff_in in H1.
      rewrite <- in_extract_Some in H1.
      eapply in_map_iff in H1. invs.
      eapply filter_In in H4. invs.
      pose proof H2. rewrite <- H1 in H2.
      eapply H in H2. simpl in H2.
      propositional. subst. invert H0. propositional.
      subst. rewrite H6 in *. discriminate.
      simpl. propositional.
      simpl. propositional.
      eapply partial_injective_cons; eauto.
  - pose proof H. pose proof H0. 
    cases (f a); cases (result_lookup_Z_option a r).
    + rewrite array_add_empty_l.
      rewrite partial_fold_left_array_add_accum_assoc;
        try rewrite dom_empty; eauto.
      assert (forall l l' : list Z, {l = l'} + {l <> l'}).
      apply list_eq_dec. apply Z.eq_dec.
      specialize (H5 index a). invert H5; subst.
      * rewrite Heq in *. invert H2.        
        rewrite lookup_add_eq by auto. auto.
      * rewrite lookup_add_ne.
        eapply IHdomain; eauto. invert H0.
        eapply partial_injective_cons; eauto.
        invert H0. auto.
        unfold not. intros.
        subst.
        pose proof Heq. rewrite <- H2 in Heq.
        eapply H in Heq. simpl in Heq.
        propositional. subst. invert H4. propositional.
        subst. rewrite H7 in *. discriminate.
        simpl. propositional.
        simpl. propositional.
      * invert H0. auto.
      * eapply partial_injective_cons; eauto.
      * eapply Forall_forall. intros.
        cases (f x); auto.
      * eapply Forall_forall. intros.
        cases (f x); auto.
        unfold not. intros. subst.
        pose proof Heq. rewrite <- Heq1 in Heq.
        eapply H in Heq. simpl in Heq. propositional. subst.
        invert H4. propositional. rewrite H7 in *. discriminate.
        simpl. propositional.
        simpl. propositional.
    + eapply IHdomain; eauto.
      eapply partial_injective_cons; eauto.
      invert H0. auto.
    + eapply IHdomain; eauto.
      eapply partial_injective_cons; eauto.
      invert H0. auto.
    + eapply IHdomain; eauto.
      eapply partial_injective_cons; eauto.
      invert H0. auto.
Qed.

Lemma tensor_to_array_delta_cons_generic_indexer :
  forall r r0 f l,
    result_has_shape (V (r::r0)) l ->
    partial_injective f
                      (filter
                         (fun x =>
                            negb (is_None
                                    (result_lookup_Z_option x (V (r :: r0)))))
                         (mesh_grid (result_shape_Z (V (r::r0))))) ->
    tensor_to_array_delta f (V (r :: r0)) =
      array_add
        (tensor_to_array_delta (fun index => f (0::index)%Z) r)
        (tensor_to_array_delta (fun index =>
                                          match index with
                                          | x::xs => f (x+1::xs)%Z
                                          | _ => f index
                                          end) (V r0)).
Proof.
  intros. 
  cases l. invert H.
  unfold tensor_to_array_delta.
  eapply fmap_ext. intros.
  unfold tensor_to_array_delta_by_indices.
  pose proof (in_dec (option_eq_dec Z.eq_dec)).
  specialize (H1 (Some k)
                 (map f
                      (filter
                         (fun x =>
                            negb (is_None
                                    (result_lookup_Z_option x (V (r :: r0)))))
                         (mesh_grid (result_shape_Z (V (r :: r0))))))).
  invert H1.
  - eapply in_map_iff in H2. invs.
    repeat decomp_index.

    erewrite partial_lookup_fold_left_array_add; eauto using no_dup_mesh_grid.
    2: { eapply no_dup_filter.
         eapply no_dup_mesh_grid. }
    2: { eapply filter_In. propositional. }

    erewrite result_has_shape_result_shape_Z in H1 by eauto.
    repeat decomp_index.
    assert (z = 0 \/ z <> 0)%Z as Hcase by lia.
    inversion Hcase as [ Hcase1 | Hcase2 ]; clear Hcase.
    + subst.
      rewrite lookup_array_add_l.
      2: { rewrite partial_dom_fold_left_array_add.
           rewrite dom_empty. rewrite cup_empty_r.
           rewrite filter_idempotent.
           rewrite <- In_iff_in.
           erewrite <- in_extract_Some.
           eapply in_map_iff. eexists. split. eauto.
           eapply filter_In.
           propositional. invert H.
           erewrite result_has_shape_result_shape_Z by eauto.
           decomp_goal_index. eauto.
           eapply partial_injective_cons_0.
           eauto. }
      2: { rewrite partial_dom_fold_left_array_add.
           rewrite dom_empty. rewrite cup_empty_r.
           rewrite filter_idempotent.
           rewrite partial_dom_fold_left_array_add.
           rewrite dom_empty. rewrite cup_empty_r.
           rewrite filter_idempotent.
           eapply constant_cap_eval_step_empty; eauto.
           eapply partial_injective_shift_top_dim_reindexer_match; eauto.
           eapply partial_injective_cons_0; eauto. }
      erewrite partial_lookup_fold_left_array_add; eauto.
      2: { eapply partial_injective_cons_0; eauto. }
      2: { eapply no_dup_filter.
           eapply no_dup_mesh_grid. }
      2: { invert H. erewrite result_has_shape_result_shape_Z by eauto.
           eapply filter_In. propositional.
           repeat decomp_goal_index. eauto. }
      reflexivity.
    + rewrite lookup_array_add_r.
      2: { rewrite partial_dom_fold_left_array_add.
           rewrite dom_empty. rewrite cup_empty_r.
           rewrite filter_idempotent.
           rewrite <- In_iff_in.
           erewrite <- in_extract_Some.
           eapply in_map_iff. eexists (z-1::x)%Z. split.
           rewrite <- H2. f_equal. f_equal. lia.
           eapply filter_In. propositional.
           erewrite result_has_shape_result_shape_Z.
           2: { invert H.
                eapply forall_result_has_shape. eauto. reflexivity. }
           repeat decomp_goal_index.
           propositional. lia.
           eapply result_has_shape_length in H. invert H. simpl in *. lia.
           rewrite <- H4. simpl.
           cases (z-1)%Z; try lia.
           cases z; try lia.
           cases (Z.to_nat (Z.pos p)); try lia. simpl nth_error at 2.
           repeat f_equal. eq_match_discriminee. f_equal. lia.
           cases z; try lia.
           cases (Z.to_nat (Z.pos p0)); try lia. simpl nth_error at 2.
           repeat f_equal. eq_match_discriminee. f_equal. lia.
           eapply partial_injective_shift_top_dim_reindexer_match; eauto. }
      2: { repeat rewrite partial_dom_fold_left_array_add.
           repeat rewrite dom_empty.
           repeat rewrite cup_empty_r.
           repeat rewrite filter_idempotent.
           eapply constant_cap_eval_step_empty; eauto.
           eapply partial_injective_shift_top_dim_reindexer_match; eauto.
           eapply partial_injective_cons_0; eauto. }
      erewrite partial_lookup_fold_left_array_add with (index:=(z-1::x)%Z).
      2: { eapply partial_injective_shift_top_dim_reindexer_match; eauto. }
      2: { eapply no_dup_filter.
           eapply no_dup_mesh_grid. }
      2: { eapply filter_In. propositional.
           erewrite result_has_shape_result_shape_Z.
           2: { invert H.
                eapply forall_result_has_shape. eauto. reflexivity. }
           repeat decomp_goal_index.
           propositional. lia.
           invert H. simpl in *. lia.
           rewrite <- H4. simpl.
           cases (z-1)%Z; try lia.
           cases z; try lia.
           cases (Z.to_nat (Z.pos p)); try lia.
           simpl nth_error at 2.
           repeat f_equal. eq_match_discriminee. f_equal. lia.
           cases z; try lia.
           cases (Z.to_nat (Z.pos p0)); try lia.
           simpl nth_error at 2.
           repeat f_equal. eq_match_discriminee. f_equal. lia. }
      2: { rewrite <- H2. f_equal. f_equal. lia. }
      simpl.
      cases z; try lia.
      cases (Z.pos p -1)%Z; try lia.
      cases (Z.to_nat (Z.pos p)); try lia. simpl nth_error at 1.
      repeat f_equal. eq_match_discriminee. f_equal. lia.
      cases (Z.to_nat (Z.pos p)); try lia. simpl nth_error at 1.
      repeat f_equal. eq_match_discriminee. f_equal. lia.
  - (* Out of range *)
    rewrite None_dom_lookup.
    rewrite None_dom_lookup.
    reflexivity.
    + unfold not.
      rewrite dom_array_add.
      rewrite partial_dom_fold_left_array_add.
      rewrite partial_dom_fold_left_array_add.
      rewrite dom_empty. repeat rewrite cup_empty_r.
      rewrite union_constant. intros.
      rewrite <- In_iff_in in H1.
      eapply in_app_or in H1.
      propositional.
      * eapply H2.
        erewrite <- in_extract_Some in H3. invs.
        eapply in_map_iff in H3. invs.
        eapply in_map_iff. eexists. split. eassumption.
        eapply filter_In. propositional.
        erewrite result_has_shape_result_shape_Z by eauto.
        repeat decomp_goal_index. propositional. lia.
        invert H. lia.
        rewrite @filter_idempotent in *.
        repeat decomp_index.
        invert H. erewrite result_has_shape_result_shape_Z in H1 by eauto.
        repeat decomp_index.
        eauto.
        rewrite @filter_idempotent in *.
        repeat decomp_index.
        rewrite <- H5.
        reflexivity.
      * eapply H2.
        erewrite <- in_extract_Some in H3. 
        eapply in_map_iff in H3. invs.
        repeat decomp_index.
        erewrite result_has_shape_result_shape_Z in H4.
        2: { invert H. eapply forall_result_has_shape. eauto. reflexivity. }
        repeat decomp_index.
        eapply in_map_iff.
        eexists. split. eassumption.
        eapply filter_In.
        propositional.
        erewrite result_has_shape_result_shape_Z by eauto.
        repeat decomp_goal_index. propositional. lia.
        invert H. lia.
        rewrite <- H5. simpl.
        cases (z+1)%Z; try lia.
        cases z; try lia.
        cases (Z.to_nat (Z.pos p)); try lia. simpl nth_error at 1.
        repeat f_equal. eq_match_discriminee. f_equal. lia.
        cases (Z.to_nat (Z.pos p)); try lia. simpl nth_error at 1.
        repeat f_equal. eq_match_discriminee. f_equal. lia.
      * eapply partial_injective_shift_top_dim_reindexer_match; eauto.
      * eapply partial_injective_cons_0; eauto.
    + rewrite partial_dom_fold_left_array_add.
      rewrite dom_empty. repeat rewrite cup_empty_r.
      rewrite <- In_iff_in.
      rewrite filter_idempotent.
      rewrite <- in_extract_Some. auto.
      eauto.
Qed.

Lemma eq_tensor_to_array_delta_by_indices_shuffle :
  forall reindexer1 reindexer2 r1 r2 dom1 dom2 shuffle,
    (forall x, In x dom2 ->
               result_lookup_Z_option (shuffle x) r1 =
                 result_lookup_Z_option x r2) ->
    (forall x, In x dom2 ->
               reindexer1 (shuffle x) = reindexer2 x) ->
    (forall x, In x dom2 -> In (shuffle x) dom1) ->
    (forall x, In x dom1 -> exists y, shuffle y = x /\ In y dom2) ->
    partial_injective reindexer2 dom2 ->
    partial_injective reindexer1 dom1 ->
    injective dom2 shuffle ->    
    no_dup dom2 ->
    no_dup dom1 ->     
    tensor_to_array_delta_by_indices reindexer1 r1 dom1 =
      tensor_to_array_delta_by_indices reindexer2 r2 dom2.
Proof.
  intros ? ? ? ? ? ? ? Hlookup Hshuffle Hfor Hback Hinj2 Hinj1 Hinjshuf Hnd2
         Hnd1.
  unfold tensor_to_array_delta_by_indices.
  eapply fmap_ext. intros.
  pose proof (in_dec (option_eq_dec (Z.eq_dec))).
  specialize (H (Some k) (map reindexer2 dom2)).
  invert H.
  - eapply in_map_iff in H0. invs.
    symmetry.
    erewrite partial_lookup_fold_left_array_add; eauto.
    erewrite partial_lookup_fold_left_array_add; eauto.
    2: rewrite Hshuffle; auto.
    rewrite Hlookup; auto.
  - rewrite None_dom_lookup.
    rewrite None_dom_lookup.
    reflexivity.
    rewrite partial_dom_fold_left_array_add.
    rewrite dom_empty. rewrite cup_empty_r.
    rewrite <- In_iff_in. erewrite <- in_extract_Some.
    unfold not. intros. apply H0.
    erewrite in_map_iff in *. invs. decomp_index.
    eauto. eauto.
    rewrite partial_dom_fold_left_array_add.
    rewrite dom_empty. rewrite cup_empty_r.
    rewrite <- In_iff_in. erewrite <- in_extract_Some.
    unfold not. intros. apply H0.
    erewrite in_map_iff in *. invs. decomp_index.
    eapply Hback in H1. invs. eexists.
    rewrite <- Hshuffle. split. eassumption. auto. auto. auto.
Qed.

Lemma eq_tensor_to_array_delta_by_indices :
  forall f g r dom,
    (forall idx, In idx dom -> f idx = g idx) ->
    partial_injective f dom ->
    partial_injective g dom ->
    no_dup dom ->
    tensor_to_array_delta_by_indices f r dom =
      tensor_to_array_delta_by_indices g r dom .
Proof.
  unfold tensor_to_array_delta_by_indices. intros.
  eapply fmap_ext. intros.
  pose proof (option_eq_dec Z.eq_dec).
  pose proof (list_eq_dec H3).
  pose proof H0.
  pose proof (in_dec H3).
  specialize (H6 (Some k) (map f dom0)).
  invert H6.
  - eapply in_map_iff in H7. invs.
    erewrite partial_lookup_fold_left_array_add; eauto.
    erewrite partial_lookup_fold_left_array_add.
    reflexivity. eauto. eauto. eauto. erewrite <- H; eauto.
  - rewrite None_dom_lookup.
    rewrite None_dom_lookup.
    reflexivity.
    rewrite partial_dom_fold_left_array_add.
    rewrite dom_empty. rewrite cup_empty_r.
    pose proof H.
    eapply map_dom_eq in H6.
    erewrite <- In_iff_in.
    erewrite <- in_extract_Some.
    unfold not. intros.
    eapply H7.
    eapply in_map_iff in H8. invs.
    eapply in_map_iff.
    eapply filter_In in H10. invs.
    rewrite <- H in H8 by auto.
    eexists. split. eassumption. eauto. auto.
    rewrite partial_dom_fold_left_array_add.
    rewrite dom_empty. rewrite cup_empty_r.
    erewrite <- In_iff_in.
    erewrite <- in_extract_Some.
    unfold not. intros. apply H7.
    erewrite in_map_iff in *. invs.
    eapply filter_In in H9. invs.
    eexists. split. eauto. auto. auto.
Qed.

Lemma tensor_to_array_delta_empty_tensor :
  forall reindexer sh v,
  (tensor_to_array_delta
     (partial_interpret_reindexer reindexer sh v) (V [])) = $0.
Proof. reflexivity. Qed.

Lemma tensor_to_array_delta_cons :
  forall r0 v i lo hi reindexer,
    Z.to_nat (hi - lo) = Datatypes.S (Datatypes.length r0) ->
    forall r,
      result_has_shape (V (r::r0)) (result_shape_nat (V (r::r0))) ->
      partial_injective
           (partial_interpret_reindexer reindexer (result_shape_Z (V (r :: r0))) v)
           (filter
              (fun x : list Z =>
               negb (is_None (result_lookup_Z_option x (V (r :: r0)))))
              (mesh_grid (result_shape_Z (V (r :: r0))))) ->
           (forall l1 l2 : list (Zexpr * Z),
             eq_Z_tuple_index_list l1 l2 ->
             eq_Z_tuple_index_list (reindexer l1) (reindexer l2)) ->
               vars_of_reindexer (reindexer []) \subseteq dom v ->
             (forall (var : var) (k : Z) (l : list (Zexpr * Z)),
                 ~ var \in vars_of_reindexer (reindexer []) ->
                           map (subst_var_in_Z_tup var k) (reindexer l) =
                             reindexer (map (subst_var_in_Z_tup var k) l)) ->
             (forall l : list (Zexpr * Z),
                 vars_of_reindexer (reindexer l) =
                   vars_of_reindexer (reindexer []) \cup vars_of_reindexer l) ->
      ~ i \in dom v ->
      (forall var, contains_substring "?" var -> ~ var \in dom v) ->        
      ~ In i (shape_to_vars (result_shape_Z r)) ->
      array_add
        (tensor_to_array_delta
           (partial_interpret_reindexer
              (shift_top_dim_reindexer reindexer) (result_shape_Z (V r0)) v) 
           (V r0))
        (tensor_to_array_delta
           (partial_interpret_reindexer
              (fun l0 => reindexer
                           (((! i ! - | lo |)%z,
                              (hi - lo)%Z) :: l0))
              (result_shape_Z r)
              (v $+ (i, lo))) r) =
        tensor_to_array_delta (partial_interpret_reindexer
                                 reindexer (result_shape_Z (V (r :: r0))) v)
                              (V (r :: r0)).
Proof.
  intros ? ? ? ? ? ? ? ? ? Hinj HeqZlist Hvarsub Hmap Hvarsarg. intros.
  cases r0.
  { unfold tensor_to_array_delta at 1.
    unfold tensor_to_array_delta_by_indices at 1. simpl.
    rewrite array_add_empty_l.
    remember mesh_grid.
    simpl in *.
    subst.
    unfold tensor_to_array_delta.
    erewrite result_has_shape_result_shape_Z.
    2: { invert H0. eauto. }
    erewrite result_has_shape_result_shape_Z by eauto.
    simpl map.
    symmetry.
    eapply eq_tensor_to_array_delta_by_indices_shuffle
           with (shuffle:= fun x => (0::x)%Z).
    - intros. repeat decomp_index.
      reflexivity.
    - intros. repeat decomp_index.
      erewrite eq_partial_interpret_reindexer_eval_0 with (r0:=[]); eauto.
        simpl in *. lia. 
    - intros. repeat decomp_index.
      eapply filter_In. propositional.
      repeat decomp_goal_index.
      propositional. lia. lia.
      repeat decomp_goal_index.
      auto.
    - intros. repeat decomp_index.
      assert (z = 0)%Z by lia. subst.
      eexists. split. reflexivity.
      eapply filter_In. propositional.
      decomp_goal_index. auto.
    - replace (map Z.of_nat (filter_until (result_shape_nat r) 0))
        with (result_shape_Z r).
      2: { erewrite result_has_shape_result_shape_Z. reflexivity.
           invert H0. eauto. } About partial_injective_cons_reindexer.
      eapply partial_injective_cons_reindexer with (r0:=[]);
        try eapply H3; eauto.
      simpl in *. lia.
    - erewrite result_has_shape_result_shape_Z in Hinj.
      2: { eauto. }      
      eauto.
    - unfold injective. propositional.
      invert H7. auto.
    - eapply no_dup_filter.
      eapply no_dup_mesh_grid.
    - eapply no_dup_filter.
      eapply no_dup_mesh_grid. }      
  rewrite array_add_comm. symmetry.
  erewrite tensor_to_array_delta_cons_generic_indexer; eauto.
  symmetry.
  f_equal.
  - unfold tensor_to_array_delta.
    eapply eq_tensor_to_array_delta_by_indices.
    2: { eapply partial_injective_cons_reindexer; eauto.
         simpl in *. lia. }
    2: { eapply partial_injective_cons_0; eauto. }
    intros.

    erewrite result_has_shape_result_shape_Z at 1.
    2: { invert H0. eauto. }
    erewrite eq_partial_interpret_reindexer_eval_0.
    erewrite result_has_shape_result_shape_Z by eauto.
    reflexivity.
    eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    simpl in *. lia.
    eapply no_dup_filter.
    eapply no_dup_mesh_grid.
  - erewrite result_has_shape_result_shape_Z.
    2: { invert H0. eapply forall_result_has_shape. eauto. reflexivity. }
    unfold tensor_to_array_delta.
    eapply eq_tensor_to_array_delta_by_indices.
    intros.
    erewrite result_has_shape_result_shape_Z in H4.
    2: { eapply forall_result_has_shape. invert H0. eauto. reflexivity. }
    repeat decomp_index.
    erewrite eq_partial_interpret_reindexer_shift_top_dim_reindexer.
    erewrite result_has_shape_result_shape_Z by eauto.
    reflexivity. eauto.
    eauto. eauto. eauto. eauto. eauto. inversion 1.
    replace (map Z.of_nat
                 (filter_until
                    (length (r0 :: r1) :: result_shape_nat r) 0))
      with (result_shape_Z (V (r0 :: r1))).
    2: { erewrite result_has_shape_result_shape_Z.
         invert H0. reflexivity.
         eapply forall_result_has_shape. invert H0. eauto. auto. }
    eapply partial_injective_shift_top_dim_reindexer; eauto; try apply H3.
    inversion 1.
    eapply partial_injective_shift_top_dim_reindexer_match; eauto;
      try apply H3.
    eapply no_dup_filter.
    eapply no_dup_mesh_grid.
Qed.
 
Lemma tensor_to_array_delta_add_valuation :
  forall reindexer sh r v i loz0,
    ~ i \in dom v ->
    ~ contains_substring "?" i ->
    result_has_shape r sh ->
    partial_injective 
      (partial_interpret_reindexer reindexer (result_shape_Z r)
                           (v $+ (i, loz0)))
      (filter
         (fun x => negb (is_None (result_lookup_Z_option x r)))
         (mesh_grid (result_shape_Z r))) ->
       (forall (var : var) (k : Z) (l : list (Zexpr * Z)),
           ~ var \in vars_of_reindexer (reindexer []) ->
                     map (subst_var_in_Z_tup var k) (reindexer l) =
                       reindexer (map (subst_var_in_Z_tup var k) l)) ->
       vars_of_reindexer (reindexer []) \subseteq dom v ->
       (tensor_to_array_delta         
          (partial_interpret_reindexer reindexer
                               (result_shape_Z r) (v $+ (i, loz0))) r) =
         (tensor_to_array_delta         
            (partial_interpret_reindexer reindexer (result_shape_Z r) v) r).
Proof.
  unfold tensor_to_array_delta. intros.
  erewrite result_has_shape_result_shape_Z by eauto.
  eapply eq_tensor_to_array_delta_by_indices.
  - intros.
    unfold partial_interpret_reindexer.
    decomp_index.
    rewrite partially_eval_Z_tup_add_partial by auto.
    replace (fun e : Zexpr * Z =>
               subst_var_in_Z_tup i loz0 (partially_eval_Z_tup v e)) with
      (fun e : Zexpr * Z =>
         partially_eval_Z_tup v  (subst_var_in_Z_tup i loz0 e)).
    2: { eapply functional_extensionality. intros.
         erewrite subst_var_in_Z_tup_partially_eval_Z_tup_comm; auto. }
    rewrite <- map_map.
    rewrite H3.
    2: { unfold not. intros.
         eapply H. eapply H4. eauto. }
    unfold shape_to_index.
    rewrite map_subst_var_in_Z_tup_combine_not_in.
    2: { unfold not. intros.
         eapply H0. eapply shape_to_vars_contains_substring. eauto. }
    reflexivity.
  - unfold partial_injective in *. propositional.
    erewrite result_has_shape_result_shape_Z in H2.
    eapply H2; eauto. eauto.
  - unfold partial_injective in *. propositional.
    erewrite result_has_shape_result_shape_Z in H2 by eauto.
    unfold partial_interpret_reindexer in *.
    decomp_index.
    rewrite partially_eval_Z_tup_add_partial in * by auto.
    replace (fun e : Zexpr * Z =>
               subst_var_in_Z_tup i loz0 (partially_eval_Z_tup v e)) with
      (fun e : Zexpr * Z =>
         partially_eval_Z_tup v  (subst_var_in_Z_tup i loz0 e)) in *.
    2: { eapply functional_extensionality. intros.
         erewrite subst_var_in_Z_tup_partially_eval_Z_tup_comm; auto. }
    rewrite <- map_map with (f:=subst_var_in_Z_tup i loz0) in *.
    rewrite H3 in *.
    2: { unfold not. intros.
         eapply H. eapply H4. eauto. }
    unfold shape_to_index in *.
    rewrite map_subst_var_in_Z_tup_combine_not_in in *.
    2: { unfold not. intros.
         eapply H0. eapply shape_to_vars_contains_substring. eauto. }
    eapply H2.
    auto.
    eapply filter_In. propositional.
    apply H7.
  - eapply no_dup_filter.
    eapply no_dup_mesh_grid.
Qed.

Lemma tensor_to_array_delta_shift_match :
  forall reindexer v xs1 x1,
    partial_injective
      (partial_interpret_reindexer reindexer (result_shape_Z (V (x1 :: xs1))) v)
      (filter
         (fun x : list Z =>
            negb (is_None (result_lookup_Z_option x (V (x1 :: xs1)))))
         (mesh_grid (result_shape_Z (V (x1 :: xs1))))) ->
    (forall l1 l2 : list (Zexpr * Z),
        eq_Z_tuple_index_list l1 l2 ->
             eq_Z_tuple_index_list (reindexer l1) (reindexer l2)) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall (var : var) (k : Z) (l : list (Zexpr * Z)),
        ~ var \in vars_of_reindexer (reindexer []) ->
                  map (subst_var_in_Z_tup var k) (reindexer l) =
                    reindexer (map (subst_var_in_Z_tup var k) l)) ->
           (forall l : list (Zexpr * Z),
               vars_of_reindexer (reindexer l) =
                 vars_of_reindexer (reindexer []) \cup vars_of_reindexer l) ->
           (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
           result_has_shape (V (x1::xs1)) (result_shape_nat (V (x1::xs1))) ->
           tensor_to_array_delta
             (fun index : list Z =>
         match index with
         | [] =>
             partial_interpret_reindexer
               reindexer (result_shape_Z (V (x1 :: xs1))) v index
        | x :: xs =>
            partial_interpret_reindexer
              reindexer (result_shape_Z (V (x1 :: xs1))) v
              ((x + 1)%Z :: xs)
         end) (V xs1)
    = tensor_to_array_delta
      (partial_interpret_reindexer (shift_top_dim_reindexer reindexer)
                                   (result_shape_Z (V xs1)) v) (V xs1).
Proof.
  unfold tensor_to_array_delta.
  intros ? ? ? ?.
  intros Hinj HeqZlist Hvarsub Hmap Hvarsarg. intros.
  eapply eq_tensor_to_array_delta_by_indices; eauto with reindexers.
  intros. erewrite result_has_shape_result_shape_Z in H1.
  2: { eapply forall_result_has_shape. invert H0. eauto. eauto. }
  repeat decomp_index.
  erewrite result_has_shape_result_shape_Z by eauto.
  erewrite result_has_shape_result_shape_Z.
  2: { eapply forall_result_has_shape. invert H0. eauto. eauto. }
  unfold partial_interpret_reindexer. unfold shift_top_dim_reindexer.
  unfold shape_to_vars. simpl.
  cases (xs1). simpl in *. lia.
  simpl.  
  rewrite shape_to_index_cons.
  repeat rewrite index_to_partial_function_vars_cons; eauto with reindexers.
  rewrite Hmap; eauto with reindexers.
  rewrite Hmap; eauto with reindexers.
  simpl.

  rewrite map_subst_var_in_Z_tup_combine_not_in; eauto with reindexers.
  unfold shape_to_index.
  rewrite map_subst_var_in_Z_tup_combine_not_in; eauto with reindexers.
  unfold subst_var_in_Z_tup. simpl.
  assert (result_shape_nat r = result_shape_nat x1).
  invert H0. invert H10.
  symmetry.
  erewrite result_has_shape_result_shape_nat; eauto. symmetry.
  erewrite result_has_shape_result_shape_nat; eauto.
  erewrite eq_index_to_partial_function. reflexivity.

  eapply eq_Z_tuple_index_list_partially_eval_Z_tup.
  eapply HeqZlist.
  erewrite <- eq_Z_tuple_index_list_cons_tup.
  split.
  eapply eq_zexpr_comm. eapply eq_zexpr_add_literal.
  split. lia.
  eapply eq_Z_tuple_index_list_id.
  eapply partial_injective_shift_top_dim_reindexer_match. apply Hinj. eauto.
  cases xs1. simpl. unfold partial_injective. propositional. invert H2.
  eapply partial_injective_shift_top_dim_reindexer; eauto; try apply H.
  inversion 1.
  eapply no_dup_filter. eapply no_dup_mesh_grid.
Qed.

Lemma tensor_to_array_delta_cons0 : forall reindexer x1 xs1 v,
    partial_injective
           (partial_interpret_reindexer reindexer (result_shape_Z (V (x1 :: xs1))) v)
           (filter
              (fun x : list Z =>
               negb (is_None (result_lookup_Z_option x (V (x1 :: xs1)))))
              (mesh_grid (result_shape_Z (V (x1 :: xs1))))) ->
(forall l1 l2 : list (Zexpr * Z),
             eq_Z_tuple_index_list l1 l2 ->
             eq_Z_tuple_index_list (reindexer l1) (reindexer l2)) ->
               vars_of_reindexer (reindexer []) \subseteq dom v ->
  (forall (var : var) (k : Z) (l : list (Zexpr * Z)),
         ~ var \in vars_of_reindexer (reindexer []) ->
         map (subst_var_in_Z_tup var k) (reindexer l) =
         reindexer (map (subst_var_in_Z_tup var k) l)) ->
  (forall l : list (Zexpr * Z),
      vars_of_reindexer (reindexer l) =
        vars_of_reindexer (reindexer []) \cup vars_of_reindexer l) ->

               (forall var, contains_substring "?" var -> ~ var \in dom v) ->
    result_has_shape (V (x1 :: xs1)) (result_shape_nat (V (x1 :: xs1))) ->
    tensor_to_array_delta
      (fun index : list Z =>
         partial_interpret_reindexer
           reindexer (result_shape_Z (V (x1 :: xs1))) v (0%Z :: index)) x1 =
      tensor_to_array_delta
        (partial_interpret_reindexer
           (fun l =>
              reindexer (((|0|, Z.of_nat (length (x1::xs1)))%z)::l))
           (result_shape_Z x1) v) x1.
Proof.
  intros ? ? ? ?.
  intros Hinj HeqZlist Hvarsub Hmap Hvarsarg. intros.
  
  unfold tensor_to_array_delta.
  eapply eq_tensor_to_array_delta_by_indices. intros.
  unfold partial_interpret_reindexer.
  unfold result_shape_Z. simpl.
  posnats.
  unfold shape_to_vars. simpl. rewrite shape_to_index_cons.
  rewrite index_to_partial_function_vars_cons by eauto with reindexers.
  unfold nat_range. repeat rewrite length_map.
  rewrite Hmap by (eapply not_var_generation_in_index; eauto).
  rewrite map_cons.
  unfold subst_var_in_Z_tup at 1. simpl. posnats.
  rewrite map_subst_var_in_Zexpr_shape_to_index_id.
  rewrite index_to_partial_function_subst_vars.
  2: { eapply forall_map_not_in_dom. apply H. }
  symmetry.
  rewrite index_to_partial_function_subst_vars.
  2: { eapply forall_map_not_in_dom. apply H. }
  symmetry.
  erewrite map_fold_left_subst_var_in_Z_tup_reindexer
    by eauto with reindexers.
  rewrite map_cons.
  rewrite fold_left_subst_var_in_Z_tup_ZLit.
  rewrite map_fold_left_subst_var_in_Z_tup_shape_to_index.
  erewrite map_fold_left_subst_var_in_Z_tup_reindexer
    by eauto with reindexers.
  rewrite map_cons.
  rewrite fold_left_subst_var_in_Z_tup_ZLit.
  rewrite map_fold_left_subst_var_in_Z_tup_shape_to_index.
  reflexivity.
  rewrite length_map. rewrite length_nat_range_rec.
  eapply length_mesh_grid_indices. decomp_index. auto.
  eapply no_dup_var_generation.
  rewrite length_map. rewrite length_nat_range_rec.
  eapply length_mesh_grid_indices. decomp_index. auto.
  eapply no_dup_var_generation.
  rewrite length_map. rewrite length_nat_range_rec.
  eapply length_mesh_grid_indices. decomp_index. auto.
  rewrite length_map. rewrite length_nat_range_rec.
  eapply length_mesh_grid_indices. decomp_index. auto.
  eapply not_In_var_map. lia.
  eapply partial_injective_cons_0. apply Hinj.
  eapply partial_injective_eval_cons0; try eapply Hinj; eauto.  
  eapply no_dup_filter.
  eapply no_dup_mesh_grid.
Qed.

Lemma tensor_to_array_delta_gen_pad : forall f sh,
    tensor_to_array_delta f (gen_pad sh) = $0.
Proof.
  propositional. unfold tensor_to_array_delta.
  replace (fun x => negb (is_None (result_lookup_Z_option x (gen_pad sh))))
    with (fun x : list Z => false).
  2: { eapply functional_extensionality. intros.
       rewrite result_lookup_Z_option_gen_pad.
       reflexivity. }
  rewrite filter_false_empty.
  unfold tensor_to_array_delta_by_indices. reflexivity.
Qed.

Lemma tensor_to_array_delta_id_valuation :
  forall sh v,
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    (partial_interpret_reindexer (fun l : list (Zexpr * Z) => l)
                                 sh v)
    =
    (partial_interpret_reindexer (fun l : list (Zexpr * Z) => l)
       sh $0).
Proof.
  unfold interpret_reindexer.
  intros.
  unfold partial_interpret_reindexer.
  erewrite eq_index_to_partial_function.
  reflexivity.
  rewrite partially_eval_Z_tup_empty_id. rewrite map_id.
  rewrite map_partially_eval_Z_tup_shape_to_index; auto.
  eapply eq_Z_tuple_index_list_id.
Qed.  
  
Lemma array_add_tensor_to_array_delta_concat :
  forall r1 r2 f g x1 x2 xs,
    constant (extract_Some (map f (filter
                         (fun x0 =>
                            negb (is_None (result_lookup_Z_option x0 (V r1))))
                         (mesh_grid (result_shape_Z (V r1)))))) \cap
             constant (extract_Some (map g (filter
                         (fun x0 =>
                            negb (is_None (result_lookup_Z_option x0 (V r2))))
                         (mesh_grid (result_shape_Z (V r2)))))) =
      constant [] ->
    result_has_shape (V r1) (x1::xs) ->
    result_has_shape (V r2) (x2::xs) ->
    partial_injective f
                      (filter
                         (fun x0 =>
                            negb (is_None (result_lookup_Z_option x0 (V r1))))
                         (mesh_grid (result_shape_Z (V r1)))) ->
    partial_injective g
                      (filter
                         (fun x0 =>
                            negb (is_None (result_lookup_Z_option x0 (V r2))))
                         (mesh_grid (result_shape_Z (V r2)))) ->
    array_add (tensor_to_array_delta f (V r1))
              (tensor_to_array_delta g (V r2)) =
      tensor_to_array_delta
        (fun i => match i with
                  | x::xs => if (x <? Z.of_nat (length r1))%Z
                             then f (x::xs)
                             else g (x-Z.of_nat (length r1)::xs)%Z
                  | _ => None
                  end) (V (r1++r2)).
Proof.
  intros. unfold result_shape_Z in *.
  erewrite result_has_shape_result_shape_nat in * by eassumption.
  erewrite result_has_shape_result_shape_nat in * by eassumption.
  unfold tensor_to_array_delta.
  symmetry. unfold tensor_to_array_delta_by_indices. 
  erewrite result_has_shape_result_shape_Z.
  2: { eapply result_has_shape_concat; eassumption. }
  erewrite result_has_shape_length by eassumption.
  simpl in *.
  cases (x1 =? 0)%nat.
  - eapply Nat.eqb_eq in Heq. subst.
    invert H0. simpl in *. rewrite array_add_empty_l.
    cases (x2=?0)%nat.
    + eapply Nat.eqb_eq in Heq. subst. invert H1. simpl in *. reflexivity.
    + eapply Nat.eqb_neq in Heq. cases x2. lia.
      invert H1. clear H.
      erewrite result_has_shape_result_shape_Z.
      2: { econstructor; eauto. }
      eapply fold_left_extensionality.
      intros.
      repeat decomp_index.
      simpl map in *.
      invert H.
      eapply Z.ltb_ge in H0. rewrite H0. rewrite Z.sub_0_r. reflexivity.
  - cases (x2=?0)%nat.
    + eapply Nat.eqb_eq in Heq0.
      subst. invert H1. simpl. rewrite app_nil_r. rewrite array_add_empty_r.
      eapply Nat.eqb_neq in Heq.
      cases x1. lia. simpl map. rewrite add_0_r. posnats.
      invert H0.
      erewrite result_has_shape_result_shape_Z.
      2: { econstructor; eauto. }
      eapply fold_left_extensionality.
      intros. simpl map in *.
      repeat decomp_index. invert H0.
      eapply Z.ltb_lt in H6. posnats. rewrite H6.
      reflexivity.
    + eapply Nat.eqb_neq in Heq0,Heq.
      cases x1; cases x2; try lia.
      simpl (map Z.of_nat _).
      clear Heq. clear Heq0.
      posnats.
      rewrite <- add_succ_l.
      rewrite Nat2Z.inj_add.
      erewrite mesh_grid_app; try eassumption; try lia.
      eapply fmap_ext. intros. symmetry.
      cases r1. invert H0.
      cases r2. invert H1.
      simpl (map Z.of_nat _). posnats.
      cases ((fold_left
       (fun (arr : array) (index : list Z) =>
        match f index with
        | Some z =>
            match result_lookup_Z_option index (V (r :: r1)) with
            | Some val => array_add arr ($0 $+ (z, val))
            | None => arr
            end
        | None => arr
        end)
       (filter
          (fun x => negb (is_None (result_lookup_Z_option x (V (r :: r1)))))
          (mesh_grid (result_shape_Z (V (r :: r1))))) $0) $? k).
      * erewrite lookup_array_add_l. rewrite Heq.
        2: { eapply lookup_Some_dom in Heq. eauto. }
        2: { repeat rewrite partial_dom_fold_left_array_add.
             - rewrite dom_empty. repeat rewrite cup_empty_r.
               rewrite @filter_idempotent in *.
               rewrite @filter_idempotent in *.
               erewrite result_has_shape_result_shape_Z by eauto.
               erewrite result_has_shape_result_shape_Z by eauto.
               auto.
             - erewrite result_has_shape_result_shape_Z by eauto.
               eauto.
             - erewrite result_has_shape_result_shape_Z by eauto.
               eauto. }
        pose proof Heq.
        eapply lookup_Some_dom in Heq.
        rewrite partial_dom_fold_left_array_add in Heq.
        rewrite dom_empty in *. rewrite @cup_empty_r in *.
        erewrite <- @In_iff_in in Heq.
        erewrite <- in_extract_Some in Heq.
        eapply in_map_iff in Heq. invs.
        rewrite map_cons in *.
        rewrite @filter_idempotent in *.
        erewrite partial_lookup_fold_left_array_add
          with (f:= fun x =>
                      match x with
                      | [] => None
                      | x0 :: xs0 =>
                          if (x0 <? Z.of_nat (Datatypes.S x1))%Z
                          then f (x0 :: xs0)
                          else g ((x0 - Z.of_nat (Datatypes.S x1))%Z :: xs0)
                      end)
               (index:=x).
        5: { rewrite <- H6.
             erewrite result_has_shape_result_shape_Z in * by eauto.
             repeat decomp_index.
             invert H7. eapply Z.ltb_lt in H10. posnats.
             rewrite H10. reflexivity. }
        3: { eapply no_dup_filter.
             eapply no_dup_app.
             eapply no_dup_mesh_grid.
             eapply no_dup_injective_map.
             unfold injective. propositional.
             repeat decomp_index. invert H10. f_equal. lia.
             eapply no_dup_mesh_grid.
             eapply Forall_forall. intros.
             erewrite in_map_iff in H5. invs.
             repeat decomp_index.
             unfold not. intros.
             repeat decomp_index.
             lia. }
        3: { eapply filter_In. propositional.
             repeat decomp_index.             
             erewrite result_has_shape_result_shape_Z in H5 by eauto.
             repeat decomp_index.
             eapply in_or_app. left.
             repeat decomp_goal_index. propositional.
             repeat decomp_goal_index. auto.
             repeat decomp_index.
             rewrite <- H8.
             erewrite result_has_shape_result_shape_Z in H5; eauto.
             repeat decomp_index.
             simpl.
             rewrite app_comm_cons.
             rewrite nth_error_app1.
             reflexivity.
             erewrite result_has_shape_length by eauto. lia. }
        3: { erewrite result_has_shape_result_shape_Z by eauto. auto. }
        erewrite result_has_shape_result_shape_Z in H7 by eauto.
        repeat decomp_index.
        erewrite partial_lookup_fold_left_array_add with
          (index:=(z::x)) in H4.
        rewrite <- H4.
        simpl. rewrite app_comm_cons.
        rewrite nth_error_app1. reflexivity.
        erewrite result_has_shape_length by eauto. lia.
        erewrite result_has_shape_result_shape_Z by eauto.
        auto.
        eapply no_dup_filter. eapply no_dup_mesh_grid.
        eapply filter_In. propositional.
        erewrite result_has_shape_result_shape_Z by eauto.
        repeat decomp_goal_index.  propositional.
        eauto.
        eapply partial_injective_concat; eauto.
      * cases ((fold_left
       (fun (arr : array) (index : list Z) =>
        match g index with
        | Some z =>
            match result_lookup_Z_option index (V (r0 :: r2)) with
            | Some val => array_add arr ($0 $+ (z, val))
            | None => arr
            end
        | None => arr
        end)
       (filter
          (fun x : list Z =>
           negb (is_None (result_lookup_Z_option x (V (r0 :: r2)))))
          (mesh_grid (result_shape_Z (V (r0 :: r2))))) $0) $? k).
        -- rewrite lookup_array_add_r. rewrite Heq0.
           pose proof Heq0. eapply lookup_Some_dom in H4.
           rewrite partial_dom_fold_left_array_add in H4.
           2: { erewrite result_has_shape_result_shape_Z by eauto.
                eauto. }
           2: { eapply lookup_Some_dom in Heq0. auto. }
           2: { repeat rewrite partial_dom_fold_left_array_add.
                rewrite dom_empty. repeat rewrite cup_empty_r.
                rewrite @filter_idempotent.
                rewrite @filter_idempotent.
                erewrite result_has_shape_result_shape_Z by eauto.
                erewrite result_has_shape_result_shape_Z by eauto.
                eauto.
                erewrite result_has_shape_result_shape_Z by eauto.
                eauto.
                erewrite result_has_shape_result_shape_Z by eauto.
                eauto. }
           rewrite dom_empty in *.
           rewrite @cup_empty_r in *.
           rewrite <- In_iff_in in H4.
           rewrite <- in_extract_Some in H4.
           eapply in_map_iff in H4. invs.
           rewrite @filter_idempotent in *.
           erewrite partial_lookup_fold_left_array_add in Heq0; eauto.
           2: { erewrite result_has_shape_result_shape_Z by eauto. eauto. }
           2: { eapply no_dup_filter. eapply no_dup_mesh_grid. }
           erewrite result_has_shape_result_shape_Z in * by eauto.
           repeat decomp_index.
           erewrite partial_lookup_fold_left_array_add
             with (f:= fun x =>
                         match x with
                         | [] => None
                         | x0 :: xs0 =>
                             if (x0 <? Z.of_nat (Datatypes.S x1))%Z
                             then f (x0 :: xs0)
                             else g ((x0 -
                                        Z.of_nat (Datatypes.S x1))%Z :: xs0)
                         end)
                  (index:=(z+Z.of_nat (Datatypes.S x1))%Z::x).
           rewrite <- Heq0.
           simpl. rewrite app_comm_cons.
           rewrite nth_error_app2.
           cases z; try lia.
           simpl Z.add. symmetry.
           eq_match_discriminee.
           f_equal. invert H0. simpl. lia.
           cases (Z.pos p + Z.pos (Pos.of_succ_nat x1))%Z ; try lia.
           eq_match_discriminee.
           f_equal. invert H0. simpl. lia.
           erewrite result_has_shape_length by eauto. lia.
           eapply partial_injective_concat; eauto.
           eapply no_dup_filter.
           eapply no_dup_app.
           eapply no_dup_mesh_grid.
           eapply no_dup_injective_map.
           unfold injective. propositional.
           repeat decomp_index. invert H12. f_equal. lia.
           eapply no_dup_mesh_grid.
           eapply Forall_forall. intros.
           unfold not. intros.
           repeat decomp_index. eapply in_map_iff in H5. invs.
           repeat decomp_index. invert H5. lia.
           eapply filter_In. propositional.
           eapply in_or_app. right.
           eapply in_map_iff. eexists (z::x).
           propositional.
           repeat decomp_goal_index. propositional.
           decomp_goal_index. auto.
           rewrite <- H7.
           simpl.
           cases z; try lia.
           simpl is_None at 1.
           repeat f_equal. eq_match_discriminee.
           rewrite app_comm_cons.
           rewrite nth_error_app2.
           f_equal. invert H0. simpl. lia.
           invert H0. simpl. lia.
           cases (Z.pos p + Z.pos (Pos.of_succ_nat x1))%Z; try lia.
           repeat f_equal.
           rewrite app_comm_cons. rewrite nth_error_app2.
           eq_match_discriminee. f_equal. invert H0. simpl. lia.
           invert H0. simpl. lia.
           rewrite <- H4.
           cases (z + Z.of_nat(Datatypes.S x1) <? Z.of_nat(Datatypes.S x1))%Z.
           eapply Z.ltb_lt in Heq1. lia.
           f_equal. f_equal. lia.
        -- rewrite None_dom_lookup.
           2: { rewrite dom_array_add.
                eapply lookup_None_dom in Heq,Heq0. sets. }
           rewrite None_dom_lookup. reflexivity.
           rewrite partial_dom_fold_left_array_add.
           rewrite dom_empty. rewrite cup_empty_r.
           rewrite filter_idempotent.
           eapply lookup_None_dom in Heq,Heq0.
           rewrite partial_dom_fold_left_array_add in Heq,Heq0.
           rewrite dom_empty in *.
           rewrite @cup_empty_r in *.
           rewrite <- In_iff_in in *.
           rewrite <- in_extract_Some in *.
           unfold not. intros.
           rewrite in_map_iff in *. invs.
           repeat decomp_index.
           eapply in_app_or in H5. invert H5.
           ++ eapply Heq.
              repeat decomp_index.
              invert H5. pose proof H9.
              eapply Z.ltb_lt in H9. rewrite H9 in H4.
              eexists. split. eassumption.
              rewrite filter_idempotent.
              eapply filter_In. propositional.
              erewrite result_has_shape_result_shape_Z by eauto.
              repeat decomp_goal_index.
              propositional.
              rewrite <- H7.
              simpl. rewrite app_comm_cons.
              rewrite nth_error_app1. reflexivity.
              erewrite result_has_shape_length by eauto. lia.
           ++ eapply Heq0.
              eapply in_map_iff in H6. invs.
              repeat decomp_index.
              rewrite filter_idempotent.
              cases (z + Z.of_nat (Datatypes.S x1) <?
                       Z.of_nat (Datatypes.S x1))%Z.
              eapply Z.ltb_lt in Heq1. lia.
              rewrite <- H4. eexists. split. reflexivity.
              eapply filter_In. propositional.
              erewrite result_has_shape_result_shape_Z by eauto.
              repeat decomp_goal_index. propositional. lia. lia.
              rewrite <- H7.
              simpl.
              rewrite app_comm_cons.
              rewrite nth_error_app2.
              rewrite Z.add_simpl_r.
              cases z; try lia.
              simpl is_None at 2.
              repeat f_equal. eq_match_discriminee. f_equal.
              invert H0. lia.
              cases (Z.pos p + Z.pos (Pos.of_succ_nat x1))%Z; try lia.
              repeat f_equal. eq_match_discriminee. f_equal.
              invert H0. simpl. lia.
              invert H0. simpl. lia.
           ++ erewrite result_has_shape_result_shape_Z by eauto. eauto.
           ++ erewrite result_has_shape_result_shape_Z by eauto. eauto.
           ++ eapply partial_injective_concat; eauto.
Qed.

Lemma tensor_to_array_delta_partial_interpret_reindexer_flatten :
  forall rs,
    tensor_to_array_delta
      (partial_interpret_reindexer
         (fun l0 => l0)
         (result_shape_Z (V rs)) $0) 
      (V rs) =
      tensor_to_array_delta
        (fun args =>
           Some (flatten
                   (result_shape_Z (V rs)) args)) 
        (V rs).
Proof.
  intros.
  unfold tensor_to_array_delta.
  eapply eq_tensor_to_array_delta_by_indices.
  intros.
  cases rs.
  { simpl in *. propositional. }
  unfold result_shape_Z in *. simpl map in *.
  repeat decomp_index.
  rewrite partial_interpret_reindexer_id_flatten. reflexivity.
  repeat decomp_goal_index.
  propositional. rewrite dom_empty. intros. sets.
  eapply partial_injective_id_reindexer. rewrite dom_empty. sets.
  unfold partial_injective. propositional.
  unfold result_shape_Z in *. simpl map in *.
  cases rs. simpl in *. propositional. invs.
  repeat decomp_index.
  eapply injective_flatten in H3.
  propositional. posnats. auto. posnats. auto.
  eapply no_dup_filter. eapply no_dup_mesh_grid.
Qed.

Lemma result_lookup_Z_tensor_to_array_delta :
  forall rs x2 f,
    result_has_shape (V rs) (result_shape_nat (V rs)) ->
    In x2 (mesh_grid (result_shape_Z (V rs))) ->
    injective (mesh_grid (result_shape_Z (V rs))) f ->
  tensor_to_array_delta
    (fun args : list Z => Some (f args)) 
    (V rs) $? f x2 =
    result_lookup_Z_option x2 (V rs).
Proof.
  intros. unfold tensor_to_array_delta.
  unfold tensor_to_array_delta_by_indices.
  pose proof (in_dec (list_eq_dec Z.eq_dec)).
  cases (result_lookup_Z_option x2 (V rs)).
  - erewrite partial_lookup_fold_left_array_add with
      (f:= fun x => Some (f x)).
    eassumption.
    unfold partial_injective. propositional.
    invert H5.
    unfold injective in *.
    repeat decomp_index. 
    specialize (H1 args1 args2). 
    propositional.
    eapply no_dup_filter.
    eapply no_dup_mesh_grid.
    eapply filter_In. rewrite Heq. auto. reflexivity.
  - rewrite None_dom_lookup. auto.
    erewrite partial_dom_fold_left_array_add with
      (f:= fun x => Some (f x)).
    rewrite filter_idempotent.
    rewrite dom_empty. rewrite cup_empty_r.
    rewrite <- In_iff_in.
    rewrite <- in_extract_Some.
    rewrite in_map_iff.
    unfold not. intros. invs.
    repeat decomp_index.
    unfold injective in *.
    specialize (H1 x x2). propositional. subst.
    rewrite Heq in *. simpl in *. discriminate.
    unfold partial_injective. propositional.
    invert H5.
    unfold injective in *.
    repeat decomp_index. 
    specialize (H1 args1 args2). 
    propositional.
Qed.

Lemma size_of_eval_expr_result_has_shape :
  forall e sz,
    size_of e sz ->
    forall v sh ec r,
      eval_expr sh v ec e r ->
      result_has_shape r sz.
Proof.
  intros e. induct e; intros; simpl in *.
  - (* GEN *) invs. invert H0.
    + (* EMPTY GEN *)
      eapply eval_Zexpr_includes_valuation in H7, H8; try apply empty_includes.
      eapply eval_Zexpr_Z_eval_Zexpr in H8,H7.
      rewrite H7, H8 in *. invs.
      replace (Z.to_nat (hiz0 - loz0)) with 0 by lia. constructor.
    + (* STEP GEN *)
      eapply eval_Zexpr_includes_valuation in H7, H8; try apply empty_includes.
      eapply eval_Zexpr_Z_eval_Zexpr in H8,H7.
      rewrite H7, H8 in *. invs.
      simpl. cases (Z.to_nat (hiz0-loz0)%Z). lia.
      econstructor. erewrite length_eval_expr_gen.
      2: { eassumption. }
      2: { simpl. rewrite H7,H8. eauto. }
      lia.
      clear Heq. clear n.
      eapply IHe. eauto. eassumption.
      pose proof (eval_expr_for_gen_result_has_shape
                    n sh v ec i (lo+|1|)%z hi (loz0+1) hiz0 e l).
      assert (eval_Zexpr_Z v (lo + | 1 |)%z = Some (loz0+1)%Z).
      simpl. eapply eval_Zexpr_Z_eval_Zexpr in H8. rewrite H7. eauto.
      assert ((hiz0 - (loz0 + 1))%Z = Z.of_nat n). lia.
      specialize (H ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
      eapply Forall_forall. intros.
      eapply In_nth with (d:= S (SS 0)) in H2. invs.
      eapply IHe. eauto.
      eapply H. eapply length_eval_expr_gen in H16; eauto.
      2: { simpl. rewrite H7,H8. reflexivity. }
      lia.
  - (* SUM *)
    invert H. invert H0.
    + (* STEP SUM *)
      eapply result_has_shape_add_result.
      eassumption.
      eapply IHe. 2: eassumption. propositional.
      eapply result_has_shape_for_sum.
      eapply IHe. propositional.
      4: eassumption. simpl. rewrite H4. reflexivity.
      eassumption. rewrite Z2Nat.id. reflexivity. lia.
    + (* EMPTY SUM *)
      eq_size_of. eq_eval_Zlist.
      eapply result_has_shape_gen_pad.
  - invs. invert H0.
    eq_size_of.
    apply result_has_shape_gen_pad.
    eauto.
  - invs. invert H0.
    + eauto.
    + eauto.
  - invs. invert H0. eauto using result_has_shape_concat.
  - invs. invert H0. eauto using result_has_shape_flatten.
  - invs. invert H0.
    apply eval_Zexpr_Z_eval_Zexpr in H4. rewrite H4 in *. invs.
    eapply result_has_shape_split_result. lia. eauto.
  - invs. invert H0.
    simpl.
    eq_size_of. invert H.
    eapply result_has_shape_transpose_result.
    repeat rewrite <- map_cons.
    eapply IHe; eauto.
  - invs. invert H0.
    eapply result_has_shape_rev.
    eapply eval_Zexpr_includes_valuation in H4; try apply empty_includes.
    eapply eval_Zexpr_Z_eval_Zexpr in H4. rewrite H2 in H4. invs.
    eapply result_has_shape_truncl_list.
    eapply result_has_shape_rev.
    erewrite <- result_has_shape_filter_until_0.
    eapply IHe; eauto.
  - invs. invert H0.
    eapply eval_Zexpr_includes_valuation in H4; try apply empty_includes.
    eapply eval_Zexpr_Z_eval_Zexpr in H4. rewrite H2 in H4. invs.
    eapply result_has_shape_truncl_list.
    erewrite <- result_has_shape_filter_until_0.
    eapply IHe; eauto.
  - invs. invert H0.
    eq_size_of. invert H.
    eapply eval_Zexpr_includes_valuation in H5; try apply empty_includes.
    eapply eval_Zexpr_Z_eval_Zexpr in H5. rewrite H2 in H5. invs.
    eapply result_has_shape_concat.
    eapply IHe; eauto.
    eapply result_has_shape_repeat_gen_pad.
  - invs. invert H0.
    eq_size_of. invert H.
    eapply eval_Zexpr_includes_valuation in H5; try apply empty_includes.
    eapply eval_Zexpr_Z_eval_Zexpr in H5. rewrite H2 in H5. invs.
    rewrite Nat.add_comm.
    eapply result_has_shape_concat.
    eapply result_has_shape_repeat_gen_pad.
    eapply IHe; eauto.
  - invs. invert H0. econstructor.
Qed.

