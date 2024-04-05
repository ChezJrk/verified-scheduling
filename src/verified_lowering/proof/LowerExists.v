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

Set Warnings "-deprecate-hint-without-locality,-deprecated".
Import ListNotations.

From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.
From Lower Require Import
     Zexpr Bexpr Array Range Sexpr Result ListMisc Meshgrid VarGeneration
     Injective Constant InterpretReindexer AssignNoOverwrite
     WellFormedEnvironment WellFormedReindexer WellFormedAllocation
     ResultToArrayDelta ContextsAgree Pad ATLDeep LowerCorrect.

Open Scope string_scope.
Local Hint Constructors eval_Zexpr eval_Bexpr eval_Sexpr size_of.
Local Hint Resolve
      eval_Zexprlist_includes_valuation includes_add_new None_dom_lookup.

Hint Resolve no_dup_var_generation no_dup_mesh_grid
     forall_map_not_in_index forall_map_not_in_dom
     not_In_var_map2 not_In_var_map
     not_var_generation_in_dom2 not_var_generation_in_index2
     not_var_generation_in_index not_var_generation_in_dom : reindexers.
Hint Extern 3 (Datatypes.length _ = Datatypes.length _) =>
       rewrite map_length; rewrite length_nat_range_rec;
       eapply length_mesh_grid_indices; eassumption : reindexers.
Arguments flatten : simpl nomatch.

Lemma fold_left_mul_filter_until_0 : forall l x,
    fold_left mul l x = fold_left mul (filter_until l 0) x.
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. cases a. simpl. rewrite mul_0_r.
    replace 0 with (0*0) by lia. rewrite fold_left_mul_assoc_nat.
    lia. simpl. eauto.
Qed.

Lemma eval_Sexpr_eval_Sstmt_exists
     : forall (sh : context) (v : valuation) (ec : expr_context) 
         (s : Sexpr) (r : scalar_result),
       eval_Sexpr sh v ec s r ->
       forall (st : stack) (h : heap),
       contexts_agree ec st h sh ->
       eval_Sstmt v st h (lowerS s sh) match r with
                                       | SS s0 => s0
                                       | SX => 0%R
                                       end.
Proof.
  induct 1; intros; simpl in *.
  - econstructor. eapply H1 in H. invs. rewrite H3. f_equal.
    cases r; auto.
  - eapply H3 in H. invs. rewrite H0 in H. invert H. rewrite H0.
    pose proof H2. eapply eval_get_eval_Zexprlist in H. invs.
    econstructor. eauto.
    eapply eval_Zexpr_Z_eval_Zexpr.
    eapply eval_Zexpr_Z_flatten_index_flatten.
    eapply forall_no_vars_eval_Zexpr_Z_total.
    rewrite map_fst_combine by lia. eauto.
    rewrite map_snd_combine by lia. eauto.
    eapply flatten_sh_nonneg. eapply eval_get_In_meshgrid in H2.
    erewrite result_has_shape_result_shape_Z in H2.
    2: { eauto. }
    repeat decomp_index. rewrite map_fst_combine by lia.
    rewrite mesh_grid_map_Nat2Z_id in *. eauto.
    eapply result_has_shape_self; eauto. eauto.
    replace ((map Z.of_nat
                  (filter_until
                     (map Z.to_nat (map (eval_Zexpr_Z_total $0) x0)) 0)))
      with (result_shape_Z (V rs)).
    2: { erewrite result_has_shape_result_shape_Z by eauto. reflexivity. }
    rewrite partial_result_to_array_delta_partial_interpret_reindexer_flatten.
    unfold array_add.
    rewrite lookup_merge.
    erewrite result_has_shape_result_shape_Z by eauto.
    pose proof H7. eapply eval_get_In_meshgrid in H; eauto.
    erewrite result_has_shape_result_shape_Z in H by eauto.
    rewrite mesh_grid_filter_until in *.
    rewrite mesh_grid_map_Nat2Z_id in H.
    2: { eapply result_has_shape_self; eauto. }
    rewrite map_fst_combine in * by lia.
    rewrite filter_until_0_id.
    2: { eapply mesh_grid_shape_pos in H. eapply Forall_map.
         eapply Forall_impl. 2: eassumption. simpl. lia. }
    rewrite Z2Natid_list.
    2: { eapply mesh_grid_shape_pos in H.
         eapply Forall_impl. 2: eassumption. simpl. lia. }
    rewrite result_lookup_Z_partial_result_to_array_delta in *.
    2: { eapply result_has_shape_self; eauto. }
    2: { erewrite result_has_shape_result_shape_Z by eauto.
         decomp_goal_index. rewrite mesh_grid_map_Nat2Z_id. eauto. }
    2: { erewrite result_has_shape_result_shape_Z by eauto.
         rewrite mesh_grid_filter_until. rewrite mesh_grid_map_Nat2Z_id.
         unfold injective. intros. invs. eapply injective_flatten.
         eauto. eauto. eauto. }
    cases x0. invert H5.
    pose proof (lookup_alloc_array
                      (Z.to_nat (fold_left Z.mul (map (eval_Zexpr_Z_total $0) (z :: x0)) 1%Z))
                      (flatten (map (eval_Zexpr_Z_total $0) (z :: x0)) x1)).
    pose proof H. rewrite map_cons in *.
    eapply in_mesh_grid_args_flatten_bounds in H.
    invert H9.
    + eapply lookup_None_dom in H11.
      rewrite dom_alloc_array in H11.
      rewrite Z2Nat.id in H11.
      2: { eapply fold_left_mul_nonneg. eapply mesh_grid_shape_pos in H10.
           eapply Forall_impl. 2: eassumption. simpl. lia. lia. }
      exfalso. apply H11.
      erewrite <- In_iff_in.
      eapply in_mesh_grid_flatten_in_range.
      eapply mesh_grid_shape_pos in H10.
      eapply Forall_impl. 2: eassumption. simpl. lia.
      eauto.
    + rewrite H11.
      pose proof H2. eapply eval_get_lookup_result_Z in H9; eauto.
      subst.
      
      cases (result_lookup_Z_option x1 (V rs)).
      * eapply result_lookup_Z_option_result_lookup_Z in Heq.
        rewrite Heq. f_equal. ring.
      * eapply result_lookup_Z_option_result_lookup_Z_None in Heq.
        cases (result_lookup_Z x1 (V rs)); subst; eauto.
  - cases r1; cases r2; simpl; econstructor; eauto.
  - cases r1; cases r2; simpl; econstructor; eauto.
  - cases r1; cases r2; simpl; econstructor; eauto.
  - cases r1; cases r2; simpl; econstructor; eauto.
  - econstructor.
Qed.

Lemma snd_vars_of_reindexer_vars_of_Zexpr_subseteq :
  forall l x1,
    In x1 (map snd l) ->
    constant (vars_of_Zexpr x1) \subseteq (vars_of_reindexer l).
Proof.
  induct l; intros.
  - simpl in *. propositional.
  - simpl in *. cases a. simpl in *. invert H.
    + sets.
    + eapply IHl in H0. sets.
Qed.

Lemma fst_vars_of_reindexer_vars_of_Zexpr_subseteq :
  forall l x1,
    In x1 (map fst l) ->
    constant (vars_of_Zexpr x1) \subseteq (vars_of_reindexer l).
Proof.
  induct l; intros.
  - simpl in *. propositional.
  - simpl in *. cases a. simpl in *. invert H.
    + sets.
    + eapply IHl in H0. sets.
Qed.

Theorem lower_correct_exists :
  forall e,
    constant_nonneg_bounds e ->
    forall sh v ec r,
      (* functional evaluation of ATL *)
      eval_expr sh v ec e r ->
      forall l, size_of e l ->
      forall p st h reindexer asn,
        (* imperative evaluation of lowering *)
        (* our environment is well-formed *)
        well_formed_environment st h p sh v (vars_of e) ec ->
        (* reindexer is well-formed *)
        partial_well_formed_reindexer reindexer v r ->
        (* allocation is well-formed *)
        partial_well_formed_allocation reindexer r st h p v ->
        (* expr context and imperative state agree *)
        contexts_agree ec st h sh ->
        forall pads g,
          has_pad sh v g e pads ->
        (forall pads (x : var) (r0 : result),
            g $? x = Some pads ->
            ec $? x = Some r0 ->
            relate_pads pads r0 (result_shape_nat r0)) ->
        assign_no_overwrite st h p reindexer r v asn ->
        exists st' h', eval_stmt v st h (lower e reindexer p asn sh) st' h'.
Proof.
  intros e Hconst sh v ec r.
  induct 1; intros ls Hsize p st h reindexer asm
                   Henv Hrdx Halloc Hctx pads g Hpad Hrelate Hassign.
  - simpl. eexists. eexists. eapply EvalForBase; eauto.
  - simpl in *. invs. pose proof H10.
    invert Hpad. pose proof H6 as Hlo.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
      with (v:=$0) in H6.
    pose proof H as HHlo.
    eapply eval_Zexpr_Z_eval_Zexpr in H.
    eapply H6 in H. invert H.
    cases k.
    2: { eapply IHeval_expr1 in H9; eauto.
         2: { eapply well_formed_environment_add_valuation; eauto. }
         2: { eapply partial_well_formed_reindexer_eval0.
              8: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total.
                   apply H8. }
              all: eauto. apply Henv.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep. eapply HHlo.
                   eapply H0. lia. eassumption. eauto. eauto. eauto. }
              simpl. invert H6. rewrite H11. propositional. eauto.
              unfold not. intros. apply H3.
              eapply shape_to_vars_contains_substring. eauto.
              simpl length.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0.
                   rewrite HHlo. reflexivity. }
              rewrite H5. lia. }
         2: { pose proof Halloc.
              eapply partial_well_formed_allocation_result_V in H. invs.
              eapply partial_well_formed_allocation_eval_step. eauto. eauto.
              eapply Hrdx. eapply Henv. eapply Hrdx. eapply Hrdx. eapply Hrdx.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   eapply HHlo. eapply H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0. lia.
                   eauto. eauto. eauto. eauto. }
              econstructor; eauto. eauto. eauto. eauto.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
              lia. 
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0.
                   rewrite HHlo. reflexivity. }
              rewrite H5. lia.
              eapply Hrdx. eapply Hrdx.
         }
         2: { eapply H26. lia. lia. }
         invs.
         pose proof H9 as Hfirst.
         eapply lower_correct_weak in H9.
         2: { eauto. }
         2: { eauto. }
         2: { eauto. }
         2: { eapply well_formed_environment_add_valuation; eauto. }
         2: { eapply partial_well_formed_reindexer_eval0; eauto. apply Henv.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   eapply HHlo. eapply H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0. lia.
                   eauto. eauto. eauto. eauto. }
              econstructor; eauto. eauto.
              unfold not. intros. eapply H3.
              eapply shape_to_vars_contains_substring; eauto.
              simpl.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0.
                   rewrite HHlo. reflexivity. }
              rewrite H5. lia.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
         }
         2: { pose proof Halloc.
              eapply partial_well_formed_allocation_result_V in H. invs.
              eapply partial_well_formed_allocation_eval_step; eauto.
              eapply Hrdx. eapply Henv. eapply Hrdx. eapply Hrdx.
              eapply Hrdx.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   eapply HHlo. eapply H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0. lia.
                   eauto. eauto. eauto. eauto. }
              econstructor; eauto. eauto.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
              lia.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0.
                   rewrite HHlo. reflexivity. }
              rewrite H5. lia.
              apply Hrdx. apply Hrdx. }
         2: { eauto. }
         2: { eapply H26. lia. lia. }
         2: { eauto. }
         cases (reindexer
           (((! i ! - lo)%z, (hi - lo)%z)
              :: shape_to_index (result_shape_Z r)
              (shape_to_vars (result_shape_Z r)))).
         { eapply reindexer_not_empty_vars_in_index in Heq. invert Heq.
           apply Hrdx.
           simpl. unfold not. intros.
           eapply cup_empty in H. invs.
           eapply cup_empty in H11. invs.
           rewrite constant_app_no_dups in H.
           eapply cup_empty in H. invs.
           eapply constant_not_empty in H11. propositional. inversion 1. }
         pose proof Halloc.
         eapply partial_well_formed_allocation_result_V in H.
         invs.
         assert (vars_of_Zexpr lo ++/ [] = [] /\
                   vars_of_Zexpr hi = [] /\
                   (0 <= eval_Zexpr_Z_total $0 hi -
                           eval_Zexpr_Z_total $0 (lo + | 1 |)%z)%Z /\
                   constant_nonneg_bounds body).
         { erewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 3. simpl.
              rewrite H8.
              invert H6. rewrite H12. sets. }
         eapply IHeval_expr2 with (reindexer:=
                                     fun l =>
                                       (shift_top_dim_reindexer reindexer l))
           in H9.
         2: { eauto. }
         3: { eapply partial_well_formed_reindexer_shift_top_dim_reindexer.
              eauto. apply Henv.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   eapply HHlo. eapply H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0. lia.
                   eauto. eauto. eauto. eauto. }
              econstructor; eauto. eauto. }
         3: { eapply partial_well_formed_allocation_shift_top_dim_reindexer.
              eauto. eauto. apply Hrdx. apply Henv. apply Hrdx.
              apply Hrdx. apply Hrdx.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   eapply HHlo. eapply H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0. lia.
                   eauto. eauto. eauto. eauto. }
              econstructor; eauto. eauto.
              apply Hrdx. }
         2: { eapply well_formed_environment_add_heap. eauto. eauto. }
         2: { eapply contexts_agree_add_heap; try apply Henv; eauto. }
         2: { eapply HasPadGen with (k:=k) (c:=c) (ll:=ll) (rr:=rr).
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 3. simpl. lia.
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 3. simpl. lia.
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 3. simpl. lia.
              eauto.
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 2. simpl.
              unfold eval_Zexpr_Z_total at 3. simpl. intros.
              eapply H23. lia.
              eapply H25.
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 2. simpl.
              unfold eval_Zexpr_Z_total at 4. simpl. intros.
              apply H26. lia. lia.
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 3. simpl.
              lia. }
         2: { eauto. }
         2: { eapply assign_no_overwrite_array_add_shift_top_dim_reindexer;
              try assumption.
              7: eapply H6.
              7: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total.
                   apply H8. }
              9: eassumption.
              8: { eapply length_eval_expr_gen in H5; eauto.
                   simpl. rewrite H0.
                   eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
                   specialize (H14 v).
                   pose proof H14. eapply eval_Zexpr_Z_eval_Zexpr in H21.
                   eapply H6 in H14. invert H14.
                   rewrite H21. f_equal.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H9. eapply H9 in H0. invert H0. lia. }
              2: lia.
              2: eauto.
              2: eauto.
              2: eauto. simpl. propositional. eauto.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   6: eauto. 6: eauto.
                   eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
                   specialize (H14 v).
                   pose proof H14. eapply eval_Zexpr_Z_eval_Zexpr in H21.
                   eapply H6 in H14. invert H14.
                   rewrite H21. f_equal.
                   eauto. lia. auto. auto. }
              2: eauto.
              simpl. propositional. }
         2: apply Hrdx.
         invs.
         eexists. eexists.
         eapply EvalForStep.
         eapply eval_Zexpr_Z_eval_Zexpr. apply H6. econstructor. eauto.
         lia.
         pose proof Hfirst.
         eapply Hfirst.
         unfold shift_top_dim_reindexer in *.
         unfold lookup_total. rewrite H.
         eapply eq_eval_stmt_for. eassumption.
         simpl. rewrite HHlo. reflexivity.
         eassumption.
         intros.
         eapply eq_eval_stmt_lower_eq_reindexers. eassumption.
         intros. simpl.
         eapply Hrdx.
         erewrite <- eq_Z_tuple_index_list_cons_tup.
         split.
         eapply eq_zexpr_transitivity.
         eapply eq_zexpr_sub_sub_distr.
         eapply eq_zexpr_transitivity.
         eapply eq_zexpr_sub.
         eapply eq_zexpr_id. auto.
         eapply eq_zexpr_add_sub_id.
         eauto.
         split.
         eapply eq_zexpr_transitivity.
         eapply eq_zexpr_sub_sub_distr.
         eapply eq_zexpr_transitivity.
         eapply eq_zexpr_sub.
         eapply eq_zexpr_id. auto.
         eapply eq_zexpr_add_sub_id.
         eauto.
         eapply eq_Z_tuple_index_list_id.
         pose proof Halloc.
         eapply partial_well_formed_allocation_result_V in H. invs.
         eapply assign_no_overwrite_cons_0; eauto.
         simpl. propositional. lia.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
         eapply result_has_shape_self.
         eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
         3: { eapply EvalGenStep.
              6: eauto. 6: eauto.
              eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
              specialize (H11 v).
              pose proof H11. eapply eval_Zexpr_Z_eval_Zexpr in H13.
              eapply H6 in H11. invert H11. rewrite H13. f_equal.
              eauto. lia. auto. auto. }
         2: eauto.
         simpl. propositional.
         eapply length_eval_expr_gen in H5; eauto.
         simpl. rewrite H0.
         eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
         specialize (H11 v).
         pose proof H11. eapply eval_Zexpr_Z_eval_Zexpr in H13.
         eapply H6 in H11. invert H11.
         rewrite H13. f_equal.
         eapply eval_Zexpr_Z_eval_Zexpr in H0.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
           with (v:=$0) in H8. eapply H8 in H0. invert H0. lia. apply Hrdx.
         pose proof Halloc.
         eapply partial_well_formed_allocation_result_V in H. invs.
         eapply assign_no_overwrite_cons_0; eauto.
         simpl. propositional. lia.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
         eapply result_has_shape_self.
         eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
         3: { eapply EvalGenStep.
              6: eauto. 6: eauto.
              eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
              specialize (H11 v).
              pose proof H11. eapply eval_Zexpr_Z_eval_Zexpr in H13.
              eapply H6 in H11. invert H11. rewrite H13. f_equal.
              eauto. lia. auto. auto. }
         2: eauto.
         simpl. propositional.
         eapply length_eval_expr_gen in H5; eauto.
         simpl. rewrite H0.
         eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
         specialize (H11 v).
         pose proof H11. eapply eval_Zexpr_Z_eval_Zexpr in H13.
         eapply H6 in H11. invert H11.
         rewrite H13. f_equal.
         eapply eval_Zexpr_Z_eval_Zexpr in H0.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
           with (v:=$0) in H8. eapply H8 in H0. invert H0. lia. apply Hrdx.
    }
    simpl Z.of_nat in *. rewrite Z.sub_0_r in *.
    cases ll.
    2: { eapply IHeval_expr1 in H9; eauto.
         2: { eapply well_formed_environment_add_valuation; eauto. }
         2: { eapply partial_well_formed_reindexer_eval0.
              8: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total.
                   apply H8. }
              all: eauto. apply Henv.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep. eapply HHlo.
                   eapply H0. lia. eassumption. eauto. eauto. eauto. }
              simpl. invert H6. rewrite H11. propositional. eauto.
              unfold not. intros. apply H3.
              eapply shape_to_vars_contains_substring. eauto.
              simpl length.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0.
                   rewrite HHlo. reflexivity. }
              rewrite H5. lia. }
         2: { pose proof Halloc.
              eapply partial_well_formed_allocation_result_V in H. invs.
              eapply partial_well_formed_allocation_eval_step. eauto. eauto.
              eapply Hrdx. eapply Henv. eapply Hrdx. eapply Hrdx. eapply Hrdx.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   eapply HHlo. eapply H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0. lia.
                   eauto. eauto. eauto. eauto. }
              econstructor; eauto. eauto. eauto. eauto.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
              lia. 
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0.
                   rewrite HHlo. reflexivity. }
              rewrite H5. lia.
              eapply Hrdx. eapply Hrdx.
         }
         2: { eapply H23. lia. }
         invs.
         pose proof H9 as Hfirst.
         eapply lower_correct_weak in H9.
         2: { eauto. }
         2: { eauto. }
         2: { eauto. }
         2: { eapply well_formed_environment_add_valuation; eauto. }
         2: { eapply partial_well_formed_reindexer_eval0; eauto. apply Henv.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   eapply HHlo. eapply H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0. lia.
                   eauto. eauto. eauto. eauto. }
              econstructor; eauto. eauto.
              unfold not. intros. eapply H3.
              eapply shape_to_vars_contains_substring; eauto.
              simpl.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0.
                   rewrite HHlo. reflexivity. }
              rewrite H5. lia.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
         }
         2: { pose proof Halloc.
              eapply partial_well_formed_allocation_result_V in H. invs.
              eapply partial_well_formed_allocation_eval_step; eauto.
              eapply Hrdx. eapply Henv. eapply Hrdx. eapply Hrdx.
              eapply Hrdx.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   eapply HHlo. eapply H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0. lia.
                   eauto. eauto. eauto. eauto. }
              econstructor; eauto. eauto.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
              lia.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0.
                   rewrite HHlo. reflexivity. }
              rewrite H5. lia.
              apply Hrdx. apply Hrdx. }
         2: { eauto. }
         2: { eapply H23. lia. }
         2: { eauto. }
         cases (reindexer
                  (((! i ! - lo)%z, (hi - lo)%z)
                     :: shape_to_index (result_shape_Z r)
                     (shape_to_vars (result_shape_Z r)))).
         { eapply reindexer_not_empty_vars_in_index in Heq. invert Heq.
           apply Hrdx.
           simpl. unfold not. intros.
           eapply cup_empty in H. invs.
           eapply cup_empty in H11. invs.
           rewrite constant_app_no_dups in H.
           eapply cup_empty in H. invs.
           eapply constant_not_empty in H11. propositional. inversion 1. }
         pose proof Halloc.
         eapply partial_well_formed_allocation_result_V in H.
         invs.
         assert (vars_of_Zexpr lo ++/ [] = [] /\
                   vars_of_Zexpr hi = [] /\
                   (0 <= eval_Zexpr_Z_total $0 hi -
                           eval_Zexpr_Z_total $0 (lo + | 1 |)%z)%Z /\
                   constant_nonneg_bounds body).
         { erewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 3. simpl.
              rewrite H8.
              invert H6. rewrite H12. sets. }
         eapply IHeval_expr2 with (reindexer:=
                                     fun l =>
                                       (shift_top_dim_reindexer reindexer l))
           in H9.
         2: { eauto. }
         3: { eapply partial_well_formed_reindexer_shift_top_dim_reindexer.
              eauto. apply Henv.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   eapply HHlo. eapply H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0. lia.
                   eauto. eauto. eauto. eauto. }
              econstructor; eauto. eauto. }
         3: { eapply partial_well_formed_allocation_shift_top_dim_reindexer.
              eauto. eauto. apply Hrdx. apply Henv. apply Hrdx.
              apply Hrdx. apply Hrdx.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   eapply HHlo. eapply H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0. lia.
                   eauto. eauto. eauto. eauto. }
              econstructor; eauto. eauto.
              apply Hrdx. }
         2: { eapply well_formed_environment_add_heap. eauto. eauto. }
         2: { eapply contexts_agree_add_heap; try apply Henv; eauto. }
         2: { eapply HasPadGen with (k:=0) (c:=c) (ll:=ll) (rr:=rr).
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 3. simpl. lia.
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 3. simpl. lia.
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 3. simpl. lia.
              eauto.
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 2. simpl.
              unfold eval_Zexpr_Z_total at 3. simpl. intros.
              eapply H23. lia.
              eapply H25.
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 2. simpl.
              unfold eval_Zexpr_Z_total at 4. simpl. intros.
              apply H26. lia. lia.
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 3. simpl.
              lia. }
         2: { eauto. }
         2: { eapply assign_no_overwrite_array_add_shift_top_dim_reindexer;
              try assumption.
              7: eapply H6.
              7: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total.
                   apply H8. }
              9: eassumption.
              8: { eapply length_eval_expr_gen in H5; eauto.
                   simpl. rewrite H0.
                   eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
                   specialize (H14 v).
                   pose proof H14. eapply eval_Zexpr_Z_eval_Zexpr in H21.
                   eapply H6 in H14. invert H14.
                   rewrite H21. f_equal.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H9. eapply H9 in H0. invert H0. lia. }
              2: lia.
              2: eauto.
              2: eauto.
              2: eauto. simpl. propositional. eauto.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   6: eauto. 6: eauto.
                   eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
                   specialize (H14 v).
                   pose proof H14. eapply eval_Zexpr_Z_eval_Zexpr in H21.
                   eapply H6 in H14. invert H14.
                   rewrite H21. f_equal.
                   eauto. lia. auto. auto. }
              2: eauto.
              simpl. propositional. }
         2: apply Hrdx.
         invs.
         eexists. eexists.
         eapply EvalForStep.
         eapply eval_Zexpr_Z_eval_Zexpr. apply H6. econstructor. eauto.
         lia.
         pose proof Hfirst.
         eapply Hfirst.
         unfold shift_top_dim_reindexer in *.
         unfold lookup_total. rewrite H.
         eapply eq_eval_stmt_for. eassumption.
         simpl. rewrite HHlo. reflexivity.
         eassumption.
         intros.
         eapply eq_eval_stmt_lower_eq_reindexers. eassumption.
         intros. simpl.
         eapply Hrdx.
         erewrite <- eq_Z_tuple_index_list_cons_tup.
         split.
         eapply eq_zexpr_transitivity.
         eapply eq_zexpr_sub_sub_distr.
         eapply eq_zexpr_transitivity.
         eapply eq_zexpr_sub.
         eapply eq_zexpr_id. auto.
         eapply eq_zexpr_add_sub_id.
         eauto.
         split.
         eapply eq_zexpr_transitivity.
         eapply eq_zexpr_sub_sub_distr.
         eapply eq_zexpr_transitivity.
         eapply eq_zexpr_sub.
         eapply eq_zexpr_id. auto.
         eapply eq_zexpr_add_sub_id.
         eauto.
         eapply eq_Z_tuple_index_list_id.
         pose proof Halloc.
         eapply partial_well_formed_allocation_result_V in H. invs.
         eapply assign_no_overwrite_cons_0; eauto.
         simpl. propositional. lia.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
         eapply result_has_shape_self.
         eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
         3: { eapply EvalGenStep.
              6: eauto. 6: eauto.
              eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
              specialize (H11 v).
              pose proof H11. eapply eval_Zexpr_Z_eval_Zexpr in H13.
              eapply H6 in H11. invert H11. rewrite H13. f_equal.
              eauto. lia. auto. auto. }
         2: eauto.
         simpl. propositional.
         eapply length_eval_expr_gen in H5; eauto.
         simpl. rewrite H0.
         eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
         specialize (H11 v).
         pose proof H11. eapply eval_Zexpr_Z_eval_Zexpr in H13.
         eapply H6 in H11. invert H11.
         rewrite H13. f_equal.
         eapply eval_Zexpr_Z_eval_Zexpr in H0.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
           with (v:=$0) in H8. eapply H8 in H0. invert H0. lia. apply Hrdx.
         pose proof Halloc.
         eapply partial_well_formed_allocation_result_V in H. invs.
         eapply assign_no_overwrite_cons_0; eauto.
         simpl. propositional. lia.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
         eapply result_has_shape_self.
         eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
         3: { eapply EvalGenStep.
              6: eauto. 6: eauto.
              eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
              specialize (H11 v).
              pose proof H11. eapply eval_Zexpr_Z_eval_Zexpr in H13.
              eapply H6 in H11. invert H11. rewrite H13. f_equal.
              eauto. lia. auto. auto. }
         2: eauto.
         simpl. propositional.
         eapply length_eval_expr_gen in H5; eauto.
         simpl. rewrite H0.
         eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
         specialize (H11 v).
         pose proof H11. eapply eval_Zexpr_Z_eval_Zexpr in H13.
         eapply H6 in H11. invert H11.
         rewrite H13. f_equal.
         eapply eval_Zexpr_Z_eval_Zexpr in H0.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
           with (v:=$0) in H8. eapply H8 in H0. invert H0. lia. apply Hrdx.
    }
    simpl in *. cases rr.
    2: { eapply IHeval_expr1 in H9; eauto.
         2: { eapply well_formed_environment_add_valuation; eauto. }
         2: { eapply partial_well_formed_reindexer_eval0.
              8: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total.
                   apply H8. }
              all: eauto. apply Henv.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep. eapply HHlo.
                   eapply H0. lia. eassumption. eauto. eauto. eauto. }
              simpl. invert H6. rewrite H11. propositional. eauto.
              unfold not. intros. apply H3.
              eapply shape_to_vars_contains_substring. eauto.
              simpl length.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0.
                   rewrite HHlo. reflexivity. }
              rewrite H5. lia. }
         2: { pose proof Halloc.
              eapply partial_well_formed_allocation_result_V in H. invs.
              eapply partial_well_formed_allocation_eval_step. eauto. eauto.
              eapply Hrdx. eapply Henv. eapply Hrdx. eapply Hrdx. eapply Hrdx.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   eapply HHlo. eapply H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0. lia.
                   eauto. eauto. eauto. eauto. }
              econstructor; eauto. eauto. eauto. eauto.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
              lia. 
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0.
                   rewrite HHlo. reflexivity. }
              rewrite H5. lia.
              eapply Hrdx. eapply Hrdx.
         }
         2: { eapply H25. lia. }
         invs.
         pose proof H9 as Hfirst.
         eapply lower_correct_weak in H9.
         2: { eauto. }
         2: { eauto. }
         2: { eauto. }
         2: { eapply well_formed_environment_add_valuation; eauto. }
         2: { eapply partial_well_formed_reindexer_eval0; eauto. apply Henv.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   eapply HHlo. eapply H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0. lia.
                   eauto. eauto. eauto. eauto. }
              econstructor; eauto. eauto.
              unfold not. intros. eapply H3.
              eapply shape_to_vars_contains_substring; eauto.
              simpl.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0.
                   rewrite HHlo. reflexivity. }
              rewrite H5. lia.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
         }
         2: { pose proof Halloc.
              eapply partial_well_formed_allocation_result_V in H. invs.
              eapply partial_well_formed_allocation_eval_step; eauto.
              eapply Hrdx. eapply Henv. eapply Hrdx. eapply Hrdx.
              eapply Hrdx.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   eapply HHlo. eapply H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0. lia.
                   eauto. eauto. eauto. eauto. }
              econstructor; eauto. eauto.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
              lia.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0.
                   rewrite HHlo. reflexivity. }
              rewrite H5. lia.
              apply Hrdx. apply Hrdx. }
         2: { eauto. }
         2: { eapply H25. lia. }
         2: { eauto. }
         cases (reindexer
           (((! i ! - lo)%z, (hi - lo)%z)
              :: shape_to_index (result_shape_Z r)
              (shape_to_vars (result_shape_Z r)))).
         { eapply reindexer_not_empty_vars_in_index in Heq. invert Heq.
           apply Hrdx.
           simpl. unfold not. intros.
           eapply cup_empty in H. invs.
           eapply cup_empty in H11. invs.
           rewrite constant_app_no_dups in H.
           eapply cup_empty in H. invs.
           eapply constant_not_empty in H11. propositional. inversion 1. }
         pose proof Halloc.
         eapply partial_well_formed_allocation_result_V in H.
         invs.
         assert (vars_of_Zexpr lo ++/ [] = [] /\
                   vars_of_Zexpr hi = [] /\
                   (0 <= eval_Zexpr_Z_total $0 hi -
                           eval_Zexpr_Z_total $0 (lo + | 1 |)%z)%Z /\
                   constant_nonneg_bounds body).
         { erewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 3. simpl.
              rewrite H8.
              invert H6. rewrite H12. sets. }
         eapply IHeval_expr2 with (reindexer:=
                                     fun l =>
                                       (shift_top_dim_reindexer reindexer l))
           in H9.
         2: { eauto. }
         3: { eapply partial_well_formed_reindexer_shift_top_dim_reindexer.
              eauto. apply Henv.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   eapply HHlo. eapply H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0. lia.
                   eauto. eauto. eauto. eauto. }
              econstructor; eauto. eauto. }
         3: { eapply partial_well_formed_allocation_shift_top_dim_reindexer.
              eauto. eauto. apply Hrdx. apply Henv. apply Hrdx.
              apply Hrdx. apply Hrdx.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   eapply HHlo. eapply H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0. lia.
                   eauto. eauto. eauto. eauto. }
              econstructor; eauto. eauto.
              apply Hrdx. }
         2: { eapply well_formed_environment_add_heap. eauto. eauto. }
         2: { eapply contexts_agree_add_heap; try apply Henv; eauto. }
         2: { eapply HasPadGen with (k:=0) (c:=c) (ll:=0) (rr:=rr).
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 3. simpl. lia.
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 3. simpl. lia.
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 3. simpl. lia.
              eauto.
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 2. simpl.
              unfold eval_Zexpr_Z_total at 3. simpl. intros.
              eapply H23. lia.
              intros. eapply H25. lia.
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 2. simpl.
              unfold eval_Zexpr_Z_total at 4. simpl. intros.
              apply H26. lia. lia.
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 3. simpl.
              lia. }
         2: { eauto. }
         2: { eapply assign_no_overwrite_array_add_shift_top_dim_reindexer;
              try assumption.
              7: eapply H6.
              7: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total.
                   apply H8. }
              9: eassumption.
              8: { eapply length_eval_expr_gen in H5; eauto.
                   simpl. rewrite H0.
                   eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
                   specialize (H14 v).
                   pose proof H14. eapply eval_Zexpr_Z_eval_Zexpr in H21.
                   eapply H6 in H14. invert H14.
                   rewrite H21. f_equal.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H9. eapply H9 in H0. invert H0. lia. }
              2: lia.
              2: eauto.
              2: eauto.
              2: eauto. simpl. propositional. eauto.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   6: eauto. 6: eauto.
                   eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
                   specialize (H14 v).
                   pose proof H14. eapply eval_Zexpr_Z_eval_Zexpr in H21.
                   eapply H6 in H14. invert H14.
                   rewrite H21. f_equal.
                   eauto. lia. auto. auto. }
              2: eauto.
              simpl. propositional. }
         2: apply Hrdx.
         invs.
         eexists. eexists.
         eapply EvalForStep.
         eapply eval_Zexpr_Z_eval_Zexpr. apply H6. econstructor. eauto.
         lia.
         pose proof Hfirst.
         eapply Hfirst.
         unfold shift_top_dim_reindexer in *.
         unfold lookup_total. rewrite H.
         eapply eq_eval_stmt_for. eassumption.
         simpl. rewrite HHlo. reflexivity.
         eassumption.
         intros.
         eapply eq_eval_stmt_lower_eq_reindexers. eassumption.
         intros. simpl.
         eapply Hrdx.
         erewrite <- eq_Z_tuple_index_list_cons_tup.
         split.
         eapply eq_zexpr_transitivity.
         eapply eq_zexpr_sub_sub_distr.
         eapply eq_zexpr_transitivity.
         eapply eq_zexpr_sub.
         eapply eq_zexpr_id. auto.
         eapply eq_zexpr_add_sub_id.
         eauto.
         split.
         eapply eq_zexpr_transitivity.
         eapply eq_zexpr_sub_sub_distr.
         eapply eq_zexpr_transitivity.
         eapply eq_zexpr_sub.
         eapply eq_zexpr_id. auto.
         eapply eq_zexpr_add_sub_id.
         eauto.
         eapply eq_Z_tuple_index_list_id.
         pose proof Halloc.
         eapply partial_well_formed_allocation_result_V in H. invs.
         eapply assign_no_overwrite_cons_0; eauto.
         simpl. propositional. lia.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
         eapply result_has_shape_self.
         eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
         3: { eapply EvalGenStep.
              6: eauto. 6: eauto.
              eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
              specialize (H11 v).
              pose proof H11. eapply eval_Zexpr_Z_eval_Zexpr in H13.
              eapply H6 in H11. invert H11. rewrite H13. f_equal.
              eauto. lia. auto. auto. }
         2: eauto.
         simpl. propositional.
         eapply length_eval_expr_gen in H5; eauto.
         simpl. rewrite H0.
         eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
         specialize (H11 v).
         pose proof H11. eapply eval_Zexpr_Z_eval_Zexpr in H13.
         eapply H6 in H11. invert H11.
         rewrite H13. f_equal.
         eapply eval_Zexpr_Z_eval_Zexpr in H0.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
           with (v:=$0) in H8. eapply H8 in H0. invert H0. lia. apply Hrdx.
         pose proof Halloc.
         eapply partial_well_formed_allocation_result_V in H. invs.
         eapply assign_no_overwrite_cons_0; eauto.
         simpl. propositional. lia.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
         eapply result_has_shape_self.
         eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
         3: { eapply EvalGenStep.
              6: eauto. 6: eauto.
              eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
              specialize (H11 v).
              pose proof H11. eapply eval_Zexpr_Z_eval_Zexpr in H13.
              eapply H6 in H11. invert H11. rewrite H13. f_equal.
              eauto. lia. auto. auto. }
         2: eauto.
         simpl. propositional.
         eapply length_eval_expr_gen in H5; eauto.
         simpl. rewrite H0.
         eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
         specialize (H11 v).
         pose proof H11. eapply eval_Zexpr_Z_eval_Zexpr in H13.
         eapply H6 in H11. invert H11.
         rewrite H13. f_equal.
         eapply eval_Zexpr_Z_eval_Zexpr in H0.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
           with (v:=$0) in H8. eapply H8 in H0. invert H0. lia. apply Hrdx.
    }
    eapply IHeval_expr1 with (asn:=asm) in H9; eauto.
    2: { eapply well_formed_environment_add_valuation; eauto. }
    2: { eapply partial_well_formed_reindexer_eval0.
         8: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total.
              apply H8. }
         all: eauto. apply Henv.
         eapply result_has_shape_self.
         eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
         3: { eapply EvalGenStep. eapply HHlo.
              eapply H0. lia. eassumption. eauto. eauto. eauto. }
         simpl. invert H6. rewrite H11. propositional. eauto.
         unfold not. intros. apply H3.
         eapply shape_to_vars_contains_substring. eauto.
         simpl length.
         eapply length_eval_expr_gen in H5.
         2: { simpl. rewrite H0.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                with (v:=$0) in H8.
              eapply eval_Zexpr_Z_eval_Zexpr in H0.
              eapply H8 in H0. invert H0.
              rewrite HHlo. reflexivity. } 
         rewrite H5. eapply eval_Zexpr_Z_eval_Zexpr in H0.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
           with (v:=$0) in H8.
         eapply H8 in H0. invert H0.
         lia. }
         2: { pose proof Halloc.
              eapply partial_well_formed_allocation_result_V in H. invs.
              eapply partial_well_formed_allocation_eval_step. eauto. eauto.
              eapply Hrdx. eapply Henv. eapply Hrdx. eapply Hrdx. eapply Hrdx.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   eapply HHlo. eapply H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0. lia.
                   eauto. eauto. eauto. eauto. }
              econstructor; eauto. eauto. eauto. eauto.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
              eapply eval_Zexpr_Z_eval_Zexpr in H0.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                with (v:=$0) in H8.
              eapply H8 in H0. invert H0.
              lia. 
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0.
                   rewrite HHlo. reflexivity. }
              rewrite H5. lia.
              eapply Hrdx. eapply Hrdx.
         }
         2: { eapply H26.
              eapply eval_Zexpr_Z_eval_Zexpr in H0.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                with (v:=$0) in H8.
              eapply H8 in H0. invert H0.
              lia. lia. }
         invs.
         pose proof H9 as Hfirst.
         eapply lower_correct_weak in H9.
         2: { eauto. }
         2: { eauto. }
         2: { eauto. }
         2: { eapply well_formed_environment_add_valuation; eauto. }
         2: { eapply partial_well_formed_reindexer_eval0; eauto. apply Henv.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   eapply HHlo. eapply H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0. lia.
                   eauto. eauto. eauto. eauto. }
              econstructor; eauto. eauto.
              unfold not. intros. eapply H3.
              eapply shape_to_vars_contains_substring; eauto.
              simpl.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0.
                   rewrite HHlo. reflexivity. }
              rewrite H5.
              eapply eval_Zexpr_Z_eval_Zexpr in H0.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                with (v:=$0) in H8.
              eapply H8 in H0. invert H0.
              lia.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
         }
         2: { pose proof Halloc.
              eapply partial_well_formed_allocation_result_V in H. invs.
              eapply partial_well_formed_allocation_eval_step; eauto.
              eapply Hrdx. eapply Henv. eapply Hrdx. eapply Hrdx.
              eapply Hrdx.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   eapply HHlo. eapply H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0. lia.
                   eauto. eauto. eauto. eauto. }
              econstructor; eauto. eauto.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
              eapply eval_Zexpr_Z_eval_Zexpr in H0.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                with (v:=$0) in H8.
              eapply H8 in H0. invert H0.
              lia.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0.
                   rewrite HHlo. reflexivity. }
              rewrite H5. lia.
              apply Hrdx. apply Hrdx. }
         2: { eauto. }
         2: { eapply H26.
              eapply eval_Zexpr_Z_eval_Zexpr in H0.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                with (v:=$0) in H8.
              eapply H8 in H0. invert H0.
              lia. lia. }
         2: { eauto. }
         cases (reindexer
           (((! i ! - lo)%z, (hi - lo)%z)
              :: shape_to_index (result_shape_Z r)
              (shape_to_vars (result_shape_Z r)))).
         { eapply reindexer_not_empty_vars_in_index in Heq. invert Heq.
           apply Hrdx.
           simpl. unfold not. intros.
           eapply cup_empty in H. invs.
           eapply cup_empty in H11. invs.
           rewrite constant_app_no_dups in H.
           eapply cup_empty in H. invs.
           eapply constant_not_empty in H11. propositional. inversion 1. }
         pose proof Halloc.
         eapply partial_well_formed_allocation_result_V in H.
         invs.
         assert (vars_of_Zexpr lo ++/ [] = [] /\
                   vars_of_Zexpr hi = [] /\
                   (0 <= eval_Zexpr_Z_total $0 hi -
                           eval_Zexpr_Z_total $0 (lo + | 1 |)%z)%Z /\
                   constant_nonneg_bounds body).
         { erewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 3. simpl.
              rewrite H8.
              invert H6. rewrite H12. sets.
              eapply eval_Zexpr_Z_eval_Zexpr in H0.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
           with (v:=$0) in H8.
         eapply H8 in H0. invert H0. lia.
         }
         eapply IHeval_expr2 with (reindexer:=
                                     fun l =>
                                       (shift_top_dim_reindexer reindexer l))
                                  (asn:=asm)
           in H9.
         2: { eauto. }
         3: { eapply partial_well_formed_reindexer_shift_top_dim_reindexer.
              eauto. apply Henv.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   eapply HHlo. eapply H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0. lia.
                   eauto. eauto. eauto. eauto. }
              econstructor; eauto. eauto. }
         3: { eapply partial_well_formed_allocation_shift_top_dim_reindexer.
              eauto. eauto. apply Hrdx. apply Henv. apply Hrdx.
              apply Hrdx. apply Hrdx.
              eapply result_has_shape_self.
              eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   eapply HHlo. eapply H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply H8 in H0. invert H0. lia.
                   eauto. eauto. eauto. eauto. }
              econstructor; eauto. eauto.
              apply Hrdx. }
         2: { eapply well_formed_environment_add_heap. eauto. eauto. }
         2: { eapply contexts_agree_add_heap; try apply Henv; eauto. }
         2: { eapply HasPadGen with (k:=0) (c:=c-1) (ll:=0) (rr:=0).
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 3. simpl. lia.
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 3. simpl.
              eapply eval_Zexpr_Z_eval_Zexpr in H0.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                with (v:=$0) in H8.
              eapply H8 in H0. invert H0.
              lia.
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 3. simpl. lia.
              eauto.
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 2. simpl.
              unfold eval_Zexpr_Z_total at 3. simpl. intros.
              eapply H23. lia.
              intros. lia.
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 2. simpl.
              unfold eval_Zexpr_Z_total at 4. simpl. intros.
              apply H26. lia. lia.
              rewrite eval_Zexpr_Z_total_add_distr by eauto.
              unfold eval_Zexpr_Z_total at 3. simpl.
              lia. }
         2: { eauto. }
         2: { eapply assign_no_overwrite_array_add_shift_top_dim_reindexer;
              try assumption.
              7: eapply H6.
              7: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total.
                   apply H8. }
              8: { eapply length_eval_expr_gen in H5; eauto.
                   simpl. rewrite H0.
                   eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
                   specialize (H14 v).
                   pose proof H14. eapply eval_Zexpr_Z_eval_Zexpr in H21.
                   eapply H6 in H14. invert H14.
                   rewrite H21. f_equal.
                   eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H9. eapply H9 in H0. invert H0. lia. }
              2: { eapply eval_Zexpr_Z_eval_Zexpr in H0.
                   eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
                     with (v:=$0) in H8.
                   eapply H8 in H0. invert H0.
                   lia. }
              2: eauto.
              2: eauto.
              2: eauto. simpl. propositional. eauto.
              eapply result_has_shape_self.
              eapply
                constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: { eapply EvalGenStep.
                   6: eauto. 6: eauto.
                   eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
                   specialize (H14 v).
                   pose proof H14. eapply eval_Zexpr_Z_eval_Zexpr in H21.
                   eapply H6 in H14. invert H14.
                   rewrite H21. f_equal.
                   eauto. lia. auto. auto. }
              2: eauto.
              simpl. propositional. }
         2: apply Hrdx.
         invs.
         eexists. eexists.
         eapply EvalForStep.
         eapply eval_Zexpr_Z_eval_Zexpr. apply H6. econstructor. eauto.
         lia.
         pose proof Hfirst.
         eapply Hfirst.
         unfold shift_top_dim_reindexer in *.
         unfold lookup_total. rewrite H.
         eapply eq_eval_stmt_for. eassumption.
         simpl. rewrite HHlo. reflexivity.
         eassumption.
         intros.
         eapply eq_eval_stmt_lower_eq_reindexers. eassumption.
         intros. simpl.
         eapply Hrdx.
         erewrite <- eq_Z_tuple_index_list_cons_tup.
         split.
         eapply eq_zexpr_transitivity.
         eapply eq_zexpr_sub_sub_distr.
         eapply eq_zexpr_transitivity.
         eapply eq_zexpr_sub.
         eapply eq_zexpr_id. auto.
         eapply eq_zexpr_add_sub_id.
         eauto.
         split.
         eapply eq_zexpr_transitivity.
         eapply eq_zexpr_sub_sub_distr.
         eapply eq_zexpr_transitivity.
         eapply eq_zexpr_sub.
         eapply eq_zexpr_id. auto.
         eapply eq_zexpr_add_sub_id.
         eauto.
         eapply eq_Z_tuple_index_list_id.
         pose proof Halloc.
         eapply partial_well_formed_allocation_result_V in H. invs.
         eapply assign_no_overwrite_cons_0; eauto.
         simpl. propositional.
         eapply eval_Zexpr_Z_eval_Zexpr in H0.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
           with (v:=$0) in H8.
         eapply H8 in H0. invert H0.
         lia.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
         eapply result_has_shape_self.
         eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
         3: { eapply EvalGenStep.
              6: eauto. 6: eauto.
              eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
              specialize (H11 v).
              pose proof H11. eapply eval_Zexpr_Z_eval_Zexpr in H13.
              eapply H6 in H11. invert H11. rewrite H13. f_equal.
              eauto. lia. auto. auto. }
         2: eauto.
         simpl. propositional.
         eapply length_eval_expr_gen in H5; eauto.
         simpl. rewrite H0.
         eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
         specialize (H11 v).
         pose proof H11. eapply eval_Zexpr_Z_eval_Zexpr in H13.
         eapply H6 in H11. invert H11.
         rewrite H13. f_equal.
         eapply eval_Zexpr_Z_eval_Zexpr in H0.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
           with (v:=$0) in H8. eapply H8 in H0. invert H0. lia. apply Hrdx.
         pose proof Halloc.
         eapply partial_well_formed_allocation_result_V in H. invs.
         eapply assign_no_overwrite_cons_0; eauto.
         simpl. propositional.
         eapply eval_Zexpr_Z_eval_Zexpr in H0.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
           with (v:=$0) in H8.
         eapply H8 in H0. invert H0.
         lia.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
         eapply result_has_shape_self.
         eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
         3: { eapply EvalGenStep.
              6: eauto. 6: eauto.
              eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
              specialize (H11 v).
              pose proof H11. eapply eval_Zexpr_Z_eval_Zexpr in H13.
              eapply H6 in H11. invert H11. rewrite H13. f_equal.
              eauto. lia. auto. auto. }
         2: eauto.
         simpl. propositional.
         eapply length_eval_expr_gen in H5; eauto.
         simpl. rewrite H0.
         eapply vars_of_Zexpr_empty_eval_Zexpr_literal in Hlo. invs.
         specialize (H11 v).
         pose proof H11. eapply eval_Zexpr_Z_eval_Zexpr in H13.
         eapply H6 in H11. invert H11.
         rewrite H13. f_equal.
         eapply eval_Zexpr_Z_eval_Zexpr in H0.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
           with (v:=$0) in H8. eapply H8 in H0. invert H0. lia. apply Hrdx.
  - (* STEPPING SUM *)
    simpl.
    pose proof Hconst as Hcont'.
    simpl in Hcont'. invs.
    pose proof H7 as Hlo.
    pose proof H9 as Hhi.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total with (v:=$0) in
      Hlo, Hhi.
    invert Hpad.
    { eapply eval_Zexpr_Z_eval_Zexpr in H,H0.
      eapply Hlo in H. eapply Hhi in H0. invert H. invert H0. lia. }
    pose proof Hconst as Hsh.
    eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in Hsh.
    2: { eauto. }
    2: { eapply EvalSumStep. eauto. eauto. lia. eauto. eauto. eauto. eauto.
         eauto. }
    pose proof H10 as HI1. 
    eapply IHeval_expr1 in HI1; eauto.
    2: { simpl in Henv.
         eapply well_formed_environment_add_valuation. eauto.
         sets. eauto. }
    2: { pose proof H6.
         eapply result_has_shape_add_result_result in H6; eauto.         
         eapply partial_well_formed_reindexer_add_valuation; eauto.
         decomp_partial_well_formed_reindexer.
         propositional.
         eapply partial_injective_add_result_l.
         4: eauto. eauto. eauto. eauto.
         eauto. eauto. eauto. eauto. eauto. apply Henv. }
    2: { eapply partial_well_formed_allocation_add_valuation;
         eauto; try apply Hrdx.
         eapply partial_well_formed_allocation_add_result_l; eauto.
         eapply result_has_shape_add_result_result in H6; eauto.
         propositional. 
         eapply result_has_shape_add_result_result in H6; eauto.
         propositional. }
    2: eauto.
    invs.

    pose proof H11 as Heval1.
    eapply lower_correct_weak with (asn:=Reduce) in H11.
    2: { eauto. }
    2: { eauto. }
    2: { eauto. }
    2: { eapply well_formed_environment_add_valuation; eauto. }
    2: { eapply partial_well_formed_reindexer_add_valuation; eauto.
         decomp_partial_well_formed_reindexer.
         propositional.
         pose proof Hsh.
         eapply result_has_shape_add_result_result in Hsh.
         2: { eauto. }
         invs. 
         eapply partial_injective_add_result_l.
         4: eauto. eauto. eauto. eauto.
         eauto. apply Henv. }
    2: { eapply partial_well_formed_allocation_add_valuation; eauto.
         pose proof Hsh.
         eapply result_has_shape_add_result_result in Hsh.
         2: { eauto. }
         invs. 
         eapply partial_well_formed_allocation_add_result_l; eauto.
         eapply result_has_shape_add_result_result in H6; eauto.
         propositional.
         eapply Hrdx. propositional. apply Hrdx. }
    2: eauto.
    2: { eapply H19. eapply eval_Zexpr_Z_eval_Zexpr in H.
         eapply Hlo in H. invert H. lia. }
    2: eauto.
    2: { eapply assign_no_overwrite_reduce. }
    2: { eapply H19. eapply eval_Zexpr_Z_eval_Zexpr in H.
         eapply Hlo in H. invert H. lia. }
    
    assert (constant_nonneg_bounds (Sum i (lo + | 1 |)%z hi body)).
    { econstructor. simpl. rewrite H7. sets. propositional. }

    cases (reindexer
            (shape_to_index (result_shape_Z r) (shape_to_vars (result_shape_Z r)))).
    { assert (loz + 1 < hiz \/ loz + 1 = hiz)%Z by lia. invert H12.
      { unfold result_shape_Z in *. simpl in *.
        pose proof Halloc.
        unfold partial_well_formed_allocation in H12.
        unfold result_shape_Z in H12.
        replace (result_shape_nat s) with (result_shape_nat r) in *.
        2: { eapply result_has_shape_add_result_result in H6.
             2: { eauto. }
             invs.
             erewrite result_has_shape_result_shape_nat by eauto. symmetry.
             erewrite result_has_shape_result_shape_nat by eauto. symmetry.
             auto. }
        rewrite Heq in H12. invert H12. rewrite H14 in *.        
        eapply IHeval_expr2 with (asn:=Reduce) (st:= x) (h:=x0) in H8;
          invert H11.
        2: { econstructor; eauto. }
        2: eauto.
        2: { eapply well_formed_environment_add_stack.
             eauto. eapply lookup_Some_dom. eauto. }
        2: { decomp_partial_well_formed_reindexer. clear IHeval_expr1.
             propositional.
             pose proof H6. eapply result_has_shape_add_result_result in H22.
             2: { eauto. } invert H22.
             eapply partial_injective_add_result_r.
             4: eauto. eauto. eauto. eauto.
             eauto. eauto. eauto. eauto. eauto. }
        2: { eapply partial_well_formed_allocation_same_add_stack.
             eapply partial_well_formed_allocation_add_result_r; eauto.
             eapply result_has_shape_add_result_result in H6; eauto.
             propositional. 
             eapply result_has_shape_add_result_result in H6; eauto.
             propositional. }
        2: { eapply contexts_agree_add_in_stack. eauto. eauto.
             apply Henv. apply Henv. }
        2: { eapply HasPadSum.
             erewrite eval_Zexpr_Z_total_add_distr.
             unfold eval_Zexpr_Z_total at 2. simpl. intros.
             eapply H19. lia. eauto. eauto.
             erewrite eval_Zexpr_Z_total_add_distr.
             unfold eval_Zexpr_Z_total at 3. simpl.
             eapply eval_Zexpr_Z_eval_Zexpr in H,H0.
             eapply Hlo in H. eapply Hhi in H0. invert H. invert H0. lia.
             eauto. eauto. }
        2: { eauto. }
        invs.
        eexists. eexists.
        eapply EvalForStep.
        eauto. eauto. lia.
        eassumption. eapply H8.
        eapply assign_no_overwrite_reduce.
      }
      { unfold result_shape_Z in *. simpl in *.
        pose proof Halloc.
        unfold partial_well_formed_allocation in H12.
        unfold result_shape_Z in H12.
        replace (result_shape_nat s) with (result_shape_nat r) in *.
        2: { eapply result_has_shape_add_result_result in H6.
             2: { eauto. }
             invs.
             erewrite result_has_shape_result_shape_nat by eauto. symmetry.
             erewrite result_has_shape_result_shape_nat by eauto. symmetry.
             auto. }
        rewrite Heq in H12. invert H12. rewrite H13 in *.        
        invs.
        eexists. eexists.
        eapply EvalForStep.
        eauto. eauto. lia.
        eassumption.
        eapply EvalForBase.
        simpl. rewrite H. reflexivity. eassumption. lia.
      }
    }
    { assert (loz + 1 < hiz \/ loz + 1 = hiz)%Z by lia. invert H12.
      { unfold result_shape_Z in *. simpl in *.
        pose proof Halloc.
        unfold partial_well_formed_allocation in H12.
        unfold result_shape_Z in H12.
        replace (result_shape_nat s) with (result_shape_nat r) in *.
        2: { eapply result_has_shape_add_result_result in H6.
             2: { eauto. }
             invs.
             erewrite result_has_shape_result_shape_nat by eauto. symmetry.
             erewrite result_has_shape_result_shape_nat by eauto. symmetry.
             auto. }
        rewrite Heq in H12. invert H12. invert H14. unfold lookup_total in *.
        rewrite H12 in *.
        eapply IHeval_expr2 with (asn:=Reduce) (st:= x) (h:=x0) in H8;
          invert H11.
        2: { econstructor; eauto. }
        2: { eapply well_formed_environment_add_heap.
             eauto. eauto. }
        2: { decomp_partial_well_formed_reindexer. clear IHeval_expr1.
             propositional.
             pose proof H6. eapply result_has_shape_add_result_result in H23.
             2: { eauto. } invert H23.
             eapply partial_injective_add_result_r.
             4: eauto. eauto. eauto. eauto.
             eauto. eauto. eauto. eauto. eauto. }
        2: { eapply partial_well_formed_allocation_add_heap; eauto.
             eapply partial_well_formed_allocation_add_result_r; eauto.
             eapply result_has_shape_add_result_result in H6; eauto.
             propositional. 
             eapply result_has_shape_add_result_result in H6; eauto.
             propositional. }
        2: { eapply contexts_agree_add_heap; eauto. apply Henv. apply Henv. }
        2: { eapply HasPadSum.
             erewrite eval_Zexpr_Z_total_add_distr.
             unfold eval_Zexpr_Z_total at 2. simpl. intros.
             eapply H19. lia. eauto. eauto.
             erewrite eval_Zexpr_Z_total_add_distr.
             unfold eval_Zexpr_Z_total at 3. simpl.
             eapply eval_Zexpr_Z_eval_Zexpr in H,H0.
             eapply Hlo in H. eapply Hhi in H0. invert H. invert H0. lia.
             eauto. eauto. }
        2: { eauto. }
        invs.
        eexists. eexists.
        eapply EvalForStep.
        eauto. eauto. lia.
        eassumption. eapply H8.
        eapply assign_no_overwrite_reduce.
      }
      { unfold result_shape_Z in *. simpl in *.
        pose proof Halloc.
        unfold partial_well_formed_allocation in H12.
        unfold result_shape_Z in H12.
        replace (result_shape_nat s) with (result_shape_nat r) in *.
        2: { eapply result_has_shape_add_result_result in H6.
             2: { eauto. }
             invs.
             erewrite result_has_shape_result_shape_nat by eauto. symmetry.
             erewrite result_has_shape_result_shape_nat by eauto. symmetry.
             auto. }
        rewrite Heq in H12. invert H12. invert H13. unfold lookup_total in *.
        rewrite H12 in *. invs.
        eexists. eexists.
        eapply EvalForStep.
        eauto. eauto. lia.
        eassumption.
        eapply EvalForBase.
        simpl. rewrite H. reflexivity. eassumption. lia.
      }
    }
    eapply assign_no_overwrite_reduce.
  - simpl in *. invs.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
      with (v:=$0) in H4,H6.
    eapply eval_Zexpr_Z_eval_Zexpr in H,H0.
    eapply H4 in H. eapply H6 in H0. invert H. invert H0.
    invert Hpad. 2: lia.
    eexists. eexists.
    eapply EvalForBase.
    eapply eval_Zexpr_Z_eval_Zexpr. eapply H4. econstructor.
    eapply eval_Zexpr_Z_eval_Zexpr. eapply H6. econstructor.
    lia.
  - eexists. eexists. simpl. eapply EvalIfFalse. eauto.
  - simpl. invert Hpad. eq_eval_B. discriminate.
    eapply IHeval_expr in Halloc. invs.
    eexists. eexists. eapply EvalIfTrue. eapply H2.
    all: simpl in *; invs; eauto.
  - simpl in *. invs. erewrite size_of_sizeof in * by eauto. simpl.
    pose proof H1 as Heval1. invert Hpad. eq_size_of.
    eapply IHeval_expr1 with (st:= st $+ (x,0%R)) in Heval1; eauto.
    2: { eapply well_formed_environment_alloc_stack.
         eassumption. sets. sets. sets. }
    2: { eapply partial_well_formed_reindexer_id. apply Henv. }
    2: { unfold partial_well_formed_allocation.
         unfold shape_to_index. unfold result_shape_Z. simpl.
         eexists. rewrite lookup_add_eq by auto. reflexivity. }
    2: { eapply contexts_agree_alloc_stack. eauto. sets. }
    invs. pose proof H9.
    eapply lower_correct_weak in H8.
    2: { eauto. }
    2: { eauto. }
    2: { eauto. }
    2: { eapply well_formed_environment_alloc_stack.
         eassumption. sets. sets. sets. }
    2: { eapply partial_well_formed_reindexer_id. apply Henv. }
    2: { unfold partial_well_formed_allocation.
         unfold shape_to_index. unfold result_shape_Z. simpl.
         eexists. rewrite lookup_add_eq by auto. reflexivity. }
    2: { eapply contexts_agree_alloc_stack. eauto. sets. }
    2: { eauto. }
    2: { eauto. }
    unfold result_shape_Z in H8. simpl in H8.
    invert H8. rewrite add_overwrite in H9.
    rewrite lookup_add_eq in H9 by auto. pose proof H7.
    eapply IHeval_expr2 in H8.
    2: { eauto. }
    2: { invs. 
         eapply well_formed_environment_let_bind1_scalar. eauto.
         sets. sets. sets. }
    2: { eauto. }
    2: { eapply partial_well_formed_allocation_add_stack. eauto.
         unfold well_formed_environment in Henv. sets. }
    2: { eapply contexts_agree_let_bind1_scalar. eauto. }
    2: { eauto. }
    2: { intros. cases (x0 =? x). eapply String.eqb_eq in Heq. subst.
         repeat rewrite lookup_add_eq in * by auto. invert H11.
         simpl. invert H10.
         eapply has_pad_gen_pad. eauto. eauto. eauto. econstructor. eauto.
         eapply contexts_agree_result_has_shape. eauto. eauto.
         eapply String.eqb_neq in Heq. rewrite lookup_add_ne in * by eauto.
         eauto. }
    invs.
    pose proof H8.
    eexists. eexists. econstructor. econstructor.
    econstructor. eassumption. econstructor.
    rewrite Rplus_0_l. eauto. econstructor.
    eapply assign_no_overwrite_add_stack; eauto.
    eapply assign_no_overwrite_alloc_stack; eauto.
    eapply assign_no_overwrite_alloc_stack; eauto.
  - simpl in *. invs. erewrite size_of_sizeof in * by eauto.
    cases esh1. propositional. invert H1.
    pose proof H3 as Heval1. invert Hpad. eq_size_of.
    eapply IHeval_expr1 with
      (h:=(alloc_array_in_heap
             [(fold_left mul (map Z.to_nat zs) (Z.to_nat z0))] h x))
      in Heval1; eauto.
    2: { eapply well_formed_environment_letbind1.
         3: sets. sets.
         2: { eauto. }
         sets. }
    2: { eapply partial_well_formed_reindexer_id. apply Henv. }
    2: { rewrite <- (Nat2Z.id (fold_left _ _ _)).
         eapply partial_well_formed_allocation_letbind1. eapply Henv.
         unfold well_formed_environment in *. sets.
         erewrite result_has_shape_result_shape_Z.
         2: { eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: eauto. eauto. eauto. }
         eapply constant_nonneg_bounds_size_of_nonneg in Heval1.
         2: { eauto. }
         2: { econstructor. eauto. eauto. }
         eapply constant_nonneg_bounds_size_of_no_vars in H3.
         2: { eauto. }
         eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H3.
         invert H3. eq_eval_Z. eq_eval_Zlist.
         rewrite <- Z_of_nat_fold_left_mul. f_equal.
         simpl. cases (Z.to_nat (eval_Zexpr_Z_total $0 z)).
         simpl. replace 0 with (0*0) at 1 by lia.
         rewrite fold_left_mul_assoc_nat. lia.
         simpl. rewrite add_0_r. rewrite <- Heq.
         rewrite <- fold_left_mul_filter_until_0. reflexivity. }
    2: { eapply contexts_agree_alloc_array_in_heap. eauto. eauto. }
    invert Heval1. invert H1. pose proof H10.
    eapply lower_correct_weak in H1.
    2: { eauto. }
    2: { eauto. }
    2: { eauto. }
    2: { eapply well_formed_environment_letbind1.
         3: sets. sets.
         2: { eauto. }
         sets. }
    2: { eapply partial_well_formed_reindexer_id. apply Henv. }
    2: { rewrite <- (Nat2Z.id (fold_left _ _ _)).
         eapply partial_well_formed_allocation_letbind1. eapply Henv.
         unfold well_formed_environment in *. sets.
         erewrite result_has_shape_result_shape_Z.
         2: { eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: eauto. eauto. eauto. }
         pose proof H3.
         eapply constant_nonneg_bounds_size_of_no_vars in H11.
         2: { eauto. }
         eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H11.
         invert H11. eq_eval_Z. eq_eval_Zlist.
         rewrite <- Z_of_nat_fold_left_mul. f_equal.         
         simpl. cases (Z.to_nat (eval_Zexpr_Z_total $0 z)).
         simpl. replace 0 with (0*0) at 1 by lia.
         rewrite fold_left_mul_assoc_nat. lia.
         simpl. rewrite add_0_r. rewrite <- Heq.
         rewrite <- fold_left_mul_filter_until_0. reflexivity. }

    cases (shape_to_index (result_shape_Z (V l1))
                          (shape_to_vars (result_shape_Z (V l1)))).
    { eapply shape_to_index_not_empty_Z in Heq. propositional. }
    unfold alloc_array_in_heap in H1. rewrite add_overwrite in H1.
    unfold lookup_total in H1. rewrite lookup_add_eq in H1 by auto.

    pose proof H9.
    eapply IHeval_expr2 in H11.
    2: { eauto. }
    2: { invs.
         eapply well_formed_environment_alloc_heap. eauto. eauto.
         sets. sets. sets. }
    2: { eauto. }
    2: { eapply partial_well_formed_allocation_add_heap_var.
         invs. eauto. unfold well_formed_environment in*. sets. }
    2: { eapply contexts_agree_add_alloc_heap. invs. eauto. eauto.
         eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
         3: eauto. eauto. eauto.
         eapply constant_nonneg_bounds_size_of_nonneg.
         3: { eapply forall_no_vars_eval_Zexpr_Z_total.
              eapply constant_nonneg_bounds_size_of_no_vars.
              2: eauto. eauto. }
         2: { eauto. }
         eauto. eapply constant_nonneg_bounds_size_of_no_vars.
         2: eauto. eauto. reflexivity. }    
    2: { eauto. }
    2: { intros. cases (x2 =? x). eapply String.eqb_eq in Heq0. subst.
         repeat rewrite lookup_add_eq in * by auto. invert H12.
         simpl. invert H15.
         eapply has_pad_gen_pad. eauto. eauto. eauto.
         eapply result_has_shape_self.
         eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
         3: eauto. eauto. eauto. eauto.
         eapply contexts_agree_result_has_shape. eauto. eauto.
         eapply String.eqb_neq in Heq0. rewrite lookup_add_ne in * by eauto.
         eauto. }    
    invs.
    eexists. eexists. econstructor.
    unfold flat_sizeof. erewrite size_of_sizeof by eauto. simpl.
    econstructor.
    pose proof H3.
    eapply constant_nonneg_bounds_size_of_no_vars in H1; eauto.
    eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H1; eauto.
    invert H1. eq_eval_Z. eq_eval_Zlist.
    eapply eval_Zexpr_Z_eval_Zexpr.
    eapply eval_Zexpr_Z_fold_left_ZTimes.
    eauto. eauto.
    
    econstructor.
    rewrite <- (Nat2Z.id (fold_left _ _ _)) in H10.
    replace (Z.to_nat (Z.of_nat (fold_left mul (map Z.to_nat zs) (Z.to_nat z0)))) with (Z.to_nat
          (fold_left Z.mul (map (eval_Zexpr_Z_total $0) esh1)
                     (eval_Zexpr_Z_total $0 z))) in H10.
    2: { pose proof H3.
         eapply constant_nonneg_bounds_size_of_no_vars in H3. 2: eauto.
         eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H3; eauto.
         invert H3. eq_eval_Z. eq_eval_Zlist.
         rewrite <- (mul_1_l (Z.to_nat (eval_Zexpr_Z_total $0 _))).
         rewrite fold_left_mul_assoc_nat.
         rewrite Nat2Z.inj_mul. rewrite Z_of_nat_fold_left_mul.
         f_equal.
         rewrite <- fold_left_mul_assoc. rewrite Z.mul_1_l.
         eapply constant_nonneg_bounds_size_of_nonneg in H1.
         2: { eauto. }
         2: { eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v).
              eapply constant_nonneg_bounds_size_of_no_vars; eauto. }
         invert H1.
         rewrite Z2Nat.id by lia.
         rewrite map_map.
         symmetry. erewrite map_extensionality.
         2: { intros. erewrite Z2Nat.id. reflexivity.
              eapply Forall_forall in H1.
              2: { eauto. } simpl in *. lia. }
         rewrite map_id. reflexivity. }
    eapply H10. simpl. rewrite add_0_r in *.
    econstructor.
    replace (array_add
       (alloc_array
          (Z.to_nat
             (fold_left Z.mul (map (eval_Zexpr_Z_total $0) esh1)
                (eval_Zexpr_Z_total $0 z))) $0)
       (partial_result_to_array_delta
          (partial_interpret_reindexer (fun l3 : list (Zexpr * Zexpr) => l3)
             (result_shape_Z (V l1)) v) (V l1))) with
      (array_add
             (alloc_array
                (Z.to_nat
                   (fold_left Z.mul
                      (map Z.of_nat
                         (filter_until
                            (map Z.to_nat (map (eval_Zexpr_Z_total $0) (z :: esh1)))
                            0)) 1%Z)) $0)
             (partial_result_to_array_delta
                (partial_interpret_reindexer (fun l : list (Zexpr * Zexpr) => l)
                   (map Z.of_nat
                      (filter_until
                         (map Z.to_nat (map (eval_Zexpr_Z_total $0) (z :: esh1))) 0))
                   $0) (V l1))).
    eassumption. repeat rewrite map_cons.
    f_equal.
    2: { erewrite result_has_shape_result_shape_Z.
         2: { eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
              3: eauto. eauto.  eauto. }
         repeat rewrite map_cons.
         unfold partial_result_to_array_delta. f_equal.
         unfold partial_interpret_reindexer.
         rewrite partially_eval_Z_tup_empty_id. rewrite map_id.
         rewrite map_partially_eval_Z_tup_shape_to_index.
         reflexivity. apply Henv. }
    f_equal. f_equal.
    rewrite <- Z_of_nat_fold_left_mul.
    rewrite <- (Z.mul_1_l (eval_Zexpr_Z_total $0 z) ) at 2.
    rewrite fold_left_mul_assoc.
    replace (map (eval_Zexpr_Z_total $0) esh1) with
      (map Z.of_nat (map Z.to_nat (map (eval_Zexpr_Z_total $0) esh1))).
    2: { rewrite map_map.
         eapply constant_nonneg_bounds_size_of_nonneg in H3.
         2: { eauto. }
         2: { eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v).
              eapply constant_nonneg_bounds_size_of_no_vars. 2: eauto. eauto. }
         invert H3. erewrite map_extensionality.
         2: { intros. erewrite Z2Nat.id. reflexivity.
              eapply Forall_forall in H1.
              2: { eauto. } simpl in *. lia. }
         rewrite map_id. reflexivity. }
    rewrite <- Z_of_nat_fold_left_mul.
    rewrite <- fold_left_mul_filter_until_0.
    simpl. rewrite add_0_r.
    eapply constant_nonneg_bounds_size_of_nonneg in H3.
    2: { eauto. }
    2: { eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v).
         eapply constant_nonneg_bounds_size_of_no_vars. 2: eauto. eauto. }
    rewrite Z2Natid_list.
    2: { invert H3. eauto. }
    replace (eval_Zexpr_Z_total $0 z) with
      (Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 z))).
    2: { invert H3. rewrite Z2Nat.id by lia. reflexivity. }
    rewrite <- Nat2Z.inj_mul. f_equal.
    rewrite Nat2Z.id.
    rewrite <- fold_left_mul_assoc_nat. rewrite mul_1_l. reflexivity.
    econstructor. invs.
    eapply assign_no_overwrite_add_heap; eauto.
    eapply contexts_agree_alloc_array_in_heap. eauto. eauto. eauto.
    eauto.
    rewrite <- (Nat2Z.id (fold_left mul _ _)).
    pose proof H3.
    eapply constant_nonneg_bounds_size_of_nonneg in H11; eauto. invert H11.
    eapply assign_no_overwrite_alloc_heap. eapply H3. all: eauto.
    unfold flat_sizeof. erewrite size_of_sizeof by eauto. simpl.
    eapply eval_Zexpr_Z_eval_Zexpr.
    erewrite eval_Zexpr_Z_fold_left_ZTimes.
    replace (fold_left mul (map Z.to_nat zs) (Z.to_nat z0)) with
      (fold_left mul (map Z.to_nat (z0::zs)) 1).
    2: { simpl. rewrite add_0_r. reflexivity. }    
    rewrite Z_of_nat_fold_left_mul. simpl. rewrite Z.mul_1_l. reflexivity.
    erewrite Z2Natid_list by eauto. eauto.
    rewrite Z2Nat.id by lia. eauto.
    eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
    apply H3. all: eauto.
    rewrite <- (Nat2Z.id (fold_left mul _ _)).
    pose proof H3.
    eapply constant_nonneg_bounds_size_of_nonneg in H1; eauto. invert H1.
    eapply assign_no_overwrite_alloc_heap. eapply H3. all: eauto.
    unfold flat_sizeof. erewrite size_of_sizeof by eauto. simpl.
    eapply eval_Zexpr_Z_eval_Zexpr.
    erewrite eval_Zexpr_Z_fold_left_ZTimes.
    replace (fold_left mul (map Z.to_nat zs) (Z.to_nat z0)) with
      (fold_left mul (map Z.to_nat (z0::zs)) 1).
    2: { simpl. rewrite add_0_r. reflexivity. }    
    rewrite Z_of_nat_fold_left_mul. simpl. rewrite Z.mul_1_l. reflexivity.
    erewrite Z2Natid_list by eauto. eauto.
    rewrite Z2Nat.id by lia. eauto.
    eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
    apply H3. all: eauto.
  - simpl in *. invs. repeat erewrite size_of_sizeof in * by eauto. simpl.
    invert Hpad.
    pose proof H1. pose proof H2.
    eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H3;
      eauto.
    eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H4;
      eauto.
    pose proof H1. pose proof H2.
    eapply constant_nonneg_bounds_size_of_no_vars in H14.
    2: { eauto. }
    eapply constant_nonneg_bounds_size_of_no_vars in H15.
    2: { eauto. }
    pose proof H14. pose proof H15.
    eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H16.
    eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H18.
    invert H16. invert H18.
    eq_size_of. invert H9. invert H16.
    rewrite H8 in *.
    pose proof H1.
    eapply IHeval_expr1 in H7.
    2: { eauto. }
    2: { eapply well_formed_environment_subseteq_vars. eauto. sets. }
    2: { eapply partial_well_formed_reindexer_concat_l. eauto.
         repeat rewrite map_cons in *. eauto.
         repeat rewrite map_cons in *. rewrite H8. eauto.
         apply Henv. eauto. }
    2: { eapply partial_well_formed_allocation_concat_l. eauto.
         repeat rewrite map_cons in *. eauto.
         repeat rewrite map_cons in *. rewrite H8. eauto.
         eapply Henv. apply Hrdx. apply Hrdx. apply Hrdx. eauto.
         apply Hrdx. }
    invs.
    pose proof H7.
    eapply lower_correct_weak with (asn:=asm) in H9; eauto.
    2: { eapply well_formed_environment_subseteq_vars. eauto. sets. }
    2: { eapply partial_well_formed_reindexer_concat_l. eauto.
         repeat rewrite map_cons in *. eauto.
         repeat rewrite map_cons in *. rewrite H8. eauto.
         apply Henv. eauto. }
    2: { eapply partial_well_formed_allocation_concat_l. eauto.
         repeat rewrite map_cons in *. eauto.
         repeat rewrite map_cons in *. rewrite H8. eauto.
         eapply Henv. apply Hrdx. apply Hrdx. apply Hrdx. eauto.
         apply Hrdx. }
    2: { rewrite Z2Nat.id.
         2: { eapply constant_nonneg_bounds_size_of_nonneg in H2; eauto.
              invert H2. eauto. }
         eapply partial_well_formed_allocation_result_V in Halloc. invs.
         eapply assign_no_overwrite_concat_l_; eauto.
         rewrite H8. eauto.
         eapply result_has_shape_concat; eauto. rewrite H8. eauto.
         eapply constant_nonneg_bounds_size_of_nonneg in H1; eauto.
         invert H1. eauto.
         eapply constant_nonneg_bounds_size_of_nonneg in H2; eauto.
         invert H2. eauto.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. invert H14.
         eauto.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. invert H15.
         eauto.
         invert H15. eauto. apply Hrdx. }
    2: { eauto. }
    2: { eauto. }
    2: { eauto. }
    cases (reindexer
           match
             shape_to_index (result_shape_Z (V l1))
               (shape_to_vars (result_shape_Z (V l1)))
           with
           | [] =>
               shape_to_index (result_shape_Z (V l1))
                 (shape_to_vars (result_shape_Z (V l1)))
           | (v0, d) :: xs =>
               (v0, (d + | Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 dim2)) |)%z)
               :: xs
           end).
    { cases (shape_to_index (result_shape_Z (V l1))
                            (shape_to_vars (result_shape_Z (V l1)))).
      eapply shape_to_index_not_empty_Z in Heq0. propositional.
      eapply reindexer_not_empty_vars_in_index in Heq. propositional.
      apply Hrdx.
      unfold not. intros.
      simpl in H16.
      unfold shape_to_index,shape_to_vars, result_shape_Z in Heq0. simpl in *.
      cases l1.
      - simpl in *. invert Heq0. simpl in H16.
        eapply cup_empty in H16. invs.
        eapply cup_empty in H18. invs.
        eapply constant_not_empty in H9. propositional. inversion 1.
      - simpl in *. invert Heq0. simpl in H16.
        eapply cup_empty in H16. invs.
        eapply cup_empty in H18. invs.
        eapply constant_not_empty in H9. propositional. inversion 1. }        

    pose proof H2.
    eapply IHeval_expr2 with (st:=x0) (h:= x1) in H16; eauto.
    2: { invert H9.
         pose proof Halloc.
         eapply partial_well_formed_allocation_result_V in H9. invert H9.
         invert H18.
         eapply well_formed_environment_add_heap.
         eapply well_formed_environment_subseteq_vars. eauto. sets.
         unfold lookup_total. rewrite H9. reflexivity.
         apply Hrdx. }
    2: { eapply partial_well_formed_reindexer_concat_r. eauto.
         simpl in H3. eauto. rewrite H8. simpl in H4. eauto.
         apply Henv.
         invert H14.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto.
         eapply constant_nonneg_bounds_size_of_nonneg in H1; eauto.
         invert H1. lia. }
    2: { invert H9. unfold lookup_total.
         pose proof Halloc.
         eapply partial_well_formed_allocation_result_V in H9. invert H9.
         invert H18. rewrite H9 in *.
         eapply partial_well_formed_allocation_add_heap.
         eapply partial_well_formed_allocation_concat_r.  eauto.
         simpl in *. eauto. simpl in *. rewrite H8. eauto.
         eapply Henv. apply Hrdx. apply Hrdx. apply Hrdx. apply Hrdx.
         invert H14.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto.
         eapply constant_nonneg_bounds_size_of_nonneg in H1; eauto.
         invert H1. lia.  eauto. apply Hrdx. }
    2: { pose proof Halloc.
         eapply partial_well_formed_allocation_result_V in H18. invert H18.
         invert H20. unfold lookup_total in *. rewrite H18 in *.
         invert H9. eapply contexts_agree_add_heap. eauto. eauto.
         unfold well_formed_environment in *. sets.
         unfold well_formed_environment in *. sets.
         apply Hrdx. }
    invs.
    eexists. eexists.
    econstructor.
    rewrite Z2Nat.id in *.
    2: { eapply constant_nonneg_bounds_size_of_nonneg in H2; eauto.
         invert H2. lia. }
    2: { eapply constant_nonneg_bounds_size_of_nonneg in H2; eauto.
         invert H2. lia. }
    2: { eapply constant_nonneg_bounds_size_of_nonneg in H2; eauto.
         invert H2. lia. }
    eapply eq_eval_stmt_lower_eq_reindexers. eassumption.
    intros. cases l0. eapply eq_Z_tuple_index_list_id.
    cases p1. eapply Hrdx.
    erewrite <- eq_Z_tuple_index_list_cons_tup.
    split. eauto. split.
    2: eapply eq_Z_tuple_index_list_id.
    eapply eq_zexpr_transitivity.
    eapply eq_zexpr_add. eapply eq_zexpr_id. reflexivity.
    eapply eq_zexpr_comm.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total.
    invert H15. eauto. eauto. 
    rewrite Z2Nat.id in *.
    2: { eapply constant_nonneg_bounds_size_of_nonneg in H2; eauto.
         invert H2. lia. }
    eauto.
    eapply constant_nonneg_bounds_size_of_nonneg in H2; eauto.
    invert H2. lia.
    eapply constant_nonneg_bounds_size_of_nonneg in H2; eauto.
    invert H2. lia. invs.
    unfold lookup_total.
    pose proof Halloc. eapply partial_well_formed_allocation_result_V in H9.
    invs. rewrite H9.    
    rewrite Z2Nat.id.
    2: { eapply constant_nonneg_bounds_size_of_nonneg in H16; eauto.
         invert H16. eauto. }
    eapply assign_no_overwrite_concat_r_; eauto.
    rewrite H8. eauto.
    eapply result_has_shape_concat. eauto. rewrite H8. eauto.
    eapply constant_nonneg_bounds_size_of_nonneg in H1; eauto.
    invert H1. eauto.
    eapply constant_nonneg_bounds_size_of_nonneg in H16; eauto.
    invert H16. eauto.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. invert H14. eauto.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. invert H15. eauto.
    apply Hrdx.
    rewrite Z2Nat.id.
    2: { eapply constant_nonneg_bounds_size_of_nonneg in H2; eauto.
         invert H2. eauto. }
    eapply partial_well_formed_allocation_result_V in Halloc. invs.
    eapply assign_no_overwrite_concat_l_; eauto.
    rewrite H8. eauto.
    eapply result_has_shape_concat; eauto. rewrite H8. eauto.
    eapply constant_nonneg_bounds_size_of_nonneg in H7; eauto.
    invert H7. eauto.
    eapply constant_nonneg_bounds_size_of_nonneg in H2; eauto.
    invert H2. eauto.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. invert H14. eauto.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. invert H15. eauto.
    invert H15. eauto.
    apply Hrdx.
  - simpl in *. invs. eq_size_of. invert H1. 
    pose proof Hconst. invert Hpad.
    + pose proof H1. eq_size_of. invert H8.
      eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H2;
        eauto. simpl in *.
      pose proof H1.
      eapply constant_nonneg_bounds_size_of_no_vars in H4; eauto. invert H4.
      invert H13.
      eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
        with (v:=$0) in H12,H10.
      eapply H10 in H5.
      eapply H12 in H6. invert H5. invert H6.
      eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H14.
      eq_eval_Zlist.
      eapply IHeval_expr in H1.
      2: { eauto. }
      2: { eauto. }
      2: { eapply partial_well_formed_reindexer_transpose.
           simpl in *. eauto. eauto. apply Henv. }
      2: { eapply partial_well_formed_allocation_transpose;
           try apply Hrdx; try apply Henv; eauto. }
      2: { eauto. }
      2: { eauto. }
      2: { eauto. }
      eauto.
      eapply partial_well_formed_allocation_result_V in Halloc. invs.
      eapply assign_no_overwrite_transpose; eauto.
      repeat rewrite <- map_cons.
      eapply forall_no_vars_eval_Zexpr_Z_total.
      eapply constant_nonneg_bounds_size_of_no_vars; eauto.
      eapply constant_nonneg_bounds_size_of_no_vars in H0; eauto. invert H0.
      auto.
      eapply constant_nonneg_bounds_size_of_no_vars in H0; eauto. invert H0.
      invert H14. auto.
      eapply constant_nonneg_bounds_size_of_no_vars in H0; eauto. invert H0.
      invert H14. auto.
      apply Hrdx.
    + pose proof H1. eq_size_of. invert H7.
      eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H2;
        eauto. simpl in *.
      pose proof H1.
      eapply constant_nonneg_bounds_size_of_no_vars in H4; eauto. invert H4.
      invert H11.
      eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
        with (v:=$0) in H10,H8.
      eapply H8 in H5.
      eapply H10 in H6. invert H5. invert H6.
      eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H12.
      eq_eval_Zlist.
      eapply IHeval_expr in H1.
      2: { eauto. }
      2: { eauto. }
      2: { eapply partial_well_formed_reindexer_transpose.
           simpl in *. eauto. eauto. apply Henv. }
      2: { eapply partial_well_formed_allocation_transpose;
           try apply Hrdx; try apply Henv; eauto. }
      2: { eauto. }
      2: { eauto. }
      2: { eauto. }
      eauto.
      eapply partial_well_formed_allocation_result_V in Halloc. invs.
      eapply assign_no_overwrite_transpose; eauto.
      repeat rewrite <- map_cons.
      eapply forall_no_vars_eval_Zexpr_Z_total.
      eapply constant_nonneg_bounds_size_of_no_vars; eauto.
      eapply constant_nonneg_bounds_size_of_no_vars in H0; eauto. invert H0.
      auto.
      eapply constant_nonneg_bounds_size_of_no_vars in H0; eauto. invert H0.
      invert H12. auto.
      eapply constant_nonneg_bounds_size_of_no_vars in H0; eauto. invert H0.
      invert H12. auto.
      apply Hrdx.
  - simpl in *. invs. invert Hpad.
    eq_size_of. invert H1.
    pose proof Hconst.
    eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H1;
      eauto. simpl in *.
    pose proof Hconst.
    eapply constant_nonneg_bounds_size_of_no_vars in H4; eauto. invert H4.
    invert H13.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
        with (v:=$0) in H12,H11.
    eapply IHeval_expr in Hconst; eauto.
    eapply partial_well_formed_reindexer_flatten;
      try apply Henv; try apply Hrdx; eauto.
    eapply partial_well_formed_allocation_flatten;
      try apply Henv; try apply Hrdx; eauto.
    eapply partial_well_formed_allocation_result_V in Halloc. invs.
    eapply assign_no_overwrite_flatten; eauto. apply Hrdx.
  - simpl in *. invs. invert Hpad. eq_size_of. invert H2.
    pose proof H3.
    eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H2;
      eauto. simpl in *.
    pose proof H3.
    eapply constant_nonneg_bounds_size_of_no_vars in H5; eauto. invert H5.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
      with (v:=$0) in H12,H1.
    pose proof H3.
    eapply constant_nonneg_bounds_size_of_nonneg in H5; eauto.
    2: { econstructor. eapply H12 with (v:=v). econstructor.
         eapply forall_no_vars_eval_Zexpr_Z_total. eauto. }
    invert H5.
    eapply IHeval_expr in H3; eauto.
    eapply partial_well_formed_reindexer_split;
      try apply Hrdx; try apply Henv; eauto.
    eapply partial_well_formed_allocation_split;
      try apply Hrdx; try apply Henv; eauto.
    pose proof Halloc.
    eapply partial_well_formed_allocation_result_V in H5. invs.
    eapply assign_no_overwrite_split; eauto.
    eapply H1. apply Hrdx.
  - simpl in *. invs. invert Hpad. erewrite size_of_sizeof in * by eauto.
    eq_size_of. simpl in *.
    pose proof H2.
    eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H5;
      eauto. simpl in *.
    pose proof H2.
    eapply constant_nonneg_bounds_size_of_no_vars in H7; eauto. invert H7.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
      with (v:=$0) in H12,H4.
    pose proof H2.
    eapply constant_nonneg_bounds_size_of_nonneg in H7; eauto.
    2: { econstructor. eapply H12 with (v:=v). econstructor.
         eapply forall_no_vars_eval_Zexpr_Z_total. eauto. }
    invert H7. pose proof H8.
    eapply has_pad_gen_pad in H8; eauto.
    2: { eapply contexts_agree_result_has_shape; eauto. }
    simpl in H8. invs.
    eapply eval_Zexpr_Z_eval_Zexpr in H. eapply H4 in H. invert H.

    eapply IHeval_expr in H2; eauto.
    rewrite <- (firstn_skipn (length l - (Z.to_nat (eval_Zexpr_Z_total $0 k))) l).
    rewrite <- (rev_involutive (skipn _ _)).
    rewrite <- firstn_rev.
    eapply forall_firstn_ge with (m:= Z.to_nat (eval_Zexpr_Z_total $0 k))
      in H8.
    2: { lia. }
    eapply forall_eq_gen_pad in H8. rewrite H8.
    simpl gen_pad_list. rewrite rev_repeat.
    
    rewrite firstn_length. rewrite rev_length.
    erewrite result_has_shape_length.
    2: { eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape
      in H2; eauto. }

    rewrite min_l by lia.
    eapply partial_well_formed_reindexer_truncr.
    rewrite rev_app_distr.
    rewrite truncl_list_app.
    2: { rewrite rev_length. simpl. rewrite repeat_length. lia. }
    rewrite truncl_list_skipn.
    rewrite skipn_all2.
    2: { rewrite rev_length. simpl. rewrite repeat_length. lia. }
    replace (Z.to_nat (eval_Zexpr_Z_total $0 m)) with (length l).
    2: { erewrite result_has_shape_length by eauto. reflexivity. }
    rewrite <- skipn_rev. simpl.
    rewrite <- truncl_list_skipn. eauto.
    eapply forall_result_has_shape.
    eapply Forall_app. split.
    eapply forall_firstn. eapply result_has_shape_forall. eauto.
    simpl. eapply Forall_repeat. eapply result_has_shape_gen_pad.
    rewrite app_length. simpl. rewrite firstn_length.
    rewrite repeat_length. erewrite result_has_shape_length by eauto.
    rewrite min_l by lia. rewrite sub_add. reflexivity. lia.
    apply Henv. eauto. lia. lia.

    rewrite <- (firstn_skipn
                  (length l-(Z.to_nat (eval_Zexpr_Z_total $0 k))) l).
    rewrite <- (rev_involutive (skipn _ _)).
    rewrite <- firstn_rev.
    eapply forall_firstn_ge with (m:= Z.to_nat (eval_Zexpr_Z_total $0 k))
      in H8.
    2: { lia. }
    eapply forall_eq_gen_pad in H8. rewrite H8.
    simpl gen_pad_list. rewrite rev_repeat.
    
    rewrite firstn_length. rewrite rev_length.
    erewrite result_has_shape_length.
    2: { eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape
      in H2; eauto. }

    rewrite min_l by lia.    
    eapply partial_well_formed_allocation_truncr.
    rewrite rev_app_distr.
    rewrite truncl_list_app.
    2: { rewrite rev_length. simpl. rewrite repeat_length. lia. }
    rewrite truncl_list_skipn.
    rewrite skipn_all2.
    2: { rewrite rev_length. simpl. rewrite repeat_length. lia. }
    replace (Z.to_nat (eval_Zexpr_Z_total $0 m)) with (length l).
    2: { erewrite result_has_shape_length by eauto. reflexivity. }
    simpl.
    rewrite <- skipn_rev. simpl.
    rewrite <- truncl_list_skipn. eauto. apply Hrdx.
    eapply forall_result_has_shape.
    eapply Forall_app. split.
    eapply forall_firstn. eapply result_has_shape_forall. eauto.
    simpl. eapply Forall_repeat. eapply result_has_shape_gen_pad.
    rewrite app_length. simpl. rewrite firstn_length.
    rewrite repeat_length. erewrite result_has_shape_length by eauto.
    rewrite min_l by lia. rewrite sub_add. reflexivity. lia. lia.
    apply Hrdx. eauto. apply Henv. apply Hrdx. apply Hrdx.

    eapply partial_well_formed_allocation_result_V in Halloc. invs.
    assert (Forall (fun x => 0 <= x)%Z
                   (eval_Zexpr_Z_total $0 m
                                       ::(map (eval_Zexpr_Z_total $0) l0))).
    econstructor; eauto.
    eapply forall_nonneg_exists_zero_or_forall_pos_Z in H.
    invert H.
    { rewrite <- (rev_involutive l).
      rewrite <- (firstn_skipn (Z.to_nat (eval_Zexpr_Z_total $0 k)) (rev l)).
      rewrite rev_app_distr.
      eapply forall_firstn_ge with (m:=Z.to_nat (eval_Zexpr_Z_total $0 k))
        in H8.
      eapply forall_eq_gen_pad in H8. rewrite H8. simpl gen_pad_list.
      rewrite rev_repeat. rewrite firstn_length. rewrite rev_length.
      erewrite result_has_shape_length by eauto. rewrite min_l by lia.
      assert (eval_Zexpr_Z_total $0 k < eval_Zexpr_Z_total $0 m \/
                eval_Zexpr_Z_total $0 m <= eval_Zexpr_Z_total $0 k)%Z by lia.
      cases H.
      2: { rewrite skipn_all2. simpl.
           pose proof assign_no_overwrite_gen_pad.
           specialize H21 with
             (sh:= (Z.to_nat (eval_Zexpr_Z_total $0 k))
                     :: (map Z.to_nat (map (eval_Zexpr_Z_total $0) l0))).
           simpl gen_pad_list in H21. eapply H21. eauto.
           rewrite rev_length. erewrite result_has_shape_length by eauto.
           lia. }
      eapply assign_no_overwrite_trunc_r. eauto.
      rewrite rev_involutive.
      pose proof Hrdx. rewrite truncl_list_skipn.
      rewrite skipn_app. rewrite skipn_all2.
      2: { rewrite repeat_length. lia. }
      simpl. rewrite repeat_length. rewrite sub_diag. simpl.
      rewrite <- truncl_list_skipn. eauto. 
      eauto.
      eapply forall_result_has_shape. eapply Forall_app. split.
      eapply Forall_rev. eapply forall_skipn. eapply Forall_rev.
      eapply result_has_shape_forall; eauto.
      eapply Forall_repeat. eapply result_has_shape_gen_pad.
      rewrite app_length. rewrite rev_length. rewrite repeat_length.
      rewrite skipn_length. rewrite rev_length.
      erewrite result_has_shape_length by eauto. lia.
      eapply H4. lia. eauto. eapply H12. eauto. 
      lia. invert H20. eauto. eauto.
      rewrite <- truncl_list_skipn. eauto. lia. }
    invert H20. rewrite H21 in *. invert H5.
    eapply assign_no_overwrite_empty_tensor. eauto.
    eapply assign_no_overwrite_tensor_shape_0. eauto. eauto. eauto.
    apply Hrdx.
  - simpl in *. invs. invert Hpad. erewrite size_of_sizeof in * by eauto.
    eq_size_of. simpl in *.
    pose proof H2.
    eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H5;
      eauto. simpl in *.
    pose proof H2.
    eapply constant_nonneg_bounds_size_of_no_vars in H7; eauto. invert H7.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
      with (v:=$0) in H12,H4.
    pose proof H2.
    eapply constant_nonneg_bounds_size_of_nonneg in H7; eauto.
    2: { econstructor. eapply H12 with (v:=v). econstructor.
         eapply forall_no_vars_eval_Zexpr_Z_total. eauto. }
    invert H7. pose proof H8.
    eapply has_pad_gen_pad in H8; eauto.
    2: { eapply contexts_agree_result_has_shape; eauto. }
    simpl in H8. invs.
    eapply eval_Zexpr_Z_eval_Zexpr in H. eapply H4 in H. invert H.

    eapply IHeval_expr in H2; eauto.
    rewrite <- (firstn_skipn
                   (Z.to_nat (eval_Zexpr_Z_total $0 k)) l).
    eapply forall_firstn_ge with (m:= Z.to_nat (eval_Zexpr_Z_total $0 k))
      in H10.
    2: { lia. }
    eapply forall_eq_gen_pad in H10. rewrite H10.
    simpl gen_pad_list.
    
    rewrite firstn_length. 
    erewrite result_has_shape_length.
    2: { eauto. } 

    rewrite min_l by lia.
    eapply partial_well_formed_reindexer_truncl.
    rewrite <- truncl_list_skipn. eauto. simpl.
    eapply forall_result_has_shape.
    eapply Forall_app. split.
    simpl. eapply Forall_repeat. eapply result_has_shape_gen_pad.
    eapply forall_skipn. eapply result_has_shape_forall. eauto.
    rewrite app_length. simpl. rewrite skipn_length.
    rewrite repeat_length. erewrite result_has_shape_length by eauto.
    rewrite le_plus_minus_r. reflexivity. lia.
    apply Henv. eauto. lia. lia.

    rewrite <- (firstn_skipn (Z.to_nat (eval_Zexpr_Z_total $0 k)) l).
    eapply forall_firstn_ge with (m:= Z.to_nat (eval_Zexpr_Z_total $0 k))
      in H10.
    2: { lia. }
    eapply forall_eq_gen_pad in H10. rewrite H10.
    simpl gen_pad_list.

    rewrite firstn_length.
    erewrite result_has_shape_length by eauto.

    rewrite min_l by lia.    
    eapply partial_well_formed_allocation_truncl.
    erewrite <- truncl_list_skipn. eauto. apply Hrdx.
    simpl. eapply forall_result_has_shape.
    eapply Forall_app. split.
    simpl. eapply Forall_repeat. eapply result_has_shape_gen_pad.
    eapply forall_skipn. eapply result_has_shape_forall. eauto.
    rewrite app_length. simpl. rewrite skipn_length.
    rewrite repeat_length. erewrite result_has_shape_length by eauto.
    rewrite le_plus_minus_r. reflexivity. lia. lia.
    apply Hrdx. eauto. eauto. apply Henv. apply Hrdx. apply Hrdx.

eapply partial_well_formed_allocation_result_V in Halloc. invs.
    assert (Forall (fun x => 0 <= x)%Z
                   (eval_Zexpr_Z_total $0 m
                                       ::(map (eval_Zexpr_Z_total $0) l0))).
    econstructor; eauto.
    eapply forall_nonneg_exists_zero_or_forall_pos_Z in H.
    invert H.
    { rewrite <- (firstn_skipn (Z.to_nat (eval_Zexpr_Z_total $0 k)) l).
      eapply forall_firstn_ge with (m:=Z.to_nat (eval_Zexpr_Z_total $0 k))
        in H10.
      eapply forall_eq_gen_pad in H10. rewrite H10. simpl gen_pad_list.
      rewrite firstn_length.
      erewrite result_has_shape_length by eauto. rewrite min_l by lia.
      assert (eval_Zexpr_Z_total $0 k < eval_Zexpr_Z_total $0 m \/
                eval_Zexpr_Z_total $0 m <= eval_Zexpr_Z_total $0 k)%Z by lia.
      cases H.
      2: { rewrite skipn_all2. simpl.
           pose proof assign_no_overwrite_gen_pad.
           specialize H21 with
             (sh:= (Z.to_nat (eval_Zexpr_Z_total $0 k))
                     :: (map Z.to_nat (map (eval_Zexpr_Z_total $0) l0))).
           simpl gen_pad_list in H21. rewrite app_nil_r. eapply H21. eauto.
           erewrite result_has_shape_length by eauto. lia. }
      eapply assign_no_overwrite_trunc_l. eauto.
      rewrite <- truncl_list_skipn. eauto.
      rewrite <- truncl_list_skipn. eauto.
      eauto. eauto.
      simpl.
      eapply forall_result_has_shape. eapply Forall_app. split.
      eapply Forall_repeat. eapply result_has_shape_gen_pad.
      eapply forall_skipn. eapply result_has_shape_forall; eauto.
      rewrite app_length. rewrite repeat_length.
      rewrite skipn_length.
      erewrite result_has_shape_length by eauto. lia.
      eapply H4. lia. eauto. invert H20. eauto. eassumption. eauto. lia. }
    invert H20. rewrite H21 in *. invert H5.
    eapply assign_no_overwrite_empty_tensor. eauto.
    eapply assign_no_overwrite_tensor_shape_0. eauto. eauto. eauto.
    apply Hrdx.
  - invert Hsize. eq_size_of. invert H4. invert Hconst. invs. pose proof H4.
    invert Hpad.
    + eq_size_of. invert H8.
      eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H2;
        eauto.
      invert H2. 2: lia.
      eapply IHeval_expr in H5; eauto.
      { decomp_partial_well_formed_reindexer. propositional.
        - unfold result_shape_Z. unfold partial_injective. simpl.
          propositional.
        - eapply HeqZlist. cases l1; cases l2.
          eauto. invert H8. simpl in *. lia.
          eauto. invert H8. simpl in *. lia.
          cases p0. cases p1.
          erewrite <- eq_Z_tuple_index_list_cons_tup in H8. invs.
          erewrite <- eq_Z_tuple_index_list_cons_tup. split. eauto. split.
          eapply eq_zexpr_add; eauto. eauto.
        - rewrite Hmap by eauto. cases l; eauto. simpl.
          cases p0. simpl. f_equal. f_equal.
          unfold subst_var_in_Z_tup. simpl. f_equal.
          f_equal. eapply subst_var_in_Zexpr_id. rewrite H6. sets.
        - rewrite Hvarsarg. cases l; eauto. cases p0. simpl.
          rewrite H6. simpl. repeat rewrite app_no_dups_empty_r.
          reflexivity. }
      { unfold partial_well_formed_allocation.
        cases (shape_to_index (result_shape_Z (V []))
                              (shape_to_vars (result_shape_Z (V [])))).
        eapply shape_to_index_not_empty_Z in Heq. propositional.
        cases (reindexer (let (v0, d) := p0 in ((v0)%z, (d + k)%z) :: l)).
        { eapply reindexer_not_empty_vars_in_index in Heq0. propositional.
          apply Hrdx.
          unfold not. intros.
          unfold shape_to_index, shape_to_vars, result_shape_Z in *.
          simpl in Heq. invert Heq. simpl in H2.
          eapply cup_empty in H2. invs.
          eapply cup_empty in H8. invs.
          rewrite H6 in *. simpl in *. rewrite app_no_dups_empty_r in *.
          eapply constant_not_empty in H2. propositional.
          inversion 1. }
        pose proof Halloc.
        eapply partial_well_formed_allocation_result_V in H2. invs.
        eexists. split. eassumption. unfold result_shape_Z. simpl. sets.
        apply Hrdx. }
      { eapply partial_well_formed_allocation_result_V in Halloc. invs.
        eapply assign_no_overwrite_empty_tensor. eauto. apply Hrdx. }
    + eq_size_of. invert H8.
      eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H2;
        eauto.
      eapply IHeval_expr in H5; eauto.
      { eapply partial_well_formed_reindexer_padr. eauto.
        simpl gen_pad_list in *.
        eapply constant_nonneg_bounds_size_of_no_vars in H1; eauto.
        eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H1.
        invert H1. eq_eval_Zlist.
        eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total with (v:=$0)
          in H6.
        eapply eval_Zexpr_Z_eval_Zexpr in H. eapply H6 in H. invert H.
        eauto.
        eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. lia.
        apply Henv. }
      { eapply partial_well_formed_allocation_padr. eauto.
        eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. lia.
        eapply constant_nonneg_bounds_size_of_no_vars in H1; eauto.
        eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H1.
        invert H1. eq_eval_Zlist.
        eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total with (v:=$0)
          in H6.
        eapply eval_Zexpr_Z_eval_Zexpr in H. eapply H6 in H. invert H.
        simpl gen_pad_list in *. eauto. apply Hrdx. apply Henv.
        apply Hrdx. apply Hrdx. apply Hrdx. }
      { simpl gen_pad_list in *.
        eapply partial_well_formed_allocation_result_V in Halloc. invs.
        pose proof H5.
        eapply constant_nonneg_bounds_size_of_no_vars in H8; eauto.
        eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H8.
        invert H8. eq_eval_Z. eq_eval_Zlist.
        eapply eval_Zexpr_Z_eval_Zexpr in H.
        eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
          with (v:=$0) in H6. eapply H6 in H. invert H.
        eapply assign_no_overwrite_pad_r; eauto.
        simpl. propositional. apply H6. 
        eapply constant_nonneg_bounds_size_of_nonneg in H5.
        2: { eauto. }
        2: { econstructor. eauto. eauto. }
        invert H5. auto.
        eapply constant_nonneg_bounds_size_of_no_vars in H5.
        2: { eauto. }
        invert H5. auto.
        eapply constant_nonneg_bounds_size_of_no_vars in H5; eauto. invert H5.
        eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
        apply Hrdx. }
  - invert Hsize. eq_size_of. invert H4. invert Hconst. invs. pose proof H4.
    invert Hpad.
    + eq_size_of. invert H8.
      eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H2;
        eauto.
      invert H2. 2: lia.
      eapply IHeval_expr in H5; eauto.
      { decomp_partial_well_formed_reindexer. propositional.
        - unfold result_shape_Z. unfold partial_injective. simpl.
          propositional.
        - eapply HeqZlist. cases l1; cases l2.
          eauto. invert H8. simpl in *. lia.
          eauto. invert H8. simpl in *. lia.
          cases p0. cases p1.
          erewrite <- eq_Z_tuple_index_list_cons_tup in H8. invs.
          erewrite <- eq_Z_tuple_index_list_cons_tup. split.
          eapply eq_zexpr_add; eauto. split.
          eapply eq_zexpr_add; eauto. eauto.
        - rewrite Hmap by eauto. cases l; eauto. simpl.
          cases p0. simpl. f_equal. f_equal.
          unfold subst_var_in_Z_tup. simpl. f_equal.
          f_equal. eapply subst_var_in_Zexpr_id. rewrite H6. sets.
          f_equal. eapply subst_var_in_Zexpr_id. rewrite H6. sets.
        - rewrite Hvarsarg. cases l; eauto. cases p0. simpl.
          rewrite H6. simpl. repeat rewrite app_no_dups_empty_r.
          reflexivity. }
      { unfold partial_well_formed_allocation.
        cases (shape_to_index (result_shape_Z (V []))
                              (shape_to_vars (result_shape_Z (V [])))).
        eapply shape_to_index_not_empty_Z in Heq. propositional.
        cases (reindexer (let (v0, d) := p0 in ((v0 + k)%z, (d + k)%z) :: l)).
        { eapply reindexer_not_empty_vars_in_index in Heq0. propositional.
          apply Hrdx.
          unfold not. intros.
          unfold shape_to_index, shape_to_vars, result_shape_Z in *.
          simpl in Heq. invert Heq. simpl in H2.
          eapply cup_empty in H2. invs.
          eapply cup_empty in H8. invs.
          rewrite H6 in *. simpl in *. rewrite app_no_dups_empty_r in *.
          eapply constant_not_empty in H2. propositional.
          inversion 1. }
        pose proof Halloc. rewrite app_nil_r in *.
        eapply partial_well_formed_allocation_result_V in H2. invs.
        eexists. split. eassumption. unfold result_shape_Z. simpl. sets.
        apply Hrdx. }
      { eapply partial_well_formed_allocation_result_V in Halloc. invs.
        eapply assign_no_overwrite_empty_tensor. eauto. apply Hrdx. }
    + eq_size_of. invert H8.
      eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H2;
        eauto.
      
      simpl gen_pad_list in *.
      pose proof H1 as Hsize.
      eapply constant_nonneg_bounds_size_of_no_vars in H1; eauto.
      eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H1.
      invert H1. eq_eval_Zlist.
      eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total with (v:=$0)
        in H6.
      eapply eval_Zexpr_Z_eval_Zexpr in H. eapply H6 in H. invert H.
        
      eapply IHeval_expr in H5; eauto.
      { eapply partial_well_formed_reindexer_padl. apply Hrdx.
        simpl map in *. eauto. apply Henv. eauto.
        eapply constant_nonneg_bounds_size_of_no_vars in H5; eauto.
        invert H5.
        eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. lia.
        lia. apply Hrdx. apply Hrdx. apply Hrdx. apply Hrdx. }
      { eapply partial_well_formed_allocation_padl. eauto. eauto.
        apply Hrdx. lia. lia. apply Hrdx. eauto.
        eapply constant_nonneg_bounds_size_of_no_vars in Hsize; eauto.
        invert Hsize. 
        eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
        apply Henv. apply Hrdx. apply Hrdx. }
      { simpl gen_pad_list in *.
        eapply partial_well_formed_allocation_result_V in Halloc. invs.
        pose proof H5.
        eapply constant_nonneg_bounds_size_of_no_vars in H; eauto.
        eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H.
        invert H. eq_eval_Z. eq_eval_Zlist.
        eapply assign_no_overwrite_pad_l; eauto.
        simpl. propositional. apply H6.
        eapply constant_nonneg_bounds_size_of_nonneg in H5.
        2: { eauto. }
        2: { econstructor. eauto. eauto. }
        invert H5. auto.
        eapply constant_nonneg_bounds_size_of_no_vars in H5.
        2: { eauto. }
        invert H5. auto.
        eapply constant_nonneg_bounds_size_of_no_vars in H5.
        2: { eauto. } invert H5. eauto.
        apply H6. apply Hrdx.
      }
  - simpl in *. invert Hsize.
    pose proof Halloc as Halloc1.
    unfold partial_well_formed_allocation in Halloc.
    unfold result_shape_Z, shape_to_index in Halloc. simpl in *.
    cases (reindexer []).
    + invs. pose proof H.
      eapply eval_Sexpr_eval_Sstmt_exists in H1; eauto.
      cases asm.
      * eapply lower_correct_weak with (e:= Scalar s) in Hrdx; eauto.
        2: { econstructor. eauto. }
        2: { simpl.
             econstructor. eauto. eauto.
             invert Hpad. eauto. }
        unfold result_shape_Z, shape_to_index, shape_to_vars in Hrdx.
        simpl in Hrdx. rewrite Heq in *. invs.
        rewrite H0 in *. 
        eexists. eexists. econstructor. eauto. eassumption. auto.
      * eapply lower_correct_weak with (e:= Scalar s) in Hrdx; eauto.
        2: { econstructor. eauto. }
        2: { simpl.
             econstructor. eauto. eauto.
             invert Hpad. eauto. }
        unfold result_shape_Z, shape_to_index, shape_to_vars in Hrdx.
        simpl in Hrdx. rewrite Heq in *. invs.
        rewrite H0 in *. 
        eexists. eexists. econstructor. eauto. eassumption. auto.
    + cases r.
      2: { invert H. cases r; try discriminate.
           cases r; try discriminate.
           cases r1; cases r2; try discriminate.
           cases r1; cases r2; try discriminate.
           cases r1; cases r2; try discriminate.
           cases r1; cases r2; try discriminate. }
      simpl in *. rewrite map_id in *.
      unfold shape_to_index, shape_to_vars in *. simpl in *.
      rewrite Heq in *. pose proof H.
      eapply eval_Sexpr_eval_Sstmt_exists in H; eauto.
      cases asm.
      * invs. pose proof Hrdx as Hsnd.
        rewrite eval_Zexprlist_map_match_fst_map_eval_Zexpr_Z_tup_total
          in H3.
        rewrite eval_Zexprlist_map_match_snd_map_eval_Zexpr_Z_tup_total
          in H3.
        eapply dom_lookup_Some in H3. invs.                      
        
        eapply lower_correct_weak with (e:= Scalar s) in Hsnd; eauto.
        2: { econstructor. eauto. }
        2: { simpl. eapply EvalAssignV. eauto. rewrite Heq. inversion 1.
             eapply H2.
             eapply eval_Zexpr_Z_flatten_index_flatten.
             eapply eval_Zexprlist_map_partially_eval_Zexpr.
             eapply forall_no_vars_eval_Zexpr_Z_total.
             decomp_partial_well_formed_reindexer.
             eapply Forall_map. eapply Forall_forall.
             intros.
             eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.
             eapply subseteq_transitivity.
             eapply snd_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
             eauto.
             eapply eval_Zexprlist_map_partially_eval_Zexpr.
             eapply forall_no_vars_eval_Zexpr_Z_total.
             decomp_partial_well_formed_reindexer.
             eapply Forall_map. eapply Forall_forall.
             intros.
             eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.             
             eapply subseteq_transitivity.
             eapply fst_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
             eauto.
             eassumption. }
        eexists. eexists. eapply EvalAssignV.
        unfold shape_to_index, shape_to_vars, result_shape_Z in *.
        simpl in *. rewrite Heq in *. unfold lookup_total in *.
        rewrite H2 in *. invs. eauto. inversion 1. eauto.
        rewrite <- Heq in *.

        decomp_partial_well_formed_reindexer.
        eapply eval_Zexpr_Z_flatten_index_flatten.
        eapply eval_Zexprlist_map_partially_eval_Zexpr.
        eapply forall_no_vars_eval_Zexpr_Z_total.
        eapply Forall_map. eapply Forall_forall.
        intros.
        eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.
        eapply subseteq_transitivity.
        eapply snd_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
        eauto.
        eapply eval_Zexprlist_map_partially_eval_Zexpr.
        eapply forall_no_vars_eval_Zexpr_Z_total.
        eapply Forall_map. eapply Forall_forall.
        intros.
        eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.             
        eapply subseteq_transitivity.
        eapply fst_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
        eauto.

        eassumption. rewrite <- Heq.
        rewrite map_snd_map_partially_eval_Z_tup.
        rewrite map_fst_map_partially_eval_Z_tup. sets.
        rewrite <- Heq in *.
        eapply eval_Zexprlist_map_partially_eval_Zexpr.
        eapply forall_no_vars_eval_Zexpr_Z_total.
        decomp_partial_well_formed_reindexer.
        rewrite map_snd_map_partially_eval_Z_tup.
        eapply Forall_map. eapply Forall_forall. intros.
        eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.
        eapply subseteq_transitivity.
        eapply snd_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
        eauto.
        eapply eval_Zexprlist_map_partially_eval_Zexpr.
        eapply forall_no_vars_eval_Zexpr_Z_total.
        decomp_partial_well_formed_reindexer.
        rewrite map_fst_map_partially_eval_Z_tup.
        eapply Forall_map. eapply Forall_forall. intros.
        eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.
        eapply subseteq_transitivity.
        eapply fst_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
        eauto.
        rewrite <- Heq in *. eauto.
        rewrite <- Heq in *.
        eapply eval_Zexprlist_map_partially_eval_Zexpr.
        eapply forall_no_vars_eval_Zexpr_Z_total.
        decomp_partial_well_formed_reindexer.
        rewrite map_snd_map_partially_eval_Z_tup.
        eapply Forall_map. eapply Forall_forall. intros.
        eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.
        eapply subseteq_transitivity.
        eapply snd_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
        eauto.
        rewrite <- Heq in *.
        eapply eval_Zexprlist_map_partially_eval_Zexpr.
        eapply forall_no_vars_eval_Zexpr_Z_total.
        decomp_partial_well_formed_reindexer.
        rewrite map_fst_map_partially_eval_Z_tup.
        eapply Forall_map. eapply Forall_forall. intros.
        eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.
        eapply subseteq_transitivity.
        eapply fst_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
        eauto.
      * invs. pose proof Hrdx as Hsnd.
        rewrite eval_Zexprlist_map_match_fst_map_eval_Zexpr_Z_tup_total
          in H3.
        rewrite eval_Zexprlist_map_match_snd_map_eval_Zexpr_Z_tup_total
          in H3.
        eapply dom_lookup_Some in H3. invs.                      
        eapply lower_correct_weak with (e:= Scalar s) in Hrdx; eauto.
        2: { econstructor. eauto. }
        2: { simpl. eapply EvalReduceV. eauto. rewrite Heq. inversion 1.
             eauto.
             eapply eval_Zexpr_Z_flatten_index_flatten.
             eapply eval_Zexprlist_map_partially_eval_Zexpr.
             eapply forall_no_vars_eval_Zexpr_Z_total.
             decomp_partial_well_formed_reindexer.
             eapply Forall_map. eapply Forall_forall.
             intros.
             eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.
             eapply subseteq_transitivity.
             eapply snd_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
             eauto.
             eapply eval_Zexprlist_map_partially_eval_Zexpr.
             eapply forall_no_vars_eval_Zexpr_Z_total.
             decomp_partial_well_formed_reindexer.
             eapply Forall_map. eapply Forall_forall.
             intros.
             eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.             
             eapply subseteq_transitivity.
             eapply fst_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
             eauto.
             eassumption. }
        eexists. eexists. eapply EvalReduceV.
        unfold shape_to_index, shape_to_vars, result_shape_Z in *.
        simpl in *. rewrite Heq in *. unfold lookup_total in *.
        rewrite H2 in *. invs. eauto. inversion 1. eauto.
        rewrite <- Heq in *.

        decomp_partial_well_formed_reindexer.
        eapply eval_Zexpr_Z_flatten_index_flatten.
        eapply eval_Zexprlist_map_partially_eval_Zexpr.
        eapply forall_no_vars_eval_Zexpr_Z_total.
        eapply Forall_map. eapply Forall_forall.
        intros.
        eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.
        eapply subseteq_transitivity.
        eapply snd_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
        eauto.
        eapply eval_Zexprlist_map_partially_eval_Zexpr.
        eapply forall_no_vars_eval_Zexpr_Z_total.
        eapply Forall_map. eapply Forall_forall.
        intros.
        eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.             
        eapply subseteq_transitivity.
        eapply fst_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
        eauto.

        eassumption. rewrite <- Heq.
        rewrite map_snd_map_partially_eval_Z_tup.
        rewrite map_fst_map_partially_eval_Z_tup. sets.
        rewrite <- Heq in *.
        eapply eval_Zexprlist_map_partially_eval_Zexpr.
        eapply forall_no_vars_eval_Zexpr_Z_total.
        decomp_partial_well_formed_reindexer.
        rewrite map_snd_map_partially_eval_Z_tup.
        eapply Forall_map. eapply Forall_forall. intros.
        eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.
        eapply subseteq_transitivity.
        eapply snd_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
        eauto.
        eapply eval_Zexprlist_map_partially_eval_Zexpr.
        eapply forall_no_vars_eval_Zexpr_Z_total.
        decomp_partial_well_formed_reindexer.
        rewrite map_fst_map_partially_eval_Z_tup.
        eapply Forall_map. eapply Forall_forall. intros.
        eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.
        eapply subseteq_transitivity.
        eapply fst_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
        eauto.
        rewrite <- Heq in *. eauto.
        rewrite <- Heq in *.
        eapply eval_Zexprlist_map_partially_eval_Zexpr.
        eapply forall_no_vars_eval_Zexpr_Z_total.
        decomp_partial_well_formed_reindexer.
        rewrite map_snd_map_partially_eval_Z_tup.
        eapply Forall_map. eapply Forall_forall. intros.
        eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.
        eapply subseteq_transitivity.
        eapply snd_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
        eauto.
        rewrite <- Heq in *.
        eapply eval_Zexprlist_map_partially_eval_Zexpr.
        eapply forall_no_vars_eval_Zexpr_Z_total.
        decomp_partial_well_formed_reindexer.
        rewrite map_fst_map_partially_eval_Z_tup.
        eapply Forall_map. eapply Forall_forall. intros.
        eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.
        eapply subseteq_transitivity.
        eapply fst_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
        eauto.
        Unshelve. eauto. eauto.
Qed.
   
