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
From Lower Require Import
     Zexpr Bexpr Array Range Sexpr Result ListMisc Meshgrid VarGeneration
     Injective Constant InterpretReindexer WellFormedEnvironment WellFormedReindexer WellFormedAllocation
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
       rewrite length_map; rewrite length_nat_range_rec;
       eapply length_mesh_grid_indices; eassumption : reindexers.
Arguments flatten : simpl nomatch.

Lemma eval_Sexpr_eval_Sstmt_exists
     : forall (v : valuation) (ec : expr_context) 
         (s : Sexpr) (r : scalar_result),
       eval_Sexpr v ec s r ->
       forall (st : stack) (h : heap) sh,
       contexts_agree ec st h sh ->
       eval_Sstmt v st h (lowerS s sh) match r with
                                       | SS s0 => s0
                                       | SX => 0%R
                                       end.
Proof.
  induct 1; intros; simpl in *.
  - econstructor. eapply H0 in H. invs. rewrite H2. f_equal.
    cases r; auto.
  - eapply H1 in H. invs'. rewrite H.
    pose proof H0 as H0'. eapply eval_get_eval_Zexprlist in H0'. invs'.
    assert (length x0 = length l).
    { eapply eval_get_length in H0; eauto. }
    econstructor. eauto.
    eapply eval_Zexpr_Z_eval_Zexpr.
    eapply eval_Zexpr_Z_flatten_index_flatten.
    rewrite map_snd_combine by (rewrite length_map; auto). eauto.
    eapply flatten_sh_nonneg. eapply eval_get_In_meshgrid in H0.
    erewrite result_has_shape_result_shape_Z in H0.
    2: { eauto. }
    repeat decomp_index. rewrite map_fst_combine by (rewrite length_map; auto).
    eassumption.
    eapply result_has_shape_self; eauto. eauto.
    replace (map Z.of_nat (filter_until x0 0)) with (result_shape_Z (V rs)).
    2: { erewrite result_has_shape_result_shape_Z by eauto. reflexivity. }
    rewrite tensor_to_array_delta_partial_interpret_reindexer_flatten.
    unfold array_add.
    rewrite lookup_merge.
    erewrite result_has_shape_result_shape_Z by eauto.
    pose proof H0 as H0'. eapply eval_get_In_meshgrid in H0'; eauto.
    erewrite result_has_shape_result_shape_Z in H0' by eauto.
    rewrite mesh_grid_filter_until in *.
    2: { eapply result_has_shape_self; eauto. }
    rewrite map_fst_combine in * by (rewrite length_map; auto).
    rewrite filter_until_0_id.
    2: { eapply mesh_grid_shape_pos in H0'. rewrite Forall_map in H0'.
         eapply Forall_impl. 2: eassumption. simpl. lia. }
    rewrite result_lookup_Z_tensor_to_array_delta in *.
    2: { eapply result_has_shape_self; eauto. }
    2: { erewrite result_has_shape_result_shape_Z by eauto.
         decomp_goal_index. assumption. }
    2: { erewrite result_has_shape_result_shape_Z by eauto.
         rewrite mesh_grid_filter_until. unfold injective. intros. invs.
         eapply injective_flatten. eauto. eauto. eauto. }
    cases x0. invert H2.
    pose proof (lookup_alloc_array
                      (Z.to_nat (fold_left Z.mul (map Z.of_nat (n :: x0)) 1%Z))
                      (flatten (map Z.of_nat (n :: x0)) x1)) as H7.
    pose proof H0' as H0''. rewrite map_cons in *.
    eapply in_mesh_grid_args_flatten_bounds in H0'.
    destruct H7 as [H7|H7].
    + eapply lookup_None_dom in H7.
      rewrite dom_alloc_array in H7.
      rewrite Z2Nat.id in H7.
      2: { eapply fold_left_mul_nonneg. eapply mesh_grid_shape_pos in H0''.
           eapply Forall_impl. 2: eassumption. simpl. lia. lia. }
      exfalso. apply H7.
      erewrite <- In_iff_in.
      eapply in_mesh_grid_flatten_in_range.
      eapply mesh_grid_shape_pos in H0''.
      eapply Forall_impl. 2: eassumption. simpl. lia.
      eauto.
    + rewrite H7.
      pose proof H0 as H9. eapply eval_get_lookup_result_Z in H9; eauto.
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
    forall v ec r,
      (* functional evaluation of ATL *)
      eval_expr v ec e r ->
      forall l, size_of e l ->
      forall p st h reindexer asn sh,
        (* imperative evaluation of lowering *)
        (* our environment is well-formed *)
        well_formed_environment st h p sh v (vars_of e) ec ->
        (* reindexer is well-formed *)
        well_formed_reindexer reindexer v r st h p asn ->
        (* allocation is well-formed *)
        well_formed_allocation reindexer r st h p v ->
        (* expr context and imperative state agree *)
        contexts_agree ec st h sh ->
        forall pads g,
          has_pad v g e pads ->
        (forall pads (x : var) (r0 : result),
            g $? x = Some pads ->
            ec $? x = Some r0 ->
            relate_pads pads r0 (result_shape_nat r0)) ->
        exists st' h', eval_stmt v st h (lower e reindexer p asn sh) st' h'.
Proof.
  intros e v ec r.
  induct 1; intros ls Hsize p st h reindexer asm sh
                   Henv Hrdx Halloc Hctx pads g Hpad Hrelate.
  - simpl. eexists. eexists. eapply EvalForBase; eauto.
  - simpl in *. invs.

    rename H13 into Hsize.
    rename H11 into Hlo. rename H12 into Hhi.
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'.
    eapply eval_Zexpr_includes_valuation in Hlo', Hhi'; try apply empty_includes.
    apply eval_Zexpr_Z_eval_Zexpr in Hlo', Hhi'. rewrite Hlo', Hhi' in *. invs'.
    apply eval_Zexpr_Z_eval_Zexpr in Hlo, Hhi.

    invert Hpad. eq_size_of. pose proof Hsize as Hsize'.
    cbv [eval_Zexpr_Z_total] in *. cbn [eval_Zexpr_Z] in *. rewrite Hhi, Hlo in *.
    cases k.
    2: { eapply IHeval_expr1 in Hsize; eauto.
         2: { eapply well_formed_environment_add_valuation; eauto. }
         2: { eapply well_formed_allocation_result_V in Halloc. 
              invert Halloc.
              eapply well_formed_reindexer_eval0 with (hi := hiz) (lo := loz); eauto.
              apply Henv.
              eapply result_has_shape_self.
              eapply size_of_eval_expr_result_has_shape.
              2: { eapply EvalGenStep. eapply Hlo'.
                   eapply Hhi'. lia. eassumption. eauto. eauto. eauto. }
              econstructor. 1,2: apply eval_Zexpr_Z_eval_Zexpr; eauto. eauto.
              unfold not. intros. apply H3.
              eapply shape_to_vars_contains_substring. eauto.
              simpl length.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite Hhi', Hlo'. reflexivity. }
              rewrite H5. lia. apply H. apply Hrdx. }
         2: { pose proof Halloc.
              eapply well_formed_allocation_result_V in H. invs.
              eapply well_formed_allocation_eval_step. eauto. eauto.
              eapply Hrdx. eapply Henv. eapply Hrdx. eapply Hrdx. eapply Hrdx.
              eapply result_has_shape_self.
              eapply size_of_eval_expr_result_has_shape.
              2: { eapply EvalGenStep.
                   eapply Hlo'. eapply Hhi'. all: eauto. }
              econstructor. 1,2: apply eval_Zexpr_Z_eval_Zexpr; eauto.
              eauto. eauto. eauto. eauto.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite Hhi', Hlo'. reflexivity. }
              rewrite H5. lia.
              eapply Hrdx. eapply Hrdx.
         }
         2: { eapply H17; lia. }
         invs'.
         pose proof H0 as Hfirst.
         eapply lower_correct_weak in H0.
         2: { eauto. }
         2: { eauto. }
         2: { eapply well_formed_environment_add_valuation; eauto. }
         2: { eapply well_formed_allocation_result_V in Halloc. invs.
              eapply well_formed_reindexer_eval0; eauto. apply Henv.
              eapply result_has_shape_self.
              eapply size_of_eval_expr_result_has_shape.
              2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
              econstructor. 1,2: apply eval_Zexpr_Z_eval_Zexpr; eauto. eauto.
              unfold not. intros. eapply H3.
              eapply shape_to_vars_contains_substring; eauto.
              simpl.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite Hhi', Hlo'. reflexivity. }
              rewrite H5. lia.
              apply Hrdx.
         }
         2: { pose proof Halloc.
              eapply well_formed_allocation_result_V in H. invs'.
              eapply well_formed_allocation_eval_step; eauto.
              eapply Hrdx. eapply Henv. eapply Hrdx. eapply Hrdx.
              eapply Hrdx.
              eapply result_has_shape_self.
              eapply size_of_eval_expr_result_has_shape.
              2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
              econstructor. 1,2: apply eval_Zexpr_Z_eval_Zexpr; eauto. eauto.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite Hhi', Hlo'. reflexivity. }
              rewrite H5. lia.
              apply Hrdx. apply Hrdx. }
         2: { eauto. }
         2: { eapply H17; lia. }
         2: { eauto. }
         cases (reindexer
           (((! i ! - | loz |)%z, (hiz - loz)%Z)
              :: shape_to_index (result_shape_Z r)
              (shape_to_vars (result_shape_Z r)))).
         { eapply reindexer_not_empty_vars_in_index in Heq. invert Heq.
           apply Hrdx.
           simpl. intro. cups_empty. }
         pose proof Halloc.
         eapply well_formed_allocation_result_V in H.
         invs.
         eassert (size_of _ _) as Hsize1.
         2: eapply IHeval_expr2 with (reindexer:=
                                        fun l =>
                                          (shift_top_dim_reindexer reindexer l))
           in Hsize1.
         { econstructor; eauto.
           apply eval_Zexpr_Z_eval_Zexpr. simpl. rewrite Hlo. reflexivity.
           apply eval_Zexpr_Z_eval_Zexpr. eassumption. }
         3: { pose proof Halloc as Halloc2.
              eapply well_formed_allocation_result_V in Halloc.
              eapply well_formed_reindexer_shift_top_dim_reindexer
              with (lo:=loz) (hi:=hiz).
              eauto. apply Henv.
              eapply result_has_shape_self.
              eapply size_of_eval_expr_result_has_shape.
              2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
              econstructor. eauto. 1,2: apply eval_Zexpr_Z_eval_Zexpr; eauto.
              all: eauto.
              erewrite result_has_shape_length.
              2: { eapply size_of_eval_expr_result_has_shape in H5.
                   2: eauto. eauto. }
              lia.
              apply Hrdx. }
         3: { eapply well_formed_allocation_shift_top_dim_reindexer.
              eauto. eauto. apply Hrdx. apply Henv. apply Hrdx.
              apply Hrdx. apply Hrdx.
              eapply result_has_shape_self.
              eapply size_of_eval_expr_result_has_shape.
              2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
              econstructor; eauto. 1,2: apply eval_Zexpr_Z_eval_Zexpr; eauto.
              apply Hrdx. }
         2: { eapply well_formed_environment_add_heap. eauto. eauto. }
         2: { eapply contexts_agree_add_heap; try apply Henv; eauto. }
         2: { eapply HasPadGen with (k:=k) (c:=c) (ll:=ll) (rr:=rr).
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
              eauto.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo.
              intros. apply H14; lia.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hhi.
              intros. apply H16; lia.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
              intros. apply H17; lia.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
              intros. lia. }
         2: { eauto. }
         2: apply Hrdx.
         invs'.
         eexists. eexists.
         eapply EvalForStep.
         eassumption. eassumption.
         lia.
         pose proof Hfirst.
         eapply Hfirst.
         unfold shift_top_dim_reindexer in *.
         unfold lookup_total. rewrite H.
         eapply eq_eval_stmt_for. eassumption.
         simpl. rewrite Hlo'. reflexivity.
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
         apply eq_zexpr_sub_literal.
         apply eq_zexpr_id. f_equal. f_equal. lia.
         split. lia.
         eapply eq_Z_tuple_index_list_id. }
    simpl Z.of_nat in *. rewrite Z.sub_0_r in *.
    cases ll.
    2: { eapply IHeval_expr1 in Hsize'; eauto.
         2: { eapply well_formed_environment_add_valuation; eauto. }
         2: { pose proof Halloc as Halloc2.
              eapply well_formed_allocation_result_V in Halloc2. invs'.
              eapply well_formed_reindexer_eval0; eauto. apply Henv.
              eapply result_has_shape_self.
              eapply size_of_eval_expr_result_has_shape.
              2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
              econstructor; eauto. 1,2: apply eval_Zexpr_Z_eval_Zexpr; eauto.
              unfold not. intros. eapply H3.
              eapply shape_to_vars_contains_substring; eauto.
              simpl.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite Hhi', Hlo'. reflexivity. }
              rewrite H5. lia.
              apply Hrdx. }
         2: { pose proof Halloc.
              eapply well_formed_allocation_result_V in H. invs'.
              eapply well_formed_allocation_eval_step. eauto. eauto.
              eapply Hrdx. eapply Henv. eapply Hrdx. eapply Hrdx. eapply Hrdx.
              eapply result_has_shape_self.
              eapply size_of_eval_expr_result_has_shape.
              2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
              econstructor. eauto. 1,2: apply eval_Zexpr_Z_eval_Zexpr; eauto.
              all: eauto.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite Hhi', Hlo'. reflexivity. }
              rewrite H5. lia.
              eapply Hrdx. eapply Hrdx.
         }
         2: { apply H14; lia. }
         invs'.
         pose proof H0 as Hfirst.
         eapply lower_correct_weak in H0.
         2: { eauto. }
         2: { eauto. }
         2: { eapply well_formed_environment_add_valuation; eauto. }
         2: { pose proof Halloc as Halloc2.
              eapply well_formed_allocation_result_V in Halloc2. invs'.
              eapply well_formed_reindexer_eval0; eauto. apply Henv.
              eapply result_has_shape_self.
              eapply size_of_eval_expr_result_has_shape.
              2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
              econstructor; eauto. 1,2: apply eval_Zexpr_Z_eval_Zexpr; eauto.
              unfold not. intros. eapply H3.
              eapply shape_to_vars_contains_substring; eauto.
              simpl.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite Hhi', Hlo'. reflexivity. }
              rewrite H5. lia.
              apply Hrdx.
         }
         2: { pose proof Halloc.
              eapply well_formed_allocation_result_V in H. invs'.
              eapply well_formed_allocation_eval_step; eauto.
              eapply Hrdx. eapply Henv. eapply Hrdx. eapply Hrdx.
              eapply Hrdx.
              eapply result_has_shape_self.
              eapply size_of_eval_expr_result_has_shape.
              2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
              econstructor; eauto. 1,2: apply eval_Zexpr_Z_eval_Zexpr; eauto.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite Hlo', Hhi'. reflexivity. }
              rewrite H5. lia.
              apply Hrdx. apply Hrdx. }
         2: { eauto. }
         2: { apply H14; lia. }
         2: { eauto. }
         cases (reindexer
                  (((! i ! - | loz |)%z, (hiz - loz)%Z)
                     :: shape_to_index (result_shape_Z r)
                     (shape_to_vars (result_shape_Z r)))).
         { eapply reindexer_not_empty_vars_in_index in Heq. invert Heq.
           apply Hrdx.
           simpl. intro. cups_empty. }
         pose proof Halloc.
         eapply well_formed_allocation_result_V in H.
         invs'.
         eassert (size_of _ _) as Hsize1.
         2: eapply IHeval_expr2 with (reindexer:=
                                        fun l =>
                                          (shift_top_dim_reindexer reindexer l))
           in Hsize1.
         { econstructor; eauto.
           apply eval_Zexpr_Z_eval_Zexpr. simpl. rewrite Hlo. reflexivity.
           apply eval_Zexpr_Z_eval_Zexpr. eassumption. }
         3: { pose proof Halloc as Halloc2.
              eapply well_formed_allocation_result_V in Halloc2. invs.
              eapply well_formed_reindexer_shift_top_dim_reindexer with
              (lo:=loz) (hi:=hiz).
              eauto. apply Henv.
              eapply result_has_shape_self.
              eapply size_of_eval_expr_result_has_shape.
              2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
              econstructor; eauto.
              all: eauto.
              erewrite result_has_shape_length.
              2: { eapply size_of_eval_expr_result_has_shape in H5; eauto. }
              lia.
              apply Hrdx. }
         3: { eapply well_formed_allocation_shift_top_dim_reindexer.
              eauto. eauto. apply Hrdx. apply Henv. apply Hrdx.
              apply Hrdx. apply Hrdx.
              eapply result_has_shape_self.
              eapply size_of_eval_expr_result_has_shape.
              2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
              econstructor; eauto. 1,2: apply eval_Zexpr_Z_eval_Zexpr; eauto.
              apply Hrdx. }
         2: { eapply well_formed_environment_add_heap. eauto. eauto. }
         2: { eapply contexts_agree_add_heap; try apply Henv; eauto. }
         2: { eapply HasPadGen with (k:=0) (c:=c) (ll:=ll) (rr:=rr).
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
              eauto.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo.
              intros. apply H14; lia.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hhi.
              intros. apply H16; lia.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
              intros. apply H17; lia.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
              intros. lia. }
         2: { eauto. }
         2: { apply Hrdx. }
         invs'.
         eexists. eexists.
         eapply EvalForStep. eassumption. eassumption. lia.
         pose proof Hfirst.
         eapply Hfirst.
         unfold shift_top_dim_reindexer in *.
         unfold lookup_total. rewrite H.
         eapply eq_eval_stmt_for. eassumption.
         simpl. rewrite Hlo'. reflexivity.
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
         apply eq_zexpr_sub_literal.
         apply eq_zexpr_id. f_equal. f_equal. lia.
         split. lia.
         eapply eq_Z_tuple_index_list_id. }


    simpl in *. cases rr.
    2: { eapply IHeval_expr1 in Hsize'; eauto.
         2: { eapply well_formed_environment_add_valuation; eauto. }
         2: { pose proof Halloc as Halloc2.
              eapply well_formed_allocation_result_V in Halloc2. invs'.
              eapply well_formed_reindexer_eval0; eauto. apply Henv.
              eapply result_has_shape_self.
              eapply size_of_eval_expr_result_has_shape.
              2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
              econstructor; eauto. 1,2: apply eval_Zexpr_Z_eval_Zexpr; eauto.
              unfold not. intros. eapply H3.
              eapply shape_to_vars_contains_substring; eauto.
              simpl.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite Hhi', Hlo'. reflexivity. }
              rewrite H5. lia.
              apply Hrdx. }
         2: { pose proof Halloc.
              eapply well_formed_allocation_result_V in H. invs.
              eapply well_formed_allocation_eval_step. eauto. eauto.
              eapply Hrdx. eapply Henv. eapply Hrdx. eapply Hrdx. eapply Hrdx.
              eapply result_has_shape_self.
              eapply size_of_eval_expr_result_has_shape.
              2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
              econstructor. eauto. 1,2: apply eval_Zexpr_Z_eval_Zexpr; eauto.
              all: eauto.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite Hhi', Hlo'. reflexivity. }
              apply H5.
              eapply Hrdx. eapply Hrdx. }
         2: { apply H16; lia. }
         invs'.
         pose proof H0 as Hfirst.
         eapply lower_correct_weak in H0.
         2: { eauto. }
         2: { eauto. }
         2: { eapply well_formed_environment_add_valuation; eauto. }
         2: { pose proof Halloc as Halloc2.
              eapply well_formed_allocation_result_V in Halloc2. invs.
              eapply well_formed_reindexer_eval0; eauto. apply Henv.
              eapply result_has_shape_self.
              eapply size_of_eval_expr_result_has_shape.
              2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
              econstructor; eauto. 1,2: apply eval_Zexpr_Z_eval_Zexpr; eauto.
              unfold not. intros. eapply H3.
              eapply shape_to_vars_contains_substring; eauto.
              simpl.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite Hhi', Hlo'. reflexivity. }
              rewrite H5. lia.
              apply Hrdx. }
         2: { pose proof Halloc.
              eapply well_formed_allocation_result_V in H. invs'.
              eapply well_formed_allocation_eval_step; eauto.
              eapply Hrdx. eapply Henv. eapply Hrdx. eapply Hrdx.
              eapply Hrdx.
              eapply result_has_shape_self.
              eapply size_of_eval_expr_result_has_shape.
              2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
              econstructor; eauto. 1,2: apply eval_Zexpr_Z_eval_Zexpr; eauto.
              eapply length_eval_expr_gen in H5.
              2: { simpl. rewrite Hlo', Hhi'. reflexivity. }
              rewrite H5. lia.
              apply Hrdx. apply Hrdx. }
         2: { eauto. }
         2: { apply H16; lia. }
         2: { eauto. }
         cases (reindexer
           (((! i ! - | loz |)%z, (hiz - loz)%Z)
              :: shape_to_index (result_shape_Z r)
              (shape_to_vars (result_shape_Z r)))).
         { eapply reindexer_not_empty_vars_in_index in Heq. invert Heq.
           apply Hrdx.
           simpl. intro. cups_empty. }
         pose proof Halloc.
         eapply well_formed_allocation_result_V in H.
         invs'.
         eassert (size_of _ _) as Hsize1.
         2: eapply IHeval_expr2 with (reindexer:=
                                        fun l =>
                                          (shift_top_dim_reindexer reindexer l))
           in Hsize1.
         { econstructor; eauto.
           apply eval_Zexpr_Z_eval_Zexpr. simpl. rewrite Hlo. reflexivity.
           apply eval_Zexpr_Z_eval_Zexpr. eassumption. }
         3: { pose proof Halloc as Halloc2.
              eapply well_formed_allocation_result_V in Halloc2. invs.
              eapply well_formed_reindexer_shift_top_dim_reindexer with
              (lo:=loz) (hi:=hiz).
              eauto. apply Henv.
              eapply result_has_shape_self.
              eapply size_of_eval_expr_result_has_shape.
              2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
              econstructor; eauto.
              all: eauto.
              erewrite result_has_shape_length.
              2: { eapply size_of_eval_expr_result_has_shape in H5; eauto. }
              lia.
              apply Hrdx. }
         3: { eapply well_formed_allocation_shift_top_dim_reindexer.
              eauto. eauto. apply Hrdx. apply Henv. apply Hrdx.
              apply Hrdx. apply Hrdx.
              eapply result_has_shape_self.
              eapply size_of_eval_expr_result_has_shape.
              2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
              econstructor; eauto. 1,2: apply eval_Zexpr_Z_eval_Zexpr; eauto.
              apply Hrdx. }
         2: { eapply well_formed_environment_add_heap. eauto. eauto. }
         2: { eapply contexts_agree_add_heap; try apply Henv; eauto. }
         2: { eapply HasPadGen with (k:=0) (c:=c) (ll:=0) (rr:=rr).
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
              eauto.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo.
              intros. apply H14; lia.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hhi.
              intros. apply H16; lia.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
              intros. apply H17; lia.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
              intros. lia. }
         2: { eauto. }
         2: apply Hrdx.
         invs'.
         eexists. eexists.
         eapply EvalForStep. eassumption. eassumption. lia.
         pose proof Hfirst.
         eapply Hfirst.
         unfold shift_top_dim_reindexer in *.
         unfold lookup_total. rewrite H.
         eapply eq_eval_stmt_for. eassumption.
         simpl. rewrite Hlo'. reflexivity.
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
         apply eq_zexpr_sub_literal.
         apply eq_zexpr_id. f_equal. f_equal. lia.
         split. lia.
         eapply eq_Z_tuple_index_list_id. }
    eapply IHeval_expr1 with (asn:=asm) in Hsize'; eauto.
    2: { eapply well_formed_environment_add_valuation; eauto. }
    2: { pose proof Halloc as Halloc2.
         eapply well_formed_allocation_result_V in Halloc2. invs.
         eapply well_formed_reindexer_eval0; eauto. apply Henv.
         eapply result_has_shape_self.
         eapply size_of_eval_expr_result_has_shape.
         2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
         econstructor; eauto. 1,2: apply eval_Zexpr_Z_eval_Zexpr; eauto.
         unfold not. intros. eapply H3.
         eapply shape_to_vars_contains_substring; eauto.
         simpl.
         eapply length_eval_expr_gen in H5.
         2: { simpl. rewrite Hhi', Hlo'. reflexivity. }
         rewrite H5. lia.
         apply Hrdx. }
    2: { pose proof Halloc.
         eapply well_formed_allocation_result_V in H. invs'.
         eapply well_formed_allocation_eval_step; eauto.
         eapply Hrdx. eapply Henv. eapply Hrdx. eapply Hrdx.
         eapply Hrdx.
         eapply result_has_shape_self.
         eapply size_of_eval_expr_result_has_shape.
         2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
         econstructor; eauto. 1,2: apply eval_Zexpr_Z_eval_Zexpr; eauto.
         eapply length_eval_expr_gen in H5.
         2: { simpl. rewrite Hlo', Hhi'. reflexivity. }
         rewrite H5. lia.
         apply Hrdx. apply Hrdx. }
    2: { apply H17; lia. }
    invs'.
    pose proof H0 as Hfirst.
    eapply lower_correct_weak in H0.
    2: { eauto. }
    2: { eauto. }
    2: { eapply well_formed_environment_add_valuation; eauto. }
    2: { pose proof Halloc as Halloc2.
         eapply well_formed_allocation_result_V in Halloc2. invs.
         eapply well_formed_reindexer_eval0; eauto. apply Henv.
         eapply result_has_shape_self.
         eapply size_of_eval_expr_result_has_shape.
         2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
         econstructor; eauto. 1,2: apply eval_Zexpr_Z_eval_Zexpr; eauto.
         unfold not. intros. eapply H3.
         eapply shape_to_vars_contains_substring; eauto.
         simpl.
         eapply length_eval_expr_gen in H5.
         2: { simpl. rewrite Hhi', Hlo'. reflexivity. }
         rewrite H5. lia.
         apply Hrdx. }
    2: { pose proof Halloc.
         eapply well_formed_allocation_result_V in H. invs'.
         eapply well_formed_allocation_eval_step; eauto.
         eapply Hrdx. eapply Henv. eapply Hrdx. eapply Hrdx.
         eapply Hrdx.
         eapply result_has_shape_self.
         eapply size_of_eval_expr_result_has_shape.
         2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
         econstructor; eauto. 1,2: apply eval_Zexpr_Z_eval_Zexpr; eauto.
         eapply length_eval_expr_gen in H5.
         2: { simpl. rewrite Hlo', Hhi'. reflexivity. }
         rewrite H5. lia.
         apply Hrdx. apply Hrdx. }
    2: { eauto. }
    2: { apply H17; lia. }
    2: { eauto. }
    cases (reindexer
           (((! i ! - | loz |)%z, (hiz - loz)%Z)
              :: shape_to_index (result_shape_Z r)
              (shape_to_vars (result_shape_Z r)))).
         { eapply reindexer_not_empty_vars_in_index in Heq. invert Heq.
           apply Hrdx.
           simpl. intro. cups_empty. }
         pose proof Halloc.
         eapply well_formed_allocation_result_V in H.
         invs.
         eassert (size_of _ _) as Hsize1.
         2: eapply IHeval_expr2 with (reindexer:=
                                        fun l =>
                                          (shift_top_dim_reindexer reindexer l))
           in Hsize1.
         { econstructor; eauto.
           apply eval_Zexpr_Z_eval_Zexpr. simpl. rewrite Hlo. reflexivity.
           apply eval_Zexpr_Z_eval_Zexpr. eassumption. }
         3: { pose proof Halloc as Halloc2.
              eapply well_formed_allocation_result_V in Halloc2. invs.
              eapply well_formed_reindexer_shift_top_dim_reindexer with
              (lo:=loz) (hi:=hiz).
              eauto. apply Henv.
              eapply result_has_shape_self.
              eapply size_of_eval_expr_result_has_shape.
              2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
              econstructor; eauto.
              all: eauto.
              erewrite result_has_shape_length.
              2: { eapply size_of_eval_expr_result_has_shape in H5; eauto. }
              lia.
              apply Hrdx. }
         3: { eapply well_formed_allocation_shift_top_dim_reindexer.
              eauto. eauto. apply Hrdx. apply Henv. apply Hrdx.
              apply Hrdx. apply Hrdx.
              eapply result_has_shape_self.
              eapply size_of_eval_expr_result_has_shape.
              2: { eapply EvalGenStep. apply Hlo'. apply Hhi'. all: eauto. }
              econstructor; eauto. 1,2: apply eval_Zexpr_Z_eval_Zexpr; eauto.
              apply Hrdx. }
         2: { eapply well_formed_environment_add_heap. eauto. eauto. }
         2: { eapply contexts_agree_add_heap; try apply Henv; eauto. }
         2: { eapply HasPadGen with (k:=0) (c:=c-1) (ll:=0) (rr:=0).
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
              eauto.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo.
              intros. apply H14; lia.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hhi.
              intros. apply H16; lia.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
              intros. apply H17; lia.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
              intros. lia. }
         2: { eauto. }
         2: apply Hrdx.
         invs'.
         eexists. eexists.
         eapply EvalForStep. eassumption. eassumption. lia.
         pose proof Hfirst.
         eapply Hfirst.
         unfold shift_top_dim_reindexer in *.
         unfold lookup_total. rewrite H.
         eapply eq_eval_stmt_for. eassumption.
         simpl. rewrite Hlo'. reflexivity.
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
         apply eq_zexpr_sub_literal.
         apply eq_zexpr_id. f_equal. f_equal. lia.
         split. lia.
         eapply eq_Z_tuple_index_list_id.
  - (* STEPPING SUM *)
    simpl in *. pose proof Hsize as Hsize0. invert Hsize. 

    rename H12 into Hsize. pose proof Hsize as Hsize'.
    rename H into Hlo. rename H0 into Hhi.

    invert Hpad.
    { cbv [eval_Zexpr_Z_total] in *. cbn [eval_Zexpr_Z] in *. rewrite Hhi, Hlo in *.
      lia. }
    cbv [eval_Zexpr_Z_total] in *. cbn [eval_Zexpr_Z] in *. rewrite Hhi, Hlo in *.
    eapply size_of_eval_expr_result_has_shape in Hsize0.
    2: { eapply EvalSumStep; eauto. }
    eapply IHeval_expr1 with (asn:=Reduce) in Hsize'; eauto.
    2: { simpl in Henv.
         eapply well_formed_environment_add_valuation. eauto.
         sets. eauto. }
    2: { pose proof H6.
         eapply result_has_shape_add_result_result in H6; eauto.         
         eapply well_formed_reindexer_add_valuation; eauto.
         decomp_well_formed_reindexer.
         propositional.
         eapply partial_injective_add_result_l.
         4: eauto. eauto. eauto. eauto.
         eauto. eauto. eauto. eauto. eauto.
                eapply nondestructivity_reduce. apply Henv.
    eapply result_has_shape_self; eauto. eapply H6. }
    2: { eapply well_formed_allocation_add_valuation;
         eauto; try apply Hrdx.
         eapply well_formed_allocation_add_result_l; eauto.
         eapply result_has_shape_add_result_result in H6; eauto.
         propositional. 
         eapply result_has_shape_add_result_result in H6; eauto.
         propositional. }
    2: eauto.
    invs'.
    pose proof H0 as Heval1.
    eapply lower_correct_weak with (asn:=Reduce) in H0.
    2: { eauto. }
    2: { eauto. }
    2: { eapply well_formed_environment_add_valuation; eauto. }
    2: { eapply well_formed_reindexer_add_valuation; eauto.
         decomp_well_formed_reindexer.
         propositional.
         pose proof Hsize0 as Hsh.
         eapply result_has_shape_add_result_result in Hsh.
         2: { eauto. }
         invs'. 
         eapply partial_injective_add_result_l.
         4: eauto. eauto. eauto. eauto. eauto. eapply nondestructivity_reduce.

         apply Henv.
         eapply result_has_shape_self; eauto.
         eapply result_has_shape_add_result_result in H6; eauto.
         eapply H6. 
    }
    2: { eapply well_formed_allocation_add_valuation; eauto.
         pose proof Hsize0 as Hsh.
         eapply result_has_shape_add_result_result in Hsh.
         2: { eauto. }
         invs. 
         eapply well_formed_allocation_add_result_l; eauto.
         eapply result_has_shape_add_result_result in H6; eauto.
         propositional.
         eapply Hrdx. propositional. apply Hrdx. }
    2: eauto.
    2: { apply H12; lia. }
    2: eauto.
    2: { apply H12; lia. }
    
    cases (reindexer
            (shape_to_index (result_shape_Z r) (shape_to_vars (result_shape_Z r)))).
    { assert (loz + 1 < hiz \/ loz + 1 = hiz)%Z as [H|H] by lia.
      { unfold result_shape_Z in *. simpl in *.
        pose proof Halloc as Halloc'.
        unfold well_formed_allocation in Halloc'.
        unfold result_shape_Z in Halloc'.
        replace (result_shape_nat s) with (result_shape_nat r) in *.
        2: { eapply result_has_shape_add_result_result in H6.
             2: { eauto. }
             invs.
             erewrite result_has_shape_result_shape_nat by eauto. symmetry.
             erewrite result_has_shape_result_shape_nat by eauto. symmetry.
             auto. }
        invs'.
        rewrite Heq in Halloc'. invs'. rewrite H0 in *.
        eassert (size_of _ _) as Hsize1.
        2: eapply IHeval_expr2 with (asn:=Reduce) in Hsize1.
        { eauto. }
        2: { eapply well_formed_environment_add_stack.
             eauto. eapply lookup_Some_dom. eauto. }
        2: { decomp_well_formed_reindexer. clear IHeval_expr1.
             propositional.
             pose proof H6 as H7. eapply result_has_shape_add_result_result in H6.
             2: { eauto. } invs'.
             eapply partial_injective_add_result_r.
             4: eauto. eauto. eauto. eauto.
             eauto. eauto. eauto. eauto. eauto.
             eapply nondestructivity_reduce. }
        2: { eapply well_formed_allocation_same_add_stack.
             eapply well_formed_allocation_add_result_r; eauto.
             eapply result_has_shape_add_result_result in H6; eauto.
             propositional. 
             eapply result_has_shape_add_result_result in H6; eauto.
             propositional. }
        2: { eapply contexts_agree_add_in_stack. eauto. eauto.
             apply Henv. apply Henv. }
        2: { eapply HasPadSum.
             cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
             intros. apply H12; lia.
             cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
             lia. }
        2: { eauto. }
        invs'.
        eexists. eexists.
        eapply EvalForStep.
        eauto. eauto. lia.
        eassumption. eapply H8.
      }
      { unfold result_shape_Z in *. simpl in *.
        pose proof Halloc as Halloc'.
        unfold well_formed_allocation in Halloc'.
        unfold result_shape_Z in Halloc'.
        replace (result_shape_nat s) with (result_shape_nat r) in *.
        2: { eapply result_has_shape_add_result_result in H6.
             2: { eauto. }
             invs.
             erewrite result_has_shape_result_shape_nat by eauto. symmetry.
             erewrite result_has_shape_result_shape_nat by eauto. symmetry.
             auto. }
        rewrite Heq in Halloc'. invs'. rewrite H in *.        
        invs'.
        eexists. eexists.
        eapply EvalForStep.
        eauto. eauto. lia.
        eassumption.
        eapply EvalForBase.
        simpl. rewrite Hlo. reflexivity. eassumption. lia.
      }
    }
    { assert (loz + 1 < hiz \/ loz + 1 = hiz)%Z as [H11|H11] by lia.
      { unfold result_shape_Z in *. simpl in *.
        pose proof Halloc as Halloc'.
        unfold well_formed_allocation in Halloc'.
        unfold result_shape_Z in Halloc'.
        replace (result_shape_nat s) with (result_shape_nat r) in *.
        2: { eapply result_has_shape_add_result_result in H6.
             2: { eauto. }
             invs.
             erewrite result_has_shape_result_shape_nat by eauto. symmetry.
             erewrite result_has_shape_result_shape_nat by eauto. symmetry.
             auto. }
        rewrite Heq in Halloc'. invs'. unfold lookup_total in *.
        rewrite H0 in *.
        eassert (size_of _ _) as Hsize1.
        2: eapply IHeval_expr2 with (asn:=Reduce) in Hsize1.
        { eauto. }
        2: { eapply well_formed_environment_add_heap.
             eauto. eauto. }
        2: { decomp_well_formed_reindexer. clear IHeval_expr1.
             propositional.
             pose proof H6 as H8. eapply result_has_shape_add_result_result in H8.
             2: { eauto. } invs'.
             eapply partial_injective_add_result_r.
             4: eauto. eauto. eauto. eauto.
             eauto. eauto. eauto. eauto. eauto.
             eapply nondestructivity_reduce. }
        2: { eapply well_formed_allocation_add_heap; eauto.
             eapply well_formed_allocation_add_result_r; eauto.
             eapply result_has_shape_add_result_result in H6; eauto.
             propositional. 
             eapply result_has_shape_add_result_result in H6; eauto.
             propositional. }
        2: { eapply contexts_agree_add_heap; eauto. apply Henv. apply Henv. }
        2: { eapply HasPadSum.
             cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
             intros. apply H12; lia.
             cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
             lia. }
        2: { eauto. }
        invs.
        eexists. eexists.
        eapply EvalForStep.
        eauto. eauto. lia.
        eassumption. eapply H8.
      }
      { unfold result_shape_Z in *. simpl in *.
        pose proof Halloc as Halloc'.
        unfold well_formed_allocation in Halloc'.
        unfold result_shape_Z in Halloc'.
        replace (result_shape_nat s) with (result_shape_nat r) in *.
        2: { eapply result_has_shape_add_result_result in H6.
             2: { eauto. }
             invs.
             erewrite result_has_shape_result_shape_nat by eauto. symmetry.
             erewrite result_has_shape_result_shape_nat by eauto. symmetry.
             auto. }
        rewrite Heq in Halloc'. invs'. unfold lookup_total in *.
        rewrite H0 in *.
        eexists. eexists.
        eapply EvalForStep.
        eauto. eauto. lia.
        eassumption.
        eapply EvalForBase.
        simpl. rewrite Hlo. reflexivity. eassumption. lia.
      }
    }
  - simpl in *. invs.

    rename H into Hlo. rename H0 into Hhi.

    invert Hpad.
    2: { cbv [eval_Zexpr_Z_total] in *. rewrite Hlo, Hhi in *. lia. }
    eexists. eexists.
    eapply EvalForBase; eauto.
  - eexists. eexists. simpl. eapply EvalIfFalse. eauto.
  - simpl. invert Hpad. eq_eval_B. discriminate.
    eapply IHeval_expr in Halloc. invs.
    eexists. eexists. eapply EvalIfTrue. eapply H2.
    all: simpl in *; invs; eauto.
  - cases sz1; simpl in *.
    + invs. erewrite size_of_sizeof in * by eauto. simpl.
      invert Hpad. eq_size_of. pose proof H as Heval1.
      assert (result_has_shape l1 []) as Hl1.
      { eauto using size_of_eval_expr_result_has_shape. }
      invert Hl1.
      eapply IHeval_expr1 with (asn:=Assign) (st:= st $+ (x,0%R)) (reindexer:=
                                                                     fun x => x) in Heval1;
        eauto.
      2: { eapply well_formed_environment_alloc_stack.
           eassumption. sets. sets. sets. }
      2: { decomp_well_formed_reindexer.
           propositional. eapply partial_injective_id_reindexer. apply Henv.
           sets. sets.
           unfold nondestructivity. rewrite lookup_add_eq. rewrite dom_add.
           split; intros. sets. invs'. eauto. eauto. }
      2: { unfold well_formed_allocation.
           unfold shape_to_index. unfold result_shape_Z. simpl.
           eexists. rewrite lookup_add_eq by auto. reflexivity. }
      2: { eapply contexts_agree_alloc_stack. eauto. sets. }
      invs'. pose proof H7 as H8.
      eapply lower_correct_weak in H8.
      2: { eauto. }
      2: { eauto. }
      2: { eapply well_formed_environment_alloc_stack.
           eassumption. sets. sets. sets. }
      2: { decomp_well_formed_reindexer.
           propositional. eapply partial_injective_id_reindexer. apply Henv.
           sets. sets.
           unfold nondestructivity. rewrite lookup_add_eq. rewrite dom_add.
           split; intros. sets. invs'. eauto. eauto. }
      2: { unfold well_formed_allocation.
           unfold shape_to_index. unfold result_shape_Z. simpl.
           eexists. rewrite lookup_add_eq by auto. reflexivity. }
      2: { eapply contexts_agree_alloc_stack. eauto. sets. }
      2: { eauto. }
      2: { eauto. }
      unfold result_shape_Z in H8. simpl in H8.
      invs'. rewrite add_overwrite in H7.
      rewrite lookup_add_eq in H7 by auto. pose proof H10 as Heval2.
      eapply IHeval_expr2 with (reindexer:= reindexer) (asn:=asm) in Heval2.
      2: { invs. 
           eapply well_formed_environment_let_bind1_scalar. eauto.
           sets. sets. sets. }
      2: { decomp_well_formed_reindexer.
           propositional. 
           unfold nondestructivity. rewrite dom_add.
           rewrite lookup_add_ne.
           split; intros. eapply Hnondstr; eauto. sets.
           eapply Hnondstr; eauto.
           invert Henv. sets. }

      2: { eapply well_formed_allocation_add_stack. eauto.
           unfold well_formed_environment in Henv. sets. }
      2: { eapply contexts_agree_let_bind1_scalar. eauto. }
      2: { eauto. }
      2: { intros. cases (x0 =? x). eapply String.eqb_eq in Heq. subst.
           repeat rewrite lookup_add_eq in * by auto. invs'. simpl.
           eapply has_pad_gen_pad. eauto. eauto. eauto. econstructor. eauto.
           eauto. 
           eapply String.eqb_neq in Heq. rewrite lookup_add_ne in * by eauto.
           eauto. }
      invs'.
      pose proof H8.
      eexists. eexists. econstructor. econstructor.
      econstructor. eassumption. econstructor.
      rewrite Rplus_0_l. eauto. econstructor.
    + simpl in *. invs. erewrite size_of_sizeof in * by eauto.
      eassert (result_has_shape l1 _) as Hl1.
      { eauto using size_of_eval_expr_result_has_shape. }
      destruct l1 as [|l1]; [solve[invert Hl1] |].
      invert Hpad. eq_size_of. pose proof H as Heval1. 
      eapply IHeval_expr1 with
        (h:=(alloc_array_in_heap
               [(fold_left mul sz1 n)] h x))
        (asn:=Assign) (reindexer:= fun x => x) in Heval1; eauto.
      2: { eapply well_formed_environment_letbind1.
           3: sets. sets.
           2: { eauto. }
           sets. }
      2: { decomp_well_formed_reindexer.
           propositional. eapply partial_injective_id_reindexer. apply Henv.
           eauto. sets.
           unfold nondestructivity. unfold alloc_array_in_heap.
           rewrite lookup_add_eq by eauto.
           rewrite dom_add. split; intros. 2: sets.
           invs'. rewrite add_0_r.
           epose proof (lookup_alloc_array (fold_left mul sz1 _) _) as [H20|H20].
           2: eassumption.
           eapply lookup_None_dom in H20.
           rewrite dom_alloc_array in H20.
           exfalso. apply H20.
           erewrite <- In_iff_in in *. clear H20.
           unfold tensor_to_array_delta in H9.
           unfold tensor_to_array_delta_by_indices in H9.
           erewrite partial_dom_fold_left_array_add in H9.
           2: { eapply partial_injective_id_reindexer. apply Henv. }
           rewrite dom_empty in H9. rewrite cup_empty_r in H9.
           eapply In_iff_in in H9.
           eapply in_extract_Some in H9.
           eapply in_map_iff in H9. invs'.
           rewrite filter_idempotent in H11.
           decomp_index.
           replace (fold_left mul sz1 n) with (fold_left mul (n :: sz1) 1).
           2: { simpl. rewrite add_0_r. reflexivity. }
           rewrite partial_interpret_reindexer_id_flatten in H9. invert H9.
           erewrite result_has_shape_result_shape_Z.
           2: { eapply size_of_eval_expr_result_has_shape in H4; eauto. }
           erewrite <- fold_left_mul_filter_until.
           erewrite Z_of_nat_fold_left_mul.
           eapply in_mesh_grid_flatten_in_range.
           eapply Forall_map. eapply Forall_forall. intros. lia.
           erewrite result_has_shape_result_shape_Z in H1.
           2: { eapply size_of_eval_expr_result_has_shape in H4; eauto. }
           eauto. eauto. apply Henv. }
      2: { rewrite <- (Nat2Z.id (fold_left _ _ _)).
           eapply well_formed_allocation_letbind1. eapply Henv.
           unfold well_formed_environment in *. invs'. sets.
           erewrite result_has_shape_result_shape_Z.
           2: { eapply size_of_eval_expr_result_has_shape; eauto. }
           replace 1%Z with (Z.of_nat 1) by reflexivity.
           rewrite <- Z_of_nat_fold_left_mul.
           f_equal. rewrite fold_left_mul_filter_until.
           simpl. invs. eq_size_of. eq_eval_Z. simpl. f_equal. lia. }
      2: { eapply contexts_agree_alloc_array_in_heap. eauto. eauto. }
      invs'. pose proof H7 as H9.
      eapply lower_correct_weak in H9.
      2: { eauto. }
      2: { eauto. }
      2: { eapply well_formed_environment_letbind1.
           3: sets. sets.
           2: { eauto. }
           sets. }
      2: { decomp_well_formed_reindexer. propositional.
           eapply partial_injective_id_reindexer. apply Henv. sets. sets.
           unfold nondestructivity. unfold alloc_array_in_heap.
           rewrite lookup_add_eq by eauto.
           rewrite dom_add. split; intros. 2: sets.
           invs'. rewrite add_0_r.
           pose proof (lookup_alloc_array (fold_left mul sz1 n) x2) as [H22|H22].
           2: solve [eauto].
           eapply lookup_None_dom in H22.
           rewrite dom_alloc_array in H22.
           exfalso. apply H22.
           erewrite <- In_iff_in in *. clear H22.
           unfold tensor_to_array_delta in H13.
           unfold tensor_to_array_delta_by_indices in H13.
           erewrite partial_dom_fold_left_array_add in H13.
           2: { eapply partial_injective_id_reindexer. apply Henv. }
           rewrite dom_empty in H13. rewrite cup_empty_r in H13.
           eapply In_iff_in in H13.
           eapply in_extract_Some in H13.
           eapply in_map_iff in H13. invs'.
           rewrite filter_idempotent in H14.
           decomp_index.
           replace (fold_left mul sz1 n) with (fold_left mul (n :: sz1) 1).
           2: { simpl. rewrite add_0_r. eauto. }
           rewrite partial_interpret_reindexer_id_flatten in H13. invs'.
           erewrite result_has_shape_result_shape_Z.
           2: { eapply size_of_eval_expr_result_has_shape in H4; eauto. }
           erewrite <- fold_left_mul_filter_until.
           erewrite Z_of_nat_fold_left_mul.
           eapply in_mesh_grid_flatten_in_range.
           eapply Forall_map. eapply Forall_forall. intros. lia.
           erewrite result_has_shape_result_shape_Z in H1.
           2: { eapply size_of_eval_expr_result_has_shape in H4; eauto. }
           eauto. eauto. apply Henv. }
      2: { rewrite <- (Nat2Z.id (fold_left _ _ _)).
           eapply well_formed_allocation_letbind1. eapply Henv.
           unfold well_formed_environment in *. sets.
           erewrite result_has_shape_result_shape_Z.
           2: { eapply size_of_eval_expr_result_has_shape in H4; eauto. }
           replace 1%Z with (Z.of_nat 1) by reflexivity.
           rewrite <- Z_of_nat_fold_left_mul.
           rewrite fold_left_mul_filter_until. f_equal.
           invs. eq_size_of. eq_eval_Z. simpl. f_equal. lia. }

      cases (shape_to_index (result_shape_Z (V l1))
               (shape_to_vars (result_shape_Z (V l1)))).
      { eapply shape_to_index_not_empty_Z in Heq. propositional. }
      unfold alloc_array_in_heap in H9. rewrite add_overwrite in H9.
      unfold lookup_total in H9. rewrite lookup_add_eq in H9 by auto.

      pose proof H10 as Heval2.
      eapply IHeval_expr2 with (h:=x1) (asn:=asm) (reindexer:=reindexer) in Heval2.
      2: { invs'.
           eapply well_formed_environment_alloc_heap. eauto. eauto.
           sets. sets. sets. }
      2: { invs'.
           decomp_well_formed_reindexer. propositional.
           unfold nondestructivity. rewrite dom_add.
           rewrite lookup_add_ne.
           2: { invert Henv. sets. }
           split; intros. apply Hnondstr; eauto.
           apply Hnondstr; eauto. sets. }
      2: { invs'. eapply well_formed_allocation_add_heap_var.
           eauto. unfold well_formed_environment in*. sets. }
      2: { invs'.
           erewrite result_has_shape_result_shape_Z.
           2: { eapply size_of_eval_expr_result_has_shape in H4; eauto. }
           simpl fold_left. rewrite add_0_r.
           replace (fold_left mul sz1 n) with (fold_left mul (n :: sz1) 1).
           2: { simpl. rewrite add_0_r. eauto. }

           rewrite <- (Nat2Z.id ((fold_left _ _ _))).
           rewrite tensor_to_array_delta_id_valuation. 2: apply Henv.
           eapply contexts_agree_add_alloc_heap. eauto. eauto.
           eapply size_of_eval_expr_result_has_shape in H4; eauto.
           f_equal. replace 1%Z with (Z.of_nat 1) by reflexivity.
           rewrite <- Z_of_nat_fold_left_mul.
           erewrite fold_left_mul_filter_until. eauto. }    
      2: { eauto. }
      2: { intros. cases (x2 =? x). eapply String.eqb_eq in Heq0. subst.
           repeat rewrite lookup_add_eq in * by auto. invs'. simpl.
           eapply has_pad_gen_pad. eauto. eauto. eauto.
           eapply result_has_shape_self.
           eapply size_of_eval_expr_result_has_shape in H4; eauto.
           eauto. eauto.
           eapply String.eqb_neq in Heq0. rewrite lookup_add_ne in * by eauto.
           eauto. }    
      invs'.

      eexists. eexists. econstructor.
      unfold flat_sizeof. erewrite size_of_sizeof by eauto. simpl.
      econstructor.
      
      econstructor.
      eapply H7. simpl. rewrite add_0_r in *.
      econstructor.
      simpl in H7. rewrite add_0_r in H7.
      erewrite result_has_shape_result_shape_Z in H7.
      2: { eapply size_of_eval_expr_result_has_shape in H4; eauto. }
      eassert (array_add _ _ = _) as ->. 2: eassumption.
      
      f_equal. f_equal. simpl. lia.
      econstructor.
      eapply contexts_agree_alloc_array_in_heap. eauto. eauto. eauto.
      eauto.
  - simpl in *. invs. repeat erewrite size_of_sizeof in * by eauto. simpl.
    invert Hpad. eq_size_of. invs'.
    rename H3 into Hsize1. rename H4 into Hsize2.
    pose proof Hsize1 as Hsize1'. pose proof Hsize2 as Hsize2'.
    eapply size_of_eval_expr_result_has_shape in Hsize1'; eauto.
    eapply size_of_eval_expr_result_has_shape in Hsize2'; eauto.
    pose proof Hsize1 as Heval1.
    eapply IHeval_expr1 in Heval1.
    2: { eapply well_formed_environment_subseteq_vars. eauto. sets. }
    2: { pose proof Halloc as Halloc'.
         eapply well_formed_allocation_result_V in Halloc'. invs'.
         eapply well_formed_reindexer_concat_l. apply Hrdx.
         eauto. eauto. apply Henv. eauto. apply Hrdx. }
    2: { eapply well_formed_allocation_concat_l. eauto.
         eauto. eauto.
         eapply Henv. apply Hrdx. apply Hrdx. apply Hrdx. apply Hrdx. }
    invs'.
    pose proof H2 as H11.
    eapply lower_correct_weak with (asn:=asm) in H11; eauto.
    2: { eapply well_formed_environment_subseteq_vars. eauto. sets. }
    2: { pose proof Halloc as Halloc'.
         eapply well_formed_allocation_result_V in Halloc'. invs.
         eapply well_formed_reindexer_concat_l. apply Hrdx.
         eauto. eauto. apply Henv. eauto. apply Hrdx. }
    2: { eapply well_formed_allocation_concat_l. eauto.
         eauto. eauto. apply Henv. apply Hrdx. apply Hrdx. apply Hrdx.
         apply Hrdx. }
    2: { eauto. }
    2: { eauto. }
    2: { eauto. }
    destruct (reindexer match shape_to_index _ _ with _ => _ end) eqn:Heq.
    { cases (shape_to_index (result_shape_Z (V l1))
                            (shape_to_vars (result_shape_Z (V l1)))).
      eapply shape_to_index_not_empty_Z in Heq0. propositional.
      eapply reindexer_not_empty_vars_in_index in Heq. propositional.
      apply Hrdx. destruct p0.
      unfold not. intros.
      simpl in H15.
      unfold shape_to_index,shape_to_vars, result_shape_Z in Heq0. simpl in *.
      cases l1.
      - simpl in *. invs'. simpl in *. cups_empty.
      - simpl in *. invs'. simpl in *. cups_empty. }        

    pose proof Hsize2 as Heval2.
    pose proof Halloc as Halloc'.
    eapply well_formed_allocation_result_V in Halloc'. invs'.
    unfold lookup_total in *. rewrite H3 in *.
    match goal with
    | H: context[h $+ (?a, ?b)] |- _ => 
        eapply IHeval_expr2 with (st:=st) (h:= h $+ (a, b)) in Heval2; eauto
    end.
    2: { eapply well_formed_environment_add_heap.
         eapply well_formed_environment_subseteq_vars. eauto. sets. eauto. }
    2: { eapply well_formed_reindexer_concat_r. eauto.
         rewrite Nat2Z.id. eauto. eauto. apply Henv. lia. assumption. }
    2: { eapply well_formed_allocation_add_heap.
         eapply well_formed_allocation_concat_r. eauto.
         rewrite Nat2Z.id. eauto.
         rewrite Nat2Z.id. eauto.
         apply Henv. apply Hrdx. apply Hrdx. apply Hrdx. apply Hrdx.
         lia. assumption. }
    2: { eapply contexts_agree_add_heap. eauto. eauto.
         unfold well_formed_environment in *. sets.
         unfold well_formed_environment in *. sets. }
    invs'.
    eexists. eexists.
    econstructor.
    2: { eauto. }
    2: { apply Hrdx. }
    eapply eq_eval_stmt_lower_eq_reindexers. eassumption.
    intros. simpl. cases l4. eapply eq_Z_tuple_index_list_id.
    cases p1.
    eapply Hrdx.
    erewrite <- eq_Z_tuple_index_list_cons_tup.
    split. eauto. split. eauto.
    eapply eq_Z_tuple_index_list_id.
  - simpl in *. invs. eq_size_of. invs'. invert Hpad.
    + eq_size_of. invs'. rename H0 into Hsize. pose proof Hsize as Hsh.
      eapply size_of_eval_expr_result_has_shape in Hsh; eauto.
      pose proof Hsize as Heval.
      eapply IHeval_expr in Heval.
      2: { eauto. }
      2: { eapply well_formed_allocation_result_V in Halloc.
           invert Halloc. invs'.
           eapply well_formed_reindexer_transpose.
           simpl in *. eauto. eauto. apply Henv. eauto.
           apply Hrdx. }
      2: { eapply well_formed_allocation_transpose;
           try apply Hrdx; try apply Henv; eauto. }
      2: { eauto. }
      2: { eauto. }
      2: { eauto. }
      eauto.
    + eq_size_of. invs'. pose proof H0 as Hsize. pose proof Hsize as Hsh.
      eapply size_of_eval_expr_result_has_shape in Hsh; eauto.
      pose proof Hsize as Heval.
      eapply IHeval_expr in Heval.
      2: { eauto. }
      2: { eapply well_formed_allocation_result_V in Halloc.
           invert Halloc. invs'.
           eapply well_formed_reindexer_transpose.
           simpl in *. eauto. eauto. apply Henv. eauto.
           apply Hrdx. }
      2: { eapply well_formed_allocation_transpose;
           try apply Hrdx; try apply Henv; eauto. }
      2: { eauto. }
      2: { eauto. }
      2: { eauto. }
      eauto.
  - simpl in *. invs. invert Hpad.
    eq_size_of. invs'.
    rename H2 into Hsize. pose proof Hsize as Hsh.
    eapply size_of_eval_expr_result_has_shape in Hsh; eauto.
    pose proof Hsize as Heval.
    eapply IHeval_expr in Heval; eauto.
    pose proof Halloc as Halloc2.
    eapply well_formed_allocation_result_V in Halloc2. invert Halloc2. invs.
    eapply well_formed_reindexer_flatten;
      try apply Henv; try apply Hrdx; eauto. apply Hrdx.
    eapply well_formed_allocation_flatten;
      try apply Henv; try apply Hrdx; eauto.
  - simpl in *. invs. invert Hpad. eq_size_of. invs'.
    rename H7 into Hsize. pose proof Hsize as Hsh.
    eapply size_of_eval_expr_result_has_shape in Hsh; eauto.
    rename H4 into Hk. apply eval_Zexpr_Z_eval_Zexpr in Hk.
    cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *. invs'.
    
    pose proof Hsize as Heval.
    eapply IHeval_expr in Heval; eauto.
    pose proof Halloc as Halloc2.
    eapply well_formed_allocation_result_V in Halloc2. invert Halloc2. invs'.
    eapply well_formed_reindexer_split;
      try apply Hrdx; try apply Henv; eauto. apply Hrdx.
    eapply well_formed_allocation_split;
      try apply Hrdx; try apply Henv; eauto.
  - simpl in *. invs. invert Hpad.
    rename H5 into Hsize. pose proof Hsize as Hsh.
    eapply size_of_eval_expr_result_has_shape in Hsh; eauto.
    rename H4 into Hk. pose proof Hk as Hk'.
    eapply eval_Zexpr_includes_valuation in Hk'; try apply empty_includes.
    apply eval_Zexpr_Z_eval_Zexpr in Hk'.
    rewrite Hk' in *. invs'. apply eval_Zexpr_Z_eval_Zexpr in Hk.
    cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *.
    pose proof H6 as Hpad.
    eapply has_pad_gen_pad in Hpad; eauto.
    simpl in Hpad. invs'.

    pose proof Hsize as Heval.
    eapply IHeval_expr in Heval; eauto.
    rewrite <- (firstn_skipn (length l - (Z.to_nat kz)) l).
    rewrite <- (rev_involutive (skipn _ _)).
    rewrite <- firstn_rev.
    eapply forall_firstn_ge with (m:= Z.to_nat kz) in H3.
    2: { lia. }
    eapply forall_eq_gen_pad in H3. rewrite H3.
    simpl gen_pad_list. rewrite rev_repeat.
    
    rewrite length_firstn. rewrite length_rev.
    erewrite result_has_shape_length.
    2: { eauto using size_of_eval_expr_result_has_shape. }

    rewrite min_l by lia.
    pose proof Halloc as Halloc2.
    eapply well_formed_allocation_result_V in Halloc2. invert Halloc2. invs'.

    destruct (m - Z.to_nat kz) eqn:hmk.
    { simpl.
      replace (V (repeat (gen_pad sh0) (Z.to_nat kz))) with
        (gen_pad (Z.to_nat kz :: sh0))
        by eauto.
      decomp_well_formed_reindexer. propositional.
      rewrite filter_negb_is_None_result_lookup_Z_option_gen_pad.
      unfold partial_injective. simpl. propositional.
      destruct l1; destruct l2; eauto.
      invert H4. discriminate.
      invert H4. discriminate.
      destruct p0. destruct p1.
      eapply HeqZlist.
      erewrite <- eq_Z_tuple_index_list_cons_tup in *.
      propositional. subst. reflexivity.
      destruct l1; simpl; rewrite Hmap; eauto.
      destruct p0. simpl. unfold subst_var_in_Z_tup at 1. reflexivity.
      erewrite Hvarsarg. destruct l1. reflexivity.
      destruct p0. reflexivity.
      unfold nondestructivity. unfold tensor_to_array_delta.
      rewrite filter_negb_is_None_result_lookup_Z_option_gen_pad.
      unfold tensor_to_array_delta_by_indices. simpl. rewrite dom_empty.
      split; intros. sets.
      eapply lookup_Some_dom in H8. sets. }
    
    rewrite <- hmk in *.
    rewrite <- (Z2Nat.id kz) by lia. rewrite Nat2Z.id.
    eapply well_formed_reindexer_truncr.
    rewrite rev_app_distr.
    rewrite truncl_list_app.
    2: { rewrite length_rev. simpl. rewrite repeat_length. lia. }
    rewrite truncl_list_skipn.
    rewrite skipn_all2.
    2: { rewrite length_rev. simpl. rewrite repeat_length. lia. }
    replace m with (length l).
    2: { erewrite result_has_shape_length by eauto. reflexivity. }
    rewrite <- skipn_rev. simpl.
    rewrite <- truncl_list_skipn. eauto.
    eapply forall_result_has_shape.
    eapply Forall_app. split.
    eapply forall_firstn. eapply result_has_shape_forall. eauto.
    simpl. eapply Forall_repeat. eapply result_has_shape_gen_pad.
    rewrite length_app. simpl. rewrite length_firstn.
    rewrite repeat_length. erewrite result_has_shape_length by eauto.
    rewrite min_l by lia. rewrite sub_add. reflexivity. lia.
    apply Henv. eauto. lia. apply Hrdx.

    rewrite <- (firstn_skipn (length l-(Z.to_nat kz)) l).
    rewrite <- (rev_involutive (skipn _ _)).
    rewrite <- firstn_rev.
    eapply forall_firstn_ge with (m:= Z.to_nat kz) in H3.
    2: { lia. }
    eapply forall_eq_gen_pad in H3. rewrite H3.
    simpl gen_pad_list. rewrite rev_repeat.
    
    rewrite length_firstn. rewrite length_rev.
    erewrite result_has_shape_length.
    2: { eauto using size_of_eval_expr_result_has_shape. }

    rewrite min_l by lia.
    
    rewrite <- (Z2Nat.id kz) by lia. rewrite Nat2Z.id.
    eapply well_formed_allocation_truncr.
    rewrite rev_app_distr.
    rewrite truncl_list_app.
    2: { rewrite length_rev. simpl. rewrite repeat_length. lia. }
    rewrite truncl_list_skipn.
    rewrite skipn_all2.
    2: { rewrite length_rev. simpl. rewrite repeat_length. lia. }
    replace m with (length l).
    2: { erewrite result_has_shape_length by eauto. reflexivity. }
    simpl.
    rewrite <- skipn_rev. simpl.
    rewrite <- truncl_list_skipn. eauto. apply Hrdx.
    eapply forall_result_has_shape.
    eapply Forall_app. split.
    eapply forall_firstn. eapply result_has_shape_forall. eauto.
    simpl. eapply Forall_repeat. eapply result_has_shape_gen_pad.
    rewrite length_app. simpl. rewrite length_firstn.
    rewrite repeat_length. erewrite result_has_shape_length by eauto.
    rewrite min_l by lia. rewrite sub_add. reflexivity. lia.
    apply Hrdx. eauto. apply Henv. apply Hrdx. apply Hrdx.
  - simpl in *. invs. invert Hpad.
    rename H5 into Hsize. pose proof Hsize as Hsh.
    eapply size_of_eval_expr_result_has_shape in Hsh; eauto.
    rename H4 into Hk. pose proof Hk as Hk'.
    eapply eval_Zexpr_includes_valuation in Hk'; try apply empty_includes.
    apply eval_Zexpr_Z_eval_Zexpr in Hk'.
    rewrite Hk' in *. invs'. apply eval_Zexpr_Z_eval_Zexpr in Hk.
    cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *.
    pose proof H6 as Hpad.
    eapply has_pad_gen_pad in Hpad; eauto.
    simpl in Hpad. invs'.

    pose proof Hsize as Heval.
    eapply IHeval_expr in Heval; eauto.
    rewrite <- (firstn_skipn (Z.to_nat kz) l).
    eapply forall_firstn_ge with (m:= Z.to_nat kz) in H.
    2: { lia. }
    eapply forall_eq_gen_pad in H. rewrite H.
    simpl gen_pad_list.
    
    rewrite length_firstn. 
    erewrite result_has_shape_length.
    2: { eauto. } 

    rewrite min_l by lia.
    pose proof Halloc as Halloc2.
    eapply well_formed_allocation_result_V in Halloc2. invert Halloc2. invs.

    destruct (m - Z.to_nat kz) eqn:hmk.
    { rewrite skipn_all2. rewrite app_nil_r.
      2: { erewrite result_has_shape_length.
           2: { eauto using size_of_eval_expr_result_has_shape. }
           lia. }
      replace (V (repeat (gen_pad sh0) (Z.to_nat kz))) with
        (gen_pad (Z.to_nat kz :: sh0))
        by eauto.
      decomp_well_formed_reindexer. propositional.
      erewrite filter_negb_is_None_result_lookup_Z_option_gen_pad.
      unfold partial_injective. simpl. propositional.
      destruct l1; destruct l2; eauto.
      invert H4. discriminate.
      invert H4. discriminate.
      destruct p0. destruct p1. eapply HeqZlist.
      erewrite <- eq_Z_tuple_index_list_cons_tup in *.
      propositional. subst. eapply eq_zexpr_sub; eauto.
      subst. reflexivity.
      destruct l1; rewrite Hmap. eauto. eauto. 
      destruct p0. simpl. unfold subst_var_in_Z_tup at 1. reflexivity.
      eauto.
      destruct l1; rewrite Hvarsarg; eauto.
      destruct p0. simpl. rewrite app_no_dups_empty_r. reflexivity.
      unfold nondestructivity in *.
      unfold tensor_to_array_delta.
      rewrite filter_negb_is_None_result_lookup_Z_option_gen_pad.
      unfold tensor_to_array_delta_by_indices.
      simpl. rewrite dom_empty.
      split; intros. sets.
      eapply Hnondstr; eauto.
    }
    eapply well_formed_reindexer_truncl.
    rewrite <- truncl_list_skipn. eauto. simpl.
    eapply forall_result_has_shape.
    eapply Forall_app. split.
    simpl. eapply Forall_repeat. eapply result_has_shape_gen_pad.
    eapply forall_skipn. eapply result_has_shape_forall. eauto.
    rewrite length_app. simpl. rewrite length_skipn.
    rewrite repeat_length. erewrite result_has_shape_length by eauto.
    instantiate (1 := m). lia.
    apply Henv. eauto. eauto. lia. apply Hrdx. 

    rewrite <- (firstn_skipn (Z.to_nat kz) l).
    eapply forall_firstn_ge with (m:= Z.to_nat kz) in H.
    2: { lia. }
    eapply forall_eq_gen_pad in H. rewrite H.
    simpl gen_pad_list.

    rewrite length_firstn.
    erewrite result_has_shape_length by eauto.

    rewrite min_l by lia.    
    eapply well_formed_allocation_truncl.
    erewrite <- truncl_list_skipn. eauto. apply Hrdx.
    simpl. eapply forall_result_has_shape.
    eapply Forall_app. split.
    simpl. eapply Forall_repeat. eapply result_has_shape_gen_pad.
    eapply forall_skipn. eapply result_has_shape_forall. eauto.
    rewrite length_app. simpl. rewrite length_skipn.
    rewrite repeat_length. erewrite result_has_shape_length by eauto.
    instantiate (1 := m). lia. lia.
    apply Hrdx. eauto. eauto. apply Henv. apply Hrdx. apply Hrdx.

  - invert Hsize. eq_size_of. invs'.
    rename H1 into Hsize. pose proof Hsize as Hsh.
    eapply size_of_eval_expr_result_has_shape in Hsh; eauto.
    rename H5 into Hk. pose proof Hk as Hk'.
    eapply eval_Zexpr_includes_valuation in Hk'; try apply empty_includes.
    apply eval_Zexpr_Z_eval_Zexpr in Hk'.
    rewrite Hk' in *. invs'. apply eval_Zexpr_Z_eval_Zexpr in Hk.
    
    invert Hpad.
    + eq_size_of. invs'. invert Hsh.
      pose proof Hsize as Heval.
      eapply IHeval_expr in Heval; eauto.
      { decomp_well_formed_reindexer. propositional.
        - unfold result_shape_Z. unfold partial_injective. simpl.
          propositional.
        - eapply HeqZlist. cases l1; cases l2.
          eauto.
          invert H. discriminate. 
          invert H. discriminate. 
          cases p0. cases p1.
          erewrite <- eq_Z_tuple_index_list_cons_tup in H. invs'.
          erewrite <- eq_Z_tuple_index_list_cons_tup. split. eauto. split.
          lia. eauto.
        - rewrite Hmap by eauto. cases l; eauto. simpl.
          cases p0. simpl. reflexivity.
        - rewrite Hvarsarg. cases l; eauto. cases p0. reflexivity.
        - unfold nondestructivity. unfold tensor_to_array_delta. simpl.
          unfold tensor_to_array_delta_by_indices. simpl. rewrite dom_empty.
          split; intros. sets.
          eapply well_formed_allocation_result_V in Halloc. invs.
          eapply lookup_Some_dom in H1. sets. eauto. }
      { unfold well_formed_allocation.
        cases (shape_to_index (result_shape_Z (V []))
                              (shape_to_vars (result_shape_Z (V [])))).
        eapply shape_to_index_not_empty_Z in Heq. propositional.
        destruct (reindexer (let (v0, d) := p0 in _)) eqn:Heq0.
        { eapply reindexer_not_empty_vars_in_index in Heq0. propositional.
          apply Hrdx.
          unfold not. intros.
          unfold shape_to_index, shape_to_vars, result_shape_Z in *.
          simpl in Heq. invert Heq. simpl in *. cups_empty. }
        pose proof Halloc as Halloc'.
        eapply well_formed_allocation_result_V in Halloc'. invs.
        eexists. split. eassumption. unfold result_shape_Z. simpl. sets.
        apply Hrdx. }
    + eq_size_of. invs'. invert Hsh. lia.
      pose proof Hsize as Heval.
      eapply IHeval_expr in Heval; eauto.
      { cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *.
        pose proof Halloc as Halloc2.
        eapply well_formed_allocation_result_V in Halloc2. invs'.
        rewrite <- (Z2Nat.id kz) by lia.
        eapply well_formed_reindexer_padr. eauto.
        simpl gen_pad_list in *. econstructor; eauto.
        eauto. lia. apply Henv. eauto. apply Hrdx. }
      { cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *.
        eapply well_formed_allocation_padr. econstructor; eauto.
        eauto. simpl gen_pad_list in *. eauto. apply Hrdx. apply Henv.
        apply Hrdx. apply Hrdx. apply Hrdx. }
  - invert Hsize. eq_size_of. invs'.
    rename H1 into Hsize. pose proof Hsize as Hsh.
    eapply size_of_eval_expr_result_has_shape in Hsh; eauto.
    rename H5 into Hk. pose proof Hk as Hk'.
    eapply eval_Zexpr_includes_valuation in Hk'; try apply empty_includes.
    apply eval_Zexpr_Z_eval_Zexpr in Hk'.
    rewrite Hk' in *. invs'. apply eval_Zexpr_Z_eval_Zexpr in Hk.

    invert Hpad.
    + eq_size_of. invs'. invert Hsh.
      pose proof Hsize as Heval.
      eapply IHeval_expr in Heval; eauto.
      { decomp_well_formed_reindexer. propositional.
        - unfold result_shape_Z. unfold partial_injective. simpl.
          propositional.
        - eapply HeqZlist. cases l1; cases l2.
          eauto.
          invert H. discriminate.
          invert H. discriminate.
          cases p0. cases p1.
          erewrite <- eq_Z_tuple_index_list_cons_tup in H. invs'.
          erewrite <- eq_Z_tuple_index_list_cons_tup. split.
          eapply eq_zexpr_add; eauto. split.
          reflexivity.
          assumption.
        - rewrite Hmap by eauto. cases l; eauto. simpl.
          cases p0. reflexivity.
        - rewrite Hvarsarg. cases l; eauto. cases p0. simpl.
          rewrite app_no_dups_empty_r. reflexivity.
        - unfold nondestructivity.
          unfold tensor_to_array_delta, tensor_to_array_delta_by_indices.
          simpl. rewrite dom_empty. split; intros.
          sets.
          eapply well_formed_allocation_result_V in Halloc. invs'.
          eapply lookup_Some_dom in H1. sets. eauto.
      }
      { unfold well_formed_allocation.
        cases (shape_to_index (result_shape_Z (V []))
                              (shape_to_vars (result_shape_Z (V [])))).
        eapply shape_to_index_not_empty_Z in Heq. propositional.
        destruct (reindexer (let (v0, d) := p0 in _)) eqn:Heq0.
        { eapply reindexer_not_empty_vars_in_index in Heq0. propositional.
          apply Hrdx.
          unfold not. intros.
          unfold shape_to_index, shape_to_vars, result_shape_Z in *.
          simpl in Heq. invs'. simpl in *. cups_empty. }
        pose proof Halloc as Halloc'. rewrite app_nil_r in *.
        eapply well_formed_allocation_result_V in Halloc'. invs.
        eexists. split. eassumption. unfold result_shape_Z. simpl. sets.
        apply Hrdx. }
    + eq_size_of. invs'.
      
      simpl gen_pad_list in *.

      pose proof Hsize as Heval.
      eapply IHeval_expr in Heval; eauto.
      { cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *.
        pose proof Halloc as Halloc2.
        eapply well_formed_allocation_result_V in Halloc2. invs'.
        eapply well_formed_reindexer_padl. apply Hrdx.
        simpl map in *. eauto. apply Henv. eauto.
        lia. apply Hrdx. apply Hrdx. apply Hrdx. apply Hrdx. eauto.
        eapply Hrdx. eauto. apply Hrdx.
      }
      { cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *.
        pose proof Halloc as Halloc2.
        eapply well_formed_allocation_result_V in Halloc2.
        invs. eapply well_formed_allocation_padl. eauto. eauto.
        apply Hrdx. lia. apply Hrdx. eauto.
        apply Henv. apply Hrdx. apply Hrdx. apply Hrdx. }
  - simpl in *. invert Hsize.
    pose proof Halloc as Halloc1.
    unfold well_formed_allocation in Halloc.
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
             decomp_well_formed_reindexer.
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

        decomp_well_formed_reindexer.
        eapply eval_Zexpr_Z_flatten_index_flatten.
        eapply eval_Zexprlist_map_partially_eval_Zexpr.
        eapply forall_no_vars_eval_Zexpr_Z_total.
        eapply Forall_map. eapply Forall_forall.
        intros.
        eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.
        eapply subseteq_transitivity.
        eapply fst_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
        eauto.
        eassumption.

        rewrite <- Heq.
        rewrite map_snd_map_partially_eval_Z_tup.
        rewrite map_fst_map_partially_eval_Z_tup. sets.
        rewrite <- Heq in *.
        eapply eval_Zexprlist_map_partially_eval_Zexpr.
        eapply forall_no_vars_eval_Zexpr_Z_total.
        decomp_well_formed_reindexer.
        rewrite map_fst_map_partially_eval_Z_tup.
        eapply Forall_map. eapply Forall_forall. intros.
        eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.
        eapply subseteq_transitivity.
        eapply fst_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
        eauto.
        eapply eval_Zexprlist_map_partially_eval_Zexpr.
        eapply forall_no_vars_eval_Zexpr_Z_total.
        decomp_well_formed_reindexer.
        rewrite map_fst_map_partially_eval_Z_tup.
        eapply Forall_map. eapply Forall_forall. intros.
        eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.
        eapply subseteq_transitivity.
        eapply fst_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
        eauto.
        rewrite <- Heq in *. eauto.
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
             decomp_well_formed_reindexer.
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

        decomp_well_formed_reindexer.
        eapply eval_Zexpr_Z_flatten_index_flatten.
        eapply eval_Zexprlist_map_partially_eval_Zexpr.
        eapply forall_no_vars_eval_Zexpr_Z_total.
        eapply Forall_map. eapply Forall_forall.
        intros.
        eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.
        eapply subseteq_transitivity.
        eapply fst_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
        eauto.
        eassumption.

        rewrite <- Heq.
        rewrite map_snd_map_partially_eval_Z_tup.
        rewrite map_fst_map_partially_eval_Z_tup. sets.
        rewrite <- Heq in *.
        eapply eval_Zexprlist_map_partially_eval_Zexpr.
        eapply forall_no_vars_eval_Zexpr_Z_total.
        decomp_well_formed_reindexer.
        rewrite map_fst_map_partially_eval_Z_tup.
        eapply Forall_map. eapply Forall_forall. intros.
        eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.
        eapply subseteq_transitivity.
        eapply fst_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
        eauto.
        eapply eval_Zexprlist_map_partially_eval_Zexpr.
        eapply forall_no_vars_eval_Zexpr_Z_total.
        decomp_well_formed_reindexer.
        rewrite map_fst_map_partially_eval_Z_tup.
        eapply Forall_map. eapply Forall_forall. intros.
        eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.
        eapply subseteq_transitivity.
        eapply fst_vars_of_reindexer_vars_of_Zexpr_subseteq. eauto.
        eauto.
        rewrite <- Heq in *. eauto.
        Unshelve. all: exact nil.
Qed.
