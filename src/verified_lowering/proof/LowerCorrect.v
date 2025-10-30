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
     Injective Constant InterpretReindexer 
     WellFormedEnvironment WellFormedReindexer WellFormedAllocation
     ResultToArrayDelta ContextsAgree Pad ATLDeep.

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

Theorem lower_correct_weak :
  forall e,
    forall sh v ec r,
      (* functional evaluation of ATL *)
      eval_expr sh v ec e r ->
      forall l, size_of e l ->
      forall p st h st' h' reindexer asn,
        (* imperative evaluation of lowering *)
        eval_stmt v st h (lower e reindexer p asn sh) st' h' ->
        (* our environment is well-formed *)
        well_formed_environment st h p sh v (vars_of e) ec ->
        (* reindexer is well-formed *)
        well_formed_reindexer reindexer v r st h p asn ->
        (* allocation is well-formed *)
        well_formed_allocation reindexer r st h p v ->
        (* expr context and imperative state agree *)
        contexts_agree ec st h sh ->
        forall pads g,
          has_pad sh v g e pads ->
        (forall pads (x : var) (r0 : result),
            g $? x = Some pads ->
            ec $? x = Some r0 ->
            relate_pads pads r0 (result_shape_nat r0)) ->
        match reindexer (shape_to_index
                           (result_shape_Z r)
                           (shape_to_vars (result_shape_Z r))) with
        | [] => h' = h
           /\ st' = st $+ (p, match st $? p with
                              | Some r => r
                              |_ => 0%R
                              end + match r with
                                    | S (SS s) => s
                                    | _ => 0%R
                                    end)%R
        | _ =>
            (h' = h $+ (p,
                         array_add
                           (h $! p)
                           (tensor_to_array_delta
                              (partial_interpret_reindexer reindexer
                                                   (result_shape_Z r) v) r))
             /\ st' = st)
        end.
Proof.
  intros e sh v ec r.
  induct 1; intros ls Hsize p st h st' h' reindexer asm
                   Heval Henv Hrdx Halloc Hctx pads g Hpad Hrelate.
  12: { (* SPLIT *) simpl in *. invert Hsize.
        rename H5 into Hk. apply eval_Zexpr_Z_eval_Zexpr in Hk.
        cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *. invs'.
        
     assert (result_has_shape (V l) (n::sh0)) as Hsh.
     { eapply size_of_eval_expr_result_has_shape in H.
       eapply H. eassumption. }

     pose proof Hsh as Hsh'.
     repeat rewrite map_cons in *.
     eapply result_has_shape_split_result
       with (k:=Z.to_nat kz) in Hsh'.
     2: { invert Hpad. lia. }

     invert Hpad.
     eapply IHeval_expr in Heval.
     2: { eauto. }
     2: { eauto. }
     2: { eapply well_formed_allocation_result_V in Halloc.
          2: { apply Hrdx. } invs'.
          eapply well_formed_reindexer_split; eauto.
          apply Henv. }
     2: { eapply well_formed_allocation_split; eauto.
          apply Hrdx. apply Hrdx. apply Henv. apply Hrdx. apply Hrdx. }
     2: { eauto. }
     2: { eauto. }
     2: { eauto. }

     eq_size_of. invert H0.
     cases (shape_to_index (result_shape_Z (V l))
                           (shape_to_vars (result_shape_Z (V l)))).
     { eapply shape_to_index_not_empty_Z in Heq. propositional. }
     destruct (reindexer (let (v, d) := p0 in _)) eqn:Heq0.
     { unfold result_shape_Z,shape_to_index, shape_to_vars in Heq.
       simpl in Heq. cases l.
       - simpl in *. invert Heq.
         eapply reindexer_not_empty_vars_in_index in Heq0.
         2: { apply Hrdx. }
         2: { simpl. unfold not. intros. cups_empty. }
         propositional.
       - simpl in *. invert Heq.
         eapply reindexer_not_empty_vars_in_index in Heq0.
         2: { apply Hrdx. }
         2: { simpl. unfold not. intros. cups_empty. }
         propositional. }
     
     destruct Heval.
     cases (reindexer
      (shape_to_index
         (result_shape_Z (V (split_result (Z.to_nat kz) l)))
         (shape_to_vars
            (result_shape_Z
               (V (split_result (Z.to_nat kz) l)))))).
     { eapply reindexer_not_empty in Heq1. propositional.
       apply Hrdx. erewrite result_has_shape_result_shape_Z.
       2: { eauto. }
       cases (m //n (Z.to_nat kz)).
       simpl. inversion 1.
       simpl. inversion 1. }
     pose proof Halloc as Halloc'.
     eapply well_formed_allocation_result_V in Halloc'.
     invs'.
     unfold lookup_total. rewrite H0. split; auto.
     2: apply Hrdx.
     f_equal. f_equal.
     unfold tensor_to_array_delta.
     erewrite result_has_shape_result_shape_Z.
     2: { eauto. }
     erewrite result_has_shape_result_shape_Z.
     2: { eauto. }
     cases l.
     { simpl. invert Hsh. rewrite div_ceil_n_0. simpl.
       unfold tensor_to_array_delta_by_indices. reflexivity. lia. }
     cases m.
     {  invert Hsh. }
     rewrite filter_until_0_cons by lia.
     symmetry.
     eapply eq_tensor_to_array_delta_by_indices_shuffle
       with (shuffle:= fun l =>
                         match l with
                         | x::xs => (x/kz)%Z
                                    ::(Zmod x kz)%Z::xs
                         | _ => l
                         end).
        - intros. cases x0. propositional.
          rewrite map_cons in *.
          repeat decomp_index. remember (Z.to_nat _).
          rewrite <- (Z2Nat.id kz) by lia.
          subst.
          eapply result_lookup_Z_option_split; eauto. lia. lia. lia.
        - rewrite map_cons. intros. cases x0. propositional.
          repeat decomp_index. 
          erewrite <- eq_partial_interpret_reindexer_split;
            try apply Henv; try apply Hrdx; try lia; eauto.
          repeat decomp_index. eauto.
          repeat decomp_index. eauto.
        - repeat rewrite map_cons.
          intros. repeat decomp_index.
          eapply filter_In. split.
          repeat decomp_goal_index.
          split. split.
          eapply Z.div_pos. lia. lia.
          rewrite <- of_nat_div_distr by lia.
          rewrite Z2Nat.id by lia.
          eapply floor_lt_ceil_mono_l; lia.
          decomp_goal_index. split.
          rewrite Z2Nat.id by lia. eapply Z.mod_pos_bound. lia.
          eauto.
          rewrite <- H10.
          f_equal. f_equal.
          rewrite <- (Z2Nat.id kz) at 1 by lia.
          rewrite <- (Z2Nat.id kz) at 2 by lia.
          erewrite result_lookup_Z_option_split. reflexivity.
          eauto. lia. apply H5. lia. eauto.
        - repeat rewrite map_cons.
          intros. repeat decomp_index.
          eexists ((z*kz + z0)%Z::x0).
          rewrite Z.div_add_l by lia.
          rewrite Z.div_small by lia. rewrite Z.add_0_r.
          pose proof Z.add_mul_mod_distr_r.
          specialize H11 with (b:=1%Z) (c:= kz).
          rewrite Z.mul_1_l in *.
          rewrite H11.
          rewrite Z.mod_1_r. split. auto.
          eapply filter_In. split.
          repeat decomp_goal_index. split.
          split. lia.
          rewrite <- of_nat_div_distr in * by lia.
          rewrite Z2Nat.id in * by lia.
          eapply result_lookup_Z_option_split_true. eauto.
          lia. lia. lia. eauto. rewrite Nat2Z.id. eauto.
          decomp_goal_index. eauto.
          rewrite <- H10. f_equal. f_equal.
          erewrite <- result_lookup_Z_option_split with (k:=Z.to_nat kz).
          2: { eauto. }
          2: { lia. }
          3: lia.
          3: { eauto. }
          all: try lia.
          2: { rewrite <- of_nat_div_distr in * by lia.
               rewrite Z2Nat.id in * by lia.
               eapply result_lookup_Z_option_split_true. eauto.
               lia. lia. lia. eauto. rewrite Nat2Z.id. eauto.  }
          rewrite Z2Nat.id by lia.
          rewrite Z.div_add_l by lia. rewrite Z.div_small by lia.
          rewrite Z.add_0_r.
          pose proof Z.add_mul_mod_distr_r.
          specialize H13 with (b:=1%Z) (c:= kz).
          rewrite Z.mul_1_l in *.
          rewrite H11.
          rewrite Z.mod_1_r. reflexivity. lia. lia. lia.
        - replace (map Z.of_nat (Datatypes.S m :: filter_until sh1 0))
            with
            (result_shape_Z (V (r0::l))).
          2: { erewrite result_has_shape_result_shape_Z by eauto.
               reflexivity. }
          eapply partial_injective_split. apply Hrdx.
          eauto. apply Henv.
          apply Hrdx. apply Hrdx. apply Hrdx. apply Hrdx. lia.
        - replace (map Z.of_nat
             (filter_until
                (Datatypes.S m //n (Z.to_nat kz)
                 :: Z.to_nat kz
                 :: sh1) 0)) with
            (result_shape_Z
               (V (split_result (Z.to_nat kz) (r0 :: l)))).
          apply Hrdx.
          erewrite result_has_shape_result_shape_Z.
          2:{ eapply result_has_shape_split_result. lia. eauto. }
          reflexivity.
        - unfold injective. propositional.
          repeat decomp_index.
          repeat rewrite map_cons in *. repeat decomp_index.
          invert H11.
          rewrite (Z.div_mod z kz).
          rewrite (Z.div_mod z0 kz).
          rewrite H16. rewrite H17. reflexivity. lia. lia.
        - eapply no_dup_filter. eauto with reindexers.
        - eapply no_dup_filter. eauto with reindexers.
  } 
   - (* EMPTY GEN *)
     simpl in *.
     rewrite array_add_empty_r.
     unfold lookup_total.
     invert Heval.
     rewrite H,H0 in *. invert H6. invert H9. lia.
     rewrite H,H0 in *. invert H10. invert H11.
     eapply well_formed_allocation_result_V in Halloc; try apply Hrdx.
     cases (reindexer
              (shape_to_index (result_shape_Z (V []))
                              (shape_to_vars (result_shape_Z (V []))))).
     eapply reindexer_not_empty in Heq; simpl; propositional; try apply Hrdx;
       discriminate.
     clear Heq. invs'.
     rewrite H3. rewrite add_id. auto. auto.
   - (* STEPPING GEN *)
     simpl in Heval.
     unfold lookup_total in *.
     invert Hsize. rename H10 into Hsize.
     rename H12 into Hlo. rename H13 into Hhi.
     pose proof Hlo as Hlo'. pose proof Hhi as Hhi'.
     eapply eval_Zexpr_includes_valuation in Hlo', Hhi'; try apply empty_includes.
     apply eval_Zexpr_Z_eval_Zexpr in Hlo', Hhi'. rewrite Hlo', Hhi' in *. invs'.
     apply eval_Zexpr_Z_eval_Zexpr in Hlo, Hhi.

     assert (result_has_shape (V (r::l)) (result_shape_nat (V(r::l)))) as Hsh.
     { assert (eval_expr sh v ec (Gen i lo hi body) (V (r::l))).
       econstructor; eauto.
       eapply result_has_shape_self.
       eapply size_of_eval_expr_result_has_shape.
       2: eassumption. eauto. econstructor; eauto.
       apply eval_Zexpr_Z_eval_Zexpr. eassumption.
       apply eval_Zexpr_Z_eval_Zexpr. eassumption. }
     pose proof Halloc as Halloc1.
     eapply well_formed_allocation_result_V in Halloc; try apply Hrdx.
     invs'.
     cases (reindexer
      (shape_to_index (result_shape_Z (V (r :: l)))
                      (shape_to_vars (result_shape_Z (V (r :: l)))))).
     eapply reindexer_not_empty in Heq; propositional; try apply Hrdx;
       discriminate.
     erewrite <- tensor_to_array_delta_cons
       with (i:=i) (hi:=hiz) (lo:=loz);
       try eapply result_shape_gen_length in H5; eauto; simpl;
       try rewrite H; try rewrite Hlo'; try rewrite Hhi'; try reflexivity; try lia.
     2: apply Hrdx.
     2: apply Hrdx.
     2: apply Hrdx.
     2: apply Hrdx.
     2: apply Hrdx.
     2: apply Henv.
     2: { unfold shape_to_vars. unfold not. intros. eapply H3.
          eapply in_map_iff in H. invs'.
          eapply var_generation_contains_substring. }
     invert Heval.
     2: { rewrite Hlo', Hhi' in *. invs'. lia. }
     rewrite Hlo',Hhi' in *. invs'. invert Hpad.

     cbv [eval_Zexpr_Z_total] in *. cbn [eval_Zexpr_Z] in *. rewrite Hlo, Hhi in *.

     cases k.
     2: { eapply IHeval_expr1 in H17.
          cases (reindexer
                   (((! i ! - | loz0 |)%z, (hiz0 - loz0)%Z)
                      :: shape_to_index (result_shape_Z r)
                      (shape_to_vars (result_shape_Z r)))).
          { eapply reindexer_not_empty_vars_in_index in Heq0; try apply Hrdx.
            propositional.
            simpl. unfold app_no_dups.
            rewrite <- union_constant.
            unfold not. intros. cups_empty. }
          invs'.
          * clear IHeval_expr1. pose proof IHeval_expr2 as H. simpl in H.
            unfold shift_top_dim_reindexer.
            specialize H with
              (p:=p)
              (reindexer:= shift_top_dim_reindexer reindexer)
              (h:=(h $+ (p,
                          array_add
                            x
                            (tensor_to_array_delta
                               (partial_interpret_reindexer
                                  (fun l =>
                                     reindexer
                                       (((! i ! - | loz0 |)%z,(hiz0 - loz0)%Z) :: l))
                                  (result_shape_Z r)
                                  (v $+ (i, loz0))) r)))).
            rewrite lookup_add_eq in * by auto.
            rewrite add_overwrite in H.
            rewrite (array_add_comm (tensor_to_array_delta _ _)).
            rewrite array_add_assoc.
            cases (shift_top_dim_reindexer
                     reindexer
                     (shape_to_index (result_shape_Z (V l))
                                     (shape_to_vars (result_shape_Z (V l))))).
            { unfold shift_top_dim_reindexer in Heq1.
              unfold result_shape_Z, shape_to_vars, shape_to_index in Heq1.
              simpl in Heq1.
              cases l; invert Heq1.
              - eapply reindexer_not_empty_vars_in_index in H8. propositional.
                apply Hrdx. simpl. unfold not. intros. cups_empty.
              - eapply reindexer_not_empty_vars_in_index in H8. propositional.
                apply Hrdx. simpl. unfold not. intros. cups_empty. }
            rewrite H0 in *. eapply H with (st:=st) (st':=st') (asn:=asm).
            -- econstructor. eauto.
               apply eval_Zexpr_Z_eval_Zexpr. simpl. rewrite Hlo. reflexivity.
               apply eval_Zexpr_Z_eval_Zexpr. simpl. rewrite Hhi. reflexivity.
               reflexivity.
            -- clear IHeval_expr2.
            invs'.
            unfold shift_top_dim_reindexer.
            eapply eq_eval_stmt_for.
            eassumption. simpl. rewrite Hlo'. reflexivity.
            rewrite Hhi'. eauto.
            intros.
            eapply eq_eval_stmt_lower_eq_reindexers;
              simpl; intros; decomp_well_formed_reindexer.
            ++ eassumption.
            ++ invs'. eapply HeqZlist.
               erewrite <- eq_Z_tuple_index_list_cons.
               propositional.
               cbv [eval_Zexpr_Z_total]. simpl. rewrite Hhi, Hlo.
               2: apply eq_Z_tuple_index_list_id.
               unfold eq_Z_tup. simpl.
               split.
               eapply eq_zexpr_comm.
               eapply eq_zexpr_transitivity.
               eapply eq_zexpr_sub_sub_distr.
               eapply eq_zexpr_transitivity.
               eapply eq_zexpr_sub.
               eapply eq_zexpr_id. auto.
               apply eq_zexpr_sub_literal.
               apply eq_zexpr_id.
               f_equal. f_equal. lia. lia.
         -- decomp_well_formed_environment.
            unfold well_formed_environment.
            split. auto.
            ++ rewrite dom_add.
               eapply lookup_Some_dom in H0.
               unfold well_formed_environment in *. invs'.
               simpl in *.
               split.
               replace (constant [p] \cup dom h) with (dom h) by sets.
               eauto.
               split.
               rewrite intersection_comm.
               rewrite intersection_comm in Hsthec.
               repeat rewrite cap_distr.
               repeat rewrite cap_distr in Hsthec.
               eapply cup_empty in Hsthec.
               inversion Hsthec as [ Hsthec1 Hsthec2 ]. clear Hsthec.
               eapply cup_empty in Hsthec1.
               inversion Hsthec1 as [ Hsthec3 Hsthec4 ]. clear Hsthec1.
               rewrite Hsthec3,Hsthec4,Hsthec2.
               repeat rewrite cup_empty_r.
               rewrite cup_empty_l.
               eapply constant_cap_empty. auto.
               propositional.
         -- unfold well_formed_environment in *. invs'.
            eapply well_formed_reindexer_shift_top_dim_reindexer;
              eauto.
         -- eapply well_formed_allocation_shift_top_dim_reindexer;
              try apply Hrdx; try apply Henv; eauto.
         -- eapply contexts_agree_add_heap; try apply Henv; auto.
         -- eapply HasPadGen with (k:=k) (c:=c) (ll:=ll) (rr:=rr).
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
            eauto.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo.
            intros. apply H20; lia.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hhi.
            intros. apply H22; lia.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
            intros. apply H23; lia.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
            intros. lia.
         -- eauto.
     * eassumption.
     * eapply well_formed_environment_add_valuation.
       simpl in Henv.
       auto. auto. auto.
     * eapply well_formed_allocation_result_V in Halloc1.
       eapply well_formed_reindexer_eval0. eassumption.
       eapply Henv.
       eauto. eauto. 
       unfold not. intros H.
       eapply shape_to_vars_contains_substring in H.
       propositional.
       simpl in *. lia. auto. auto. eauto.
       lia. eauto. apply Hrdx.
     * eapply well_formed_allocation_eval_step;
         try apply Halloc; eauto; try apply Hrdx; try apply Henv.
     * eauto.
     * eapply H23; lia.
     * eauto.
}

     (* k = 0, no left padding *)
     cases ll.
     2: { eapply IHeval_expr1 in H17.
          cases (reindexer
                   (((! i ! - | loz0 |)%z, (hiz0 - loz0)%Z)
                      :: shape_to_index (result_shape_Z r)
                      (shape_to_vars (result_shape_Z r)))).
          { eapply reindexer_not_empty_vars_in_index in Heq0; try apply Hrdx.
            propositional.
            simpl. unfold app_no_dups.
            rewrite <- union_constant.
            unfold not. intros. cups_empty. }
          invs'. clear Heq0. clear Heq.
          * clear IHeval_expr1. pose proof IHeval_expr2 as H. simpl in H.
            unfold shift_top_dim_reindexer.
            specialize H with
              (p:=p)
              (reindexer:= shift_top_dim_reindexer reindexer)
              (h:=(h $+ (p,
                          array_add
                            x
                            (tensor_to_array_delta
                               (partial_interpret_reindexer
                                  (fun l =>
                                     reindexer
                                       (((! i ! - | loz0 |)%z,(hiz0 - loz0)%Z) :: l))
                                  (result_shape_Z r)
                                  (v $+ (i, loz0))) r)))).
            rewrite lookup_add_eq in * by auto.
            rewrite add_overwrite in H.
            rewrite (array_add_comm (tensor_to_array_delta _ _)).
            rewrite array_add_assoc.
            cases (shift_top_dim_reindexer
                     reindexer
                     (shape_to_index (result_shape_Z (V l))
                                     (shape_to_vars (result_shape_Z (V l))))).
            { unfold shift_top_dim_reindexer in Heq.
              unfold result_shape_Z, shape_to_vars, shape_to_index in Heq.
              simpl in Heq.
              cases l; invert Heq.
              - eapply reindexer_not_empty_vars_in_index in H8. propositional.
                apply Hrdx. simpl. intros ?. cups_empty.
              - eapply reindexer_not_empty_vars_in_index in H8. propositional.
                apply Hrdx. simpl. intros ?. cups_empty. }
            rewrite H0 in *.
            cbv [eval_Zexpr_Z_total] in *. cbn [eval_Zexpr_Z] in *. rewrite Hlo, Hhi in *.
            eapply H with (st:=st) (st':=st') (asn:=asm).
         -- econstructor. eauto.
            apply eval_Zexpr_Z_eval_Zexpr. simpl. rewrite Hlo. reflexivity.
            apply eval_Zexpr_Z_eval_Zexpr. simpl. rewrite Hhi. reflexivity.
            reflexivity.
         -- clear IHeval_expr2.
            invs'.
            unfold shift_top_dim_reindexer.
            eapply eq_eval_stmt_for.
            eassumption. simpl. rewrite Hlo'. reflexivity.
            rewrite Hhi'. eauto.
            intros.
            eapply eq_eval_stmt_lower_eq_reindexers;
              simpl; intros; decomp_well_formed_reindexer.
            ++ eassumption.
            ++ invs'. eapply HeqZlist.
               erewrite <- eq_Z_tuple_index_list_cons.
               propositional.
               2: apply eq_Z_tuple_index_list_id.
               unfold eq_Z_tup. simpl.
               split.
               eapply eq_zexpr_comm.
               eapply eq_zexpr_transitivity.
               eapply eq_zexpr_sub_sub_distr.
               eapply eq_zexpr_transitivity.
               eapply eq_zexpr_sub.
               eapply eq_zexpr_id. auto.
               apply eq_zexpr_sub_literal.
               apply eq_zexpr_id.
               f_equal. f_equal. lia. lia.
         -- decomp_well_formed_environment.
            unfold well_formed_environment.
            split. auto.
            ++ rewrite dom_add.
               eapply lookup_Some_dom in H0.
               unfold well_formed_environment in *. invs'.
               simpl in *.
               split.
               replace (constant [p] \cup dom h) with (dom h) by sets.
               eauto.
               split.
               rewrite intersection_comm.
               rewrite intersection_comm in Hsthec.
               repeat rewrite cap_distr.
               repeat rewrite cap_distr in Hsthec.
               eapply cup_empty in Hsthec.
               inversion Hsthec as [ Hsthec1 Hsthec2 ]. clear Hsthec.
               eapply cup_empty in Hsthec1.
               inversion Hsthec1 as [ Hsthec3 Hsthec4 ]. clear Hsthec1.
               rewrite Hsthec3,Hsthec4,Hsthec2.
               repeat rewrite cup_empty_r.
               rewrite cup_empty_l.
               eapply constant_cap_empty. auto.
               propositional.
         -- unfold well_formed_environment in *. invs'.
            eapply well_formed_reindexer_shift_top_dim_reindexer;
              eauto.
         -- eapply well_formed_allocation_shift_top_dim_reindexer;
              try apply Hrdx; try apply Henv; eauto.
         -- eapply contexts_agree_add_heap; try apply Henv; auto.
         -- eapply HasPadGen with (k:=0) (c:=c) (ll:=ll) (rr:=rr).
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
            eauto.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo.
            intros. apply H20; lia.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hhi.
            intros. apply H22; lia.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
            intros. apply H23; lia.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
            intros. lia.
         -- eauto.
     * eassumption.
     * eapply well_formed_environment_add_valuation.
       simpl in Henv.
       auto. auto. auto.
     * eapply well_formed_allocation_result_V in Halloc1.
       eapply well_formed_reindexer_eval0. eassumption.
       eapply Henv.
       eauto. eauto. 
       unfold not. intros.
       eapply shape_to_vars_contains_substring in H.
       propositional.
       simpl in *. lia. auto. auto. eauto. lia. eauto. apply Hrdx.
     * eapply well_formed_allocation_eval_step;
         try apply Halloc; eauto; try apply Hrdx; try apply Henv.
     * eauto.
     * eapply H20; lia.
     * eauto.
     }

     cases rr.
          2: { eapply IHeval_expr1 in H17.
          cases (reindexer
                   (((! i ! - | loz0 |)%z, (hiz0 - loz0)%Z)
                      :: shape_to_index (result_shape_Z r)
                      (shape_to_vars (result_shape_Z r)))).
          { eapply reindexer_not_empty_vars_in_index in Heq0; try apply Hrdx.
            propositional.
            simpl. unfold app_no_dups.
            rewrite <- union_constant.
            unfold not. intros. cups_empty. }
          invs'. clear Heq0. clear Heq.
          * clear IHeval_expr1. pose proof IHeval_expr2 as H. simpl in H.
            unfold shift_top_dim_reindexer.
            specialize H with
              (p:=p)
              (reindexer:= shift_top_dim_reindexer reindexer)
              (h:=(h $+ (p,
                          array_add
                            x
                            (tensor_to_array_delta
                               (partial_interpret_reindexer
                                  (fun l =>
                                     reindexer
                                       (((! i ! - | loz0 |)%z,(hiz0 - loz0)%Z) :: l))
                                  (result_shape_Z r)
                                  (v $+ (i, loz0))) r)))).
            rewrite lookup_add_eq in * by auto.
            rewrite add_overwrite in H.
            rewrite (array_add_comm (tensor_to_array_delta _ _)).
            rewrite array_add_assoc.
            cases (shift_top_dim_reindexer
                     reindexer
                     (shape_to_index (result_shape_Z (V l))
                                     (shape_to_vars (result_shape_Z (V l))))).
            { unfold shift_top_dim_reindexer in Heq.
              unfold result_shape_Z, shape_to_vars, shape_to_index in Heq.
              simpl in Heq.
              cases l; invert Heq.
              - eapply reindexer_not_empty_vars_in_index in H8. propositional.
                apply Hrdx. simpl. unfold not. intros. cups_empty.
              - eapply reindexer_not_empty_vars_in_index in H8. propositional.
                apply Hrdx. simpl. unfold not. intros. cups_empty. }
            rewrite H0 in *.
            cbv [eval_Zexpr_Z_total] in *. cbn [eval_Zexpr_Z] in *. rewrite Hlo, Hhi in *.
            eapply H with (st:=st) (st':=st') (asn:=asm).
         -- econstructor. eauto.
            apply eval_Zexpr_Z_eval_Zexpr. simpl. rewrite Hlo. reflexivity.
            apply eval_Zexpr_Z_eval_Zexpr. simpl. rewrite Hhi. reflexivity.
            reflexivity.
         -- clear IHeval_expr2.
            invs'.
            unfold shift_top_dim_reindexer.
            eapply eq_eval_stmt_for.
            eassumption. simpl. rewrite Hlo'. reflexivity.
            rewrite Hhi'. eauto.
            intros.
            eapply eq_eval_stmt_lower_eq_reindexers;
              simpl; intros; decomp_well_formed_reindexer.
            ++ eassumption.
            ++ invs'. eapply HeqZlist.
               erewrite <- eq_Z_tuple_index_list_cons.
               propositional.
               2: apply eq_Z_tuple_index_list_id.
               unfold eq_Z_tup. simpl.
               split.
               eapply eq_zexpr_comm.
               eapply eq_zexpr_transitivity.
               eapply eq_zexpr_sub_sub_distr.
               eapply eq_zexpr_transitivity.
               eapply eq_zexpr_sub.
               eapply eq_zexpr_id. auto.
               apply eq_zexpr_sub_literal.
               apply eq_zexpr_id.
               f_equal. f_equal. lia. lia.
         -- decomp_well_formed_environment.
            unfold well_formed_environment.
            split. auto.
            ++ rewrite dom_add.
               eapply lookup_Some_dom in H0.
               unfold well_formed_environment in *. invs'.
               simpl in *.
               split.
               replace (constant [p] \cup dom h) with (dom h) by sets.
               eauto.
               split.
               rewrite intersection_comm.
               rewrite intersection_comm in Hsthec.
               repeat rewrite cap_distr.
               repeat rewrite cap_distr in Hsthec.
               eapply cup_empty in Hsthec.
               inversion Hsthec as [ Hsthec1 Hsthec2 ]. clear Hsthec.
               eapply cup_empty in Hsthec1.
               inversion Hsthec1 as [ Hsthec3 Hsthec4 ]. clear Hsthec1.
               rewrite Hsthec3,Hsthec4,Hsthec2.
               repeat rewrite cup_empty_r.
               rewrite cup_empty_l.
               eapply constant_cap_empty. auto.
               propositional.
         -- unfold well_formed_environment in *. invs'.
            eapply well_formed_reindexer_shift_top_dim_reindexer;
              eauto.
         -- eapply well_formed_allocation_shift_top_dim_reindexer;
              try apply Hrdx; try apply Henv; eauto.
         -- eapply contexts_agree_add_heap; try apply Henv; auto.
         -- eapply HasPadGen with (k:=0) (c:=c) (ll:=0) (rr:=rr).
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
            eauto.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo.
            intros. apply H20; lia.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hhi.
            intros. apply H22; lia.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
            intros. apply H23; lia.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
            intros. lia.
         -- eauto.
     * eassumption.
     * eapply well_formed_environment_add_valuation.
       simpl in Henv.
       auto. auto. auto.
     * eapply well_formed_allocation_result_V in Halloc1.
       eapply well_formed_reindexer_eval0. eassumption.
       eapply Henv.
       eauto. eauto. 
       unfold not. intros.
       eapply shape_to_vars_contains_substring in H.
       propositional.
       simpl in *. lia. auto. auto. eauto. lia. eauto. apply Hrdx.
     * eapply well_formed_allocation_eval_step;
         try apply Halloc; eauto; try apply Hrdx; try apply Henv.
     * eauto.
     * eapply H22; lia.
     * eauto.
 }

          eapply IHeval_expr1 in H17.
          cases (reindexer
                   (((! i ! - | loz0 |)%z, (hiz0 - loz0)%Z)
                      :: shape_to_index (result_shape_Z r)
                      (shape_to_vars (result_shape_Z r)))).
          { eapply reindexer_not_empty_vars_in_index in Heq0; try apply Hrdx.
            propositional.
            simpl. unfold app_no_dups.
            rewrite <- union_constant.
            unfold not. intros. cups_empty. }
          invs'. clear Heq0. clear Heq.
          * clear IHeval_expr1. pose proof IHeval_expr2 as H. simpl in H.
            unfold shift_top_dim_reindexer.
            specialize H with
              (p:=p)
              (reindexer:= shift_top_dim_reindexer reindexer)
              (h:=(h $+ (p,
                          array_add
                            x
                            (tensor_to_array_delta
                               (partial_interpret_reindexer
                                  (fun l =>
                                     reindexer
                                       (((! i ! - | loz0 |)%z,(hiz0 - loz0)%Z) :: l))
                                  (result_shape_Z r)
                                  (v $+ (i, loz0))) r)))).
            rewrite lookup_add_eq in * by auto.
            rewrite add_overwrite in H.
            rewrite (array_add_comm (tensor_to_array_delta _ _)).
            rewrite array_add_assoc.
            cases (shift_top_dim_reindexer
                     reindexer
                     (shape_to_index (result_shape_Z (V l))
                                     (shape_to_vars (result_shape_Z (V l))))).
            { unfold shift_top_dim_reindexer in Heq.
              unfold result_shape_Z, shape_to_vars, shape_to_index in Heq.
              simpl in Heq.
              cases l; invert Heq.
              - eapply reindexer_not_empty_vars_in_index in H8. propositional.
                apply Hrdx. simpl. unfold not. intros. cups_empty.
              - eapply reindexer_not_empty_vars_in_index in H8. propositional.
                apply Hrdx. simpl. unfold not. intros. cups_empty. }
            rewrite H0 in *.
            cbv [eval_Zexpr_Z_total] in *. cbn [eval_Zexpr_Z] in *. rewrite Hlo, Hhi in *.
            eapply H with (st:=st) (st':=st') (asn:=asm).
         -- econstructor. eauto.
            apply eval_Zexpr_Z_eval_Zexpr. simpl. rewrite Hlo. reflexivity.
            apply eval_Zexpr_Z_eval_Zexpr. simpl. rewrite Hhi. reflexivity.
            reflexivity.
         -- clear IHeval_expr2.
            invs'.
            unfold shift_top_dim_reindexer.
            eapply eq_eval_stmt_for.
            eassumption. simpl. rewrite Hlo'. reflexivity.
            rewrite Hhi'. eauto.
            intros.
            eapply eq_eval_stmt_lower_eq_reindexers;
              simpl; intros; decomp_well_formed_reindexer.
            ++ eassumption.
            ++ invs'. eapply HeqZlist.
               erewrite <- eq_Z_tuple_index_list_cons.
               propositional.
               2: apply eq_Z_tuple_index_list_id.
               unfold eq_Z_tup. simpl.
               split.
               eapply eq_zexpr_comm.
               eapply eq_zexpr_transitivity.
               eapply eq_zexpr_sub_sub_distr.
               eapply eq_zexpr_transitivity.
               eapply eq_zexpr_sub.
               eapply eq_zexpr_id. auto.
               apply eq_zexpr_sub_literal.
               apply eq_zexpr_id.
               f_equal. f_equal. lia. lia.
         -- decomp_well_formed_environment.
            unfold well_formed_environment.
            split. auto.
            ++ rewrite dom_add.
               eapply lookup_Some_dom in H0.
               unfold well_formed_environment in *. invs'.
               simpl in *.
               split.
               replace (constant [p] \cup dom h) with (dom h) by sets.
               eauto.
               split.
               rewrite intersection_comm.
               rewrite intersection_comm in Hsthec.
               repeat rewrite cap_distr.
               repeat rewrite cap_distr in Hsthec.
               eapply cup_empty in Hsthec.
               inversion Hsthec as [ Hsthec1 Hsthec2 ]. clear Hsthec.
               eapply cup_empty in Hsthec1.
               inversion Hsthec1 as [ Hsthec3 Hsthec4 ]. clear Hsthec1.
               rewrite Hsthec3,Hsthec4,Hsthec2.
               repeat rewrite cup_empty_r.
               rewrite cup_empty_l.
               eapply constant_cap_empty. auto.
               propositional.
         -- unfold well_formed_environment in *. invs'.
            eapply well_formed_reindexer_shift_top_dim_reindexer;
              eauto.
         -- eapply well_formed_allocation_shift_top_dim_reindexer;
              try apply Hrdx; try apply Henv; eauto.
         -- eapply contexts_agree_add_heap; try apply Henv; auto.
         -- eapply HasPadGen with (k:=0) (c:=c-1) (ll:=0) (rr:=0).
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
            eauto.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo.
            intros. apply H20; lia.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hhi.
            intros. apply H22; lia.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
            intros. apply H23; lia.
            cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
            intros. lia.
         -- eauto.
     * eassumption.
     * eapply well_formed_environment_add_valuation.
       simpl in Henv.
       auto. auto. auto.
     * eapply well_formed_allocation_result_V in Halloc1.
       eapply well_formed_reindexer_eval0. eassumption.
       eapply Henv.
       eauto. eauto. 
       unfold not. intros.
       eapply shape_to_vars_contains_substring in H.
       propositional.
       simpl in *. lia. auto. auto. eauto. lia. eauto. apply Hrdx.
     * eapply well_formed_allocation_eval_step;
         try apply Halloc; eauto; try apply Hrdx; try apply Henv.
     * eauto.
     * eapply H23; lia.
     * eauto.
   - (* STEPPING SUM *)
     simpl in *.
     unfold lookup_total in *.
     invert Hsize. rename H14 into Hsize.
     rename H12 into Hlo. rename H13 into Hhi.
     pose proof Hlo as Hlo'. pose proof Hhi as Hhi'.
     eapply eval_Zexpr_includes_valuation in Hlo', Hhi'; try apply empty_includes.
     apply eval_Zexpr_Z_eval_Zexpr in Hlo', Hhi'. rewrite Hlo', Hhi' in *. invs'.
     apply eval_Zexpr_Z_eval_Zexpr in Hlo, Hhi.
     
     assert (result_has_shape s ls) as Hsh.
     { assert (eval_expr sh v ec (Sum i lo hi body) s).
       econstructor; eauto.
       eapply size_of_eval_expr_result_has_shape.
       2: eassumption. eauto. econstructor; eauto.
       apply eval_Zexpr_Z_eval_Zexpr. eassumption.
       apply eval_Zexpr_Z_eval_Zexpr. eassumption. }
       pose proof H6 as Hshh.
       eapply result_has_shape_add_result_result in Hshh.
       2: { eassumption. }
       inversion Hshh as [Hsh1 Hsh2 ]. clear Hshh.
       invert Heval; eq_eval_Z; try lia.
       rewrite Hlo',Hhi' in *. invs'.
       invert Hpad.
       { cbv [eval_Zexpr_Z_total] in *. rewrite Hhi, Hlo in *. lia. }
         
       eapply IHeval_expr1 with (asn:=Reduce) in H16; clear IHeval_expr1.
       cases (reindexer
                (shape_to_index (result_shape_Z s)
                                (shape_to_vars (result_shape_Z s)))).
     + pose proof Halloc as Halloc1.
       erewrite result_has_shape_result_shape_Z in *; try eassumption.
       rewrite Heq in *. invs'.
       cases r.
       2: { invert Hsh1.
            eapply reindexer_not_empty in Heq.
            propositional. apply Hrdx. inversion 1.
            eapply reindexer_not_empty in Heq.
            propositional. apply Hrdx. inversion 1. }
       invert H6.
         invert Hsh. invert Hsh1. invert Hsh2.
         unfold well_formed_allocation in Halloc1.
         unfold result_shape_Z in Halloc1.
         simpl in Halloc1. simpl in Heq. rewrite Heq in Halloc1. invs'.
         rewrite H in *.

         cbv [eval_Zexpr_Z_total] in *. rewrite Hlo, Hhi in *.
         
         cases (Z.to_nat (hiz0 - (loz0 + 1))).
         { invert H5.
           cbv [eval_Zexpr_Z_total] in *. simpl in *. rewrite Hlo', Hhi' in *.
           invs'. lia.
           
           cbv [eval_Zexpr_Z_total] in *. simpl in *. rewrite Hlo', Hhi' in *.
           invs'.
           cases sz; simpl in *; try discriminate. invert H12.
           invert H0.
           * eapply IHeval_expr2 with (asn:=Reduce) in H17.
             2: { econstructor; eauto. econstructor; eauto.
                  apply eval_Zexpr_Z_eval_Zexpr. eassumption.
                  apply eval_Zexpr_Z_eval_Zexpr. eassumption. }
             2: { eapply well_formed_environment_add_stack. eauto.
                  eapply lookup_Some_dom in H. sets. }
             2: { replace (S SX) with (gen_pad []) by reflexivity.
                  decomp_well_formed_reindexer. simpl. propositional.
                  unfold partial_injective. intros. invert0 H5.
                  unfold nondestructivity. split; intros; discriminate. }
             2: { eapply well_formed_allocation_same_add_stack.
                  replace (S SX) with (gen_pad []) by reflexivity.
                  eapply well_formed_allocation_gen_pad. eauto.
                  econstructor. }
             2: { unfold well_formed_environment in *. invs'.
                  eapply contexts_agree_add_in_stack.
                  eauto. eauto. auto. eauto. }
             2: { eapply HasPadSumEmpty. eauto.
                  cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
                  reflexivity. }
             rewrite Heq in *. invs'.
             rewrite lookup_add_eq in * by auto.
             rewrite add_overwrite.
             propositional. f_equal. ring.
             eauto.
           * eapply IHeval_expr2 with (asn:=Reduce) in H17.
             2: { econstructor; eauto. econstructor; eauto.
                  apply eval_Zexpr_Z_eval_Zexpr. eassumption.
                  apply eval_Zexpr_Z_eval_Zexpr. eassumption. }
             2: { eapply well_formed_environment_add_stack. eauto.
                  eapply lookup_Some_dom in H. sets. }
             2: { replace (S SX) with (gen_pad []) by reflexivity.
                  decomp_well_formed_reindexer. propositional.
                  simpl. unfold nondestructivity.
                  split; intros; discriminate. }
             2: { rewrite Rplus_0_r. rewrite add_id by auto.
                  replace (S SX) with (gen_pad []) by reflexivity.
                  eapply well_formed_allocation_gen_pad. eauto.
                  econstructor. }
             2: { unfold well_formed_environment in *. invs'.
                  eapply contexts_agree_add_in_stack.
                  eauto. eauto. auto. eauto. }
             2: { eapply HasPadSumEmpty. eauto.
                  cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
                  reflexivity. }
             rewrite Heq in *. invs'.
             rewrite lookup_add_eq in * by auto.
             rewrite add_overwrite.
             propositional. f_equal. ring. eauto.
         }
         pose proof Heq0 as Heq'. clear Heq0.
         eapply IHeval_expr2 with (asn:=Reduce) in H17; clear IHeval_expr2.
         simpl in H17. rewrite Heq in *. invs'.
         rewrite lookup_add_eq by auto.
         rewrite add_overwrite. propositional. f_equal.
         cases z; cases s2; cases s3; try now invert H0.
         invert H0. ring.
         invert H0. ring.
         invert H0. ring.
         ring.
         { econstructor; eauto. econstructor; eauto.
           apply eval_Zexpr_Z_eval_Zexpr. eassumption.
           apply eval_Zexpr_Z_eval_Zexpr. eassumption. }
         eapply well_formed_environment_add_stack. eauto.
         eapply lookup_Some_dom. eauto.
         decomp_well_formed_reindexer.
         unfold result_shape_Z in *. simpl in *. propositional.
         cases s2; cases s3; simpl in *; auto.
         invert H0. invert H0. simpl in *.
         unfold partial_injective in *.
         propositional. simpl in *. propositional.
         unfold nondestructivity.
         split; intros; discriminate.
         unfold well_formed_allocation.
         unfold result_shape_Z. simpl. rewrite Heq.
         eexists. rewrite lookup_add_eq by auto.
         reflexivity.
         eapply contexts_agree_add_in_stack; eauto.
         apply Henv. apply Henv.
         apply HasPadSum.
         cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
         intros. eapply H13; lia.
         cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
         eauto.
     + pose proof Heq.
       eapply well_formed_allocation_reindexer_not_empty in Heq;
         try apply Halloc.       
       invs'. rewrite H7 in *.
       erewrite result_has_shape_result_shape_Z in *; try eassumption.
       invs'. rewrite H in *. invs'.
       cases (Z.to_nat (hiz0 - (loz0 + 1))).
       { invert H5.
         simpl in *. rewrite Hlo', Hhi' in *. invs'. lia.

         eq_size_of.
         simpl in *. rewrite Hlo', Hhi' in *. invs'.
         
         pose proof H6 as Hh.
         eapply add_result_gen_pad_r in Hh; eauto. subst.

         eapply IHeval_expr2 with (asn:=Reduce) in H17.
         2: { econstructor; eauto. econstructor; eauto.
              apply eval_Zexpr_Z_eval_Zexpr. eassumption.
              apply eval_Zexpr_Z_eval_Zexpr. eassumption. }
         2: { eapply well_formed_environment_add_heap. eauto. eauto. }
         2: { pose proof Hrdx.
              decomp_well_formed_reindexer.
              propositional.
              unfold partial_injective. intros.
              erewrite filter_negb_is_None_result_lookup_Z_option_gen_pad
                in *. invert0 H12.
              unfold nondestructivity. split; intros; discriminate. }
         2: { eapply well_formed_allocation_add_heap.
              eapply well_formed_allocation_gen_pad. eauto.
              eapply result_has_shape_filter_until_0.
              erewrite <- result_has_shape_filter_until_0.
              eauto. eauto. }
         2: { unfold well_formed_environment in *.
              eapply contexts_agree_add_heap. eauto. eauto.
              propositional. propositional. }
         2: { eapply HasPadSumEmpty. eauto.
              cbv [eval_Zexpr_Z_total]. simpl. rewrite Hhi, Hlo. lia.
              reflexivity. }
         rewrite H in *.
         rewrite lookup_add_eq in * by auto.
         invs'. propositional.
         rewrite add_overwrite.
         rewrite tensor_to_array_delta_gen_pad.
         rewrite array_add_empty_r.
         f_equal. f_equal. f_equal.
         eapply partial_interpret_reindexer_add_valuation; eauto.
         eauto.
       }

       eapply IHeval_expr2 with (asn:=Reduce) in H17; clear IHeval_expr2;
         try apply Hrdx; try apply Henv; eauto.
       rewrite lookup_add_eq in H17 by auto.
       rewrite H in *. invs'.
       rewrite add_overwrite.
       rewrite <- array_add_assoc. split. 2: auto. f_equal. f_equal.
       2: { econstructor; eauto. econstructor; eauto.
            apply eval_Zexpr_Z_eval_Zexpr. eassumption.
            apply eval_Zexpr_Z_eval_Zexpr. eassumption. }
       2: { eapply well_formed_environment_add_heap; eauto. }
       2 :{ decomp_well_formed_reindexer. propositional.
            eapply partial_injective_add_result_r; try apply H6; eauto.
            unfold nondestructivity. split; intros; discriminate. }
       2: { eapply well_formed_allocation_add_heap; eauto.
            eapply well_formed_allocation_add_result_r; eauto. }
       2: { eapply contexts_agree_add_heap; eauto.
            apply Henv. apply Henv. }
       
       replace (map Z.of_nat (filter_until ls 0))
         with (result_shape_Z r) at 1.
       2: { erewrite result_has_shape_result_shape_Z; eauto. }
       erewrite tensor_to_array_delta_add_valuation; eauto;
         try apply Hrdx.
       2: { eapply partial_injective_add_result_l; try apply H6; eauto.
            eapply partial_injective_add_valuation; try apply Hrdx; eauto. }
       
       replace (map Z.of_nat (filter_until ls 0))
         with (result_shape_Z r') at 1.
       2: { erewrite result_has_shape_result_shape_Z; eauto. }
       replace (map Z.of_nat (filter_until ls 0))
         with (result_shape_Z s) at 1.
       2: { erewrite result_has_shape_result_shape_Z; eauto. }

       eapply tensor_to_array_delta_add_result. auto.
       eapply result_has_shape_self; eassumption.
       erewrite result_has_shape_result_shape_nat by eassumption.
       erewrite <- result_has_shape_filter_until_0. eauto.
       erewrite result_has_shape_result_shape_nat by eassumption.
       erewrite <- result_has_shape_filter_until_0. eauto.
       apply Hrdx. apply Hrdx. apply Hrdx. apply Hrdx. apply Hrdx.
       auto. apply Henv.
       apply HasPadSum.
       cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi.
       intros. apply H13. cbv [eval_Zexpr_Z_total]. rewrite Hlo, Hhi. lia.
       cbv [eval_Zexpr_Z_total]. simpl. rewrite Hlo, Hhi. lia.
     + eassumption.
     + eapply well_formed_environment_add_valuation; eauto.
     + eapply well_formed_reindexer_add_valuation; eauto.
       decomp_well_formed_reindexer.
       propositional.
       eapply partial_injective_add_result_l; try apply H6; eauto.
       unfold nondestructivity. propositional; try discriminate.
       apply Henv.
       eapply result_has_shape_self; eauto.
     + eapply well_formed_allocation_add_valuation;
         eauto; try apply Hrdx.
       eapply well_formed_allocation_add_result_l; eauto.
     + eauto.
     + apply H13.
       cbv [eval_Zexpr_Z_total] in *. rewrite Hhi, Hlo in *. lia.
     + eauto.
     + erewrite H13 in *. erewrite H14 in *. invs'. lia.
   - (* EMPTY SUM *)
     simpl in Heval. invert Heval.
     rewrite H, H0 in *. invs'. lia.
     unfold lookup_total in *.
     invert Hsize. rename H10 into Hsize. eq_size_of.
     rename H8 into Hlo. rename H9 into Hhi.
     pose proof Hlo as Hlo'. pose proof Hhi as Hhi'.
     eapply eval_Zexpr_includes_valuation in Hlo', Hhi'; try apply empty_includes.
     apply eval_Zexpr_Z_eval_Zexpr in Hlo', Hhi'. rewrite Hlo', Hhi' in *. invs'.
     apply eval_Zexpr_Z_eval_Zexpr in Hlo, Hhi.

     destruct (reindexer
              (shape_to_index
                 (result_shape_Z (gen_pad _))
                 (shape_to_vars (result_shape_Z (gen_pad _))))) eqn:Heq.
     { unfold well_formed_allocation in *. rewrite Heq in *. invs'.
       rewrite H. split. auto.
       cases ls; simpl; rewrite add_id; try rewrite Rplus_0_r; auto. }
     eapply well_formed_allocation_reindexer_not_empty in Heq;
       try apply Halloc. invs'.
     rewrite H0 in *.
     rewrite tensor_to_array_delta_gen_pad.
     rewrite array_add_empty_r.
     split; auto.
     rewrite add_id; auto.
   - (* FALSE IVERSON *)
     simpl in Heval. invert Heval; eq_eval_B; try lia.
     unfold lookup_total.
     cases (reindexer
              (shape_to_index
                 (result_shape_Z (gen_pad sz))
                 (shape_to_vars
                    (result_shape_Z (gen_pad sz))))).
     { unfold well_formed_allocation in *. rewrite Heq in *. invs'.
       rewrite H2. split. auto.
       cases sz; simpl; rewrite add_id; try rewrite Rplus_0_r; auto. }
     eapply well_formed_allocation_reindexer_not_empty in Heq;
       try apply Halloc. invs'.
     rewrite H3. rewrite tensor_to_array_delta_gen_pad.
     rewrite array_add_empty_r. rewrite add_id. propositional. auto.
    - (* TRUE IVERSON *)
      cases (reindexer
               (shape_to_index (result_shape_Z r)
                               (shape_to_vars (result_shape_Z r)))).
     + unfold well_formed_allocation in *.
       rewrite Heq in *. invs. 
       simpl in Heval. invert Heval; eq_eval_B; try lia.
       invert Hpad. eq_eval_B. discriminate. 
       eapply IHeval_expr in H7; eauto.
       rewrite Heq in *. auto.
       rewrite Heq. eauto.
     + simpl in Heval. invert Heval; eq_eval_B; try lia.
       invert Hpad. eq_eval_B. discriminate. 
       eapply IHeval_expr in H5; eauto.
       rewrite Heq in H5. auto.
       invs. eauto.
   - (* SCALAR LET *)     
     simpl in *.     
     erewrite size_of_sizeof in Heval by eassumption. simpl in Heval.
     invert Heval. invert H12. invert H14. invert H15. invert H9.
     invert Hpad.
     eapply IHeval_expr1 in H10; try eassumption.
     2: { eapply well_formed_environment_alloc_stack; eauto. sets.
          sets. }
     2: { decomp_well_formed_reindexer. propositional.
          simpl. unfold partial_injective.
          { destruct r1.
          - simpl. intros. propositional. subst. propositional.
          - simpl. propositional. }
          simpl. sets.
          simpl. sets.
          unfold nondestructivity. simpl.
          rewrite lookup_add_eq by eauto. rewrite dom_add.
          split; intros. sets. invs'. sets. }
     2: { apply well_formed_allocation_scalar_id. } 
     2: { eapply contexts_agree_alloc_stack; eauto. }
     simpl in H10. rewrite lookup_add_eq in * by auto.
     rewrite add_overwrite in H10. invert H10.
     clear IHeval_expr1.
     eapply IHeval_expr2 in H11.
     2: eauto.
     2: { invert Hsize. eauto. }
     2: { rewrite Rplus_0_l.
          eapply well_formed_environment_let_bind1_scalar.
          eauto. sets. sets. sets. }
     2: { decomp_well_formed_reindexer. propositional.
          unfold nondestructivity in *. rewrite dom_add.
          invert Henv. rewrite lookup_add_ne.
          2: { sets. }
          split; intros.
          eapply Hnondstr. eauto. eauto. sets.
          eauto. eapply Hnondstr. eauto. eauto. sets. }
     2: { eapply well_formed_allocation_add_stack. auto.
          unfold well_formed_environment in *. sets. }
     2: { rewrite Rplus_0_l.
          eapply contexts_agree_let_bind1_scalar. auto. }
     2: { eq_size_of. eassumption. }
     2: { intros. cases (x0 ==v x).
          - subst. rewrite lookup_add_eq in * by auto. invs'.
            simpl. eq_size_of.
            eapply has_pad_gen_pad in H13.
            2: { eauto. }
            2: { econstructor. }
            eauto. eauto. eauto.
            eapply contexts_agree_result_has_shape. eauto.
            eauto.
          - rewrite lookup_add_ne in * by eauto. eauto. }
            
     pose proof Halloc as Halloc1.
     unfold well_formed_allocation in Halloc1.
     cases (reindexer
              (shape_to_index (result_shape_Z l2)
                              (shape_to_vars (result_shape_Z l2)))).
     + rewrite lookup_add_ne in *.
       2: { decomp_well_formed_environment. sets. }
       invs'. propositional.
       rewrite H1 in *.
       eq_size_of.
       rewrite Rplus_0_l.
       rewrite add_comm.
       2: { decomp_well_formed_environment. sets. }
       erewrite <- add_remove_id. reflexivity.
       rewrite dom_add.
       decomp_well_formed_environment.       
       rewrite cap_distr in Hsthec.
       eapply cup_empty in Hsthec. invs'.
       rewrite cap_distr in H7. 
       eapply cup_empty in H7. invs'.
       eapply constant_cap_empty in H9.
       sets. 
     + invs'. unfold lookup_total.
       rewrite H7. split. auto.
       erewrite <- add_remove_id. reflexivity.
       decomp_well_formed_environment.
       rewrite cap_distr in Hsthec.
       eapply cup_empty in Hsthec. invs'.
       rewrite cap_distr in H1.
       eapply cup_empty in H1. invs'.
       eapply constant_cap_empty in H10.
       sets.
   - (* VECTOR LET *)
     simpl in *.
     cases sz1; simpl in *; try now propositional.
     erewrite size_of_sizeof in Heval by eassumption. simpl in Heval.
     invs'.
     assert (result_has_shape (V l1) (n::sz1)) as Hsh1.
     { eapply size_of_eval_expr_result_has_shape; eauto. }
     invs.
     assert (result_has_shape l2 ls) as Hsh2.
     { eapply size_of_eval_expr_result_has_shape; eauto. }
     invert Hpad. eq_size_of.
     eapply IHeval_expr1 in H15; clear IHeval_expr1.
     2: eassumption.
     2: { eapply well_formed_environment_letbind1; eauto. }
     2: { decomp_well_formed_reindexer. propositional.
          eapply partial_injective_id_reindexer. apply Henv.
          simpl. sets. simpl. sets.
          unfold nondestructivity. unfold alloc_array_in_heap.
          rewrite lookup_add_eq by auto. rewrite dom_add.
          split; intros.
          2: sets. invs'. rewrite add_0_r.
          eapply dom_lookup_Some in H10. invert H10.
          unfold flat_sizeof in *.
          erewrite size_of_sizeof in * by eauto.
          simpl in *.
          pose proof (lookup_alloc_array (fold_left mul sz1 n) x1) as H10.
          destruct H10.
          2: eassumption.
          eapply lookup_None_dom in H10.
          rewrite dom_alloc_array in H10.
          exfalso. apply H10.
          erewrite <- In_iff_in.
          eapply In_zrange. clear H10.
          unfold tensor_to_array_delta in *.          
          eapply lookup_Some_dom in H0.
          unfold tensor_to_array_delta_by_indices in H0.
          erewrite partial_dom_fold_left_array_add in H0.
          rewrite dom_empty in *. rewrite cup_empty_r in *.
          rewrite filter_idempotent in H0.
          eapply In_iff_in in H0.
          eapply in_extract_Some in H0. eapply in_map_iff in H0. invert H0.
          invert H10. decomp_index.
          rewrite partial_interpret_reindexer_id_flatten in H0; eauto.
          invert H0.
          eapply In_zrange. eassert (zrange _ _ = _) as ->; cycle 1.
          eapply in_mesh_grid_flatten_in_range.
          eapply Forall_map. eapply Forall_forall. intros. lia.
          eauto.
          f_equal. erewrite result_has_shape_result_shape_Z by eauto.
          replace 1%Z with (Z.of_nat 1%nat) by reflexivity.
          rewrite <- Z_of_nat_fold_left_mul. f_equal.
          rewrite fold_left_mul_filter_until. simpl. f_equal. lia.
          apply Henv.

          eapply partial_injective_id_reindexer; eauto. apply Henv. }
     2: { eassert (flat_sizeof _ = _) as ->.
          2: { eapply well_formed_allocation_letbind1; eauto.
               apply Henv.
               eapply well_formed_environment_not_in_stack_heap. apply Henv. sets. }
          unfold flat_sizeof in *.
          erewrite size_of_sizeof in * by eassumption.
          simpl in *. cbv [result_shape_Z].
          replace 1%Z with (Z.of_nat 1) by reflexivity.
          rewrite <- Z_of_nat_fold_left_mul.
          rewrite Nat2Z.id. erewrite result_has_shape_result_shape_nat by eassumption.
          rewrite fold_left_mul_filter_until.
          simpl. f_equal. lia. }
     3: { eassumption. }
     3: { eauto. }
     cases (shape_to_index (result_shape_Z (V l1))
                           (shape_to_vars (result_shape_Z (V l1)))).
     { eapply shape_to_index_not_empty_Z in Heq. propositional. }
     invs'.
     pose proof H11 as Hsize. pose proof Hsize as Hsize'.
     eapply IHeval_expr2 in Hsize'.
     2: { eauto. }
     2: { unfold alloc_array_in_heap. rewrite add_overwrite.
          eapply well_formed_environment_alloc_heap; try apply Henv; eauto.
          sets. }
     2: { unfold alloc_array_in_heap.
          rewrite add_overwrite.
          unfold lookup_total. rewrite lookup_add_eq by auto.
          decomp_well_formed_reindexer. propositional.
          eapply WellFormedReindexer.nondestructivity_add_heap. eauto. 
          eauto. }
     2: { unfold alloc_array_in_heap.
          rewrite add_overwrite.
          cases (p ==v x). subst. 
          unfold well_formed_environment in *. invs'.
          sets.
          eapply well_formed_allocation_add_heap_var; eauto. }
     2: { unfold alloc_array_in_heap.
          rewrite add_overwrite.
          rewrite lookup_total_add_eq. simpl.
          rewrite add_0_r.
          unfold result_shape_Z.
          erewrite result_has_shape_result_shape_nat by eassumption.
          
          erewrite tensor_to_array_delta_id_valuation.
          2: { apply Henv. }
          eapply contexts_agree_add_alloc_heap; eauto.
          cbv [flat_sizeof].
          erewrite size_of_sizeof in * by eassumption.
          cbn -[filter_until].
          replace 1%Z with (Z.of_nat 1) by reflexivity.
          rewrite <- Z_of_nat_fold_left_mul. rewrite Nat2Z.id.
          rewrite fold_left_mul_filter_until.
          simpl. f_equal. lia. }
     2: { eauto. }
     2: { intros. cases (x==v x1).
          - subst. rewrite lookup_add_eq in * by auto. invs'.
            eapply has_pad_gen_pad. eauto. eauto.
            eapply size_of_eval_expr_result_has_shape
              in H1; eauto.
            eapply result_has_shape_self; eauto.
            eauto.
            eapply contexts_agree_result_has_shape. eauto.
            eauto.
          - rewrite lookup_add_ne in * by auto. eauto. }
     2: { eapply contexts_agree_alloc_array_in_heap; eauto. }
     cases (reindexer
              (shape_to_index (result_shape_Z l2)
                              (shape_to_vars (result_shape_Z l2)))).
     + unfold well_formed_allocation in *. rewrite Heq0 in *.
       invs'. rewrite H0.
       rewrite add_remove.
       unfold alloc_array_in_heap.
       rewrite add_remove.
       split. 2: auto.
       decomp_well_formed_environment.
       eapply remove_id.
       rewrite cap_distr in Hsthec. eapply cup_empty in Hsthec. invs'.
       rewrite cap_distr in H3. eapply cup_empty in H3. invs'.
       eapply constant_cap_empty in H10. sets.
     + unfold well_formed_allocation in *. rewrite Heq0 in *.
       invs'. unfold lookup_total. rewrite H3.
       unfold alloc_array_in_heap.
       repeat rewrite add_overwrite.
       rewrite lookup_add_eq by auto.
       rewrite lookup_add_ne.
       rewrite H3.              
       rewrite add_remove_comm.
       2: { intros. pose proof var_eq as Hor. specialize (Hor k k').
            destruct Hor; auto. }
       2: { unfold well_formed_environment in *. invs'.
            sets. }
       2: { unfold well_formed_environment in *. invs'.
            sets. }
     rewrite <- add_remove_id.
     2: { eapply well_formed_environment_not_in_stack_heap.
          eapply Henv. sets. }
     auto.
   - (* CONCAT *)
     pose proof Halloc as Halloc1.
     eapply well_formed_allocation_result_V in Halloc1.
     invert Halloc1. invert H1.
     simpl in *.
     cases (reindexer
      (shape_to_index (result_shape_Z (V (l1 ++ l2)))
                      (shape_to_vars (result_shape_Z (V (l1 ++ l2)))))).
     { eapply reindexer_not_empty in Heq. propositional.
       apply Hrdx. unfold result_shape_Z. simpl.
       cases l1; cases l2; simpl; inversion 1. }
     unfold lookup_total in *.
     invert Hsize. pose proof H5 as Hsize1. pose proof H6 as Hsize2.
     clear H6. clear H5.
     assert (result_has_shape (V l1) (n::sh0)) as Hsh1.
     { eapply size_of_eval_expr_result_has_shape; eauto. }
     assert (result_has_shape (V l2) (m::sh0)) as Hsh2.
     { eapply size_of_eval_expr_result_has_shape; eauto. }
     pose proof (result_has_shape_length _ _ _ Hsh1).
     pose proof (result_has_shape_length _ _ _ Hsh2). subst.
     pose proof (result_has_shape_concat _ _ _ _ _ Hsh1 Hsh2).
     erewrite size_of_sizeof in * by eassumption.

     invert Heval. invert Hpad. eq_size_of. invert H4. invert H5.
     eapply IHeval_expr1 in H8; auto; clear IHeval_expr1.
     2: { eauto. }
     2: { eapply well_formed_environment_subseteq_vars. eassumption. sets. }
     2: { eapply well_formed_allocation_result_V in Halloc.
          eapply well_formed_reindexer_concat_l;
            try apply Hrdx.
          rewrite H2 in *. eauto. rewrite H2 in *. eauto.
          apply Henv. eauto.
          apply Hrdx. }
     2: { eapply well_formed_allocation_concat_l; eauto;
          try eapply Henv; try eapply Hrdx. }
     cases (shape_to_index (result_shape_Z (V l1))
                           (shape_to_vars (result_shape_Z (V l1)))).
     { eapply shape_to_index_not_empty_Z in Heq0. propositional. }
     destruct (reindexer (let (v, d) := p1 in _)) eqn:Heq1.
     { unfold result_shape_Z, shape_to_index, shape_to_vars in Heq0.
       simpl in Heq0.
       cases l1; invert Heq0.
       - eapply reindexer_not_empty_vars_in_index in Heq1. propositional.
         apply Hrdx. simpl.
         unfold not. intros. cups_empty.
       - eapply reindexer_not_empty_vars_in_index in Heq1. propositional.
         apply Hrdx. simpl.
         unfold not. intros. cups_empty. }
     invs'. rewrite H2 in *.
     eapply IHeval_expr2 in H11; clear IHeval_expr2.
     cases (shape_to_index (result_shape_Z (V l2))
                           (shape_to_vars (result_shape_Z (V l2)))). 
     { eapply shape_to_index_not_empty_Z in Heq2. propositional. } 
     destruct (reindexer (let (v, d) := p3 in _)) eqn:Heq3.
     { unfold result_shape_Z, shape_to_index, shape_to_vars in Heq2.
       cases l2; invert Heq2.
       - eapply reindexer_not_empty_vars_in_index in Heq3. propositional.
         apply Hrdx. simpl.
         unfold not. intros. cups_empty.
       - eapply reindexer_not_empty_vars_in_index in Heq3. propositional.
         apply Hrdx. simpl.
         unfold not. intros. cups_empty. }
     
     rewrite lookup_add_eq in * by auto. invs'.
     rewrite add_overwrite. split; auto.
     rewrite <- array_add_assoc. f_equal. f_equal.
     symmetry.
     unfold tensor_to_array_delta at 1.

     erewrite array_add_tensor_to_array_delta_concat; auto.
     unfold tensor_to_array_delta.
     2: { eapply cap_empty_exclusion. intros.
          repeat erewrite <- In_iff_in.
          repeat rewrite <- in_extract_Some.
          repeat rewrite in_map_iff.
          propositional.
          - invs'.
            repeat erewrite result_has_shape_result_shape_Z in * by eauto.
            repeat decomp_index.
            rewrite <- H5 in H4.
            clear Heq. clear Heq0. clear Heq2. clear H3.
            decomp_well_formed_reindexer.
            erewrite result_has_shape_result_shape_Z in Hinj by eauto.
            About eq_partial_interpret_reindexer_padl.
            erewrite eq_partial_interpret_reindexer_padl in H5,H4;
              try assumption; try apply Henv; try lia.
            2: { erewrite size_of_sizeof by eauto. simpl. lia. }
            2: { erewrite size_of_sizeof by eauto. simpl. lia. }
            erewrite size_of_sizeof in * by eauto.
            simpl eval_Zexpr_Z_total in H5,H4.
            erewrite eq_partial_interpret_reindexer_concat_l in H4;
              try assumption; try apply Henv; try lia.
            3: apply Hsh1.
            3: apply Hsh2.
            2: { erewrite result_has_shape_result_shape_Z by eauto.
                 eapply filter_In. propositional.
                 repeat decomp_goal_index.
                 propositional. }
            cbv match in *.
            rewrite Nat2Z.id in *.
            pose proof H4 as H4'.
            eapply Hinj in H4.
            invert H4.
            + invs'. lia.
            + rewrite H4' in H3. rewrite H3 in *.
              discriminate.
            + eapply filter_In. propositional.
              repeat decomp_goal_index.
              propositional. lia. 
              rewrite <- H15.
              simpl.
              rewrite nth_error_app1.
              auto.
              erewrite result_has_shape_length by eauto.
              lia.
            + eapply filter_In. propositional.
              repeat decomp_goal_index.
              propositional. lia. lia.
              rewrite <- H15.
              simpl.
              rewrite nth_error_app2 by lia.
              rewrite Z2Nat.inj_add by lia.
              rewrite Nat2Z.id.
              erewrite result_has_shape_length by eauto.
              rewrite add_sub.
              cases z; try lia.
              simpl Z.add.
              cases (Z.of_nat (length l1)); try lia.
              eauto.
              cases (Z.pos p0 + Z.of_nat (length l1))%Z; try lia.
              eauto.
          - invs'.
            repeat erewrite result_has_shape_result_shape_Z in * by eauto.
            repeat decomp_index.
            rewrite <- H5 in H4.
            clear Heq. clear Heq0. clear Heq2. clear H3.
            decomp_well_formed_reindexer.
            erewrite result_has_shape_result_shape_Z in Hinj by eauto.
            erewrite eq_partial_interpret_reindexer_padl in H4;
              try assumption; try apply Henv; try lia.
            2: { erewrite size_of_sizeof by eauto. simpl. lia. }
            erewrite size_of_sizeof in * by eauto.
            cbv match in *.
            erewrite eq_partial_interpret_reindexer_concat_l in H5,H4;
              try assumption; try apply Henv; try lia.
            3: apply Hsh1.
            3: apply Hsh2.
            4: apply Hsh1.
            4: apply Hsh2.
            2: { erewrite result_has_shape_result_shape_Z by eauto.
                 eapply filter_In. propositional.
                 repeat decomp_goal_index.
                 propositional. }
            2: { erewrite result_has_shape_result_shape_Z by eauto.
                 eapply filter_In. propositional.
                 repeat decomp_goal_index.
                 propositional. }
            rewrite Nat2Z.id in *.
            pose proof H4 as H4'.
            eapply Hinj in H4.
            invert H4.
            + invs'. lia.
            + rewrite H4' in H3. rewrite H3 in *.
              discriminate.
            + eapply filter_In. propositional.
              repeat decomp_goal_index.
              propositional. lia. lia.
              rewrite <- H11.
              simpl.
              rewrite nth_error_app2 by lia.
              rewrite Z2Nat.inj_add by lia.
              erewrite result_has_shape_length by eauto.
              rewrite Nat2Z.id. rewrite add_sub.
              cases z0; try lia.
              simpl Z.add.
              cases (Z.of_nat (length l1)); try lia.
              eauto.
              cases (Z.pos p0 + Z.of_nat (length l1))%Z; try lia.
              eauto.
            + eapply filter_In. propositional.
              repeat decomp_goal_index.
              propositional. lia. 
              rewrite <- H11.
              simpl.
              rewrite nth_error_app1 by lia.
              auto. }
     2: { eauto. }
     2: { eauto. }
     2: { decomp_well_formed_reindexer.
          unfold well_formed_reindexer. propositional.
          erewrite result_has_shape_result_shape_Z by eauto.
            eapply partial_injective_concat_l; eauto; try apply Henv. }
     2: { decomp_well_formed_reindexer.
          erewrite size_of_sizeof by eassumption. simpl.
          erewrite result_has_shape_result_shape_Z by eauto.
          eapply partial_injective_concat_r; eauto.          
          3: lia. 2: apply Henv. rewrite Nat2Z.id. assumption. }
     2: { eassumption. }
     2: { eapply well_formed_environment_add_heap.
          eapply well_formed_environment_subseteq_vars. eassumption.
          sets. auto. }
     2: { erewrite size_of_sizeof by eassumption. simpl.
          eapply well_formed_allocation_result_V in Halloc.
          invert Halloc. invs'.
          eapply well_formed_reindexer_concat_r;
            try apply Henv; eauto.
          rewrite Nat2Z.id. assumption.
          lia.
          apply Hrdx. }
     2: { eapply well_formed_allocation_add_heap.
          erewrite size_of_sizeof by eauto.
          eapply well_formed_allocation_concat_r; eauto;
            try apply Henv; try apply Hrdx.
          rewrite Nat2Z.id. eassumption.
          rewrite Nat2Z.id. eassumption.
          lia.
          eassumption. }
       2: { eapply contexts_agree_add_heap; eauto;
            try apply Henv. }
       eapply eq_tensor_to_array_delta_by_indices. intros.
     2: { eapply Hrdx. }
     2: { erewrite size_of_sizeof by eauto. simpl.
          decomp_well_formed_reindexer.
          repeat erewrite result_has_shape_result_shape_Z by eauto.
          replace (fun e : Zexpr =>
                          match eval_Zexpr_Z $0 e with
                          | Some x0 => x0
                          | None => 0%Z
                          end) with
            (eval_Zexpr_Z_total $0) in * by reflexivity.
          cases l1. invert Hsh1.
          { simpl length. simpl Z.of_nat.
            rewrite add_0_l. rewrite app_nil_l.
            unfold partial_injective.
            rewrite app_nil_l in Hinj.
            erewrite result_has_shape_result_shape_Z in Hinj by eauto.
            rewrite add_0_l in *. propositional.
            repeat decomp_index.
            cases (z0 <? 0)%Z. eapply Z.ltb_lt in Heq4. lia.
            cases (z <? 0)%Z. eapply Z.ltb_lt in Heq5. lia.
            rewrite Z.sub_0_r in *.

            erewrite eq_partial_interpret_reindexer_padl in H6;
              eauto; try apply Henv; try lia.
            erewrite eq_partial_interpret_reindexer_padl in H6;
              eauto; try apply Henv; try lia.

            rewrite add_0_l in *.
            rewrite Z.sub_0_r in *.
            rewrite Z.add_0_r in *.
            eapply Hinj in H6.
            destruct H6 as [H6|H6].
            - invert H6. left. f_equal. lia. 
            - erewrite eq_partial_interpret_reindexer_padl;
                eauto; try apply Henv.
              rewrite Z.add_0_r.
              simpl Z.to_nat. rewrite add_0_l.
              rewrite H6. propositional.
              lia. lia.
            - eapply filter_In. propositional.
              repeat decomp_goal_index. propositional.
            - rewrite Z.add_0_r.
              eapply filter_In. propositional.
              repeat decomp_goal_index. propositional. }
          cases l2. invert Hsh2.
          { rewrite add_0_r in *. rewrite app_nil_r.
            erewrite result_has_shape_length; eauto.
            unfold partial_injective.
            propositional.
            repeat decomp_index.
            cbn [length] in *.
            destruct (z0 <? Z.of_nat _)%Z eqn:Heq4.
            2: { eapply Z.ltb_ge in Heq4. lia. }
            destruct (z <? Z.of_nat _)%Z eqn:Heq5.
            2: { eapply Z.ltb_ge in Heq5. lia. }
            erewrite eq_partial_interpret_reindexer_concat_l in H6;
              auto; try apply Henv.
            3: apply Hsh1.
            3: { econstructor. }
            erewrite eq_partial_interpret_reindexer_concat_l in H6;
              auto; try apply Henv.
            3: apply Hsh1.
            3: { econstructor. }
            rewrite add_0_r in *.
            rewrite app_nil_r in *.
            erewrite result_has_shape_result_shape_Z in Hinj by eauto.
            simpl Z.to_nat in Hinj. eapply Hinj in H6.
            invert H6.
            propositional.
            erewrite eq_partial_interpret_reindexer_concat_l;
              auto; try apply Henv.
            3: apply Hsh1.
            3: { econstructor. }
            rewrite add_0_r.
            rewrite H7. propositional.
            erewrite result_has_shape_result_shape_Z by eauto.
            eapply filter_In. propositional.
            repeat decomp_goal_index. propositional.
            eapply filter_In. propositional.
            repeat decomp_goal_index. propositional.
            eapply filter_In. propositional.
            repeat decomp_goal_index. propositional.
            erewrite result_has_shape_result_shape_Z by eauto.
            eapply filter_In. propositional.
            repeat decomp_goal_index. propositional.
            erewrite result_has_shape_result_shape_Z by eauto.
            eapply filter_In. propositional.
            repeat decomp_goal_index. propositional. }
          invert Hsh1. invert Hsh2.
          simpl map. posnats.
          rewrite <- add_succ_l.
          rewrite Nat2Z.inj_add.
          rewrite mesh_grid_app.
          eapply partial_injective_concat.
          { repeat erewrite <- map_cons.
            simpl length in *.
            rewrite <- filter_until_cons by lia.
            repeat rewrite <- map_cons.
            eapply partial_injective_concat_r.
            eassumption.
            rewrite Nat2Z.id.
            econstructor; eauto.
            simpl.
            econstructor; eauto.
            apply Henv.
            auto. auto. auto. lia. auto. }
          { repeat erewrite <- map_cons.
            simpl length in *.
            rewrite <- filter_until_cons by lia.
            repeat rewrite <- map_cons.
            eapply partial_injective_concat_l.
            eassumption.
            simpl.
            econstructor; eauto.
            simpl.
            econstructor; eauto.
            apply Henv.
            auto. auto. auto. }
          { apply cap_empty_exclusion. propositional.
            - rewrite <- @In_iff_in in *.
              rewrite <- @in_extract_Some in *.
              rewrite in_map_iff in *. invs'.
              repeat decomp_index. simpl map in *.
              repeat decomp_index.
              pose proof H4 as H4'.
              rewrite <- H5 in H4'.
              rewrite <- map_cons in H4',H5.
              rewrite <- filter_until_cons in H4',H5 by lia.
              erewrite eq_partial_interpret_reindexer_concat_l in H4'.
              3: { econstructor. reflexivity. eapply H11. eauto. }
              3: { apply VectorConsShape. reflexivity.
                   eauto. eauto. }

              2: { eapply filter_In. propositional.
                   erewrite result_has_shape_result_shape_Z.
                   2: { econstructor. reflexivity. eauto. eauto. }
                   repeat decomp_goal_index.
                   propositional. }
              2: { apply Henv. }
              2: { auto. }
              2: { auto. }
              2: { auto. }
              rewrite <- map_cons in H4'.
              rewrite <- filter_until_cons in H4' by lia.
              erewrite eq_partial_interpret_reindexer_padl in H4',H5; eauto; try lia.
              2: { apply Henv. }
              2: { apply Henv. }
              erewrite result_has_shape_result_shape_Z in Hinj.
              2: { eapply result_has_shape_concat.
                   econstructor; eauto.
                   econstructor; eauto. }
              rewrite Nat2Z.id in *. cbn [length] in *.
              pose proof H4' as H4''.
              eapply Hinj in H4'.
              invert H4'. invs'. lia.
              rewrite H6 in H4''.
              rewrite <- H4'' in H5.
              discriminate.
              eapply filter_In. propositional.
              repeat decomp_goal_index.
              propositional. lia.
              rewrite <- H21.
              simpl.
              rewrite app_comm_cons.
              rewrite nth_error_app1. auto.
              erewrite result_has_shape_length.
              2: { econstructor. reflexivity. eauto. eauto. }
              lia.
              eapply filter_In. propositional.
              repeat decomp_goal_index.
              propositional. lia. lia.
              rewrite <- H21.
              cbn [result_lookup_Z_option].
              rewrite nth_error_app2.
              erewrite (result_has_shape_length (_ :: _)).
              2: { econstructor. reflexivity. eauto. eauto. }
              rewrite Z2Nat.inj_add by lia.
              rewrite Nat2Z.id. rewrite add_sub.
              cases z0; try lia.
              simpl Z.add at 1.
              cbv match. eauto.
              destruct ((Z.pos p5 + Z.of_nat _)%Z) eqn:?; try lia.
              eauto. simpl. lia.
            - rewrite <- @In_iff_in in *.
              rewrite <- @in_extract_Some in *.
              rewrite in_map_iff in *. invs'.
              repeat decomp_index. simpl map in *.
              repeat decomp_index.
              pose proof H4 as H4'.
              rewrite <- H5 in H4'.
              rewrite <- map_cons in H4',H5.
              rewrite <- filter_until_cons in H4',H5 by lia.
              erewrite eq_partial_interpret_reindexer_padl in H4'; eauto;
                try apply Henv; try lia.
              rewrite Nat2Z.id in *.
              rewrite <- map_cons in H4'.
              rewrite <- filter_until_cons in H4' by lia.
              erewrite eq_partial_interpret_reindexer_concat_l in H4',H5;
                try apply Henv.
              3: { econstructor. reflexivity. apply H11. auto. }
              9: { econstructor. reflexivity. apply H11. auto. }
              3: { econstructor. reflexivity. apply H11. auto. }
              7: { econstructor. reflexivity. apply H11. auto. }
              2: { eapply filter_In. propositional.
                   erewrite result_has_shape_result_shape_Z by
                     (econstructor; eauto).
                   repeat decomp_goal_index.
                   propositional. }
              2: { auto. }
              2: { auto. }
              2: { auto. }
              2: { eapply filter_In. propositional.
                   erewrite result_has_shape_result_shape_Z by
                     (econstructor; eauto).
                   repeat decomp_goal_index.
                   propositional. }
              2: { auto. }
              2: { auto. }
              2: { auto. }
              erewrite result_has_shape_result_shape_Z in Hinj.
              2: { eapply result_has_shape_concat.
                   econstructor; eauto.
                   econstructor; eauto. }
              pose proof H4' as H4''.
              eapply Hinj in H4'.
              invert H4'. invs'. lia.
              cbn [length] in *.
              rewrite H6 in H4''.
              rewrite <- H4'' in H5.
              discriminate.
              eapply filter_In. propositional.
              repeat decomp_goal_index.
              propositional. lia. simpl. lia.
              rewrite <- H21.
              cbn [length result_lookup_Z_option].
              rewrite nth_error_app2.
              erewrite (result_has_shape_length (_ :: _)).
              2: { econstructor. reflexivity. eauto. eauto. }
              rewrite Z2Nat.inj_add by lia.
              rewrite Nat2Z.id. rewrite add_sub.
              cases z0; try lia.
              simpl Z.add at 1. posnats.
              destruct (Z.of_nat _) eqn:?; try lia.
              eauto. 
              destruct ((Z.pos p5 + Z.of_nat _)%Z) eqn:?; try lia.
              eauto. simpl. lia.
              eapply filter_In. propositional.
              repeat decomp_goal_index.
              propositional. lia. 
              rewrite <- H22.
              simpl.
              rewrite app_comm_cons.
              rewrite nth_error_app1. auto.
              erewrite result_has_shape_length.
              2: { econstructor. reflexivity. eauto. eauto. }
              lia. }
          econstructor; eauto.
          econstructor; eauto.
          lia. lia.
     }
     2: { eapply no_dup_filter.
          eapply no_dup_mesh_grid. }
     erewrite result_has_shape_result_shape_Z in H4 by eauto.
     repeat decomp_index.
     erewrite size_of_sizeof by eauto. simpl.
     assert (z < Z.of_nat (length l1) \/ Z.of_nat (length l1) <= z)%Z
       as Hcase by lia.
     inversion Hcase as [ Hcase1 | Hcase2 ]; clear Hcase.
     { pose proof Hcase1 as Hcase1'.
       eapply Z.ltb_lt in Hcase1'. rewrite Hcase1'. clear Hcase1'.
       symmetry.
       repeat erewrite result_has_shape_result_shape_Z by eauto.
       erewrite eq_partial_interpret_reindexer_concat_l.
       3: { apply Hsh1. }
       3: { apply Hsh2. }
       reflexivity.
       erewrite result_has_shape_result_shape_Z by eauto.
       eapply filter_In. propositional.
       repeat decomp_goal_index.
       propositional.
       rewrite <- H6.
       simpl.
       rewrite nth_error_app1. auto. lia.
       apply Henv. apply Hrdx. apply Hrdx. apply Hrdx. }
     pose proof Hcase2 as Hcase2'.
     eapply Z.ltb_ge in Hcase2'.
     rewrite Hcase2'. clear Hcase2'.
     repeat erewrite result_has_shape_result_shape_Z by eauto.
     erewrite eq_partial_interpret_reindexer_padl.
     f_equal. f_equal. f_equal. f_equal. lia.
     f_equal. lia.
     apply Henv. apply Hrdx. apply Hrdx. apply Hrdx. apply Hrdx. lia. lia.
     eauto. eauto.
     eauto. eauto.
     apply Hrdx.
   - (* TRANSPOSE *)
     simpl in *.
     pose proof Halloc as Halloc1.
     eapply well_formed_allocation_result_V in Halloc1.
     inversion Halloc1 as [ a Htmp  ]. clear Halloc1.
     inversion Htmp as [ Heq Hsub ]. clear Htmp.
     assert (result_has_shape (V l) (n::m::esh)) as Hsh.
     { eapply size_of_eval_expr_result_has_shape; eauto. }
     invert Hsize. eq_size_of. invs'. pose proof H0 as Hsize. clear H0.
     
     invert Hpad.
     { 
     eapply IHeval_expr in Heval; eauto. invs'. clear IHeval_expr.
     cases (shape_to_index (result_shape_Z (V l))
                           (shape_to_vars (result_shape_Z (V l)))).
     { eapply shape_to_index_not_empty_Z in Heq0. propositional. }
     cases (reindexer
      (shape_to_index
         (result_shape_Z
            (transpose_result l
               (m0 :: n0 :: sh0)))
         (shape_to_vars
            (result_shape_Z
               (transpose_result l
                  (m0 :: n0 :: sh0)))))).
     { eapply reindexer_not_empty in Heq1. propositional. apply Hrdx.
       erewrite result_has_shape_result_shape_Z.
       2: eapply result_has_shape_transpose_result; eauto.
       simpl.
       cases m0; simpl.
       inversion 1.
       cases n0.
       simpl. inversion 1. simpl. inversion 1. }
     destruct (reindexer (let (v, d) := p0 in _)) eqn:Heq2.
     { unfold result_shape_Z, shape_to_index, shape_to_vars in Heq0.
       cases l; invert Heq0.
       - eapply reindexer_not_empty_vars_in_index in Heq2.
         propositional. apply Hrdx. simpl. destruct l4; simpl; intros ?; cups_empty.
       - eapply reindexer_not_empty_vars_in_index in Heq2.
         propositional. apply Hrdx.
         simpl. repeat rewrite cup_empty_r.
         cases (result_shape_nat r0); simpl; intros ?; cups_empty. }
     invs'.
     split; auto.
     f_equal. f_equal.
     { unfold tensor_to_array_delta.
       eapply eq_tensor_to_array_delta_by_indices_shuffle
         with (shuffle:=(fun l => match l with
                                 | x::y::xs => y::x::xs
                                 | _ => l
                                  end)).
       - intros ? H0.
         erewrite result_has_shape_result_shape_Z in H0.
         2: { eapply result_has_shape_transpose_result.
              simpl in Hsh.
              eauto. }
         repeat decomp_index.
         erewrite result_lookup_Z_option_transpose.
         reflexivity. lia. lia. eauto.
       - intros ? H0.
         erewrite result_has_shape_result_shape_Z in H0.
         2: { eapply result_has_shape_transpose_result.
              simpl in Hsh.
              eauto. }
         erewrite result_has_shape_result_shape_Z by eauto.
         erewrite result_has_shape_result_shape_Z.
         2: { eapply result_has_shape_transpose_result.
              simpl in Hsh.
              eauto. }
         repeat decomp_index.
         rewrite eq_partial_interpret_reindexer_transpose;
           try apply Henv; try apply Hrdx; eauto.
       - intros ? H0.
         erewrite result_has_shape_result_shape_Z in H0.
         2: { eapply result_has_shape_transpose_result.
              simpl in Hsh.
              eauto. }
         repeat decomp_index.
         eapply filter_In. erewrite result_has_shape_result_shape_Z by eauto.
         propositional.
         repeat decomp_goal_index.
         propositional.
         repeat decomp_goal_index.
         propositional.
         rewrite <- H5.
         erewrite result_lookup_Z_option_transpose.
         reflexivity.
         lia. lia. eauto.
       - intros ? H0.
         erewrite result_has_shape_result_shape_Z in H0 by eauto.
         erewrite result_has_shape_result_shape_Z.
         2: { eapply result_has_shape_transpose_result.
              simpl in Hsh.
              eauto. }
         repeat decomp_index.
         eexists (z0::z::x0).
         split. auto.
         eapply filter_In. propositional.
         repeat decomp_goal_index. propositional. 
         repeat decomp_goal_index. propositional.
         rewrite <- H5.
         erewrite result_lookup_Z_option_transpose.
         reflexivity.
         lia. lia. eauto.
       - apply Hrdx.
       - decomp_well_formed_reindexer.
         eapply partial_injective_transpose; eauto.
         apply Henv.
       - erewrite result_has_shape_result_shape_Z.
         2: { eapply result_has_shape_transpose_result.
              simpl in Hsh.
              eauto. }
         unfold injective.
         propositional. repeat decomp_index.
         invs'. auto.
       - eapply no_dup_filter. eapply no_dup_mesh_grid.
       - eapply no_dup_filter. eapply no_dup_mesh_grid. }
     eapply well_formed_reindexer_transpose; try apply Henv; eauto.
     eapply well_formed_allocation_transpose;
       try apply Henv; try apply Hrdx; eauto.
     }
     { 
     eapply IHeval_expr in Heval; eauto. invs'. clear IHeval_expr.
     cases (shape_to_index (result_shape_Z (V l))
                           (shape_to_vars (result_shape_Z (V l)))).
     { eapply shape_to_index_not_empty_Z in Heq0. propositional. }
     cases (reindexer
      (shape_to_index
         (result_shape_Z
            (transpose_result l
               (m0 :: n0 :: sh0)))
         (shape_to_vars
            (result_shape_Z
               (transpose_result l
                  (m0 :: n0 :: sh0)))))).
     { eapply reindexer_not_empty in Heq1. propositional. apply Hrdx.
       erewrite result_has_shape_result_shape_Z.
       2: eapply result_has_shape_transpose_result; eauto.
       simpl.
       cases m0; simpl.
       inversion 1.
       cases n0.
       simpl. inversion 1. simpl. inversion 1. }
     destruct (reindexer (let (v, d) := p0 in _)) eqn:Heq2.
     { unfold result_shape_Z, shape_to_index, shape_to_vars in Heq0.
       cases l; invert Heq0.
       - eapply reindexer_not_empty_vars_in_index in Heq2.
         propositional. apply Hrdx.
         simpl. intros ?. cups_empty.
       - eapply reindexer_not_empty_vars_in_index in Heq2.
         propositional. apply Hrdx.
         simpl.
         cases (result_shape_nat r0); simpl; intros ?; cups_empty. }
     invs'.
     split; auto.
     f_equal. f_equal.
     { unfold tensor_to_array_delta.
       eapply eq_tensor_to_array_delta_by_indices_shuffle
         with (shuffle:=(fun l => match l with
                                 | x::y::xs => y::x::xs
                                 | _ => l
                                  end)).
       - intros ? H0.
         erewrite result_has_shape_result_shape_Z in H0.
         2: { eapply result_has_shape_transpose_result.
              simpl in Hsh.
              eauto. }
         repeat decomp_index.
         erewrite result_lookup_Z_option_transpose.
         reflexivity. lia. lia. eauto.
       - intros ? H0.
         erewrite result_has_shape_result_shape_Z in H0.
         2: { eapply result_has_shape_transpose_result.
              simpl in Hsh.
              eauto. }
         erewrite result_has_shape_result_shape_Z by eauto.
         erewrite result_has_shape_result_shape_Z.
         2: { eapply result_has_shape_transpose_result.
              simpl in Hsh.
              eauto. }
         repeat decomp_index.
         rewrite eq_partial_interpret_reindexer_transpose;
           try apply Henv; try apply Hrdx; eauto.
       - intros ? H0.
         erewrite result_has_shape_result_shape_Z in H0.
         2: { eapply result_has_shape_transpose_result.
              simpl in Hsh.
              eauto. }
         repeat decomp_index.
         eapply filter_In. erewrite result_has_shape_result_shape_Z by eauto.
         propositional.
         repeat decomp_goal_index.
         propositional.
         repeat decomp_goal_index.
         propositional.
         rewrite <- H4.
         erewrite result_lookup_Z_option_transpose.
         reflexivity.
         lia. lia. eauto.
       - intros ? H0.
         erewrite result_has_shape_result_shape_Z in H0 by eauto.
         erewrite result_has_shape_result_shape_Z.
         2: { eapply result_has_shape_transpose_result.
              simpl in Hsh.
              eauto. }
         repeat decomp_index.
         eexists (z0::z::x0).
         split. auto.
         eapply filter_In. propositional.
         repeat decomp_goal_index. propositional. 
         repeat decomp_goal_index. propositional.
         rewrite <- H4.
         erewrite result_lookup_Z_option_transpose.
         reflexivity.
         lia. lia. eauto.
       - apply Hrdx.
       - decomp_well_formed_reindexer.
         eapply partial_injective_transpose; eauto.
         apply Henv.
       - erewrite result_has_shape_result_shape_Z.
         2: { eapply result_has_shape_transpose_result.
              simpl in Hsh.
              eauto. }
         unfold injective.
         propositional. repeat decomp_index.
         invs'. auto.
       - eapply no_dup_filter. eapply no_dup_mesh_grid.
       - eapply no_dup_filter. eapply no_dup_mesh_grid. }
     eapply well_formed_reindexer_transpose; try apply Henv; eauto.
     eapply well_formed_allocation_transpose;
       try apply Henv; try apply Hrdx; eauto.
     }
     apply Hrdx.     
   - (* FLATTEN *)
     simpl in *. invert Hsize.
     assert (result_has_shape (V l) (n::m::sh0)).
     { eapply size_of_eval_expr_result_has_shape; eauto. }
     simpl map in *.
     cases (reindexer
      (shape_to_index (result_shape_Z (V (flatten_result l)))
                      (shape_to_vars
                         (result_shape_Z (V (flatten_result l)))))).
     { eapply reindexer_not_empty in Heq. propositional. apply Hrdx.
       erewrite result_has_shape_result_shape_Z.
       2: eapply result_has_shape_flatten; eassumption.
       simpl. cases (n * m =? 0)%nat.
       inversion 1. inversion 1. }
     clear Heq.
     pose proof Halloc as Halloc1.
     eapply well_formed_allocation_result_V in Halloc1.
     inversion Halloc1 as [a Htmp]. clear Halloc1.
     inversion Htmp as [ Heq Hsub ]. clear Htmp.
     unfold lookup_total. rewrite Heq.

     invert Hpad.
     
     eapply IHeval_expr in Heval; eauto.
     cases (shape_to_index (result_shape_Z (V l))
                           (shape_to_vars (result_shape_Z (V l)))).
     { eapply shape_to_index_not_empty_Z in Heq0. propositional. }
     destruct (reindexer (let (v, d) := p1 in _)) eqn:Heq1.
     { erewrite result_has_shape_result_shape_Z in Heq0 by eassumption.
       simpl in Heq0.
       cases (n =? 0)%nat; invert Heq0.
       - eapply reindexer_not_empty_vars_in_index in Heq1.
         propositional. apply Hrdx.
         simpl. intros ?. cups_empty.
       - eapply reindexer_not_empty_vars_in_index in Heq1.
         propositional. apply Hrdx.
         cases (m =? 0)%nat; simpl; intros ?; cups_empty. }
     invs'. split; auto.
     unfold lookup_total. rewrite Heq.
     f_equal. f_equal.
     unfold tensor_to_array_delta.
     erewrite result_has_shape_result_shape_Z by eauto.
     erewrite result_has_shape_result_shape_Z.
     2: { eapply result_has_shape_flatten; eauto. }
     { symmetry.
       eapply eq_tensor_to_array_delta_by_indices_shuffle
         with (shuffle:= fun l =>
                           match l with
                           | x::y::xs =>
                               (x*Z.of_nat m + y)%Z::xs
                           | _ => l
                           end).
       - intros. repeat decomp_index.
         erewrite result_lookup_Z_option_flatten. reflexivity.
         lia. apply H3. eauto. lia. lia. eauto.
       - intros. repeat decomp_index.
         eapply eq_partial_interpret_reindexer_flatten;
           try apply Henv; try apply Hrdx; eauto.
       - intros. repeat decomp_index.
         eapply filter_In. propositional.
         repeat decomp_goal_index. propositional.
         lia.
         rewrite Nat2Z.inj_mul.
         eapply mul_add_lt. lia. lia. lia. lia.
         rewrite <- H12.
         erewrite result_lookup_Z_option_flatten. reflexivity.
         lia. eauto. eauto. lia. eauto. eauto.
       - intros. repeat decomp_index.
         pose proof (Z_div_mod z (Z.of_nat m)).
         assert (Z.of_nat m > 0)%Z by lia.
         propositional.
         cases (Z.div_eucl z (Z.of_nat m)).
         invs'.
         eexists (z0::z1::x0).
         rewrite Z.mul_comm.
         split. auto.
         eapply filter_In. propositional.
         repeat decomp_goal_index. propositional.
         assert (-1 * Z.of_nat m < z0 * Z.of_nat m)%Z
           by lia.
         apply Zorder.Zmult_lt_reg_r in H17.
         lia. lia.
         rewrite Nat2Z.inj_mul in H16.
         rewrite
           (Z.mul_comm (Z.of_nat n)) in H16.
         eapply div_eucl_bound in H16.
         lia.
         assert (-1 * Z.of_nat m < z0 * Z.of_nat m)%Z
           by lia.
         eapply Zorder.Zmult_lt_reg_r in H17.
         lia. lia.
         lia.
         repeat decomp_goal_index. propositional.
         rewrite <- H12.
         erewrite <- result_lookup_Z_option_flatten.
         rewrite Z.mul_comm. reflexivity.
         assert (-1 * Z.of_nat m < z0 * Z.of_nat m)%Z
           by lia.
         eapply Zorder.Zmult_lt_reg_r in H17.
         lia. lia.
         rewrite Nat2Z.inj_mul in H16.
         rewrite (Z.mul_comm (Z.of_nat n)) in H16.
         eapply div_eucl_bound in H16.
         apply H16. 
         assert (-1 * Z.of_nat m < z0 * Z.of_nat m)%Z
           by lia.
         eapply Zorder.Zmult_lt_reg_r in H17.
         lia. lia.
         eauto. eauto.
         lia. lia.
         eauto.
       - decomp_well_formed_reindexer.
         erewrite result_has_shape_result_shape_Z in Hinj.
         2: { eapply result_has_shape_flatten; eauto. }
         eapply partial_injective_flatten; try apply Henv; eauto.
       - decomp_well_formed_reindexer.
         erewrite result_has_shape_result_shape_Z in Hinj.
         2: { eapply result_has_shape_flatten; eauto. }
         eauto.
       - unfold injective. propositional.
         repeat decomp_index. invs'.
         rewrite Z.mul_comm in H24. symmetry in H24.
         rewrite Z.mul_comm in H24. symmetry in H24.
         eapply Z.div_mod_unique in H24.
         invs'. auto.
         lia. lia.
       - eapply no_dup_filter.
         eapply no_dup_mesh_grid.
       - eapply no_dup_filter.
         eapply no_dup_mesh_grid. }
     eapply well_formed_reindexer_flatten; try apply Henv; eauto.
     eapply well_formed_allocation_flatten;
       try apply Henv; try apply Hrdx; eauto.
     apply Hrdx. 
   - (* TRUNCR *) simpl in *. invert Hsize.
     rename H5 into Hk. pose proof Hk as Hk'.
     eapply eval_Zexpr_includes_valuation in Hk'; try apply empty_includes.
     apply eval_Zexpr_Z_eval_Zexpr in Hk'.
     rewrite Hk' in *. invs'. apply eval_Zexpr_Z_eval_Zexpr in Hk.
     assert (result_has_shape (V l) (m::sh0)) as Hsh.
     { eapply size_of_eval_expr_result_has_shape; eauto. }
     
     assert (m = Z.to_nat kz \/ Z.to_nat kz < m) as HHcase by lia.
     inversion HHcase as [ HHcase1 | HHcase2]; clear HHcase.
     { pose proof (truncl_list_length_empty (Z.to_nat kz) (rev l)) as H7.
       erewrite length_rev in H7.
       erewrite result_has_shape_length in H7.
       2: { simpl map in *. eauto. }
       assert (H8: m <= Z.to_nat kz) by lia.
       eapply H7 in H8.
       rewrite H8 in *. clear H6. simpl rev.
       invert Hpad.
       cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *.
       rename H3 into Hpad. pose proof Hpad as Hpad'.
       eapply has_pad_gen_pad in Hpad'.
       2: { eauto. }
       2: { eauto. }
       2: { eauto. }
       2: { eapply contexts_agree_result_has_shape. eauto. }
       2: { eauto. }
       simpl in Hpad'. destruct Hpad' as (_&Hpad'&Hpad''&_).
       rewrite firstn_all2 in Hpad'.
       2: { erewrite length_rev. erewrite result_has_shape_length.
            2: simpl in *; eauto. lia. }
       eapply Forall_rev in Hpad'.
       rewrite rev_involutive in *.
       eapply forall_eq_gen_pad in Hpad'. rewrite Hpad' in *.
       eapply IHeval_expr in H4.
       2: { eauto. }
       2: { eauto. }
       2: { simpl. rewrite <- gen_pad_cons.
            apply well_formed_allocation_result_V in Halloc.
            2: apply Hrdx.
            invert Halloc.

            decomp_well_formed_reindexer.
            rewrite filter_negb_is_None_result_lookup_Z_option_gen_pad in *.
            split.
            unfold partial_injective. intros. simpl in *. contradiction.
            split.
            intros l1 l2 HeqZlist'. destruct l1; destruct l2.
            eauto.
            invert HeqZlist'. discriminate.
            invert HeqZlist'. discriminate.
            destruct p0. destruct p1.
            eapply HeqZlist.
            erewrite <- eq_Z_tuple_index_list_cons_tup.
            erewrite <- eq_Z_tuple_index_list_cons_tup in HeqZlist'.
            propositional. subst. reflexivity.
            split.
            auto.
            split. intros var k0 l1 H2.
            destruct l1. simpl. rewrite Hmap. eauto. eauto.
            destruct p0. simpl. rewrite Hmap. simpl. reflexivity.
            assumption.
            split.
            intros l1.
            destruct l1. rewrite Hvarsarg. sets.
            destruct p0. simpl. rewrite Hvarsarg. simpl.
            sets.
            unfold nondestructivity.
            split; intros.
            unfold tensor_to_array_delta in H6.
            rewrite filter_negb_is_None_result_lookup_Z_option_gen_pad in *.
            unfold tensor_to_array_delta_by_indices in *. simpl in *.
            rewrite dom_empty in *. sets.
            invs'.
            eapply lookup_Some_dom in H6. sets. } 
       2: { simpl. rewrite <- gen_pad_cons.
            replace kz with (Z.of_nat (Z.to_nat kz)) by lia.
            eapply well_formed_allocation_gen_pad.
            eapply well_formed_allocation_truncr
              with (x:=[]).
            simpl. rewrite rev_repeat.
            pose proof (truncl_list_length_empty
                          (Z.to_nat kz)
                          (repeat (gen_pad sh0) (Z.to_nat kz))) as H6.
            rewrite repeat_length in *.
            assert (Z.to_nat kz <= Z.to_nat kz) as H9 by lia.
            eapply H6 in H9.
            rewrite H9. eauto.
            eapply Hrdx. 
            simpl. eapply result_has_shape_repeat.
            eapply result_has_shape_gen_pad.
            apply Hrdx.
            apply Henv. apply Hrdx. apply Hrdx.
            simpl.
            rewrite Hpad'. simpl. rewrite repeat_length.
            simpl in Hsh. eapply result_has_shape_length in Hsh.
            rewrite repeat_length in Hsh. rewrite Hsh.
            eapply result_has_shape_repeat.
            eapply result_has_shape_gen_pad. }
       2: { eauto. }
       2: { eauto. }
       2: { eauto. }
       cases (reindexer
      (shape_to_index (result_shape_Z (V []))
                      (shape_to_vars (result_shape_Z (V []))))).
       { eapply reindexer_not_empty_vars_in_index in Heq. propositional.
         apply Hrdx. simpl. intros ?. cups_empty. }
       cases ((fun l : list (Zexpr * Z) =>
          reindexer
            match l with
            | [] => l
            | (v, d) :: xs => (v, (d - kz)%Z) :: xs
            end)
           (shape_to_index
              (result_shape_Z
                 (V
                    (gen_pad_list
                       (Datatypes.length l :: sh0))))
              (shape_to_vars
                 (result_shape_Z
                    (V
                       (gen_pad_list
                          (Datatypes.length l :: sh0))))))).
       { cases (shape_to_index
               (result_shape_Z
                  (V
                     (gen_pad_list
                        (length l :: sh0))))
               (shape_to_vars
                  (result_shape_Z
                     (V
                        (gen_pad_list
                           (length l :: sh0)))))).
         eapply shape_to_index_not_empty_Z in Heq1. propositional.
         eapply reindexer_not_empty_vars_in_index in Heq0.
         propositional. apply Hrdx.
         unfold result_shape_Z,shape_to_index,shape_to_vars in Heq1.
         simpl in *. cases l. simpl in *.
         - invert Heq1. simpl. intro. cups_empty.
         - invert Heq1. simpl. intro. cups_empty. }
       unfold lookup_total in *. invs'. split; auto.
       eapply well_formed_allocation_result_V in Halloc.
       invs'. f_equal. f_equal.
       rewrite tensor_to_array_delta_empty_tensor.
       simpl. rewrite <- gen_pad_cons.
       rewrite tensor_to_array_delta_gen_pad. reflexivity.
       apply Hrdx.
     }
     pose proof (forall_nonneg_exists_zero_or_forall_pos sh0) as [H2|H2].
     2: { pose proof Hpad as Hpad'. invert Hpad'.
          eapply IHeval_expr in Heval.
          2: { eauto. }
          2: { eauto. }
          2: { decomp_well_formed_reindexer.
               split.
               { erewrite result_has_shape_result_shape_Z by eauto.
                 unfold partial_injective. intros.
                 repeat decomp_index.
                 eapply mesh_grid_shape_pos in H13.
                 apply Forall_Exists_neg in H2. contradiction.
                 eapply Forall_impl. 2: apply Forall_map; eassumption.
                 simpl. lia. }
               split.
               { intros l1 l2 Hl.
                 cases l1; cases l2.
                 - eapply HeqZlist. eauto.
                 - invert Hl. discriminate.
                 - invert Hl. discriminate.
                 - cases p0. cases p1.
                   erewrite <- eq_Z_tuple_index_list_cons_tup in Hl. invs'.
                   eapply HeqZlist.
                   erewrite <- eq_Z_tuple_index_list_cons_tup. invs'.
                   split. auto. auto. }
               split.
               auto.
               split.
               intros. rewrite Hmap by auto.
               cases l1. reflexivity. cases p0. simpl.
               unfold subst_var_in_Z_tup at 1. reflexivity.
               split.
               { intros. rewrite Hvarsarg.
                 cases l1. reflexivity. cases p0. reflexivity. }
               { invert Hpad. cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *.
                 rename H13 into Hpad.
                 eapply has_pad_gen_pad in Hpad.
                 2: { eauto. }
                 2: { eauto. }
                 2: { eauto. }
                 2: { eapply contexts_agree_result_has_shape. eauto. }
                 2: { eauto. }
                 simpl in Hpad. invs'.
                 unfold nondestructivity in *. split; intros.
                 unfold tensor_to_array_delta in H13.
                 rewrite exists_0_empty_mesh_grid in H13.
                 2: { cbv [result_shape_Z]. apply Exists_map.
                      erewrite result_has_shape_result_shape_nat by eauto.
                      eapply Exists_impl.
                      2: { apply exists_filter_until_0. auto. }
                      simpl. lia. }
                 simpl in H13. unfold tensor_to_array_delta_by_indices in H13.
                 simpl in H13. rewrite dom_empty in H13. sets.
                 eapply well_formed_allocation_result_V in Halloc.
                 invert Halloc. invs'. eapply lookup_Some_dom in H11.
                 sets. eauto.                 
               }
          }
          2: { unfold well_formed_allocation.
               rewrite exists_0_empty_mesh_grid.
               simpl.
               eapply well_formed_allocation_result_V in Halloc.
               invs'. rewrite H3.
               cases (shape_to_index (result_shape_Z (V l))
                                     (shape_to_vars (result_shape_Z (V l)))).
               { eapply shape_to_index_not_empty_Z in Heq. propositional. }
               destruct (reindexer (let (v0, d) := p0 in _)) eqn:Heq0.
               { unfold result_shape_Z, shape_to_index, shape_to_vars in Heq.
                 simpl in *. invert Heq.
                 rewrite length_map in *.
                 cases l.
                 - simpl in *. invs'.
                   eapply reindexer_not_empty_vars_in_index in Heq0.
                   contradiction.
                   apply Hrdx.
                   simpl. intro. cups_empty.
                 - simpl in *. invs'.
                   eapply reindexer_not_empty_vars_in_index in Heq0.
                   contradiction.
                   apply Hrdx.
                   simpl. intro. cups_empty. }
               eexists. split. reflexivity. sets.
               apply Hrdx.
               cbv [result_shape_Z]. apply Exists_map.
               erewrite result_has_shape_result_shape_nat by eauto.
               eapply Exists_impl.
               2: { apply exists_filter_until_0. auto. }
               simpl. lia. }
          2: { eauto. }
          2: { eauto. }
          
          cases (shape_to_index (result_shape_Z (V l))
                                (shape_to_vars (result_shape_Z (V l)))).
          { eapply shape_to_index_not_empty_Z in Heq. propositional. }
          destruct (reindexer (let (v, d) := p0 in _)) eqn:Heq0.
          { unfold result_shape_Z, shape_to_index, shape_to_vars in Heq.
            simpl in *. invert Heq.
            rewrite length_map in *.
            cases l.
            - simpl in *. invs'.
              eapply reindexer_not_empty_vars_in_index in Heq0.
              contradiction.
              apply Hrdx.
              simpl. intro. cups_empty.
            - simpl in *. invs'.
              eapply reindexer_not_empty_vars_in_index in Heq0.
              contradiction.
              apply Hrdx.
              simpl. intro. cups_empty. }
          invs.
          unfold lookup_total.
          eapply well_formed_allocation_result_V in Halloc. invs.
          rewrite H3. 
          cases (reindexer
                   (shape_to_index
                      (result_shape_Z
                         (V (rev
                               (truncl_list
                                  (Z.to_nat kz)
                                  (rev l)))))
                      (shape_to_vars
                         (result_shape_Z
                            (V (rev (truncl_list
                                       (Z.to_nat
                                          kz)
                                       (rev l)))))))).
          { erewrite result_has_shape_result_shape_Z in Heq1.
            2: { eapply result_has_shape_rev.
                 eapply result_has_shape_truncl_list.
                 eapply result_has_shape_rev.
                 erewrite <- result_has_shape_filter_until_0.
                 simpl in *. eauto. }
            unfold result_shape_Z, shape_to_index, shape_to_vars in Heq1.
            simpl in *. 
            rewrite length_map in *.
            cases (m - Z.to_nat kz).
            - simpl in *. 
              eapply reindexer_not_empty_vars_in_index in Heq1.
              contradiction.
              apply Hrdx.
              simpl. intro. cups_empty.
            - simpl in *. 
              eapply reindexer_not_empty_vars_in_index in Heq1.
              contradiction.
              apply Hrdx.
              simpl. intro. cups_empty. }
          split. 2: auto.
          f_equal. f_equal.
          unfold tensor_to_array_delta,
            tensor_to_array_delta_by_indices.
          rewrite exists_0_empty_mesh_grid.
          rewrite exists_0_empty_mesh_grid.
          simpl. reflexivity.
          erewrite result_has_shape_result_shape_Z.
          2: { eapply result_has_shape_rev.
               eapply result_has_shape_truncl_list.
               eapply result_has_shape_rev.
               erewrite <- result_has_shape_filter_until_0.
               simpl in *. eauto. }
          erewrite Exists_map.
          eapply Exists_impl; [|apply exists_filter_until_0].
          simpl. lia.
          right. eauto.
          erewrite result_has_shape_result_shape_Z by eauto.
          erewrite Exists_map.
          eapply Exists_impl; [|apply exists_filter_until_0].
          simpl. lia.
          simpl. right. eauto.
          apply Hrdx. eauto.
     }
     
     assert (exists l', l =
                          l' ++
                             gen_pad_list
                             (Z.to_nat kz :: sh0))%list.
     { invert Hpad.
       cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *.
       eapply has_pad_gen_pad in H5.
       2: { eauto. }
       2: { eauto. } 
       2: { eauto. }
       2: { eapply contexts_agree_result_has_shape; eauto. }
       2: eauto.
       simpl in *. invs.
       rewrite <- (rev_involutive l).
       erewrite <- firstn_skipn
         with (l:=rev l) (n:=(Z.to_nat kz)).
       rewrite rev_app_distr.
       eexists (rev (skipn (Z.to_nat kz) (rev l))).
       f_equal.
       eapply forall_firstn_ge in H5.
       2: { apply H10. }
       eapply forall_eq_gen_pad in H5.
       simpl in H5.
       rewrite H5.
       rewrite rev_repeat. rewrite length_firstn.
       rewrite length_rev.
       erewrite result_has_shape_length by eauto. f_equal. lia. }

     invs'.
     invert Hpad.
     cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *.
     
     eapply IHeval_expr in Heval; clear IHeval_expr; eauto.
     2: { eapply well_formed_allocation_result_V in Halloc.
          invert Halloc. invs'.
          rewrite <- (Z2Nat.id kz) by lia. rewrite Nat2Z.id.
          eapply well_formed_reindexer_truncr. eauto.
          repeat rewrite map_cons in Hsh. eauto.
          apply Henv.
          eassumption.
          lia.
          apply Hrdx. }
     2: { rewrite <- (Z2Nat.id kz) by lia. rewrite Nat2Z.id.
          eapply well_formed_allocation_truncr. eauto.
          apply Hrdx. eauto.
          apply Hrdx. apply Henv. apply Hrdx. apply Hrdx. }
     match goal with
     | |- context[reindexer ?x] => destruct (reindexer x) eqn:Heq
     end.
     { eapply reindexer_not_empty in Heq. propositional. apply Hrdx.
       erewrite result_has_shape_result_shape_Z.
       2: { eapply result_has_shape_rev.
            eapply result_has_shape_truncl_list.
            erewrite <- result_has_shape_filter_until_0.
            eapply result_has_shape_rev.
            repeat rewrite map_cons in Hsh.
            eauto. }
       simpl.
       cases (m - Z.to_nat kz =? 0)%nat; inversion 1. }
     cases (shape_to_index
                  (result_shape_Z
                     (V
                        (x ++
                         gen_pad_list
                           (Z.to_nat kz :: sh0))))
                  (shape_to_vars
                     (result_shape_Z
                        (V
                           (x ++
                            gen_pad_list
                              (Z.to_nat kz :: sh0)))))).
     { eapply shape_to_index_not_empty_Z in Heq0. propositional. }
     destruct (reindexer (let (v, d) := p1 in _)) eqn:Heq1.
     { unfold shape_to_index, shape_to_vars, result_shape_Z in Heq0.
       simpl in Heq0.
       cases ((x ++ repeat (gen_pad sh0) (Z.to_nat kz))%list);
         invert Heq0.
       - eapply reindexer_not_empty_vars_in_index in Heq1. propositional.
         apply Hrdx. simpl. intro. cups_empty.
       - eapply reindexer_not_empty_vars_in_index in Heq1. propositional.
         apply Hrdx. simpl. intro. cups_empty. }
     invs'.
     pose proof Halloc as Halloc1.
     eapply well_formed_allocation_result_V in Halloc1;
       try apply Hrdx. invs'.
     unfold lookup_total. rewrite H3.
     split. 2: auto. f_equal.
     f_equal.

     erewrite result_has_shape_result_shape_Z by eassumption.
     erewrite result_has_shape_result_shape_Z.
     2: { eapply result_has_shape_rev.
          eapply result_has_shape_truncl_list.
          erewrite <- result_has_shape_filter_until_0.
          eapply result_has_shape_rev.
          repeat rewrite map_cons in Hsh.
          eassumption. }
     unfold tensor_to_array_delta.

     rewrite rev_app_distr in *.
     simpl gen_pad_list in *.
     rewrite rev_repeat in *.
     pose proof truncl_list_gen_pad_id as H.
     simpl gen_pad_list in H.
     rewrite H in *. clear H.
     rewrite rev_involutive in *.
     
     erewrite result_has_shape_result_shape_Z by eassumption.

     repeat rewrite <- map_cons.
     pose proof filter_pad_r_mesh_grid as H. simpl gen_pad_list in H.
     rewrite H. clear H.

     2: { repeat rewrite map_cons in Hsh.
          pose proof Hsh. eapply result_has_shape_app_l in Hsh.
          eapply result_has_shape_app_r in H8.
          2: { rewrite repeat_length. reflexivity. }
          2: { reflexivity. }
          simpl map.
          simpl. replace m with (Z.to_nat kz + (m - Z.to_nat kz)) by lia.
          eapply result_has_shape_concat.
          eapply result_has_shape_repeat_gen_pad.
          eauto. }
     2: { lia. }

     eapply eq_tensor_to_array_delta_by_indices_shuffle with
       (shuffle:=fun x => x).
        + intros ? H.
          erewrite result_has_shape_result_shape_Z in H.
          2: { repeat rewrite map_cons in Hsh.
               eapply result_has_shape_app_r; eauto. }
          rewrite repeat_length in *.
          repeat decomp_index.
          simpl. rewrite nth_error_app1. auto.
          erewrite result_has_shape_length.
          2: { repeat rewrite map_cons in Hsh.
               eapply result_has_shape_app_r; eauto. }
          rewrite repeat_length. lia.
        + intros ? H.
          erewrite result_has_shape_result_shape_Z in H.
          2: { repeat rewrite map_cons in Hsh.
               eapply result_has_shape_app_r; eauto. }
          rewrite repeat_length in *.
          repeat decomp_index.
          rewrite <- (Z2Nat.id kz) by lia. rewrite Nat2Z.id.
          rewrite eq_partial_interpret_reindexer_truncr;
            try apply Henv; try apply Hrdx.
          reflexivity.
          lia.
        + intros ? H.
          erewrite result_has_shape_result_shape_Z in H.
          2: { repeat rewrite map_cons in Hsh.
               eapply result_has_shape_app_r; eauto. }
          rewrite repeat_length in *. eauto.
        + intros.
          erewrite result_has_shape_result_shape_Z.
          2: { repeat rewrite map_cons in Hsh.
               eapply result_has_shape_app_r; eauto. }
          rewrite repeat_length in *. eauto.
        + decomp_well_formed_reindexer.
          pose proof Hinj as H.
          erewrite result_has_shape_result_shape_Z in H.
          2: { repeat rewrite map_cons in Hsh.
               eapply result_has_shape_app_r; eauto. }
          erewrite result_has_shape_result_shape_Z.
          2: { repeat rewrite map_cons in Hsh.
               eapply result_has_shape_app_r; eauto. }
          rewrite repeat_length in *. eauto.
        + decomp_well_formed_reindexer.
          erewrite result_has_shape_result_shape_Z in Hinj.
          2: { repeat rewrite map_cons in Hsh.
               eapply result_has_shape_app_r; eauto. }
          rewrite repeat_length in *.
          rewrite <- (Z2Nat.id kz) by lia. rewrite Nat2Z.id.
          eapply partial_injective_truncr; eauto.
          apply Henv.
          lia.
        + unfold injective. propositional.
        + eapply no_dup_filter.
          eapply no_dup_mesh_grid.
        + eapply no_dup_filter.
          eapply no_dup_mesh_grid.
   - (* TRUNCL *) simpl in *. invert Hsize.
     rename H5 into Hk. pose proof Hk as Hk'.
     eapply eval_Zexpr_includes_valuation in Hk'; try apply empty_includes.
     apply eval_Zexpr_Z_eval_Zexpr in Hk'.
     rewrite Hk' in *. invs'. apply eval_Zexpr_Z_eval_Zexpr in Hk.
     
     assert (result_has_shape (V l) (m::sh0)) as Hsh.
     { eapply size_of_eval_expr_result_has_shape; eauto. }

     assert (m = Z.to_nat kz \/ Z.to_nat kz < m) as HHcase by lia.
     inversion HHcase as [ HHcase1 | HHcase2]; clear HHcase.
     { pose proof (truncl_list_length_empty (Z.to_nat kz) l) as H8.
       erewrite result_has_shape_length in H8.
       2: { simpl map in *. eauto. }
       assert (m <= Z.to_nat kz) as H9 by lia.
       eapply H8 in H9.
       rewrite H9 in *. clear H8.
       invert Hpad.
       cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *.
       rename H3 into Hpad. pose proof Hpad as Hpad'.
       eapply has_pad_gen_pad in Hpad'.
       2: { eauto. }
       2: { eauto. }
       2: { eauto. }
       2: { eapply contexts_agree_result_has_shape. eauto. }
       2: { eauto. }
       simpl in Hpad'. destruct Hpad' as (Hpad'&_&_&_).
       rewrite firstn_all2 in Hpad'.
       2: { erewrite result_has_shape_length.
            2: simpl in *; eauto. lia. }
       eapply forall_eq_gen_pad in Hpad'. rewrite Hpad' in *.
       eapply IHeval_expr in H4.
       2: { eauto. }
       2: { eauto. }
       2: { simpl. rewrite <- gen_pad_cons.
            eapply well_formed_allocation_result_V in Halloc.
            invert Halloc.
            decomp_well_formed_reindexer.
            erewrite filter_negb_is_None_result_lookup_Z_option_gen_pad.
            split.
            unfold partial_injective. intros.
            simpl in *. contradiction.
            split.
            intros l1 l2 Hl. destruct l1; destruct l2.
            eauto.
            invert Hl. discriminate.
            invert Hl. discriminate.
            destruct p0. destruct p1.
            eapply HeqZlist.
            erewrite <- eq_Z_tuple_index_list_cons_tup.
            erewrite <- eq_Z_tuple_index_list_cons_tup in Hl.
            propositional.
            eapply eq_zexpr_sub; eauto.
            subst. reflexivity.
            split. auto.
            split. intros.
            destruct l1. simpl. rewrite Hmap. eauto. eauto.
            destruct p0. rewrite Hmap. simpl.
            unfold subst_var_in_Z_tup at 1. reflexivity.
            eauto.
            split.
            intros l1. destruct l1. rewrite Hvarsarg. sets.
            destruct p0. simpl. rewrite Hvarsarg. simpl.
            rewrite app_no_dups_empty_r. reflexivity.
            unfold nondestructivity.
            unfold tensor_to_array_delta.
            erewrite filter_negb_is_None_result_lookup_Z_option_gen_pad.
            unfold tensor_to_array_delta_by_indices.
            simpl. rewrite dom_empty. split; intros. sets.
            invs'.
            eapply lookup_Some_dom in H7. sets. apply Hrdx. }
       2: { simpl. rewrite <- gen_pad_cons.
            eapply well_formed_allocation_gen_pad.
            Check well_formed_allocation_truncl.
            eapply well_formed_allocation_truncl
              with (x:=[]).
            eauto.
            eapply Hrdx. 
            simpl. rewrite app_nil_r. eapply result_has_shape_repeat.
            eapply result_has_shape_gen_pad.
            lia. apply Hrdx.
            apply Henv. apply Hrdx. apply Hrdx.
            simpl.
            rewrite Hpad'. simpl. rewrite repeat_length.
            simpl in Hsh. eapply result_has_shape_length in Hsh.
            rewrite repeat_length in Hsh. rewrite Hsh.
            rewrite app_nil_r.
            eapply result_has_shape_repeat.
            eapply result_has_shape_gen_pad. }
       2: { eauto. }
       2: { eauto. }
       2: { eauto. }
       cases (reindexer
      (shape_to_index (result_shape_Z (V []))
                      (shape_to_vars (result_shape_Z (V []))))).
       { eapply reindexer_not_empty_vars_in_index in Heq. propositional.
         apply Hrdx. simpl. intro. cups_empty. }
       cases ((fun l : list (Zexpr * Z) =>
          reindexer
            match l with
            | [] => l
            | (v, d) :: xs => ((v- | kz |)%z, (d - kz)%Z) :: xs
            end)
           (shape_to_index
              (result_shape_Z
                 (V
                    (gen_pad_list
                       (Datatypes.length l
                        :: sh0))))
              (shape_to_vars
                 (result_shape_Z
                    (V
                       (gen_pad_list
                          (Datatypes.length l
                                            :: sh0))))))).
       { cases (shape_to_index
               (result_shape_Z
                  (V
                     (gen_pad_list
                        (length l :: sh0))))
               (shape_to_vars
                  (result_shape_Z
                     (V
                        (gen_pad_list
                           (length l :: sh0)))))).
         eapply shape_to_index_not_empty_Z in Heq1. propositional.
         eapply reindexer_not_empty_vars_in_index in Heq0.
         propositional. apply Hrdx.
         unfold result_shape_Z,shape_to_index,shape_to_vars in Heq1.
         simpl in *. cases l. simpl in *.
         - invert Heq1. simpl. intro. cups_empty.
         - invert Heq1. simpl. intro. cups_empty. }
       unfold lookup_total in *. invs. split; auto.
       eapply well_formed_allocation_result_V in Halloc.
       invs. rewrite H2 in *. f_equal. f_equal.
       rewrite tensor_to_array_delta_empty_tensor.
       simpl. rewrite <- gen_pad_cons.
       rewrite tensor_to_array_delta_gen_pad. reflexivity.
       apply Hrdx. }
       
     pose proof (forall_nonneg_exists_zero_or_forall_pos sh0) as [H2|H2].
     2: { pose proof Hpad as Hpad'. invert Hpad'.
          eapply IHeval_expr in Heval.
          2: { eauto. }
          2: { eauto. }
          2: { decomp_well_formed_reindexer.
               split.
               { erewrite result_has_shape_result_shape_Z by eauto.
                 unfold partial_injective. intros.
                 repeat decomp_index.
                 eapply mesh_grid_shape_pos in H13.
                 apply Forall_Exists_neg in H2. contradiction.
                 eapply Forall_impl. 2: apply Forall_map; eassumption.
                 simpl. lia. }
               split.
               { intros l1 l2 Hl.
                 cases l1; cases l2.
                 - eapply HeqZlist. eauto.
                 - invert Hl. discriminate.
                 - invert Hl. discriminate.
                 - cases p0. cases p1.
                   erewrite <- eq_Z_tuple_index_list_cons_tup in Hl. invs'.
                   eapply HeqZlist.
                   erewrite <- eq_Z_tuple_index_list_cons_tup. invs'.
                   split. apply eq_zexpr_sub. auto.
                   apply eq_zexpr_id. auto. auto. }
               split.
               auto.
               split.
              intros. rewrite Hmap by auto.
              cases l1. reflexivity. cases p0. simpl.
              unfold subst_var_in_Z_tup at 1. simpl. reflexivity.
              split.
              { intros. rewrite Hvarsarg.
                cases l1. reflexivity. cases p0. f_equal.
                simpl. rewrite app_no_dups_empty_r. reflexivity. }
              { unfold nondestructivity in *. split; intros.
                 unfold tensor_to_array_delta in H8.
                 rewrite exists_0_empty_mesh_grid in H8.
                 2: { cbv [result_shape_Z]. apply Exists_map.
                      erewrite result_has_shape_result_shape_nat by eauto.
                      eapply Exists_impl.
                      2: { apply exists_filter_until_0. auto. }
                      simpl. lia. }
                 simpl in H8. unfold tensor_to_array_delta_by_indices in H8.
                 simpl in H8. rewrite dom_empty in H8. sets.
                 eapply well_formed_allocation_result_V in Halloc.
                 invert Halloc. invs'. eapply lookup_Some_dom in H3.
                 sets. eauto. }
          }
          2: { unfold well_formed_allocation.
               rewrite exists_0_empty_mesh_grid.
               simpl.
               eapply well_formed_allocation_result_V in Halloc.
               invs'. rewrite H3.
               cases (shape_to_index (result_shape_Z (V l))
                                     (shape_to_vars (result_shape_Z (V l)))).
               { eapply shape_to_index_not_empty_Z in Heq. propositional. }
               destruct (reindexer (let (v0, d) := p0 in _)) eqn:Heq0.
               { unfold shape_to_index,result_shape_Z,shape_to_vars in Heq.
                 simpl in Heq. invert Heq.
                 repeat rewrite length_map in *.
                 cases l.
                 - simpl in *. invs'.
                   eapply reindexer_not_empty_vars_in_index in Heq0.
                   contradiction.
                   apply Hrdx.
                   simpl. intro. cups_empty.
                 - simpl in *. invs'.
                   eapply reindexer_not_empty_vars_in_index in Heq0.
                   contradiction.
                   apply Hrdx.
                   simpl. intro. cups_empty. }
               eexists. split. reflexivity. sets.
               apply Hrdx.
               erewrite result_has_shape_result_shape_Z by eauto.
               erewrite Exists_map.
               eapply Exists_impl; [|apply exists_filter_until_0].
               simpl. lia.
               simpl. right. eauto. }
          2: { eauto. }
          2: { eauto. }
          
          cases (shape_to_index (result_shape_Z (V l))
                                (shape_to_vars (result_shape_Z (V l)))).
          { eapply shape_to_index_not_empty_Z in Heq. propositional. }

          destruct (reindexer (let (v, d) := p0 in _)) eqn:Heq0.
          { unfold shape_to_index,result_shape_Z,shape_to_vars in Heq.
            simpl in Heq0. invert Heq.
            repeat rewrite length_map in *.
            cases l.
            - simpl in *. invs'.
              eapply reindexer_not_empty_vars_in_index in Heq0.
              contradiction.
              apply Hrdx.
              simpl. intro. cups_empty.
            - simpl in *. invs'.
              eapply reindexer_not_empty_vars_in_index in Heq0.
              contradiction.
              apply Hrdx.
              simpl. intro. cups_empty. }
          invs'.
          unfold lookup_total.
          eapply well_formed_allocation_result_V in Halloc. invs'.
          rewrite H3.
          match goal with
          | |- context[reindexer ?x] => destruct (reindexer x) eqn:Heq1
          end.
          { erewrite result_has_shape_result_shape_Z in Heq1.
            2: { eapply result_has_shape_truncl_list.
                 erewrite <- result_has_shape_filter_until_0.
                 simpl in *. eauto. }
            simpl in *.
            cases (m - Z.to_nat kz).
            - simpl in *.
              eapply reindexer_not_empty_vars_in_index in Heq1.
              contradiction.
              apply Hrdx.
              simpl. intro. cups_empty. 
            - simpl in *.
              eapply reindexer_not_empty_vars_in_index in Heq1.
              contradiction.
              apply Hrdx.
              simpl. intro. cups_empty. }
          split. 2: auto.
          f_equal. f_equal.
          unfold tensor_to_array_delta,
            tensor_to_array_delta_by_indices.
          rewrite exists_0_empty_mesh_grid.
          rewrite exists_0_empty_mesh_grid.
          simpl. reflexivity.
          erewrite result_has_shape_result_shape_Z.
          2: { eapply result_has_shape_truncl_list.
               erewrite <- result_has_shape_filter_until_0.
               simpl in *. eauto. }
          erewrite Exists_map.
          eapply Exists_impl; [|apply exists_filter_until_0].
          simpl. lia.
          right. eauto.
          erewrite result_has_shape_result_shape_Z by eauto.
          erewrite Exists_map.
          eapply Exists_impl; [|apply exists_filter_until_0].
          simpl. lia.
          simpl. right. eauto.
          apply Hrdx. eauto. }

     assert (exists l', l = gen_pad_list (Z.to_nat kz :: sh0)++l')%list.
     { invert Hpad.
       cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *.
       eapply has_pad_gen_pad in H5.
       2: { eauto. }
       2: { eauto. } 
       2: { eauto. }
       2: { eapply contexts_agree_result_has_shape. eauto. }
       2: { eauto. }
       simpl in *. destruct H5 as (H5&_&_&_).
       erewrite <- firstn_skipn
         with (l:=l) (n:=(Z.to_nat kz)).
       eexists (skipn (Z.to_nat kz) l).
       f_equal.
       eapply forall_firstn_ge in H5.
       2: apply H10.
       eapply forall_eq_gen_pad in H5.
       simpl in H5.
       rewrite H5.
       rewrite length_firstn.
       erewrite result_has_shape_length by eauto. f_equal. lia. }
     invs'.

     rewrite truncl_list_gen_pad_id in *.

     invert Hpad.
     cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *.
     eapply IHeval_expr in Heval; clear IHeval_expr; eauto.
     2: { eapply well_formed_allocation_result_V in Halloc.
          invert Halloc. invs'.
          eapply well_formed_reindexer_truncl; 
          try apply Henv.
          auto. simpl in *. eassumption. lia.
          eassumption. lia. apply Hrdx. }
     2: { eapply well_formed_allocation_truncl;
          try apply Henv; try apply Hrdx; auto.
          simpl in *. eauto. }

     cases (reindexer
              (shape_to_index (result_shape_Z (V x))
                              (shape_to_vars (result_shape_Z (V x))))).
     { eapply reindexer_not_empty in Heq. propositional. apply Hrdx.
       cases x; unfold result_shape_Z; simpl; inversion 1. }
     
     cases (shape_to_index
              (result_shape_Z
                 (V
                    (gen_pad_list
                       (Z.to_nat kz :: sh0) ++ x)))
              (shape_to_vars
                 (result_shape_Z
                    (V
                       (gen_pad_list
                          (Z.to_nat kz :: sh0) ++
                          x))))).
     { eapply shape_to_index_not_empty_Z in Heq0. propositional. }
     destruct (reindexer (let (v, d) := p1 in _)) eqn:Heq1.
     { erewrite result_has_shape_result_shape_Z in Heq0.
       2: { eauto. }
       unfold shape_to_index, shape_to_vars, result_shape_Z in Heq0.
       simpl in Heq0.
       cases m. lia.
       cases l; invert Heq0.
       - eapply reindexer_not_empty_vars_in_index in Heq1. propositional.
         apply Hrdx. simpl. intro. cups_empty.
       - eapply reindexer_not_empty_vars_in_index in Heq1. propositional.
         apply Hrdx. simpl. intro. cups_empty. }
     invs'.
     pose proof Halloc as Halloc1.
     
     eapply well_formed_allocation_result_V in Halloc1;
       try apply Hrdx. invs.
     unfold lookup_total. rewrite H3.
     split. 2: auto. f_equal.     
     f_equal.
     invs. subst.
     unfold tensor_to_array_delta.
     erewrite result_has_shape_result_shape_Z.
     2: { eauto. }
     erewrite result_has_shape_result_shape_Z.
     2: { simpl in *.
          eapply result_has_shape_app_l.
          2: eauto. simpl. rewrite repeat_length. reflexivity. }
     rewrite filter_pad_l_mesh_grid; auto.
     eapply eq_tensor_to_array_delta_by_indices_shuffle
       with (shuffle:=(fun l => match l with
                                | [] => l
                                | x::xs => (x+kz)%Z::xs
                                end)).
        + intros. repeat decomp_index.
          eapply result_lookup_Z_option_concat_l; lia.
        + intros. repeat decomp_index.
          eapply eq_partial_interpret_reindexer_truncl.
          apply Henv.
          apply Hrdx.
          apply Hrdx.
          apply Hrdx.
          apply Hrdx.
          lia. lia.
        + intros. repeat decomp_index.
          eapply in_map_iff. eexists (z::x2).
          propositional.
          eapply filter_In. propositional.
          repeat decomp_goal_index. propositional.
        + intros ? H. eapply in_map_iff in H. invs.
          repeat decomp_index.
          eexists (z::x3). propositional.
          eapply filter_In. propositional.
          repeat decomp_goal_index.
          propositional.
        + decomp_well_formed_reindexer. pose proof Hinj as H.
          erewrite result_has_shape_result_shape_Z in H.
          eapply H.
          eapply result_has_shape_app_l; eauto.
          simpl. rewrite repeat_length. reflexivity.
        + decomp_well_formed_reindexer.
          eapply partial_injective_truncl.
          eauto.
          eassumption.
          apply Henv.         
          auto. auto. auto. auto. lia. lia.
        + unfold injective. propositional.
          repeat decomp_index.
          invs'. f_equal. lia.
        + eapply no_dup_filter. eapply no_dup_mesh_grid.
        + eapply no_dup_injective_map.
          2: { eapply no_dup_filter.
               eapply no_dup_mesh_grid. }
          unfold injective.
          propositional.
          repeat decomp_index.
          invs'. f_equal. lia.
   - (* PADR *) simpl in *. invert Hsize. eq_size_of. invs'.

        rename H6 into Hk. pose proof Hk as Hk'.
        eapply eval_Zexpr_includes_valuation in Hk'; try apply empty_includes.
        apply eval_Zexpr_Z_eval_Zexpr in Hk'.
        rewrite Hk' in *. invs'. apply eval_Zexpr_Z_eval_Zexpr in Hk.

        assert (result_has_shape (V l) (m::sh0)) as Hsh.
        { eapply size_of_eval_expr_result_has_shape; eauto. }
        pose proof Halloc as Halloc1.
        eapply well_formed_allocation_result_V in Halloc1.
        inversion Halloc1 as [a Htmp]. clear Halloc1.
        inversion Htmp as [Heq Hsub]. clear Htmp.

        invert Hpad; eq_size_of; invs'.
        { cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *.
          invert Hsh. rewrite app_nil_l in *.
          rewrite <- gen_pad_cons in *.
          rewrite filter_negb_is_None_result_lookup_Z_option_gen_pad in *.
          unfold lookup_total. rewrite Heq.
          match goal with
          | |- context[reindexer ?x] => destruct (reindexer x) eqn:Heq0
          end.
          {  eapply reindexer_not_empty_vars_in_index in Heq0.
             contradiction.
             apply Hrdx.
             erewrite result_has_shape_result_shape_Z
               by eapply result_has_shape_gen_pad.
             cases (Z.to_nat kz); simpl; intro; cups_empty. }
          unfold result_shape_Z in IHeval_expr.
          unfold shape_to_index, shape_to_vars in IHeval_expr. 
          simpl in IHeval_expr.
          rewrite tensor_to_array_delta_gen_pad in *.
          rewrite array_add_empty_r. rewrite add_id by auto.
          eapply IHeval_expr in Heval; clear IHeval_expr; eauto.
          2: { apply well_formed_allocation_result_V in Halloc.
               invert Halloc.
               decomp_well_formed_reindexer.
               propositional. simpl. unfold partial_injective.
               intros. simpl in *. contradiction.
               destruct l1; destruct l2; eauto.
               invert H. discriminate.
               invert H. discriminate.
               destruct p1. destruct p2. eapply HeqZlist.
               erewrite <- eq_Z_tuple_index_list_cons_tup.
               erewrite <- eq_Z_tuple_index_list_cons_tup in H.
               propositional. subst. reflexivity.
               destruct l0. simpl. rewrite Hmap. eauto. eauto.
               destruct p1. simpl. rewrite Hmap.
               simpl. unfold subst_var_in_Z_tup at 1. reflexivity.
               assumption.
               destruct l0. simpl. sets.
               destruct p1. simpl.
               rewrite Hvarsarg. reflexivity.
               unfold nondestructivity.
               unfold tensor_to_array_delta. simpl.
               unfold tensor_to_array_delta_by_indices. simpl.
               rewrite dom_empty. split; intros. sets.
               eapply lookup_Some_dom in Heq. sets. apply Hrdx. }
          cases (reindexer [((! "?" !)%z, (0 + kz)%Z)]).
          eapply reindexer_not_empty_vars_in_index in Heq1. propositional.
          apply Hrdx. simpl. intro. cups_empty.
          invs'. subst. unfold lookup_total. rewrite Heq.
          rewrite tensor_to_array_delta_empty_tensor.
          rewrite array_add_empty_r. rewrite add_id. propositional. auto.
          eapply well_formed_allocation_padr.
          constructor.
          lia.
          eauto.
          apply Hrdx. apply Henv. apply Hrdx. apply Hrdx. apply Hrdx. }

        cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *.
        eapply IHeval_expr in Heval; eauto.
        subst.
        erewrite result_has_shape_result_shape_Z.
        2: { eapply result_has_shape_concat.
             simpl in Hsh.
             apply Hsh.
             eapply result_has_shape_repeat_gen_pad. }
        match goal with
        | |- context[reindexer ?x] => destruct (reindexer x) eqn:Heq0
        end.
     { eapply reindexer_not_empty in Heq0. propositional. apply Hrdx.
       simpl.
       cases (dim + Z.to_nat kz)%nat; inversion 1. }
     cases (shape_to_index (result_shape_Z (V l))
                  (shape_to_vars (result_shape_Z (V l)))).
     { eapply shape_to_index_not_empty_Z in Heq1. propositional. }
     unfold lookup_total. rewrite Heq.
     
     destruct (reindexer (let (v, d) := p1 in _)) eqn:Heq2.
     { erewrite result_has_shape_result_shape_Z in Heq1; eauto.      
       unfold result_shape_Z, shape_to_index, shape_to_vars in Heq1.
       simpl in *.
       cases dim; invert Heq1.
       - eapply reindexer_not_empty_vars_in_index in Heq2. propositional.
         apply Hrdx. simpl. intro. cups_empty.
       - eapply reindexer_not_empty_vars_in_index in Heq2. propositional.
         apply Hrdx. simpl. intro. cups_empty. }
     invs'.
     split; auto. f_equal.
     unfold lookup_total. rewrite Heq.
     f_equal.

     unfold tensor_to_array_delta.
     symmetry.
     erewrite result_has_shape_result_shape_Z.
     2: { eapply result_has_shape_concat.
          simpl in Hsh. eauto.
          eapply result_has_shape_repeat_gen_pad. }
     
     pose proof filter_pad_r_mesh_grid as H. simpl gen_pad_list in H.
     rewrite H.
     
     erewrite result_has_shape_result_shape_Z by eauto.
     rewrite add_sub.
     eapply eq_tensor_to_array_delta_by_indices_shuffle
       with (shuffle:=fun l1  => l1).
        + intros.
          repeat decomp_index.
          simpl. rewrite nth_error_app1. auto.
          erewrite result_has_shape_length.
          2: { simpl in Hsh. eauto. }
          lia.
        + intros.
          repeat decomp_index.
          rewrite <- (Z2Nat.id kz) by lia. rewrite Nat2Z.id.
          erewrite eq_partial_interpret_reindexer_concat_l;
            try apply Hrdx; try apply Henv.
          reflexivity.
          2: eauto.
          2: { eapply result_has_shape_repeat_gen_pad. }
          erewrite result_has_shape_result_shape_Z by eauto.
          eapply filter_In. propositional.
          repeat decomp_goal_index.
          propositional.
        + intros. auto.
        + intros.
          repeat decomp_index.
          eexists. split. reflexivity.
          eapply filter_In. propositional.
          repeat decomp_goal_index.
          propositional.
        + decomp_well_formed_reindexer.
          erewrite result_has_shape_result_shape_Z in Hinj.
          2: { eapply result_has_shape_concat.
               simpl in Hsh. eauto.
               eapply result_has_shape_repeat_gen_pad. }

          rewrite <- (Z2Nat.id kz) by lia.
          eapply partial_injective_concat_l; auto; try apply Henv.
          erewrite result_has_shape_result_shape_Z.
          2: { eapply result_has_shape_concat. simpl in Hsh. eassumption.
               eapply result_has_shape_repeat_gen_pad
                 with (k:=Z.to_nat kz). }
          rewrite filter_fun_pad_r in *.
          auto.
          eapply result_has_shape_repeat_gen_pad.
        + decomp_well_formed_reindexer.
          erewrite result_has_shape_result_shape_Z in Hinj.
          2: { eapply result_has_shape_concat.
               simpl in Hsh. eauto.
               eapply result_has_shape_repeat_gen_pad. }          
          rewrite filter_fun_pad_r in *.
          simpl filter_until at 2.
          simpl filter_until at 2 in Hinj.
          cases dim.
          { simpl in *.
            unfold partial_injective. simpl in *. propositional. }
          simpl map at 2. posnats.
          simpl map at 2 in Hinj. posnats.
          rewrite <- add_succ_l in Hinj.
          rewrite Nat2Z.inj_add in Hinj.
          rewrite mesh_grid_app in Hinj by lia.
          rewrite filter_app in Hinj.
          eapply partial_injective_app_l in Hinj.
          eassumption.
        + unfold injective. propositional.
        + eapply no_dup_filter.
          eapply no_dup_mesh_grid.
        + eapply no_dup_filter.
          eapply no_dup_mesh_grid.
        + simpl. rewrite Nat.add_comm.
          eapply result_has_shape_concat.
          eapply result_has_shape_repeat_gen_pad.
          eauto.
        + lia.
        + subst.
          rewrite <- (Z2Nat.id kz) by lia.
          eapply well_formed_reindexer_padr; try apply Henv; eauto.
        + subst.
          eapply well_formed_allocation_padr;
            try apply Hrdx; try apply Henv; eauto.
        + apply Hrdx.
   - (* PADL *) simpl in *. invert Hsize. eq_size_of. invs'.

        rename H6 into Hk. pose proof Hk as Hk'.
        eapply eval_Zexpr_includes_valuation in Hk'; try apply empty_includes.
        apply eval_Zexpr_Z_eval_Zexpr in Hk'.
        rewrite Hk' in *. invs'. apply eval_Zexpr_Z_eval_Zexpr in Hk.
        
        assert (result_has_shape (V l) (m::sh0)) as Hsh.
        { eapply size_of_eval_expr_result_has_shape; eauto. }
        pose proof Halloc as Halloc1.
        eapply well_formed_allocation_result_V in Halloc1.
        inversion Halloc1 as [a Htmp]. clear Halloc1.
        inversion Htmp as [Heq Hsub]. clear Htmp.

        invert Hpad; eq_size_of; invs'.
        { cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *.
          invert Hsh. rewrite app_nil_r in *.
          rewrite <- gen_pad_cons in *.
          rewrite filter_negb_is_None_result_lookup_Z_option_gen_pad in *.
          unfold lookup_total. rewrite Heq.
          match goal with
          | |- context[reindexer ?x] => destruct (reindexer x) eqn:Heq0
          end.
          {  eapply reindexer_not_empty_vars_in_index in Heq0. propositional.
             apply Hrdx.
             erewrite result_has_shape_result_shape_Z
               by eapply result_has_shape_gen_pad.
             simpl.
             cases (Z.to_nat kz).
             simpl. intro. cups_empty.
             simpl. intro. cups_empty. }
          unfold result_shape_Z in IHeval_expr.
          unfold shape_to_index, shape_to_vars in IHeval_expr. 
          simpl in IHeval_expr.
          rewrite tensor_to_array_delta_gen_pad in *.
          rewrite array_add_empty_r. rewrite add_id by auto.

          eapply IHeval_expr in Heval; eauto.
          2: { eapply well_formed_allocation_result_V in Halloc.
               invert Halloc.
               decomp_well_formed_reindexer.
               propositional.
               unfold partial_injective. simpl. propositional.
               destruct l1; destruct l2; eauto.
               invert H. discriminate.
               invert H. discriminate.
               destruct p1. destruct p2. eapply HeqZlist.
               erewrite <- eq_Z_tuple_index_list_cons_tup.
               erewrite <- eq_Z_tuple_index_list_cons_tup in H.
               propositional. eapply eq_zexpr_add; eauto.
               subst. reflexivity.
               destruct l0. rewrite Hmap. eauto. eauto.
               destruct p1. simpl. rewrite Hmap. reflexivity.
               assumption.
               destruct l0. rewrite Hvarsarg. sets.
               destruct p1. rewrite Hvarsarg. simpl.
               rewrite app_no_dups_empty_r. reflexivity.
               unfold nondestructivity.
               unfold tensor_to_array_delta, tensor_to_array_delta_by_indices.
               simpl. rewrite dom_empty. split; intros. sets.
               eapply lookup_Some_dom in Heq. sets.
               apply Hrdx.
          }
          2: { eapply well_formed_allocation_padl.
               rewrite app_nil_r. eauto.
               econstructor.
               apply Hrdx. lia. apply Hrdx.
               apply Henv. apply Hrdx. apply Hrdx. }
          
          cases (reindexer [((! "?" ! + | kz |)%z, (0 + kz)%Z)]).
          eapply reindexer_not_empty_vars_in_index in Heq1. propositional.
          apply Hrdx. simpl. intro. cups_empty.
          invs'. subst. unfold lookup_total. rewrite Heq.
          rewrite tensor_to_array_delta_empty_tensor.
          rewrite array_add_empty_r. rewrite add_id. propositional. auto.
        }

        cbv [eval_Zexpr_Z_total] in *. rewrite Hk in *.
        eapply IHeval_expr in Heval.
        subst.
        erewrite result_has_shape_result_shape_Z.
        2: { eapply result_has_shape_concat.
             eapply result_has_shape_repeat_gen_pad.
             simpl in *. eassumption. }
        match goal with
        | |- context[reindexer ?x] => destruct (reindexer x) eqn:Heq0
        end.
     { eapply reindexer_not_empty in Heq0. propositional. apply Hrdx.
       simpl.
       cases (Z.to_nat kz + dim)%nat; inversion 1. }
     cases (shape_to_index (result_shape_Z (V l))
                  (shape_to_vars (result_shape_Z (V l)))).
     { eapply shape_to_index_not_empty_Z in Heq1. propositional. }
     unfold lookup_total. rewrite Heq.
     
     destruct (reindexer (let (v, d) := p1 in _)) eqn:Heq2.
     { erewrite result_has_shape_result_shape_Z in Heq1; eauto.      
       unfold result_shape_Z, shape_to_index, shape_to_vars in Heq1.
       simpl in *.
       cases dim; invert Heq1.
       - eapply reindexer_not_empty_vars_in_index in Heq2. propositional.
         apply Hrdx. simpl. intro. cups_empty. 
       - eapply reindexer_not_empty_vars_in_index in Heq2. propositional.
         apply Hrdx. simpl. intro. cups_empty. }
     invs'.
     split; auto. f_equal.
     unfold lookup_total. rewrite Heq.
     f_equal.

     unfold tensor_to_array_delta.
     symmetry.
     erewrite result_has_shape_result_shape_Z.
     2: { eapply result_has_shape_concat.
          eapply result_has_shape_repeat_gen_pad.
          eauto. }
     pose proof filter_pad_l_mesh_grid as H. simpl gen_pad_list in H.
     rewrite H.
     
     erewrite result_has_shape_result_shape_Z by eauto.
     eapply eq_tensor_to_array_delta_by_indices_shuffle
       with (shuffle:=fun l1 : list Z =>
                        match l1 with
                        | [] => l1
                        | x1 :: xs => (x1 + kz)%Z :: xs
                        end).
        + intros.
          repeat decomp_index.
          pose proof result_lookup_Z_option_concat_l.
          simpl gen_pad_list in H5. rewrite H5. reflexivity. lia. lia.
        + intros.
          repeat decomp_index.
          repeat rewrite map_cons.
          erewrite eq_partial_interpret_reindexer_padl; eauto.
          apply Henv. apply Hrdx. apply Hrdx. apply Hrdx. apply Hrdx.
        + intros.
          repeat decomp_index.
          eapply in_map_iff. eexists (z::x0).
          propositional.
          eapply filter_In. propositional.
          repeat decomp_goal_index.
          propositional. lia.
        + intros ? H14.
          eapply in_map_iff in H14. invs.
          repeat decomp_index.          
          eexists (z::x1).
          propositional.
          eapply filter_In. propositional.
          repeat decomp_goal_index. propositional. lia.
        + assert (dim = 0 \/ dim <> 0) as [H14|H14] by lia.
          { rewrite H14. simpl.
            unfold partial_injective. propositional. simpl in *. contradiction. }
          decomp_well_formed_reindexer.
          eapply partial_injective_padl; eauto.
          apply Henv.
        + decomp_well_formed_reindexer.
          erewrite result_has_shape_result_shape_Z in Hinj.
          2: { eapply result_has_shape_concat.
               eapply result_has_shape_repeat_gen_pad.
               simpl in Hsh. eauto. }
          pose proof filter_pad_l_mesh_grid as H8.
          simpl gen_pad_list in H8.
          rewrite H8 in Hinj.
          clear H8.
          apply Hinj.
          
          eapply result_has_shape_concat.
          eapply result_has_shape_repeat_gen_pad. eauto.
          lia.
        + unfold injective. propositional.
          repeat decomp_index. invs'. f_equal. lia.
        + eapply no_dup_filter.
          eapply no_dup_mesh_grid.
        + eapply no_dup_injective_map.
          unfold injective. propositional.
          repeat decomp_index. invs'. f_equal. lia.
          eapply no_dup_filter.
          eapply no_dup_mesh_grid.
        + simpl.
          simpl. eapply result_has_shape_concat.
          eapply result_has_shape_repeat_gen_pad. auto.
        + lia.
        + eauto.
        + eauto.
        + decomp_well_formed_reindexer. subst.
          eapply well_formed_allocation_result_V in Halloc. invert Halloc.
          invs'.
          eapply well_formed_reindexer_padl; eauto. apply Henv. eauto.
        + decomp_well_formed_reindexer. subst.
          eapply well_formed_allocation_padl; eauto. apply Henv.
        + eauto.
        + eauto.
        + eauto.
        + apply Hrdx.
   - (* SCALAR *)
     simpl in *.     
     invert Heval.
     + unfold result_shape_Z in *. simpl in *.
       unfold shape_to_index, shape_to_vars in *.
       simpl in *. rewrite H10 in *. invs.
       rewrite H9 in *. invs.
       split. auto.
       
       eapply eval_Sexpr_eval_Sstmt in H8; eauto. subst.
       eapply Hrdx in H9. subst. f_equal. ring. reflexivity.
       eapply lookup_Some_dom in H9. unfold well_formed_environment in *.
       sets.
     + cases (reindexer
                (shape_to_index
                   (result_shape_Z (S r))
                   (shape_to_vars (result_shape_Z (S r))))).
       { unfold well_formed_allocation in Halloc. rewrite Heq in *.
         invs.
         eapply lookup_Some_dom in H0,H10.
         unfold well_formed_environment in Henv. invs. sets. }
       unfold lookup_total. rewrite H10.
       unfold partial_interpret_reindexer. simpl.
       eapply eval_Zexpr_Z_eval_Zexpr in H11.
       simpl in *. unfold tensor_to_array_delta.
       unfold tensor_to_array_delta_by_indices.
       unfold result_shape_Z in *. unfold shape_to_index in *.
       simpl in *.
       cases r.
       2: { simpl in *. rewrite array_add_empty_r. propositional.
            decomp_well_formed_reindexer.
            unfold nondestructivity in Hnondstr. invert Hnondstr. clear H1.
            invert H.
            - cases r; try discriminate.
            - cases r; try discriminate.
            - cases r1; cases r2; simpl in *; try discriminate.
            - cases r1; cases r2; simpl in *; try discriminate.
            - cases r1; cases r2; simpl in *; try discriminate.
            - cases r1; cases r2; simpl in *; try discriminate. }
       simpl.
       rewrite array_add_empty_l.
       unfold index_to_partial_function.
       decomp_well_formed_reindexer.
       rewrite map_id.
       eapply vars_of_reindexer_subseteq_map_partially_eval_Z_tup in Hvarsub.
       eapply forall_no_vars_eval_Zexpr_Z_total with (v:=$0) in Hvarsub.
       rewrite map_fst_map_partially_eval_Z_tup in *.
       rewrite map_eval_Zexpr_Z_total_map_partially_eval_Zexpr_join in *.
       
       propositional.
       f_equal.
       eapply eval_Zexpr_Z_eval_Zexpr in H11.
       rewrite partially_eval_Zexpr_empty_valuation in H11.
       rewrite partially_eval_Zexpr_flatten_shape_index in H11.
       erewrite eval_Zexpr_Z_flatten_index_flatten in H11.
       2: { eauto. }
       invs.
       rewrite join_empty_r in *.
       rewrite map_eval_Zexpr_Z_tup_total_map_partially_eval_Z_tup.
       rewrite eval_Zexprlist_map_match_fst_map_eval_Zexpr_Z_tup_total in *;
         eauto.
       rewrite eval_Zexprlist_map_match_snd_map_eval_Zexpr_Z_tup_total in *;
         eauto.
       unfold array_add.
       rewrite merge_add2.
       2: { intros. cases x; discriminate. }
       2: { rewrite dom_empty. sets. }
       rewrite H12. 
       rewrite merge_empty2.
       f_equal. 
       eapply eval_Sexpr_eval_Sstmt in H.
       2: { eauto. }
       2: { eauto. }
       rewrite H.
       eapply Hnondstr with
         (x:=flatten
               (map snd (reindexer []))
               (map (eval_Zexpr_Z_total v) (map fst (reindexer []))))
         in H10; eauto.
       2: { eapply lookup_Some_dom in H10.
            unfold well_formed_environment in *. sets. }
       2: { clear H0. unfold result_shape_Z. simpl.
            unfold tensor_to_array_delta. simpl.
            unfold tensor_to_array_delta_by_indices. simpl.
            rewrite array_add_empty_l. unfold shape_to_index,shape_to_vars.
            simpl. rewrite dom_add. rewrite dom_empty. rewrite cup_empty_r.
            rewrite map_id.
            rewrite map_eval_Zexpr_Z_tup_total_map_partially_eval_Z_tup.
            rewrite eval_Zexprlist_map_match_snd_map_eval_Zexpr_Z_tup_total;
              eauto.
            rewrite eval_Zexprlist_map_match_fst_map_eval_Zexpr_Z_tup_total;
              eauto.
            sets. }
       rewrite H10 in *. invert H12. ring.
       intros; cases x; auto.
     + unfold well_formed_allocation in Halloc.
       unfold result_shape_Z in *. simpl in *.
       unfold shape_to_index, shape_to_vars in *.
       simpl in *. rewrite H10 in *. invs.
       rewrite H9 in *. invs.
       split. auto.
       eapply eval_Sexpr_eval_Sstmt in H8; eauto. subst.
       f_equal. ring.
     + cases (reindexer
                (shape_to_index
                   (result_shape_Z (S r))
                   (shape_to_vars (result_shape_Z (S r))))).
       { unfold well_formed_allocation in Halloc. rewrite Heq in *.
         invs.
         eapply lookup_Some_dom in H0,H10.
         unfold well_formed_environment in Henv. invs. sets. }
       unfold lookup_total. rewrite H10.
       unfold partial_interpret_reindexer. simpl.
       eapply eval_Zexpr_Z_eval_Zexpr in H11.
       simpl in *. unfold tensor_to_array_delta.
       unfold tensor_to_array_delta_by_indices.
       unfold result_shape_Z in *. unfold shape_to_index in *.
       simpl in *.
       cases r.
       2: { eapply eval_Sexpr_eval_Sstmt in H; eauto.
            subst.
            propositional.
            simpl.
            rewrite array_add_empty_r.
            f_equal.
            unfold well_formed_allocation in *.
            unfold result_shape_Z, shape_to_index, shape_to_vars in *.
            simpl in *. rewrite Heq in *. invs. rewrite H0 in *. invs.
            rewrite add_arr_id. auto. rewrite H12. f_equal. ring. }
       simpl.
       rewrite array_add_empty_l.
       unfold index_to_partial_function.
       decomp_well_formed_reindexer.
       rewrite map_id.
       eapply vars_of_reindexer_subseteq_map_partially_eval_Z_tup in Hvarsub.
       eapply forall_no_vars_eval_Zexpr_Z_total with (v:=$0) in Hvarsub.
       rewrite map_fst_map_partially_eval_Z_tup in *.
       rewrite map_eval_Zexpr_Z_total_map_partially_eval_Zexpr_join in *.
       
       propositional.
       f_equal.
       eapply eval_Zexpr_Z_eval_Zexpr in H11.
       rewrite partially_eval_Zexpr_empty_valuation in H11.
       rewrite partially_eval_Zexpr_flatten_shape_index in H11.
       erewrite eval_Zexpr_Z_flatten_index_flatten in H11.
       2: { eauto. }
       invs.
       rewrite join_empty_r in *.
       rewrite map_eval_Zexpr_Z_tup_total_map_partially_eval_Z_tup.
       rewrite eval_Zexprlist_map_match_fst_map_eval_Zexpr_Z_tup_total in *;
         eauto.
       rewrite eval_Zexprlist_map_match_snd_map_eval_Zexpr_Z_tup_total in *;
         eauto.
       unfold array_add.
       rewrite merge_add2.
       2: { intros. cases x; discriminate. }
       2: { rewrite dom_empty. sets. }
       rewrite H12. 
       rewrite merge_empty2.
       rewrite Rplus_comm.
       f_equal. f_equal.
       eapply eval_Sexpr_eval_Sstmt in H.
       rewrite H. reflexivity. eauto. eauto.
       intros; cases x; auto.
Qed.

Theorem lower_correct :
  forall e,
    forall r,
      (* functional evaluation of ATL *)
      eval_expr $0 $0 $0 e r ->
      forall l, size_of e l ->
      forall p st h st' h' asn,
        (h,st) =
          match (shape_to_index
                   (result_shape_Z r)
                   (shape_to_vars (result_shape_Z r))) with
          | [] => ($0,$0 $+ (p,0%R))
          | _ => (alloc_array_in_heap (result_shape_nat r) $0 p,$0)
          end ->
        (* imperative evaluation of lowering *)
        eval_stmt $0 st h (lower e (fun l => l) p asn $0) st' h' ->
        ~ p \in vars_of e ->
        forall pads,
          has_pad $0 $0 $0 e pads ->
        match (fun l => l) (shape_to_index
                 (result_shape_Z r)
                 (shape_to_vars (result_shape_Z r))) with
        | [] => h' = h
           /\ st' = st $+ (p, match st $? p with
                              | Some r => r
                              |_ => 0%R
                              end + match r with
                                    | S (SS s) => s
                                    | _ => 0%R
                                    end)%R
        | _ =>
            (h' = h $+ (p,
                         array_add
                           (h $! p)
                           (tensor_to_array_delta
                              (partial_interpret_reindexer (fun l => l)
                                                   (result_shape_Z r) $0) r))
             /\ st' = st)
        end.
Proof.
  intros.
  eapply lower_correct_weak; eauto.
  - unfold result_shape_Z, shape_to_index, shape_to_vars in *.
    cases r.
    + simpl in *. invert H1.
      unfold well_formed_environment.
      rewrite dom_add. 
      repeat rewrite dom_empty.
      repeat rewrite cup_empty_r.
      repeat rewrite cap_empty_r.
      split. sets.
      split. auto.
      split. sets. 
      split. sets.
      split. sets.
      split. sets.
      auto.
    + simpl in *. cases v.
      * invert H1.
        unfold alloc_array_in_heap. simpl.
        unfold well_formed_environment.
        rewrite dom_add. 
        repeat rewrite dom_empty.
        repeat rewrite cup_empty_r.
        repeat rewrite cap_empty_r.
        split. sets.
        split. auto.
        split. sets. 
        split. sets.
        split. sets.
        split. sets.
        auto.
      * invert H1.
        unfold alloc_array_in_heap. simpl.
        unfold well_formed_environment.
        rewrite dom_add. 
        repeat rewrite dom_empty.
        repeat rewrite cup_empty_r.
        repeat rewrite cap_empty_r.
        split. sets.
        split. auto.
        split. sets. 
        split. sets.
        split. sets.
        split. sets.
        auto.
  - unfold well_formed_reindexer.
    propositional.
    + eapply partial_injective_id_reindexer. rewrite dom_empty. sets.
    + simpl. sets.
    + simpl. sets.
    + destruct r.
      * simpl in *. invert H1.
        unfold nondestructivity. rewrite lookup_empty. rewrite dom_add.
        rewrite dom_empty. rewrite cup_empty_r. rewrite lookup_add_eq by auto.
        rewrite dom_empty.
        split; intros. discriminate. invert H1. eauto.
      * destruct (shape_to_index (result_shape_Z (V v))
                    (shape_to_vars (result_shape_Z (V v)))) eqn:ee.
        eapply shape_to_index_not_empty_Z in ee. propositional.
        invert H1.
        unfold nondestructivity. rewrite lookup_empty.
        unfold alloc_array_in_heap. rewrite dom_add.
        repeat rewrite dom_empty. rewrite cup_empty_r.
        rewrite lookup_add_eq by auto.
        split; intros. invert H1.
        2: { discriminate. }
        destruct v. simpl in *.
        unfold tensor_to_array_delta in H7. simpl in H7.
        unfold tensor_to_array_delta_by_indices in H7. simpl in H7.
        rewrite dom_empty in *. sets.
        pose proof (lookup_alloc_array
                      (fold_left mul (Datatypes.S (length v) ::
                                        result_shape_nat r) 1) x).
        invert H1; eauto.
        eapply lookup_None_dom in H5.
        rewrite dom_alloc_array in H5.
        unfold tensor_to_array_delta in H7.
        unfold tensor_to_array_delta_by_indices in H7.
        erewrite partial_dom_fold_left_array_add in H7.
        rewrite dom_empty in H7. rewrite cup_empty_r in H7.
        2: { eapply partial_injective_id_reindexer; eauto.
             rewrite dom_empty. sets. }
        exfalso. apply H5.
        erewrite <- In_iff_in. eapply In_iff_in in H7.
        eapply in_extract_Some in H7. eapply in_map_iff in H7. invs.
        rewrite filter_idempotent in H8.
        erewrite partial_interpret_reindexer_id_flatten in H7.
        2: { decomp_index. eauto. }
        2: { rewrite dom_empty. sets. }
        invs'.
        unfold result_shape_Z. simpl result_shape_nat.
        erewrite Z_of_nat_fold_left_mul.
        eapply in_mesh_grid_flatten_in_range.
        2: { unfold result_shape_Z in *. simpl result_shape_nat in *.
             decomp_index. eauto. }
        eapply Forall_map. eapply Forall_forall. intros. lia.
  - unfold result_shape_Z, shape_to_index, shape_to_vars in *.
    cases r.
    + simpl in *. invert H1. unfold well_formed_allocation.
      simpl. rewrite lookup_add_eq by auto. eauto.
    + cases v.
      * simpl in *. invert H1. unfold well_formed_allocation.
        simpl. unfold alloc_array_in_heap in *. simpl.
        rewrite lookup_add_eq by auto.
        eexists. split. eauto. sets.
      * invert H1.
        unfold well_formed_allocation.
        unfold shape_to_index, shape_to_vars.
        set (mesh_grid (map Z.of_nat (result_shape_nat (V (r :: v))))).
        subst l0. unfold alloc_array_in_heap.
        rewrite lookup_add_eq by auto.
        eexists. split. reflexivity.
        rewrite dom_alloc_array.
        rewrite constant_partial_interpret_reindexer_id_flatten_filter.
        2: { rewrite dom_empty. sets. }
        simpl result_shape_nat.
        rewrite Z_of_nat_fold_left_mul.
        eapply subseteq_transitivity.
        eapply constant_map_filter_subseteq.
        eapply constant_map_flatten_zrange.
  - unfold contexts_agree.
    intros. repeat rewrite lookup_empty. propositional; discriminate.
Qed.
