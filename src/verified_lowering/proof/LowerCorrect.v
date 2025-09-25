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
       rewrite map_length; rewrite length_nat_range_rec;
       eapply length_mesh_grid_indices; eassumption : reindexers.
Arguments flatten : simpl nomatch.
            
Theorem lower_correct_weak :
  forall e,
    constant_nonneg_bounds e ->
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
  intros e Hconst sh v ec r.
  induct 1; intros ls Hsize p st h st' h' reindexer asm
                   Heval Henv Hrdx Halloc Hctx pads g Hpad Hrelate.
  12: { (* SPLIT *) simpl in *. invert Hsize. simpl in Hconst. invert Hconst.
     invert H2. pose proof H3 as Hconst.
     assert (result_has_shape (V l)
                              (map Z.to_nat
                                   (map (eval_Zexpr_Z_total $0) (n::l0))))
       as Hsh.
     { eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H3.
       eapply H3. eassumption. eauto. }

     pose proof Hsh as Hsh'.
     repeat rewrite map_cons in *.
     eapply result_has_shape_split_result
       with (k:=(Z.to_nat (eval_Zexpr_Z_total $0 k))) in Hsh'.
     2: { invert Hpad. lia. }

     invert Hpad.     
     eapply IHeval_expr in H7.
     2: { eauto. }
     2: { eauto. }
     2: { eauto. }
     2: { eauto. }
     2: { eapply well_formed_allocation_result_V in Halloc.
          2: { apply Hrdx. } invs.
          eapply well_formed_reindexer_split; eauto.
          apply Henv.
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto.
          eq_size_of. invert H2.
          eapply constant_nonneg_bounds_size_of_nonneg in H3; eauto.
          2: { eapply forall_no_vars_eval_Zexpr_Z_total with (v:=$0).
               eapply constant_nonneg_bounds_size_of_no_vars. eauto. eauto. }
          invert H3. lia.
     }
     2: { eapply well_formed_allocation_split; eauto.
          apply Hrdx.
          eq_size_of. invert H2.
          eapply constant_nonneg_bounds_size_of_nonneg in H3; eauto.
          2: { eapply forall_no_vars_eval_Zexpr_Z_total with (v:=$0).
               eapply constant_nonneg_bounds_size_of_no_vars. eauto. eauto. }
          invert H3. lia.
          apply Hrdx.
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto.
          eq_size_of. invert H2.          
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total.
          eapply constant_nonneg_bounds_size_of_no_vars in H3; eauto.
          invert H3. eauto. apply Henv. apply Hrdx. apply Hrdx. }
     2: { eauto. }
     2: { eauto. }
     
     eq_size_of. invert H2.
     cases (shape_to_index (result_shape_Z (V l))
                           (shape_to_vars (result_shape_Z (V l)))).
     { eapply shape_to_index_not_empty_Z in Heq. propositional. }
     cases (reindexer
              (let (v, d) := p0 in
               ((v / k)%z, (d // k)%z) :: ((ZMod v k)%z, k) :: l0)).
     { unfold result_shape_Z,shape_to_index, shape_to_vars in Heq.
       simpl in Heq. cases l.
       - simpl in *. invert Heq.
         eapply reindexer_not_empty_vars_in_index in Heq0.
         2: { apply Hrdx. }
         2: { simpl. repeat rewrite constant_app_no_dups.
              repeat rewrite <- union_constant.
              unfold not. intros.
              eapply cup_empty in H2. invert H2.
              eapply cup_empty in H6. invert H6.
              eapply cup_empty in H8. invert H8.
              eapply cup_empty in H2. invert H2.
              eapply constant_not_empty in H8. contradiction.
              inversion 1. }
         propositional.
       - simpl in *. invert Heq.
         eapply reindexer_not_empty_vars_in_index in Heq0.
         2: { apply Hrdx. }
         2: { simpl. repeat rewrite constant_app_no_dups.
              repeat rewrite <- union_constant.
              unfold not. intros.
              eapply cup_empty in H2. invert H2.
              eapply cup_empty in H6. invert H6.
              eapply cup_empty in H8. invert H8.
              eapply cup_empty in H2. invert H2.
              eapply constant_not_empty in H8. contradiction.
              inversion 1. }
         propositional. }
     
     invert H7.
     cases (reindexer
      (shape_to_index
         (result_shape_Z (V (split_result (Z.to_nat (eval_Zexpr_Z_total $0 k)) l)))
         (shape_to_vars
            (result_shape_Z
               (V (split_result (Z.to_nat (eval_Zexpr_Z_total $0 k)) l)))))).
     { eapply reindexer_not_empty in Heq1. propositional.
       apply Hrdx. erewrite result_has_shape_result_shape_Z.
       2: { eauto. }
       cases (Z.to_nat (eval_Zexpr_Z_total $0 m) //n
                       (Z.to_nat (eval_Zexpr_Z_total $0 k))).
       simpl. inversion 1.
       simpl. inversion 1. }
     pose proof Halloc.
     eapply well_formed_allocation_result_V in H2.
     invs.
     unfold lookup_total. rewrite H2. split; auto.
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
     cases (Z.to_nat (eval_Zexpr_Z_total $0 m)).
     {  invert Hsh. }
     rewrite filter_until_0_cons by lia.
     symmetry.
     eapply eq_tensor_to_array_delta_by_indices_shuffle
       with (shuffle:= fun l =>
                         match l with
                         | x::xs => (x/eval_Zexpr_Z_total $0 k)%Z
                                    ::(Zmod x (eval_Zexpr_Z_total $0 k))%Z::xs
                         | _ => l
                         end).
        - intros. cases x0. propositional.
          rewrite map_cons in *.
          repeat decomp_index.
          rewrite <- (Z2Nat.id (eval_Zexpr_Z_total $0 k)) at 1 by lia. 
          rewrite <- (Z2Nat.id (eval_Zexpr_Z_total $0 k)) at 2 by lia.
          erewrite result_lookup_Z_option_split. reflexivity.
          repeat decomp_index. eauto. lia. apply H6. lia.
          rewrite Nat2Z.id by lia. eauto.
        - rewrite map_cons. intros. cases x0. propositional.
          repeat decomp_index.
          rewrite <- Heq2.
          rewrite <- Z2Nat_div_distr by lia.
          erewrite <- eq_partial_interpret_reindexer_split;
            try apply Henv; try apply Hrdx; try lia; eauto.
          2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. }
          2: { repeat decomp_index. eauto. }
          2: { repeat decomp_index. lia. }
          rewrite Z2Nat.id by lia. rewrite filter_until_0_cons by lia.
          rewrite map_cons. rewrite Z2Nat.id by lia. auto.
        - rewrite <- Heq2. repeat rewrite map_cons.
          intros. repeat decomp_index.
          eapply filter_In. split.
          repeat decomp_goal_index.
          split. split.
          eapply Z.div_pos. lia. lia.
          rewrite <- Z2Nat_div_distr by lia.
          rewrite Z2Nat.id.
          2: { eapply div_nonneg. lia. lia. }
          eapply floor_lt_ceil_mono_l; lia.
          decomp_goal_index. split.
          rewrite Z2Nat.id by lia. eapply Z.mod_pos_bound. lia.
          eauto.
          rewrite <- H11.
          f_equal. f_equal.
          rewrite <- (Z2Nat.id (eval_Zexpr_Z_total $0 k)) at 1 by lia.
          rewrite <- (Z2Nat.id (eval_Zexpr_Z_total $0 k)) at 2 by lia.
          erewrite result_lookup_Z_option_split. reflexivity.
          eauto. lia. apply H6. lia. rewrite Z2Nat.id.
          rewrite Heq2. eauto. lia.
        - rewrite <- Heq2. repeat rewrite map_cons.
          intros. repeat decomp_index.
          eexists ((z*(eval_Zexpr_Z_total $0 k) + z0)%Z::x0).
          rewrite Z.div_add_l by lia.
          rewrite Z.div_small by lia. rewrite Z.add_0_r.
          pose proof Z.add_mul_mod_distr_r.
          specialize H12 with (b:=1%Z) (c:= eval_Zexpr_Z_total $0 k).
          rewrite Z.mul_1_l in *.
          rewrite H12.
          rewrite Z.mod_1_r. split. auto.
          eapply filter_In. split.
          repeat decomp_goal_index. split.
          split. lia. rewrite Z2Nat.id by lia.
          rewrite <- Z2Nat_div_distr in * by lia.
          rewrite Z2Nat.id in * by lia.
          eapply result_lookup_Z_option_split_true. eauto.
          lia. lia. lia. eauto. rewrite Heq2. eauto. 
          decomp_goal_index. eauto.
          rewrite <- H11. f_equal. f_equal.
          erewrite <- result_lookup_Z_option_split
            with (k:=Z.to_nat (eval_Zexpr_Z_total $0 k)).
          2: { eauto. }
          2: { lia. }
          3: lia.
          3: { rewrite <- Heq2 in *. eauto. }
          all: try lia.
          2: { rewrite <- Z2Nat_div_distr in * by lia.
               rewrite Z2Nat.id in * by lia.
               eapply result_lookup_Z_option_split_true. eauto.
               lia. lia. lia. eauto. rewrite Heq2. eauto.  }
          rewrite Z2Nat.id by lia.
          rewrite Z.div_add_l by lia. rewrite Z.div_small by lia.
          rewrite Z.add_0_r.
          pose proof Z.add_mul_mod_distr_r.
          specialize H14 with (b:=1%Z) (c:= eval_Zexpr_Z_total $0 k).
          rewrite Z.mul_1_l in *.
          rewrite H14.
          rewrite Z.mod_1_r. reflexivity. lia. lia. lia.
        - replace (map Z.of_nat
             (Datatypes.S n
                          :: filter_until
                          (map Z.to_nat (map (eval_Zexpr_Z_total $0) sh0)) 0))
            with
            (result_shape_Z (V (r0::l))).
          2: { erewrite result_has_shape_result_shape_Z by eauto.
               reflexivity. }
          eapply partial_injective_split. apply Hrdx.
          rewrite <- Heq2 in *. eauto. apply Henv.
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
          apply Hrdx. apply Hrdx. apply Hrdx. apply Hrdx. lia. lia.
        - replace (map Z.of_nat
             (filter_until
                (Datatypes.S n //n (Z.to_nat (eval_Zexpr_Z_total $0 k))
                 :: Z.to_nat (eval_Zexpr_Z_total $0 k)
                 :: map Z.to_nat (map (eval_Zexpr_Z_total $0) sh0)) 0)) with
            (result_shape_Z
               (V (split_result (Z.to_nat (eval_Zexpr_Z_total $0 k)) (r0 :: l)))).
          apply Hrdx.
          erewrite result_has_shape_result_shape_Z.
          2:{ eapply result_has_shape_split_result. lia. eauto. }
          reflexivity.
        - unfold injective. propositional.
          repeat decomp_index.
          repeat rewrite map_cons in *. repeat decomp_index.
          invert H13.
          rewrite (Z.div_mod z (eval_Zexpr_Z_total $0 k)).
          rewrite (Z.div_mod z0 (eval_Zexpr_Z_total $0 k)).
          rewrite H18. rewrite H19. reflexivity. lia. lia.
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
     clear Heq. invs.
     rewrite H7. rewrite add_id. auto. auto.
   - (* STEPPING GEN *)
     simpl in Heval.
     unfold lookup_total in *.
     invert Hsize. pose proof H11 as Hsize. clear H11.
     assert (eq_zexpr lo (|eval_Zexpr_Z_total $0 lo|)%z) as Heqlo.
     { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total.
       invert Hconst. eauto. }
     assert (eq_zexpr hi (|eval_Zexpr_Z_total $0 hi|)%z) as Heqhi.
     { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total.
       invert Hconst. invert H7. eauto. }
     assert (loz = eval_Zexpr_Z_total $0 lo).
     { invert Heqlo. eapply eval_Zexpr_Z_eval_Zexpr in H. eapply H6 in H.
       invert H. eauto. }
     assert (hiz = eval_Zexpr_Z_total $0 hi).
     { invert Heqhi. eapply eval_Zexpr_Z_eval_Zexpr in H0. eapply H7 in H0.
       invert H0. eauto. }
     subst.
     
     assert (result_has_shape (V (r::l)) (result_shape_nat (V(r::l)))) as Hsh.
     { assert (eval_expr sh v ec (Gen i lo hi body) (V (r::l))).
       econstructor; eauto.
       eapply result_has_shape_self.       
       eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
       3: eassumption. eauto.
       econstructor. eauto. }
     pose proof Halloc as Halloc1.
     eapply well_formed_allocation_result_V in Halloc; try apply Hrdx.
     invs.
     cases (reindexer
      (shape_to_index (result_shape_Z (V (r :: l)))
                      (shape_to_vars (result_shape_Z (V (r :: l)))))).
     eapply reindexer_not_empty in Heq; propositional; try apply Hrdx;
       discriminate.
     erewrite <- tensor_to_array_delta_cons
       with (i:=i) (hi:=hi) (lo:=lo);
         try eapply result_shape_gen_length in H5;
       eauto; simpl; try rewrite H; try rewrite H0; try reflexivity; try lia.
     2: apply Hrdx.
     2: apply Hrdx.
     2: apply Hrdx.
     2: apply Hrdx.
     2: apply Hrdx.
     2: apply Henv.
     2: { unfold shape_to_vars. unfold not. intros. eapply H3.
          eapply in_map_iff in H6. invs.
          eapply var_generation_contains_substring. }
     invert Heval.
     2: { rewrite H,H0 in *. invert H16. invert H17. lia. }
     rewrite H,H0 in *. invert H12. invert H15.
     invert Hpad.

     cases k.
     2: { eapply IHeval_expr1 in H19.
          cases (reindexer
                   (((! i ! - lo)%z, (hi - lo)%z)
                      :: shape_to_index (result_shape_Z r)
                      (shape_to_vars (result_shape_Z r)))).
          { eapply reindexer_not_empty_vars_in_index in Heq0; try apply Hrdx.
            propositional.
            simpl. unfold app_no_dups.
            rewrite <- union_constant.
            unfold not. intros.
            eapply cup_empty in H6. invs.
            eapply cup_empty in H9. invs.
            eapply cup_empty in H6. invs.
            eapply constant_not_empty in H9. propositional. inversion 1. }
          invs. rewrite H7 in *. clear Heq0. clear Heq.
          * clear IHeval_expr1. pose proof IHeval_expr2. simpl in H6.
            unfold shift_top_dim_reindexer.
            specialize H6 with
              (p:=p)
              (reindexer:= shift_top_dim_reindexer reindexer)
              (h:=(h $+ (p,
                          array_add
                            x
                            (tensor_to_array_delta
                               (partial_interpret_reindexer
                                  (fun l =>
                                     reindexer
                                       (((! i ! - lo)%z,(hi - lo)%z) :: l))
                                  (result_shape_Z r)
                                  (v $+ (i, eval_Zexpr_Z_total $0 lo))) r)))).
            rewrite lookup_add_eq in * by auto.
            rewrite add_overwrite in H6.
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
              - eapply reindexer_not_empty_vars_in_index in H10. propositional.
                apply Hrdx. simpl.
                repeat rewrite app_no_dups_empty_r. repeat rewrite cup_empty_r.
                unfold not. intros.
                eapply constant_not_empty in H9. propositional. inversion 1.
              - eapply reindexer_not_empty_vars_in_index in H10. propositional.
                apply Hrdx. simpl.
                repeat rewrite app_no_dups_empty_r. repeat rewrite cup_empty_r.
                unfold not. intros.
                eapply cup_empty in H9. invs.
                eapply constant_not_empty in H11. propositional. inversion 1. }
eapply H6 with (st:=st) (st':=st') (asn:=asm).
         -- invert Hconst. simpl. invs. rewrite H9,H11. propositional.
            rewrite eval_Zexpr_Z_total_add_distr.
            simpl. unfold eval_Zexpr_Z_total at 3. simpl. lia.
            eauto. eauto.
         -- econstructor. eauto.
         -- clear IHeval_expr2.
            invs.
            unfold shift_top_dim_reindexer.
            eapply eq_eval_stmt_for.
            eassumption. simpl. rewrite H. reflexivity.
            rewrite H0. eauto.
            intros.
            eapply eq_eval_stmt_lower_eq_reindexers;
              simpl; intros; decomp_well_formed_reindexer.
            ++ eassumption.
            ++ invs. eapply HeqZlist.
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
               eapply eq_zexpr_add_sub_id.
               eauto.
               eapply eq_zexpr_comm.
               eapply eq_zexpr_transitivity.
               eapply eq_zexpr_sub_sub_distr.
               eapply eq_zexpr_transitivity.
               eapply eq_zexpr_sub.
               eapply eq_zexpr_id. auto.
               eapply eq_zexpr_add_sub_id.
               eauto.
         -- decomp_well_formed_environment.
            unfold well_formed_environment.
            split. auto.
            ++ rewrite dom_add.
               eapply lookup_Some_dom in H7.
               unfold well_formed_environment in *. invs.
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
         -- unfold well_formed_environment in *. invs.
            eapply well_formed_reindexer_shift_top_dim_reindexer;
              eauto.
         -- eapply well_formed_allocation_shift_top_dim_reindexer;
              try apply Hrdx; try apply Henv; eauto.
         -- eapply contexts_agree_add_heap; try apply Henv; auto.
         -- eapply HasPadGen with (k:=k) (c:=c) (ll:=ll) (rr:=rr).
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 3. simpl. lia.
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 3. simpl. lia.
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 3. simpl. lia.
            eauto.
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 2. simpl.
            unfold eval_Zexpr_Z_total at 3. simpl.
            intros. apply H22. lia. 
            intros. eapply H24. lia.
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 2. simpl.
            unfold eval_Zexpr_Z_total at 4. simpl.
            intros. apply H25. lia. lia.
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 3. simpl. lia.
         -- eauto.
     * invert Hconst. propositional.
     * eassumption.
     * eapply well_formed_environment_add_valuation.
       simpl in Henv.
       auto. auto. auto.
     * eapply well_formed_allocation_result_V in Halloc1.
       eapply well_formed_reindexer_eval0. eassumption.
       eapply Henv.
       eauto. eauto. 
       unfold not. intros.
       eapply shape_to_vars_contains_substring in H6.
       propositional.
       simpl in *. lia. auto. auto. eauto.
       lia. eauto. apply Hrdx.
     * eapply well_formed_allocation_eval_step;
         try apply Halloc; eauto; try apply Hrdx; try apply Henv.
     * eauto.
     * eapply H25. lia. lia.
     * eauto.
}

     (* k = 0, no left padding *)
     cases ll.
     2: { eapply IHeval_expr1 in H19.
          cases (reindexer
                   (((! i ! - lo)%z, (hi - lo)%z)
                      :: shape_to_index (result_shape_Z r)
                      (shape_to_vars (result_shape_Z r)))).
          { eapply reindexer_not_empty_vars_in_index in Heq0; try apply Hrdx.
            propositional.
            simpl. unfold app_no_dups.
            rewrite <- union_constant.
            unfold not. intros.
            eapply cup_empty in H6. invs.
            eapply cup_empty in H9. invs.
            eapply cup_empty in H6. invs.
            eapply constant_not_empty in H9. propositional. inversion 1. }
          invs. rewrite H7 in *. clear Heq0. clear Heq.
          * clear IHeval_expr1. pose proof IHeval_expr2. simpl in H6.
            unfold shift_top_dim_reindexer.
            specialize H6 with
              (p:=p)
              (reindexer:= shift_top_dim_reindexer reindexer)
              (h:=(h $+ (p,
                          array_add
                            x
                            (tensor_to_array_delta
                               (partial_interpret_reindexer
                                  (fun l =>
                                     reindexer
                                       (((! i ! - lo)%z,(hi - lo)%z) :: l))
                                  (result_shape_Z r)
                                  (v $+ (i, eval_Zexpr_Z_total $0 lo))) r)))).
            rewrite lookup_add_eq in * by auto.
            rewrite add_overwrite in H6.
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
              - eapply reindexer_not_empty_vars_in_index in H10. propositional.
                apply Hrdx. simpl.
                repeat rewrite app_no_dups_empty_r. repeat rewrite cup_empty_r.
                unfold not. intros.
                eapply constant_not_empty in H9. propositional. inversion 1.
              - eapply reindexer_not_empty_vars_in_index in H10. propositional.
                apply Hrdx. simpl.
                repeat rewrite app_no_dups_empty_r. repeat rewrite cup_empty_r.
                unfold not. intros.
                eapply cup_empty in H9. invs.
                eapply constant_not_empty in H11. propositional. inversion 1. }
eapply H6 with (st:=st) (st':=st') (asn:=asm).
         -- invert Hconst. simpl. invs. rewrite H9,H11. propositional.
            rewrite eval_Zexpr_Z_total_add_distr.
            simpl. unfold eval_Zexpr_Z_total at 3. simpl. lia.
            eauto. eauto.
         -- econstructor. eauto.
         -- clear IHeval_expr2.
            invs.
            unfold shift_top_dim_reindexer.
            eapply eq_eval_stmt_for.
            eassumption. simpl. rewrite H. reflexivity.
            rewrite H0. eauto.
            intros.
            eapply eq_eval_stmt_lower_eq_reindexers;
              simpl; intros; decomp_well_formed_reindexer.
            ++ eassumption.
            ++ invs. eapply HeqZlist.
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
               eapply eq_zexpr_add_sub_id.
               eauto.
               eapply eq_zexpr_comm.
               eapply eq_zexpr_transitivity.
               eapply eq_zexpr_sub_sub_distr.
               eapply eq_zexpr_transitivity.
               eapply eq_zexpr_sub.
               eapply eq_zexpr_id. auto.
               eapply eq_zexpr_add_sub_id.
               eauto.
         -- decomp_well_formed_environment.
            unfold well_formed_environment.
            split. auto.
            ++ rewrite dom_add.
               eapply lookup_Some_dom in H7.
               unfold well_formed_environment in *. invs.
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
         -- unfold well_formed_environment in *. invs.
            eapply well_formed_reindexer_shift_top_dim_reindexer;
              eauto.
         -- eapply well_formed_allocation_shift_top_dim_reindexer;
              try apply Hrdx; try apply Henv; eauto.
         -- eapply contexts_agree_add_heap; try apply Henv; auto.
         -- eapply HasPadGen with (k:=0) (c:=c) (ll:=ll) (rr:=rr).
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 3. simpl. lia.
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 3. simpl. lia.
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 3. simpl. lia.
            eauto.
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 2. simpl.
            unfold eval_Zexpr_Z_total at 3. simpl.
            intros. apply H22. lia. 
            intros. eapply H24. lia.
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 2. simpl.
            unfold eval_Zexpr_Z_total at 4. simpl.
            intros. apply H25. lia. lia.
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 3. simpl. lia.
         -- eauto.
     * invert Hconst. propositional.
     * eassumption.
     * eapply well_formed_environment_add_valuation.
       simpl in Henv.
       auto. auto. auto.
     * eapply well_formed_allocation_result_V in Halloc1.
       eapply well_formed_reindexer_eval0. eassumption.
       eapply Henv.
       eauto. eauto. 
       unfold not. intros.
       eapply shape_to_vars_contains_substring in H6.
       propositional.
       simpl in *. lia. auto. auto. eauto. lia. eauto. apply Hrdx.
     * eapply well_formed_allocation_eval_step;
         try apply Halloc; eauto; try apply Hrdx; try apply Henv.
     * eauto.
     * eapply H22. lia.
     * eauto.
     }

     cases rr.
          2: { eapply IHeval_expr1 in H19.
          cases (reindexer
                   (((! i ! - lo)%z, (hi - lo)%z)
                      :: shape_to_index (result_shape_Z r)
                      (shape_to_vars (result_shape_Z r)))).
          { eapply reindexer_not_empty_vars_in_index in Heq0; try apply Hrdx.
            propositional.
            simpl. unfold app_no_dups.
            rewrite <- union_constant.
            unfold not. intros.
            eapply cup_empty in H6. invs.
            eapply cup_empty in H9. invs.
            eapply cup_empty in H6. invs.
            eapply constant_not_empty in H9. propositional. inversion 1. }
          invs. rewrite H7 in *. clear Heq0. clear Heq.
          * clear IHeval_expr1. pose proof IHeval_expr2. simpl in H6.
            unfold shift_top_dim_reindexer.
            specialize H6 with
              (p:=p)
              (reindexer:= shift_top_dim_reindexer reindexer)
              (h:=(h $+ (p,
                          array_add
                            x
                            (tensor_to_array_delta
                               (partial_interpret_reindexer
                                  (fun l =>
                                     reindexer
                                       (((! i ! - lo)%z,(hi - lo)%z) :: l))
                                  (result_shape_Z r)
                                  (v $+ (i, eval_Zexpr_Z_total $0 lo))) r)))).
            rewrite lookup_add_eq in * by auto.
            rewrite add_overwrite in H6.
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
              - eapply reindexer_not_empty_vars_in_index in H10. propositional.
                apply Hrdx. simpl.
                repeat rewrite app_no_dups_empty_r. repeat rewrite cup_empty_r.
                unfold not. intros.
                eapply constant_not_empty in H9. propositional. inversion 1.
              - eapply reindexer_not_empty_vars_in_index in H10. propositional.
                apply Hrdx. simpl.
                repeat rewrite app_no_dups_empty_r. repeat rewrite cup_empty_r.
                unfold not. intros.
                eapply cup_empty in H9. invs.
                eapply constant_not_empty in H11. propositional. inversion 1. }
eapply H6 with (st:=st) (st':=st') (asn:=asm).
         -- invert Hconst. simpl. invs. rewrite H9,H11. propositional.
            rewrite eval_Zexpr_Z_total_add_distr.
            simpl. unfold eval_Zexpr_Z_total at 3. simpl. lia.
            eauto. eauto.
         -- econstructor. eauto.
         -- clear IHeval_expr2.
            invs.
            unfold shift_top_dim_reindexer.
            eapply eq_eval_stmt_for.
            eassumption. simpl. rewrite H. reflexivity.
            rewrite H0. eauto.
            intros.
            eapply eq_eval_stmt_lower_eq_reindexers;
              simpl; intros; decomp_well_formed_reindexer.
            ++ eassumption.
            ++ invs. eapply HeqZlist.
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
               eapply eq_zexpr_add_sub_id.
               eauto.
               eapply eq_zexpr_comm.
               eapply eq_zexpr_transitivity.
               eapply eq_zexpr_sub_sub_distr.
               eapply eq_zexpr_transitivity.
               eapply eq_zexpr_sub.
               eapply eq_zexpr_id. auto.
               eapply eq_zexpr_add_sub_id.
               eauto.
         -- decomp_well_formed_environment.
            unfold well_formed_environment.
            split. auto.
            ++ rewrite dom_add.
               eapply lookup_Some_dom in H7.
               unfold well_formed_environment in *. invs.
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
         -- unfold well_formed_environment in *. invs.
            eapply well_formed_reindexer_shift_top_dim_reindexer;
              eauto.
         -- eapply well_formed_allocation_shift_top_dim_reindexer;
              try apply Hrdx; try apply Henv; eauto.
         -- eapply contexts_agree_add_heap; try apply Henv; auto.
         -- eapply HasPadGen with (k:=0) (c:=c) (ll:=0) (rr:=rr).
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 3. simpl. lia.
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 3. simpl. lia.
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 3. simpl. lia.
            eauto.
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 2. simpl.
            unfold eval_Zexpr_Z_total at 3. simpl.
            intros. apply H22. lia. 
            intros. eapply H24. lia.
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 2. simpl.
            unfold eval_Zexpr_Z_total at 4. simpl.
            intros. apply H25. lia. lia.
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 3. simpl. lia.
         -- eauto.
     * invert Hconst. propositional.
     * eassumption.
     * eapply well_formed_environment_add_valuation.
       simpl in Henv.
       auto. auto. auto.
     * eapply well_formed_allocation_result_V in Halloc1.
       eapply well_formed_reindexer_eval0. eassumption.
       eapply Henv.
       eauto. eauto. 
       unfold not. intros.
       eapply shape_to_vars_contains_substring in H6.
       propositional.
       simpl in *. lia. auto. auto. eauto. lia. eauto. apply Hrdx.
     * eapply well_formed_allocation_eval_step;
         try apply Halloc; eauto; try apply Hrdx; try apply Henv.
     * eauto.
     * eapply H24. lia.
     * eauto.
 }

          eapply IHeval_expr1 in H19.
          cases (reindexer
                   (((! i ! - lo)%z, (hi - lo)%z)
                      :: shape_to_index (result_shape_Z r)
                      (shape_to_vars (result_shape_Z r)))).
          { eapply reindexer_not_empty_vars_in_index in Heq0; try apply Hrdx.
            propositional.
            simpl. unfold app_no_dups.
            rewrite <- union_constant.
            unfold not. intros.
            eapply cup_empty in H6. invs.
            eapply cup_empty in H9. invs.
            eapply cup_empty in H6. invs.
            eapply constant_not_empty in H9. propositional. inversion 1. }
          invs. rewrite H7 in *. clear Heq0. clear Heq.
          * clear IHeval_expr1. pose proof IHeval_expr2. simpl in H6.
            unfold shift_top_dim_reindexer.
            specialize H6 with
              (p:=p)
              (reindexer:= shift_top_dim_reindexer reindexer)
              (h:=(h $+ (p,
                          array_add
                            x
                            (tensor_to_array_delta
                               (partial_interpret_reindexer
                                  (fun l =>
                                     reindexer
                                       (((! i ! - lo)%z,(hi - lo)%z) :: l))
                                  (result_shape_Z r)
                                  (v $+ (i, eval_Zexpr_Z_total $0 lo))) r)))).
            rewrite lookup_add_eq in * by auto.
            rewrite add_overwrite in H6.
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
              - eapply reindexer_not_empty_vars_in_index in H10. propositional.
                apply Hrdx. simpl.
                repeat rewrite app_no_dups_empty_r. repeat rewrite cup_empty_r.
                unfold not. intros.
                eapply constant_not_empty in H9. propositional. inversion 1.
              - eapply reindexer_not_empty_vars_in_index in H10. propositional.
                apply Hrdx. simpl.
                repeat rewrite app_no_dups_empty_r. repeat rewrite cup_empty_r.
                unfold not. intros.
                eapply cup_empty in H9. invs.
                eapply constant_not_empty in H11. propositional. inversion 1. }
eapply H6 with (st:=st) (st':=st') (asn:=asm).
         -- invert Hconst. simpl. invs. rewrite H9,H11. propositional.
            rewrite eval_Zexpr_Z_total_add_distr.
            simpl. unfold eval_Zexpr_Z_total at 3. simpl. lia.
            eauto. eauto.
         -- econstructor. eauto.
         -- clear IHeval_expr2.
            invs.
            unfold shift_top_dim_reindexer.
            eapply eq_eval_stmt_for.
            eassumption. simpl. rewrite H. reflexivity.
            rewrite H0. eauto.
            intros.
            eapply eq_eval_stmt_lower_eq_reindexers;
              simpl; intros; decomp_well_formed_reindexer.
            ++ eassumption.
            ++ invs. eapply HeqZlist.
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
               eapply eq_zexpr_add_sub_id.
               eauto.
               eapply eq_zexpr_comm.
               eapply eq_zexpr_transitivity.
               eapply eq_zexpr_sub_sub_distr.
               eapply eq_zexpr_transitivity.
               eapply eq_zexpr_sub.
               eapply eq_zexpr_id. auto.
               eapply eq_zexpr_add_sub_id.
               eauto.
         -- decomp_well_formed_environment.
            unfold well_formed_environment.
            split. auto.
            ++ rewrite dom_add.
               eapply lookup_Some_dom in H7.
               unfold well_formed_environment in *. invs.
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
         -- unfold well_formed_environment in *. invs.
            eapply well_formed_reindexer_shift_top_dim_reindexer;
              eauto.
         -- eapply well_formed_allocation_shift_top_dim_reindexer;
              try apply Hrdx; try apply Henv; eauto.
         -- eapply contexts_agree_add_heap; try apply Henv; auto.
         -- eapply HasPadGen with (k:=0) (c:=c-1) (ll:=0) (rr:=0).
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 3. simpl. lia.
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 3. simpl. lia.
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 3. simpl. lia.
            eauto.
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 2. simpl.
            unfold eval_Zexpr_Z_total at 3. simpl.
            intros. apply H22. lia. 
            intros. eapply H24. lia.
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 2. simpl.
            unfold eval_Zexpr_Z_total at 4. simpl.
            intros. apply H25. lia. lia.
            erewrite eval_Zexpr_Z_total_add_distr by auto.
            unfold eval_Zexpr_Z_total at 3. simpl. lia.
         -- eauto.
     * invert Hconst. propositional.
     * eassumption.
     * eapply well_formed_environment_add_valuation.
       simpl in Henv.
       auto. auto. auto.
     * eapply well_formed_allocation_result_V in Halloc1.
       eapply well_formed_reindexer_eval0. eassumption.
       eapply Henv.
       eauto. eauto. 
       unfold not. intros.
       eapply shape_to_vars_contains_substring in H6.
       propositional.
       simpl in *. lia. auto. auto. eauto. lia. eauto. apply Hrdx.
     * eapply well_formed_allocation_eval_step;
         try apply Halloc; eauto; try apply Hrdx; try apply Henv.
     * eauto.
     * eapply H25. lia. lia.
     * eauto.
   - (* STEPPING SUM *)
     simpl in *.
     unfold lookup_total in *.
     invert Hsize. pose proof H12 as Hsize. clear H12.
     assert (result_has_shape s
                              (map Z.to_nat
                                   (map (eval_Zexpr_Z_total $0) ls))) as Hsh.
     { assert (eval_expr sh v ec (Sum i lo hi body) s).
       econstructor; eauto.
       eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
       3: eassumption. eauto.
       eauto. }
       pose proof H6 as Hshh.
       eapply result_has_shape_add_result_result in Hshh.
       2: { eassumption. }
       inversion Hshh as [Hsh1 Hsh2 ]. clear Hshh.
       invert Heval; eq_eval_Z; try lia.
       rewrite H11,H14 in *. invert H. invert H0.
       invert Hpad.
       { eapply eval_Zexpr_Z_eval_Zexpr in H11,H14.
         invs. eq_eval_Z.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
           with (v:=$0) in H,H7. invert H. invert H7.
         eapply H in H14.
         eapply H0 in H11. invert H14. invert H11. lia. }
         
       eapply IHeval_expr1 with (asn:=Reduce) in H18; clear IHeval_expr1.
       cases (reindexer
                (shape_to_index (result_shape_Z s)
                                (shape_to_vars (result_shape_Z s)))).
     + pose proof Halloc as Halloc1.
       erewrite result_has_shape_result_shape_Z in *; try eassumption.
       rewrite Heq in *. invs.
       cases r.
       2: { invert H6. eq_size_of. invert Hsh1.
            rewrite <- H10 in *. simpl in *.
            eapply reindexer_not_empty in Heq.
            propositional. apply Hrdx. inversion 1.
            rewrite <- H6 in *. simpl in *.
            eapply reindexer_not_empty in Heq.
            propositional. apply Hrdx. inversion 1. }
       invert H6.
       * invert Hsh. invert Hsh1. invert Hsh2.
         rewrite <- H10 in *. simpl in *.
         unfold well_formed_allocation in Halloc1.
         unfold result_shape_Z in Halloc1.
         simpl in Halloc1. rewrite Heq in Halloc1. invs.
         rewrite H0.

         cases (Z.to_nat (eval_Zexpr_Z_total $0 hi -
                            (eval_Zexpr_Z_total $0 lo + 1))).
         { invert H5.
           simpl in H22. rewrite H11 in *. rewrite H23 in *. invs.
           eapply eval_Zexpr_Z_eval_Zexpr in H23,H11.
           eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
             with (v:=$0) in H,H7.
           invert H. invert H7.
           eapply H5 in H11. eapply H in H23. invert H23. invert H11. lia.

           simpl in H25. rewrite H11 in *. rewrite H26 in *. invs.
           eapply eval_Zexpr_Z_eval_Zexpr in H26,H11.
           eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
             with (v:=$0) in H,H7.
           invert H. invert H7.
           eapply H5 in H11. eapply H in H26. invert H26. invert H11.
           assert (eval_Zexpr_Z_total $0 hi = eval_Zexpr_Z_total $0 lo + 1)%Z
             by lia. rewrite H7 in *.
           cases lz; simpl in *; try discriminate. invert H22.
           invert H9.
           * rewrite H0 in *.
             assert (vars_of_Zexpr lo ++/ [] = [] /\
                       vars_of_Zexpr hi = [] /\ constant_nonneg_bounds body).
             { rewrite H6. propositional. }
             
             eapply IHeval_expr2 with (asn:=Reduce) in H9.
             2: { econstructor. eauto. }
             2: { eauto. }
             2: { eapply well_formed_environment_add_stack. eauto.
                  eapply lookup_Some_dom in H0. sets. }
             2: { replace (S SX) with (gen_pad []) by reflexivity.
                  decomp_well_formed_reindexer. simpl. propositional.
                  unfold partial_injective. intros. invert H21.
                  unfold nondestructivity. split; intros; discriminate. }
             2: { eapply well_formed_allocation_same_add_stack.
                  replace (S SX) with (gen_pad []) by reflexivity.
                  eapply well_formed_allocation_gen_pad. eauto.
                  econstructor. }
             2: { unfold well_formed_environment in *. invs.
                  eapply contexts_agree_add_in_stack.
                  eauto. eauto. auto. eauto. }
             2: { eapply HasPadSumEmpty. eauto.                  
                  erewrite eval_Zexpr_Z_total_add_distr.
                  unfold eval_Zexpr_Z_total at 3. simpl. lia.
                  eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total.
                  eauto. eauto. eauto. }             
             rewrite Heq in *. invs.
             rewrite lookup_add_eq in * by auto.
             rewrite add_overwrite.
             propositional. f_equal. ring.
             eauto.
           * rewrite H0 in *.
             assert (vars_of_Zexpr lo ++/ [] = [] /\
                       vars_of_Zexpr hi = [] /\ constant_nonneg_bounds body).
             { rewrite H6. propositional. }
             
             eapply IHeval_expr2 with (asn:=Reduce) in H9.
             2: { econstructor. eauto. }
             2: { eauto. }
             2: { eapply well_formed_environment_add_stack. eauto.
                  eapply lookup_Some_dom in H0. sets. }
             2: { replace (S SX) with (gen_pad []) by reflexivity.
                  decomp_well_formed_reindexer. propositional.
                  simpl. unfold nondestructivity.
                  split; intros; discriminate. }
             2: { rewrite Rplus_0_r. rewrite add_id by auto.
                  replace (S SX) with (gen_pad []) by reflexivity.
                  eapply well_formed_allocation_gen_pad. eauto.
                  econstructor. }
             2: { unfold well_formed_environment in *. invs.
                  eapply contexts_agree_add_in_stack.
                  eauto. eauto. auto. eauto. }
             2: { eapply HasPadSumEmpty. eauto.                  
                  erewrite eval_Zexpr_Z_total_add_distr.
                  unfold eval_Zexpr_Z_total at 3. simpl. lia.
                  eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total.
                  eauto. eauto. eauto. }
             rewrite Heq in *. invs.
             rewrite lookup_add_eq in * by auto.
             rewrite add_overwrite.
             propositional. f_equal. ring. eauto.
         }
         pose proof Heq0 as Heq'. clear Heq0.
         eapply IHeval_expr2 with (asn:=Reduce) in H19; clear IHeval_expr2.
         rewrite Heq in *. invs.
         rewrite H0. 
         rewrite lookup_add_eq by auto.
         rewrite add_overwrite. propositional. f_equal.
         cases z; cases s2; cases s3; try now invert H9.
         invert H9. ring.
         invert H9. ring.
         invert H9. ring.
         ring.
         eauto.
         eauto.
         eauto.
         rewrite H. propositional. eauto. eauto.
         eapply well_formed_environment_add_stack. eauto.
         eapply lookup_Some_dom. eauto.
         decomp_well_formed_reindexer.
         unfold result_shape_Z in *. simpl in *. propositional.
         cases s2; cases s3; simpl in *; auto.
         invert H9. invert H9. simpl in *.
         unfold partial_injective in *.
         propositional. simpl in *. propositional.
         rewrite H0.
         unfold nondestructivity.
         split; intros; discriminate.
         unfold well_formed_allocation.
         unfold result_shape_Z. simpl. rewrite Heq.
         eexists. rewrite H0. rewrite lookup_add_eq by auto.
         reflexivity.
         rewrite H0.
         eapply contexts_agree_add_in_stack; eauto.
         apply Henv. apply Henv.
         apply HasPadSum.
         rewrite eval_Zexpr_Z_total_add_distr.
         unfold eval_Zexpr_Z_total at 2. simpl.
         intros. eapply H15. lia.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total.
         eauto.
         eauto.
         eauto.
         rewrite eval_Zexpr_Z_total_add_distr.
         unfold eval_Zexpr_Z_total at 3. simpl.
         lia.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. eauto.
         eauto.
     + pose proof Heq.
       eapply well_formed_allocation_reindexer_not_empty in Heq;
         try apply Halloc.       
       invs. rewrite H10 in *.
       erewrite result_has_shape_result_shape_Z in *; try eassumption.
       invs. rewrite H in *. invs.
       cases (Z.to_nat (eval_Zexpr_Z_total $0 hi -
                          (eval_Zexpr_Z_total $0 lo + 1))).
       { invert H5.
         simpl in H21. rewrite H11 in *. rewrite H22 in *. invs.
         eapply eval_Zexpr_Z_eval_Zexpr in H22,H11.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
           with (v:=$0) in H0,H8.
         invert H0. invert H8.
         eapply H5 in H11. eapply H0 in H22. invert H22. invert H11. lia.

         eq_size_of.
         simpl in H21. rewrite H11 in *. rewrite H24 in *. invs.
         eapply eval_Zexpr_Z_eval_Zexpr in H24,H11.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
           with (v:=$0) in H0,H8.
         invert H0. invert H8.
         eapply H5 in H11. eapply H0 in H24. invert H24. invert H11.
         assert (eval_Zexpr_Z_total $0 hi = eval_Zexpr_Z_total $0 lo + 1)%Z
           by lia. rewrite H8 in *.
         pose proof H6 as Hh.
         eapply add_result_gen_pad_r in Hh. subst.
         2: { reflexivity. }
         2: { eapply result_has_shape_add_result_result in Hh; eauto. 
              invs.
              pose proof (result_has_shape_gen_pad (map Z.to_nat lz)).
              pose proof H11.
              eapply result_has_shape_result_shape_nat in H14,H18.
              rewrite H14 in H18. clear H14.
              eapply result_has_shape_filter_until_0.
              rewrite <- H18.
              erewrite <- result_has_shape_filter_until_0. eauto. }

         assert (vars_of_Zexpr lo ++/ [] = [] /\
                   vars_of_Zexpr hi = [] /\ constant_nonneg_bounds body).
         { rewrite H7. propositional. }

         eapply IHeval_expr2 with (asn:=Reduce) in H11.
         2: { econstructor. eauto. }
         2: { eauto. }
         2: { eapply well_formed_environment_add_heap. eauto. eauto. }
         2: { pose proof Hrdx.
              decomp_well_formed_reindexer.
              propositional.
              unfold partial_injective. intros.
              erewrite filter_negb_is_None_result_lookup_Z_option_gen_pad
                in *. invert H29.
              unfold nondestructivity. split; intros; discriminate. }
         2: { eapply well_formed_allocation_add_heap.
              eapply well_formed_allocation_gen_pad. eauto.
              pose proof (result_has_shape_gen_pad (map Z.to_nat lz)).
              eapply result_has_shape_result_shape_nat in H14,Hsh2.
              rewrite Hsh2 in *.
              eapply result_has_shape_filter_until_0.
              rewrite <- H14.
              erewrite <- result_has_shape_filter_until_0.
              eauto. eauto. }
         2: { unfold well_formed_environment in *.
              eapply contexts_agree_add_heap. eauto. eauto.
              propositional. propositional. }
         2: { eapply HasPadSumEmpty. eauto.
              erewrite eval_Zexpr_Z_total_add_distr.
              unfold eval_Zexpr_Z_total at 3. simpl. lia.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto.
              eauto. eauto. }
         rewrite H in *.
         rewrite lookup_add_eq in * by auto.
         invs. propositional.
         rewrite add_overwrite.
         rewrite tensor_to_array_delta_gen_pad.
         rewrite array_add_empty_r.
         f_equal. f_equal. f_equal.
         eapply partial_interpret_reindexer_add_valuation; eauto.
         eauto.
       }

       eapply IHeval_expr2 with (asn:=Reduce) in H19; clear IHeval_expr2;
         try apply Hrdx; try apply Henv; eauto.
       rewrite lookup_add_eq in H19 by auto.
       rewrite H in *. invs.
       rewrite add_overwrite.
       rewrite <- array_add_assoc. split. 2: auto. f_equal. f_equal.
       2: { rewrite H0. propositional. }
       2: { eapply well_formed_environment_add_heap; eauto. }
       2 :{ decomp_well_formed_reindexer. propositional.
            eapply partial_injective_add_result_r; try apply H6; eauto.
            unfold nondestructivity. split; intros; discriminate. }
       2: { eapply well_formed_allocation_add_heap; eauto.
            eapply well_formed_allocation_add_result_r; eauto. }
       2: { eapply contexts_agree_add_heap; eauto.
            apply Henv. apply Henv. }
       
       replace (map Z.of_nat
                    (filter_until (map Z.to_nat
                                       (map (eval_Zexpr_Z_total $0) ls)) 0))
         with (result_shape_Z r) at 1.
       2: { erewrite result_has_shape_result_shape_Z; eauto. }
       erewrite tensor_to_array_delta_add_valuation; eauto;
         try apply Hrdx.
       2: { eapply partial_injective_add_result_l; try apply H6; eauto.
            eapply partial_injective_add_valuation; try apply Hrdx; eauto. }
       
       replace (map Z.of_nat
                    (filter_until (map Z.to_nat
                                       (map (eval_Zexpr_Z_total $0) ls)) 0))
         with (result_shape_Z r') at 1.
       2: { erewrite result_has_shape_result_shape_Z; eauto. }
       replace (map Z.of_nat
                    (filter_until (map Z.to_nat
                                       (map (eval_Zexpr_Z_total $0) ls)) 0))
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
       rewrite eval_Zexpr_Z_total_add_distr.
       unfold eval_Zexpr_Z_total at 2. simpl.
       intros. apply H15. lia.
       eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total.
       eauto.
       eauto.
       rewrite eval_Zexpr_Z_total_add_distr.
       unfold eval_Zexpr_Z_total at 3. simpl.
       lia.
       eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. eauto.
     + propositional.
     + eauto.
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
     + eapply H15. invs.
       eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
         with (v:=$0) in H,H7.
       invert H. invert H7. eapply eval_Zexpr_Z_eval_Zexpr in H11,H14.
       eapply H0 in H11. eapply H in H14. invert H11. invert H14. lia.
     + eauto.
     + erewrite H15 in *. erewrite H16 in *. invs. lia.
   - (* EMPTY SUM *)
     simpl in Heval. invert Heval.
     rewrite H8,H11 in *. invert H. invert H0. lia.
     rewrite H12,H13 in *. invert H. invert H0.
     unfold lookup_total.
     simpl in Hconst. invert Hsize. eq_size_of.
     inversion Hconst as [ Hlo [ Hhi Hconst' ]]; clear Hconst.
     pose proof Hconst' as Hconst.
     eapply constant_nonneg_bounds_sizeof_nonneg in Hconst.
     2: { erewrite size_of_sizeof by eassumption. eassumption. }
     cases (reindexer
              (shape_to_index
                 (result_shape_Z (gen_pad (map Z.to_nat lz)))
                 (shape_to_vars (result_shape_Z (gen_pad
                                                   (map Z.to_nat lz)))))).
     { unfold well_formed_allocation in *. rewrite Heq in *. invs.
       rewrite H. split. auto.
       cases lz; simpl; rewrite add_id; try rewrite Rplus_0_r; auto. }
     eapply well_formed_allocation_reindexer_not_empty in Heq;
       try apply Halloc. invs.
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
                 (result_shape_Z (gen_pad (map Z.to_nat lz)))
                 (shape_to_vars
                    (result_shape_Z (gen_pad (map Z.to_nat lz)))))).
     { unfold well_formed_allocation in *. rewrite Heq in *. invs.
       rewrite H3. split. auto.
       cases lz; simpl; rewrite add_id; try rewrite Rplus_0_r; auto. }
     eapply well_formed_allocation_reindexer_not_empty in Heq;
       try apply Halloc. invs.
     rewrite H4. rewrite tensor_to_array_delta_gen_pad.
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
     inversion Hconst as [ Hconst1 Hconst2].
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
          split; intros. sets. invert H12. sets. }
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
          - subst. rewrite lookup_add_eq in * by auto. invs.
            simpl. eq_size_of.
            eapply has_pad_gen_pad in H13.
            2: { eauto. }
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
       invs. propositional.
       rewrite H8 in *.
       eq_size_of.
       rewrite Rplus_0_l.
       rewrite add_comm.
       2: { decomp_well_formed_environment. sets. }
       erewrite <- add_remove_id. reflexivity.
       rewrite dom_add.
       decomp_well_formed_environment.       
       rewrite cap_distr in Hsthec.
       eapply cup_empty in Hsthec. invs.
       rewrite cap_distr in H10. 
       eapply cup_empty in H10. invs.
       eapply constant_cap_empty in H12.
       sets. 
     + invs. unfold lookup_total.
       rewrite H9. split. auto.
       erewrite <- add_remove_id. reflexivity.
       decomp_well_formed_environment.
       rewrite cap_distr in Hsthec.
       eapply cup_empty in Hsthec. invs.
       rewrite cap_distr in H8.
       eapply cup_empty in H8. invs.
       eapply constant_cap_empty in H12.
       sets.
   - (* VECTOR LET *)
     simpl in *.
     cases esh1; simpl in *; try now propositional.
     erewrite size_of_sizeof in Heval by eassumption. simpl in Heval.
     invs.
     assert (result_has_shape (V l1)
                              (map Z.to_nat
                                   (map (eval_Zexpr_Z_total $0) (z::esh1))))
     as Hsh1.
     {
       eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
       3: eassumption. eauto. eauto. }
     invs.
     assert (result_has_shape (l2)
                              (map Z.to_nat
                                   (map (eval_Zexpr_Z_total $0) ls)))
     as Hsh2.
     {
       eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
       3: eassumption. eauto. eauto. }
     invert Hpad. eq_size_of.
     eapply IHeval_expr1 in H17; clear IHeval_expr1.
     2: eauto.
     2: { eassumption. }
     2: { eapply well_formed_environment_letbind1; eauto. }
     2: { decomp_well_formed_reindexer. propositional.
          eapply partial_injective_id_reindexer. apply Henv.
          simpl. sets. simpl. sets.
          unfold nondestructivity. unfold alloc_array_in_heap.
          rewrite lookup_add_eq by auto. rewrite dom_add.
          split; intros.
          2: sets. invert H10. clear H1. rewrite add_0_r.
          eapply dom_lookup_Some in H16. invert H16.
          unfold flat_sizeof in *.
          erewrite size_of_sizeof in * by eauto.
          simpl in H21.
          eapply eval_Zexpr_ZTimes_no_vars in H21.
          subst.
          pose proof (lookup_alloc_array (Z.to_nat
       (fold_left Z.mul
          (map Z.of_nat
             (filter_until (map Z.to_nat (map (eval_Zexpr_Z_total $0) (z :: esh1)))
                0)) 1%Z)) x0). invert H10.
          2: eauto.
          eapply lookup_None_dom in H16.
          rewrite dom_alloc_array in H16.
          rewrite Z2Nat.id in H16.
          2: { eapply fold_left_mul_nonneg.
               eapply Forall_map. eapply Forall_forall. intros. lia. lia. }
          exfalso. apply H16.
          erewrite <- In_iff_in.
          eapply In_zrange. clear H16.
          unfold tensor_to_array_delta in *.          
          eapply lookup_Some_dom in H1.
          unfold tensor_to_array_delta_by_indices in H1.
          erewrite partial_dom_fold_left_array_add in H1.
          rewrite dom_empty in *. rewrite cup_empty_r in *.
          rewrite filter_idempotent in H1.
          eapply In_iff_in in H1.
          eapply in_extract_Some in H1. eapply in_map_iff in H1. invert H1.
          invert H10. decomp_index.
          rewrite partial_interpret_reindexer_id_flatten in H1; eauto.
          invert H1.
          erewrite result_has_shape_result_shape_Z by eauto.
          eapply In_zrange.
          eapply in_mesh_grid_flatten_in_range.
          eapply Forall_map. eapply Forall_forall. intros. lia.
          erewrite result_has_shape_result_shape_Z in H10 by eauto.
          eauto.
          apply Henv.

          eauto.
          eapply partial_injective_id_reindexer; eauto. apply Henv.
          eapply constant_nonneg_bounds_size_of_no_vars.
          2: eauto. eauto.
          eapply constant_nonneg_bounds_size_of_nonneg. 2: apply H0.
          eauto. rewrite <- map_cons.
          eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v).
          eapply constant_nonneg_bounds_size_of_no_vars.
          2: apply H0.
          eauto. }
     2: { eapply well_formed_allocation_letbind1.
          try apply Henv. clear IHeval_expr2.
          eapply well_formed_environment_not_in_stack_heap. apply Henv.
          sets.
          unfold flat_sizeof in *.
          erewrite size_of_sizeof in * by eassumption.
          simpl in *|-.
          pose proof H3.
          eapply constant_nonneg_bounds_sizeof_no_vars in H3.
          erewrite size_of_sizeof in * by eassumption.
          pose proof H3. eq_size_of.
          eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H3.
          invert H3. eq_eval_Z. eq_eval_Zlist.
          eapply constant_nonneg_bounds_sizeof_nonneg in H1.
          2: { erewrite size_of_sizeof by eassumption.
               econstructor. eauto. eauto. }
          erewrite result_has_shape_result_shape_Z by eauto.
          eapply eval_Zexpr_ZTimes_no_vars; eauto. }
     3: { eassumption. }
     3: { eauto. }
     cases (shape_to_index (result_shape_Z (V l1))
                           (shape_to_vars (result_shape_Z (V l1)))).
     { eapply shape_to_index_not_empty_Z in Heq. propositional. }
     invs.
     eapply IHeval_expr2 in H18.
     2: { eauto. }
     2: eassumption. 
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
          unfold well_formed_environment in *. invs.
          sets.
          eapply well_formed_allocation_add_heap_var; eauto. }
     2: { unfold alloc_array_in_heap.
          rewrite add_overwrite.
          rewrite lookup_total_add_eq. simpl.
          rewrite add_0_r.
          unfold result_shape_Z.
          erewrite result_has_shape_result_shape_nat by eassumption.
          pose proof H3. eq_size_of.
          eapply constant_nonneg_bounds_sizeof_no_vars in H1.
          erewrite size_of_sizeof in H1 by eassumption.
          eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H1.
          invert H1. 
          eq_eval_Z. eq_eval_Zlist.
          erewrite tensor_to_array_delta_id_valuation.
          2: { apply Henv. }
          eapply contexts_agree_add_alloc_heap; eauto.
          eapply constant_nonneg_bounds_sizeof_nonneg in H3.
          2: { erewrite size_of_sizeof by eassumption.
               econstructor; eauto. }
          eauto. econstructor; eauto.
          eapply constant_nonneg_bounds_size_of_no_vars in H0.
          invert H0. propositional. eauto. 
          eapply constant_nonneg_bounds_size_of_no_vars in H0.
          invert H0. propositional. eauto. 
          unfold flat_sizeof in *.
          erewrite size_of_sizeof in * by eassumption.
          simpl in H21.
          eapply eval_Zexpr_ZTimes_no_vars in H21.
          auto.
          eapply constant_nonneg_bounds_size_of_no_vars; try apply H3; eauto.
          eapply constant_nonneg_bounds_size_of_nonneg; try apply H3; eauto. }
     2: { eauto. }
     2: { intros. cases (x==v x0).
          - subst. rewrite lookup_add_eq in * by auto. invs.
            eapply has_pad_gen_pad. eauto. eauto. eauto.
            eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape
              in H5; eauto.
            eapply result_has_shape_self in H5. eauto.
            eauto.
            eapply contexts_agree_result_has_shape. eauto.
            eauto.
          - rewrite lookup_add_ne in * by auto. eauto. }
     2: { eapply contexts_agree_alloc_array_in_heap; eauto. }
     cases (reindexer
              (shape_to_index (result_shape_Z l2)
                              (shape_to_vars (result_shape_Z l2)))).
     + unfold well_formed_allocation in *. rewrite Heq0 in *.
       invs. rewrite H1.
       rewrite add_remove.
       unfold alloc_array_in_heap.
       rewrite add_remove.
       split. 2: auto.
       decomp_well_formed_environment.
       eapply remove_id.
       rewrite cap_distr in Hsthec. eapply cup_empty in Hsthec. invs.
       rewrite cap_distr in H10. eapply cup_empty in H10. invs.
       eapply constant_cap_empty in H12. sets.
     + unfold well_formed_allocation in *. rewrite Heq0 in *.
       invs. unfold lookup_total. rewrite H10.
       unfold alloc_array_in_heap.
       repeat rewrite add_overwrite.
       rewrite lookup_add_eq by auto.
       rewrite lookup_add_ne.
       rewrite H10.              
       rewrite add_remove_comm.
       2: { intros. pose proof var_eq. specialize (H1 k k').
            invert H1; propositional. }
       2: { unfold well_formed_environment in *. invs.
            sets. }
       2: { unfold well_formed_environment in *. invs.
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
     assert (result_has_shape (V l1)
                              (map Z.to_nat
                                   (map (eval_Zexpr_Z_total $0) (n::l0))))
       as Hsh1.
     { eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
       3: eassumption. propositional. eassumption. }
     assert (result_has_shape (V l2)
                              (map Z.to_nat
                                   (map (eval_Zexpr_Z_total $0) (m::l0))))
       as Hsh2.
     { simpl.
       rewrite H8. repeat rewrite <- map_cons.
       eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
       3: eassumption. propositional. eassumption. }
     simpl map in *.
     pose proof (result_has_shape_length _ _ _ Hsh1).
     pose proof (result_has_shape_length _ _ _ Hsh2). subst.
     pose proof (result_has_shape_concat _ _ _ _ _ Hsh1 Hsh2).
     invert Hconst. pose proof H6. pose proof H7.
     eapply constant_nonneg_bounds_sizeof_no_vars in H6,H7.
     erewrite size_of_sizeof in * by eassumption.
     invert H6. invert H7.
     pose proof H13. pose proof H12.
     eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H13,H12.
     invert H13. invert H12.
     pose proof (H11 $0). pose proof (H13 $0).
     eapply eval_Zexpr_Z_eval_Zexpr in H12,H16.
     unfold eval_Zexpr_Z_total in Hsh1 at 1.
     unfold eval_Zexpr_Z_total in Hsh2 at 1.
     unfold eval_Zexpr_Z_total in H1,H4.
     unfold eval_Zexpr_Z_total in H5 at 1.
     unfold eval_Zexpr_Z_total in H5 at 1.
     rewrite H12,H16 in *.
     pose proof H9. pose proof H10.
     eapply constant_nonneg_bounds_sizeof_nonneg in H17,H18.
     2: { erewrite size_of_sizeof by eassumption.
          eapply forall_no_vars_eval_Zexpr_Z_total with (v:=$0).
          econstructor. eauto. eauto. }
     2: { erewrite size_of_sizeof by eassumption.
          eapply forall_no_vars_eval_Zexpr_Z_total with (v:=$0).
          econstructor. eauto. eauto. }
     invert H17. invert H18.
     unfold eval_Zexpr_Z_total in H21,H20.
     rewrite H12,H16 in *.
     assert (eq_zexpr n (| eval_Zexpr_Z_total $0 n|)%z) as Heqn.
     { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. }
     assert (eq_zexpr m (| eval_Zexpr_Z_total $0 m|)%z) as Heqm.
     { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. }
     assert (x0 = eval_Zexpr_Z_total $0 n)%Z as Heqx0.
     { unfold eval_Zexpr_Z_total. rewrite H12. auto. }
     assert (x1 = eval_Zexpr_Z_total $0 m)%Z as Heqx1.
     { unfold eval_Zexpr_Z_total. rewrite H16. auto. }
     subst.
     
     invert Heval. invert Hpad. eq_size_of. invert H17. invert H18.
     eapply IHeval_expr1 in H25; auto; clear IHeval_expr1.
     2: { eauto. }
     2: { eapply well_formed_environment_subseteq_vars. eassumption. sets. }
     2: { rewrite <- H1 in *. rewrite <- H4 in *.
          eapply well_formed_allocation_result_V in Halloc.
          eapply well_formed_reindexer_concat_l;
            try apply Hrdx.
          rewrite H4 in *. eauto. rewrite H1 in *. eauto.
          lia. lia.
          eauto. eauto. 
          apply Henv.
          eauto. apply Hrdx. }
     2: { eapply well_formed_allocation_concat_l; eauto;
          try eapply Henv; try eapply Hrdx.
          rewrite Z2Nat.id. eauto. lia. }
     cases (shape_to_index (result_shape_Z (V l1))
                           (shape_to_vars (result_shape_Z (V l1)))).
     { eapply shape_to_index_not_empty_Z in Heq0. propositional. }
     cases (reindexer
              (let (v, d) := p1 in ((v, (d + dim2)%z) :: l0)) ).
     { unfold result_shape_Z, shape_to_index, shape_to_vars in Heq0.
       simpl in Heq0.
       cases l1; invert Heq0.
       - eapply reindexer_not_empty_vars_in_index in Heq1. propositional.
         apply Hrdx. simpl.
         unfold not. intros.
         eapply cup_empty in H17. invs.
         eapply cup_empty in H18. invs.
         eapply constant_not_empty in H17. propositional.
         inversion 1.
       - eapply reindexer_not_empty_vars_in_index in Heq1. propositional.
         apply Hrdx. simpl.
         unfold not. intros.
         eapply cup_empty in H17. invs.
         eapply cup_empty in H18. invs.
         eapply constant_not_empty in H17. propositional.
         inversion 1. }
     invs. rewrite H2 in *.
     eapply IHeval_expr2 in H28; clear IHeval_expr2.
     cases (shape_to_index (result_shape_Z (V l2))
                           (shape_to_vars (result_shape_Z (V l2)))). 
     { eapply shape_to_index_not_empty_Z in Heq2. propositional. } 
     cases (reindexer
            (let (v, d) := p3 in
             ((v + match sizeof e1 with
                   | [] => | 0 |
                   | n :: _ => n
                   end)%z,
             (d + match sizeof e1 with
                  | [] => | 0 |
                  | n :: _ => n
                  end)%z) :: l6)).
     { unfold result_shape_Z, shape_to_index, shape_to_vars in Heq2.
       cases l2; invert Heq2.
       - eapply reindexer_not_empty_vars_in_index in Heq3. propositional.
         apply Hrdx. simpl.
         unfold not. intros.
         eapply cup_empty in H17. invs.
         eapply cup_empty in H18. invs.
         eapply constant_not_empty in H17. propositional.
         inversion 1.
       - eapply reindexer_not_empty_vars_in_index in Heq3. propositional.
         apply Hrdx. simpl.
         unfold not. intros.
         eapply cup_empty in H17. invs.
         eapply cup_empty in H18. invs.
         eapply constant_not_empty in H17. propositional.
         inversion 1. }
     
     rewrite lookup_add_eq in * by auto. invs.
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
          - invs.
            repeat erewrite result_has_shape_result_shape_Z in * by eauto.
            repeat decomp_index.
            repeat rewrite mesh_grid_map_Nat2Z_id in *.
            rewrite <- H18 in H17.
            clear Heq. clear Heq0. clear Heq2. clear H3.
            decomp_well_formed_reindexer.
            erewrite result_has_shape_result_shape_Z in Hinj by eauto.
            replace (fun e : Zexpr =>
                          match eval_Zexpr_Z $0 e with
                          | Some x => x
                          | None => 0%Z
                          end) with
              (eval_Zexpr_Z_total $0) in *.
            2: { reflexivity. }
            erewrite eq_partial_interpret_reindexer_padl in H18,H17;
              try assumption; try apply Henv; try lia.
            2: { erewrite size_of_sizeof by eauto. simpl. auto. }
            2: { erewrite size_of_sizeof by eauto. simpl. lia. }
            2: { erewrite size_of_sizeof by eauto. simpl. auto. }
            2: { erewrite size_of_sizeof by eauto. simpl. lia. }
            erewrite size_of_sizeof in * by eauto.
            simpl eval_Zexpr_Z_total in H18,H17.
            erewrite eq_partial_interpret_reindexer_concat_l in H17;
              try assumption; try apply Henv; try lia.
            3: apply Hsh1.
            3: apply Hsh2.
            2: { erewrite result_has_shape_result_shape_Z by eauto.
                 eapply filter_In. propositional.
                 repeat decomp_goal_index.
                 propositional. 
                 rewrite mesh_grid_map_Nat2Z_id. auto. }
            2: { rewrite Z2Nat.id by lia. auto. }
            pose proof H17.
            eapply Hinj in H17.
            invert H17.
            + invert H19. lia.
            + rewrite H3 in H19. rewrite H19 in *.
              discriminate.
            + eapply filter_In. propositional.
              repeat decomp_goal_index.
              propositional. lia. 
              rewrite mesh_grid_map_Nat2Z_id. auto.
              rewrite <- H32.
              simpl.
              rewrite nth_error_app1.
              auto.
              erewrite result_has_shape_length by eauto.
              lia.
            + eapply filter_In. propositional.
              repeat decomp_goal_index.
              propositional. lia. lia.
              rewrite mesh_grid_map_Nat2Z_id. auto.
              rewrite <- H32.
              simpl.
              rewrite nth_error_app2.
              rewrite Z2Nat.inj_add by lia.
              erewrite result_has_shape_length by eauto.
              rewrite add_sub.
              cases z; try lia.
              simpl Z.add.
              cases (eval_Zexpr_Z_total $0 dim1); try lia.
              eauto.
              cases (Z.pos p0 + eval_Zexpr_Z_total $0 dim1)%Z; try lia.
              eauto. lia.
          - invs.
            repeat erewrite result_has_shape_result_shape_Z in * by eauto.
            repeat decomp_index.
            repeat rewrite mesh_grid_map_Nat2Z_id in *.
            rewrite <- H18 in H17.
            clear Heq. clear Heq0. clear Heq2. clear H3.
            decomp_well_formed_reindexer.
            erewrite result_has_shape_result_shape_Z in Hinj by eauto.
            replace (fun e : Zexpr =>
                          match eval_Zexpr_Z $0 e with
                          | Some x => x
                          | None => 0%Z
                          end) with
              (eval_Zexpr_Z_total $0) in *.
            2: { reflexivity. }
            erewrite eq_partial_interpret_reindexer_padl in H17;
              try assumption; try apply Henv; try lia.
            2: { erewrite size_of_sizeof by eauto. simpl. auto. }
            2: { erewrite size_of_sizeof by eauto. simpl. lia. }
            erewrite size_of_sizeof in * by eauto.
            simpl eval_Zexpr_Z_total in H17.
            erewrite eq_partial_interpret_reindexer_concat_l in H18,H17;
              try assumption; try apply Henv; try lia.
            3: apply Hsh1.
            3: apply Hsh2.
            5: apply Hsh1.
            5: apply Hsh2.            
            2: { erewrite result_has_shape_result_shape_Z by eauto.
                 eapply filter_In. propositional.
                 repeat decomp_goal_index.
                 propositional. 
                 rewrite mesh_grid_map_Nat2Z_id. auto. }
            2: { rewrite Z2Nat.id by lia. auto. }
            2: { erewrite result_has_shape_result_shape_Z by eauto.
                 eapply filter_In. propositional.
                 repeat decomp_goal_index.
                 propositional. 
                 rewrite mesh_grid_map_Nat2Z_id. auto. }
            2: { rewrite Z2Nat.id by lia. auto. }
            pose proof H17.
            eapply Hinj in H17.
            invert H17.
            + invert H19. lia.
            + rewrite H3 in H19. rewrite H19 in *.
              discriminate.
            + eapply filter_In. propositional.
              repeat decomp_goal_index.
              propositional. lia. lia.
              rewrite mesh_grid_map_Nat2Z_id. auto.
              rewrite <- H28.
              simpl.
              rewrite nth_error_app2.
              rewrite Z2Nat.inj_add by lia.
              erewrite result_has_shape_length by eauto.
              rewrite add_sub.
              cases z0; try lia.
              simpl Z.add.
              cases (eval_Zexpr_Z_total $0 dim1); try lia.
              eauto.
              cases (Z.pos p0 + eval_Zexpr_Z_total $0 dim1)%Z; try lia.
              eauto. lia.
            + eapply filter_In. propositional.
              repeat decomp_goal_index.
              propositional. lia. 
              rewrite mesh_grid_map_Nat2Z_id. auto.
              rewrite <- H28.
              simpl.
              rewrite nth_error_app1.
              auto.
              erewrite result_has_shape_length by eauto.
              lia.
     }
     2: { eauto. }
     2: { eauto. }
     2: { decomp_well_formed_reindexer.
          unfold well_formed_reindexer. propositional.
          erewrite result_has_shape_result_shape_Z by eauto.
            replace (fun e : Zexpr =>
                          match eval_Zexpr_Z $0 e with
                          | Some x => x
                          | None => 0%Z
                          end) with
              (eval_Zexpr_Z_total $0) in * by reflexivity.          
            eapply partial_injective_concat_l; eauto; try apply Henv.
            rewrite Z2Nat.id by lia. auto. }
     2: { decomp_well_formed_reindexer.
          erewrite size_of_sizeof by eassumption. simpl.
          erewrite result_has_shape_result_shape_Z by eauto.
          replace (fun e : Zexpr =>
                          match eval_Zexpr_Z $0 e with
                          | Some x => x
                          | None => 0%Z
                          end) with
            (eval_Zexpr_Z_total $0) in * by reflexivity.
          eapply partial_injective_concat_r; eauto.          
          apply Henv. }
     2: { eauto. }
     2: { eassumption. }
     2: { eapply well_formed_environment_add_heap.
          eapply well_formed_environment_subseteq_vars. eassumption.
          sets. auto. }
     2: { erewrite size_of_sizeof by eassumption. simpl.
          eapply well_formed_allocation_result_V in Halloc.
          invert Halloc. invert H17.
          eapply well_formed_reindexer_concat_r;
            try apply Henv; eauto.
          apply Hrdx.
     }
     2: { eapply well_formed_allocation_add_heap.
          erewrite size_of_sizeof by eauto.
          eapply well_formed_allocation_concat_r; eauto;
            try apply Henv; try apply Hrdx.
          simpl. eauto.
          simpl. eauto.
          auto. }
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
          { assert (eval_Zexpr_Z_total $0 dim1 = 0)%Z by lia.
            simpl length. simpl Z.of_nat.
            rewrite add_0_l. rewrite app_nil_l.
            unfold partial_injective.
            rewrite app_nil_l in Hinj.
            erewrite result_has_shape_result_shape_Z in Hinj by eauto.
            rewrite <- H17 in *.
            rewrite add_0_l in *. propositional.
            repeat decomp_index.
            cases (z0 <? 0)%Z. eapply Z.ltb_lt in Heq4. lia.
            cases (z <? 0)%Z. eapply Z.ltb_lt in Heq5. lia.
            rewrite Z.sub_0_r in *.

            erewrite eq_partial_interpret_reindexer_padl in H25;
              eauto; try apply Henv; try lia.
            erewrite eq_partial_interpret_reindexer_padl in H25;
              eauto; try apply Henv; try lia.

            rewrite H18 in *.
            rewrite add_0_l in *.
            rewrite Z.sub_0_r in *.
            rewrite Z.add_0_r in *.
            eapply Hinj in H25.
            invert H25.
            - invert H28. left. f_equal. lia. 
            - erewrite eq_partial_interpret_reindexer_padl;
                eauto; try apply Henv.
              rewrite H18. rewrite Z.add_0_r.
              simpl Z.to_nat. rewrite add_0_l.
              rewrite H28. propositional.
              eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total.
              invert Heqn. sets. auto.
              lia. lia.
            - eapply filter_In. propositional.
              repeat decomp_goal_index. propositional.
            - rewrite Z.add_0_r.
              eapply filter_In. propositional.
              repeat decomp_goal_index. propositional. }
          cases l2. invert Hsh2.
          { rewrite add_0_r in *. rewrite app_nil_r.
            assert (eval_Zexpr_Z_total $0 dim2 = 0)%Z by lia.
            erewrite result_has_shape_length; eauto.
            rewrite Z2Nat.id by lia.
            unfold partial_injective.
            propositional.
            repeat decomp_index.
            cases (z0 <? eval_Zexpr_Z_total $0 dim1)%Z.
            2: { eapply Z.ltb_ge in Heq4. lia. }
            cases (z <? eval_Zexpr_Z_total $0 dim1)%Z.
            2: { eapply Z.ltb_ge in Heq5. lia. }
            erewrite eq_partial_interpret_reindexer_concat_l in H25;
              auto; try apply Henv.
            3: apply Hsh1.
            3: { econstructor. }
            erewrite eq_partial_interpret_reindexer_concat_l in H25;
              auto; try apply Henv.
            3: apply Hsh1.
            3: { econstructor. }
            rewrite add_0_r in *.
            rewrite app_nil_r in *.
            erewrite result_has_shape_result_shape_Z in Hinj by eauto.
            rewrite H18 in Hinj.
            simpl Z.to_nat in Hinj. rewrite add_0_r in Hinj.
            eapply Hinj in H25.
            invert H25.
            propositional.
            erewrite eq_partial_interpret_reindexer_concat_l;
              auto; try apply Henv.
            3: apply Hsh1.
            3: { econstructor. }
            rewrite add_0_r.
            rewrite H28. propositional.
            erewrite result_has_shape_result_shape_Z by eauto.
            rewrite H18. simpl Z.to_nat. rewrite add_0_r.
            eapply filter_In. propositional.
            repeat decomp_goal_index. propositional.
            rewrite H18 in Heqm. auto.
            eapply filter_In. propositional.
            repeat decomp_goal_index. propositional.
            rewrite H18 in Heqm. auto.
            eapply filter_In. propositional.
            repeat decomp_goal_index. propositional.
            rewrite H18 in Heqm. auto.
            erewrite result_has_shape_result_shape_Z by eauto.
            eapply filter_In. propositional.
            repeat decomp_goal_index. propositional.
            rewrite H18 in Heqm. auto.
            erewrite result_has_shape_result_shape_Z by eauto.
            eapply filter_In. propositional.
            repeat decomp_goal_index. propositional.
            rewrite H18 in Heqm. auto. }
          invert Hsh1. invert Hsh2.
          simpl map. posnats.
          rewrite <- add_succ_l.
          rewrite Nat2Z.inj_add.
          rewrite mesh_grid_app.
          eapply partial_injective_concat.
          { repeat erewrite <- map_cons.
            simpl length in *.
            rewrite H4.
            rewrite <- filter_until_cons by lia.
            repeat rewrite <- map_cons.
            eapply partial_injective_concat_r.
            eassumption.
            simpl.
            rewrite <- H19.
            econstructor; eauto.
            simpl.
            rewrite <- H4.
            econstructor; eauto.
            apply Henv.
            auto. auto. auto. auto. lia. auto. }
          { repeat erewrite <- map_cons.
            simpl length in *.
            rewrite H19.
            rewrite <- filter_until_cons by lia.
            repeat rewrite <- map_cons.
            simpl map.
            eapply partial_injective_concat_l.
            eassumption.
            simpl.
            rewrite <- H1.
            econstructor; eauto.
            simpl.
            econstructor; eauto.
            apply Henv.
            auto. auto. auto. rewrite H24. rewrite Z2Nat.id by lia.
            auto. }
          { apply cap_empty_exclusion. propositional.
            - rewrite <- @In_iff_in in *.
              rewrite <- @in_extract_Some in *.
              rewrite in_map_iff in *. invs.
              repeat decomp_index. simpl map in *.
              repeat decomp_index.
              pose proof H17.
              rewrite <- H18 in H25.
              rewrite <- map_cons in H25,H18.
              rewrite <- filter_until_cons in H25,H18 by lia.
              erewrite eq_partial_interpret_reindexer_concat_l in H25.
              3: { econstructor. reflexivity. apply H28. eauto. }
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
              2: { rewrite H24. rewrite Z2Nat.id by lia. auto. }
              rewrite H24 in H25.
              rewrite <- map_cons in H25.
              rewrite <- filter_until_cons in H25 by lia.
              rewrite H24 in H18.
              erewrite eq_partial_interpret_reindexer_padl in H25,H18; eauto.
              2: { apply Henv. }
              2: { lia. }
              2: { apply Henv. }
              2: { lia. }
              rewrite H19 in H25.
              erewrite result_has_shape_result_shape_Z in Hinj.
              2: { eapply result_has_shape_concat.
                   econstructor; eauto.
                   econstructor; eauto. }
              rewrite H19,H24 in Hinj.
              pose proof H25.
              eapply Hinj in H25.
              invert H25. invert H43. lia.
              rewrite H43 in H42.
              rewrite <- H42 in H18.
              discriminate.
              eapply filter_In. propositional.
              repeat decomp_goal_index.
              propositional. lia.
              rewrite <- H38.
              simpl.
              rewrite app_comm_cons.
              rewrite nth_error_app1. auto.
              erewrite result_has_shape_length.
              2: { econstructor. reflexivity. eauto. eauto. }
              lia.
              eapply filter_In. propositional.
              repeat decomp_goal_index.
              propositional. lia. lia.
              rewrite <- H38.
              simpl.
              rewrite app_comm_cons.
              rewrite nth_error_app2.
              erewrite result_has_shape_length.
              2: { econstructor. reflexivity. eauto. eauto. }
              rewrite H19.
              rewrite Z2Nat.inj_add by lia.
              rewrite add_sub.
              cases z0; try lia.
              simpl Z.add at 1.
              cases (eval_Zexpr_Z_total $0 dim1); try lia.
              eauto.
              cases ((Z.pos p5 + eval_Zexpr_Z_total $0 dim1)%Z); try lia.
              eauto. simpl. lia.
            - rewrite <- @In_iff_in in *.
              rewrite <- @in_extract_Some in *.
              rewrite in_map_iff in *. invs.
              repeat decomp_index. simpl map in *.
              repeat decomp_index.
              pose proof H17.
              rewrite <- H18 in H25.
              rewrite <- map_cons in H25,H18.
              rewrite <- filter_until_cons in H25,H18 by lia.
              rewrite H24 in *. rewrite H19 in *.
              erewrite eq_partial_interpret_reindexer_padl in H25; eauto;
                try apply Henv; try lia.
              rewrite <- map_cons in H25,H18.
              rewrite <- filter_until_cons in H25 by lia.
              rewrite map_cons in H18.
              erewrite eq_partial_interpret_reindexer_concat_l in H25,H18.
                try apply Henv.
              3: { rewrite <- H19. econstructor. reflexivity.
                   apply H28. auto. }
              10: { rewrite <- H19. econstructor. reflexivity.
                    apply H28. auto. }
              3: { eapply VectorConsShape. reflexivity.
                   eauto. eauto. }
              9: { eapply VectorConsShape. reflexivity.
                   eauto. eauto. }
              2: { eapply filter_In. propositional.
                   erewrite result_has_shape_result_shape_Z by
                     (econstructor; eauto).
                   repeat decomp_goal_index.
                   propositional. lia. }
              2: { apply Henv. }
              2: { auto. }
              2: { auto. }
              2: { auto. }
              2: { rewrite H24. rewrite Z2Nat.id by lia. auto. }
              2: { eapply filter_In. propositional.
                   erewrite result_has_shape_result_shape_Z by
                     (econstructor; eauto).
                   repeat decomp_goal_index.
                   propositional. lia. }
              2: { apply Henv. }
              2: { auto. }
              2: { auto. }
              2: { auto. }
              2: { rewrite H24. rewrite Z2Nat.id by lia. auto. }
              rewrite H24 in *.
              erewrite result_has_shape_result_shape_Z in Hinj.
              2: { eapply result_has_shape_concat.
                   econstructor; eauto.
                   econstructor; eauto. }
              rewrite H19,H24 in Hinj.
              pose proof H25.
              eapply Hinj in H25.
              invert H25. invert H43. lia.
              rewrite H43 in H42.
              rewrite <- H42 in H18.
              discriminate.
              eapply filter_In. propositional.
              repeat decomp_goal_index.
              propositional. lia. lia.
              rewrite <- H38.
              simpl.
              rewrite app_comm_cons.
              rewrite nth_error_app2.
              erewrite result_has_shape_length.
              2: { econstructor. reflexivity. eauto. eauto. }
              rewrite H19.
              rewrite Z2Nat.inj_add by lia.
              rewrite add_sub.
              cases z0; try lia.
              simpl Z.add at 1.
              cases (eval_Zexpr_Z_total $0 dim1); try lia.
              eauto. 
              cases ((Z.pos p5 + eval_Zexpr_Z_total $0 dim1)%Z); try lia.
              eauto. simpl. lia.
              eapply filter_In. propositional.
              repeat decomp_goal_index.
              propositional. lia. 
              rewrite <- H39.
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
     erewrite result_has_shape_result_shape_Z in H17 by eauto.
     repeat decomp_index.
     erewrite size_of_sizeof by eauto. simpl.
     replace (fun e : Zexpr =>
                     match eval_Zexpr_Z $0 e with
                     | Some x => x
                     | None => 0%Z
                     end) with
       (eval_Zexpr_Z_total $0) in * by reflexivity.
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
       lia.
       rewrite <- H19.
       simpl.
       rewrite nth_error_app1. auto. lia.
       apply Henv. apply Hrdx. apply Hrdx. apply Hrdx.
       rewrite Z2Nat.id by lia. auto. }
     pose proof Hcase2 as Hcase2'.
     eapply Z.ltb_ge in Hcase2'.
     rewrite Hcase2'. clear Hcase2'.
     rewrite H1 in *.
     repeat erewrite result_has_shape_result_shape_Z by eauto.
     erewrite eq_partial_interpret_reindexer_padl.
     f_equal. f_equal. lia.
     eauto.
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
     assert (result_has_shape (V l)
                              (map Z.to_nat
                                   (map (eval_Zexpr_Z_total $0)
                                        (n::m::esh)))) as Hsh.
     { eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
       eauto. eauto. eauto. }
     invert Hsize. pose proof H3 as Hsize. clear H3.
     eq_size_of. invert H2.
     pose proof Hconst.
     eapply constant_nonneg_bounds_sizeof_no_vars in H2.
     erewrite  size_of_sizeof in H2.
     2: { eassumption. }
     eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H2.
     eq_eval_Zlist. simpl in H3. invert H3.
     pose proof Hconst.
     eapply constant_nonneg_bounds_sizeof_no_vars in H2.
     erewrite size_of_sizeof in * by eassumption.
     invert H2. invert H6.
     pose proof H4. pose proof H5.
     repeat rewrite map_cons in *.     

     invert Hpad.
     { 
     eapply IHeval_expr in Heval; eauto. invs. clear IHeval_expr.
     cases (shape_to_index (result_shape_Z (V l))
                           (shape_to_vars (result_shape_Z (V l)))).
     { eapply shape_to_index_not_empty_Z in Heq0. propositional. }
     cases (reindexer
      (shape_to_index
         (result_shape_Z
            (transpose_result l
               (Z.to_nat (eval_Zexpr_Z_total $0 m0)
                :: Z.to_nat (eval_Zexpr_Z_total $0 n0)
                   :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0))))
         (shape_to_vars
            (result_shape_Z
               (transpose_result l
                  (Z.to_nat (eval_Zexpr_Z_total $0 m0)
                   :: Z.to_nat (eval_Zexpr_Z_total $0 n0)
                      :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0))))))).
     { eapply reindexer_not_empty in Heq1. propositional. apply Hrdx.
       erewrite result_has_shape_result_shape_Z.
       2: eapply result_has_shape_transpose_result; eauto.
       simpl.
       cases (Z.to_nat (eval_Zexpr_Z_total $0 m0)); simpl.
       inversion 1.
       cases (Z.to_nat (eval_Zexpr_Z_total $0 n0)).
       simpl. inversion 1. simpl. inversion 1. }
     cases (reindexer
              (let (v, d) := p0 in
               match l4 with
               | [] => p0 :: l4
               | (vi, di) :: xs => (vi, di) :: (v, d) :: xs
               end)).
     { unfold result_shape_Z, shape_to_index, shape_to_vars in Heq0.
       cases l; invert Heq0.
       - eapply reindexer_not_empty_vars_in_index in Heq2.
         propositional. apply Hrdx.
         simpl. repeat rewrite cup_empty_r.
         unfold not. intros. eapply constant_not_empty in H1. propositional.
         inversion 1.
       - eapply reindexer_not_empty_vars_in_index in Heq2.
         propositional. apply Hrdx.
         simpl. repeat rewrite cup_empty_r.
         cases (result_shape_nat r0); simpl; repeat rewrite cup_empty_r;
           unfold not; intros.
         eapply constant_not_empty in H1. propositional. inversion 1.
         eapply cup_empty in H1. invs.
         eapply constant_not_empty in H6. propositional. inversion 1.
     }
     invs.
     split; auto.
     f_equal. f_equal.
     { unfold tensor_to_array_delta.
       eapply eq_tensor_to_array_delta_by_indices_shuffle
         with (shuffle:=(fun l => match l with
                                 | x::y::xs => y::x::xs
                                 | _ => l
                                  end)).
       - intros.
         erewrite result_has_shape_result_shape_Z in H1.
         2: { eapply result_has_shape_transpose_result.
              simpl in Hsh.
              eauto. }
         repeat decomp_index.
         rewrite mesh_grid_map_Nat2Z_id in *.
         erewrite result_lookup_Z_option_transpose.
         reflexivity. lia. lia. eauto.
       - intros.
         erewrite result_has_shape_result_shape_Z in H1.
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
       - intros.
         erewrite result_has_shape_result_shape_Z in H1.
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
         rewrite <- H11.
         erewrite result_lookup_Z_option_transpose.
         reflexivity.
         lia. lia. eauto.
       - intros.
         erewrite result_has_shape_result_shape_Z in H1 by eauto.
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
         rewrite <- H11.
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
         invert H12. auto.
       - eapply no_dup_filter. eapply no_dup_mesh_grid.
       - eapply no_dup_filter. eapply no_dup_mesh_grid. }
     eapply well_formed_reindexer_transpose; try apply Henv; eauto.
     eapply well_formed_allocation_transpose;
       try apply Henv; try apply Hrdx; eauto.
     }
     { 
     eapply IHeval_expr in Heval; eauto. invs. clear IHeval_expr.
     cases (shape_to_index (result_shape_Z (V l))
                           (shape_to_vars (result_shape_Z (V l)))).
     { eapply shape_to_index_not_empty_Z in Heq0. propositional. }
     cases (reindexer
      (shape_to_index
         (result_shape_Z
            (transpose_result l
               (Z.to_nat (eval_Zexpr_Z_total $0 m0)
                :: Z.to_nat (eval_Zexpr_Z_total $0 n0)
                   :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0))))
         (shape_to_vars
            (result_shape_Z
               (transpose_result l
                  (Z.to_nat (eval_Zexpr_Z_total $0 m0)
                   :: Z.to_nat (eval_Zexpr_Z_total $0 n0)
                      :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0))))))).
     { eapply reindexer_not_empty in Heq1. propositional. apply Hrdx.
       erewrite result_has_shape_result_shape_Z.
       2: eapply result_has_shape_transpose_result; eauto.
       simpl.
       cases (Z.to_nat (eval_Zexpr_Z_total $0 m0)); simpl.
       inversion 1.
       cases (Z.to_nat (eval_Zexpr_Z_total $0 n0)).
       simpl. inversion 1. simpl. inversion 1. }
     cases (reindexer
              (let (v, d) := p0 in
               match l4 with
               | [] => p0 :: l4
               | (vi, di) :: xs => (vi, di) :: (v, d) :: xs
               end)).
     { unfold result_shape_Z, shape_to_index, shape_to_vars in Heq0.
       cases l; invert Heq0.
       - eapply reindexer_not_empty_vars_in_index in Heq2.
         propositional. apply Hrdx.
         simpl. repeat rewrite cup_empty_r.
         unfold not. intros. eapply constant_not_empty in H1. propositional.
         inversion 1.
       - eapply reindexer_not_empty_vars_in_index in Heq2.
         propositional. apply Hrdx.
         simpl. repeat rewrite cup_empty_r.
         cases (result_shape_nat r0); simpl; repeat rewrite cup_empty_r;
           unfold not; intros.
         eapply constant_not_empty in H1. propositional. inversion 1.
         eapply cup_empty in H1. invs.
         eapply constant_not_empty in H6. propositional. inversion 1.
     }
     invs.
     split; auto.
     f_equal. f_equal.
     { unfold tensor_to_array_delta.
       eapply eq_tensor_to_array_delta_by_indices_shuffle
         with (shuffle:=(fun l => match l with
                                 | x::y::xs => y::x::xs
                                 | _ => l
                                  end)).
       - intros.
         erewrite result_has_shape_result_shape_Z in H1.
         2: { eapply result_has_shape_transpose_result.
              simpl in Hsh.
              eauto. }
         repeat decomp_index.
         rewrite mesh_grid_map_Nat2Z_id in *.
         erewrite result_lookup_Z_option_transpose.
         reflexivity. lia. lia. eauto.
       - intros.
         erewrite result_has_shape_result_shape_Z in H1.
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
       - intros.
         erewrite result_has_shape_result_shape_Z in H1.
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
         rewrite <- H10.
         erewrite result_lookup_Z_option_transpose.
         reflexivity.
         lia. lia. eauto.
       - intros.
         erewrite result_has_shape_result_shape_Z in H1 by eauto.
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
         rewrite <- H10.
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
         invert H11. auto.
       - eapply no_dup_filter. eapply no_dup_mesh_grid.
       - eapply no_dup_filter. eapply no_dup_mesh_grid. }
     eapply well_formed_reindexer_transpose; try apply Henv; eauto.
     eapply well_formed_allocation_transpose;
       try apply Henv; try apply Hrdx; eauto.
     }
     apply Hrdx.     
   - (* FLATTEN *)
     simpl in *. invert Hsize.
     assert (result_has_shape (V l)
                              (map Z.to_nat
                                   (map (eval_Zexpr_Z_total $0) (n::m::l0)))).
     { eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
       eassumption. eassumption. eauto. }
     simpl map in *.
     cases (reindexer
      (shape_to_index (result_shape_Z (V (flatten_result l)))
                      (shape_to_vars
                         (result_shape_Z (V (flatten_result l)))))).
     { eapply reindexer_not_empty in Heq. propositional. apply Hrdx.
       erewrite result_has_shape_result_shape_Z.
       2: eapply result_has_shape_flatten; eassumption.
       simpl. cases ((Z.to_nat (eval_Zexpr_Z_total $0 n)
                      * Z.to_nat (eval_Zexpr_Z_total $0 m) =? 0)%nat).
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
     cases (reindexer
              (let (v, d) := p1 in
               match l5 with
               | [] => p1 :: l5
               | (vi, di) :: xs => ((v * di + vi)%z, (d * di)%z) :: xs
               end)).
     { erewrite result_has_shape_result_shape_Z in Heq0 by eassumption.
       simpl in Heq0.
       cases (Z.to_nat (eval_Zexpr_Z_total $0 n) =? 0)%nat; invert Heq0.
       - eapply reindexer_not_empty_vars_in_index in Heq1.
         propositional. apply Hrdx.
         simpl. repeat rewrite cup_empty_r.
         unfold not. intros. eapply constant_not_empty in H3. propositional.
         inversion 1.
       - eapply reindexer_not_empty_vars_in_index in Heq1.
         propositional. apply Hrdx.
         simpl. repeat rewrite cup_empty_r.
         cases (Z.to_nat (eval_Zexpr_Z_total $0 m) =? 0)%nat; simpl;
           repeat rewrite cup_empty_r; unfold app_no_dups;
           simpl; unfold not; intros.
         eapply constant_not_empty in H3. propositional. inversion 1.
         eapply cup_empty in H3. invs.
         eapply constant_not_empty in H11. propositional. inversion 1. }
     invs. split; auto.
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
                               (x*(Z.of_nat
                                     (Z.to_nat
                                        (eval_Zexpr_Z_total $0 m))) + y)%Z::xs
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
         pose proof (Z_div_mod 
                       z (Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)))).
         assert (Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)) > 0)%Z by lia.
         propositional.
         cases (Z.div_eucl z (Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)))).
         invert H17.
         clear H3.
         eexists (z0::z1::x0).
         rewrite Z.mul_comm.
         split. auto.
         eapply filter_In. propositional.
         repeat decomp_goal_index. propositional.
         assert (-1 * Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)) <
                   z0 * Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)))%Z
           by lia.
         eapply Zmult_lt_reg_r in H17.
         lia. lia.
         rewrite Nat2Z.inj_mul in H16.
         rewrite
           (Z.mul_comm (Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 n)))) in H16.
         eapply div_eucl_bound in H16.
         lia.
         assert (-1 * Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)) <
                   z0 * Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)))%Z
           by lia.
         eapply Zmult_lt_reg_r in H17.
         lia. lia.
         lia.
         repeat decomp_goal_index. propositional.
         rewrite <- H12.
         erewrite <- result_lookup_Z_option_flatten.
         rewrite Z.mul_comm. reflexivity.
         assert (-1 * Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)) <
                   z0 * Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)))%Z
           by lia.
         eapply Zmult_lt_reg_r in H17.
         lia. lia.
         rewrite Nat2Z.inj_mul in H16.
         rewrite
           (Z.mul_comm (Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 n)))) in H16.
         eapply div_eucl_bound in H16.
         apply H16. 
         assert (-1 * Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)) <
                   z0 * Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)))%Z
           by lia.
         eapply Zmult_lt_reg_r in H17.
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
         repeat decomp_index. invert H14.
         rewrite Z.mul_comm in H21. symmetry in H21.
         rewrite Z.mul_comm in H21. symmetry in H21.
         eapply Z.div_mod_unique in H21.
         invs. auto.
         lia. lia.
       - eapply no_dup_filter.
         eapply no_dup_mesh_grid.
       - eapply no_dup_filter.
         eapply no_dup_mesh_grid. }
     eapply well_formed_reindexer_flatten; try apply Henv; eauto.
     eapply well_formed_allocation_flatten;
       try apply Henv; try apply Hrdx; eauto.
     apply Hrdx. 
   - (* TRUNCR *) simpl in *. invert Hsize. invert Hconst.
     assert (result_has_shape (V l)
                              (map Z.to_nat
                                   (map (eval_Zexpr_Z_total $0) (m::l0))))
       as Hsh.
     { eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H2.
       eapply H2. eassumption. eauto. }
     invs.
     eq_size_of.
     pose proof H2 as Hconst.
     eapply constant_nonneg_bounds_size_of_no_vars in H2; eauto.
     invert H2.
     assert (eval_Zexpr_Z_total $0 k = kz)%Z.
     { pose proof H4. 
       eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
         with (v:=$0) in H2.
       eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
         with (v:=v) in H4.
       invert H2. invert H4. simpl in *.
       pose proof H.
       eapply eval_Zexpr_Z_eval_Zexpr in H,H4.
       eapply H2 in H. invert H.
       eapply H6 in H4. invert H4. auto. }
     subst. erewrite size_of_sizeof in H7 by eauto. simpl in H7.

     assert (Forall (fun x => (0 < x)%Z) (map (eval_Zexpr_Z_total $0) l0) \/
               Exists (fun x => x = 0%Z) (map (eval_Zexpr_Z_total $0) l0)).
     { eapply forall_nonneg_exists_zero_or_forall_pos_Z.
       pose proof H5.
       eapply constant_nonneg_bounds_size_of_nonneg in H5.
       2: { eauto. }
       2: { eapply forall_no_vars_eval_Zexpr_Z_total with (v:=$0).
            econstructor; eauto. }
       invert H5. eauto. }

     assert (eval_Zexpr_Z_total $0 m = eval_Zexpr_Z_total $0 k \/
               eval_Zexpr_Z_total $0 k < eval_Zexpr_Z_total $0 m)%Z
       as HHcase by lia.
     inversion HHcase as [ HHcase1 | HHcase2]; clear HHcase.
     { pose proof (truncl_list_length_empty
                     (Z.to_nat (eval_Zexpr_Z_total $0 k))
                     (rev l)).
       erewrite rev_length in H6.
       erewrite result_has_shape_length in H6.
       2: { simpl map in *. eauto. }
       assert (Z.to_nat (eval_Zexpr_Z_total $0 m) <=
                 Z.to_nat (eval_Zexpr_Z_total $0 k)) by lia.
       eapply H6 in H8.
       rewrite H8 in *. clear H6. simpl rev.
       invert Hpad.
       pose proof Hconst as HH. pose proof H12 as Hpad.
       eapply has_pad_gen_pad in H12.
       2: { eauto. }
       2: { eauto. }
       2: { eauto. }
       2: { eauto. }
       2: { eapply contexts_agree_result_has_shape. eauto. }
       2: { eauto. }
       simpl in H12. invs.
       rewrite firstn_all2 in H12.
       2: { erewrite rev_length. erewrite result_has_shape_length.
            2: simpl in *; eauto. lia. }
       clear H9. clear H14. clear H6. eapply Forall_rev in H12.
       rewrite rev_involutive in *.
       eapply forall_eq_gen_pad in H12. rewrite H12 in *.
       clear H7.
       eapply IHeval_expr in HH.
       2: { eauto. }
       2: { eauto. }
       2: { eauto. }
       2: { simpl. rewrite <- gen_pad_cons.
            apply well_formed_allocation_result_V in Halloc.
            2: apply Hrdx.
            invert Halloc.

            decomp_well_formed_reindexer.
            rewrite filter_negb_is_None_result_lookup_Z_option_gen_pad in *.
            split.
            unfold partial_injective. intros. invert H7.
            split.
            intros. destruct l2; destruct l3.
            eauto. invert H7. simpl in *. lia. invert H7. simpl in *. lia.
            destruct p0. destruct p1.
            eapply HeqZlist.
            erewrite <- eq_Z_tuple_index_list_cons_tup.
            erewrite <- eq_Z_tuple_index_list_cons_tup in H7.
            propositional. eapply eq_zexpr_sub. eauto. eauto.
            eapply eq_zexpr_sub. eauto. eauto.
            split.
            auto.
            split. intros.
            destruct l2. simpl. rewrite Hmap. eauto. eauto.
            destruct p0. simpl. rewrite Hmap. simpl.
            unfold subst_var_in_Z_tup at 1. simpl.
            erewrite subst_var_in_Zexpr_id with (lo:=k). eauto.
            rewrite H4. sets. eauto.
            split.
            intros.
            destruct l2. rewrite Hvarsarg. sets.
            destruct p0. simpl. rewrite Hvarsarg. simpl.
            rewrite H4. rewrite app_no_dups_empty_r. sets.
            unfold nondestructivity.
            split; intros.
            unfold tensor_to_array_delta in H14.
            rewrite filter_negb_is_None_result_lookup_Z_option_gen_pad in *.
            unfold tensor_to_array_delta_by_indices in *. simpl in *.
            rewrite dom_empty in *. sets.
            invert H6.
            eapply lookup_Some_dom in H14. sets. } 
       2: { simpl. rewrite <- gen_pad_cons.
            eapply well_formed_allocation_gen_pad.
            eapply well_formed_allocation_truncr
              with (x:=[]) (l0:=l0).
            simpl. rewrite rev_repeat.
            pose proof (truncl_list_length_empty
                          (Z.to_nat (eval_Zexpr_Z_total $0 k))
                          (repeat (gen_pad (map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)))
                                  (Z.to_nat (eval_Zexpr_Z_total $0 k)))).
            rewrite repeat_length in *.
            assert (Z.to_nat (eval_Zexpr_Z_total $0 k) <= Z.to_nat (eval_Zexpr_Z_total $0 k)) by lia.
            eapply H6 in H7.
            rewrite H7. eauto.
            eapply Hrdx. 
            simpl. eapply result_has_shape_repeat.
            eapply result_has_shape_gen_pad.
            lia. apply Hrdx.
            eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
            apply Henv. apply Hrdx. apply Hrdx.
            simpl.
            rewrite H12. simpl. rewrite repeat_length.
            simpl in Hsh. eapply result_has_shape_length in Hsh.
            rewrite repeat_length in Hsh. rewrite Hsh.
            rewrite HHcase1. 
            eapply result_has_shape_repeat.
            eapply result_has_shape_gen_pad. }
       2: { eauto. }
       2: { eauto. }
       2: { eauto. }
       cases (reindexer
      (shape_to_index (result_shape_Z (V []))
                      (shape_to_vars (result_shape_Z (V []))))).
       { eapply reindexer_not_empty_vars_in_index in Heq. propositional.
         apply Hrdx. simpl. unfold not. intros.
         eapply cup_empty in H6. invert H6.
         eapply cup_empty in H7. invert H7.
         eapply constant_not_empty in H6. propositional.
         inversion 1. }
       cases ((fun l : list (Zexpr * Zexpr) =>
          reindexer
            match l with
            | [] => l
            | (v, d) :: xs => (v, (d - k)%z) :: xs
            end)
           (shape_to_index
              (result_shape_Z
                 (V
                    (gen_pad_list
                       (Datatypes.length l
                        :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)))))
              (shape_to_vars
                 (result_shape_Z
                    (V
                       (gen_pad_list
                          (Datatypes.length l
                                            :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)))))))).
       { cases (shape_to_index
               (result_shape_Z
                  (V
                     (gen_pad_list
                        (length l
                                :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)))))
               (shape_to_vars
                  (result_shape_Z
                     (V
                        (gen_pad_list
                           (length l
                                   :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0))))))).
         eapply shape_to_index_not_empty_Z in Heq1. propositional.
         eapply reindexer_not_empty_vars_in_index in Heq0.
         propositional. apply Hrdx.
         unfold result_shape_Z,shape_to_index,shape_to_vars in Heq1.
         simpl in *. cases l. simpl in *.
         - invert Heq1. simpl. unfold not. intros.
           eapply cup_empty in H6. invert H6.
           eapply cup_empty in H7. invert H7.
           eapply constant_not_empty in H6. propositional. inversion 1.
         - invert Heq1. simpl. unfold not. intros.
           eapply cup_empty in H6. invert H6.
           eapply cup_empty in H7. invert H7.
           eapply constant_not_empty in H6. propositional. inversion 1. }
       unfold lookup_total in *. invs. split; auto.
       eapply well_formed_allocation_result_V in Halloc.
       invs. rewrite H7 in *. f_equal. f_equal.
       rewrite tensor_to_array_delta_empty_tensor.
       simpl. rewrite <- gen_pad_cons.
       rewrite tensor_to_array_delta_gen_pad. reflexivity.
       apply Hrdx.
     }     
     invert H2. 
     2: { pose proof Hpad as Hpad'. invert Hpad'.
          eapply IHeval_expr in Heval.
          2: { eauto. }
          2: { eauto. }
          2: { eauto. }
          2: { decomp_well_formed_reindexer.
               split.
               { erewrite result_has_shape_result_shape_Z by eauto.
                 unfold partial_injective. intros.
                 repeat decomp_index.
                 eapply mesh_grid_shape_pos in H18.
                 pose proof H6.
                 apply Forall_Exists_neg in H13. invert H13.
                 erewrite Forall_map in H18.
                 erewrite Forall_map in H18.
                 eapply Forall_impl. 2: apply H18.
                 simpl. intros. lia. }
               split.
               { intros.
                 cases l2; cases l3.
                 - eapply HeqZlist. eauto.
                 - invert H2. invs. invert H2.
                   simpl in *. lia.
                 - invert H2. invs. invert H2.
                   simpl in *. lia.
                 - cases p0. cases p1.
                   erewrite <- eq_Z_tuple_index_list_cons_tup in H2. invs.
                   eapply HeqZlist.
                   erewrite <- eq_Z_tuple_index_list_cons_tup. invs.
                   split. auto. split. 
                   eapply eq_zexpr_sub; eauto. eauto. }
               split.
               auto.
               split.
               intros. rewrite Hmap by auto.
               cases l2. reflexivity. cases p0. simpl.
               unfold subst_var_in_Z_tup at 1. simpl.
               rewrite (subst_var_in_Zexpr_id k). reflexivity.
               rewrite H4. sets.
               split.
               { intros. rewrite Hvarsarg.
                 cases l2. reflexivity. cases p0. f_equal.
                 simpl.
                 rewrite H4. rewrite app_no_dups_empty_r. reflexivity. }
               { invert Hpad.
                 pose proof Hconst as HH. pose proof H18 as Hpad.
                 eapply has_pad_gen_pad in H18.
                 2: { eauto. }
                 2: { eauto. }
                 2: { eauto. }
                 2: { eauto. }
                 2: { eapply contexts_agree_result_has_shape. eauto. }
                 2: { eauto. }
                 simpl in H18. invs.
                 unfold nondestructivity in *. split; intros.
                 unfold tensor_to_array_delta in H18.
                 rewrite exists_0_empty_mesh_grid in H18.
                 2: { erewrite result_has_shape_result_shape_Z by eauto.
                      pose proof H6.
                      eapply Exists_map.
                      eapply exists_filter_until_0. simpl.
                      right. eauto. }
                 simpl in H18. unfold tensor_to_array_delta_by_indices in H18.
                 simpl in H18. rewrite dom_empty in H18. sets.
                 eapply well_formed_allocation_result_V in Halloc.
                 invert Halloc. invert H18. eapply lookup_Some_dom in H16.
                 sets. eauto.                 
               }
          }
          2: { unfold well_formed_allocation.
               rewrite exists_0_empty_mesh_grid.
               simpl.
               eapply well_formed_allocation_result_V in Halloc.
               invs. rewrite H8.
               cases (shape_to_index (result_shape_Z (V l))
                                     (shape_to_vars (result_shape_Z (V l)))).
               { eapply shape_to_index_not_empty_Z in Heq. propositional. }
               cases (reindexer (let (v0, d) := p0 in (v0, (d - k)%z) :: l2)).
               { unfold result_shape_Z, shape_to_index, shape_to_vars in Heq.
                 simpl in *. invert Heq.
                 rewrite map_length in *.
                 cases l.
                 - simpl in *. invert H13.
                   eapply reindexer_not_empty_vars_in_index in Heq0.
                   propositional. apply Hrdx.
                   simpl. unfold not. intros.
                   eapply cup_empty in H2. invs.
                   eapply cup_empty in H13. invs.
                   eapply constant_not_empty in H2. propositional.
                   inversion 1.
                 - simpl in *. invert H13.
                   eapply reindexer_not_empty_vars_in_index in Heq0.
                   propositional. apply Hrdx.
                   simpl. unfold not. intros.
                   eapply cup_empty in H2. invs.
                   eapply cup_empty in H13. invs.
                   eapply constant_not_empty in H2. propositional.
                   inversion 1. }
               eexists. split. reflexivity. sets.
               apply Hrdx.
               erewrite result_has_shape_result_shape_Z by eauto.
               eapply Exists_map.
               eapply exists_filter_until_0. simpl. right. eauto. }
          2: { eauto. }
          2: { eauto. }
          
          cases (shape_to_index (result_shape_Z (V l))
                                (shape_to_vars (result_shape_Z (V l)))).
          { eapply shape_to_index_not_empty_Z in Heq. propositional. }
          cases (reindexer (let (v, d) := p0 in (v, (d - k)%z) :: l2)).
          { unfold result_shape_Z, shape_to_index, shape_to_vars in Heq.
            simpl in *. invert Heq.
            rewrite map_length in *.
            cases l.
            - simpl in *. invert H8.
              eapply reindexer_not_empty_vars_in_index in Heq0.
              propositional. apply Hrdx.
              simpl. unfold not. intros.
              eapply cup_empty in H2. invs.
              eapply cup_empty in H8. invs.
              eapply constant_not_empty in H2. propositional.
              inversion 1.
            - simpl in *. invert H8.
              eapply reindexer_not_empty_vars_in_index in Heq0.
              propositional. apply Hrdx.
              simpl. unfold not. intros.
              eapply cup_empty in H2. invs.
              eapply cup_empty in H8. invs.
              eapply constant_not_empty in H2. propositional.
              inversion 1. }
          invs.
          unfold lookup_total.
          eapply well_formed_allocation_result_V in Halloc. invs.
          rewrite H8. 
          cases (reindexer
                   (shape_to_index
                      (result_shape_Z
                         (V (rev
                               (truncl_list
                                  (Z.to_nat (eval_Zexpr_Z_total $0 k))
                                  (rev l)))))
                      (shape_to_vars
                         (result_shape_Z
                            (V (rev (truncl_list
                                       (Z.to_nat
                                          (eval_Zexpr_Z_total $0 k))
                                       (rev l)))))))).
          { erewrite result_has_shape_result_shape_Z in Heq1.
            2: { eapply result_has_shape_rev.
                 eapply result_has_shape_truncl_list.
                 eapply result_has_shape_rev.
                 erewrite <- result_has_shape_filter_until_0.
                 simpl in *. eauto. }
            unfold result_shape_Z, shape_to_index, shape_to_vars in Heq1.
            simpl in *. 
            rewrite map_length in *.
            cases (Z.to_nat (eval_Zexpr_Z_total $0 m) -
                             Z.to_nat (eval_Zexpr_Z_total $0 k)).
            - simpl in *. 
              eapply reindexer_not_empty_vars_in_index in Heq1.
              propositional. apply Hrdx.
              simpl. unfold not. intros.
              eapply cup_empty in H2. invs.
              eapply cup_empty in H13. invs.
              eapply constant_not_empty in H2. propositional.
              inversion 1.
            - simpl in *. 
              eapply reindexer_not_empty_vars_in_index in Heq1.
              propositional. apply Hrdx.
              simpl. unfold not. intros.
              eapply cup_empty in H2. invs.
              eapply cup_empty in H13. invs.
              eapply constant_not_empty in H2. propositional.
              inversion 1. }
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
          rewrite <- Z2Nat.inj_sub by lia.
          rewrite <- map_cons.
          eapply exists_filter_until_0.
          right. eauto.
          erewrite result_has_shape_result_shape_Z by eauto.
          erewrite Exists_map.
          eapply exists_filter_until_0.
          simpl. right. eauto.
          apply Hrdx. eauto.
     }
     
     assert (exists l', l =
                          l' ++
                             gen_pad_list
                             (Z.to_nat
                                (eval_Zexpr_Z_total $0 k)
                                :: map Z.to_nat
                                (map (eval_Zexpr_Z_total $0) l0)))%list.
     { invert Hpad.
       eapply has_pad_gen_pad in H11.
       2: { eauto. }
       2: { eauto. } 
       2: { eauto. }
       2: { eauto. }
       2: { eapply contexts_agree_result_has_shape; eauto. }
       2: eauto.
       simpl in *. invs.
       rewrite <- (rev_involutive l).
       erewrite <- firstn_skipn
         with (l:=rev l) (n:=(Z.to_nat (eval_Zexpr_Z_total $0 k))).
       rewrite rev_app_distr.
       eexists (rev (skipn (Z.to_nat (eval_Zexpr_Z_total $0 k)) (rev l))).
       f_equal.
       eapply forall_firstn_ge in H11.
       2: { apply H15. }
       eapply forall_eq_gen_pad in H11.
       simpl in H11.
       rewrite H11.
       rewrite rev_repeat. rewrite firstn_length.
       rewrite rev_length.
       erewrite result_has_shape_length by eauto. f_equal. lia. }

     invs. 
     invert Hpad.
     
     eapply IHeval_expr in Heval; clear IHeval_expr; eauto.
     2: { eapply well_formed_allocation_result_V in Halloc.
          invert Halloc.
          eapply well_formed_reindexer_truncr. eauto.
          repeat rewrite map_cons in Hsh. eauto.
          try apply Henv.
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
          lia. lia. apply H2.
          eauto. lia. apply Hrdx.
     }
     2: { eapply well_formed_allocation_truncr. eauto.
          apply Hrdx. repeat rewrite map_cons in *. eauto. lia.
          try apply Henv; try apply Hrdx; eauto.
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
          apply Henv. apply Hrdx. apply Hrdx. }
     cases (reindexer
              (shape_to_index
                 (result_shape_Z
                    (V
                       (rev
                          (truncl_list
                             (Z.to_nat (eval_Zexpr_Z_total $0 k))
                             (rev
                                (x ++
                                   gen_pad_list
                                   (Z.to_nat (eval_Zexpr_Z_total $0 k)
                                             :: map Z.to_nat
                                             (map (eval_Zexpr_Z_total $0) l0))))))))
                 (shape_to_vars
                    (result_shape_Z
                       (V
                          (rev
                             (truncl_list
                                (Z.to_nat (eval_Zexpr_Z_total $0 k))
                                (rev
                                   (x ++
                                      gen_pad_list
                                      (Z.to_nat (eval_Zexpr_Z_total $0 k)
                                                :: map Z.to_nat
                                                (map (eval_Zexpr_Z_total $0) l0))))))))))).
     { eapply reindexer_not_empty in Heq. propositional. apply Hrdx.
       erewrite result_has_shape_result_shape_Z.
       2: { eapply result_has_shape_rev.
            eapply result_has_shape_truncl_list.
            erewrite <- result_has_shape_filter_until_0.
            eapply result_has_shape_rev.
            repeat rewrite map_cons in Hsh.
            eauto. }
       simpl.
       cases ((Z.to_nat (eval_Zexpr_Z_total $0 m) -
                 Z.to_nat (eval_Zexpr_Z_total $0 k) =? 0)%nat);
         inversion 1. }
     cases (shape_to_index
                  (result_shape_Z
                     (V
                        (x ++
                         gen_pad_list
                           (Z.to_nat (eval_Zexpr_Z_total $0 k)
                            :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)))))
                  (shape_to_vars
                     (result_shape_Z
                        (V
                           (x ++
                            gen_pad_list
                              (Z.to_nat (eval_Zexpr_Z_total $0 k)
                               :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0))))))).
     { eapply shape_to_index_not_empty_Z in Heq0. propositional. }
     cases (reindexer (let (v, d) := p1 in (v, (d - k)%z) :: l2)).
     { unfold shape_to_index, shape_to_vars, result_shape_Z in Heq0.
       simpl in Heq0.
       cases ((x ++
                 repeat
                 (gen_pad
                    (map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)))
                 (Z.to_nat (eval_Zexpr_Z_total $0 k)))%list);
         invert Heq0.
       - eapply reindexer_not_empty_vars_in_index in Heq1. propositional.
         apply Hrdx. simpl. unfold app_no_dups. simpl.
         unfold not. intros.
         eapply cup_empty in H2. invs.
         eapply cup_empty in H8. invs.
         eapply constant_not_empty in H2. propositional. inversion 1.
       - eapply reindexer_not_empty_vars_in_index in Heq1. propositional.
         apply Hrdx. simpl. unfold app_no_dups. simpl.
         unfold not. intros.
         eapply cup_empty in H2. invs.
         eapply cup_empty in H8. invs.
         eapply constant_not_empty in H2. propositional. inversion 1. }
     invs.
     pose proof Halloc as Halloc1.
     eapply well_formed_allocation_result_V in Halloc1;
       try apply Hrdx. invs.
     unfold lookup_total. rewrite H8.
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
     repeat rewrite <- map_cons.

     unfold tensor_to_array_delta.

     rewrite rev_app_distr in *.
     simpl gen_pad_list in *.
     rewrite rev_repeat in *.
     pose proof truncl_list_gen_pad_id.
     simpl gen_pad_list in H2.
     rewrite H2 in *. clear H2.
     rewrite rev_involutive in *.
     
     erewrite result_has_shape_result_shape_Z by eassumption.

     repeat rewrite <- map_cons.
     pose proof filter_pad_r_mesh_grid. simpl gen_pad_list in H2.
     rewrite H2. clear H2.

     2: { repeat rewrite map_cons in Hsh.
          pose proof Hsh. eapply result_has_shape_app_l in Hsh.
          eapply result_has_shape_app_r in H13.
          2: { rewrite repeat_length. reflexivity. }
          2: { reflexivity. }
          simpl map.
          simpl. replace (Z.to_nat (eval_Zexpr_Z_total $0 m)) with
            (Z.to_nat (eval_Zexpr_Z_total $0 k) +
               (Z.to_nat (eval_Zexpr_Z_total $0 m) -
                  Z.to_nat (eval_Zexpr_Z_total $0 k))) by lia.
          eapply result_has_shape_concat.
          eapply result_has_shape_repeat_gen_pad.
          eauto. }
     2: { lia. }

     eapply eq_tensor_to_array_delta_by_indices_shuffle with
       (shuffle:=fun x => x).
        + intros.
          erewrite result_has_shape_result_shape_Z in H2.
          2: { repeat rewrite map_cons in Hsh.
               eapply result_has_shape_app_r; eauto. }
          rewrite repeat_length in *.
          repeat decomp_index.
          simpl. rewrite nth_error_app1. auto.
          erewrite result_has_shape_length.
          2: { repeat rewrite map_cons in Hsh.
               eapply result_has_shape_app_r; eauto. }
          rewrite repeat_length. lia.
        + intros.
          erewrite result_has_shape_result_shape_Z in H2.
          2: { repeat rewrite map_cons in Hsh.
               eapply result_has_shape_app_r; eauto. }
          rewrite repeat_length in *.
          repeat decomp_index.
          rewrite eq_partial_interpret_reindexer_truncr;
            try apply Henv; try apply Hrdx.
          reflexivity.
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
          lia. lia. lia.
        + intros.
          erewrite result_has_shape_result_shape_Z in H2.
          2: { repeat rewrite map_cons in Hsh.
               eapply result_has_shape_app_r; eauto. }
          rewrite repeat_length in *. eauto.
        + intros.
          erewrite result_has_shape_result_shape_Z.
          2: { repeat rewrite map_cons in Hsh.
               eapply result_has_shape_app_r; eauto. }
          rewrite repeat_length in *. eauto.
        + decomp_well_formed_reindexer.
          pose proof Hinj.
          erewrite result_has_shape_result_shape_Z in H2.
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
          rewrite repeat_length in *. eauto.
          eapply partial_injective_truncr; eauto.
          apply Henv.
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
          lia. lia.
        + unfold injective. propositional.
        + eapply no_dup_filter.
          eapply no_dup_mesh_grid.
        + eapply no_dup_filter.
          eapply no_dup_mesh_grid.
   - (* TRUNCL *) simpl in *. invert Hsize. invert Hconst.
     assert (result_has_shape (V l)
                              (map Z.to_nat
                                   (map (eval_Zexpr_Z_total $0) (m::l0))))
       as Hsh.
     { eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H2.
       eapply H2. eassumption. eauto. }
     invs. eq_size_of. erewrite size_of_sizeof in * by eauto. simpl in H7.
     assert (eval_Zexpr_Z_total $0 k = kz)%Z.
       { pose proof H4.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
           with (v:=$0) in H4.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
           with (v:=v) in H6.
         invert H6. invert H4. simpl in *.
         pose proof H.
         eapply eval_Zexpr_Z_eval_Zexpr in H,H4.
         eapply H6 in H. invert H.
         eapply H6 in H4. invert H4. auto. }
       subst. 

       assert (Forall (fun x => (0 < x)%Z) (map (eval_Zexpr_Z_total $0) l0) \/
               Exists (fun x => x = 0%Z) (map (eval_Zexpr_Z_total $0) l0)).
     { eapply forall_nonneg_exists_zero_or_forall_pos_Z.
       pose proof H5.
       eapply constant_nonneg_bounds_size_of_nonneg in H5.
       2: { eauto. }
       2: { eapply forall_no_vars_eval_Zexpr_Z_total with (v:=$0).
            eapply constant_nonneg_bounds_size_of_no_vars. eauto. eauto. }
       invert H5. eauto. }
     assert (eval_Zexpr_Z_total $0 m = eval_Zexpr_Z_total $0 k \/
               eval_Zexpr_Z_total $0 k < eval_Zexpr_Z_total $0 m)%Z
       as HHcase by lia.
     inversion HHcase as [ HHcase1 | HHcase2]; clear HHcase.
     { pose proof (truncl_list_length_empty
                     (Z.to_nat (eval_Zexpr_Z_total $0 k)) l).
       erewrite result_has_shape_length in H8.
       2: { simpl map in *. eauto. }
       assert (Z.to_nat (eval_Zexpr_Z_total $0 m) <=
                 Z.to_nat (eval_Zexpr_Z_total $0 k)) by lia.
       eapply H8 in H9.
       rewrite H9 in *. clear H8.
       invert Hpad. 
       pose proof H2 as HH. pose proof H11 as Hpad.
       eapply has_pad_gen_pad in H11.
       2: { eauto. }
       2: { eauto. }
       2: { eauto. }
       2: { eauto. }
       2: { eapply contexts_agree_result_has_shape. eauto. }
       2: { eauto. }
       simpl in H11. invs.
       rewrite firstn_all2 in H8.
       2: { erewrite result_has_shape_length.
            2: simpl in *; eauto. lia. }
       clear H13. clear H10. clear H11.
       eapply forall_eq_gen_pad in H8. rewrite H8 in *.
       eapply IHeval_expr in HH.
       2: { eauto. }
       2: { eauto. }
       2: { eauto. }
       2: { simpl. rewrite <- gen_pad_cons.
            eapply well_formed_allocation_result_V in Halloc.
            invert Halloc.
            decomp_well_formed_reindexer.
            erewrite filter_negb_is_None_result_lookup_Z_option_gen_pad.
            split.
            unfold partial_injective. intros. invert H11.
            split.
            intros. destruct l2; destruct l3. eauto.
            invert H11. simpl in *. lia.
            invert H11. simpl in *. lia.
            destruct p0. destruct p1.
            eapply HeqZlist.
            erewrite <- eq_Z_tuple_index_list_cons_tup.
            erewrite <- eq_Z_tuple_index_list_cons_tup in H11.
            propositional.
            eapply eq_zexpr_sub; eauto.
            eapply eq_zexpr_sub; eauto.
            eapply eq_zexpr_sub; eauto.
            eapply eq_zexpr_sub; eauto.
            split. auto.
            split. intros.
            destruct l2. simpl. rewrite Hmap. eauto. eauto.
            destruct p0. rewrite Hmap. simpl.
            unfold subst_var_in_Z_tup at 1. simpl.
            rewrite subst_var_in_Zexpr_id with (lo:=k). eauto.
            rewrite H4. sets. eauto.
            split.
            intros. destruct l2. rewrite Hvarsarg. sets.
            destruct p0. simpl. rewrite Hvarsarg. simpl.
            rewrite H4. rewrite app_no_dups_empty_r.
            rewrite app_no_dups_empty_r. sets.
            unfold nondestructivity.
            unfold tensor_to_array_delta.
            erewrite filter_negb_is_None_result_lookup_Z_option_gen_pad.
            unfold tensor_to_array_delta_by_indices.
            simpl. rewrite dom_empty. split; intros. sets.
            invert H10.
            eapply lookup_Some_dom in H14. sets. apply Hrdx. }
       2: { simpl. rewrite <- gen_pad_cons.
            eapply well_formed_allocation_gen_pad.
            eapply well_formed_allocation_truncl
              with (x:=[]) (l0:=l0).
            eauto.
            eapply Hrdx. 
            simpl. rewrite app_nil_r. eapply result_has_shape_repeat.
            eapply result_has_shape_gen_pad.
            lia. apply Hrdx.
            eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
            eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
            apply Henv. apply Hrdx. apply Hrdx.
            simpl.
            rewrite H8. simpl. rewrite repeat_length.
            simpl in Hsh. eapply result_has_shape_length in Hsh.
            rewrite repeat_length in Hsh. rewrite Hsh.
            rewrite HHcase1. rewrite app_nil_r.
            eapply result_has_shape_repeat.
            eapply result_has_shape_gen_pad. }
       2: { eauto. }
       2: { eauto. }
       2: { eauto. }
       cases (reindexer
      (shape_to_index (result_shape_Z (V []))
                      (shape_to_vars (result_shape_Z (V []))))).
       { eapply reindexer_not_empty_vars_in_index in Heq. propositional.
         apply Hrdx. simpl. unfold not. intros.
         eapply cup_empty in H10. invert H10.
         eapply cup_empty in H11. invert H11.
         eapply constant_not_empty in H10. propositional.
         inversion 1. }
       cases ((fun l : list (Zexpr * Zexpr) =>
          reindexer
            match l with
            | [] => l
            | (v, d) :: xs => ((v-k)%z, (d - k)%z) :: xs
            end)
           (shape_to_index
              (result_shape_Z
                 (V
                    (gen_pad_list
                       (Datatypes.length l
                        :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)))))
              (shape_to_vars
                 (result_shape_Z
                    (V
                       (gen_pad_list
                          (Datatypes.length l
                                            :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)))))))).
       { cases (shape_to_index
               (result_shape_Z
                  (V
                     (gen_pad_list
                        (length l
                                :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)))))
               (shape_to_vars
                  (result_shape_Z
                     (V
                        (gen_pad_list
                           (length l
                                   :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0))))))).
         eapply shape_to_index_not_empty_Z in Heq1. propositional.
         eapply reindexer_not_empty_vars_in_index in Heq0.
         propositional. apply Hrdx.
         unfold result_shape_Z,shape_to_index,shape_to_vars in Heq1.
         simpl in *. cases l. simpl in *.
         - invert Heq1. simpl. unfold not. intros.
           eapply cup_empty in H10. invert H10.
           eapply cup_empty in H11. invert H11.
           eapply constant_not_empty in H10. propositional. inversion 1.
         - invert Heq1. simpl. unfold not. intros.
           eapply cup_empty in H10. invert H10.
           eapply cup_empty in H11. invert H11.
           eapply constant_not_empty in H10. propositional. inversion 1. }
       unfold lookup_total in *. invs. split; auto.
       eapply well_formed_allocation_result_V in Halloc.
       invs. rewrite H8 in *. f_equal. f_equal.
       rewrite tensor_to_array_delta_empty_tensor.
       simpl. rewrite <- gen_pad_cons.
       rewrite tensor_to_array_delta_gen_pad. reflexivity.
       apply Hrdx. }
       
     invert H6. 
     2: { pose proof Hpad as Hpad'. invert Hpad'.
          eapply IHeval_expr in Heval.
          2: { eauto. }
          2: { eauto. }
          2: { eauto. }
          2: { decomp_well_formed_reindexer.
               split.
               { erewrite result_has_shape_result_shape_Z by eauto.
                 unfold partial_injective. intros.
                 repeat decomp_index.
                 eapply mesh_grid_shape_pos in H17.
                 pose proof H8.
                 apply Forall_Exists_neg in H12. invert H12.
                 erewrite Forall_map in H17.
                 erewrite Forall_map in H17.
                 eapply Forall_impl. 2: apply H17.
                 simpl. intros. lia. }
               split.
               { intros.
                 cases l2; cases l3.
                 - eapply HeqZlist. eauto.
                 - invert H6. invs. invert H6.
                   simpl in *. lia.
                 - invert H6. invs. invert H6.
                   simpl in *. lia.
                 - cases p0. cases p1.
                   erewrite <- eq_Z_tuple_index_list_cons_tup in H6. invs.
                   eapply HeqZlist.
                   erewrite <- eq_Z_tuple_index_list_cons_tup. 
                   split. eapply eq_zexpr_sub; auto. split. 
                   eapply eq_zexpr_sub; eauto. eauto. }
               split.
               auto.
               split.
              intros. rewrite Hmap by auto.
              cases l2. reflexivity. cases p0. simpl.
              unfold subst_var_in_Z_tup at 1. simpl.
              rewrite (subst_var_in_Zexpr_id k). reflexivity.
              rewrite H4. sets.
              split.
              { intros. rewrite Hvarsarg.
                cases l2. reflexivity. cases p0. f_equal.
                simpl.
                rewrite H4. repeat rewrite app_no_dups_empty_r.
                reflexivity. }
              { unfold nondestructivity in *. split; intros.
                 unfold tensor_to_array_delta in H12.
                 rewrite exists_0_empty_mesh_grid in H12.
                 2: { erewrite result_has_shape_result_shape_Z by eauto.
                      eapply Exists_map.
                      eapply exists_filter_until_0. simpl.
                      right. eauto. }
                 simpl in H12. unfold tensor_to_array_delta_by_indices in H12.
                 simpl in H12. rewrite dom_empty in H12. sets.
                 eapply well_formed_allocation_result_V in Halloc.
                 invert Halloc. invert H12. eapply lookup_Some_dom in H9.
                 sets. eauto. }
          }
          2: { unfold well_formed_allocation.
               rewrite exists_0_empty_mesh_grid.
               simpl.
               eapply well_formed_allocation_result_V in Halloc.
               invs. rewrite H9.
               cases (shape_to_index (result_shape_Z (V l))
                                     (shape_to_vars (result_shape_Z (V l)))).
               { eapply shape_to_index_not_empty_Z in Heq. propositional. }
               cases (reindexer (let (v0, d) := p0 in
                                 ((v0 - k)%z, (d - k)%z) :: l2)).
               { unfold shape_to_index,result_shape_Z,shape_to_vars in Heq.
                 simpl in Heq. invert Heq.
                 repeat rewrite map_length in *.
                 cases l.
                 - simpl in *. invert H12.
                   eapply reindexer_not_empty_vars_in_index in Heq0.
                   propositional. apply Hrdx.
                   simpl. unfold app_no_dups.
                   rewrite <- union_constant.
                   simpl. unfold not. intros. 
                   eapply cup_empty in H6. invs.
                   eapply cup_empty in H12. invs.
                   eapply cup_empty in H6. invs.
                   eapply constant_not_empty in H12. propositional.
                   inversion 1.
                 - simpl in *. invert H12.
                   eapply reindexer_not_empty_vars_in_index in Heq0.
                   propositional. apply Hrdx.
                   simpl. unfold app_no_dups.
                   rewrite <- union_constant.
                   simpl. unfold not. intros. 
                   eapply cup_empty in H6. invs.
                   eapply cup_empty in H12. invs.
                   eapply cup_empty in H6. invs.
                   eapply constant_not_empty in H12. propositional.
                   inversion 1. }
               eexists. split. reflexivity. sets.
               apply Hrdx.
               erewrite result_has_shape_result_shape_Z by eauto.
               eapply Exists_map.
               eapply exists_filter_until_0. simpl. right. eauto. }
          2: { eauto. }
          2: { eauto. }
          
          cases (shape_to_index (result_shape_Z (V l))
                                (shape_to_vars (result_shape_Z (V l)))).
          { eapply shape_to_index_not_empty_Z in Heq. propositional. }

          cases (reindexer (let (v, d) := p0 in ((v - k)%z, (d - k)%z) :: l2)).
          { unfold shape_to_index,result_shape_Z,shape_to_vars in Heq.
            simpl in Heq0. invert Heq.
            repeat rewrite map_length in *.
            cases l.
            - simpl in *. invert H9.
              eapply reindexer_not_empty_vars_in_index in Heq0.
              propositional. apply Hrdx.
              simpl. unfold app_no_dups.
              rewrite <- union_constant.
              simpl. unfold not. intros. 
              eapply cup_empty in H6. invs.
              eapply cup_empty in H9. invs.
              eapply cup_empty in H6. invs.
              eapply constant_not_empty in H9. propositional.
              inversion 1.
            - simpl in *. invert H9.
              eapply reindexer_not_empty_vars_in_index in Heq0.
              propositional. apply Hrdx.
              simpl. unfold app_no_dups.
              rewrite <- union_constant.
              simpl. unfold not. intros. 
              eapply cup_empty in H6. invs.
              eapply cup_empty in H9. invs.
              eapply cup_empty in H6. invs.
              eapply constant_not_empty in H9. propositional.
              inversion 1. }
          invs.
          unfold lookup_total.
          eapply well_formed_allocation_result_V in Halloc. invs.
          rewrite H9. 
          cases (reindexer
                   (shape_to_index
                      (result_shape_Z (V (truncl_list (Z.to_nat (eval_Zexpr_Z_total $0 k)) l)))
                      (shape_to_vars
                         (result_shape_Z (V (truncl_list (Z.to_nat (eval_Zexpr_Z_total $0 k)) l)))))).
          { erewrite result_has_shape_result_shape_Z in Heq1.
            2: { eapply result_has_shape_truncl_list.
                 erewrite <- result_has_shape_filter_until_0.
                 simpl in *. eauto. }
            simpl in *.
            cases (Z.to_nat (eval_Zexpr_Z_total $0 m) -
                     Z.to_nat (eval_Zexpr_Z_total $0 k)).
            - simpl in *.
              eapply reindexer_not_empty_vars_in_index in Heq1.
              propositional. apply Hrdx.
              simpl. unfold not. intros.
              eapply cup_empty in H6. invs.
              eapply cup_empty in H12. invs.
              eapply constant_not_empty in H6. propositional. inversion 1. 
            - simpl in *.
              eapply reindexer_not_empty_vars_in_index in Heq1.
              propositional. apply Hrdx.
              simpl. unfold not. intros.
              eapply cup_empty in H6. invs.
              eapply cup_empty in H12. invs.
              eapply constant_not_empty in H6. propositional. inversion 1. }
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
          eapply Exists_map.
          rewrite <- Z2Nat.inj_sub by lia.
          rewrite <- map_cons.
          eapply exists_filter_until_0.
          right. eauto.
          erewrite result_has_shape_result_shape_Z by eauto.
          eapply Exists_map.
          eapply exists_filter_until_0.
          simpl. right. eauto.
          apply Hrdx. eauto. }
     
     assert (exists l', l =                        
                          gen_pad_list
                            (Z.to_nat
                               (eval_Zexpr_Z_total $0 k)
                               :: map Z.to_nat
                               (map (eval_Zexpr_Z_total $0) l0))++l')%list.
          { invert Hpad.
            eapply has_pad_gen_pad in H10.
            2: { eauto. }
            2: { eauto. } 
            2: { eauto. }
            2: { eauto. }
            2: { eapply contexts_agree_result_has_shape. eauto. }
            2: { eauto. }
            simpl in *. invs.
            erewrite <- firstn_skipn
              with (l:=l) (n:=(Z.to_nat (eval_Zexpr_Z_total $0 k))).
            eexists (skipn (Z.to_nat (eval_Zexpr_Z_total $0 k)) l).
            f_equal.
            eapply forall_firstn_ge in H6.
            2: apply H14.
            eapply forall_eq_gen_pad in H6.
            simpl in H6.
            rewrite H6.
            rewrite firstn_length.
            erewrite result_has_shape_length by eauto. f_equal. lia. }
          invs.     

     rewrite truncl_list_gen_pad_id in *.

     invert Hpad.
     eapply IHeval_expr in Heval; clear IHeval_expr; eauto.
     2: { eapply well_formed_allocation_result_V in Halloc.
          invert Halloc.
          eapply well_formed_reindexer_truncl; 
          try apply Henv.
          auto. simpl in *. eassumption.
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto.
          lia. lia. eapply H6. lia. apply Hrdx. }
     2: { eapply well_formed_allocation_truncl;
          try apply Henv; try apply Hrdx; auto.
          simpl in *. eauto.
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
          eapply constant_nonneg_bounds_sizeof_no_vars in H2.
          erewrite size_of_sizeof in H2; eauto. invert H2.
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
     }

     cases (reindexer
              (shape_to_index (result_shape_Z (V x))
                              (shape_to_vars (result_shape_Z (V x))))).
     { eapply reindexer_not_empty in Heq. propositional. apply Hrdx.
       cases x; unfold result_shape_Z; simpl; inversion 1. }
     
     cases (shape_to_index
              (result_shape_Z
                 (V
                    (gen_pad_list
                       (Z.to_nat (eval_Zexpr_Z_total $0 k)
                                 :: map Z.to_nat
                                 (map (eval_Zexpr_Z_total $0) l0)) ++ x)))
              (shape_to_vars
                 (result_shape_Z
                    (V
                       (gen_pad_list
                          (Z.to_nat (eval_Zexpr_Z_total $0 k)
                                    :: map Z.to_nat
                                    (map (eval_Zexpr_Z_total $0) l0)) ++
                          x))))).
     { eapply shape_to_index_not_empty_Z in Heq0. propositional. }
     cases (reindexer
              (let (v, d) := p1 in
               ((v - k)%z, (d - k)%z) :: l2)).
     { erewrite result_has_shape_result_shape_Z in Heq0.
       2: { eauto. }
       unfold shape_to_index, shape_to_vars, result_shape_Z in Heq0.
       simpl in Heq0.
       cases (Z.to_nat (eval_Zexpr_Z_total $0 m)). lia.
       cases l; invert Heq0.
       - eapply reindexer_not_empty_vars_in_index in Heq1. propositional.
         apply Hrdx. simpl. unfold app_no_dups. simpl.
         unfold not. intros.
         eapply cup_empty in H6. invs.
         eapply cup_empty in H9. invs.
         eapply constant_not_empty in H6. propositional. inversion 1.
       - eapply reindexer_not_empty_vars_in_index in Heq1. propositional.
         apply Hrdx. simpl. unfold app_no_dups. simpl.
         unfold not. intros.
         eapply cup_empty in H6. invs.
         eapply cup_empty in H9. invs.
         eapply constant_not_empty in H6. propositional. inversion 1. }
     invs.
     pose proof Halloc as Halloc1.
     
     eapply well_formed_allocation_result_V in Halloc1;
       try apply Hrdx. invs.
     unfold lookup_total. rewrite H9.
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
     repeat rewrite map_cons.
     rewrite <- map_cons.
     rewrite <- map_cons.
     rewrite filter_pad_l_mesh_grid; auto.
     eapply eq_tensor_to_array_delta_by_indices_shuffle
       with (shuffle:=(fun l => match l with
                                | [] => l
                                | x::xs => (x+eval_Zexpr_Z_total $0 k)%Z::xs
                                end)).
        + intros. repeat decomp_index.
          eapply result_lookup_Z_option_concat_l; lia.
        + intros. repeat decomp_index.
          eapply eq_partial_interpret_reindexer_truncl.
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto.
          apply Henv.
          apply Hrdx.
          apply Hrdx.
          apply Hrdx.
          apply Hrdx.
          lia. lia. lia.
        + intros. repeat decomp_index.
          eapply in_map_iff. eexists (z::x2).
          propositional.
          eapply filter_In. propositional.
          repeat decomp_goal_index. propositional.
        + intros. eapply in_map_iff in H6. invs.
          repeat decomp_index.
          eexists (z::x3). propositional.
          eapply filter_In. propositional.
          repeat decomp_goal_index.
          propositional.
        + decomp_well_formed_reindexer. pose proof Hinj.
          erewrite result_has_shape_result_shape_Z in H6.
          eapply H6.
          eapply result_has_shape_app_l; eauto.
          simpl. rewrite repeat_length. reflexivity.
        + decomp_well_formed_reindexer.
          eapply partial_injective_truncl.
          eauto.
          eassumption.
          apply Henv.         
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto.
          auto. auto. auto. auto. lia. lia. lia.
        + unfold injective. propositional.
          repeat decomp_index.
          invert H15. f_equal. lia.
        + eapply no_dup_filter. eapply no_dup_mesh_grid.
        + eapply no_dup_injective_map.
          2: { eapply no_dup_filter.
               eapply no_dup_mesh_grid. }
          unfold injective.
          propositional.
          repeat decomp_index.
          invert H15. f_equal. lia.
   - (* PADR *) simpl in *. invert Hconst. invert Hsize. eq_size_of.
     invert H6.
        assert (result_has_shape (V l)
                                 (map Z.to_nat
                                      (map (eval_Zexpr_Z_total $0) (m::l0))))
          as Hsh.
        { eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
          eassumption. eassumption. eauto. }
        pose proof H4.
        eapply constant_nonneg_bounds_sizeof_nonneg in H6.
        2: { erewrite size_of_sizeof by eassumption.
             eapply forall_no_vars_eval_Zexpr_Z_total with (v:=$0).
             eapply constant_nonneg_bounds_sizeof_no_vars in H6.
             erewrite size_of_sizeof in * by eassumption.
             eauto. }
        invert H6.
        pose proof H4.
        eapply constant_nonneg_bounds_sizeof_no_vars in H6.
        erewrite size_of_sizeof in * by eassumption.
        invert H6. invs.
        pose proof Halloc as Halloc1.
        eapply well_formed_allocation_result_V in Halloc1.
        inversion Halloc1 as [a Htmp]. clear Halloc1.
        inversion Htmp as [Heq Hsub]. clear Htmp.

        assert (eval_Zexpr_Z_total $0 k = kz)%Z.
        { pose proof H6.
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
            with (v:=$0) in H6.
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
            with (v:=v) in H5.
          invert H6. invert H5. simpl in *.
          pose proof H.
          eapply eval_Zexpr_Z_eval_Zexpr in H,H5.
          eapply H8 in H. invert H.
          eapply H6 in H5. invert H5. auto. }

        assert ((map (eval_Zexpr_Z_total $0) l0) = sz).
        { eapply constant_nonneg_bounds_size_of_no_vars in H4; eauto.
          invert H4.
          eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H15.
          eq_eval_Zlist. auto. }
        assert (eq_zexpr k (|eval_Zexpr_Z_total $0 k|)%z) as Heqk.
        eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
        assert (eq_zexpr m (|eval_Zexpr_Z_total $0 m|)%z) as Heqm.
        eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.

        invert Hpad; eq_size_of.
        { invert H5. repeat rewrite map_cons in *.
          rewrite H21 in *. invert Hsh. rewrite app_nil_l in *.
          rewrite <- gen_pad_cons in *.
          rewrite filter_negb_is_None_result_lookup_Z_option_gen_pad in *.
          unfold lookup_total. rewrite Heq.
          cases (reindexer
                   (shape_to_index
                      (result_shape_Z
                         (gen_pad
                            (Z.to_nat (eval_Zexpr_Z_total $0 k)
                                      :: map Z.to_nat
                                      (map (eval_Zexpr_Z_total $0) rest))))
                      (shape_to_vars
                         (result_shape_Z
                            (gen_pad
                               (Z.to_nat
                                  (eval_Zexpr_Z_total $0 k)
                                  :: map Z.to_nat
                                  (map (eval_Zexpr_Z_total $0) rest))))))).
          {  eapply reindexer_not_empty_vars_in_index in Heq0. propositional.
             apply Hrdx.
             erewrite result_has_shape_result_shape_Z
               by eapply result_has_shape_gen_pad.
             simpl.
             cases (Z.to_nat (eval_Zexpr_Z_total $0 k)).
             simpl. unfold not. intros.
             eapply cup_empty in H5. invs. eapply cup_empty in H8. invs.
             eapply constant_not_empty in H5. propositional. inversion 1.
             simpl. unfold not. intros.
             eapply cup_empty in H5. invs. eapply cup_empty in H8. invs.
             eapply constant_not_empty in H5. propositional. inversion 1. }
          unfold result_shape_Z in IHeval_expr.
          unfold shape_to_index, shape_to_vars in IHeval_expr. 
          simpl in IHeval_expr.
          rewrite tensor_to_array_delta_gen_pad in *.
          rewrite array_add_empty_r. rewrite add_id by auto.
          eapply IHeval_expr in Heval; clear IHeval_expr; eauto.
          2: { apply well_formed_allocation_result_V in Halloc.
               invert Halloc.
               decomp_well_formed_reindexer.
               propositional. simpl. unfold partial_injective. intros.
               invert H5.
               destruct l1; destruct l2; eauto.
               invert H5; simpl in *; try lia.
               invert H5; simpl in *; try lia.
               destruct p1. destruct p2. eapply HeqZlist.
               erewrite <- eq_Z_tuple_index_list_cons_tup.
               erewrite <- eq_Z_tuple_index_list_cons_tup in H5.
               propositional.
               eapply eq_zexpr_add; eauto.
               destruct l0. simpl. rewrite Hmap. eauto. eauto.
               destruct p1. simpl. rewrite Hmap.
               simpl. unfold subst_var_in_Z_tup at 1. simpl.
               rewrite subst_var_in_Zexpr_id with (lo:=k). eauto.
               invert Heqk. rewrite H15. sets. auto.
               destruct l0. rewrite Hvarsarg. sets. destruct p1.
               rewrite Hvarsarg. simpl.
               invert Heqk. rewrite H14. simpl.
               rewrite app_no_dups_empty_r. sets. 
               unfold nondestructivity.
               unfold tensor_to_array_delta. simpl.
               unfold tensor_to_array_delta_by_indices. simpl.
               rewrite dom_empty. split; intros. sets.
               eapply lookup_Some_dom in Heq. sets. apply Hrdx. }
          cases (reindexer [((! "?" !)%z, (| 0 | + k)%z)]).
          eapply reindexer_not_empty_vars_in_index in Heq1. propositional.
          apply Hrdx. simpl.
          unfold not. intros.
          eapply cup_empty in H5. invs.
          eapply cup_empty in H8. invs.
          apply constant_not_empty in H5. propositional. inversion 1.
          invs. subst. unfold lookup_total. rewrite Heq.
          rewrite tensor_to_array_delta_empty_tensor.
          rewrite array_add_empty_r. rewrite add_id. propositional. auto.

          eapply well_formed_allocation_padr with (m:=dim) (l0:=rest).
          simpl. rewrite H21. econstructor. eauto. eauto.
          simpl. eauto. apply Hrdx. apply Henv. apply Hrdx. apply Hrdx.
          apply Hrdx.
        }
          
        eapply IHeval_expr in Heval; eauto.
        subst.
        erewrite result_has_shape_result_shape_Z.
        2: { eapply result_has_shape_concat.
             simpl in Hsh.
             apply Hsh.
             eapply result_has_shape_repeat_gen_pad. }
        cases (reindexer
      (shape_to_index
         (map Z.of_nat
            (filter_until
               (Z.to_nat (eval_Zexpr_Z_total $0 m) +
                  Z.to_nat (eval_Zexpr_Z_total $0 k)
                           :: map Z.to_nat
                           (map (eval_Zexpr_Z_total $0) l0)) 0))
         (shape_to_vars
            (map Z.of_nat
                 (filter_until
                    (Z.to_nat (eval_Zexpr_Z_total $0 m) +
                       Z.to_nat (eval_Zexpr_Z_total $0 k)
                                :: map Z.to_nat
                                (map (eval_Zexpr_Z_total $0) l0)) 0))))).
     { eapply reindexer_not_empty in Heq0. propositional. apply Hrdx.
       simpl.
       cases (Z.to_nat (eval_Zexpr_Z_total $0 m)
              + Z.to_nat (eval_Zexpr_Z_total $0 k))%nat;
         inversion 1. }
     cases (shape_to_index (result_shape_Z (V l))
                  (shape_to_vars (result_shape_Z (V l)))).
     { eapply shape_to_index_not_empty_Z in Heq1. propositional. }
     unfold lookup_total. rewrite Heq.
     
     cases (reindexer (let (v, d) := p1 in (v, (d + k)%z) :: l3)).
     { erewrite result_has_shape_result_shape_Z in Heq1; eauto.      
       unfold result_shape_Z, shape_to_index, shape_to_vars in Heq1.
       simpl in *.
       cases (Z.to_nat (eval_Zexpr_Z_total $0 m)); invert Heq1.
       - eapply reindexer_not_empty_vars_in_index in Heq2. propositional.
         apply Hrdx. simpl. unfold app_no_dups.
         rewrite <- union_constant.
         unfold not. intros.
         eapply cup_empty in H8. invs.
         eapply cup_empty in H13. invs.
         eapply constant_not_empty in H8. propositional. inversion 1. 
       - eapply reindexer_not_empty_vars_in_index in Heq2. propositional.
         apply Hrdx. simpl. unfold app_no_dups.
         rewrite <- union_constant.
         unfold not. intros.
         eapply cup_empty in H8. invs.
         eapply cup_empty in H13. invs.
         eapply constant_not_empty in H8. propositional. inversion 1. }
     invs.
     split; auto. f_equal.
     unfold lookup_total. rewrite Heq.
     f_equal.

     unfold tensor_to_array_delta.
     symmetry.
     erewrite result_has_shape_result_shape_Z.
     2: { eapply result_has_shape_concat.
          simpl in Hsh. eauto.
          eapply result_has_shape_repeat_gen_pad. }
     
     pose proof filter_pad_r_mesh_grid. simpl gen_pad_list in H8.
     rewrite <- Z2Nat.inj_add.
     rewrite <- map_cons.
     rewrite <- eval_Zexpr_Z_total_add_distr;
       try eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
     rewrite <- map_cons.
     rewrite H8.
     rewrite map_cons.
     rewrite eval_Zexpr_Z_total_add_distr;
       try eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.

     erewrite result_has_shape_result_shape_Z by eauto.
     rewrite Z2Nat.inj_add by lia.
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
          repeat rewrite map_cons.
          erewrite eq_partial_interpret_reindexer_concat_l;
            try apply Hrdx; try apply Henv.
          rewrite Z2Nat.inj_add by lia. reflexivity.
          2: eauto.
          2: { eapply result_has_shape_repeat_gen_pad. }
          erewrite result_has_shape_result_shape_Z by eauto.
          eapply filter_In. propositional.
          repeat decomp_goal_index.
          propositional.
          rewrite Z2Nat.id by lia.
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto.
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

          repeat rewrite map_cons.
          eapply partial_injective_concat_l; auto; try apply Henv.
          erewrite result_has_shape_result_shape_Z.
          2: { eapply result_has_shape_concat. simpl in Hsh. eassumption.
               eapply result_has_shape_repeat_gen_pad
                 with (k:=Z.to_nat (eval_Zexpr_Z_total $0 k)). }
          rewrite filter_fun_pad_r in *.
          auto.
          eapply result_has_shape_repeat_gen_pad.
          rewrite Z2Nat.id by lia. auto.
        + decomp_well_formed_reindexer.
          erewrite result_has_shape_result_shape_Z in Hinj.
          2: { eapply result_has_shape_concat.
               simpl in Hsh. eauto.
               eapply result_has_shape_repeat_gen_pad. }          
          rewrite filter_fun_pad_r in *.
          simpl filter_until at 2.
          simpl filter_until at 2 in Hinj.
          cases (Z.to_nat (eval_Zexpr_Z_total $0 m)).
          { simpl in *.
            unfold partial_injective. simpl in *. propositional. }
          simpl map at 4. posnats.
          simpl map at 4 in Hinj. posnats.
          rewrite <- add_succ_l in Hinj.
          rewrite <- Heq3 in *.
          clear Heq3. clear n.
          rewrite Nat2Z.inj_add in Hinj.
          rewrite mesh_grid_app in Hinj by lia.
          rewrite filter_app in Hinj.
          eapply partial_injective_app_l in Hinj.
          rewrite map_cons.
          rewrite Z2Nat.inj_add by lia.
          eassumption.
        + unfold injective. propositional.
        + eapply no_dup_filter.
          eapply no_dup_mesh_grid.
        + eapply no_dup_filter.
          eapply no_dup_mesh_grid.
        + simpl. rewrite eval_Zexpr_Z_total_add_distr by eauto.
          rewrite Z2Nat.inj_add by lia.
          rewrite Nat.add_comm.
          eapply result_has_shape_concat.
          eapply result_has_shape_repeat_gen_pad.
          eauto.
        + lia.
        + lia.
        + lia.
        + subst.
          eapply well_formed_reindexer_padr; try apply Henv; eauto.
          invert H5. lia.
        + subst.
          eapply well_formed_allocation_padr;
            try apply Hrdx; try apply Henv; eauto.
        + apply Hrdx.
   - (* PADL *) simpl in *. invert Hconst. invert Hsize. eq_size_of.
        invert H6.
        assert (result_has_shape (V l)
                                 (map Z.to_nat
                                      (map (eval_Zexpr_Z_total $0) (m::l0))))
          as Hsh.
        { eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
          eassumption. eassumption. eauto. }
        pose proof H4.
        eapply constant_nonneg_bounds_sizeof_nonneg in H6.
        2: { erewrite size_of_sizeof by eassumption.
             eapply forall_no_vars_eval_Zexpr_Z_total with (v:=$0).
             eapply constant_nonneg_bounds_sizeof_no_vars in H6.
             erewrite size_of_sizeof in * by eassumption.
             eauto. }
        invert H6.
        pose proof H4.
        eapply constant_nonneg_bounds_sizeof_no_vars in H6.
        erewrite size_of_sizeof in * by eassumption.
        invert H6. invs.
        pose proof Halloc as Halloc1.
        eapply well_formed_allocation_result_V in Halloc1.
        inversion Halloc1 as [a Htmp]. clear Halloc1.
        inversion Htmp as [Heq Hsub]. clear Htmp.

        assert (eval_Zexpr_Z_total $0 k = kz)%Z.
        { pose proof H6.
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
            with (v:=$0) in H6.
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
            with (v:=v) in H5.
          invert H6. invert H5. simpl in *.
          pose proof H.
          eapply eval_Zexpr_Z_eval_Zexpr in H,H5.
          eapply H8 in H. invert H.
          eapply H6 in H5. invert H5. auto. }

        assert ((map (eval_Zexpr_Z_total $0) l0) = sz).
        { eapply constant_nonneg_bounds_size_of_no_vars in H4; eauto.
          invert H4.
          eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H15.
          eq_eval_Zlist. auto. }
        invert Hpad; eq_size_of.
        { invert H5. repeat rewrite map_cons in *. rewrite H21 in *.
          invert Hsh. rewrite app_nil_r in *.
          rewrite <- gen_pad_cons in *.
          rewrite filter_negb_is_None_result_lookup_Z_option_gen_pad in *.
          unfold lookup_total. rewrite Heq.
          cases (reindexer
                   (shape_to_index
                      (result_shape_Z
                         (gen_pad
                            (Z.to_nat (eval_Zexpr_Z_total $0 k)
                                      :: map Z.to_nat
                                      (map (eval_Zexpr_Z_total $0) rest))))
                      (shape_to_vars
                         (result_shape_Z
                            (gen_pad
                               (Z.to_nat
                                  (eval_Zexpr_Z_total $0 k)
                                  :: map Z.to_nat
                                  (map (eval_Zexpr_Z_total $0) rest))))))).
          {  eapply reindexer_not_empty_vars_in_index in Heq0. propositional.
             apply Hrdx.
             erewrite result_has_shape_result_shape_Z
               by eapply result_has_shape_gen_pad.
             simpl.
             cases (Z.to_nat (eval_Zexpr_Z_total $0 k)).
             simpl. unfold not. intros.
             eapply cup_empty in H5. invs. eapply cup_empty in H8. invs.
             eapply constant_not_empty in H5. propositional. inversion 1.
             simpl. unfold not. intros.
             eapply cup_empty in H5. invs. eapply cup_empty in H8. invs.
             eapply constant_not_empty in H5. propositional. inversion 1. }
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
               invert H14; simpl in *; lia.
               invert H14; simpl in *; lia.
               destruct p1. destruct p2. eapply HeqZlist.
               erewrite <- eq_Z_tuple_index_list_cons_tup.
               erewrite <- eq_Z_tuple_index_list_cons_tup in H14.
               propositional. eapply eq_zexpr_add; eauto.
               eapply eq_zexpr_add; eauto.
               destruct l0. rewrite Hmap. eauto. eauto.
               destruct p1. simpl. rewrite Hmap. simpl.
               unfold subst_var_in_Z_tup at 1. simpl.
               rewrite subst_var_in_Zexpr_id with (lo:=k). eauto.
               rewrite H6. sets. eauto.
               destruct l0. rewrite Hvarsarg. sets.
               destruct p1. rewrite Hvarsarg. simpl.
               rewrite H6. repeat rewrite app_no_dups_empty_r. sets.
               unfold nondestructivity.
               unfold tensor_to_array_delta, tensor_to_array_delta_by_indices.
               simpl. rewrite dom_empty. split; intros. sets.
               eapply lookup_Some_dom in Heq. sets.
               apply Hrdx.
          }
          2: { eapply well_formed_allocation_padl.
               rewrite app_nil_r. eauto.
               simpl. rewrite H21. econstructor.
               apply Hrdx. lia. lia. apply Hrdx.
               eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto. 
               eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto. 
               apply Henv. apply Hrdx. apply Hrdx. }
          invs.

          cases (reindexer [((! "?" ! + k)%z, (| 0 | + k)%z)]).
          eapply reindexer_not_empty_vars_in_index in Heq1. propositional.
          apply Hrdx. simpl.
          unfold not. intros.
          eapply cup_empty in H5. invs.
          eapply cup_empty in H8. invs.
          apply constant_not_empty in H5. propositional. inversion 1.
          invs. subst. unfold lookup_total. rewrite Heq.
          rewrite tensor_to_array_delta_empty_tensor.
          rewrite array_add_empty_r. rewrite add_id. propositional. auto.
        }
          
        eapply IHeval_expr in Heval.
        subst.
        erewrite result_has_shape_result_shape_Z.
        2: { eapply result_has_shape_concat.
             eapply result_has_shape_repeat_gen_pad.
             simpl in *. eassumption. }
        cases (reindexer
      (shape_to_index
         (map Z.of_nat
            (filter_until
               (Z.to_nat (eval_Zexpr_Z_total $0 k) +
                  Z.to_nat (eval_Zexpr_Z_total $0 m)
                           :: map Z.to_nat
                           (map (eval_Zexpr_Z_total $0) l0)) 0))
         (shape_to_vars
            (map Z.of_nat
                 (filter_until
                    (Z.to_nat (eval_Zexpr_Z_total $0 k) +
                       Z.to_nat (eval_Zexpr_Z_total $0 m)
                                :: map Z.to_nat
                                (map (eval_Zexpr_Z_total $0) l0)) 0))))).
     { eapply reindexer_not_empty in Heq0. propositional. apply Hrdx.
       simpl.
       cases (Z.to_nat (eval_Zexpr_Z_total $0 k)
              + Z.to_nat (eval_Zexpr_Z_total $0 m))%nat;
         inversion 1. }
     cases (shape_to_index (result_shape_Z (V l))
                  (shape_to_vars (result_shape_Z (V l)))).
     { eapply shape_to_index_not_empty_Z in Heq1. propositional. }
     unfold lookup_total. rewrite Heq.
     
     cases (reindexer (let (v, d) := p1 in ((v + k)%z, (d + k)%z) :: l3)).
     { erewrite result_has_shape_result_shape_Z in Heq1; eauto.      
       unfold result_shape_Z, shape_to_index, shape_to_vars in Heq1.
       simpl in *.
       cases (Z.to_nat (eval_Zexpr_Z_total $0 m)); invert Heq1.
       - eapply reindexer_not_empty_vars_in_index in Heq2. propositional.
         apply Hrdx. simpl. unfold app_no_dups.
         rewrite <- union_constant.
         unfold not. intros.
         eapply cup_empty in H8. invs.
         eapply cup_empty in H13. invs.
         eapply cup_empty in H8. invs.
         eapply constant_not_empty in H13. propositional. inversion 1. 
       - eapply reindexer_not_empty_vars_in_index in Heq2. propositional.
         apply Hrdx. simpl. unfold app_no_dups.
         rewrite <- union_constant.
         unfold not. intros.
         eapply cup_empty in H8. invs.
         eapply cup_empty in H13. invs.
         eapply cup_empty in H8. invs.
         eapply constant_not_empty in H13. propositional. inversion 1. }
     invs.
     split; auto. f_equal.
     unfold lookup_total. rewrite Heq.
     f_equal.

     unfold tensor_to_array_delta.
     symmetry.
     erewrite result_has_shape_result_shape_Z.
     2: { eapply result_has_shape_concat.
          eapply result_has_shape_repeat_gen_pad.
          eauto. simpl in *. eauto. }
     pose proof filter_pad_l_mesh_grid. simpl gen_pad_list in H8.
     rewrite <- Z2Nat.inj_add.
     rewrite <- map_cons.
     rewrite <- eval_Zexpr_Z_total_add_distr;
       try eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
     rewrite <- map_cons.
     rewrite H8.
     rewrite map_cons.
     rewrite eval_Zexpr_Z_total_add_distr;
       try eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.

     erewrite result_has_shape_result_shape_Z by eauto.
     eapply eq_tensor_to_array_delta_by_indices_shuffle
       with (shuffle:=fun l1 : list Z =>
                        match l1 with
                        | [] => l1
                        | x1 :: xs => (x1 + eval_Zexpr_Z_total $0 k)%Z :: xs
                        end).
        + intros.
          repeat decomp_index.
          pose proof result_lookup_Z_option_concat_l.
          simpl gen_pad_list in H14. rewrite H14. reflexivity. lia. lia.
        + intros.
          repeat decomp_index.
          repeat rewrite map_cons.
          erewrite eq_partial_interpret_reindexer_padl; eauto.
          rewrite Z2Nat.inj_add by lia. auto.          
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto.
          apply Henv. apply Hrdx. apply Hrdx. apply Hrdx. apply Hrdx.
          lia.
        + intros.
          repeat decomp_index.
          eapply in_map_iff. eexists (z::x0).
          propositional.
          eapply filter_In. propositional.
          repeat decomp_goal_index.
          propositional. lia.
        + intros.
          eapply in_map_iff in H13. invs.
          repeat decomp_index.          
          eexists (z::x1).
          propositional.
          eapply filter_In. propositional.
          repeat decomp_goal_index. propositional. lia.
        + repeat rewrite map_cons.
          assert (eval_Zexpr_Z_total $0 m = 0 \/
                    eval_Zexpr_Z_total $0 m <> 0)%Z by lia. invert H13.
          { rewrite H14. simpl.
            unfold partial_injective. propositional. invert H16. }
          decomp_well_formed_reindexer.
          eapply partial_injective_padl; eauto.
          apply Henv.
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto.
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto.
          lia.
        + decomp_well_formed_reindexer.
          erewrite result_has_shape_result_shape_Z in Hinj.
          2: { eapply result_has_shape_concat.
               eapply result_has_shape_repeat_gen_pad.
               simpl in Hsh. eauto. }
          rewrite <- Z2Nat.inj_add in Hinj by lia.
          rewrite <- map_cons in Hinj.
          rewrite <- eval_Zexpr_Z_total_add_distr in Hinj;
            try eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
          rewrite <- map_cons in Hinj.
          pose proof filter_pad_l_mesh_grid.
          simpl gen_pad_list in H8.
          rewrite H8 in Hinj.
          clear H8.
          rewrite map_cons in Hinj.
          rewrite eval_Zexpr_Z_total_add_distr in Hinj;
            try eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.

          repeat rewrite map_cons.
          rewrite eval_Zexpr_Z_total_add_distr;
            try eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
          rewrite Z2Nat.inj_add by lia.
          eapply result_has_shape_concat.
          eapply result_has_shape_repeat_gen_pad. eauto.
          lia.
        + unfold injective. propositional.
          repeat decomp_index. invert H19. f_equal. lia.
        + eapply no_dup_filter.
          eapply no_dup_mesh_grid.
        + eapply no_dup_injective_map.
          unfold injective. propositional.
          repeat decomp_index. invert H19. f_equal. lia.
          eapply no_dup_filter.
          eapply no_dup_mesh_grid.
        + simpl.
          rewrite eval_Zexpr_Z_total_add_distr;
            try eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
          rewrite Z2Nat.inj_add by lia.
          simpl. eapply result_has_shape_concat.
          eapply result_has_shape_repeat_gen_pad. auto.
        + lia.
        + lia.
        + lia.
        + eauto.
        + eauto.
        + eauto.
        + decomp_well_formed_reindexer. subst.
          eapply well_formed_allocation_result_V in Halloc. invert Halloc.
          eapply well_formed_reindexer_padl; auto. eauto.
          simpl in Hsh. eauto. apply Henv.
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto.
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto.
          invert H5. lia.
          eapply H8.
          eauto. 
          apply H8.
          eauto.
        + decomp_well_formed_reindexer. subst.
          eapply well_formed_allocation_padl; auto.
          eauto. eauto. lia. 
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto.
          eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto.
          apply Henv.
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
       invs.
       eapply forall_no_vars_eval_Zexpr_Z_total with (v:=$0) in H0,H1.
       rewrite map_fst_map_partially_eval_Z_tup in *.
       rewrite map_snd_map_partially_eval_Z_tup in *.
       rewrite map_eval_Zexpr_Z_total_map_partially_eval_Zexpr_join in *.
       
       propositional.
       f_equal.
       eapply eval_Zexpr_Z_eval_Zexpr in H11.
       rewrite partially_eval_Zexpr_empty_valuation in H11.
       rewrite partially_eval_Zexpr_flatten_shape_index in H11.
       erewrite eval_Zexpr_Z_flatten_index_flatten in H11.
       2: { eauto. }
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
               (map (eval_Zexpr_Z_total v) (map snd (reindexer [])))
               (map (eval_Zexpr_Z_total v) (map fst (reindexer []))))
         in H10; eauto.
       2: { eapply lookup_Some_dom in H10.
            unfold well_formed_environment in *. sets. }
       2: { clear H2. unfold result_shape_Z. simpl.
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
       invs.
       eapply forall_no_vars_eval_Zexpr_Z_total with (v:=$0) in H0,H1.
       rewrite map_fst_map_partially_eval_Z_tup in *.
       rewrite map_snd_map_partially_eval_Z_tup in *.
       rewrite map_eval_Zexpr_Z_total_map_partially_eval_Zexpr_join in *.
       
       propositional.
       f_equal.
       eapply eval_Zexpr_Z_eval_Zexpr in H11.
       rewrite partially_eval_Zexpr_empty_valuation in H11.
       rewrite partially_eval_Zexpr_flatten_shape_index in H11.
       erewrite eval_Zexpr_Z_flatten_index_flatten in H11.
       2: { eauto. }
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
    constant_nonneg_bounds e ->
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
    + simpl in *. invert H2.
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
      * invert H2.
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
      * invert H2.
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
      * simpl in *. invert H2.
        unfold nondestructivity. rewrite lookup_empty. rewrite dom_add.
        rewrite dom_empty. rewrite cup_empty_r. rewrite lookup_add_eq by auto.
        rewrite dom_empty.
        split; intros. discriminate. invert H2. eauto.
      * destruct (shape_to_index (result_shape_Z (V v))
                    (shape_to_vars (result_shape_Z (V v)))) eqn:ee.
        eapply shape_to_index_not_empty_Z in ee. propositional.
        invert H2.
        unfold nondestructivity. rewrite lookup_empty.
        unfold alloc_array_in_heap. rewrite dom_add.
        repeat rewrite dom_empty. rewrite cup_empty_r.
        rewrite lookup_add_eq by auto.
        split; intros. invert H2.
        2: { discriminate. }
        destruct v. simpl in *.
        unfold tensor_to_array_delta in H8. simpl in H8.
        unfold tensor_to_array_delta_by_indices in H8. simpl in H8.
        rewrite dom_empty in *. sets.
        pose proof (lookup_alloc_array
                      (fold_left mul (Datatypes.S (length v) ::
                                        result_shape_nat r) 1) x).
        invert H2; eauto.
        eapply lookup_None_dom in H6.
        rewrite dom_alloc_array in H6.
        unfold tensor_to_array_delta in H8.
        unfold tensor_to_array_delta_by_indices in H8.
        erewrite partial_dom_fold_left_array_add in H8.
        rewrite dom_empty in H8. rewrite cup_empty_r in H8.
        2: { eapply partial_injective_id_reindexer; eauto.
             rewrite dom_empty. sets. }
        exfalso. apply H6.
        erewrite <- In_iff_in. eapply In_iff_in in H8.
        eapply in_extract_Some in H8. eapply in_map_iff in H8. invs.
        rewrite filter_idempotent in H9.
        erewrite partial_interpret_reindexer_id_flatten in H8.
        2: { decomp_index. eauto. }
        2: { rewrite dom_empty. sets. }
        invert H8.
        unfold result_shape_Z. simpl result_shape_nat.
        erewrite Z_of_nat_fold_left_mul.
        eapply in_mesh_grid_flatten_in_range.
        2: { unfold result_shape_Z in *. simpl result_shape_nat in *.
             decomp_index. eauto. }
        eapply Forall_map. eapply Forall_forall. intros. lia.
  - unfold result_shape_Z, shape_to_index, shape_to_vars in *.
    cases r.
    + simpl in *. invert H2. unfold well_formed_allocation.
      simpl. rewrite lookup_add_eq by auto. eauto.
    + cases v.
      * simpl in *. invert H2. unfold well_formed_allocation.
        simpl. unfold alloc_array_in_heap in *. simpl.
        rewrite lookup_add_eq by auto.
        eexists. split. eauto. sets.
      * invert H2.
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

