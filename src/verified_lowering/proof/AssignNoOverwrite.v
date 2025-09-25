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

Definition assign_no_overwrite (st : stack) h p reindexer r v asn :=
  (forall arr,
      h $? p = Some arr ->
      asn = Assign ->
      ~ p \in dom st ->
   forall x,
     x \in dom (partial_result_to_array_delta
                  (partial_interpret_reindexer reindexer (result_shape_Z r)
                  v) r) ->
           arr $? x = Some 0%R) /\
    (forall a,
        st $? p = Some a ->
      asn = Assign ->
        ~ p \in dom h ->
                a = 0%R).

Lemma assign_no_overwrite_split :
  forall st h p reindexer n k l v asm e ec sh l0 x,
    well_formed_environment st h p sh v (vars_of e) ec ->
    partial_well_formed_reindexer
      reindexer v
      (V (split_result (Z.to_nat (eval_Zexpr_Z_total $0 k)) l)) ->
    partial_well_formed_allocation
      reindexer
      (V (split_result (Z.to_nat (eval_Zexpr_Z_total $0 k)) l)) st h p v ->
    assign_no_overwrite
      st h p reindexer
      (V (split_result (Z.to_nat (eval_Zexpr_Z_total $0 k)) l)) v asm ->
    vars_of_Zexpr k = [] ->
    (0 < eval_Zexpr_Z_total $0 k)%Z ->
    constant_nonneg_bounds e ->
    result_has_shape (V l)
                     (Z.to_nat (eval_Zexpr_Z_total $0 n)
                               :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)) ->
    h $? p = Some x ->
    size_of e (n::l0) ->
  assign_no_overwrite st h p
    (fun l2 : list (Zexpr * Zexpr) =>
     reindexer
       match l2 with
       | [] => l2
       | (v0, d) :: xs => ((v0 / k)%z, (d // k)%z) :: ((ZMod v0 k)%z, k) :: xs
       end) (V l) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? Henv Hrdx Halloc Hassign Hk Hkpos Hconst
         Hsh Hheap Hsize.
  unfold assign_no_overwrite. split; intros.
  2: { eapply lookup_Some_dom in Hheap. sets. }
  assert (Some x = Some arr). rewrite <- H,<-Hheap. auto. invert H3.
  eapply Hassign; try apply Hrdx; eauto.
  unfold partial_result_to_array_delta in *.
  pose proof Hsh as Hshsplit.
  eapply result_has_shape_split_result
    with (k:= Z.to_nat (eval_Zexpr_Z_total $0 k)) in Hshsplit.
  erewrite partial_eq_result_to_array_delta_by_indices_shuffle
    with (shuffle:=
            fun l =>
              match l with
              | x::xs => (x/eval_Zexpr_Z_total $0 k)%Z
                          ::(Zmod x (eval_Zexpr_Z_total $0 k))%Z::xs
              | _ => l
              end). eassumption.
  - intros. cases x. propositional.
    erewrite result_has_shape_result_shape_Z in H0 by eauto.
    repeat decomp_index.
    rewrite <- (Z2Nat.id (eval_Zexpr_Z_total $0 k)) at 1 by lia. 
    rewrite <- (Z2Nat.id (eval_Zexpr_Z_total $0 k)) at 2 by lia.
    erewrite result_lookup_Z_option_split. reflexivity.
    repeat decomp_index. eauto. lia. apply H0. lia.
    rewrite Nat2Z.id by lia. eauto.
  - intros. erewrite result_has_shape_result_shape_Z in * by eauto.
    erewrite result_has_shape_result_shape_Z in * by eauto.
    repeat decomp_index.
    rewrite <- Z2Nat_div_distr by lia.
    erewrite <- eq_partial_interpret_reindexer_split;
      try apply Henv; try apply Hrdx; try lia; eauto.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total;
      eauto.
  - erewrite result_has_shape_result_shape_Z in * by eauto.
    erewrite result_has_shape_result_shape_Z in * by eauto.
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
    rewrite <- H4.
    f_equal. f_equal.
    rewrite <- (Z2Nat.id (eval_Zexpr_Z_total $0 k)) at 1 by lia.
    rewrite <- (Z2Nat.id (eval_Zexpr_Z_total $0 k)) at 2 by lia.
    erewrite result_lookup_Z_option_split. reflexivity.
    eauto. lia. apply H0. lia. rewrite Z2Nat.id. eauto. lia.
  - erewrite result_has_shape_result_shape_Z in * by eauto.
    erewrite result_has_shape_result_shape_Z in * by eauto.
    intros. repeat decomp_index.
    eexists ((z*(eval_Zexpr_Z_total $0 k) + z0)%Z::x).
    rewrite Z.div_add_l by lia.
    rewrite Z.div_small by lia. rewrite Z.add_0_r.
    pose proof Z.add_mul_mod_distr_r.
    specialize H5 with (b:=1%Z) (c:= eval_Zexpr_Z_total $0 k).
    rewrite Z.mul_1_l in *.
    rewrite H5.
    rewrite Z.mod_1_r. split. auto.
    eapply filter_In. split.
    repeat decomp_goal_index. split.
    split. lia. rewrite Z2Nat.id.
    2: { eapply constant_nonneg_bounds_size_of_nonneg in Hconst; eauto.
         2: { eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v).
              eapply constant_nonneg_bounds_size_of_no_vars; eauto. }
         invert Hconst. lia. }
    eapply result_lookup_Z_option_split_true. eauto.
    rewrite <- Z2Nat_div_distr in *.
    2: { lia. }
    2: { eapply constant_nonneg_bounds_size_of_nonneg in Hconst; eauto.
         2: { eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v).
              eapply constant_nonneg_bounds_size_of_no_vars; eauto. }
         invert Hconst. lia. }
    rewrite Z2Nat.id in H0.
    2: { eapply ceil_div_nonneg.
         eapply constant_nonneg_bounds_size_of_nonneg in Hconst; eauto.
         2: { eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v).
              eapply constant_nonneg_bounds_size_of_no_vars; eauto. }
         invert Hconst. lia. lia. }
    lia. lia.
    eapply constant_nonneg_bounds_size_of_nonneg in Hconst; eauto.
    2: { eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v).
         eapply constant_nonneg_bounds_size_of_no_vars; eauto. }
    invert Hconst. lia. lia. 
    eapply constant_nonneg_bounds_size_of_nonneg in Hconst; eauto.
    2: { eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v).
         eapply constant_nonneg_bounds_size_of_no_vars; eauto. }
    invert Hconst. lia. eauto. eauto. eauto.
    rewrite <- H4.
    erewrite <- result_lookup_Z_option_split
            with (k:=Z.to_nat (eval_Zexpr_Z_total $0 k)); eauto.
    2: { lia. }
    3: lia.
    3: { lia. }
    all: try lia.
    2: { rewrite <- Z2Nat_div_distr in H0.
         2: { lia. }
         2: { eapply constant_nonneg_bounds_size_of_nonneg in Hconst; eauto.
              2: { eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v).
                   eapply constant_nonneg_bounds_size_of_no_vars; eauto. }
              invert Hconst. lia. }
         rewrite Z2Nat.id in * by lia.
         eapply result_lookup_Z_option_split_true. eauto.
         lia. lia.
         eapply constant_nonneg_bounds_size_of_nonneg in Hconst; eauto.
         2: { eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v).
              eapply constant_nonneg_bounds_size_of_no_vars; eauto. }
         invert Hconst. lia. eauto. eauto. }
    rewrite Z2Nat.id by lia.
    rewrite Z.div_add_l by lia. rewrite Z.div_small by lia.
    rewrite Z.add_0_r.
    pose proof Z.add_mul_mod_distr_r.
    specialize H7 with (b:=1%Z) (c:= eval_Zexpr_Z_total $0 k).
    rewrite Z.mul_1_l in *.
    rewrite H7.
    rewrite Z.mod_1_r. reflexivity. lia. lia. lia.
  - eapply partial_injective_split. apply Hrdx. eauto. apply Henv.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
    apply Hrdx. apply Hrdx. apply Hrdx. apply Hrdx.
    eapply constant_nonneg_bounds_size_of_nonneg in Hconst; eauto.
    2: { eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v).
         eapply constant_nonneg_bounds_size_of_no_vars; eauto. }
    invert Hconst. lia. lia.
  - apply Hrdx.
  - unfold injective.
    erewrite result_has_shape_result_shape_Z by eauto.
    propositional. repeat decomp_index.
    invert H5.
    rewrite (Z.div_mod z (eval_Zexpr_Z_total $0 k)).
    rewrite (Z.div_mod z0 (eval_Zexpr_Z_total $0 k)).
    rewrite H10. rewrite H11. reflexivity. lia. lia.
  - eapply no_dup_filter. eauto with reindexers.
  - eapply no_dup_filter. eauto with reindexers.
  - lia.
Qed.

Lemma assign_no_overwrite_array_add_shift_top_dim_reindexer :
  forall i lo hi body l st h sh v ec x p r reindexer l0 asm,
    constant_nonneg_bounds (Gen i lo hi body) ->
    (eval_Zexpr_Z_total $0 lo < eval_Zexpr_Z_total $0 hi)%Z ->
    ~ i \in dom v ->
    ~ contains_substring "?" i ->
    well_formed_environment st h p sh v (vars_of (Gen i lo hi body)) ec ->
    partial_well_formed_reindexer reindexer v (V (r :: l)) ->
    size_of body l0 ->
    eq_zexpr lo (| eval_Zexpr_Z_total $0 lo |)%z ->
    eq_zexpr hi (| eval_Zexpr_Z_total $0 hi |)%z ->
    result_has_shape (V (r :: l)) (result_shape_nat (V (r :: l))) ->
    partial_well_formed_allocation reindexer (V (r :: l)) st h p v ->
    length l =
      Z.to_nat (eval_Zexpr_Z_total $0 hi - (eval_Zexpr_Z_total $0 lo + 1)) ->
    assign_no_overwrite st h p reindexer (V (r :: l)) v asm ->
    h $? p = Some x ->
  assign_no_overwrite st
    (h $+ (p,
     array_add x
       (partial_result_to_array_delta
          (partial_interpret_reindexer
             (fun l5 : list (Zexpr * Zexpr) =>
              reindexer (((! i ! - lo)%z, (hi - lo)%z) :: l5)) 
             (result_shape_Z r) (v $+ (i, eval_Zexpr_Z_total $0 lo))) r))) p
    (shift_top_dim_reindexer reindexer) (V l) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hconst Hlohi Hidom Hsubstring Henv
         Hrdx Hsize Hlo Hhi Hsh Halloc Hlen Hassign Hlookup.
  unfold assign_no_overwrite. split; intros.
  2: { rewrite dom_add in H1. sets. }
  rewrite lookup_add_eq in H by auto. invert H.
  erewrite lookup_array_add_weak_l.
  2: { unfold not. intros. eapply dom_lookup_Some in H,H2. invs.
       unfold partial_result_to_array_delta in *.
       unfold partial_result_to_array_delta_by_indices in *.
       eapply lookup_Some_dom in H.
       rewrite partial_dom_fold_left_array_add in H.
       rewrite@ filter_idempotent in *.
       rewrite dom_empty in *. rewrite @cup_empty_r in *.
       eapply In_iff_in in H.
       eapply in_extract_Some in H.
       eapply in_map_iff in H. invs.
       eapply lookup_Some_dom in H0.
       rewrite partial_dom_fold_left_array_add in H0.
       rewrite@ filter_idempotent in *.
       rewrite dom_empty in *. rewrite @cup_empty_r in *.
       eapply In_iff_in in H0. eapply in_extract_Some in H0.
       eapply in_map_iff in H0. invs. rewrite <- H in H0.
       repeat decomp_index.
       erewrite result_has_shape_result_shape_Z in H4.
       2: { invert Hsh. eapply forall_result_has_shape; eauto. }
       2: { eapply partial_injective_cons_reindexer; eauto;
            try apply Hrdx. apply Henv. unfold not. intros.
            apply Hsubstring. eapply shape_to_vars_contains_substring.
            eauto. simpl. lia. }
       2: { eapply partial_injective_shift_top_dim_reindexer;
            try apply Hrdx; eauto. apply Henv. cases l.
            inversion 1. rewrite dom_empty in *. sets.
            inversion 1. }
       symmetry in H0.
       erewrite result_has_shape_result_shape_Z in H0,H.
       2: { invert Hsh. eapply forall_result_has_shape; eauto. }
       repeat decomp_index.
       erewrite
         eq_partial_interpret_reindexer_shift_top_dim_reindexer
                   in H0,H; try apply Hrdx; eauto. 2: apply Henv. 
       2: { cases l. inversion 1. simpl in *. lia. inversion 1. }
       2: apply Henv.
       2: { cases l. inversion 1. simpl in *. lia. inversion 1. }
       2: { eapply forall_result_has_shape; eauto. invert Hsh. eauto. }
       symmetry in H0.
       erewrite result_has_shape_result_shape_Z in H0.
       2: { invert Hsh. eauto. }
       erewrite eq_partial_interpret_reindexer_eval_0 in H0;
         try apply Hrdx; eauto. 2: apply Henv.
       2: { unfold not. intros. apply Hsubstring.
            eapply shape_to_vars_contains_substring. eauto. }
       2: { simpl. lia. }
       decomp_partial_well_formed_reindexer.
       replace (map Z.of_nat
                    (filter_until
                       (result_shape_nat (V (r :: l))) 0))
         with (result_shape_Z (V (r::l))) in *.
       2: { erewrite result_has_shape_result_shape_Z; eauto. }

       pose proof H0.
       eapply Hinj in H0.
       2: { erewrite result_has_shape_result_shape_Z by eauto.
            eapply filter_In. split. repeat decomp_goal_index.
            split. lia. eauto. rewrite <- H5. reflexivity. }
       2: { erewrite result_has_shape_result_shape_Z by eauto.
            eapply filter_In. split. repeat decomp_goal_index.
            split. lia. eauto. rewrite <- H6.
            simpl.
            cases (z+1)%Z; try lia. f_equal.
            replace (Z.to_nat (Z.pos p0))
              with (Datatypes.S (Z.to_nat z)) by lia.
            simpl. cases z; try lia. reflexivity. reflexivity. }
       invert H0. invert H8. lia.
       rewrite H4 in H8. rewrite H in H8. discriminate. }

  eapply Hassign; eauto.
  erewrite <- partial_result_to_array_delta_cons.
  2: { eapply Hlo. }
  2: { eapply Hhi. }
  all: eauto.
  2: { lia. }
  2: { apply Henv. }
  2: { unfold not. intros. apply Hsubstring.
       eapply shape_to_vars_contains_substring; eauto. }
  rewrite dom_array_add. sets.
Qed.

Lemma assign_no_overwrite_cons_0 :
  forall reindexer i lo hi body v st h p sh ec r l x l0 asm,
    constant_nonneg_bounds (Gen i lo hi body) ->
    (eval_Zexpr_Z_total $0 lo < eval_Zexpr_Z_total $0 hi)%Z ->
    ~ i \in dom v ->
    ~ contains_substring "?" i ->
    well_formed_environment st h p sh v (vars_of (Gen i lo hi body)) ec ->
    partial_well_formed_reindexer reindexer v (V (r :: l)) ->
    size_of body l0 ->
    eq_zexpr lo (| eval_Zexpr_Z_total $0 lo |)%z ->
    eq_zexpr hi (| eval_Zexpr_Z_total $0 hi |)%z ->
    result_has_shape (V (r :: l)) (result_shape_nat (V (r :: l))) ->
    partial_well_formed_allocation reindexer (V (r :: l)) st h p v ->
    h $? p = Some x ->
    length l =
      Z.to_nat (eval_Zexpr_Z_total $0 hi - (eval_Zexpr_Z_total $0 lo + 1)) ->
    assign_no_overwrite st h p reindexer (V (r :: l)) v asm ->
  assign_no_overwrite st h p
    (fun l3 : list (Zexpr * Zexpr) =>
     reindexer (((! i ! - lo)%z, (hi - lo)%z) :: l3)) r
    (v $+ (i, eval_Zexpr_Z_total $0 lo)) asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hconst Hlohi Hidom Hsubstring
         Henv Hrdx Hsize Hlo Hhi Hsh Halloc Hheap Hlen Hassign.
  unfold assign_no_overwrite. split; intros.
  2: { eapply lookup_Some_dom in Hheap. sets. }
  assert (Some arr = Some x). rewrite <-H,<-Hheap. auto. invert H3.
  eapply Hassign; eauto.
  erewrite <- partial_result_to_array_delta_cons.
  2: { eapply Hlo. }
  2: { eapply Hhi. }
  all: eauto.
  2: { lia. }
  2: { apply Henv. }
  2: { unfold not. intros. apply Hsubstring.
       eapply shape_to_vars_contains_substring; eauto. }
  rewrite dom_array_add. sets.
Qed.

Lemma assign_no_overwrite_reduce :
  forall st h p reindexer r v,
    assign_no_overwrite st h p reindexer r v Reduce.
Proof.
  intros. unfold assign_no_overwrite. split; intros; discriminate.
Qed.

Lemma assign_no_overwrite_add_stack :
  forall st h'0 p sh v x e1 e2 ec l2 asm reindexer r1,
    well_formed_environment st h'0 p sh v
                            ((constant [x] \cup vars_of e1) \cup vars_of e2) ec ->
    assign_no_overwrite st h'0 p reindexer l2 v asm ->
    assign_no_overwrite (st $+ (x, r1)) h'0 p reindexer l2 v asm.
Proof.
  intros. unfold assign_no_overwrite in *.
  invs. split; intros.
  * rewrite dom_add in *.
    eapply H1; eauto. sets.
  * rewrite lookup_add_ne in H0.
    2: { unfold well_formed_environment in *. sets. }
    eapply H2; eauto.
Qed.

Lemma assign_no_overwrite_alloc_stack :
  forall st h'0 p sh v x e1 e2 ec reindexer l2 asm r1,
    well_formed_environment st h'0 p sh v 
                            ((constant [x] \cup vars_of e1) \cup vars_of e2) ec ->
    assign_no_overwrite st h'0 p reindexer l2 v asm ->
    assign_no_overwrite (st $+ (x, 0%R)) h'0 x (fun l => l)
                        (S r1) v Assign.
Proof.
  intros.
  unfold assign_no_overwrite in *. split; intros.
  * rewrite dom_add in *. sets.
  * rewrite lookup_add_eq in * by eauto. invert H1. eauto.
Qed.

Lemma assign_no_overwrite_add_heap :
  forall st'0 h p sh v x e1 e2 ec asm reindexer l2 arr,
    well_formed_environment st'0 h p sh v
                            ((constant [x] \cup vars_of e1) \cup vars_of e2) ec ->
    assign_no_overwrite st'0 h p reindexer l2 v asm ->
    assign_no_overwrite st'0
                        (h $+ (x,arr)) p reindexer l2 v asm.
Proof.
  intros. unfold assign_no_overwrite in *. invs.
  split; intros.
  - rewrite lookup_add_ne in H0.
    2: { unfold well_formed_environment in *. sets. }
    eapply H1; eauto.
  - rewrite dom_add in *. eapply H2; eauto. sets.
Qed.

Lemma assign_no_overwrite_alloc_heap :
  forall e1 esh1 st'0 h p sh v x e2 ec l2 asm z0 zs nz z reindexer l1,
  constant_nonneg_bounds e1 ->
  size_of e1 (z::esh1) ->
  well_formed_environment st'0 h p sh v
                          ((constant [x] \cup vars_of e1) \cup vars_of e2) ec ->
  assign_no_overwrite st'0 h p reindexer l2 v asm ->
  eval_Zexpr v z z0 ->
  eval_Zexprlist v esh1 zs ->
  eval_Zexpr v (flat_sizeof e1) nz ->
  result_has_shape (V l1)
                   (map Z.to_nat (map (eval_Zexpr_Z_total $0) (z :: esh1))) ->
  assign_no_overwrite st'0 (alloc_array_in_heap [Z.to_nat nz] h x) x
                      (fun l : list (Zexpr * Zexpr) => l) (V l1) v Assign.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hconst Hsize Henv Hassign Hz Hzs
         Hflat Hsh.
  unfold assign_no_overwrite in *. invs.
  split; intros.
  - unfold alloc_array_in_heap in *. rewrite lookup_add_eq in * by auto.
    invert H1.
    unfold partial_result_to_array_delta in H4.
    unfold partial_result_to_array_delta_by_indices in H4.
    rewrite partial_dom_fold_left_array_add in H4.
    2: { eapply partial_injective_id_reindexer. apply Henv. }
    rewrite dom_empty in H4. rewrite cup_empty_r in H4.
    eapply In_iff_in in H4. eapply in_extract_Some in H4.
    eapply in_map_iff in H4. invs. rewrite @filter_idempotent in *.
    rewrite partial_interpret_reindexer_id_flatten in H4.
    invert H4. rewrite add_0_r.
    2: { decomp_index. eauto. }
    2: { apply Henv. }
    pose proof (lookup_alloc_array (Z.to_nat nz)
                                        (flatten (result_shape_Z (V l1)) x1)).
    invert H1. 2: auto.
    eapply lookup_None_dom in H4. exfalso. apply H4.
    rewrite dom_alloc_array. erewrite <- In_iff_in.
    unfold flat_sizeof in *. erewrite size_of_sizeof in * by eauto.
    simpl in Hflat. eapply eval_Zexpr_Z_eval_Zexpr in Hflat.
    erewrite eval_Zexpr_Z_fold_left_ZTimes in Hflat; eauto. invert Hflat.
    replace (fold_left Z.mul zs z0) with (fold_left Z.mul (z0::zs) 1%Z).
    2: { simpl. f_equal. lia. }
    rewrite Z2Nat.id. erewrite result_has_shape_result_shape_Z by eauto.
    pose proof Hconst.
    eapply constant_nonneg_bounds_size_of_no_vars in H1.
    2: { eauto. }
    2: { eapply fold_left_mul_nonneg. 2: lia.
         eapply constant_nonneg_bounds_size_of_nonneg. eauto.
         eauto. econstructor; eauto. }
    eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H1.
    invert H1. eq_eval_Z. eq_eval_Zlist. repeat decomp_index.
    erewrite filter_until_0_id.
    2: { erewrite result_has_shape_result_shape_Z in H1 by eauto.
         decomp_index.
         pose proof Hconst.
         eapply constant_nonneg_bounds_size_of_nonneg in H5; eauto.
         invert H5.
         rewrite Z2Nat.id in * by lia.
         rewrite Z2Natid_list in H1; eauto.
         eapply mesh_grid_shape_pos in H1. rewrite map_cons.
         eapply Forall_map. eapply Forall_impl.
         2: apply H1. simpl. lia. }
    rewrite <- map_cons.
    rewrite Z2Natid_list.
    2: { pose proof Hconst.
         eapply constant_nonneg_bounds_size_of_nonneg in H5; eauto.
         eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v).
         eapply constant_nonneg_bounds_size_of_no_vars. eauto. eauto. }
    eapply in_mesh_grid_flatten_in_range.
    eapply constant_nonneg_bounds_size_of_nonneg. eauto. eauto.
    eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v).
    eapply constant_nonneg_bounds_size_of_no_vars. eapply Hconst. eauto.
    erewrite result_has_shape_result_shape_Z in H1 by eauto.
    repeat decomp_index. rewrite mesh_grid_map_Nat2Z_id in *.
    simpl map. decomp_goal_index. propositional. lia.
  - rewrite dom_alloc_array_in_heap in *. sets. inversion 1.
Qed.

Lemma assign_no_overwrite_concat_r :
  forall st h p sh v e1 e2 ec l1 l2 reindexer asm x rest1 rest2 dim1 dim2,
well_formed_environment st h p sh v (vars_of e1 \cup vars_of e2) ec ->
partial_well_formed_reindexer reindexer v (V (l1 ++ l2)) ->
assign_no_overwrite st h p reindexer (V (l1 ++ l2)) v asm ->
h $? p = Some x ->
size_of e1 (dim1 :: rest1) ->
size_of e2 (dim2 :: rest2) ->
result_has_shape (V l2)
           (Z.to_nat (eval_Zexpr_Z_total $0 dim2)
            :: map Z.to_nat
                 (map
                    (eval_Zexpr_Z_total $0) rest1)) ->
result_has_shape (V l1)
           (Z.to_nat (eval_Zexpr_Z_total $0 dim1)
            :: map Z.to_nat
                 (map
                    (eval_Zexpr_Z_total $0) rest1)) ->
result_has_shape (V (l1 ++ l2))
         (Z.to_nat (eval_Zexpr_Z_total $0 dim1) +
          Z.to_nat (eval_Zexpr_Z_total $0 dim2)
          :: map Z.to_nat
               (map
                  (eval_Zexpr_Z_total $0) rest1)) ->
(0 <= eval_Zexpr_Z_total $0 dim1)%Z ->
(0 <= eval_Zexpr_Z_total $0 dim2)%Z ->
eq_zexpr dim1 (| eval_Zexpr_Z_total $0 dim1 |)%z ->
eq_zexpr dim2 (| eval_Zexpr_Z_total $0 dim2 |)%z ->
  assign_no_overwrite st
    (h $+ (p,
     array_add x
       (partial_result_to_array_delta
          (partial_interpret_reindexer
             (fun l6 : list (Zexpr * Zexpr) =>
              reindexer
                match l6 with
                | [] => l6
                | (v0, d) :: xs => (v0, (d + dim2)%z) :: xs
                end) (result_shape_Z (V l1)) v) (V l1)))) p
    (fun l6 : list (Zexpr * Zexpr) =>
     reindexer
       match l6 with
       | [] => l6
       | (v0, d) :: xs =>
           ((v0 + match sizeof e1 with
                  | [] => | 0 |
                  | n :: _ => n
                  end)%z,
           (d + match sizeof e1 with
                | [] => | 0 |
                | n :: _ => n
                end)%z) :: xs
       end) (V l2) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Henv Hrdx Hassign Hheap
         Hsize1 Hsize2 Hsh2 Hsh1 Hsh Hdim1nonneg Hdim2nonneg Heqdim1 Heqdim2.
  unfold assign_no_overwrite in *. invs.
  split; intros.
  - rewrite lookup_add_eq in * by auto. invert H1.
    erewrite lookup_array_add_weak_l.
    2: { erewrite result_has_shape_result_shape_Z by eauto.
         erewrite size_of_sizeof in * by eauto. simpl in H4. 
         erewrite result_has_shape_result_shape_Z in H4 by eauto.
         unfold partial_result_to_array_delta,
           partial_result_to_array_delta_by_indices in *.
         rewrite partial_dom_fold_left_array_add in *.
         2: { apply Hrdx. }
         2: { erewrite result_has_shape_result_shape_Z by eauto.
              eapply partial_injective_concat_r.
              eapply Hrdx. eauto. eauto. apply Henv.
              all: try apply Hrdx.
              eauto. eauto. }
         2: { erewrite result_has_shape_result_shape_Z by eauto.
              eapply partial_injective_concat_l.
              eapply Hrdx. eauto. eauto. apply Henv.
              all: try apply Hrdx.
              rewrite Z2Nat.id by lia.
              eauto. }
         rewrite filter_idempotent in *.
         rewrite dom_empty in *. rewrite cup_empty_r in *.
         erewrite result_has_shape_result_shape_Z in * by eauto.
         unfold not. intros.
         eapply In_iff_in in H1,H4.
         eapply in_extract_Some in H1,H4.
         eapply in_map_iff in H1,H4. invs.
         rewrite <- H1 in H4.
         repeat decomp_index.
         erewrite eq_partial_interpret_reindexer_padr in H1, H4.
         erewrite eq_partial_interpret_reindexer_padl in H4.
         rewrite (Nat.add_comm (Z.to_nat (eval_Zexpr_Z_total $0 dim2)))
           in H1,H4.
         unfold partial_well_formed_reindexer in *. invs.
         pose proof H6 as Hinj; clear H6.
         erewrite result_has_shape_result_shape_Z in Hinj by eauto.
         pose proof H4.
         eapply Hinj in H4.
         invert H4. invert H16. lia.
         rewrite H16 in H6.
         rewrite H1 in H6. discriminate.
         eapply filter_In. split; eauto.
         repeat decomp_goal_index. split. lia. eauto. rewrite <- H7.
         rewrite <- (Z2Nat.id (eval_Zexpr_Z_total $0 dim1)) by lia.
         erewrite <- result_lookup_Z_truncl. 2: lia.
         rewrite truncl_list_skipn. rewrite skipn_app.
         rewrite skipn_all2.
         2: { erewrite result_has_shape_length by eauto. lia. }
         erewrite result_has_shape_length by eauto. rewrite sub_diag.
         simpl. reflexivity.
         eapply filter_In. split.
         repeat decomp_goal_index. split. lia. eauto. rewrite <- H9.
         simpl. cases z0; try lia.
         rewrite nth_error_app1.
         2: { erewrite result_has_shape_length by eauto. lia. } auto.
         rewrite nth_error_app1.
         2: { erewrite result_has_shape_length by eauto. lia. } auto.
         all: try apply Hrdx.
         all: try apply Henv.
         all: try lia.
         all: eauto. }
    eapply H; eauto.
    erewrite size_of_sizeof in * by eauto. simpl in H4.
    erewrite result_has_shape_result_shape_Z in * by eauto.
    unfold partial_result_to_array_delta in *.
    unfold partial_result_to_array_delta_by_indices in *.
    rewrite partial_dom_fold_left_array_add in *.
    2: { erewrite result_has_shape_result_shape_Z by eauto.
         eapply partial_injective_concat_r.
         eapply Hrdx. eauto. eauto. apply Henv.
         all: try apply Hrdx. eauto. eauto. }
    2: { unfold partial_well_formed_reindexer in *. invs.
         erewrite result_has_shape_result_shape_Z in * by eauto.
         eauto. }
    rewrite dom_empty in *. rewrite cup_empty_r in *.
    erewrite <- In_iff_in in *.
    erewrite <- in_extract_Some in *.
    erewrite in_map_iff in *. invs.
    rewrite filter_idempotent in *.
    erewrite result_has_shape_result_shape_Z in * by eauto.
    repeat decomp_index.
    erewrite eq_partial_interpret_reindexer_padl in H2; eauto;
      try apply Henv; try apply Hrdx; try lia.
    eexists. rewrite H2. split. auto. eapply filter_In.
    split. repeat decomp_goal_index.
    split. lia. eauto. rewrite <- H5.
    rewrite <- (Z2Nat.id (eval_Zexpr_Z_total $0 dim1)) by lia.
    erewrite <- result_lookup_Z_truncl.
    rewrite truncl_list_skipn. rewrite skipn_app.
    rewrite skipn_all2.
    2: { erewrite result_has_shape_length by eauto. lia. }
    erewrite result_has_shape_length by eauto. rewrite sub_diag.
    simpl. reflexivity.
    lia. unfold partial_well_formed_reindexer in *. invs.
    erewrite result_has_shape_result_shape_Z in * by eauto. eauto.
  - rewrite dom_add in *. sets.
Qed.

Lemma assign_no_overwrite_concat_l :
  forall st h p sh v e1 e2 ec l1 l2 reindexer asm x rest1 rest2 dim1 dim2,
well_formed_environment st h p sh v (vars_of e1 \cup vars_of e2) ec ->
partial_well_formed_reindexer reindexer v (V (l1 ++ l2)) ->
assign_no_overwrite st h p reindexer (V (l1 ++ l2)) v asm ->
h $? p = Some x ->
size_of e1 (dim1 :: rest1) ->
size_of e2 (dim2 :: rest2) ->
result_has_shape (V l2)
           (Z.to_nat (eval_Zexpr_Z_total $0 dim2)
            :: map Z.to_nat
                 (map
                    (eval_Zexpr_Z_total $0) rest1)) ->
result_has_shape (V l1)
           (Z.to_nat (eval_Zexpr_Z_total $0 dim1)
            :: map Z.to_nat
                 (map
                    (eval_Zexpr_Z_total $0) rest1)) ->
result_has_shape (V (l1 ++ l2))
         (Z.to_nat (eval_Zexpr_Z_total $0 dim1) +
          Z.to_nat (eval_Zexpr_Z_total $0 dim2)
          :: map Z.to_nat
               (map
                  (eval_Zexpr_Z_total $0) rest1)) ->
(0 <= eval_Zexpr_Z_total $0 dim1)%Z ->
(0 <= eval_Zexpr_Z_total $0 dim2)%Z ->
eq_zexpr dim1 (| eval_Zexpr_Z_total $0 dim1 |)%z ->
eq_zexpr dim2 (| eval_Zexpr_Z_total $0 dim2 |)%z ->
vars_of_Zexpr dim2 = [] ->
   assign_no_overwrite st h p
    (fun l0 : list (Zexpr * Zexpr) =>
     reindexer
       match l0 with
       | [] => l0
       | (v0, d) :: xs => (v0, (d + dim2)%z) :: xs
       end) (V l1) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Henv Hrdx Hassign Hheap
         Hsize1 Hsize2 Hsh2 Hsh1 Hsh Hdim1nonneg Hdim2nonneg Heqdim1 Heqdim2
         Hvardim2.
  unfold assign_no_overwrite in *. invs.
  split; intros.
  - eapply H; eauto.
    erewrite result_has_shape_result_shape_Z in H4 by eauto.
    unfold partial_result_to_array_delta in *.
    unfold partial_result_to_array_delta_by_indices in *.
    erewrite partial_dom_fold_left_array_add.
    erewrite partial_dom_fold_left_array_add in H4.
    2: { erewrite result_has_shape_result_shape_Z by eauto.
         eapply partial_injective_concat_l; try apply Hrdx; eauto.
         apply Henv. rewrite Z2Nat.id by lia.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto. }
    2: { eapply Hrdx. }
    rewrite @filter_idempotent in *. rewrite dom_empty in *.
    rewrite cup_empty_r in *.
    erewrite <- In_iff_in. erewrite <- In_iff_in in H4.
    erewrite <- in_extract_Some in H4. erewrite <- in_extract_Some.
    erewrite in_map_iff in H4. erewrite in_map_iff. invs.
    erewrite eq_partial_interpret_reindexer_concat_l in H2.
    2: { eauto. }
    2: { eauto. }
    2: { apply Hsh2. }
    2: { apply Henv. }
    2: apply Hrdx.
    2: apply Hrdx.
    2: apply Hrdx.
    2: { rewrite Z2Nat.id by lia. eauto. }
    erewrite result_has_shape_result_shape_Z by eauto. eexists x1.
    split. auto. 
    erewrite result_has_shape_result_shape_Z in * by eauto.
    repeat decomp_index. eapply filter_In. split.
    repeat decomp_goal_index. split. lia. eauto.
    rewrite <- H6.
    simpl. rewrite nth_error_app1.
    2: { erewrite result_has_shape_length by eauto. lia. }
    reflexivity.
  - eapply lookup_Some_dom in Hheap. sets.
Qed.

Lemma assign_no_overwrite_transpose :
  forall e n0 m0 l0 st h p sh v ec l reindexer asm a,
    constant_nonneg_bounds e ->
    eval_Zexprlist v (n0 :: m0 :: l0) 
                   (eval_Zexpr_Z_total $0 n0
                                       :: eval_Zexpr_Z_total $0 m0
                                       :: map (eval_Zexpr_Z_total $0) l0) ->
    size_of e (n0 :: m0 :: l0) ->
    well_formed_environment st h p sh v (vars_of e) ec ->
    partial_well_formed_reindexer
      reindexer v
      (transpose_result l
                        (Z.to_nat (eval_Zexpr_Z_total $0 m0)
                                  :: Z.to_nat (eval_Zexpr_Z_total $0 n0)
                                  :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0))) ->
    assign_no_overwrite st h p reindexer
                        (transpose_result l
                                          (Z.to_nat (eval_Zexpr_Z_total $0 m0)
                                                    :: Z.to_nat (eval_Zexpr_Z_total $0 n0)
                                                    :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0))) v asm ->
    h $? p = Some a ->
    result_has_shape (V l)
                     (Z.to_nat (eval_Zexpr_Z_total $0 n0)
                               :: Z.to_nat (eval_Zexpr_Z_total $0 m0)
                               :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)) ->
    vars_of_Zexpr n0 = [] ->
    vars_of_Zexpr m0 = [] ->
    Forall (fun z : Zexpr => vars_of_Zexpr z = []) l0 ->
    assign_no_overwrite st h p
                        (fun l4 : list (Zexpr * Zexpr) =>
                           reindexer
                             match l4 with
                             | [] => l4
                             | [(v0, d0)] => l4
                             | (v0, d0) :: (vi, di) :: xs0 => (vi, di) :: (v0, d0) :: xs0
                             end) (V l) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hconst HeqZlist Hsize Henv Hrdx Hassign
         Hheap Hsh Hvarn0 Hvarm0 Hvarl0.
  unfold assign_no_overwrite in *. invs.
  split; intros.
  - eapply H; eauto. unfold partial_result_to_array_delta in *.
    erewrite <- partial_eq_result_to_array_delta_by_indices_shuffle
      with (shuffle:=(fun l => match l with
                               | x::y::xs => y::x::xs
                               | _ => l
                               end)). eassumption.
    + intros.
      erewrite result_has_shape_result_shape_Z in H7.
      2: { eapply result_has_shape_transpose_result. simpl in Hsh. eauto. }
      repeat decomp_index.
      rewrite mesh_grid_map_Nat2Z_id in *.
      erewrite result_lookup_Z_option_transpose.
      reflexivity. lia. lia. eauto.
    + intros.
      erewrite result_has_shape_result_shape_Z in H7.
      2: { eapply result_has_shape_transpose_result. simpl in Hsh. eauto. }
      erewrite result_has_shape_result_shape_Z by eauto.
      erewrite result_has_shape_result_shape_Z.
      2: { eapply result_has_shape_transpose_result. simpl in Hsh. eauto. }
      repeat decomp_index.
      rewrite eq_partial_interpret_reindexer_transpose;
        try apply Henv; try apply Hrdx; eauto.
    + intros.
      erewrite result_has_shape_result_shape_Z in H7.
      2: { eapply result_has_shape_transpose_result. simpl in Hsh. eauto. }
      repeat decomp_index.
      eapply filter_In. erewrite result_has_shape_result_shape_Z by eauto.
      propositional. repeat decomp_goal_index.
      propositional. repeat decomp_goal_index.
      propositional. rewrite <- H10.
      erewrite result_lookup_Z_option_transpose.
      reflexivity. lia. lia. eauto.
    + intros.
      erewrite result_has_shape_result_shape_Z in H7 by eauto.
      erewrite result_has_shape_result_shape_Z.
      2: { eapply result_has_shape_transpose_result. simpl in Hsh. eauto. }
      repeat decomp_index. eexists (z0::z::x0).
      split. auto. eapply filter_In. propositional.
      repeat decomp_goal_index. propositional. 
      repeat decomp_goal_index. propositional.
      rewrite <- H10. erewrite result_lookup_Z_option_transpose.
      reflexivity. lia. lia. eauto.
    + apply Hrdx.
    + decomp_partial_well_formed_reindexer.
      eapply partial_injective_transpose; eauto. apply Henv.
    + erewrite result_has_shape_result_shape_Z.
      2: { eapply result_has_shape_transpose_result. simpl in Hsh. eauto. }
      unfold injective.
      propositional. repeat decomp_index. invert H11. auto.
    + eapply no_dup_filter. eapply no_dup_mesh_grid.
    + eapply no_dup_filter. eapply no_dup_mesh_grid.
  - eapply lookup_Some_dom in Hheap. sets.
Qed.

Lemma assign_no_overwrite_flatten :
  forall e st h p sh v ec asm n m l0 a reindexer l,
    constant_nonneg_bounds e ->
    well_formed_environment st h p sh v (vars_of e) ec ->
    partial_well_formed_reindexer reindexer v (V (flatten_result l)) ->
    size_of e (n :: m :: l0) ->
    result_has_shape (V l)
                     (Z.to_nat (eval_Zexpr_Z_total $0 n)
                               :: Z.to_nat (eval_Zexpr_Z_total $0 m)
                               :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)) ->
    h $? p = Some a ->
    assign_no_overwrite st h p reindexer (V (flatten_result l)) v asm ->
    assign_no_overwrite st h p
                        (fun l5 : list (Zexpr * Zexpr) =>
                           reindexer
                             match l5 with
                             | [] => l5
                             | [(v0, d0)] => l5
                             | (v0, d0) :: (vi, di) :: xs => ((v0 * di + vi)%z, (d0 * di)%z) :: xs
                             end) (V l) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hconst Henv Hrdx Hsize Hsh Hheap Hassign.
  unfold assign_no_overwrite in *. invs.
  split; intros.
  - eapply H; eauto. unfold partial_result_to_array_delta in *.
    erewrite partial_eq_result_to_array_delta_by_indices_shuffle
      with (shuffle:= fun l =>
                        match l with
                        | x::y::xs =>
                            (x*(Z.of_nat
                                  (Z.to_nat
                                     (eval_Zexpr_Z_total $0 m))) + y)%Z::xs
                        | _ => l
                        end). eassumption.
    + intros. erewrite result_has_shape_result_shape_Z in H5 by eauto.
      repeat decomp_index.
      erewrite result_lookup_Z_option_flatten. reflexivity.
      lia. apply H2. eauto. lia. lia. eauto.
    + intros. erewrite result_has_shape_result_shape_Z in H5 by eauto.
      repeat decomp_index.
      erewrite result_has_shape_result_shape_Z.
      2: { eapply result_has_shape_flatten. eauto. }
      erewrite result_has_shape_result_shape_Z by eauto.
      eapply eq_partial_interpret_reindexer_flatten;
        try apply Henv; try apply Hrdx; eauto.
    + intros. erewrite result_has_shape_result_shape_Z in H5 by eauto.
      repeat decomp_index. eapply filter_In. propositional.
      erewrite result_has_shape_result_shape_Z.
      2: { eapply result_has_shape_flatten. eauto. }
      repeat decomp_goal_index. propositional. lia.
      rewrite Nat2Z.inj_mul.
      eapply mul_add_lt. lia. lia. lia. lia.
      rewrite <- H7. erewrite result_lookup_Z_option_flatten.
      reflexivity. lia. eauto. eauto. lia. eauto. eauto.
    + intros. erewrite result_has_shape_result_shape_Z in H5.
      2: { eapply result_has_shape_flatten. eauto. }
      repeat decomp_index.
      pose proof (Z_div_mod 
                    z (Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)))).
      assert (Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)) > 0)%Z by lia.
      propositional.
      cases (Z.div_eucl z (Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)))).
      invert H2. eexists (z0::z1::x0). rewrite Z.mul_comm.
      split. auto. erewrite result_has_shape_result_shape_Z by eauto.
      eapply filter_In. propositional.
      repeat decomp_goal_index. propositional. 
      assert (-1 * Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)) <
                z0 * Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)))%Z
        by lia.
      eapply Zmult_lt_reg_r in H11.
      lia. lia.
      rewrite Nat2Z.inj_mul in H10.
      rewrite
        (Z.mul_comm (Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 n)))) in H10.
      eapply div_eucl_bound in H10.
      lia.
      assert (-1 * Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)) <
                z0 * Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)))%Z
        by lia.
      eapply Zmult_lt_reg_r in H11.
      lia. lia.
      lia.
      repeat decomp_goal_index. propositional.
      rewrite <- H7.
      erewrite <- result_lookup_Z_option_flatten.
      rewrite Z.mul_comm. reflexivity.
      assert (-1 * Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)) <
                z0 * Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)))%Z
        by lia.
      eapply Zmult_lt_reg_r in H11.
      lia. lia. 
      rewrite Nat2Z.inj_mul in H10.
      rewrite
        (Z.mul_comm (Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 n)))) in H10.
      eapply div_eucl_bound in H10.
      apply H10.
      assert (-1 * Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)) <
                z0 * Z.of_nat (Z.to_nat (eval_Zexpr_Z_total $0 m)))%Z
        by lia.
      eapply Zmult_lt_reg_r in H11.
      lia. lia.
      eauto. eauto.
      lia. lia.
      eauto.
    + decomp_partial_well_formed_reindexer.
      erewrite result_has_shape_result_shape_Z in Hinj.
      2: { eapply result_has_shape_flatten; eauto. }
      erewrite result_has_shape_result_shape_Z by eauto.
      eapply partial_injective_flatten; try apply Henv; eauto.
    + decomp_partial_well_formed_reindexer. eauto.
    + unfold injective.
      erewrite result_has_shape_result_shape_Z by eauto.
      propositional.
      repeat decomp_index. invert H8.
      rewrite Z.mul_comm in H14. symmetry in H14.
      rewrite Z.mul_comm in H14. symmetry in H14.
      eapply Z.div_mod_unique in H14.
      invs. auto.
      lia. lia.
    + eapply no_dup_filter. eapply no_dup_mesh_grid.
    + eapply no_dup_filter. eapply no_dup_mesh_grid.
  - eapply lookup_Some_dom in Hheap. sets.
Qed.

Lemma assign_no_overwrite_gen_pad :
  forall st h p reindexer sh asm v a,
    h $? p = Some a ->
    assign_no_overwrite st h p reindexer
                        (V (gen_pad_list sh)) v asm.
Proof.
  intros.
  unfold assign_no_overwrite. split; intros.
  - cases sh. simpl in *.
    + rewrite partial_result_to_array_delta_empty_tensor in *.
      rewrite dom_empty in *. sets.
    + simpl gen_pad_list in *. rewrite <- gen_pad_cons in *.
      rewrite partial_result_to_array_delta_gen_pad in *.
      rewrite dom_empty in *. sets.
  - eapply lookup_Some_dom in H. sets.
Qed.

Lemma assign_no_overwrite_empty_tensor :
  forall st h p reindexer asm v a,
    h $? p = Some a ->
    assign_no_overwrite st h p reindexer (V []) v asm.
Proof.
  intros.
  unfold assign_no_overwrite. split; intros.
  - rewrite partial_result_to_array_delta_empty_tensor in *.
    rewrite dom_empty in *. sets.
  - eapply lookup_Some_dom in H. sets.
Qed.

Lemma assign_no_overwrite_tensor_shape_0 :
  forall l x l0 p x0 reindexer h st asm v,
    result_has_shape (V l)
                     (map Z.to_nat (x:: (map (eval_Zexpr_Z_total $0) l0))) ->
    Exists (fun x : Z => x = 0%Z) (map (eval_Zexpr_Z_total $0) l0) ->
    h $? p = Some x0 ->
    assign_no_overwrite st h p reindexer (V l) v asm.
Proof.
  intros.
  unfold assign_no_overwrite. split; intros.
  - unfold partial_result_to_array_delta in H5.
    erewrite result_has_shape_result_shape_Z in H5 by eauto.
    rewrite mesh_grid_filter_until in H5.
    rewrite mesh_grid_map_Nat2Z_id in H5.
    erewrite exists_0_empty_mesh_grid in H5.
    2: { simpl. right. eauto. }
    unfold partial_result_to_array_delta_by_indices in *. simpl in *.
    rewrite dom_empty in *. sets.
  - eapply lookup_Some_dom in H1. sets. 
Qed.

Lemma assign_no_overwrite_trunc_r :
  forall st h p sh v e ec reindexer m l0 k x asm x1,
    well_formed_environment st h p sh v (vars_of e) ec ->
    partial_well_formed_reindexer reindexer v
           (V
              (rev
                 (truncl_list (Z.to_nat (eval_Zexpr_Z_total $0 k))
                    (repeat
                       (gen_pad (map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)))
                       (Z.to_nat (eval_Zexpr_Z_total $0 k)) ++ 
                     rev x)))) ->
    size_of e (m :: l0) ->
    result_has_shape
          (V
             (x ++
              repeat (gen_pad (map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)))
                (Z.to_nat (eval_Zexpr_Z_total $0 k))))
          (Z.to_nat (eval_Zexpr_Z_total $0 m)
           :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)) ->
    vars_of_Zexpr k = [] ->
    (0 <= eval_Zexpr_Z_total $0 k)%Z ->
    constant_nonneg_bounds e ->
    vars_of_Zexpr m = [] ->
    Forall (fun z : Zexpr => vars_of_Zexpr z = []) l0 ->
    (eval_Zexpr_Z_total $0 k < eval_Zexpr_Z_total $0 m)%Z ->
    Forall (fun x : Z => (0 < x)%Z) (map (eval_Zexpr_Z_total $0) l0) ->
    h $? p = Some x1 ->
    assign_no_overwrite st h p reindexer (V x) v asm ->
    assign_no_overwrite st h p
                        (fun l1 : list (Zexpr * Zexpr) =>
                           reindexer match l1 with
                                     | [] => l1
                                     | (v0, d) :: xs => (v0, (d - k)%z) :: xs
                                     end)
                        (V
                           (x ++
                              repeat (gen_pad
                                        (map Z.to_nat
                                             (map (eval_Zexpr_Z_total $0) l0)))
                              (Z.to_nat (eval_Zexpr_Z_total $0 k)))) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? Henv Hrdx Hsize Hsh Hk Hknonneg Hconst
         Hm Hl0 Hmknonneg Hlopos Hheap Hassign.
  unfold assign_no_overwrite in *. invs.
  split; intros.
  - eapply H; eauto. simpl in *. 
    unfold partial_result_to_array_delta in *.
    erewrite partial_eq_result_to_array_delta_by_indices_shuffle with
      (shuffle:=fun x => x) in H4. eassumption.
    + intros. erewrite result_has_shape_result_shape_Z in H5.
      2: { repeat rewrite map_cons in Hsh.
           eapply result_has_shape_app_r; eauto. }
      rewrite repeat_length in *.
      repeat decomp_index.
      simpl. rewrite nth_error_app1. auto.
      erewrite result_has_shape_length.
      2: { repeat rewrite map_cons in Hsh.
           eapply result_has_shape_app_r; eauto. }
      rewrite repeat_length. lia.
    + intros. erewrite result_has_shape_result_shape_Z in H5.
      2: { repeat rewrite map_cons in Hsh.
           eapply result_has_shape_app_r; eauto. }
      rewrite repeat_length in *.
      repeat decomp_index.
      erewrite result_has_shape_result_shape_Z by eauto.
      repeat rewrite <- map_cons.
      rewrite eq_partial_interpret_reindexer_truncr;
        try apply Henv; try apply Hrdx.
      erewrite result_has_shape_result_shape_Z.
      2: { eapply result_has_shape_app_r in Hsh. eauto.
           rewrite repeat_length. reflexivity. }
      reflexivity.
      eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
      lia. lia. lia.
    + intros. erewrite result_has_shape_result_shape_Z in H5.
      2: { repeat rewrite map_cons in Hsh.
           eapply result_has_shape_app_r; eauto. }
      rewrite filter_fun_pad_r. repeat decomp_index.
      eapply filter_In. split; eauto.
      erewrite result_has_shape_result_shape_Z by eauto.
      repeat decomp_goal_index. split. lia. eauto.
    + intros. erewrite result_has_shape_result_shape_Z in H5; eauto.
      rewrite filter_fun_pad_r in *. repeat decomp_index.
      eexists (z::x2). propositional.
      erewrite result_has_shape_result_shape_Z.
      2: { repeat rewrite map_cons in Hsh.
           eapply result_has_shape_app_r; eauto. }
      eapply filter_In. split; eauto.
      rewrite repeat_length. repeat decomp_goal_index.
      split. simpl in H7. cases z; try lia.
      cases (nth_error x (Z.to_nat (Z.pos p0))); simpl in *.
      2: { discriminate. }
      eapply nth_error_Some in Heq.
      erewrite result_has_shape_length in Heq.
      2: { repeat rewrite map_cons in Hsh.
           eapply result_has_shape_app_r; eauto. }
      rewrite repeat_length in *. lia. eauto.
    + decomp_partial_well_formed_reindexer.
      pose proof Hinj.
      rewrite @truncl_list_app in *.
      2: { rewrite repeat_length; lia. }
      rewrite @truncl_list_skipn in *. rewrite @skipn_all2 in H5.
      2: { rewrite repeat_length. lia. }
      simpl in *. rewrite @rev_involutive in *.
      eauto. rewrite repeat_length. lia.
    + decomp_partial_well_formed_reindexer.
      rewrite @truncl_list_app in *.
      2: { rewrite repeat_length; lia. }
      rewrite @truncl_list_skipn in *. rewrite @skipn_all2 in Hinj.
      2: { rewrite repeat_length. lia. }
      simpl in *. rewrite @rev_involutive in *.
      erewrite result_has_shape_result_shape_Z in Hinj.
      2: { repeat rewrite map_cons in Hsh.
           eapply result_has_shape_app_r; eauto. }
      rewrite repeat_length in *. rewrite filter_fun_pad_r in *.
      erewrite result_has_shape_result_shape_Z by eauto.
      unfold partial_injective. intros.
      repeat decomp_index. repeat rewrite <- map_cons in *.
      erewrite eq_partial_interpret_reindexer_truncr in H7;
        eauto; try apply Henv; try lia.
      2: eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; auto.
      symmetry in H7.
      erewrite eq_partial_interpret_reindexer_truncr in H7; eauto;
        try apply Henv; try lia.
      2: eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; auto.
      pose proof H7.
      erewrite eq_partial_interpret_reindexer_truncr; eauto; try apply Henv;
        try lia.
      2: eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
      eapply Hinj in H7.
      2: { eapply filter_In. split; eauto. repeat decomp_goal_index.
           split; eauto. simpl in H9.
           cases z; try lia.
           cases (nth_error x (Z.to_nat (Z.pos p0))); simpl in *.
           2: discriminate.
           eapply nth_error_Some in Heq.
           erewrite result_has_shape_length in Heq.
           2: { repeat rewrite map_cons in Hsh.
                eapply result_has_shape_app_r; eauto. }
           rewrite repeat_length in *. lia. }
      2: { eapply filter_In. split; eauto. repeat decomp_goal_index.
           split; eauto. simpl in H10.
           cases z0; try lia.
           cases (nth_error x (Z.to_nat (Z.pos p0))); simpl in *.
           2: discriminate.
           eapply nth_error_Some in Heq.
           erewrite result_has_shape_length in Heq.
           2: { repeat rewrite map_cons in Hsh.
                eapply result_has_shape_app_r; eauto. }
           rewrite repeat_length in *. lia. }
      invert H7. left. invert H12. auto.
      rewrite <- H12. rewrite H8. auto.
    + unfold injective. propositional.
    + eapply no_dup_filter. eapply no_dup_mesh_grid.
    + eapply no_dup_filter. eapply no_dup_mesh_grid.
  - eapply lookup_Some_dom in Hheap. sets.
Qed.

Lemma assign_no_overwrite_trunc_l :
  forall st h p sh v e ec reindexer x x0 asm m l0 k x1,
    well_formed_environment st h p sh v (vars_of e) ec ->
    partial_well_formed_reindexer reindexer v (V x) ->
    assign_no_overwrite st h p reindexer (V x) v asm ->
    size_of e (m :: l0) ->
    constant_nonneg_bounds e ->
    result_has_shape
      (V
         (gen_pad_list
          (Z.to_nat (eval_Zexpr_Z_total $0 k)
                    :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)) ++ x))
      (map Z.to_nat (map (eval_Zexpr_Z_total $0) (m :: l0))) ->
    vars_of_Zexpr k = [] ->
    (0 <= eval_Zexpr_Z_total $0 k)%Z ->
    (eval_Zexpr_Z_total $0 k < eval_Zexpr_Z_total $0 m)%Z ->
    Forall (fun x : Z => (0 < x)%Z) (map (eval_Zexpr_Z_total $0) l0) ->
    Z.to_nat (eval_Zexpr_Z_total $0 k) <= x0 ->
    h $? p = Some x1 ->
    assign_no_overwrite st h p
                        (fun l1 : list (Zexpr * Zexpr) =>
                           reindexer
                             match l1 with
                             | [] => l1
                             | (v0, d) :: xs => ((v0 - k)%z, (d - k)%z) :: xs
                             end)
                        (V
                           (gen_pad_list
                              (Z.to_nat (eval_Zexpr_Z_total $0 k)
                                        :: map Z.to_nat
                                        (map (eval_Zexpr_Z_total $0) l0))
                              ++ x)) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Henv Hrdx Hassign Hsize Hconst Hsh Hk
         Hknonneg Hkm Hl0pos Hkx0 Hheap.
  unfold assign_no_overwrite in *. invs. split; intros.
  - eapply H; eauto.
    unfold partial_result_to_array_delta in *.
    erewrite partial_eq_result_to_array_delta_by_indices_shuffle
      with (shuffle:=(fun l => match l with
                               | [] => l
                               | x::xs =>
                                   (x+eval_Zexpr_Z_total $0 k)%Z::xs
                               end)) in H4. eassumption.
    + intros. erewrite result_has_shape_result_shape_Z in H5.
      2: { simpl in Hsh. eapply result_has_shape_app_l; eauto. }
      repeat decomp_index. rewrite repeat_length in *.
      eapply result_lookup_Z_option_concat_l; lia.
    + intros. erewrite result_has_shape_result_shape_Z in H5.
      2: { simpl in Hsh. eapply result_has_shape_app_l; eauto. }
      repeat decomp_index.
      erewrite result_has_shape_result_shape_Z by eauto.
      repeat rewrite map_cons.
      erewrite eq_partial_interpret_reindexer_truncl.
      erewrite result_has_shape_result_shape_Z.
      2: { simpl in Hsh. eapply result_has_shape_app_l; eauto. }
      rewrite repeat_length. reflexivity. 
      eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto.
      apply Henv. apply Hrdx. apply Hrdx. apply Hrdx. apply Hrdx.
      lia. lia. lia.
    + intros. erewrite result_has_shape_result_shape_Z in H5.
      2: { simpl in Hsh. eapply result_has_shape_app_l; eauto. }
      repeat decomp_index. rewrite repeat_length in *.
      erewrite result_has_shape_result_shape_Z by eauto.
      eapply filter_In. propositional.
      repeat decomp_goal_index. split. lia. eauto.
      rewrite <- H7. rewrite result_lookup_Z_option_concat_l. auto.
      lia. lia.
    + intros. erewrite result_has_shape_result_shape_Z in H5.
      2: eauto. repeat decomp_index. 
      eexists (z- eval_Zexpr_Z_total $0 k::x3)%Z. propositional.
      f_equal. lia. eapply filter_In. propositional.
      erewrite result_has_shape_result_shape_Z.
      2: { simpl in Hsh. eapply result_has_shape_app_l; eauto. }
      rewrite repeat_length. repeat decomp_goal_index.
      split; eauto.
      * cases (result_lookup_Z_option
                           (z :: x3)
                           (V
                              (gen_pad_list
                                 (Z.to_nat (eval_Zexpr_Z_total $0 k)
                                           :: map Z.to_nat
                                           (map (eval_Zexpr_Z_total $0) l0))
                                 ++ x))).
                  2: discriminate.
                  simpl in Heq. cases z; try lia.
                  cases ((Z.to_nat (eval_Zexpr_Z_total $0 k))).
                  -- simpl in *. lia.
                  -- simpl in *.
                     rewrite result_lookup_Z_option_gen_pad in Heq.
                     discriminate.
                  -- assert ((Z.to_nat (Z.pos p0)) <
                                (Z.to_nat (eval_Zexpr_Z_total $0 k)) \/
                                (Z.to_nat (eval_Zexpr_Z_total $0 k)) <=
                                  (Z.to_nat (Z.pos p0))) by lia.
                     invert H2. rewrite nth_error_app1 in Heq.
                     2: { rewrite repeat_length. lia. }
                     2: { lia. }
                     rewrite nth_error_repeat in Heq by lia.
                     rewrite result_lookup_Z_option_gen_pad in Heq.
                     discriminate.
      * rewrite <- H7. replace z with
          (z - eval_Zexpr_Z_total $0 k + eval_Zexpr_Z_total $0 k)%Z
          at 2 by lia.
        erewrite result_lookup_Z_option_concat_l. auto.
        2: lia.
        simpl in H7. cases z; try lia.
        cases ((Z.to_nat (eval_Zexpr_Z_total $0 k))).
        -- simpl in *. lia.
        -- simpl in *.
           rewrite result_lookup_Z_option_gen_pad in H7.
           discriminate.
        -- assert ((Z.to_nat (Z.pos p0)) <
                     (Z.to_nat (eval_Zexpr_Z_total $0 k)) \/
                     (Z.to_nat (eval_Zexpr_Z_total $0 k)) <=
                       (Z.to_nat (Z.pos p0))) by lia.
           invert H2. rewrite nth_error_app1 in H7.
           2: { rewrite repeat_length. lia. }
           2: { lia. }
           rewrite nth_error_repeat in H7 by lia.
           rewrite result_lookup_Z_option_gen_pad in H7.
           discriminate.
    + decomp_partial_well_formed_reindexer. eauto.
    + decomp_partial_well_formed_reindexer.
      erewrite result_has_shape_result_shape_Z by eauto.
      pose proof Hinj.
      erewrite result_has_shape_result_shape_Z in H5.
      2: { simpl in Hsh. eapply result_has_shape_app_l; eauto. }
      rewrite repeat_length in *.
      unfold partial_injective. intros.
      repeat decomp_index. repeat rewrite map_cons in *.
      replace z with ((z - eval_Zexpr_Z_total $0 k)
                      + eval_Zexpr_Z_total $0 k)%Z in H8 by lia.
      replace z0 with ((z0 - eval_Zexpr_Z_total $0 k)
                       + eval_Zexpr_Z_total $0 k)%Z in * by lia.
      erewrite eq_partial_interpret_reindexer_truncl in H8;
        eauto; try apply Henv.
      2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto. }
      2: { lia. }
      2: { lia. }
      symmetry in H8.
      erewrite eq_partial_interpret_reindexer_truncl in H8; eauto;
        try apply Henv.
      2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto. }
      2: { lia. }
      2: { lia. }
      symmetry in H8.
      repeat rewrite map_cons.
      erewrite eq_partial_interpret_reindexer_truncl; eauto; try apply Henv.
      2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto. }
      2: { lia. }
      2: { lia. }
      erewrite result_has_shape_result_shape_Z in Hinj.
      2: { simpl in Hsh. eapply result_has_shape_app_l; eauto. }
      rewrite repeat_length in *. eapply Hinj in H8.
      2: { eapply filter_In. split. repeat decomp_goal_index.
           split.
           - clear Hinj. rewrite Z.sub_add in *. simpl in *.
             cases z0; try lia.
             + cases (Z.to_nat (eval_Zexpr_Z_total $0 k)).
               * simpl in *. lia.
               * simpl in *.
                 rewrite result_lookup_Z_option_gen_pad in *.
                 simpl in *. discriminate.
             + assert ((Z.to_nat (Z.pos p0)) <
                         (Z.to_nat (eval_Zexpr_Z_total $0 k)) \/
                         (Z.to_nat (eval_Zexpr_Z_total $0 k)) <=
                           (Z.to_nat (Z.pos p0))) by lia.
               invert H9. rewrite nth_error_app1 in H11.
               2: { rewrite repeat_length. lia. }
               2: { lia. }
               rewrite nth_error_repeat in H11 by lia.
               rewrite result_lookup_Z_option_gen_pad in H11.
               discriminate.
           - auto.
           - rewrite <- H11.
             erewrite result_lookup_Z_option_concat_l.
             reflexivity.
             simpl in *. rewrite Z.sub_add in *.
             cases z0; try lia.
             + cases (Z.to_nat (eval_Zexpr_Z_total $0 k)).
               * simpl in *. lia.
               * simpl in *.
                 rewrite result_lookup_Z_option_gen_pad in *.
                 simpl in *. discriminate.
             + assert ((Z.to_nat (Z.pos p0)) <
                         (Z.to_nat (eval_Zexpr_Z_total $0 k)) \/
                         (Z.to_nat (eval_Zexpr_Z_total $0 k)) <=
                           (Z.to_nat (Z.pos p0))) by lia.
               invert H9. rewrite nth_error_app1 in H11.
               2: { rewrite repeat_length. lia. }
               2: { lia. }
               rewrite nth_error_repeat in H11 by lia.
               rewrite result_lookup_Z_option_gen_pad in H11.
               discriminate.
             + lia. }
      2: { eapply filter_In. split. repeat decomp_goal_index.
           split.
           - clear Hinj. rewrite Z.sub_add in *. simpl in *.
             cases z; try lia.
             + cases (Z.to_nat (eval_Zexpr_Z_total $0 k)).
               * simpl in *. lia.
               * simpl in *.
                 rewrite result_lookup_Z_option_gen_pad in *.
                 simpl in *. discriminate.
             + assert ((Z.to_nat (Z.pos p0)) <
                         (Z.to_nat (eval_Zexpr_Z_total $0 k)) \/
                         (Z.to_nat (eval_Zexpr_Z_total $0 k)) <=
                           (Z.to_nat (Z.pos p0))) by lia.
               invert H9. rewrite nth_error_app1 in H10.
               2: { rewrite repeat_length. lia. }
               2: { lia. }
               rewrite nth_error_repeat in H10 by lia.
               rewrite result_lookup_Z_option_gen_pad in H10.
               discriminate.
           - auto.
           - rewrite <- H10.
             replace z with (z - eval_Zexpr_Z_total $0 k +
                               eval_Zexpr_Z_total $0 k)%Z
                            at 2 by lia.
             erewrite result_lookup_Z_option_concat_l.
             reflexivity.
             simpl in *. rewrite Z.sub_add in *.
             cases z; try lia.
             + cases (Z.to_nat (eval_Zexpr_Z_total $0 k)).
               * simpl in *. lia.
               * simpl in *.
                 rewrite result_lookup_Z_option_gen_pad in *.
                 simpl in *. discriminate.
             + assert ((Z.to_nat (Z.pos p0)) <
                         (Z.to_nat (eval_Zexpr_Z_total $0 k)) \/
                         (Z.to_nat (eval_Zexpr_Z_total $0 k)) <=
                           (Z.to_nat (Z.pos p0))) by lia.
               invert H9. rewrite nth_error_app1 in H10.
               2: { rewrite repeat_length. lia. }
               2: { lia. }
               rewrite nth_error_repeat in H10 by lia.
               rewrite result_lookup_Z_option_gen_pad in H10.
               discriminate.
             + lia. }
               invert H8.
               invert H9. left. f_equal. lia. rewrite H9. eauto.
    + unfold injective. erewrite result_has_shape_result_shape_Z.
      2: { simpl in Hsh. eapply result_has_shape_app_l; eauto. }
      propositional. repeat decomp_index.
      invert H8. f_equal. lia.
    + eapply no_dup_filter. eapply no_dup_mesh_grid.
    + eapply no_dup_filter. eapply no_dup_mesh_grid.
  - eapply lookup_Some_dom in Hheap. sets.
Qed.

Lemma assign_no_overwrite_pad_r :
  forall st h p sh v e ec l k rest asm reindexer dim a,
    well_formed_environment st h p sh v (vars_of e) ec ->
    partial_well_formed_reindexer
      reindexer v
      (V
         (l ++
            repeat (gen_pad (map Z.to_nat (map (eval_Zexpr_Z_total $0) rest)))
            (Z.to_nat (eval_Zexpr_Z_total $0 k)))) ->
    assign_no_overwrite st h p reindexer
                        (V
                           (l ++
                              repeat
                              (gen_pad
                                 (map Z.to_nat
                                      (map (eval_Zexpr_Z_total $0) rest)))
                              (Z.to_nat (eval_Zexpr_Z_total $0 k)))) v asm ->
    constant_nonneg_bounds e ->
    Forall (fun x : Z => (0 <= x)%Z) (map (eval_Zexpr_Z_total $0) rest) ->
    result_has_shape (V l)
                     (map Z.to_nat (map (eval_Zexpr_Z_total $0) (dim::rest))) ->
    Forall (fun z : Zexpr => vars_of_Zexpr z = []) rest ->
    (0 <= eval_Zexpr_Z_total $0 k)%Z ->
    h $? p = Some a ->
    eq_zexpr k (| eval_Zexpr_Z_total $0 k |)%z ->
    eq_zexpr dim (| eval_Zexpr_Z_total $0 dim |)%z ->
    (0 < eval_Zexpr_Z_total $0 dim)%Z ->
    assign_no_overwrite st h p
                        (fun l0 : list (Zexpr * Zexpr) =>
                           reindexer match l0 with
                                     | [] => l0
                                     | (v0, d) :: xs => (v0, (d + k)%z) :: xs
                                     end) (V l) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? Henv Hrdx Hassign Hconst Hrestnonneg
         Hsh Hrest Hknonneg Hheap Hk Hdim Hdimpos.
  unfold assign_no_overwrite in *. invs.
  split; intros.
  - eapply H; eauto. unfold partial_result_to_array_delta in *.
    erewrite partial_eq_result_to_array_delta_by_indices_shuffle
      with (shuffle:=fun l1  => l1). eassumption.
    + intros. erewrite result_has_shape_result_shape_Z in * by eauto.
      repeat decomp_index.
      simpl. rewrite nth_error_app1. auto.
      erewrite result_has_shape_length.
      2: { simpl in Hsh. eauto. }
      lia.
    + intros. erewrite result_has_shape_result_shape_Z in * by eauto.
      repeat decomp_index. symmetry.
      erewrite result_has_shape_result_shape_Z by eauto.
      repeat rewrite map_cons.
      erewrite eq_partial_interpret_reindexer_concat_l
        with (l2:=repeat
                    (gen_pad (map Z.to_nat (map (eval_Zexpr_Z_total $0) rest)))
                    (Z.to_nat (eval_Zexpr_Z_total $0 k)));
        try apply Hrdx; try apply Henv.
      erewrite result_has_shape_result_shape_Z.
      2: { eapply result_has_shape_app.
           eapply result_has_shape_forall. simpl in Hsh. eauto.
           eapply Forall_repeat. eapply result_has_shape_gen_pad.
           rewrite repeat_length. reflexivity.
           erewrite result_has_shape_length.
           2: { simpl in Hsh. eauto. } lia. }
      erewrite result_has_shape_length.
      2: { simpl in Hsh. eauto. }
      reflexivity.
      2: { eauto. }
      erewrite result_has_shape_result_shape_Z by eauto.
      eapply filter_In. split. repeat decomp_goal_index.
      split. lia. eauto. eauto. eapply result_has_shape_repeat.
      eapply result_has_shape_gen_pad.
      rewrite Z2Nat.id by lia. eauto.
    + intros. rewrite filter_fun_pad_r.
      erewrite result_has_shape_result_shape_Z in H5 by eauto.
      erewrite result_has_shape_result_shape_Z.
      2: { eapply result_has_shape_app.
           eapply result_has_shape_forall. simpl in Hsh. eauto.
           eapply Forall_repeat. eapply result_has_shape_gen_pad.
           rewrite repeat_length. reflexivity.
           erewrite result_has_shape_length.
           2: { simpl in Hsh. eauto. } lia. }
      eapply filter_In. split; eauto.
      erewrite result_has_shape_length.
      2: { simpl in Hsh. eauto. }
      repeat decomp_index. repeat decomp_goal_index.
      split; eauto. lia. repeat decomp_index. eauto.
    + intros. erewrite result_has_shape_result_shape_Z by eauto.
      rewrite filter_fun_pad_r in *.
      erewrite result_has_shape_result_shape_Z in H5.
      2: { eapply result_has_shape_app.
           eapply result_has_shape_forall. simpl in Hsh. eauto.
           eapply Forall_repeat. eapply result_has_shape_gen_pad.
           rewrite repeat_length. reflexivity.
           erewrite result_has_shape_length.
           2: { simpl in Hsh. eauto. } lia. }
      erewrite result_has_shape_length in H5.
      2: { simpl in Hsh. eauto. }
      repeat decomp_index. eexists. split. reflexivity.
      eapply filter_In. split; eauto.
      repeat decomp_goal_index. split.
      simpl in H7.
      cases z; try lia.
      * cases (nth_error l (Z.to_nat (Z.pos p0))).
        -- simpl in *. eapply nth_error_Some in Heq.
           erewrite result_has_shape_length in Heq.
           2: { simpl in Hsh. eauto. } lia.
        -- simpl in *. discriminate.
      * eauto.
    + decomp_partial_well_formed_reindexer. pose proof Hinj.
      erewrite result_has_shape_result_shape_Z by eauto.
      repeat rewrite map_cons.
      eapply partial_injective_concat_l; auto; try apply Henv.
      repeat rewrite map_cons in Hinj. eapply Hinj.
      eapply result_has_shape_repeat_gen_pad.               
      rewrite Z2Nat.id by lia. auto.
    + decomp_partial_well_formed_reindexer. eauto.
    + unfold injective. propositional.
    + eapply no_dup_filter. eapply no_dup_mesh_grid.
    + eapply no_dup_filter. eapply no_dup_mesh_grid.
  - eapply lookup_Some_dom in Hheap. sets.
Qed.

Lemma assign_no_overwrite_pad_l :
  forall st h p sh v e ec reindexer asm l rest dim k a,
    well_formed_environment st h p sh v (vars_of e) ec ->
    partial_well_formed_reindexer
      reindexer v
      (V
         (repeat (gen_pad (map Z.to_nat (map (eval_Zexpr_Z_total $0) rest)))
                 (Z.to_nat (eval_Zexpr_Z_total $0 k)) ++ l)) ->
    constant_nonneg_bounds e ->
    Forall (fun x : Z => (0 <= x)%Z) (map (eval_Zexpr_Z_total $0) rest) ->
    result_has_shape (V l)
                     (map Z.to_nat
                          (map (eval_Zexpr_Z_total $0) (dim :: rest))) ->
    vars_of_Zexpr dim = [] ->
    Forall (fun z : Zexpr => vars_of_Zexpr z = []) rest ->
    vars_of_Zexpr k = [] ->
    (0 <= eval_Zexpr_Z_total $0 k)%Z ->
    h $? p = Some a ->
    (0 < eval_Zexpr_Z_total $0 dim)%Z ->
    assign_no_overwrite
      st h p reindexer
      (V
         (repeat (gen_pad (map Z.to_nat (map (eval_Zexpr_Z_total $0) rest)))
                 (Z.to_nat (eval_Zexpr_Z_total $0 k)) ++ l)) v asm ->
    assign_no_overwrite st h p
                        (fun l0 : list (Zexpr * Zexpr) =>
                           reindexer
                             match l0 with
                             | [] => l0
                             | (v0, d) :: xs => ((v0 + k)%z, (d + k)%z) :: xs
                             end) (V l) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? Henv Hrdx Hconst Hrestnonneg Hsh Hdim
         Hrest Hk Hknonneg Hheap Hdimpos Hassign.
  unfold assign_no_overwrite in *. invs.
  split; intros.
  2: { eapply lookup_Some_dom in Hheap. sets. }
  eapply H; eauto.
  unfold partial_result_to_array_delta in *.
  erewrite partial_eq_result_to_array_delta_by_indices_shuffle
    with (shuffle:=fun l1 : list Z =>
                     match l1 with
                     | [] => l1
                     | x1 :: xs =>
                         (x1 + eval_Zexpr_Z_total $0 k)%Z :: xs
                     end). eassumption.
  - erewrite result_has_shape_result_shape_Z by eauto. intros.
    repeat decomp_index. pose proof result_lookup_Z_option_concat_l.
    simpl gen_pad_list in H6. rewrite H6. reflexivity. lia. lia.
  - erewrite result_has_shape_result_shape_Z by eauto. intros.
    repeat decomp_index. repeat rewrite map_cons.
    erewrite eq_partial_interpret_reindexer_padl; eauto.
    erewrite result_has_shape_result_shape_Z.
    2: { eapply result_has_shape_concat.
         eapply result_has_shape_repeat.
         eapply result_has_shape_gen_pad. simpl in Hsh. eauto. }
    auto. 
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto.
    apply Henv. apply Hrdx. apply Hrdx. apply Hrdx. apply Hrdx.
  - erewrite result_has_shape_result_shape_Z by eauto. intros.
    repeat decomp_index.
    erewrite result_has_shape_result_shape_Z.
    2: { eapply result_has_shape_concat.
         eapply result_has_shape_repeat.
         eapply result_has_shape_gen_pad. simpl in Hsh. eauto. }
    rewrite <- Z2Nat.inj_add by lia.
    repeat rewrite <- map_cons.
    rewrite <- eval_Zexpr_Z_total_add_distr.
    rewrite <- map_cons.
    pose proof filter_pad_l_mesh_grid. simpl gen_pad_list in H6.
    rewrite H6. clear H6.
    2: { repeat rewrite map_cons.
         erewrite eval_Zexpr_Z_total_add_distr.
         rewrite Z2Nat.inj_add by lia.
         eapply result_has_shape_concat.
         eapply result_has_shape_repeat.
         eapply result_has_shape_gen_pad. simpl in Hsh. eauto. 
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total.
         eauto.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total.
         eauto.
    }
    eapply in_map_iff. eexists (z::x0). split. reflexivity.
    eapply filter_In. split; eauto.
    repeat decomp_goal_index. split.
    erewrite eval_Zexpr_Z_total_add_distr. lia.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
    eauto. lia.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
  - intros. erewrite result_has_shape_result_shape_Z by eauto.
    erewrite result_has_shape_result_shape_Z in H5.
    2: { eapply result_has_shape_concat.
         eapply result_has_shape_repeat.
         eapply result_has_shape_gen_pad. simpl in Hsh. eauto. }
    pose proof filter_pad_l_mesh_grid. simpl gen_pad_list in H6.
    erewrite <- Z2Nat.inj_add in H5 by lia.
    erewrite <- eval_Zexpr_Z_total_add_distr in H5.
    repeat rewrite <- map_cons in H5.
    rewrite H6 in H5. clear H6.
    2: { repeat rewrite map_cons.
         erewrite eval_Zexpr_Z_total_add_distr.
         rewrite Z2Nat.inj_add by lia.
         eapply result_has_shape_concat.
         eapply result_has_shape_repeat.
         eapply result_has_shape_gen_pad. simpl in Hsh. eauto. 
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total.
         eauto.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total.
         eauto. }
    2: lia.
    2: eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
    2: eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
    eapply in_map_iff in H5. invs.
    repeat decomp_index .
    rewrite eval_Zexpr_Z_total_add_distr in H5.
    2: eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
    2: eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto.
    eexists (z::x1). split. reflexivity.
    eapply filter_In. split; eauto. repeat decomp_goal_index.
    split. lia. eauto.
  - erewrite result_has_shape_result_shape_Z by eauto.
    repeat rewrite map_cons.
    assert (eval_Zexpr_Z_total $0 dim = 0 \/
              eval_Zexpr_Z_total $0 dim <> 0)%Z by lia. invert H5.
    { rewrite H6. simpl.
      unfold partial_injective. propositional. invert H2. }
    decomp_partial_well_formed_reindexer.
    eapply partial_injective_padl; eauto.
    apply Henv.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto.
  - decomp_partial_well_formed_reindexer. eauto.
  - unfold injective.
    erewrite result_has_shape_result_shape_Z by eauto.
    propositional. repeat decomp_index. invert H8. f_equal. lia.
  - eapply no_dup_filter. eapply no_dup_mesh_grid.
  - eapply no_dup_filter. eapply no_dup_mesh_grid.
Qed.

Lemma assign_no_overwrite_concat_r_ :
  forall st h p sh v e1 e2 ec l1 l2 reindexer asm x rest1 rest2 dim1 dim2,
well_formed_environment st h p sh v (vars_of e1 \cup vars_of e2) ec ->
partial_well_formed_reindexer reindexer v (V (l1 ++ l2)) ->
assign_no_overwrite st h p reindexer (V (l1 ++ l2)) v asm ->
h $? p = Some x ->
size_of e1 (dim1 :: rest1) ->
size_of e2 (dim2 :: rest2) ->
result_has_shape (V l2)
           (Z.to_nat (eval_Zexpr_Z_total $0 dim2)
            :: map Z.to_nat
                 (map
                    (eval_Zexpr_Z_total $0) rest1)) ->
result_has_shape (V l1)
           (Z.to_nat (eval_Zexpr_Z_total $0 dim1)
            :: map Z.to_nat
                 (map
                    (eval_Zexpr_Z_total $0) rest1)) ->
result_has_shape (V (l1 ++ l2))
         (Z.to_nat (eval_Zexpr_Z_total $0 dim1) +
          Z.to_nat (eval_Zexpr_Z_total $0 dim2)
          :: map Z.to_nat
               (map
                  (eval_Zexpr_Z_total $0) rest1)) ->
(0 <= eval_Zexpr_Z_total $0 dim1)%Z ->
(0 <= eval_Zexpr_Z_total $0 dim2)%Z ->
eq_zexpr dim1 (| eval_Zexpr_Z_total $0 dim1 |)%z ->
eq_zexpr dim2 (| eval_Zexpr_Z_total $0 dim2 |)%z ->
  assign_no_overwrite st
    (h $+ (p,
     array_add x
       (partial_result_to_array_delta
          (partial_interpret_reindexer
             (fun l6 : list (Zexpr * Zexpr) =>
              reindexer
                match l6 with
                | [] => l6
                | (v0, d) :: xs => (v0, (d + |eval_Zexpr_Z_total $0 dim2|)%z) :: xs
                end) (result_shape_Z (V l1)) v) (V l1)))) p
    (fun l6 : list (Zexpr * Zexpr) =>
     reindexer
       match l6 with
       | [] => l6
       | (v0, d) :: xs =>
           ((v0 + dim1)%z,
           (d + dim1)%z) :: xs
       end) (V l2) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Henv Hrdx Hassign Hheap
         Hsize1 Hsize2 Hsh2 Hsh1 Hsh Hdim1nonneg Hdim2nonneg Heqdim1 Heqdim2.
  unfold assign_no_overwrite in *. invs.
  split; intros.
  - rewrite lookup_add_eq in * by auto. invert H1.
    erewrite lookup_array_add_weak_l.
    2: { erewrite result_has_shape_result_shape_Z by eauto.
         erewrite result_has_shape_result_shape_Z in H4 by eauto.
         unfold partial_result_to_array_delta,
           partial_result_to_array_delta_by_indices in *.
         rewrite partial_dom_fold_left_array_add in *.
         2: { apply Hrdx. }
         2: { erewrite result_has_shape_result_shape_Z by eauto.
              eapply partial_injective_concat_r.
              eapply Hrdx. eauto. eauto. apply Henv.
              all: try apply Hrdx.
              eauto. eauto. }
         2: { erewrite result_has_shape_result_shape_Z by eauto.
              eapply partial_injective_concat_l.
              eapply Hrdx. eauto. eauto. apply Henv.
              all: try apply Hrdx.
              rewrite Z2Nat.id by lia.
              eauto. }
         rewrite filter_idempotent in *.
         rewrite dom_empty in *. rewrite cup_empty_r in *.
         erewrite result_has_shape_result_shape_Z in * by eauto.
         unfold not. intros.
         eapply In_iff_in in H1,H4.
         eapply in_extract_Some in H1,H4.
         eapply in_map_iff in H1,H4. invs.
         rewrite <- H1 in H4.
         repeat decomp_index.
         erewrite eq_partial_interpret_reindexer_padr in H1, H4.
         erewrite eq_partial_interpret_reindexer_padl in H4.
         rewrite (Nat.add_comm (Z.to_nat (eval_Zexpr_Z_total $0 dim2)))
           in H1,H4.
         unfold partial_well_formed_reindexer in *. invs.
         pose proof H6 as Hinj; clear H6.
         erewrite result_has_shape_result_shape_Z in Hinj by eauto.
         pose proof H4.
         eapply Hinj in H4.
         invert H4. invert H16. lia.
         rewrite H16 in H6.
         rewrite H1 in H6. discriminate.
         eapply filter_In. split; eauto.
         repeat decomp_goal_index. split. lia. eauto. rewrite <- H7.
         rewrite <- (Z2Nat.id (eval_Zexpr_Z_total $0 dim1)) by lia.
         erewrite <- result_lookup_Z_truncl. 2: lia.
         rewrite truncl_list_skipn. rewrite skipn_app.
         rewrite skipn_all2.
         2: { erewrite result_has_shape_length by eauto. lia. }
         erewrite result_has_shape_length by eauto. rewrite sub_diag.
         simpl. reflexivity.
         eapply filter_In. split.
         repeat decomp_goal_index. split. lia. eauto. rewrite <- H9.
         simpl. cases z0; try lia.
         rewrite nth_error_app1.
         2: { erewrite result_has_shape_length by eauto. lia. } auto.
         rewrite nth_error_app1.
         2: { erewrite result_has_shape_length by eauto. lia. } auto.
         all: try apply Hrdx.
         all: try apply Henv.
         all: try lia.
         all: eauto. }
    eapply H; eauto.
    erewrite result_has_shape_result_shape_Z in * by eauto.
    unfold partial_result_to_array_delta in *.
    unfold partial_result_to_array_delta_by_indices in *.
    rewrite partial_dom_fold_left_array_add in *.
    2: { erewrite result_has_shape_result_shape_Z by eauto.
         eapply partial_injective_concat_r.
         eapply Hrdx. eauto. eauto. apply Henv.
         all: try apply Hrdx. eauto. eauto. }
    2: { unfold partial_well_formed_reindexer in *. invs.
         erewrite result_has_shape_result_shape_Z in * by eauto.
         eauto. }
    rewrite dom_empty in *. rewrite cup_empty_r in *.
    erewrite <- In_iff_in in *.
    erewrite <- in_extract_Some in *.
    erewrite in_map_iff in *. invs.
    rewrite filter_idempotent in *.
    erewrite result_has_shape_result_shape_Z in * by eauto.
    repeat decomp_index.
    erewrite eq_partial_interpret_reindexer_padl in H2; eauto;
      try apply Henv; try apply Hrdx; try lia.
    eexists. rewrite H2. split. auto. eapply filter_In.
    split. repeat decomp_goal_index.
    split. lia. eauto. rewrite <- H5.
    rewrite <- (Z2Nat.id (eval_Zexpr_Z_total $0 dim1)) by lia.
    erewrite <- result_lookup_Z_truncl.
    rewrite truncl_list_skipn. rewrite skipn_app.
    rewrite skipn_all2.
    2: { erewrite result_has_shape_length by eauto. lia. }
    erewrite result_has_shape_length by eauto. rewrite sub_diag.
    simpl. reflexivity.
    lia. unfold partial_well_formed_reindexer in *. invs.
    erewrite result_has_shape_result_shape_Z in * by eauto. eauto.
  - rewrite dom_add in *. sets.
Qed.

Lemma assign_no_overwrite_concat_l_ :
  forall st h p sh v e1 e2 ec l1 l2 reindexer asm x rest1 rest2 dim1 dim2,
well_formed_environment st h p sh v (vars_of e1 \cup vars_of e2) ec ->
partial_well_formed_reindexer reindexer v (V (l1 ++ l2)) ->
assign_no_overwrite st h p reindexer (V (l1 ++ l2)) v asm ->
h $? p = Some x ->
size_of e1 (dim1 :: rest1) ->
size_of e2 (dim2 :: rest2) ->
result_has_shape (V l2)
           (Z.to_nat (eval_Zexpr_Z_total $0 dim2)
            :: map Z.to_nat
                 (map
                    (eval_Zexpr_Z_total $0) rest1)) ->
result_has_shape (V l1)
           (Z.to_nat (eval_Zexpr_Z_total $0 dim1)
            :: map Z.to_nat
                 (map
                    (eval_Zexpr_Z_total $0) rest1)) ->
result_has_shape (V (l1 ++ l2))
         (Z.to_nat (eval_Zexpr_Z_total $0 dim1) +
          Z.to_nat (eval_Zexpr_Z_total $0 dim2)
          :: map Z.to_nat
               (map
                  (eval_Zexpr_Z_total $0) rest1)) ->
(0 <= eval_Zexpr_Z_total $0 dim1)%Z ->
(0 <= eval_Zexpr_Z_total $0 dim2)%Z ->
eq_zexpr dim1 (| eval_Zexpr_Z_total $0 dim1 |)%z ->
eq_zexpr dim2 (| eval_Zexpr_Z_total $0 dim2 |)%z ->
vars_of_Zexpr dim2 = [] ->
   assign_no_overwrite st h p
    (fun l0 : list (Zexpr * Zexpr) =>
     reindexer
       match l0 with
       | [] => l0
       | (v0, d) :: xs => (v0, (d + | eval_Zexpr_Z_total $0 dim2| )%z) :: xs
       end) (V l1) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Henv Hrdx Hassign Hheap
         Hsize1 Hsize2 Hsh2 Hsh1 Hsh Hdim1nonneg Hdim2nonneg Heqdim1 Heqdim2
         Hvardim2.
  unfold assign_no_overwrite in *. invs.
  split; intros.
  - eapply H; eauto.
    erewrite result_has_shape_result_shape_Z in H4 by eauto.
    unfold partial_result_to_array_delta in *.
    unfold partial_result_to_array_delta_by_indices in *.
    erewrite partial_dom_fold_left_array_add.
    erewrite partial_dom_fold_left_array_add in H4.
    2: { erewrite result_has_shape_result_shape_Z by eauto.
         eapply partial_injective_concat_l; try apply Hrdx; eauto.
         apply Henv. rewrite Z2Nat.id by lia. eauto. }
    2: { eapply Hrdx. }
    rewrite @filter_idempotent in *. rewrite dom_empty in *.
    rewrite cup_empty_r in *.
    erewrite <- In_iff_in. erewrite <- In_iff_in in H4.
    erewrite <- in_extract_Some in H4. erewrite <- in_extract_Some.
    erewrite in_map_iff in H4. erewrite in_map_iff. invs.
    erewrite eq_partial_interpret_reindexer_concat_l in H2.
    2: { eauto. }
    2: { eauto. }
    2: { apply Hsh2. }
    2: { apply Henv. }
    2: apply Hrdx.
    2: apply Hrdx.
    2: apply Hrdx.
    2: { rewrite Z2Nat.id by lia. eauto. }
    erewrite result_has_shape_result_shape_Z by eauto. eexists x1.
    split. auto. 
    erewrite result_has_shape_result_shape_Z in * by eauto.
    repeat decomp_index. eapply filter_In. split.
    repeat decomp_goal_index. split. lia. eauto.
    rewrite <- H6.
    simpl. rewrite nth_error_app1.
    2: { erewrite result_has_shape_length by eauto. lia. }
    reflexivity.
  - eapply lookup_Some_dom in Hheap. sets.
Qed.

