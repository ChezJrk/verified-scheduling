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
     ResultToArrayDelta ContextsAgree Pad ATLDeep 
     LowerExists LowerCorrect.

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
            
Theorem lower_correct_weak_top :
  forall e,
    constant_nonneg_bounds e ->
    forall sh v ec r,
      (* functional evaluation of ATL *)
      eval_expr sh v ec e r ->
      forall l, size_of e l ->
      forall p st h reindexer asn,
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
        (* imperative evaluation of lowering *)
        eval_stmt v st h (lower e reindexer p asn sh)
                  (match reindexer (shape_to_index
                           (result_shape_Z r)
                           (shape_to_vars (result_shape_Z r))) with
                   | [] => st $+ (p, match st $? p with
                                     | Some r => r
                                     |_ => 0%R
                                     end + match r with
                                           | S (SS s) => s
                                           | _ => 0%R
                                           end)%R
                   | _ => st
                   end)
                  (match reindexer (shape_to_index
                                      (result_shape_Z r)
                                      (shape_to_vars (result_shape_Z r))) with
                   | [] => h
                   | _ =>
                       h $+ (p,
                              array_add
                                (h $! p)
                                (tensor_to_array_delta
                                   (partial_interpret_reindexer
                                      reindexer
                                      (result_shape_Z r) v) r))
                   end)
.
Proof.
  intros e Hconst sh v ec r Heval ls Hsize p st h reindexer asm
         Henv Hrdx Halloc Hctx pads g Hpad Hrelate.
  pose proof Heval.
  eapply lower_correct_exists in H; eauto. invs. pose proof H.
  eapply lower_correct_weak in H; eauto.
  cases (reindexer
           (shape_to_index (result_shape_Z r)
                           (shape_to_vars (result_shape_Z r)))); invs; eauto.
Qed.

Theorem lower_correct_top :
  forall e,
    constant_nonneg_bounds e ->
    forall r,
      (* functional evaluation of ATL *)
      eval_expr $0 $0 $0 e r ->
      forall l, size_of e l ->
      forall p st h asn,
        (h,st) =
          match (shape_to_index
                   (result_shape_Z r)
                   (shape_to_vars (result_shape_Z r))) with
          | [] => ($0,$0 $+ (p,0%R))
          | _ => (alloc_array_in_heap (result_shape_nat r) $0 p,$0)
          end ->
        ~ p \in vars_of e ->
        forall pads,
          has_pad $0 $0 $0 e pads ->
        (* imperative evaluation of lowering *)
        eval_stmt $0 st h (lower e (fun l => l) p asn $0) 
                  (match (fun l => l) (shape_to_index
                            (result_shape_Z r)
                            (shape_to_vars (result_shape_Z r))) with
                   | [] => st $+ (p, match st $? p with
                                     | Some r => r
                                     |_ => 0%R
                                     end + match r with
                                           | S (SS s) => s
                                           | _ => 0%R
                                           end)%R
                   | _ => st
                   end)
                  (match (fun l => l) (shape_to_index
                            (result_shape_Z r)
                            (shape_to_vars (result_shape_Z r))) with
                   | [] => h
                   | _ =>
                       h $+ (p,
                              array_add
                                (h $! p)
                                (tensor_to_array_delta
                                   (partial_interpret_reindexer
                                      (fun l => l)
                                      (result_shape_Z r) $0) r))
                   end).
Proof.
  intros.
  eapply lower_correct_weak_top; eauto.
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
    + unfold nondestructivity.
      destruct (result_shape_Z r) eqn:Hr.
      * simpl in *. invert H2. rewrite dom_add. rewrite lookup_add_eq by auto.
        rewrite dom_empty. rewrite cup_empty_r. rewrite lookup_empty.
        rewrite dom_empty.
        split; intros. discriminate. invert H2. eauto.
      * simpl in H2. invert H2. unfold alloc_array_in_heap.
        rewrite dom_empty. rewrite dom_add. rewrite lookup_add_eq by auto.
        rewrite dom_empty. rewrite cup_empty_r. rewrite lookup_empty.
        split; intros.
        2: discriminate.
        invert H2. pose proof Hr as Hrr.
        unfold result_shape_Z in Hr. destruct (result_shape_nat r).
        invert Hr. inversion Hr. subst.
        pose proof (lookup_alloc_array (fold_left mul (n :: l1) 1) x).
        invert H2; eauto.
        eapply lookup_None_dom in H5. rewrite dom_alloc_array in H5.
        exfalso. apply H5. clear H5.
        unfold tensor_to_array_delta in H7. rewrite Hrr in *.
        unfold tensor_to_array_delta_by_indices in H7.
        erewrite partial_dom_fold_left_array_add in H7.
        rewrite dom_empty in H7. rewrite cup_empty_r in H7.
        erewrite <- In_iff_in in *.
        eapply in_extract_Some in H7. eapply in_map_iff in H7. invs.
        rewrite partial_interpret_reindexer_id_flatten in H5. invert H5.
        rewrite filter_idempotent in H7.
        rewrite Z_of_nat_fold_left_mul.
        eapply in_mesh_grid_flatten_in_range.
        eapply Forall_map. eapply Forall_forall. lia.
        decomp_index. eauto.
        rewrite filter_idempotent in H7.
        decomp_index. eauto. rewrite dom_empty. sets.
        eapply partial_injective_id_reindexer. rewrite dom_empty. sets.
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

