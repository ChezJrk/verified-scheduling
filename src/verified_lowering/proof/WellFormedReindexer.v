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
From Lower Require Import Zexpr Bexpr Array Range Sexpr Result ListMisc
  Meshgrid VarGeneration Injective Constant InterpretReindexer ATLDeep
  WellFormedEnvironment WellFormedAllocation ResultToArrayDelta.

Open Scope string_scope.

Definition nondestructivity (st : stack) h p reindexer r v asn :=
  (forall arr,
      h $? p = Some arr ->
      asn = Assign ->
      ~ p \in dom st ->
   forall x,
     x \in dom (tensor_to_array_delta
                  (partial_interpret_reindexer reindexer (result_shape_Z r)
                  v) r) ->
           arr $? x = Some 0%R) /\
    (forall a,
        st $? p = Some a ->
      asn = Assign ->
        ~ p \in dom h ->
                a = 0%R).

Definition well_formed_reindexer
           (c : list (Zexpr * Z) -> list (Zexpr * Z))
           (v : valuation)
           (r : result) st h o a
  :=
  partial_injective
    (partial_interpret_reindexer c (result_shape_Z r) v)
    ((filter
        (fun x =>
           negb (is_None (result_lookup_Z_option x r)))
        (mesh_grid (result_shape_Z r)))) /\
    (forall l1 l2,
        eq_Z_tuple_index_list l1 l2 ->
        eq_Z_tuple_index_list (c l1) (c l2)) /\
    (vars_of_reindexer (c [])) \subseteq dom v /\
    (forall var k l,
        ~ var \in (vars_of_reindexer (c [])) ->
        map (subst_var_in_Z_tup var k) (c l) =
          c (map (subst_var_in_Z_tup var k) l)) /\
      (forall l, vars_of_reindexer (c l) =
                   vars_of_reindexer (c []) \cup vars_of_reindexer l) /\
    nondestructivity st h o c r v a.

Ltac decomp_well_formed_reindexer :=
  match goal with
  | H : well_formed_reindexer _ _ _ _ _ _ _ |- _ =>
      unfold well_formed_reindexer in * ;
      inversion H as [ Hinj Hrest1 ]; clear H;
      inversion Hrest1 as [ HeqZlist Hrest2 ]; clear Hrest1;
      inversion Hrest2 as [ Hvarsub Hrest3 ]; clear Hrest2;
      inversion Hrest3 as [ Hmap Hrest4 ]; clear Hrest3;
      inversion Hrest4 as [ Hvarsarg Hnondstr ]; clear Hrest4
  end.

Lemma nondestructivity_split :
  forall st h p reindexer n k l v asm l0 x,
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
partial_injective
           (partial_interpret_reindexer reindexer
              (result_shape_Z
                 (V (split_result (Z.to_nat k) l))) v)
           (filter
              (fun x : list Z =>
               negb
                 (is_None
                    (result_lookup_Z_option x
                       (V (split_result (Z.to_nat k) l)))))
              (mesh_grid
                 (result_shape_Z
                    (V (split_result (Z.to_nat k) l))))) ->
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
    nondestructivity
      st h p reindexer
      (V (split_result (Z.to_nat k) l)) v asm ->
    (0 < k)%Z ->
    result_has_shape (V l) (n :: l0) ->
    h $? p = Some x ->
  nondestructivity st h p
    (fun l2 : list (Zexpr * Z) =>
     reindexer
       match l2 with
       | [] => l2
       | (v0, d) :: xs => ((v0 / | k |)%z, (d // k)%Z) :: ((v0 % | k |)%z, k) :: xs
       end) (V l) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? Henv Hinj HeqZlist Hvarsub Hmap Hvarsarg
    Hassign Hkpos Hsh Hheap.
  unfold nondestructivity. split; intros.
  2: { eapply lookup_Some_dom in Hheap. sets. }
  assert (Some x = Some arr). rewrite <- H,<-Hheap. auto. invert H3.
  eapply Hassign; try apply Hrdx; eauto.
  unfold tensor_to_array_delta in *.
  pose proof Hsh as Hshsplit.
  eapply result_has_shape_split_result
    with (k:= Z.to_nat k) in Hshsplit.
  erewrite eq_tensor_to_array_delta_by_indices_shuffle
    with (shuffle:=
            fun l =>
              match l with
              | x::xs => (x/ k)%Z ::(Zmod x k)%Z::xs
              | _ => l
              end). eassumption.
  - intros. cases x. propositional.
    erewrite result_has_shape_result_shape_Z in H0 by eauto.
    repeat decomp_index.
    rewrite <- (Z2Nat.id k) at 1 by lia. 
    rewrite <- (Z2Nat.id k) at 2 by lia.
    erewrite result_lookup_Z_option_split. reflexivity.
    repeat decomp_index. eauto. lia. apply H0. lia. eauto.
  - intros. erewrite result_has_shape_result_shape_Z in * by eauto.
    erewrite result_has_shape_result_shape_Z in * by eauto.
    repeat decomp_index.
    erewrite <- eq_partial_interpret_reindexer_split;
      try apply Henv; try apply Hrdx; try lia; eauto.
  - erewrite result_has_shape_result_shape_Z in * by eauto.
    erewrite result_has_shape_result_shape_Z in * by eauto.
    intros. repeat decomp_index.
    eapply filter_In. split.
    repeat decomp_goal_index.
    split. split.
    eapply Z.div_pos. lia. lia.
    rewrite <- of_nat_div_distr.
    rewrite Z2Nat.id by lia.
    eapply floor_lt_ceil_mono_l; lia.
    decomp_goal_index. split.
    rewrite Z2Nat.id by lia. eapply Z.mod_pos_bound. lia.
    eauto.
    rewrite <- H4.
    f_equal. f_equal.
    rewrite <- (Z2Nat.id k) at 1 by lia.
    rewrite <- (Z2Nat.id k) at 2 by lia.
    erewrite result_lookup_Z_option_split. reflexivity.
    eauto. lia. apply H0. lia. eauto.
  - erewrite result_has_shape_result_shape_Z in * by eauto.
    erewrite result_has_shape_result_shape_Z in * by eauto.
    intros. repeat decomp_index.
    eexists ((z*k + z0)%Z::x).
    rewrite Z.div_add_l by lia.
    rewrite Z.div_small by lia. rewrite Z.add_0_r.
    pose proof Z.add_mul_mod_distr_r.
    specialize H5 with (b:=1%Z) (c:= k).
    rewrite Z.mul_1_l in *.
    rewrite H5.
    rewrite Z.mod_1_r. split. auto.
    eapply filter_In. split.
    repeat decomp_goal_index. split.
    split. lia.
    eapply result_lookup_Z_option_split_true; eauto.
    rewrite <- of_nat_div_distr in *.
    rewrite Z2Nat.id in H0.
    lia. lia. lia. lia.
    all: eauto.
    rewrite Nat2Z.id. eauto.
    rewrite <- H4.
    erewrite <- result_lookup_Z_option_split
            with (k:=Z.to_nat k); eauto.
    2: { lia. }
    3: lia.
    all: try lia.
    2: { rewrite <- of_nat_div_distr in *.
         rewrite Z2Nat.id in * by lia.
         eapply result_lookup_Z_option_split_true. eauto.
         lia. lia. lia. eauto. rewrite Nat2Z.id. eauto. }
    rewrite Z2Nat.id by lia.
    rewrite Z.div_add_l by lia. rewrite Z.div_small by lia.
    rewrite Z.add_0_r.
    pose proof Z.add_mul_mod_distr_r.
    specialize H7 with (b:=1%Z) (c:= k).
    rewrite Z.mul_1_l in *.
    rewrite H7.
    rewrite Z.mod_1_r. reflexivity. lia. lia. lia.
  - eapply partial_injective_split. eauto. eauto. apply Henv.
    all: eauto.
  - eauto.
  - unfold injective.
    erewrite result_has_shape_result_shape_Z by eauto.
    propositional. repeat decomp_index.
    invert H5.
    rewrite (Z.div_mod z k).
    rewrite (Z.div_mod z0 k).
    rewrite H10. rewrite H11. reflexivity. lia. lia.
  - eapply no_dup_filter. eauto with reindexers.
  - eapply no_dup_filter. eauto with reindexers.
  - lia.
Qed.

Lemma nondestructivity_array_add_shift_top_dim_reindexer :
  forall i lo hi l st h v x p r reindexer asm,
    (lo < hi)%Z ->
    ~ i \in dom v ->
    ~ contains_substring "?" i ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
  partial_injective
           (partial_interpret_reindexer reindexer (result_shape_Z (V (r :: l))) v)
           (filter
              (fun x : list Z =>
               negb (is_None (result_lookup_Z_option x (V (r :: l)))))
              (mesh_grid (result_shape_Z (V (r :: l))))) ->
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
    result_has_shape (V (r :: l)) (result_shape_nat (V (r :: l))) ->
    well_formed_allocation reindexer (V (r :: l)) st h p v ->
    length l =
      Z.to_nat (hi - (lo + 1)) ->
    nondestructivity st h p reindexer (V (r :: l)) v asm ->
    h $? p = Some x ->
  nondestructivity st
    (h $+ (p,
     array_add x
       (tensor_to_array_delta
          (partial_interpret_reindexer
             (fun l5 : list (Zexpr * Z) =>
              reindexer (((! i ! - | lo |)%z, (hi - lo)%Z) :: l5)) 
             (result_shape_Z r) (v $+ (i, lo))) r))) p
    (shift_top_dim_reindexer reindexer) (V l) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? Hlohi Hidom Hsubstring Henv
    Hinj HeqZlist Hvarsub Hmap Hvarsarg Hsh Halloc Hlen Hassign
    Hlookup.
  unfold nondestructivity. split; intros.
  2: { rewrite dom_add in H1. sets. }
  rewrite lookup_add_eq in H by auto. invert H.
  erewrite lookup_array_add_weak_l.
  2: { unfold not. intros. eapply dom_lookup_Some in H,H2. invs.
       unfold tensor_to_array_delta in *.
       unfold tensor_to_array_delta_by_indices in *.
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
            try apply Hrdx. unfold not. intros.
            apply Hsubstring. eapply shape_to_vars_contains_substring.
            eauto. simpl. lia. }
       2: { eapply partial_injective_shift_top_dim_reindexer;
            try apply Hrdx; eauto. cases l.
            inversion 1. rewrite dom_empty in *. sets.
            inversion 1. }
       symmetry in H0.
       erewrite result_has_shape_result_shape_Z in H0,H.
       2: { invert Hsh. eapply forall_result_has_shape; eauto. }
       repeat decomp_index.
       erewrite
         eq_partial_interpret_reindexer_shift_top_dim_reindexer
                   in H0,H; try apply Hrdx; eauto. 
       2: { cases l. inversion 1. simpl in *. lia. inversion 1. }
       2: { cases l. inversion 1. simpl in *. lia. inversion 1. }
       2: { eapply forall_result_has_shape; eauto. invert Hsh. eauto. }
       symmetry in H0.
       erewrite result_has_shape_result_shape_Z in H0.
       2: { invert Hsh. eauto. }
       erewrite eq_partial_interpret_reindexer_eval_0 in H0;
         try apply Hrdx; eauto. 
       2: { unfold not. intros. apply Hsubstring.
            eapply shape_to_vars_contains_substring. eauto. }
       2: { simpl. lia. }
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
  erewrite <- tensor_to_array_delta_cons with (hi := hi) (lo := lo).
  all: eauto.
  rewrite dom_array_add. sets.
  lia.
  unfold not. intros. eapply shape_to_vars_contains_substring in H. sets.
Qed.

Lemma nondestructivity_cons_0 :
  forall reindexer i lo hi v st h p r l x asm,
    (lo < hi)%Z ->
    ~ i \in dom v ->
    ~ contains_substring "?" i ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    partial_injective
           (partial_interpret_reindexer reindexer (result_shape_Z (V (r :: l))) v)
           (filter
              (fun x : list Z =>
               negb (is_None (result_lookup_Z_option x (V (r :: l)))))
              (mesh_grid (result_shape_Z (V (r :: l))))) ->
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
    result_has_shape (V (r :: l)) (result_shape_nat (V (r :: l))) ->
    h $? p = Some x ->
    length l =
      Z.to_nat (hi - (lo + 1)) ->
    nondestructivity st h p reindexer (V (r :: l)) v asm ->
  nondestructivity st h p
    (fun l3 : list (Zexpr * Z) =>
     reindexer (((! i ! - | lo |)%z, (hi - lo)%Z) :: l3)) r
    (v $+ (i, lo)) asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? Hlohi Hidom Hsubstring
    Henv Hinj HeqZlist Hvarsub Hmap Hvarsarg Hsh
    Hheap Hlen Hassign.
  unfold nondestructivity. split; intros.
  2: { eapply lookup_Some_dom in Hheap. sets. }
  assert (Some arr = Some x). rewrite <-H,<-Hheap. auto. invert H3.
  eapply Hassign; eauto.
  erewrite <- tensor_to_array_delta_cons with (lo := lo) (hi := hi).
  all: eauto.
  rewrite dom_array_add. sets.
  lia.
  unfold not. intros. apply Hsubstring.
  eapply shape_to_vars_contains_substring; eauto.
Qed.

Lemma nondestructivity_reduce :
  forall st h p reindexer r v,
    nondestructivity st h p reindexer r v Reduce.
Proof.
  intros. unfold nondestructivity. split; intros; discriminate.
Qed.

Lemma nondestructivity_add_stack :
  forall st h'0 p sh v x e1 e2 ec l2 asm reindexer r1,
    well_formed_environment st h'0 p sh v
                            ((constant [x] \cup vars_of e1) \cup vars_of e2) ec ->
    nondestructivity st h'0 p reindexer l2 v asm ->
    nondestructivity (st $+ (x, r1)) h'0 p reindexer l2 v asm.
Proof.
  intros. unfold nondestructivity in *.
  invs. split; intros.
  * rewrite dom_add in *.
    eapply H1; eauto. sets.
  * rewrite lookup_add_ne in H0.
    2: { unfold well_formed_environment in *. sets. }
    eapply H2; eauto.
Qed.

Lemma nondestructivity_alloc_stack :
  forall st h'0 p v x reindexer l2 asm r1,
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    nondestructivity st h'0 p reindexer l2 v asm ->
    nondestructivity (st $+ (x, 0%R)) h'0 x (fun l => l)
                        (S r1) v Assign.
Proof.
  intros.
  unfold nondestructivity in *. split; intros.
  * rewrite dom_add in *. sets.
  * rewrite lookup_add_eq in * by eauto. invert H1. eauto.
Qed.

Lemma nondestructivity_add_heap :
  forall st'0 h p sh v x e1 e2 ec asm reindexer l2 arr,
    well_formed_environment st'0 h p sh v
                            ((constant [x] \cup vars_of e1) \cup vars_of e2) ec ->
    nondestructivity st'0 h p reindexer l2 v asm ->
    nondestructivity st'0
                        (h $+ (x,arr)) p reindexer l2 v asm.
Proof.
  intros. unfold nondestructivity in *. invs.
  split; intros.
  - rewrite lookup_add_ne in H0.
    2: { unfold well_formed_environment in *. sets. }
    eapply H1; eauto.
  - rewrite dom_add in *. eapply H2; eauto. sets.
Qed.

Lemma nondestructivity_alloc_heap :
  forall e1 sz1 st'0 h p v x l2 asm z reindexer l1,
  size_of e1 (z::sz1) ->
  (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
  nondestructivity st'0 h p reindexer l2 v asm ->
  result_has_shape (V l1) (z :: sz1) ->
  nondestructivity st'0 (alloc_array_in_heap [flat_sizeof e1] h x) x
                      (fun l : list (Zexpr * Z) => l) (V l1) v Assign.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? Hsize Henv Hassign Hsh.
  unfold nondestructivity in *. invs.
  split; intros.
  - unfold alloc_array_in_heap in *. rewrite lookup_add_eq in * by auto.
    invert H1.
    unfold tensor_to_array_delta in H4.
    unfold tensor_to_array_delta_by_indices in H4.
    rewrite partial_dom_fold_left_array_add in H4.
    2: { eapply partial_injective_id_reindexer. apply Henv. }
    rewrite dom_empty in H4. rewrite cup_empty_r in H4.
    eapply In_iff_in in H4. eapply in_extract_Some in H4.
    eapply in_map_iff in H4. invs. rewrite @filter_idempotent in *.
    rewrite partial_interpret_reindexer_id_flatten in H4.
    invert H4. rewrite add_0_r.
    2: { decomp_index. eauto. }
    2: { apply Henv. }
    pose proof (lookup_alloc_array (flat_sizeof e1) (flatten (result_shape_Z (V l1)) x1)).
    invert H1. 2: auto.
    eapply lookup_None_dom in H4. exfalso. apply H4.
    rewrite dom_alloc_array. erewrite <- In_iff_in.
    unfold flat_sizeof in *. erewrite size_of_sizeof in * by eauto.
    erewrite result_has_shape_result_shape_Z by eauto.
    repeat decomp_index.
    erewrite filter_until_0_id.
    2: { erewrite result_has_shape_result_shape_Z in H1 by eauto.
         decomp_index.
         eapply mesh_grid_shape_pos in H1.
         eapply Forall_impl. 2: apply Forall_map; eassumption.
         simpl. lia. }
    rewrite Z_of_nat_fold_left_mul.
    replace (fold_left Z.mul (map Z.of_nat sz1) (Z.of_nat z)) with
      (fold_left Z.mul (map Z.of_nat (z :: sz1)) 1%Z).
    2: { simpl. f_equal. lia. }
    eapply in_mesh_grid_flatten_in_range.
    apply Forall_map. apply Forall_forall. lia.
    erewrite result_has_shape_result_shape_Z in H1 by eauto.
    repeat decomp_index.
    simpl map. decomp_goal_index. propositional.
  - rewrite dom_alloc_array_in_heap in *. sets. inversion 1.
Qed.

Lemma nondestructivity_concat_r :
  forall st h p v e1 e2 l1 l2 reindexer asm x rest1 rest2 dim1 dim2,
(forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
partial_injective
           (partial_interpret_reindexer reindexer (result_shape_Z (V (l1 ++ l2))) v)
           (filter
              (fun x : list Z =>
               negb (is_None (result_lookup_Z_option x (V (l1 ++ l2)))))
              (mesh_grid (result_shape_Z (V (l1 ++ l2))))) ->
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
nondestructivity st h p reindexer (V (l1 ++ l2)) v asm ->
h $? p = Some x ->
size_of e1 (dim1 :: rest1) ->
size_of e2 (dim2 :: rest2) ->
result_has_shape (V l2) (dim2 :: rest1) ->
result_has_shape (V l1) (dim1 :: rest1) ->
result_has_shape (V (l1 ++ l2)) (dim1 + dim2 :: rest1) ->
  nondestructivity st
    (h $+ (p,
     array_add x
       (tensor_to_array_delta
          (partial_interpret_reindexer
             (fun l6 : list (Zexpr * Z) =>
              reindexer
                match l6 with
                | [] => l6
                | (v0, d) :: xs => (v0, (d + Z.of_nat dim2)%Z) :: xs
                end) (result_shape_Z (V l1)) v) (V l1)))) p
    (fun l6 : list (Zexpr * Z) =>
     reindexer
       match l6 with
       | [] => l6
       | (v0, d) :: xs =>
           ((v0 + match sizeof e1 with
                  | [] => | 0 |
                  | n :: _ => | Z.of_nat n |
                  end)%z,
           (d + match sizeof e1 with
                | [] => 0
                | n :: _ => Z.of_nat n
                end)%Z) :: xs
       end) (V l2) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Henv Hinj HeqZlist Hvarsub Hmap
    Hvarsarg Hassign Hheap Hsize1 Hsize2 Hsh2 Hsh1 Hsh.
  unfold nondestructivity in *. invs.
  split; intros.
  - rewrite lookup_add_eq in * by auto. invert H1.
    erewrite lookup_array_add_weak_l.
    2: { erewrite result_has_shape_result_shape_Z by eauto.
         erewrite size_of_sizeof in * by eauto. simpl in H4. 
         erewrite result_has_shape_result_shape_Z in H4 by eauto.
         unfold tensor_to_array_delta,
           tensor_to_array_delta_by_indices in *.
         rewrite partial_dom_fold_left_array_add in *.
         2: { eauto. }
         2: { erewrite result_has_shape_result_shape_Z by eauto.
              eapply partial_injective_concat_r. eauto.
              cbn [eval_Zexpr_Z_total eval_Zexpr_Z] in *. rewrite Nat2Z.id in *.
              eauto. eauto. apply Henv.
              all: eauto.
              cbn [eval_Zexpr_Z_total eval_Zexpr_Z] in *. lia. }
         2: { erewrite result_has_shape_result_shape_Z by eauto.
              eapply partial_injective_concat_l.
              eauto. eauto. eauto. apply Henv.
              all: eauto. }
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
         rewrite (Nat.add_comm dim2)
           in H1,H4.
         (* pose proof H6 as Hinj; clear H6.
         erewrite result_has_shape_result_shape_Z in Hinj by eauto. *)
         cbn [eval_Zexpr_Z_total eval_Zexpr_Z] in H4. rewrite Nat2Z.id in H4.
         pose proof H4.
         eapply Hinj in H4.
         invert H4. invert H11. lia.
         rewrite H11 in H2.
         rewrite H1 in H2. discriminate.
         eapply filter_In. split; eauto.
         repeat decomp_goal_index. split. lia. eauto. rewrite <- H7.
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
    unfold tensor_to_array_delta in *.
    unfold tensor_to_array_delta_by_indices in *.
    rewrite partial_dom_fold_left_array_add in *.
    2: { erewrite result_has_shape_result_shape_Z by eauto.
         eapply partial_injective_concat_r with (l1:=l1).
         erewrite result_has_shape_result_shape_Z by eauto. eauto.
         cbn [eval_Zexpr_Z_total eval_Zexpr_Z] in *. rewrite Nat2Z.id in *.
         eauto. eauto. apply Henv.
         all: eauto.
         cbn [eval_Zexpr_Z_total eval_Zexpr_Z]. lia. }
    2: { invs.
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
    cbn [eval_Zexpr_Z_total eval_Zexpr_Z] in H2. rewrite Nat2Z.id in H2.
    eexists. rewrite H2. split. auto. eapply filter_In.
    split. repeat decomp_goal_index.
    split. lia. eauto. rewrite <- H5.
    erewrite <- result_lookup_Z_truncl.
    rewrite truncl_list_skipn. rewrite skipn_app.
    rewrite skipn_all2.
    2: { erewrite result_has_shape_length by eauto. lia. }
    erewrite result_has_shape_length by eauto. rewrite sub_diag.
    simpl. reflexivity.
    lia. erewrite result_has_shape_result_shape_Z in * by eauto. eauto.
  - rewrite dom_add in *. sets.
Qed.

Lemma nondestructivity_concat_r__ :
  forall st h p v l1 l2 reindexer asm x rest1 dim1 dim2,
(forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
partial_injective
           (partial_interpret_reindexer reindexer (result_shape_Z (V (l1 ++ l2))) v)
           (filter
              (fun x : list Z =>
               negb (is_None (result_lookup_Z_option x (V (l1 ++ l2)))))
              (mesh_grid (result_shape_Z (V (l1 ++ l2))))) ->
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
nondestructivity st h p reindexer (V (l1 ++ l2)) v asm ->
h $? p = Some x ->
result_has_shape (V l2) (dim2 :: rest1) ->
result_has_shape (V l1) (Z.to_nat dim1 :: rest1) ->
(0 <= dim1)%Z ->
  nondestructivity st
    (h $+ (p,
     array_add x
       (tensor_to_array_delta
          (partial_interpret_reindexer
             (fun l6 : list (Zexpr * Z) =>
              reindexer
                match l6 with
                | [] => l6
                | (v0, d) :: xs => (v0, (d + Z.of_nat dim2)%Z) :: xs
                end) (result_shape_Z (V l1)) v) (V l1)))) p
    (fun l6 : list (Zexpr * Z) =>
     reindexer
       match l6 with
       | [] => l6
       | (v0, d) :: xs =>
           ((v0 + | dim1 |)%z,
           (d + dim1)%Z) :: xs
       end) (V l2) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? Henv Hinj HeqZlist Hvarsub Hmap
    Hvarsarg Hnondstr Hheap Hsh2 Hsh1 Hdim1nonneg.
  unfold nondestructivity in *. invs.
  split; intros.
  - rewrite lookup_add_eq in * by auto. invert H1.
    erewrite lookup_array_add_weak_l.
    2: { erewrite result_has_shape_result_shape_Z by eauto.
         simpl in H4. 
         erewrite result_has_shape_result_shape_Z in H4 by eauto.
         unfold tensor_to_array_delta,
           tensor_to_array_delta_by_indices in *.
         rewrite partial_dom_fold_left_array_add in *.
         2: { eauto. }
         2: { erewrite result_has_shape_result_shape_Z by eauto.
              eapply partial_injective_concat_r. eauto.
              eauto. eauto. apply Henv.
              all: eauto. }
         2: { erewrite result_has_shape_result_shape_Z by eauto.
              eapply partial_injective_concat_l.
              eauto. eauto. eauto. apply Henv.
              all: eauto. }
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
         rewrite (Nat.add_comm dim2)
           in H1,H4.
         (* pose proof H6 as Hinj; clear H6.
          by eauto. *)
         erewrite result_has_shape_result_shape_Z in Hinj.
         2: { eapply result_has_shape_concat. eauto. eauto. }
         pose proof H4.
         eapply Hinj in H4.
         invert H4. invert H11. lia.
         rewrite H11 in H2.
         rewrite H1 in H2. discriminate.
         eapply filter_In. split; eauto.
         repeat decomp_goal_index. split. lia. eauto. rewrite <- H7.
         rewrite <- (Z2Nat.id dim1) by lia.
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
    simpl in H4.
    erewrite result_has_shape_result_shape_Z in * by eauto.
    unfold tensor_to_array_delta in *.
    unfold tensor_to_array_delta_by_indices in *.
    rewrite partial_dom_fold_left_array_add in *.
    2: { eauto.  }
    2: { erewrite result_has_shape_result_shape_Z by eauto.
         eapply partial_injective_concat_r with (l1:=l1).
         eauto. eauto. eauto. apply Henv. all: eauto. }
    2: { invs.
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
    eexists.
    erewrite result_has_shape_result_shape_Z.
    2: { eapply result_has_shape_concat; eauto. }
    rewrite H2. split. auto. eapply filter_In.
    split. repeat decomp_goal_index.
    split. lia. eauto. rewrite <- H5.
    rewrite <- (Z2Nat.id dim1) by lia.
    erewrite <- result_lookup_Z_truncl.
    rewrite truncl_list_skipn. rewrite skipn_app.
    rewrite skipn_all2.
    2: { erewrite result_has_shape_length by eauto. lia. }
    erewrite result_has_shape_length by eauto. rewrite sub_diag.
    simpl. reflexivity. lia.
  - rewrite dom_add in *. sets.
Qed.

Lemma nondestructivity_concat_l :
  forall st h p v l1 l2 reindexer asm x rest1 dim1 dim2,
(forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
partial_injective
           (partial_interpret_reindexer reindexer (result_shape_Z (V (l1 ++ l2))) v)
           (filter
              (fun x : list Z =>
               negb (is_None (result_lookup_Z_option x (V (l1 ++ l2)))))
              (mesh_grid (result_shape_Z (V (l1 ++ l2))))) ->
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
nondestructivity st h p reindexer (V (l1 ++ l2)) v asm ->
h $? p = Some x ->
result_has_shape (V l2) (dim2 :: rest1) ->
result_has_shape (V l1) (dim1 :: rest1) ->
   nondestructivity st h p
    (fun l0 : list (Zexpr * Z) =>
     reindexer
       match l0 with
       | [] => l0
       | (v0, d) :: xs => (v0, (d + Z.of_nat dim2)%Z) :: xs
       end) (V l1) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? Henv Hinj HeqZlist Hvarsub Hmap
    Hvarsarg Hassign Hheap Hsh2 Hsh1.
  unfold nondestructivity in *. invs.
  split; intros.
  - eapply H; eauto.
    erewrite result_has_shape_result_shape_Z in H4 by eauto.
    unfold tensor_to_array_delta in *.
    unfold tensor_to_array_delta_by_indices in *.
    erewrite partial_dom_fold_left_array_add.
    erewrite partial_dom_fold_left_array_add in H4.
    2: { erewrite result_has_shape_result_shape_Z by eauto.
         eapply partial_injective_concat_l; try apply Hrdx; eauto. }
    2: { eauto. }
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
    all: eauto.
    erewrite result_has_shape_result_shape_Z.
    2: { eapply result_has_shape_concat. eauto. eauto. }
    eexists x1.
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

Lemma nondestructivity_transpose :
  forall n0 m0 l0 st h p v l reindexer asm a,
    (*eval_Zexprlist v (n0 :: m0 :: l0) 
                   (eval_Zexpr_Z_total $0 n0
                                       :: eval_Zexpr_Z_total $0 m0
                                       :: map (eval_Zexpr_Z_total $0) l0) ->*)
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->

    partial_injective
           (partial_interpret_reindexer reindexer
              (result_shape_Z
                 (transpose_result l
                    (m0 :: n0 :: l0))) v)
           (filter
              (fun x : list Z =>
               negb
                 (is_None
                    (result_lookup_Z_option x
                       (transpose_result l
                          (m0 :: n0 :: l0)))))
              (mesh_grid
                 (result_shape_Z
                    (transpose_result l
                       (m0 :: n0 :: l0))))) ->
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

    nondestructivity st h p reindexer
                        (transpose_result l
                                          (m0 :: n0 :: l0)) v asm ->
    h $? p = Some a ->
    result_has_shape (V l)
                     (n0 :: m0 :: l0) ->
    nondestructivity st h p
                        (fun l4 : list (Zexpr * Z) =>
                           reindexer
                             match l4 with
                             | [] => l4
                             | [(v0, d0)] => l4
                             | (v0, d0) :: (vi, di) :: xs0 => (vi, di) :: (v0, d0) :: xs0
                             end) (V l) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? Henv Hinj HeqZZlist
    Hvarsub Hmap Hvarsarg Hassign Hheap Hsh.
  unfold nondestructivity in *. invs.
  split; intros.
  - eapply H; eauto. unfold tensor_to_array_delta in *.
    erewrite <- eq_tensor_to_array_delta_by_indices_shuffle
      with (shuffle:=(fun l => match l with
                               | x::y::xs => y::x::xs
                               | _ => l
                               end)). eassumption.
    + intros.
      erewrite result_has_shape_result_shape_Z in H5.
      2: { eapply result_has_shape_transpose_result. simpl in Hsh. eauto. }
      repeat decomp_index.
      erewrite result_lookup_Z_option_transpose.
      reflexivity. lia. lia. eauto.
    + intros.
      erewrite result_has_shape_result_shape_Z in H5.
      2: { eapply result_has_shape_transpose_result. simpl in Hsh. eauto. }
      erewrite result_has_shape_result_shape_Z by eauto.
      erewrite result_has_shape_result_shape_Z.
      2: { eapply result_has_shape_transpose_result. simpl in Hsh. eauto. }
      repeat decomp_index.
      rewrite eq_partial_interpret_reindexer_transpose;
        try apply Henv; try apply Hrdx; eauto.
    + intros.
      erewrite result_has_shape_result_shape_Z in H5.
      2: { eapply result_has_shape_transpose_result. simpl in Hsh. eauto. }
      repeat decomp_index.
      eapply filter_In. erewrite result_has_shape_result_shape_Z by eauto.
      propositional. repeat decomp_goal_index.
      propositional. repeat decomp_goal_index.
      propositional. rewrite <- H7.
      erewrite result_lookup_Z_option_transpose.
      reflexivity. lia. lia. eauto.
    + intros.
      erewrite result_has_shape_result_shape_Z in H5 by eauto.
      erewrite result_has_shape_result_shape_Z.
      2: { eapply result_has_shape_transpose_result. simpl in Hsh. eauto. }
      repeat decomp_index. eexists (z0::z::x0).
      split. auto. eapply filter_In. propositional.
      repeat decomp_goal_index. propositional. 
      repeat decomp_goal_index. propositional.
      rewrite <- H7. erewrite result_lookup_Z_option_transpose.
      reflexivity. lia. lia. eauto.
    + eauto.
    + eapply partial_injective_transpose; eauto. 
    + erewrite result_has_shape_result_shape_Z.
      2: { eapply result_has_shape_transpose_result. simpl in Hsh. eauto. }
      unfold injective.
      propositional. repeat decomp_index. invert H8. auto.
    + eapply no_dup_filter. eapply no_dup_mesh_grid.
    + eapply no_dup_filter. eapply no_dup_mesh_grid.
  - eapply lookup_Some_dom in Hheap. sets.
Qed.

Lemma nondestructivity_flatten :
  forall st h p v asm n m l0 a reindexer l,
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    partial_injective
           (partial_interpret_reindexer reindexer
              (result_shape_Z (V (flatten_result l))) v)
           (filter
              (fun x : list Z =>
               negb (is_None (result_lookup_Z_option x (V (flatten_result l)))))
              (mesh_grid (result_shape_Z (V (flatten_result l))))) ->
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
    result_has_shape (V l) (n :: m :: l0) ->
    h $? p = Some a ->
    nondestructivity st h p reindexer (V (flatten_result l)) v asm ->
    nondestructivity st h p
                        (fun l5 : list (Zexpr * Z) =>
                           reindexer
                             match l5 with
                             | [] => l5
                             | [(v0, d0)] => l5
                             | (v0, d0) :: (vi, di) :: xs => ((v0 * | di | + vi)%z, (d0 * di)%Z) :: xs
                             end) (V l) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? Henv Hinj HeqZlist
    Hvarsub Hmap Hvarsarg Hsh Hheap Hassign.
  unfold nondestructivity in *. invs.
  split; intros.
  - eapply H; eauto. unfold tensor_to_array_delta in *.
    erewrite eq_tensor_to_array_delta_by_indices_shuffle
      with (shuffle:= fun l =>
                        match l with
                        | x::y::xs =>
                            (x*(Z.of_nat
                                  m) + y)%Z::xs
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
                    z (Z.of_nat m)).
      assert (Z.of_nat m > 0)%Z by lia.
      propositional.
      cases (Z.div_eucl z (Z.of_nat m)).
      invert H2. eexists (z0::z1::x0). rewrite Z.mul_comm.
      split. auto. erewrite result_has_shape_result_shape_Z by eauto.
      eapply filter_In. propositional.
      repeat decomp_goal_index. propositional. 
      assert (-1 * Z.of_nat m <
                z0 * Z.of_nat m)%Z
        by lia.
      eapply Zorder.Zmult_lt_reg_r in H11.
      lia. lia.
      rewrite Nat2Z.inj_mul in H10.
      rewrite
        (Z.mul_comm (Z.of_nat n)) in H10.
      eapply div_eucl_bound in H10.
      lia.
      assert (-1 * Z.of_nat m < z0 * Z.of_nat m)%Z
        by lia.
      eapply Zorder.Zmult_lt_reg_r in H11.
      lia. lia.
      lia.
      repeat decomp_goal_index. propositional.
      rewrite <- H7.
      erewrite <- result_lookup_Z_option_flatten.
      rewrite Z.mul_comm. reflexivity.
      assert (-1 * Z.of_nat m < z0 * Z.of_nat m)%Z
        by lia.
      eapply Zorder.Zmult_lt_reg_r in H11.
      lia. lia. 
      rewrite Nat2Z.inj_mul in H10.
      rewrite
        (Z.mul_comm (Z.of_nat n)) in H10.
      eapply div_eucl_bound in H10.
      apply H10.
      assert (-1 * Z.of_nat m < z0 * Z.of_nat m)%Z
        by lia.
      eapply Zorder.Zmult_lt_reg_r in H11.
      lia. lia.
      eauto. eauto.
      lia. lia.
      eauto.
    + erewrite result_has_shape_result_shape_Z in Hinj.
      2: { eapply result_has_shape_flatten; eauto. }
      erewrite result_has_shape_result_shape_Z by eauto.
      eapply partial_injective_flatten; try apply Henv; eauto.
    + eauto.
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

Lemma nondestructivity_gen_pad :
  forall st h p reindexer sh asm v a,
    h $? p = Some a ->
    nondestructivity st h p reindexer
                        (V (gen_pad_list sh)) v asm.
Proof.
  intros.
  unfold nondestructivity. split; intros.
  - cases sh. simpl in *.
    + rewrite tensor_to_array_delta_empty_tensor in *.
      rewrite dom_empty in *. sets.
    + simpl gen_pad_list in *. rewrite <- gen_pad_cons in *.
      rewrite tensor_to_array_delta_gen_pad in *.
      rewrite dom_empty in *. sets.
  - eapply lookup_Some_dom in H. sets.
Qed.

Lemma nondestructivity_empty_tensor :
  forall st h p reindexer asm v a,
    h $? p = Some a ->
    nondestructivity st h p reindexer (V []) v asm.
Proof.
  intros.
  unfold nondestructivity. split; intros.
  - rewrite tensor_to_array_delta_empty_tensor in *.
    rewrite dom_empty in *. sets.
  - eapply lookup_Some_dom in H. sets.
Qed.

Lemma nondestructivity_tensor_shape_0 :
  forall l x l0 p x0 reindexer h st asm v,
    result_has_shape (V l)
                     (map Z.to_nat (x:: (map (eval_Zexpr_Z_total $0) l0))) ->
    Exists (fun x : Z => x = 0%Z) (map (eval_Zexpr_Z_total $0) l0) ->
    h $? p = Some x0 ->
    nondestructivity st h p reindexer (V l) v asm.
Proof.
  intros.
  unfold nondestructivity. split; intros.
  - unfold tensor_to_array_delta in H5.
    erewrite result_has_shape_result_shape_Z in H5 by eauto.
    rewrite mesh_grid_filter_until in H5.
    rewrite mesh_grid_map_Nat2Z_id in H5.
    erewrite exists_0_empty_mesh_grid in H5.
    2: { simpl. right. eauto. }
    unfold tensor_to_array_delta_by_indices in *. simpl in *.
    rewrite dom_empty in *. sets.
  - eapply lookup_Some_dom in H1. sets. 
Qed.

Lemma nondestructivity_trunc_r :
  forall st h p v reindexer m l0 k x asm x1,
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
partial_injective
           (partial_interpret_reindexer reindexer
              (result_shape_Z
                 (V
                    (rev
                       (truncl_list k
                          (repeat
                             (gen_pad l0)
                             k ++ 
                           rev x))))) v)
           (filter
              (fun x0 : list Z =>
               negb
                 (is_None
                    (result_lookup_Z_option x0
                       (V
                          (rev
                             (truncl_list k
                                (repeat
                                   (gen_pad l0)
                                   k ++ 
                                 rev x)))))))
              (mesh_grid
                 (result_shape_Z
                    (V
                       (rev
                          (truncl_list k
                             (repeat
                                (gen_pad l0)
                                k ++ 
                              rev x))))))) ->
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
    result_has_shape
          (V
             (x ++
              repeat (gen_pad l0)
                k))
          (m :: l0) ->
    (k < m) ->
    h $? p = Some x1 ->
    nondestructivity st h p reindexer (V x) v asm ->
    nondestructivity st h p
                        (fun l1 : list (Zexpr * Z) =>
                           reindexer match l1 with
                                     | [] => l1
                                     | (v0, d) :: xs => (v0, (d - Z.of_nat k)%Z) :: xs
                                     end)
                        (V
                           (x ++
                              repeat (gen_pad l0)
                              k)) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? Henv Hinj HeqZlist
    Hvarsub Hmap Hvarsarg Hsh Hmknonneg Hheap Hassign.
  unfold nondestructivity in *. invs.
  split; intros.
  - eapply H; eauto. simpl in *. 
    unfold tensor_to_array_delta in *.
    erewrite eq_tensor_to_array_delta_by_indices_shuffle with
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
      rewrite eq_partial_interpret_reindexer_truncr;
        try apply Henv; try apply Hrdx.
      erewrite result_has_shape_result_shape_Z.
      2: { eapply result_has_shape_app_r in Hsh. eauto.
           rewrite repeat_length. reflexivity. }
      reflexivity.
      all: eauto.
      lia. 
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
    + pose proof Hinj.
      rewrite @truncl_list_app in *.
      2: { rewrite repeat_length; lia. }
      rewrite @truncl_list_skipn in *. rewrite @skipn_all2 in H5.
      2: { rewrite repeat_length. lia. }
      simpl in *. rewrite @rev_involutive in *.
      eauto. rewrite repeat_length. lia.
    + rewrite @truncl_list_app in *.
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
      symmetry in H7.
      erewrite eq_partial_interpret_reindexer_truncr in H7; eauto;
        try apply Henv; try lia.
      pose proof H7.
      erewrite eq_partial_interpret_reindexer_truncr; eauto; try apply Henv;
        try lia.
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

Lemma nondestructivity_pad_r :
  forall st h p v l k rest asm reindexer dim a,
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
partial_injective
           (partial_interpret_reindexer reindexer
              (result_shape_Z
                 (V
                    (l ++ repeat (gen_pad rest) k)))
              v)
           (filter
              (fun x : list Z =>
               negb
                 (is_None
                    (result_lookup_Z_option x
                       (V
                          (l ++ repeat (gen_pad rest) k)))))
              (mesh_grid
                 (result_shape_Z
                    (V
                       (l ++ repeat (gen_pad rest) k))))) ->
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
    nondestructivity st h p reindexer
                        (V
                           (l ++
                              repeat
                              (gen_pad rest)
                              k)) v asm ->
    result_has_shape (V l) (dim::rest) ->
    h $? p = Some a ->
    (0 < dim) ->
    nondestructivity st h p
                        (fun l0 : list (Zexpr * Z) =>
                           reindexer match l0 with
                                     | [] => l0
                                     | (v0, d) :: xs => (v0, (d + Z.of_nat k)%Z) :: xs
                                     end) (V l) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? Henv Hinj HeqZlist
    Hvarsub Hmap Hvarsarg Hassign Hsh Hheap Hdimpos.
  unfold nondestructivity in *. invs.
  split; intros.
  - eapply H; eauto. unfold tensor_to_array_delta in *.
    erewrite eq_tensor_to_array_delta_by_indices_shuffle
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
                    (gen_pad rest) k);
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
      all: eauto.
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
    + pose proof Hinj.
      erewrite result_has_shape_result_shape_Z by eauto.
      repeat rewrite map_cons.
      eapply partial_injective_concat_l; auto; try apply Henv.
      repeat rewrite map_cons in Hinj. eapply Hinj.
      eapply result_has_shape_repeat_gen_pad.               
    + eauto.
    + unfold injective. propositional.
    + eapply no_dup_filter. eapply no_dup_mesh_grid.
    + eapply no_dup_filter. eapply no_dup_mesh_grid.
  - eapply lookup_Some_dom in Hheap. sets.
Qed.

Lemma nondestructivity_pad_l :
  forall st h p v reindexer asm l rest dim k a,
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
partial_injective
           (partial_interpret_reindexer reindexer
              (result_shape_Z
                 (V
                    (repeat (gen_pad rest)
                       (Z.to_nat k) ++ l))) v)
           (filter
              (fun x : list Z =>
               negb
                 (is_None
                    (result_lookup_Z_option x
                       (V
                          (repeat
                             (gen_pad rest)
                             (Z.to_nat k) ++ l)))))
              (mesh_grid
                 (result_shape_Z
                    (V
                       (repeat
                          (gen_pad rest)
                          (Z.to_nat k) ++ l))))) ->
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
    result_has_shape (V l) (dim :: rest) ->
    (0 <= k)%Z ->
    h $? p = Some a ->
    (0 < dim) ->
    nondestructivity
      st h p reindexer
      (V
         (repeat (gen_pad rest)
                 (Z.to_nat k) ++ l)) v asm ->
    nondestructivity st h p
                        (fun l0 : list (Zexpr * Z) =>
                           reindexer
                             match l0 with
                             | [] => l0
                             | (v0, d) :: xs => ((v0 + | k |)%z, (d + k)%Z) :: xs
                             end) (V l) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? Henv Hinj HeqZlist
    Hvarsub Hmap Hvarsarg Hsh Hknonneg Hheap Hdimpos Hassign.
  unfold nondestructivity in *. invs.
  split; intros.
  2: { eapply lookup_Some_dom in Hheap. sets. }
  eapply H; eauto.
  unfold tensor_to_array_delta in *.
  erewrite eq_tensor_to_array_delta_by_indices_shuffle
    with (shuffle:=fun l1 : list Z =>
                     match l1 with
                     | [] => l1
                     | x1 :: xs =>
                         (x1 + k)%Z :: xs
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
  - erewrite result_has_shape_result_shape_Z by eauto. intros.
    repeat decomp_index.
    erewrite result_has_shape_result_shape_Z.
    2: { eapply result_has_shape_concat.
         eapply result_has_shape_repeat.
         eapply result_has_shape_gen_pad. simpl in Hsh. eauto. }
    repeat rewrite <- map_cons.
    pose proof filter_pad_l_mesh_grid. simpl gen_pad_list in H6.
    rewrite H6. clear H6.
    2: { repeat rewrite map_cons.
         eapply result_has_shape_concat.
         eapply result_has_shape_repeat.
         eapply result_has_shape_gen_pad. simpl in Hsh. eauto. }
    eapply in_map_iff. eexists (z::x0). split. reflexivity.
    eapply filter_In. split; eauto.
    repeat decomp_goal_index. split. lia.
    eauto. lia.
  - intros. erewrite result_has_shape_result_shape_Z by eauto.
    erewrite result_has_shape_result_shape_Z in H5.
    2: { eapply result_has_shape_concat.
         eapply result_has_shape_repeat.
         eapply result_has_shape_gen_pad. simpl in Hsh. eauto. }
    pose proof filter_pad_l_mesh_grid. simpl gen_pad_list in H6.
    repeat rewrite <- map_cons in H5.
    rewrite H6 in H5. clear H6.
    2: { repeat rewrite map_cons.
         eapply result_has_shape_concat.
         eapply result_has_shape_repeat.
         eapply result_has_shape_gen_pad. simpl in Hsh. eauto. }
    2: lia.
    eapply in_map_iff in H5. invs.
    repeat decomp_index .
    eexists (z::x1). split. reflexivity.
    eapply filter_In. split; eauto. repeat decomp_goal_index.
    split. lia. eauto.
  - erewrite result_has_shape_result_shape_Z by eauto.
    repeat rewrite map_cons.
    eapply partial_injective_padl; eauto.
  - eauto.
  - unfold injective.
    erewrite result_has_shape_result_shape_Z by eauto.
    propositional. repeat decomp_index. invert H8. f_equal. lia.
  - eapply no_dup_filter. eapply no_dup_mesh_grid.
  - eapply no_dup_filter. eapply no_dup_mesh_grid.
Qed.

Lemma nondestructivity_concat_r_ :
  forall st h p v e1 e2 l1 l2 reindexer asm x rest1 rest2 dim1 dim2,
(forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
partial_injective
           (partial_interpret_reindexer reindexer (result_shape_Z (V (l1 ++ l2))) v)
           (filter
              (fun x : list Z =>
               negb (is_None (result_lookup_Z_option x (V (l1 ++ l2)))))
              (mesh_grid (result_shape_Z (V (l1 ++ l2))))) ->
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
nondestructivity st h p reindexer (V (l1 ++ l2)) v asm ->
h $? p = Some x ->
size_of e1 (dim1 :: rest1) ->
size_of e2 (dim2 :: rest2) ->
result_has_shape (V l2) (dim2 :: rest1) ->
result_has_shape (V l1) (dim1 :: rest1) ->
result_has_shape (V (l1 ++ l2)) (dim1 + dim2 :: rest1) ->
  nondestructivity st
    (h $+ (p,
     array_add x
       (tensor_to_array_delta
          (partial_interpret_reindexer
             (fun l6 : list (Zexpr * Z) =>
              reindexer
                match l6 with
                | [] => l6
                | (v0, d) :: xs => (v0, (d + Z.of_nat dim2)%Z) :: xs
                end) (result_shape_Z (V l1)) v) (V l1)))) p
    (fun l6 : list (Zexpr * Z) =>
     reindexer
       match l6 with
       | [] => l6
       | (v0, d) :: xs =>
           ((v0 + | Z.of_nat dim1 |)%z,
           (d + Z.of_nat dim1)%Z) :: xs
       end) (V l2) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Henv Hinj HeqZlist
    Hvarsub Hmap Hvarsarg Hassign Hheap Hsize1 Hsize2 Hsh2 Hsh1 Hsh.
  unfold nondestructivity in *. invs.
  split; intros.
  - rewrite lookup_add_eq in * by auto. invert H1.
    erewrite lookup_array_add_weak_l.
    2: { erewrite result_has_shape_result_shape_Z by eauto.
         erewrite result_has_shape_result_shape_Z in H4 by eauto.
         unfold tensor_to_array_delta,
           tensor_to_array_delta_by_indices in *.
         rewrite partial_dom_fold_left_array_add in *.
         2: { eauto. }
         2: { erewrite result_has_shape_result_shape_Z by eauto.
              eapply partial_injective_concat_r. all: eauto.
              all: cbn [eval_Zexpr_Z_total eval_Zexpr_Z].
              rewrite Nat2Z.id. eauto.
              lia. }
         2: { erewrite result_has_shape_result_shape_Z by eauto.
              eapply partial_injective_concat_l.
              all: eauto. }
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
         rewrite (Nat.add_comm dim2)
           in H1,H4.
         cbn [eval_Zexpr_Z_total eval_Zexpr_Z] in H4. rewrite Nat2Z.id in H4.
         pose proof H4.
         eapply Hinj in H4.
         invert H4. invert H11. lia.
         rewrite H11 in H2.
         rewrite H1 in H2. discriminate.
         eapply filter_In. split; eauto.
         repeat decomp_goal_index. split. lia. eauto. rewrite <- H7.
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
    unfold tensor_to_array_delta in *.
    unfold tensor_to_array_delta_by_indices in *.
    rewrite partial_dom_fold_left_array_add in *.
    2: { erewrite result_has_shape_result_shape_Z by eauto.
         eapply partial_injective_concat_r. all: eauto.
         erewrite result_has_shape_result_shape_Z by eauto. eauto.
         all: cbn [eval_Zexpr_Z_total eval_Zexpr_Z].
         rewrite Nat2Z.id. eauto.
         lia. }
    2: { invs.
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
    cbn [eval_Zexpr_Z_total eval_Zexpr_Z] in H2. rewrite Nat2Z.id in H2.
    eexists. rewrite H2. split. auto. eapply filter_In.
    split. repeat decomp_goal_index.
    split. lia. eauto. rewrite <- H5.
    erewrite <- result_lookup_Z_truncl.
    rewrite truncl_list_skipn. rewrite skipn_app.
    rewrite skipn_all2.
    2: { erewrite result_has_shape_length by eauto. lia. }
    erewrite result_has_shape_length by eauto. rewrite sub_diag.
    simpl. reflexivity.
    lia. invs.
    erewrite result_has_shape_result_shape_Z in * by eauto. eauto.
  - rewrite dom_add in *. sets.
Qed.

Lemma nondestructivity_concat_l_ :
  forall st h p v e1 e2 l1 l2 reindexer asm x rest1 rest2 dim1 dim2,
(forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
partial_injective
           (partial_interpret_reindexer reindexer (result_shape_Z (V (l1 ++ l2))) v)
           (filter
              (fun x : list Z =>
               negb (is_None (result_lookup_Z_option x (V (l1 ++ l2)))))
              (mesh_grid (result_shape_Z (V (l1 ++ l2))))) ->
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
nondestructivity st h p reindexer (V (l1 ++ l2)) v asm ->
h $? p = Some x ->
size_of e1 (dim1 :: rest1) ->
size_of e2 (dim2 :: rest2) ->
result_has_shape (V l2) (dim2 :: rest1) ->
result_has_shape (V l1) (dim1 :: rest1) ->
result_has_shape (V (l1 ++ l2)) (dim1 + dim2 :: rest1) ->
   nondestructivity st h p
    (fun l0 : list (Zexpr * Z) =>
     reindexer
       match l0 with
       | [] => l0
       | (v0, d) :: xs => (v0, (d + Z.of_nat dim2)%Z) :: xs
       end) (V l1) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Henv Hinj HeqZlist
    Hvarsub Hmap Hvarsarg Hassign Hheap Hsize1 Hsize2 Hsh2 Hsh1 Hsh.
  unfold nondestructivity in *. invs.
  split; intros.
  - eapply H; eauto.
    erewrite result_has_shape_result_shape_Z in H4 by eauto.
    unfold tensor_to_array_delta in *.
    unfold tensor_to_array_delta_by_indices in *.
    erewrite partial_dom_fold_left_array_add.
    erewrite partial_dom_fold_left_array_add in H4.
    2: { erewrite result_has_shape_result_shape_Z by eauto.
         eapply partial_injective_concat_l; try apply Hrdx; eauto. }
    2: { eauto. }
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
    all: eauto.
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

Lemma nondestructivity_trunc_l :
  forall st h p v reindexer x asm m l0 k x1,
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
partial_injective
           (partial_interpret_reindexer reindexer (result_shape_Z (V x)) v)
           (filter
              (fun x0 : list Z => negb (is_None (result_lookup_Z_option x0 (V x))))
              (mesh_grid (result_shape_Z (V x)))) ->
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
    nondestructivity st h p reindexer (V x) v asm ->
    result_has_shape
      (V
         (gen_pad_list
          (Z.to_nat k :: l0) ++ x))
      (m :: l0) ->
    (0 <= k)%Z ->
    (k < Z.of_nat m)%Z ->
    h $? p = Some x1 ->
    nondestructivity st h p
                        (fun l1 : list (Zexpr * Z) =>
                           reindexer
                             match l1 with
                             | [] => l1
                             | (v0, d) :: xs => ((v0 - | k |)%z, (d - k)%Z) :: xs
                             end)
                        (V
                           (gen_pad_list
                              (Z.to_nat k :: l0)
                              ++ x)) v asm.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? Henv Hinj HeqZlist
    Hvarsub Hmap Hvarsarg Hassign Hsh Hknonneg Hkm Hheap.
  unfold nondestructivity in *. invs. split; intros.
  - eapply H; eauto.
    unfold tensor_to_array_delta in *.
    erewrite eq_tensor_to_array_delta_by_indices_shuffle
      with (shuffle:=(fun l => match l with
                               | [] => l
                               | x::xs =>
                                   (x+k)%Z::xs
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
      apply Henv. all: eauto.
      lia. 
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
      eexists (z- k::x2)%Z. propositional.
      f_equal. lia. eapply filter_In. propositional.
      erewrite result_has_shape_result_shape_Z.
      2: { simpl in Hsh. eapply result_has_shape_app_l; eauto. }
      rewrite repeat_length. repeat decomp_goal_index.
      split; eauto.
      * cases (result_lookup_Z_option
                           (z :: x2)
                           (V
                              (gen_pad_list
                                 (Z.to_nat k :: l0)
                                 ++ x))).
                  2: discriminate.
                  simpl in Heq. cases z; try lia.
                  cases ((Z.to_nat k)).
                  -- simpl in *. lia.
                  -- simpl in *.
                     rewrite result_lookup_Z_option_gen_pad in Heq.
                     discriminate.
                  -- assert ((Z.to_nat (Z.pos p0)) <
                                (Z.to_nat k) \/
                                (Z.to_nat k) <=
                                  (Z.to_nat (Z.pos p0))) by lia.
                     invert H2. rewrite nth_error_app1 in Heq.
                     2: { rewrite repeat_length. lia. }
                     2: { lia. }
                     rewrite nth_error_repeat in Heq by lia.
                     rewrite result_lookup_Z_option_gen_pad in Heq.
                     discriminate.
      * rewrite <- H7. replace z with
          (z - k + k)%Z
          at 2 by lia.
        erewrite result_lookup_Z_option_concat_l. auto.
        2: lia.
        simpl in H7. cases z; try lia.
        cases ((Z.to_nat k)).
        -- simpl in *. lia.
        -- simpl in *.
           rewrite result_lookup_Z_option_gen_pad in H7.
           discriminate.
        -- assert ((Z.to_nat (Z.pos p0)) <
                     (Z.to_nat k) \/
                     (Z.to_nat k) <=
                       (Z.to_nat (Z.pos p0))) by lia.
           invert H2. rewrite nth_error_app1 in H7.
           2: { rewrite repeat_length. lia. }
           2: { lia. }
           rewrite nth_error_repeat in H7 by lia.
           rewrite result_lookup_Z_option_gen_pad in H7.
           discriminate.
    + eauto.
    + erewrite result_has_shape_result_shape_Z by eauto.
      pose proof Hinj.
      erewrite result_has_shape_result_shape_Z in H5.
      2: { simpl in Hsh. eapply result_has_shape_app_l; eauto. }
      rewrite repeat_length in *.
      unfold partial_injective. intros.
      repeat decomp_index. repeat rewrite map_cons in *.
      replace z with ((z - k)
                      + k)%Z in H8 by lia.
      replace z0 with ((z0 - k)
                       + k)%Z in * by lia.
      erewrite eq_partial_interpret_reindexer_truncl in H8;
        eauto; try apply Henv.
      2: { lia. }
      symmetry in H8.
      erewrite eq_partial_interpret_reindexer_truncl in H8; eauto;
        try apply Henv.
      2: { lia. }
      symmetry in H8.
      repeat rewrite map_cons.
      erewrite eq_partial_interpret_reindexer_truncl; eauto; try apply Henv.
      2: { lia. }
      erewrite result_has_shape_result_shape_Z in Hinj.
      2: { simpl in Hsh. eapply result_has_shape_app_l; eauto. }
      rewrite repeat_length in *. eapply Hinj in H8.
      2: { eapply filter_In. split. repeat decomp_goal_index.
           split.
           - clear Hinj. rewrite Z.sub_add in *. simpl in *.
             cases z0; try lia.
             + cases (Z.to_nat k).
               * simpl in *. lia.
               * simpl in *.
                 rewrite result_lookup_Z_option_gen_pad in *.
                 simpl in *. discriminate.
             + assert ((Z.to_nat (Z.pos p0)) <
                         (Z.to_nat k) \/
                         (Z.to_nat k) <=
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
             + cases (Z.to_nat k).
               * simpl in *. lia.
               * simpl in *.
                 rewrite result_lookup_Z_option_gen_pad in *.
                 simpl in *. discriminate.
             + assert ((Z.to_nat (Z.pos p0)) <
                         (Z.to_nat k) \/
                         (Z.to_nat k) <=
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
             + cases (Z.to_nat k).
               * simpl in *. lia.
               * simpl in *.
                 rewrite result_lookup_Z_option_gen_pad in *.
                 simpl in *. discriminate.
             + assert ((Z.to_nat (Z.pos p0)) <
                         (Z.to_nat k) \/
                         (Z.to_nat k) <=
                           (Z.to_nat (Z.pos p0))) by lia.
               invert H9. rewrite nth_error_app1 in H10.
               2: { rewrite repeat_length. lia. }
               2: { lia. }
               rewrite nth_error_repeat in H10 by lia.
               rewrite result_lookup_Z_option_gen_pad in H10.
               discriminate.
           - auto.
           - rewrite <- H10.
             replace z with (z - k +
                               k)%Z
                            at 2 by lia.
             erewrite result_lookup_Z_option_concat_l.
             reflexivity.
             simpl in *. rewrite Z.sub_add in *.
             cases z; try lia.
             + cases (Z.to_nat k).
               * simpl in *. lia.
               * simpl in *.
                 rewrite result_lookup_Z_option_gen_pad in *.
                 simpl in *. discriminate.
             + assert ((Z.to_nat (Z.pos p0)) <
                         (Z.to_nat k) \/
                         (Z.to_nat k) <=
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

Lemma well_formed_reindexer_truncl :
  forall reindexer m l0 k v x st h o asn arr,
    well_formed_reindexer reindexer v (V x) st h o asn ->
    result_has_shape
      (V (gen_pad_list
            (Z.to_nat k :: l0) ++ x))
      (m :: l0) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    (0 <= k)%Z ->
    h $? o = Some arr ->
    (k < Z.of_nat m)%Z ->
    well_formed_reindexer
      (fun l : list (Zexpr * Z) =>
         reindexer
           match l with
           | [] => l
           | (v0, d) :: xs => ((v0 - | k |)%z, (d - k)%Z) :: xs
           end) v
      (V (gen_pad_list
            (Z.to_nat k :: l0) ++ x)) st h o asn.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? H Hsh Hvar Hknonneg Hheap Hkm.
  decomp_well_formed_reindexer.
  propositional.
  - assert (0 < Z.of_nat m - k \/ Z.of_nat m - k <= 0)%Z
      by lia.
    invert H.
    + erewrite result_has_shape_result_shape_Z; eauto.
      rewrite filter_pad_l_mesh_grid; eauto.
      eapply partial_injective_truncl.
      eauto.
      eassumption.
      auto. eauto.
      auto. auto. auto. auto. lia.
    + erewrite result_has_shape_result_shape_Z; eauto.
      rewrite filter_pad_l_mesh_grid; eauto.
      replace (m - Z.to_nat k) with 0 by lia.
      simpl filter.
      unfold partial_injective.
      propositional. invert H1.
  - eapply HeqZlist.
    cases l1; cases l2. eauto.
    invert H. invert H0.
    invert H. invert H0.
    erewrite <- eq_Z_tuple_index_list_cons in H. propositional.
    cases p. cases p0. 
    erewrite <- eq_Z_tuple_index_list_cons. propositional.
    unfold eq_Z_tup. simpl. propositional.
    eapply eq_zexpr_sub. apply H0. apply eq_zexpr_id. auto.
    invert H0. simpl in *. lia.
  - rewrite Hmap; auto.
    cases l. auto. cases p. reflexivity.
  - rewrite Hvarsarg.
    cases l. auto. cases p. simpl.
    repeat rewrite constant_app_no_dups.
    sets.
  - eapply nondestructivity_trunc_l; eauto.
Qed.

Lemma well_formed_reindexer_padl :
  forall reindexer m l0 k v x0 st h o asn a,
    partial_injective
      (partial_interpret_reindexer
         reindexer
         (result_shape_Z
            (V (repeat
                  (gen_pad l0)
                  (Z.to_nat k)
                  ++ x0))) v)
      (filter
         (fun x =>
            negb
              (is_None
                 (result_lookup_Z_option
                    x
                    (V (repeat
                          (gen_pad l0)
                          (Z.to_nat k)
                          ++ x0)))))
         (mesh_grid
            (result_shape_Z
               (V (repeat
                     (gen_pad l0)
                     (Z.to_nat k)                     
                          ++ x0))))) ->
    result_has_shape
      (V x0) (m :: l0) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    (0 < m) ->
    (0 <= k)%Z ->
    (forall l1 l2 : list (Zexpr * Z),
        eq_Z_tuple_index_list l1 l2 ->
        eq_Z_tuple_index_list (reindexer l1) (reindexer l2)) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall (var : var) (k0 : Z) (l : list (Zexpr * Z)),
        ~ var \in vars_of_reindexer (reindexer []) ->
                  map (subst_var_in_Z_tup var k0) (reindexer l) =
                    reindexer (map (subst_var_in_Z_tup var k0) l)) ->
    (forall l : list (Zexpr * Z),
        vars_of_reindexer (reindexer l) =
          vars_of_reindexer (reindexer []) \cup vars_of_reindexer l) ->
    nondestructivity st h o reindexer
   (V
      (repeat (gen_pad l0)
         (Z.to_nat k) ++ x0)) v asn ->
    h $? o = Some a ->
    well_formed_reindexer
      (fun l : list (Zexpr * Z) =>
         reindexer
           match l with
           | [] => l
           | (v0, d) :: xs => ((v0 + | k |)%z, (d + k)%Z) :: xs
           end) v
      (V x0) st h o asn.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? H Hsh Hvar Hmnonneg Hknonneg HeqZlist
    Hvarsub Hmap Hvarsarg Hnondstr Hheap.
  unfold well_formed_reindexer. propositional.
  - erewrite result_has_shape_result_shape_Z by eauto.
    cases m.
    simpl. unfold partial_injective. propositional. invert H1.
    eapply partial_injective_padl; eauto. 
  - eapply HeqZlist. pose proof H0.
    cases l1; cases l2.
    eauto.
    invert H1. invert H3.
    invert H1. invert H3.
    cases p. cases p0.
    erewrite <- eq_Z_tuple_index_list_cons_tup.
    erewrite <- eq_Z_tuple_index_list_cons_tup in H1.
    propositional.
    eapply eq_zexpr_add; eauto.
    lia.
  - rewrite Hmap by auto.
    cases l. reflexivity. cases p. reflexivity.
  - rewrite Hvarsarg. cases l. reflexivity.
    cases p. simpl.
    repeat rewrite constant_app_no_dups. sets.
  - eapply nondestructivity_pad_l; eauto.
Qed.

Lemma well_formed_reindexer_truncr :
  forall reindexer x m l0 k v st h o a arr,
    well_formed_reindexer
      reindexer v
      (V
         (rev
            (truncl_list
               k
               (rev
                  (x ++
                     gen_pad_list
                     (k :: l0)))))) st h o a ->
    result_has_shape
      (V
         (x ++
            gen_pad_list
            (k :: l0)))
      (m :: l0) ->    
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    h $? o = Some arr ->
    (k < m) ->
    well_formed_reindexer
      (fun l : list (Zexpr * Z) =>
         reindexer match l with
                   | [] => l
                   | (v0, d) :: xs => (v0, (d - Z.of_nat k)%Z) :: xs
                   end) v
      (V
         (x ++
            gen_pad_list
            (k :: l0))) st h o a.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? Hrdx Hsh Hvar Hheap Hkm.
  decomp_well_formed_reindexer.
  propositional.
  - assert (0 < m - k \/ m - k <= 0) by lia.
    invert H.
    2: { eapply result_has_shape_app_r in Hsh.
         2: simpl; rewrite repeat_length; eauto.
         cases x.
         2: { simpl in *. invert Hsh. simpl in *. lia. }
         invert Hsh.
         rewrite app_nil_l.
         rewrite filter_gen_pad_empty.
         unfold partial_injective. propositional. invert H2. }
    erewrite result_has_shape_result_shape_Z by eauto.
    rewrite filter_pad_r_mesh_grid.
    eapply partial_injective_truncr.
    rewrite rev_app_distr in Hinj.
    simpl gen_pad_list in Hinj.
    rewrite rev_repeat in Hinj.
    pose proof truncl_list_gen_pad_id.
    simpl in H. rewrite H in Hinj. clear H.
    rewrite rev_involutive in Hinj.
    erewrite result_has_shape_result_shape_Z in Hinj.
    2: { eapply result_has_shape_app_r; eauto. }
    simpl gen_pad_list in Hinj. rewrite repeat_length in *.
    apply Hinj.
    eauto. auto. auto. auto. auto. auto. auto.
    simpl.
    replace m with
      (k +
         (m - k)) by lia.
    eapply result_has_shape_concat.
    eapply result_has_shape_repeat_gen_pad.
    eapply result_has_shape_app_r; eauto.
    simpl. rewrite repeat_length. auto.
    lia.
  - cases l1; cases l2; pose proof H; invert H; simpl; auto.
    invert H1.
    invert H1.
    invert H1. eapply HeqZlist.
    cases p. cases p0.
    erewrite <- eq_Z_tuple_index_list_cons in *.
    propositional.
    unfold eq_Z_tup in *. simpl in H. propositional.
    simpl. subst. reflexivity.
  - rewrite Hmap by auto. cases l. reflexivity.
    cases p. simpl.
    unfold subst_var_in_Z_tup. reflexivity.
  - rewrite Hvarsarg. cases l. reflexivity.
    cases p. reflexivity.
  - eapply nondestructivity_trunc_r; eauto.
    rewrite rev_app_distr in Hinj.
    simpl in *. rewrite rev_repeat in Hinj.
    rewrite truncl_list_skipn in Hinj.
    replace (repeat (gen_pad l0) k) with (gen_pad_list (k :: l0))
    in Hinj.
    2: { simpl. eauto. }
    rewrite <- truncl_list_skipn in Hinj.
    erewrite truncl_list_gen_pad_id in Hinj.
    rewrite rev_involutive in Hinj.
    simpl in *. 
    rewrite truncl_list_skipn.
    replace (repeat (gen_pad l0) k) with (gen_pad_list (k :: l0)).
    2: { simpl. eauto. }
    rewrite <- truncl_list_skipn.
    erewrite truncl_list_gen_pad_id.
    rewrite rev_involutive.
    eauto.
    rewrite rev_app_distr in Hnondstr.
    simpl in *. rewrite rev_repeat in Hnondstr.
    rewrite truncl_list_skipn in Hnondstr.
    replace (repeat (gen_pad l0) k) with (gen_pad_list (k :: l0))
    in Hnondstr.
    2: { simpl. eauto. }
    rewrite <- truncl_list_skipn in Hnondstr.
    erewrite truncl_list_gen_pad_id in Hnondstr.
    rewrite rev_involutive in Hnondstr.
    eauto.
Qed.

Lemma well_formed_reindexer_eval_cons0 :
  forall r1 r2 v reindexer st h o a,
    well_formed_reindexer reindexer v (V (r1 :: r2)) st h o a ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    result_has_shape (V (r1 :: r2)) (result_shape_nat (V (r1 :: r2))) ->
    well_formed_reindexer
      (fun l => reindexer
                  (((|0|)%z,Z.of_nat (Datatypes.S (length r2))%Z)::l))
      v r1 st h o a.
Proof.
  intros. decomp_well_formed_reindexer. propositional.
  - erewrite result_has_shape_result_shape_Z in Hinj by eauto.
    erewrite result_has_shape_result_shape_Z.
    2: { invert H1. eauto. }    
    unfold partial_injective in *.
    propositional.
    repeat decomp_index.
    rewrite eq_partial_interpret_reindexer_eval_cons0 in H3; eauto.
    rewrite eq_partial_interpret_reindexer_eval_cons0 in H3; eauto.
    rewrite eq_partial_interpret_reindexer_eval_cons0; eauto.
    apply Hinj in H3.
    propositional. invert H. propositional.
    eapply filter_In. propositional. repeat decomp_goal_index.
    propositional. lia. lia.
    eapply filter_In. propositional. repeat decomp_goal_index.
    propositional. lia. lia.
  - eapply HeqZlist.
    erewrite <- eq_Z_tuple_index_list_cons.
    propositional.
    unfold eq_Z_tup. simpl. propositional. auto.
  - rewrite Hvarsarg.
    simpl. sets.
  - rewrite Hmap.
    simpl.
    unfold subst_var_in_Z_tup. simpl. reflexivity.
    intros. apply H.
    simpl. rewrite Hvarsarg. simpl. sets.
  - rewrite Hvarsarg. simpl.
    symmetry. rewrite Hvarsarg. simpl. sets.
  - 
Admitted. 

Lemma well_formed_reindexer_shift_top_dim_reindexer :
  forall x1 xs1 reindexer v st h o a arr i lo hi,
    well_formed_reindexer reindexer
                                  v (V (x1 :: xs1)) st h o a ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    result_has_shape (V (x1 :: xs1)) (result_shape_nat (V (x1 :: xs1))) ->
    h $? o = Some arr ->
    ~ i \in dom v ->
    ~ contains_substring "?" i ->
    (lo < hi)%Z ->
    well_formed_allocation reindexer (V (x1 :: xs1)) st h o v ->
    Datatypes.length xs1 = Z.to_nat (hi - (lo + 1)) ->
    well_formed_reindexer (shift_top_dim_reindexer reindexer) 
                          v (V xs1) st (h $+ (o,
          array_add arr
            (tensor_to_array_delta
               (partial_interpret_reindexer
                  (fun l5 : list (Zexpr * Z) =>
                   reindexer (((! i ! - | lo |)%z, (hi - lo)%Z) :: l5))
                  (result_shape_Z x1) (v $+ (i, lo))) x1))) o a.
Proof. 
  intros. decomp_well_formed_reindexer.
  unfold well_formed_reindexer. 
  propositional.
  - cases xs1. simpl. unfold partial_injective.
    propositional. invert H.
    eapply partial_injective_shift_top_dim_reindexer; eauto.
    inversion 1.
  - cases l1; cases l2; simpl in *; pose proof H;
      try invert H; simpl in *.
    eapply HeqZlist. eauto.
    invert0 H9. invert0 H9. invert H1.
    cases p. cases p0.
    eapply HeqZlist. simpl in *. 
    erewrite <- eq_Z_tuple_index_list_cons in *. invs.
    propositional.
    unfold eq_Z_tup in *. simpl in *. invs.
    propositional.
    eapply eq_zexpr_add; auto.
  - unfold shift_top_dim_reindexer. cases l. simpl.
    rewrite Hmap. reflexivity. auto.
    cases p. simpl. rewrite Hmap by auto.
    rewrite map_cons. reflexivity.
  - unfold shift_top_dim_reindexer.
    cases l. simpl. sets.
    cases p. simpl. rewrite Hvarsarg. simpl.
    repeat rewrite app_no_dups_empty_r. reflexivity.
  - eapply nondestructivity_array_add_shift_top_dim_reindexer; eauto.
Qed.

Lemma tensor_to_array_delta_add_result : forall r1 r2 r3,
    add_result r1 r2 r3 ->
    forall v reindexer,
      result_has_shape r1 (result_shape_nat r1) ->
      result_has_shape r2 (result_shape_nat r1) ->
      result_has_shape r3 (result_shape_nat r1) ->
      partial_injective
           (partial_interpret_reindexer reindexer (result_shape_Z r3) v)
           (filter (fun x : list Z => negb (is_None (result_lookup_Z_option x r3)))
              (mesh_grid (result_shape_Z r3))) ->
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
      array_add
        (tensor_to_array_delta
           (partial_interpret_reindexer reindexer (result_shape_Z r1) v) r1)
        (tensor_to_array_delta
           (partial_interpret_reindexer reindexer (result_shape_Z r2) v) r2) =
        tensor_to_array_delta
          (partial_interpret_reindexer reindexer (result_shape_Z r3) v) r3.
Proof.
  intros.
  pose proof (add_result_mut
  (fun (r1 r2 r3 : result) (HH : add_result r1 r2 r3) =>
     forall v reindexer,
       result_has_shape r1 (result_shape_nat r1) ->
       result_has_shape r2 (result_shape_nat r1) ->
       result_has_shape r3 (result_shape_nat r1) ->       
       partial_injective
           (partial_interpret_reindexer reindexer (result_shape_Z r3) v)
           (filter (fun x : list Z => negb (is_None (result_lookup_Z_option x r3)))
              (mesh_grid (result_shape_Z r3))) ->
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
     array_add
       (tensor_to_array_delta
          (partial_interpret_reindexer reindexer (result_shape_Z r1) v) r1)
       (tensor_to_array_delta
          (partial_interpret_reindexer reindexer (result_shape_Z r2) v) r2) =
       tensor_to_array_delta
         (partial_interpret_reindexer reindexer (result_shape_Z r3) v) r3)
  (fun (r1 r2 r3 : list result) (HH : add_list r1 r2 r3) =>
     forall v reindexer,
       result_has_shape (V r1) (result_shape_nat (V r1)) ->
       result_has_shape (V r2) (result_shape_nat (V r1)) ->
       result_has_shape (V r3) (result_shape_nat (V r1)) ->

       
partial_injective (partial_interpret_reindexer reindexer (result_shape_Z (V r3)) v)
    (filter (fun x : list Z => negb (is_None (result_lookup_Z_option x (V r3))))
       (mesh_grid (result_shape_Z (V r3)))) ->
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
     array_add
       (tensor_to_array_delta
          (partial_interpret_reindexer
             reindexer (result_shape_Z (V r1)) v) (V r1))
       (tensor_to_array_delta
          (partial_interpret_reindexer reindexer
                                       (result_shape_Z (V r2)) v) (V r2)) =
       tensor_to_array_delta
         (partial_interpret_reindexer reindexer
                                      (result_shape_Z (V r3)) v) (V r3))).
  eapply H9; clear H9.
  - intros.
    unfold tensor_to_array_delta.
    simpl in *. unfold tensor_to_array_delta_by_indices.
    simpl.
    cases s1; cases s2; simpl in *; repeat rewrite array_add_empty_l.
    + unfold result_shape_Z in *. simpl in *.
      invert a. simpl.
      unfold shape_to_index, shape_to_vars. simpl.
      repeat rewrite array_add_empty_l.      
      unfold array_add.
      rewrite merge_add2. rewrite lookup_add_eq by auto.
      rewrite merge_empty2.
      rewrite add_array_overwrite. reflexivity.
      intros; cases x; auto.
      intros; cases x; discriminate.
      rewrite dom_empty. sets.
    + unfold result_shape_Z in *. simpl in *.
      invert a. simpl.
      unfold shape_to_index, shape_to_vars. simpl.
      repeat rewrite array_add_empty_l.      
      unfold array_add.
      rewrite merge_add1. rewrite lookup_empty.
      rewrite merge_empty2.
      reflexivity.
      intros; cases x; auto.
      intros. cases y; discriminate.
      rewrite dom_empty. sets.
    + unfold result_shape_Z in *. simpl in *.
      invert a. simpl.
      unfold shape_to_index, shape_to_vars. simpl.
      repeat rewrite array_add_empty_l.      
      unfold array_add.
      reflexivity.
    + invert a.
      unfold result_shape_Z in *. simpl in *.
      reflexivity.
      (*
  - intros. unfold result_shape_Z. simpl.
    unfold partial_result_to_array_delta.
    simpl in *. unfold partial_result_to_array_delta_by_indices.
    simpl. rewrite array_add_empty_l.
    rewrite array_add_empty_r.
    reflexivity.
  - intros. unfold result_shape_Z. simpl.
    unfold partial_result_to_array_delta.
    simpl in *. unfold partial_result_to_array_delta_by_indices.
    simpl. rewrite array_add_empty_l.
    unfold shape_to_index,shape_to_vars. simpl.
    rewrite array_add_empty_l. reflexivity. *)
  - intros. eapply H9; eauto.
  - intros. simpl.
    repeat erewrite tensor_to_array_delta_cons_generic_indexer.
    rewrite array_add_assoc.
    rewrite (array_add_comm (array_add
                               (tensor_to_array_delta _ _)
                               (tensor_to_array_delta _ _)) _).
    rewrite array_add_assoc.
    rewrite <- array_add_assoc.
    f_equal.
    + rewrite array_add_comm.
      repeat rewrite tensor_to_array_delta_cons0; auto.
      simpl length.      
      assert (length xs2 = length xs1).
      { invert H12. lia. }
      assert (length r4 = length xs1).
      { invert H13. lia. } 
      rewrite H20, H21.
      eapply H9; auto.
      * invert H11. auto.
      * invert H12. auto.
      * invert H13. auto.
      * rewrite <- H21.
        eapply partial_injective_eval_cons0; eauto.
        eapply result_has_shape_self; eauto.
      * intros. eapply H15.
        erewrite <- eq_Z_tuple_index_list_cons_tup.
        split. eauto. split; eauto.
      * erewrite H18. simpl. sets.
      * intros. rewrite H18 in H22. rewrite H17.
        simpl. unfold subst_var_in_Z_tup at 1. simpl. eauto. sets.
      * intros. rewrite H18. symmetry. rewrite H18. simpl. sets.
      * eapply result_has_shape_self. eauto.
      * eapply partial_injective_add_result_r; try apply Hinj.
        4: econstructor; econstructor; eauto.
        eauto. eauto. eauto. eauto.
      * eapply result_has_shape_self. eauto.
      * propositional.
        eapply partial_injective_add_result_l; try apply Hinj.
        4: econstructor; econstructor; eauto.
        eauto. eauto. eauto. eauto.
    + repeat rewrite tensor_to_array_delta_shift_match; eauto.
      2: { eapply result_has_shape_self; eauto. }
      3: { eapply result_has_shape_self; eauto. }
      eapply H10.
      * eapply result_has_shape_self_tail. eassumption.
      * eapply result_has_shape_tail_transitivity; eauto.
      * eapply result_has_shape_tail_transitivity; eauto.
      * destruct r4. simpl. unfold result_shape_Z. simpl.
        unfold partial_injective. intros. inversion H20.
        eapply partial_injective_shift_top_dim_reindexer; eauto.
        eapply result_has_shape_self; eauto. inversion 1.
      * intros. unfold shift_top_dim_reindexer.
        destruct l1; destruct l2.
        eapply H15; eauto.
        inversion H20. simpl in *. invert0 H21. invert H20. invert0 H21.
        invert H20. invert H21.
        destruct p. destruct p0. simpl in *.
        apply H15.
        split. simpl. f_equal; auto. lia.
        invert H22. simpl. constructor; auto.
        eapply eq_zexpr_add. propositional. eauto.
      * unfold shift_top_dim_reindexer. sets.
      * intros. unfold shift_top_dim_reindexer.
        destruct l. simpl. sets.
        destruct p. simpl. rewrite H17. simpl. eauto. sets.
      * intros. unfold shift_top_dim_reindexer. destruct l.
        sets. destruct p. simpl. rewrite H18. symmetry. rewrite H18.
        simpl. rewrite app_no_dups_empty_r. reflexivity.
      * eauto.
      * propositional.
        eapply partial_injective_add_result_r; try apply Hinj.
        4: econstructor; econstructor; eauto.
        eauto. eauto. eauto. eauto.
      * propositional.
        eapply partial_injective_add_result_l; try apply Hinj.
        4: econstructor; econstructor; eauto.
        eauto. eauto. eauto. eauto.
    + eassumption. 
    + apply H14. 
    + eassumption.
    + eapply partial_injective_add_result_r; try apply H14.
      4: { econstructor; econstructor; eauto. }
      eauto. eauto. eauto. 
    + eassumption.
    + eapply partial_injective_add_result_l; try apply H14.
      4: { econstructor; econstructor; eauto. }
      eauto. eauto. eauto.
  - intros. unfold result_shape_Z in *. simpl in *.
    unfold partial_interpret_reindexer. unfold shape_to_vars. simpl.
    unfold shape_to_index. simpl.
    unfold tensor_to_array_delta. simpl.
    unfold tensor_to_array_delta_by_indices. simpl.
    rewrite array_add_empty_l. auto.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
Qed.

Lemma well_formed_reindexer_eval0 : 
  forall x1 xs1 reindexer v i lo hi st h o a arr,
    well_formed_reindexer reindexer v
                                  (V (x1 :: xs1)) st h o a ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    result_has_shape (V (x1 :: xs1)) (result_shape_nat (V (x1 :: xs1))) ->
    ~ i \in dom v ->
    ~ In i (shape_to_vars (result_shape_Z x1)) ->
    (hi - lo)%Z = Z.of_nat (Datatypes.length (x1 :: xs1)) ->
    h $? o = Some arr ->
    (lo < hi)%Z ->
    ~ contains_substring "?" i ->
    well_formed_reindexer
      (fun l0 : list (Zexpr * Z) =>
         reindexer (((! i ! - | lo |)%z,
                      (hi - lo)%Z) :: l0))
      (v $+ (i, lo)) x1 st h o a.
Proof.
  intros. decomp_well_formed_reindexer. propositional.
  - eapply partial_injective_cons_reindexer; eauto.
  - eapply HeqZlist. 
    erewrite <- eq_Z_tuple_index_list_cons in *. propositional.
    unfold eq_Z_tup. simpl. propositional.
    eauto.
  - rewrite dom_add. rewrite Hvarsarg.
    simpl. rewrite cup_empty_r.
    repeat rewrite constant_app_no_dups.
    rewrite Hvarsarg. sets.
  - rewrite Hmap. simpl.
    unfold subst_var_in_Z_tup at 1. simpl.
    rewrite Hvarsarg in H. simpl in H.
    repeat rewrite constant_app_no_dups in H.
    rewrite cup_empty_r in H.
    cases (i ==v var). sets.
    reflexivity.
    rewrite Hvarsarg in H. simpl in *. sets.
  - rewrite Hvarsarg.
    symmetry.
    rewrite Hvarsarg.
    symmetry.
    simpl. repeat rewrite cup_empty_r. sets.
  - eapply nondestructivity_cons_0; eauto.
    simpl length in *. lia.
Qed.

Lemma well_formed_reindexer_add_valuation :
  forall reindexer sh v i x st h o a,
    well_formed_reindexer reindexer v sh st h o a ->
    ~ i \in dom v ->
    ~ contains_substring "?" i ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    result_has_shape sh (result_shape_nat sh) ->
    well_formed_reindexer reindexer (v $+ (i, x)) sh st h o a.
Proof.
  unfold well_formed_reindexer. propositional.
  - unfold partial_injective in *. propositional.
    unfold partial_interpret_reindexer in *.
    rewrite @partially_eval_Z_tup_add_partial in * by auto.
    replace (fun e : Zexpr * Z =>
               subst_var_in_Z_tup i x (partially_eval_Z_tup v e)) with
      (fun e : Zexpr * Z =>
         partially_eval_Z_tup v (subst_var_in_Z_tup i x e)) in *.
    2: { eapply functional_extensionality. intros.
         rewrite subst_var_in_Z_tup_partially_eval_Z_tup_comm. auto.
         auto. }
    rewrite <- map_map with (f:=subst_var_in_Z_tup i x) in *.
    rewrite H6 in *; eauto with reindexers.
    2: { intros. eapply H0. eapply H5. sets. }
    2: { intros. eapply H0. eapply H5. sets. }
    rewrite map_subst_var_in_Zexpr_shape_to_index_id in *.
    2: { unfold not. intros. eapply shape_to_vars_contains_substring in H12.
         propositional. }
    2: { unfold not. intros. eapply shape_to_vars_contains_substring in H12.
         propositional. }
    eauto.
  - rewrite dom_add.
    sets.
  - unfold nondestructivity in *. invert H9. split; intros.
    + eapply H8; eauto.
      erewrite tensor_to_array_delta_add_valuation in H13; eauto.
      eapply partial_injective_add_valuation; eauto.
    + eapply H10; eauto.
Qed.
(*
Lemma well_formed_reindexer_id : forall v r st h o a,
    (forall var : var, contains_substring "?" var ->
                       var \in dom v -> False) ->    
    well_formed_reindexer (fun l : list (Zexpr * Zexpr) => l) v 
    (S r) (st $+ (o, 0%R)) h o a.

well_formed_reindexer (fun l : list (Zexpr * Zexpr) => l) v 
    (V l1) st'0 (alloc_array_in_heap [Z.to_nat nz] h x) x Assign
Proof.  
  unfold well_formed_reindexer. propositional.
  - eapply partial_injective_id_reindexer. auto.
  - sets.
  - sets.
  - unfold nondestructivity. split; intros.
    + admit.
    + 
Qed.
*)
Lemma well_formed_reindexer_transpose :
  forall l n0 m0 l0 v reindexer st h o a arr,
  result_has_shape (V l) (n0 :: m0 :: l0) ->
  well_formed_reindexer
    reindexer v (transpose_result l (m0 :: n0 :: l0))
  st h o a ->
  (forall var : var, contains_substring "?" var -> var \in dom v -> False) ->
  h $? o = Some arr ->
  well_formed_reindexer
    (fun l1 : list (Zexpr * Z) =>
     reindexer
       match l1 with
       | [] => l1
       | [(v0, d)] => l1
       | (v0, d) :: (vi, di) :: xs => (vi, di) :: (v0, d) :: xs
       end) v (V l) st h o a.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? Hsh Hrdx Henv Harr.
  decomp_well_formed_reindexer. propositional.
  - eapply partial_injective_transpose; eauto.
  - eapply HeqZlist.
    cases l1; cases l2.
    eapply eq_Z_tuple_index_list_id.
    invert H. invert0 H0.
    invert H. invert0 H0.
    cases p. cases p0.
    erewrite <- eq_Z_tuple_index_list_cons in H. invs.
    cases l1; cases l2.
    simpl.
    erewrite <- eq_Z_tuple_index_list_cons.
    propositional.
    invert H1. invert0 H.
    invert H1. invert0 H.
    cases p. cases p0.
    erewrite <- eq_Z_tuple_index_list_cons in H1. invs.
    erewrite <- eq_Z_tuple_index_list_cons.
    propositional.
    erewrite <- eq_Z_tuple_index_list_cons.
    propositional.
  - rewrite Hmap by eauto.
    cases l1. reflexivity.
    cases p. simpl.
    cases l1. reflexivity.
    cases p. simpl.
    f_equal.
  - rewrite Hvarsarg.
    cases l1. auto.
    cases p. cases l1. auto.
    cases p. simpl.
    sets.
  - eapply nondestructivity_transpose; eauto.    
Qed.

Lemma well_formed_reindexer_concat_l :
  forall reindexer l1 l2 v st h o a arr dim1 dim2 rest1,
    well_formed_reindexer
      reindexer v (V (l1 ++ l2)) st h o a ->
    result_has_shape (V l2) (dim2 :: rest1) ->
    result_has_shape (V l1) (dim1 :: rest1) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    h $? o = Some arr ->
    well_formed_reindexer
      (fun l3 : list (Zexpr * Z) =>
         reindexer
         match l3 with
         | [] => l3
         | (v0, d) :: xs => ((v0, (d + Z.of_nat dim2)%Z) :: xs)
         end) v (V l1) st h o a.
Proof.
  intros.
  decomp_well_formed_reindexer.
  propositional.
  - erewrite result_has_shape_result_shape_Z by eauto.
    eapply partial_injective_concat_l; eauto.
  - cases l0; cases l3.
    eapply HeqZlist. auto.
    invert H. invert0 H4.
    invert H. invert0 H4.
    cases p. cases p0.
    erewrite <- eq_Z_tuple_index_list_cons_tup in H.
    eapply HeqZlist.
    erewrite <- eq_Z_tuple_index_list_cons_tup.
    propositional. lia.
  - cases l.
    simpl. rewrite Hmap by auto. reflexivity.
    cases p.
    simpl. rewrite Hmap by auto.
    reflexivity.
  - cases l.
    rewrite Hvarsarg. sets.
    cases p.
    rewrite Hvarsarg. reflexivity.
  - eapply nondestructivity_concat_l; eauto.    
Qed.

Lemma well_formed_reindexer_concat_r :
  forall reindexer l1 l2 v n m l0 st h o a arr,
    well_formed_reindexer reindexer v (V (l1 ++ l2)) st h o a ->
    result_has_shape (V l1) (Z.to_nat n :: l0) ->
    result_has_shape (V l2) (m :: l0) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    (0 <= n)%Z ->
    h $? o = Some arr ->
    well_formed_reindexer
      (fun l3 : list (Zexpr * Z) =>
         reindexer
         match l3 with
         | [] => l3
         | (v0, d) :: xs => (((v0 + | n |)%z, (d + n)%Z) :: xs)
         end) v (V l2) st (h $+ (o,
     array_add arr
       (tensor_to_array_delta
          (partial_interpret_reindexer
             (fun l6 : list (Zexpr * Z) =>
              reindexer
                match l6 with
                | [] => l6
                | (v0, d) :: xs => (v0, (d + Z.of_nat m)%Z) :: xs
                end) (result_shape_Z (V l1)) v) (V l1)))) o a.
Proof.
  intros.
  decomp_well_formed_reindexer.
  propositional.
  - erewrite result_has_shape_result_shape_Z by eauto.    
    eapply partial_injective_concat_r; eauto.
  - cases l3; cases l4.
    eapply HeqZlist. auto.
    invert H. invert0 H6.
    invert H. invert0 H6.
    cases p. cases p0.
    erewrite <- eq_Z_tuple_index_list_cons_tup in H.
    eapply HeqZlist.
    erewrite <- eq_Z_tuple_index_list_cons_tup.
    propositional. eapply eq_zexpr_add; auto.
    lia.
  - cases l.
    simpl. rewrite Hmap by auto. reflexivity.
    cases p.
    simpl. rewrite Hmap by auto. reflexivity.
  - cases l.
    rewrite Hvarsarg. sets.
    cases p.
    rewrite Hvarsarg. f_equal.
    simpl.
    repeat rewrite app_no_dups_empty_r. 
    reflexivity.
  - eapply nondestructivity_concat_r__; eauto.
Qed.

Lemma well_formed_reindexer_flatten :
  forall v l n m l0 reindexer st h o a arr,
    result_has_shape (V l) (n :: m :: l0) ->
    well_formed_reindexer reindexer v (V (flatten_result l)) st h o a ->
    (forall var : var, contains_substring "?" var -> var \in dom v -> False)->
    h $? o = Some arr ->
    well_formed_reindexer
      (fun l2 : list (Zexpr * Z) =>
         reindexer
           match l2 with
           | [] => l2
           | [(v0, d)] => l2
           | (v0, d) :: (vi, di) :: xs =>
               ((v0 * | di | + vi)%z, (d * di)%Z) :: xs
           end) v (V l) st h o a.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? Hsh Hrdx Henv Hheap.
  decomp_well_formed_reindexer. propositional.
  - erewrite result_has_shape_result_shape_Z by eauto.
    eapply partial_injective_flatten; eauto.
    erewrite result_has_shape_result_shape_Z in Hinj.
    2: { eapply result_has_shape_flatten; eauto. }
    eauto.
  - eapply HeqZlist.
    cases l1; cases l2.
    eapply eq_Z_tuple_index_list_id.
    invert H. invert0 H0.
    invert H. invert0 H0.
    erewrite <- eq_Z_tuple_index_list_cons in H. propositional.
    cases p. cases p0.
    cases l1; cases l2.    
    erewrite <- eq_Z_tuple_index_list_cons. propositional.
    invert H1. invert0 H.
    invert H1. invert0 H.
    cases p. cases p0.
    erewrite <- eq_Z_tuple_index_list_cons. propositional.
    unfold eq_Z_tup in *. propositional. simpl in *.
    erewrite <- eq_Z_tuple_index_list_cons_tup in H1. propositional.
    eapply eq_zexpr_add; auto.
    eapply eq_zexpr_mul; auto.
    subst. apply eq_zexpr_id. reflexivity.
    invert H1. simpl in *. invert H0. lia.
    apply eq_Z_tuple_index_list_cons in H1. destruct H1. assumption.
  - rewrite Hmap by eauto. cases l1.
    reflexivity.
    cases p. simpl. cases l1. reflexivity.
    cases p. simpl. reflexivity.
  - rewrite Hvarsarg.
    cases l1. auto.
    cases p. cases l1. auto.
    cases p. simpl. repeat rewrite constant_app_no_dups. sets.
  - eapply nondestructivity_flatten; eauto.
Qed.    

Lemma well_formed_reindexer_padr :
  forall l m l0 v reindexer k st h o a arr,
    result_has_shape (V l) (m :: l0) ->
    well_formed_reindexer
      reindexer v
      (V
         (l ++ repeat (gen_pad l0) k)) st h o a ->
    (0 < m) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    h $? o = Some arr ->
    well_formed_reindexer
      (fun l1 : list (Zexpr * Z) =>
         reindexer match l1 with
                   | [] => l1
                   | (v0, d) :: xs => (v0, (d + Z.of_nat k)%Z) :: xs
                   end) v (V l) st h o a.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? Hsh Hrdx Hmpos Henv Hheap.
  decomp_well_formed_reindexer. propositional.
  - erewrite result_has_shape_result_shape_Z by eauto.
    pose proof Hinj.
    eapply partial_injective_concat_l; auto; try apply Henv.
    apply Hinj.
    eapply result_has_shape_repeat_gen_pad.
  - eapply HeqZlist.
    cases l1; cases l2.
    apply eq_Z_tuple_index_list_id.
    invert H. invert0 H0.
    invert H. invert0 H0.
    cases p. cases p0.
    erewrite <- eq_Z_tuple_index_list_cons_tup in H. propositional.
    erewrite <- eq_Z_tuple_index_list_cons_tup. propositional.
    subst. reflexivity.
  - rewrite Hmap by auto.
    cases l1. auto.
    cases p. reflexivity.
  - rewrite Hvarsarg. cases l1. auto.
    cases p. reflexivity.
  - eapply nondestructivity_pad_r; eauto.
Qed.  

Lemma well_formed_reindexer_gen_pad : forall reindexer sh v s st h o a,
    well_formed_reindexer reindexer v s st h o a ->
    well_formed_reindexer reindexer v (gen_pad sh) st h o a.
Proof.
  intros. decomp_well_formed_reindexer.
  propositional.
  rewrite filter_negb_is_None_result_lookup_Z_option_gen_pad.
  unfold partial_injective. intros. simpl in *. propositional.
  unfold nondestructivity in *. invert Hnondstr.
  split; eauto. intros.
  erewrite tensor_to_array_delta_gen_pad in H4.
  rewrite dom_empty in H4. sets.
Qed.

Lemma partial_interpret_reindexer_add_valuation :
  forall reindexer i v sh val s st h o a,
    (i \in dom v -> False) ->
    ~ contains_substring "?" i ->
  well_formed_reindexer reindexer v s st h o a ->
  partial_interpret_reindexer reindexer sh (v $+ (i, val)) =
  partial_interpret_reindexer reindexer sh v.
Proof.
  intros. decomp_well_formed_reindexer.
  unfold partial_interpret_reindexer.
  rewrite partially_eval_Z_tup_add_partial by auto.
  rewrite <- map_map.
  rewrite map_partially_eval_Z_tup_map_subst_var_in_Z_tup_comm by auto.
  rewrite Hmap.
  2: { unfold not. intros. eapply H. eapply Hvarsub. eauto. }
  erewrite map_subst_var_in_Zexpr_shape_to_index_id.
  2: { unfold shape_to_vars. unfold not. intros. apply H0.
       eapply shape_to_vars_contains_substring. apply H1. }
  reflexivity.
Qed.       

Lemma well_formed_reindexer_split :
  forall reindexer l0 k v l n st h o a arr,
    well_formed_reindexer reindexer v
      (V (split_result (Z.to_nat k) l)) st h o a ->
    result_has_shape (V l) (n :: l0) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    (0 < k)%Z ->
    h $? o = Some arr ->
    well_formed_reindexer
    (fun l2 : list (Zexpr * Z) =>
     reindexer
       match l2 with
       | [] => l2
       | (v0, d) :: xs => ((v0 / | k |)%z, (d // k)%Z) :: ((v0 % | k |)%z, k) :: xs
       end) v (V l) st h o a.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? H Hsh Hvar Hknonneg Hheap.
  decomp_well_formed_reindexer.
  propositional.
  - eapply partial_injective_split; eauto.
  - eapply HeqZlist.
    cases l1; cases l2. eauto.
    invert H. invert0 H0.
    invert H. invert0 H0.
    erewrite <- eq_Z_tuple_index_list_cons in H. propositional.
    cases p. cases p0. 
    erewrite <- eq_Z_tuple_index_list_cons. propositional.
    unfold eq_Z_tup. simpl. propositional.
    eapply eq_zexpr_div. apply H0. apply eq_zexpr_id. auto.
    invert H0. simpl in *. subst. reflexivity.
    erewrite <- eq_Z_tuple_index_list_cons. propositional.
    unfold eq_Z_tup. simpl. propositional.
    eapply eq_zexpr_mod. apply H0. apply eq_zexpr_id. auto.
  - rewrite Hmap; auto.
    cases l1. auto. cases p. simpl.
    unfold subst_var_in_Z_tup. simpl. reflexivity.
  - rewrite Hvarsarg.
    cases l1. auto. cases p. simpl.
    repeat rewrite constant_app_no_dups.
    sets.
  - eapply nondestructivity_split; eauto.
Qed.
