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
From Lower Require Import Zexpr Bexpr Array Range Sexpr Result ListMisc Meshgrid VarGeneration
     Injective Constant InterpretReindexer ResultToArrayDelta.

Open Scope string_scope.

Definition well_formed_allocation
           reindexer r (st : stack) (h : heap) p v :=
  match reindexer (shape_to_index (result_shape_Z r)
                                  (shape_to_vars (result_shape_Z r))) with
  | [] => exists a, st $? p = Some a
  | _ => exists a,
      h $? p = Some a /\
        constant
          (extract_Some
             (map
                (partial_interpret_reindexer reindexer (result_shape_Z r) v)
                (filter
                   (fun x =>
                      negb (is_None
                              (result_lookup_Z_option x r)))
                   (mesh_grid (result_shape_Z r))))) \subseteq dom a
  end.

Lemma constant_not_empty {X} : forall (l : list X),
    l <> [] ->
    constant l = constant [] ->
    False.
Proof.
  intros.
  erewrite <- sets_equal in H0.
  cases l. propositional.
  specialize (H0 x).
  propositional. simpl in H1. sets.
Qed.

Lemma reindexer_not_empty : forall reindexer sh,
    (forall l : list (Zexpr * Zexpr),
        vars_of_reindexer (reindexer l) =
          vars_of_reindexer (reindexer []) \cup vars_of_reindexer l)->
    sh <> [] ->
    reindexer (shape_to_index sh (shape_to_vars sh)) <> [].
Proof.
  intros. cases sh. propositional.
  clear H0.
  unfold not. intros.
  specialize (H (shape_to_index (z :: sh) (shape_to_vars (z :: sh)))).
  rewrite H0 in *.
  unfold shape_to_index, shape_to_vars in *.
  simpl in *.
  repeat rewrite cup_empty_r in H.
  symmetry in H.
  eapply cup_empty in H. invs.
  eapply cup_empty in H2. invs.
  eapply constant_not_empty in H. propositional. inversion 1.
Qed.
  
Lemma well_formed_allocation_result_V :
  forall l st h p v reindexer,
    well_formed_allocation reindexer
                                   (V l) st h p v ->
    (forall l : list (Zexpr * Zexpr),
        vars_of_reindexer (reindexer l) =
          vars_of_reindexer (reindexer []) \cup vars_of_reindexer l)->
    exists a : array,
      h $? p = Some a /\
        constant
          (extract_Some
             (map (partial_interpret_reindexer
                     reindexer (result_shape_Z (V l)) v)
                  (filter
                     (fun x => negb
                                 (is_None
                                    (result_lookup_Z_option x (V l))))
                     (mesh_grid (result_shape_Z (V l)))))) \subseteq dom a.
Proof.
  unfold well_formed_allocation. intros.
  unfold result_shape_Z in *. simpl in *.
  cases (reindexer
          (shape_to_index
             (map Z.of_nat
                  match l with
                  | [] => [0]
                  | x :: xs => Datatypes.S (length xs) :: result_shape_nat x
                end)
             (shape_to_vars
                (map Z.of_nat
                   match l with
                   | [] => [0]
                   | x :: xs =>
                       Datatypes.S (length xs) :: result_shape_nat x
                   end)))).
  - cases l.
    + eapply reindexer_not_empty in Heq; simpl; propositional; discriminate.
    + eapply reindexer_not_empty in Heq; simpl; propositional; discriminate.
  - cases l.
    + invs. eauto.
    + invs. eexists. split. eauto.
      eapply subseteq_transitivity.
      2: eassumption.
      eapply subseteq_In.
      propositional.
Qed.

Lemma well_formed_allocation_padl :
  forall reindexer st h p v k l0 l m,
    well_formed_allocation
      reindexer
      (V (repeat (gen_pad (map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)))
                 (Z.to_nat (eval_Zexpr_Z_total $0 k)) ++ l)) st h p v ->
    result_has_shape (V l)
                     (map Z.to_nat (map (eval_Zexpr_Z_total $0) (m :: l0))) ->
    (forall l0 : list (Zexpr * Zexpr),
        vars_of_reindexer (reindexer l0) =
          vars_of_reindexer (reindexer []) \cup vars_of_reindexer l0) ->
    (0 <= eval_Zexpr_Z_total $0 k)%Z ->
    (0 <= eval_Zexpr_Z_total $0 m)%Z ->
    (forall (var : var) (k0 : Z) (l2 : list (Zexpr * Zexpr)),
        ~ var \in vars_of_reindexer (reindexer []) ->
                  map (subst_var_in_Z_tup var k0) (reindexer l2) =
                    reindexer (map (subst_var_in_Z_tup var k0) l2)) ->
    (eq_zexpr k (| eval_Zexpr_Z_total $0 k |)%z) ->
    (eq_zexpr m (| eval_Zexpr_Z_total $0 m |)%z) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall l2 l3 : list (Zexpr * Zexpr),
        eq_Z_tuple_index_list l2 l3 ->
        eq_Z_tuple_index_list (reindexer l2) (reindexer l3)) ->
    well_formed_allocation
      (fun l : list (Zexpr * Zexpr) =>
         reindexer
           match l with
           | [] => l
           | (v0, d) :: xs => ((v0 + k)%z, (d + k)%z) :: xs
           end)      
         (V l) st h p v.
Proof.
  intros ? ? ? ? ? ? ? ? ? Halloc Hsh Hvarsub Hknonneg Hmnonneg Hmap Hkz Hm
         Henv Hvarsubdom HeqZlist.
  eapply well_formed_allocation_result_V in Halloc; eauto.
  invs. unfold well_formed_allocation.
  cases (shape_to_index
           (result_shape_Z (V l))
           (shape_to_vars (result_shape_Z (V l)))).
  { eapply shape_to_index_not_empty_Z in Heq. propositional. }
  cases (reindexer (let (v0, d) := p0 in ((v0 + k)%z, (d + k)%z) :: l1)).
  { eapply reindexer_not_empty_vars_in_index in Heq0.
    propositional. auto.    
    unfold result_shape_Z,shape_to_index,shape_to_vars in Heq. simpl in *.
    cases l.
    - simpl in *. invert Heq. simpl.
      repeat rewrite constant_app_no_dups.
      unfold not. intros.
      eapply cup_empty in H. invs.
      eapply cup_empty in H2. invs.
      eapply cup_empty in H. invs.
      eapply constant_not_empty in H2. propositional.
      inversion 1.
    - simpl in *. invert Heq. simpl.
      repeat rewrite constant_app_no_dups.
      unfold not. intros.
      eapply cup_empty in H. invs.
      eapply cup_empty in H2. invs.
      eapply cup_empty in H. invs.
      eapply constant_not_empty in H2. propositional.
      inversion 1. }
  erewrite result_has_shape_result_shape_Z by eauto.
  erewrite result_has_shape_result_shape_Z in H1.
  2: { eapply result_has_shape_concat.
       eapply result_has_shape_repeat_gen_pad.
       simpl in *. eauto. }
  rewrite <- Z2Nat.inj_add in H1 by lia.
  rewrite <- map_cons in H1.
  rewrite <- eval_Zexpr_Z_total_add_distr in H1; eauto.
  rewrite <- map_cons in H1.
  pose proof filter_pad_l_mesh_grid. simpl gen_pad_list in H.
  rewrite H in H1; eauto.
  clear H.
  2: { repeat rewrite map_cons.
       rewrite eval_Zexpr_Z_total_add_distr; eauto.
       rewrite Z2Nat.inj_add by lia.
       eapply result_has_shape_concat.
       eapply result_has_shape_repeat_gen_pad. eauto. }
  eexists. split. eauto.
  eapply subseteq_transitivity. 2: eassumption.
  eapply subseteq_In.
  propositional.
  - rewrite <- In_iff_in in *.
    erewrite <- in_extract_Some in *.
    erewrite in_map_iff in *. invs.
    repeat decomp_index.
    rewrite <- H.
    repeat rewrite map_cons.
    erewrite eq_partial_interpret_reindexer_padl.
    eexists ((z + eval_Zexpr_Z_total $0 k)%Z :: x1).
    split.
    f_equal. f_equal. f_equal. f_equal. rewrite <- Z2Nat.inj_add by lia.
    f_equal.
    eapply eval_Zexpr_Z_total_add_distr; eauto.
    eapply in_map_iff. eexists (z::x1).
    propositional.
    eapply filter_In. propositional.
    repeat decomp_goal_index.
    propositional.
    rewrite eval_Zexpr_Z_total_add_distr; eauto.
    lia.
    eauto.
    auto. auto. auto. auto. auto. lia. lia.
Qed.

Lemma well_formed_allocation_truncl :
  forall reindexer st h p v k l0 x m,
    well_formed_allocation reindexer (V x) st h p v ->
    (forall l0 : list (Zexpr * Zexpr),
        vars_of_reindexer (reindexer l0) =
          vars_of_reindexer (reindexer []) \cup vars_of_reindexer l0) ->
    result_has_shape
      (V
         (gen_pad_list
            (Z.to_nat (eval_Zexpr_Z_total $0 k)
                      :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)) ++ x))
      (Z.to_nat (eval_Zexpr_Z_total $0 m)
                :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)) ->    
    (0 <= eval_Zexpr_Z_total $0 k)%Z ->
    (forall (var : var) (k0 : Z) (l2 : list (Zexpr * Zexpr)),
        ~ var \in vars_of_reindexer (reindexer []) ->
                  map (subst_var_in_Z_tup var k0) (reindexer l2) =
                    reindexer (map (subst_var_in_Z_tup var k0) l2)) ->
    (eq_zexpr k (| eval_Zexpr_Z_total $0 k |)%z) ->
    (eq_zexpr m (| eval_Zexpr_Z_total $0 m |)%z) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall l2 l3 : list (Zexpr * Zexpr),
        eq_Z_tuple_index_list l2 l3 ->
        eq_Z_tuple_index_list (reindexer l2) (reindexer l3)) ->
    well_formed_allocation
      (fun l : list (Zexpr * Zexpr) =>
         reindexer
           match l with
           | [] => l
           | (v0, d) :: xs => ((v0 - k)%z, (d - k)%z) :: xs
           end)      
         (V
            (gen_pad_list
               (Z.to_nat (eval_Zexpr_Z_total $0 k)
                         :: map Z.to_nat
                         (map (eval_Zexpr_Z_total $0) l0)) ++ x)) st h p v.
Proof.
  intros ? ? ? ? ? ? ? ? ? Halloc Hvarsub Hsh Hknonneg Hmap Hkz Hm Henv
         Hvarsubdom HeqZlist.
  eapply well_formed_allocation_result_V in Halloc; eauto.
  invs. unfold well_formed_allocation.
  cases (shape_to_index
           (result_shape_Z
              (V
                 (gen_pad_list
                    (Z.to_nat
                       (eval_Zexpr_Z_total $0 k)
                       :: map Z.to_nat
                       (map (eval_Zexpr_Z_total $0) l0)) ++ x)))
           (shape_to_vars
              (result_shape_Z
                 (V
                    (gen_pad_list
                       (Z.to_nat (eval_Zexpr_Z_total $0 k)
                                 :: map Z.to_nat
                                 (map (eval_Zexpr_Z_total $0) l0)) ++ x))))).
  { eapply shape_to_index_not_empty_Z in Heq. propositional. }  
  cases (reindexer
      (let (v0, d) := p0 in ((v0 - k)%z, (d - k)%z) :: l)).
  { erewrite result_has_shape_result_shape_Z in Heq.
    2: eauto. 
    eapply reindexer_not_empty_vars_in_index in Heq0; auto. propositional.
    unfold result_shape_Z in Heq. simpl in Heq.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 m)).
    - invert Heq. simpl. unfold app_no_dups.
      repeat rewrite <- union_constant.
      repeat rewrite cup_empty_r.
      repeat rewrite cup_empty_l.
      unfold not. intros.
      eapply cup_empty in H. invs.
      eapply cup_empty in H2. invs.
      eapply constant_not_empty in H. propositional. inversion 1.
    - invert Heq. simpl.
      unfold app_no_dups.
      repeat rewrite <- union_constant.
      repeat rewrite cup_empty_r.
      repeat rewrite cup_empty_l.
      unfold not. intros.
      eapply cup_empty in H. invs.
      eapply cup_empty in H2. invs.
      eapply cup_empty in H. invs.
      eapply constant_not_empty in H2. propositional. inversion 1. }
  erewrite result_has_shape_result_shape_Z.
  2: eauto.
  rewrite <- map_cons.
  rewrite <- map_cons.
  rewrite filter_pad_l_mesh_grid; eauto.
  eexists. split. eassumption.
  eapply subseteq_transitivity. 2: eassumption.
  eapply subseteq_In. intros.
  rewrite <- In_iff_in in *.
  erewrite <- in_extract_Some in *.
  erewrite in_map_iff in *. invs.
  erewrite result_has_shape_result_shape_Z in * by eassumption.
  repeat decomp_index.
  rewrite <- H.
  erewrite result_has_shape_result_shape_Z.
  2: { eapply result_has_shape_app_l; eauto. }
  simpl gen_pad_list. rewrite repeat_length.       
  eapply in_map_iff in H3. invs.
  repeat decomp_index.
  exists (z::x3).
  split.
  rewrite map_cons.
  rewrite map_cons.
  erewrite eq_partial_interpret_reindexer_truncl.
  reflexivity.
  eauto.
  auto. auto. auto. auto. auto.
  lia. lia. lia.
  eapply filter_In. propositional.
  repeat decomp_goal_index. propositional.
Qed.

Lemma well_formed_allocation_truncr :
  forall reindexer x st h p v k l0 m,
    well_formed_allocation
      reindexer
      (V
         (rev
            (truncl_list
               (Z.to_nat (eval_Zexpr_Z_total $0 k))
               (rev
                  (x ++
                     gen_pad_list
                     (Z.to_nat (eval_Zexpr_Z_total $0 k)
                               :: map Z.to_nat
                               (map (eval_Zexpr_Z_total $0) l0)))))))
      st h p v ->
    (forall l0 : list (Zexpr * Zexpr),
        vars_of_reindexer (reindexer l0) =
          vars_of_reindexer (reindexer []) \cup vars_of_reindexer l0) ->
    result_has_shape
      (V
         (x ++
            gen_pad_list
            (Z.to_nat (eval_Zexpr_Z_total $0 k)
                      :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0))))
      (Z.to_nat (eval_Zexpr_Z_total $0 m)
                :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)) ->
    (0 <= eval_Zexpr_Z_total $0 k)%Z ->
    (forall (var : var) (k0 : Z) (l2 : list (Zexpr * Zexpr)),
        ~ var \in vars_of_reindexer (reindexer []) ->
                  map (subst_var_in_Z_tup var k0) (reindexer l2) =
                    reindexer (map (subst_var_in_Z_tup var k0) l2)) ->
    (eq_zexpr k (| eval_Zexpr_Z_total $0 k |)%z) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall l2 l3 : list (Zexpr * Zexpr),
        eq_Z_tuple_index_list l2 l3 ->
        eq_Z_tuple_index_list (reindexer l2) (reindexer l3)) ->
    well_formed_allocation
      (fun l : list (Zexpr * Zexpr) =>
         reindexer match l with
                   | [] => l
                   | (v0, d) :: xs => (v0, (d - k)%z) :: xs
                   end)
      (V
         (x ++
            gen_pad_list
            (Z.to_nat (eval_Zexpr_Z_total $0 k)
                      :: map Z.to_nat
                      (map (eval_Zexpr_Z_total $0) l0)))) st h p v.
Proof.
  intros ? ? ? ? ? ? ? ? ? Halloc Hvarsub Hsh Hknonneg Hmap Hkz Henv
         Hvarsubdom HeqZlist.      
  
  eapply well_formed_allocation_result_V in Halloc; eauto.
  invs. unfold well_formed_allocation.
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
  { eapply shape_to_index_not_empty_Z in Heq. propositional. }
  cases (reindexer (let (v0, d) := p0 in (v0, (d - k)%z) :: l)).
  { eapply reindexer_not_empty_vars_in_index in Heq0; auto. propositional.
    unfold result_shape_Z in Heq. simpl in Heq.
    cases ((x ++
                repeat (gen_pad (map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)))
                  (Z.to_nat (eval_Zexpr_Z_total $0 k)))%list).
    - invert Heq. simpl. unfold app_no_dups.
      repeat rewrite <- union_constant.
      repeat rewrite cup_empty_r.
      repeat rewrite cup_empty_l.
      unfold not. intros.
      eapply cup_empty in H. invs.
      eapply constant_not_empty in H2. propositional. inversion 1.
    - invert Heq. simpl.
      unfold app_no_dups.
      repeat rewrite <- union_constant.
      repeat rewrite cup_empty_r.
      repeat rewrite cup_empty_l.
      unfold not. intros.
      eapply cup_empty in H. invs.
      eapply cup_empty in H2. invs.
      eapply constant_not_empty in H. propositional. inversion 1. }
  assert (0 < eval_Zexpr_Z_total $0 m - eval_Zexpr_Z_total $0 k \/
            eval_Zexpr_Z_total $0 m - eval_Zexpr_Z_total $0 k <= 0)%Z
    as Hcase by lia.
  inversion Hcase as [ Hcase1 | Hcase2 ]; clear Hcase.
  2: { eapply result_has_shape_app_r in Hsh; eauto.
       simpl gen_pad_list in Hsh. rewrite repeat_length in Hsh.
       cases x; invert Hsh; try lia.
       rewrite app_nil_l.
       rewrite filter_gen_pad_empty. eexists. split. eassumption.
       simpl. sets. }
  eexists. split. eassumption.
  eapply subseteq_transitivity. 2: eassumption.
  rewrite rev_app_distr in *.
  simpl gen_pad_list in *. rewrite rev_repeat in *.
  pose proof truncl_list_gen_pad_id.
  simpl gen_pad_list in H. rewrite H in *. clear H.
  rewrite rev_involutive in *.
  eapply subseteq_In. intros.
  rewrite <- In_iff_in in *.
  erewrite <- in_extract_Some in *.
  erewrite in_map_iff in *. invs.
  erewrite result_has_shape_result_shape_Z in *; eauto.
  2: { eapply result_has_shape_app_r; eauto. }
  2: { eapply result_has_shape_app_r; eauto. }
  rewrite repeat_length in *.
  repeat decomp_index.
  repeat rewrite <- map_cons in H.
  erewrite eq_partial_interpret_reindexer_truncr in H; eauto; try lia.
  eexists. rewrite <- H.
  split. reflexivity.
  eapply filter_In. propositional.
  repeat decomp_goal_index. propositional.
  pose proof Hsh. eapply result_has_shape_app_r in H3.
  2: { rewrite repeat_length. reflexivity. }
  cases (result_lookup_Z_option
           (z :: x2)
           (V
              (x ++
                 repeat (gen_pad
                           (map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)))
                 (Z.to_nat (eval_Zexpr_Z_total $0 k)))));
    try (simpl in *; discriminate).
  eapply result_lookup_Z_option_Some_pad_r in Heq1; auto.
  erewrite result_has_shape_length in Heq1.
  2: { eapply result_has_shape_app_r; eauto. }
  rewrite repeat_length in *. lia.
  rewrite <- H4. f_equal. f_equal. simpl.
  rewrite nth_error_app1. auto.
  erewrite result_has_shape_length.
  2: { eapply result_has_shape_app_r; eauto. }
  rewrite repeat_length.
  cases (result_lookup_Z_option
           (z :: x2)
           (V
              (x ++
                 repeat (gen_pad
                           (map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)))
                 (Z.to_nat (eval_Zexpr_Z_total $0 k)))));
    try (simpl in *; discriminate).
  eapply result_lookup_Z_option_Some_pad_r in Heq1; auto.
  erewrite result_has_shape_length in Heq1.
  2: { eapply result_has_shape_app_r; eauto. }
  rewrite repeat_length in *. lia.
Qed.
(*
Definition well_formed_allocation reindexer sh (st : stack) (h : heap) p v :=
  match reindexer (shape_to_index sh (shape_to_vars sh)) with
  | [] => exists a, st $? p = Some a
  | _ => exists a, h $? p = Some a /\
                     constant
                       (map (interpret_reindexer reindexer sh v)
                            (mesh_grid sh)) \subseteq dom a
  end.

Lemma well_formed_allocation_id_scalar : forall st v h x r k,
    ~ x \in dom h ->
            partial_well_formed_allocation (fun l => l)
                                   (result_shape_Z (S r))
                                   (st $+ (x, k)) h x v.
Proof.
  unfold well_formed_allocation. propositional.
  simpl. eexists. rewrite lookup_add_eq by auto. reflexivity.
Qed.

Lemma well_formed_allocation_add_in_stack :
  forall reindexer sh st h v p val,
    p \in dom st ->
    dom st \cap dom h = constant [] ->
  well_formed_allocation reindexer sh st h p v ->
  well_formed_allocation reindexer sh (st $+ (p, val)) h p v.
Proof.
  unfold well_formed_allocation. intros.
  cases (reindexer (shape_to_index sh (shape_to_vars sh))).
  - invs. rewrite lookup_add_eq by auto. eauto.
  - invs. eapply lookup_Some_dom in H1. sets.
Qed.
*)

Lemma well_formed_allocation_scalar_id : forall r st (x : var) h v val,
    well_formed_allocation (fun l : list (Zexpr * Zexpr) => l) (S r)
      (st $+ (x, val)) h x v.
Proof.
  intros. unfold well_formed_allocation. simpl.
  rewrite lookup_add_eq by auto. eauto.
Qed.

(*
Lemma well_formed_allocation_result_V :
  forall l st h p v reindexer,
    well_formed_allocation reindexer (result_shape_Z (V l)) st h p v ->
    (forall l : list (Zexpr * Zexpr),
        vars_of_reindexer (reindexer l) =
          vars_of_reindexer (reindexer []) \cup vars_of_reindexer l)->
    exists a : array,
      h $? p = Some a /\
        constant (map (interpret_reindexer
                         reindexer (result_shape_Z (V l)) v)
                      (mesh_grid (result_shape_Z (V l)))) \subseteq dom a.
Proof.
  unfold well_formed_allocation. intros.
  unfold result_shape_Z in *. simpl in *.
  cases (reindexer
          (shape_to_index
             (map Z.of_nat
                  match l with
                  | [] => [0]
                  | x :: xs => Datatypes.S (length xs) :: result_shape_nat x
                end)
             (shape_to_vars
                (map Z.of_nat
                   match l with
                   | [] => [0]
                   | x :: xs =>
                       Datatypes.S (length xs) :: result_shape_nat x
                   end)))).
  - cases l.
    + eapply reindexer_not_empty in Heq; simpl; propositional; discriminate.
    + eapply reindexer_not_empty in Heq; simpl; propositional; discriminate.
  - invs. clear Heq. eauto.
Qed.

Lemma well_formed_allocation_in_heap : forall sh st h p v reindexer a,
    well_formed_allocation reindexer sh st h p v ->
    h $? p = Some a ->
    dom st \cap dom h = constant [] ->
    constant (map (interpret_reindexer reindexer sh v) (mesh_grid sh))
             \subseteq dom a.
Proof.
  unfold well_formed_allocation in *. intros.
  cases (reindexer (shape_to_index sh (shape_to_vars sh))).
  - invs. eapply lookup_Some_dom in H0,H2. sets.
  - invs. rewrite H in H0. invs. eauto.
Qed.
*)
Lemma eq_constant_map_transpose_reindexer :
  forall v l reindexer n m xs,
    result_has_shape (V l) (n::m::xs) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    (forall (var : var) (k : Z) (l : list (Zexpr * Zexpr)),
        ~ var \in vars_of_reindexer (reindexer []) ->
                  map (subst_var_in_Z_tup var k) (reindexer l) =
                    reindexer (map (subst_var_in_Z_tup var k) l)) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    constant (map (interpret_reindexer
                     reindexer
                     (result_shape_Z (transpose_result l (m::n::xs))) v)
                  (mesh_grid (result_shape_Z
                                (transpose_result l (m::n::xs))))) = 
      constant
        (map
           (interpret_reindexer
              (fun l0 : list (Zexpr * Zexpr) =>
                 reindexer
                   match l0 with
                   | [] => l0
                   | [(v0, d)] => l0
                   | (v0, d) :: (vi, di) :: xs => (vi, di) :: (v0, d) :: xs
                   end) (result_shape_Z (V l)) v)
           (mesh_grid (result_shape_Z (V l)))).
Proof.
  intros. cases m. invert H. reflexivity.
  invert H7. simpl.
  rewrite map_constant_repeat. unfold zrange.
  rewrite length_zrange'. rewrite Z.sub_0_r.
  rewrite concat_repeat_empty.
  rewrite concat_repeat_empty. simpl. reflexivity.
  symmetry.
  erewrite result_has_shape_result_shape_Z by eassumption.
  erewrite result_has_shape_result_shape_Z.
  2: { eapply result_has_shape_transpose_result. eassumption. }
  apply sets_equal. propositional.
  - eapply In_iff_in in H3.
    eapply In_iff_in.
    erewrite <- In_iff_in.
    eapply in_map_iff in H3. invs.
    eapply in_map_iff.
    eapply in_mesh_grid_cons_filter_until_0 in H5.
    cases x0. eapply not_In_empty_map2_cons in H5. propositional.
    rewrite map_cons in *.
    eapply in_mesh_grid_cons__ in H5. invs.
    cases x0. eapply not_In_empty_map2_cons in H4. propositional.
    rewrite map_cons in *.
    eapply in_mesh_grid_cons__ in H4. invs.
    eexists (z0::z::x0). split.
    2: { erewrite <- in_mesh_grid_cons_filter_until_0. simpl map.
         erewrite <- in_mesh_grid_cons__. propositional.
         erewrite <- in_mesh_grid_cons__. propositional. }
    simpl. cases n. simpl in *. lia. simpl. posnats.
    unfold interpret_reindexer.
    unfold shape_to_vars. simpl.
    repeat rewrite index_to_function_alt_vars_cons; eauto with reindexers.
    rewrite H1; try eapply not_var_generation_in_index; eauto. 
    rewrite H1; try eapply not_var_generation_in_index; eauto. 
    rewrite H1; try eapply not_var_generation_in_index; eauto. 
    rewrite H1; try eapply not_var_generation_in_index; eauto. 
    simpl.
    repeat rewrite map_subst_var_in_Z_tup_combine_not_in;
      eauto with reindexers.
    eapply not_var_generation_in_index2; eauto. 
    eapply not_var_generation_in_index2; eauto. 
  - eapply In_iff_in in H3.
    eapply In_iff_in.
    erewrite <- In_iff_in.
    eapply in_map_iff in H3. invs.
    eapply in_map_iff.
    eapply in_mesh_grid_cons_filter_until_0 in H5.
    cases x0. eapply not_In_empty_map2_cons in H5. propositional.
    rewrite map_cons in *.
    eapply in_mesh_grid_cons__ in H5. invs. simpl map in H4.
    cases x0. eapply not_In_empty_map2_cons in H4. propositional.
    eapply in_mesh_grid_cons__ in H4. invs.
    eexists (z0::z::x0). split.
    2: { erewrite <- in_mesh_grid_cons_filter_until_0. simpl map.
         erewrite <- in_mesh_grid_cons__. propositional.
         erewrite <- in_mesh_grid_cons__. propositional. }
    simpl. cases n; simpl; try lia.
    unfold interpret_reindexer.
    unfold shape_to_vars. simpl.
    repeat rewrite index_to_function_alt_vars_cons; eauto with reindexers.
    rewrite H1; try eapply not_var_generation_in_index; eauto. 
    rewrite H1; try eapply not_var_generation_in_index; eauto. 
    rewrite H1; try eapply not_var_generation_in_index; eauto. 
    rewrite H1; try eapply not_var_generation_in_index; eauto. 
    simpl.
    repeat rewrite map_subst_var_in_Z_tup_combine_not_in;
      eauto with reindexers.
    eapply not_var_generation_in_index2; eauto. 
    eapply not_var_generation_in_index2; eauto. 
Qed.

Lemma empty_not_in_mesh_grid_cons : forall x xs,
    ~ In [] (mesh_grid (x::xs)).
Proof.
  intros.
  simpl.
  eapply not_In_empty_map2_cons.
Qed.  
(*
Lemma well_formed_allocation_transpose :
  forall st h p v l reindexer n m xs,
    well_formed_allocation reindexer
                           (result_shape_Z (transpose_result l (m::n::xs)))
                           st h p v ->
    result_has_shape (V l) (n::m::xs) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    (forall (var : var) (k : Z) (l0 : list (Zexpr * Zexpr)),
        ~ var \in vars_of_reindexer (reindexer []) ->
                  map (subst_var_in_Z_tup var k) (reindexer l0) =
                    reindexer (map (subst_var_in_Z_tup var k) l0)) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall l, vars_of_reindexer (reindexer l) =
                 vars_of_reindexer (reindexer []) \cup vars_of_reindexer l) ->
    well_formed_allocation
      (fun l0 : list (Zexpr * Zexpr) =>
         reindexer
           match l0 with
           | [] => l0
           | [(v0, d)] => l0
           | (v0, d) :: (vi, di) :: xs => (vi, di) :: (v0, d) :: xs
           end) (result_shape_Z (V l)) st h p v.
Proof.
  unfold well_formed_allocation. propositional.
  simpl filter_until in *.
  cases m; cases n.
  - erewrite result_has_shape_result_shape_Z in *.
    2: { eapply result_has_shape_transpose_result. eauto. }
    2: { eauto. }
    simpl in *. eauto.
  - unfold shape_to_vars in *.
    unfold shape_to_index in *.
    simpl in *|-.
    cases (reindexer [((! "?" !)%z, (| 0 |)%z)]).
    + erewrite result_has_shape_result_shape_Z in *.
      2: { eapply result_has_shape_transpose_result. eauto. }
      2: { eauto. }
      specialize (H4 [((! "?" !)%z, (| 0 |)%z)]).
      simpl in *. rewrite Heq in H4.
      simpl in H4. repeat rewrite cup_empty_r in H4.
      symmetry in H4.
      eapply cup_empty in H4. invs.
      eapply constant_not_empty in H6. propositional. propositional. invert H4.
    + invs.
      simpl combine.
      cases (reindexer
               [((! "??" !)%z, (| 0 |)%z);
                ((! "?" !)%z, (| Z.pos (Pos.of_succ_nat n) |)%z)]).
      * erewrite result_has_shape_result_shape_Z in *.
        2: { eapply result_has_shape_transpose_result. eauto. }
        2: { eauto. }
        simpl in *. 
        specialize (H4 [((! "??" !)%z, (| 0 |)%z);
                        ((! "?" !)%z, (| Z.pos (Pos.of_succ_nat n) |)%z)]).
        simpl in *.
        rewrite Heq0 in *.
        repeat rewrite cup_empty_r in H4.
        simpl in H4. symmetry in H4.
        eapply cup_empty in H4. invs.
        rewrite union_constant in *.
        simpl in H6.
        eapply constant_not_empty in H6. propositional. propositional.
        invert H4.
      * erewrite result_has_shape_result_shape_Z in *.
        2: { eapply result_has_shape_transpose_result. eauto. }
        2: { eauto. }
        simpl (map Z.of_nat _) in *.
        erewrite exists_0_empty_mesh_grid in * by eauto.
        simpl in *.
        simpl in l1.
        rewrite Heq0,Heq in *. invs. eexists. split. 
        eassumption. sets.
  - unfold shape_to_vars in *.
    unfold shape_to_index in *.
    simpl in *.
    erewrite result_has_shape_result_shape_Z by eassumption.
    erewrite result_has_shape_result_shape_Z in *.
    2: { eapply result_has_shape_transpose_result. eauto. }
    cases (reindexer
          [((! "?" !)%z, (| Z.pos (Pos.of_succ_nat m) |)%z);
           ((! "??" !)%z, (| 0 |)%z)]).
    + specialize (H4 [((! "?" !)%z, (| Z.pos (Pos.of_succ_nat m) |)%z);
                      ((! "??" !)%z, (| 0 |)%z)]).
      simpl in *. rewrite Heq in H4.
      simpl in H4. repeat rewrite cup_empty_r in H4.
      symmetry in H4.
      eapply cup_empty in H4. invs.
      rewrite union_constant in H6. simpl in H6.
      eapply constant_not_empty in H6. propositional. propositional.
      invert H4.
    + invs. 
      cases (reindexer [((! "?" !)%z, (| 0 |)%z)]).
      * specialize (H4 [((! "?" !)%z, (| 0 |)%z)]).
        simpl in *. rewrite Heq0 in H4.
        simpl in H4. repeat rewrite cup_empty_r in H4.
        symmetry in H4.
        eapply cup_empty in H4. invs.
        eapply constant_not_empty in H6. propositional. propositional.
        invert H4.
      * simpl (map Z.of_nat _) in *.
        erewrite exists_0_empty_mesh_grid in * by eauto.
        simpl.
        rewrite Heq0.
        simpl in H. rewrite Heq in *. invs.
        eexists. split. eassumption. auto.
  - remember (      exists a : array,
        h $? p = Some a /\
        constant
          (map
             (interpret_reindexer
                (fun l1 : list (Zexpr * Zexpr) =>
                 reindexer
                   match l1 with
                   | [] => l1
                   | [(v0, d)] => l1
                   | (v0, d) :: (vi, di) :: xs0 => (vi, di) :: (v0, d) :: xs0
                   end) (result_shape_Z (V l)) v) (mesh_grid (result_shape_Z (V l)))) \subseteq
        dom a
             ).
    cases (shape_to_index (result_shape_Z (V l)) (shape_to_vars (result_shape_Z (V l)))).
    + erewrite result_has_shape_result_shape_Z in Heq by eassumption.
      invert Heq.
    + erewrite result_has_shape_result_shape_Z in Heq by eassumption.
      simpl in Heq.
      unfold shape_to_vars in Heq. simpl in *.
      repeat rewrite shape_to_index_cons in Heq.
      invert Heq.
      cases (reindexer
      (((! "??" !)%z, (| Z.pos (Pos.of_succ_nat m) |)%z)
       :: ((! "?" !)%z, (| Z.pos (Pos.of_succ_nat n) |)%z)
          :: shape_to_index (map Z.of_nat (filter_until xs 0))
               (map (fun k : nat => String.concat "" (repeat "?" (k + 1)))
                  (nat_range_rec
                     (Datatypes.length (map Z.of_nat (filter_until xs 0))) 2)))).
      * specialize (H4 (((! "??" !)%z, (| Z.pos (Pos.of_succ_nat m) |)%z)
           :: ((! "?" !)%z, (| Z.pos (Pos.of_succ_nat n) |)%z)
              :: shape_to_index (map Z.of_nat (filter_until xs 0))
                   (map (fun k : nat => String.concat "" (repeat "?" (k + 1)))
                      (nat_range_rec
                         (Datatypes.length (map Z.of_nat (filter_until xs 0))) 2)))).
        simpl in H4.
        rewrite Heq in H4. repeat rewrite cup_empty_r in H4.        
        symmetry in H4.
        eapply cup_empty in H4. invert H4.
        eapply cup_empty in H6. invert H6.
        eapply constant_not_empty in H4. propositional. propositional.
        invert H6.
      * remember ((shape_to_index
             (result_shape_Z
                (transpose_result l (Datatypes.S m :: Datatypes.S n :: xs)))
             (shape_to_vars
                (result_shape_Z
                   (transpose_result l (Datatypes.S m :: Datatypes.S n :: xs)))))).
        erewrite result_has_shape_result_shape_Z in Heql1.
        2: { eapply result_has_shape_transpose_result. eauto. }
        simpl in Heql1.
        rewrite Heql1 in *. clear Heql1.
        cases (reindexer
          (shape_to_index
             (Z.pos (Pos.of_succ_nat m)
              :: Z.pos (Pos.of_succ_nat n) :: map Z.of_nat (filter_until xs 0))
             (shape_to_vars
                (Z.pos (Pos.of_succ_nat m)
                       :: Z.pos (Pos.of_succ_nat n) :: map Z.of_nat (filter_until xs 0))))).
        -- specialize (H4 (shape_to_index
              (Z.pos (Pos.of_succ_nat m)
               :: Z.pos (Pos.of_succ_nat n) :: map Z.of_nat (filter_until xs 0))
              (shape_to_vars
                 (Z.pos (Pos.of_succ_nat m)
                        :: Z.pos (Pos.of_succ_nat n) :: map Z.of_nat (filter_until xs 0))))).
           rewrite Heq0 in *.           
           unfold shape_to_index in H4. unfold shape_to_vars in H4.
           simpl in H4. repeat rewrite cup_empty_r in H4.
           symmetry in H4.
           eapply cup_empty in H4. invert H4.
           eapply cup_empty in H6. invert H6.
           eapply constant_not_empty in H4. propositional.
           propositional. invert H6.
        -- invs. eexists. split. eassumption.
           eapply subseteq_transitivity.
           2: eassumption.
           erewrite eq_constant_map_transpose_reindexer;eauto.
Qed.
*)
Lemma eq_constant_map_flatten_reindexer :
  forall v l reindexer n m xs,
    result_has_shape (V l) (n::m::xs) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    (forall (var : var) (k : Z) (l : list (Zexpr * Zexpr)),
        ~ var \in vars_of_reindexer (reindexer []) ->
                  map (subst_var_in_Z_tup var k) (reindexer l) =
                    reindexer (map (subst_var_in_Z_tup var k) l)) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall l1 l2 : list (Zexpr * Zexpr),
        eq_Z_tuple_index_list l1 l2 ->
        eq_Z_tuple_index_list (reindexer l1) (reindexer l2)) ->
    constant (map (interpret_reindexer
                     reindexer
                     (result_shape_Z (V (flatten_result l))) v)
                  (mesh_grid (result_shape_Z (V (flatten_result l))))) =
      constant
        (map
           (interpret_reindexer
              (fun l0 : list (Zexpr * Zexpr) =>
                 reindexer
                   match l0 with
                   | [] => l0
                   | [(v0, d)] => l0
                   | (v0, d) :: (vi, di) :: xs =>
                       ((v0 * di + vi)%z, (d * di)%z) :: xs
                   end) (result_shape_Z (V l)) v)
           (mesh_grid (result_shape_Z (V l)))).
Proof.
  intros. cases m.
  erewrite result_has_shape_result_shape_Z.
  2: { eapply result_has_shape_flatten. eassumption. }
  erewrite result_has_shape_result_shape_Z by eauto.
  invert H. reflexivity. invert H8. simpl (map Z.of_nat _).
  rewrite mul_0_r in *. 
  erewrite exists_0_empty_mesh_grid.
  2: { simpl. eauto. }
  erewrite exists_0_empty_mesh_grid.
  2: { simpl. eauto. }
  reflexivity.

  erewrite result_has_shape_result_shape_Z.
  2: { eapply result_has_shape_flatten. eassumption. }
  erewrite result_has_shape_result_shape_Z by eauto.
  apply sets_equal. propositional.
  - eapply In_iff_in in H4.
    eapply In_iff_in.
    erewrite <- In_iff_in.
    eapply in_map_iff in H4. invs.
    eapply in_map_iff.
    eapply in_mesh_grid_cons_filter_until_0 in H6.
    rewrite map_cons in *.
    decomp_index. eapply empty_not_in_mesh_grid_cons in H6. propositional.
    eapply in_mesh_grid_cons__ in H6. invs.
    rewrite Nat2Z.inj_mul in H7.
    pose proof (Z_div_mod z (Z.of_nat (Datatypes.S m))).
    cases (Z.div_eucl z (Z.of_nat (Datatypes.S m))).
    assert (Z.of_nat (Datatypes.S m) > 0)%Z by lia. propositional. subst.
    rewrite Z.mul_comm. 
    rewrite Z.mul_comm in H6.
    eexists (z0::z1::x0).
    split.
    simpl.
    cases n; simpl in *; try lia.
    unfold interpret_reindexer.
    repeat rewrite map_cons. unfold shape_to_vars. simpl.
    repeat rewrite index_to_function_alt_vars_cons; eauto with reindexers.
    repeat (rewrite H1; try eapply not_var_generation_in_index;
            try eapply not_var_generation_in_index2; eauto).
    simpl.
    repeat rewrite map_subst_var_in_Z_tup_combine_not_in
      by eauto with reindexers.
    unfold subst_var_in_Z_tup. simpl.
    rewrite index_to_function_alt_subst_vars by eauto with reindexers.
    symmetry.
    rewrite index_to_function_alt_subst_vars by eauto with reindexers.
    symmetry.
    rewrite map_fold_left_subst_var_in_Z_tup_reindexer
      by eauto with reindexers.
    simpl.
    rewrite map_fold_left_subst_var_in_Z_tup_combine;
      eauto with reindexers.
    rewrite fold_left_subst_var_in_Z_tup_id; eauto.
    symmetry.
    rewrite map_fold_left_subst_var_in_Z_tup_reindexer
      by eauto with reindexers.
    simpl.
    rewrite map_fold_left_subst_var_in_Z_tup_combine;
      eauto with reindexers.
    rewrite fold_left_subst_var_in_Z_tup_id; eauto.
    erewrite eq_index_to_function_alt. reflexivity.
    eapply eq_Z_tuple_index_list_partially_eval_Z_tup.
    eapply H3.
    erewrite <- eq_Z_tuple_index_list_cons_tup.
    split.
    eapply eq_zexpr_comm.
    eapply eq_zexpr_transitivity.
    eapply eq_zexpr_add. eapply eq_zexpr_mul_literal.
    eapply eq_zexpr_id. reflexivity.
    eapply eq_zexpr_add_literal.
    split.
    eapply eq_zexpr_comm.
    eapply eq_zexpr_transitivity.
    eapply eq_zexpr_mul_literal.
    eapply eq_zexpr_id. f_equal. lia.
    eapply eq_Z_tuple_index_list_id.
    rewrite map_length. rewrite length_nat_range_rec.
    rewrite map_length. eapply length_mesh_grid_indices.
    erewrite <- in_mesh_grid_cons_filter_until_0. auto.
    rewrite map_length. rewrite length_nat_range_rec.
    rewrite map_length. eapply length_mesh_grid_indices.
    erewrite <- in_mesh_grid_cons_filter_until_0. auto.
    assert (-1 * z1 <= z0* Z.of_nat (Datatypes.S m))%Z by lia.
    assert (-1 * Z.of_nat (Datatypes.S m) < -1 * z1)%Z by lia.
    assert (-1 * Z.of_nat (Datatypes.S m) < z0* Z.of_nat (Datatypes.S m))%Z
      by lia.
    eapply Zmult_gt_0_lt_reg_r in H12.
    erewrite <- in_mesh_grid_cons_filter_until_0. simpl map.
    erewrite <- in_mesh_grid_cons__. propositional.
    lia. 
    rewrite (Z.mul_comm (Z.of_nat n)) in H7. 
    eapply div_eucl_bound in H7.  lia. lia. lia.
    erewrite <- in_mesh_grid_cons__. propositional. lia.
  - eapply In_iff_in in H4.
    eapply In_iff_in.
    erewrite <- In_iff_in.
    eapply in_map_iff in H4. invs.
    eapply in_map_iff.
    eapply in_mesh_grid_cons_filter_until_0 in H6.
    repeat rewrite map_cons in *.
    cases x0. eapply empty_not_in_mesh_grid_cons in H6. propositional.
    eapply in_mesh_grid_cons__ in H6. invs.
    cases x0. eapply empty_not_in_mesh_grid_cons in H5. propositional.
    eapply in_mesh_grid_cons__ in H5. invs.
    eexists (z* Z.of_nat (Datatypes.S m) + z0::x0)%Z.
    split.
    simpl. cases n; simpl in *; try lia.
    unfold interpret_reindexer.
    repeat rewrite map_cons. unfold shape_to_vars. simpl.
    repeat rewrite index_to_function_alt_vars_cons; eauto with reindexers.
    repeat (rewrite H1; try eapply not_var_generation_in_index;
            try eapply not_var_generation_in_index2; eauto).
    simpl.
    repeat rewrite map_subst_var_in_Z_tup_combine_not_in
      by eauto with reindexers.
    unfold subst_var_in_Z_tup. simpl.
    rewrite index_to_function_alt_subst_vars by eauto with reindexers.
    symmetry.
    rewrite index_to_function_alt_subst_vars by eauto with reindexers.
    symmetry.
    rewrite map_fold_left_subst_var_in_Z_tup_reindexer
      by eauto with reindexers.
    simpl.
    rewrite map_fold_left_subst_var_in_Z_tup_combine;
      eauto with reindexers.
    rewrite fold_left_subst_var_in_Z_tup_id; eauto.
    symmetry.
    rewrite map_fold_left_subst_var_in_Z_tup_reindexer
      by eauto with reindexers.
    simpl.
    rewrite map_fold_left_subst_var_in_Z_tup_combine;
      eauto with reindexers.
    rewrite fold_left_subst_var_in_Z_tup_id; eauto.
    erewrite eq_index_to_function_alt. reflexivity.
    eapply eq_Z_tuple_index_list_partially_eval_Z_tup.
    eapply H3.
    erewrite <- eq_Z_tuple_index_list_cons_tup.
    split.
    eapply eq_zexpr_transitivity.
    eapply eq_zexpr_add. eapply eq_zexpr_mul_literal.
    eapply eq_zexpr_id. reflexivity.
    eapply eq_zexpr_add_literal.
    split.
    eapply eq_zexpr_transitivity.
    eapply eq_zexpr_mul_literal.
    eapply eq_zexpr_id. f_equal. lia.
    eapply eq_Z_tuple_index_list_id.
    rewrite map_length. rewrite length_nat_range_rec.
    rewrite map_length. eapply length_mesh_grid_indices.
    erewrite <- in_mesh_grid_cons_filter_until_0. auto.
    rewrite map_length. rewrite length_nat_range_rec.
    rewrite map_length. eapply length_mesh_grid_indices.
    erewrite <- in_mesh_grid_cons_filter_until_0. auto.
    simpl map. cases n. simpl in *. lia.
    simpl map. posnats.
    erewrite <- in_mesh_grid_cons__. propositional. lia. posnats.
    replace (Z.of_nat (Datatypes.S (m + n * Datatypes.S m))) with
              (Z.of_nat (Datatypes.S n * Datatypes.S m)) by lia.
    rewrite Nat2Z.inj_mul.    
    eapply mul_add_lt; lia.
    erewrite <- in_mesh_grid_cons_filter_until_0. auto.
Qed.
(*
Lemma well_formed_allocation_flatten :
  forall l st h p v reindexer n m xs,
    well_formed_allocation reindexer
                           (result_shape_Z (V (flatten_result l))) st h p v ->
    result_has_shape (V l) (n::m::xs) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    (forall (var : var) (k : Z) (l0 : list (Zexpr * Zexpr)),
        ~ var \in vars_of_reindexer (reindexer []) ->
                  map (subst_var_in_Z_tup var k) (reindexer l0) =
                    reindexer (map (subst_var_in_Z_tup var k) l0)) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall l1 l2 : list (Zexpr * Zexpr),
        eq_Z_tuple_index_list l1 l2 ->
        eq_Z_tuple_index_list (reindexer l1) (reindexer l2)) ->
(forall l, vars_of_reindexer (reindexer l) =
             vars_of_reindexer (reindexer []) \cup vars_of_reindexer l) ->

    well_formed_allocation
      (fun l0 : list (Zexpr * Zexpr) =>
         reindexer
           match l0 with
           | [] => l0
           | [(v0, d)] => l0
           | (v0, d) :: (vi, di) :: xs => ((v0 * di + vi)%z, (d * di)%z) :: xs
           end) (result_shape_Z (V l)) st h p v.
Proof.
  unfold well_formed_allocation. propositional.
  cases (reindexer
          (shape_to_index (result_shape_Z (V (flatten_result l)))
                          (shape_to_vars (result_shape_Z (V (flatten_result l)))))).
  - erewrite result_has_shape_result_shape_Z in *.
    2: { eapply result_has_shape_flatten. eauto. }
    2: { eassumption. }
    specialize (H5 (shape_to_index (map Z.of_nat
                                        (filter_until (n * m :: xs) 0))
                                   (shape_to_vars
                                      (map Z.of_nat
                                           (filter_until (n * m :: xs) 0))))).
    rewrite Heq in H5.
    unfold shape_to_vars in H5. simpl in H5.
    cases (n * m).
    + simpl in *. repeat rewrite cup_empty_r in H5.
      symmetry in H5.
      eapply cup_empty in H5. invert H5.
      eapply constant_not_empty in H7. propositional.
      propositional. invert H5.
    + simpl in H5.
      repeat rewrite cup_empty_r in H5.
      symmetry in H5.
      eapply cup_empty in H5. invert H5.
      eapply cup_empty in H7. invert H7.
      eapply constant_not_empty in H5. propositional. inversion 1.
  - invs. clear Heq.
    cases (shape_to_index (result_shape_Z (V l)) (shape_to_vars (result_shape_Z (V l)))).
    + erewrite result_has_shape_result_shape_Z in Heq by eauto.
      simpl in Heq.
      cases n. simpl in Heq. invert Heq. simpl in Heq. invert Heq.
    + erewrite result_has_shape_result_shape_Z in Heq by eauto.
      simpl in Heq.
      cases n.
      * simpl in Heq. invert Heq.
        cases (reindexer [((! "?" !)%z, (| 0 |)%z)]).
        -- specialize (H5 [((! "?" !)%z, (| 0 |)%z)]).
           rewrite Heq in H5. simpl in H5.
           repeat rewrite cup_empty_r in H5.
           symmetry in H5.
           eapply cup_empty in H5. invert H5.
           eapply constant_not_empty in H8. propositional. inversion 1.
        -- eexists. split. eassumption.
           erewrite result_has_shape_result_shape_Z by eassumption.
           simpl map.
           sets.
      * simpl in Heq.
        cases m.
        -- simpl in *. invert Heq.
           cases (reindexer
                    [((! "?" ! * | 0 | + ! "??" !)%z, (| Z.pos (Pos.of_succ_nat n) | * | 0 |)%z)]).
           ++ specialize (H5 [((! "?" ! * | 0 | + ! "??" !)%z,
                                (| Z.pos (Pos.of_succ_nat n) | * | 0 |)%z)]).
              rewrite Heq in H5.
              simpl in H5.
              repeat rewrite cup_empty_r in H5.
              symmetry in H5.
              eapply cup_empty in H5. invert H5.
              unfold app_no_dups in *. simpl in H8.
              eapply constant_not_empty in H8. propositional. inversion 1.
           ++ erewrite result_has_shape_result_shape_Z by eassumption.
              erewrite exists_0_empty_mesh_grid by (simpl; eauto).
              eexists. split. eassumption. sets.
        -- simpl in *.
           invert Heq.
           cases (reindexer
      (((! "?" ! * | Z.pos (Pos.of_succ_nat m) | + ! "??" !)%z,
       (| Z.pos (Pos.of_succ_nat n) | * | Z.pos (Pos.of_succ_nat m) |)%z)
       :: combine
            (map ZVar
               (map (fun k : nat => String.concat "" (repeat "?" (k + 1)))
                  (nat_range_rec
                     (Datatypes.length (map Z.of_nat (filter_until xs 0))) 2)))
            (map ZLit (map Z.of_nat (filter_until xs 0))))).
           ++ specialize (H5 (((! "?" ! * | Z.pos (Pos.of_succ_nat m) | + ! "??" !)%z,
           (| Z.pos (Pos.of_succ_nat n) | * | Z.pos (Pos.of_succ_nat m) |)%z)
           :: combine
                (map ZVar
                   (map (fun k : nat => String.concat "" (repeat "?" (k + 1)))
                      (nat_range_rec
                         (Datatypes.length (map Z.of_nat (filter_until xs 0))) 2)))
                (map ZLit (map Z.of_nat (filter_until xs 0))))).
              rewrite Heq in H5.
              simpl in H5.
              unfold app_no_dups in *. simpl in *.
              repeat rewrite cup_empty_r in H5.
              symmetry in H5.
              eapply cup_empty in H5. invert H5.
              eapply cup_empty in H8. invert H8.
              eapply constant_not_empty in H5. propositional. inversion 1.
           ++ eexists. split. eassumption. clear Heq.
              erewrite <- eq_constant_map_flatten_reindexer; eauto.
Qed.
*)
Lemma well_formed_allocation_eval_step :
  forall reindexer r l st h v p hi lo i a,
    well_formed_allocation reindexer
                                   (V (r :: l)) st h p v ->
    h $? p = Some a ->
    (forall l1 l2 : list (Zexpr * Zexpr),
        eq_Z_tuple_index_list l1 l2 ->
        eq_Z_tuple_index_list (reindexer l1) (reindexer l2)) ->
    (forall var, contains_substring "?" var -> var \in dom v -> False) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall (var : var) (k : Z) (l0 : list (Zexpr * Zexpr)),
        (var \in vars_of_reindexer (reindexer []) -> False) ->
    map (subst_var_in_Z_tup var k) (reindexer l0) =
      reindexer (map (subst_var_in_Z_tup var k) l0)) ->
    (forall l0 : list (Zexpr * Zexpr),
      vars_of_reindexer (reindexer l0) =
        vars_of_reindexer (reindexer []) \cup vars_of_reindexer l0) ->
    result_has_shape (V (r :: l)) (result_shape_nat (V (r :: l))) ->
    ~ contains_substring "?" i ->
    ~ i \in dom v ->
    eq_zexpr lo (| eval_Zexpr_Z_total $0 lo |)%z ->
    eq_zexpr hi (| eval_Zexpr_Z_total $0 hi |)%z ->
    (eval_Zexpr_Z_total $0 lo < eval_Zexpr_Z_total $0 hi)%Z ->
    Datatypes.length l =
      Z.to_nat (eval_Zexpr_Z_total $0 hi - (eval_Zexpr_Z_total $0 lo + 1)) ->
    partial_injective 
      (partial_interpret_reindexer
         reindexer (result_shape_Z (V (r :: l))) v)
      (filter
                 (fun x =>
                    negb (is_None (result_lookup_Z_option x (V (r :: l)))))
                    (mesh_grid (result_shape_Z (V (r :: l)))))
     ->
    well_formed_allocation
      (fun l1 : list (Zexpr * Zexpr) =>
         reindexer (((! i ! - lo)%z,
                      (hi - lo)%z) :: l1))
      r st h p (v $+ (i, eval_Zexpr_Z_total $0 lo)).
Proof.
  unfold well_formed_allocation in *. propositional.
  cases (reindexer
          (shape_to_index (result_shape_Z (V (r :: l)))
                          (shape_to_vars (result_shape_Z (V (r :: l)))))).
  - eapply reindexer_not_empty in Heq. propositional. auto.
    erewrite result_has_shape_result_shape_Z by eassumption.
    simpl. inversion 1.   
  - clear Heq.
    cases (reindexer
      (((! i ! - lo)%z, (hi - lo)%z)
         :: shape_to_index (result_shape_Z r)
         (shape_to_vars (result_shape_Z r)))).
    + eapply reindexer_not_empty_vars_in_index in Heq. propositional. auto.
      simpl. unfold app_no_dups.
      rewrite <- union_constant.
      unfold not. intros. eapply cup_empty in H14. invs.
      eapply cup_empty in H15. invs.
      eapply cup_empty in H14. invs.
      eapply constant_not_empty in H15. propositional. inversion 1.
    + clear Heq. invs.
      eexists. split. eassumption.
      eapply subseteq_transitivity.
      2: eassumption.
      eapply constant_partial_reindexer_subseteq; eauto.
      lia.
Qed.

Lemma well_formed_allocation_reindexer_not_empty :
  forall reindexer st h p v a b r,
    well_formed_allocation reindexer r st h p v ->
    reindexer (shape_to_index (result_shape_Z r)
                              (shape_to_vars (result_shape_Z r))) = a::b ->
    exists a : array,
      h $? p = Some a /\
        constant
          (extract_Some
             (map (partial_interpret_reindexer
                     reindexer (result_shape_Z r) v)
                  (filter
                     (fun x => negb
                                 (is_None
                                    (result_lookup_Z_option x r)))
                     (mesh_grid (result_shape_Z r)))))
                 \subseteq dom a.
Proof.
  unfold well_formed_allocation. intros.
  rewrite H0 in *. eauto.
Qed.

Lemma well_formed_allocation_add_heap :
  forall reindexer sh st h p a val v,
    well_formed_allocation reindexer sh st h p v ->
    h $? p = Some a ->
    well_formed_allocation
      reindexer sh st (h $+ (p, array_add a val)) p v.
Proof.
  unfold well_formed_allocation. propositional.
  cases (reindexer
           (shape_to_index (result_shape_Z sh)
                           (shape_to_vars (result_shape_Z sh)))).
  eauto.
  rewrite lookup_add_eq in * by auto.
  eexists. split. reflexivity.
  invs. rewrite H in H0. invs.
  rewrite dom_array_add. sets.
Qed.

Lemma well_formed_allocation_add_valuation :
  forall sh st h p v i x reindexer,
    well_formed_allocation reindexer sh st h p v ->
    ~ i \in dom v ->
    ~ contains_substring "?" i ->            
    (forall (var : var) (k : Z) (l : list (Zexpr * Zexpr)),
        ~ var \in vars_of_reindexer (reindexer []) ->
                  map (subst_var_in_Z_tup var k) (reindexer l) =
                    reindexer (map (subst_var_in_Z_tup var k) l)) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    well_formed_allocation reindexer sh st h p (v $+ (i, x)).
Proof.
  unfold well_formed_allocation. propositional.
  cases (reindexer
           (shape_to_index (result_shape_Z sh)
                           (shape_to_vars (result_shape_Z sh)))).
  - invs. eauto.
  - invs. eexists. split. eassumption.
    eapply subseteq_transitivity. 2: eassumption.
    unfold partial_interpret_reindexer.
    rewrite partially_eval_Z_tup_add_partial by auto.
    replace (fun e : Zexpr * Zexpr =>
               subst_var_in_Z_tup i x (partially_eval_Z_tup v e)) with
      (fun e : Zexpr * Zexpr =>
         partially_eval_Z_tup v (subst_var_in_Z_tup i x e)).
    2: { eapply functional_extensionality. intros.
         rewrite subst_var_in_Z_tup_partially_eval_Z_tup_comm; auto. }
    rewrite <- (map_map (fun e => subst_var_in_Z_tup i x e)).
    rewrite H2. rewrite map_subst_var_in_Zexpr_shape_to_index_id.
    sets. unfold not. intros.
    eapply shape_to_vars_contains_substring in H4. propositional.
    intros. eapply H0. eapply H3. eassumption.
Qed.

Lemma well_formed_allocation_add_stack :
  forall sh st h p v x reindexer val,
    well_formed_allocation reindexer sh st h p v ->
    p <> x ->
    well_formed_allocation reindexer sh (st $+ (x, val)) h p v.
Proof.
  unfold well_formed_allocation. propositional.
  cases (reindexer
           (shape_to_index (result_shape_Z sh)
                           (shape_to_vars (result_shape_Z sh)))).
  - rewrite lookup_add_ne by auto. eauto.
  - eauto.
Qed.

Lemma well_formed_allocation_shift_top_dim_reindexer :
  forall reindexer r l st h v p hi lo i a,
    well_formed_allocation reindexer
                                   (V (r :: l)) st h p v ->
    h $? p = Some a ->
    (forall l1 l2 : list (Zexpr * Zexpr),
        eq_Z_tuple_index_list l1 l2 ->
        eq_Z_tuple_index_list (reindexer l1) (reindexer l2)) ->
    (forall var, contains_substring "?" var -> var \in dom v -> False) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall (var : var) (k : Z) (l0 : list (Zexpr * Zexpr)),
        (var \in vars_of_reindexer (reindexer []) -> False) ->
    map (subst_var_in_Z_tup var k) (reindexer l0) =
      reindexer (map (subst_var_in_Z_tup var k) l0)) ->
    (forall l0 : list (Zexpr * Zexpr),
      vars_of_reindexer (reindexer l0) =
        vars_of_reindexer (reindexer []) \cup vars_of_reindexer l0) ->
    result_has_shape (V (r :: l)) (result_shape_nat (V (r :: l))) ->
    partial_injective 
      (partial_interpret_reindexer
         reindexer (result_shape_Z (V (r :: l))) v)
      (filter
         (fun x =>
            negb (is_None (result_lookup_Z_option x (V (r :: l)))))
         (mesh_grid (result_shape_Z (V (r :: l))))) ->
    well_formed_allocation
      (shift_top_dim_reindexer reindexer) 
      (V l) st
      (h $+ (p,
              array_add a
                        (tensor_to_array_delta
                           (partial_interpret_reindexer
                              (fun l1 : list (Zexpr * Zexpr) =>
                                 reindexer (((! i ! - lo)%z,
                                              (hi - lo)%z) :: l1)) 
                              (result_shape_Z r)
                              (v $+ (i, eval_Zexpr_Z_total $0 lo))) r))) p v.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? Halloc Heq HeqZlist Hvar Hvarsub Hmap
         Hvarindexsub Hsh Hinj.
  cases l.
  { eapply well_formed_allocation_result_V in Halloc. invs.
    rewrite H0 in *. invs. unfold result_shape_Z in *. simpl in *.
    repeat rewrite app_nil_r in *. invert Hsh.
    unfold well_formed_allocation.
    unfold shape_to_index, shape_to_vars, shift_top_dim_reindexer.
    simpl.
    cases (reindexer [((! "?" ! + | 1 |)%z, (| 0 | + | 1 |)%z)]).
    eapply reindexer_not_empty_vars_in_index in Heq. propositional.
    auto. simpl. unfold app_no_dups. simpl. repeat rewrite cup_empty_r.
    unfold not. intros.
    eapply constant_not_empty in H. propositional. inversion 1.
    rewrite lookup_add_eq by auto. eexists. split. reflexivity.
    sets. auto. }
  eapply well_formed_allocation_result_V in Halloc. invs.
  rewrite H0 in *. invs.
  unfold well_formed_allocation.
  cases (shift_top_dim_reindexer
           reindexer
           (shape_to_index (result_shape_Z (V (r0::l)))
                           (shape_to_vars (result_shape_Z (V (r0::l)))))).
  { unfold result_shape_Z, shift_top_dim_reindexer in Heq.
    unfold shape_to_vars in Heq. simpl in *.
    cases l.
    - simpl in Heq.
      eapply reindexer_not_empty_vars_in_index in Heq. propositional. auto.
      simpl. unfold app_no_dups. simpl. repeat rewrite cup_empty_r.
      unfold not. intros. eapply cup_empty in H. invert H.
      eapply constant_not_empty in H2. propositional.
      inversion 1.
    - simpl in Heq.
      eapply reindexer_not_empty_vars_in_index in Heq. propositional. auto.
      simpl. unfold app_no_dups. simpl. repeat rewrite cup_empty_r.
      unfold not. intros. eapply cup_empty in H. invs.
      eapply constant_not_empty in H2. propositional.
      inversion 1. }
  rewrite lookup_add_eq by auto.
  eexists. split. reflexivity.
  rewrite dom_array_add.
  eapply subseteq_transitivity.
  2: { eapply subseteq_transitivity.
       eapply H1. sets. }
  apply subseteq_In; intros; 
    erewrite <- In_iff_in in *; erewrite <- in_extract_Some in *;
    erewrite in_map_iff in *.
  - invs.
    erewrite result_has_shape_result_shape_Z in H3.
    2: { invert Hsh. eapply forall_result_has_shape. eauto. eauto. }
    repeat decomp_index.
    erewrite result_has_shape_result_shape_Z in H.
    2: { invert Hsh. eapply forall_result_has_shape. eauto. eauto. }
    replace (Datatypes.S (Datatypes.length l)) with
      (length (r0::l)) in H by reflexivity.
    rewrite eq_partial_interpret_reindexer_shift_top_dim_reindexer in H.
    eexists. split.
    erewrite result_has_shape_result_shape_Z by eassumption.
    apply H.
    erewrite result_has_shape_result_shape_Z by eassumption.
    eapply filter_In. propositional.
    repeat decomp_goal_index. propositional. lia. lia.
    rewrite <- H4. simpl.
    cases (z+1)%Z; try lia.
    cases z; try lia.
    cases (Z.to_nat (Z.pos p1)); try lia. simpl nth_error at 1.
    repeat f_equal. eq_match_discriminee. f_equal. lia.
    cases (Z.to_nat (Z.pos p1)); try lia. simpl nth_error at 1.
    repeat f_equal. eq_match_discriminee. f_equal. lia.
    eauto.
    auto. auto. auto. auto. auto. inversion 1.
  - auto.
Qed.

Lemma well_formed_allocation_add_result_l :
  forall r1 r2 r3 reindexer st h p v sh,
    add_result r1 r2 r3 ->
    result_has_shape r1 sh ->
    result_has_shape r2 sh ->
    result_has_shape r3 sh ->
    well_formed_allocation reindexer r3 st h p v ->
    well_formed_allocation reindexer r1 st h p v.
Proof.
  unfold well_formed_allocation. propositional.
  cases r1.
  - invert H.
    + unfold result_shape_Z in *. simpl in *.
      unfold shape_to_index, shape_to_vars in *. simpl in *.
      cases z.
      * simpl in *. invert H5; auto.
      * simpl in *.
        cases s3.
        -- simpl map in H3.
           cases (reindexer []). auto. invs.
           rewrite H3. eexists. split. reflexivity. sets.
        -- simpl map in H3.
           cases (reindexer []). auto. invs.
           rewrite H3. eexists. split. reflexivity. sets.
  - invert H.
    erewrite result_has_shape_result_shape_Z in * by eauto.
    cases (reindexer
             (shape_to_index (map Z.of_nat (filter_until sh 0))
                             (shape_to_vars
                                (map Z.of_nat (filter_until sh 0))))).
    + eauto.
    + invs. eexists.
      split. eassumption.
      eapply subseteq_transitivity. 2: eassumption.
      apply subseteq_In. intros.
      rewrite <- In_iff_in in *.
      rewrite <- in_extract_Some in *.
      rewrite in_map_iff in *. invs.
      repeat decomp_index.
      eexists. split. eassumption.
      eapply filter_In.
      propositional. decomp_goal_index. auto.
      eapply negb_is_None_lookup_result_Z_option_add_result_l; eauto.
      econstructor. eauto.
Qed.    

Lemma well_formed_allocation_add_result_r :
  forall r1 r2 r3 reindexer st h p v sh,
    add_result r1 r2 r3 ->
    result_has_shape r1 sh ->
    result_has_shape r2 sh ->
    result_has_shape r3 sh ->
    well_formed_allocation reindexer r3 st h p v ->
    well_formed_allocation reindexer r2 st h p v.
Proof.
  unfold well_formed_allocation. propositional.
  cases r1.
  - invert H.
    + unfold result_shape_Z in *. simpl in *.
      unfold shape_to_index, shape_to_vars in *. simpl in *.
      cases s2.
      * simpl in *. cases s3.
        -- eauto.
        -- invert H5.
      * cases s3.
        -- simpl map in *.
           cases (reindexer []). eauto. invs.
           eexists. split. eassumption.
           sets.
        -- simpl map in *.
           cases (reindexer []). eauto. invs.
           eexists. split. eassumption.
           sets.
  - invert H.
    erewrite result_has_shape_result_shape_Z in * by eauto.
    cases (reindexer
             (shape_to_index (map Z.of_nat (filter_until sh 0))
                             (shape_to_vars
                                (map Z.of_nat (filter_until sh 0))))).
    + eauto.
    + invs. eexists.
      split. eassumption.
      eapply subseteq_transitivity. 2: eassumption.
      apply subseteq_In. intros.
      rewrite <- In_iff_in in *.
      rewrite <- in_extract_Some in *.
      rewrite in_map_iff in *. invs.
      repeat decomp_index.
      eexists. split. eassumption.
      eapply filter_In.
      propositional. decomp_goal_index. auto.
      eapply negb_is_None_lookup_result_Z_option_add_result_r; eauto.
      econstructor. eauto.
Qed.    

Lemma well_formed_allocation_letbind1 :
  forall st h v nz x r,
  (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
  ~ x \in dom st ->
  (nz = (fold_left Z.mul (result_shape_Z (V r)) 1%Z)) ->
  well_formed_allocation
    (fun l => l) (V r) st (alloc_array_in_heap [Z.to_nat nz] h x) x v.
Proof.
  unfold well_formed_allocation in *. propositional.
  cases (shape_to_index (result_shape_Z (V r))
                        (shape_to_vars (result_shape_Z (V r)))).
  - eapply shape_to_index_not_empty_Z in Heq. propositional. 
  - unfold alloc_array_in_heap. rewrite lookup_add_eq by auto.
    eexists. split. reflexivity.
    rewrite dom_alloc_array.
    apply subseteq_In. intros.
    rewrite <- In_iff_in in *.
    rewrite <- @in_extract_Some in *.
    erewrite @in_map_iff in *. invs.
    repeat decomp_index.
    unfold result_shape_Z in *. simpl in *.
    cases r.
    + simpl in *. propositional.
    + simpl. rewrite add_0_r.
      pose proof constant_map_flatten_zrange.      
      rewrite partial_interpret_reindexer_id_flatten in *.
      invert H1. 
      simpl map in *.
      repeat decomp_index. posnats.
      specialize (H2 (Z.of_nat (Datatypes.S (Datatypes.length r0))
                               :: map Z.of_nat (result_shape_nat r))).
      erewrite subseteq_In in H2.
      rewrite Z2Nat.id.
      apply H2.
      rewrite <- In_iff_in.
      eapply in_map_iff. eexists. split. reflexivity.
      repeat decomp_goal_index.
      propositional.
      eapply fold_left_mul_nonneg.
      eapply Forall_forall. intros. eapply in_map_iff in H3. invs. lia.
      lia.
      eauto.
      eauto.
Qed.

Lemma well_formed_allocation_add_heap_var :
  forall reindexer sh st h p v val x,
    well_formed_allocation reindexer sh st h p v ->
    p <> x ->
    well_formed_allocation reindexer sh st (h $+ (x, val)) p v.
Proof.
  unfold well_formed_allocation. propositional.
  cases (reindexer
           (shape_to_index (result_shape_Z sh)
                           (shape_to_vars (result_shape_Z sh)))).
  - eauto.
  - rewrite lookup_add_ne by auto. eauto.
Qed. 

Lemma constant_subseteq_transpose :
  forall l n0 m0 l0 v reindexer,
    result_has_shape
      (V l)
      (Z.to_nat (eval_Zexpr_Z_total $0 n0)
                :: Z.to_nat (eval_Zexpr_Z_total $0 m0)
                :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    (forall (var : var) (k : Z) (l0 : list (Zexpr * Zexpr)),
        ~ var \in vars_of_reindexer (reindexer []) ->
                  map (subst_var_in_Z_tup var k) (reindexer l0) =
                    reindexer (map (subst_var_in_Z_tup var k) l0)) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall l : list (Zexpr * Zexpr),
        vars_of_reindexer (reindexer l) =
          vars_of_reindexer (reindexer []) \cup vars_of_reindexer l) ->
    (forall l1 l2 : list (Zexpr * Zexpr),
        eq_Z_tuple_index_list l1 l2 ->
        eq_Z_tuple_index_list (reindexer l1) (reindexer l2)) ->
    constant
      (extract_Some
         (map
            (partial_interpret_reindexer
               (fun l4 : list (Zexpr * Zexpr) =>
                  reindexer
                    match l4 with
                    | [] => l4
                    | [(v0, d)] => l4
                    | (v0, d) :: (vi, di) :: xs => (vi, di) :: (v0, d) :: xs
                    end) (result_shape_Z (V l)) v)
            (filter
               (fun x0 => negb (is_None (result_lookup_Z_option x0 (V l))))
               (mesh_grid (result_shape_Z (V l)))))) \subseteq
      constant
      (extract_Some
         (map
            (partial_interpret_reindexer
               reindexer
               (result_shape_Z
                  (transpose_result
                     l
                     (Z.to_nat (eval_Zexpr_Z_total $0 m0)
                               :: Z.to_nat (eval_Zexpr_Z_total $0 n0)
                               :: map Z.to_nat
                               (map (eval_Zexpr_Z_total $0) l0)))) v)
            (filter
               (fun x0 : list Z =>
                  negb
                    (is_None
                       (result_lookup_Z_option
                          x0
                          (transpose_result
                             l
                             (Z.to_nat (eval_Zexpr_Z_total $0 m0)
                                       :: Z.to_nat (eval_Zexpr_Z_total $0 n0)
                                       :: map Z.to_nat
                                       (map (eval_Zexpr_Z_total $0) l0))))))
               (mesh_grid
                  (result_shape_Z
                     (transpose_result
                        l
                        (Z.to_nat (eval_Zexpr_Z_total $0 m0)
                                  :: Z.to_nat (eval_Zexpr_Z_total $0 n0)
                                  :: map Z.to_nat
                                  (map (eval_Zexpr_Z_total $0) l0)))))))).
Proof.
  intros ? ? ? ? ? ? Hsh Henv Hmap Hvarsub Hvarsarg HeqZlist.
  eapply subseteq_In. intros.
  erewrite <- In_iff_in in *.
  erewrite <- in_extract_Some in *.
  erewrite in_map_iff in *. invs.
  erewrite result_has_shape_result_shape_Z in *; eauto.
  2: { eapply result_has_shape_transpose_result; eauto. }
  repeat decomp_index.
  eexists (z0::z::x0).
  split.
  erewrite <- eq_partial_interpret_reindexer_transpose; eauto.
  eapply filter_In. propositional.
  repeat decomp_goal_index. propositional.
  repeat decomp_goal_index. propositional.
  rewrite <- H2.
  erewrite result_lookup_Z_option_transpose. reflexivity.
  lia. lia. eauto.
Qed.  

Lemma well_formed_allocation_transpose :
  forall l n0 m0 l0 reindexer st h p v,
  result_has_shape (V l)
                   (Z.to_nat
                      (eval_Zexpr_Z_total $0 n0)
                      :: Z.to_nat (eval_Zexpr_Z_total $0 m0)
                      :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)) ->
  well_formed_allocation
    reindexer
    (transpose_result l
                      (Z.to_nat
                         (eval_Zexpr_Z_total $0 m0)
                         :: Z.to_nat (eval_Zexpr_Z_total $0 n0)
                         :: map Z.to_nat
                         (map (eval_Zexpr_Z_total $0) l0))) st h p v ->
  (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
  (forall (var : var) (k : Z) (l0 : list (Zexpr * Zexpr)),
      ~ var \in vars_of_reindexer (reindexer []) ->
                map (subst_var_in_Z_tup var k) (reindexer l0) =
                  reindexer (map (subst_var_in_Z_tup var k) l0)) ->
  vars_of_reindexer (reindexer []) \subseteq dom v ->
  (forall l, vars_of_reindexer (reindexer l) =
               vars_of_reindexer (reindexer []) \cup vars_of_reindexer l) ->
  (forall l4 l5 : list (Zexpr * Zexpr),
      eq_Z_tuple_index_list l4 l5 ->
      eq_Z_tuple_index_list (reindexer l4) (reindexer l5)) ->
  well_formed_allocation
    (fun l1 : list (Zexpr * Zexpr) =>
     reindexer
       match l1 with
       | [] => l1
       | [(v0, d)] => l1
       | (v0, d) :: (vi, di) :: xs => (vi, di) :: (v0, d) :: xs
       end) (V l) st h p v.
Proof.
  intros ? ? ? ? ? ? ? ? ? Hsh Halloc Henv Hmap Hvarsub Hvarsarg HeqZlist.
  unfold well_formed_allocation in *.
  cases (shape_to_index
           (result_shape_Z (V l))
           (shape_to_vars (result_shape_Z (V l)))).
  { eapply shape_to_index_not_empty_Z in Heq. propositional. }
  cases (reindexer
      (let (v0, d) := p0 in
       match l1 with
       | [] => p0 :: l1
       | (vi, di) :: xs => (vi, di) :: (v0, d) :: xs
       end)).
  { eapply reindexer_not_empty_vars_in_index in Heq0. propositional. auto.
    unfold result_shape_Z, shape_to_index, shape_to_vars in Heq. simpl in Heq.
    cases l.
    - simpl in *. invert Heq. simpl.
      unfold not. intros.
      eapply cup_empty in H. invs.
      eapply cup_empty in H0. invs.
      eapply constant_not_empty in H. propositional. inversion 1.
    - simpl in Heq. invert Heq.
      cases r. simpl.
      unfold not. intros.
      eapply cup_empty in H. invs.
      eapply cup_empty in H0. invs.
      eapply constant_not_empty in H. propositional. inversion 1.
      simpl.
      unfold not. intros.
      cases v0.
      simpl.
      unfold not. intros.
      eapply cup_empty in H. invs.
      eapply cup_empty in H0. invs.
      eapply constant_not_empty in H. propositional. inversion 1.
      simpl.
      unfold not. intros.
      eapply cup_empty in H. invs.
      eapply cup_empty in H0. invs.
      eapply constant_not_empty in H. propositional. inversion 1. }
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
  { eapply reindexer_not_empty_vars_in_index in Heq1. propositional. auto.
    erewrite result_has_shape_result_shape_Z.
    2: { eapply result_has_shape_transpose_result. eauto. }
    simpl.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 m0));
      cases (Z.to_nat (eval_Zexpr_Z_total $0 n0)).
    - simpl.
      unfold not. intros.
      eapply cup_empty in H. invs.
      eapply cup_empty in H0. invs.
      eapply constant_not_empty in H2. propositional. inversion 1.
    - simpl.
      unfold not. intros.
      eapply cup_empty in H. invs.
      eapply cup_empty in H0. invs.
      eapply constant_not_empty in H2. propositional. inversion 1.
    - simpl.
      simpl.
      unfold not. intros.
      eapply cup_empty in H. invs.
      eapply cup_empty in H0. invs.
      eapply constant_not_empty in H2. propositional. inversion 1.
    - simpl.
      unfold not. intros.
      eapply cup_empty in H. invs.
      eapply cup_empty in H0. invs.
      eapply constant_not_empty in H2. propositional. inversion 1. }
  invs. eexists.
  split. eassumption.
  eapply subseteq_transitivity. 2: eassumption.
  eapply constant_subseteq_transpose; eauto.
Qed.

Lemma well_formed_allocation_concat_l :
  forall l1 l2 st h p v reindexer xs x2 n m,
    well_formed_allocation
      reindexer (V (l1 ++ l2)%list)
                           st h p v->
    result_has_shape (V l1) (n::xs) ->
    result_has_shape (V l2) (m::xs) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    (forall (var : var) (k : Z) (l0 : list (Zexpr * Zexpr)),
        ~ var \in vars_of_reindexer (reindexer []) ->
                  map (subst_var_in_Z_tup var k) (reindexer l0) =
                    reindexer (map (subst_var_in_Z_tup var k) l0)) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall l1 l2 : list (Zexpr * Zexpr),
        eq_Z_tuple_index_list l1 l2 ->
        eq_Z_tuple_index_list (reindexer l1) (reindexer l2)) ->
    eq_zexpr x2 (|Z.of_nat m|)%z ->
    (forall l : list (Zexpr * Zexpr),
        vars_of_reindexer (reindexer l) =
          vars_of_reindexer (reindexer []) \cup vars_of_reindexer l) ->
    well_formed_allocation
      (fun l : list (Zexpr * Zexpr) =>
         reindexer
         match l with
         | [] => l
         | (v0, d) :: xs =>
               ((v0, (d + x2)%z) :: xs)
         end) (V l1) st h p v.
Proof.
  unfold well_formed_allocation. propositional.
  -  pose proof (result_has_shape_concat _ _ _ _ _ H0 H1).
     cases (shape_to_index (result_shape_Z (V l1))
                           (shape_to_vars (result_shape_Z (V l1)))).
     { eapply shape_to_index_not_empty_Z in Heq. propositional. }
     cases ((reindexer
               (let (v0, d) := p0 in ((v0, (d + x2)%z) :: l)))).
     { unfold result_shape_Z,shape_to_index, shape_to_vars in Heq.
       simpl in *. cases l1.
       - invert Heq.
         eapply reindexer_not_empty_vars_in_index in Heq0. propositional.
         auto.
         simpl.
         rewrite app_no_dups_empty_l.
         rewrite cup_empty_r.
         unfold not. intros.
         eapply cup_empty in H9. invs.
         eapply constant_not_empty in H10. propositional. inversion 1.
       - invert Heq.
         eapply reindexer_not_empty_vars_in_index in Heq0. propositional.
         auto.
         simpl.
         rewrite app_no_dups_empty_l.
         unfold not. intros.
         eapply cup_empty in H9. invs.
         eapply cup_empty in H10. invs.
         eapply constant_not_empty in H9. propositional. inversion 1. }
     cases (reindexer
          (shape_to_index (result_shape_Z (V (l1 ++ l2)))
                          (shape_to_vars (result_shape_Z (V (l1 ++ l2)))))).
     { eapply reindexer_not_empty in Heq1. propositional.
       auto.
       erewrite result_has_shape_result_shape_Z; eauto.
       simpl.
       cases (n + m); inversion 1. }
     invs.
     eexists. split. eassumption.
     eapply subseteq_transitivity. 2: eassumption.
     eapply subseteq_In.
     intros.
     rewrite <- In_iff_in in *.
     rewrite <- in_extract_Some in *.
     rewrite in_map_iff in *.
     invs.
     repeat decomp_index.
     eexists.
     erewrite result_has_shape_result_shape_Z by eauto.
     erewrite <- eq_partial_interpret_reindexer_concat_l; try eassumption.
     erewrite result_has_shape_result_shape_Z in H9 by eauto.
     split. eassumption. 
     eapply filter_In. propositional.
     erewrite result_has_shape_result_shape_Z in H11.
     2: { eauto. }
     repeat decomp_index.
     repeat decomp_goal_index.
     propositional. lia.
     erewrite <- H13.
     simpl. erewrite result_has_shape_result_shape_Z in H11 by eauto.
     repeat decomp_index. simpl.
     rewrite nth_error_app1. reflexivity.
     erewrite result_has_shape_length by eauto.
     lia.
     eapply filter_In. propositional.
Qed.

Lemma well_formed_allocation_concat_r :
  forall l1 l2 st h p v reindexer l0 n m,
    well_formed_allocation
      reindexer (V (l1 ++ l2)%list)
                           st h p v->
    result_has_shape (V l1) (map Z.to_nat (map (eval_Zexpr_Z_total $0)
                                 (n :: l0))) ->
    result_has_shape (V l2) (map Z.to_nat (map (eval_Zexpr_Z_total $0)
                                 (m :: l0))) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    (forall (var : var) (k : Z) (l0 : list (Zexpr * Zexpr)),
        ~ var \in vars_of_reindexer (reindexer []) ->
                  map (subst_var_in_Z_tup var k) (reindexer l0) =
                    reindexer (map (subst_var_in_Z_tup var k) l0)) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall l1 l2 : list (Zexpr * Zexpr),
        eq_Z_tuple_index_list l1 l2 ->
        eq_Z_tuple_index_list (reindexer l1) (reindexer l2)) ->
    (forall l : list (Zexpr * Zexpr),
        vars_of_reindexer (reindexer l) =
          vars_of_reindexer (reindexer []) \cup vars_of_reindexer l) ->
    eq_zexpr n (| eval_Zexpr_Z_total $0 n |)%z ->
    (0 <= eval_Zexpr_Z_total $0 n)%Z ->
    well_formed_allocation
      (fun l : list (Zexpr * Zexpr) =>
         reindexer
         match l with
         | [] => l
         | (v0, d) :: xs =>
               (((v0 + n)%z, (d + n)%z) :: xs)
         end) (V l2) st h p v.
Proof.
  unfold well_formed_allocation. propositional.
  simpl in H0,H1.
  pose proof (result_has_shape_concat _ _ _ _ _ H0 H1).
  cases (shape_to_index (result_shape_Z (V l2))
                        (shape_to_vars (result_shape_Z (V l2)))).
  { eapply shape_to_index_not_empty_Z in Heq. propositional. }
  cases (reindexer (let (v0, d) := p0 in ((v0 + n)%z, (d + n)%z) :: l)).
  { unfold result_shape_Z,shape_to_index, shape_to_vars in Heq.
    simpl in *. cases l2.
    - invert Heq.
      eapply reindexer_not_empty_vars_in_index in Heq0. propositional.
      auto.
      simpl.
      rewrite app_no_dups_empty_l.
      rewrite cup_empty_r. unfold app_no_dups.
      unfold not. intros.
      eapply cup_empty in H10. invs.
      eapply constant_not_empty in H11. propositional. inversion 1.
    - invert Heq.
      eapply reindexer_not_empty_vars_in_index in Heq0. propositional.
      auto.
      simpl.
      rewrite app_no_dups_empty_l. unfold app_no_dups.
      unfold not. intros.
      eapply cup_empty in H10. invs.
      eapply cup_empty in H11. invs.
      eapply constant_not_empty in H10. propositional. inversion 1. }
  cases (reindexer
           (shape_to_index (result_shape_Z (V (l1 ++ l2)))
                           (shape_to_vars (result_shape_Z (V (l1 ++ l2)))))).
  { eapply reindexer_not_empty in Heq1. propositional.
    auto.
    erewrite result_has_shape_result_shape_Z; eauto.
    simpl.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 n) +
             Z.to_nat (eval_Zexpr_Z_total $0 m));
      inversion 1. }

  assert (0 < eval_Zexpr_Z_total $0 m \/ eval_Zexpr_Z_total $0 m <= 0)%Z
    as Hcase by lia.
  inversion Hcase as [ Hcase1 | Hcase2 ]; clear Hcase.
  
  invs.
  eexists. split. eassumption.
  eapply subseteq_transitivity. 2: eassumption.
  eapply subseteq_In.
  intros.
  rewrite <- In_iff_in in *.
  rewrite <- in_extract_Some in *.
  rewrite in_map_iff in *.
  invs.
  erewrite result_has_shape_result_shape_Z in H13 by eauto.
  repeat decomp_index.
  eexists.
  erewrite result_has_shape_result_shape_Z by eauto.
  erewrite <- eq_partial_interpret_reindexer_padl; eauto.     
  erewrite result_has_shape_result_shape_Z in H10 by eauto.
  split.
  eassumption. 
  eapply filter_In. propositional.
  repeat decomp_index.
  repeat decomp_goal_index.
  propositional. lia. lia.
  erewrite <- H14.
  simpl.
  rewrite nth_error_app2.
  erewrite result_has_shape_length by eauto.
  rewrite Z2Nat.inj_add.
  rewrite add_sub.
  cases z; try lia.
  simpl Z.add.
  cases (eval_Zexpr_Z_total $0 n); try lia.
  eauto. eauto.
  cases (Z.pos p3 + eval_Zexpr_Z_total $0 n)%Z; try lia.
  eauto. lia. lia. invert H0. simpl. lia. simpl. lia. 

  erewrite result_has_shape_result_shape_Z by eauto.
  simpl.
  cases (Z.to_nat (eval_Zexpr_Z_total $0 m)). 2: lia.
  simpl.
  invs. eexists. split. eauto. sets.
Qed.

Lemma constant_subseteq_flatten :
  forall l n m l0 v reindexer,
    result_has_shape (V l)
                     (Z.to_nat (eval_Zexpr_Z_total $0 n)
                               :: Z.to_nat (eval_Zexpr_Z_total $0 m)
                               :: map Z.to_nat
                               (map (eval_Zexpr_Z_total $0) l0)) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    (forall (var : var) (k : Z) (l0 : list (Zexpr * Zexpr)),
        ~ var \in vars_of_reindexer (reindexer []) ->
                  map (subst_var_in_Z_tup var k) (reindexer l0) =
                    reindexer (map (subst_var_in_Z_tup var k) l0)) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall l : list (Zexpr * Zexpr),
        vars_of_reindexer (reindexer l) =
          vars_of_reindexer (reindexer []) \cup vars_of_reindexer l) ->
    (forall l1 l2 : list (Zexpr * Zexpr),
        eq_Z_tuple_index_list l1 l2 ->
        eq_Z_tuple_index_list (reindexer l1) (reindexer l2)) ->
  constant
    (extract_Some
       (map
          (partial_interpret_reindexer
             (fun l3 : list (Zexpr * Zexpr) =>
              reindexer
                match l3 with
                | [] => l3
                | [(v0, d)] => l3
                | (v0, d) :: (vi, di) :: xs0 =>
                    ((v0 * di + vi)%z, (d * di)%z) :: xs0
                end)
             (map Z.of_nat
                  (filter_until
                     (Z.to_nat (eval_Zexpr_Z_total $0 n)
                               :: Z.to_nat (eval_Zexpr_Z_total $0 m)
                               :: map Z.to_nat
                               (map (eval_Zexpr_Z_total $0) l0)) 0)) v)
          (filter
             (fun x0 => negb (is_None (result_lookup_Z_option x0 (V l))))
             (mesh_grid
                (map Z.of_nat
                     (filter_until
                        (Z.to_nat (eval_Zexpr_Z_total $0 n)
                                  :: Z.to_nat (eval_Zexpr_Z_total $0 m)
                                  :: map Z.to_nat
                                  (map (eval_Zexpr_Z_total $0) l0)) 0))))))
    \subseteq
    constant
    (extract_Some
       (map
          (partial_interpret_reindexer
             reindexer
             (map Z.of_nat
                  (filter_until
                     (Z.to_nat (eval_Zexpr_Z_total $0 n) *
                        Z.to_nat (eval_Zexpr_Z_total $0 m)
                                 :: map Z.to_nat
                                 (map (eval_Zexpr_Z_total $0) l0)) 0)) v)
          (filter
             (fun x0 =>
                negb (is_None
                        (result_lookup_Z_option x0 (V (flatten_result l)))))
             (mesh_grid
                (map Z.of_nat
                     (filter_until
                        (Z.to_nat (eval_Zexpr_Z_total $0 n) *
                           Z.to_nat (eval_Zexpr_Z_total $0 m)
                                    :: map Z.to_nat
                                    (map (eval_Zexpr_Z_total $0) l0)) 0)))))).
Proof.
  intros ? ? ? ? ? ? Hsh Henv Hmap Hvarsub Hvarsarg HeqZlist.
  eapply subseteq_In. intros.
  rewrite <- In_iff_in in *.
  rewrite <- in_extract_Some in *.
  rewrite in_map_iff in *. invs.
  repeat decomp_index.
  eexists. split.
  rewrite eq_partial_interpret_reindexer_flatten; eauto.
  eapply filter_In. propositional.
  repeat decomp_goal_index.
  propositional. lia.
  rewrite Nat2Z.inj_mul.
  eapply mul_add_lt. lia. lia. lia. lia.
  rewrite <- H2.
  erewrite result_lookup_Z_option_flatten. reflexivity.
  lia. eassumption. eauto. lia. lia. eauto.
Qed.

Lemma well_formed_allocation_flatten :
  forall l st h p v reindexer n m xs,
    well_formed_allocation reindexer
                                   (V (flatten_result l)) st h p v ->
    result_has_shape (V l)
                     (Z.to_nat (eval_Zexpr_Z_total $0 n)
                               :: Z.to_nat (eval_Zexpr_Z_total $0 m)
                               :: map Z.to_nat
                               (map (eval_Zexpr_Z_total $0) xs)) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    (forall (var : var) (k : Z) (l0 : list (Zexpr * Zexpr)),
        ~ var \in vars_of_reindexer (reindexer []) ->
                  map (subst_var_in_Z_tup var k) (reindexer l0) =
                    reindexer (map (subst_var_in_Z_tup var k) l0)) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall l, vars_of_reindexer (reindexer l) =
                 vars_of_reindexer (reindexer []) \cup vars_of_reindexer l) ->
    (forall l3 l4 : list (Zexpr * Zexpr),
        eq_Z_tuple_index_list l3 l4 ->
        eq_Z_tuple_index_list (reindexer l3) (reindexer l4)) ->
    well_formed_allocation
      (fun l2 : list (Zexpr * Zexpr) =>
         reindexer
           match l2 with
           | [] => l2
           | [(v0, d)] => l2
           | (v0, d) :: (vi, di) :: xs => ((v0 * di + vi)%z, (d * di)%z) :: xs
           end) (V l) st h p v.
Proof.
  intros ? ? ? ? ? ? ? ? ? Halloc Hsh Henv Hmap Hvarsub Hvarsarg HeqZlist.
  unfold well_formed_allocation in *.
  simpl in *.
  cases (shape_to_index
           (result_shape_Z (V l))
           (shape_to_vars (result_shape_Z (V l)))).
  { eapply shape_to_index_not_empty_Z in Heq. propositional. }
  cases (reindexer
      (let (v0, d) := p0 in
       match l0 with
       | [] => p0 :: l0
       | (vi, di) :: xs0 => ((v0 * di + vi)%z, (d * di)%z) :: xs0
       end)).
  { unfold shape_to_index,shape_to_vars,result_shape_Z in Heq.
    simpl in Heq.
    cases l.
    - invert Heq. eapply reindexer_not_empty_vars_in_index in Heq0.
      propositional. auto. simpl.
      unfold not. intros.
      eapply cup_empty in H. invs.
      eapply cup_empty in H0. invs.
      eapply constant_not_empty in H. propositional. inversion 1.
    - simpl in Heq. 
      invert Heq. cases r.
      + simpl in *. eapply reindexer_not_empty_vars_in_index in Heq0.
        propositional. auto. simpl.
        unfold not. intros.
        eapply cup_empty in H. invs.
        eapply cup_empty in H0. invs.
        eapply constant_not_empty in H. propositional. inversion 1.
      + simpl in *. eapply reindexer_not_empty_vars_in_index in Heq0.
        propositional. auto. simpl.
        cases v0.
        * simpl in *. repeat rewrite constant_app_no_dups.
          unfold not. intros.
          eapply cup_empty in H. invs.
          eapply cup_empty in H0. invs.
          eapply cup_empty in H. invs.
          eapply cup_empty in H0. invs.
          eapply constant_not_empty in H. propositional. inversion 1.
        * simpl in *. repeat rewrite constant_app_no_dups.
          unfold not. intros.
          eapply cup_empty in H. invs.
          eapply cup_empty in H0. invs.
          eapply cup_empty in H. invs.
          eapply cup_empty in H0. invs.
          eapply constant_not_empty in H. propositional. inversion 1. }
  cases (reindexer
           (shape_to_index
              (result_shape_Z (V (flatten_result l)))
              (shape_to_vars (result_shape_Z (V (flatten_result l)))))).
  { eapply reindexer_not_empty_vars_in_index in Heq1. propositional. auto.
    erewrite result_has_shape_result_shape_Z.
    2: { eapply result_has_shape_flatten; eauto. }
    simpl.
    unfold shape_to_index, shape_to_vars, result_shape_Z. simpl.
    cases ((Z.to_nat (eval_Zexpr_Z_total $0 n) *
                Z.to_nat (eval_Zexpr_Z_total $0 m))).
    - simpl. unfold not. intros.
      apply cup_empty in H. invs.
      apply cup_empty in H0. invs.
      apply constant_not_empty in H2. propositional. inversion 1.
    - simpl. unfold not. intros.
      apply cup_empty in H. invs.
      apply cup_empty in H0. invs.
      apply constant_not_empty in H2. propositional. inversion 1. }
  invs.
  eexists. split. eassumption.
  eapply subseteq_transitivity. 2: eassumption.
  erewrite result_has_shape_result_shape_Z by eauto.
  erewrite result_has_shape_result_shape_Z.
  2: { eapply result_has_shape_flatten; eauto. }
  eapply constant_subseteq_flatten; eauto.
Qed.  

Lemma well_formed_allocation_padr :
  forall l m l0 k st h p v reindexer,
    result_has_shape (V l)
                     (map Z.to_nat (map (eval_Zexpr_Z_total $0) (m :: l0))) ->
    eq_zexpr k (| eval_Zexpr_Z_total $0 k |)%z ->
    (0 <= eval_Zexpr_Z_total $0 k)%Z ->
    well_formed_allocation
      reindexer
      (V
         (l ++
            repeat (gen_pad (map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)))
            (Z.to_nat (eval_Zexpr_Z_total $0 k)))) st h p v ->
    (forall l : list (Zexpr * Zexpr),
        vars_of_reindexer (reindexer l) =
          vars_of_reindexer (reindexer []) \cup vars_of_reindexer l) ->
    (forall var : var, contains_substring "?" var -> var \in dom v -> False)->
    (forall l4 l5 : list (Zexpr * Zexpr),
        eq_Z_tuple_index_list l4 l5 ->
        eq_Z_tuple_index_list (reindexer l4) (reindexer l5)) ->
    (vars_of_reindexer (reindexer []) \subseteq dom v) ->
    (forall (var : var) (k0 : Z) (l4 : list (Zexpr * Zexpr)),
        (var \in vars_of_reindexer (reindexer []) -> False) ->
        map (subst_var_in_Z_tup var k0) (reindexer l4) =
          reindexer (map (subst_var_in_Z_tup var k0) l4)) ->
    well_formed_allocation
      (fun l1 : list (Zexpr * Zexpr) =>
         reindexer match l1 with
                   | [] => l1
                   | (v0, d) :: xs => (v0, (d + k)%z) :: xs
                   end) (V l) st h p v.
Proof.
  intros ? ? ? ? ? ? ? ? ? Hsh Hk Hknonneg Halloc Hvarsarg Henv HeqZlist
         Hvarsub Hmap.
  unfold well_formed_allocation in *.
  simpl in *.
  cases (shape_to_index
           (result_shape_Z (V l))
           (shape_to_vars (result_shape_Z (V l)))).
  { eapply shape_to_index_not_empty_Z in Heq. propositional. }
  cases (reindexer (let (v0, d) := p0 in (v0, (d + k)%z) :: l1)).
  { unfold shape_to_index,shape_to_vars,result_shape_Z in Heq.
    simpl in Heq.
    cases l.
    - invert Heq. eapply reindexer_not_empty_vars_in_index in Heq0.
      propositional. auto. simpl. auto.
      unfold not. intros.
      eapply cup_empty in H. invs.
      eapply cup_empty in H0. invs.
      eapply constant_not_empty in H. propositional. inversion 1.
    - simpl in Heq. 
      invert Heq.
      eapply reindexer_not_empty_vars_in_index in Heq0.
      propositional. auto. simpl.
      repeat rewrite constant_app_no_dups.
      unfold not. intros.
      eapply cup_empty in H. invs.
      eapply cup_empty in H0. invs.
      eapply constant_not_empty in H. propositional. inversion 1. }
  cases (reindexer
           (shape_to_index
              (result_shape_Z
                 (V
                    (l ++
                       repeat
                       (gen_pad
                          (map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)))
                       (Z.to_nat (eval_Zexpr_Z_total $0 k)))))
              (shape_to_vars
                 (result_shape_Z
                    (V
                       (l ++
                          repeat
                          (gen_pad
                             (map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)))
                          (Z.to_nat (eval_Zexpr_Z_total $0 k)))))))).
  { eapply reindexer_not_empty_vars_in_index in Heq1. propositional. auto.
    erewrite result_has_shape_result_shape_Z.
    2: { eapply result_has_shape_concat. eauto.
         eapply result_has_shape_repeat_gen_pad. }
    simpl.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 m) +
             Z.to_nat (eval_Zexpr_Z_total $0 k)).
    - simpl. unfold not. intros.
      eapply cup_empty in H. invs.
      eapply cup_empty in H0. invs.
      eapply constant_not_empty in H2. propositional. inversion 1.
    - simpl. unfold not. intros.
      eapply cup_empty in H. invs.
      eapply cup_empty in H0. invs.
      eapply constant_not_empty in H2. propositional. inversion 1. }
  invs. eexists. split. eassumption.
  eapply subseteq_transitivity. 2: eassumption.
  rewrite filter_fun_pad_r.
  erewrite result_has_shape_result_shape_Z by eauto.
  erewrite result_has_shape_result_shape_Z.
  2: { eapply result_has_shape_concat. eauto.
       eapply result_has_shape_repeat_gen_pad. }
  eapply subseteq_In. propositional.
  erewrite <- In_iff_in in *.
  erewrite <- in_extract_Some in *.
  erewrite in_map_iff in *. invs.
  repeat decomp_index.
  eexists.
  erewrite <- eq_partial_interpret_reindexer_concat_l.
  split. eassumption.
  all: try eauto.
  eapply filter_In. propositional.
  repeat decomp_goal_index.
  propositional. lia.
  erewrite result_has_shape_result_shape_Z by eauto.
  eapply filter_In. propositional.
  repeat decomp_goal_index.
  propositional.
  eapply result_has_shape_repeat_gen_pad.
  rewrite Z2Nat.id by lia. auto.
Qed.  

Lemma well_formed_allocation_gen_pad :
  forall s st h p v sh reindexer,
    well_formed_allocation reindexer s st h p v ->
    result_has_shape s sh ->
    well_formed_allocation reindexer (gen_pad sh) st h p v.
Proof.
  intros. unfold well_formed_allocation in *.
  erewrite result_has_shape_result_shape_Z in * by eauto.
  erewrite result_has_shape_result_shape_Z.
  2: { eapply result_has_shape_gen_pad. }
  rewrite filter_negb_is_None_result_lookup_Z_option_gen_pad.
  simpl.
  cases (reindexer
           (shape_to_index
              (map Z.of_nat (filter_until sh 0))
              (shape_to_vars (map Z.of_nat (filter_until sh 0))))).
  eauto.
  invs. eexists. split. eassumption. sets.
Qed.

Lemma well_formed_allocation_same_add_stack :
  forall s st h p v reindexer val,
  well_formed_allocation reindexer s st h p v ->
  well_formed_allocation reindexer s (st $+ (p, val)) h p v.
Proof.
  intros. unfold well_formed_allocation in *.
  cases (reindexer
           (shape_to_index
              (result_shape_Z s) (shape_to_vars (result_shape_Z s)))).
  - invs. rewrite lookup_add_eq by auto. eexists. reflexivity.
  - invs. eexists. split. eauto. eauto.
Qed.

Lemma well_formed_allocation_split :
  forall reindexer st h p v k l0 l n,
    well_formed_allocation reindexer
             (V (split_result (Z.to_nat (eval_Zexpr_Z_total $0 k)) l)) st h p v ->
result_has_shape (V l)
          (Z.to_nat (eval_Zexpr_Z_total $0 n)
           :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)) ->
    (forall l0 : list (Zexpr * Zexpr),
        vars_of_reindexer (reindexer l0) =
          vars_of_reindexer (reindexer []) \cup vars_of_reindexer l0) ->
    (0 < eval_Zexpr_Z_total $0 k)%Z ->
    (0 <= eval_Zexpr_Z_total $0 n)%Z ->
    (forall (var : var) (k0 : Z) (l2 : list (Zexpr * Zexpr)),
        ~ var \in vars_of_reindexer (reindexer []) ->
                  map (subst_var_in_Z_tup var k0) (reindexer l2) =
                    reindexer (map (subst_var_in_Z_tup var k0) l2)) ->
    (eq_zexpr k (| eval_Zexpr_Z_total $0 k |)%z) ->
    (eq_zexpr n (| eval_Zexpr_Z_total $0 n |)%z) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall l2 l3 : list (Zexpr * Zexpr),
        eq_Z_tuple_index_list l2 l3 ->
        eq_Z_tuple_index_list (reindexer l2) (reindexer l3)) ->
well_formed_allocation
    (fun l2 : list (Zexpr * Zexpr) =>
     reindexer
       match l2 with
       | [] => l2
       | (v0, d) :: xs => ((v0 / k)%z, (d // k)%z) :: ((ZMod v0 k)%z, k) :: xs
       end) (V l) st h p v.
Proof.
  intros ? ? ? ? ? ? ? ? ? Halloc Hsh Hvarsub Hknonneg Hmnonneg Hmap Hkz Hm
         Henv Hvarsubdom HeqZlist.
  eapply well_formed_allocation_result_V in Halloc; eauto.
  invs. unfold well_formed_allocation.
  cases (shape_to_index
           (result_shape_Z (V l))
           (shape_to_vars (result_shape_Z (V l)))).
  { eapply shape_to_index_not_empty_Z in Heq. propositional. }
  cases (reindexer
           (let (v0,d):= p0 in ((v0/k)%z,(d // k)%z)::((ZMod v0 k)%z,k)::l1)).
  { eapply reindexer_not_empty_vars_in_index in Heq0.
    propositional. auto.
    unfold result_shape_Z,shape_to_index,shape_to_vars in Heq. simpl in *.
    cases l.
    - simpl in *. invert Heq. simpl.
      repeat rewrite constant_app_no_dups.
      unfold not. intros.
      eapply cup_empty in H. invs.
      eapply cup_empty in H2. invs.
      eapply cup_empty in H. invs.
      eapply constant_not_empty in H2. propositional.
      inversion 1.
    - simpl in *. invert Heq. simpl.
      repeat rewrite constant_app_no_dups.
      unfold not. intros.
      eapply cup_empty in H. invs.
      eapply cup_empty in H2. invs.
      eapply cup_empty in H. invs.
      eapply constant_not_empty in H2. propositional.
      inversion 1. }
  erewrite result_has_shape_result_shape_Z by eauto.
  erewrite result_has_shape_result_shape_Z in H1.
  2: { eapply result_has_shape_split_result. lia. eauto. }
  rewrite <- map_cons in H1.
  eexists. split. eauto.
  eapply subseteq_transitivity. 2: eassumption.
  eapply subseteq_In.
  propositional.
  - rewrite <- In_iff_in in *.
    erewrite <- in_extract_Some in *.
    erewrite in_map_iff in *. invs. 
    repeat decomp_index.
    rewrite <- H.
    repeat rewrite map_cons.
    erewrite eq_partial_interpret_reindexer_split.
    eexists ((z / eval_Zexpr_Z_total $0 k)%Z ::
                                          (z mod eval_Zexpr_Z_total $0 k)%Z :: x1).
    split.  
    rewrite Z2Nat_div_distr by lia. reflexivity.
    eapply filter_In. propositional.
    repeat decomp_goal_index.
    propositional.
    eapply Z.div_pos. lia. lia.
    rewrite <- Z2Nat_div_distr by lia.
    rewrite Z2Nat.id.
    2: { unfold div_ceil. eapply Z.div_pos. lia. lia. }
    eapply floor_lt_ceil_mono_l. lia. lia. lia. lia.
    repeat decomp_goal_index. propositional.
    eapply mod_nonneg. lia.
    rewrite Z2Nat.id by lia.
    eapply mod_upper_bound. lia.
    rewrite <- H4.
    f_equal. f_equal.
    rewrite <- (Z2Nat.id (eval_Zexpr_Z_total $0 k)) at 1 by lia.
    rewrite <- (Z2Nat.id (eval_Zexpr_Z_total $0 k)) at 2 by lia.
    erewrite result_lookup_Z_option_split. reflexivity.
    eauto. lia. eassumption. lia. rewrite Z2Nat.id by lia. eauto.
    eauto. eauto. eauto. eauto. eauto. eauto. lia. lia. eauto. lia.
Qed.

