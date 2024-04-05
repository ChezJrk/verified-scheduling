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
     Injective Constant InterpretReindexer.

Open Scope string_scope.

Definition partial_well_formed_reindexer
           (c : list (Zexpr * Zexpr) -> list (Zexpr * Zexpr))
           (v : valuation)
           (r : result)
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
                   vars_of_reindexer (c []) \cup vars_of_reindexer l).

Ltac decomp_partial_well_formed_reindexer :=
  match goal with
  | H : partial_well_formed_reindexer _ _ _ |- _ =>
      unfold partial_well_formed_reindexer in * ;
      inversion H as [ Hinj Hrest1 ]; clear H;
      inversion Hrest1 as [ HeqZlist Hrest2 ]; clear Hrest1;
      inversion Hrest2 as [ Hvarsub Hrest3 ]; clear Hrest2;
      inversion Hrest3 as [ Hmap Hvarsarg ]; clear Hrest3
  end.

Lemma partial_well_formed_reindexer_truncl :
  forall reindexer m l0 k v x,
    partial_well_formed_reindexer reindexer v (V x) ->
    result_has_shape
      (V (gen_pad_list
            (Z.to_nat (eval_Zexpr_Z_total $0 k)
                      :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)) ++ x))
      (map Z.to_nat (map (eval_Zexpr_Z_total $0) (m :: l0))) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    eq_zexpr k (| eval_Zexpr_Z_total $0 k |)%z ->
    (0 <= eval_Zexpr_Z_total $0 m)%Z ->
    (0 <= eval_Zexpr_Z_total $0 k)%Z ->
    partial_well_formed_reindexer
      (fun l : list (Zexpr * Zexpr) =>
         reindexer
           match l with
           | [] => l
           | (v0, d) :: xs => ((v0 - k)%z, (d - k)%z) :: xs
           end) v
      (V (gen_pad_list
            (Z.to_nat (eval_Zexpr_Z_total $0 k)
                      :: map Z.to_nat
                      (map (eval_Zexpr_Z_total $0) l0)) ++ x)) .
Proof.
  intros ? ? ? ? ? ? H Hsh Hvar Hk Hmnonneg Hknonneg.
  decomp_partial_well_formed_reindexer.
  propositional.
  - assert (0 < eval_Zexpr_Z_total $0 m - eval_Zexpr_Z_total $0 k \/
              eval_Zexpr_Z_total $0 m - eval_Zexpr_Z_total $0 k <= 0)%Z
      by lia.
    invert H.
    + erewrite result_has_shape_result_shape_Z; eauto.
      rewrite filter_pad_l_mesh_grid; eauto.
      eapply partial_injective_truncl.
      eauto.
      eassumption.
      auto. eauto.
      auto. auto. auto. auto. lia. lia. lia.
    + erewrite result_has_shape_result_shape_Z; eauto.
      rewrite filter_pad_l_mesh_grid; eauto.
      replace (Z.to_nat (eval_Zexpr_Z_total $0 m) -
                 Z.to_nat (eval_Zexpr_Z_total $0 k)) with 0 by lia.
      simpl filter.
      unfold partial_injective.
      propositional. invert H1.
  - eapply HeqZlist.
    cases l1; cases l2. eauto.
    invert H. simpl in *. lia.
    invert H. simpl in *. lia.
    erewrite <- eq_Z_tuple_index_list_cons in H. propositional.
    cases p. cases p0. 
    erewrite <- eq_Z_tuple_index_list_cons. propositional.
    unfold eq_Z_tup. simpl. propositional.
    eapply eq_zexpr_sub. apply H0. apply eq_zexpr_id. auto.
    eapply eq_zexpr_sub. apply H0. apply eq_zexpr_id. auto.
  - rewrite Hmap; auto.
    cases l. auto. cases p. simpl.
    unfold subst_var_in_Z_tup. simpl. f_equal. f_equal.
    rewrite (subst_var_in_Zexpr_id k). auto.
    invert Hk. rewrite H1. sets.
  - rewrite Hvarsarg.
    cases l. auto. cases p. simpl.
    invert Hk. rewrite H0. repeat rewrite constant_app_no_dups.
    sets.
Qed.

Lemma partial_well_formed_reindexer_padl :
  forall reindexer m l0 k v x0,
    partial_injective
      (partial_interpret_reindexer
         reindexer
         (result_shape_Z
            (V (repeat
                  (gen_pad
                     (map Z.to_nat
                          (map (eval_Zexpr_Z_total $0) l0)))
                  (Z.to_nat (eval_Zexpr_Z_total $0 k))
                  ++ x0))) v)
      (filter
         (fun x =>
            negb
              (is_None
                 (result_lookup_Z_option
                    x
                    (V (repeat
                          (gen_pad
                             (map Z.to_nat
                                  (map (eval_Zexpr_Z_total $0) l0)))
                          (Z.to_nat (eval_Zexpr_Z_total $0 k))
                          ++ x0)))))
         (mesh_grid
            (result_shape_Z
               (V (repeat
                     (gen_pad
                        (map Z.to_nat
                             (map (eval_Zexpr_Z_total $0) l0)))
                     (Z.to_nat (eval_Zexpr_Z_total $0 k))                     
                          ++ x0))))) ->
    result_has_shape
      (V x0) (Z.to_nat (eval_Zexpr_Z_total $0 m)
                       :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    eq_zexpr k (| eval_Zexpr_Z_total $0 k |)%z ->
    eq_zexpr m (| eval_Zexpr_Z_total $0 m |)%z ->
    (0 <= eval_Zexpr_Z_total $0 m)%Z ->
    (0 <= eval_Zexpr_Z_total $0 k)%Z ->
    (forall l1 l2 : list (Zexpr * Zexpr),
        eq_Z_tuple_index_list l1 l2 ->
        eq_Z_tuple_index_list (reindexer l1) (reindexer l2)) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall (var : var) (k0 : Z) (l : list (Zexpr * Zexpr)),
        ~ var \in vars_of_reindexer (reindexer []) ->
                  map (subst_var_in_Z_tup var k0) (reindexer l) =
                    reindexer (map (subst_var_in_Z_tup var k0) l)) ->
    (forall l : list (Zexpr * Zexpr),
        vars_of_reindexer (reindexer l) =
          vars_of_reindexer (reindexer []) \cup vars_of_reindexer l) ->
    partial_well_formed_reindexer
      (fun l : list (Zexpr * Zexpr) =>
         reindexer
           match l with
           | [] => l
           | (v0, d) :: xs => ((v0 + k)%z, (d + k)%z) :: xs
           end) v
      (V x0) .
Proof.
  intros ? ? ? ? ? ? H Hsh Hvar Hk Hm Hmnonneg Hknonneg HeqZlist Hvarsub Hmap
         Hvarsarg.
  unfold partial_well_formed_reindexer. propositional.
  - erewrite result_has_shape_result_shape_Z by eauto.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 m)).
    simpl. unfold partial_injective. propositional. invert H1.
    rewrite <- Heq in *. 
    eapply partial_injective_padl; eauto. lia.
  - eapply HeqZlist. pose proof H0.
    cases l1; cases l2; invert H0; simpl in *; try lia.
    eapply eq_Z_tuple_index_list_id.
    cases p. cases p0.
    erewrite <- eq_Z_tuple_index_list_cons.
    propositional.
    2: { erewrite <- eq_Z_tuple_index_list_cons in H1. propositional. }
    unfold eq_Z_tup. simpl. propositional.
    erewrite <- eq_Z_tuple_index_list_cons in H1. invs.
    eapply eq_zexpr_add. apply H3. eapply eq_zexpr_id. auto.
    erewrite <- eq_Z_tuple_index_list_cons in H1. invs.
    eapply eq_zexpr_add. apply H3. eapply eq_zexpr_id. auto.
  - rewrite Hmap by auto.
    cases l. reflexivity. cases p. simpl.
    unfold subst_var_in_Z_tup. f_equal. f_equal. simpl.
    rewrite (subst_var_in_Zexpr_id k). auto.
    invert Hk. rewrite H2. sets.
  - rewrite Hvarsarg. cases l. reflexivity.
    cases p. simpl.
    repeat rewrite constant_app_no_dups.
    invert Hk. rewrite H1. sets.
Qed.

Lemma partial_well_formed_reindexer_truncr :
  forall reindexer x m l0 k v,
    partial_well_formed_reindexer
      reindexer v
      (V
         (rev
            (truncl_list
               (Z.to_nat (eval_Zexpr_Z_total $0 k))
               (rev
                  (x ++
                     gen_pad_list
                     (Z.to_nat (eval_Zexpr_Z_total $0 k)
                               :: map Z.to_nat
                               (map (eval_Zexpr_Z_total $0) l0))))))) ->
    result_has_shape
      (V
         (x ++
            gen_pad_list
            (Z.to_nat (eval_Zexpr_Z_total $0 k)
                      :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0))))
      (Z.to_nat (eval_Zexpr_Z_total $0 m)
                :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)) ->    
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    eq_zexpr k (| eval_Zexpr_Z_total $0 k |)%z ->
    (0 <= eval_Zexpr_Z_total $0 m)%Z ->
    (0 <= eval_Zexpr_Z_total $0 k )%Z ->
    partial_well_formed_reindexer
      (fun l : list (Zexpr * Zexpr) =>
         reindexer match l with
                   | [] => l
                   | (v0, d) :: xs => (v0, (d - k)%z) :: xs
                   end) v
      (V
         (x ++
            gen_pad_list
            (Z.to_nat (eval_Zexpr_Z_total $0 k)
                      :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)))).
Proof.
  intros ? ? ? ? ? ? H Hsh Hvar Hk Hmnonneg Hknonneg.
  decomp_partial_well_formed_reindexer.
  propositional.
  - assert (0 < eval_Zexpr_Z_total $0 m - eval_Zexpr_Z_total $0 k \/
              eval_Zexpr_Z_total $0 m - eval_Zexpr_Z_total $0 k <= 0)%Z
      by lia.
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
    rewrite <-map_cons.
    rewrite <-map_cons.
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
    eauto. auto. auto. auto. auto. auto. auto. auto. auto.
    lia.
    simpl.
    replace (Z.to_nat (eval_Zexpr_Z_total $0 m)) with
      (Z.to_nat (eval_Zexpr_Z_total $0 k) +
         ((Z.to_nat (eval_Zexpr_Z_total $0 m) -
             (Z.to_nat (eval_Zexpr_Z_total $0 k))))) by lia.
    eapply result_has_shape_concat.
    eapply result_has_shape_repeat_gen_pad.
    eapply result_has_shape_app_r; eauto.
    simpl. rewrite repeat_length. auto.
    lia.
  - cases l1; cases l2; pose proof H; invert H; simpl in *; try lia.
    eapply HeqZlist. eapply eq_Z_tuple_index_list_id.
    cases p. cases p0.
    eapply HeqZlist.
    simpl.
    erewrite <- eq_Z_tuple_index_list_cons in *.
    propositional.
    unfold eq_Z_tup in *. simpl in H. propositional.
    simpl. eapply eq_zexpr_sub; auto.
  - rewrite Hmap by auto. cases l. reflexivity.
    cases p. simpl.
    unfold subst_var_in_Z_tup. simpl. f_equal.
    f_equal. rewrite (subst_var_in_Zexpr_id k).
    reflexivity. invert Hk. rewrite H1. sets.
  - rewrite Hvarsarg. cases l. reflexivity.
    cases p. simpl. rewrite constant_app_no_dups.
    invert Hk. rewrite H0. sets.
Qed.


Lemma partial_well_formed_reindexer_eval_cons0 :
  forall r1 r2 v reindexer ,
    partial_well_formed_reindexer reindexer v (V (r1 :: r2)) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    result_has_shape (V (r1 :: r2)) (result_shape_nat (V (r1 :: r2))) ->
    partial_well_formed_reindexer
      (fun l => reindexer
                  (((|0|)%z,(| Z.of_nat (Datatypes.S (length r2)) |)%z)::l))
      v r1.
Proof.
  intros. decomp_partial_well_formed_reindexer. propositional.
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
    unfold eq_Z_tup. simpl. propositional. auto. auto.
  - rewrite Hvarsarg.
    simpl. sets.
  - rewrite Hmap.
    simpl.
    unfold subst_var_in_Z_tup. simpl. reflexivity.
    intros. apply H.
    simpl. rewrite Hvarsarg. simpl. sets.
  - rewrite Hvarsarg. simpl.
    symmetry. rewrite Hvarsarg. simpl. sets.
Qed. 

Lemma partial_well_formed_reindexer_shift_top_dim_reindexer :
  forall x1 xs1 reindexer v,
    partial_well_formed_reindexer reindexer
                                  v (V (x1 :: xs1)) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    result_has_shape (V (x1 :: xs1)) (result_shape_nat (V (x1 :: xs1))) ->
    partial_well_formed_reindexer (shift_top_dim_reindexer reindexer) 
                          v (V xs1).
Proof. 
  intros. decomp_partial_well_formed_reindexer.
  unfold partial_well_formed_reindexer. 
  propositional.
  - cases xs1. simpl. unfold partial_injective.
    propositional. invert H.
    eapply partial_injective_shift_top_dim_reindexer; eauto.
    inversion 1.
  - cases l1; cases l2; simpl in *; pose proof H;
      try invert H; simpl in *; try lia.
    eapply HeqZlist. eauto.
    cases p. cases p0.
    eapply HeqZlist. simpl in *. 
    erewrite <- eq_Z_tuple_index_list_cons in *. invs.
    propositional.
    unfold eq_Z_tup in *. simpl in *. invs.
    propositional.
    eapply eq_zexpr_add; auto.
    eapply eq_zexpr_add; auto.
  - unfold shift_top_dim_reindexer. cases l. simpl.
    rewrite Hmap. reflexivity. auto.
    cases p. simpl. rewrite Hmap by auto.
    rewrite map_cons. reflexivity.
  - unfold shift_top_dim_reindexer.
    cases l. simpl. sets.
    cases p. simpl. rewrite Hvarsarg. simpl.
    repeat rewrite app_no_dups_empty_r. reflexivity.
Qed.

Lemma partial_well_formed_reindexer_eval0 : 
  forall x1 xs1 reindexer v i lo hi,
    partial_well_formed_reindexer reindexer v
                                  (V (x1 :: xs1)) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    result_has_shape (V (x1 :: xs1)) (result_shape_nat (V (x1 :: xs1))) ->
    ~ i \in dom v ->
    ~ In i (shape_to_vars (result_shape_Z x1)) ->
    (eval_Zexpr_Z_total $0 hi - eval_Zexpr_Z_total $0 lo)%Z =
      Z.of_nat (Datatypes.length (x1 :: xs1)) ->
    eq_zexpr lo (|eval_Zexpr_Z_total $0 lo|)%z ->
    eq_zexpr hi (|eval_Zexpr_Z_total $0 hi|)%z ->
    partial_well_formed_reindexer
      (fun l0 : list (Zexpr * Zexpr) =>
         reindexer (((! i ! - lo)%z,
                      (hi - lo)%z) :: l0))
      (v $+ (i, eval_Zexpr_Z_total $0 lo)) x1.
Proof.
  intros. decomp_partial_well_formed_reindexer. propositional.
  - eapply partial_injective_cons_reindexer; eauto.
  - eapply HeqZlist. 
    erewrite <- eq_Z_tuple_index_list_cons in *. propositional.
    unfold eq_Z_tup. simpl. propositional.
    eauto. eauto.
  - rewrite dom_add. rewrite Hvarsarg.
    simpl. rewrite cup_empty_r.
    repeat rewrite constant_app_no_dups.
    invert H5. rewrite H7. invert H6. rewrite H8.
    simpl. sets.
  - rewrite Hmap. simpl.
    unfold subst_var_in_Z_tup at 1. simpl.
    rewrite Hvarsarg in H. simpl in H.
    repeat rewrite constant_app_no_dups in H.
    rewrite cup_empty_r in H.
    cases (i ==v var). sets.
    rewrite subst_var_in_Zexpr_id by sets.
    rewrite subst_var_in_Zexpr_id by sets.
    reflexivity.
    rewrite Hvarsarg in H. simpl in *. sets.
  - rewrite Hvarsarg.
    symmetry.
    rewrite Hvarsarg.
    symmetry.
    simpl. repeat rewrite cup_empty_r. sets.
Qed.

Lemma partial_well_formed_reindexer_add_valuation : forall reindexer sh v i x,
    partial_well_formed_reindexer reindexer v sh ->
    ~ i \in dom v ->
    ~ contains_substring "?" i ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    partial_well_formed_reindexer reindexer (v $+ (i, x)) sh.
Proof.
  unfold partial_well_formed_reindexer. propositional.
  - unfold partial_injective in *. propositional.
    unfold partial_interpret_reindexer in *.
    rewrite @partially_eval_Z_tup_add_partial in * by auto.
    replace (fun e : Zexpr * Zexpr =>
               subst_var_in_Z_tup i x (partially_eval_Z_tup v e)) with
      (fun e : Zexpr * Zexpr =>
         partially_eval_Z_tup v (subst_var_in_Z_tup i x e)) in *.
    2: { eapply functional_extensionality. intros.
         rewrite subst_var_in_Z_tup_partially_eval_Z_tup_comm. auto.
         auto. }
    rewrite <- map_map with (f:=subst_var_in_Z_tup i x) in *.
    rewrite H5 in *; eauto with reindexers.
    2: { intros. eapply H0. eapply H4. sets. }
    2: { intros. eapply H0. eapply H4. sets. }
    rewrite map_subst_var_in_Zexpr_shape_to_index_id in *.
    2: { unfold not. intros. eapply shape_to_vars_contains_substring in H10.
         propositional. }
    2: { unfold not. intros. eapply shape_to_vars_contains_substring in H10.
         propositional. }
    eauto.
  - rewrite dom_add.
    sets.
Qed.

Lemma partial_well_formed_reindexer_id : forall v r,
    (forall var : var, contains_substring "?" var ->
                       var \in dom v -> False) ->    
    partial_well_formed_reindexer (fun l : list (Zexpr * Zexpr) => l) v r.
Proof.  
  unfold partial_well_formed_reindexer. propositional.
  - eapply partial_injective_id_reindexer. auto.
  - sets.
  - sets.
Qed.

Lemma partial_well_formed_reindexer_transpose :
  forall l n0 m0 l0 v reindexer,
  result_has_shape (V l)
                   (Z.to_nat
                      (eval_Zexpr_Z_total $0 n0)
                      :: Z.to_nat (eval_Zexpr_Z_total $0 m0)
                      :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)) ->
  partial_well_formed_reindexer
    reindexer v
    (transpose_result l
                      (Z.to_nat
                         (eval_Zexpr_Z_total $0 m0)
                         :: Z.to_nat (eval_Zexpr_Z_total $0 n0)
                         :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0))) ->
  (forall var : var, contains_substring "?" var -> var \in dom v -> False) -> 
  partial_well_formed_reindexer
    (fun l1 : list (Zexpr * Zexpr) =>
     reindexer
       match l1 with
       | [] => l1
       | [(v0, d)] => l1
       | (v0, d) :: (vi, di) :: xs => (vi, di) :: (v0, d) :: xs
       end) v (V l).
Proof.
  intros ? ? ? ? ? ? Hsh Hrdx Henv.
  decomp_partial_well_formed_reindexer. propositional.
  - eapply partial_injective_transpose; eauto.
  - eapply HeqZlist.
    cases l1; cases l2.
    eapply eq_Z_tuple_index_list_id.
    invert H. simpl in *. lia.
    invert H. simpl in *. lia.
    cases p. cases p0.
    erewrite <- eq_Z_tuple_index_list_cons in H. invs.
    cases l1; cases l2.
    simpl.
    erewrite <- eq_Z_tuple_index_list_cons.
    propositional.
    invert H1. simpl in *. lia.
    invert H1. simpl in *. lia.
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
Qed.

Lemma partial_well_formed_reindexer_concat_l :
  forall reindexer l1 l2 v e xs n m,
    partial_well_formed_reindexer
      reindexer v (V (l1 ++ l2)) ->
    result_has_shape (V l1) (n::xs) ->
    result_has_shape (V l2) (m::xs) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    eq_zexpr e (| Z.of_nat m |)%z ->
    partial_well_formed_reindexer
      (fun l3 : list (Zexpr * Zexpr) =>
         reindexer
         match l3 with
         | [] => l3
         | (v0, d) :: xs => ((v0, (d + e)%z) :: xs)
         end) v (V l1).
Proof.
  intros.
  decomp_partial_well_formed_reindexer.
  propositional.
  - erewrite result_has_shape_result_shape_Z by eauto.
    eapply partial_injective_concat_l; eauto.
  - cases l0; cases l3.
    eapply HeqZlist. auto.
    invert H. simpl in *. lia.
    invert H. simpl in *. lia.
    cases p. cases p0.
    erewrite <- eq_Z_tuple_index_list_cons_tup in H.
    eapply HeqZlist.
    erewrite <- eq_Z_tuple_index_list_cons_tup.
    propositional. eapply eq_zexpr_add; auto.
  - cases l.
    simpl. rewrite Hmap by auto. reflexivity.
    cases p.
    simpl. rewrite Hmap by auto.
    simpl. f_equal. f_equal.
    unfold subst_var_in_Z_tup. simpl.
    rewrite (subst_var_in_Zexpr_id e).
    reflexivity.
    unfold eq_zexpr in *. simpl in *. invs. rewrite H5. sets.
  - cases l.
    rewrite Hvarsarg. sets.
    cases p.
    rewrite Hvarsarg. f_equal.
    simpl.
    unfold eq_zexpr in *. simpl in *. invs. rewrite H4.
    rewrite app_no_dups_empty_r. 
    sets.
Qed.

Lemma partial_well_formed_reindexer_concat_r :
  forall reindexer l1 l2 v n m l0,
    partial_well_formed_reindexer
      reindexer v (V (l1 ++ l2)) ->
    result_has_shape (V l1) (Z.to_nat (eval_Zexpr_Z_total $0 n)
            :: map Z.to_nat
                 (map (eval_Zexpr_Z_total $0) l0)) ->
    result_has_shape (V l2) (Z.to_nat (eval_Zexpr_Z_total $0 m)
            :: map Z.to_nat
                 (map (eval_Zexpr_Z_total $0) l0)) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    eq_zexpr n (| eval_Zexpr_Z_total $0 n |)%z ->
    (0 <= eval_Zexpr_Z_total $0 n)%Z ->
    partial_well_formed_reindexer
      (fun l3 : list (Zexpr * Zexpr) =>
         reindexer
         match l3 with
         | [] => l3
         | (v0, d) :: xs => (((v0 + n)%z, (d + n)%z) :: xs)
         end) v (V l2).
Proof.
  intros.
  decomp_partial_well_formed_reindexer.
  propositional.
  - erewrite result_has_shape_result_shape_Z by eauto.    
    eapply partial_injective_concat_r; eauto.
  - cases l3; cases l4.
    eapply HeqZlist. auto.
    invert H. simpl in *. lia.
    invert H. simpl in *. lia.
    cases p. cases p0.
    erewrite <- eq_Z_tuple_index_list_cons_tup in H.
    eapply HeqZlist.
    erewrite <- eq_Z_tuple_index_list_cons_tup.
    propositional. eapply eq_zexpr_add; auto.
    eapply eq_zexpr_add; auto.
  - cases l.
    simpl. rewrite Hmap by auto. reflexivity.
    cases p.
    simpl. rewrite Hmap by auto.
    simpl. f_equal. f_equal.
    unfold subst_var_in_Z_tup. simpl.
    rewrite (subst_var_in_Zexpr_id n).
    reflexivity.
    invert H3. rewrite H6. sets.
  - cases l.
    rewrite Hvarsarg. sets.
    cases p.
    rewrite Hvarsarg. f_equal.
    simpl.
    unfold eq_zexpr in *. simpl in *. invs. rewrite H5.
    repeat rewrite app_no_dups_empty_r. 
    sets.
Qed.

Lemma partial_well_formed_reindexer_flatten :
  forall v l n m l0 reindexer,
    result_has_shape (V l)
                     (Z.to_nat (eval_Zexpr_Z_total $0 n)
                               :: Z.to_nat (eval_Zexpr_Z_total $0 m)
                               :: map Z.to_nat
                               (map (eval_Zexpr_Z_total $0) l0)) ->
    partial_well_formed_reindexer reindexer v (V (flatten_result l)) ->
    (forall var : var, contains_substring "?" var -> var \in dom v -> False)->
    partial_well_formed_reindexer
      (fun l2 : list (Zexpr * Zexpr) =>
         reindexer
           match l2 with
           | [] => l2
           | [(v0, d)] => l2
           | (v0, d) :: (vi, di) :: xs =>
               ((v0 * di + vi)%z, (d * di)%z) :: xs
           end) v (V l).
Proof.
  intros ? ? ? ? ? ? Hsh Hrdx Henv.
  decomp_partial_well_formed_reindexer. propositional.
  - erewrite result_has_shape_result_shape_Z by eauto.
    eapply partial_injective_flatten; eauto.
    erewrite result_has_shape_result_shape_Z in Hinj.
    2: { eapply result_has_shape_flatten; eauto. }
    eauto.
  - eapply HeqZlist.
    cases l1; cases l2.
    eapply eq_Z_tuple_index_list_id.
    invert H. simpl in *. lia.
    invert H. simpl in *. lia.
    erewrite <- eq_Z_tuple_index_list_cons in H. propositional.
    cases p. cases p0.
    cases l1; cases l2.    
    erewrite <- eq_Z_tuple_index_list_cons. propositional.
    invert H1. simpl in *. lia.
    invert H1. simpl in *. lia.
    cases p. cases p0.
    erewrite <- eq_Z_tuple_index_list_cons. propositional.
    unfold eq_Z_tup in *. propositional. simpl in *.
    erewrite <- eq_Z_tuple_index_list_cons_tup in H1. propositional.
    eapply eq_zexpr_add; auto.
    eapply eq_zexpr_mul; auto.
    simpl.
    eapply eq_zexpr_mul; auto.
    erewrite <- eq_Z_tuple_index_list_cons_tup in H1. propositional.
    erewrite <- eq_Z_tuple_index_list_cons_tup in H1. propositional.
  - rewrite Hmap by eauto. cases l1.
    reflexivity.
    cases p. simpl. cases l1. reflexivity.
    cases p. simpl. reflexivity.
  - rewrite Hvarsarg.
    cases l1. auto.
    cases p. cases l1. auto.
    cases p. simpl. repeat rewrite constant_app_no_dups. sets.
Qed.    

Lemma partial_well_formed_reindexer_padr :
  forall l m l0 v reindexer k,
    result_has_shape (V l)
                     (map Z.to_nat (map (eval_Zexpr_Z_total $0) (m :: l0))) ->
    partial_well_formed_reindexer
      reindexer v
      (V
         (l ++
            repeat (gen_pad (map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)))
            (Z.to_nat (eval_Zexpr_Z_total $0 k)))) ->
    eq_zexpr k (| eval_Zexpr_Z_total $0 k|)%z ->
    (0 <= eval_Zexpr_Z_total $0 k)%Z ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    partial_well_formed_reindexer
      (fun l1 : list (Zexpr * Zexpr) =>
         reindexer match l1 with
                   | [] => l1
                   | (v0, d) :: xs => (v0, (d + k)%z) :: xs
                   end) v (V l).
Proof.
  intros ? ? ? ? ? ? Hsh Hrdx Hk Hkpos Henv.
  decomp_partial_well_formed_reindexer. propositional.
  - erewrite result_has_shape_result_shape_Z by eauto.
    pose proof Hinj.
    rewrite map_cons.
    rewrite map_cons.
    eapply partial_injective_concat_l; auto; try apply Henv.
    apply Hinj.
    eapply result_has_shape_repeat_gen_pad.
    rewrite Z2Nat.id by lia. auto.
  - eapply HeqZlist.
    cases l1; cases l2.
    apply eq_Z_tuple_index_list_id.
    invert H. simpl in *. lia.
    invert H. simpl in *. lia.
    cases p. cases p0.
    erewrite <- eq_Z_tuple_index_list_cons_tup in H. propositional.
    erewrite <- eq_Z_tuple_index_list_cons_tup. propositional.
    eapply eq_zexpr_add; auto.
  - rewrite Hmap by auto.
    cases l1. auto.
    cases p. simpl.
    f_equal. f_equal. unfold subst_var_in_Z_tup. simpl.
    rewrite (subst_var_in_Zexpr_id k). auto.
    invert Hk. rewrite H1. sets.
  - rewrite Hvarsarg. cases l1. auto.
    cases p. simpl.
    repeat rewrite constant_app_no_dups.
    invert Hk. rewrite H0. sets.
Qed.  

Lemma partial_well_formed_reindexer_gen_pad : forall reindexer sh v s,
    partial_well_formed_reindexer reindexer v s ->
    partial_well_formed_reindexer reindexer v (gen_pad sh).
Proof.
  intros. decomp_partial_well_formed_reindexer.
  propositional.
  rewrite filter_negb_is_None_result_lookup_Z_option_gen_pad.
  unfold partial_injective. intros. simpl in *. propositional.
Qed.

Lemma partial_interpret_reindexer_add_valuation :
  forall reindexer i v sh val s,
    (i \in dom v -> False) ->
    ~ contains_substring "?" i ->
  partial_well_formed_reindexer reindexer v s ->
  partial_interpret_reindexer reindexer sh (v $+ (i, val)) =
  partial_interpret_reindexer reindexer sh v.
Proof.
  intros. decomp_partial_well_formed_reindexer.
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

Lemma partial_well_formed_reindexer_split :
  forall reindexer l0 k v l n,
partial_well_formed_reindexer reindexer v
           (V (split_result (Z.to_nat (eval_Zexpr_Z_total $0 k)) l)) ->
result_has_shape (V l)
          (Z.to_nat (eval_Zexpr_Z_total $0 n)
           :: map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    eq_zexpr k (| eval_Zexpr_Z_total $0 k |)%z ->
    (0 <= eval_Zexpr_Z_total $0 n)%Z ->
    (0 < eval_Zexpr_Z_total $0 k)%Z ->
    partial_well_formed_reindexer
    (fun l2 : list (Zexpr * Zexpr) =>
     reindexer
       match l2 with
       | [] => l2
       | (v0, d) :: xs => ((v0 / k)%z, (d // k)%z) :: ((ZMod v0 k)%z, k) :: xs
       end) v (V l) .
Proof.
  intros ? ? ? ? ? ? H Hsh Hvar Hk Hnnonneg Hknonneg.
  decomp_partial_well_formed_reindexer.
  propositional.
  - eapply partial_injective_split; eauto.
  - eapply HeqZlist.
    cases l1; cases l2. eauto.
    invert H. simpl in *. lia.
    invert H. simpl in *. lia.
    erewrite <- eq_Z_tuple_index_list_cons in H. propositional.
    cases p. cases p0. 
    erewrite <- eq_Z_tuple_index_list_cons. propositional.
    unfold eq_Z_tup. simpl. propositional.
    eapply eq_zexpr_div. apply H0. apply eq_zexpr_id. auto.
    eapply eq_zexpr_divc. apply H0. apply eq_zexpr_id. auto.
    erewrite <- eq_Z_tuple_index_list_cons. propositional.
    unfold eq_Z_tup. simpl. propositional.
    eapply eq_zexpr_mod. apply H0. apply eq_zexpr_id. auto.
    apply eq_zexpr_id. auto.
  - rewrite Hmap; auto.
    cases l1. auto. cases p. simpl.
    unfold subst_var_in_Z_tup. simpl. f_equal. f_equal.
    rewrite (subst_var_in_Zexpr_id k). auto.
    invert Hk. rewrite H1. sets.
    f_equal. rewrite (subst_var_in_Zexpr_id k). auto.
    invert Hk. rewrite H1. sets.
  - rewrite Hvarsarg.
    cases l1. auto. cases p. simpl.
    invert Hk. rewrite H0. repeat rewrite constant_app_no_dups.
    sets.
Qed.

