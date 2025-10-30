From Stdlib Require Import ZArith.Zdiv.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.

Import ListNotations.

From ATL Require Import FrapWithoutSets Var Div.
From Lower Require Import Array Range Constant ListMisc Zexpr
     Meshgrid Result InterpretReindexer VarGeneration.

Definition injective {X Y} domain (f : X -> Y) :=
  forall args1 args2, In args1 domain /\ In args2 domain /\
                        f args1 = f args2 -> args1 = args2.

Definition partial_injective {X Y} (f : X -> option Y) dom :=
  forall args1 args2,
    In args1 dom ->
    In args2 dom ->
    f args1 = f args2 ->
    (args1 = args2) \/ (f args1 = None).

Lemma partial_injective_cons {X Y} : forall domain (f : X -> option Y) a,
    partial_injective f (a::domain) ->
    partial_injective f domain.
Proof.
  unfold partial_injective. propositional.
  eapply H in H2; eauto. simpl. propositional. simpl. propositional.
Qed.

Lemma partial_injective_cons_0 {X} : forall (f : list Z -> option X) r r0,
  partial_injective
    f
    (filter (fun x => negb (is_None (result_lookup_Z_option x (V (r :: r0)))))
            (mesh_grid (result_shape_Z (V (r::r0))))) ->
  partial_injective
    (fun index => f (0%Z :: index))
    (filter (fun x0 : list Z => negb (is_None (result_lookup_Z_option x0 r)))
            (mesh_grid (result_shape_Z r))).
Proof.
  unfold partial_injective. propositional.
  eapply H in H2. propositional. invert H3. propositional.
  eapply filter_In.
  repeat decomp_index.
  simpl result_lookup_Z_option. propositional.
  unfold result_shape_Z. simpl map. decomp_goal_index.
  propositional. lia. lia.
  eapply filter_In.
  repeat decomp_index.
  simpl result_lookup_Z_option. propositional.
  unfold result_shape_Z. simpl map. decomp_goal_index.
  propositional. lia. lia.
Qed.

Lemma partial_injective_app_l {X Y} : forall (f : X -> option Y) dom1 dom2,
  partial_injective f (dom1 ++ dom2) ->
  partial_injective f dom1.
Proof.
  unfold partial_injective. propositional.
  eapply H in H2. propositional.
  eapply in_or_app. propositional.
  eapply in_or_app. propositional.
Qed.

Lemma partial_injective_app_r {X Y} : forall (f : X -> option Y) dom1 dom2,
  partial_injective f (dom1 ++ dom2) ->
  partial_injective f dom2.
Proof.
  unfold partial_injective. propositional.
  eapply H in H2. propositional.
  eapply in_or_app. propositional.
  eapply in_or_app. propositional.
Qed.

Fixpoint list_vars_of_index (idx : list (_ * Z)) :=
  match idx with
  | (a,b)::idx' => vars_of_Zexpr a ++/ list_vars_of_index idx'
  | _ => []
  end.    

Lemma list_vars_of_index_empty_map_partially_eval_Z_tup_id : forall l v,
    list_vars_of_index l = [] ->
    map (partially_eval_Z_tup v) l = l.
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. simpl in *. cases a.
    eapply app_no_dups_empty_args in H. invert H.
    unfold partially_eval_Z_tup at 1. simpl.
    rewrite partially_eval_Zexpr_no_vars by eauto.
    f_equal. eauto.
Qed.

Lemma no_dup_list_vars_of_index : forall l,
    no_dup (list_vars_of_index l).
Proof.
  induct l; intros.
  - econstructor.
  - simpl. cases a.
    eapply no_dup_app_no_dups.
    eapply vars_of_Zexpr_no_dups. eauto.
Qed.

Lemma zexpr_dec : forall (z1 z2 : Zexpr), {z1 = z2} + {z1 <> z2}.
Proof. intros. decide equality. eapply Z_as_Int.eq_dec. eapply var_eq. Qed.  
    
Lemma list_vars_of_index_subst_var_in_Z_tup : forall l a z,
    list_vars_of_index (map (subst_var_in_Z_tup a z) l) =
      filter (fun x => negb (x =? a)) (list_vars_of_index l).
Proof.
  induct l ;intros.
  - reflexivity.
  - simpl. cases a. simpl.
    repeat rewrite filter_app_no_dups.
    repeat rewrite vars_of_Zexpr_subst_var_in_Zexpr.
    f_equal. eauto.
Qed.

Lemma filter_ext_weak :
  forall [A : Type] (f g : A -> bool), forall l,
  (forall a : A, In a l -> f a = g a) -> filter f l = filter g l.
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. pose proof (H a). simpl in *.
    rewrite H by auto.
    cases (g a). f_equal. eauto. eauto.
Qed.

Lemma partially_eval_Z_tup_subst_var_in_Zexpr_remove :
  forall v a z,
    v $? a = Some z ->
    (fun x : Zexpr * Z => partially_eval_Z_tup (v $- a) (subst_var_in_Z_tup a z x)) =
      partially_eval_Z_tup v.
Proof.
  intros. eapply functional_extensionality. intros.
  erewrite <- subst_var_in_Z_tup_partially_eval_Z_tup_comm.
  2: { rewrite dom_remove. sets. }
  rewrite <- partially_eval_Z_tup_add.
  2: { rewrite dom_remove. sets. }
  f_equal.
  eapply fmap_ext. intros.
  cases (k =? a).
  - eapply String.eqb_eq in Heq. subst. rewrite lookup_add_eq. auto. auto.
  - eapply String.eqb_neq in Heq. rewrite lookup_add_ne by auto.
    rewrite lookup_remove_ne by auto. auto.
Qed.

Lemma map_subst_var_in_Z_tup_idemp : forall l z a,
    map (subst_var_in_Z_tup a z) (map (subst_var_in_Z_tup a z) l) =
      (map (subst_var_in_Z_tup a z) l).
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. f_equal. 2: eauto.
    rewrite subst_var_in_Z_tup_id. reflexivity.
    unfold subst_var_in_Z_tup. simpl.
    rewrite vars_of_Zexpr_subst_var_in_Zexpr.
    unfold not. intros. eapply filter_In in H.
    rewrite String.eqb_refl in H. simpl in *. invert H. discriminate.
Qed.

Lemma eq_partial_interpret_reindexer_split :
  forall reindexer k n l0 z0 v args1,
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
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
    (0 < k)%Z ->
    In args1
       (mesh_grid (map Z.of_nat l0)) ->
    (0 <= z0 < Z.of_nat n)%Z ->
partial_interpret_reindexer
         (fun l2 : list (Zexpr * Z) =>
          reindexer
            match l2 with
            | [] => l2
            | (v0, d) :: xs => ((v0 / | k |)%z, d // k) :: ((v0 % | k |)%z, k) :: xs
            end)
         (map Z.of_nat
            (filter_until (n :: l0) 0)) v
         (z0 :: args1) =
      partial_interpret_reindexer
        reindexer
        (map Z.of_nat
             (filter_until
                (n //n (Z.to_nat k) :: Z.to_nat k :: l0) 0)) v 
        ((z0 / k)%Z :: (Stdlib.ZArith.BinIntDef.Z.modulo z0 k) :: args1).
Proof.
  intros ? ? ? ? ? ? ? Hvar HeqZlistwrap Hvarsub Hmap
         Hvarrdx Hknonneg Harg Hle.
  unfold partial_interpret_reindexer.
  unfold shape_to_vars in *. simpl.
  cases n.
  { lia. }
  cases (Datatypes.S n //n (Z.to_nat k)).
  { exfalso. unfold div_ceil_n in Heq. simpl in *. rewrite Nat.sub_0_r in *.
    replace (Z.to_nat k) with (1*Z.to_nat k) in Heq at 1 by lia.
    rewrite Nat.add_comm in Heq.
    rewrite Nat.div_add_l in Heq by lia. lia.
  }
  simpl. 
  cases (Z.to_nat k). lia.
  simpl. posnats.
  repeat rewrite shape_to_index_cons.
  posnats. simpl.
  repeat rewrite index_to_partial_function_vars_cons; eauto with reindexers.
  repeat rewrite Hmap; eauto with reindexers.
  repeat rewrite map_cons.
  repeat rewrite map_subst_var_in_Zexpr_shape_to_index_id;
    eauto with reindexers.
  repeat rewrite map_subst_var_in_Z_tup_combine_not_in; eauto with reindexers.
  unfold subst_var_in_Z_tup. simpl.
  erewrite index_to_partial_function_subst_vars.
  2: { eauto with reindexers. }
  2: { rewrite length_map. rewrite length_map. 
       rewrite length_nat_range_rec.
       rewrite <- mesh_grid_filter_until in Harg.
       eapply length_mesh_grid_indices_Z in Harg.
       rewrite length_map in Harg. lia. }
  symmetry.
  erewrite index_to_partial_function_subst_vars.
  2: { eauto with reindexers. }
  2: { rewrite length_map. rewrite length_map. 
       rewrite length_nat_range_rec.
       rewrite <- mesh_grid_filter_until in Harg.
       eapply length_mesh_grid_indices_Z in Harg.
       rewrite length_map in Harg. lia. }
  symmetry.
  rewrite map_fold_left_subst_var_in_Z_tup_reindexer.
  2: { eauto. }
  2: { eauto with reindexers. }
  symmetry.
  rewrite map_fold_left_subst_var_in_Z_tup_reindexer.
  2: { eauto. }
  2: { eauto with reindexers. }
  symmetry.
  simpl.
  repeat rewrite fold_left_subst_var_in_Z_tup_ZLit.
  rewrite fold_left_subst_var_in_Z_tup_id by reflexivity.
  rewrite fold_left_subst_var_in_Z_tup_id by reflexivity.
  rewrite map_fold_left_subst_var_in_Z_tup_shape_to_index.
  2: { rewrite length_map. rewrite length_map. 
       rewrite length_nat_range_rec.
       rewrite <- mesh_grid_filter_until in Harg.
       eapply length_mesh_grid_indices_Z in Harg.
       rewrite length_map in Harg. lia. }
  2: { eauto with reindexers. }
  symmetry.
  rewrite map_fold_left_subst_var_in_Z_tup_combine.
  2: { rewrite length_map. rewrite length_map. 
       rewrite length_nat_range_rec.
       rewrite <- mesh_grid_filter_until in Harg.
       eapply length_mesh_grid_indices_Z in Harg.
       rewrite length_map in Harg. lia. }
  2: { eauto with reindexers. }
  erewrite eq_index_to_partial_function. reflexivity.
  eapply eq_Z_tuple_index_list_partially_eval_Z_tup.
  eapply HeqZlistwrap.
  erewrite <- eq_Z_tuple_index_list_cons.
  split.
  unfold eq_Z_tup. simpl.
  split. eapply eq_zexpr_comm.
  apply eq_zexpr_div_literal. 
  posnats. rewrite <- Heq.
  rewrite <- of_nat_div_distr.
  f_equal. lia.
  erewrite <- eq_Z_tuple_index_list_cons.
  split.
  2: { eapply eq_Z_tuple_index_list_id. }
  unfold eq_Z_tup. simpl. split.
  eapply eq_zexpr_comm. eapply eq_zexpr_mod_literal.
  posnats. lia.
Qed.

Lemma eq_partial_interpret_reindexer_shift_top_dim_reindexer :
  forall reindexer r r0 v args1 z1,
    result_has_shape (V (r :: r0)) (result_shape_nat (V (r :: r0))) ->
    partial_injective
      (partial_interpret_reindexer
         reindexer (result_shape_Z (V (r :: r0))) v)
      (filter
         (fun x =>
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
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    r0 <> [] ->
    partial_interpret_reindexer
      (shift_top_dim_reindexer reindexer)
      (map Z.of_nat
           (filter_until (Datatypes.length r0 :: result_shape_nat r) 0)) v
      (z1 :: args1) =
      partial_interpret_reindexer
        reindexer
        (map Z.of_nat (filter_until (result_shape_nat (V (r :: r0))) 0)) v
        ((z1 + 1)%Z :: args1).
Proof.
  intros.
  unfold partial_interpret_reindexer.
  unfold shape_to_vars. simpl.
  cases r0.
  { propositional. }
  simpl in *.
  rewrite index_to_partial_function_vars_cons; eauto with reindexers.
  symmetry.
  rewrite index_to_partial_function_vars_cons; eauto with reindexers.
  symmetry.
  rewrite H3; eauto with reindexers.
  symmetry.
  rewrite H3; eauto with reindexers.
  symmetry.
  simpl.
  rewrite map_subst_var_in_Z_tup_combine_not_in by eauto with reindexers.
  rewrite map_subst_var_in_Z_tup_combine_not_in by eauto with reindexers.
  unfold subst_var_in_Z_tup. simpl.
  erewrite eq_index_to_partial_function. reflexivity.
  eapply eq_Z_tuple_index_list_partially_eval_Z_tup.
  eapply H1.
  erewrite <- eq_Z_tuple_index_list_cons.
  split.
  2: eapply eq_Z_tuple_index_list_id.
  unfold eq_Z_tup. simpl. propositional.
  eapply eq_zexpr_add_literal. f_equal. lia.
Qed.

Lemma eq_partial_interpret_reindexer_padl :
  forall reindexer k m l0 z v x1,
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
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
    (0 < m)%nat ->
    (0 <= k)%Z ->
    partial_interpret_reindexer
      (fun l : list (Zexpr * Z) =>
         reindexer
           match l with
           | [] => l
           | (v0, d) :: xs => ((v0 + | k |)%z, (d + k)%Z) :: xs
           end)
      (map Z.of_nat (filter_until (m :: l0) 0)) v (z :: x1) =
      partial_interpret_reindexer
        reindexer
        (map Z.of_nat
             (filter_until
                (Z.to_nat k + m :: l0) 0)) v 
        ((z + k)%Z :: x1).
Proof.
  intros ? ? ? ? ? ? ? Hvar HeqZlistwrap Hvarsub Hmap
         Hvarrdx Hmnonneg Hknonneg.
  unfold partial_interpret_reindexer.
  unfold shape_to_vars in *. simpl.
  cases m. lia.
  simpl.
  rewrite Nat.add_succ_r in *.
  simpl shape_to_index at 1.
  rewrite shape_to_index_cons.
  posnats. simpl.
  repeat rewrite index_to_partial_function_vars_cons; eauto with reindexers.
  repeat rewrite Hmap; eauto with reindexers.
  repeat rewrite map_cons.
  repeat rewrite map_subst_var_in_Zexpr_shape_to_index_id;
    eauto with reindexers.
  rewrite map_subst_var_in_Z_tup_combine_not_in; eauto with reindexers.
  unfold subst_var_in_Z_tup. simpl.
  erewrite eq_index_to_partial_function. reflexivity.
  eapply eq_Z_tuple_index_list_partially_eval_Z_tup.
  eapply HeqZlistwrap.
  erewrite <- eq_Z_tuple_index_list_cons.
  split.
  2: eapply eq_Z_tuple_index_list_id.
  unfold eq_Z_tup. simpl.
  split.
  apply eq_zexpr_add_literal.
  lia.
Qed.

Lemma eq_partial_interpret_reindexer_truncl :
  forall reindexer k m l0 z v x1,
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
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
    (0 <= k)%Z ->
    (0 < Z.of_nat m - k)%Z ->
    partial_interpret_reindexer
      (fun l : list (Zexpr * Z) =>
         reindexer
           match l with
           | [] => l
           | (v0, d) :: xs => ((v0 - | k |)%z, (d - k)%Z) :: xs
           end)
      (map Z.of_nat
           (filter_until(m :: l0) 0)) v
      ((z + k)%Z :: x1) =
      partial_interpret_reindexer
        reindexer
        (map Z.of_nat
             (filter_until
                (m -
                   Z.to_nat k :: l0) 0)) v 
        (z :: x1).
Proof. 
  intros ? ? ? ? ? ? ? Hvar HeqZlistwrap Hvarsub Hmap
         Hvarrdx Hknonneg Htruncnonneg.
  { unfold partial_interpret_reindexer.
    unfold shape_to_vars in *. simpl.
    cases m. lia.
    simpl shape_to_index at 1.
    rewrite shape_to_index_cons.
    simpl nat_range at 1. posnats.
    
    cases (Datatypes.S m - Z.to_nat k). lia.
    simpl. posnats.
    repeat rewrite index_to_partial_function_vars_cons; eauto with reindexers.
    rewrite shape_to_index_cons.
    repeat rewrite Hmap; eauto with reindexers.
    repeat rewrite map_cons.
    repeat rewrite map_subst_var_in_Zexpr_shape_to_index_id;
      eauto with reindexers.
    unfold subst_var_in_Z_tup. simpl.
    erewrite eq_index_to_partial_function. reflexivity.
    eapply eq_Z_tuple_index_list_partially_eval_Z_tup.
    eapply HeqZlistwrap.
    erewrite <- eq_Z_tuple_index_list_cons.
    split.
    2: eapply eq_Z_tuple_index_list_id.
    unfold eq_Z_tup. simpl. propositional.
    eapply eq_zexpr_transitivity.
    apply eq_zexpr_sub_literal.
    eapply eq_zexpr_id. f_equal. lia.
    lia. }
Qed.

Lemma eq_partial_interpret_reindexer_truncr :
  forall reindexer k m l0 z0 args1 v,
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
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
    (0 < m - k) ->
    partial_interpret_reindexer
      (fun l1 : list (Zexpr * Z) =>
         reindexer
           match l1 with
           | [] => l1
           | (v0, d) :: xs => (v0, (d - Z.of_nat k)%Z) :: xs
       end)
      (map Z.of_nat
           (filter_until (m :: l0) 0)) v
      (z0 :: args1) =
      partial_interpret_reindexer
        reindexer
        (map Z.of_nat
             (filter_until (m - k :: l0) 0)) v
    (z0 :: args1).
Proof. 
  intros ? ? ? ? ? ? ? Hvar HeqZlistwrap Hvarsub Hmap
         Hvarrdx Htruncnonneg.
  { unfold partial_interpret_reindexer.
    unfold shape_to_vars in *. simpl.
    cases m. lia.
    simpl shape_to_index at 1.
    rewrite shape_to_index_cons.
    simpl nat_range at 1. posnats.
    
    cases (Datatypes.S m - k). lia.
    simpl. posnats. rewrite <- Heq in *. clear Heq. clear n.
    repeat rewrite index_to_partial_function_vars_cons; eauto with reindexers.
    rewrite shape_to_index_cons.
    repeat rewrite Hmap; eauto with reindexers.
    repeat rewrite map_cons.
    repeat rewrite map_subst_var_in_Zexpr_shape_to_index_id;
      eauto with reindexers.
    unfold subst_var_in_Z_tup. simpl.
    erewrite eq_index_to_partial_function. reflexivity.
    eapply eq_Z_tuple_index_list_partially_eval_Z_tup.
    eapply HeqZlistwrap.
    erewrite <- eq_Z_tuple_index_list_cons.
    split. 2: eapply eq_Z_tuple_index_list_id.
    unfold eq_Z_tup. simpl. propositional.
    eauto.
    destruct k; lia. }
Qed.

Lemma partial_injective_padl :
  forall reindexer m l0 k v x0,
    partial_injective
      (partial_interpret_reindexer
         reindexer
         (result_shape_Z
            (V (repeat (gen_pad l0)
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
    (0 <= k)%Z ->
    partial_injective
      (partial_interpret_reindexer
         (fun l : list (Zexpr * Z) =>
            reindexer
              match l with
              | [] => l
              | (v0, d) :: xs => ((v0 + | k |)%z, (d + k)%Z) :: xs
              end)
         (map Z.of_nat
              (filter_until (m :: l0) 0)) v)
      (filter
         (fun x1 =>
            negb (is_None (result_lookup_Z_option x1 (V x0))))       
         (mesh_grid
            (map Z.of_nat
                 (filter_until (m :: l0) 0)))).
Proof.
  intros ? ? ? ? ? ? Hinj Hsh Hvar Hk Hm HeqZwraplist Hvarsub Hmap
         Hvarrdx Hmnonneg Hknonneg.
  simpl in Hsh.
  erewrite result_has_shape_result_shape_Z in *.
  2: { eapply result_has_shape_concat.
       eapply result_has_shape_repeat_gen_pad. eauto. }
  unfold partial_injective. propositional.
  repeat decomp_index.
  simpl. cases m; simpl; try lia.
  posnats.
  rewrite <- map_cons.
  rewrite <- filter_until_0_cons by lia.
  repeat rewrite <- map_cons in Hinj.
  pose proof filter_pad_l_mesh_grid as H1. simpl gen_pad_list in H1.
  repeat rewrite map_cons in H1. 
  rewrite H1 in Hinj.
  2: { simpl.
       eapply result_has_shape_concat.
       eapply result_has_shape_repeat_gen_pad. auto. }
  erewrite eq_partial_interpret_reindexer_padl in H0; eauto.
  erewrite eq_partial_interpret_reindexer_padl in H0; eauto.
  clear H1.

  repeat rewrite map_cons in Hinj.
  
  eapply Hinj in H0.
  
  propositional.
  invert H5. left. f_equal. lia.

  erewrite eq_partial_interpret_reindexer_padl; eauto.
  lia. 

  eapply in_map_iff.
  eexists (_ :: _ ).
  propositional.
  eapply filter_In. propositional.
  repeat decomp_goal_index. propositional.
  lia.

  eapply in_map_iff.
  eexists (_ :: _).
  propositional.
  eapply filter_In. propositional.
  repeat decomp_goal_index. propositional.
  lia.  
  lia.
  lia.
  lia.
Qed.

Lemma partial_injective_truncl :
  forall reindexer m l0 k v x0,
    partial_injective
      (partial_interpret_reindexer reindexer (result_shape_Z (V x0)) v)
      (filter
         (fun x : list Z => negb (is_None (result_lookup_Z_option x (V x0))))
         (mesh_grid (result_shape_Z (V x0))))->
    result_has_shape
          (V
             (gen_pad_list
                (Z.to_nat k
                 :: l0) ++ x0))
          (m :: l0) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
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
    (0 <= k)%Z ->
    (0 < Z.of_nat m - k)%Z ->
    partial_injective
      (partial_interpret_reindexer
         (fun l : list (Zexpr * Z) =>
            reindexer
              match l with
              | [] => l
              | (v0, d) :: xs => ((v0 - | k |)%z, (d - k)%Z) :: xs
              end)
         (map Z.of_nat
              (filter_until
                 (m :: l0) 0)) v)
      (map
          (fun l : list Z =>
           match l with
           | [] => l
           | x1 :: xs => (x1 + k)%Z :: xs
           end)
          (filter (fun x1 =>
                     negb
                       (is_None (result_lookup_Z_option x1 (V x0))))       
          (mesh_grid
             (map Z.of_nat
                (filter_until
                   (m - Z.to_nat k
                    :: l0) 0)))))
.      
Proof.
  intros ? ? ? ? ? ? Hinj Hsh Hvar HeqZwraplist Hvarsub Hmap
         Hvarrdx Hknonneg Hmknonneg.
  simpl in Hsh.
  erewrite result_has_shape_result_shape_Z in *.
  2: { eapply result_has_shape_app_l.
       2: eauto. simpl. rewrite repeat_length. reflexivity. }
  unfold partial_injective. propositional.
  
  eapply in_map_iff in H,H0. invs.
  repeat decomp_index.
  simpl. cases m; simpl; try lia.
  posnats.
  rewrite <- map_cons.
  rewrite <- filter_until_0_cons.
  erewrite eq_partial_interpret_reindexer_truncl in H1; eauto.
  erewrite eq_partial_interpret_reindexer_truncl in H1; eauto.
  eapply Hinj in H1.
  
  propositional.
  + invert H3. auto.
  + erewrite eq_partial_interpret_reindexer_truncl; eauto.
  + eapply filter_In. propositional.
    repeat decomp_goal_index. propositional.
  + eapply filter_In. propositional.
    repeat decomp_goal_index. propositional.
  + lia.
Qed.

Lemma partial_injective_truncr :
  forall reindexer x0 m l0 k v,
    partial_injective
      (partial_interpret_reindexer
         reindexer
         (map Z.of_nat
              (filter_until (m - k :: l0) 0)) v)
      (filter
         (fun x => negb (is_None (result_lookup_Z_option x (V x0))))
         (mesh_grid
            (map Z.of_nat
                 (filter_until
                    (m - k :: l0) 0)))) ->
    result_has_shape
      (V
         (x0 ++
             repeat (gen_pad l0)
             k))
          (m :: l0) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
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
    (0 < m - k)%nat ->
    partial_injective
    (partial_interpret_reindexer
       (fun l3 : list (Zexpr * Z) =>
          reindexer
            match l3 with
            | [] => l3
            | (v0, d) :: xs => (v0, (d - Z.of_nat k)%Z) :: xs
            end)
       (map Z.of_nat
            (filter_until
               (m :: l0) 0)) v)
    (filter (fun x1 => negb (is_None (result_lookup_Z_option x1 (V x0))))
            (mesh_grid
               (map Z.of_nat
                    (filter_until
                       (m - k :: l0) 0)))).
Proof.
  intros ? ? ? ? ? ? Hinj Hsh Hvar HeqZwraplist Hvarsub Hmap
         Hvarrdx Hmknonneg.
  unfold partial_injective. propositional.
  repeat decomp_index.
  simpl. cases m. lia.
  simpl. posnats.

  erewrite eq_partial_interpret_reindexer_truncr in H1; eauto.
  erewrite eq_partial_interpret_reindexer_truncr in H1; eauto.
  eapply Hinj in H1.
  
  propositional.
  repeat rewrite <- map_cons.
  rewrite <- filter_until_0_cons by lia.
  repeat rewrite <- map_cons.
  rewrite eq_partial_interpret_reindexer_truncr; eauto.

  eapply filter_In. propositional.
  repeat decomp_goal_index.
  propositional.

  eapply filter_In. propositional.
  repeat decomp_goal_index.
  propositional.  
Qed.

Lemma eq_partial_interpret_reindexer_eval_0 :
  forall reindexer r r0 v i loz hiz args1,
    result_has_shape (V (r :: r0)) (result_shape_nat (V (r :: r0))) ->
    partial_injective
      (partial_interpret_reindexer
         reindexer (result_shape_Z (V (r :: r0))) v)
    (filter
       (fun x =>
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
       ~ i \in dom v ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    ~ In i (shape_to_vars (result_shape_Z r)) ->
    (hiz - loz)%Z = Z.of_nat (Datatypes.length (r::r0)) ->  
   partial_interpret_reindexer
     (fun l0 : list (Zexpr * Z) =>
        reindexer (((! i ! - | loz |)%z,
                     (hiz - loz)%Z) :: l0))
     (map Z.of_nat (filter_until (result_shape_nat r) 0)) 
     (v $+ (i, loz)) args1 =
     partial_interpret_reindexer reindexer
        (map Z.of_nat (filter_until (result_shape_nat (V (r :: r0))) 0)) v
        (0%Z :: args1).
Proof.
  intros ? ? ? ? ? ? ? ? Hsh Hinj HeqZlist Hvar Hmap Hidom
         Hnotvar Hishape Hhilo.
  assert (length args1 =
            length (map Z.of_nat (filter_until (result_shape_nat r) 0)) \/
            length args1 <> length
                              (map Z.of_nat
                                   (filter_until (result_shape_nat r) 0)) )
    as Hcase by lia.
  inversion Hcase as [ Hcase1 | Hcase2]; clear Hcase.
  2: { repeat erewrite partial_interpret_reindexer_vars_None by (simpl; lia).
       auto. }
  unfold partial_interpret_reindexer.
  unfold shape_to_vars. simpl.
  rewrite index_to_partial_function_vars_cons.
  rewrite Hmap. simpl.
  rewrite map_subst_var_in_Z_tup_combine_not_in; eauto with reindexers.
  2: { eapply not_var_generation_in_index; eauto. }
  2: { eapply not_var_generation_in_dom; eauto. }
  unfold subst_var_in_Z_tup. simpl.
  rewrite partially_eval_Z_tup_add_partial.
  replace (fun e : Zexpr * Z => subst_var_in_Z_tup i loz (partially_eval_Z_tup v e)) with
    (fun e : Zexpr * Z => partially_eval_Z_tup v (subst_var_in_Z_tup i loz e)).
  2: { eapply functional_extensionality. intros.
       rewrite subst_var_in_Z_tup_partially_eval_Z_tup_comm. reflexivity.
       auto. }
  rewrite <- map_map.
  rewrite Hmap.
  simpl.

  unfold shape_to_index.
  rewrite map_subst_var_in_Z_tup_combine_not_in; eauto with reindexers.
  2: { unfold not. intros. apply Hishape.
       eapply in_map_iff in H. invs.
       unfold shape_to_vars.
       eapply in_map_iff.  eexists. split. reflexivity.
       erewrite result_has_shape_result_shape_Z. eassumption.
       invert Hsh. auto. }
  2: { unfold not. intros.
       eapply Hidom. eapply Hvar. eassumption. }
  unfold subst_var_in_Z_tup. simpl.
  cases (i ==v i).
  2: { propositional. }
  
  replace (combine
                   (map ZVar
                      (map (fun k : nat => String.concat "" (repeat "?" (k + 1)))
                         (nat_range
                            (Datatypes.length
                               (map Z.of_nat (filter_until (result_shape_nat r) 0))))))
                   (map Z.of_nat (filter_until (result_shape_nat r) 0))) with
    (shape_to_index (map Z.of_nat (filter_until (result_shape_nat r) 0))
                    (shape_to_vars (map Z.of_nat (filter_until (result_shape_nat r) 0)))).
  2: { reflexivity. }

  (* rewrite subst_var_in_Zexpr_id. *)
  (* 2: { invert Hlo. rewrite H0. sets. } *)
  
  erewrite index_to_partial_function_subst_vars;
    unfold nat_range; eauto with reindexers.
  2: rewrite length_map; rewrite length_nat_range_rec; lia.
  symmetry.
  erewrite index_to_partial_function_subst_vars;
    unfold nat_range; eauto with reindexers.  
  2: rewrite length_map; rewrite length_nat_range_rec; lia.
  symmetry.
  rewrite map_fold_left_subst_var_in_Z_tup_reindexer;
    eauto with reindexers.
  symmetry.
  rewrite map_fold_left_subst_var_in_Z_tup_reindexer;
    eauto with reindexers.
  symmetry.
  simpl.
  repeat rewrite map_fold_left_subst_var_in_Z_tup_combine;
    eauto with reindexers.
  2: rewrite length_map; rewrite length_nat_range_rec; lia.
  rewrite fold_left_subst_var_in_Z_tup_ZLit.
  rewrite map_fold_left_subst_var_in_Z_tup_shape_to_index.
  2: unfold shape_to_vars; unfold nat_range; rewrite length_map;
  rewrite length_nat_range_rec; lia.  
  rewrite fold_left_subst_var_in_Z_tup_id by reflexivity.
  
  erewrite eq_index_to_partial_function. reflexivity.
  eapply eq_Z_tuple_index_list_partially_eval_Z_tup.
  eapply HeqZlist.
  erewrite <- eq_Z_tuple_index_list_cons_tup.  
  split.  

  eapply eq_zexpr_transitivity.
  eapply eq_zexpr_sub.
  eapply eq_zexpr_id. eauto. eauto.
  eapply eq_zexpr_transitivity.
  eapply eq_zexpr_sub_literal.
  eapply eq_zexpr_id. f_equal. lia.

  split. simpl in Hhilo. lia.
  eapply eq_Z_tuple_index_list_id.
  simpl. eapply no_dup_var_generation.
  auto.
Qed.

Lemma partial_injective_cons_reindexer :
  forall reindexer r r0 v i hi lo,
    result_has_shape (V (r :: r0)) (result_shape_nat (V (r :: r0))) ->
    partial_injective
      (partial_interpret_reindexer
         reindexer (result_shape_Z (V (r :: r0))) v)
      (filter
         (fun x =>
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
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    ~ In i (shape_to_vars (result_shape_Z r)) ->
    (hi - lo)%Z = Z.of_nat (Datatypes.length (r::r0)) ->
    partial_injective
      (partial_interpret_reindexer
         (fun l0 : list (Zexpr * Z) =>
            reindexer (((! i ! - | lo |)%z, (hi - lo)%Z) :: l0)) 
         (result_shape_Z r) (v $+ (i, lo)))
      (filter
         (fun x =>
            negb (is_None (result_lookup_Z_option x r)))
         (mesh_grid (result_shape_Z r))).
Proof.
  intros.
  erewrite result_has_shape_result_shape_Z in * by eassumption.
  inversion H. subst.
  erewrite result_has_shape_result_shape_Z by eassumption.
  unfold partial_injective. propositional.
  destruct (partial_interpret_reindexer
          (fun l0 : list (Zexpr * Z) =>
             reindexer (((! i ! - | lo |)%z, _) :: l0))
          (map Z.of_nat (filter_until (result_shape_nat r) 0)) 
          (v $+ (i, lo)) args1) eqn:Heq.
  + left.
    assert (0%Z::args1 = 0%Z::args2 -> args1 = args2).
    inversion 1. auto.
    apply H12.
    pose proof Heq as Heq'. rewrite H11 in Heq.
    erewrite eq_partial_interpret_reindexer_eval_0 in Heq.
    erewrite eq_partial_interpret_reindexer_eval_0 in Heq.
    
    eapply H0 in Heq. propositional.
    erewrite eq_partial_interpret_reindexer_eval_0 in Heq'.
    rewrite Heq' in H16; discriminate.

    assumption.  erewrite result_has_shape_result_shape_Z by eassumption.
    eassumption.
    auto. auto. auto. auto. auto. auto. auto. eauto. auto.
    erewrite result_has_shape_result_shape_nat by eauto.
    repeat decomp_index.
    eapply filter_In. propositional. 
    repeat decomp_goal_index. propositional.
    lia. lia. repeat decomp_goal_index. auto.
    repeat decomp_index.
    eapply filter_In. propositional. 
    repeat decomp_goal_index. propositional.
    lia. lia. repeat decomp_goal_index. auto.

    erewrite result_has_shape_result_shape_Z by eassumption.
    eassumption.
    auto. auto. auto. auto. auto. auto. auto. eauto. auto. eauto.
    
    erewrite result_has_shape_result_shape_Z by eassumption. auto.
    auto. auto. auto. auto. auto. auto. auto.
  + auto.
Qed.

Lemma partial_injective_shift_top_dim_reindexer :
  forall reindexer r r0 v,
    result_has_shape (V (r :: r0)) (result_shape_nat (V (r :: r0))) ->
    partial_injective 
      (partial_interpret_reindexer
         reindexer (result_shape_Z (V (r :: r0))) v)
      (filter
         (fun x =>
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
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    r0 <> [] ->
    partial_injective 
      (partial_interpret_reindexer (shift_top_dim_reindexer reindexer)
                                   (result_shape_Z (V r0)) v)
      (filter
         (fun x =>
            negb (is_None (result_lookup_Z_option x (V r0))))
         (mesh_grid (result_shape_Z (V r0)))).
Proof.
  intros.
  erewrite result_has_shape_result_shape_Z in * by eassumption.
  inversion H. subst.
  erewrite result_has_shape_result_shape_Z.
  2: { eapply forall_result_has_shape. eassumption. reflexivity. }
  unfold partial_injective. propositional.
  cases (partial_interpret_reindexer
           (shift_top_dim_reindexer reindexer)
           (map Z.of_nat (filter_until
                            (Datatypes.length r0 :: result_shape_nat r) 0))).
  2: auto. left.
  pose proof Heq. rewrite H10 in Heq.
  repeat decomp_index.
  pose proof H10.
  rewrite H9 in H10.

  erewrite eq_partial_interpret_reindexer_shift_top_dim_reindexer in H10;
    eauto.
  2: { pose proof H0. erewrite result_has_shape_result_shape_Z by eauto.
       eauto. }
  erewrite eq_partial_interpret_reindexer_shift_top_dim_reindexer in H10;
    eauto.
  2: { pose proof H0. erewrite result_has_shape_result_shape_Z by eauto.
       eauto. }
  eapply H0 in H10.
  propositional. invert H7. f_equal. lia.
  erewrite eq_partial_interpret_reindexer_shift_top_dim_reindexer in H14;
    eauto.
  2: { pose proof H0. erewrite result_has_shape_result_shape_Z by eauto.
       eauto. }
  rewrite H7 in *. discriminate.

  eapply filter_In. propositional. repeat decomp_goal_index. propositional.
  lia. lia.
  rewrite <- H17. simpl.
  replace (Z.to_nat (z1 + 1)) with (Datatypes.S (Z.to_nat z1)) by lia.
  simpl.
  cases (z1 + 1)%Z; try lia.
  cases z1; try lia; auto.

  eapply filter_In. propositional. repeat decomp_goal_index. propositional.
  lia. lia.
  rewrite <- H15. simpl.
  replace (Z.to_nat (z0 + 1)) with (Datatypes.S (Z.to_nat z0)) by lia.
  simpl.
  cases (z0 + 1)%Z; try lia.
  cases z0; try lia; auto.
Qed.

Lemma constant_cap_eval_step_empty :
  forall (f : list Z -> option Z) r r0 n l,
    partial_injective
      f
      (filter
         (fun x =>
            negb (is_None (result_lookup_Z_option x (V (r :: r0)))))
         (mesh_grid (result_shape_Z (V (r :: r0))))) ->
    result_has_shape (V (r :: r0)) (n::l) ->
    constant
      (extract_Some
         (map (fun index => f (0%Z :: index))
              (filter (fun x0 => negb (is_None (result_lookup_Z_option x0 r)))
                      (mesh_grid (result_shape_Z r))))) \cap
      constant
      (extract_Some
         (map
            (fun index : list Z =>
               match index with
               | [] => f index
               | x0 :: xs => f ((x0 + 1)%Z :: xs)
               end)
            (filter
               (fun x0 => negb (is_None (result_lookup_Z_option x0 (V r0))))
               (mesh_grid (result_shape_Z (V r0)))))) = constant [].
Proof.
  intros. apply cap_empty_exclusion.
  propositional; rewrite <- @In_iff_in in *;
    rewrite <- @in_extract_Some in *; erewrite @in_map_iff in *; invs.
  - erewrite result_has_shape_result_shape_Z in H4.
    2: { eapply forall_result_has_shape. invert H0. eauto. eauto. }
    repeat decomp_index.
    pose proof H2.
    rewrite <- H1 in H2.
    eapply H in H2. 
    propositional. invert H4. lia.
    rewrite H4 in *. discriminate.
    eapply filter_In. propositional.
    erewrite result_has_shape_result_shape_Z by eauto.
    repeat decomp_goal_index.
    propositional. lia. invert H0. lia.
    rewrite <- H6. simpl.
    repeat f_equal.
    cases (z+1)%Z; try lia.
    cases z; try lia.
    eq_match_discriminee.
    rewrite <- Heq. simpl. auto.
    cases (Z.to_nat (Z.pos p)). lia. simpl. eq_match_discriminee.
    f_equal. lia.
    eapply filter_In. propositional.
    erewrite result_has_shape_result_shape_Z by eauto.
    repeat decomp_goal_index.
    propositional. lia. invert H0. lia.
    erewrite result_has_shape_result_shape_Z in H3.
    2: { invert H0. eauto. }
    repeat decomp_index. auto.
  - erewrite result_has_shape_result_shape_Z in H5.
    2: { eapply forall_result_has_shape. invert H0. eauto. eauto. }
    repeat decomp_index.
    pose proof H2. rewrite <- H1 in H2.
    eapply H in H2.
    propositional. invert H5. lia.
    rewrite H5 in *. discriminate.
    eapply filter_In. propositional.
    erewrite result_has_shape_result_shape_Z by eauto.
    repeat decomp_goal_index.
    propositional. lia. invert H0. lia.
    erewrite result_has_shape_result_shape_Z in H3.
    2: { invert H0. eauto. }
    repeat decomp_index. auto.
    eapply filter_In. propositional.
    erewrite result_has_shape_result_shape_Z by eauto.
    repeat decomp_goal_index.
    propositional. lia. invert H0. lia.
    rewrite <- H6.
    simpl. repeat f_equal.
    cases (z + 1)%Z; try lia.
    simpl. cases (Pos.to_nat p); try lia.
    simpl.
    cases z; try lia.
    eq_match_discriminee. f_equal. lia.
    eq_match_discriminee. f_equal. lia.
Qed.

Lemma partial_injective_shift_top_dim_reindexer_match :
  forall (f : list Z -> option Z) r r0 n l,
    partial_injective
      f
      (filter
         (fun x : list Z =>
            negb (is_None (result_lookup_Z_option x (V (r :: r0)))))
         (mesh_grid (result_shape_Z (V (r :: r0))))) ->
    result_has_shape (V (r :: r0)) (n :: l) ->
    partial_injective
      (fun index : list Z =>
         match index with
         | [] => f index
         | x :: xs => f ((x + 1)%Z :: xs)
         end)
      (filter (fun x => negb (is_None (result_lookup_Z_option x (V r0))))
              (mesh_grid (result_shape_Z (V r0)))).
Proof.
  unfold partial_injective. propositional.
  erewrite result_has_shape_result_shape_Z in *.
  2: { eauto. }
  2: { eapply forall_result_has_shape. invert H0. eauto. reflexivity. }
  2: { eapply forall_result_has_shape. invert H0. eauto. reflexivity. }
  repeat decomp_index.
  eapply H in H3. propositional.
  invert H1. left. f_equal. lia.
  eapply filter_In. propositional.
  repeat decomp_goal_index. propositional. lia. invert H0. lia.
  rewrite <- H7. simpl.
  cases (Z.to_nat (z0 + 1)). lia. simpl.
  repeat f_equal.
  cases (z0+1)%Z; try lia.
  cases z0; try lia.
  eq_match_discriminee. f_equal. lia.
  eq_match_discriminee. f_equal. lia.
  eapply filter_In. propositional.
  repeat decomp_goal_index. propositional. lia. invert H0. lia.
  rewrite <- H5. simpl.
  cases (Z.to_nat (z + 1)). lia. simpl.
  repeat f_equal.
  cases (z+1)%Z; try lia.
  cases z; try lia.
  eq_match_discriminee. f_equal. lia.
  eq_match_discriminee. f_equal. lia.
Qed.

Lemma constant_partial_reindexer_subseteq :
  forall r r0 reindexer lo hi i v,
    (forall (var : var) (k : Z) (l : list (Zexpr * Z)),
        ~ var \in vars_of_reindexer (reindexer []) ->
                  map (subst_var_in_Z_tup var k) (reindexer l) =
                    reindexer (map (subst_var_in_Z_tup var k) l)) ->
    (forall l1 l2 : list (Zexpr * Z),
        eq_Z_tuple_index_list l1 l2 ->
        eq_Z_tuple_index_list (reindexer l1) (reindexer l2)) ->
    (hi - lo)%Z = Z.of_nat (Datatypes.S (Datatypes.length r0)) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    ~ contains_substring "?" i ->
    ~ i \in dom v ->
            result_has_shape (V (r::r0)) (result_shape_nat (V (r::r0))) ->
            partial_injective 
              (partial_interpret_reindexer
                 reindexer (result_shape_Z (V (r :: r0))) v)
              (filter
                 (fun x =>
                    negb (is_None (result_lookup_Z_option x (V (r :: r0)))))
                    (mesh_grid (result_shape_Z (V (r :: r0)))))->
            constant
              (extract_Some
                 (map
                    (partial_interpret_reindexer
                       (fun l0 : list (Zexpr * Z) =>
                          reindexer (((! i ! - | lo |)%z, (hi - lo)%Z) :: l0)) 
                       (result_shape_Z r)
                       (v $+ (i, lo)))
                    (filter
                       (fun x0 : list Z =>
                          negb (is_None (result_lookup_Z_option x0 r)))
                       (mesh_grid (result_shape_Z r)))))
              \subseteq
              constant
              (extract_Some (map
                               (partial_interpret_reindexer
                                  reindexer 
                                  (result_shape_Z (V (r::r0))) v)
                               (filter
             (fun x0 : list Z =>
                negb (is_None (result_lookup_Z_option x0 (V (r :: r0)))))
             (mesh_grid (result_shape_Z (V (r::r0))))))).
Proof.
  intros.
  apply subseteq_In; intros;
    rewrite <- In_iff_in in *;
    rewrite <- in_extract_Some in *;
    rewrite in_map_iff in *; invs.
  - eexists (0%Z::x0). split.
    erewrite result_has_shape_result_shape_Z by eassumption.
    erewrite <- eq_partial_interpret_reindexer_eval_0.
    erewrite result_has_shape_result_shape_Z in H8.
    2: { invert H6. eauto. }
    eassumption.
    auto. auto. auto. auto. auto. auto. auto.
    unfold not. intros.
    unfold shape_to_vars in H9.
    eapply H4.
    eapply shape_to_vars_contains_substring. apply H9.
    eassumption.
    erewrite result_has_shape_result_shape_Z by eassumption.
    repeat decomp_index.
    eapply filter_In. propositional.
    repeat decomp_goal_index. propositional. lia. lia.
Qed.

Lemma partial_injective_add_valuation :
  forall reindexer s v i loz,
  partial_injective
    (partial_interpret_reindexer reindexer (result_shape_Z s) v)
    (filter (fun x0 : list Z => negb (is_None (result_lookup_Z_option x0 s)))
            (mesh_grid (result_shape_Z s))) ->
  (forall (var : var) (k : Z) (l : list (Zexpr * Z)),
      ~ var \in vars_of_reindexer (reindexer []) ->
                map (subst_var_in_Z_tup var k) (reindexer l) =
                  reindexer (map (subst_var_in_Z_tup var k) l)) ->
  ~ i \in dom v ->
          ~ contains_substring "?" i ->
          vars_of_reindexer (reindexer []) \subseteq dom v ->
  partial_injective
    (partial_interpret_reindexer reindexer (result_shape_Z s) (v $+ (i, loz)))
    (filter (fun x0 : list Z => negb (is_None (result_lookup_Z_option x0 s)))
       (mesh_grid (result_shape_Z s))).
Proof.
  intros. unfold partial_injective in *. propositional.
  repeat decomp_index.
  unfold partial_interpret_reindexer in *.
  rewrite partially_eval_Z_tup_add_partial in *.  
  replace (fun e : Zexpr * Z =>
             subst_var_in_Z_tup i loz (partially_eval_Z_tup v e)) with
    (fun e : Zexpr * Z =>
       partially_eval_Z_tup v  (subst_var_in_Z_tup i loz e)) in *.
  2: { eapply functional_extensionality. intros.
       erewrite subst_var_in_Z_tup_partially_eval_Z_tup_comm; auto. }
  rewrite <- map_map with (f:=subst_var_in_Z_tup i loz) in *.
  rewrite H0 in *; eauto.
  2: { unfold not. intros.
       apply H1. apply H3. sets. }
  2: { unfold not. intros.
       apply H1. apply H3. sets. }  
  unfold shape_to_index in *.  
  rewrite map_subst_var_in_Z_tup_combine_not_in in *; eauto.
  2: { unfold not. intros.
       eapply H2. eapply shape_to_vars_contains_substring. eauto. } 
  2: { unfold not. intros.
       eapply H2. eapply shape_to_vars_contains_substring. eauto. }
  2: { unfold not. intros. apply H1. auto. }
  2: { unfold not. intros. apply H1. auto. }
  eapply H in H6. propositional.
  eapply filter_In. propositional.
  eapply filter_In. propositional.
Qed.  

Lemma partial_injective_weaken {X Y} : forall (f : X -> option Y) dom1 dom2,
    partial_injective f dom1 ->
    (forall x, In x dom2 -> In x dom1) ->
    partial_injective f dom2.
Proof.
  unfold partial_injective. propositional.
  eapply H in H3; eauto.
Qed.

Lemma negb_is_None_lookup_result_Z_option_add_result_l :
  forall r1 r2 r3,
    add_result r1 r2 r3 ->
    forall x,
    negb (is_None (result_lookup_Z_option x r1)) = true ->
    negb (is_None (result_lookup_Z_option x r3)) = true.
Proof.
  pose proof (add_result_mut
  (fun (r1 r2 r3 : result) (HH : add_result r1 r2 r3) =>
     forall x,
    negb (is_None (result_lookup_Z_option x r1)) = true ->
    negb (is_None (result_lookup_Z_option x r3)) = true)
   (fun (r1 r2 r3 : list result) (HH : add_list r1 r2 r3) =>
     forall x,
    negb (is_None (result_lookup_Z_option x (V r1))) = true ->
    negb (is_None (result_lookup_Z_option x (V r3))) = true)).
  eapply H; clear H; intros.
  - cases x; auto.
    simpl in *.
    cases s1; simpl in *; try discriminate.
    cases s2; invert a; auto.
  - cases x; auto.
  - cases x; auto.
    simpl in *.
    cases z.
    + simpl in *. eauto.
    + simpl in *.
      cases (Pos.to_nat p).
      * simpl. eauto.
      * simpl nth_error in *.
        specialize (H0 (Z.of_nat n::x)).
        simpl in H0.
        cases (Z.of_nat n); try lia.
        -- replace n with 0 in * by lia. eauto.
        -- replace (Z.to_nat (Z.pos p0)) with n in * by lia.
           eauto.
    + eauto.
  - cases x; auto.
Qed.

Lemma negb_is_None_lookup_result_Z_option_add_result_r :
  forall r1 r2 r3,
    add_result r1 r2 r3 ->
    forall x,
    negb (is_None (result_lookup_Z_option x r2)) = true ->
    negb (is_None (result_lookup_Z_option x r3)) = true.
Proof.
  pose proof (add_result_mut
  (fun (r1 r2 r3 : result) (HH : add_result r1 r2 r3) =>
     forall x,
    negb (is_None (result_lookup_Z_option x r2)) = true ->
    negb (is_None (result_lookup_Z_option x r3)) = true)
   (fun (r1 r2 r3 : list result) (HH : add_list r1 r2 r3) =>
     forall x,
    negb (is_None (result_lookup_Z_option x (V r2))) = true ->
    negb (is_None (result_lookup_Z_option x (V r3))) = true)).
  eapply H; clear H; intros.
  - cases x; auto.
    simpl in *.
    cases s2; simpl in *; try discriminate.
    cases s1; invert a; auto.
  - cases x; auto.
  - cases x; auto.
    simpl in *.
    cases z.
    + simpl in *. eauto.
    + simpl in *.
      cases (Pos.to_nat p); try lia.
      simpl nth_error in *.      
      specialize (H0 (Z.of_nat n::x)).
      simpl in H0.
      cases (Z.of_nat n); try lia.
      * replace n with 0 in * by lia. eauto.
      * replace n with (Z.to_nat (Z.pos p0)) in * by lia. eauto.
    + eauto.
  - cases x; auto.
Qed.

Lemma partial_injective_add_result_r :
  forall r1 r2 r3 reindexer v sh,
    result_has_shape r1 sh ->
    result_has_shape r2 sh ->
    result_has_shape r3 sh ->
    add_result r1 r2 r3 ->
    partial_injective
      (partial_interpret_reindexer
         reindexer (result_shape_Z r3) v)
      (filter (fun x => negb (is_None (result_lookup_Z_option x r3)))
              (mesh_grid (result_shape_Z r3))) ->
    partial_injective
      (partial_interpret_reindexer
         reindexer (result_shape_Z r2) v)
      (filter (fun x => negb (is_None (result_lookup_Z_option x r2)))
              (mesh_grid (result_shape_Z r2))).
Proof.
  intros.
  erewrite result_has_shape_result_shape_Z in * by eauto.
  eapply partial_injective_weaken; try eassumption.
  intros. repeat decomp_index.
  eapply filter_In. propositional.
  repeat decomp_goal_index. propositional.
  eapply negb_is_None_lookup_result_Z_option_add_result_r; eauto.
Qed.

Lemma partial_injective_add_result_l :
  forall r1 r2 r3 reindexer v sh,
    result_has_shape r1 sh ->
    result_has_shape r2 sh ->
    result_has_shape r3 sh ->
    add_result r1 r2 r3 ->
    partial_injective
      (partial_interpret_reindexer
         reindexer (result_shape_Z r3) v)
      (filter (fun x => negb (is_None (result_lookup_Z_option x r3)))
              (mesh_grid (result_shape_Z r3))) ->
    partial_injective
      (partial_interpret_reindexer
         reindexer (result_shape_Z r1) v)
      (filter (fun x => negb (is_None (result_lookup_Z_option x r1)))
              (mesh_grid (result_shape_Z r1))).
Proof.
  intros.
  erewrite result_has_shape_result_shape_Z in * by eauto.
  eapply partial_injective_weaken; try eassumption.
  intros. repeat decomp_index.
  eapply filter_In. propositional.
  repeat decomp_goal_index. propositional.
  eapply negb_is_None_lookup_result_Z_option_add_result_l; eauto.
Qed.

Lemma eq_partial_interpret_reindexer_eval_cons0 :
  forall reindexer r2 args1 r1 v,
    (forall var, contains_substring "?" var -> var \in dom v -> False) ->
    result_has_shape (V (r1 :: r2)) (result_shape_nat (V (r1 :: r2))) ->
    (forall l1 l2 : list (Zexpr * Z),
        eq_Z_tuple_index_list l1 l2 ->
        eq_Z_tuple_index_list (reindexer l1) (reindexer l2)) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall (var : var) (k : Z) (l : list (Zexpr * Z)),
        (var \in vars_of_reindexer (reindexer []) -> False) ->
        map (subst_var_in_Z_tup var k) (reindexer l) =
          reindexer (map (subst_var_in_Z_tup var k) l)) ->
    (forall l : list (Zexpr * Z),
        vars_of_reindexer (reindexer l) =
          vars_of_reindexer (reindexer []) \cup vars_of_reindexer l) ->
    In args1 (mesh_grid (map Z.of_nat (result_shape_nat r1))) ->
    negb (is_None (result_lookup_Z_option args1 r1)) = true ->    
    partial_interpret_reindexer
      (fun l : list (Zexpr * Z) =>
         reindexer
           (((|0|)%z,Z.of_nat (Datatypes.S (length r2))) :: l))
      (map Z.of_nat (filter_until (result_shape_nat r1) 0)) v args1 =
      partial_interpret_reindexer
        reindexer
        (map Z.of_nat
             (filter_until
                (result_shape_nat (V (r1 :: r2))) 0)) v (0%Z::args1).
Proof.
  intros ? ? ? ? ? Henv Hsh HeqZlist Hvarsub Hmap Hvarsarg Harg1 Hnone.
  unfold partial_interpret_reindexer.
  simpl. unfold shape_to_vars. simpl. rewrite shape_to_index_cons.
  rewrite index_to_partial_function_vars_cons; eauto with reindexers.
  rewrite Hmap.
  2: { eapply not_var_generation_in_index; eauto. }
  unfold shape_to_index.
  simpl.
  rewrite map_subst_var_in_Z_tup_combine_not_in; eauto with reindexers.
  unfold subst_var_in_Z_tup. simpl.
  
  erewrite index_to_partial_function_subst_vars.
  2: { eapply forall_shape_to_vars_not_in_dom; eauto. }
  2: { rewrite length_map. unfold nat_range. rewrite length_nat_range_rec.
       rewrite length_map. eapply length_mesh_grid_indices.
       repeat decomp_goal_index. eauto. }
  symmetry.
  erewrite index_to_partial_function_subst_vars.
  2: { eapply forall_map_not_in_dom; eauto. } 
  2: { rewrite length_map. unfold nat_range. rewrite length_nat_range_rec.
       rewrite length_map. eapply length_mesh_grid_indices.
       repeat decomp_goal_index. eauto. }
  rewrite map_fold_left_subst_var_in_Z_tup_reindexer; eauto with reindexers.
  symmetry.
  rewrite map_fold_left_subst_var_in_Z_tup_reindexer; eauto with reindexers.
  2: { eapply forall_map_not_in_index; eauto. }
  symmetry.
  simpl.
  repeat rewrite fold_left_subst_var_in_Z_tup_ZLit.
  rewrite map_fold_left_subst_var_in_Z_tup_combine.
  2: { rewrite length_map. rewrite length_nat_range_rec. rewrite length_map.
       eapply length_mesh_grid_indices.
       decomp_goal_index. auto. }
  symmetry.
  rewrite map_fold_left_subst_var_in_Z_tup_combine.
  2: { rewrite length_map. unfold nat_range.
       rewrite length_nat_range_rec. rewrite length_map.
       eapply length_mesh_grid_indices.
       decomp_goal_index. auto. }
  symmetry.
  reflexivity.
  eapply no_dup_var_generation.
  eapply no_dup_var_generation.
Qed.

Lemma injective_flatten :
  forall sh args1 args2,
    In args1 (mesh_grid sh) ->
    In args2 (mesh_grid sh) ->
    flatten sh args1 = flatten sh args2 ->
    args1 = args2.
Proof.
  induct sh; intros.
  - simpl in *; propositional. subst. auto.
  - cases args1.
    simpl in H. eapply not_In_empty_map2_cons in H. propositional.
    cases args2.
    simpl in H0. eapply not_In_empty_map2_cons in H0. propositional.
    eapply in_mesh_grid_cons__ in H.
    eapply in_mesh_grid_cons__ in H0.
    invert H. invert H0. invert H1.
    cases sh.
    + simpl in *. propositional. subst. f_equal. auto.
    + simpl in H5.
      repeat rewrite (Z.mul_comm _ (fold_left _ _ _)) in H5.  
      eapply Z.div_mod_unique in H5. invert H5.
      f_equal. auto.
      eapply in_mesh_grid_args_flatten_bounds. eassumption.
      eapply in_mesh_grid_args_flatten_bounds. eassumption.
Qed.

Lemma injective_index_to_partial_function_ZLit :
  forall sh args1 args2,
    In args1 (mesh_grid sh) ->
    In args2 (mesh_grid sh) ->
    index_to_partial_function (combine (map ZLit args1)
                                       sh) [] [] =
      index_to_partial_function (combine (map ZLit args2)
                                         sh) [] [] ->
    args1 = args2.
Proof.
  unfold index_to_partial_function.
  simpl. intros.
  invert H1. 

  repeat rewrite map_id in *.
  rewrite @map_eval_Zexpr_Z_tup_total_ZLit in *.
  2: { symmetry. eapply length_mesh_grid_indices_Z. auto. }
  rewrite @map_eval_Zexpr_Z_tup_total_ZLit in *.
  2: { symmetry. eapply length_mesh_grid_indices_Z. auto. }
  repeat rewrite map_map in *.
  rewrite @map_snd_combine in *.
  2: { symmetry. eapply length_mesh_grid_indices_Z. auto. }
  rewrite @map_snd_combine in *.
  2: { symmetry. eapply length_mesh_grid_indices_Z. auto. }  
  rewrite @map_fst_combine in *.
  2: { symmetry. eapply length_mesh_grid_indices_Z. auto. }  
  rewrite @map_fst_combine in *.
  2: { symmetry. eapply length_mesh_grid_indices_Z. auto. }  
  
  eapply injective_flatten in H3; eauto.
Qed.  

Lemma partial_injective_id_reindexer :
  forall sh v r,
    (forall var : var, contains_substring "?" var ->
                       var \in dom v -> False) ->
    partial_injective
      (partial_interpret_reindexer (fun l : list (Zexpr * Z) => l) sh v)
      (filter
         (fun x => negb (is_None (result_lookup_Z_option x r)))
         (mesh_grid sh)).
Proof.
  unfold partial_injective. set (fun l : list (Zexpr * Z) => l).
  unfold partial_interpret_reindexer.
  propositional.
  unfold shape_to_vars in *. unfold nat_range in *.
  repeat decomp_index.
  rewrite index_to_partial_function_subst_vars in H2.
  2: { eapply forall_map_not_in_dom; eauto. }
  symmetry in H2.
  rewrite index_to_partial_function_subst_vars in H2.
  2: { eapply forall_map_not_in_dom; eauto. }
  symmetry in H2.
  subst l. simpl in H2.
  rewrite map_fold_left_subst_var_in_Z_tup_shape_to_index in H2;
    eauto with reindexers.
  symmetry in H2.
  rewrite map_fold_left_subst_var_in_Z_tup_shape_to_index in H2;
    eauto with reindexers.
  symmetry in H2.
  repeat rewrite map_partially_eval_Z_tup_ZLit in H2.
  eapply injective_index_to_partial_function_ZLit in H2; propositional.
  rewrite length_map. rewrite length_nat_range_rec.
  eapply length_mesh_grid_indices_Z. eauto.
  rewrite length_map. rewrite length_nat_range_rec.
  eapply length_mesh_grid_indices_Z. eauto.
  rewrite length_map. rewrite length_nat_range_rec.
  eapply length_mesh_grid_indices_Z. eauto.
  rewrite length_map. rewrite length_nat_range_rec.
  eapply length_mesh_grid_indices_Z. eauto.
Qed.

Lemma partial_injective_eval_cons0 : forall x1 xs1 reindexer v,
  partial_injective
    (partial_interpret_reindexer reindexer (result_shape_Z (V (x1::xs1))) v)
    (filter (fun x => negb (is_None (result_lookup_Z_option x (V (x1::xs1)))))
            (mesh_grid (result_shape_Z (V (x1::xs1))))) ->
  (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
  result_has_shape (V (x1::xs1)) (result_shape_nat (V (x1::xs1))) ->
  (forall l1 l2 : list (Zexpr * Z),
      eq_Z_tuple_index_list l1 l2 ->
      eq_Z_tuple_index_list (reindexer l1) (reindexer l2)) ->
  vars_of_reindexer (reindexer []) \subseteq dom v ->
  (forall (var : var) (k : Z) (l : list (Zexpr * Z)),
  (var \in vars_of_reindexer (reindexer []) -> False) ->
  map (subst_var_in_Z_tup var k) (reindexer l) =
    reindexer (map (subst_var_in_Z_tup var k) l)) ->
  (forall l : list (Zexpr * Z),
  vars_of_reindexer (reindexer l) =
  vars_of_reindexer (reindexer []) \cup vars_of_reindexer l) ->
  partial_injective
    (partial_interpret_reindexer
       (fun l : list (Zexpr * Z) =>
        reindexer
          (((| 0 |)%z, Z.of_nat (Datatypes.length (x1 :: xs1))) :: l))
       (result_shape_Z x1) v)
    (filter (fun x : list Z => negb (is_None (result_lookup_Z_option x x1)))
            (mesh_grid (result_shape_Z x1))).
Proof.
  intros ? ? ? ? Hinj Henv Hsh HeqZlist Hvarsub Hmap Hvarsarg.
  unfold partial_injective. propositional.
  erewrite result_has_shape_result_shape_Z in Hinj by eauto.
  erewrite result_has_shape_result_shape_Z.
  2: { invert Hsh. eauto. }    
  propositional.
  repeat decomp_index.
  simpl length in *.
  erewrite result_has_shape_result_shape_Z in H1.
  2: { invert Hsh. eauto. }
  rewrite eq_partial_interpret_reindexer_eval_cons0 in H1; eauto.
  rewrite eq_partial_interpret_reindexer_eval_cons0 in H1; eauto.
  rewrite eq_partial_interpret_reindexer_eval_cons0; eauto.
  apply Hinj in H1.
  propositional. invert H. propositional.
  eapply filter_In. propositional. repeat decomp_goal_index.
  propositional. lia. lia.
  eapply filter_In. propositional. repeat decomp_goal_index.
  propositional. lia. lia.
Qed.

Lemma eq_partial_interpret_reindexer_transpose :
  forall z z0 x reindexer v m0 n0 l0,
    (forall var : var, contains_substring "?" var -> var \in dom v -> False)->
    (forall l1 l2 : list (Zexpr * Z),
        eq_Z_tuple_index_list l1 l2 ->
        eq_Z_tuple_index_list (reindexer l1) (reindexer l2)) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall (var : var) (k : Z) (l : list (Zexpr * Z)),
      (var \in vars_of_reindexer (reindexer []) -> False) ->
      map (subst_var_in_Z_tup var k) (reindexer l) =
        reindexer (map (subst_var_in_Z_tup var k) l)) ->    
    (0 <= z < Z.of_nat m0)%Z ->
    (0 <= z0 < Z.of_nat n0)%Z ->
    In x (mesh_grid (map Z.of_nat l0)) ->
  partial_interpret_reindexer
    (fun l4 : list (Zexpr * Z) =>
     reindexer
       match l4 with
       | [] => l4
       | [(v0, d)] => l4
       | (v0, d) :: (vi, di) :: xs => (vi, di) :: (v0, d) :: xs
       end)
    (map Z.of_nat
       (filter_until
          (n0 :: m0:: l0) 0)) v 
    (z0 :: z :: x) =
  partial_interpret_reindexer reindexer
    (map Z.of_nat
       (filter_until
          (m0 :: n0 :: l0) 0)) v 
    (z :: z0 :: x).
Proof.
  intros ? ? ? ? ? ? ? ? Henv HeqZlist Hvarsub Hmap Hzlim Hz0lim Hx.
  unfold partial_interpret_reindexer.
  simpl.
  cases n0. lia.
  cases m0. lia.
  simpl. posnats. unfold shape_to_index, shape_to_vars. simpl.
  repeat rewrite index_to_partial_function_vars_cons;
    eauto with reindexers.
  repeat rewrite Hmap;
    try eapply not_var_generation_in_index2;
    try eapply not_var_generation_in_index; eauto.
  simpl.
  repeat rewrite map_subst_var_in_Z_tup_combine_not_in; eauto with reindexers.
Qed.                                                            

Lemma partial_injective_transpose :
  forall l n0 m0 l0 reindexer v,
    result_has_shape (V l) (n0 :: m0 :: l0) ->
    partial_injective
      (partial_interpret_reindexer
         reindexer
         (result_shape_Z
            (transpose_result l (m0 :: n0 :: l0))) v)
    (filter
       (fun x : list Z =>
          negb
            (is_None
               (result_lookup_Z_option
                  x
                  (transpose_result l (m0 :: n0 :: l0)))))
       (mesh_grid
          (result_shape_Z
             (transpose_result l (m0 :: n0 :: l0))))) ->
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
    (forall var : var, contains_substring "?" var -> var \in dom v -> False)->
  partial_injective
    (partial_interpret_reindexer
       (fun l4 : list (Zexpr * Z) =>
          reindexer
            match l4 with
            | [] => l4
            | [(v0, d)] => l4
            | (v0, d) :: (vi, di) :: xs => (vi, di) :: (v0, d) :: xs
            end) (result_shape_Z (V l)) v)
    (filter (fun x => negb (is_None (result_lookup_Z_option x (V l))))
            (mesh_grid (result_shape_Z (V l)))).
Proof.
  intros ? ? ? ? ? ? Hsh Hinj HeqZlist Hvarsub Hmap Hvarsarg Henv.
  erewrite result_has_shape_result_shape_Z by eauto.
  erewrite result_has_shape_result_shape_Z in *.
  2: { eapply result_has_shape_transpose_result. eauto. }
  unfold partial_injective. propositional.
  repeat decomp_index.
  erewrite eq_partial_interpret_reindexer_transpose in H1; eauto.
  erewrite eq_partial_interpret_reindexer_transpose in H1; eauto.
  eapply Hinj in H1.
  propositional.
  - invert H4. propositional.
  - erewrite eq_partial_interpret_reindexer_transpose; eauto.
  - eapply filter_In. propositional.
    repeat decomp_goal_index. propositional.
    repeat decomp_goal_index. propositional.
    rewrite <- H6.
    erewrite result_lookup_Z_option_transpose. reflexivity.
    lia. lia. eauto.
  - eapply filter_In. propositional.
    repeat decomp_goal_index. propositional.
    repeat decomp_goal_index. propositional.
    rewrite <- H3.
    erewrite result_lookup_Z_option_transpose. reflexivity.
    lia. lia. eauto.
Qed.


Lemma eq_partial_interpret_reindexer_concat_l :
  forall args1 l1 l2 l0 reindexer v n m,
    In args1
       (filter
          (fun x => negb (is_None (result_lookup_Z_option x (V l1))))
          (mesh_grid (result_shape_Z (V l1)))) ->
    result_has_shape (V l1) (n :: l0) ->
    result_has_shape (V l2) (m :: l0) ->
    (forall var : var, contains_substring "?" var -> var \in dom v -> False)->
    (forall l1 l2 : list (Zexpr * Z),
        eq_Z_tuple_index_list l1 l2 ->
        eq_Z_tuple_index_list (reindexer l1) (reindexer l2)) ->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall (var : var) (k : Z) (l : list (Zexpr * Z)),
      (var \in vars_of_reindexer (reindexer []) -> False) ->
      map (subst_var_in_Z_tup var k) (reindexer l) =
        reindexer (map (subst_var_in_Z_tup var k) l)) ->
      partial_interpret_reindexer
        (fun l : list (Zexpr * Z) =>
           reindexer
           match l with
           | [] => l
           | (v0, d) :: xs => ((v0, (d + Z.of_nat m)%Z) :: xs)
           end) (map Z.of_nat (filter_until ((n :: l0)) 0))
        v args1 =
        partial_interpret_reindexer
          reindexer (map Z.of_nat (filter_until ((n + m :: l0)) 0)) v args1.
Proof.
  intros ? ? ? ? ? ? ? ? Harg Hsh1 Hsh2 Henv HeqZlist Hvarsub Hmap.
  pose proof (result_has_shape_concat _ _ _ _ _ Hsh1 Hsh2).
  erewrite result_has_shape_result_shape_Z in Harg by eauto.
  repeat decomp_index.
  repeat erewrite result_has_shape_result_shape_Z; eauto.
  
  unfold partial_interpret_reindexer.
  simpl.
  cases n. simpl in *. lia.
  simpl.
  unfold shape_to_index,shape_to_vars.
  simpl.
  repeat erewrite index_to_partial_function_vars_cons; eauto with reindexers.
  rewrite Hmap; eauto with reindexers.
  2: { eapply not_var_generation_in_index; eauto. }
  rewrite Hmap; eauto with reindexers.
  2: { eapply not_var_generation_in_index; eauto. }
  simpl.
  rewrite map_subst_var_in_Z_tup_combine_not_in; eauto with reindexers.
  unfold subst_var_in_Z_tup.
  simpl.
  erewrite eq_index_to_partial_function.
  reflexivity.
  eapply eq_Z_tuple_index_list_partially_eval_Z_tup.
  eapply HeqZlist.
  erewrite <- eq_Z_tuple_index_list_cons_tup.
  split. auto.
  split. lia.
  eapply eq_Z_tuple_index_list_id.
Qed.

Lemma partial_injective_concat_l : forall l1 reindexer l2 v l0 n m,
    partial_injective 
      (partial_interpret_reindexer reindexer
                                   (result_shape_Z (V (l1 ++ l2)%list)) v)
      (filter (fun x => negb
                          (is_None
                             (result_lookup_Z_option x (V (l1 ++ l2)%list))))
              (mesh_grid (result_shape_Z (V (l1 ++ l2)%list)))) ->
    result_has_shape (V l1) (n :: l0) ->
    result_has_shape (V l2) (m :: l0) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    (forall l1 l2 : list (Zexpr * Z),
        eq_Z_tuple_index_list l1 l2 -> eq_Z_tuple_index_list (reindexer l1)
                                                             (reindexer l2))->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall (var : var) (k : Z) (l : list (Zexpr * Z)),
        ~ var \in vars_of_reindexer (reindexer []) ->
                  map (subst_var_in_Z_tup var k) (reindexer l) =
                    reindexer (map (subst_var_in_Z_tup var k) l)) ->
    partial_injective 
      (partial_interpret_reindexer
         (fun l : list (Zexpr * Z) =>
            reindexer
            match l with
            | [] => l
            | (v0, d) :: xs =>
                  ((v0, (d + Z.of_nat m)%Z) :: xs)
                    end) (map Z.of_nat (filter_until (n :: l0) 0)) v)
      (filter (fun x => negb (is_None (result_lookup_Z_option x (V l1))))
              (mesh_grid (map Z.of_nat (filter_until (n :: l0) 0)))).
Proof.
  unfold partial_injective in *. propositional.
  repeat decomp_index.

  repeat rewrite <- map_cons in *.
  erewrite eq_partial_interpret_reindexer_concat_l; eauto.
  2: { eapply filter_In. propositional.
       erewrite result_has_shape_result_shape_Z by eauto.
       repeat decomp_goal_index. propositional. }
  erewrite eq_partial_interpret_reindexer_concat_l in H8; eauto. 
  2: { eapply filter_In. propositional.
       erewrite result_has_shape_result_shape_Z by eauto.
       repeat decomp_goal_index. propositional. }
  erewrite eq_partial_interpret_reindexer_concat_l in H8; eauto. 
  2: { eapply filter_In. propositional.
       erewrite result_has_shape_result_shape_Z by eauto.
       repeat decomp_goal_index. propositional. }

  erewrite result_has_shape_result_shape_Z in *.
  2: { eapply result_has_shape_concat; eauto. }
  eapply H in H8.
  invert H8. propositional.
  rewrite H9. propositional.
  eapply filter_In. propositional.
  repeat decomp_goal_index. propositional. simpl in *. lia.
  rewrite <- H12.
  simpl.
  rewrite nth_error_app1.
  reflexivity.
  erewrite result_has_shape_length by eauto.
  lia.
  eapply filter_In. propositional.  
  repeat decomp_goal_index. propositional. simpl in *. lia.
  rewrite <- H10.
  simpl.
  rewrite nth_error_app1.
  reflexivity.
  erewrite result_has_shape_length by eauto.
  lia.
Qed.

Lemma partial_injective_concat_r : forall l1 reindexer l2 v l0 n m,
    partial_injective 
      (partial_interpret_reindexer reindexer
                                   (result_shape_Z (V (l1 ++ l2)%list)) v)
      (filter (fun x => negb
                          (is_None
                             (result_lookup_Z_option x (V (l1 ++ l2)%list))))
              (mesh_grid (result_shape_Z (V (l1 ++ l2)%list)))) ->
    result_has_shape (V l1) (Z.to_nat n :: l0) ->
    result_has_shape (V l2) (m :: l0) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    (forall l1 l2 : list (Zexpr * Z),
        eq_Z_tuple_index_list l1 l2 -> eq_Z_tuple_index_list (reindexer l1)
                                                             (reindexer l2))->
    vars_of_reindexer (reindexer []) \subseteq dom v ->
    (forall (var : var) (k : Z) (l : list (Zexpr * Z)),
        ~ var \in vars_of_reindexer (reindexer []) ->
                  map (subst_var_in_Z_tup var k) (reindexer l) =
                    reindexer (map (subst_var_in_Z_tup var k) l)) ->
    (0 <= n)%Z ->
    (forall l : list (Zexpr * Z),
        vars_of_reindexer (reindexer l) =
          vars_of_reindexer (reindexer []) \cup vars_of_reindexer l) ->
    partial_injective 
      (partial_interpret_reindexer
         (fun l : list (Zexpr * Z) =>
            reindexer
            match l with
            | [] => l
            | (v0, d) :: xs =>
                  (((v0+ | n |)%z, (d + n)%Z) :: xs)
            end) (map Z.of_nat
                      (filter_until (m :: l0) 0)) v)
      (filter (fun x => negb (is_None (result_lookup_Z_option x (V l2))))
              (mesh_grid (map Z.of_nat
                              (filter_until (m :: l0) 0)))).
Proof.
  unfold partial_injective in *. propositional.
  repeat decomp_index.
  erewrite eq_partial_interpret_reindexer_padl; eauto.
  erewrite eq_partial_interpret_reindexer_padl in H10; eauto.
  erewrite eq_partial_interpret_reindexer_padl in H10; eauto. 

  erewrite result_has_shape_result_shape_Z in *.
  2: { eapply result_has_shape_concat; eauto. }
  apply H in H10.
  invert H10.
  invert H11. left. f_equal. lia.
  rewrite H11. propositional.
  eapply filter_In. propositional.
  repeat decomp_goal_index. propositional.
  lia. lia.
  rewrite <- H12.
  simpl.
  rewrite nth_error_app2.
  erewrite result_has_shape_length by eauto.
  rewrite Z2Nat.inj_add.
  rewrite Nat.add_sub.
  cases z0; try lia.
  simpl Z.add at 1.
  cases n; try lia.
  eauto. eauto.
  cases ((Z.pos p + n)%Z); try lia.
  eauto. lia. lia. invert H0. simpl. lia. simpl. lia.
  eapply filter_In. propositional.  
  repeat decomp_goal_index. propositional.
  lia. lia.
  rewrite <- H12.
  simpl.
  rewrite nth_error_app2.
  erewrite result_has_shape_length by eauto.
  rewrite Z2Nat.inj_add.
  rewrite Nat.add_sub.
  cases z; try lia.
  simpl Z.add at 1.
  cases n; try lia.
  eauto. eauto.
  cases ((Z.pos p + n)%Z); try lia.
  eauto. lia. lia. invert H0. simpl. lia. simpl. lia. simpl. lia.
  cbn [eval_Zexpr_Z_total eval_Zexpr_Z]. lia. lia.
Qed.

Lemma partial_injective_concat :
  forall (f g : list Z -> option Z) r0 r2 x2 x1 xs r r1,
partial_injective g
         (filter
            (fun x0 : list Z =>
             negb (is_None (result_lookup_Z_option x0 (V (r0 :: r2)))))
            (mesh_grid
               (Z.of_nat (Datatypes.S x2) :: map Z.of_nat (filter_until xs 0)))) ->
  partial_injective f
         (filter
            (fun x0 : list Z =>
             negb (is_None (result_lookup_Z_option x0 (V (r :: r1)))))
            (mesh_grid
               (Z.of_nat (Datatypes.S x1) :: map Z.of_nat (filter_until xs 0)))) ->
  constant
        (extract_Some
           (map f
              (filter
                 (fun x0 : list Z =>
                  negb (is_None (result_lookup_Z_option x0 (V (r :: r1)))))
                 (mesh_grid
                    (Z.of_nat (Datatypes.S x1) :: map Z.of_nat (filter_until xs 0)))))) \cap
      constant
        (extract_Some
           (map g
              (filter
                 (fun x0 : list Z =>
                  negb (is_None (result_lookup_Z_option x0 (V (r0 :: r2)))))
                 (mesh_grid (map Z.of_nat (Datatypes.S x2 :: filter_until xs 0)))))) =
      constant [] ->
      result_has_shape (V (r :: r1)) (Datatypes.S x1 :: xs) ->
  result_has_shape (V (r0 :: r2)) (Datatypes.S x2 :: xs) ->
  partial_injective
    (fun x0 : list Z =>
     match x0 with
     | [] => None
     | x3 :: xs0 =>
         if (x3 <? Z.of_nat (Datatypes.S x1))%Z
         then f (x3 :: xs0)
         else g ((x3 - Z.of_nat (Datatypes.S x1))%Z :: xs0)
     end)
    (filter
       (fun x0 : list Z =>
        negb (is_None (result_lookup_Z_option x0 (V ((r :: r1) ++ r0 :: r2)))))
       (mesh_grid (Z.of_nat (Datatypes.S x1) :: map Z.of_nat (filter_until xs 0)) ++
        map
          (fun l : list Z =>
           match l with
           | [] => l
           | i :: is => (i + Z.of_nat (Datatypes.S x1))%Z :: is
           end)
          (mesh_grid (Z.of_nat (Datatypes.S x2) :: map Z.of_nat (filter_until xs 0))))).
Proof.
  unfold partial_injective.
  propositional.
  repeat decomp_index.
  eapply in_app_or in H7,H5.
  propositional.
  - repeat decomp_index.
    invert H5. invert H7.
    pose proof H12. pose proof H13.
    eapply Z.ltb_lt in H12,H13.
    rewrite H12,H13 in *.
    eapply H0 in H6.
    propositional.
    eapply filter_In. propositional. repeat decomp_goal_index.
    propositional. repeat decomp_goal_index. auto.
    rewrite <- H9.
    simpl. rewrite app_comm_cons. rewrite nth_error_app1. auto.
    erewrite result_has_shape_length by eauto. lia.
    eapply filter_In. propositional. repeat decomp_goal_index.
    propositional. repeat decomp_goal_index. auto.
    rewrite <- H8.
    simpl. rewrite app_comm_cons. rewrite nth_error_app1. auto.
    erewrite result_has_shape_length by eauto. lia.
  - eapply in_map_iff in H7. invs.
    repeat decomp_index.
    cases (z + Z.of_nat (Datatypes.S x1) <? Z.of_nat (Datatypes.S x1))%Z.
    eapply Z.ltb_lt in Heq. lia.
    invert H10. pose proof H12.
    eapply Z.ltb_lt in H12. rewrite H12 in *.
    rewrite Z.add_simpl_r in *.
    rewrite cap_empty_exclusion in H1.
    cases (g (z::x)). 2: propositional.
    specialize (H1 z1).
    repeat rewrite <- In_iff_in in H1.
    repeat rewrite <- in_extract_Some in H1.
    invs.
    rewrite <- Heq0 in H15 at 1.
    rewrite <- Heq0 in H5 at 2.
    rewrite H6 in H5,H15.
    assert (In (g (z :: x))
               (map g
                    (filter
                       (fun x0 =>
                          negb
                            (is_None
                               (result_lookup_Z_option x0 (V (r0 :: r2)))))
                       (mesh_grid
                          (map Z.of_nat
                               (Datatypes.S x2 :: filter_until xs 0)))))).
    { eapply in_map.
      eapply filter_In. propositional. simpl map.
      repeat decomp_goal_index.
      propositional.
      repeat decomp_goal_index. propositional.
      rewrite <- H9.
      simpl. rewrite app_comm_cons.
      rewrite nth_error_app2.
      cases z; try lia.
      - simpl is_None at 2.
        repeat f_equal. eq_match_discriminee. f_equal.
        invert H2.
        lia.
      - cases (Z.pos p + Z.pos (Pos.of_succ_nat x1))%Z; try lia.
        repeat f_equal. eq_match_discriminee. f_equal.
        invert H2. simpl.
        lia.
      - invert H2. simpl. lia. }
    propositional.
    exfalso. apply H16.
    eapply in_map.
    eapply filter_In. propositional. simpl map.
    repeat decomp_goal_index.
    propositional.
    repeat decomp_goal_index. propositional.
    rewrite <- H8.
    simpl.
    rewrite app_comm_cons. rewrite nth_error_app1. auto.
    erewrite result_has_shape_length by eauto. lia.
  - eapply in_map_iff in H4. invs.
    repeat decomp_index.
    invert H10.
    pose proof H12.
    eapply Z.ltb_lt in H12. rewrite H12 in *.
    cases (z + Z.of_nat (Datatypes.S x1) <? Z.of_nat (Datatypes.S x1))%Z.
    eapply Z.ltb_lt in Heq. lia.
    rewrite Z.add_simpl_r in *.
    rewrite cap_empty_exclusion in H1.
    cases (f (z0::args1)). 2: propositional.
    specialize (H1 z1).
    repeat rewrite <- In_iff_in in H1.
    repeat rewrite <- in_extract_Some in H1.
    invs.
    rewrite <- Heq0 in H15 at 2.
    rewrite <- Heq0 in H4 at 1.
    rewrite H6 in H4,H15.
    assert (In (f (z0 :: args1))
               (map f
                    (filter
                       (fun x0 =>
                          negb
                            (is_None
                               (result_lookup_Z_option x0 (V (r :: r1)))))
                       (mesh_grid
                          (Z.of_nat (Datatypes.S x1)
                                    :: map Z.of_nat (filter_until xs 0)))))).
    { eapply in_map.
      eapply filter_In. propositional. simpl map.
      repeat decomp_goal_index.
      propositional.
      repeat decomp_goal_index. propositional.
      rewrite <- H9.
      simpl. rewrite app_comm_cons.
      rewrite nth_error_app1.
      auto.
      erewrite result_has_shape_length by eauto. lia. }
    propositional.
    exfalso. apply H16.
    eapply in_map.
    eapply filter_In. propositional. simpl map.
    repeat decomp_goal_index.
    propositional.
    repeat decomp_goal_index. propositional.
    rewrite <- H8.
    simpl.
    rewrite app_comm_cons. rewrite nth_error_app2.
    cases z; try lia.
    + simpl is_None at 2.
      repeat f_equal. eq_match_discriminee. f_equal. invert H2. lia.
    + cases (Z.pos p + Z.pos (Pos.of_succ_nat x1))%Z; try lia.
      repeat f_equal. eq_match_discriminee. f_equal. invert H2. simpl. lia.
    + erewrite result_has_shape_length by eauto. lia.
  - eapply in_map_iff in H4,H7. invs.
    repeat decomp_index.
    cases (z0 + Z.of_nat (Datatypes.S x1) <? Z.of_nat (Datatypes.S x1))%Z.
    eapply Z.ltb_lt in Heq. lia.
    cases (z + Z.of_nat (Datatypes.S x1) <? Z.of_nat (Datatypes.S x1))%Z.
    eapply Z.ltb_lt in Heq0. lia.
    rewrite Z.add_simpl_r in *.
    eapply H in H6.
    propositional. invert H7.
    rewrite Z.add_simpl_r. propositional.
    eapply filter_In. propositional.
    repeat decomp_goal_index. propositional.
    repeat decomp_goal_index. propositional.
    rewrite <- H9.
    simpl. rewrite app_comm_cons.
    rewrite nth_error_app2.
    cases z0; try lia.
    + simpl is_None at 2.
      repeat f_equal. eq_match_discriminee. f_equal. invert H2. lia.
    + cases (Z.pos p + Z.pos (Pos.of_succ_nat x1))%Z; try lia.
      repeat f_equal. eq_match_discriminee. f_equal. invert H2. simpl. lia.
    + simpl. invert H2. lia.
    + rewrite Z.add_simpl_r.
      eapply filter_In. propositional.      
      repeat decomp_goal_index. propositional.
      repeat decomp_goal_index. propositional.
      rewrite <- H8.
      simpl.
      cases z; try lia.
      * simpl is_None at 2. rewrite app_comm_cons.
        rewrite nth_error_app2.
        repeat f_equal. eq_match_discriminee. f_equal. invert H2. simpl. lia.
        erewrite result_has_shape_length by eauto. lia.
      * cases (Z.pos p + Z.pos (Pos.of_succ_nat x1))%Z; try lia.
        rewrite app_comm_cons.
        rewrite nth_error_app2.
        repeat f_equal. eq_match_discriminee. f_equal. invert H2. simpl. lia.
        erewrite result_has_shape_length by eauto. lia.
Qed.

Lemma injective_cons {X Y} : forall a d (f : X -> Y),
    injective (a::d) f ->
    injective d f.
Proof.
  unfold injective. propositional.
  specialize (H args1 args2). simpl in *.
  propositional.
Qed.

Lemma no_dup_injective_map {X Y} : forall d (f : X -> Y),
    injective d f ->
    no_dup d ->
    no_dup (map f d).
Proof.
  induct d; intros.
  - simpl. econstructor.
  - simpl. invert H0.
    econstructor. eapply IHd; eauto.
    eapply injective_cons. eauto.
    erewrite in_map_iff. 
    unfold not. intros. invs.
    unfold injective in H.
    specialize (H x a). simpl in H. propositional.
    subst. propositional.
Qed.

Lemma eq_partial_interpret_reindexer_flatten :
  forall z z0 n m x l0 v reindexer,
  (0 <= z < Z.of_nat n)%Z ->
  (0 <= z0 < Z.of_nat m)%Z ->
  In x (mesh_grid (map Z.of_nat l0)) ->
  (forall var : var, contains_substring "?" var -> var \in dom v -> False)->
  (forall l1 l2 : list (Zexpr * Z),
      eq_Z_tuple_index_list l1 l2 ->
      eq_Z_tuple_index_list (reindexer l1) (reindexer l2)) ->
  vars_of_reindexer (reindexer []) \subseteq dom v ->
  (forall (var : var) (k : Z) (l : list (Zexpr * Z)),
      (var \in vars_of_reindexer (reindexer []) -> False) ->
      map (subst_var_in_Z_tup var k) (reindexer l) =
        reindexer (map (subst_var_in_Z_tup var k) l)) ->    
  partial_interpret_reindexer
    reindexer
    (map Z.of_nat
         (filter_until (n * m :: l0) 0)) v
    ((z * Z.of_nat m + z0)%Z :: x) =
    partial_interpret_reindexer
      (fun l4 : list (Zexpr * Z) =>
         reindexer
           match l4 with
           | [] => l4
           | [(v0, d)] => l4
           | (v0, d) :: (vi, di) :: xs =>
               ((v0 * | di | + vi)%z, (d * di)%Z) :: xs
           end)
      (map Z.of_nat
           (filter_until
              (n :: m :: l0) 0)) v 
      (z :: z0 :: x).
Proof.
  intros ? ? ? ? ? ? ? ? Hz Hz0 Hx Henv HeqZlist Hvarsub Hmap.
  unfold partial_interpret_reindexer.
  simpl.
  cases n; try lia.
  cases m; try lia.
  simpl. unfold shape_to_vars. simpl.
  rewrite shape_to_index_cons.
  repeat rewrite index_to_partial_function_vars_cons; eauto with reindexers.
  repeat rewrite Hmap;
    try eapply not_var_generation_in_index;
    try eapply not_var_generation_in_index2; eauto.
  simpl.
  unfold shape_to_index.
  repeat rewrite map_subst_var_in_Z_tup_combine_not_in; eauto with reindexers.
  unfold subst_var_in_Z_tup. simpl.
  rewrite index_to_partial_function_subst_vars; eauto with reindexers.
  2: { rewrite length_map. rewrite length_nat_range_rec. rewrite length_map.
       eapply length_mesh_grid_indices.
       repeat decomp_goal_index. auto. }
  symmetry.
  rewrite index_to_partial_function_subst_vars; eauto with reindexers.
  2: { rewrite length_map. rewrite length_nat_range_rec. rewrite length_map.
       eapply length_mesh_grid_indices.
       repeat decomp_goal_index. auto. }
  symmetry.
  rewrite map_fold_left_subst_var_in_Z_tup_reindexer; eauto with reindexers.
  symmetry.
  rewrite map_fold_left_subst_var_in_Z_tup_reindexer; eauto with reindexers.
  symmetry.
  simpl.
  rewrite map_fold_left_subst_var_in_Z_tup_combine; eauto with reindexers.
  2: { rewrite length_map. rewrite length_nat_range_rec. rewrite length_map.
       eapply length_mesh_grid_indices.
       repeat decomp_goal_index. auto. }
  rewrite map_fold_left_subst_var_in_Z_tup_combine; eauto with reindexers.
  2: { rewrite length_map. rewrite length_nat_range_rec. rewrite length_map.
       eapply length_mesh_grid_indices.
       repeat decomp_goal_index. auto. }
  rewrite fold_left_subst_var_in_Z_tup_id.
  2: { sets. }
  rewrite fold_left_subst_var_in_Z_tup_id.
  2: { sets. }
  erewrite <- eq_index_to_partial_function. reflexivity.
  eapply eq_Z_tuple_index_list_partially_eval_Z_tup.
  eapply HeqZlist.
  erewrite <- eq_Z_tuple_index_list_cons_tup. propositional.
  eapply eq_zexpr_transitivity.
  eapply eq_zexpr_add.
  eapply eq_zexpr_mul_literal. eauto.
  eapply eq_zexpr_add_literal. lia.
  eapply eq_Z_tuple_index_list_id.
Qed.

Lemma partial_injective_flatten :
  forall reindexer v n m l0 l,
    result_has_shape (V l) (n :: m :: l0) ->
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
    partial_injective
      (partial_interpret_reindexer
         reindexer
         (map Z.of_nat
              (filter_until
                 (n * m :: l0) 0)) v)
      (filter
         (fun x : list Z =>
            negb (is_None (result_lookup_Z_option x (V (flatten_result l)))))
         (mesh_grid
            (map Z.of_nat
                 (filter_until
                    (n * m :: l0) 0)))) ->
    (forall var : var, contains_substring "?" var -> var \in dom v -> False)->
    partial_injective
      (partial_interpret_reindexer
         (fun l4 : list (Zexpr * Z) =>
            reindexer
              match l4 with
              | [] => l4
              | [(v0, d)] => l4
              | (v0, d) :: (vi, di) :: xs =>
                  ((v0 * | di | + vi)%z, (d * di)%Z) :: xs
              end)
         (map Z.of_nat
              (filter_until
                 (n :: m :: l0) 0)) v)
      (filter (fun x => negb (is_None (result_lookup_Z_option x (V l))))
              (mesh_grid
                 (map Z.of_nat
                      (filter_until
                         (n :: m :: l0) 0)))).
Proof.
  intros ? ? ? ? ? ? Hsh HeqZlist Hvarsub Hmap Hvarsarg Hinj.
  unfold partial_injective. propositional. repeat decomp_index.
  erewrite <- eq_partial_interpret_reindexer_flatten in H2;
    eauto with reindexers.
  erewrite <- eq_partial_interpret_reindexer_flatten in H2;
    eauto with reindexers.
  eapply Hinj in H2.
  propositional.
  rewrite Z.mul_comm in H5. symmetry in H5.
  rewrite Z.mul_comm in H5. symmetry in H5.
  invert H5.
  eapply Z.div_mod_unique in H14. invs. propositional.
  lia. lia.
  erewrite <- eq_partial_interpret_reindexer_flatten;
    eauto with reindexers.
  eapply filter_In. propositional.
  repeat decomp_goal_index. propositional. lia.
  rewrite Nat2Z.inj_mul.
  eapply mul_add_lt. lia. lia. lia. lia.
  rewrite <- H7.
  erewrite result_lookup_Z_option_flatten. reflexivity.
  lia. eassumption. eassumption. eassumption. eassumption. auto.
  eapply filter_In. propositional.
  repeat decomp_goal_index. propositional. lia.
  rewrite Nat2Z.inj_mul.
  eapply mul_add_lt. lia. lia. lia. lia.
  rewrite <- H4.
  erewrite result_lookup_Z_option_flatten. reflexivity.
  lia. eassumption. eassumption. eassumption. eassumption. auto.
Qed.

Lemma filter_negb_is_None_result_lookup_Z_option_gen_pad : forall sh l,
      filter
       (fun x => negb (is_None (result_lookup_Z_option x (gen_pad sh))))
       l = [].
Proof.
  intros. eapply filter_empty.
  eapply Forall_forall. intros.
  rewrite result_lookup_Z_option_gen_pad. reflexivity.
Qed.

Lemma partial_injective_split :
  forall reindexer n l0 k v l,
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
result_has_shape (V l) (n :: l0) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
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
    (0 < k)%Z ->
    partial_injective
    (partial_interpret_reindexer
       (fun l2 : list (Zexpr * Z) =>
        reindexer
          match l2 with
          | [] => l2
          | (v0, d) :: xs => ((v0 / | k |)%z, (d // k)%Z) :: ((v0 % | k |)%z, k) :: xs
          end) (result_shape_Z (V l)) v)
    (filter (fun x : list Z => negb (is_None (result_lookup_Z_option x (V l))))
       (mesh_grid (result_shape_Z (V l)))).      
Proof.
  intros ? ? ? ? ? ? Hinj Hsh Hvar HeqZwraplist Hvarsub Hmap
         Hvarrdx Hknonneg.
  erewrite result_has_shape_result_shape_Z in *.
  2: { eapply result_has_shape_split_result. lia. eauto. }
  2: { eauto. }
  unfold partial_injective. propositional.
  
  repeat decomp_index.
  simpl. cases n; simpl ; try lia.
  posnats.
  rewrite <- map_cons.
  rewrite <- filter_until_0_cons.
  erewrite eq_partial_interpret_reindexer_split in H1; eauto.
  erewrite eq_partial_interpret_reindexer_split in H1; eauto.
  eapply Hinj in H1.
  rewrite (Z_div_mod_eq_full z0 k) at 1 by lia.
  rewrite (Z_div_mod_eq_full z k) at 1 by lia.     
  propositional.
  + invert H. auto.
  + erewrite eq_partial_interpret_reindexer_split; eauto.
  + eapply filter_In. propositional.
    rewrite mesh_grid_filter_until. simpl map.
    repeat decomp_goal_index. propositional.
    eapply Z.div_pos. lia. lia.
    rewrite <- of_nat_div_distr.
    rewrite Z2Nat.id by lia.
    eapply floor_lt_ceil_mono_l. lia. lia. lia. lia.
    repeat decomp_goal_index.
    split. split. eapply mod_nonneg. lia.
    rewrite Z2Nat.id by lia. eapply mod_upper_bound. lia. auto.
    rewrite <- H5. f_equal. f_equal.
    rewrite <- (Z2Nat.id k) at 1 by lia.
    rewrite <- (Z2Nat.id k) at 2 by lia.    
    erewrite result_lookup_Z_option_split. reflexivity.
    eauto. lia. eassumption. lia. eauto.
  + eapply filter_In. propositional.
    rewrite mesh_grid_filter_until. simpl map.
    repeat decomp_goal_index. propositional.
    eapply Z.div_pos. lia. lia.
    rewrite <- of_nat_div_distr.
    rewrite Z2Nat.id by lia.    
    eapply floor_lt_ceil_mono_l. lia. lia. lia. lia.
    repeat decomp_goal_index.
    split. split. eapply mod_nonneg. lia.
    rewrite Z2Nat.id by lia. eapply mod_upper_bound. lia. auto.
    rewrite <- H3. f_equal. f_equal.
    rewrite <- (Z2Nat.id k) at 1 by lia.
    rewrite <- (Z2Nat.id k) at 2 by lia.    
    erewrite result_lookup_Z_option_split. reflexivity.
    eauto. lia. eassumption. lia. eauto.
  + lia.
Qed.

Lemma eq_partial_interpret_reindexer_padr:
  forall (reindexer : list (Zexpr * Z) -> list (Zexpr * Z)) 
    (k m : nat) (l0 : list nat) (z : Z) (v : fmap var Z) 
    (x1 : list Z),
  (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
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
  (0 < m)%nat ->
  partial_interpret_reindexer
    (fun l : list (Zexpr * Z) =>
     reindexer
       match l with
       | [] => l
       | (v0, d) :: xs => (v0, (d + Z.of_nat k)%Z) :: xs
       end)
    (map Z.of_nat
       (filter_until
          (m :: l0) 0)) v 
    (z :: x1) =
  partial_interpret_reindexer reindexer
    (map Z.of_nat
       (filter_until
          (k + m :: l0) 0)) v
    (z :: x1).
Proof.
    intros ? ? ? ? ? ? ? Hvar HeqZlistwrap Hvarsub Hmap
         Hvarrdx Hmnonneg.
  unfold partial_interpret_reindexer.
  unfold shape_to_vars in *. simpl.
  cases m. lia.
  simpl.
  rewrite Nat.add_succ_r in *.
  simpl shape_to_index at 1.
  rewrite shape_to_index_cons.
  posnats. simpl.
  repeat rewrite index_to_partial_function_vars_cons; eauto with reindexers.
  repeat rewrite Hmap; eauto with reindexers.
  repeat rewrite map_cons.
  repeat rewrite map_subst_var_in_Zexpr_shape_to_index_id;
    eauto with reindexers.
  rewrite map_subst_var_in_Z_tup_combine_not_in; eauto with reindexers.
  unfold subst_var_in_Z_tup. simpl.
  erewrite eq_index_to_partial_function. reflexivity.
  eapply eq_Z_tuple_index_list_partially_eval_Z_tup.
  eapply HeqZlistwrap.
  erewrite <- eq_Z_tuple_index_list_cons.
  split.
  2: eapply eq_Z_tuple_index_list_id.
  unfold eq_Z_tup. simpl.
  split. eauto. lia.
Qed.

