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
From Lower Require Import Zexpr Bexpr Array Range Sexpr Result ListMisc Meshgrid VarGeneration
     Constant.

Definition shift_top_dim_reindexer
           (reindexer : list (Zexpr * Zexpr) -> list (Zexpr * Zexpr)) :=
  fun l => match l with
           | (var,dim)::xs => reindexer
                                ((var + | 1 |,dim + | 1 |)%z :: xs)
           | _ => reindexer l
           end.

Hint Resolve no_dup_var_generation no_dup_mesh_grid
     forall_map_not_in_index forall_map_not_in_dom
     not_In_var_map2 not_In_var_map
     not_var_generation_in_dom2 not_var_generation_in_index2
     not_var_generation_in_index not_var_generation_in_dom : reindexers.
Hint Extern 3 (Datatypes.length _ = Datatypes.length _) =>
       rewrite map_length; rewrite length_nat_range_rec;
       eapply length_mesh_grid_indices; eassumption : reindexers.

Lemma flatten_index_to_function_alt : forall sh args,
    length sh = length args ->
    flatten sh args =
      index_to_function_alt (combine (map ZLit args) (map ZLit sh)) [] [].
Proof.
  induction sh; intros; cases args; auto.
  simpl. unfold flatten. cases sh; auto.
  cases sh; cases args; simpl in *; try lia.
  unfold index_to_function_alt. simpl. reflexivity.  
  simpl. rewrite IHsh.
  unfold index_to_function_alt.
  unfold index_to_function_rec_alt.
  simpl.
  erewrite eval_Zexpr_Z_flatten_index_flatten.
  2: { econstructor. eauto. rewrite map_snd_combine
      by (repeat rewrite map_length; simpl; try lia).
       eapply eval_Zexprlist_map_ZLit. }
  2: { econstructor. eauto. rewrite map_fst_combine
      by (repeat rewrite map_length; simpl; try lia).
       eapply eval_Zexprlist_map_ZLit. }
  rewrite map_snd_combine
    by (repeat rewrite map_length; simpl; try lia).
  erewrite eval_Zexpr_Z_fold_left_ZTimes.
  2: eapply eval_Zexprlist_map_ZLit.
  2: eauto.
  unfold flatten_index. simpl.
  rewrite map_snd_combine
    by (repeat rewrite map_length; simpl; try lia).
  rewrite map_fst_combine
    by (repeat rewrite map_length; simpl; try lia).
  erewrite eval_Zexpr_Z_flatten_index_flatten.
  2: { econstructor. eauto. eapply eval_Zexprlist_map_ZLit. }
  2: { econstructor. eauto. eapply eval_Zexprlist_map_ZLit. }
  reflexivity.
  simpl in *. lia.
Qed.

Definition interpret_reindexer
           (reindexer : list (Zexpr * Zexpr) -> list (Zexpr * Zexpr))
           (sh : list Z) (v : valuation) : list Z -> Z :=
  let vars := shape_to_vars sh in
  let result_index := shape_to_index sh vars in
  let full_index := reindexer result_index in
  let evaled_index := map (partially_eval_Z_tup v) full_index in
  index_to_function_alt evaled_index vars.

Lemma interpret_reindexer_id_flatten : forall sh x v,
    In x (mesh_grid sh) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    (interpret_reindexer (fun l : list (Zexpr * Zexpr) => l) sh v) x =
      flatten sh x.
Proof.
  induct sh; intros.
  - simpl in *. propositional. subst.
    reflexivity.
  - cases x.
    eapply not_In_empty_map2_cons in H; propositional.
    unfold interpret_reindexer.
    unfold shape_to_vars.
    simpl length. unfold nat_range. simpl nat_range_rec.
    rewrite map_cons.
    rewrite shape_to_index_cons.
    rewrite index_to_function_alt_vars_cons; eauto with reindexers.
    rewrite map_cons.
    unfold subst_var_in_Z_tup at 1. simpl subst_var_in_Zexpr.
    rewrite map_subst_var_in_Zexpr_shape_to_index_id.
    2: simpl; eauto with reindexers.
    rewrite index_to_function_alt_subst_vars.
    rewrite map_cons.
    rewrite fold_left_subst_var_in_Z_tup_ZLit.
    rewrite map_fold_left_subst_var_in_Z_tup_shape_to_index.
    simpl.
    rewrite map_partially_eval_Z_tup_ZLit. simpl.
    rewrite flatten_index_to_function_alt.
    reflexivity.
    eapply length_mesh_grid_indices_Z. auto.
    rewrite map_length. rewrite length_nat_range_rec.
    eapply length_mesh_grid_indices_Z in H. simpl in *. lia.
    eapply no_dup_var_generation.
    eauto with reindexers.
Qed.    

Lemma constant_interpret_reindexer_id_flatten : forall sh v,
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
  constant (map (interpret_reindexer (fun l => l) sh v) (mesh_grid sh)) =
    constant (map (flatten sh) (mesh_grid sh)).
Proof.
  intros. f_equal.
  eapply map_extensionality. intros.
  eapply interpret_reindexer_id_flatten. auto. auto.
Qed.

Lemma constant_interpret_reindexer_id_flatten_filter : forall v r,
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    constant (map (interpret_reindexer (fun l => l) (result_shape_Z r) v)
                  (filter
                     (fun x =>
                        negb (is_None
                                (result_lookup_Z_option x r)))
                     (mesh_grid (result_shape_Z r)))) =
    constant (map (flatten (result_shape_Z r)) (filter
                     (fun x =>
                        negb (is_None
                                (result_lookup_Z_option x r)))
                     (mesh_grid (result_shape_Z r)))).
Proof.
  intros. f_equal.
  eapply map_extensionality. intros.
  eapply interpret_reindexer_id_flatten.
  repeat decomp_index. propositional. auto.
Qed.

Lemma dom_interpret_reindexer_id :
  forall sh v,
    (Forall (fun x => 0 <= x)%Z sh) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    constant (map (interpret_reindexer (fun l => l) sh v) (mesh_grid sh)) =
      constant (zrange 0 (fold_left Z.mul sh 1%Z)).
Proof.
  intros.
  rewrite constant_interpret_reindexer_id_flatten.
  apply sets_equal. intros. split; intros.
  - pose proof (@In_iff_in Z).
    eapply H2.
    erewrite <- H2.
    eapply H2 in H1.
    clear H2.
    eapply in_map_iff in H1. invs.
    apply in_mesh_grid_flatten_in_range; auto.
  - pose proof (@In_iff_in Z).
    eapply H2.
    erewrite <- H2.
    eapply H2 in H1.
    clear H2.
    pose proof (in_zrange'_lower_bound _ _ _ H1).
    pose proof (in_zrange'_upper_bound _ _ _ H1).
    rewrite Z.sub_0_r in H3.
    rewrite Z.add_0_l in H3.
    rewrite Z2Nat.id in H3.
    eapply in_range_in_flatten; auto.
    eapply fold_left_mul_nonneg.
    eapply Forall_impl. 2: eassumption.
    intros. simpl in *. lia. lia.
  - auto.
Qed.
    
Lemma vars_of_shift_top_dim_reindexer : forall reindexer l,
    ((forall l : list (Zexpr * Zexpr),
         vars_of_reindexer (reindexer l) =
           vars_of_reindexer (reindexer []) \cup vars_of_reindexer l)) ->
    vars_of_reindexer (shift_top_dim_reindexer reindexer l) =
      vars_of_reindexer (reindexer l).
Proof.
  unfold shift_top_dim_reindexer. intros.
  cases l.
  - reflexivity.
  - cases p. erewrite H. symmetry. erewrite H. symmetry.
    simpl. repeat rewrite app_no_dups_empty_r.
    reflexivity.
Qed.

Definition index_to_partial_function
           (index : list (Zexpr * Zexpr)) vars (args : list Z) : option Z
  :=
  if (length vars =? length args)%nat
  then let evaled_list_index :=
         map (eval_Zexpr_Z_tup_total $0)
             (map (fun tup =>
                     (fold_left
                        (fun (z : Zexpr * Zexpr) (tup : string * Z) =>
                           subst_var_in_Z_tup (fst tup) (snd tup) z)
                        (combine vars args) tup)) index) in
       Some (flatten
               (map (fun o => match o with
                              | Some x => snd x
                              | None => 0%Z
                              end) evaled_list_index)
               (map (fun o => match o with
                              | Some x => fst x
                              | None => 0%Z
                              end) evaled_list_index))
  else None.

Definition partial_interpret_reindexer
           (reindexer : list (Zexpr * Zexpr) -> list (Zexpr * Zexpr))
           (sh : list Z) (v : valuation) : list Z -> option Z :=
  let vars := shape_to_vars sh in
  let result_index := shape_to_index sh vars in
  let full_index := reindexer result_index in
  let evaled_index := map (partially_eval_Z_tup v) full_index in
  index_to_partial_function evaled_index vars.

Lemma flatten_index_to_partial_function : forall sh args,
    In args (mesh_grid sh) ->
    Some (flatten sh args) =
      index_to_partial_function (combine (map ZLit args) (map ZLit sh)) [] [].
Proof.
  induction sh; intros; cases args; auto.
  simpl. unfold flatten. cases sh; auto.
  decomp_index.
  unfold index_to_partial_function. simpl.
  propositional.
  replace (0 <=? z)%Z with true.
  2: { symmetry. eapply Z.leb_le. lia. }
  replace (z <? a)%Z with true.
  2: { symmetry. eapply Z.ltb_lt. lia. }
  simpl.
  rewrite map_id. rewrite map_eval_Zexpr_Z_tup_total_ZLit.
  2: { symmetry. eapply length_mesh_grid_indices_Z. auto. }
  rewrite map_map. rewrite map_map.
  rewrite map_snd_combine.
  2: { symmetry. eapply length_mesh_grid_indices_Z. auto. }
  rewrite map_fst_combine.
  2: { symmetry. eapply length_mesh_grid_indices_Z. auto. }
  reflexivity.
Qed.

Ltac eq_if_discriminee :=
  match goal with
  | |- (if ?p0 then _ else _) = if ?p1 then _ else _ =>
      assert (p0 = p1)
  | H : (if ?p0 then _ else _) = if ?p1 then _ else _ |- _=>
      assert (p0 = p1)
  end.

Lemma index_to_partial_function_vars_cons :
  forall var vars k x
         (reindexer : list (Zexpr * Zexpr) -> list (Zexpr * Zexpr)) v l,
    ~ var \in dom v ->
              index_to_partial_function
      (map (partially_eval_Z_tup v)
           (reindexer l)) (var::vars) (k :: x) = 
      index_to_partial_function      
        (map (partially_eval_Z_tup v)
             (map (fun e => (subst_var_in_Z_tup var k e))
                  (reindexer l))) vars x.
Proof.
  intros. unfold index_to_partial_function.
  simpl in *.
  cases ((Datatypes.length vars =? Datatypes.length x)%nat); auto.
  f_equal. f_equal.
  symmetry.
  replace (map (partially_eval_Z_tup v)
               (map (fun e => subst_var_in_Z_tup var k e) (reindexer l))) with
    (map (fun e => subst_var_in_Z_tup var k e)
         (map (partially_eval_Z_tup v) (reindexer l))).
    2: { repeat rewrite map_map. f_equal.
         eapply functional_extensionality. intros.
         eapply subst_var_in_Z_tup_partially_eval_Z_tup_comm. auto. }
    repeat rewrite map_map. reflexivity.
    repeat rewrite map_map.
    f_equal.
    eapply functional_extensionality. intros. simpl.
    repeat rewrite subst_var_in_Z_tup_partially_eval_Z_tup_comm.
    reflexivity.
    auto.
Qed.

Lemma index_to_partial_function_subst_vars :
  forall vars x (rdxr : list (Zexpr * Zexpr) -> list (Zexpr * Zexpr)) l v,
    (Forall (fun var =>  ~ var \in dom v) vars) ->
    length vars = length x ->
    index_to_partial_function
      (map (partially_eval_Z_tup v) (rdxr l)) vars x =
      index_to_partial_function
        (map (partially_eval_Z_tup v)
             (map (fun y =>
                     fold_left (fun a t => subst_var_in_Z_tup
                                             (fst t) (snd t) a)
                               (combine vars x) y) (rdxr l))) [] [].
Proof.
  induct vars; intros; cases x; simpl in *; try lia.
  - rewrite map_map. reflexivity.
  - invert H.
    rewrite index_to_partial_function_vars_cons by auto.
    rewrite IHvars by (auto; lia).
    repeat rewrite map_map.
    reflexivity.
Qed.

Lemma partial_interpret_reindexer_id_flatten : forall sh x v,
    In x (mesh_grid sh) ->
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    (partial_interpret_reindexer (fun l : list (Zexpr * Zexpr) => l) sh v) x =
      Some (flatten sh x).
Proof.
  induct sh; intros.
  - simpl in *. propositional. subst.
    reflexivity.
  - repeat decomp_index.
    unfold partial_interpret_reindexer.
    unfold shape_to_vars.
    simpl length. unfold nat_range. simpl nat_range_rec.
    rewrite map_cons.
    rewrite shape_to_index_cons.
    rewrite index_to_partial_function_vars_cons; eauto with reindexers.
    rewrite map_cons.
    unfold subst_var_in_Z_tup at 1. simpl subst_var_in_Zexpr.
    rewrite map_subst_var_in_Zexpr_shape_to_index_id.
    2: simpl; eauto with reindexers.
    rewrite index_to_partial_function_subst_vars.
    rewrite map_cons.
    rewrite fold_left_subst_var_in_Z_tup_ZLit.
    rewrite map_fold_left_subst_var_in_Z_tup_shape_to_index.
    simpl.
    rewrite map_partially_eval_Z_tup_ZLit. simpl.
    unfold partially_eval_Z_tup. simpl.
    rewrite flatten_index_to_partial_function.
    reflexivity.
    erewrite <- in_mesh_grid_cons__. propositional.

    rewrite map_length. rewrite length_nat_range_rec.    
    eapply length_mesh_grid_indices_Z. auto.
    eapply no_dup_var_generation.
    eauto with reindexers.
    rewrite map_length. rewrite length_nat_range_rec.
    eapply length_mesh_grid_indices_Z. auto.
Qed.

Lemma constant_partial_interpret_reindexer_id_flatten:
  forall (sh : list Z) (v : fmap var Z),
  (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
  constant
    (extract_Some
       (map (partial_interpret_reindexer (fun l => l) sh v)
            (mesh_grid sh))) = constant (map (flatten sh) (mesh_grid sh)).
Proof.
  intros.
  apply sets_equal.
  propositional; eapply In_iff_in; rewrite <- In_iff_in;
    eapply In_iff_in in H0. 
  - rewrite <- in_extract_Some in H0.
    rewrite in_map_iff in *. invs.
    rewrite partial_interpret_reindexer_id_flatten in *; auto.
    invert H0. eauto.
  - rewrite <- in_extract_Some.
    rewrite in_map_iff in *. invs.
    eexists.
    rewrite partial_interpret_reindexer_id_flatten in *; auto.
Qed.  

Lemma constant_partial_interpret_reindexer_id_flatten_filter:
  forall (v : fmap var Z) r,
  (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
  constant
    (extract_Some
       (map (partial_interpret_reindexer (fun l => l) (result_shape_Z r) v)
            (filter
                     (fun x =>
                        negb (is_None
                                (result_lookup_Z_option x r)))
                     (mesh_grid (result_shape_Z r))))) =
    constant (map (flatten (result_shape_Z r)) (filter
                     (fun x =>
                        negb (is_None
                                (result_lookup_Z_option x r)))
                     (mesh_grid (result_shape_Z r)))).
Proof.
  intros.
  apply sets_equal.
  propositional; eapply In_iff_in; rewrite <- In_iff_in;
    eapply In_iff_in in H0. 
  - rewrite <- in_extract_Some in H0.
    rewrite in_map_iff in *. invs.
    rewrite partial_interpret_reindexer_id_flatten in *; auto.
    invert H0. eauto. decomp_index.
    propositional.
  - rewrite <- in_extract_Some.
    rewrite in_map_iff in *. invs.
    eexists.
    rewrite partial_interpret_reindexer_id_flatten in *; auto.
    decomp_index. propositional.
Qed.  

Lemma partial_interpret_reindexer_vars_None :
  forall reindexer sh v args,
    length sh <> length args ->
    partial_interpret_reindexer reindexer sh v args = None.
Proof.
  unfold partial_interpret_reindexer. unfold index_to_partial_function.
  intros. unfold shape_to_vars.
  rewrite map_length. unfold nat_range. rewrite length_nat_range_rec.  
  eapply Nat.eqb_neq in H. rewrite H. auto.
Qed.

Lemma partial_interpret_reindexer_vars_Some :
  forall reindexer sh v args x,
    partial_interpret_reindexer reindexer sh v args = Some x ->
    length args = length sh.
Proof.
  unfold partial_interpret_reindexer. unfold index_to_partial_function.
  intros.
  cases (Datatypes.length (shape_to_vars sh) =? Datatypes.length args)%nat.
  - eapply Nat.eqb_eq in Heq.
    unfold shape_to_vars in *.
    rewrite map_length in *. unfold nat_range in *.
    rewrite length_nat_range_rec in *. auto.
  - discriminate.
Qed.

Lemma eq_index_to_partial_function :
  forall index1 index2,
    eq_Z_tuple_index_list index1 index2 ->
    index_to_partial_function index1 = index_to_partial_function index2.
Proof.
  intros.
  unfold index_to_partial_function.
  eapply functional_extensionality. intros.
  eapply functional_extensionality. intros.
  cases (Datatypes.length x =? Datatypes.length x0)%nat; auto.
  f_equal. f_equal.
  - f_equal.
    eapply map_eval_Zexpr_Z_tup_total_map_fold_left_subst_var_in_Z_tup. eauto.
  - f_equal.
    eapply map_eval_Zexpr_Z_tup_total_map_fold_left_subst_var_in_Z_tup. eauto.
Qed.

Lemma constant_map_filter_subseteq {X Y} :
  forall (l : list X) (f : X -> Y) g,
  ((constant (map f (filter g l)) \subseteq constant (map f l))).
Proof.
  induct l; intros.
  - simpl. sets.
  - simpl.
    erewrite subseteq_In in *. intros.
    erewrite <- In_iff_in in *.
    simpl in *.
    cases (g a).
    + simpl. invert H. propositional.
      right.
      eapply IHl. eapply H0.
    + simpl in *. right. eapply IHl. apply H.
Qed.

