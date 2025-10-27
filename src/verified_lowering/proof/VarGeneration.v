From Stdlib Require Import ZArith.Zdiv.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.

Import ListNotations.

From ATL Require Import FrapWithoutSets Var.
From Lower Require Import Range ListMisc Zexpr Result.

Definition shape_to_vars (shape : list Z) :=
  (map (fun k => (String.concat "" (repeat "?" (k+1))))
               (nat_range (length shape))).

Definition shape_to_index (shape : list Z) (vars : list var) :=
  combine (map ZVar vars) (map ZLit shape).  
        
Lemma shape_to_index_cons : forall var vars s sh,
    shape_to_index (s::sh) (var::vars) =
      (! var !,| s |)%z :: (shape_to_index sh vars).
Proof. auto. Qed.

Lemma map_subst_var_in_Zexpr_shape_to_index_id :
  forall vars v z sh,
    ~ In v vars ->
    map (subst_var_in_Z_tup v z) (shape_to_index sh vars) =
      shape_to_index sh vars.
Proof.
  induct vars; intros.
  - unfold shape_to_index. reflexivity.
  - cases sh. unfold shape_to_index. reflexivity.
    rewrite shape_to_index_cons. simpl.
    unfold subst_var_in_Z_tup at 1. simpl.
    cases (a ==v v). subst. sets. rewrite IHvars by sets. reflexivity.
Qed.

Lemma string_concat_empty : forall s1 s2 k,
  s2 <> "" -> 
  String.concat s1 (repeat s2 k) = "" ->
  k = 0.
Proof.
  induct k; propositional.
  simpl in *.
  cases (repeat s2 k).
  - simpl in *. propositional.
  - cases s2. simpl in *. propositional. simpl.
    invert H0.
Qed.    

Lemma string_app_l : forall s1 s2 s3,
    s1 ++ s2 = s1 ++ s3 ->
    s2 = s3.
Proof.
  induct s1; intros.
  - simpl in *. auto.
  - simpl in *. invert H.
    eauto.
Qed.

Lemma string_concat_repeat_eq : forall k k' s1,
    String.concat s1 (repeat "?" k') = String.concat s1 (repeat "?" k) ->
    k = k'.
Proof.
  induction k; intros.
  - simpl in *. eapply string_concat_empty in H. lia. propositional.
    invert H0.
  - simpl repeat in H.
    cases k'. simpl in *.
    cases (repeat "?" k); invert H.
    simpl repeat in H.
    simpl in *.
    cases k; cases k'; simpl repeat in H.
    + auto.
    + invert H.
      cases k'; simpl in *; cases s1; simpl in *; invert H1.
    + invert H.
      cases k; simpl in *; cases s1; simpl in *; invert H1.
    + simpl in H. invert H. f_equal.
      eapply IHk with (s1:=s1). simpl.
      eapply string_app_l. eassumption.
Qed.


Lemma not_In_var_generation : forall n k k',
    (k <= k') ->
    ~ In (String.concat "" (repeat "?" k))
      (map (fun k0 => String.concat "" (repeat "?" (k0 + 1)))
           (nat_range_rec n k')).
Proof.
  induct n; intros.
  - simpl. propositional.
  - simpl. propositional.
    + assert (k = k'+1).
      eapply string_concat_repeat_eq. eassumption.
      invert H0.
      lia.
    + eapply IHn. 2: eassumption. lia.
Qed.

Lemma no_dup_var_generation : forall n k,
    no_dup
      (map (fun k => String.concat "" (repeat "?" (k + 1)))
           (nat_range_rec n k)).
Proof.
  induct n; intros.
  - simpl. econstructor.
  - simpl.
    econstructor. auto.
    eapply not_In_var_generation. lia.
Qed.

Lemma substring0 : forall l n, substring n 0 l = "".
Proof.
  induct l; intros.
  - simpl. cases n; auto.
  - simpl. cases n. auto. auto.
Qed.

Lemma var_generation_contains_substring : forall n,
  contains_substring "?" (String.concat "" (repeat "?" (n+1))).
Proof.
  intros. replace (n+1) with (Datatypes.S n) by lia.
  simpl. cases (repeat "?" n).
  + unfold contains_substring. exists 0. reflexivity.
  + unfold contains_substring. simpl. exists 0.
    rewrite substring0. auto.
Qed.

Lemma not_In_var_map : forall len n,
    1 <= n ->
    ~ In "?"
      (map (fun k : nat => String.concat "" (repeat "?" (k + 1)))
           (nat_range_rec len n)).
Proof.
  intros.
  replace "?" with (String.concat "" (repeat "?" (0+1))) by reflexivity.
  eapply not_In_var_generation. lia.
Qed.

Lemma not_In_var_map2 : forall len n,
    2 <= n ->
    ~ In "??"
      (map (fun k : nat => String.concat "" (repeat "?" (k + 1)))
           (nat_range_rec len n)).
Proof.
  intros.
  replace "??" with (String.concat "" (repeat "?" (1+1))) by reflexivity.
  eapply not_In_var_generation. lia.
Qed.

Lemma not_var_generation_in_dom :
  forall (v : valuation),
    (forall var : var, contains_substring "?" var ->
                       var \in dom v -> False) ->
  ~ "?" \in dom v.
Proof.
  replace "?" with (String.concat "" (repeat "?" (0+1))) by reflexivity.
  unfold not. propositional.
  eapply H. 2: eassumption. eapply var_generation_contains_substring.
Qed.

Lemma not_var_generation_in_dom2 :
  forall (v : valuation),
    (forall var : var, contains_substring "?" var ->
                       var \in dom v -> False) ->
  ~ "??" \in dom v.
Proof.
  replace "??" with (String.concat "" (repeat "?" (1+1))) by reflexivity.
  unfold not. propositional.
  eapply H. 2: eassumption. eapply var_generation_contains_substring.
Qed.

Lemma not_var_generation_in_index :
  forall index (v : valuation),
  vars_of_reindexer index \subseteq dom v ->
  (forall var : var, contains_substring "?" var -> var \in dom v -> False) ->
  ~ "?" \in vars_of_reindexer index.
Proof.
  replace "?" with (String.concat "" (repeat "?" (0+1))) by reflexivity.
  unfold not. propositional.
  eapply H0. 2: eapply H; eapply H1.
  eapply var_generation_contains_substring.
Qed.

Lemma not_var_generation_in_index2 :
  forall index (v : valuation),
  vars_of_reindexer index \subseteq dom v ->
  (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
  ~ "??" \in vars_of_reindexer index.
Proof.
  replace "??" with (String.concat "" (repeat "?" (1+1))) by reflexivity.
  propositional.
  eapply H0. 2: eapply H; eapply H1.
  eapply var_generation_contains_substring.
Qed.

Lemma forall_map_not_in_index {X} :
  forall index (v : valuation) (sh : list X) k,
  (forall var : var, contains_substring "?" var -> var \in dom v -> False) ->
  vars_of_reindexer index \subseteq dom v ->
  Forall (fun var : var => ~ var \in vars_of_reindexer index)
         (map (fun k : nat => String.concat "" (repeat "?" (k + 1)))
              (nat_range_rec (Datatypes.length sh) k)).  
Proof.
  propositional.
  eapply Forall_map.
  eapply Forall_forall. intros. eapply H.
  2: eapply H0; eapply H2.
  eapply var_generation_contains_substring.
Qed.

Lemma forall_shape_to_vars_not_in_index :
  forall index (v : valuation) sh,
  (forall var : var, contains_substring "?" var -> var \in dom v -> False) ->
  vars_of_reindexer index \subseteq dom v ->
  Forall (fun var : var => ~ var \in vars_of_reindexer index)
         (shape_to_vars sh).
Proof.
  unfold shape_to_vars. unfold nat_range.
  intros.
  eapply forall_map_not_in_index; eauto.
Qed.

Lemma forall_map_not_in_dom {X} :
  forall (v : valuation) (sh : list X) k,
  (forall var : var, contains_substring "?" var -> var \in dom v -> False) ->
    Forall (fun var : var => ~ var \in dom v)
           (map (fun k : nat => String.concat "" (repeat "?" (k + 1)))
                (nat_range_rec (Datatypes.length sh) k)).
Proof.
  propositional.
  eapply Forall_map. eapply Forall_forall. intros.
  eapply H. 2: eassumption.
  eapply var_generation_contains_substring.
Qed.  

Lemma forall_shape_to_vars_not_in_dom :
  forall (v : valuation) sh,
  (forall var : var, contains_substring "?" var -> var \in dom v -> False) ->
  Forall (fun var : var => ~ var \in dom v)
         (shape_to_vars sh).
Proof.
  propositional. unfold shape_to_vars.
  eapply forall_map_not_in_dom; eauto.
Qed.  

Lemma empty_not_in_var_generation : forall l,
    ~ In "" (shape_to_vars l).
Proof.
  unfold not. intros.
  unfold shape_to_vars in H.
  eapply Forall_forall in H.
  2: { eapply Forall_map.
       eapply Forall_forall. intros.
       eapply var_generation_contains_substring. }
  unfold contains_substring in H.
  firstorder.
  simpl in *.
  cases x; invert H.
Qed.

Lemma shape_to_vars_contains_substring : forall l i,
    In i (shape_to_vars l) ->
    contains_substring "?" i.
Proof.
  induct l; intros; simpl in *.
  - propositional.
  - propositional.
    + subst. unfold contains_substring. exists 0. reflexivity.
    + unfold shape_to_vars in IHl. unfold nat_range in IHl.      
      cases l. simpl in *. propositional.
      simpl length in IHl. simpl in IHl.
      simpl length in H0.
      rewrite succ_nat_range_rec_app_end in H0.
      rewrite map_app in H0.
      eapply in_app_or in H0.
      invert H0. eauto.
      simpl in *. propositional. subst.
      eapply var_generation_contains_substring.
Qed.

Lemma map_partially_eval_Z_tup_combine : forall sh v k,
    (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    map (partially_eval_Z_tup v)
        (combine
           (map ZVar
                (map (fun k => String.concat "" (repeat "?" (k + 1)))
                     (nat_range_rec (length sh) k))) (map ZLit sh)) =
      combine
        (map ZVar
             (map (fun k => String.concat "" (repeat "?" (k + 1)))
                  (nat_range_rec (length sh) k))) (map ZLit sh).
Proof.
  induct sh; intros; auto.
  simpl. rewrite IHsh; auto.
  f_equal. unfold partially_eval_Z_tup.
  simpl. cases (v $? String.concat "" (repeat "?" (k + 1))); auto.
  eapply lookup_Some_dom in Heq.
  eapply H in Heq. propositional. eapply var_generation_contains_substring.
Qed.

Lemma map_partially_eval_Z_tup_shape_to_index : forall sh v,
  (forall var : var, contains_substring "?" var -> ~ var \in dom v) ->
    (map (partially_eval_Z_tup v) (shape_to_index sh (shape_to_vars sh))) =
      (shape_to_index sh (shape_to_vars sh)).
Proof.
  unfold shape_to_index, shape_to_vars, nat_range.
  intros.
  apply map_partially_eval_Z_tup_combine. auto.
Qed.

Lemma map_fold_left_subst_var_in_Z_tup_shape_to_index :
  forall vars x sh,
    length vars = length x ->
    no_dup vars ->
    map
      (fun y =>
         fold_left
           (fun a t0 =>
              subst_var_in_Z_tup (fst t0) (snd t0) a) (combine vars x) y)
      (shape_to_index sh vars) =
      combine (map ZLit x) (map ZLit sh).
Proof.
  unfold shape_to_index.
  intros. eapply map_fold_left_subst_var_in_Z_tup_combine; eauto.
Qed.

Lemma shape_to_index_not_empty_Z : forall l,
    shape_to_index (result_shape_Z (V l))
                   (shape_to_vars (result_shape_Z (V l))) <> [].
Proof.
  unfold result_shape_Z. simpl. intros.
  cases l; unfold shape_to_vars, shape_to_index; simpl; inversion 1.
Qed.

