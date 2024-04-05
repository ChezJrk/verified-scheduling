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

Definition contexts_agree
           (ec : expr_context) (st : stack) (h : heap) sh :=
  forall x,
    (forall v, ec $? x = Some (V v) ->
               exists l,
                 sh $? x = Some l /\
                   Forall (fun x => vars_of_Zexpr x = []) l /\
                   result_has_shape
                     (V v)
                     (map Z.to_nat (map (eval_Zexpr_Z_total $0) l)) /\
                   (Forall (fun x => 0 <= x)%Z
                           (map (eval_Zexpr_Z_total $0) l)) /\
               exists arr,
                 h $? x = Some arr /\
                   array_add
                     (alloc_array
                        (Z.to_nat
                           (fold_left
                              Z.mul
                              (map Z.of_nat
                                   (filter_until
                                      (map Z.to_nat
                                           (map (eval_Zexpr_Z_total $0) l)
                                      ) 0)) 1%Z)) $0)
                     (partial_result_to_array_delta
                        (partial_interpret_reindexer
                           (fun l => l)
                           (map Z.of_nat
                                (filter_until
                                   (map Z.to_nat
                                        (map (eval_Zexpr_Z_total $0) l)) 0)) $0)
                        (V v)) = arr) /\
      (forall s, ec $? x = Some (S s) -> sh $? x = Some [] /\
                                           st $? x = Some (match s with
                                                           | SS r => r
                                                           | SX => 0%R
                                                           end)).
(*
Lemma contexts_agree_add_valuation : forall ec st h sh i x,    
    contexts_agree ec st h sh ->
    contexts_agree (v $+ (i, x)) ec st h sh.
Proof.
  unfold contexts_agree. propositional.
  - eapply H in H1. invs. clear H.
    eexists. eexists. split. eassumption. split.
    eapply eval_Zexprlist_add. eassumption. sets.
    split. auto. split. auto. eexists. split. eassumption. reflexivity.
  - eapply H in H1. propositional.
  - eapply H in H1. propositional.
Qed.
*)
Lemma contexts_agree_add_heap : forall ec st h sh a val p,
    contexts_agree ec st h sh ->
    h $? p = Some a ->
    ~ p \in dom sh ->
    ~ p \in dom ec ->
    contexts_agree ec st (h $+ (p,array_add a val)) sh.
Proof.
  unfold contexts_agree. propositional.
  - eapply H in H3. invs. clear H.    
    cases (x ==v p). subst. eapply lookup_Some_dom in H3. sets.
    rewrite lookup_add_ne by auto.
    eexists. split.
    eassumption. split. eassumption. split. eassumption.
    split. eassumption.
    eexists. split. eassumption. reflexivity.
  - eapply H in H3. propositional.
  - eapply H in H3. propositional.
Qed.

Lemma contexts_agree_alloc_array_in_heap :
  forall ec st h sh x l,
    contexts_agree ec st h sh ->
    ec $? x = None ->
    contexts_agree ec st (alloc_array_in_heap l h x) sh.
Proof.
  unfold contexts_agree. propositional.
  - cases (x ==v x0). subst. rewrite H0 in *. discriminate.
    eapply H in H1.
    invs.
    eexists.
    split. eassumption.
    split. eassumption.
    split. eassumption.
    split. eassumption.    
    eexists. unfold alloc_array_in_heap.
    rewrite lookup_add_ne by auto.
    split. eassumption. reflexivity.
  - eapply H. eauto.
  - eapply H. eauto.
Qed.    

Lemma contexts_agree_add_in_stack :
  forall ec st h sh p val a,
    contexts_agree ec st h sh ->
    st $? p = Some a ->
          ~ p \in dom sh ->
       ~ p \in dom ec ->
          contexts_agree ec (st $+ (p, val)) h sh.
Proof.
  unfold contexts_agree. propositional.
  - eapply H. auto.
  - cases (x ==v p).
    + subst. eapply H. eauto. 
    + subst. eapply H. eauto. 
  - cases (x ==v p).
    + subst. rewrite lookup_add_eq by auto.
      eapply lookup_Some_dom in H3. sets.
    + rewrite lookup_add_ne by auto.
      eapply H. auto.
Qed.

Lemma contexts_agree_alloc_stack : forall ec st x val h sh,
    contexts_agree ec st h sh ->
    ec $? x = None ->
    contexts_agree ec (st $+ (x, val)) h sh.
Proof.
  unfold contexts_agree. propositional.
  - eapply H. eauto. 
  - cases (x ==v x0). subst. rewrite H1 in *. discriminate.
    eapply H. eauto.
  - cases (x ==v x0). subst. rewrite H1 in *. discriminate.
    rewrite lookup_add_ne by auto.
    eapply H. auto.
Qed.

Lemma contexts_agree_let_bind1_scalar :
  forall ec st h sh x r,
  contexts_agree ec st h sh ->
  contexts_agree (ec $+ (x, S r)) (st $+ (x, (match r with
                                                | SS r' => r'
                                                | SX => 0%R
                                                end))) h (sh $+ (x, [])).
Proof.
  unfold contexts_agree. propositional.
  - cases (x ==v x0).
    + subst. repeat rewrite lookup_add_eq in * by auto. invs.
    + rewrite lookup_add_ne in * by auto. eapply H in H0.
      eauto.
  - cases (x ==v x0).
    + subst. rewrite lookup_add_eq in * by auto. invs. auto.
    + rewrite lookup_add_ne in * by auto.
      eapply H. eauto.
  - cases (x ==v x0).
    + subst. rewrite lookup_add_eq in * by auto. invs. auto.
    + rewrite lookup_add_ne in * by auto.
      eapply H. auto.
Qed.

Lemma contexts_agree_add_alloc_heap :
  forall ec st h sh x nz z esh1 l1,
  contexts_agree ec st h sh ->
  ec $? x = None ->
  result_has_shape (V l1)
                   (map Z.to_nat (map (eval_Zexpr_Z_total $0) (z :: esh1))) ->
  Forall (fun x : Z => (0 <= x)%Z) (map (eval_Zexpr_Z_total $0) (z :: esh1))->
  Forall (fun x : Zexpr => vars_of_Zexpr x = []) (z :: esh1) ->
  fold_left Z.mul
            (map Z.of_nat
                 (filter_until
                    (map Z.to_nat
                         (map (eval_Zexpr_Z_total $0) (z :: esh1))) 0))
            1%Z = nz ->  
  contexts_agree (ec $+ (x, V l1)) st (h $+ (x,
          array_add (alloc_array (Z.to_nat nz) $0)
                    (partial_result_to_array_delta
                       (partial_interpret_reindexer
                          (fun l : list (Zexpr * Zexpr) => l)
                          (map Z.of_nat
                               (filter_until
                                  (map Z.to_nat
                                       (map (eval_Zexpr_Z_total $0)
                                            (z :: esh1))) 0)) $0)
                       (V l1)))) (sh $+ (x, z :: esh1)).
Proof.
  unfold contexts_agree. propositional.
  - cases (x ==v x0).
    + subst. rewrite lookup_add_eq in * by auto.
      invs. 
      eexists.
      split. reflexivity.
      split. eauto.
      split. eauto.
      split. eassumption.
      eexists. rewrite lookup_add_eq by auto.
      split. reflexivity.
      f_equal.
    + rewrite lookup_add_ne in * by auto.
      eapply H in H5. clear H. invs.
      eexists.
      split. eassumption.
      split. eassumption.
      split. eassumption.
      split. eassumption.
      eexists. rewrite lookup_add_ne by auto. split.
      eassumption. reflexivity.
  - cases (x ==v x0).
    + subst. rewrite lookup_add_eq in * by auto.
      invert H5.
    + rewrite lookup_add_ne in * by auto.
      eapply H. eauto.
  - cases (x ==v x0).
    + subst. rewrite lookup_add_eq in * by auto.
      invert H5.
    + rewrite lookup_add_ne in * by auto.
      eapply H. eauto.
Qed.

Lemma contexts_agree_result_has_shape :
  forall ec st h sh,
  contexts_agree ec st h sh ->
  (forall (x0 : var) (r0 : result) (size0 : list Zexpr),
      sh $? x0 = Some size0 ->
      ec $? x0 = Some r0 ->
      result_has_shape r0
                       (map Z.to_nat (map (eval_Zexpr_Z_total $0) size0))).
Proof.
  unfold contexts_agree. intros. specialize (H x0).
  invs.
  cases r0.
  - eapply H3 in H1. propositional. rewrite H in *. invs. econstructor.
  - eapply H2 in H1; clear H2. invs. rewrite H1 in *. invs.
    eauto.
Qed.    

