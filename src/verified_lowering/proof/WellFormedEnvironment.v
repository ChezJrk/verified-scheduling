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

From ATL Require Import ATL Map Sets FrapWithoutSets Tactics Div.
From Lower Require Import Zexpr Bexpr Array Range Sexpr Result ListMisc Meshgrid VarGeneration
     Injective Constant InterpretReindexer.

Definition well_formed_environment
           (st : stack) (h : heap) (p : var) (sh : context)
           (v : valuation) (vars : set var) (ec : expr_context)
  :=
  (forall var : var, contains_substring "?" var -> ~ var \in dom v) /\
    (dom st \cap dom h = constant []) /\
    vars \cap (dom st \cup dom h \cup dom ec) = constant [] /\
    ~ p \in vars /\
    ~ p \in dom sh /\
    ~ p \in dom ec /\
    vars \cap dom sh = constant []
.

Ltac decomp_well_formed_environment :=
  match goal with
  | H : well_formed_environment _ _ _ _ _ _ _  |- _ =>
      unfold well_formed_environment in H;
      inversion H as [ Hvardom Hrest ]; clear H;
      inversion Hrest as [ Hsth Hrest1 ]; clear Hrest;
      inversion Hrest1 as [ Hsthec Hrest2 ]; clear Hrest1;
      inversion Hrest2 as [ Hpvars Hrest3 ]; clear Hrest2;
      inversion Hrest3 as [ Hpsh Hrest4 ]; clear Hrest3;
      inversion Hrest4 as [ Hpec Hvarssh ]; clear Hrest4
  end.

Lemma well_formed_environment_subseteq_vars :
  forall st h p sh v vars1 vars2 ec,
    well_formed_environment st h p sh v vars1 ec ->
    vars2 \subseteq vars1 ->
    well_formed_environment st h p sh v vars2 ec.
Proof.
  unfold well_formed_environment in *. intros. invs. split.
  auto. split.
  auto. split.
  eapply subset_cap_empty. 2: eassumption. sets. split.
  sets. split.
  auto. split. auto.
  eapply subset_cap_empty. 2: eassumption. sets.
Qed.

Lemma well_formed_environment_add_valuation : forall st h p sh v i x vars ec,
    well_formed_environment st h p sh v vars ec ->
    ~ i \in dom v ->
    ~ contains_substring "?" i ->    
    well_formed_environment st h p sh (v $+ (i, x)) vars ec.
Proof.
  unfold well_formed_environment. propositional.
  rewrite dom_add in H9.
  assert (var \in constant [i] \/ var \in dom v). sets.
  invert H10. 
  eapply In_iff_in in H11. invert H11.
  2: { invert H10. }
  eapply H1. auto.
  eapply H2. eassumption. auto.
Qed.

Lemma well_formed_environment_add_heap :
  forall st h p sh vars val v a ec,
    well_formed_environment st h p sh v vars ec ->
    h $? p = Some a ->
    well_formed_environment st
                            (h $+
                               (p, array_add a val)) p sh v vars ec.
Proof.
  unfold well_formed_environment. propositional.
  - rewrite dom_add. rewrite intersection_comm. rewrite cap_distr.
    repeat rewrite (intersection_comm _ (dom st)).
    rewrite H. rewrite cup_empty_r.
    rewrite intersection_comm.
    eapply constant_cap_empty. eapply lookup_Some_dom in H0. sets.
  - rewrite dom_add.
    rewrite intersection_comm. rewrite cap_distr.
    rewrite intersection_comm in H2. rewrite cap_distr in H2.
    eapply cup_empty in H2. invs. rewrite cap_distr in H6.
    eapply cup_empty in H6. invs.
    rewrite H8. rewrite cap_distr. 
    rewrite H2. rewrite cup_empty_r. rewrite cup_empty_l.
    rewrite cap_distr. rewrite H9. sets.
Qed.

Lemma well_formed_environment_letbind1 :
  forall st h p sh v ec x vars1 vars2 nz,
    ~ x \in vars1 ->
    ~ x \in vars2 ->
    ec $? x = None ->
    well_formed_environment
      st h p sh v ((constant [x] \cup vars1) \cup vars2) ec ->  
    well_formed_environment st (alloc_array_in_heap [nz] h x) x sh v vars1 ec.
Proof.
  unfold well_formed_environment in *. unfold alloc_array_in_heap.
  intros. rewrite dom_add.
  invs.
  repeat rewrite cap_distr in H4.
  eapply cup_empty in H4. invert H4.
  eapply cup_empty in H8. invert H8.
  rewrite intersection_comm in H4.
  repeat rewrite cap_distr in H4. 
  eapply cup_empty in H4. invert H4.
  eapply cup_empty in H8.
  rewrite intersection_comm in H8. invert H8.
  split. auto.
  rewrite intersection_comm. repeat rewrite cap_distr.
  rewrite H4. rewrite intersection_comm. rewrite H2.
  rewrite intersection_comm.
  repeat rewrite cap_distr.
  rewrite intersection_comm in H10,H11.
  repeat rewrite cap_distr in H10,H11.
  eapply cup_empty in H10,H11. invert H10. invert H11.
  eapply cup_empty in H8,H10. invert H8. invert H10.
  repeat rewrite cap_distr in H9.
  eapply cup_empty in H9. invert H9.
  eapply cup_empty in H10. invert H10.
  rewrite H8. rewrite H17. rewrite H15.
  split. rewrite cup_empty_r. reflexivity.
  split. repeat rewrite cup_empty_r. rewrite cup_empty_l.
  eapply constant_cap_empty. auto.
  split.
  auto.
  split.
  erewrite <- constant_cap_empty. auto.
  split.
  eapply lookup_None_dom. auto.
  auto.
Qed.

Lemma well_formed_environment_not_in_stack_heap :
  forall st h p sh v vars ec x,
    well_formed_environment st h p sh v vars ec ->
    x \in vars ->
          ~ x \in dom st /\ ~ x \in dom h.
Proof.
  unfold well_formed_environment. propositional.
  rewrite intersection_comm in H2.
  repeat rewrite cap_distr in H2. eapply cup_empty in H2.
  invert H2. eapply cup_empty in H8. invert H8.
  sets.
  rewrite intersection_comm in H2.
  repeat rewrite cap_distr in H2. eapply cup_empty in H2.
  invert H2. eapply cup_empty in H8. invert H8.
  sets.
Qed.

Lemma well_formed_environment_alloc_heap :
  forall st h p sh v vars vars' (ec : expr_context) arr sha r x ec,
  well_formed_environment st h p sh v vars ec ->
  x \in vars ->
  vars' \subseteq vars ->
  ~ x \in vars' ->
  well_formed_environment st (h $+ (x, arr)) p (sh $+ (x, sha)) v
                          vars' (ec $+ (x, r)).
Proof.
  unfold well_formed_environment. intros. invs.
  repeat rewrite dom_add.
  rewrite intersection_comm in H4.
  repeat rewrite cap_distr in H4.
  eapply cup_empty in H4. invert H4.
  eapply cup_empty in H8. invert H8.
  rewrite intersection_comm. rewrite cap_distr.
  split. auto.
  assert (~ x \in dom st). sets.
  eapply constant_cap_empty in H8. rewrite H8.
  rewrite intersection_comm. rewrite H.
  split. rewrite cup_empty_r. reflexivity.
  rewrite intersection_comm.
  repeat rewrite cap_distr.
  assert (dom st \cap vars' = constant []) by sets.
  rewrite H12.
  assert (constant [x] \cap vars' = constant []) by sets.
  rewrite H13.
  assert (dom h \cap vars' = constant []) by sets.
  rewrite H14.
  assert (dom ec0 \cap vars' = constant []) by sets.
  rewrite H15.
  split. repeat rewrite cup_empty_r. reflexivity.
  split. sets. split. sets. split. sets.
  rewrite intersection_comm. rewrite cap_distr.
  eapply constant_cap_empty in H2. rewrite H2.
  assert (dom sh \cap vars' = constant []) by sets.
  rewrite H16.
  rewrite cup_empty_r. reflexivity.
Qed.

Lemma well_formed_environment_add_stack :
  forall st h p sh v vars ec val,
    well_formed_environment st h p sh v vars ec ->
    p \in dom st ->
    well_formed_environment (st $+ (p, val)) h p sh v vars ec.
Proof.
  intros. decomp_well_formed_environment.
  unfold well_formed_environment.
  split. auto. repeat rewrite dom_add.
  rewrite intersection_comm in Hsthec.
  repeat rewrite cap_distr in Hsthec.
  eapply cup_empty in Hsthec. invs.
  eapply cup_empty in H. invs.
  repeat rewrite cap_distr.
  split. rewrite Hsth. sets.
  split. rewrite intersection_comm.
  repeat rewrite cap_distr.
  rewrite H1,H2,H3. sets.
  sets.
Qed.

Lemma well_formed_environment_let_bind1_scalar :
  forall st h p sh vars vars' x ec val v,
    well_formed_environment st h p sh v vars ec ->
    x \in vars ->
   ~ x \in vars' ->
    vars' \subseteq vars ->
    well_formed_environment (st $+ (x, match val with
                                       | SS r => r
                                       | SX => 0%R
                                       end)) h p 
                            (sh $+ (x, [])) v vars' (ec $+ (x, S val)).
Proof.
  intros. decomp_well_formed_environment. unfold well_formed_environment.
  split. auto.
  repeat rewrite dom_add.
  rewrite intersection_comm in Hsthec.
  repeat rewrite cap_distr in Hsthec.
  eapply cup_empty in Hsthec. invs.
  eapply cup_empty in H. invs.
  repeat rewrite cap_distr.
  rewrite Hsth.
  split. sets.
  rewrite intersection_comm.
  repeat rewrite cap_distr.  
  eapply constant_cap_empty in H1.
  rewrite H1.
  split. repeat erewrite cap_monotone_contra by eassumption.
  repeat rewrite cup_empty_r. reflexivity.
  sets.
Qed.

Lemma well_formed_environment_alloc_stack :
  forall st h p sh v vars vars' ec x val,
    well_formed_environment st h p sh v vars ec ->
    x \in vars ->
          ~ x \in vars' ->
    vars' \subseteq vars ->
    well_formed_environment (st $+ (x, val)) h x sh v vars' ec.
Proof.
  intros.
  decomp_well_formed_environment. unfold well_formed_environment.
  rewrite dom_add.
  split. auto.
  rewrite cap_distr.
  rewrite intersection_comm in Hsthec.
  repeat rewrite cap_distr in Hsthec.
  eapply cup_empty in Hsthec. invs.
  eapply cup_empty in H. invs.
  rewrite Hsth.
  split. sets.
  split.
  rewrite intersection_comm. repeat rewrite cap_distr.  
  pose proof constant_cap_empty x vars'.
  eapply H in H1. rewrite H1.  
  erewrite cap_monotone_contra; try eassumption.
  erewrite cap_monotone_contra; try eassumption.
  erewrite cap_monotone_contra; try eassumption.
  repeat rewrite cup_empty_r. reflexivity.
  split. auto.
  split. sets.
  split. sets.
  sets.
Qed.

