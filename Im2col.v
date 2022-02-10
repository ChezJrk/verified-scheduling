From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat. 
From Coq Require Import omega.PreOmega.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Coq Require Import ZArith.Int. Import Znat.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.

From ATL Require Import ATL Common CommonTactics Tactics GenPushout LetLifting.

Set Warnings "-omega-is-deprecated,-deprecated".

Definition im2col_mini K W RR (w : (list (list R))) (x : list R) :=
    GEN [ k < K ]
      GEN [ p < W ]
        SUM [ r < RR ]
        (w _[ k ; r ] * x _[ p + r ])%R .

Definition im2col_mini_lifted K W RR (w : (list (list R))) (x : list R) :=
    tlet y := GEN [ p < W ] GEN [ r < RR ]
             x _[ p + r ] in
    GEN [ k < K ]
      GEN [ p < W ]
        SUM [ r < RR ]
        (w _[ k ; r ] * y _[ p ; r ])%R.

Definition im2colmini K W RR (w : (list (list R))) (x : list R) :=
    GEN [ k < K ]
      GEN [ p < W ]
        SUM [ r < RR ]
        |[ p + r <? K ]| (w _[ k ; r ] * x _[ p + r ])%R.

Definition im2colminilifted K W RR (w : (list (list R))) (x : list R) :=
    tlet y := GEN [ p < W ] GEN [ r < RR ]
             |[ p + r <? K ]| x _[ p + r ] in
    GEN [ k < K ]
      GEN [ p < W ]
        SUM [ r < RR ]
        (w _[ k ; r ] * y _[ p ; r ])%R.

Definition im2col B K W C RR (w x : (list (list (list R)))) :=
    GEN [ n < B ]
    GEN [ k < K ]
    GEN [ p < W ]
    SUM [ c < C ]
    SUM [ r < RR ]
    (w _[ k ; c ; r ] * x _[ n ; c ; p + r ])%R.

Definition im2col_lifted B K W C RR (w x : (list (list (list R)))) :=
    tlet y :=
         GEN [ n < B ]
         GEN [ c < W ]
         GEN [ p < C ]
         GEN [ r < RR ]
          x _[ n ; p ; c + r ] in
    GEN [ n < B ]
    GEN [ k < K ]
    GEN [ p < W ]
    SUM [ c < C ]
    SUM [ r < RR ]
    (w _[ k ; c ; r ] * y _[ n ; p ; c ; r ])%R.

Hint Unfold im2col im2col_lifted im2colmini im2colminilifted im2col_mini im2col_mini_lifted : examples.
  
Theorem im2col_mini_sched : forall K W RR (w : (list (list R))) (x : list R),
    im2col_mini K W RR w x =
    im2col_mini_lifted K W RR w x.
Proof.
  intros.
  autounfold with examples.

  rw^ @lbind_helper for (fun e => _ * e)%R.

  time rw ll_sum.

  rw @ll_gen.

  rw @ll_gen_indep.
  
  reflexivity.
Qed.

Example mini_equiv : forall K W RR (w : (list (list R))) (x : list R),
    {sched |
     (0 < RR)%Z ->
     im2col_mini K W RR w x = sched}.
Proof.
  reschedule.

  rw^ @lbind_helper for (fun e => _ * e)%R.

  time rw ll_sum.

  rw @ll_gen.

  rw @ll_gen_indep.

  done.
Defined.

Eval simpl in (fun K W RR w x => proj1_sig (mini_equiv K W RR w x)).

Theorem im2col_sched : forall B K W C RR (w x : (list (list (list R)))),
    im2col B K W C RR w x =
    im2col_lifted B K W C RR w x.
Proof.
  intros.
  autounfold with examples.

  rw^ @lbind_helper for (fun e => _ * e)%R.

  rw @ll_sum.

  rw @ll_sum.

  rw @ll_gen.

  rw @ll_gen_indep.

  rw @ll_gen.

  reflexivity.
Qed.

Example equiv : forall B K W C RR (w x : (list (list (list R)))),
    {sched |
     im2col B K W C RR w x = sched }.
Proof.
  reschedule.

  rw^ @lbind_helper for (fun e => _ * e)%R.

  rw @ll_sum.

  rw @ll_sum.

  rw @ll_gen.

  rw @ll_gen_indep.

  rw @ll_gen.

  done.
Defined.

Eval simpl in (fun B K W C RR w x => proj1_sig (equiv B K W C RR w x)).
