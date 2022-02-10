From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.PreOmega.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Coq Require Import ZArith.Int. Import Znat.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.

From ATL Require Import ATL Common Tactics GenPushout CommonTactics.
 
Set Warnings "-omega-is-deprecated,-deprecated".

Definition gather_ B K W C R x w :=
  GEN [ n < B ]
      GEN [ k < K ]
      GEN [ p < W ]
      SUM [ r < C ]
      SUM [ c < R ]
      |[ p + r <? W ]|
      (x _[n;c;p+r] * w _[k;c;r])%R.

Definition scatter_ B K W C x w :=
  SUM [ i < W ]
      GEN [ n < B ]
      GEN [ k < K ]
      SUM [ c < C ]
      GEN [ p < W ]
      |[ 0 <=? i-p ]|
      ( x _[n;c;i] * w _[k;c;i-p])%R.

Theorem scatter_gather : forall W C B K (x w : list (list (list R))) R a b,
    { prog |
      consistent w (a,(b,(Z.to_nat R, tt))) ->
    (0 < C)%Z ->
    (0 < W)%Z ->
    (W <=C)%Z ->
    (0 < K)%Z ->
    (0 < R)%Z ->
    (0 < B)%Z ->
    scatter_ B K W C x w = prog}.
Proof.
  intros. unfold scatter_.
  reschedule.

  rw get_guard at (_ - _)%Z.
  
  rw guard_mul_r.
  rw<- @sum_bound_indic_no_f for (fun a => _ * _ _[a])%R.

  rw @sum_iverson_lift.

  rw<- @sum_gen_swap.
  rw^<- @sum_gen_swap.
  rw^<- @sum_gen_swap.
  rw^<- @sum_gen_swap.
  rw^ @sum_swap.
  rw @sum_swap.

  solve_for_index.

  rw collapse_iverson.

  rw andb_comm.

  rw @sum_bound_indic.

  simpl_guard.

  done.
Qed.

Definition gather1 W C x w :=
  GEN [ p < W ] SUM [ r < C ] |[ p + r <? W ]|
  (x _[ p + r ] * w _[ r ])%R.

Definition gather2 W C x w :=
  GEN [ p < W ]
      SUM [ r < C ] SUM [ i < W ] |[ i =? p + r ]| (x _[ i ] * w _[ r ])%R.

Definition gather3 W C x w :=
  SUM [ i < W ]
      GEN [ p < W ] SUM [ r < C ] |[ r =? i - p ]| (x _[ i ] * w _[ r ])%R.

Definition scatter W x w :=
  SUM [ i < W ] GEN [ p < W ] |[ 0 <=? i-p ]| (x _[ i ] * w _[ i - p ])%R.

Hint Unfold gather1 gather2 gather3 scatter : examples.

Theorem _scatter_gather : forall W C x w,
    (0 < C)%Z ->
    (0 < W)%Z ->
    (W <=C)%Z ->
    scatter W x w = gather1 W C x w.
Proof.
  intros.
  autounfold with examples.

  rw<- sum_bound_indic_no_f_guard for (fun a => x _[_] * w _[a])%R upto C.

  rw @sum_iverson_lift.

  rw collapse_iverson.

  rw andb_comm.
  
  simpl_guard.

  rw<- sum_gen_swap.

  rw sum_swap.

  solve_for_index.

  rw Z.add_comm.

  rw sum_bound_indic_no_f.

  simpl_guard.

  done.
Qed.
  
Theorem loop_reorder_equiv12 : forall W C x w,
    (0 < W)%Z ->
    (Z.of_nat (length x) < W)%Z ->
    gather1 W C x w = gather2 W C x w.
Proof.
  intros.
  autounfold with examples.

  rw get_guard_R.

  rw guard_mul_l.

  rw<- @sum_bound_indic_no_f for (fun k => x _[ k ] * w _[ _ ])%R.

  rw sum_iverson_lift.

  rw collapse_iverson.

  rw andb_comm.

  simpl_guard.

  simpl_guard.
  
  reflexivity.
Qed.

Theorem loop_reorder_equiv23 : forall W C x w,
    (0 < W)%Z ->
    length x < Z.to_nat W ->
    gather2 W C x w = gather3 W C x w.
Proof.
  intros.
  autounfold with examples.
  rw sum_swap.
  rw sum_gen_swap.
  solve_for_index.
  reflexivity.
Qed.

Theorem loop_reorder_equiv34 : forall W C x w,
    (0 < W)%Z ->
    (0 < C)%Z ->
    (Z.of_nat (length x) < W)%Z ->
    (Z.of_nat (length w) < W)%Z ->
    gather3 W W x w = scatter W x w.
Proof.
  intros.
  autounfold with examples.
  rw sum_bound_indic_no_f.
  apply sum_eq_bound; intros.
  apply gen_eq_bound; intros.
  rewrite Rmult_comm. simpl_guard.
  reflexivity.
Qed.

Example equiv : forall W C x w,
    {loop |
     (0 < W)%Z ->
     (0 < C)%Z ->
     (Z.of_nat (length x) < W)%Z ->
     (Z.of_nat (length w) < C)%Z ->
     GEN [ p < W ]
         SUM [ r < C ]
         ((x _[ p + r] * w _[ r])%R) = loop}.
Proof.
  reschedule.

  rw get_guard_R.

  rw guard_mul_l.

  rw<- @sum_bound_indic_no_f for (fun i => x _[i] * _)%R.

  rw sum_swap.

  solve_for_index.

  rw sum_gen_swap.

  rw sum_bound_indic_no_f.

  done.
Defined.

Eval simpl in (fun W C x w => proj1_sig (equiv W C x w)).

