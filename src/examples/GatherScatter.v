From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Int. Import Znat.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Import Logic.FunctionalExtensionality.
Require Coq.derive.Derive.
Import ListNotations.

From ATL Require Import ATL Common Tactics GenPushout CommonTactics.
 
Definition scatter_full B K W C x w :=
  SUM [ i < W ]
      GEN [ n < B ]
      GEN [ k < K ]
      SUM [ c < C ]
      GEN [ p < W ]
      |[ 0 <=? i-p ]|
      ( x _[n;c;i] * w _[k;c;i-p])%R.
Hint Unfold scatter_full : examples.

Section Full.
  Variables (W C B K : Z) (x w : list (list (list R))) (R : Z) (a b :nat).
  Derive gather_full SuchThat
         (consistent w (a,(b,(Z.to_nat R, tt))) ->
          (0 < C)%Z ->
          (0 < W)%Z ->
          (W <=C)%Z ->
          (0 < K)%Z ->
          (0 < R)%Z ->
          (0 < B)%Z ->
          scatter_full B K W C x w = gather_full) As gather_correct.
  Proof.
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
End Full.

Hint Unfold gather_full scatter_full : examples.

Definition scatter W x w :=
  SUM [ i < W ] GEN [ p < W ] |[ 0 <=? i-p ]| (x _[ i ] * w _[ i - p ])%R.
(*
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
*)  

Hint Unfold scatter : examples.

Section Mini.
  Variables (W C : Z) (x w : list R).
  Derive gather SuchThat
         ((0 < W)%Z ->
          (0 < C)%Z ->
          (Z.of_nat (length x) < W)%Z ->
          (Z.of_nat (length w) < C)%Z ->
          scatter W x w = gather) As gather_min_correct.
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
  Qed.
End Mini.

Hint Unfold gather : examples.  

Goal forall W x w,
    gather W x w =
    SUM [ i < W ]
        GEN [ i0 < W ]
        (|[ 0 <=? i - i0 ]|
         (|[ (i <? W) && (0 <=? i) ]| (x _[ i] * w _[ i - i0])%R)).
Proof. reflexivity. Qed.

Goal forall W C B K x w R0,
    gather_full W C B K x w R0 =
    GEN [ i < B ]
        GEN [ i0 < K ]
        GEN [ i1 < W ]
        SUM [ i2 < C ]
        SUM [ i3 < R0 ]
        (|[ i3 + i1 <? W ]| (x _[ i; i2; i3 + i1] * w _[ i0; i2; i3])%R).
Proof. reflexivity. Qed.
