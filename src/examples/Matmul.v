From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import micromega.Lia.
From Coq Require Import Lists.List.
From Coq Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Coq Require Import ZArith.Int. Import Znat.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Logic.FunctionalExtensionality.
Require Coq.derive.Derive.
Import ListNotations.

From ATL Require Import ATL Common CommonTactics Tactics GenPushout LetLifting
     Reshape Div.

Definition matmul A B C (m1 m2 : (list (list R))) :=
    GEN [ i < A ]
      GEN [ j < C ]
      SUM [ k < B ]
      (m1 _[i;k] * m2 _[k;j])%R.

Hint Unfold matmul : examples.  

Section Tile.
  Variables (A B C : nat) (m1 m2 : (list (list R))) (k : Z).
  Derive matmul_tiled SuchThat
         ((0 < k)%Z ->
          0 < A ->
          0 < B ->
          0 < C ->
          consistent m1 (A,(B,tt)) ->
          consistent m2 (B,(C,tt)) ->
          matmul (Z.of_nat A) (Z.of_nat B) (Z.of_nat C) m1 m2 =
            matmul_tiled) As matmultiled.
  Proof.
    reschedule.

    wrapid^ @flatten_truncr_tile_id' around (GEN [ _ < (Z.of_nat A) ] _)
      with (Z.to_nat k).

    inline tile.
    rw @get_gen_some.

    wrapid^ @transpose_transpose_id around (GEN [ _ < k ] _).
    rw @unfold_inner_transpose.

    rw @consistent_length.
    rw @consistent_length.
    rw @get_gen_some.
    rw^ @gp_gen_iverson.    
    rw @get_gen_some.
    rewrite Z2Nat.id by lia.
    
    wrapid^ @flatten_truncr_tile_id' around (GEN [ _ < (Z.of_nat C) ] _)
      with (Z.to_nat k).

    inline tile.
    rw @get_gen_some.
    rw^ @gp_gen_iverson.    

    rw @gp_double_iverson.
    done.
  Defined.
End Tile.

Hint Unfold matmul matmul_tiled : examples.  

Hint Resolve floor_lt_ceil Z.div_pos : crunch.

Section Tile.
  Variables (A B C : nat) (m1 m2 : (list (list R))) (k : Z).
  Derive matmul_tiled_split SuchThat
         ((0 < k)%Z ->
          0 < A ->
          0 < B ->
          0 < C ->
          consistent m1 (A,(B,tt)) ->
          consistent m2 (B,(C,tt)) ->
          matmul (Z.of_nat A) (Z.of_nat B) (Z.of_nat C) m1 m2 =
            matmul_tiled_split) As matmultiledsplit.
  Proof.
    reschedule.

    wrapid^ @flatten_truncr_tile_id' around (GEN [ _ < (Z.of_nat A) ] _)
      with (Z.to_nat k).

    inline tile.
    rw @get_gen_some.

    rw^ @split_gen at (Z.of_nat A / k )%Z.

    simpl_guard.
    wrapid^ @transpose_transpose_id around (GEN [ _ < k ] _).
    rw @unfold_inner_transpose.

    rw @consistent_length.
    rw @consistent_length.
    rw @get_gen_some.
    rw^ @gp_gen_iverson.    
    rw @get_gen_some.
    rewrite Z2Nat.id by lia.

    wrapid^ @flatten_truncr_tile_id' around (GEN [ _ < (Z.of_nat C) ] _)
      with (Z.to_nat k).

    inline tile.
    rw @get_gen_some.
    rw^ @gp_gen_iverson.    

    rw^ @split_gen upto (Z.of_nat C // k)%Z at (Z.of_nat C / k )%Z.
    simpl_guard.

    done.
  Defined.
End Tile.

Hint Unfold matmul_tiled_split : examples.  

