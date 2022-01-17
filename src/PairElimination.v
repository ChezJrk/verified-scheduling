From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Vectors.Vector.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.

From ATL Require Import ATL Common CommonTactics Tactics Div.

Set Warnings "-omega-is-deprecated,-deprecated".

Theorem pair_elimination {X Y} `{TensorElem X} `{TensorElem Y} :
  forall N I (e1 : Z -> X) (e2 : Z -> Y),
    (GEN [ n' < N ] (e1 n', e2 n')) _[ I ]
    = ((GEN [ n' < N ] e1 n') _[I], (GEN [ n' < N ] e2 n') _[I]).
Proof.
  intros.
  destruct (I <? N)%Z eqn:iltn;
    destruct (0 <=? I)%Z eqn:igt0; unbool_hyp.
  - repeat rewrite get_gen_some; auto with crunch.
  - destruct N.
    + reflexivity.
    + unfold gen, genr. simpl.
      posnat. simpl gen_helper.
      repeat rewrite get_neg_null; auto.
    + reflexivity.
  - destruct N.
    + reflexivity.
    + unfold gen, genr. simpl.
      posnat. simpl gen_helper.
      repeat rewrite get_znlt_null.
      * reflexivity.
      * simpl. rewrite gen_helper_length. zify. omega.
      * simpl. rewrite gen_helper_length. zify. omega.
      * simpl. rewrite gen_helper_length. zify. omega.
    + repeat rewrite gen_neg_empty; auto; zify; omega.
  - destruct N; zify; try omega.
   reflexivity.
Qed.
