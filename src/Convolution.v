From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Coq Require Import ZArith.Int. Import Znat.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.

Set Warnings "-omega-is-deprecated,-deprecated".

From ATL Require Import ATL Common Tactics GenPushout CommonTactics.

Definition conv1 (c : list R) (n m : Z) : list R :=
  GEN [ i < n ]
      SUM [ j < m ]
      (|[ 0 <=? i - j ]| ((GEN [ - m + 1 <= k < n ]
                               (|[ k =? 2 + (- m + 1) ]| 1)) _[ i - j ] *
                          c _[ j ])%R). 

Definition conv2 (c : list R) (n m : Z) : list R :=
  GEN [ i < n ] SUM [ j < m ] |[ i - j =? 2 ]| c _[ j ].

Definition conv3 (c : list R) n m : list R :=
  GEN [ i < n ]
  SUM [ j < m ] |[ (j =? i - 2) && (0 <=? j) && (j <? m) ]| c _[ j ].

Definition conv4 (c : list R) (n m : Z) : list R :=
  GEN [ i < n ] |[ (0 <=? i - 2) && (i - 2 <? m) ]| c _[ i - 2 ].

Hint Unfold conv1 conv2 conv3 conv4 : examples.

Theorem conv12_equiv : forall c n m,
    (0 <= m)%Z -> (0 <= n)%Z -> (0 < n + m - 1)%Z ->
    conv1 c n m = conv2 c n m.
Proof.
  intros.
  autounfold with examples.

  rw @get_genr_some.
  
  apply gen_eq_bound; intros.
  apply sum_eq_bound; intros.
  solve_for (i-i0)%Z.
  autorewrite with crunch.
  rewrite collapse_iverson.
  apply iverson_eq.
  auto with crunch.
Qed.

Theorem conv23_equiv : forall c n m,
    (0 <= m)%Z -> (0 <= n)%Z ->
    conv2 c n m = conv3 c n m.
Proof.
  intros.
  autounfold with examples.
  
  auto with crunch.
Qed.

Example conv34_equiv : forall c n m,
    (0 < m)%Z -> (0 <= n)%Z ->
    conv3 c n m = conv4 c n m.
Proof.
  intros.
  autounfold with examples.
  setoid_rewrite <- andb_assoc.
  rw sum_bound_indic.
  apply gen_eq_bound; intros.
  auto with crunch.
Qed.

Example equiv : forall c n m,
    {conv | (0 < m)%Z -> (0 <= n)%Z ->
            conv1 c n m = conv }.
Proof.
  reschedule.

  rw get_genr_some.

  rw guard_mul_l.

  solve_for_index.
  
  rw collapse_iverson.

  rw andb_comm.

  rw sum_bound_indic.
  
  simpl_guard.

  done.
Defined.

Eval simpl in (fun c n m => proj1_sig (equiv c n m)).
