From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import micromega.Lia.
From Coq Require Import micromega.Zify.
From Coq Require Import Lists.List.
From Coq Require Import Vectors.Vector.
From Coq Require Import Reals.Reals. Import RIneq. Import Rdefinitions.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.

From ATL Require Import ATL Common Tactics Div CommonTactics.

Lemma gp_genr_iverson {X} `{TensorElem X} :
  forall p N K (body : Z -> X),
    (|[ p ]| (GEN [K <= i < N ] body i )) = GEN [ K <= n' < N ] (|[ p ]| body n' ).
Proof.
  unfold iverson. intros.
  destruct p. repeat setoid_rewrite mul_1_id. auto.
  simpl. rewrite <- genr_map. reflexivity.
Qed.

Theorem gp_gen_iverson {X} `{TensorElem X} :
  forall p N (body : Z -> X),
    (|[ p ]| (GEN [i < N ] body i )) = GEN [ n' < N ] (|[ p ]| body n' ).
Proof.
  unfold iverson. simpl. auto with crunch.
Qed.
Theorem gp_gen_iverson' {X} `{TensorElem X} :
  forall p N (body : Z -> X),
    GEN [ n' < N ] (|[ p ]| body n' ) = (|[ p ]| (GEN [i < N ] body i )).
Proof.
  unfold iverson. simpl. auto with crunch.
Qed.

Goal forall X (H: TensorElem X) (f : Z -> Z -> (list X)) n m (l: list (list X)),
GEN [ i < Z.of_nat (n + 1) ]
  GEN [ n' < Z.of_nat m ]
  (|[ i <? Z.of_nat n ]| (|[ 0 <=? n' - 1 ]| l _[ i; n' - 1]) <+>
                         l _[ i; n'] <+>
                         (|[ n' + 1 <? Z.of_nat m ]| l _[ i;
                                                     n' + 1])) = [].
Proof.
  intros.
  rw<- @gp_gen_iverson.
Abort.

Theorem gp_double_iverson {X} `{TensorElem X} :
  forall p0 p1 e,
    (|[ p0 ]| (|[ p1 ]| e)) = |[ andb p0 p1 ]| e.
Proof.
  intros p0 p1 ?.
  destruct p0; destruct p1; unfold iverson; try (rewrite mul_1_id; reflexivity).
  simpl. now rewrite mul_0_idemp.
Qed.

Theorem collapse_iverson_same {X} `{TensorElem X} :
  forall (p : bool) (e : R),
    (|[ p ]| (|[ p ]| e)) = (|[ p ]| e).
Proof.
  intros.
  rewrite gp_double_iverson.
  rewrite Bool.andb_diag.
  reflexivity.
Qed.

Theorem iverson_comm {X} `{TensorElem X} :
  forall p1 p2 e,
    (|[ p1 ]| (|[ p2 ]| e)) = (|[ p2 ]| (|[ p1 ]| e)).
Proof.
  intros.
  rewrite gp_double_iverson.
  rewrite gp_double_iverson.
  rewrite Bool.andb_comm.
  reflexivity.
Qed.

Theorem gp_flatten_trunc_iverson {X} `{TensorElem X} :
  forall p k v,
    (|[ p ]| flatten_trunc k v) = flatten_trunc k (|[ p ]| v).
Proof.
  intros.
  unfold flatten_trunc.
  rewrite gp_gen_iverson.
  rw sum_iverson_lift.
  rw sum_iverson_lift.
  apply gen_eq_bound; intros.
  rewrite iverson_length.
  apply sum_eq_bound; intros.
  autorewrite with crunch reds.
  apply sum_eq_bound; intros.
  autorewrite with crunch reds.
  rewrite Bool.andb_comm.
  reflexivity.
Qed.

