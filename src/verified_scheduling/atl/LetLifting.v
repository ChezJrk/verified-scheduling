From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import micromega.Zify.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Reals.Rpower.
Import ListNotations.

From ATL Require Import ATL Common Tactics CommonTactics.

Theorem ll_exp {X} `{TensorElem X} : forall (e : X) a,
  exp (tlet x := e in a) = tlet x := e in exp a.
Proof. trivial. Qed.
  
Theorem ll_concat_l {X Y} `{TensorElem X} :
  forall (a : Y -> list X) (b : list X) (e : Y),
    (tlet a' := e in a a') <++> b = tlet a' := e in (a a') <++> b.
Proof. trivial. Qed.

Theorem ll_concat_r {X Y} `{TensorElem X} :
  forall (a : Y -> list X) (b : list X) (e : Y),
    b <++> (tlet a' := e in a a') = tlet a' := e in b <++> (a a').
Proof. trivial. Qed.

Theorem ll_bin_l {X Y} `{TensorElem X} : forall (a : Y -> X) (b : X) (e : Y),
    (tlet a' := e in a a') <+> b = tlet a' := e in (a a') <+> b.
Proof. trivial. Qed.

Theorem ll_bin_r {X Y} `{TensorElem X} : forall (a : Y -> X) (b : X) (e : Y),
    b <+> (tlet a' := e in a a') = tlet a' := e in b <+> (a a').
Proof. trivial. Qed.

Theorem ll_plus_l {X} : forall (e0 : X) (e1 : X -> R) (e2 : R),
    Rplus (tlet x := e0 in e1 x) e2 = tlet x := e0 in Rplus (e1 x) e2.
Proof. trivial. Qed.

Theorem ll_plus_r {X} : forall (e0 : X) (e1 : X -> R) (e2 : R),
    Rplus e2 (tlet x := e0 in e1 x) = tlet x := e0 in Rplus e2 (e1 x).
Proof. trivial. Qed.

Theorem ll_mult_l {X} : forall (e0 : X) (e1 : X -> R) (e2 : R),
    Rmult (tlet x := e0 in e1 x) e2 = tlet x := e0 in Rmult (e1 x) e2.
Proof. trivial. Qed.

Theorem ll_mult_r {X} : forall (e0 : X) (e1 : X -> R) (e2 : R),
    Rmult e2 (tlet x := e0 in e1 x) = tlet x := e0 in Rmult e2 (e1 x).
Proof. trivial. Qed.

Theorem ll_div_l {X} : forall (e0 : X) (e1 : X -> R) (e2 : R),
    Rdiv (tlet x := e0 in e1 x) e2 = tlet x := e0 in Rdiv (e1 x) e2.
Proof. trivial. Qed.

Theorem ll_div_r {X} : forall (e0 : X) (e1 : X -> R) (e2 : R),
    Rdiv e2 (tlet x := e0 in e1 x) = tlet x := e0 in Rdiv e2 (e1 x).
Proof. trivial. Qed.

Theorem ll_arg {X Y Z} : forall (f : Y -> Z) (e0 : X) (e1 : X -> Y),
    f (tlet x := e0 in e1 x) = tlet x := e0 in f (e1 x).
Proof. trivial. Qed.

Theorem ll_tuple_l {X Y Z} : forall (e0 : X) (e1 : X -> Y) (e2 : Z),
    (tlet x := e0 in e1 x, e2) = tlet x := e0 in (e1 x,e2).
Proof. trivial. Qed.

Theorem ll_tuple_r {X Y Z} : forall (e0 : X) (e1 : Y) (e2 : X -> Z),
    (e1, tlet x := e0 in e2 x) = tlet x := e0 in (e1,e2 x).
Proof. trivial. Qed.

Theorem ll_fst {X Y Z} : forall (e0 : X) (e1 : X -> Y * Z),
    fst (tlet x := e0 in e1 x) = tlet x := e0 in fst (e1 x).
Proof. trivial. Qed.

Theorem ll_snd {X Y Z} : forall (e0 : X) (e1 : X -> Y * Z),
    snd (tlet x := e0 in e1 x) = tlet x := e0 in snd (e1 x).
Proof. trivial. Qed.
  
Theorem ll_gen {X Y} `{TensorElem X} `{TensorElem Y}:
  forall N (e0 : Z -> X) (e1 : X -> Z -> Y),
  GEN [ n' < N ] (tlet x := e0 n' in e1 x n')
  = tlet x := GEN [ i < N ] e0 i in
    GEN [ n' < N ] e1 (x _[ n' ]) n'.
Proof.
  intros. simpl.
  apply gen_eq_bound.
  intros. f_equal. symmetry.
  rewrite get_gen_some; auto with crunch.
Qed.

Theorem ll_gen_indep {X Y} `{TensorElem X} `{TensorElem Y}:
  forall N (e0 : X) (e1 : X -> Z -> Y),
  GEN [ n' < N ] (tlet x := e0 in e1 x n')
  = tlet x := e0 in
    GEN [ n' < N ] e1 x n'.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem ll_gen_bound {X Y} `{TensorElem X} `{TensorElem Y}:
  forall N (e0 : Z -> X) (e1 : X -> Z -> Y) k s,
    (k <= N)%Z ->
    (0 < k)%Z ->
    (forall x, consistent (e0 x) s) ->
  GEN [ n' < N ] (tlet x := (|[ n' <? k ]| e0 n') in e1 x n')
  = tlet x := GEN [ n' < k ] e0 n' in
    GEN [ n' < N ] e1 (x _[n']) n'.
Proof.
  intros. unfold let_binding.
  apply gen_eq_bound; intros.
  destruct (i <? k)%Z eqn:e; unbool_hyp.
  - rewrite true_iverson.
    rewrite get_gen_some by auto.
    reflexivity.
  - rewrite get_gen_null by lia.
    f_equal.
    unfold iverson. eapply mul_0_absorb; eauto.  
Qed.

Theorem ll_sumr {X Y} `{TensorElem X} `{TensorElem Y}:
  forall N m (e0 : Z -> X) (e1 : X -> Z -> Y),
  SUM [ m <= n' < N ] (tlet x := e0 n' in e1 x n')
  = tlet x := GEN [ m <= i < N ] e0 i in
    SUM [ m <= n' < N ] e1 (x _[ n' - m ]) n'.
Proof.
  intros. simpl.
  apply sumr_eq_bound.
  intros. unfold let_binding. 
  rewrite get_genr_some; try lia.
  rewrite Zplus_minus. reflexivity.
Qed.

Theorem ll_sum {X Y} `{TensorElem X} `{TensorElem Y}:
  forall N (e0 : Z -> X) (e1 : X -> Z -> Y),
  SUM [ n' < N ] (tlet x := e0 n' in e1 x n')
  = tlet x := GEN [ i < N ] e0 i in
    SUM [ n' < N ] e1 (x _[ n' ]) n'.
Proof.
  intros. simpl.
  apply sum_eq_bound.
  intros. f_equal. symmetry.
  rewrite get_gen_some; auto with crunch.
Qed.

Theorem ll_sum_indep {X Y} `{TensorElem X} `{TensorElem Y}:
  forall N (e0 : X) (e1 : X -> Z -> Y),
  SUM [ n' < N ] (tlet x := e0 in e1 x n')
  = tlet x := e0 in
    SUM [ n' < N ] e1 x n'.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem ll_get {X Y} `{TensorElem X} `{TensorElem Y} :
  forall (I : Z) (e0 : X) (e1 : X -> list Y),
    (tlet x := e0 in e1 x) _[ I ] = tlet x := e0 in (e1 x) _[ I ].
Proof. trivial. Qed.

Theorem ll_iverson {X Y} `{TensorElem X} `{TensorElem Y} :
  forall (p : bool) (e0 : X) (e1 : X -> Y) a s,
    consistent e0 s ->
    (forall x, consistent x s -> consistent (e1 x) a) ->
    (|[ p ]| (tlet x := e0 in e1 x)) = tlet x := |[ p ]| e0 in |[ p ]| (e1 x).
Proof.
  unfold iverson.
  unfold let_binding.
  destruct p; intros.
  repeat rewrite mul_1_id. reflexivity.
  eapply mul_0_absorb; eauto.
  eapply H2.
  eapply consistent_mul. auto.
Qed.

Theorem ll_iverson_ {X Y} `{TensorElem Y} :
  forall (p : bool) (e0 : X) (e1 : X -> Y),
    (|[ p ]| (tlet x := e0 in e1 x)) = tlet x := e0 in |[ p ]| (e1 x).
Proof.
  unfold iverson.
  unfold let_binding.
  intros. auto.
Qed.

Theorem let_let_same {X Y} `{TensorElem Y} :
  forall e1 (f : X -> X -> Y),
  (tlet x := e1 in (tlet y := e1 in f x y)) =
  tlet x := e1 in f x x.
Proof. intros. unfold let_binding. reflexivity. Qed.

Theorem let_let_flip {X Y Z} `{TensorElem Z} `{TensorElem Y} :
  forall (e1 : X) (f : X -> Y) (g : Y -> Z),
    let_binding (let_binding e1 f) g =
    let_binding e1 (fun x => g (f x)).
Proof.
  intros. unfold let_binding. reflexivity.
Qed.

Theorem let_rotate_concat_right {X Y} `{TensorElem X} `{TensorElem X} :
  forall (e1 e2 : list X) (f : list X -> Y),
    let_binding (e1 <++> e2) f = let_binding e1 (fun e => f (e <++> e2)).
Proof. intros. unfold let_binding. reflexivity. Qed.

Theorem let_rotate_concat_left {X Y} `{TensorElem X} `{TensorElem X} :
  forall (e1 e2 : list X) (f : list X -> Y),
    let_binding (e1 <++> e2) f = let_binding e2 (fun e => f (e1 <++> e)).
Proof. intros. unfold let_binding. reflexivity. Qed.

Lemma let_guard_lift {X Y} `{TensorElem X} `{TensorElem Y} :
  forall p (e1 : X) (e2 : X -> Y) s s',
    consistent e1 s ->
    (forall x, consistent x s -> consistent (e2 x) s') ->
    let_binding e1 (fun x => |[ p ]| e2 x) =
    let_binding (|[ p ]| e1) (fun x => |[ p ]| e2 x).
Proof.
  intros. unfold let_binding.
  destruct p. repeat rewrite true_iverson. auto.
  unfold iverson.
  eapply mul_0_absorb.
  eauto. apply H2.
  apply consistent_mul. auto. auto.
Qed.

Theorem let_let_comm {X Y Z} `{TensorElem Z} `{TensorElem Y} :
  forall (e1 : X) (f : X -> Y) (g : Y -> Z),
    let_binding (let_binding e1 f) g =
    let_binding e1 (fun x => let_binding (f x) g).
Proof.
  intros. unfold let_binding. reflexivity.
Qed.
