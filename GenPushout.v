From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.PreOmega.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Vectors.Vector.
From Coq Require Import Reals.Reals. Import RIneq. Import Rdefinitions.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.

From ATL Require Import ATL Common Tactics Div CommonTactics.

Set Warnings "-omega-is-deprecated,-deprecated".

Definition to_val {X} `{TensorElem X} (opt : option X) : X :=
  match opt with
  | None => null
  | Some v => v
  end.

Lemma nth_map {X} `{TensorElem X} : forall i f v,
    i < length v ->
    @nth_error X (List.map f v) i = Some (f (to_val (nth_error v i))).
Proof.
  induction i; intros f v H0; destruct v; simpl in *;
    try contra_crush; auto.
    apply lt_S_n in H0.
    eapply IHi in H0.
    apply H0.
Qed.

Theorem gp_iverson {X} `{TensorElem X} :
  forall I p (e : list X),
    (|[ p ]| e) _[I] = |[ p ]| (e _[I]).
Proof.
  intros.
  destruct (I <? Z.of_nat (length e))%Z eqn:ie;
    destruct (0 <=? I)%Z eqn: i0; unbool.
  -  unfold iverson, get. simpl.
     destruct I.
     + destruct e.
       simpl in ie. lia.
       simpl. auto.
     + simpl in *. rewrite nth_map by (zify; lia).
       destruct e. simpl in *. lia.
       simpl.
       unfold to_val.
       assert (Pos.to_nat p0 < length (x::e)) by (zify; lia).
       apply nth_error_Some in H0.
       destruct (nth_error (x::e) (Pos.to_nat p0)). auto. contradiction.
     + contradiction.
  - destruct e.
    + simpl. unfold get. simpl. 
      destruct p.
      * repeat rewrite true_iverson.
        reflexivity.
      * unfold iverson.
        symmetry.
        apply mul_0_null.
    + rewrite get_neg_null; try lia.
      destruct p.
      * repeat rewrite true_iverson.
        rewrite get_neg_null; try lia.
        auto.
      * unfold iverson.
        rewrite mul_0_idemp.
        unfold scalar_mul at 1. simpl.
        rewrite get_neg_null; auto.
        unfold iverson. apply mul_0_idemp.
  - destruct e.
    + unfold get. simpl.
      destruct p.
      * rewrite true_iverson. auto.
      * unfold iverson.
        symmetry.
        apply mul_0_null.
    + rewrite get_znlt_null; try lia.
      destruct p.
      * repeat rewrite true_iverson.
        rewrite get_znlt_null; try lia.
        reflexivity.
      * unfold iverson.
        rewrite mul_0_idemp.
        unfold scalar_mul at 1. simpl.
        destruct I; try (simpl in *; zify; lia).
        rewrite get_znlt_null.
        unfold iverson.
        rewrite mul_0_idemp.
        reflexivity.
        assert (length (scalar_mul 0 x :: List.map (scalar_mul 0) e) <=
                Pos.to_nat p).
        { simpl. rewrite map_length. simpl in *. zify. lia. }
        zify. lia.
  - zify. lia.
Qed.
Hint Rewrite @gp_iverson : crunch.

Lemma gp_genr_iverson {X} `{TensorElem X} :
  forall p N K (body : Z -> X),
    (|[ p ]| (GEN [K <= i < N ] body i )) = GEN [ K <= n' < N ] (|[ p ]| body n' ).
Proof.
Admitted.

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

