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

From ATL Require Import ATL Common CommonTactics Tactics GenPushout LetLifting.

Definition im2colmini K W RR (w : (list (list R))) (x : list R) :=
    GEN [ k < K ]
      GEN [ p < W ]
        SUM [ r < RR ]
        |[ p + r <? K ]| (w _[ k ; r ] * x _[ p + r ])%R.

Definition im2col B K W C RR (w x : (list (list (list R)))) :=
    GEN [ n < B ]
    GEN [ k < K ]
    GEN [ p < W ]
    SUM [ c < C ]
    SUM [ r < RR ]
    (w _[ k ; c ; r ] * x _[ n ; c ; p + r ])%R.

Hint Unfold im2col im2colmini : examples.  

Section Mini.
  Variables (K W RR : Z) (w : (list (list R))) (x : list R).
  Derive im2colminilifted SuchThat
     ((0 < RR)%Z ->
     im2colmini K W RR w x = im2colminilifted) As miniim2col.         
  Proof.
    reschedule.

    rw<- guard_mul_r.

    rw^ @lbind_helper for (fun e => _ * e)%R.

    time rw ll_sum.

    rw @ll_gen.

    rw @ll_gen_indep.

    done.
  Defined.
End Mini.

Section Im2col.
  Variables (B K W C RR : Z) (w x : (list (list (list R)))).
  Derive im2col_lifted SuchThat
         (im2col B K W C RR w x =
          im2col_lifted) As im2col_sched.
  Proof.
    reschedule.

    rw^ @lbind_helper for (fun e => _ * e)%R.

    rw @ll_sum.

    rw @ll_sum.

    rw @ll_gen.
    
    rw @ll_gen_indep.

    rw @ll_gen.

    done.    
  Qed.
End Im2col.

Hint Unfold im2col_lifted im2colminilifted : examples.  

Goal forall B K W C RR w x,
    im2col_lifted B K W C RR w x =
    tlet x0
  := GEN [ i < B ]
         GEN [ i0 < W ]
         GEN [ i1 < C ]
         GEN [ i2 < RR ]
         x _[ i; i1; i0 + i2]
    in GEN [ n' < B ]
           GEN [ n'0 < K ]
           GEN [ n'1 < W ]
           SUM [ n'2 < C ]
           SUM [ n'3 < RR ]
           (w _[ n'0; n'2; n'3] * x0 _[ n'; n'1; n'2; n'3])%R.
Proof. reflexivity. Qed.
    
Goal forall K W RR w x,
    im2colminilifted K W RR w x =
    tlet x0 := GEN [ i < W ]
                   GEN [ i0 < RR ]
                   (|[ i + i0 <? K ]| x _[ i + i0])
    in GEN [ n' < K ]
           GEN [ n'0 < W ]
           SUM [ n'1 < RR ]
           (w _[ n'; n'1] * x0 _[ n'0; n'1])%R.
Proof. reflexivity. Qed.
    
