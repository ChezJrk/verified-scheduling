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

Definition add A B C D (m1 m2 : (list (list (list (list R))))) :=
    GEN [ i < A ]
      GEN [ j < C ]
      GEN [ k < B ]
      GEN [ l < D ]
      (m1 _[i;j;k;l] * m2 _[i;j;k;l])%R.

Hint Unfold add : examples.  
Hint Resolve Z.div_lt_upper_bound mul_add_lt : crunch.

Lemma mul_add_lt : forall i j k A C,
    (0 <= i < A * C )%Z ->
    (0 <= j < A)%Z ->
    (0 <= k < C)%Z ->
    (i =? j * C + k)%Z = ((j =? i / C)%Z && (k =? i mod C))%Z.
Proof.
  intros. unbool. split; intros; try split.
  - subst. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
  - subst. rewrite Z.add_comm. rewrite Z.mod_add by lia.
    rewrite Z.mod_small by lia. reflexivity.
  - inversion H2. subst.
    rewrite div_mod_eq by lia. reflexivity.
Qed.      

Section Add.
  Variables (A B C D : nat) (m1 m2 : (list (list (list (list R))))).
  Derive add_split SuchThat
         (0 < A ->
          0 < B ->
          0 < C ->
          0 < D ->
          consistent m1 (A,(B,(C,(D,tt)))) ->
          consistent m2 (A,(B,(C,(D,tt)))) ->
          add (Z.of_nat A) (Z.of_nat B) (Z.of_nat C) (Z.of_nat D) m1 m2 =
            add_split) As matmultiled.
  Proof.
    reschedule.

    wrapid^ @tile_flatten_id around (GEN [ _ < (Z.of_nat A) ] _).

    inline flatten.
    rw @consistent_length.
    rw @consistent_length.
    rw @consistent_length.
    rw @get_gen_some.
    rw @get_gen_some.
    rw @mul_add_lt.
    rw<- @gp_double_iverson.
    rw<- @sum_iverson_lift.
    rw @sum_bound_indic_no_f_guard.
    rw @sum_bound_indic_no_f_guard.

    wrapid^ @tile_flatten_id around (GEN [ _ < _ * _] _).
    inline flatten.
    rw @consistent_length.
    rw @consistent_length.
    rw @consistent_length.
    rw @get_gen_some.
    rw @get_gen_some.
    rw @mul_add_lt.
    rw<- @gp_double_iverson.
    rw<- @sum_iverson_lift.
    rw @sum_bound_indic_no_f_guard.
    rw @sum_bound_indic_no_f_guard.

    wrapid^ @tile_flatten_id around (GEN [ _ < _ * _] _).
    inline flatten.
    rw @consistent_length.
    rw @consistent_length.
    rw @consistent_length.
    rw @get_gen_some.
    rw @get_gen_some.
    rw @mul_add_lt.
    rw<- @gp_double_iverson.
    rw<- @sum_iverson_lift.
    rw @sum_bound_indic_no_f_guard.
    rw @sum_bound_indic_no_f_guard.

    repeat rw Z.div_div.
    done.
  Defined.
 End Add.

Hint Unfold add add_split : examples.  
