From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import omega.PreOmega.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Coq Require Import ZArith.Int.
From Coq Require Import ZArith.Zdiv.
From Coq Require Import ZArith.Znat.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Classes.Morphisms.
Import ListNotations.
From ATL Require Import ATL Tactics Common CommonTactics Div GenPushout
     LetLifting.

Set Warnings "-omega-is-deprecated,-deprecated".

Generalizable All Variables.

(* IDENTITIES *)
Theorem trunc_r_pad_r_id {X} `{TensorElem X} : forall (V : list X) K n s,
    consistent V (n,s) ->
    trunc_r n (pad_r K V) = V.
Proof.
  intros. unfold trunc_r, pad_r. inversion H0.
  rw @get_gen_some. rewrite H6. simpl_guard.
  rewrite gen_of_nat_get_id; auto.
Qed.

Theorem trunc_r_pad_r_unsafe_id {X} `{TensorElem X} : forall (V : list X) K n s,
    consistent V (n,s) ->
    trunc_r n (pad_r_unsafe K V) = V.
Proof.
  intros. unfold trunc_r, pad_r_unsafe. inversion H0.
  rw @get_gen_some.
  rewrite gen_of_nat_get_id; auto.
Qed.

Theorem trunc_l_pad_l_unsafe_id {X} `{TensorElem X} :
  forall (V : list X) K n s,
    consistent V (n,s) ->
    trunc_l n (pad_l_unsafe K V) = V.
Proof.
  intros. unfold trunc_l, pad_l_unsafe. inversion H0.
  rw @get_gen_some.
  rewrite H6.
  rw minus_plus.
  rw Z.add_simpl_r.
  rewrite gen_of_nat_get_id; eauto.
Qed.

Theorem trunc_l_pad_l_id {X} `{TensorElem X} : forall (V : list X) K n s,
    consistent V (n,s) ->
    trunc_l n (pad_l K V) = V.
Proof.
  intros. unfold trunc_l, pad_l. inversion H0.
  rw @get_gen_some.
  rewrite H6.
  rewrite minus_plus.
  rw Z.add_simpl_r.
  simpl_guard.
  rewrite gen_of_nat_get_id; auto.
Qed.

Theorem flatten_trunc_tile_id {X} `{TensorElem X} :
  forall (V : list X) K n s,
    0 < K ->
    consistent V (n,s)->
    flatten_trunc n (tile V K) = V.
Proof.
  intros.
  inversion H1.
  unfold tile.
  unfold flatten_trunc.
  rewrite of_nat_div_distr.
  rewrite gen_length.
  rewrite Z2Nat.id by lia. rewrite H7.
  erewrite consistent_length by
      (eapply consistent_get;
       eapply @consistent_gen; rewrite <- H7; simpl; auto with crunch;       
       intros;
       apply consistent_gen; auto;
       intros;
       apply consistent_iverson;
       eapply consistent_get;
       subst; eauto;
       eauto; eauto).

  etransitivity.
  apply gen_eq_bound; intros.
  apply sum_eq_bound; intros.
  apply sum_eq_bound; intros.
  replace (i =? i0 * Z.of_nat K + i1)%Z with
      (i1 =? i - i0 * Z.of_nat K)%Z by (unbool; zify; lia).
  apply iverson_weak.
  rewrite get_gen_some by auto with crunch.
  rewrite get_gen_some by auto with crunch.
  reflexivity. lazy beta.

  etransitivity.
  apply gen_eq_bound; intros.
  apply sum_eq_bound; intros.
  erewrite sum_bound_indic_no_f.
  rewrite Zplus_minus.
  replace (i <? Z.of_nat n)%Z with (true). rewrite true_iverson.
  reflexivity. unbool. split; auto.
  auto with crunch.
  intros. apply consistent_iverson. eapply consistent_get. subst. eauto.
  apply consistent_iverson. eapply consistent_get. subst. eauto.
  lazy beta.

  etransitivity.
  apply gen_eq_bound; intros.
  pose (Z_div_mod i (Z.of_nat K)). peel_hyp.
  destruct (Z.div_eucl i (Z.of_nat K)) eqn:ee.
  destruct y.
  apply sum_eq_bound; intros.
  replace (i - i0 * Z.of_nat K <? Z.of_nat K)%Z with
      (i - Z.of_nat K <? i0 * Z.of_nat K)%Z by
      (unbool; zify; lia).
  replace (0 <=? i - i0 * Z.of_nat K)%Z with
      ( i0 * Z.of_nat K <=? i )%Z by
      (unbool; zify; lia).
  rewrite H10 at 1. rewrite H10 at 1.  
 
  replace (Z.of_nat K * z + z0 - Z.of_nat K <? i0 * Z.of_nat K)%Z with
      (Z.of_nat K * z - Z.of_nat K * 1 - i0 * Z.of_nat K <? - z0)%Z by
      (unbool; zify; lia).
  replace (i0 * Z.of_nat K <=? Z.of_nat K * z + z0)%Z with
      (i0 * Z.of_nat K - Z.of_nat K * z <=? z0)%Z by
      (unbool; zify; lia).
  replace (i0 * Z.of_nat K)%Z with (Z.of_nat K * i0)%Z by apply Z.mul_comm.
  repeat rewrite <- Z.mul_sub_distr_l.

  replace (Z.of_nat K * (z - 1 - i0) <? - z0)%Z with
      (z0 <? Z.of_nat K * (i0 + 1 - z))%Z.

  2: {
  unbool. rewrite Z.opp_lt_mono.
  rewrite <- Z.mul_opp_r.
  rewrite Z.opp_sub_distr.
  rewrite Z.opp_add_distr.
  rewrite Z.add_opp_r.
  rewrite Z.add_comm.
  rewrite Z.add_sub_assoc.
  rewrite Z.add_opp_r.
  replace (z - i0 - 1)%Z with (z - 1 -i0)%Z by lia.
  split; intros. auto. auto. }

  replace (z0 <? Z.of_nat K * (i0 + 1 - z))%Z with
      (0 <=? (i0 - z))%Z by (unbool; rewrite mul_lt; lia).

  replace (Z.of_nat K * (i0 - z) <=? z0)%Z with
      (i0 - z <=? 0)%Z by
      (unbool; rewrite mul_le; lia).

  replace ((0 <=? i0 - z)%Z && (i0 - z <=? 0)%Z) with (i0 =? z)%Z by
      (unbool; zify; lia).

  pose (div_eucl_div i (Z.of_nat K)). peel_hyp.
  rewrite ee in y. rewrite y.
  reflexivity.
  lazy beta.

  etransitivity. apply gen_eq_bound; intros.
  erewrite sum_bound_indic_no_f.
  assert ((0 <=? i / Z.of_nat K)%Z = true). unbool.
  apply Z.div_pos. auto. auto with crunch. rewrite H10.
  rewrite andb_true_r.
  rewrite <- of_nat_div_distr.

  assert ((i / Z.of_nat K <?
           Z.of_nat n // (Z.of_nat K) )%Z = true).
  unbool. apply floor_lt_ceil_mono_l; lia.
  rewrite H11. rewrite true_iverson.
  reflexivity. auto with crunch.
  intros. eapply consistent_get; subst; eauto.
  eapply consistent_get; subst; eauto.
  apply gen_get_id.
  rewrite Nat2Z.id. auto.
Qed.
  
Theorem tile_flatten_id {X} `{TensorElem X} :
  forall (V : list (list X)) K n s,
    consistent V (n,(K,s))->
    tile (flatten V) K = V.
Proof.
  intros.

  inversion H0. inversion H3.
  unfold flatten.
  rewrite <- Nat2Z.inj_mul.
  simpl length.
  unfold tile.
  rewrite gen_of_nat_length.
  rewrite of_nat_div_distr.
  simpl length in *. subst.
  rewrite nat_mul_div_id by lia.

  etransitivity.
  {
    apply gen_eq_bound; intros.
    apply gen_eq_bound; intros.
    assert ((i * Z.of_nat (S (length xs0)) + i0 <?
             Z.of_nat (S (length xs) * S (length xs0)))%Z = true) by
    (unbool; zify; apply mul_add_lt; auto). rewrite H7. rewrite true_iverson.
    rewrite get_gen_some.
    reflexivity.
    {
      rewrite Nat2Z.inj_mul.
      apply mul_add_lt; auto.
    }
    auto with crunch.
  } lazy beta.

  etransitivity.
  apply gen_eq_bound; intros.
  apply gen_eq_bound; intros.
  apply sum_eq_bound; intros.
  apply sum_eq_bound; intros.
  rewrite factor_unique by auto with crunch.
  rewrite <- collapse_iverson.
  reflexivity. lazy beta.

  etransitivity.
  apply gen_eq_bound; intros.
  apply gen_eq_bound; intros.
  apply sum_eq_bound; intros.
  rewrite <- sum_iverson_lift.

  rewrite Z.eqb_sym.
  apply iverson_weak.
  apply sum_eq_bound; intros.
  rewrite Z.eqb_sym.
  reflexivity. lazy beta.

  etransitivity.
  apply gen_eq_bound; intros.
  apply gen_eq_bound; intros.
  erewrite sum_of_nat_bound_indic_no_f; auto with crunch.
  replace (0 <=? i)%Z with true by (unbool; split; auto).
  rewrite andb_true_r.
  replace (i <? Z.of_nat (S (length xs)))%Z with true by (unbool; split; auto).
  rewrite true_iverson.
  erewrite sum_of_nat_bound_indic_no_f; auto with crunch.  
  intros.
  consistent_shape; subst; eauto.
  consistent_shape; subst; eauto.
  intros.
  consistent_shape; subst; eauto with crunch.
  consistent_shape; subst; eauto with crunch.  

  etransitivity. apply gen_eq_bound; intros.
  erewrite gen_of_nat_get_id'. reflexivity.
  consistent_shape; subst; eauto. auto.

  erewrite gen_of_nat_get_id'; subst; eauto.
Qed.

Theorem transpose_transpose_id {X} `{TensorElem X} :
  forall (V : list (list X)) s,
    consistent V s ->
    transpose (transpose V) = V.
Proof.
  intros.
  inversion H0.
  inversion H1.
  subst.
  unfold transpose.
  repeat rewrite get_0_cons.
  repeat rewrite get_0_gen_of_nat by (simpl; auto with crunch).
  repeat rewrite gen_of_nat_length.

  etransitivity.
  apply gen_eq_bound; intros.
  apply gen_eq_bound; intros.
  rewrite get_gen_some.
  rewrite get_gen_some. reflexivity.
  eauto.
  auto. eauto. auto. auto. auto. lazy beta.

  etransitivity.
  apply gen_eq_bound; intros.
  erewrite gen_of_nat_get_id. reflexivity.
  erewrite get_length. eauto.
  eauto.
  erewrite gen_of_nat_get_id. reflexivity. auto.
Qed.              

(* HALF IDENTITIES *)
Lemma gen_trunc_guarded {X} `{TensorElem X} :
  forall I N (body : Z -> X),
             GEN [ i < Z.of_nat N ] body i =
             trunc_l N (GEN [ i < Z.of_nat (N + I)]
                       |[ Z.of_nat I <=? i ]| body (i-Z.of_nat I)%Z).
Proof.
    intros. unfold trunc_l.
    rewrite gen_of_nat_length.
    rewrite minus_plus. simpl.
    symmetry.
    rw @get_gen_some.    
    rw @Z.add_simpl_r.
    simpl_guard.
    reflexivity.
Qed.  

Lemma pad_gen {X} `{TensorElem X} :
  forall I N (body : Z -> X) s,
    0 < N ->
    (forall x, consistent (body x) s) ->
    GEN [ i < Z.of_nat (N+I) ] (|[ i <? Z.of_nat N ]| body i) =
    pad_r_unsafe I (GEN [ i < Z.of_nat N ] body i).
Proof.
  intros. unfold pad_r_unsafe.
  rewrite gen_of_nat_length.
  apply gen_eq_bound; intros.
  symmetry.
  erewrite get_gen_some_guard.
  simpl_guard.
  reflexivity. lia. eauto.
Qed.

Lemma trunc_gen {X} `{TensorElem X} :
  forall N (body : Z -> X) I,
    (GEN [ i < Z.of_nat (N-I) ] body i) =
    trunc_r (N-I) (GEN [ i < Z.of_nat N ] body i).
Proof.
  intros. unfold trunc_r.
  apply gen_eq_bound; intros.
  symmetry.
  rewrite get_gen_some. auto. zify. lia. auto.
Qed.

Lemma gen_trunc {X} `{TensorElem X} :
  forall N (body : Z -> X) I,
             GEN [ i < Z.of_nat N ] body i =
             trunc_l N (GEN [ i < Z.of_nat (N + I)] body (i-Z.of_nat I)%Z).
Proof.
    intros. unfold trunc_l.
    rewrite gen_of_nat_length.
    rewrite minus_plus. simpl.
    symmetry.
    rw @get_gen_some.
    rw @Z.add_simpl_r.
    reflexivity.
Qed.  

Lemma help {X} `{TensorElem X} :
  forall N body I s,
    1 < N ->
    I < N ->
    (forall x, consistent (body x) s) ->
    GEN [ i < Z.of_nat N ] (|[ 0 <=? i- Z.of_nat I]| body i) =
  pad_l_unsafe I (GEN [ i < Z.of_nat (N-I) ] body (i+ Z.of_nat I)%Z).
Proof.
  intros. unfold pad_l_unsafe.
  rewrite gen_of_nat_length. simpl.
  rewrite Nat.sub_add by lia.
  apply gen_eq_bound; intros.
  erewrite get_gen_some_guard.
  rewrite Nat2Z.inj_sub.
  symmetry.
  simpl_guard.
  rewrite Z.sub_add by lia.
  reflexivity. lia. auto with crunch. 
  eauto.
Qed.

Goal forall n m k (v : list (list R)),
    0 < k ->
    0 < n ->
    0 < m ->
    consistent v (n,(m,tt)) ->
    GEN [ i < Z.of_nat n ] GEN [ j < Z.of_nat m ]
        v _[i;j] <+> v _[i+1;j+1] = @nil _.
Proof.
  intros.
  wrapid @flatten_trunc_tile_id around (GEN [ _ < Z.of_nat n ] _) with m.
Abort.

(* TRANSPOSE TRANSFORMATIONS *)
Theorem transpose_gen_gen {X} `{TensorElem X} : forall n m f,
    (0 < n)%Z ->
    (0 < m)%Z ->
    transpose (GEN [ i < n ] GEN [ j < m ] f i j) =
    GEN [ j < m ] GEN [ i < n ] f i j.
Proof.
  intros. unfold transpose.
  rewrite gen_length.
  rewrite Z2Nat.id; try lia.
  replace ((length ((GEN [ i < n ]
                               GEN [ j < m ]
                               f i j) _[ 0]))) with (Z.to_nat m).
  rewrite Z2Nat.id; try lia.

  etransitivity.
  apply gen_eq_bound; intros.
  apply gen_eq_bound; intros.
  rewrite get_gen_some; auto with crunch.
  rewrite get_gen_some; auto with crunch.
  reflexivity. lazy beta. reflexivity.

  destruct n; try (zify; lia).
  unfold gen, genr.
  rewrite Z.sub_0_r.
  simpl. posnat.
  simpl. rewrite get_0_cons.
  rewrite Z.sub_0_r.
  rewrite gen_helper_length.
  auto.
Qed.

Theorem transpose_iverson {X} `{TensorElem X} : forall p e s,
    consistent e s ->
    transpose (|[ p ]| e) = (|[ p ]| transpose e).
Proof.
  intros.
  inversion H0.
  inversion H1.
  subst.
  destruct p.
  - autorewrite with crunch.
    reflexivity.
  - unfold transpose.
    rewrite gp_gen_iverson.
    erewrite consistent_length.
    apply gen_eq_bound; intros.
    erewrite consistent_length.
    rewrite gp_gen_iverson.
    apply gen_eq_bound; intros.
    autorewrite with crunch.
    reflexivity.

    apply consistent_iverson.
    eauto.

    eapply consistent_get.
    apply consistent_iverson. simpl.
    eauto.
Qed.
    
Theorem transpose_sum {X} `{TensorElem X} : forall f n s,
    (0 < n)%Z ->
    (forall x, 0 <= x /\ x < n -> consistent (f x) s)%Z ->
    transpose (SUM [ i < n ] f i) = SUM [i < n ] transpose (f i).
Proof.
  intros.
  unfold transpose.
  assert (consistent (SUM [i < n ] f i) s).
  { apply consistent_sum; auto. }

  destruct s.  
  assert (consistent ((SUM [i < n ] f i) _[0]) s).
  { eapply consistent_get. eapply consistent_sum; eauto. }

  destruct s.

  erewrite get_length; eauto.
  erewrite consistent_length; eauto.
  
  symmetry.
  etransitivity.
  eapply sum_eq_bound; intros.
  erewrite get_length; eauto.
  erewrite consistent_length; eauto.
  reflexivity. lazy beta.

  rewrite <- @sum_gen_swap; auto.
  apply gen_eq_bound; intros.
  rewrite <- @sum_gen_swap; auto.
  apply gen_eq_bound; intros.
  
  erewrite @get_sum.
  erewrite @get_sum.
  auto. auto. eauto. auto. intros.
  eapply consistent_get. eauto.
Qed.  

Theorem transpose_bin {X} `{TensorElem X} : forall (a b : list (list X)) s,
    consistent a s ->
    consistent b s ->
    transpose (a <+> b) = transpose a <+> transpose b.
Proof.
  intros. inversion H0. inversion H1.
  inversion H2. inversion H7. subst.
  unfold transpose. simpl bin.

  rewrite tensor_add_step. rewrite get_0_cons.
  inversion H11. subst.

  erewrite consistent_length by
  ( eapply consistent_bin; eauto; simpl; try rewrite H6; eauto).
  simpl. rewrite H6.

  pose proof (@bin_gen (list X) _). simpl in H4.
  rewrite H4.
  apply gen_eq_bound; intros.
  replace (length (tensor_add xs xs0)) with (length xs0).

  pose proof (@bin_gen X _). simpl in H14.
  rewrite H14.
  apply gen_eq_bound; intros.
  repeat erewrite <- get_bin_distr.
  simpl. symmetry. rewrite tensor_add_step.
  reflexivity.

  eauto. eauto.
  eapply consistent_get. eauto.
  eapply consistent_get. eauto.
  
  erewrite length_add_length. eauto. eauto. eauto.
Qed.

Theorem transpose_let {X Y} `{TensorElem X} `{TensorElem Y} :
  forall (e1 : Y) (e2 : Y -> list (list X)),
    transpose (tlet x := e1 in e2 x) = tlet x := e1 in transpose (e2 x).
Proof.
  intros.
  unfold let_binding.
  auto.
Qed.

(* UNFOLDING *)
Theorem unfold_transpose {X} `{TensorElem X} :
  forall (v : list (list X)) s n m,
    consistent v (n,(m,s)) ->
    transpose v = GEN [ x0 < Z.of_nat m ]
                      GEN [ y < Z.of_nat n ]
                      v _[ y; x0].
Proof.
  intros. unfold transpose.
  erewrite consistent_length by (eapply consistent_get; eauto).
  inversion H0. rewrite H6.
  reflexivity.
Qed.

Theorem unfold_inner_transpose {X} `{TensorElem X} :
  forall v s,
    consistent v s ->
    transpose (transpose v) =
    transpose (GEN [ x < Z.of_nat (length (v _[ 0])) ]
                   GEN [ y < Z.of_nat (length v) ]
                   v _[ y; x]).
Proof. intros. reflexivity. Qed.

Theorem unfold_outer_transpose {X} `{TensorElem X} :
  forall v s,
    consistent v s ->
    transpose (transpose v) =
    GEN [ x < Z.of_nat (length v) ]
        GEN [ y < Z.of_nat (length (v _[0])) ]
        (transpose v) _[ y; x].
Proof. intros. inversion H0.
       inversion H1.
       unfold transpose at 1.
       erewrite get_length by (consistent_shape; subst; eauto).
       erewrite get_length by (consistent_shape; subst; eauto). subst.
       apply gen_eq_bound; intros.
       erewrite consistent_length by (consistent_shape; subst; eauto).
       reflexivity.
Qed.

Lemma unfold_flatten_trunc {X} `{TensorElem X} : forall k (v : list (list X)),
    flatten_trunc k v = GEN [ i < Z.of_nat k ]
                            SUM [ j < Z.of_nat (length v) ]
                            SUM [ k0 < Z.of_nat (length (v _[ 0])) ]
                            (|[ i =? j * Z.of_nat (length (v _[ 0])) + k0 ]|
                             v _[ j; k0]).
Proof. intros. unfold flatten_trunc. auto. Qed.

Lemma unfold_flatten {X} `{TensorElem X} : forall (v : list (list X)),
    flatten v =
    GEN [ i < Z.of_nat (length v) * Z.of_nat (length (v _[ 0])) ]
        SUM [ j < Z.of_nat (length v) ]
        SUM [ k < Z.of_nat (length (v _[ 0])) ]
        (|[ i =? j * Z.of_nat (length (v _[ 0])) + k ]| v _[ j; k]).
Proof. intros. unfold flatten. reflexivity. Qed.

(* NORMALIZE FLATTEN *)
Theorem flatten_let {X Y} `{TensorElem X} `{TensorElem Y} :
  forall (e1 : X) (e2 : X -> list (list Y)),
    flatten (let_binding e1 e2) = let_binding e1 (fun x => flatten (e2 x)).
Proof. intros. unfold let_binding. reflexivity. Qed.

Theorem flatten_iverson {X} `{TensorElem X} :
  forall p (e : list (list X)) s n m,
    consistent e (n,(m,s)) ->
    flatten (|[ p ]| e) = |[ p ]| (flatten e).
Proof.
  intros. unfold flatten.
  rw^ @consistent_length.
  rw^ @consistent_length. symmetry.
  rw^ @consistent_length.
  rw^ @consistent_length.
  rw @gp_gen_iverson.
  rw^ @sum_iverson_lift.
  rw^ @sum_iverson_lift.
  rw collapse_iverson. symmetry.
  rw @gp_iverson.
  rw collapse_iverson.
  rw andb_comm.
  reflexivity.
Qed.
  
Theorem flatten_gen {X} `{TensorElem X} : forall n m s (f : Z -> list X),
    (forall x, consistent (f x) (m,s)) ->
    0 < m ->
    0 < n ->
    flatten (GEN [ i < Z.of_nat n ] f i) =
    GEN [ i < Z.of_nat (n * m) ]
        f (i / Z.of_nat m)%Z _[ i mod Z.of_nat m].
Proof.
  intros. unfold flatten.
  rw^ @consistent_length.
  rw^ @consistent_length.
  rw @get_gen_some.
  solve_for_index.
  rw @sum_bound_indic_no_f.
  rewrite <- Nat2Z.inj_mul.
  etransitivity.
  apply gen_eq_bound; intros.
  apply sum_eq_bound; intros.
  erewrite guard_comp_to_eq. reflexivity.
  auto. eassumption. auto. auto.
  rewrite nat_mul_div_id by auto.
  auto. lazy beta.
  rw @sum_bound_indic_no_f.  

  simpl_guard.
  rw expand_Zmod.
  etransitivity. apply gen_eq_bound; intros.
  assert ((i / Z.of_nat m <? Z.of_nat n)%Z = true).
  unbool.
  eapply Zmult_lt_reg_r with (p:= Z.of_nat m). auto with crunch.
  rewrite <- Nat2Z.inj_mul.
  pose proof (Z.mul_div_le i (Z.of_nat m)).
  peel_hyp. rewrite Z.mul_comm.
  auto with crunch.
  rewrite H5.
  rewrite true_iverson.
  reflexivity. lazy beta.
  reflexivity.
Qed.
  
Theorem flatten_sum {X} `{TensorElem X} :
  forall n (f : Z -> list (list X)) s m o,
    (forall x, consistent (f x) (m,(o,s))) ->
    0 < n ->
    0 < m ->
    0 < o ->
    flatten (SUM [ i < Z.of_nat n ] f i) =
    SUM [ y < Z.of_nat n ]
        GEN [ x < Z.of_nat (m * o) ]
        f y _[ x / Z.of_nat o; x mod Z.of_nat o].
Proof.
  intros.
  unfold flatten.
  rw^ @consistent_length.
  rw^ @consistent_length.
  solve_for_index.
  rw @sum_bound_indic_no_f.
  rewrite <- Nat2Z.inj_mul.
  etransitivity.
  apply gen_eq_bound; intros.
  apply sum_eq_bound; intros.
  erewrite guard_comp_to_eq. reflexivity. auto. eassumption. auto. auto.
  rewrite nat_mul_div_id. auto. auto. lazy beta.
  rw @sum_bound_indic_no_f.
  simpl_guard.
  rw<- @get_sum.
  rw<- @get_sum.
  etransitivity.
  apply gen_eq_bound; intros.
  assert ((i / Z.of_nat o <? Z.of_nat m)%Z = true).
  unbool.
  eapply Zmult_lt_reg_r with (p:= Z.of_nat o). auto with crunch.
  rewrite <- Nat2Z.inj_mul.
  pose proof (Z.mul_div_le i (Z.of_nat o)).
  peel_hyp. rewrite Z.mul_comm.
  auto with crunch.
  rewrite H6.
  rewrite true_iverson.
  rewrite expand_Zmod by auto with crunch.
  reflexivity. lazy beta.
  rw sum_gen_swap.
  reflexivity.
Qed.

Theorem flatten_gen_gen {X} `{TensorElem X} : forall n m f s,
    (forall x y, consistent (f x y) s) ->
    0 < n ->
    0 < m ->
    flatten (GEN [ i < Z.of_nat n ] GEN [ j < Z.of_nat m ] f i j) =
    GEN [ k < Z.of_nat n * Z.of_nat m ]
        f (k / Z.of_nat m)%Z (Zmod k (Z.of_nat m))%Z.
Proof.
  intros. unfold flatten.
  rewrite gen_of_nat_length.
  rw^ @consistent_length.
  rw @get_gen_some.
  rw @get_gen_some.
  solve_for_index.
  rewrite <- Nat2Z.inj_mul.
  rw @sum_bound_indic_no_f.
  etransitivity.
  apply gen_eq_bound; intros.
  apply sum_eq_bound; intros.
  erewrite guard_comp_to_eq. reflexivity.
  auto. eassumption. auto. auto.
  rewrite nat_mul_div_id. auto. auto.
  lazy beta.
  rw sum_bound_indic_no_f.
  rw expand_Zmod.
  simpl_guard.
  etransitivity.
  apply gen_eq_bound; intros.
  assert ((i / Z.of_nat m <? Z.of_nat n)%Z = true).
  unbool.
  eapply Zmult_lt_reg_r with (p:= Z.of_nat m). auto with crunch.
  rewrite <- Nat2Z.inj_mul.
  pose proof (Z.mul_div_le i (Z.of_nat m)).
  peel_hyp. rewrite Z.mul_comm.
  auto with crunch.
  rewrite H5.
  rewrite true_iverson.
  reflexivity. lazy beta.
  reflexivity.
Qed.


(* FLATTEN TRUNC TRANSFORMATIONS *)
Theorem get_flatten_trunc {X} `{TensorElem X} :
  forall n k i j m (v : list (list X)) s,
    consistent v (n,(m,s)) ->
    0 < k ->
    0 < n ->
    0 < m ->
    (0 <= i)%Z ->    
    (i < Z.of_nat n)%Z ->
    (0 <= j)%Z ->
    (j < Z.of_nat m)%Z ->
    (flatten_trunc k v) _[i * Z.of_nat m + j] =
|[ i * Z.of_nat m + j <? Z.of_nat k ]| v _[i;j].
Proof.
  intros.
  unfold flatten_trunc. inversion H0. inversion H10.
  destruct (i * Z.of_nat m + j <? Z.of_nat k)%Z eqn:e; unbool.
  - rw @get_gen_some.
    rewrite get_0_cons.
    subst.
    rw factor_unique.
    rw<- collapse_iverson.
    rw<- sum_iverson_lift.
    solve_for_index.
    rw sum_bound_indic_no_f.
    simpl_guard.
    rw @sum_bound_indic_no_f.
    simpl_guard. try simpl_guard. rewrite true_iverson.
    reflexivity.
  - rw get_gen_null.
    rewrite get_0_cons.
    unfold iverson at 1. symmetry.
    unfold iverson at 1. symmetry.
    eapply mul_0_absorb.
    consistent_shape; subst; eauto with crunch.
    consistent_shape; subst; eauto with crunch.
    auto.
Qed.

Theorem flatten_trunc_let {X Y} `{TensorElem X} `{TensorElem Y} :
  forall k (e1 : X) (e2 : X -> list (list Y)),
    flatten_trunc k (let_binding e1 e2) =
    let_binding e1 (fun x => flatten_trunc k (e2 x)).
Proof. intros. unfold let_binding. reflexivity. Qed.

Theorem flatten_trunc_iverson {X} `{TensorElem X} :
  forall p (e : list (list X)) s n m k,
    consistent e (n,(m,s)) ->
    flatten_trunc k (|[ p ]| e) = |[ p ]| (flatten_trunc k e).
Proof.
  intros. unfold flatten_trunc.
  rw^ @consistent_length.
  rw^ @consistent_length. symmetry.
  rw^ @consistent_length.
  rw^ @consistent_length.
  rw @gp_gen_iverson.
  rw^ @sum_iverson_lift.
  rw^ @sum_iverson_lift.
  rw collapse_iverson. symmetry.
  rw @gp_iverson.
  rw collapse_iverson.
  rw andb_comm.
  reflexivity.
Qed.

Theorem trunc_r_gen {X} `{TensorElem X} : forall n f k,
    k <= n ->
    trunc_r k (GEN [ i < Z.of_nat n ] f i) = GEN [ i < Z.of_nat k ] f i.
Proof.
  intros. unfold trunc_r.
  rw @get_gen_some.
  reflexivity.
Qed.

Theorem flatten_trunc_to_trunc {X} `{TensorElem X} :
  forall k (v : list (list X)) n m s,
    consistent v (n,(m,s)) ->
    (k <= n * m) ->
    flatten_trunc k v = trunc_r k (flatten v).
Proof.
  intros.
  unfold flatten_trunc, flatten, trunc_r.
  rw^ @consistent_length.
  rw^ @consistent_length. symmetry.
  rw^ @consistent_length.
  rw^ @consistent_length.
  rw @get_gen_some.
  reflexivity.
Qed.

Theorem flatten_trunc_gen {X} `{TensorElem X} :
  forall n m s (f : Z -> list X) k,
    (forall x, consistent (f x) (m,s)) ->
    0 < m ->
    0 < n ->
    k <= n * m ->
    flatten_trunc k (GEN [ i < Z.of_nat n ] f i) =
    GEN [ i < Z.of_nat k ]
        f (i / Z.of_nat m)%Z _[ i mod Z.of_nat m].
Proof.
  intros. erewrite flatten_trunc_to_trunc; consistent_shape; eauto.
  erewrite flatten_gen; try intros; consistent_shape; eauto.
  rewrite trunc_r_gen by auto.
  reflexivity.
Qed.
  
Theorem flatten_trunc_sum {X} `{TensorElem X} :
  forall n (f : Z -> list (list X)) s m o k,
    (forall x, consistent (f x) (m,(o,s))) ->
    0 < n ->
    0 < m ->
    0 < o ->
    k <= m * o ->
    flatten_trunc k (SUM [ i < Z.of_nat n ] f i) =
    SUM [ y < Z.of_nat n ]
        GEN [ x < Z.of_nat k ]
        f y _[ x / Z.of_nat o; x mod Z.of_nat o].
Proof.
  intros. erewrite flatten_trunc_to_trunc; consistent_shape; eauto with crunch.
  erewrite flatten_sum; try intros; consistent_shape; eauto.
  rw<- sum_gen_swap.
  rewrite trunc_r_gen by auto with crunch.
  rw sum_gen_swap.
  reflexivity.
Qed.

Theorem flatten_trunc_gen_gen {X} `{TensorElem X} : forall n m f s k,
    (forall x y, consistent (f x y) s) ->
    0 < n ->
    0 < m ->
    k <= n * m ->
    flatten_trunc k (GEN [ i < Z.of_nat n ] GEN [ j < Z.of_nat m ] f i j) =
    GEN [ k < Z.of_nat k ]
        f (k / Z.of_nat m)%Z (Zmod k (Z.of_nat m))%Z.
Proof.
  intros. erewrite flatten_trunc_to_trunc; consistent_shape; eauto with crunch.
  erewrite flatten_gen_gen; try intros; consistent_shape; eauto.
  rewrite <- Nat2Z.inj_mul.
  rewrite trunc_r_gen by auto.
  reflexivity.
Qed.

Theorem flatten_trunc_gen_let {X Y} `{TensorElem X} `{TensorElem Y} :
  forall k (e1 : Z -> X) (e2 : Z -> X -> list Y) n m s,
    (forall a b, consistent (e2 a b) (m,s)) ->
    0 < m ->
    0 < n ->
    k <= n * m ->
    flatten_trunc k
    (GEN [ i < Z.of_nat n ] 
         let_binding (e1 i) (e2 i)) =
    GEN [ i < Z.of_nat k ]
        (tlet x := e1 (i / Z.of_nat m)%Z in
             e2 (i / Z.of_nat m)%Z x _[ i mod Z.of_nat m]).
Proof.
  intros.
  erewrite flatten_trunc_gen;
    try intros; consistent_shape; subst; eauto with crunch typeclass_instances.
  rw @ll_get.
  reflexivity.
Qed.

Theorem flatten_trunc_gen_transpose {X} `{TensorElem X} :
  forall n k (f : Z -> (list (list X))) a s,
    (forall x, consistent (f x) (a,(k,s))) ->
    0 < n ->
    0 < a ->
    0 < k ->
    flatten_trunc n
     (GEN [ i < Z.of_nat (n //n k) ]
          transpose (f i)) =
    GEN [ i < Z.of_nat n ]
        transpose (f (i / Z.of_nat k)%Z) _[ i mod Z.of_nat k].
Proof.
  intros.
  erewrite flatten_trunc_gen; try intros; consistent_shape; eauto with crunch.
Qed.

Lemma guard_null {X} `{TensorElem X} : forall p, (|[ p ]| null) = null.
Proof.
  intros. destruct p. apply true_iverson. unfold iverson. apply mul_0_null.
Qed.

(* CONCAT *)
Theorem split_gen {X} `{TensorElem X} :
  forall N I body s,
    (0 <= I)%Z ->
    (I <= N)%Z ->
    (forall x, consistent (body x) s) ->
    GEN [ i < N ] body i =
    (GEN [ i < I ] body i) <++> (GEN [ I <= i < N ] body i).
Proof.
  intros.
  symmetry.
  unfold fuse.
  rewrite gen_length.
  rewrite genr_length.
  rewrite Z2Nat.inj_sub by lia.
  rewrite Nat2Z.inj_add.
  rewrite Z2Nat.id by lia.
  rewrite Nat2Z.inj_sub by (zify; lia).
  rewrite Z2Nat.id by lia.
  rewrite Z2Nat.id by lia.
  rewrite Zplus_minus.
  apply gen_eq_bound; intros.
  destruct (0 <? I)%Z eqn:e; unbool;
    destruct (I <? N)%Z eqn:ee; unbool.
  - etransitivity.
    apply bin_eq_l.
    eapply iverson_in; intros; unbool.
    rw @get_gen_some. reflexivity.
    split; consistent_shape; eauto.
    etransitivity.
    apply bin_eq_r.
    eapply iverson_in; intros; unbool.
    rewrite get_genr_some.
    rw Zplus_minus.
    reflexivity. lia. lia. auto with crunch.
    split; consistent_shape; eauto.
    apply guard_split.
  - unfold genr.
    destruct (N-I)%Z eqn:eee. simpl.
    unfold get at 2.
    rewrite guard_null.
    rewrite bin_null_id_r.
    replace ((i<?I)%Z) with true by (symmetry; unbool; lia).
    rewrite true_iverson.
    rw get_gen_some.
    reflexivity.
    zify. lia.
    simpl.
    unfold get at 2.
    rewrite guard_null.
    rewrite bin_null_id_r.
    replace ((i<?I)%Z) with true by (symmetry; unbool; lia).
    rewrite true_iverson.
    rw get_gen_some.
    reflexivity.
  - assert (I = 0)%Z by lia.
    rewrite H5.
    replace (i <? 0)%Z with false by (symmetry; unbool; lia).
    replace (0 <=? i)%Z with true by (symmetry; unbool; lia).
    rewrite true_iverson.
    rewrite Z.sub_0_r.
    unfold gen.
    unfold genr at 1.
    simpl.
    unfold get at 1.
    rewrite guard_null.
    rewrite bin_null_id_l.
    rewrite get_genr_some; try lia;
    rewrite Z.add_0_l. reflexivity;
    rewrite Z.sub_0_r; auto with crunch.
  - lia.
Qed.

Lemma gen_helper_offset {X} `{TensorElem X} :
  forall N body K,
      gen_helper N 0 (fun i : Z => body (K + i)%Z) =
      gen_helper N K body.
Proof.
  induction N; intros.
  - reflexivity.
  - simpl. rewrite Z.add_0_r.
    f_equal.
    rewrite <- (IHN _ K).
    apply gen_helper_eq_bound; intros.
    f_equal. lia.
Qed.

Theorem split_genr {X} `{TensorElem X} :
  forall N I body K s,
    (K <= I)%Z ->
    (I <= N)%Z ->
    (forall x, consistent (body x) s) ->
    GEN [ K <= i < N ] body i =
    (GEN [ K <= i < I ] body i) <++> (GEN [ I <= i < N ] body i).
Proof.
  intros.
  symmetry.
  unfold fuse.
  rewrite genr_length.
  rewrite genr_length.
  rewrite Z2Nat.id by lia.
  rewrite Nat2Z.inj_add.
  rewrite Z2Nat.id by lia.
  rewrite Z2Nat.id by lia.
  replace (I - K + (N-I))%Z with (N - K)%Z by lia.
  etransitivity.
  apply gen_eq_bound; intros.
  destruct (K<?I)%Z eqn:e; 
    destruct (I<?N)%Z eqn:ee; unbool.
  - etransitivity.
    apply bin_eq_l.
    eapply iverson_in; intros; unbool.
    rw @get_genr_some.
    reflexivity.
    split; consistent_shape; eauto.
    etransitivity.
    apply bin_eq_r.
    eapply iverson_in; intros; unbool.
    rewrite get_genr_some.
    replace (I + (i-(I-K)))%Z with (K+i)%Z by lia.
    reflexivity. lia. lia.
    auto with crunch.
    split; consistent_shape; eauto.
    apply guard_split.
  - lazy beta.
    assert (I=N)%Z by lia. rewrite H5.
    unfold genr at 2.
    rewrite Z.sub_diag.
    simpl. unfold get at 2.
    rewrite guard_null.
    rewrite bin_null_id_r.
    rw @get_genr_some.
    simpl_guard.
    reflexivity.
  - lazy beta.
    assert (K=I)%Z by lia. rewrite H5.
    unfold genr at 1.
    rewrite Z.sub_diag.
    simpl. unfold get at 1.
    rewrite guard_null.
    rewrite bin_null_id_l.
    rewrite Z.sub_0_r.
    simpl_guard.
    rw @get_genr_some.
    reflexivity.
  - lia.
  - lazy beta.
    unfold gen,genr.
    rewrite Z.sub_0_r.
    apply gen_helper_offset.
Qed.

Theorem split_gen_plus {X} `{TensorElem X} :
  forall N M body s,
    (0 <= N)%Z ->
    (0 <= M)%Z ->
    (forall x, consistent (body x) s) ->
    GEN [ i < N+M ] body i =
    (GEN [ i < N ] body i) <++> (GEN [ N <= i < N+M ] body i).
Proof.
  intros.
  eapply split_gen.
  lia. lia. eauto.
Qed.

Lemma distrib_gen_concat {X} `{TensorElem X} :
  forall m n (f g : Z -> list X) a b s,
    (forall x, consistent (f x) (a,s)) ->
    (forall x, consistent (g x) (b,s)) ->
    (0 < n - m)%Z ->
    (0 < a) ->
    (0 < b) -> 
    transpose (GEN [ m <= i < n ]
        (f i) <++> (g i)) =
        (transpose (GEN [ m <= i < n ] f i))
          <++> (transpose (GEN [ m <= i < n ] g i)).
Proof.
  intros.
  unfold fuse.
  etransitivity.
  apply transpose_eq.
  apply genr_eq_bound; intros.
  erewrite consistent_length; eauto.
  erewrite consistent_length; eauto.
  reflexivity.
  symmetry.
  rw^ @consistent_length.
  rw^ @consistent_length.
  unfold transpose.
  rw^ @consistent_length.
  rw^ @consistent_length.
  rw^ @consistent_length.
  rw^ @consistent_length.
  symmetry.
  rw^ @consistent_length.
  rw^ @consistent_length.
  rewrite Z2Nat.id by lia.
  rw @get_genr_some.
  rw @get_gen_some.
  symmetry.
  apply gen_eq_bound; intros.
  etransitivity.
  apply bin_eq_l.
  eapply iverson_in; intros; unbool.
  rw @get_gen_some.
  rw @get_genr_some.
  reflexivity.
  split; consistent_shape; eauto with crunch.
  etransitivity.
  apply bin_eq_r.
  eapply iverson_in; intros; unbool.
  rw @get_gen_some.
  rw @get_genr_some.
  reflexivity.
  split; consistent_shape; eauto with crunch.
  
Admitted.
