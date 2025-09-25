From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Zdiv.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Classes.Morphisms.

From ATL Require Import Tactics FrapWithoutSets.

Open Scope Z_scope.

Definition div_ceil (n d : Z) : Z := (n + d - 1) / d.
  
Notation "a // b" := (div_ceil a b) (at level 10, left associativity).

Theorem zero_div : forall n, 0 < n -> 0 // n = 0.
Proof.
  intros.
  apply Zdiv_small.
  lia.
Qed.

Theorem div_zero : forall n, n // 0 = 0.
Proof.  intros. unfold div_ceil. apply Zdiv_0_r. Qed.

Definition div_ceil_n (n d : nat) : nat := ((n + d - 1) / d)%nat.

Notation "a //n b" := (div_ceil_n a b) (at level 10, left associativity).
Arguments div_ceil_n : simpl never.

Theorem of_nat_div_distr : forall n c,
    (Z.of_nat n) // (Z.of_nat c) = Z.of_nat ( n //n c).
Proof.
  intros.
  destruct c.
  - rewrite div_zero. reflexivity.
  - unfold div_ceil, div_ceil_n.
    rewrite <- Nat2Z.inj_add.
    replace 1 with (Z.of_nat (S O)) by reflexivity.
    rewrite <- Nat2Z.inj_sub by lia.
    rewrite <- Nat2Z.inj_div by lia.
    reflexivity.
Qed.

Theorem znat_id_distr : forall n c,
    (Z.to_nat (Z.of_nat n // (Z.of_nat c))) =
    (Z.to_nat (Z.of_nat n)) //n (Z.to_nat (Z.of_nat c)).
Proof.
  intros.
  rewrite of_nat_div_distr.
  repeat rewrite Nat2Z.id.
  reflexivity.
Qed.
      
Theorem mul_add_lt : forall i j n m,
    0 <= i ->
    i < n ->
    0 <= j ->
    j < m ->
    i * m + j < n * m.
Proof.
  intros.
  assert (i*m <= (n-1) * m).
  {
    apply Z.mul_le_mono_nonneg_r. lia. lia.
  }
  assert ((n-1)*m + j < (n-1)*m + m).
  {
    apply Zplus_lt_compat_l. auto.
  }
  assert (i*m + j <= (n-1)*m + j).
  {
    apply Zplus_le_compat_r. auto.
  }
  eapply Z.le_lt_trans.
  apply H5.
  rewrite Zmult_succ_l_reverse in H4.
  assert (Z.succ (n-1) = n). lia.
  rewrite H6 in H4. auto.
Qed.

Close Scope Z_scope.

Theorem nat_mul_div_id : forall n m,
    0 < m ->
    (n * m) //n m = n.
Proof.
  intros.
  unfold div_ceil_n.
  rewrite <- add_sub_assoc by lia.
  rewrite div_add_l by lia.
  rewrite div_small. lia. lia.
Qed.

Theorem ndiv_pos : forall n m,
    0 < n ->
    0 < m ->
    0 < n //n m .
Proof.
  intros.
  unfold "_ //n _".
  destruct n. lia.
  simpl.
  rewrite sub_0_r.
  apply div_str_pos.
  lia.
Qed.
Hint Extern 1 (0 < _ //n _) => apply ndiv_pos : crunch.

Theorem div_pos : forall n m,
    (0 < n)%Z ->
    (0 < m)%Z ->
    (0 < n // m)%Z.
Proof.
  intros. unfold div_ceil.
  apply Z.div_str_pos. lia.
Qed.
Hint Extern 1 ((0 < _ // _)%Z) => apply div_pos : crunch.

Theorem div_nonneg : forall n m,
    (0 <= n)%Z ->
    (0 < m)%Z ->
    (0 <= n // m)%Z.
Proof.
  intros. unfold div_ceil.
  apply Z.div_pos; lia.
Qed.
Hint Extern 1 ((0 <= _ // _)%Z) => apply div_nonneg : crunch.

Lemma of_nat_nonneg : forall x,
    (0 <= Z.of_nat x)%Z.
Proof. intros. lia. Qed.
Hint Extern 1 ((0 <= _)%Z) => apply of_nat_nonneg : crunch.

Lemma znat_lt : forall x n,
    (0 <= x)%Z ->
    (x < Z.of_nat n)%Z ->
    Z.to_nat x < n.
Proof. intros. lia. Qed.                   

Hint Extern 5 (Z.to_nat _ < _) => apply znat_lt : crunch.

Lemma pos_nat_succ : forall p, exists n, Pos.to_nat p = S n.
Proof.
  intros p.
  specialize (Pos2Nat.is_pos p); intros.
  destruct (Pos.to_nat p); try lia; eauto.
Qed.

Ltac posnat :=
  match goal with
  | [ |- context[Pos.to_nat ?p] ] => specialize (pos_nat_succ p);
                                     intros [pn Hpos]; rewrite Hpos
  end.

Lemma znat_0lt : forall x, (0 < x)%Z -> 0 < (Z.to_nat x).
Proof. intros. lia.
Qed.

Hint Resolve znat_0lt : crunch.

Lemma natz_0lt : forall x, 0 < x -> (0 < (Z.of_nat x))%Z.
Proof. intros. lia. Qed.

Hint Resolve natz_0lt : crunch.

Lemma weaker_Z2Nat_injlt : forall i j,
    Z.to_nat i < Z.to_nat j ->
    (0 <= i)%Z ->
    (i < j)%Z.
Proof.
  intros. destruct j eqn:e.
  - simpl in *. lia.
  - rewrite <- e in *.
    apply Z2Nat.inj_lt in H; auto.
    subst.
    apply Zle_0_pos.
  - simpl in *. lia.
Qed.

Lemma factor_unique : forall i i0 i1 i2 m,
    (0 <= i0 < m)%Z ->
    (0 <= i2 < m)%Z ->    
    ((i * m + i0 =? i1 * m + i2)%Z =
     (i=?i1)%Z && (i0=?i2)%Z).
Proof.
  intros.
  unbool.  
  split; intros.  
  - eapply Z.div_mod_unique.
    left.
    eauto.
    left.
    lia.
    rewrite Z.mul_comm. rewrite H1. rewrite Z.mul_comm. reflexivity.
  - destruct H1. subst. reflexivity.
Qed.  

Lemma div_eucl_div : forall a b,
    (b > 0)%Z ->
    let (q,_) := Z.div_eucl a b in
    q = (a / b)%Z.
Proof.
  intros.
  pose (Z_div_mod a b). peel_hyp.
  destruct (Z.div_eucl a b) eqn:e. destruct y.
  subst.
  rewrite Z.add_comm.
  rewrite Z.mul_comm.
  rewrite Z_div_plus by auto.
  rewrite Zdiv_small; auto.
Qed.  

Lemma mul_lt : forall z k x,
  (0 <= z < k)%Z ->
  ((z < k * x)%Z <-> (0 < x)%Z).
Proof.
  intros.
  split; intros.
  - destruct x. lia. zlia. 
    assert (0 < k * Z.neg p)%Z by lia.
    assert (0 < k)%Z by lia.
    apply Z.lt_0_mul in H1.
    lia.
  - destruct x; try lia.
    assert (1 <= Z.pos p )%Z by lia.
    replace z with (z * 1)%Z by lia.
    destruct (1 =? Z.pos p)%Z eqn:ee; unbool.
    * rewrite <- ee.
      lia.
    * assert (1 < Z.pos p)%Z by lia.
      apply Z.mul_lt_mono_nonneg; try lia.
Qed.

Lemma mul_le : forall z k x,
    (0 <= z < k)%Z ->
    (k * x <= z <-> x <= 0)%Z.
Proof.
  intros.
  split; intros.
  - destruct x; try lia.
    assert (k < k * Z.pos p)%Z.
    assert (1 <= Z.pos p )%Z by lia.
    destruct (1 =? Z.pos p)%Z eqn:ee; unbool.
    + rewrite <- ee in *. rewrite Z.mul_1_r in *. lia.
    + assert (1 < Z.pos p)%Z by lia.
      replace k with (k * 1)%Z at 1 by lia.
      apply Zmult_lt_compat_l; lia.
    + lia.
  - destruct (x =? 0)%Z eqn:ee; unbool.
    + subst. rewrite Z.mul_0_r. lia.
    + assert (x < 0)%Z by lia.
      assert (k * x < 0)%Z.
      apply Z.mul_pos_neg; lia.
      lia.
Qed.

Lemma floor_lt_ceil : forall x y,
    (0 <= x)%Z ->
    (0 < y)%Z ->
    (x / y <= x // y)%Z.
Proof.
  intros.
  unfold div_ceil.
  apply Z_div_le. lia. lia.
Qed.

Lemma div_eq_num_diff : forall a b c,
    (0 <= a)%Z ->
    (0 <= b)%Z ->
    (0 < c)%Z ->
    (a / c = b / c)%Z ->
    (a < b)%Z ->
    (b - a < c)%Z.
Proof.
  intros.
  pose (Z_div_mod a c). peel_hyp.
  pose (Z_div_mod b c). peel_hyp.
  destruct (Z.div_eucl a c).
  destruct (Z.div_eucl b c).
  destruct y. destruct y0. subst.
  rewrite Z.sub_add_distr.
  repeat rewrite (Z.mul_comm c) in H2.
  repeat rewrite Z.div_add_l in H2 by lia.
  repeat rewrite Z.div_small in H2 by lia.
  repeat rewrite Z.add_0_r in H2.
  subst. lia.
Qed.

Lemma floor_lt_ceil_mono_l : forall i k n,
    (0 <= i)%Z ->
    (i < n)%Z ->
    (0 < k)%Z ->
    (0 < n)%Z ->
    (i / k < n // k)%Z.
Proof.
  intros. unfold div_ceil.
  pose proof (Z.div_le_mono i (n+k-1)%Z k). peel_hyp; try lia.
  destruct (i / k =? (n + k - 1) / k)%Z eqn:e; unbool.
  - rewrite <- e in *. clear H3.
    apply div_eq_num_diff in e; try lia.
  - lia.
Qed.
Hint Resolve floor_lt_ceil_mono_l : crunch.

Lemma floor_lt_nat_ceil_mono_l : forall i k n,
    (0 <= i)%Z ->
    (i < Z.of_nat n)%Z ->
    0 < k ->
    0 < n ->
    (i / Z.of_nat k < Z.of_nat (n //n k))%Z.
Proof.
  intros.
  rewrite <- of_nat_div_distr.
  apply floor_lt_ceil_mono_l; auto with crunch.
Qed.
Hint Resolve floor_lt_nat_ceil_mono_l : crunch.

Theorem pos_zofnat : forall n,
    0 < n ->
    (0 < Z.of_nat n)%Z.
Proof. intros. lia. Qed.
Hint Resolve pos_zofnat : crunch.
Hint Resolve Z.div_pos : crunch.

Lemma expand_Zmod : forall i m,
    (0 < m)%Z ->
    (i - i / m * m = Coq.ZArith.BinIntDef.Z.modulo i m)%Z.
Proof.
  intros. unfold Coq.ZArith.BinIntDef.Z.modulo.
  pose proof (Z_div_mod i m).
  assert (m > 0)%Z by lia.
  apply H0 in H1.
  destruct (Z.div_eucl i m) eqn:e.
  destruct H1.
  rewrite H1.
  rewrite Z.mul_comm.
  rewrite Z_div_plus_full_l by lia.
  rewrite Zdiv_small by lia.
  rewrite Z.add_0_r. lia.
Qed.

Lemma Zplus_assoc : forall p m n, (n + (m + p))%Z = (n + m + p)%Z.
Proof. intros. lia. Qed.

Lemma div_ceil_n_lower_bound : forall n k,
    0 < k ->
    n <= n //n k * k.
Proof.
  intros n k Hk_pos.
  unfold div_ceil_n.
  assert (k <> 0) as Hk_nzero by lia.
  pose proof (div_mod (n + k - 1) k Hk_nzero).
  assert ((n + k - 1) mod k < k) by (apply mod_upper_bound; apply Hk_nzero).
  assert (n <= k * ((n + k - 1) / k)) by lia.
  rewrite mul_comm. assumption.
Qed.

Hint Resolve div_ceil_n_lower_bound : crunch.

Lemma mod_upper_bound : forall k i,
    (0 < k)%Z ->
    (i mod k < k)%Z.
Proof.
  intros.
  pose proof (Z.mod_pos_bound i k).
  peel_hyp. lia.
Qed.

Lemma mod_nonneg : forall k i,
    (0 < k)%Z ->
    (0 <= i mod k)%Z.
Proof.
  intros.
  pose proof (Z.mod_pos_bound i k).
  peel_hyp. lia.
Qed.  

Hint Resolve mod_upper_bound mod_nonneg : crunch.

Theorem div_mod_eq : forall i k,
    (0 < k)%Z ->
    (i / k * k + i mod k = i)%Z.
Proof.
  intros.
  rewrite <- expand_Zmod by lia.
  rewrite Zplus_minus.
  reflexivity.
Qed.

Lemma gt_add_r : forall k a b,
    (0 <= a)%Z ->
    (k <= b)%Z ->
    (k <= a + b)%Z.
Proof. intros. lia. Qed.

Hint Resolve Z.max_lub Z.min_glb Z.le_max_l Z.le_min_r Z.le_min_l : crunch.

Lemma ceil_div_pos : forall (m k : Z),
    (0 < m)%Z ->
    (0 < k)%Z ->
    (0 < m // k)%Z.
Proof.
  intros.
  unfold div_ceil.
  assert (m + k - 1 >= k)%Z by lia.
  apply Z.div_str_pos.
  split; lia.
Qed.

Lemma ceil_div_nonneg : forall (m k : Z),
    (0 <= m)%Z ->
    (0 < k)%Z ->
    (0 <= m // k)%Z.
Proof.
  intros.
  assert (m = 0 \/ 0 < m)%Z as [ Hm_zero | Hm_pos ] by lia.
  {
    rewrite Hm_zero in *.
    rewrite zero_div by assumption.
    lia.
  }
  {
    pose proof (ceil_div_pos m k Hm_pos H0).
    lia.
  }
Qed.

Lemma ceil_div_mod_pos : forall (m k : Z),
    (0 < m)%Z ->
    (0 < k)%Z ->
    (0 < (m mod k) // k)%Z \/ (0 < m /k)%Z.
Proof.
  intros m k H H0.
  assert (0 <= m)%Z as H' by lia.
  pose proof (Z.mod_bound_pos m k H' H0) as [Hlb Hub].
  assert ((m mod k = 0)%Z \/ (0 < m mod k)%Z) as [Heq | Hgt]by lia.
  {
    assert (k <> 0)%Z as Hk_nzero by lia.
    pose proof (Znumtheory.Zmod_divide m k Hk_nzero Heq).
    right.
    assert (k = 1 \/ 1 < k)%Z as [Hk_eq1 | Hk_gt1] by lia.
    {
      rewrite Hk_eq1 in *.
      rewrite Z.div_1_r.
      assumption.
    }
    {
      pose proof (Znumtheory.Zdivide_Zdiv_lt_pos k m Hk_gt1 H H1) as [H_goal _].
      apply H_goal.
    }
  }
  {
    left.
    apply ceil_div_pos; assumption.
  }
Qed.

Lemma split_floor_rest_nonneg : forall m k,
    (0 < m)%Z ->
    (0 < k)%Z ->
    (0 < m / k + (m mod k) // k)%Z.
Proof.
  intros.
  assert (0 <= m / k)%Z as Hdiv_nneg.
  {
    apply Z.div_pos; lia.
  }
  assert (0 <= (m mod k) // k)%Z as Hdiv_mod_nneg.
  {
    apply ceil_div_nonneg.
    { apply mod_nonneg; assumption. }
    { assumption. }
  }
  pose proof (ceil_div_mod_pos m k H H0) as [ Hdiv_mod_pos | H_div_pos ];
  lia.
Qed.

Lemma floor_div_mono_helper : forall (n k : Z),
  (0 < k)%Z -> (n < k * (n / k) + k)%Z.
Proof.
  intros n k Hk_pos.
  assert (k <> 0)%Z as Hk_nzero by lia.
  pose proof (Z.div_mod n k Hk_nzero).
  pose proof (mod_upper_bound k n Hk_pos).
  lia.
Qed.

Lemma floor_div_mono_strict : forall (n m k : Z),
    (0 < k)%Z ->
    (n / k < m / k)%Z ->
    (n < m)%Z.
Proof.
  intros.
  assert (k * (n / k) < k * (m / k))%Z as H_mul_lt.
  { apply Z.mul_lt_mono_pos_l; assumption. }
  pose proof (floor_div_mono_helper n k H).
  pose proof (Z.mul_div_le m k H).
  assert ((n / k) + 1 <= (m / k))%Z by lia.
  assert (k * ((n / k) + 1) <= k * ((m / k)))%Z.
  { apply Z.mul_le_mono_nonneg_l; lia. }
  assert (k * (n / k) + k <= m)%Z.
  { rewrite Z.mul_add_distr_l in H4. lia. }
  lia.
Qed.


Lemma floor_div_mono_upper : forall (n m k : Z),
  (0 < k)%Z ->
  (m < n / k)%Z ->
  (m * k <= n - k)%Z.
Proof.
  intros.
  assert (m * k / k <= (n - k) / k)%Z as H_div_bound.
  {
    rewrite Z.div_mul by lia.
    replace (n - k)%Z with (n + -1 * k)%Z by lia.
    rewrite Z.div_add; lia.
  }
  assert (m * k / k = (n - k) / k \/ m * k / k < (n - k) / k)%Z as [ H_div_eq | H_div_lt ] by lia.
  {
    rewrite Z.div_mul in H_div_eq by lia.
    rewrite H_div_eq in *.
    rewrite Z.mul_comm.
    apply Z.mul_div_le.
    assumption.
  }
  {
    pose proof (floor_div_mono_strict (m * k) (n - k) k H H_div_lt).
    lia.
  }
Qed.

Lemma floor_div_mul_lt : forall n k i0 i1,
    (0 < k)%Z ->
    (0 <= i0)%Z ->
    (i0 < n / k)%Z ->
    (0 <= i1)%Z ->
    (i1 < k)%Z ->
    (i0 * k + i1 < n)%Z.
Proof.
  intros.
  assert (i0 * k <= n - k)%Z.
  { apply floor_div_mono_upper; assumption. }
  { lia. }
Qed.

Hint Resolve floor_div_mul_lt split_floor_rest_nonneg Z.div_pos  : crunch.

Lemma Z_div_mod_eq : forall (n k : Z),
    (k <> 0)%Z ->
    (k * (n / k) = n - (n mod k))%Z.
Proof.
  intros n k Hk_nzero.
  pose proof (Z.div_mod n k Hk_nzero).
  lia.
Qed.

Lemma ceil_floor_mod : forall n k,
    (0 <= n)%Z ->
    (0 < k)%Z ->
    (n//k = n/k + ((n mod k) // k))%Z.
Proof.
  intros n k Hn_nneg Hk_pos.
  unfold div_ceil.
  apply Z.mul_cancel_l with (p := k).
  { lia. }
  rewrite Z.mul_add_distr_l.
  assert (k <> 0)%Z as Hk_nzero by lia.
  repeat rewrite Z_div_mod_eq by assumption.
  replace (n - n mod k + (n mod k + k - 1 - (n mod k + k - 1) mod k))%Z
    with (n + k - 1 - (n mod k + k - 1) mod k)%Z by lia.
  assert ((n + k - 1) mod k = (n mod k + k - 1) mod k)%Z.
  2: lia.
  replace (n + k - 1)%Z with (n + (k - 1))%Z by lia.
  replace (n mod k + k - 1)%Z with (n mod k + (k - 1))%Z by lia.
  rewrite Z.add_mod by assumption.
  symmetry.
  rewrite Z.add_mod by assumption.
  rewrite Z.mod_mod by assumption.
  lia.
Qed.

Lemma div_eucl_bound : forall x y z k,
    (0 <= x)%Z ->
    (0 <= y < k)%Z ->
    (k * x + y < k * z)%Z ->
    (x < z)%Z.
Proof.
  propositional.
  assert (x = z \/ x < z \/ z < x)%Z by lia.
  propositional.
  + subst. lia.
  + assert (x = (z + (x -z)))%Z by lia.
    rewrite H4 in H1.
    rewrite Z.mul_add_distr_l in H1.
    assert (k * (x-z) + y < 0)%Z by lia. clear H1. clear H4.
    assert (0 <= x -z)%Z by lia.
    assert (0 <=k)%Z by lia.
    pose proof (Z.mul_nonneg_nonneg _ _ H4 H1).
    pose proof (Z.add_nonneg_nonneg _ _ H6 H2). lia.
Qed.

Lemma div_eucl_pos : forall a b z,
    (0 < a)%Z ->
    (0 <= b < a)%Z ->
    (0 <= a * z + b)%Z ->
    (0 <= z)%Z.
Proof.
  propositional.
  assert (z < 0 \/ 0 <= z)%Z by lia.
  propositional.
  assert (a = b + (a -b))%Z by lia.
  rewrite H0 in H1.
  rewrite Z.mul_add_distr_r in H1.
  assert (0 <= b * (z+1) + (a-b) *z)%Z by lia. clear H1.
  assert ( 0 < a - b )%Z. lia.
  eapply Z.mul_pos_neg in H1. 2: apply H4.
  clear H0.
  assert (z+1 <= 0)%Z. lia.
  eapply Z.mul_nonneg_nonpos in H2. 2: eapply H0. clear H0.
  lia.
Qed.

Lemma div_ceil_n_0 : forall l,
    0 < l ->
    0 //n l = 0.
Proof.
  unfold div_ceil_n. intros. rewrite div_small by lia. reflexivity.
Qed.

Lemma sub_sub_distr : forall a b c,
    c <= b ->
    b <= a ->
    a - (b - c) = a - b + c.
Proof. intros. lia. Qed.

Lemma div_mul_upper_bound : forall n k,
    0 < k ->
    n / k * k <= n.
Proof.
  intros. unfold div. cases k. lia.
  pose proof (divmod_spec n k 0 k). cases (divmod n k 0 k).
  assert (k<=k) by lia. propositional. simpl in *. invert H0.
  rewrite mul_0_r in *. rewrite add_0_r in *. rewrite sub_diag in *.
  rewrite add_0_r in *. subst. lia.
Qed.

Lemma mod_id : forall x k,
    0 < k ->
    x mod k <> 0 ->
    x mod k + (k - x mod k) mod k= k.
Proof.
  intros.
  unfold modulo in *. cases k. lia.
  assert (k<=k) by lia.
  pose proof (divmod_spec x k 0 k).
  cases (divmod x k 0 k). propositional. remember sub. simpl in *. subst.
  rewrite mul_0_r in *. rewrite sub_diag in *. repeat rewrite add_0_r in *.
  subst.
  assert (n0 <k) by lia. clear H4.
  replace (Datatypes.S k - (k - n0)) with (Datatypes.S n0) by lia.
  pose proof (divmod_spec (Datatypes.S n0) k 0 k).
  cases (divmod (Datatypes.S n0) k 0 k). propositional.
  rewrite mul_0_r in *. rewrite sub_diag in *. repeat rewrite add_0_r in *.
  simpl.
  assert (k-n2 = Datatypes.S n0 - Datatypes.S k * n1). lia.
  rewrite H4. 
  cases n1.
  + rewrite mul_0_r. rewrite sub_0_r.
    rewrite <- add_sub_swap by lia.
    rewrite <- add_sub_assoc by lia. lia.
  + rewrite mul_comm in H4. simpl in H4. rewrite sub_add_distr in H4.
    replace (n0 - k) with 0 in H4 by lia. rewrite sub_0_l in *.
    replace n2 with k in * by lia. rewrite sub_diag in *.
    rewrite add_0_r in *.
    lia.
Qed.    

Lemma add_mod_div_bound : forall a b k,
    0 < k ->
    (a mod k + b mod k) / k <= 1.
Proof.
  intros. pose proof (Nat.mod_upper_bound a k).
  pose proof (Nat.mod_upper_bound b k).
  assert (a mod k + b mod k < 2 * k) by lia.
  eapply le_trans with (m:=(k+k-1)/k).
  eapply Div0.div_le_mono. lia. 
  rewrite <- add_sub_assoc by lia.
  replace k with (1*k) at 1  by lia.
  rewrite div_add_l by lia. rewrite div_small by lia. lia.
Qed.  

Lemma mod_0_iff_ceil_eq_floor_0 : forall n m,
    0 < m ->
    n mod m = 0 <->
    n //n m = n / m.
Proof.
  unfold div_ceil_n. propositional.
  - cases m. simpl in *. lia.
    eapply Div0.mod_divides in H0; try lia. invert H0.
    rewrite <- add_sub_assoc by lia.
    rewrite Nat.mul_comm. rewrite div_add_l by lia.
    rewrite div_mul by lia.
    rewrite div_small by lia. lia.
  - erewrite (Nat.div_mod_eq n m) in *.
    rewrite mul_comm in H0. rewrite div_add_l in H0 by lia.
    rewrite (div_small (n mod m)) in H0.
    2: { eapply Nat.mod_upper_bound. lia. }
    rewrite add_0_r in *.
    rewrite <- add_sub_assoc in H0 by lia.
    rewrite <- add_assoc in H0.
    rewrite div_add_l in H0 by lia.
    rewrite <- H0.
    rewrite Div0.add_mod_idemp_r by lia.
    cases (n mod m).
    + simpl in *. rewrite (div_small (m-1)) by lia. rewrite add_0_r.
      pose proof Heq. eapply Div0.div_exact in H1. 
      rewrite <- H1.
      replace (n+n) with (2*n) by lia.
      rewrite <- Div0.mul_mod_idemp_r by lia. rewrite Heq. simpl.
      rewrite Div0.mod_0_l by lia. reflexivity.
    + rewrite add_succ_comm in H0.
      rewrite <- sub_succ_l in H0 by lia. simpl in H0. rewrite sub_0_r in H0.
      replace m with (1*m) in H0 at 2 by lia.
      rewrite (Nat.add_comm n0) in H0. rewrite div_add_l in H0 by lia.
      simpl. lia.
Qed.

Lemma mod_0_iff_ceil_sub_floor_0 : forall n m,
    0 < m ->
    n mod m = 0 <->
    n //n m - n / m = 0.
Proof.
  unfold div_ceil_n. propositional.
  - cases m. simpl in *. lia.
    eapply Div0.mod_divides in H0; try lia.
    invert H0. rewrite <- add_sub_assoc by lia.
    rewrite Nat.mul_comm. rewrite div_add_l by lia.
    rewrite div_mul by lia.
    rewrite div_small by lia. lia.
  - erewrite (Nat.div_mod_eq n m) in *.
    rewrite mul_comm in H0. rewrite div_add_l in H0 by lia.
    rewrite (div_small (n mod m)) in H0.
    2: { eapply Nat.mod_upper_bound. lia. }
    rewrite add_0_r in *.
    rewrite <- add_sub_assoc in H0 by lia.
    rewrite <- add_assoc in H0.
    rewrite div_add_l in H0 by lia.
    rewrite <- H0.
    rewrite Div0.add_mod_idemp_r by lia.
    cases (n mod m).
    + simpl in *. rewrite (div_small (m-1)) by lia. rewrite add_0_r.
      pose proof Heq. eapply Div0.div_exact in H1.
      rewrite <- H1.
      replace (n+n) with (2*n) by lia.
      rewrite <- Div0.mul_mod_idemp_r by lia. rewrite Heq. simpl.
      rewrite Div0.mod_0_l by lia. rewrite sub_diag. reflexivity.
    + rewrite add_succ_comm in H0.
      rewrite <- sub_succ_l in H0 by lia. simpl in H0. rewrite sub_0_r in H0.
      replace m with (1*m) in H0 at 2 by lia.
      rewrite (Nat.add_comm n0) in H0. rewrite div_add_l in H0 by lia.
      simpl. lia.
Qed.

Lemma Z2Nat_div_distr : forall n c,
    (0 < c)%Z ->
    (0 <= n)%Z ->
    Z.to_nat (n // c) = (Z.to_nat n) //n (Z.to_nat c).
Proof.
  unfold div_ceil. intros.
  cases n.
  simpl. rewrite Zdiv_small by lia. simpl.
  unfold div_ceil_n. rewrite div_small by lia. reflexivity.
  unfold div_ceil_n.
  repeat rewrite Z2Nat.inj_div by lia.
  f_equal. rewrite Z2Nat.inj_sub by lia. rewrite Z2Nat.inj_add by lia.
  reflexivity. lia.
Qed.

Lemma ceil_sub_floor_le_1 : forall n m,
    n //n m - n / m <= 1.
Proof.
  unfold div_ceil_n. intros. cases m. simpl. lia.
  remember (Datatypes.S m). cases n. simpl. rewrite div_small by lia.
  rewrite div_small by lia. lia.
  rewrite add_sub_swap by lia. remember (Datatypes.S n).
  replace n0 with (1*n0) at 1 by lia.
  rewrite div_add by lia.
  subst. simpl div. rewrite sub_0_r.
  cases m. simpl.
  - pose proof (divmod_spec n 0 0 0).
    pose proof (divmod_spec n 0 1 0).
    cases (divmod n 0 0 0). cases (divmod n 0 1 0).
    simpl in *. repeat rewrite add_0_r in *.
    assert (0 <= 0) by lia. propositional. subst.
    lia.
  - pose proof (divmod_spec n (Datatypes.S m) 0 (Datatypes.S m)).
    pose proof (divmod_spec n (Datatypes.S m) 0 m).
    cases (divmod n (Datatypes.S m) 0 (Datatypes.S m)).
    cases (divmod n (Datatypes.S m) 0 m).
    simpl.
    assert (m <= Datatypes.S m) by lia.
    assert (Datatypes.S m <= Datatypes.S m) by lia.
    rewrite mul_0_r in * . rewrite add_0_r in *.
    rewrite sub_succ_l in * by lia. rewrite sub_diag in *. propositional.
    rewrite add_0_r in *. subst.
    rewrite add_sub_assoc in H0 by lia.
    rewrite add_sub_assoc in H0 by lia.
    cases (n0 + 1 - n2). lia.
    rewrite <- Heq1.
    assert (n0 >= n2) by lia.
    rewrite Nat.add_comm. rewrite <- add_sub_assoc by lia.
    assert (Datatypes.S (Datatypes.S m) * n0 + Datatypes.S m - n1 + 1 - Datatypes.S (Datatypes.S m) * n2 =
              Datatypes.S (Datatypes.S m) * n2 + Datatypes.S m - n3 - Datatypes.S (Datatypes.S m) * n2) by lia.
    rewrite add_sub_swap in H3 by lia.
    rewrite (Nat.add_comm _ (Datatypes.S m)) in H3.
    rewrite <- sub_add_distr in H3.
    rewrite (Nat.add_comm n1) in H3.
    rewrite sub_add_distr in H3.
    rewrite <- add_sub_assoc in H3 by lia.
    rewrite <- mul_sub_distr_l in H3.
    symmetry in H3.
    rewrite (Nat.add_comm _ (Datatypes.S m)) in H3.
    rewrite <- sub_add_distr in H3.
    rewrite (Nat.add_comm n3) in H3.
    rewrite sub_add_distr in H3.
    rewrite <- add_sub_assoc in H3 by lia.
    rewrite <- mul_sub_distr_l in H3. rewrite sub_diag in H3.
    rewrite mul_0_r in H3. rewrite add_0_r in H3.
    cases (n0-n2). lia. lia.
Qed.

