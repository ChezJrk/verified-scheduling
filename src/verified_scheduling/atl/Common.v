From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import micromega.Lia.
From Coq Require Import micromega.Zify.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Coq Require Import ZArith.Zdiv.
From Coq Require Import ZArith.Int.
From Coq Require Import ZArith.Znat.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Classes.Morphisms.

Set Warnings "-deprecate-hint-without-locality,-deprecated".

Import ListNotations.

From ATL Require Import ATL Tactics Div.

Generalizable All Variables.

Instance pointwise_eq_ext {A B : Type} `(sb : subrelation B RB Logic.eq)
  : subrelation (pointwise_relation A RB) Logic.eq. 
Proof.
  intros f g Hfg. apply functional_extensionality. intro x; apply sb, (Hfg x).
Qed.

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

(* Hole Establishing and Context Diving *)

Lemma concat_eq_l {X} `{TensorElem X} :
  forall a b c,
    a = c ->
    a <++> b = c <++> b.
Proof. intros. subst. reflexivity. Qed.

Lemma concat_eq_r {X} `{TensorElem X} :
  forall a b c,
    a = c ->
    b <++> a = b <++> c.
Proof. intros. subst. reflexivity. Qed.

Lemma tlet_eq_bound {X Y} `{TensorElem X} `{TensorElem Y} :
  forall (e1 e2 : X) (f : X -> Y),
    e1 = e2 ->
    let_binding e1 f =
    let_binding e2 f.
Proof.
  intros. subst. reflexivity.
Qed.

Theorem let_extensionality {X Y} `{TensorElem X} `{TensorElem Y} :
  forall (x : X) (f g : X -> Y) s,
    consistent x s ->
    (forall x, consistent x s -> f x = g x) ->
    let_binding x f = let_binding x g.
Proof.
  intros.
  unfold let_binding.
  apply H2. auto.
Qed.

Lemma lbind_helper {X Y} `{TensorElem Y} :
  forall (body : X -> Y) x,
    body x = tlet v := x in body v.
Proof. intros. unfold let_binding. reflexivity. Qed.

Lemma tlet_bin_distr {X Y} `{TensorElem Y} :
  forall (e1 e2 : X) (f1 f2 : X -> Y),
    e1 = e2 ->
    (tlet a := e1 in f1 a) <+> (tlet b := e2 in f2 b) =
    tlet a := e1 in (f1 a <+> f2 a).
Proof. intros. unfold let_binding. subst. auto. Qed.

Lemma tlet_f_bound_body {X Y Z} `{TensorElem Z} `{TensorElem X} `{TensorElem Y}:
  forall (f : X -> Y) (e1 : X) (e2 : Y -> Z),
    (tlet x := f e1 in e2 x) = tlet x := e1 in ((fun a => e2 (f a)) x).
Proof.
  intros. unfold let_binding. auto.
Qed.
Lemma tlet_id_split {X Y} `{TensorElem X} `{TensorElem Y} :
  forall (f : X -> X) (g : X -> X) s (x : X) (body : X -> Y),
    consistent x s ->        
    (forall x', consistent x' s -> f (g x') = x') ->
    let_binding x body = let_binding (g x) (fun x' => body (f x')).
Proof.
  intros.
  unfold let_binding.  
  rewrite H2; auto.
Qed.

Lemma tlet_eq_body {X Y} :
  forall (e : X) (f g : X -> Y),
    (forall i, f i  = g i) ->
    let_binding e f = let_binding e g.
Proof.
  intros. unfold let_binding. auto.
Qed.
  
Lemma bin_eq_l {X} `{TensorElem X} : forall a b c,
    a = b -> a <+> c = b <+> c.
Proof.
  intros. subst. reflexivity.
Qed.

Lemma bin_eq_r {X} `{TensorElem X} : forall a b c,
    a = b -> c <+> a = c <+> b.
Proof.
  intros. subst. reflexivity.
Qed.

Lemma iverson_weak {X} `{TensorElem X} : forall p (e1 e2 : X),
    e1 = e2 ->
  (|[ p ]| e1) = (|[ p ]| e2).
Proof.
  intros. subst. reflexivity.
Qed.

Lemma iverson_in {X} `{TensorElem X} : forall p (e1 e2 : X) s,
  (p = true -> e1 = e2) ->
  (p = false -> consistent e1 s /\ consistent e2 s) ->
  (|[ p ]| e1) = (|[ p ]| e2).
Proof.
  intros.
  destruct p.
  - peel_hyp. subst. reflexivity.
  - unfold iverson. peel_hyp. destruct H1.
    eapply mul_0_absorb; eauto.
Qed.

Lemma true_iverson {X} `{TensorElem X} : forall e, (|[ true ]| e) = e.
Proof. unfold iverson. apply mul_1_id. Qed.

Hint Rewrite @true_iverson : crunch.

Theorem sum_helper_eq_bound_0 {X} `{TensorElem X} : forall n f g,
    (forall i, 0 <= i -> i < n -> f (Z.of_nat i) = g (Z.of_nat i)) ->
    sum_helper n 0 f = sum_helper n 0 g.
Proof.
  induction n; intros f g H0.
  - reflexivity.
  - simpl. f_equal.
    + apply (H0 0); lia.
    + apply IHn.
      intros.
      replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) by
          (now rewrite Nat2Z.inj_succ).
      apply H0; lia.
Qed.

Theorem sum_helper_eq_bound {X} `{TensorElem X} : forall n m f g,
    (forall i, 0 <= i -> i < n ->
               f (Z.of_nat i + m)%Z = g (Z.of_nat i + m)%Z) ->
    sum_helper n m f = sum_helper n m g.
Proof.
    induction n; intros.
  - reflexivity.
  - simpl.
    f_equal.
    apply (H0 0); lia.
    apply IHn. intros.
    replace (Z.of_nat i + m + 1)%Z with ((Z.of_nat (S i)) + m)%Z by
        (rewrite Nat2Z.inj_succ; lia).
    apply H0; lia.
Qed.    

Theorem sumr_eq_bound {X} `{TensorElem X} : forall n m f g,
    (forall i, m <= i -> i < n ->
               f i = g i)%Z ->
    SUM [ m <= i < n ] f i = SUM [ m <= i < n ] g i.
Proof.
  unfold sumr.
  intros.
  destruct (0<=?n-m)%Z eqn:nm; unbool.
  apply sum_helper_eq_bound.
  intros. apply H0. lia.
  zify. 
  lia.
  destruct (n-m)%Z. lia. zify. lia. reflexivity.
Qed.    

Theorem gen_helper_eq_bound {X} `{TensorElem X} : forall n m f g,
    (forall i, 0 <= i -> i < n ->
               f (Z.of_nat i + m)%Z = g (Z.of_nat i + m)%Z) ->
    gen_helper n m f = gen_helper n m g.
Proof.
    induction n; intros.
  - reflexivity.
  - simpl.
    f_equal.
    apply (H0 0); lia.
    apply IHn. intros.
    replace (Z.of_nat i + m + 1)%Z with ((Z.of_nat (S i)) + m)%Z by
        (rewrite Nat2Z.inj_succ; lia).
    apply H0; lia.
Qed.    

Hint Resolve sum_helper_eq_bound : crunch.

Lemma get_eq_index {X} `{TensorElem X} : forall i v u,
  v = u ->
  v _[i] = u _[i].
Proof.
  intros. subst. reflexivity.
Qed.

Theorem gen_eq_bound {X} `{TensorElem X} : forall N (f g : Z -> X),
  (forall i, (0 <= i)%Z -> (i < N)%Z -> f i = g i) ->
  GEN [ i < N ] f i = GEN [ i < N ] g i.
Proof.
  destruct N; intros f g H0; try reflexivity.
  unfold gen, genr. simpl. posnat.
  apply gen_helper_eq_bound; intros.
  apply H0. lia. simpl.
  rewrite Z.add_0_r. lia.
Qed.

Theorem genr_eq_bound {X} `{TensorElem X} : forall N (f g : Z -> X) K,
  (forall i, (K <= i)%Z -> (i < N)%Z -> f i = g i) ->
  GEN [ K <= i < N ] f i = GEN [ K <= i < N ] g i.
Proof.
  destruct N; intros; try reflexivity.
  unfold gen, genr. 
  apply gen_helper_eq_bound; intros.
  apply H0. lia. zify. lia.
  unfold gen, genr. 
  apply gen_helper_eq_bound; intros.
  apply H0. lia. zify. lia.
  unfold gen, genr. 
  apply gen_helper_eq_bound; intros.
  apply H0. lia. zify. lia.
Qed.

Theorem sum_eq_bound {X} `{TensorElem X} : forall N (f g : Z -> X),
  (forall i, (0 <= i)%Z -> (i < N)%Z -> f i = g i) ->
  SUM [ i < N ] f i = SUM [ i < N ] g i.
Proof.
  destruct N; intros f g H0; try reflexivity.
  unfold sum, sumr. simpl. posnat.
  apply sum_helper_eq_bound_0; intros.
  apply H0. lia. simpl. lia.
Qed.

Hint Resolve sum_eq_bound : crunch.
Hint Resolve gen_eq_bound : crunch.

Lemma iverson_eq {X} `{TensorElem X} :
  forall p1 p2 e, p1 = p2 -> (|[ p1 ]| e) = (|[ p2 ]| e).
Proof. 
  intros. subst. reflexivity.
Qed.

Hint Rewrite andb_false_r : crunch.
Hint Rewrite andb_false_l : crunch.
Hint Rewrite andb_true_r : crunch.
Hint Rewrite andb_true_l : crunch.
Hint Extern 4 => exists 0%Z : crunch.
Hint Extern 0 ((_,_) = (_,_)) => f_equal : crunch.
Hint Extern 0 (Some _ = Some _) => f_equal : crunch.
Hint Resolve Z.mul_nonneg_nonneg : crunch.
Hint Resolve Z.add_nonneg_nonneg : crunch.
Hint Extern 6 (0%R = (|[ _ ]| _)) => analyze_bool : crunch.
Hint Extern 1 (Z.of_nat _ <= _)%Z => apply Z2Nat.inj_le : crunch.
Hint Extern 5 (_ = _) => (unbool; lia) : crunch.
Hint Extern 6 (_ < _)%Z => lia : crunch.
Hint Extern 6 (_ < _) => lia : crunch.
Hint Extern 6 (_ <= _) => lia : crunch.
Hint Extern 6 (_ <= _)%Z => lia : crunch.
Hint Extern 6 (_ = _) => lia : crunch.
Hint Extern 3 (Z.to_nat _ < Z.to_nat _) => apply Z2Nat.inj_lt; lia : crunch.
Hint Extern 3 (Z.to_nat _ <= Z.to_nat _) => apply Z2Nat.inj_le; lia : crunch.
Hint Extern 4 => ring : crunch.
Hint Extern 5 (bin _ _ = bin _ _) => f_equal : crunch.
Hint Extern 5 ((|[ _ ]| _ ) = (|[ _ ]| _ )) => f_equal : crunch.
Hint Extern 0 (~ _ < _) => apply nlt_ge : crunch.
Hint Extern 0 (_ < _ -> False) => apply nlt_ge : crunch.
Hint Extern 0 (0 = _)%R => symmetry : crunch.

Notation "'inc' f" := (fun x => f (x+1)%Z) (at level 80).

Hint Rewrite @get_empty_null : crunch.

Lemma sum_helper_const {X} `{TensorElem X} : forall m n,
    sum_helper m n (fun _ => null) = null.
Proof.
  induction m; intros; try reflexivity.
  simpl. rewrite IHm. rewrite bin_null_id_r. reflexivity.
Qed.

Hint Resolve sum_helper_const : crunch.

Lemma guard_mul_l : forall p e1 e2, ((|[ p ]| e1) * e2)%R = (|[ p ]| (e1 * e2))%R.
Proof.
  destruct p; intros.
  - now repeat rewrite true_iverson.
  - unfold iverson. now repeat rewrite Rmult_0_l.
Qed.

Lemma guard_mul_r : forall p e1 e2, (e2 * (|[ p ]| e1))%R = (|[ p ]| (e2 * e1))%R.
Proof.
  intros.
  rewrite Rmult_comm.
  rewrite guard_mul_l.
  rewrite Rmult_comm.
  reflexivity.
Qed.

Hint Rewrite guard_mul_l : crunch.
Hint Rewrite Rmult_1_l : crunch.

Lemma gen_helper_length {X} `{TensorElem X} : forall n (f : Z -> X) x,
    length (gen_helper n x f) = n.
Proof.
  induction n; intros; simpl; auto with crunch.
Qed.

Hint Resolve gen_helper_length : crunch.
Hint Resolve functional_extensionality : crunch.
Hint Resolve -> Pos2Nat.inj_lt : crunch.
Hint Extern 3 => lia : crunch.

Lemma genr_length {X} `{TensorElem X} : forall n m (f : Z -> X),
    length (GEN [ m <= i < n ] f i) = Z.to_nat (n - m).
Proof.
  unfold genr.
  auto with crunch.
Qed.

Lemma gen_length {X} `{TensorElem X} : forall n (f : Z -> X),
    length (GEN [ i < n ] f i) = Z.to_nat n.
Proof.
  intros.
  unfold gen, genr.
  rewrite Z.sub_0_r.
  auto with crunch.
Qed.

Lemma gen_of_nat_length {X} `{TensorElem X} : forall n (f : Z -> X),
    length (GEN [ i < Z.of_nat n ] f i) = n.
Proof.
  intros.
  rewrite gen_length.
  rewrite Nat2Z.id. auto.
Qed.

Hint Rewrite @gen_of_nat_length : crunch.

Theorem gen_map {X Y} `{TensorElem X} `{TensorElem Y} :
  forall n (f : X -> Y) (g : Z -> X),
    GEN [ x < n ] (f (g x)) = map f (GEN [ i < n ] g i).
Proof.
  unfold gen, genr.
  intros n.
  rewrite Z.sub_0_r.
  induction (Z.to_nat n); simpl; auto with crunch.
Qed.
Hint Resolve gen_map : crunch.

Theorem genr_map {X Y} `{TensorElem X} `{TensorElem Y} :
  forall n k (f : X -> Y) (g : Z -> X),
    GEN [ k <= x < n ] (f (g x)) = map f (GEN [ k <= i < n ] g i).
Proof.
  unfold gen, genr.
  intros n k.
  induction (Z.to_nat (n-k)%Z); simpl; auto with crunch.
Qed.

Lemma get_neg_null : forall i (X: Set) (H: TensorElem X) x v,
    (i < 0)%Z ->
    (x::v) _[ i ] = |[ false ]| x.
Proof.
  intros; destruct i; contra_crush.
Qed.

Lemma get_neg_null_shape : forall i (X: Set) (H: TensorElem X)
                                  (v : list X) s e n,
    (i < 0)%Z ->
    consistent v (n,s) ->
    consistent e s ->
    v _[ i ] = |[ false ]| e.
Proof.
  intros. inversion H1.
  rewrite get_neg_null by assumption.
  unfold iverson.
  eapply mul_0_absorb; eauto.
Qed.

Lemma get_znlt_null : forall i (X : Set) (H: TensorElem X) (v : list X) x,
    ~ (i < Z.of_nat (length (x::v)))%Z->
    (x::v) _[ i ] = (|[ false ]| x).
Proof.
  intros. generalize dependent i.
  induction v; destruct i; intros; try reflexivity; unfold get; simpl.
  - simpl in H0. lia.
  - posnat.
    simpl in *.
    destruct pn; reflexivity.
  - simpl in H0. zify. lia.
  - posnat. simpl.
    simpl length in *.
    destruct pn.
    simpl. zify. lia.
    simpl.
    specialize (IHv (Z.of_nat (S pn))).
    assert (~ (Z.of_nat (S pn) < Z.of_nat (S (length v)))%Z). zify. lia.
    apply IHv in H1.
    unfold get in H1. simpl in H1.
    rewrite SuccNat2Pos.id_succ in H1. simpl in H1.
    assumption.
Qed.

Lemma get_znlt_null_shape : forall i (X : Set) (H: TensorElem X)
                                   (v : list X) s e n,
    ~ (i < Z.of_nat (length v))%Z->
    consistent v (n,s) ->
    consistent e s ->
    v _[ i ] = (|[ false ]| e).
Proof.
  intros. inversion H1.
  rewrite get_znlt_null.
  unfold iverson.
  eapply mul_0_absorb; eauto.
  subst. auto.
Qed.

Lemma get_znlt_zero : forall (v : list R) (i : Z),
    ~ (i < Z.of_nat (length v))%Z -> v _[ i ] = 0%R.
Proof. intros. destruct v. reflexivity.
       rewrite (@get_znlt_null). unfold iverson.
       simpl. ring. auto.
Qed.

Lemma get_neg_zero : forall (v : list R) (i : Z),
    (i < 0)%Z -> v _[ i ] = 0%R.
Proof. intros. destruct v. reflexivity.
       rewrite get_neg_null. unfold iverson.
       simpl. ring. auto.
Qed.

Hint Resolve get_znlt_zero : crunch.
Hint Resolve get_neg_zero : crunch.

Lemma get_gen_null : forall I X (H : TensorElem X) N (f : Z -> X),
    (0 < N)%Z ->
    ~ (Z.to_nat I) < (Z.to_nat N) -> (GEN [ x < N ] f x) _[ I ] =
                                     (|[false]| f 0%Z).
Proof.
  intros.
  destruct N; try (now zify; lia).
  unfold gen, genr.
  simpl. posnat. simpl gen_helper.
  apply get_znlt_null. simpl.
  rewrite gen_helper_length.
  zify. lia.
Qed.

Lemma get_gen_neg_null {X} `{TensorElem X} : forall N I f,
    (0 < N)%Z ->
    (I < 0)%Z -> (GEN [ x < N ] f x) _[ I ] =
                                     (|[false]| f 0%Z).
Proof.
  intros.
  destruct N; try (now zify; lia).
  unfold gen, genr.
  simpl. posnat. simpl gen_helper.
  apply get_neg_null. auto.
Qed.

Lemma nth_gen_helper_some {X} `{TensorElem X} :
  forall n i m (e0 : Z -> X),
    i < n ->
    nth_error (gen_helper n m e0) i = Some (e0 (m + Z.of_nat i)%Z).
Proof. 
  induction n; intros i m e0 H0.
  - inversion H0.
  - simpl. 
    destruct i; try reflexivity.
    simpl. rewrite Z.add_0_r. reflexivity.
    apply lt_S_n in H0.
    apply (IHn _ m (inc e0)) in H0. simpl.
    rewrite H0. rewrite <- Z.add_assoc.
    rewrite Zpos_P_of_succ_nat. 
    reflexivity.
Qed.

Lemma get_gen_helper_some {X} `{TensorElem X} : forall n m f i,
    (0 <= i)%Z ->
    Z.to_nat i < n ->
    (gen_helper n m f) _[i] = f (i + m)%Z.
Proof.
  induction n; intros.
  - lia.
  - unfold get; simpl.
    destruct i.
    + reflexivity.
    + simpl Z.to_nat.
      posnat. simpl nth_error.
      specialize (IHn m (inc f) (Z.of_nat pn)).
      peel_hyp.
      unfold get in IHn. destruct n. zify. lia.
      simpl in IHn.
      destruct (Z.of_nat pn) eqn:e.
      * simpl in IHn. destruct pn eqn:ee.
        -- rewrite Z.add_comm.
           simpl.
           f_equal. zify. lia.
        -- simpl in e. zify. lia.
      * rewrite <- e in *.
        rewrite Nat2Z.id in IHn.
        rewrite Z.add_comm.
        destruct pn. simpl. f_equal. zify. lia.
        simpl nth_error in IHn.
        rewrite nth_gen_helper_some in IHn.
        simpl. rewrite nth_gen_helper_some. rewrite IHn.
        f_equal. zify. lia. zify. lia. zify. lia.
      * zify. lia.
      * assert (Z.of_nat pn < Z.pos p)%Z.
        { zify. lia. }
        rewrite Nat2Z.id. zify. lia.
    + zify. lia.
Qed.

Lemma get_genr_some {X} `{TensorElem X} :
  forall I n m (body : Z -> X),
    (m < n)%Z ->
    (0 <= I)%Z ->
    (Z.to_nat I) < (Z.to_nat (n - m)) ->
    (GEN [ m <= x < n ] body x) _[ I ] = body (m + I)%Z.
Proof.
  intros.
  unfold gen, genr.
  destruct I eqn:di; try contra_crush.
  - simpl. rewrite Z.add_0_r.
    destruct (Z.to_nat (n-m)%Z) eqn:e; try lia; try reflexivity.
  - unfold get.
    rewrite nth_gen_helper_some.
    destruct (Z.to_nat (n-m)) eqn:e.
    + lia.
    + simpl. f_equal. zify. lia.
    + zify. lia.
Qed.

Lemma get_gen_some {X} `{TensorElem X} :
  forall I (body : Z -> X) N,
    (I < N)%Z ->
    (0 <= I)%Z ->
    (GEN [ x < N ] body x) _[ I ] = body I.
Proof.
  intros.
  unfold get, gen, genr.
  destruct I eqn:di; try contra_crush.
  - rewrite Z.sub_0_r.
    destruct N eqn:dn. lia.
    simpl. posnat. simpl. auto.
    zify. lia.
  - rewrite nth_gen_helper_some.
    simpl.
    rewrite positive_nat_Z. auto.
    rewrite Z.sub_0_r.
    destruct N. lia. simpl. posnat. simpl. reflexivity.
    zify. lia.
    zify. lia.
Qed.

Lemma get_gen_some_guard {X} `{TensorElem X} :
  forall I (body : Z -> X) N s,
    (0 < N)%Z ->
    (forall x, consistent (body x) s) ->
    (GEN [ x < N ] body x) _[ I ] = |[ (I <? N) && (0 <=? I) ]| body I.
Proof.
  intros.
  destruct (I <? N)%Z eqn:e; destruct (0 <=? I)%Z eqn:ee;
    unbool_hyp; simpl andb.
  - rewrite true_iverson.
    rewrite get_gen_some by auto.
    reflexivity.
  - rewrite get_gen_neg_null.
    unfold iverson.
    eapply mul_0_absorb.
    eauto. eauto. auto. auto with crunch. auto.
  - rewrite get_gen_null.
    unfold iverson.
    eapply mul_0_absorb.
    eauto. eauto. auto. auto. auto with crunch.
  - lia.
Qed.

(*
Lemma get_gen_some_ {X} `{TensorElem X} :
  forall (e0 : Z -> X) i n k,
    (i < k)%Z ->    
    k = n ->
    (0 <= i)%Z ->
    (GEN [ x < n ] e0 x) _[ i ] = e0 i.
Proof.
  intros.
  subst.
  apply get_gen_some; auto.
Qed.
*)
Lemma get_gen_of_nat_some :
  forall I (X : Set) (H : TensorElem X) (body : Z -> X) N,
    (I < Z.of_nat N)%Z ->
    (0 <= I)%Z ->
    (GEN [ x < Z.of_nat N ] body x) _[ I ] = body I.
Proof.
  intros.
  apply get_gen_some.
  auto with crunch. auto.
Qed.
(*
Lemma get_gen {X} `{TensorElem X} : forall f a n,
    (0 < n)%Z ->
    (forall x, x < 0 \/ n <= x -> f x = (|[ false ]| f 0%Z))%Z ->
    (GEN [ i < n ] f i) _[a] =
    f a.
Proof.
  intros.
  destruct (0 <=? a)%Z eqn:a0; destruct (a <? n)%Z eqn:an; unbool.
  - rewrite get_gen_some; auto.
  - destruct n; try (zify; lia).
    unfold gen, genr. simpl. posnat.
    simpl gen_helper.
    erewrite get_znlt_null. rewrite (H1 a). reflexivity. auto.
    simpl. rewrite gen_helper_length. zomega.
  - destruct n; try (zify; lia).
    unfold gen, genr. simpl. posnat.
    simpl gen_helper.
    rewrite get_neg_null; auto.
    rewrite (H1 a); auto.
  - lia.
Qed.
 *)

Lemma get_0_cons {X} `{TensorElem X} : forall x xs,
    (x::xs) _[0] = x.
Proof.
  intros.
  unfold get.
  reflexivity.
Qed.

Lemma get_0_gen_of_nat {X} `{TensorElem X} : forall k f,
    0 < k ->
    (GEN [ x < Z.of_nat k ] f x) _[0] = f 0%Z.
Proof.
  intros.
  rewrite get_gen_some; auto with crunch.
Qed.

Lemma sum_helper_app {X} `{TensorElem X} : forall n f m,
   sum_helper (S n) m f = bin (sum_helper n m f) (f (m + Z.of_nat n)%Z).
Proof.
  induction n; intros.
  - simpl. rewrite Z.add_0_r. apply bin_comm.
  - replace (sum_helper (S (S n)) m f) with
        (bin (f m) (sum_helper (S n) m (inc f))).
    rewrite (IHn (inc f)).
    simpl.
    rewrite <- bin_assoc.
    f_equal.
    f_equal. f_equal. lia.
    reflexivity.
Qed.

Lemma simpl_sum_helper {X} `{TensorElem X} : forall n m f,
    sum_helper (S n) m f = f m <+> sum_helper n m (inc f).
Proof. reflexivity. Qed.

Lemma gen_step {X} `{TensorElem X} : forall n f,
    GEN [ i < Z.of_nat (S n) ] f i =
    f 0%Z :: GEN [ i < Z.of_nat n ] f (i + 1)%Z.
Proof.
  intros.
  unfold gen, genr.
  repeat rewrite Z.sub_0_r.
  repeat rewrite Nat2Z.id.
  simpl. f_equal.
Qed.

Lemma get_step {X} `{TensorElem X} : forall i x xs s,
    (0 <= i)%Z ->
    consistent xs (length xs, s) ->
    consistent (x::xs) (S (length xs), s) ->
    (x :: xs) _[i + 1] = xs _[i].
Proof.
  unfold get.
  intros.
  inversion H1. subst.
  replace (Z.to_nat (i + 1)%Z) with (S (Z.to_nat i)) by (zify; lia).
  rewrite <- nth_error_inc.
  destruct (i+1)%Z eqn:e; try (zify; lia).
  destruct i eqn:ee; try (zify; lia).
  - assert (scalar_mul 0 x0 = scalar_mul 0 x).
    eapply mul_0_absorb.
    eauto. inversion H2. eauto. auto.
    rewrite H3. reflexivity.
  - rewrite <- ee.
    assert (scalar_mul 0 x0 = scalar_mul 0 x).
    eapply mul_0_absorb.
    eauto. inversion H2. eauto. auto.
    rewrite H3. reflexivity.
Qed.

Lemma sum_of_nat_step {X} `{TensorElem X} : forall n f,
    SUM [ i < Z.of_nat (S n) ] f i =
    f 0%Z <+> SUM [ i < Z.of_nat n ] f (i+1)%Z.
Proof.
  intros. unfold sum, sumr.
  repeat rewrite Z.sub_0_r.
  repeat rewrite Nat2Z.id.
  reflexivity.
Qed.

Lemma iverson_length {X} `{TensorElem X} :
  forall b (l : list X), length (|[ b ]| l) = length l.
Proof.
  destruct b; intros; simpl; unfold iverson; unfold scalar_mul; simpl;
         rewrite map_length; auto.
Qed.
Hint Rewrite @iverson_length : crunch.

Lemma iverson_id_true {X} `{TensorElem X} : forall p e,
    p = true -> (|[ p ]| e) = e.
Proof.
  intros. subst. apply true_iverson.
Qed.
Hint Resolve iverson_id_true : crunch.

Lemma iverson_mul_false {X} `{TensorElem X} : forall p e,
    p = false -> (|[ p ]| e) = scalar_mul 0%R e.
Proof.
  intros. subst. reflexivity.
Qed.
Hint Resolve iverson_mul_false : crunch.

Theorem iverson_bin_distr {X} `{TensorElem X} : forall a b p,
    (|[ p ]| a <+> b) = (|[ p ]| a) <+> (|[ p ]| b).
Proof.
  intros.
  unfold iverson.
  rewrite mul_bin_distr.
  reflexivity.
Qed.

Lemma nth_gen_helper_indic_not {X} `{TensorElem X} :
  forall i n m o (f : Z -> X),
    i < n ->
    (Z.of_nat i) <> o ->
    nth_error (gen_helper n m (fun x => |[ x =? o + m ]| f x)) i
    = Some (scalar_mul 0%R (f (m + Z.of_nat i)%Z)).
Proof.
  intros.
  eapply nth_gen_helper_some in H0.
  rewrite H0.
  auto with crunch.
Qed.

Lemma nth_gen_helper_indic : forall i n m f,
    i < n ->
    nth_error (gen_helper n m (fun x => |[ x =? (Z.of_nat i) + m ]| f x)) i
    = Some (f (m + Z.of_nat i)%Z).
Proof.
  intros.
  eapply nth_gen_helper_some in H.
  rewrite H.
  rewrite Z.add_comm.
  rewrite Z.eqb_refl.
  simpl.
  auto with crunch.
Qed.

Lemma get_genr_indic_not {X} `{TensorElem X} :
  forall (I N m o : Z) (body : Z -> X),
    (m < N)%Z ->
    (I < N - m)%Z ->
    (0 <= I)%Z ->
    o <> I ->
    (GEN [ m <= x < N ] (|[ x =? o+m ]| body x)) _[I]
    = scalar_mul 0%R (body (I+m)%Z).
Proof.
  destruct I eqn:di; intros.
  - app_in_crush (get_genr_some 0 N m (fun x => |[ x =? o + m ]| body x)) H0.
    + rewrite H0. simpl. rewrite Z.add_0_r.
      auto with crunch.
  - unfold get, genr.
    rewrite <- di in *.
    assert (Z.to_nat I < Z.to_nat (N-m)%Z) by auto with crunch.
    apply
      (nth_gen_helper_indic_not (Z.to_nat I) (Z.to_nat (N-m)%Z) m o body) in H4.
    rewrite H4.    
    destruct (Z.to_nat (N-m)) eqn:e.
    zify. lia.
    simpl.
    f_equal. f_equal. zify. lia. zify. lia.
  - contra_crush.
Qed.
    
Lemma get_genr_indic : forall I N m body,
    (m < N)%Z ->
    (I < N - m)%Z ->
    (0 <= I)%Z ->
    (GEN [ m <= x < N ] (|[ x =? I+m ]| body x)) _[I]
    = body (I+m)%Z.
Proof.
  destruct I eqn:di; intros.
  - specialize (get_genr_some 0 N m (fun x => |[ x =? 0 + m ]| body (0+x)%Z)).
    intros.
    app_in_crush H2 H.
    simpl in *.
    rewrite H. rewrite Z.add_0_r.
    rewrite Z.eqb_refl.
    apply Rmult_1_l.
  - unfold get, genr.
    rewrite <- di in *.
    specialize
      (nth_gen_helper_indic (Z.to_nat I) (Z.to_nat (N-m)%Z) m body); intros.
    assert (0 <= N - m)%Z by lia.
    assert (H4 := H1).
    apply (Z2Nat.inj_lt I (N-m)%Z) in H1.
    apply H1 in H0.
    apply H2 in H0. clear H2. clear H1.
    rewrite Z2Nat.id in H0. rewrite H0.
    destruct (Z.to_nat (N-m)) eqn:e. zify. lia.
    simpl.
    rewrite Z.add_comm. reflexivity.
    assumption. assumption.
  - contra_crush.
Qed.

Lemma sum_helper_push_bound_indic {X} `{TensorElem X} :
  forall n e m,
    sum_helper n m e =
    sum_helper n m (fun x => |[ m <=? x ]| e x).
Proof.
  intros.
  apply sum_helper_eq_bound.
  intros. symmetry.
  auto with crunch.
Qed.

Lemma sum_helper_push_upper_bound_indic {X} `{TensorElem X} :
  forall n e m,
    sum_helper n m e =
    sum_helper n m (fun x => |[ x <? (m + Z.of_nat n) ]| e x).
Proof.
  intros.
  apply sum_helper_eq_bound. intros.
  symmetry. auto with crunch.
Qed.

Lemma sum_push_bound_indic {X} `{TensorElem X} :
  forall N body,
      SUM [ i < N ] body i = SUM [ x < N ] (|[ 0 <=? x ]| body x).
Proof.
  intros.
  apply sum_helper_push_bound_indic.
Qed.

Lemma sum_push_upper_bound_indic {X} `{TensorElem X} :
  forall N body,
      SUM [ i < N ] body i = SUM [ x < N ] (|[ x <? N ]| body x).
Proof.
  intros.
  unfold sum, sumr.
  rewrite sum_helper_push_upper_bound_indic.
  autorewrite with crunch.
  destruct N; try reflexivity.
  simpl. posnat.
  rewrite <- Hpos.
  rewrite positive_nat_Z. reflexivity.
Qed.

Lemma gen_helper_push_bound_indic {X} `{TensorElem X} :
  forall n e m,
    gen_helper n m e =
    gen_helper n m (fun x => |[ m <=? x ]| e x).
Proof.
  intros.
  apply gen_helper_eq_bound.
  intros. symmetry. auto with crunch.
Qed.

Lemma gen_helper_push_upper_bound_indic {X} `{TensorElem X} :
  forall n e m,
    gen_helper n m e =
    gen_helper n m (fun x => |[ x <? (m + Z.of_nat n) ]| e x).
Proof.
  intros.
  apply gen_helper_eq_bound. intros.
  symmetry. auto with crunch.
Qed.

Theorem collapse_iverson {X} `{TensorElem X} :
  forall p0 p1 e,
    (|[ p0 ]| (|[ p1 ]| e)) = |[ andb p0 p1 ]| e.
Proof.
  intros p0 p1 ?.
  destruct p0; destruct p1; try (rewrite true_iverson; reflexivity).
  unfold iverson. apply mul_0_idemp.
Qed.

Lemma genr_push_bounds {X} `{TensorElem X} : forall N m body,
  GEN [ m <= i < N ] body i =
  GEN [ m <= i < N ] |[ (m <=? i) && (i <? N) ]| body i.
Proof.
  intros.
  unfold genr.
  rewrite gen_helper_push_upper_bound_indic.
  rewrite gen_helper_push_bound_indic.
  apply gen_helper_eq_bound. intros.
  simpl. setoid_rewrite @collapse_iverson.
  f_equal.
  f_equal.
  rewrite Z2Nat.id.
  rewrite Z.add_sub_assoc.
  rewrite Z.add_simpl_l. reflexivity.
  destruct (N-m)%Z eqn:nm; try lia.
Qed.

Lemma gen_push_bounds {X} `{TensorElem X} : forall N body,
  GEN [ i < N ] body i =
  GEN [ i < N ] |[ (0 <=? i) && (i <? N) ]| body i.
Proof.
  intros.
  unfold gen.
  apply genr_push_bounds.
Qed.

Lemma consistent_length {X} `{TensorElem X} : forall (v : list X) n s,
    consistent v (n,s) ->
    length v = n.
Proof.
  intros.
  inversion H0. auto.
Qed.

Lemma consistent_tensor_add {X} `{TensorElem X} : forall a b s,
    consistent a s ->
    consistent b s ->
    consistent (tensor_add a b) s.
Proof.
  intros.
  pose proof (@consistent_bin (list X) _).
  simpl in *.
  eapply H2;eauto.
Qed.

Lemma consistent_sum_helper {X} `{TensorElem X} :
  forall n m s f,
    (forall x, m <= x -> x < m + Z.of_nat (S n) -> consistent (f x) s)%Z ->
   consistent (sum_helper (S n) m f) s.
Proof.
  induction n; intros.
  - simpl. autorewrite with crunch.
    apply H0; zify; lia.
  - replace (sum_helper (S (S n)) m f) with
        (f m <+> sum_helper (S n) m (inc f)) by reflexivity.
    eapply consistent_bin with s; auto. apply H0; zify; lia.
    apply IHn.
    intros. apply H0. lia. lia.
Qed.

Lemma consistent_sumr {X} `{TensorElem X} :
  forall n m s f,
    (m < n)%Z ->
    (forall x, m <= x -> x < n -> consistent (f x) s)%Z ->
    consistent (SUM [ m <= i < n ] f i) s.
Proof.
  intros.
  unfold sumr.
  destruct (Z.to_nat (n-m)%Z) eqn:e.
  zify. lia.
  apply consistent_sum_helper.
  intros. apply H1; zify; lia.
Qed.
  
Lemma consistent_sum {X} `{TensorElem X} :
  forall s n f,
    (0 < n)%Z ->
    (forall x, 0 <= x -> x < n -> consistent (f x) s)%Z ->
    consistent (SUM [ i < n] f i) s.
Proof.
  intros.
  unfold sum, sumr.
  rewrite Z.sub_0_r.
  destruct n; zify; try lia.
  simpl. posnat.
  apply consistent_sum_helper. simpl.
  intros. apply H1. lia. zify. lia.
Qed.

Theorem length_sum {X} `{TensorElem X} : forall n f s,
    (0 < n)%Z ->
    (forall x, 0 <= x -> x < n -> consistent (f x) s)%Z ->
    length (SUM [ i < n ] f i) = length (f 0%Z).
Proof.
  intros. destruct s.
  erewrite consistent_length.
  erewrite consistent_length. 2: eauto with crunch. eauto.
  eapply consistent_sum. auto. eauto.
Qed.

Lemma forall_consistent_gen_helper {X} `{TensorElem X} : forall m s n f,
  (forall x, m <= x -> x < m + Z.of_nat n -> consistent (f x) s)%Z ->
  Forall (fun t => consistent t s) (gen_helper n m f).
Proof.
  intros m s. induction n; intros; simpl; constructor.
  - apply H0; zify; lia.
  - apply IHn.
    intros.
    apply H0; lia.
Qed.

Lemma consistent_gen_helper {X} `{TensorElem X} : forall m s n f,
    0 < n ->
    (forall x, m <= x -> x < m + Z.of_nat n -> consistent (f x) s)%Z ->
    consistent (gen_helper n m f) (n, s).
Proof.
  intros m s. destruct n; intros; simpl.
  - lia.
  - constructor.
    apply H1; zify; lia.
    apply forall_consistent_gen_helper.
    intros.
    apply H1; zify; lia.
    simpl. rewrite gen_helper_length. auto.
Qed.

Lemma consistent_genr {X} `{TensorElem X} : forall  m s n f,
    (m < n)%Z ->
    (forall x, m <= x -> x < n -> consistent (f x) s)%Z ->
    consistent (GEN [ m <= i < n ] f i) (Z.to_nat (n-m)%Z, s).
Proof.
  unfold gen.
  intros.
  apply consistent_gen_helper.
  zify. lia.
  intros.
  apply H1; zify; lia.
Qed.

Lemma consistent_gen {X} `{TensorElem X} : forall n m f s,
    0 < n ->
    (forall x, 0 <= x -> x < Z.of_nat n -> consistent (f x) s)%Z ->
    n = m ->
    consistent (GEN [ i < Z.of_nat n ] f i) (m, s).
Proof.
  unfold gen, genr.
  intros. rewrite Z.sub_0_r. rewrite Nat2Z.id. subst.
  apply consistent_gen_helper. auto.
  intros. apply H1; lia.
Qed.

Lemma consistent_gen' {X} `{TensorElem X} : forall n m f s,
    (0 < n)%Z ->
    (forall x, 0 <= x -> x < n -> consistent (f x) s)%Z ->
    (Z.to_nat n = m)%Z ->
    consistent (GEN [ i < n ] f i) (m, s).
Proof.
  unfold gen, genr.
  intros. rewrite Z.sub_0_r. rewrite H2.
  apply consistent_gen_helper. zify. lia. 
  intros. apply H1; zify; lia.
Qed.

Theorem consistent_let {X Y : Set} `{TensorElem Y} :
  forall (f : X -> Y) (e : X) s,
    consistent (f e) s ->
    consistent (let_binding e f) s.
Proof.
  intros.
  unfold let_binding.
  auto.
Qed.

Lemma sum_helper_push_hyp_indic {X} `{TensorElem X} : forall n m P f,
  P = true ->
  sum_helper n m f = sum_helper n m (fun x => |[ P ]| f x).
Proof.
  intros. generalize dependent f.
  induction n; intros; try reflexivity.
  simpl.
  rewrite IHn. subst.
  rewrite true_iverson.
  reflexivity.
Qed.

Lemma consistent_iverson {X} `{TensorElem X} : forall (e : X) p s,
    consistent e s ->
    consistent (|[ p ]| e) s.
Proof.
  intros. destruct p; subst.
  - rewrite true_iverson. auto.
  - unfold iverson.
    apply consistent_mul. auto.
Qed.

Lemma sum_helper_indic_false {X} `{TensorElem X} : forall n a f g m,
    (a < m)%Z \/
    (m + Z.of_nat n <= a)%Z ->
    sum_helper n m (fun k : Z => |[ (k =? a) && f k ]| g k)
    = sum_helper n m (fun k : Z => |[ false ]| g k).
Proof.
  intros. destruct H0; apply sum_helper_eq_bound; intros;
    destruct (Z.of_nat i + m =? a)%Z eqn:dai; auto with crunch.
Qed.

Lemma sumr_indic_false {X} `{TensorElem X} : forall m n a f g,
    (m <= n)%Z ->
    (a - m < 0)%Z \/ (n <= a)%Z ->
    SUM [ m <= k < n ] (|[ (k =? a) && (f k) ]| g k)
    = SUM [ m <= k < n ] (|[ false ]| g k).
Proof.
  intros.
  unfold sumr.
  apply sum_helper_indic_false; intros.
  destruct H1.
  left. lia. right. rewrite Z2Nat.id; lia.
Qed.

Lemma mul_sum_sum_mul {X} `{TensorElem X} : forall n m f c,
    scalar_mul c (sum_helper (S n) m f) =
    sum_helper (S n) m (fun x => scalar_mul c (f x)).
Proof.
  induction n; intros.
  - simpl; repeat rewrite bin_null_id_r; auto.
  - simpl in *.
    repeat rewrite mul_bin_distr. f_equal.
    specialize (IHn m (inc f) c).
    simpl in IHn.
    rewrite <- IHn.
    rewrite mul_bin_distr. reflexivity.
Qed.    

Lemma mul_0_sum_helper {X} `{TensorElem X} : forall n (f : Z -> X),
    scalar_mul 0 (sum_helper n 0 f) =
    sum_helper n 0 (fun x' : Z => scalar_mul 0 (f x')).
Proof.
  induction n; intros.
  - simpl. apply mul_0_null.
  - simpl.
    rewrite mul_bin_distr.
    f_equal.
    apply IHn.
Qed.

Lemma sum_iverson_lift {X} `{TensorElem X} : forall N body p,
    (|[ p ]| SUM [ i < N ] (body i)) =
    SUM [ i < N ] (|[ p ]| body i).
Proof.
  intros.
  destruct p.
  rewrite true_iverson.
  eapply sum_eq_bound; intros.
  rewrite true_iverson.
  reflexivity.
  unfold iverson.
  apply mul_0_sum_helper.
Qed.

Lemma sum_helper_false' {X} `{TensorElem X} : forall m s n f,
    (forall x : Z, m <= x -> x < m+Z.of_nat (S n) -> consistent (f x) s)%Z ->
    sum_helper (S n) m (fun x => |[ false ]| (f x)) = |[ false ]| (f m).
Proof.
  intros m s.
  induction n; intros.
  - simpl.
    autorewrite with crunch.
    unfold iverson.
    eapply mul_0_absorb.
    apply H0; eauto; zify; lia.
    apply H0; zify; lia.
    auto.
  - rewrite simpl_sum_helper.
    rewrite IHn.
    rewrite bin_comm.
    unfold iverson.
    eapply bin_mul_0_id.
    auto with crunch.
    apply consistent_mul.
    auto with crunch.
    auto.
    auto with crunch.
Qed.

Lemma sum_helper_false {X} `{TensorElem X} : forall t m n f,
    0 < n ->
    (forall x : Z, m <= x -> x < m + Z.of_nat n -> consistent (f x) t)%Z ->
    sum_helper n m (fun x => |[ false ]| (f x)) = |[ false ]| (f m%Z).
Proof.
  intros.
  destruct n. intros. lia.
  eapply sum_helper_false'; eauto.
Qed.

Lemma sum_helper_bound_indic {X} `{TensorElem X} :
  forall n (m a : Z) (f : Z -> bool) (g : Z -> X) (t : shape),
   (forall x : Z, m <= x -> x < m + Z.of_nat (S n) -> consistent (g x) t)%Z ->
    consistent (g a) t ->
    sum_helper (S n) m (fun k => |[ (k =? a) && f k ]| g k) 
    = (|[ (a <? m + Z.of_nat (S n)) && (m <=? a) && f a ]| g a).
Proof.
  induction n; intros.
  - simpl. autorewrite with crunch.
    analyze_bool.
    + simpl.
      eapply mul_0_absorb.
      auto with crunch.
      eauto. auto.
    + simpl.
      eapply mul_0_absorb.
      auto with crunch.
      eauto. auto.
  - rewrite simpl_sum_helper.
    analyze_bool.
    + simpl andb.
      assert (forall x, x+1 =? a = (x =? a-1))%Z.
      intros; unbool; lia.
      assert (sum_helper (S n) a (fun x : Z => |[ (x + 1 =? a) && f (x + 1) ]| g (x + 1)%Z) =
                sum_helper (S n) a (fun x : Z => |[ (x =? a-1) && f (x + 1) ]| g (x + 1)%Z)).
      { eapply sum_helper_eq_bound; intros.
        rewrite H4. reflexivity. }
      rewrite H5.
      erewrite IHn.
      rewrite Z.sub_add.
      replace (a <=? a-1)%Z with false by (symmetry; unbool; lia).
      rewrite andb_false_r. simpl.
      rewrite bin_comm.
      unfold iverson.
      eapply bin_mul_0_id.
      eauto.
      apply consistent_mul.
      eauto. auto.
      intros.
      eauto with crunch.
      rewrite Z.sub_add. auto.
    + simpl andb.
      assert (forall x, x+1 =? a = (x =? a-1))%Z by (intros; unbool; lia).
      assert (sum_helper (S n) m (fun x : Z => |[ (x + 1 =? a) && f (x + 1) ]| g (x + 1)%Z) =
                sum_helper (S n) m (fun x : Z => |[ (x =? a-1) && f (x + 1) ]| g (x + 1)%Z)).
      { eapply sum_helper_eq_bound; intros. rewrite H5. eauto. }
      rewrite H6.
      erewrite IHn.
      rewrite Z.sub_add.
      replace (m<=?a-1)%Z with true by (symmetry; unbool; lia).
      replace (a - 1 <? m + Z.of_nat (S n))%Z with true by
          (symmetry; unbool; zify; lia).
      simpl andb.
      eapply bin_mul_0_id.
      apply H0; eauto with crunch.
      apply consistent_iverson. eauto. auto.
      intros. eauto with crunch.
      rewrite Z.sub_add. auto.
    + simpl andb.
      assert (forall x, x+1 =? a = (x =? a-1))%Z by (intros; unbool; lia).
      assert (sum_helper (S n) m (fun x : Z => |[ (x + 1 =? a) && f (x + 1) ]| g (x + 1)%Z) = sum_helper (S n) m (fun x : Z => |[ (x =? a-1) && f (x + 1) ]| g (x + 1)%Z)).
      { eapply sum_helper_eq_bound; intros. rewrite H5. eauto. }
      rewrite H6.
      erewrite IHn.
      rewrite Z.sub_add.
      replace (m<=?a-1)%Z with false by (symmetry; unbool; lia).
      rewrite andb_false_r. simpl andb.
      unfold iverson.
      eapply bin_mul_0_id.
      eauto with crunch.
      apply consistent_mul.
      eauto. auto.
      eauto with crunch.
      rewrite Z.sub_add. auto.
    + simpl andb.
      assert (forall x, x+1 =? a = (x =? a-1))%Z by (intros; unbool; lia).
      assert (sum_helper (S n) m (fun x : Z => |[ (x + 1 =? a) && f (x + 1) ]| g (x + 1)%Z) = sum_helper (S n) m (fun x : Z => |[ (x =? a-1) && f (x + 1) ]| g (x + 1)%Z)).
      { eapply sum_helper_eq_bound; intros. rewrite H5. eauto. }
      rewrite H6.
      erewrite IHn.
      rewrite Z.sub_add.
      replace (a - 1 <? m + Z.of_nat (S n))%Z with false by
          (symmetry; unbool; zify; lia).
      simpl andb.
      unfold iverson.
      eapply bin_mul_0_id.
      eauto with crunch.
      apply consistent_mul. eauto. auto.
      eauto with crunch.
      rewrite Z.sub_add.
      eauto with crunch.
Qed.

Lemma sumr_bound_indic {X} `{TensorElem X} :
  forall (m N a : Z) (f : Z -> bool) (body : Z -> X) (t : shape),
       (m < N)%Z ->
       (forall x : Z, m <= x -> x < N -> consistent (body x) t)%Z ->
       consistent (body a) t ->
       SUM [ m <= k < N ] (|[ (k =? a) && f k ]| body k)
       = (|[ (a <? N) && (0 <=? a - m) && f a ]| body a).
Proof.
  intros. unfold sumr.
  destruct (Z.to_nat (N-m)%Z) eqn:e.
  zify. lia.
  erewrite sum_helper_bound_indic.
  apply iverson_eq.
  rewrite <- e.
  rewrite Z2Nat.id by lia.
  f_equal.
  unbool.
  lia. intros.
  apply H1. auto. rewrite <- e in H4.
  rewrite Z2Nat.id in H4 by lia. zify. lia.
  auto.
Qed.

Lemma sum_bound_indic {X} `{TensorElem X} :
  forall (N a : Z) (f : Z -> bool) (body : Z -> X) (t : shape),
       0 < Z.to_nat N ->
       (forall x : Z, 0 <= x -> x < N -> consistent (body x) t)%Z ->
       consistent (body a) t ->
       SUM [ k < N ] (|[ (k =? a) && f k ]| body k)
       = (|[ (a <? N) && (0 <=? a) && f a ]| body a).
Proof.
  intros. unfold sum. etransitivity.
  apply sumr_bound_indic with t0;
    autorewrite with crunch;
    auto with crunch.
  destruct N; simpl in *; try lia.
  rewrite Z.sub_0_r. reflexivity.
Qed.

Lemma sum_bound_indic_no_f {X} `{TensorElem X} :
  forall (body : Z -> X) (N a : Z) (t : shape),
    0 < Z.to_nat N ->
    (forall x : Z, 0 <= x -> x < N -> consistent (body x) t)%Z ->
    consistent (body a) t ->
    SUM [ k < N ] (|[ (k =? a) ]| body k)
    = (|[ (a <? N) && (0 <=? a) ]| body a).
Proof.
  intros. etransitivity.
  eapply sum_eq_bound; intros.
  erewrite <- (andb_true_r (i =? a)%Z). reflexivity. simpl.
  erewrite sum_bound_indic; auto with crunch.
Qed.

Lemma sum_bound_indic_no_f_guard {X} `{TensorElem X} :
  forall (body : Z -> X) (N a : Z) (t : shape),
    (forall x : Z, 0 <= x -> x < N -> consistent (body x) t)%Z ->
    (a < N)%Z ->
    (0 <= a)%Z ->
    SUM [ k < N ] (|[ (k =? a) ]| body k)
    = body a.
Proof.
  intros.
  erewrite sum_bound_indic_no_f.
  assert (a<?N = true)%Z by (unbool; lia).
  assert (0<=?a = true)%Z by (unbool; lia).
  rewrite H4, H3.
  simpl. apply true_iverson. auto with crunch.
  eauto.
  eauto.
Qed.

Lemma sum_of_nat_bound_indic_no_f {X} `{TensorElem X} :
  forall (body : Z -> X) N (a : Z) (t : shape),
    0 < N ->
    (forall x : Z, 0 <= x -> x < Z.of_nat N -> consistent (body x) t)%Z ->
    consistent (body a) t ->
    SUM [ k < Z.of_nat N ] (|[ (k =? a) ]| body k)
    = (|[ (a <? Z.of_nat N) && (0 <=? a) ]| body a).
Proof.
  intros.
  eapply sum_bound_indic_no_f.
  auto with crunch.
  apply H1. apply H2.
Qed.

Lemma iverson_eq_pred {X} `{TensorElem X} :
  forall (p : bool) (e1 e2 : X) (t1 t2 : shape),
    consistent e1 t1-> consistent e2 t2->
    t1 = t2 ->
    (p = true -> e1 = e2) -> (|[p]| e1) = (|[p]| e2).
Proof.
  destruct p; intros.
  peel_hyp; subst. reflexivity.
  unfold iverson.
  eapply mul_0_absorb; subst; eauto with crunch.
Qed.

Theorem sum_bin_split {X} `{TensorElem X} : forall m n f g,
    sum_helper m n (fun x => bin (f x) (g x)) =
    bin (sum_helper m n f) (sum_helper m n g).
Proof.
  induction m; intros.
  - simpl. autorewrite with crunch. auto.
  - simpl. rewrite (IHm n (inc f) (inc g)).
    rewrite bin_assoc. rewrite bin_assoc.
    rewrite <- (bin_assoc (f n) _ (g n)).
    rewrite (bin_comm (sum_helper m n (inc f)) (g n)).
    rewrite bin_assoc. reflexivity.
Qed.

Lemma get_bin_distr {X} `{TensorElem X} : forall a b I s,
    consistent a s ->
    consistent b s ->
    (a <+> b) _[I] = a _[I] <+> b _[I].
Proof.
  induction a; destruct b; intros.
  - autorewrite with crunch. auto.
  - autorewrite with crunch. auto.
  - autorewrite with crunch in *.
    auto.
  - simpl in *.
    inversion H0.
    inversion H1. subst.
    repeat rewrite tensor_add_step.
    destruct I.
    + autorewrite with crunch. auto.
    + unfold get.
      simpl. posnat. simpl.
      specialize (IHa b (Z.of_nat pn)).
      destruct pn.
      * simpl in *.
        destruct a0; destruct b.
        -- rewrite tensor_add_empty_r.
           rewrite mul_bin_distr. auto.
        -- rewrite tensor_add_empty_l.
           symmetry. eapply bin_mul_0_id.
           simpl in *. inversion H0. eauto.
           inversion H11. eauto.
           inversion H12.
        -- rewrite tensor_add_empty_r.
           symmetry.
           rewrite bin_comm.
           eapply bin_mul_0_id.
           inversion H1. eauto.
           inversion H5. eauto.
           auto.
        -- rewrite tensor_add_step. auto. inversion H1. simpl in *. lia.
      * simpl in *.
        destruct a0; destruct b.
        -- rewrite tensor_add_empty_r.
           rewrite mul_bin_distr. auto.
        -- rewrite tensor_add_empty_l.
           replace (scalar_mul 0 (a <+> x)) with (scalar_mul 0 x).
           symmetry.
           eapply bin_mul_0_id.
           eauto.
           destruct (nth_error b pn) eqn:e.
           ++ simpl in H12.
              inversion H12.
           ++ eapply consistent_mul.
              eauto.
           ++ inversion H12.
           ++ eapply mul_0_absorb.
              eauto. eapply consistent_bin; eauto.
              inversion H12. auto.
              inversion H12.
        -- rewrite tensor_add_empty_r.
           symmetry.
           rewrite bin_comm.
           erewrite bin_mul_0_id.
           replace (scalar_mul 0 (a <+> x)) with (scalar_mul 0 a).
           auto.
           eapply mul_0_absorb.
           eauto. eapply consistent_bin; eauto.
           inversion H12. eauto.
           eauto.
           destruct (nth_error a0 pn) eqn:e.
           ++ inversion H12.
           ++ eapply consistent_mul.
              eauto.
           ++ inversion H12.
        -- rewrite tensor_add_step in *.
           pose proof (tensor_consistent_step _ _ _ _ _ H0).
           apply IHa in H2.
           unfold get in H2.
           simpl in H2.
           rewrite SuccNat2Pos.id_succ in H2.
           simpl in H2.
           replace (scalar_mul 0 (a <+> x)) with (scalar_mul 0 (x0 <+> x1)).
           replace (scalar_mul 0 a) with (scalar_mul 0 x0).
           replace (scalar_mul 0 x) with (scalar_mul 0 x1).
           auto.
           eapply mul_0_absorb. inversion H11. eauto. eauto. auto.
           eapply mul_0_absorb. inversion H5. eauto. eauto. eauto.
           eapply mul_0_absorb. inversion H11. inversion H5.
           eapply consistent_bin; eauto.
           inversion H12. eauto.
           eapply consistent_bin; eauto. inversion H12. auto. auto.
           eapply tensor_consistent_step. eauto.
           inversion H1. simpl in *. lia.
           inversion H1. simpl in *. lia.
    + unfold get.
      rewrite mul_bin_distr. auto.
    + inversion H12. lia.
Qed.
    
Lemma get_sum_helper {X} `{TensorElem X} : forall n f I s m,
    (forall x, m <= x /\ x < m + Z.of_nat (S n) -> consistent (f x) s)%Z ->
    sum_helper (S n) m (fun i => f i _[I]) = (sum_helper (S n) m f) _[I].
Proof.
  induction n; intros.
  - simpl. rewrite bin_null_id_r.
    rewrite tensor_add_empty_r.
    reflexivity.
  - rewrite simpl_sum_helper.
    erewrite IHn.
    symmetry.
    rewrite simpl_sum_helper.
    erewrite get_bin_distr.
    reflexivity.
    apply H0. zify. lia.
    eapply consistent_sum_helper.
    intros.
    apply H0. zify. lia.
    intros.
    apply H0. zify. lia.
Qed.

Lemma sum_helper_add_const {X} `{TensorElem X} : forall m n f k,
    sum_helper m (n+k) f = sum_helper m n (fun x => f (x+k)%Z).
Proof.
  induction m; intros. reflexivity.
  simpl. f_equal. erewrite IHm. f_equal.
  eapply functional_extensionality. intros. f_equal. lia.
Qed.

Lemma length_sum_helper {X} `{TensorElem X} :
  forall m n k (f : Z -> list X) s,
    (forall x : Z, (n <= x)%Z -> (x < n + Z.of_nat (S m))%Z ->
                   consistent (f x) (k,s)) ->
    length (sum_helper (S m) n f) = k.
Proof.
  induction m; intros.
  - simpl. erewrite tensor_add_empty_r.
    erewrite consistent_length. eauto. eapply H0. lia. lia.
  - simpl in *. unfold tensor_add in *.
    specialize IHm with (f:=inc f) (s:=s) (n:=n).
    repeat rewrite gen_length in *.
    erewrite (consistent_length (f n)) in *.
    2: { eapply H0. lia. lia. }
    erewrite (consistent_length (f (n+1)%Z)) in *.
    2: { eapply H0. lia. lia. }
    repeat erewrite gen_length in *. repeat rewrite Nat2Z.id in *.
    2: { eapply H0. lia. lia. }
    rewrite max_assoc. rewrite max_id.    
    erewrite IHm. eauto.
    intros. eapply H0. lia. lia.
Qed.    

Theorem sum_helper_cons_split {X} `{TensorElem X} :
  forall m n f (g : Z -> list X) s k,
    (forall x : Z, (n <= x)%Z -> (x < n + Z.of_nat (S m))%Z ->
                   consistent (g x) (k,s)) ->
    sum_helper (S m) n (fun x => f x :: g x) =
    sum_helper (S m) n f :: sum_helper (S m) n g.
Proof.
  simpl.
  induction m; intros.
  - simpl. rewrite bin_null_id_r.
    rewrite tensor_add_empty_r. rewrite tensor_add_empty_r. reflexivity.
  - simpl in *.
    specialize (IHm n (inc f) (inc g) s k). simpl in IHm.
    rewrite IHm.
    rewrite tensor_add_step. reflexivity.
    unfold tensor_add. erewrite gen_length. rewrite Nat2Z.id.    
    2: { intros. eapply H0. lia. lia. }
    assert (n <= n)%Z by lia.
    assert (n <= n+1)%Z by lia.
    eapply H0 in H1,H2. 2: lia. 2: lia.
    erewrite consistent_length. 2: eauto.
    erewrite consistent_length. 2: eauto.
    destruct m. simpl. lia.
    erewrite length_sum_helper. rewrite max_id. eauto.
    intros. eapply H0. lia. lia.
Qed.

Theorem sum_helper_gen_helper_swap {X} `{TensorElem X} :
  forall a b m n f s,
    0 < b ->
    (forall (x y : Z), (n <= x)%Z -> (x < n + Z.of_nat b)%Z ->
                       (m <= y)%Z -> (y < m + Z.of_nat a)%Z ->
                   consistent (f y x) s) ->    
    gen_helper a m  (fun x => sum_helper b n (fun y => (f x y))) =
    sum_helper b n (fun y => gen_helper a m (fun x => (f x y))).
Proof.
  induction a.
  - intros. simpl. rewrite (@sum_helper_const (list X)). reflexivity.
  - induction b.
    * intros. lia.
    * intros. specialize (IHa (S b) m n).
      simpl (fun y => gen_helper (S a) m (fun x : Z => f x y)).
      destruct a. simpl.
      { unfold tensor_add. simpl.
        destruct b. simpl. rewrite max_l by lia. unfold gen,genr.
        simpl. unfold get. simpl. reflexivity.
        erewrite length_sum_helper.
        2: { intros. econstructor. eapply H1; lia. econstructor.
             simpl. reflexivity. }
        rewrite max_id. unfold gen,genr. simpl.
        unfold get at 1. simpl. f_equal. f_equal.
        pose proof get_bin_distr.
        specialize (H2 ([ f m (n+1)%Z])).
        specialize H2 with (I:=0%Z). simpl in H2.
        destruct b.
        { simpl. unfold tensor_add. simpl. rewrite max_l by lia. simpl.
          unfold gen,genr. simpl. unfold get. simpl. eauto. }
        erewrite H2.
        2: { econstructor. eapply H1; lia. econstructor. reflexivity. }
        unfold get at 1. simpl. destruct b. simpl. unfold get. reflexivity.
        f_equal.
        pose proof get_bin_distr.
        specialize (H2 ([ f m (n+1+1)%Z])).
        specialize H3 with (I:=0%Z). simpl in H3.        
        erewrite H3.
        erewrite <- get_sum_helper. reflexivity.        
        intros. econstructor. eapply H1; lia. econstructor. simpl.
        reflexivity. simpl. econstructor. eapply H1; lia.
        econstructor. reflexivity.
        pose proof (@consistent_sum_helper (list X) _
                      b n
                      (1,s) (fun x' : Z => [f m (x' + 1 + 1 + 1)%Z])).
        simpl length. eapply H4. intros.
        econstructor. eapply H1; lia. econstructor; eauto. eauto.
        pose proof (@consistent_sum_helper (list X) _
                      b n
                      (1,s) (fun x' : Z => [f m (x' + 1 + 1)%Z])).
        simpl length. eapply H3. intros.
        econstructor. eapply H1; lia. econstructor; eauto. eauto.
      }
      destruct b.
      { simpl. rewrite tensor_add_empty_r. repeat rewrite bin_null_id_r.
        f_equal. f_equal. eapply gen_helper_eq_bound. intros.
        rewrite bin_null_id_r. eauto. }
      erewrite sum_helper_cons_split.
      2: { intros. eapply consistent_gen_helper. lia.
           intros. eapply H1. lia. lia. lia. lia. }
      specialize (IHa (fun x y => f (x+1)%Z y)).
      peel_hyp.
      erewrite <- IHa.
      destruct b; reflexivity. lia.
      intros. eapply H1. lia. lia. lia. lia.
Qed.

Theorem sum_helper_swap {X} `{TensorElem X} : forall a b m n f,
  sum_helper a m  (fun x => sum_helper b n (fun y => (f x y))) =
  sum_helper b n (fun y => sum_helper a m (fun x => (f x y))).
Proof.
  induction a; induction b; intros.
  - reflexivity.
  - simpl. rewrite sum_helper_const. rewrite bin_null_id_r. reflexivity.
  - simpl. rewrite sum_helper_const. rewrite bin_null_id_r. reflexivity.
  - simpl.
    rewrite <- bin_assoc. rewrite <- bin_assoc. f_equal.
    rewrite sum_bin_split.
    rewrite bin_assoc.
    rewrite (bin_comm (sum_helper b n (inc f m)) (sum_helper a m (fun x : Z => f (x + 1)%Z n))).
    rewrite <- bin_assoc. f_equal.
    rewrite sum_bin_split. f_equal.
    apply IHa.
Qed.

Lemma sum_swap {X} `{TensorElem X} : forall a b f,
  SUM [ x < a ] SUM [ y < b ] f x y =
  SUM [ y < b ] SUM [ x < a ] f x y.
Proof. intros. apply sum_helper_swap. Qed.

Theorem sum_gen_swap {X} `{TensorElem X} : forall a b f s,
    (0 < b)%Z ->
    (forall x y : Z,
        (0 <= x)%Z ->
        (x < 0 + Z.of_nat (Z.to_nat b))%Z ->
        (0 <= y)%Z -> (y < a)%Z ->
        consistent (f y x) s) ->
    GEN [ x < a ] SUM [ y < b ] f x y =
    SUM [ y < b ] GEN [ x < a ] f x y.
Proof.
  intros. unfold gen, genr, sum, sumr.
  autorewrite with crunch. repeat rewrite Z.sub_0_r. simpl.
  eapply sum_helper_gen_helper_swap. lia. intros. apply H1; lia.
Qed.

Lemma nth_error_some_consistent {X} `{TensorElem X} : forall v x i s n,
    nth_error v i = Some x ->
    consistent v (n,s) ->
    consistent x s.
Proof.
  intros.
  inversion H1.
  apply nth_error_In in H0.
  assert (Forall (fun x : X => consistent x s) (x0::xs)). eauto.
  eapply Forall_forall in H8.
  eauto. subst. eauto.
Qed.

Lemma get_sum {X} `{TensorElem X} : forall n f I s,
    (0 < n)%Z ->
    (forall x, 0 <= x /\ x < n -> consistent (f x) s)%Z ->
    SUM [ i < n ] (f i) _[I] = (SUM [ i < n ] f i) _[I].
Proof.
  intros.
  unfold sum, sumr.
  rewrite Z.sub_0_r.
  destruct n; try auto with crunch.
  simpl. posnat.
  eapply get_sum_helper.
  intros. apply H1. zify. lia.
Qed.

Theorem bin_gen_helper {X} `{TensorElem X} : forall n f g,
  tensor_add (gen_helper n 0 (fun i : Z => f i))
    (gen_helper n 0 (fun i : Z => g i)) =
  gen_helper n 0 (fun i : Z => f i <+> g i).
Proof.
  induction n; intros.
  - simpl.
    rewrite tensor_add_empty_r.
    reflexivity.
  - simpl.
    rewrite tensor_add_step.
    f_equal.
    apply IHn.
    repeat erewrite gen_helper_length. auto.
Qed.

Theorem bin_gen {X} `{TensorElem X} : forall n f g,
    (GEN [ i < n ] f i) <+> (GEN [ i < n ] g i) =
    GEN [ i < n ] f i <+> g i.
Proof.
  unfold gen, genr.
  intros. rewrite Z.sub_0_r.
  apply bin_gen_helper.
Qed.

Lemma get_guard {X} `{TensorElem X} : forall I N (v : list X) s,
    consistent v (Z.to_nat N,s) ->
    v _[ I ] =
    (|[ (I <? N) && (0 <=? I) ]| v _[I]).
Proof.
  intros. analyze_bool; simpl.
  - rewrite true_iverson. reflexivity.
  - inversion H0.
    rewrite get_neg_null; auto with crunch.
    unfold iverson.
    symmetry. apply mul_0_idemp.
  - unfold iverson. simpl.
    inversion H0.
    rewrite get_znlt_null; auto with crunch.
    unfold iverson. symmetry.
    apply mul_0_idemp.
  - assert (N < 0)%Z by lia.
    destruct N. lia. zify. lia. simpl in H0.
    inversion H0. inversion H9.
Qed.

Lemma get_guard_of_nat {X} `{TensorElem X} : forall I N (v : list X) s,
    consistent v (N,s) ->
    v _[ I ] =
    (|[ (I <? Z.of_nat N) && (0 <=? I) ]| v _[I]).
Proof.
  intros. analyze_bool; simpl.
  - rewrite true_iverson. reflexivity.
  - inversion H0.
    rewrite get_neg_null; auto with crunch.
    unfold iverson.
    symmetry. apply mul_0_idemp.
  - unfold iverson. simpl.
    inversion H0.
    rewrite get_znlt_null; auto with crunch.
    unfold iverson. symmetry.
    apply mul_0_idemp.
Qed.

Lemma get_guard_R : forall n a (v : list R),
    (Z.of_nat (length v) < a)%Z ->
    v _[ n ] =
    (|[ (n <? a) && (0 <=? n) ]| v _[n]).
Proof.
  intros. analyze_bool; simpl; try ring.
  - unfold iverson. rewrite mul_1_id. auto.
  - unfold iverson. simpl.
    rewrite get_neg_zero; auto with crunch.
  - unfold iverson. simpl.
    rewrite get_znlt_zero; auto with crunch.
Qed.

Lemma guard_eq_mul : forall p a b,
    a = (|[ p ]| a) \/ b = (|[ p ]| b) ->
    (a * b)%R = |[ p ]| (a * b)%R.
Proof.
  intros. destruct H; destruct p.
  - now rewrite true_iverson.
  - unfold iverson in *. simpl in *.
    rewrite H. ring.
  - now rewrite true_iverson.
  - unfold iverson in *. simpl in *.
    rewrite H. ring.
Qed.

Lemma get_forall {X} `{TensorElem X} :
  forall P l n,
    (0 <= n)%Z -> (n < Z.of_nat (length l))%Z ->
    Forall P l ->
    P (l _[n]).
Proof.
  induction l; intros.
  - simpl in *. lia.
  - destruct n eqn:en.
    + simpl. inversion H2. assumption.
    + inversion H2. subst.
      destruct l.
      * unfold get. simpl in *. posnat. simpl. destruct pn. zify. lia.
        zify. lia.
      * unfold get.
        simpl. posnat.
        simpl.
        specialize (IHl (Z.of_nat pn)).
        peel_hyp.
        unfold get in IHl.
        destruct (Z.of_nat pn) eqn:e.
        simpl in *. destruct pn. simpl. auto. zify. lia.
        rewrite <- e in IHl.
        rewrite Nat2Z.id in IHl.
        assert (pn < length (x::l)).
        {
          simpl in *. zify. lia.
        }
        apply nth_error_Some in H3.
        destruct (nth_error (x::l) pn) eqn:ee. auto. contradiction.
        zify. lia.
        simpl in *. zify. lia. auto.
    + simpl in H1. lia.
Qed.                               

Hint Extern 5 => match goal with
                   |- context[ length (_ _[_]) ] => apply get_forall
                 end : crunch.

Lemma consistent_get {X} `{TensorElem X} : forall n (l : list X) s m,
    consistent l (m,s) ->
    consistent (l _[n]) s.
Proof.
  intros.
  destruct (0<=?n)%Z eqn:n0; destruct (n<?Z.of_nat (length l))%Z eqn:nll.
  - unbool. apply get_forall; auto. destruct l. constructor. inversion H0.
    constructor. auto. auto.
  - unbool. destruct l. inversion H0.
    inversion H0. unfold iverson. subst.
    rewrite get_znlt_null; try lia.
    apply consistent_mul. auto.
  - unbool. destruct l. inversion H0.
    inversion H0. unfold iverson. rewrite get_neg_null; try lia.
    apply consistent_mul. auto.
  - unbool. lia.
Qed.

Hint Resolve guard_eq_mul : crunch.

Lemma gen_get_gen_swap {X} `{TensorElem X} :
  forall W I RR (f : Z -> Z -> X),
    (I < W)%Z ->
    (0 <= I)%Z ->
    GEN [ z < RR ] (GEN [ z0 < W ] f z z0) _[ I ] =
    (GEN [ p < W ] GEN [ r < RR ] f r p) _[ I ].
Proof.
  intros.
  rewrite get_gen_some; auto with crunch.
  apply gen_eq_bound; intros.
  rewrite get_gen_some; auto with crunch.
Qed.

Lemma gen_neg_empty {X} `{TensorElem X} : forall n f,
    (n < 0)%Z ->
    GEN [ i < n ] f i = [].
Proof.
  intros. destruct n.
  - lia.
  - specialize (Zgt_pos_0 p). intros.
    lia.
  - reflexivity.
Qed.

Fixpoint map2 {X Y Z : Set} (f : X -> Y -> Z) (l1 : list X) (l2 : list Y) :=
  match l1,l2 with
  | x::xs, y::ys => f x y :: (map2 f xs ys)
  | _,_ => []
  end.             

Lemma gen_helper_mul_distr : forall n f g,
    gen_helper n 0%Z (fun x => (f x * g x)%R) =
    map2 Rmult (gen_helper n 0%Z f) (gen_helper n 0%Z g).
Proof.
  induction n; intros.
  - reflexivity.
  - simpl.
    f_equal.
    apply IHn.
Qed.

Lemma gen_mul_distr : forall n f g,
    GEN [ x < n ] (f x * g x)%R =
    map2 Rmult (GEN [ i < n ] f i) (GEN [ i < n ] g i).
Proof. intros. apply gen_helper_mul_distr. Qed.

Lemma tensor_consistent_forall_consistent {X} `{TensorElem X} :
  forall s (l : list X),
    consistent l (length l,s) -> Forall (fun x => consistent x s) l.
Proof.
  intros.
  inversion H0. subst.
  constructor. auto. auto.
Qed.
Hint Resolve tensor_consistent_forall_consistent : crunch.

Lemma Forall_split {X} `{TensorElem X} : forall (l : list X) P Q,
  Forall (fun x => P x /\ Q x) l <->
  Forall P l /\ Forall Q l.
Proof.
  split; induction l; intros; try split; try constructor.
  - inversion H0. tauto. 
  - inversion H0. eapply Forall_impl with
                      (P:= (fun x : X => P x /\ Q x)).
    intros. tauto. auto.
  - inversion H0. tauto.
  - inversion H0. eapply Forall_impl with
                      (P:= (fun x : X => P x /\ Q x)).
    intros. tauto. auto.
  - destruct H0. inversion H0. inversion H1. split; auto.
  - apply IHl.
    destruct H0.
    inversion H0. inversion H1. split; auto.
Qed.

Lemma gen_helper_forall {X} `{TensorElem X} : forall n m f P,
  Forall P (gen_helper n m f) <->
  (forall x, m <= x -> x < m + Z.of_nat n -> P (f x))%Z.
Proof.
  split; intros.
  - pose proof (get_gen_helper_some n m f (x-m)%Z).
    peel_hyp.
    rewrite Z.sub_simpl_r in H3.
    rewrite <- H3.
    eapply get_forall. lia. rewrite gen_helper_length.
    lia. apply H0. auto with crunch.
  - generalize dependent f.
    induction n; intros.
    + constructor.
    + simpl. constructor. apply H0; zify; lia.
      apply IHn.
      intros.
      apply H0; zify; lia.
Qed.

Lemma genr_forall {X} `{TensorElem X} : forall n m f P,
  Forall P (GEN [ m <= i < n ] f i) <->
  (forall x, m <= x -> x < n -> P (f x) )%Z.
Proof.
  unfold genr.
  intros.
  pose proof (gen_helper_forall (Z.to_nat (n-m)%Z) m f P).
  destruct (0 <? n-m)%Z eqn:nm; unbool.
  - rewrite Z2Nat.id in H0 by lia.
    rewrite Zplus_minus in H0.
    apply H0.
  - destruct (n-m)%Z eqn:e; split; intros; zify; try lia; try constructor.
Qed.

Lemma gen_forall {X} `{TensorElem X} : forall n f P,
    Forall P (GEN [ i < n ] f i) <->
    (forall x, 0 <= x -> x < n -> P (f x) )%Z.
Proof.
  intros. unfold gen.
  apply genr_forall.
Qed.

Lemma gen_get_id {X} `{TensorElem X} : forall l N,
    Z.to_nat N = length l ->
    GEN [ i < N ] l _[i] = l.
Proof.
  induction l; intros.
  - simpl in H0.
    destruct N; auto. simpl in * |-. lia.
  - simpl in H0.
    unfold gen, genr.
    rewrite Z.sub_0_r.
    rewrite H0.
    simpl.
    f_equal.
    specialize (IHl (Z.of_nat (length l))).
    rewrite Nat2Z.id in IHl.
    peel_hyp.
    unfold gen, genr in IHl.
    rewrite Z.sub_0_r in IHl. rewrite Nat2Z.id in IHl.
    rewrite <- IHl at 2.
    apply gen_helper_eq_bound. intros.
    rewrite Z.add_0_r.
    replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) by (zify; lia).
    unfold get. simpl.
    rewrite SuccNat2Pos.id_succ.
    simpl.
    unfold get.
    destruct l. simpl in *. lia.
    destruct (Z.of_nat i) eqn:e. simpl. destruct i. reflexivity. zify. lia.
    rewrite <- e.
    rewrite Nat2Z.id.
    apply nth_error_Some in H2. destruct (nth_error (x::l) i). auto.
    contradiction.
    zify. lia.
Qed.

Lemma gen_of_nat_get_id {X} `{TensorElem X} : forall l N,
    N = length l ->
    GEN [ i < Z.of_nat N ] l _[i] = l.
Proof.
  intros.
  apply gen_get_id.
  rewrite Nat2Z.id. auto.
Qed.

Lemma gen_of_nat_get_id' {X} `{TensorElem X} :
  forall (l : list X) (n n' : nat) s,
    consistent l (n',s) ->
    n = n' ->
    GEN [ i < Z.of_nat n ] l _[i] = l.
Proof.
  intros.
  apply gen_get_id.
  rewrite Nat2Z.id.
  inversion H0. subst. auto.
Qed.

Lemma gen_helper_bin {X} `{TensorElem X} : forall n m f g,
    (gen_helper n m f) <+> (gen_helper n m g) =
    gen_helper n m (fun i => (f i) <+> (g i)).
Proof.
  induction n; intros.
  - reflexivity.
  - simpl.
    rewrite tensor_add_step. f_equal.
    apply IHn.
    repeat erewrite gen_helper_length. eauto.
Qed.

Lemma tensor_gen_bin {X} `{TensorElem X} : forall n m f g,
    n = m ->
    bin (GEN [ i < n ] f i) (GEN [ i < m ] g i) =
    GEN [ i < n ] bin (f i) (g i).
Proof.
  intros. destruct n; subst.
  - reflexivity.
  - unfold gen, genr. rewrite Z.sub_0_r. simpl. posnat.
    rewrite <- gen_helper_bin. reflexivity.
  - reflexivity.
Qed.

Hint Extern 4 => rewrite gen_of_nat_length : crunch.
Hint Extern 4 => rewrite get_gen_of_nat_some : crunch.

Lemma get_length {X} `{TensorElem X} : forall (v : list (list X)) i n m s,
    consistent v (n,(m,s)) ->
    length (v _[i]) = m.
Proof.
  intros.
  destruct v. inversion H0.
  inversion H0.
  destruct (0 <=? i)%Z eqn:i0;
    destruct (i <? Z.of_nat (length (l :: v)))%Z eqn:iv;
    unbool_hyp.
  - subst.
    apply get_forall. auto. auto.
    inversion H6.
    constructor.
    inversion H5. auto.
    constructor.
    constructor. inversion H0.
    inversion H10. auto.
    constructor.
    inversion H1. auto.
    eapply Forall_impl in H2.
    apply H2.
    intros. simpl.
    inversion H4. auto.
  - rewrite get_znlt_null by lia.
    rewrite iverson_length.
    inversion H5. auto.
  - rewrite get_neg_null by auto.
    rewrite iverson_length.
    inversion H5. auto.
  - lia.
Qed.

Lemma get_length_pos {X} `{TensorElem X} : forall v i s,
    consistent v s ->
    0 < length (v _[i]).
Proof.
  intros.
  destruct v. inversion H0.
  inversion H0.
  destruct s. inversion H5. subst.
  destruct l. inversion H3.
  destruct s.
  erewrite get_length; try eassumption.
  inversion H3.
  rewrite <- H10.
  simpl. lia.
Qed.
Hint Resolve get_length_pos : crunch.

Lemma bool_imp_elim : forall a b,
    (a = true -> b = true) ->
    a && b = a.
Proof. destruct a; auto. Qed.

Lemma all_R_consistent : forall r : R, consistent r tt.
  intros. reflexivity. Qed.


Definition flatten_trunc {X} `{TensorElem X} k (t : list (list X)) :=
    let n := Z.of_nat (length t) in
    let m := Z.of_nat (length (t _[0])) in
    GEN [ i < Z.of_nat k ]
        SUM [ j < n ]
        SUM [ k < m ] (|[ i =? j * m + k ]| t _[ j ; k ]).

Definition flatten {X} `{TensorElem X} (t : list (list X)) : list X :=
    let n := Z.of_nat (length t) in
    let m := Z.of_nat (length (t _[0])) in
    GEN [ i < n * m ]
        SUM [ j < n ]
        SUM [ k < m ] (|[ i =? j * m + k ]| t _[ j ; k ]).

Definition tile {X} `{TensorElem X} (t : list X) (n : nat) : list (list X) :=
  GEN [ i < (Z.of_nat (length t)) // (Z.of_nat n) ]
  GEN [ j < Z.of_nat n ]
    |[ i * (Z.of_nat n) + j <? Z.of_nat (length t) ]|
    t _[ i * (Z.of_nat n) + j ].

Definition transpose {X} `{TensorElem X} (v : list (list X)) :=
  GEN [ x < Z.of_nat (length (v _[0])) ]
      GEN [ y < Z.of_nat (length v) ]
      v _[y;x].

Definition trunc_r {X} `{TensorElem X} k v :=
  GEN [ i < Z.of_nat k ] v _[i].

Definition trunc_l {X} `{TensorElem X} k v :=
  GEN [ i < Z.of_nat k ] v _[i + (Z.of_nat (length v - k)) ].

Definition truncr {X} `{TensorElem X} k v :=
  GEN [ i < Z.of_nat (length v - k) ] v _[i].

Definition truncl {X} `{TensorElem X} k v :=
  GEN [ i < Z.of_nat (length v - k) ] v _[i + (Z.of_nat k) ].

Definition pad_r_unsafe {X} `{TensorElem X} k v :=
  GEN [ i < Z.of_nat (length v + k) ] v _[i].

Definition pad_l_unsafe {X} `{TensorElem X} k v :=
  GEN [ i < Z.of_nat (length v + k) ] v _[i - Z.of_nat k].

Definition pad_r {X} `{TensorElem X} k v :=
  GEN [ i < Z.of_nat (length v + k) ]
 |[ i <? Z.of_nat (length v) ]| v _[i].

Definition pad_l {X} `{TensorElem X} k v :=
    GEN [ i < Z.of_nat (length v + k) ]
   |[ Z.of_nat k <=? i ]| v _[i - Z.of_nat k ].

Lemma trunc_r_eq {X} `{TensorElem X} : forall u v k,
    u = v ->
    trunc_r k u = trunc_r k v.
Proof. intros. subst. reflexivity. Qed.

Lemma trunc_l_eq {X} `{TensorElem X} : forall u v k,
    u = v ->
    trunc_l k u = trunc_l k v.
Proof. intros. subst. reflexivity. Qed.

Lemma truncr_eq {X} `{TensorElem X} : forall u v k,
    u = v ->
    truncr k u = truncr k v.
Proof. intros. subst. reflexivity. Qed.

Lemma truncl_eq {X} `{TensorElem X} : forall u v k,
    u = v ->
    truncl k u = truncl k v.
Proof. intros. subst. reflexivity. Qed.

Lemma trunc_r_truncr {X} `{TensorElem X} : forall v k,
    k <= length v ->
    trunc_r k v = truncr (length v - k) v.
Proof.
  unfold trunc_r,truncr. intros.
  f_equal. lia.
Qed.

Lemma trunc_l_truncl {X} `{TensorElem X} : forall v k,
    k <= length v ->
    trunc_l k v = truncl (length v - k) v.
Proof.
  unfold trunc_l,truncl. intros.
  f_equal. lia.
Qed.

Lemma pad_r_eq {X} `{TensorElem X} : forall u v k,
    u = v ->
    pad_r k u = pad_r k v.
Proof. intros. subst. reflexivity. Qed.

Lemma pad_l_eq {X} `{TensorElem X} : forall u v k,
    u = v ->
    pad_l k u = pad_l k v.
Proof. intros. subst. reflexivity. Qed.

Lemma tile_eq {X} `{TensorElem X} : forall u v m,
    u = v -> tile u m = tile v m.
Proof.
  intros. subst. reflexivity.
Qed.

Lemma flatten_trunc_eq {X} `{TensorElem X} : forall u v m n,
    u = v -> 
    n = m ->
    flatten_trunc n u = flatten_trunc m v.
Proof.
  intros. subst. reflexivity.
Qed.

Lemma flatten_eq {X} `{TensorElem X} : forall u v,
    u = v ->
    flatten u = flatten v.
Proof.
  intros. subst. reflexivity.
Qed.

Lemma transpose_eq {X} `{TensorElem X} : forall u v,
    u = v ->
    transpose u = transpose v.
Proof.
  intros. subst. reflexivity.
Qed.

Theorem consistent_flatten {X} `{TensorElem X} :
  forall n m (l : list (list X)) s,
    consistent l (n,(m,s)) ->
    consistent (flatten l) (m*n,s).
Proof.
  intros.
  unfold flatten.
  destruct l. inversion H0.
  inversion H0.
  destruct l. inversion H5.
  inversion H0. subst.

  rewrite <- Nat2Z.inj_mul.
  apply consistent_gen. simpl.
  apply lt_0_succ.

  intros. simpl length in *.
  apply consistent_sum; simpl. lia.
  intros.
  apply consistent_sum. lia.
  intros.
  apply consistent_iverson.
  inversion H5. rewrite <- H18 in *. clear H18. subst.
  eapply consistent_get.
  eapply consistent_get. eauto.
  
  simpl in *. inversion H14. inversion H5. rewrite <- H9. subst.
  simpl. f_equal.
  rewrite mul_comm. simpl.
  rewrite (mul_comm _ (S _)).
  simpl.
  repeat rewrite add_assoc.
  rewrite add_comm. rewrite (add_comm _ (_ * _)).
  rewrite mul_comm.
  f_equal.
  apply add_comm.
Qed.

Theorem consistent_tile {X} `{TensorElem X} :
  forall (l : list X) n c (s : @shape X _),
    consistent l (n, s) ->
    0 < c ->
    consistent (tile l c)
    (Z.to_nat ((Z.of_nat n // (Z.of_nat c))), (c, s)).
Proof.
  intros.
  unfold tile.
  rewrite znat_id_distr.
  repeat rewrite Nat2Z.id.
  inversion H0. subst.
  simpl length.
  rewrite of_nat_div_distr.
  apply @consistent_gen; auto with crunch.
  intros.
  apply @consistent_gen; auto with crunch.
  intros.
  apply consistent_iverson.
  eapply consistent_get.
  eauto.
Qed.

Theorem consistent_flatten_trunc {X} `{TensorElem X} :
  forall k (v : list (list X)) n m s,
    0 < k ->
    consistent v (n,(m,s)) ->
    consistent (flatten_trunc k v) (k,s).
Proof.
  unfold flatten_trunc.
  intros. pose proof H1. inversion H1. inversion H5.
  apply @consistent_gen; auto.
  intros.
  apply consistent_sum. simpl. zify. lia.
  intros.
  apply consistent_sum. rewrite get_0_cons. simpl. zify. lia.
  intros.
  apply consistent_iverson.
  eapply consistent_get.
  eapply consistent_get.
  subst. eauto.
Qed.

Theorem length_of_flatten_trunc {X} `{TensorElem X} :
    forall k (v : list (list X)) n m s,
    0 < k ->
    consistent v (n,(m,s)) ->
    length (flatten_trunc k v) = k.
Proof.
  intros. pose proof (consistent_flatten_trunc _ _ _ _ _ H0 H1).
  inversion H2. auto.
Qed.

Theorem length_of_tile {X} `{TensorElem X} :
  forall (l : list X) n c (s : @shape X _),
    consistent l (n, s) ->
    0 < c ->
    length (tile l c) =
    (Z.to_nat ((Z.of_nat n // (Z.of_nat c)))).
Proof.
  intros. pose proof (consistent_tile l n c s H0 H1).
  inversion H2. auto.
Qed.

Theorem consistent_transpose {X} `{TensorElem X} :
  forall (v : list (list X)) n m s,
    consistent v (n,(m,s)) ->
    consistent (transpose v) (m,(n,s)).
Proof.
  intros.
  inversion H0.
  inversion H3.
  subst.
  unfold transpose.
  rewrite get_0_cons.
  eapply @consistent_gen. simpl. auto with crunch.
  intros. apply consistent_gen. simpl.
  auto with crunch. intros.
  eapply consistent_get.
  eapply consistent_get.
  eauto.
  auto. auto.
Qed.

Theorem consistent_trunc_r {X} `{TensorElem X} :
  forall (v : list X) n k s,
    0 < k ->
    consistent v (n,s) ->
    consistent (trunc_r k v) (k,s).
Proof.
  intros. unfold trunc_r.
  apply consistent_gen. auto.
  intros. eapply consistent_get.
  eauto. auto.
Qed.

Theorem consistent_trunc_l {X} `{TensorElem X} :
  forall (v : list X) n k s,
    0 < k ->
    consistent v (n,s) ->
    consistent (trunc_l k v) (k,s).
Proof.
  intros. unfold trunc_l.
  apply consistent_gen. auto.
  intros. eapply consistent_get.
  eauto. auto.
Qed.

Theorem consistent_truncr {X} `{TensorElem X} :
  forall (v : list X) n k s,
    0 < n - k ->
    consistent v (n,s) ->
    consistent (truncr k v) (n-k,s).
Proof.
  intros. unfold truncr.
  apply consistent_gen.
  erewrite consistent_length; eauto. 
  intros. eapply consistent_get.
  eauto. erewrite consistent_length; eauto. 
Qed.

Theorem consistent_truncl {X} `{TensorElem X} :
  forall (v : list X) n k s,
    0 < n - k ->
    consistent v (n,s) ->
    consistent (truncl k v) (n-k,s).
Proof.
  intros. unfold truncl.
  apply consistent_gen.
  erewrite consistent_length; eauto. 
  intros. eapply consistent_get.
  eauto. erewrite consistent_length; eauto. 
Qed.

Theorem consistent_pad_l {X} `{TensorElem X} :
  forall (v : list X) n k s,
    0 < k ->
    consistent v (n,s) ->
    consistent (pad_l k v) (k+n,s).
Proof.
  intros. unfold pad_l.
  apply consistent_gen. lia. 
  intros. apply consistent_iverson. eapply consistent_get.
  eauto. inversion H1. rewrite H7. lia.
Qed.

Theorem consistent_pad_r {X} `{TensorElem X} :
  forall (v : list X) n k s,
    0 < k ->
    consistent v (n,s) ->
    consistent (pad_r k v) (k+n,s).
Proof.
  intros. unfold pad_r.
  apply consistent_gen. lia. 
  intros. apply consistent_iverson. eapply consistent_get.
  eauto. inversion H1. rewrite H7. lia.
Qed.

Lemma guard_comp_to_eq : forall k l i i1,
    (0 <= i)%Z ->
    (i < Z.of_nat l)%Z ->
    0 < k ->
    (0 <= i1)%Z ->
    (i1 < Z.of_nat (l //n k))%Z ->
    (((i - i1 * Z.of_nat k <? Z.of_nat k)
        && (0 <=? i - i1 * Z.of_nat k))%Z = (i1 =? i / Z.of_nat k)%Z).
Proof.
  intros.

  pose proof (Z.div_mod i (Z.of_nat k)). peel_hyp.
  pose proof (div_eucl_div i (Z.of_nat k)).
  destruct (Z.div_eucl i (Z.of_nat k)). peel_hyp.
  remember (Z.of_nat k) as zk.
  remember (i mod zk)%Z as r.
  etransitivity.

  match goal with
    |- _ = ?e => remember e
  end.
  rewrite H4.
  rewrite Z.mul_comm.
  rewrite Z.add_sub_swap.
  rewrite <- Z.mul_sub_distr_r.
  
  replace (0 <=? (i / zk - i1) * zk + r)%Z with
      (0 <=? (i / zk - i1))%Z.
  2:
  {
    unbool; split; intros.
    - apply Z.add_nonneg_nonneg.
      apply Z.mul_nonneg_nonneg. auto. subst. auto with crunch.
      subst.
      pose proof (Z.mod_pos_bound i (Z.of_nat k)). peel_hyp. auto with crunch.
    - destruct (0 <=? i/zk - i1)%Z eqn:e; unbool_hyp.
      + auto.
      + assert ((i / zk - i1) * zk <= - zk)%Z .
        apply Zle_0_minus_le.
        replace (-zk)%Z with ((-1)*zk)%Z by lia.
        rewrite <- Z.mul_sub_distr_r.
        apply Z.mul_nonneg_nonneg; try lia.
        assert (r < zk)%Z.
        pose proof (Z.mod_pos_bound i zk). peel_hyp. lia.
        assert (-zk + r < 0)%Z. lia.
        assert ((i / zk - i1) * zk + r < 0)%Z. lia.
        lia.
  }

  replace ((i / zk - i1) * zk + r <? zk)%Z with
      ((i / zk - i1) <=?0)%Z.
  2:
    {
    pose proof (Z.mod_pos_bound i zk). peel_hyp. 
    assert (r < zk)%Z.
    lia.

    unbool; split; intros.
    - destruct (i/zk -i1 =? 0)%Z eqn:e; unbool_hyp.
      + rewrite e in *.
        rewrite Z.mul_0_l.
        rewrite Z.add_0_l. auto.
      + assert ((i / zk - i1) < 0)%Z by lia. clear H8. clear e.
        assert ((i / zk - i1) * zk <= - zk)%Z .
        apply Zle_0_minus_le.
        replace (-zk)%Z with ((-1)*zk)%Z by lia.
        rewrite <- Z.mul_sub_distr_r.
        apply Z.mul_nonneg_nonneg; try lia.
        eapply (Zplus_le_compat_r _ _ r) in H8.
        assert (-zk + r < zk)%Z by lia.
        lia.
    - destruct (i/zk - i1 <=? 0)%Z eqn:e; unbool_hyp.
      + auto.
      + assert (zk <= (i / zk - i1) * zk)%Z.
        apply Zle_0_minus_le.
        rewrite <- Z.add_opp_r.
        replace (-zk)%Z with ((-1)*zk)%Z by lia.
        rewrite <- Z.mul_add_distr_r.
        apply Z.mul_nonneg_nonneg; try lia.
        eapply (Zplus_le_compat_r _ _ r) in H9.
        assert (zk + r < zk)%Z by lia.
        pose proof (Z.add_le_mono_l 0 r zk)%Z.
        assert (0 <= r)%Z by lia.
        apply H11 in H12.
        rewrite Z.add_0_r in H12.
        lia.
  }

  replace ((i / zk - i1 <=? 0) && (0 <=? i / zk - i1))%Z with
      (i1 =? i/zk)%Z by (unbool; split; lia).

  rewrite Heqb.
  reflexivity. reflexivity.
Qed.

Theorem consistent_concat {X} `{TensorElem X} : forall (l1 l2 : list X) n m s k,
    0 < n ->
    0 < m ->
    k = n + m ->
    consistent l1 (n,s) ->
    consistent l2 (m,s) ->
    consistent (l1 <++> l2) (k,s).
Proof.
  intros.
  unfold concat.
  inversion H3. inversion H4.
  rewrite H10, H16.
  apply consistent_gen. lia.
  intros.
  eapply consistent_bin.
  eapply consistent_iverson. eapply consistent_get. subst. eauto.
  eapply consistent_iverson. eapply consistent_get. subst. eauto.
  auto. auto.
Qed.

Lemma help {X} `{TensorElem X} : forall (l : list X) i1 i2,
    (i1 < 0)%Z ->
    (i2 < 0)%Z ->
    l _[i1] = l _[i2].
Proof.
  destruct l.
  intros.
  unfold get. reflexivity.
  intros.
  rewrite get_neg_null by lia.
  rewrite get_neg_null by lia.
  reflexivity.
Qed.

Theorem get_concat_l {X} `{TensorElem X} : forall (l1 l2 : list X) n m s i,
    consistent l1 (n,s) ->
    consistent l2 (m,s) ->
    (i < Z.of_nat n)%Z ->
    (0 <= i)%Z ->
    (l1 <++> l2) _[i] = l1 _[i].
Proof.
  intros.
  unfold concat.
  erewrite consistent_length; eauto.
  erewrite consistent_length; eauto.
  rewrite get_gen_some by (zify; lia).
  assert (i<? Z.of_nat n = true)%Z by (unbool; zify; lia).
  rewrite H4. rewrite true_iverson.
  assert (Z.of_nat n <=? i = false)%Z by (unbool; zify; lia).
  rewrite H5.
  unfold iverson. rewrite bin_comm.
  eapply bin_mul_0_id.
  eapply consistent_get. eauto.
  eapply consistent_get. eauto.
  eauto.
Qed.

Theorem get_concat_r {X} `{TensorElem X} : forall (l1 l2 : list X) n m s i,
    consistent l1 (n,s) ->
    consistent l2 (m,s) ->
    (Z.of_nat n <= i)%Z ->
    (i < Z.of_nat (n+m))%Z ->
    (l1 <++> l2) _[i] = l2 _[i - Z.of_nat n].
Proof.
  intros.
  unfold concat.
  erewrite consistent_length; eauto.
  erewrite consistent_length; eauto.
  rewrite get_gen_some by (zify; lia).
  assert ( Z.of_nat n <=? i= true)%Z by (unbool; zify; lia).
  rewrite H4. rewrite true_iverson.
  assert (i<? Z.of_nat n = false)%Z by (unbool; zify; lia).
  rewrite H5.
  unfold iverson.
  eapply bin_mul_0_id.
  eapply consistent_get. eauto.
  eapply consistent_get. eauto.
  eauto.
Qed.

Theorem gen_to_concat {X} `{TensorElem X} : forall f n k s,
    (forall x, consistent (f x) s) ->
    0 < n ->
    0 < k ->
    GEN [ i < Z.of_nat (n+k) ] f i =
    (GEN [ i < Z.of_nat n ] f i) <++>
                                 (GEN [ i < Z.of_nat k] f (i+Z.of_nat n)%Z).
Proof.
  intros.
  unfold concat.
  erewrite consistent_length by
      (apply consistent_gen; eauto).
  erewrite consistent_length by
      (apply consistent_gen; eauto).
  symmetry.
  apply gen_eq_bound; intros.
  destruct (i <? Z.of_nat n)%Z eqn:e; unbool_hyp.
  - rewrite true_iverson.
    assert ((Z.of_nat n <=? i) = false)%Z by (unbool; zify; lia).
    rewrite H5.
    rewrite get_gen_some by lia.
    rewrite bin_comm.
    unfold iverson.
    eapply bin_mul_0_id.
    eapply consistent_get.
    eapply consistent_gen; eauto.
    eauto.
    eauto.
  - assert (Z.of_nat n <=? i = true)%Z by (unbool; auto).
    rewrite H5.
    rewrite true_iverson.
    rewrite bin_comm.
    rewrite get_gen_some.
    rewrite Z.sub_add.
    unfold iverson.
    rewrite bin_comm.
    eapply bin_mul_0_id.
    eapply consistent_get.
    eapply consistent_gen. auto. eauto. eauto. eauto. eauto.
    zify; lia. lia.
Qed.

Theorem guard_split {X} `{TensorElem X} :
  forall a b e,
    (|[ a <? b ]| e) <+> (|[ b <=? a ]| e) = e.
Proof.
  intros.
  destruct (a <? b)%Z eqn:ee.
  - rewrite true_iverson.
    unbool.
    assert ((b <=? a)%Z = false) by (unbool; lia).
    rewrite H0.
    rewrite bin_comm.
    unfold iverson.
    apply bin_mul_0_self_id.
  - assert ((b <=? a)%Z = true) by (unbool; lia).
    rewrite H0.
    rewrite true_iverson.
    unfold iverson.
    apply bin_mul_0_self_id.
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

Theorem gen_nonpos_empty {X} `{TensorElem X} : forall n f,
    (n <=0)%Z ->
    GEN [ i < n ] f i = [].
Proof.
  intros. unfold gen, genr.
  rewrite Z.sub_0_r.
  destruct n; try reflexivity.
  zify. lia.
Qed.

Definition Truncr {X} `{TensorElem X} k l  :=
  truncr (Z.to_nat k) l.

Lemma Truncr_eq {X} `{TensorElem X} : forall k l1 l2,
    l1 = l2 ->
    Truncr k l1 = Truncr k l2.
Proof. intros. subst. eauto. Qed.  

Lemma truncr_Truncr {X} `{TensorElem X} :
  forall l n,
    truncr n l = Truncr (Z.of_nat n) l.
Proof. intros. unfold Truncr. rewrite Nat2Z.id. eauto. Qed.

Lemma minus_plus : forall n m : nat, n + m - n = m. Proof. lia. Qed.


