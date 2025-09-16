From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import ZArith.Zdiv.
From Coq Require Import ZArith.Int.
From Coq Require Import ZArith.Znat.
From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
From Coq Require Import Reals.Reals. Import Rdefinitions. Import RIneq.

Import ListNotations.

From ATL Require Import FrapWithoutSets Div Tactics.
From Lower Require Import Array Zexpr ListMisc Range.

Ltac posnats :=
      repeat match goal with
    | |- context[ Z.pos (Pos.of_succ_nat _)] =>
        rewrite Zpos_P_of_succ_nat
    | H : context[ Z.pos (Pos.of_succ_nat _)] |- _ =>
        rewrite Zpos_P_of_succ_nat in H
    | |- context[Z.succ (Z.of_nat _)] =>
        rewrite <- Nat2Z.inj_succ
    | H : context[Z.succ (Z.of_nat _)] |- _ =>
        rewrite <- Nat2Z.inj_succ in H
    | |- context[Z.to_nat (Z.of_nat _)] =>
        rewrite Nat2Z.id
    | H : context[Z.to_nat (Z.of_nat _)] |- _ =>
        rewrite Nat2Z.id in H
    | |- context[Pos.to_nat (Pos.of_succ_nat _)] =>
        rewrite SuccNat2Pos.id_succ
    | H : context[Pos.to_nat (Pos.of_succ_nat _)] |- _ =>
        rewrite SuccNat2Pos.id_succ in H
    | |- context [Pos.succ (Pos.of_succ_nat _)] =>
        rewrite <- SuccNat2Pos.inj_succ
    | H : context [Pos.succ (Pos.of_succ_nat _)] |- _ =>
        rewrite <- SuccNat2Pos.inj_succ in H
    end.

Inductive scalar_result :=
| SS (r: R)
| SX.

Unset Elimination Schemes.
Inductive result :=
| S (z : scalar_result)
| V (v : list result).
Set Elimination Schemes.

Local Fixpoint result_sz (r : result) :=
  match r with
  | Result.S _ => O
  | V v => Datatypes.S (fold_right Nat.max O (map result_sz v))
  end.

Lemma result_ind P :
  (forall z, P (Result.S z)) ->
  (forall v, Forall P v -> P (V v)) ->
  forall r, P r.
Proof.
  intros * H1 H2 r. remember (result_sz r) as sz eqn:E.
  assert (Hr: (result_sz r < Datatypes.S sz)%nat) by lia.
  clear E. revert r Hr. induction (Datatypes.S sz); intros.
  - lia.
  - destruct r; auto. apply H2. induction v.
    + constructor.
    + constructor.
      -- apply IHn. simpl in Hr. lia.
      -- apply IHv. simpl in Hr. simpl. lia.
Qed.

Inductive result_has_shape : result -> list nat -> Prop :=
| ScalarShape : forall s, result_has_shape (S s) []
| VectorNilShape : forall l, result_has_shape (V []) (0::l)
| VectorConsShape : forall x xs xs_shape l,
    l = length xs ->
    result_has_shape x xs_shape ->
    Forall (fun r => result_has_shape r xs_shape) xs ->
    result_has_shape (V (x::xs)) (Datatypes.S l::xs_shape).

Fixpoint result_shape_nat r :=
  match r with
  | S _ => []
  | V [] => [0]
  | V (x::xs) => (length (x::xs))::(result_shape_nat x)
  end.

Definition result_shape_Z r := map Z.of_nat (result_shape_nat r).
Arguments result_shape_Z : simpl nomatch.

Inductive add_scalar_result :
  scalar_result -> scalar_result -> scalar_result -> Prop :=
| AddSS : forall s1 s2, add_scalar_result (SS s1) (SS s2) (SS (s1+s2)%R)
| AddSX : forall s1, add_scalar_result (SS s1) SX (SS s1)
| AddXS : forall s1, add_scalar_result SX (SS s1) (SS s1)
| AddXX : add_scalar_result SX SX SX.

Inductive add_result : result -> result -> result -> Prop :=
| AddS : forall s1 s2 s3,
    add_scalar_result s1 s2 s3 ->
    add_result (S s1) (S s2) (S s3)
| AddV : forall v1 v2 r,
    add_list v1 v2 r ->
    add_result (V v1) (V v2) (V r)
with add_list : list result -> list result -> list result -> Prop :=
    | AddCons : forall x1 x2 xs1 xs2 r1 r2,
        add_result x1 x2 r1 ->
        add_list xs1 xs2 r2 ->
        add_list (x1::xs1) (x2::xs2) (r1::r2)
    | AddNil : add_list [] [] []
.
Scheme add_result_mut := Induction for add_result Sort Prop
    with add_list_mut := Induction for add_list Sort Prop.

Fixpoint gen_pad sh :=
  match sh with
  | x::xs => V (List.repeat (gen_pad xs) x)
  | _ => S SX
  end.

Definition gen_pad_list sh :=
  match sh with
  | [] => []
  | x::xs => repeat (gen_pad xs) x
  end.

Fixpoint get_col (l : list result) (n : nat) : list result :=
  match l with
  | [] => []
  | (V x)::xs => match nth_error x n with
                 | Some val => val :: get_col xs n
                 | None => []
                 end
  | (S _)::xs => []
  end.

Definition row_length (l : list result) :=
  match l with
  | V v::xss => length v
  | _ => 0
  end.        

Fixpoint transpose_result_list (l : list result) (n : nat) :=
  match n with
  | Datatypes.S n' => V (get_col l ((row_length l) - n)) ::
                        transpose_result_list l n'
  | _ => []
  end.

Definition pad_list_result_to_shape (l : list result) (sh : list nat) :=
  match l with
  | [] => gen_pad_list sh
  | _ => l
  end.

Definition transpose_result (l : list result) (sh : list nat) :=
  V (pad_list_result_to_shape (transpose_result_list l (row_length l)) sh).

Fixpoint flatten_result (l : list result) :=
  match l with
  | [] => []
  | S _ :: _ => []
  | V v :: l0 => (v ++ flatten_result l0)%list
  end.

Definition split_result k l :=
  let sh := match result_shape_nat (V l) with
            | _::xs => xs
            | _ => []
            end in
  let l' := (l++gen_pad_list ((k - length l mod k) mod k::sh))%list in
  let range := nat_range (length l //n k) in
  map (fun i => V (firstn k (skipn (k*i) l'))) range.

Lemma result_shape_nat_gen_pad : forall lz,
    Forall (fun x => x > 0) lz ->
    result_shape_nat (gen_pad lz) = lz.
Proof.
  induction lz.
  - reflexivity.
  - intros. simpl in *. invert H.
    cases a.
    + lia.
    + simpl. rewrite IHlz.
      rewrite repeat_length. reflexivity.
      auto.
Qed.

Lemma result_shape_Z_gen_pad : forall lz,
    Forall (fun x => x > 0) lz ->
    result_shape_Z (gen_pad lz) = (map Z.of_nat lz).
Proof.
  induction lz.
  - reflexivity.
  - intros. simpl. invert H.
    cases a.
    + lia.
    + simpl. posnats. unfold result_shape_Z in *. simpl. posnats.
      rewrite IHlz.
      rewrite repeat_length. reflexivity. auto.
Qed.

Lemma result_has_shape_gen_pad :
  forall l,
    result_has_shape (gen_pad l) l.
Proof.
  induct l; intros.
  - econstructor.
  - simpl.
    cases (a =? 0)%nat.
    + eapply Nat.eqb_eq in Heq. subst.
      simpl. econstructor.
    + eapply Nat.eqb_neq in Heq.
      cases a. lia.
      simpl. econstructor.
      rewrite repeat_length. reflexivity. auto.
      eapply Forall_repeat. auto.
Qed.

Lemma result_has_shape_result_shape_nat : forall r l,
    result_has_shape r l ->
    result_shape_nat r = filter_until l 0%nat.
Proof.
  induct 1.
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite IHresult_has_shape. rewrite <- H. reflexivity.
Qed.

Lemma result_has_shape_result_shape_Z : forall r l,
    result_has_shape r l ->
    result_shape_Z r = map Z.of_nat (filter_until l 0).
Proof.
  intros.
  unfold result_shape_Z. 
  eapply result_has_shape_result_shape_nat in H.
  rewrite H. reflexivity.
Qed.

Lemma flatten_result_empty_vector : forall k,
    flatten_result (repeat (V []) k) = [].
Proof.
  induct k. reflexivity.
  simpl. auto.
Qed.

Lemma forall_empty_vector : forall xs0 sh,
  Forall (fun r : result => result_has_shape r (0::sh)) xs0 ->
  repeat (V []) (Datatypes.length xs0) = xs0.
Proof.
  induct xs0; intros.
  - reflexivity.
  - simpl. invert H. invert H2. f_equal. eauto.
Qed.

Lemma get_col_row_length : forall l,
    get_col l (row_length l) = [].
Proof.
  intros. cases l.
  - reflexivity.
  - simpl. cases r.
    + reflexivity.
    + assert (length v <= length v) by lia.
      eapply nth_error_None in H. rewrite H.
      reflexivity.
Qed.

Lemma flatten_result_empty : forall l xs,
    Forall (fun r : result => result_has_shape r (0::xs)) l ->
    flatten_result l = [].
Proof.
  induct l; intros.
  - eauto.
  - simpl.
    invert H. cases a. invert H2. invert H2.
    simpl. eauto.
Qed.

Lemma result_has_shape_app : forall l1 l2 xs x,
    Forall (fun x => result_has_shape x xs) l1 ->
    Forall (fun x => result_has_shape x xs) l2 ->
    x = length l1 + length l2 ->
    x <> 0 ->
    result_has_shape (V (l1++l2)%list) (x::xs).
Proof.
  induct l1; intros; cases l2; simpl in *; try lia.
  - subst. econstructor. eauto. invert H0. eauto. invert H0. eauto.
  - subst. rewrite app_nil_r.
    econstructor. eauto. invert H. eauto. invert H. eauto.
  - subst. econstructor. rewrite app_length. simpl. lia.
    invert H. auto.
    eapply Forall_app. split; auto. invert H. auto.
Qed.

Lemma result_has_shape_forall : forall l n xs,
    result_has_shape (V l) (n::xs) ->
    Forall (fun x => result_has_shape x xs) l.
Proof.
  induct l; intros.
  - invert H. auto.
  - invert H. eauto.
Qed.

Lemma length_transpose_result_list : forall l k,
    length (transpose_result_list l k) = k.
Proof.
  induct k; intros; simpl in *.
  - reflexivity.
  - lia.
Qed.

Lemma result_has_shape_length : forall r x xs,
    result_has_shape (V r) (x::xs) ->
    length r = x.
Proof.
  induct 1.
  - reflexivity.
  - simpl. eauto.
Qed.

Fixpoint result_lookup_Z indices r :=
  match indices with
  | (Z.neg _)::xs => SS 0%R
  | x::xs => match r with
             | V v => match nth_error v (Z.to_nat x) with
                      | None => SS 0%R
                      | Some v' => result_lookup_Z xs v'
                      end
             | _ => SS 0%R
             end
  | _ => match r with
         | S s => s
         | _ => SS 0%R
         end
  end.

Fixpoint result_lookup_Z_option indices r :=
  match indices with
  | (Z.neg _)::xs => None
  | x::xs => match r with
             | V v => match nth_error v (Z.to_nat x) with
                      | None => None
                      | Some v' => result_lookup_Z_option xs v'
                      end
             | _ => None
             end
  | _ => match r with
         | S (SS s) => Some s
         | _ => None
         end
  end.

Lemma length_add_result : forall l1 l2 l3,
    add_list l1 l2 l3 ->
    length l2 = length l1 /\ length l3 = length l1.
Proof.
  induct l1; intros; invert1 H; simpl; try equality.
  apply IHl1 in H5. equality.
Qed.

Lemma result_has_shape_tail : forall r r0 x xs,
    r0 <> [] ->
    result_has_shape (V (r :: r0)) (x::xs) ->
    result_has_shape (V r0) ((x-1)::xs).
Proof.
  intros. invert H0.
  cases r0. propositional. simpl.
  econstructor. reflexivity. invert H7. auto. invert H7. auto.
Qed.

Lemma result_has_shape_cons : forall r r0 x xs,
    result_has_shape (V (r :: r0)) (x::xs) ->
    result_has_shape r xs.
Proof.
  intros. invert H. auto.
Qed.

Lemma add_list_length : forall l1 l2 l3,
    add_list l1 l2 l3 ->
    length l1 = length l2.
Proof.
  induct 1; intros.
  - simpl in *. lia.
  - lia.
Qed.

Lemma add_list_result_length : forall l1 l2 l3,
    add_list l1 l2 l3 ->
    length l1 = length l3.
Proof.
  induct 1; intros.
  - simpl in *. lia.
  - lia.
Qed.

Lemma result_has_shape_filter_until_0 : forall sh r,
    result_has_shape r sh <->
    result_has_shape r (filter_until sh 0).
Proof.
  induct sh; propositional.
  - invert H. econstructor.
    simpl. econstructor. auto. eapply IHsh. auto.
    eapply Forall_impl. 2: eassumption. simpl. propositional.
    eapply IHsh. auto.
  - simpl in *.
    cases (a =? 0)%nat.
    eapply Nat.eqb_eq in Heq. subst. invert H. econstructor.
    eapply Nat.eqb_neq in Heq. cases a. lia.
    invert H.
    econstructor; auto.
    eapply IHsh. auto.
    eapply Forall_impl. 2: eassumption. simpl. propositional.
    eapply IHsh. auto.
Qed.

Lemma result_has_shape_self : forall r sh,
    result_has_shape r sh ->
    result_has_shape r (result_shape_nat r).
Proof.
  induct 1; intros.
  - econstructor.
  - econstructor.
  - simpl. econstructor. auto. auto.
    eapply result_has_shape_result_shape_nat in H0.
    rewrite H0 in *. eapply Forall_impl.
    2: eassumption.
    simpl. intros.
    rewrite <- result_has_shape_filter_until_0. eauto.
Qed.

Lemma result_has_shape_self_tail : forall r1 r2,
  result_has_shape (V (r1 :: r2)) (result_shape_nat (V (r1 :: r2))) ->
  result_has_shape (V r2) (result_shape_nat (V r2)).
Proof.
  intros. invert H.
  cases r2; simpl in *; try lia.
  econstructor.
  simpl. invert H6. econstructor. lia. eapply result_has_shape_self.
  eassumption.
  eapply Forall_impl. 2: eassumption.
  simpl. intros. erewrite result_has_shape_result_shape_nat. 2: apply H1.
  rewrite <- result_has_shape_filter_until_0. auto.
Qed.

Lemma result_has_shape_tail_transitivity :
  forall xs1 xs2 x1 x2,
  result_has_shape (V (x1 :: xs1)) (result_shape_nat (V (x1 :: xs1))) ->
  result_has_shape (V (x2 :: xs2)) (result_shape_nat (V (x1 :: xs1))) ->
  result_has_shape (V xs2) (result_shape_nat (V xs1)).
Proof.
  induct xs1; intros.
  - simpl in *. invert H0. cases xs2; simpl in *; try lia.
    econstructor.
  - cases xs2. simpl in *. invert H0. simpl in *. try lia.
    simpl. econstructor. invert H0. simpl in *. lia.
    invert H0. invert H7.
    invert H. invert H10.
    pose proof H2.
    eapply result_has_shape_result_shape_nat in H2.
    eapply result_has_shape_result_shape_nat in H1.
    rewrite H1. rewrite <- H2.
    eapply result_has_shape_self. eauto.
    invert H0. invert H7.
    invert H. invert H10.
    eapply result_has_shape_result_shape_nat in H1. rewrite H1.
    eapply Forall_impl. 2: eassumption. simpl. propositional.
    rewrite <- result_has_shape_filter_until_0. auto.
Qed.

Lemma length_get_col : forall l n k m xs,
    result_has_shape (V l) (k::m::xs) ->
    0 <= n < m ->
    length (get_col l n) = length l.
Proof.
  induct l; intros.
  - reflexivity. 
  - simpl. invert H. cases a. invert H6.
    cases (nth_error v n).
    + simpl. f_equal. cases l. reflexivity.
      eapply IHl. econstructor. reflexivity. invert H7. eauto.
      invert H7. eauto. auto.
    + eapply nth_error_None in Heq.
      erewrite result_has_shape_length in Heq by eassumption. lia.
Qed.

Lemma result_has_shape_repeat_gen_pad : forall k l,
    result_has_shape (V (repeat (gen_pad l) k)) (k::l).
Proof.
  induct k; intros.
  - simpl. econstructor.
  - simpl. econstructor. rewrite repeat_length.
    reflexivity.
    specialize (IHk l). invert IHk.
    eapply result_has_shape_gen_pad.
    eapply result_has_shape_gen_pad.
    specialize (IHk l). invert IHk. eauto.
    econstructor. eauto. eauto.
Qed.    

Lemma forall_result_has_shape : forall sh l k,
    (Forall (fun r => result_has_shape r sh) l) ->
    k = length l ->
    result_has_shape (V l) (k::sh).
Proof.
  induct l; intros; subst.
  - econstructor.
  - simpl. invert H. econstructor. reflexivity. eauto. eauto.
Qed.

Lemma result_has_shape_get_col :
  forall l k n m xs,
    k < m ->
    result_has_shape (V l) (n::m::xs) ->
    result_has_shape (V (get_col l k)) (n::xs).
Proof.
  induct l; intros.
  - invert H0. simpl. econstructor.
  - invert H0. simpl. cases a. invert H6.
    cases (nth_error v k).
    + eapply nth_error_In in Heq.
      econstructor. erewrite length_get_col.
      2: { eapply forall_result_has_shape; eauto. }
      reflexivity. lia.
      invert H6. invert Heq.
      eapply Forall_forall in Heq.
      2: { econstructor. 2: eassumption. apply H4. }
      apply Heq.
      eapply result_has_shape_forall.
      eapply IHl. 2: eapply forall_result_has_shape; eauto.
      lia.
    + eapply nth_error_None in Heq.
      erewrite result_has_shape_length in Heq by eassumption. lia.
Qed.

Lemma result_has_shape_transpose_result_list : forall k v l n m xs,
    k <= m ->
    result_has_shape (V (v::l)) (n::m::xs) ->
    result_has_shape (V (transpose_result_list (v::l) k)) (k::n::xs).
Proof.
  induct k; intros.
  - simpl. econstructor.
  - simpl. invert H0. cases v. invert H6. 
    cases (nth_error v (length v - Datatypes.S k)).
    + econstructor. rewrite length_transpose_result_list. reflexivity.
      pose proof Heq.
      eapply nth_error_Some in Heq.
      cases v. simpl in *. lia.
      simpl. pose proof (result_has_shape_length _ _ _ H6).
      simpl in H1. rewrite <- H1 in *.
      econstructor. erewrite length_get_col. reflexivity.
      eapply forall_result_has_shape. eassumption. reflexivity.
      lia. invert H6.
      eapply nth_error_In in H0. eapply Forall_forall in H0.
      2: { econstructor. 2: apply H10. simpl. eassumption. }
      apply H0.
      eapply result_has_shape_forall.
      eapply result_has_shape_get_col.
      2: eapply forall_result_has_shape; eauto. lia.
      eapply result_has_shape_forall. eapply IHk.
      2: { econstructor. reflexivity. eassumption. auto. }
      lia.
    + eapply nth_error_None in Heq.
      erewrite result_has_shape_length in Heq by eassumption. lia.
Qed.

Lemma gen_pad_filter_until_0 :
  forall l,
    gen_pad l = gen_pad (filter_until l 0).
Proof.
  induct l; intros.
  - reflexivity.
  - simpl.
    cases (a =? 0)%nat.
    + eapply Nat.eqb_eq in Heq. subst.
      reflexivity.
    + simpl.
      rewrite IHl.
      reflexivity.
Qed.

Lemma result_has_shape_split_result : forall l k n sh,
    0 < k ->
    result_has_shape (V l) (n :: sh) ->
    result_has_shape (V (split_result k l)) ((n //n k):: k:: sh).
Proof.
  induct l; intros.
  - invert H0. unfold split_result. simpl. unfold div_ceil_n. simpl.
    rewrite div_small by lia. simpl. econstructor.
  - unfold split_result. remember sub. simpl. invert H0.
    rewrite app_comm_cons.
    erewrite map_nat_range_extensionality.
    2: { intros. rewrite skipn_app. rewrite firstn_app.
         rewrite skipn_length. rewrite skipn_repeat.
         rewrite firstn_repeat. simpl length.
         reflexivity. }
    eapply forall_result_has_shape.
    2: { rewrite map_length. unfold nat_range.
         rewrite length_nat_range_rec. reflexivity. }

    eapply Forall_forall. intros.
    eapply in_map_iff in H0. invs.
    eapply In_nat_range in H2.
    eapply forall_result_has_shape.
    2: { rewrite app_length. rewrite firstn_length. 
         rewrite skipn_length. rewrite repeat_length.
         simpl length.
         cases (Datatypes.S (Datatypes.length l) mod k).
         - rewrite sub_0_r. rewrite Div0.mod_same by lia. rewrite sub_0_l.
           rewrite min_0_l. rewrite add_0_r.
           pose proof Heq. eapply Div0.div_exact in Heq. 
           rewrite Heq. rewrite <- mul_sub_distr_l.
           pose proof H0.
           rewrite mod_0_iff_ceil_eq_floor_0 in H0 by lia.
           rewrite H0 in H2. pose proof H1.
           cases (Datatypes.S (Datatypes.length l) / k - x0). lia.
           rewrite min_l. reflexivity.
           rewrite mul_comm. simpl. eapply le_add_r.
         - cases (Datatypes.S (length l) //n k - Datatypes.S (length l) / k).
           + eapply mod_0_iff_ceil_sub_floor_0 in Heq0. lia. lia.
           + pose proof (ceil_sub_floor_le_1 (Datatypes.S (length l)) k).
             assert (n0 = 0) by lia. subst.
             assert (x0 = Datatypes.S (Datatypes.length l) / k \/
                       x0 < Datatypes.S (Datatypes.length l) / k) by lia.
             invert H1.
             * rewrite <- Div0.mod_eq by lia.
               rewrite min_r.
               2: { pose proof (Nat.mod_upper_bound
                                  (Datatypes.S (Datatypes.length l)) k).
                    lia. }
               replace (k * (Datatypes.S (length l) / k) -
                          Datatypes.S (length l)) with 0.
               2: { pose proof (Div0.mul_div_le
                                  (Datatypes.S (length l)) k). lia. }
               rewrite sub_0_r. rewrite Heq.
               rewrite min_l.
               2: { eapply Div0.mod_le. }
               rewrite <- Heq.

               unfold modulo. unfold modulo in Heq. cases k. lia.
               pose proof (divmod_spec(Datatypes.S (Datatypes.length l)) k 0 k).
               cases (divmod (Datatypes.S (Datatypes.length l)) k 0 k).
               assert (k<=k) by lia. propositional.
               rewrite mul_0_r in *. rewrite add_0_r in *.
               rewrite sub_diag in *. rewrite add_0_r in *.
               simpl. simpl in Heq. rewrite Heq. simpl.
               f_equal.
               pose proof (divmod_spec (k - n) k 0 k).
               cases (divmod (k - n) k 0 k). propositional. simpl.
               rewrite sub_diag in *. rewrite mul_0_r in *.
               repeat rewrite add_0_r in *.
               assert (k - (k-n3) = n ->k = n + (k - n3)). lia.
               apply H8.
               rewrite sub_sub_distr by lia.
               rewrite sub_diag. simpl. clear H8.
               assert (Datatypes.S k * n2 + (k - n3) <= k) by lia.
               pose proof H8. eapply le_add_le_sub_r in H10.
               assert (k - (k-n3) <= k) by lia.
               assert (Datatypes.S k * n2 <= k) by lia.
               cases n2.
               2: { remember (Datatypes.S k). rewrite mul_comm in H12.
                    simpl in H12. subst. lia. }
               rewrite mul_0_r in H4. simpl in H4. lia.
             * erewrite (Nat.div_mod_eq (Datatypes.S (length l)) k).
               rewrite add_sub_swap.
               2: { eapply mul_le_mono_l. lia. }
               rewrite <- mul_sub_distr_l.
               rewrite min_l.
               2: { cases (Datatypes.S (Datatypes.length l) / k - x0).
                    lia. rewrite mul_comm. simpl.
                    rewrite <- add_assoc. eapply le_add_r. }
               repeat rewrite sub_add_distr.
               rewrite <- mul_sub_distr_l.
               cases (x0 - Datatypes.S (Datatypes.length l) / k).
               2: lia. rewrite mul_0_r. rewrite sub_0_l. rewrite sub_0_r.
               replace k with (k*1) at 5 by lia.
               rewrite <- mul_sub_distr_l.
               replace (1 - (Datatypes.S (length l) / k - x0)) with 0 by lia.
               rewrite mul_0_r. rewrite sub_0_l.
               rewrite min_0_r. lia.
    }
    rewrite Forall_app. split.
    eapply forall_firstn. eapply forall_skipn. econstructor; eauto.
    eapply Forall_repeat.
    erewrite result_has_shape_result_shape_nat by eauto.
    erewrite <- gen_pad_filter_until_0.
    eapply result_has_shape_gen_pad.
Qed.

Lemma result_has_shape_pad_list_result_to_shape :
  forall sh l,
    result_has_shape (V l) sh ->
    result_has_shape (V (pad_list_result_to_shape l sh)) sh.
Proof.
  induct sh; intros.
  - invert H.
  - invert H.
    + simpl. econstructor.
    + simpl. cases x.
      * invert H4. econstructor. auto.
        econstructor. auto.
      * econstructor. auto. auto. auto.
Qed.

Lemma result_has_shape_transpose_result : forall l n m xs,
    result_has_shape (V l) (n::m::xs) ->
    result_has_shape (transpose_result l (m::n::xs)) (m::n::xs).
Proof.
  induct l; unfold transpose_result in *; intros.
  - simpl. invert H.
    replace m with (length (repeat (V (repeat (gen_pad xs) 0)) m)) at 2.
    2: { rewrite repeat_length. auto. }
    eapply forall_result_has_shape.
    eapply Forall_repeat. econstructor. reflexivity.
  - invert H.
    eapply result_has_shape_pad_list_result_to_shape.
    simpl. cases a. invert H5.
    erewrite result_has_shape_length by eassumption.
    eapply result_has_shape_transpose_result_list.
    2: { econstructor. reflexivity. eassumption. eauto. } lia.
Qed.

Lemma nth_error_get_col : forall l n m xs z z0,
    result_has_shape (V l) (n::m::xs) ->
    0 <= z0 < n ->
    0 <= z < m ->
    match nth_error l z0 with
    | Some (V v) => nth_error v z
    | _ => None
    end = nth_error (get_col l z) z0.
Proof.
  induct l; intros.
  - invert H. lia.
  - invert H. cases a. invert H7.
    cases z0.
    + simpl.
      cases (nth_error v z).
      * reflexivity.
      * eapply nth_error_None in Heq.
        erewrite result_has_shape_length in Heq by eassumption. lia.
    + simpl.
      cases (nth_error  v z).
      * cases l. rewrite nth_error_empty. simpl.
        rewrite nth_error_empty. reflexivity.
        eapply IHl.
        econstructor. reflexivity. invert H8. eauto. invert H8. eauto.
        simpl in *. lia. lia.
      * eapply nth_error_None in Heq.
        erewrite result_has_shape_length in Heq by eassumption. lia.
Qed.

Lemma nth_error_transpose : forall x k l n m xs,
    result_has_shape (V l) (n::m::xs) ->
    0 < x ->
    k < m ->
    match nth_error (transpose_result_list l x) k with
    | Some x => x
    | _ => V []
    end = (V (get_col l (row_length l - (x - k)))).
Proof.
  induct x; intros.
  - simpl in *. rewrite nth_error_empty. rewrite sub_0_r.
    rewrite get_col_row_length. reflexivity.
  - simpl. cases k. reflexivity.
    simpl. cases x. simpl. rewrite nth_error_empty. rewrite sub_0_r.
    rewrite get_col_row_length. reflexivity.
    erewrite IHx. 2: eassumption. 2: lia. reflexivity. lia.
Qed.

Lemma forall_result_has_shape_get_col : forall l k n m xs,
    result_has_shape (V l) (n::m::xs) ->
    Forall (fun x => result_has_shape x xs) (get_col l k).
Proof.
  induct l.
  - invert 1. simpl. econstructor.
  - intros. invert H. cases a. invert H5. 
    cases k.
    + simpl. cases v.
      * auto.
      * cases l. simpl. econstructor. invert H5. auto. auto.
        econstructor. invert H5. auto. eapply IHl.
        econstructor. reflexivity.
        invert H6. eassumption. invert H6. auto.
    + simpl. cases v. eauto.
      cases (nth_error v k).
      * eapply nth_error_In in Heq.
        invert H5.
        econstructor.
        eapply Forall_forall in Heq. 2: eassumption. simpl in Heq. auto.
        cases l. simpl. eauto.
        eapply IHl. econstructor. reflexivity.
        invert H6. eassumption.
        invert H6. auto.
      * auto.
Qed.        

Lemma result_has_shape_row_length : forall l n m xs,
    l <> [] ->
    result_has_shape (V l) (n::m::xs) ->
    row_length l = m.
Proof.
  induct l; intros.
  - propositional.
  - simpl. invert H0. cases a. invert H6.
    eapply result_has_shape_length. eassumption.
Qed.

Lemma result_lookup_Z_transpose : forall l z z0 x n m xs,
    (0 <= z0 < Z.of_nat n)%Z ->
    (0 <= z < Z.of_nat m)%Z ->
    result_has_shape (V l) (n::m::xs) ->
    result_lookup_Z (z0 :: z :: x) (V l) =
      result_lookup_Z (z :: z0 :: x) (transpose_result l (m::n::xs)).
Proof.
  simpl. intros.
  pose proof (nth_error_transpose (row_length l) (Z.to_nat z) _ _ _ _ H1).
  cases l. simpl. rewrite nth_error_empty.
  invert H1.
  rewrite nth_error_repeat by lia.
  simpl.
  rewrite nth_error_empty. cases z0; cases z; reflexivity.
  erewrite result_has_shape_row_length in H2; try eassumption.
  2: intros; discriminate.
  simpl transpose_result_list.
  invert H1. cases r. invert H8. 
  assert (0 < m). lia. assert (Z.to_nat z < m). lia. propositional.
  replace (m - (m - Z.to_nat z)) with (Z.to_nat z) in * by lia.
  erewrite result_has_shape_length by eassumption.
  cases (transpose_result_list (V v :: l) m).
  - cases m. 2: { simpl in Heq. invert Heq. } lia.
  - simpl. rewrite <- Heq in *. clear Heq.
    pose proof (length_transpose_result_list (V v::l) m).
    cases (nth_error (transpose_result_list (V v :: l) m) (Z.to_nat z)).
    + subst.
      erewrite <- nth_error_get_col.
      2: { econstructor. reflexivity. eassumption. eassumption. }
      cases (nth_error (V v :: l) (Z.to_nat z0)).
      2: { eapply nth_error_None in Heq0. simpl in *. lia. }
      eapply nth_error_In in Heq0. eapply Forall_forall in Heq0.
      2: { econstructor. 2: apply H9. apply H8. }
      simpl in Heq0. cases r0. invert Heq0. 
      cases z0; cases z; reflexivity. lia. lia.
    + eapply nth_error_None in Heq.
      rewrite length_transpose_result_list in Heq. lia.
Qed.

Lemma result_has_shape_flatten : forall l n m xs,
    result_has_shape (V l) (n::m::xs) ->
    result_has_shape (V (flatten_result l)) (n*m::xs).
Proof.
  induct l; intros.
  - invert H. simpl. econstructor.
  - invert H. simpl. cases a. invert H5. 
    
    cases v. 
    invert H5. simpl. rewrite mul_0_r.
    eapply flatten_result_empty in H6. rewrite H6. econstructor.

    cases l.
    + simpl. rewrite app_nil_r. rewrite add_0_r. eauto.
    + assert (result_has_shape (V (r0 :: l))
                               (length (r0 :: l) :: m :: xs)).
      simpl. econstructor. auto. invert H6. auto. invert H6. auto.
      eapply IHl in H.
      eapply result_has_shape_app.
      eapply result_has_shape_forall. eauto.
      eapply result_has_shape_forall. eauto.      
      erewrite (result_has_shape_length (r::v)) by eassumption.
      erewrite (result_has_shape_length (flatten_result _)) by eassumption.
      lia.
      eapply result_has_shape_length in H5. simpl in *. subst. lia.
Qed.      

Lemma result_has_shape_no_cons : forall l sh k,
    l <> [] ->
    k = length l ->
    Forall (fun x => result_has_shape x sh) l ->
    result_has_shape (V l) (k::sh).
Proof.
  induct l; intros.
  - propositional.
  - clear H. simpl in *. subst. econstructor. auto. invert H1.
    auto. invert H1. auto.
Qed.    
    
Lemma empty_result_shape_Z_flatten : forall l,
  Forall (fun r : result => result_has_shape r [0]) l ->
  result_shape_Z (V (flatten_result l)) = [0%Z].
Proof.
  induct 1.
  - reflexivity.
  - simpl.
    invert H. simpl. eauto.
Qed.
(*
*)
Lemma exists_0_result_shape_Z_gen_pad : forall l,
    Exists (fun x => x = 0) l ->
    Exists (fun x => x = 0) (result_shape_nat (gen_pad l)).
Proof.
  induct l; intros.
  - invert H.
  - simpl. cases a. invert H. simpl. eauto.
    simpl. eauto.
    invert H. lia.
    simpl. rewrite repeat_length.
    eapply Exists_cons_tl. eauto.
Qed.

Lemma result_has_shape_add_result : forall r1 r2 r3,
    add_result r1 r2 r3 ->
    forall sh,
    result_has_shape r1 sh ->
    result_has_shape r2 sh ->
    result_has_shape r3 sh.
Proof.
  eapply (add_result_mut
            (fun r1 r2 r3 H => forall sh,
                   result_has_shape r1 sh ->
                   result_has_shape r2 sh ->
                   result_has_shape r3 sh)
            (fun l1 l2 l3 H => forall sh,
                   result_has_shape (V l1) sh ->
                   result_has_shape (V l2) sh ->
                   result_has_shape (V l3) sh)).
  - intros. simpl. invert H. econstructor.
  - intros. eauto.
  - intros. simpl. invert H1. invert H2.
    econstructor.
    2: { eapply H; auto. }
    cases xs1. simpl in *. invert a0. reflexivity.
    invert a0.
    assert (result_has_shape (V (r::xs1)) (length(r::xs1)::xs_shape)).
    simpl. econstructor;eauto. invert H8. eauto. invert H8. eauto.
    eapply H0 in H1.
    eapply result_has_shape_length in H1. lia.
    simpl. econstructor.
    simpl in *. lia. invert H10. auto. invert H10. auto.
    cases xs1. simpl in *. invert a0. auto.
    invert a0.
    assert (result_has_shape (V (r::xs1)) (length(r::xs1)::xs_shape)).
    simpl. econstructor;eauto. invert H8. eauto. invert H8. eauto.
    eapply H0 in H1.
    simpl in *. invert H1. eauto.
    simpl. econstructor. simpl in *. lia.
    invert H10. auto. invert H10. auto.
  - intros. invert H. eauto.
Qed.                     
  
Lemma result_has_shape_add_result_result : forall r1 r2 r3,
    add_result r1 r2 r3 ->
    forall sh,
      result_has_shape r3 sh ->
      result_has_shape r1 sh /\
        result_has_shape r2 sh.
Proof.
  eapply (add_result_mut
            (fun r1 r2 r3 H => forall sh,
                   result_has_shape r3 sh ->
                   result_has_shape r1 sh /\ result_has_shape r2 sh)
            (fun l1 l2 l3 H => forall sh,
                   result_has_shape (V l3) sh ->
                   result_has_shape (V l1) sh /\ result_has_shape (V l2) sh)).
  - intros. simpl. invert H. propositional; econstructor.
  - intros. eauto.
  - intros. invert H1.
    eapply H in H5. clear H. invs.
    cases r2. invert a0. simpl. split; econstructor; eauto.
    invert a0.
    assert (result_has_shape (V (r::r2)) ((length (r::r2)) :: xs_shape)).
    simpl. econstructor. auto. invert H7. auto. invert H7. auto.
    eapply H0 in H2. invs. simpl in *. invert H3. invert H4.
    split; econstructor; simpl; eauto.
  - intros. invert H. split; econstructor.
Qed.                     

Lemma length_add_list : forall l1 l2 l3,
    add_list l1 l2 l3 ->
    length l1 = length l2 /\ length l2 = length l3.
Proof.
  induct 1.
  - invs. simpl. lia.
  - eauto.
Qed.
 
Lemma result_has_shape_concat : forall l1 l2 x1 x2 xs,
    result_has_shape (V l1) (x1::xs) ->
    result_has_shape (V l2) (x2::xs) ->
    result_has_shape (V (l1++l2)) (x1+x2::xs).
Proof.
  induct l1; intros; cases l2.
  - invert H. invert H0. rewrite app_nil_r. econstructor.
  - invert H. simpl. eauto.
  - invert H0. rewrite app_nil_r. rewrite add_0_r. eauto.
  - simpl. invert H. invert H0. simpl.
    econstructor. rewrite app_length. simpl. auto. auto.
    eapply Forall_app. auto.
Qed.


Lemma result_has_shape_truncl_list :
  forall l k x xs,
    result_has_shape (V l) (filter_until (x::xs) 0) ->
    result_has_shape (V (truncl_list k l)) (x -k::xs).
Proof.
  induct l; intros; cases x.
  - rewrite truncl_list_empty. econstructor.
  - invert H.
  - invert H.
  - cases k.
    + simpl. simpl in *. invert H. econstructor. auto.
      eapply result_has_shape_filter_until_0. auto.
      eapply Forall_impl. 2: eassumption.
      simpl. intros.
      eapply result_has_shape_filter_until_0. auto.
    + simpl truncl_list. simpl Nat.sub.
      eapply IHl.
      cases l.
      * simpl in *. invert H. simpl. econstructor.
      * invert H. invert H6.
        simpl. econstructor. eauto. eauto. eauto.
Qed.

Lemma result_has_shape_rev : forall l sh,
    result_has_shape (V l) sh ->
    result_has_shape (V (rev l)) sh.
Proof.
  induct l; intros.
  - invert H. simpl. econstructor.
  - simpl. invert H.
    replace (Datatypes.S (length l)) with (length l + 1) by lia.
    cases l.
    simpl. econstructor; eauto.
    eapply result_has_shape_concat.
    2: econstructor; eauto.
    eapply IHl. invert H5. econstructor; eauto.
Qed.

Lemma result_has_shape_app_l : forall l1 l2 m sh k,
    length l1 = k ->
    result_has_shape (V (l1 ++ l2)) (m :: sh) ->
    result_has_shape (V l2) (m - k :: sh).
Proof.
  induct l1; intros.
  - subst. simpl in *. rewrite sub_0_r. auto.
  - simpl in *. invert H0.
    rewrite app_length.
    replace (Datatypes.S (Datatypes.length l1 + Datatypes.length l2) -
               Datatypes.S (Datatypes.length l1)) with (length l2) by lia.
    eapply Forall_app in H7. invs.
    eapply forall_result_has_shape; eauto.
Qed.  

Lemma result_has_shape_app_r : forall l1 l2 m sh k,
    length l2 = k ->
    result_has_shape (V (l1 ++ l2)) (m :: sh) ->
    result_has_shape (V l1) (m - k :: sh).
Proof.
  induct l1; intros.
  - subst. simpl in *. erewrite result_has_shape_length by eauto.
    rewrite sub_diag. econstructor.
  - simpl in *. invert H0.
    rewrite app_length.
    replace (Datatypes.S (Datatypes.length l1 + Datatypes.length l2) -
               (Datatypes.length l2)) with (Datatypes.S (length l1)) by lia.
    eapply Forall_app in H7. invs.
    eapply forall_result_has_shape; eauto.
Qed.

Lemma result_lookup_Z_option_gen_pad : forall x l,
    result_lookup_Z_option x (gen_pad l) = None.
Proof.
  induct x; intros; cases l; auto.
  simpl. cases a; auto.
  simpl.
  cases a; auto.
  2: { cases (nth_error (repeat (gen_pad l) n) (Z.to_nat (Z.pos p))); auto.
       pose proof Heq.
       eapply nth_error_Some in Heq.
       rewrite repeat_length in *.
       rewrite nth_error_repeat in H by lia.
       invert H.
       eauto. }
  simpl.
  cases n; simpl; auto.
Qed.

Lemma result_lookup_Z_option_concat_l : forall z k l x1 x,
    (0 <= z)%Z ->
    (0 <= k)%Z ->
    result_lookup_Z_option ((z + k)%Z :: x1)
                           (V (gen_pad_list (Z.to_nat k :: l) ++ x)) =
      result_lookup_Z_option (z :: x1) (V x).
Proof.
  intros. simpl.
  rewrite nth_error_app2.
  2: rewrite repeat_length; lia.
  rewrite repeat_length.
  cases z; try lia.
  -  simpl. cases k; try lia.
     + simpl. auto.
     + simpl. rewrite sub_diag. simpl. auto.
  - cases (Z.pos p + k)%Z; try lia.
    + simpl. eq_match_discriminee. f_equal. lia.
Qed.

Lemma truncl_list_gen_pad_id : forall k x l,
    truncl_list k (gen_pad_list (k :: l) ++ x) = x.
Proof.
  induct k; intros.
  - reflexivity.
  - simpl in *. rewrite IHk. auto.
Qed.

Lemma result_lookup_Z_option_Some_pad_r : forall z x2 x sh k r,
    (0 <= z)%Z ->
    result_lookup_Z_option
      (z :: x2) (V (x ++ repeat (gen_pad sh) (Z.to_nat k))) = Some r ->
    (z < Z.of_nat (length x))%Z.
Proof.
  intros. simpl in *.
  cases z; try lia.
  simpl in *.
  cases (x ++ repeat (gen_pad sh) (Z.to_nat k)). discriminate.
  cases x. simpl in *. cases (Z.to_nat k). simpl in *. discriminate.
  simpl in *. invert Heq.
  rewrite result_lookup_Z_option_gen_pad in H0. discriminate.
  simpl. lia.
  cases (nth_error (x ++ repeat (gen_pad sh) (Z.to_nat k))
                   (Z.to_nat (Z.pos p))).
  2 : { discriminate. }
  pose proof Heq.
  eapply nth_error_Some in Heq.
  rewrite app_length in *.
  rewrite repeat_length in *.
  assert (Z.pos p < Z.of_nat (length x) \/
            Z.pos p >= Z.of_nat (length x))%Z by lia.
  invert H2.  lia.
  rewrite nth_error_app2 in H1. 2: lia.
  rewrite nth_error_repeat in H1. 2: lia.
  invert H1.
  rewrite result_lookup_Z_option_gen_pad in H0. discriminate.
Qed.
  
Lemma result_lookup_Z_truncl :
  forall z x1 k l,
    (0 <= z)%Z ->
  result_lookup_Z_option (z :: x1) (V (truncl_list k l)) =
    result_lookup_Z_option ((z + Z.of_nat k)%Z :: x1) (V l).
Proof.
  intros. simpl. rewrite nth_error_truncl.
  cases z; try lia.
  - simpl. rewrite Nat2Z.id.
    cases (Z.of_nat k); try lia. auto. auto.
  - cases ((Z.pos p + Z.of_nat k)%Z); try lia.    
    eq_match_discriminee.
    f_equal. lia.
Qed.

Lemma result_lookup_Z_truncr :
  forall z x0 k l,
    Z.to_nat z < Datatypes.length l - k ->
    result_lookup_Z_option (z :: x0) (V (rev (truncl_list k (rev l)))) =
      result_lookup_Z_option (z :: x0) (V l).    
Proof.
  intros. simpl.
  rewrite nth_error_truncr. reflexivity.
  lia.
Qed.

Lemma result_lookup_Z_option_transpose : forall l z z0 x n m xs,
    (0 <= z0 < Z.of_nat n)%Z ->
    (0 <= z < Z.of_nat m)%Z ->
    result_has_shape (V l) (n::m::xs) ->
    result_lookup_Z_option (z0 :: z :: x) (V l) =
      result_lookup_Z_option (z :: z0 :: x) (transpose_result l (m::n::xs)).
Proof.
  simpl. intros.
  pose proof (nth_error_transpose (row_length l) (Z.to_nat z) _ _ _ _ H1).
  cases l. simpl. rewrite nth_error_empty.
  invert H1.
  rewrite nth_error_repeat by lia.
  simpl.
  rewrite nth_error_empty. cases z0; cases z; reflexivity.
  erewrite result_has_shape_row_length in H2; try eassumption.
  2: intros; discriminate.
  simpl transpose_result_list.
  invert H1. cases r. invert H8.
  assert (0 < m). lia. assert (Z.to_nat z < m). lia. propositional.
  replace (m - (m - Z.to_nat z)) with (Z.to_nat z) in * by lia.
  erewrite result_has_shape_length by eassumption.
  cases (transpose_result_list (V v :: l) m).
  - cases m. 2: { simpl in Heq. invert Heq. } lia.
  - simpl. rewrite <- Heq in *. clear Heq.
    pose proof (length_transpose_result_list (V v::l) m).
    cases (nth_error (transpose_result_list (V v :: l) m) (Z.to_nat z)).
    + subst.
      erewrite <- nth_error_get_col.
      2: { econstructor. reflexivity. eassumption. eassumption. }
      cases (nth_error (V v :: l) (Z.to_nat z0)).
      2: { eapply nth_error_None in Heq0. simpl in *. lia. }
      eapply nth_error_In in Heq0. eapply Forall_forall in Heq0.
      2: { econstructor. 2: apply H9. apply H8. }
      simpl in Heq0. cases r0. invert Heq0.
      cases z0; cases z; reflexivity. lia. lia.
    + eapply nth_error_None in Heq.
      rewrite length_transpose_result_list in Heq. lia.
Qed.

Lemma result_lookup_Z_option_result_lookup_Z :
  forall l r x,
  result_lookup_Z_option l r = Some x ->
  result_lookup_Z l r = SS x.
Proof.
  induct l; intros.
  - simpl in *. cases r; try discriminate.
    cases z. invert H. auto. discriminate.
  - simpl in *.
    cases a; try discriminate.
    + cases r; try discriminate.
      cases (nth_error v (Z.to_nat 0)).
      eapply IHl in H. auto. discriminate.
    + cases r; try discriminate.
      cases (nth_error v (Z.to_nat (Z.pos p))).
      eapply IHl in H. eauto. discriminate.
Qed.

Lemma result_lookup_Z_option_result_lookup_Z_None :
  forall l r,
    result_lookup_Z_option l r = None ->
    match result_lookup_Z l r with
    | SS s => s
    | SX => 0%R
    end = 0%R.
Proof.
  induct l; intros.
  - simpl in *. cases r; try discriminate; auto.
    cases z. discriminate. auto.
  - simpl in *.
    cases a; try discriminate; auto.
    cases r; try discriminate; auto. 
    cases (nth_error v (Z.to_nat 0)); eauto.
    cases r; auto.
    cases (nth_error v (Z.to_nat (Z.pos p))); eauto. 
Qed.

Lemma gen_pad_cons : forall x xs,
    gen_pad (x::xs) = V (repeat (gen_pad xs) x).
Proof. reflexivity. Qed.

Lemma flatten_result_repeat : forall r n,
    flatten_result (repeat (V r) n) = (concat (repeat r n)).
Proof.
  induct n; intros.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.    

Lemma result_has_shape_repeat : forall n r sh,
    result_has_shape r sh ->
    result_has_shape (V (repeat r n)) (n::sh).
Proof.
  induct n; intros.
  - econstructor.
  - simpl. econstructor.
    rewrite repeat_length. reflexivity. eauto.
    eapply result_has_shape_forall. eauto.
Qed.

Lemma concat_repeat_repeat {X} : forall m n (x : X),
    concat (repeat (repeat x n) m) = repeat x (n*m).
Proof.
  induct m; intros.
  - simpl. rewrite mul_0_r. reflexivity.
  - simpl. rewrite mul_succ_r.
    rewrite IHm.
    rewrite <- repeat_app.
    f_equal. lia.
Qed.

Lemma add_list_app_invert : forall l1 l2 l3 l4 l,
    length l1 = length l3 ->
    length l2 = length l4 ->
    add_list (l1++l2)%list (l3++l4)%list l ->
    exists l5 l6, l = (l5++l6)%list /\ add_list l1 l3 l5 /\ add_list l2 l4 l6.
Proof.
  induction l1; intros.
  - cases l3; simpl in *; try lia.
    eexists []. eexists l. simpl.
    propositional. econstructor.
  - cases l3; simpl in *; try lia.
    invert H.
    invert H1.
    eapply IHl1 in H8; auto. invs.
    eexists (r1::x). eexists x0.
    simpl. propositional.
    econstructor; eauto.
Qed.    

Lemma add_list_repeat_gen_pad : forall sh n l r1 r2,
    add_list r1 r2 l ->
    r1 = (repeat (gen_pad sh) n) ->
    r2 = (repeat (gen_pad sh) n) ->
    l = (repeat (gen_pad sh) n).
Proof.
  intros ? ? ? ? ? ?.
  eapply (add_list_mut
    (fun r1 r2 r3 H =>
            forall sh, r1 = gen_pad sh ->
                       r2 = gen_pad sh ->
                       r3 = gen_pad sh)
    (fun l1 l2 l3 H =>
             forall sh n,
               l1 = repeat (gen_pad sh) n ->
               l2 = repeat (gen_pad sh) n ->
               l3 = repeat (gen_pad sh) n));
    propositional.
  - cases sh0; simpl in *; try discriminate.
    invert H0. invert H1. invert a. auto.
  - cases sh0; simpl in * ; try discriminate.
    invert H1. invert H2. f_equal. eauto.
  - cases n0. simpl in *. discriminate.
    simpl in *. invert H2. invert H3.
    f_equal. eapply H0; eauto.
    eapply H1; eauto.
Qed.

Lemma add_result_gen_pad : forall rsh r,
  add_result (gen_pad rsh) (gen_pad rsh) r ->
  r = gen_pad rsh.
Proof.
  intros. cases rsh.
  - invert H. invert H2. reflexivity.
  - simpl in *. invert H.
    eapply add_list_repeat_gen_pad in H2; eauto.
    subst. reflexivity.
Qed.

Lemma forall_eq_gen_pad : forall l rsh,
    Forall (fun x : result => x = gen_pad rsh) l ->
    l = gen_pad_list (length l::rsh).
Proof.
  induct l; intros.
  - simpl in *. auto.
  - simpl. invert H. f_equal. eauto.
Qed.

Lemma add_list_app : forall l1 l2 l3,
    add_list l1 l2 l3 ->
    forall l4 l5 l6,
    add_list l4 l5 l6 ->
    add_list (l1++l4) (l2++l5) (l3++l6).
Proof.
  induct 1; intros.
  - simpl. econstructor. eauto.
    eapply IHadd_list. eauto.
  - simpl. eauto.
Qed.

Lemma add_list_rev : forall l1 l2 l3,
    add_list l1 l2 l3 ->
    add_list (rev l1) (rev l2) (rev l3).
Proof.
  induct 1; intros; simpl; try econstructor.
  eapply add_list_app. eauto. econstructor. eauto. econstructor.
Qed.                            

Lemma add_list_skipn : forall l1 l2 l3,
    add_list l1 l2 l3 ->
    forall n,
    add_list (skipn n l1) (skipn n l2) (skipn n l3).
Proof.
  induct 1; intros; simpl; try rewrite skipn_nil; try econstructor.
  cases n. simpl. econstructor. eauto. eauto. simpl.
  eauto.
Qed.

Lemma get_col_app : forall l1 l2 n a b x xs,
    result_has_shape (V l1) (a::b::xs) ->
    result_has_shape (V l2) (x::b::xs) ->
    n < b ->
    get_col (l1++l2)%list n = (get_col l1 n ++ get_col l2 n)%list.
Proof.
  induct l1; intros.
  - invert H. reflexivity.
  - invert H.
    cases a; try now invert H7.
    simpl.
    cases (nth_error v n).
    2: { eapply nth_error_None in Heq.
         eapply result_has_shape_length in H7. lia. }
    simpl. f_equal.
    eapply IHl1. 2: eauto. 
    eapply forall_result_has_shape. eauto. reflexivity.
    lia.
Qed.

Lemma pad_list_result_shape_id :
  forall x l m n xs,
    result_has_shape (V l) (n::m::xs) ->
    0 < n ->
    pad_list_result_to_shape
      (transpose_result_list l x) (x::n::xs) =
      transpose_result_list l x.
Proof.
  induct x; intros.
  - invert H. lia. reflexivity.
  - reflexivity.
Qed.

Lemma map_match_transpose_result_list_id :
  forall x m l1 n xs,
    x <= m ->
    result_has_shape (V l1) (n ::  m :: xs) ->
    map (fun x : result => match x with
                           | V l0 => V l0
                           | _ => V []
                           end) (transpose_result_list l1 x) =
      transpose_result_list l1 x.
Proof.
  induct x; intros.
  - reflexivity.
  - simpl. f_equal.
    eapply IHx. 2: eauto. lia.
Qed.

Lemma map_match_vector_id : forall l1 n m xs,
  result_has_shape (V l1) (Datatypes.S n :: m :: xs) ->
  (map (fun x : result => match x with
                          | V l0 => V l0
                          | _ => V []
                          end)
       (pad_list_result_to_shape (transpose_result_list l1 m)
                                 (m :: Datatypes.S n :: xs))) =
    (pad_list_result_to_shape (transpose_result_list l1 m)
                              (m :: Datatypes.S n :: xs)).
Proof.
  intros. cases m.
  - reflexivity.
  - simpl. f_equal.
    eapply map_match_transpose_result_list_id; try eassumption; lia.
Qed.

Lemma transpose_result_list_map2_match : forall x l1 l2 n a m xs,
    result_has_shape (V l1) (Datatypes.S n :: m :: xs) ->
    result_has_shape (V l2) (Datatypes.S a :: m :: xs) ->
    x <= m ->
    transpose_result_list (l1 ++ l2) x =
      map2
        (fun r1 r2 : result =>
           match r1 with
           | V l0 => match r2 with
                     | V l3 => V (l0 ++ l3)
                     | _ => V []
                     end
           | _ => V []
           end) (transpose_result_list l1 x) (transpose_result_list l2 x).
Proof.
  induct x; intros.
  - reflexivity.
  - invert H. invert H0. simpl.
    cases x0; try now invert H6.
    cases x1; try now invert H5.
    erewrite result_has_shape_length by eauto.
    erewrite result_has_shape_length by eauto.
    cases (nth_error v (m - Datatypes.S x)).
    2: { eapply nth_error_None in Heq.
         erewrite result_has_shape_length in Heq by eauto. lia. }
    cases (nth_error v0 (m - Datatypes.S x)).
    2: { eapply nth_error_None in Heq0.
         erewrite result_has_shape_length in Heq0 by eauto. lia. }
    erewrite get_col_app.
    2: { eapply forall_result_has_shape; eauto. }
    2: { econstructor. reflexivity. eauto. eauto. }
    2: lia.
    f_equal. f_equal. simpl. f_equal. rewrite Heq0. reflexivity.
    rewrite app_comm_cons.
    eapply IHx.
    econstructor. eauto. eauto. eauto.
    econstructor. reflexivity. eauto. eauto. lia.
Qed.

Lemma pad_list_result_to_shape_transpose_result_list_app :
    forall (l1 l2 : list result) (n m a : nat) (xs : list nat) (x : nat),
  result_has_shape (V l1) (n :: m :: xs) ->
  result_has_shape (V l2) (a :: m :: xs) ->
  x = n + a ->
    (pad_list_result_to_shape
       (transpose_result_list (l1 ++ l2) (row_length (l1 ++ l2))) 
       (m :: x :: xs)) =
    (map2
       (fun r1 r2 : result =>
        match r1 with
        | V l0 => match r2 with
                  | V l3 => V (l0 ++ l3)
                  | _ => V []
                  end
        | _ => V []
        end)
       (pad_list_result_to_shape (transpose_result_list l1 (row_length l1))
          (m :: n :: xs))
       (pad_list_result_to_shape (transpose_result_list l2 (row_length l2))
          (m :: a :: xs))).
Proof.
  intros.
  cases n; cases a.
  - invert H. invert H0. simpl. rewrite map2_repeat.
    2: rewrite repeat_length; auto.
    rewrite map_repeat.
    reflexivity.
  - simpl. invert H. simpl.
    erewrite result_has_shape_row_length.
    2: {invert H0. inversion 1. }
    2: eauto.
    erewrite pad_list_result_shape_id; eauto; try lia.
    rewrite map2_repeat.
    2: { rewrite length_transpose_result_list. auto. }
    simpl.
    erewrite map_match_transpose_result_list_id;
      try eassumption; auto.
  - simpl. invert H0.
    rewrite app_nil_r. simpl. rewrite add_0_r.    
    rewrite map2_repeat2.
    2: { invert H. simpl.
         cases x; try now invert H4.
         simpl. cases v.
         - simpl in *. invert H4.
           reflexivity.
         - simpl.
           rewrite length_transpose_result_list.
           eapply result_has_shape_length in H4. simpl in *. lia. }
           
    replace (fun x : result => match x with
                            | V l0 => V (l0 ++ [])
                            | _ => V []
                               end) with
      (fun x : result => match x with
                            | V l0 => V l0
                            | _ => V []
                         end).
    2: { eapply functional_extensionality. intros.
         cases x; try rewrite app_nil_r; reflexivity. }
    erewrite result_has_shape_row_length.
    2: { invert H. inversion 1. }
    2: eauto.
    rewrite map_match_vector_id; auto.
  - subst.
    erewrite result_has_shape_row_length.
    2: { invert H. invert H0. inversion 1. }
    2: { eapply result_has_shape_concat; eauto. }
    erewrite pad_list_result_shape_id; try lia; eauto.
    2: { eapply result_has_shape_concat; eauto. }
    erewrite result_has_shape_row_length.
    2: { invert H. invert H0. inversion 1. }
    2: eauto.
    erewrite result_has_shape_row_length.
    2: { invert H. invert H0. inversion 1. }
    2: eauto.
    
    erewrite pad_list_result_shape_id; try lia; eauto.
    erewrite pad_list_result_shape_id; try lia; eauto.

    eapply transpose_result_list_map2_match; eauto.
Qed.

Lemma transpose_result_app : forall l1 l2 n m a xs x,
    result_has_shape (V l1) (n::m::xs) ->
    result_has_shape (V l2) (a::m::xs) ->
    x = n+a ->
    transpose_result (l1++l2)%list (m::x::xs) =
      V (map2 (fun r1 r2 => match r1,r2 with
                            | V l1, V l2 => V (l1++l2)%list
                            | _,_ => V []
                            end)
              (pad_list_result_to_shape
                 (transpose_result_list l1 (row_length l1)) (m::n::xs))
              (pad_list_result_to_shape
                 (transpose_result_list l2 (row_length l2)) (m::a::xs))).
Proof.
  unfold transpose_result.
  intros. f_equal.
  apply pad_list_result_to_shape_transpose_result_list_app; auto.
Qed.

Lemma get_col_repeat_repeat_gen_pad : forall x n sh m,
    x < Datatypes.S m ->
    get_col (repeat (V (repeat (gen_pad sh) (Datatypes.S m))) n) x =
      repeat (gen_pad sh) n.
Proof.
  induct n; intros.
  - reflexivity.
  - simpl.
    cases (nth_error (gen_pad sh :: repeat (gen_pad sh) m) x).
    2: { eapply nth_error_None in Heq. simpl in *. rewrite repeat_length in *.
         lia. }
    rewrite <- repeat_cons in *.
    eapply nth_error_In in Heq.
    eapply repeat_spec in Heq.
    subst.
    f_equal. eapply IHn. lia.
Qed.

Lemma transpose_empty_result_list : forall x,
    transpose_result_list [] x = repeat (V []) x.
Proof.
  induct x; intros.
  auto. simpl. f_equal. eauto.
Qed.

Lemma transpose_result_list_repeat_repeat_gen_pad :
  forall x n m sh,
    x <= m ->
    pad_list_result_to_shape
      (transpose_result_list
         (repeat (V (repeat (gen_pad sh) m)) n)
         x) (x::n::sh) =
      (repeat (V (repeat (gen_pad sh) n)) x).
Proof.
  induct x; intros.
  - auto.
  - simpl. f_equal.
    + cases m. lia.
      rewrite get_col_repeat_repeat_gen_pad. auto.
      cases n. simpl. lia.
      erewrite result_has_shape_row_length.
      2: { inversion 1. }
      2: { eapply result_has_shape_repeat.
           eapply result_has_shape_repeat_gen_pad. }
      lia.
    + erewrite <- IHx with (m:=m).
      2: lia.
      cases n.
      * simpl.
        rewrite transpose_empty_result_list.
        cases x; reflexivity.
      * erewrite pad_list_result_shape_id. reflexivity.
        eapply result_has_shape_repeat.
        eapply result_has_shape_repeat_gen_pad. lia.
Qed.

Lemma add_result_gen_pad_r : forall r1 r2 r3,
    add_result r1 r2 r3 ->
    forall sh,
    r2 = gen_pad sh ->
    result_has_shape r1 sh ->
    r1 = r3.
Proof.
  eapply (add_result_mut (fun r1 r2 r3 H =>
                            forall sh,
                            r2 = gen_pad sh ->
                            result_has_shape r1 sh -> r1 = r3)
                         (fun r1 r2 r3 H =>
                            forall sh,
                            (V r2) = gen_pad sh ->
                            result_has_shape (V r1) sh -> r1 = r3)).
  - intros. invert H0. simpl in *. invert H. invert a. auto. auto.
  - intros. cases sh. simpl in *. discriminate.
    eapply H in H0; eauto. subst. eauto.
  - intros. cases sh. simpl in *. discriminate.
    simpl in *. invert H1. cases n. simpl in *. discriminate.
    invert H4.
    invert H2.
    specialize (H sh). propositional. subst. f_equal.
    specialize (H0 (length xs1::sh)). simpl in *. propositional.
    eapply H. eapply forall_result_has_shape. eauto. eauto.
  - intros. auto.
Qed.

Lemma forall_firstn_flatten_result : forall l k n m sh,
    result_has_shape (V l) (n::m::sh) ->
    Forall (fun x0 => x0 = gen_pad (m::sh)) (firstn k l) ->
    Forall (fun x0 => x0 = gen_pad sh) (firstn (k * m) (flatten_result l)).
Proof.
  induct l; intros.
  - simpl. rewrite firstn_nil. econstructor.
  - simpl. invert H. cases a. invert H6.
    rewrite firstn_app.
    pose proof H6. eapply result_has_shape_length in H. rewrite H.
    rewrite mul_comm.
    rewrite <- mul_pred_r.
    eapply Forall_app. split.
    + cases k. rewrite mul_0_r. econstructor.
      invert H0. simpl in H3. invert H3.
      eapply forall_firstn. eapply Forall_repeat. eauto.
    + rewrite mul_comm.
      eapply IHl. eapply forall_result_has_shape. eauto. eauto.
      cases k. simpl in *. econstructor. simpl in *. invert H0. eauto.
Qed.

Lemma forall_firstn_rev_flatten_result : forall l k n m sh,
    result_has_shape (V l) (n::m::sh) ->
    Forall (fun x0 => x0 = gen_pad (m::sh)) (firstn k (rev l)) ->
    Forall (fun x0 => x0 = gen_pad sh) (firstn (k * m)
                                               (rev (flatten_result l))).
Proof.
  induct l; intros.
  - simpl. rewrite firstn_nil. econstructor.
  - invert H. cases a. invert H6.
    simpl. rewrite rev_app_distr. rewrite firstn_app.
    pose proof H6. eapply result_has_shape_length in H.
    repeat rewrite rev_length.
    erewrite result_has_shape_length.
    2: { eapply result_has_shape_flatten. eapply forall_result_has_shape.
         eauto. reflexivity. }
    rewrite <- mul_sub_distr_r.
    eapply Forall_app. split.
    + eapply IHl. eapply forall_result_has_shape; eauto.
      simpl in H0. rewrite firstn_app in H0. eapply Forall_app in H0. invs.
      eauto.
    + simpl in *. rewrite firstn_app in H0. eapply Forall_app in H0. invs.
      cases (k - length l).
      * simpl. econstructor.
      * simpl. rewrite firstn_all2.
        2: { rewrite rev_length. eapply Nat.le_add_r. }
        rewrite rev_length in *. rewrite Heq in *. simpl in *. invert H2.
        invert H3. rewrite rev_repeat. eapply Forall_repeat. eauto.
Qed.

Lemma firstn_transpose_result_list : forall m0 l k n m sh,
    result_has_shape (V l) (n::m::sh) ->
    0 < n ->
    0 < m ->
    m0 <= m ->
    firstn k (transpose_result_list l m0) =
      map (fun x => V (get_col l (x+(m - m0))))
          (nat_range (Nat.min m0 k)).
Proof.
  induct m0; intros.
  - simpl. rewrite min_0_l. rewrite firstn_nil. reflexivity.
  - invert H. lia. cases x. invert H7.
    cases v. invert H7. lia.
    cases k. simpl. rewrite min_0_r. reflexivity.
    rewrite <- succ_min_distr.
    unfold nat_range. simpl nat_range_rec. rewrite map_cons.
    simpl firstn. pose proof H7.
    eapply result_has_shape_length in H. cases m. lia. invert H.
    f_equal. erewrite IHm0.
    2: { econstructor. reflexivity. eauto. eauto. }
    2: { lia. }
    2: { lia. }
    2: { lia. }
    rewrite map_nat_range_rec_shift.
    f_equal. eapply functional_extensionality. intros. f_equal.
    f_equal.
    rewrite add_sub_assoc. 
    rewrite add_sub_assoc. lia.
    lia.
    lia.
Qed.    

Lemma skipn_transpose_result_list : forall m0 l k n m sh,
    result_has_shape (V l) (n::m::sh) ->
    0 < n ->
    0 < m ->
    m0 <= m ->
    skipn k (transpose_result_list l m0) =
      map (fun x => V (get_col l x))
          (nat_range_rec (m0-k) (m-m0+k)).
Proof.
  induct m0; intros.
  - simpl. rewrite skipn_nil. reflexivity.
  - invert H. lia. cases x. invert H7.
    cases v. invert H7. lia.
    cases m. invert H7.
    simpl skipn.
    pose proof H7. eapply result_has_shape_length in H. invert H.
    cases k.
    + simpl skipn. rewrite add_0_r. rewrite sub_0_r.
      simpl nat_range_rec. rewrite map_cons. f_equal.
      specialize IHm0 with (k:=0).
      simpl in *|-. erewrite IHm0.
      rewrite add_0_r in *. rewrite sub_0_r in *.
      2: econstructor; eauto.
      2: lia.
      2: lia.
      2: lia.
      f_equal. f_equal. lia.
    + simpl skipn. erewrite IHm0.
      2: econstructor; eauto.
      2: lia.
      2: lia.
      2: lia.
      f_equal. f_equal. lia.
Qed.

Lemma firstn_rev_transpose_result_list : forall m0 l k n m sh,
    result_has_shape (V l) (n::m::sh) ->
    0 < n ->
    0 < m ->
    m0 <= m ->
    firstn k (rev (transpose_result_list l m0)) =
      map (fun x => V (get_col l (m -1 - x)))
          (nat_range (Nat.min m0 k)).
Proof.
  induct m0; intros.
  - simpl. rewrite min_0_l. rewrite firstn_nil. reflexivity.
  - invert H. lia. cases x. invert H7.
    cases v. invert H7. lia.
    cases k. simpl. rewrite min_0_r. reflexivity.
    rewrite <- succ_min_distr.
    rewrite firstn_rev.
    erewrite result_has_shape_length.
    2: { eapply result_has_shape_transpose_result_list.
         2: { econstructor; eauto. }
         lia. }
    rewrite sub_succ.
    simpl transpose_result_list.
    cases m. lia.
    pose proof H7.
    eapply result_has_shape_length in H. simpl in H. invert H.
    cases (m0-k).
    + eapply sub_0_le in Heq.
      replace (min m0 k) with m0 by lia.
      simpl skipn. simpl rev.
      unfold nat_range.
      rewrite succ_nat_range_rec_app_end. rewrite add_0_r.
      rewrite map_app.
      simpl map at 2. rewrite sub_0_r. f_equal.
      replace (nat_range_rec m0 0) with (nat_range m0) by auto.
      replace m0 with (min m0 k) at 2 by lia.
      erewrite <- IHm0.
      2: econstructor; eauto.
      2: lia.
      2: lia.
      2: lia.
      rewrite firstn_all2.
      reflexivity.
      rewrite rev_length.
      erewrite result_has_shape_length.
      2: { eapply result_has_shape_transpose_result_list.
           2: econstructor; eauto. lia. }
      lia.
    + replace (min m0 k) with k by lia.
      simpl skipn.
      assert (length (transpose_result_list (V (r :: v) :: xs) m0) = m0).
      { erewrite result_has_shape_length.
        2: eapply result_has_shape_transpose_result_list.
        reflexivity. 2: econstructor; eauto. lia. }
      rewrite <- (rev_involutive (transpose_result_list _ _)).
      rewrite skipn_rev.
      rewrite rev_involutive. rewrite rev_length. rewrite H.
      erewrite IHm0.
      2: econstructor; eauto.
      2: lia.
      2: lia.
      2: lia.
      f_equal. f_equal. lia.
Qed.

Lemma forall_gen_pad_get_col : forall l i m sh,
    Forall (fun x => x = gen_pad (m::sh)) l ->
    i < m ->
    get_col l i = gen_pad_list (length l::sh).
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. f_equal. invert H.
    simpl.
    rewrite nth_error_repeat by lia. f_equal.
    eauto.
Qed.

Lemma forall_get_col_relate_pads_rev_gen_pad : forall l i sh m n a,
  Forall
    (fun r' =>
       match r' with
       | S _ => False
       | V l =>
           Forall (fun x => x = gen_pad sh) (firstn n (rev l))
       end) l ->
  m - n <= i < m ->
  result_has_shape (V l) (a::m::sh) ->
  get_col l i = gen_pad_list (length l::sh).
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. invert H. cases a. propositional.
    eapply result_has_shape_forall in H1. invert H1.
    pose proof H3 as Hsh.
    eapply result_has_shape_length in H3.
    rewrite <- (firstn_skipn (m-n) v).
    cases (m - n).
    + simpl in *.
      eapply forall_eq_gen_pad in H4. simpl in *.
      rewrite firstn_all2 in H4.
      2: { rewrite rev_length. lia. }
      rewrite rev_length in *.
      rewrite <- rev_repeat in H4.
      assert (rev (rev v) =
                rev (rev (repeat (gen_pad sh) (Datatypes.length v)))).
      { rewrite H4; auto. }
      repeat rewrite rev_involutive in H. 
      cases (nth_error v i).
      eapply nth_error_In in Heq0.
      rewrite H in *.
      eapply repeat_spec in Heq0. subst. f_equal.
      eapply IHl. eauto.
      2: { eapply forall_result_has_shape; eauto. }
      rewrite repeat_length in *. lia.
      eapply nth_error_None in Heq0. lia.
    + rewrite nth_error_app2.
      2: { rewrite firstn_length. lia. }
      rewrite firstn_length. rewrite H3.
      replace (min (Datatypes.S n0) m) with (Datatypes.S n0) by lia.
      eapply forall_eq_gen_pad in H4.
      rewrite firstn_rev in H4.
      rewrite <- (rev_involutive (skipn (Datatypes.S n0) v)).
      rewrite <- Heq. rewrite H3 in *.
      rewrite H4.
      simpl gen_pad_list. rewrite rev_repeat.
      rewrite rev_length. rewrite skipn_length.
      rewrite H3.
      replace (m - (m-n)) with n by lia.
      rewrite nth_error_repeat.
      f_equal.
      2: { lia. }
      eapply IHl. eauto.
      2: { eapply forall_result_has_shape; eauto. }
      lia.      
Qed.

Lemma get_col_rev : forall l i sh n m,
    result_has_shape (V l) (n::m::sh) ->
    i < m ->
    get_col l (m - 1 - i) = get_col (map (fun x =>
                                            match x with
                                            | S _ => x
                                            | V l => V (rev l)
                                            end) l) i.
Proof.
  induct l; intros.
  - reflexivity.
  - simpl get_col at 1. invert H. cases a. invert H6.
    cases v.
    + invert H6. simpl. rewrite nth_error_empty. reflexivity. 
    + assert (i < m-1 \/ m-1 <= i) as Hcase by lia.
      inversion Hcase as [ Hcase1 | Hcase2 ]; clear Hcase.
      * cases (nth_error (r :: v) (m -1 - i)).
        2: { eapply nth_error_None in Heq.
             erewrite result_has_shape_length in Heq by eauto.
             assert (i = 0) by lia. 
             assert (m = 0) by lia.
             subst. invert H6. }
        erewrite IHl.
        2: eapply forall_result_has_shape; eauto.
        pose proof Heq. eapply nth_error_Some in Heq.
        simpl in Heq.
        rewrite map_cons. simpl.
        cases (nth_error (rev v ++ [r]) i).
        2: { eapply nth_error_None in Heq0. rewrite app_length in *.
             rewrite rev_length in *. simpl in *.
             pose proof H6. eapply result_has_shape_length in H1.
             simpl in H1. subst. lia. }
        f_equal.
        rewrite nth_error_rev in H.
        2: { eapply result_has_shape_length in H6. lia. }
        2: { lia. }
        simpl in *. rewrite H in *. invs. auto. lia.
      *  replace (m-1-i) with 0 by lia. simpl.
         pose proof H6. eapply result_has_shape_length in H. subst.
         simpl in *. rewrite sub_0_r in *.
         rewrite nth_error_app2.
         2: { rewrite rev_length. lia. }
         rewrite rev_length.
         erewrite <- IHl.
         2: eapply forall_result_has_shape; eauto.
         2: lia.
         simpl. rewrite sub_0_r.
         replace (i - Datatypes.length v) with 0 by lia. simpl.
         f_equal.
         replace (Datatypes.length v - i) with 0 by lia. simpl.
         reflexivity.
Qed.

Lemma get_col_empty : forall l x a b sh,
    result_has_shape (V l) (a::b::sh) ->
    b <= x ->
    get_col l x = [].
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. invert H. cases a. invert H6.
    pose proof H6. eapply result_has_shape_length in H. subst.
    cases (nth_error v x).
    + eapply nth_error_Some in Heq. lia.
    + reflexivity.
Qed.

Lemma firstn_get_col : forall l n x a b sh,
    result_has_shape (V l) (a::b::sh) ->
    firstn n (get_col l x) = get_col (firstn n l) x.
Proof.
  induct l; intros.
  - simpl. rewrite firstn_nil. reflexivity.
  - simpl. invert H. cases a. invert H5.
    cases (nth_error v x).
    + cases n. reflexivity. simpl.
      rewrite Heq. f_equal. eapply IHl.
      eapply forall_result_has_shape; eauto.
    + rewrite firstn_nil.
      eapply nth_error_None in Heq.
      erewrite get_col_empty.
      reflexivity.
      eapply forall_result_has_shape. eapply forall_firstn.
      econstructor; eauto. rewrite firstn_length.
      simpl. reflexivity. eapply result_has_shape_length in H5. lia.
Qed.

Lemma rev_get_col : forall l x a b sh,
    result_has_shape (V l) (a::b::sh) ->
    x < b ->
    rev (get_col l x) = get_col (rev l) x.
Proof.
  induct l; intros.
  - reflexivity.
  - simpl rev at 1. invert H. cases a. invert H6.
    cases (nth_error v x).
    + simpl. erewrite get_col_app.
      2: { eapply result_has_shape_rev.
           eapply forall_result_has_shape; eauto. }
      2: { eapply forall_result_has_shape. econstructor. eauto. eauto.
           simpl. reflexivity. }
      2: lia.
      erewrite IHl. 2: eapply forall_result_has_shape; eauto.
      2: lia.
      f_equal. simpl. rewrite Heq. reflexivity.
    + eapply nth_error_None in Heq. eapply result_has_shape_length in H6.
      lia.
Qed.    

Lemma skipn_get_col : forall l n x a b sh,
    result_has_shape (V l) (a::b::sh) ->
    skipn n (get_col l x) = get_col (skipn n l) x.
Proof.
  induct l; intros.
  - simpl. rewrite skipn_nil. reflexivity.
  - simpl. invert H. cases a. invert H5.
    cases (nth_error v x).
    + cases n.
      * simpl. rewrite Heq. reflexivity.
      * simpl. eapply IHl. eapply forall_result_has_shape; eauto.
    + rewrite skipn_nil.
      eapply nth_error_None in Heq.
      erewrite get_col_empty.
      reflexivity.
      eapply forall_result_has_shape. eapply forall_skipn.
      econstructor; eauto. rewrite skipn_length.
      simpl. reflexivity. eapply result_has_shape_length in H5. lia.
Qed.

Lemma forall_get_col_relate_pads_gen_pad : forall l i sh m n a,
  Forall
    (fun r' =>
       match r' with
       | S _ => False
       | V l =>
           Forall (fun x => x = gen_pad sh) (firstn n l)
       end) l ->
  i < min m n ->
  result_has_shape (V l) (a::m::sh) ->
  get_col l i = gen_pad_list (length l::sh).
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. invert H. cases a. propositional.
    eapply result_has_shape_forall in H1. invert H1.
    pose proof H3 as Hsh.
    eapply result_has_shape_length in H3.
    rewrite <- (firstn_skipn n v).
    rewrite nth_error_app1.
    2: { rewrite firstn_length. lia. }
    eapply forall_eq_gen_pad in H4. rewrite H4. simpl.
    rewrite nth_error_repeat.
    2: { rewrite firstn_length. lia. }
    f_equal. erewrite IHl. reflexivity.
    eauto.
    2: eapply forall_result_has_shape; eauto.
    lia.
Qed.

Lemma add_list_firstn : forall l1 l2 l3,
    add_list l1 l2 l3 ->
    forall n,
    add_list (firstn n l1) (firstn n l2) (firstn n l3).
Proof.
  induct 1; intros; simpl; try rewrite firstn_nil; try econstructor.
  cases n. simpl. econstructor.
  simpl. econstructor. eauto. eauto.
Qed.  

Lemma result_has_shape_map_rev : forall l sh,
  result_has_shape (V l) sh ->
  result_has_shape
    (V
       (map (fun x1 : result => match x1 with
                                | S _ => x1
                                | V l4 => V (rev l4)
                                end) l)) sh.
Proof.
  induct l; intros.
  - simpl. eauto.
  - simpl. invert H.
    cases a.
    + econstructor. rewrite map_length. reflexivity. eauto.
      eapply result_has_shape_forall. eapply IHl.
      eapply forall_result_has_shape. eauto. reflexivity.
    + econstructor. rewrite map_length. reflexivity.
      eapply result_has_shape_rev. eauto.
      eapply result_has_shape_forall. eapply IHl.
      eapply forall_result_has_shape. eauto. reflexivity.
Qed.

Lemma skipn_stride_flatten_result : forall n k l c xs,
    result_has_shape (V l) (c::k::xs) ->
    skipn (n * k) (flatten_result l) =
      flatten_result (skipn n l).
Proof.
  induct n; intros.
  - simpl. reflexivity.
  - simpl. cases l. invert H. simpl. rewrite skipn_nil. reflexivity.
    invert H. cases r. invert H5.
    simpl.
    rewrite skipn_app.
    rewrite skipn_all2.
    2: { erewrite result_has_shape_length by eauto. lia. }
    simpl. erewrite result_has_shape_length by eauto.
    rewrite Nat.add_comm. rewrite Nat.add_sub. eapply IHn.
    eapply forall_result_has_shape. eauto. reflexivity.
Qed.

Lemma firstn_stride_flatten_result : forall n k l c xs,
    result_has_shape (V l) (c::k::xs) ->
    firstn (n * k) (flatten_result l) =
      flatten_result (firstn n l).
Proof.
  induct n; intros.
  - simpl. reflexivity.
  - simpl. cases l. invert H. simpl. rewrite firstn_nil. reflexivity.
    invert H. cases r. invert H5.
    simpl.
    rewrite firstn_app.
    rewrite firstn_all2.
    2: { erewrite result_has_shape_length by eauto. lia. }
    simpl. f_equal. erewrite result_has_shape_length by eauto.
    rewrite Nat.add_comm. rewrite Nat.add_sub. eapply IHn.
    eapply forall_result_has_shape. eauto. reflexivity.
Qed.

Lemma forall_firstn_flatten_result_lt :
  forall l x a P n m xs,
    Forall
      (fun r' : result =>
         match r' with
         | S _ => False
         | V l => Forall P (firstn a l)
         end) (firstn (Datatypes.S x) l) ->
    result_has_shape (V l) (n::m::xs) ->
    a < m ->
    Forall P (firstn a (flatten_result l)).
Proof.
  induct l; intros.
  - simpl. rewrite firstn_nil. eauto.
  - simpl in *. cases a. invert H0. invert H7.
    rewrite firstn_app. invert H0. erewrite result_has_shape_length by eauto.
    pose proof (Nat.sub_0_le a0 m). inversion H0. erewrite H3 by lia.
    simpl. rewrite app_nil_r. invert H.
    eauto.
Qed.

Lemma flatten_result_app : forall l1 l2 ,
    Forall (fun x => match x with
                     | S _ => False
                     | _ => True
                     end ) l1 ->
    Forall (fun x => match x with
                     | S _ => False
                     | _ => True
                     end ) l2 ->
    flatten_result (l1 ++ l2)%list =
      (flatten_result l1 ++ flatten_result l2)%list.
Proof.
  induct l1; intros.
  - reflexivity.
  - simpl.
    invert H.
    cases a. propositional.
    erewrite IHl1; eauto.
    rewrite app_assoc. eauto.
Qed.

Lemma forall_flatten_result_rev_all : forall P l,
    Forall P (flatten_result (rev l)) ->
    Forall (fun x => match x with
                     | S _ => False
                     | _ => True
                     end ) l ->
    Forall P (flatten_result l).
Proof.
  induct l; intros.
  - econstructor.
  - simpl in *. invert H0. cases a. propositional.
    erewrite flatten_result_app in *.
    2: { eapply Forall_rev. eauto. }
    2: { econstructor; eauto. }
    repeat rewrite @Forall_app in *.  invs. simpl in *.
    rewrite @app_nil_r in *. propositional.
Qed.

Lemma forall_firstn_rev_flatten_result_lt :
  forall l x a P n m xs,
    Forall
          (fun r' : result =>
           match r' with
           | S _ => False
           | V l =>
               Forall P (firstn a (rev l))
           end) (firstn (Datatypes.S x) l) ->
    result_has_shape (V l) (n::m::xs)->
    a < m ->
    Forall P (firstn a (rev (flatten_result (rev l)))).
Proof.
  induct l ;intros.
  - simpl. rewrite firstn_nil. auto.
  - simpl. invert H0.
    erewrite flatten_result_app.
    2: { eapply Forall_rev. eapply Forall_impl. 2: eauto. simpl. intros.
         invert H0. lia. auto. }
    2: { invert H7.  lia. econstructor. eauto. eauto. }
    rewrite rev_app_distr. rewrite firstn_app.
    erewrite rev_length. erewrite result_has_shape_length.
    2: { simpl. cases a. invert H7. rewrite app_nil_r. eauto. }
    simpl. cases a. invert H7. rewrite app_nil_r.
    rewrite Forall_app. invert H. split. eauto.
    pose proof (Nat.sub_0_le a0 m). inversion H. erewrite H2 by lia.
    econstructor.
Qed.

Lemma forall_firstn_skipn_rev_flatten_result :
  forall l P l2 b n m xs x,
    Forall
          (fun r' : result =>
           match r' with
           | S _ => False
           | V l =>
               Forall P
                 (firstn l2 (skipn b (rev l)))
           end) (firstn (Datatypes.S x) l) ->
    result_has_shape (V l) (n::m::xs) ->
    b < m ->
    l2 <= m - b ->
  Forall P
         (firstn l2 (skipn b (rev (flatten_result (rev l))))).
Proof.
  induct l; intros.
  - simpl. rewrite skipn_nil. rewrite firstn_nil. auto.
  - simpl. invert H0.
    erewrite flatten_result_app.
    2: { eapply Forall_rev. eapply Forall_impl. 2: eauto.
          simpl. intros. invert H0. lia. eauto. }
    2: { econstructor. invert H8. lia. eauto. eauto. }
    rewrite rev_app_distr. rewrite skipn_app. rewrite firstn_app.
    rewrite skipn_length. repeat rewrite rev_length.
    simpl length. cases a. invert H8. simpl. rewrite app_nil_r.
    erewrite result_has_shape_length by eauto.
    pose proof (Nat.sub_0_le b m). inversion H0. erewrite H4 by lia.
    replace (l2 - (m - b)) with 0 by lia.
    simpl. rewrite app_nil_r. invert H. eauto.
Qed.
  
Lemma forall_firstn_skipn_flatten_result :
  forall l P l0 a l1 n m xs,
    Forall
      (fun r' : result =>
         match r' with
         | S _ => False
         | V l => Forall P (firstn l1 (skipn a l))
         end) (firstn (Datatypes.S l0) l) ->
    result_has_shape (V l) (n::m::xs) ->
    a < m ->
    l1 <= m - a ->
    Forall P (firstn l1 (skipn a (flatten_result l))).
Proof.
  induct l; intros.
  - simpl. rewrite skipn_nil. rewrite firstn_nil. eauto.
  - simpl in *. invert H0. cases a. invert H8. invert H.
    rewrite skipn_app. rewrite firstn_app. rewrite Forall_app.
    split. auto.
    rewrite skipn_length. erewrite result_has_shape_length by eauto.
    pose proof (Nat.sub_0_le a0 m). inversion H. erewrite H3 by lia.
    replace (l1 - (m - a0)) with 0 by lia.
    econstructor.
Qed.

Lemma forall_flatten_result : forall l P,
  Forall
         (fun r' =>
          match r' with
          | S _ => False
          | V l => Forall P l
          end) l ->
  Forall P (flatten_result l).
Proof.
  induct l; intros.
  - econstructor.
  - simpl in *. invert H. cases a. propositional.
    rewrite Forall_app. split. eauto.
    eapply IHl; eauto.
Qed.

Lemma forall_flatten_result_rev : forall l P n m xs,
  Forall
         (fun r' =>
          match r' with
          | S _ => False
          | V l => Forall P l
          end) l ->
  result_has_shape (V l) (n::m::xs) ->
  Forall P (flatten_result (rev l)).
Proof.
  induct l; intros.
  - econstructor.
  - simpl in *. invert H. cases a. propositional. invert H0.
    erewrite flatten_result_app.
    2: { eapply Forall_rev. eapply Forall_impl. 2: eauto. simpl. intros.
         invert H. eauto. eauto. }
    2: { econstructor; auto. }
    rewrite Forall_app. split. eapply IHl; eauto.
    eapply forall_result_has_shape; eauto. simpl. rewrite app_nil_r. eauto.
Qed.

Lemma flatten_result_split_nat_range_rec_gen : forall n k l a sh c,
  0 < k ->
  n * k <= length l ->
  result_has_shape (V l) (a::sh) ->
  flatten_result
    (map
       (fun x : nat =>
        V
          (firstn k (skipn (k * (x-c)) l) ++
           repeat (gen_pad sh)
             (min (Datatypes.length l mod k - (k * (x-c) - Datatypes.length l))
                (k - (Datatypes.length l - k * (x-c))))))
       (nat_range_rec n c)) = 
  firstn (n * k) l.
Proof.
  induct n; intros.
  - simpl. reflexivity.
  - simpl in *. rewrite firstn_add.
    cases l. simpl in *. lia. simpl length. rewrite sub_diag.
    rewrite mul_0_r. rewrite sub_0_l. simpl skipn. repeat rewrite sub_0_r.
    simpl length in *.
    replace (k - Datatypes.S (Datatypes.length l)) with 0 by lia.
    rewrite min_0_r. simpl repeat at 1. rewrite app_nil_r.
    f_equal.
    erewrite <- IHn with (sh:=sh) (c:=c+1).
    rewrite skipn_length. simpl length.
    2: lia.
    2: { simpl in *. rewrite skipn_length. simpl length in *. lia. }
    2: { eapply forall_result_has_shape. eapply forall_skipn.
         invert H1. econstructor. eauto. eauto. reflexivity. }
    f_equal. eapply map_nat_range_rec_extensionality.
    intros. f_equal. rewrite skipn_skipn.
    replace (k * (x - (c + 1)) + k) with (k * (Datatypes.S (x - (c + 1))))
      by lia.
    f_equal. f_equal. f_equal.
    rewrite sub_add_distr. f_equal. lia.
    replace ((Datatypes.S (Datatypes.length l) - k) mod k) with
      (Datatypes.S (Datatypes.length l) mod k).
    2: { erewrite (Nat.div_mod_eq (Datatypes.S (Datatypes.length l)) k)
      by lia.
         rewrite Div0.add_mod_idemp_r by lia.
         rewrite add_sub_swap.
         2: { cases (Datatypes.S (Datatypes.length l) / k).
              - eapply div_small_iff in Heq. lia. lia.
              - rewrite mul_comm. simpl. eapply le_add_r. }
         rewrite <- mul_pred_r.
         rewrite Div0.add_mod_idemp_r by lia.
         rewrite Div0.add_mod by lia. symmetry. rewrite Div0.add_mod by lia.
         rewrite Nat.mul_comm. rewrite Div0.mod_mul.
         rewrite Nat.mul_comm. rewrite Div0.mod_mul. reflexivity. }
    rewrite sub_add_distr.
    f_equal. f_equal. f_equal.
    repeat rewrite mul_sub_distr_l. rewrite mul_1_r.
    lia.
    symmetry.
    rewrite <- sub_add_distr.
    replace (k + k * (x - c - 1)) with (k * (x - c - 1 + 1)) by lia.
    f_equal. f_equal. f_equal. lia.
Qed.

Lemma forall_gen_pad_flatten_result : forall l k sh n,
    result_has_shape (V l) (n::k::sh) ->
    Forall (fun x => x = gen_pad sh) (flatten_result l) ->
    Forall (fun x => x = gen_pad (k:: sh)) l .
Proof.
  induct l; intros.
  - econstructor.
  - simpl in *. invert H. cases a. invert H6. rewrite Forall_app in H0.
    invert H0. econstructor.
    eapply forall_eq_gen_pad in H. rewrite H. simpl.
    erewrite result_has_shape_length by eauto. reflexivity.
    eapply IHl. eapply forall_result_has_shape. eauto. reflexivity. eauto.
Qed.

Lemma flatten_result_map_V {X} : forall (l : list X) f,
    flatten_result (map (fun x => V (f x)) l) =
      concat (map f l).
Proof.
  induct l ;intros.
  - reflexivity.
  - simpl. f_equal. eauto.
Qed.

Lemma flatten_result_split_result : forall l k sh,
    result_has_shape (V l) (length l::sh) ->
    0 < k ->
    flatten_result (split_result k l) =
      (l ++ (repeat (gen_pad sh) ((k-(length l mod k)) mod k)))%list.
Proof.
  unfold split_result. simpl. intros.
  cases l. simpl. rewrite div_ceil_n_0 by lia. rewrite Div0.mod_0_l by lia.
  rewrite sub_0_r. rewrite Div0.mod_same by lia. reflexivity.
  invert H. pose proof H6. eapply result_has_shape_result_shape_nat in H6.
  rewrite H6. rewrite <- gen_pad_filter_until_0.
  unfold nat_range.
  cases (length (r::l) mod k).
  - rewrite sub_0_r.
    rewrite Div0.mod_same by lia. simpl repeat. rewrite app_nil_r.
    pose proof flatten_result_split_nat_range_rec_gen.
    specialize H1
      with (n:=(Datatypes.length (r :: l) //n k)) (k:=k)
           (l:=(r::l)) (sh:=sh) (c:=0) (a:=length (r::l)).
    erewrite map_nat_range_rec_extensionality in H1.
    2: { intros. rewrite sub_0_r.
         rewrite Heq. rewrite sub_0_l. rewrite min_0_l.
         simpl. rewrite app_nil_r. reflexivity. }
    rewrite H1. 2: lia.
    pose proof Heq. eapply mod_0_iff_ceil_eq_floor_0 in H2. 2: lia.
    rewrite firstn_all2. reflexivity.
    rewrite H2. eapply Div0.div_exact in Heq. lia. 
    pose proof Heq. eapply mod_0_iff_ceil_eq_floor_0 in H2. 2: lia.
    rewrite H2. eapply Div0.div_exact in Heq. lia. 
    simpl. econstructor; eauto.
  - rewrite <- Heq.
    cases (Datatypes.length (r :: l) //n k).
    { unfold div_ceil_n in *. simpl in Heq0. rewrite sub_0_r in Heq0.
      replace k with (1*k) in Heq0 at 1 by lia. rewrite Nat.add_comm in Heq0.
      rewrite div_add_l in Heq0 by lia. lia. }
    pose proof (ceil_sub_floor_le_1 (length (r :: l)) k).
    cases (Datatypes.length (r :: l) //n k - Datatypes.length (r :: l) / k).
    { eapply mod_0_iff_ceil_sub_floor_0 in Heq1. lia. lia. }
    assert (n1 = 0) by lia. subst.
    rewrite succ_nat_range_rec_app_end. rewrite add_0_r.
    rewrite map_app. simpl map at 2.
    erewrite flatten_result_app.
    simpl flatten_result at 2. rewrite app_nil_r.
    assert (n0 = (length (r::l)) / k) by lia. subst.
    rewrite app_comm_cons. rewrite skipn_app. rewrite firstn_app.
    rewrite skipn_repeat. rewrite firstn_repeat.
    rewrite skipn_length. repeat rewrite app_assoc. f_equal.
    2: { f_equal. simpl length in *.
         replace (k * (Datatypes.S (length l) / k) -
                    Datatypes.S (length l)) with 0.
         2: { pose proof (Div0.mul_div_le (Datatypes.S (length l)) k). lia. }
         rewrite sub_0_r. rewrite <- Div0.mod_eq by lia.
         rewrite min_l. reflexivity.
         eapply Div0.mod_le. }
    pose proof flatten_result_split_nat_range_rec_gen.
    specialize H2
      with (n:=(Datatypes.length (r :: l) / k)) (k:=k)
           (l:=(r::l)) (sh:=sh) (c:=0) (a:=length (r::l)).
    erewrite map_nat_range_rec_extensionality in H2.
    2: { intros. rewrite sub_0_r.
         rewrite (Nat.div_mod_eq (Datatypes.length (r::l)) k) at 2.
         rewrite sub_add_distr.
         rewrite <- mul_sub_distr_l.
         replace (x - Datatypes.length (r :: l) / k) with 0 by lia.
         rewrite mul_0_r. rewrite sub_0_l. rewrite sub_0_r.
         rewrite (Nat.div_mod_eq (Datatypes.length (r::l)) k) at 2.
         rewrite add_sub_swap.
         2: { eapply mul_le_mono_l. lia. }
         rewrite <- mul_sub_distr_l.
         rewrite sub_add_distr.
         cases (Datatypes.length (r :: l) / k - x). lia.
         rewrite (mul_comm k (Datatypes.S n0)). simpl.
         rewrite sub_add_distr. rewrite sub_diag. rewrite sub_0_l.
         rewrite min_0_r. simpl. rewrite app_nil_r. reflexivity. }
    erewrite map_nat_range_rec_extensionality.
    2: { intros. rewrite skipn_app. rewrite firstn_app.
         rewrite skipn_repeat. rewrite firstn_repeat.
         rewrite skipn_length.
         rewrite (Nat.div_mod_eq (Datatypes.length (r::l)) k) at 2.
         rewrite sub_add_distr.
         rewrite <- mul_sub_distr_l.
         replace (x - Datatypes.length (r :: l) / k) with 0 by lia.
         rewrite mul_0_r. rewrite sub_0_l. rewrite sub_0_r.
         rewrite (Nat.div_mod_eq (Datatypes.length (r::l)) k) at 2.
         rewrite add_sub_swap.
         2: { eapply mul_le_mono_l. lia. }
         rewrite <- mul_sub_distr_l.
         rewrite sub_add_distr.
         cases (Datatypes.length (r :: l) / k - x). lia.
         rewrite (mul_comm k (Datatypes.S n0)). simpl.
         rewrite sub_add_distr. rewrite sub_diag. rewrite sub_0_l.
         rewrite min_0_r. simpl. rewrite app_nil_r. reflexivity. }
    rewrite H2. 2: lia.
    2: { pose proof (Div0.mul_div_le (length (r::l)) k). lia. }
    rewrite firstn_all2 with (n:=k).
    2: { rewrite skipn_length. rewrite <- Div0.mod_eq by lia.
         pose proof (Nat.mod_upper_bound (length (r::l)) k). lia. }
    symmetry.
    rewrite <- firstn_skipn with (n:=(Datatypes.length (r :: l) / k * k))
                                 (l:=(r::l)) at 1.
    f_equal. f_equal. lia.
    simpl. econstructor; eauto.
    eapply Forall_map. eapply Forall_forall. propositional.
    econstructor; eauto.
Qed. 

Lemma skipn_split_result : forall l n k a sh,
    0 < k ->
    n * k <= length l ->
    result_has_shape (V l) (a :: sh) ->
    flatten_result (skipn n (split_result k l)) =
      skipn (n * k) (l++ repeat (gen_pad sh) ((k - a mod k) mod k))%list.
Proof.
  intros. erewrite <- skipn_stride_flatten_result.
  2: { eapply result_has_shape_split_result. lia. eauto. }
  erewrite flatten_result_split_result.
  2: { eapply forall_result_has_shape.
       eapply result_has_shape_forall in H1. eauto. reflexivity. }
  2: lia.
  erewrite result_has_shape_length. 2: eauto.
  reflexivity.
Qed.

Lemma firstn_split_result : forall l n k a sh,
    0 < k ->
    n * k <= length l ->
    result_has_shape (V l) (a :: sh) ->
    flatten_result (firstn n (split_result k l)) = firstn (n * k) l.
Proof.
  intros. erewrite <- firstn_stride_flatten_result.
  2: { eapply result_has_shape_split_result. lia. eauto. }
  erewrite flatten_result_split_result.
  2: { eapply forall_result_has_shape.
       eapply result_has_shape_forall in H1. eauto. reflexivity. }
  2: lia.
  erewrite result_has_shape_length. 2: eauto.
  rewrite firstn_app.
  replace (n * k - Datatypes.length l) with 0 by lia. simpl.
  rewrite app_nil_r. reflexivity.
Qed.

Lemma forall_gen_pad_flatten_result_inv :
  forall (l : list result) (k : nat) (sh : list nat) (n : nat),
       result_has_shape (V l) (n :: k :: sh) ->
       Forall (fun x : result => x = gen_pad (k :: sh)) l ->
       Forall (fun x : result => x = gen_pad sh) (flatten_result l).
Proof.
  induct l; intros.
  - simpl. econstructor.
  - invert H. cases a. invert H6. simpl.
    rewrite Forall_app. split. invert H0. simpl in *. invert H2.
    eapply Forall_repeat. eauto.
    eapply IHl. eapply forall_result_has_shape. eauto. reflexivity.
    invert H0. eauto.
Qed.

Lemma flatten_result_nat_range_rec : forall a n l k,
    flatten_result
      (map (fun x => V (firstn k (skipn (k * x) l)))
           (nat_range_rec a n)) = firstn (a*k) (skipn (n*k) l).
Proof.
  induct a; intros.
  - simpl. reflexivity.
  - simpl. rewrite Nat.add_comm. rewrite firstn_add.
    f_equal. rewrite mul_comm. reflexivity.
    rewrite IHa. simpl. rewrite skipn_skipn. reflexivity.
Qed.

Lemma nth_error_split_result : forall l k x,
    0 < k ->
    x < length l ->
    match
      nth_error (split_result k l) (x / k)
    with
    | Some (V v) => nth_error v (x mod k) 
    | _ => None
    end = nth_error l x .
Proof.
  intros. unfold split_result.
  cases l.
  - simpl in *. rewrite div_ceil_n_0 by lia. rewrite Div0.mod_0_l by lia.
    rewrite sub_0_r. simpl. repeat rewrite nth_error_empty. reflexivity.
  - simpl. cases (Datatypes.S (Datatypes.length l) //n k).
    + unfold div_ceil_n in *. simpl in *. rewrite sub_0_r in *.
      replace k with (1*k) in Heq at 1 by lia.
      rewrite Nat.add_comm in Heq. rewrite div_add_l in Heq by lia.
      lia.
    + unfold nat_range. rewrite nth_error_map.
      rewrite nth_error_nat_range_rec.
      2: { rewrite <- Heq.
           eapply Nat2Z.inj_lt.
           rewrite Nat2Z.inj_div by lia.
           eapply floor_lt_nat_ceil_mono_l. lia.
           simpl in *. lia. lia. lia. }
      simpl.
      rewrite nth_error_firstn_elim.
      2: { eapply Nat.mod_upper_bound. lia. }
      rewrite app_comm_cons. rewrite skipn_app.
      simpl length.
      rewrite nth_error_app1.
      2: { rewrite skipn_length. simpl length in *.
           eapply Nat.add_lt_mono_l with (p:=k * (x / k)).
           rewrite <- div_mod by lia.
           rewrite Nat.add_comm. 
           rewrite Nat.sub_add. lia.
           pose proof (Div0.mul_div_le x k). lia. }
      rewrite nth_error_skipn_mod by lia. reflexivity.
Qed.

