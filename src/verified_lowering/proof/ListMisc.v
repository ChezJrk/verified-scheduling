From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Zdiv.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
Import ListNotations.
Open Scope list_scope.

From ATL Require Import Sets FrapWithoutSets.

Fixpoint filter_until l k :=
  match l with
  | x::xs => if (x =? k)%nat
             then [x]
             else x::filter_until xs k
  | _ => []
  end.

Lemma Forall_repeat {X} : forall n a (P : X -> Prop),
    P a ->
    Forall P (repeat a n).
Proof.
  induct n; intros; simpl in *; constructor; auto.
Qed.

Fixpoint in_bool_Z (l : list Z) (v : Z) : bool :=
  match l with
  | x::xs => orb (Z.eqb x v) (in_bool_Z xs v)
  | [] => false
  end.

Fixpoint map2 {X Y Z}(f : X -> Y -> Z) (l1 : list X) (l2 : list Y) : list Z :=
  match l1,l2 with
  | x::xs,y::ys => (f x y)::(map2 f xs ys)
  | _,_ => []
  end.

Lemma fold_left_cons {X} : forall (f : X -> X -> X) x xs a,
    (forall a b, f a b = f b a) ->
    (forall a b c, f a (f b c) = f (f a b) c) ->
    fold_left f (x::xs) a = f x (fold_left f xs a).
Proof.
  induct xs; intros.
  - simpl in *. eauto.
  - pose proof H. eapply IHxs in H.
    simpl. rewrite <- H. 2: auto.
    simpl. f_equal.
    rewrite H1. rewrite H0. rewrite (H1 a0). reflexivity.
Qed.

Lemma fold_left_list {X Y} : forall (f : X -> Y -> X) (l1 l2 : list Y) x,
    l1 = l2 ->
    fold_left f l1 x = fold_left f l2 x.
Proof. intros. subst. reflexivity. Qed.

Inductive no_dup {X} : list X -> Prop :=
| NoDupNil : no_dup []
| NoDupCons : forall x xs,
    no_dup xs ->
    ~ In x xs ->
    no_dup (x::xs).

Lemma Forall_impl_weak {X} : forall (P Q : X -> Prop) (l : list X),
    (forall x, In x l -> P x -> Q x) ->
    Forall P l ->
    Forall Q l.
Proof.
  induct l; intros.
  - constructor.
  - constructor. invert H0.
    apply H. constructor. auto.
    auto. eapply IHl.
    propositional.
    eapply H. simpl. propositional. auto.
    invert H0. auto.
Qed.

Lemma not_In_cons_l1 {X} : forall (x : X) xs l l2,
    In (x :: l) (map2 cons xs l2) ->
    In x xs.
Proof.
  induct xs; intros; cases l2.
  - invert H.
  - invert H.
  - invert H.
  - simpl in *. invert H.
    + invert H0. propositional.
    + right. eapply IHxs. eassumption.
Qed.

Lemma not_In_cons_l2 {X} : forall (x : X) xs l l2,
    In (x :: l) (map2 cons xs l2) ->
    In l l2.
Proof.
  induct xs; intros; cases l2.
  - invert H.
  - invert H.
  - invert H.
  - simpl in *. invert H.
    + invert H0. propositional.
    + right. eapply IHxs. eassumption.
Qed.

Lemma no_dup_map2_cons_l1 {X} : forall (l1 : list X),
    no_dup l1 ->
    forall l2,
    no_dup (map2 cons l1 l2).
Proof.
  induct 1; intros.
  - constructor.
  - cases l2.
    + constructor.
    + simpl. constructor. auto.
      unfold not in *. intros. apply H0.
      eapply not_In_cons_l1. eassumption.
Qed.

Lemma no_dup_map2_cons_l2 {X} : forall (l2 : list (list X)),
    no_dup l2 ->
    forall l1,
    no_dup (map2 cons l1 l2).
Proof.
  induct 1; intros; cases l1; try now constructor.
  simpl. constructor. auto. unfold not in *. intros.
  apply H0.
  eapply not_In_cons_l2. eassumption.
Qed.

Lemma map2_app {X Y Z} :
  forall (a1 a2 : list X) (b1 b2 : list Y) (f : X -> Y -> Z),
    length a1 = length b1 ->
    map2 f (a1++a2)%list (b1++b2)%list = (map2 f a1 b1 ++ map2 f a2 b2)%list.
Proof.
  induct a1; intros; cases b1; simpl in *; try lia.
  - auto.
  - f_equal. apply IHa1. lia.
Qed.

Lemma succ_repeat_app_end {X} : forall n (k : X),
    repeat k (Datatypes.S n) = (repeat k n ++ [k])%list.
Proof.
  induct n; intros.
  - reflexivity.
  - simpl in *.
    rewrite IHn. reflexivity.
Qed.

Lemma map2_cons_repeat {X} : forall l (k : X) n,
    length l = n ->
    map2 cons (repeat k n) l = map (fun x => k::x) l.
Proof.
  induct l; intros.
  - simpl in *. subst.
    reflexivity.
  - simpl in *. invert H.
    simpl. f_equal. eauto.
Qed.

Lemma no_dup_app {X} : forall (l1 l2 : list X),
    no_dup l1 ->
    no_dup l2 ->
    (Forall (fun x => ~ In x l1) l2) ->
    no_dup (l1++l2)%list.
Proof.
  induct l1; intros; cases l2; try rewrite app_nil_r; simpl in *.
  - econstructor.
  - invert H0. econstructor; eauto.
  - auto.
  - econstructor. eapply IHl1. invert H. auto. auto.
    eapply Forall_impl. 2: eassumption. intros. simpl in *. propositional.
    invert H1. invert H. unfold not. intros.
    eapply in_app_or in H.
    invert H. propositional.
    invert H1. propositional.
    eapply Forall_forall in H5. 2: eassumption.
    propositional.
Qed.    

Lemma length_concat {X} : forall (l : list (list X)) k,
    (Forall (fun x => length x = k) l) ->
    length (concat l) = (length l) * k.
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. rewrite length_app. invert H.
    f_equal.
    eapply IHl. auto.
Qed.

Lemma map2_repeat {X Y Z} : forall (l : list Y) (k : X) n (f : X -> Y -> Z),
    length l = n ->
    map2 f (repeat k n) l = map (fun x => f k x) l.
Proof.
  induct l; intros.
  - simpl in *. subst.
    reflexivity.
  - simpl in *. invert H.
    simpl. f_equal. eauto.
Qed.

Lemma In_iff_in {X} : forall l (x : X),
    In x l <-> x \in constant l.
Proof. induct l; propositional. Qed.

Lemma not_In_empty_map_cons : forall k l,
    ~ In [] (map (fun x : list Z => k :: x) l).
Proof.
  induct l; unfold not; intros.
  - invert H.
  - simpl in *.
    invert H. discriminate. eauto.
Qed.

Lemma not_In_empty_map2_cons {X} : forall (l1 : list X) l2,
    ~ In [] (map2 cons l1 l2).
Proof.
  induct l1; unfold not; intros; cases l2.
  - invert H.
  - invert H.
  - invert H.
  - simpl in H. invert H. discriminate. eapply IHl1. eassumption.
Qed.  

Lemma In_cons_map_cons {X} : forall l (z : X) x k,
    In (z :: x) (map (fun x => k :: x) l) <->
    z = k /\ In x l.
Proof.
  induct l; propositional; simpl in *.
  - invert H.
  - invert H.
    + invert H0. auto.
    + eapply IHl in H0. firstorder.
  - invert H.
    + invert H0. firstorder.
    + eapply IHl in H0. firstorder.
  - subst. invert H1.
    firstorder. right. eapply IHl. firstorder.
Qed.

Lemma map_map2 {X Y Z K} :
  forall (l1 : list X) (l2 : list Y) (f : Z -> K) (g : X -> Y -> Z),
    map f (map2 g l1 l2) = map2 (fun a b => f (g a b)) l1 l2.
Proof.
  induct l1; intros; cases l2; try reflexivity.
  simpl. f_equal. eauto.
Qed.

Lemma map2_map_l1 {X Y Z K} : forall (l1 : list X) (l2 : list Y)
                                   (f : Z -> Y -> K) (g : X -> Z),
    map2 (fun a b => f (g a) b) l1 l2 = map2 f (map g l1) l2.
Proof.
  induct l1; intros; cases l2; try reflexivity.
  simpl. f_equal. eauto.
Qed.

Lemma map_repeat {X Y} : forall k (l : X) (f : X -> Y),
    map f (repeat l k) = repeat (f l) k.
Proof.
  induct k; intros.
  - reflexivity.
  - simpl. f_equal. auto.
Qed.

Lemma In_eq_list {X} : forall l1 l2 (x : X),
    l1 = l2 ->
    In x l1 ->
    In x l2.
Proof. intros. subst. auto. Qed.

Lemma map_match_map2_cons {X Y} :
  forall (l1 : list X) (l2 : list (list X)) (f : list X -> Y) g,
    map
      (fun l : list X =>
          match l with
          | [] => f l
          | x :: xs => g x xs
          end)
      (map2 cons l1 l2) = (map2 (fun a b => g a b) l1 l2).
Proof.
  induct l1; intros; cases l2; try reflexivity.
  simpl. f_equal. eauto.
Qed.

Fixpoint eq_list_Z (l1 l2 : list Z) :=
  match l1,l2 with
  | x::xs,y::ys => andb (Z.eqb x y) (eq_list_Z xs ys)
  | [],[] => true
  | _,_ => false
  end.

Fixpoint in_bool_list_Z (l : list (list Z)) (k : list Z) :=
  match l with
  | [] => false
  | x::xs =>
      orb (eq_list_Z x k) (in_bool_list_Z xs k)
  end.

Lemma filter_false_empty {X} : forall (l : list X),
    filter (fun _ => false) l = [].
Proof.
  induct l.
  - reflexivity.
  - simpl. auto.
Qed.

Lemma eq_list_Z_eq : forall l x,
    eq_list_Z l x = true ->
    l = x.
Proof.
  induct l; intros; cases x; simpl in *; auto; try discriminate.
  eapply andb_prop in H. invert H.
  eapply Z.eqb_eq in H0. f_equal; auto.
Qed.

Lemma eq_list_Z_id : forall x,
    eq_list_Z x x = true.
Proof.
  induct x; intros; simpl in *; auto; try discriminate.
  rewrite IHx. rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma eq_list_Z_neq : forall l x,
    eq_list_Z l x = false ->
    l <> x.
Proof.
  induct l; intros; cases x; simpl in *; auto; try discriminate.
  eapply andb_false_iff in H. invert H.
  eapply Z.eqb_neq in H0.
  unfold not. intros. invert H. firstorder.
  eapply IHl in H0.
  unfold not. intros. inversion H. firstorder.
Qed.

Lemma in_forall_map {X Y} : forall l1 domain x (f : X -> Y),
    Forall (fun x => In x domain) l1 ->
    In x (map f l1) ->
    In x (map f domain).
Proof.
  induct l1; intros.
  - invert H0.
  - simpl in *. invert H. invert H0.
    + eapply in_map. auto.
    + eapply IHl1; auto.
Qed.

Lemma eq_list_Z_comm : forall a b,
    eq_list_Z a b = eq_list_Z b a.
Proof.
  induct a; intros; cases b; simpl; auto.
  rewrite IHa. f_equal. rewrite Z.eqb_sym. reflexivity.
Qed.

Lemma forall_filter {X} : forall f l,
    Forall (fun x : X => f x = true) (filter f l).
Proof.
  induct l; intros.
  - econstructor.
  - simpl. 
    cases (f a).
    + econstructor. auto. auto.
    + auto.
Qed.

Lemma not_in_bool_list_Z_filter_empty : forall d2 a,
  in_bool_list_Z d2 a = false ->
  filter (eq_list_Z a) d2 = [].
Proof.
  induction d2; intros.
  - reflexivity.
  - simpl in *.
    eapply orb_false_elim in H.
    invert H. rewrite eq_list_Z_comm. rewrite H0.
    eauto.
Qed.

Lemma not_in_bool_Z_filter_empty : forall d2 a,
    in_bool_Z d2 a = false -> filter (Z.eqb a) d2 = [].
Proof.
  induction d2; intros.
  - reflexivity.
  - simpl in *.
    eapply orb_false_iff in H. invert H.
    rewrite Z.eqb_sym. rewrite H0. eauto.
Qed.

Lemma filter_map {X Y} : forall (l : list X) (g : X -> Y) (f : Y -> bool),
    filter f (map g l) = map g (filter (fun x => f (g x)) l).
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. cases (f (g a)).
    + simpl. rewrite IHl. auto.
    + rewrite IHl. auto.
Qed.

Lemma in_bool_Z_true : forall d1 x,
    In x d1 <->
    in_bool_Z d1 x = true.
Proof.
  induction d1; propositional.
  - invert H.
  - invert H.
  - simpl in *. invert H.
    + rewrite Z.eqb_refl. reflexivity.
    + eapply IHd1 in H0. rewrite H0.
      rewrite orb_comm. reflexivity.
  - simpl in *. eapply orb_true_iff in H. invert H.
    eapply Z.eqb_eq in H0. propositional.
    right. eapply IHd1. auto.
Qed.

Lemma in_bool_list_Z_true : forall d1 x,
    In x d1 <->
    in_bool_list_Z d1 x = true.
Proof.
  induction d1; propositional.
  - invert H.
  - invert H.
  - simpl in *. invert H.
    + rewrite eq_list_Z_id. reflexivity.
    + eapply IHd1 in H0. rewrite H0.
      rewrite orb_comm. reflexivity.
  - simpl in *. eapply orb_true_iff in H. invert H.
    eapply eq_list_Z_eq in H0. propositional.
    right. eapply IHd1. auto.
Qed.

Lemma filter_empty {X} : forall f (l : list X),
    (Forall (fun x => f x = false) l) ->
    filter f l = [].
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. invert H. rewrite H2. eauto.
Qed.

Lemma in_bool_list_Z_map_cons : forall l k z x0,
    (k <> z)%Z ->
    in_bool_list_Z (map (cons k) l) (z :: x0) = false.
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. pose proof H. eapply Z.eqb_neq in H.
    rewrite H.
    simpl. eauto.
Qed.
Lemma map_fst_combine {X Y} : forall (l1 : list X) (l2 : list Y),
    length l1 = length l2 ->
    map fst (combine l1 l2) = l1.
Proof.
  induction l1; intros; cases l2; simpl in *; try lia.
  - reflexivity.
  - rewrite IHl1 by lia. auto.
Qed.

Lemma map_snd_combine {X Y} : forall (l2 : list X) (l1 : list Y),
    length l1 = length l2 ->
    map snd (combine l1 l2) = l2.
Proof.
  induction l2; intros; cases l1; simpl in *; try lia.
  - reflexivity.
  - rewrite IHl2 by lia. auto.
Qed.

Lemma In_combine {X} : forall (x : X * X) l1 l2,
    l1 = l2 ->
    In x (combine l1 l2) ->
    exists a, In a l1 /\ x = (a,a).
Proof.
  induct l1; intros; cases l2.
  - invert H0.
  - invert H.
  - invert H.
  - invert H.
    simpl in H0. invert H0.
    + eexists. propositional. simpl. propositional.
    + eapply IHl1 in H. simpl. firstorder.
Qed.

Lemma length_combine {X} : forall (l1 l2 : list X),
    length l1 = length l2 ->
    length (combine l1 l2) = length l1.
Proof.
  induction l1; intros; cases l2; auto.
  simpl in *. rewrite IHl1 by auto. lia.
Qed.

Lemma combine_map {X Y} : forall (l1 l2 : list X) (f : X -> Y),
    combine (map f l1) (map f l2) =
      map (fun t => (f (fst t),f (snd t))) (combine l1 l2).
Proof.
  induct l1; intros.
  - reflexivity.
  - simpl. cases l2.
    + reflexivity.
    + simpl. f_equal. eauto.
Qed.  

Lemma map_dom_eq {X} : forall (dom0 : list (list Z)) (f g : list Z -> X),
    (forall idx : list Z, In idx dom0 -> f idx = g idx) ->
    map f dom0 = map g dom0.
Proof.
  induct dom0; auto; propositional.
  simpl. f_equal. eapply H. simpl. propositional.
  eapply IHdom0. intros. apply H.
  simpl. propositional.
Qed.

Lemma nth_error_Some {X} : forall n (l : list X) val,
  nth_error l n = Some val ->
  0 <= n < length l.
Proof.
  induct n; intros; cases l; simpl in *; try discriminate.
  - lia.
  - eapply IHn in H. lia.
Qed.

Lemma forall_filter_weaken {X} : forall (l : list X) f g,
    Forall f l ->
    Forall f (filter g l).
Proof.
  induct 1; simpl; auto.
  cases (g x); eauto.
Qed.

Lemma map2_repeat2 {X Y Z} : forall l (f : X -> Y -> Z) k n,
    length l = n ->
    map2 f l (repeat k n) = map (fun x => f x k) l.
Proof.
  induct l; intros.
  - auto.
  - simpl.
    cases n. simpl in *. lia.
    simpl. f_equal. eauto.
Qed.

Lemma map_extensionality {X Y} : forall l (f g : X -> Y),
    (forall x, In x l -> f x = g x) ->
    map f l = map g l.
Proof.
  induct l; intros.
  - auto.
  - simpl. f_equal.
    eapply H. simpl. auto.
    eapply IHl.
    intros.
    eapply H. simpl. auto.
Qed.

Lemma nth_error_empty {X} : forall x,
    nth_error (@nil X) x = None.
Proof.
  intros; cases x; reflexivity.
Qed.

Lemma map2_cons_repeat_empty2 {X} : forall (l : list X) k,
    length l = k ->
    map2 cons l (repeat [] k) = map (fun x => [x]) l.
Proof.
  induct l; intros.
  reflexivity. simpl in *. subst. simpl. f_equal. eauto.
Qed.

Lemma length_map2 {X Y Z} : forall (f : X -> Y -> Z) l1 l2,
    length (map2 f l1 l2) = min (length l1) (length l2).
Proof.
  induct l1; intros.
  - simpl. lia.
  - simpl.
    cases l2. reflexivity.
    simpl.
    rewrite IHl1. lia.
Qed.

Lemma exists_0_map_of_nat : forall l,
    Exists (fun x => x = 0) l ->
    Exists (fun x => x = 0%Z) (map Z.of_nat l).
Proof.
  induct l; intros.
  - invert H.
  - invert H.
    + simpl. econstructor. reflexivity.
    + simpl. eapply IHl in H1.
      eapply Exists_cons_tl. auto.
Qed.

Lemma forall_nonneg_exists_zero_or_forall_pos : forall l,
    Forall (fun x : nat => x > 0) l \/ Exists (fun x => x = 0) l.
Proof.
  induct l; intros.
  - auto.
  - assert (a = 0 \/ a > 0) by lia. destruct H; eauto.
    destruct IHl; eauto.
Qed.

Lemma concat_repeat_empty {X} : forall n,
    concat (repeat (@nil X) n) = [].
Proof.
  induct n.
  - reflexivity.
  - simpl. auto.
Qed.

Lemma map_constant_repeat {X Y} : forall (l : list X) (k :Y),
    map (fun _ => k) l = repeat k (length l).
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. f_equal. auto.
Qed.

Lemma fold_left_map {X Y} : forall (f : X -> Y -> X) (g : Y -> Y) l x,
    fold_left f (map g l) x = fold_left (fun b a => f b (g a)) l x.
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. rewrite IHl by auto. auto.
Qed.

Lemma map2_f_l1 {X Y}: forall l1 l2 (f : X -> Y),
    map2 (fun a0 b => f a0 :: b) l1 l2 =
      map2 cons (map f l1) l2.
Proof.
  induct l1; intros.
  - reflexivity.
  - simpl. cases l2. reflexivity.
    f_equal. eauto.
Qed.

Lemma fold_left_extensionality {X Y} : forall l (f g : X -> Y -> X) k,
    (forall acc x, In x l -> f acc x = g acc x) ->
    fold_left f l k = fold_left g l k.
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. rewrite H. 2: simpl; propositional.
    eapply IHl. intros. apply H. simpl. auto.
Qed.

Lemma forall_nonneg_exists_zero_or_forall_pos_Z :
  forall l ,
    Forall (fun x => 0 <= x)%Z l ->
    Forall (fun x => 0 < x)%Z l \/ Exists (fun x => x = 0)%Z l.
Proof.
  induct l; intros.
  - left. eauto.
  - invert H.
    eapply IHl in H3.
    assert (a = 0 \/ 0 < a)%Z by lia. invert H.
    + right. eauto.
    + invert H3.
      * left. eauto.
      * right. right. eauto.
Qed.

Lemma filter_until_0_id : forall l,
    Forall (fun x : nat => x > 0) l ->
    filter_until l 0 = l.
Proof.
  induct l; intros. auto.
  simpl. invert H. cases a. lia. simpl. f_equal. eauto.
Qed.

Lemma exists_0_map_Z_of_nat : forall l,
    Exists (fun x => x = 0) l ->
    Exists (fun x0 : Z => x0 = 0%Z) (map Z.of_nat l).
Proof.
  intros.
  eapply Exists_exists in H. invert H.
  eapply Exists_exists.
  exists (Z.of_nat 0). split.
  eapply in_map. invert H0. auto. invert H0. lia.
Qed.

Lemma exists_0_filter_until_0 : forall l,
    Exists (fun x => x = 0) l ->
    Exists (fun x0 : nat => x0 = 0) (filter_until l 0).
Proof.
  induct l; intros.
  - invert H.
  - invert H.
    + simpl. econstructor. eauto.
    + simpl. cases a. simpl. econstructor. eauto. simpl.
      right. eauto.
Qed.

Lemma fold_left_mul_assoc : forall l n x,
    fold_left Z.mul l (n * x)%Z = ((fold_left Z.mul l n) * x)%Z.
Proof.
  induct l; simplify.
  - auto.
  - replace (n*x*a)%Z with (n*a*x)%Z by lia.
    rewrite IHl. auto.
Qed.

Lemma fold_left_Zmul_exists_0 : forall l k,
    Exists (fun x => x = 0)%Z l ->
    fold_left Z.mul l k = 0%Z.
Proof.
  induct l; intros.
  - invert H.
  - invert H.
    + simpl. rewrite fold_left_mul_assoc. lia.
    + simpl. rewrite fold_left_mul_assoc. rewrite IHl. lia. eauto.
Qed.
  
Lemma fold_left_mul_assoc_nat : forall l b a,
    fold_left mul l (b * a) = fold_left mul l b * a.
Proof.
  induct l; intros.
  - reflexivity.
  - simpl.
    replace (b * a0 * a) with (b * a * a0) by lia.
    rewrite IHl. auto.
Qed.

Lemma Z_of_nat_fold_left_mul : forall l n,
    Z.of_nat (fold_left mul l n) = fold_left Z.mul (map Z.of_nat l) (Z.of_nat n).
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. rewrite IHl. rewrite Nat2Z.inj_mul. reflexivity.
Qed.

Fixpoint extract_Some {X} (l : list (option X)) :=
  match l with
  | Some v:: xs => v:: extract_Some xs
  | None::xs => extract_Some xs
  | _ => []
  end.                   

Lemma in_extract_Some {X} : forall (k : X) l,
    In (Some k) l <->
      In k (extract_Some l).
Proof.
  induct l; intros; split; intros.
  - invert H.
  - invert H.
  - simpl.
    cases a.
    + simpl.
      invert H. invert H0. auto. right. propositional.
    + simpl in *. invert H. discriminate. propositional.
  - simpl in *.
    cases a.
    + simpl.
      invert H. propositional. right. propositional.
    + right. propositional.
Qed.

Lemma extract_Some_app {X} : forall (l1 l2 : list (option X)),
    (extract_Some l1 ++ extract_Some l2)%list = extract_Some (l1++l2)%list.
Proof.
  induct l1; intros.
  - reflexivity.
  - simpl.
    cases a.
    + simpl. f_equal. eauto.
    + eauto.
Qed.

Lemma Z2Natid_list : forall sh,
    Forall (fun x => 0 <= x)%Z sh ->
    map Z.of_nat (map Z.to_nat sh) = sh.
Proof.
  induct sh; intros.
  - reflexivity.
  - invert H.
    simpl. rewrite Z2Nat.id by lia. f_equal. eauto.
Qed.    

Fixpoint truncl_list {X} n (l : list X) :=
  match n with
  | Datatypes.S n' => match l with
            | x::xs => truncl_list n' xs
            | _ => l
            end
  | _ => l
  end.

Lemma truncl_list_empty {X} : forall k,
    truncl_list k (@nil X) = [].
Proof. induct k; propositional. Qed.

Lemma filter_idempotent {X} : forall (l : list X) f,
    filter f (filter f l) =  filter f l.
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. cases (f a).
    + simpl. rewrite Heq. rewrite IHl. auto.
    + eauto.
Qed.

Lemma filter_until_0_cons : forall x l,
    0 < x ->
    filter_until (x::l) 0 = x::(filter_until l 0).
Proof. intros. simpl. cases x. lia. reflexivity. Qed.

Lemma filter_until_cons : forall x xs,
    0 < x ->
    filter_until (x::xs) 0 = x::(filter_until xs 0).
Proof.
  intros. simpl. cases x. lia. reflexivity.
Qed.

Lemma rev_repeat {X} : forall n (x : X),
    rev (repeat x n) = repeat x n.
Proof.
  induct n; intros; auto.
  replace (Datatypes.S n) with (n + 1) at 1 by lia.
  rewrite repeat_app. rewrite rev_app_distr.
  simpl. rewrite IHn. eauto.
Qed.

Lemma nth_error_truncl {X} :
  forall (l : list X) k z,
    nth_error (truncl_list k l) z =
      nth_error l (z + k).
Proof.
  induct l; intros.
  - rewrite truncl_list_empty.
    repeat rewrite nth_error_empty. auto.
  - simpl. cases (z + k).
    + simpl. assert (z = 0) by lia. subst. simpl.
      assert (k = 0) by lia. subst. simpl. reflexivity.
    + simpl. cases z.
      * simpl. rewrite add_0_l in Heq. subst. simpl.
        specialize (IHl n 0). simpl in *. auto.
      * simpl in *. invert Heq.
        cases k. simpl. f_equal. lia.
        simpl. specialize (IHl k (Datatypes.S z)). simpl in *.
        rewrite add_succ_r. simpl. auto.
Qed.

Lemma rev_arg_empty {X} : forall (l : list X),
    rev l = [] <->
    l = [].
Proof.
  induct l; propositional; auto; simpl in *.
  - eapply app_eq_nil in H1. invert H1. discriminate.
  - discriminate.
Qed.

Lemma truncl_list_app {X} : forall k (l1 l2 : list X),
    k <= length l1 ->
    truncl_list k (l1 ++ l2)%list = (truncl_list k l1 ++ l2)%list.
Proof.
  induct k; intros.
  - reflexivity.
  - simpl.
    cases l1. simpl in *. lia. simpl in *. eapply IHk. lia.
Qed.

Lemma truncl_list_length_empty {X} : forall k (l : list X),
    length l <= k <->
    truncl_list k l = [].
Proof.
  induct k; intros; split; intros; cases l; simpl in *.
  - reflexivity.
  - lia.
  - lia.
  - discriminate.
  - reflexivity.
  - eapply IHk. lia.
  - lia.
  - eapply IHk in H. lia.
Qed.

Lemma nth_error_truncr {X} :
  forall (l : list X) k z,
    z < length l - k ->
    nth_error (rev
                 (truncl_list
                    k (rev l))) z =
      nth_error l z.
Proof.
  induct l; intros.
  - simpl. rewrite truncl_list_empty.
    unfold rev.
    repeat rewrite nth_error_empty. auto.
  - simpl. cases z.
    + simpl.
      cases (rev (truncl_list k (rev l ++ [a]))).
      * erewrite rev_arg_empty in Heq.
        eapply truncl_list_length_empty in Heq.
        rewrite length_app in *. rewrite length_rev in *. simpl in Heq.
        simpl length in H. lia.
      * simpl length in H.
        assert (k = length l \/ k <> length l) by lia. invert H0.
        -- rewrite truncl_list_app in Heq.
           2: try rewrite length_rev; lia.
           rewrite rev_app_distr in Heq.
           simpl in Heq. invert Heq. auto.
        -- rewrite truncl_list_app in Heq.
           rewrite rev_app_distr in Heq.
           simpl in Heq. invert Heq. auto. 
           rewrite length_rev. lia.
    + simpl. simpl length in H.
      rewrite truncl_list_app by (rewrite length_rev; lia).
      rewrite rev_app_distr. simpl. eapply IHl. lia.
Qed.

Lemma list_nat_nonneg : forall sh,
    Exists (fun x => x = 0) sh \/ Forall (fun x => 0 < x) sh.
  induct sh; intros.
  - right. econstructor.
  - simpl. invert IHsh.
    + eauto.
    + cases a.
      * eauto.
      * right. econstructor. lia. eauto.
Qed.

Lemma truncl_list_app_l {X} :
  forall k (l1 l2 : list X),
    k <= length l1 ->
    truncl_list k (l1 ++ l2)%list = (truncl_list k l1 ++ l2)%list.
Proof.
  induct k; intros.
  - reflexivity.
  - simpl.
    cases l1. simpl in *. lia.
    simpl in *.
    rewrite IHk by lia.
    reflexivity.
Qed.    

Lemma truncl_list_repeat {X} : forall k (x : X) n,
    truncl_list k (repeat x n) = repeat x (n-k).
Proof.
  induct k; intros.
  - simpl. f_equal. lia.
  - simpl.
    cases n. reflexivity. simpl. auto.
Qed.

Lemma invert_app {X} : forall (l1 l2 l3 l4 : list X),
    (l1++l2 = l3++l4)%list ->
    length l1 = length l3 ->
    l1 = l3 /\ l2 = l4.
Proof.
  induct l1; intros.
  - simpl in *. cases l3; simpl in *; try lia. propositional.
  - cases l3. simpl in *; try lia.
    simpl in H. invert H.
    eapply IHl1 in H3. propositional. subst. auto. simpl in *. lia.
Qed.

Lemma forall_skipn {X} : forall (l : list X) n P,
    Forall P l ->
    Forall P (skipn n l).
Proof.
  induct l; intros.
  - rewrite skipn_nil. eauto.
  - cases n. simpl. eauto.
    invert H. simpl. eauto.
Qed.

Lemma forall_firstn {X} : forall (l : list X) n P,
    Forall P l ->
    Forall P (firstn n l).
Proof.
  induct l; intros.
  - rewrite firstn_nil. eauto.
  - cases n. simpl. eauto.
    invert H. simpl. econstructor. eauto. eauto.
Qed.

Lemma forall_firstn_sub {X} : forall x (l : list X) P k,
    Forall P (firstn x l) ->
    Forall P (firstn x (rev (skipn k (rev l)))).
Proof.
  induct x; intros.
  - simpl in *. eauto.
  - cases l. simpl in *. rewrite skipn_nil. eauto.
    simpl in H. invert H.
    simpl. rewrite skipn_app.
    assert (k < length l \/ k >= length l) as Hcase by lia.
    inversion Hcase as [ Hcase1 | Hcase2 ]; clear Hcase.
    + replace (k - length (rev l)) with 0.
      2: { rewrite length_rev. lia. }
      simpl. rewrite rev_app_distr. simpl. econstructor. eauto. eauto.
    + rewrite skipn_all2.
      2: { rewrite length_rev. lia. }
      simpl. rewrite length_rev.
      cases (k - length l). simpl. econstructor. auto.
      rewrite firstn_nil. auto.
      simpl. rewrite skipn_nil. simpl. eauto.
Qed.

Lemma skipn_repeat {X} : forall n m (x : X),
    skipn n (repeat x m) = repeat x (m-n).
Proof.
  induct n; intros.
  - simpl. rewrite sub_0_r. auto.
  - simpl. cases m. reflexivity. simpl. eauto.
Qed.

Lemma firstn_repeat {X} : forall n m (x : X),
    firstn n (repeat x m) = repeat x (min m n).
Proof.
  induct n; intros; cases m; auto.
  simpl. rewrite <- succ_min_distr. simpl. f_equal. eauto.
Qed.

Lemma repeat_cons {X} : forall n (x : X),
    repeat x (Datatypes.S n) = x::(repeat x n).
Proof. reflexivity. Qed.

Lemma nth_error_firstn {X} : forall (l : list X) x n r0,
  nth_error l x = Some r0 ->
  x < n ->
  In r0 (firstn n l).
Proof.
  induct l; intros.
  - rewrite @nth_error_empty in *. discriminate.
  - cases x. simpl in *. invert H.
    cases n. lia. simpl. propositional.
    simpl in *.
    cases n. lia. simpl. right. eapply IHl; eauto. lia.
Qed.

Lemma nth_error_firstn_rev {X} : forall (l : list X) x n r0,
    nth_error l x = Some r0 ->
    x >= (length l) - n ->
    In r0 (firstn n (rev l)).
Proof.
  induct l; intros.
  - rewrite @nth_error_empty in *. discriminate.
  - simpl.
    rewrite firstn_app. rewrite length_rev. simpl length in *.
    eapply in_or_app.
    cases x.
    + simpl in H. invert H.
      cases (n - length l). lia. simpl. propositional.
    + simpl in H.
      eapply IHl in H; eauto. lia.
Qed.

Lemma forall_filter_until_0_pos : forall l,
  Forall (fun x : nat => 0 < x) (filter_until l 0) ->
  Forall (fun x : nat => 0 < x) l.
Proof.
  induct l; intros.
  - econstructor.
  - simpl in *. cases a. simpl in *. invert H. lia. simpl in *.
    econstructor. lia. eapply IHl. invert H. auto.
Qed.

Lemma truncl_list_skipn {X} : forall n (l : list X),
    truncl_list n l = skipn n l.
Proof.
  induct n; intros.
  - reflexivity.
  - cases l. reflexivity.
    simpl in *. eauto.
Qed.

Lemma forall_firstn_skipn {X} : forall y (l : list X) k P,
    Forall P (firstn y l) ->
    Forall P (firstn (y - k) (skipn k l)).
Proof.
  induct y; intros.
  - simpl in *. eauto.
  - simpl firstn in H.
    cases l. simpl in *. rewrite skipn_nil. rewrite firstn_nil. auto.
    invert H.
    assert (k >= length (x::l) \/ k < length (x::l)) as Hcase by lia.
    inversion Hcase as [ Hcase1 | Hcase2 ]; clear Hcase.
    + rewrite skipn_all2 by lia.
      rewrite firstn_nil. econstructor.
    + rewrite firstn_skipn_comm.
      cases (Datatypes.S y - k).
      * rewrite add_0_r.
        rewrite skipn_firstn_comm.
        rewrite sub_diag. simpl. econstructor.
      * rewrite <- Heq.
        replace (k + (Datatypes.S y - k)) with (Datatypes.S y) by lia.
        simpl.
        cases k. simpl. econstructor. eauto. eauto.
        rewrite <- firstn_cons.
        rewrite skipn_firstn_comm.
        simpl. eauto.
Qed.    

Lemma skipn_skipn {X} : forall m n (l : list X),
    skipn n (skipn m l) = skipn (n + m) l.
Proof.
  induct m; intros.
  - rewrite add_0_r. reflexivity.
  - cases l. repeat rewrite skipn_nil. auto.
    rewrite skipn_cons.
    rewrite IHm.
    rewrite add_succ_r. reflexivity.
Qed.    

Lemma rev_skipn_rev_skipn {X} : forall m n (l : list X),
    rev (skipn n (rev (skipn m l))) =
      skipn m (rev (skipn n (rev l))).
Proof.
  induct m; intros.
  - reflexivity.
  - cases l. simpl. rewrite skipn_nil. reflexivity.
    rewrite skipn_cons. rewrite IHm.
    symmetry.
    rewrite skipn_rev with (x:=n). rewrite rev_involutive.
    cases (length (x::l) - n).
    + simpl.
      rewrite skipn_all2 with (n:=n).
      2: { rewrite length_rev. simpl length in *. lia. }
      rewrite skipn_nil. auto.
    + rewrite firstn_cons. rewrite skipn_cons.
      simpl length in Heq.
      assert (length l - n = n0) by lia.
      replace l with (rev (rev l)) at 1.
      2: rewrite rev_involutive; auto.      
      rewrite firstn_rev.
      rewrite length_rev.
      f_equal. f_equal. f_equal. lia.
Qed.    

Lemma forall_skipn_le {X} : forall m (l : list X) n P,
    Forall P (skipn n l) ->
    n <= m ->
    Forall P (skipn m l).
Proof.
  induct m; intros.
  - replace n with 0 in * by lia.
    eauto.
  - simpl in *. cases l.
    + eauto.
    + cases n. simpl in *. invert H. eapply forall_skipn. auto.
      eapply IHm; eauto. lia.
Qed.

Lemma forall_firstn_ge:
  forall {X : Type} (m : nat) (l : list X) (n : nat) (P : X -> Prop),
    Forall P (firstn n l) -> m <= n -> Forall P (firstn m l).
Proof.
  induct m; intros.
  - econstructor.
  - cases l. econstructor. simpl. cases n. lia. simpl in *. invert H.
    econstructor. eauto. eapply IHm. eauto. lia.
Qed.

Lemma exists_filter_until_0 : forall l,
  Exists (fun x => x = 0) l ->
  Exists (fun x2 => x2 = 0) (filter_until l 0).
Proof.
  induct l; intros.
  - invert H.
  - invert H.
    + simpl. econstructor. lia.
    + simpl. cases a. simpl. econstructor. lia.
      simpl. right. eauto.
Qed.

Lemma nth_error_rev {X} : 
  forall (l : list X) n m,
    length l = m ->
    n < m ->
    nth_error l (m-1-n) = nth_error (rev l) n.
Proof.
  induct l; intros.
  - simpl. repeat rewrite nth_error_empty. reflexivity.
  - simpl in *.
    cases m. lia. invert H. simpl.
    rewrite sub_0_r.
    cases (length l - n).
    + simpl. rewrite nth_error_app2.
      2: { rewrite length_rev. lia. }
      rewrite length_rev.
      assert (n = length l) by lia. subst. rewrite sub_diag.
      reflexivity.
    + simpl.
      rewrite nth_error_app1.
      2: { rewrite length_rev. lia. }
      erewrite <- IHl.
      2: reflexivity. 2: lia.
      f_equal. lia.
Qed.    

Lemma nat_list_all_pos_or_exists_0 : forall l,
    Forall (fun x => 0 < x) l \/ Exists (fun x => x = 0) l.
Proof.
  induct l; intros.
  - left. eauto.
  - cases a; simpl.
    + right. eauto.
    + invert IHl.
      left. econstructor; eauto. lia.
      right. right. propositional.
Qed.

Lemma in_skipn {X} : forall (l : list X) n x,
    In x (skipn n l) ->
    In x l.
Proof.
  induct l; intros.
  - rewrite skipn_nil in *. propositional.
  - cases n. simpl in *. eauto.
    simpl in H.
    simpl. eapply IHl in H. propositional.
Qed.    

Lemma length_ge_filter_until : forall l,
    length l >= length (filter_until l 0).
Proof.
  induct l; intros.
  - simpl. lia.
  - simpl. cases a; simpl in *; lia.
Qed.

Lemma exists_filter_until_0_0 : forall l,
    Exists (fun x => x = 0) (filter_until l 0) ->
    Exists (fun x => x = 0) l.
Proof.
  induct l; intros.
  - invert H.
  - simpl in *.
    cases a; simpl in *.
    + auto.
    + right. invert H. lia. eauto.
Qed.

Lemma forall_skipn_firstn {X} : forall n2 (l : list X) a c P,
    n2 <= a ->
    Forall P (skipn c (firstn a l)) ->
    Forall P (skipn c (firstn n2 l)).
Proof.
  induct n2; intros.
  - simpl in *. rewrite skipn_nil. econstructor.
  - cases l. simpl. rewrite skipn_nil. econstructor.
    simpl. cases a. lia. simpl in *.
    cases c.
    + simpl in *. invert H0. econstructor. eauto.
      specialize (IHn2) with (c:=0). simpl in *.
      eapply IHn2. 2: eauto. lia.
    + simpl in *. eapply IHn2. 2: eauto. lia.
Qed.

Lemma in_firstn {X} : forall x (l : list X) a,
    In a (firstn x l) ->
    In a l.
Proof.
  induct x; intros.
  - invert H.
  - cases l. eauto. simpl in *. invert H. propositional. right. eauto.
Qed.

Lemma forall_firstn_skipn_firstn {X} : forall n2 (l : list X) P c r,
  Forall P (firstn r (skipn c l)) ->
  Forall P (firstn r (skipn c (firstn n2 l))).
Proof.
  induct n2; intros.
  - simpl. rewrite skipn_nil. rewrite firstn_nil. eauto.
  - cases l. rewrite firstn_nil. rewrite skipn_nil. rewrite firstn_nil. eauto.
    simpl in *. cases c.
    + simpl in *. cases r. simpl. econstructor.
      simpl in *. invert H. econstructor. eauto.
      specialize (IHn2) with (c:=0). simpl in *. eauto.
    + simpl in *. eauto.
Qed.

Lemma nth_error_firstn_elim {X} : forall (l : list X) n k,
    n < k ->
    nth_error (firstn k l) n = nth_error l n.
Proof.
  intros. rewrite <- (firstn_skipn k l) at 2.
  assert (k < length l \/ length l <= k) by lia.
  invert H0.
  - rewrite nth_error_app1. auto.
    rewrite length_firstn. rewrite min_l by lia. lia.
  - rewrite firstn_all2 by auto.
    rewrite skipn_all2 by lia. rewrite app_nil_r. eauto.
Qed.

Lemma nth_error_skipn_mod {X} : forall x (l : list X) k,
    0 < k ->
    x < length l ->
    nth_error (skipn (k * (x / k)) l) (x mod k) = nth_error l x.
Proof.
  intros. symmetry. rewrite <- (firstn_skipn (k * (x / k)) l) at 1.
  rewrite nth_error_app2.
  2: { rewrite length_firstn. rewrite min_l.
       eapply Div0.mul_div_le.
       eapply le_trans.
       eapply Div0.mul_div_le. lia. }
  rewrite length_firstn.
  rewrite min_l.
  2: { eapply le_trans. eapply Div0.mul_div_le. lia. }
  rewrite Div0.mod_eq by lia. eauto.
Qed.

Lemma fold_left_mul_filter_until l n :
  fold_left mul (filter_until l 0) n = fold_left mul l n.
Proof.
  revert n. induction l; eauto.
  assert (0 = a \/ 0 < a) as [?|?] by lia.
  - subst. simpl. intros. rewrite fold_left_mul_assoc_nat. lia.
  - rewrite filter_until_0_cons by lia. simpl. auto.
Qed.
