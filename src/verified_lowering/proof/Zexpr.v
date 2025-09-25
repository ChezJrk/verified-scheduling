From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import ZArith.Zdiv.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
  
Require Import Coq.Logic.FunctionalExtensionality.

Set Warnings "-deprecate-hint-without-locality,-deprecated".
Import ListNotations.

From ATL Require Import FrapWithoutSets Div Tactics.
From Lower Require Import Array ListMisc Constant.

Open Scope string_scope.

Definition valuation := fmap string Z.

Inductive Zexpr :=
| ZPlus (a b : Zexpr)
| ZMinus (a b : Zexpr)
| ZTimes (a b : Zexpr)
| ZDivf (a b : Zexpr)
| ZDivc (a b : Zexpr)
| ZMod (a b : Zexpr)
| ZLit (a : Z)
| ZVar (x : string).
#[export] Hint Constructors Zexpr.

Declare Scope zexpr.
Notation "a + b" := (ZPlus a b) : zexpr.
Notation "a - b" := (ZMinus a b) : zexpr.
Notation "a * b" := (ZTimes a b) : zexpr.
Notation "a / b" := (ZDivf a b) : zexpr.
Notation "a // b" := (ZDivc a b) : zexpr.
Notation "a % b" := (ZMod a b) (at level 18) : zexpr.
Notation "'|' a '|'" := (ZLit a) (at level 10) : zexpr.
Notation "'!' a '!'" := (ZVar a) (at level 18) : zexpr.
Delimit Scope zexpr with z.

Fixpoint eval_Zexpr_Z (v : valuation) (e : Zexpr) : option Z :=
  match e with
  | ZPlus x y =>
      match eval_Zexpr_Z v x, eval_Zexpr_Z v y with
      | Some xz, Some yz => Some (xz+yz)%Z
      | _,_ => None
      end
  | ZMinus x y =>
      match eval_Zexpr_Z v x, eval_Zexpr_Z v y with
      | Some xz, Some yz => Some (xz-yz)%Z
      | _,_ => None
      end      
  | ZTimes x y =>
      match eval_Zexpr_Z v x, eval_Zexpr_Z v y with
      | Some xz, Some yz => Some (xz*yz)%Z
      | _,_ => None
      end
  | ZDivf x y =>
      match eval_Zexpr_Z v x, eval_Zexpr_Z v y with
      | Some xz, Some yz => Some (xz/yz)%Z
      | _,_ => None
      end      
  | ZDivc x y =>
      match eval_Zexpr_Z v x, eval_Zexpr_Z v y with
      | Some xz, Some yz => Some (xz//yz)%Z
      | _,_ => None
      end
  | ZMod x y =>
      match eval_Zexpr_Z v x, eval_Zexpr_Z v y with
      | Some xz, Some yz => Some (xz mod yz)%Z
      | _,_ => None
      end              
  | ZLit z => Some z
  | ZVar var => v $? var
  end.      

Inductive eval_Zexpr (v : valuation) : Zexpr -> Z -> Prop :=
| EvalZPlus : forall x y xz yz,
    eval_Zexpr v x xz ->
    eval_Zexpr v y yz ->
    eval_Zexpr v (ZPlus x y) (xz + yz)%Z
| EvalZMinus : forall x y xz yz,
    eval_Zexpr v x xz ->
    eval_Zexpr v y yz ->
    eval_Zexpr v (ZMinus x y) (xz - yz)%Z
| EvalZTimes : forall x y xz yz,
    eval_Zexpr v x xz ->
    eval_Zexpr v y yz ->
    eval_Zexpr v (ZTimes x y) (xz * yz)%Z
| EvalZDivf : forall x y xz yz,
    eval_Zexpr v x xz ->
    eval_Zexpr v y yz ->
    eval_Zexpr v (ZDivf x y) (xz / yz)%Z
| EvalZDivc : forall x y xz yz,
    eval_Zexpr v x xz ->
    eval_Zexpr v y yz ->
    eval_Zexpr v (ZDivc x y) (xz // yz)%Z
| EvalZMod : forall x y xz yz,
    eval_Zexpr v x xz ->
    eval_Zexpr v y yz ->
    eval_Zexpr v (ZMod x y) (xz mod yz)%Z
| EvalZLit : forall z,
    eval_Zexpr v (ZLit z) z
| EvalZVar : forall x z,
    v $? x = Some z ->
    eval_Zexpr v (ZVar x) z.
#[export] Hint Constructors eval_Zexpr.

Lemma eval_Zexpr_includes_valuation : forall v l0 zs,
    eval_Zexpr v l0 zs ->
    forall v',
      v $<= v' ->
      eval_Zexpr v' l0 zs.
Proof. induct 1; eauto. Qed.

Fixpoint in_bool (l : list var) (v : var) : bool :=
  match l with
  | x::xs => orb (String.eqb x v) (in_bool xs v)
  | [] => false
  end.

Lemma in_bool_filter : forall f l,
    in_bool (filter f l) = (fun x => andb (f x) (in_bool l x)).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  induct l.
  - simpl. rewrite andb_false_r. reflexivity.
  - simpl.
    cases (f a).
    + cases (a =? x).
      * simpl. rewrite Heq0.
        eapply String.eqb_eq in Heq0. subst.
        rewrite Heq. reflexivity.
      * simpl. rewrite IHl. rewrite Heq0.
        simpl. reflexivity.
    + cases (a =? x).
      * eapply String.eqb_eq in Heq0. subst.
        simpl. rewrite IHl. rewrite Heq.
        reflexivity.
      * simpl. rewrite IHl. reflexivity.
Qed.
        
Definition app_no_dups (l1 l2 : list var) : list var :=
  app l1 (filter (fun v => negb (in_bool l1 v)) l2).

Notation "l1 ++/ l2" := (app_no_dups l1 l2) (at level 37, left associativity).

Fixpoint vars_of_Zexpr (z : Zexpr) : list var :=
  match z with
  | ZPlus e1 e2 => vars_of_Zexpr e1 ++/ vars_of_Zexpr e2
  | ZMinus e1 e2 => vars_of_Zexpr e1 ++/ vars_of_Zexpr e2
  | ZTimes e1 e2 => vars_of_Zexpr e1 ++/ vars_of_Zexpr e2
  | ZDivf e1 e2 => vars_of_Zexpr e1 ++/ vars_of_Zexpr e2
  | ZDivc e1 e2 => vars_of_Zexpr e1 ++/ vars_of_Zexpr e2
  | ZMod e1 e2 => vars_of_Zexpr e1 ++/ vars_of_Zexpr e2
  | ZLit _ => []
  | ZVar x => [x]
  end.

Lemma filter_filter {X} : forall (l : list X) f g,
    filter f (filter g l) =
      filter (fun x => andb (f x) (g x)) l.
Proof.
  induct l; intros.
  - reflexivity.
  - simpl.
    cases (g a).
    + simpl in *. rewrite andb_true_r.
      rewrite IHl. reflexivity.
    + rewrite andb_false_r. auto.
Qed.

Definition eq_zexpr ez1 ez2 :=
  (forall v z,
    eval_Zexpr v ez1 z <-> eval_Zexpr v ez2 z)
  /\ vars_of_Zexpr ez1 = vars_of_Zexpr ez2.

Fixpoint flatten_shape_index (sh : list Zexpr) (i : list Zexpr) :=
  match sh with
  | n::m::ns =>
    match i with
    | x::xs =>
        let stride := fold_left ZTimes ns m in
        ZPlus (ZTimes x stride) (flatten_shape_index (m::ns) xs)
    | _ => ZLit 0%Z
    end
  | [n] =>
    match i with
    | [z] => z
    | _ => ZLit 0%Z
    end
  | _ => ZLit 0%Z
  end.

Arguments flatten_shape_index : simpl nomatch.

Inductive eval_Zexprlist : valuation -> list Zexpr -> list Z -> Prop :=
| EvalZNil : forall v, eval_Zexprlist v [] []
| EvalZCons : forall v x xs z zs,
    eval_Zexpr v x z ->
    eval_Zexprlist v xs zs ->
    eval_Zexprlist v (x::xs) (z::zs).
#[export] Hint Constructors eval_Zexprlist.

Lemma eval_Zexprlist_app : forall l1 v l1z,
    eval_Zexprlist v l1 l1z ->
    forall l2 l2z,
      eval_Zexprlist v l2 l2z ->
      eval_Zexprlist v (l1++l2) (l1z++l2z).
Proof.
  induct 1; intros.
  - repeat rewrite app_nil_l. auto.
  - repeat rewrite <- app_comm_cons.
    econstructor. auto.
    auto.
Qed.

Definition eq_Z_index_list (l1 l2 : list Zexpr) :=
  length l1 = length l2 /\
  Forall (fun t => eq_zexpr (fst t) (snd t))
         (combine l1 l2).  

Definition eq_Z_tuple_index_list (l1 l2 : list (Zexpr * Zexpr)) :=
  length l1 = length l2 /\
    eq_Z_index_list (map fst l1) (map fst l2) /\
    eq_Z_index_list (map snd l1) (map snd l2).

Ltac invsZ :=
  repeat
    match goal with
    | H : _ /\ _ |- _ => invert H
    | H : exists _, _ |- _ => invert H
    | H : eval_Zexprlist _ _ [] |- _ => invert H
    | H : eval_Zexprlist _ [] _ |- _ => invert H
    | H : eval_Zexprlist _ _ (_::_) |- _ => invert H
    | H : eval_Zexprlist _ (_::_) _ |- _ => invert H
    | H : eval_Zexpr _ (ZPlus _ _) _ |- _ => invert H
    | H : eval_Zexpr _ (ZMinus _ _) _ |- _ => invert H
    | H : eval_Zexpr _ (ZTimes _ _) _ |- _ => invert H
    | H : eval_Zexpr _ (ZDivf _ _) _ |- _ => invert H
    | H : eval_Zexpr _ (ZDivc _ _) _ |- _ => invert H
    | H : eval_Zexpr _ (ZMod _ _) _ |- _ => invert H
    | H : eval_Zexpr _ (ZLit _) _ |- _ => invert H
    | H : eval_Zexpr _ (ZVar _) _ |- _ => invert H
    | H : _ = (_,_) |- _ => invert1 H
    | H : Some _ = Some _ |- _ => invert H
  end.

Lemma eval_Zexpr_deterministic : forall v n nz1 nz2,
    eval_Zexpr v n nz1 ->
    eval_Zexpr v n nz2 ->
    nz1 = nz2.
Proof.
  induction n; intros; invsZ; f_equal; eauto.
  rewrite H2 in H1.
  inversion H1.
  reflexivity.
Qed.

Ltac eq_eval_Z :=
  repeat
    match goal with
    | H1 : eval_Zexpr ?v ?e ?a, H2 : eval_Zexpr ?v ?e ?b |- _ =>
      pose proof (eval_Zexpr_deterministic _ _ _ _ H1 H2); subst;
      clear H2
    end.


Lemma eval_Zexprlist_deterministic : forall v n nz1 nz2,
    eval_Zexprlist v n nz1 ->
    eval_Zexprlist v n nz2 ->
    nz1 = nz2.
Proof.
  induction n; intros; invsZ; f_equal; eauto.
  eq_eval_Z.
  reflexivity.
Qed.

Ltac eq_eval_Zlist :=
  repeat
    match goal with
    | H1 : eval_Zexprlist ?v ?e ?a, H2 : eval_Zexprlist ?v ?e ?b |- _ =>
      pose proof (eval_Zexprlist_deterministic _ _ _ _ H1 H2); subst;
      clear H2
  end.

Lemma eval_Zexpr_Z_eval_Zexpr : forall z v x,
    eval_Zexpr v z x <-> eval_Zexpr_Z v z = Some x.
Proof.
  induct z; intros.
  - split; intros; simpl in *.
    + invert H. eapply IHz1 in H2. eapply IHz2 in H4.
      rewrite H2, H4. reflexivity.
    + cases (eval_Zexpr_Z v z1); cases (eval_Zexpr_Z v z2);
        simpl in *; try discriminate.
      * invert H.
        econstructor. eapply IHz1. assumption. eapply IHz2. assumption.
  - split; intros; simpl in *.
    + invert H. eapply IHz1 in H2. eapply IHz2 in H4.
      rewrite H2, H4. reflexivity.
    + cases (eval_Zexpr_Z v z1); cases (eval_Zexpr_Z v z2);
        simpl in *; try discriminate.
      * invert H.
        econstructor. eapply IHz1. assumption. eapply IHz2. assumption.
  - split; intros; simpl in *.
    + invert H. eapply IHz1 in H2. eapply IHz2 in H4.
      rewrite H2, H4. reflexivity.
    + cases (eval_Zexpr_Z v z1); cases (eval_Zexpr_Z v z2);
        simpl in *; try discriminate.
      * invert H.
        econstructor. eapply IHz1. assumption. eapply IHz2. assumption.
  - split; intros; simpl in *.
    + invert H. eapply IHz1 in H2. eapply IHz2 in H4.
      rewrite H2, H4. reflexivity.
    + cases (eval_Zexpr_Z v z1); cases (eval_Zexpr_Z v z2);
        simpl in *; try discriminate.
      * invert H.
        econstructor. eapply IHz1. assumption. eapply IHz2. assumption.
  - split; intros; simpl in *.
    + invert H. eapply IHz1 in H2. eapply IHz2 in H4.
      rewrite H2, H4. reflexivity.
    + cases (eval_Zexpr_Z v z1); cases (eval_Zexpr_Z v z2);
        simpl in *; try discriminate.
      * invert H.
        econstructor. eapply IHz1. assumption. eapply IHz2. assumption.
  - split; intros; simpl in *.
    + invert H. eapply IHz1 in H2. eapply IHz2 in H4.
      rewrite H2, H4. reflexivity.
    + cases (eval_Zexpr_Z v z1); cases (eval_Zexpr_Z v z2);
        simpl in *; try discriminate.
      * invert H.
        econstructor. eapply IHz1. assumption. eapply IHz2. assumption.
  - split; intros; simpl in *; invert H; eauto.
  - split; intros; simpl in *; invert H; eauto.
Qed.

Lemma eq_eval_Zexpr_Z : forall z1 z2,
    eq_zexpr z1 z2 ->
    forall v,
      eval_Zexpr_Z v z1 = eval_Zexpr_Z v z2.
Proof.
  unfold eq_zexpr in *.
  intros.
  invert H. specialize (H0 v).
  cases (eval_Zexpr_Z v z1); cases (eval_Zexpr_Z v z2).
  - eapply eval_Zexpr_Z_eval_Zexpr in Heq.
    eapply eval_Zexpr_Z_eval_Zexpr in Heq0.
    f_equal. eapply H0 in Heq. eq_eval_Z. eauto.
  - eapply eval_Zexpr_Z_eval_Zexpr in Heq.
    eapply H0 in Heq.
    eapply eval_Zexpr_Z_eval_Zexpr in Heq.
    rewrite Heq in Heq0. discriminate.
  - eapply eval_Zexpr_Z_eval_Zexpr in Heq0.
    eapply H0 in Heq0.
    eapply eval_Zexpr_Z_eval_Zexpr in Heq0.
    rewrite Heq in Heq0.
    discriminate.
  - reflexivity.
Qed.

Lemma eq_zexpr_id : forall z1 z2,
    z1 = z2 ->
    eq_zexpr z1 z2.
Proof.
  induct z1; intros; subst; unfold eq_zexpr; split;
    try intros; try invert H; eq_eval_Z; try reflexivity.
Qed.
#[export] Hint Resolve eq_zexpr_id.

Lemma eq_zexpr_mul : forall x1 x2 y1 y2,
    eq_zexpr x1 x2 ->
    eq_zexpr y1 y2 ->
    eq_zexpr (x1 * y1)%z (x2 * y2)%z.
Proof.
  intros. unfold eq_zexpr in *. invsZ.
  split.
  - intros; split; intros.
    + invsZ. econstructor.
      eapply H0. auto.
      eapply H1. auto.
    + invsZ. econstructor.
      eapply H0. auto.
      eapply H1. auto.
  - simpl. f_equal; auto.
Qed.

Lemma eq_zexpr_mod : forall x1 x2 y1 y2,
    eq_zexpr x1 x2 ->
    eq_zexpr y1 y2 ->
    eq_zexpr (ZMod x1 y1)%z (ZMod x2 y2)%z.
Proof.
  intros. unfold eq_zexpr in *. invsZ.
  split.
  - intros; split; intros.
    + invsZ. econstructor.
      eapply H0. auto.
      eapply H1. auto.
    + invsZ. econstructor.
      eapply H0. auto.
      eapply H1. auto.
  - simpl. f_equal; auto.
Qed.

Lemma eq_zexpr_add : forall x1 x2 y1 y2,
    eq_zexpr x1 x2 ->
    eq_zexpr y1 y2 ->
    eq_zexpr (x1 + y1)%z (x2 + y2)%z.
Proof.
  intros. unfold eq_zexpr in *. invsZ.
  split.
  - intros; split; intros.
    + invsZ. econstructor.
      eapply H0. auto.
      eapply H1. auto.
    + invsZ. econstructor.
      eapply H0. auto.
      eapply H1. auto.
  - simpl. f_equal; auto.
Qed.

Lemma eq_zexpr_div : forall x1 x2 y1 y2,
    eq_zexpr x1 x2 ->
    eq_zexpr y1 y2 ->
    eq_zexpr (x1 / y1)%z (x2 / y2)%z.
Proof.
  intros. unfold eq_zexpr in *. invsZ.
  split.
  - intros; split; intros.
    + invsZ. econstructor.
      eapply H0. auto.
      eapply H1. auto.
    + invsZ. econstructor.
      eapply H0. auto.
      eapply H1. auto.
  - simpl. f_equal; auto.
Qed.

Lemma eq_zexpr_divc : forall x1 x2 y1 y2,
    eq_zexpr x1 x2 ->
    eq_zexpr y1 y2 ->
    eq_zexpr (x1 // y1)%z (x2 // y2)%z.
Proof.
  intros. unfold eq_zexpr in *. invsZ.
  split.
  - intros; split; intros.
    + invsZ. econstructor.
      eapply H0. auto.
      eapply H1. auto.
    + invsZ. econstructor.
      eapply H0. auto.
      eapply H1. auto.
  - simpl. f_equal; auto.
Qed.

Lemma eq_zexpr_sub : forall x1 x2 y1 y2,
    eq_zexpr x1 x2 ->
    eq_zexpr y1 y2 ->
    eq_zexpr (x1 - y1)%z (x2 - y2)%z.
Proof.
  intros. unfold eq_zexpr in *. invsZ.
  split.
  - intros; split; intros.
    + invsZ. econstructor.
      eapply H0. auto.
      eapply H1. auto.
    + invsZ. econstructor.
      eapply H0. auto.
      eapply H1. auto.
  - simpl. f_equal; auto.
Qed.

Lemma eq_zexpr_comm : forall x y,
    eq_zexpr x y -> eq_zexpr y x.
Proof.
  unfold eq_zexpr.
  intros.
  invsZ.
  split.
  - intros. split; intros; apply H0; auto.
  - auto.
Qed.

Lemma app_no_dups_empty_r : forall l,
    l ++/ [] = l.
Proof.
  unfold app_no_dups.
  simpl. apply app_nil_r.
Qed.

Lemma eq_zexpr_add_0_r : forall e,
    eq_zexpr e (e + | 0 |)%z.
Proof.
  intros.
  unfold eq_zexpr. propositional.
  - replace z with (z+0)%Z by lia. econstructor. eauto. econstructor.
  - invert H. invert H4. replace (xz+0)%Z with xz by lia. auto.
  - simpl. rewrite app_no_dups_empty_r. reflexivity.
Qed.

Lemma eq_zexpr_transitivity : forall e1 e2 e3,
    eq_zexpr e1 e2 ->
    eq_zexpr e2 e3 ->
    eq_zexpr e1 e3.
Proof.
  intros. unfold eq_zexpr in *.
  propositional.
  - eapply H. eapply H1. auto.
  - eapply H1. eapply H. auto.
  - rewrite H2. auto.
Qed.

Lemma eq_zexpr_plus : forall x1 x2 y1 y2,
    eq_zexpr x1 x2 ->
    eq_zexpr y1 y2 ->
    eq_zexpr (x1 + y1)%z (x2 + y2)%z.
Proof.
  intros. unfold eq_zexpr in *. invsZ.
  split.
  - intros; split; intros.
    + invsZ. econstructor.
      eapply H0. auto.
      eapply H1. auto.
    + invsZ. econstructor.
      eapply H0. auto.
      eapply H1. auto.
  - simpl. f_equal; auto.
Qed.

Lemma eq_zexpr_add_sub_id : forall x y,
    eq_zexpr (x + | y | - | y |)%z x.
Proof.
  unfold eq_zexpr. propositional.
  - invsZ. eq_eval_Z.
    rewrite Z.add_simpl_r. auto.
  - replace z with (z + y - y)%Z by lia.
    eauto.
  - simpl. repeat rewrite app_no_dups_empty_r. auto.
Qed.

Lemma eq_Z_index_list_id : forall l,
    eq_Z_index_list l l.
Proof.
  induct l.
  - econstructor; econstructor.
  - econstructor; invert IHl.
    reflexivity. simpl. econstructor. eauto. eauto.
Qed.

Lemma eq_Z_index_list_cons : forall x1 xs1 x2 xs2,
    (eq_Z_index_list xs1 xs2 /\ eq_zexpr x1 x2) <->
    eq_Z_index_list (x1::xs1) (x2::xs2).
Proof.
  induct xs1; intros; cases xs2; propositional.
  - econstructor. reflexivity. econstructor. simpl.
    auto. econstructor.
  - eapply eq_Z_index_list_id.
  - invert H. invert H1. auto.
  - invert H0. simpl in *. lia.
  - invert H. simpl in *. lia.
  - invert H. simpl in *. lia.
  - invert H0. simpl in *. lia.
  - invert H. simpl in *. lia.
  - invert H. simpl in *. lia.
  - invert H0; simpl in *. econstructor. simpl. lia.
    simpl. econstructor. eauto. auto.
  - invert H. simpl in *. econstructor.
    simpl. lia. invert H1. simpl. auto.
  - invert H. invert H1. eauto.
Qed.

Lemma eq_zexpr_fold_ZTimes : forall vars1 vars2 z2 z3,
    length vars1 = length vars2 ->
    eq_zexpr z2 z3 ->
    eq_Z_index_list vars1 vars2 ->
    eq_zexpr (fold_left ZTimes vars1 z2) (fold_left ZTimes vars2 z3).
Proof.
  induction vars1; intros; cases vars2; simpl in *; try lia.
  - auto.
  - rewrite <- eq_Z_index_list_cons in H1. invert H1.
    eapply IHvars1. auto.
    eapply eq_zexpr_mul; auto.
    auto.
Qed.

Lemma eq_zexpr_fold_accum {X} : forall (f : Zexpr -> X -> Zexpr) l z1 z2,
    eq_zexpr z1 z2 ->    
    (forall x1 x2 a, eq_zexpr x1 x2 -> eq_zexpr (f x1 a) (f x2 a)) ->
    eq_zexpr (fold_left f l z1) (fold_left f l z2).
Proof.
  induction l; intros.
  - auto.
  - simpl.
    eapply IHl. auto.
    auto.
Qed.

Definition flatten_index (index : list (Zexpr * Zexpr)) :=
  flatten_shape_index (map snd index) (map fst index).

Fixpoint partially_eval_Zexpr (v : valuation) (e : Zexpr) : Zexpr :=
  match e with
  | ZPlus x y => ZPlus (partially_eval_Zexpr v x) (partially_eval_Zexpr v y)
  | ZMinus x y => ZMinus (partially_eval_Zexpr v x) (partially_eval_Zexpr v y)
  | ZTimes x y => ZTimes (partially_eval_Zexpr v x) (partially_eval_Zexpr v y)
  | ZDivf x y => ZDivf (partially_eval_Zexpr v x) (partially_eval_Zexpr v y)
  | ZDivc x y => ZDivc (partially_eval_Zexpr v x) (partially_eval_Zexpr v y)
  | ZMod x y => ZMod (partially_eval_Zexpr v x) (partially_eval_Zexpr v y)
  | ZLit z => e
  | ZVar var => match v $? var with
                | Some val => ZLit val
                | _ => e
                end
  end.      

Fixpoint subst_var_in_Zexpr (v : var) (z : Z) (e : Zexpr) : Zexpr :=
  match e with
  | ZPlus x y => ZPlus (subst_var_in_Zexpr v z x) (subst_var_in_Zexpr v z y)
  | ZMinus x y => ZMinus (subst_var_in_Zexpr v z x) (subst_var_in_Zexpr v z y)
  | ZTimes x y => ZTimes (subst_var_in_Zexpr v z x) (subst_var_in_Zexpr v z y)
  | ZDivf x y => ZDivf (subst_var_in_Zexpr v z x) (subst_var_in_Zexpr v z y)
  | ZDivc x y => ZDivc (subst_var_in_Zexpr v z x) (subst_var_in_Zexpr v z y)
  | ZMod x y => ZMod (subst_var_in_Zexpr v z x) (subst_var_in_Zexpr v z y)
  | ZLit z => e
  | ZVar var => if var ==v v
                then ZLit z
                else e
  end.      

Definition subst_var_in_Z_tup var z t :=
  (subst_var_in_Zexpr var z (fst t), subst_var_in_Zexpr var z (snd t)).

Fixpoint pair_vars_valuation (v : valuation) (vars : list var) :=
  match vars with
  | x::xs => (x, v $? x)::(pair_vars_valuation v xs)
  | [] => []
  end.

Definition partially_eval_Zexpr_alt (v : valuation) (e : Zexpr) : Zexpr :=
  let vars := vars_of_Zexpr e in
  let vars_vals := pair_vars_valuation v vars in
  fold_left (fun e t =>
               match t with
               | (var,Some val) => subst_var_in_Zexpr var val e
               | (_,None) => e
               end)
            vars_vals e.

Lemma filter_true_id {X} : forall (l : list X),
    filter (fun _ => true) l = l.
Proof.
  induct l.
  - reflexivity.
  - simpl. rewrite IHl. auto.
Qed.

Lemma app_no_dups_empty_args : forall l1 l2,
    l1 ++/ l2 = [] ->
    l1 = [] /\ l2 = [].
Proof.
  unfold app_no_dups.
  induct l1; intros.
  - rewrite app_nil_l in *.
    simpl in *.
    rewrite filter_true_id in H. subst. propositional.
  - simpl in *. discriminate.
Qed.

Lemma partially_eval_Zexpr_no_vars : forall e,
    vars_of_Zexpr e = [] ->
    forall v,
      partially_eval_Zexpr v e = e.
Proof.
  induct e; intros;
    simpl in *; try apply app_no_dups_empty_args in H; invs;
    try rewrite IHe1; try rewrite IHe2; try rewrite IHe3; auto.
  invert H.
Qed.

Lemma filter_app_no_dups : forall l1 f l2,
    filter f (l1 ++/ l2) = filter f l1 ++/ filter f l2.
Proof.
  induct l1; intros; cases l2.
  - reflexivity.
  - simpl. unfold app_no_dups. simpl.
    repeat rewrite filter_true_id. reflexivity.
  - simpl. repeat rewrite app_nil_r.
    rewrite app_no_dups_empty_r. reflexivity.
  - simpl. cases (f a).
    + unfold app_no_dups. simpl. f_equal.
      cases (a =? s).
      * simpl in *. eapply String.eqb_eq in Heq0. subst. rewrite Heq. simpl.
        rewrite String.eqb_refl. simpl.
        rewrite filter_app. f_equal.
        repeat rewrite filter_filter. f_equal.
        eapply functional_extensionality. intros.
        cases (s =? x).
        -- eapply String.eqb_eq in Heq0. subst. rewrite Heq. simpl. auto.
        -- simpl. rewrite in_bool_filter.
           cases (f x). simpl. rewrite andb_true_r. reflexivity.
           simpl. reflexivity.
      * simpl. cases (in_bool l1 s).
        -- simpl.
           cases (f s).
           ++ simpl in *. rewrite Heq0. simpl.
              rewrite in_bool_filter. rewrite Heq2,Heq1.
              simpl. rewrite filter_app.
              f_equal. repeat rewrite filter_filter. f_equal.
              eapply functional_extensionality. intros.
              cases (a =? x).
              eapply String.eqb_eq in Heq3. subst. simpl. rewrite andb_false_r.
              reflexivity.
              simpl. cases (f x). simpl. rewrite andb_true_r. reflexivity.
              simpl. reflexivity.
           ++ rewrite filter_app. f_equal.
              repeat rewrite filter_filter.
              f_equal.
              eapply functional_extensionality. intros.
              rewrite in_bool_filter.
              cases (a =? x).
              eapply String.eqb_eq in Heq3. subst. simpl. rewrite andb_false_r.
              reflexivity.
              simpl. cases (f x). simpl. rewrite andb_true_r. reflexivity.
              simpl. reflexivity.
        -- simpl. cases (f s).
           ++ simpl. rewrite Heq0. simpl. rewrite in_bool_filter.
              rewrite Heq2,Heq1. simpl. rewrite filter_app.
              f_equal. simpl. rewrite Heq2. f_equal.
              repeat rewrite filter_filter.
              f_equal.
              eapply functional_extensionality. intros.
              cases (a =? x).
              eapply String.eqb_eq in Heq3. subst. simpl. rewrite andb_false_r.
              reflexivity.
              simpl. cases (f x). simpl. rewrite andb_true_r. reflexivity.
              simpl. reflexivity.
           ++ rewrite filter_app.
              f_equal. simpl. rewrite Heq2. 
              repeat rewrite filter_filter.
              f_equal. 
              eapply functional_extensionality. intros.
              rewrite in_bool_filter.
              cases (a =? x).
              eapply String.eqb_eq in Heq3. subst. simpl. rewrite andb_false_r.
              reflexivity.
              simpl. cases (f x). simpl. rewrite andb_true_r. reflexivity.
              simpl. reflexivity.
    + simpl. cases (a =? s).
      * eapply String.eqb_eq in Heq0. subst. simpl. rewrite Heq. simpl.
        unfold app_no_dups in IHl1.
        replace (fun v : var => negb ((s =? v) || in_bool l1 v)) with
          (fun v : var => negb (in_bool l1 v) && negb (s =? v)).
        2: { eapply functional_extensionality. intros.
             rewrite negb_orb. rewrite andb_comm.
             reflexivity. }
        rewrite <- filter_filter.
        rewrite IHl1. unfold app_no_dups.
        repeat rewrite filter_filter. f_equal.
        f_equal.
        eapply functional_extensionality. intros.
        cases (s =? x). simpl.
        rewrite andb_false_r. eapply String.eqb_eq in Heq0. subst.
        rewrite Heq. rewrite andb_false_r. reflexivity.
        simpl. rewrite andb_true_r. reflexivity.
      * simpl.
        rewrite filter_app.
        cases (f s).
        -- simpl.
           unfold app_no_dups. f_equal.
           cases (in_bool l1 s).
           ++ simpl in *.
              rewrite in_bool_filter.
              rewrite Heq1. rewrite Heq2. simpl.
              repeat rewrite filter_filter.
              f_equal.
              eapply functional_extensionality. intros.
              cases (a =? x).
              ** eapply String.eqb_eq in Heq3. subst. simpl in *. rewrite Heq.
                 simpl. reflexivity.
              ** simpl.
                 rewrite negb_andb.
                 rewrite andb_orb_distrib_l.
                 cases (f x). simpl. rewrite andb_true_r. reflexivity.
                 simpl. rewrite andb_false_r. reflexivity.
           ++ simpl. rewrite in_bool_filter.
              rewrite Heq1, Heq2. simpl. f_equal.
              repeat rewrite filter_filter.
              f_equal. eapply functional_extensionality.
              intros. rewrite negb_andb.
              rewrite andb_orb_distrib_l.
              cases (a =? x).
              ** eapply String.eqb_eq in Heq3. subst. rewrite Heq.
                 simpl. rewrite andb_false_r. reflexivity.
              ** simpl.
                 cases (f x).
                 simpl. rewrite andb_true_r. reflexivity.
                 simpl. rewrite andb_false_r. reflexivity.
        -- cases (in_bool l1 s).
           ++ simpl.
              unfold app_no_dups in *.
              rewrite <- IHl1. rewrite filter_app.
              repeat rewrite filter_filter. f_equal.
              f_equal.
              eapply functional_extensionality. intros.
              cases (a =? x).
              ** eapply String.eqb_eq in Heq3. subst. rewrite Heq.
                 simpl. reflexivity.
              ** simpl. reflexivity.
           ++ simpl. rewrite Heq1. rewrite <- IHl1.
              unfold app_no_dups. rewrite filter_app.
              f_equal.
              repeat rewrite filter_filter.
              f_equal.
              f_equal.
              eapply functional_extensionality. intros.
              cases (a =? x).
              ** eapply String.eqb_eq in Heq3. subst. rewrite Heq.
                 simpl. reflexivity.
              ** simpl. reflexivity.
Qed.              

Lemma vars_of_Zexpr_subst_var_in_Zexpr : forall e v z,
    vars_of_Zexpr (subst_var_in_Zexpr v z e) =
      filter (fun v' => negb (String.eqb v' v)) (vars_of_Zexpr e).
Proof.
  induct e; intros; simpl in *; try rewrite IHe1, IHe2;
    try rewrite filter_app_no_dups; auto.
  cases (x ==v v). subst. rewrite String.eqb_refl. reflexivity.
  simpl. cases (x =? v). eapply String.eqb_eq in Heq. subst. propositional.
  reflexivity.
Qed.

(*
Lemma partially_eval_Zexpr_subst_var_in_Zexpr :
  forall e v a z,
    v $? a = Some z ->
    partially_eval_Zexpr v e =
      partially_eval_Zexpr v (subst_var_in_Zexpr a z e) .
Proof.
  induct e; intros; simpl in *; try erewrite IHe1, IHe2 by eauto;
    try reflexivity.
  cases (x ==v a).
  - subst. rewrite H. simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma pair_vars_valuation_app : forall l1 l2 v,
    pair_vars_valuation v (l1 ++ l2) =
      ((pair_vars_valuation v l1) ++ (pair_vars_valuation v l2))%list.
Proof.
  induct l1; intros.
  - reflexivity.
  - simpl. f_equal. eauto.
Qed.
*)
Lemma app_no_dups_empty_l : forall l,
    [] ++/ l = l.
Proof.
  intros. cases l.
  - reflexivity.
  - unfold app_no_dups.
    simpl. rewrite filter_true_id. auto.
Qed.

Lemma in_bool_app : forall l1 l2 x,
    in_bool (l1 ++ l2) x = in_bool l1 x || in_bool l2 x.
Proof.
  induct l1; intros.
  - reflexivity.
  - simpl. rewrite <- orb_assoc. f_equal.
    auto.
Qed.

Lemma app_no_dups_assoc : forall l1 l2 l3,
    l1 ++/ l2 ++/ l3 = l1 ++/ (l2 ++/ l3).
Proof.
  induct l1; intros.
  - repeat rewrite app_no_dups_empty_l. reflexivity.
  - unfold app_no_dups.
    repeat rewrite <- app_assoc.  f_equal.
    rewrite filter_app. f_equal.
    rewrite filter_filter.
    f_equal.
    eapply functional_extensionality. intros.
    rewrite <- negb_orb. f_equal. rewrite in_bool_app.
    cases (in_bool (a::l1) x); simpl in *.
    * reflexivity.
    * eapply orb_false_elim in Heq. invert Heq.
      rewrite in_bool_filter. rewrite H. simpl. rewrite H0.
      simpl. reflexivity.
Qed.

Lemma eq_zexpr_add_assoc : forall x1 x2 x3,
    eq_zexpr (x1 + x2 + x3)%z (x1 + (x2 + x3))%z.
Proof.
  intros.
  unfold eq_zexpr. propositional.
  - invert H. invert H2.
    replace (xz0 + yz0 + yz)%Z with (xz0 + (yz0 + yz))%Z by lia.
    econstructor. eauto. econstructor. eauto. eauto.
  - invert H. invert H4.
    replace (xz + (xz0 + yz0))%Z with (xz + xz0 + yz0)%Z by lia.
    repeat (econstructor; eauto).
  - simpl.
    eapply app_no_dups_assoc.
Qed.

Lemma eval_Zexpr_subst_var_in_Zexpr : forall e v i x k,
    eval_Zexpr (v $+ (i,k)) e x <->
    eval_Zexpr v (subst_var_in_Zexpr i k e) x.
Proof.
  induct e; intros; simpl in *; split; intros; try invert1 H;
    try econstructor; try eapply IHe1; try eapply IHe2; eauto;
    cases (x ==v i); subst;
    repeat rewrite lookup_add_eq in * by auto;
    repeat rewrite lookup_add_ne in * by auto.
  invert H1. eauto. eauto. invert H. eauto. invert H. eauto.
Qed.

Lemma eq_zexpr_subst_var_in_Zexpr : forall z1 z2,
    eq_zexpr z1 z2 ->
    forall v z,
      eq_zexpr (subst_var_in_Zexpr v z z1) (subst_var_in_Zexpr v z z2).
Proof.
  intros.
  unfold eq_zexpr in *.
  propositional;
    try eapply eval_Zexpr_subst_var_in_Zexpr;
    try eapply eval_Zexpr_subst_var_in_Zexpr in H;
    firstorder;
    repeat erewrite vars_of_Zexpr_subst_var_in_Zexpr;
    rewrite H1; reflexivity.
Qed.

Lemma map_fst_snd_id {X Y} : forall (index : list (X * Y)),
    map (fun tup => (fst tup, snd tup)) index = index.
Proof.
  induction index.
  - reflexivity.
  - simpl. cases a. f_equal.
    eauto.
Qed.

Definition index_to_function_rec_alt
           (index : list (Zexpr * Zexpr)) (args : list Z) vars : Zexpr
  :=
  let index_zexpr := flatten_index index in
  fold_left
    (fun (z : Zexpr) (tup : string * Z) =>
       subst_var_in_Zexpr (fst tup) (snd tup) z)
    (combine vars args) index_zexpr.

Definition index_to_function_alt (index : list (Zexpr * Zexpr)) vars :
  list Z -> Z :=
  fun args =>
    let evaled_index := index_to_function_rec_alt index args vars in
    match eval_Zexpr_Z $0 evaled_index with
    | Some val => val
    | None => (-1)%Z
    end.

Lemma eq_zexpr_flatten_shape_index :
  forall vars1 vars2,
    eq_Z_index_list vars1 vars2 ->
    forall dims1 dims2,
      eq_Z_index_list dims1 dims2 ->
      eq_zexpr (flatten_shape_index vars1 dims1)
               (flatten_shape_index vars2 dims2).
Proof.
  induction vars1; intros; cases vars2; cases dims1; cases dims2;
    simpl in *; eauto; try lia; try now (invert H; simpl in *; lia).
  - unfold flatten_shape_index.
    cases vars1; cases vars2; eauto.
  - invert H0; simpl in *; lia.
  - invert H0; simpl in *; lia.
  - cases vars1; cases vars2.
    + unfold flatten_shape_index.
      eapply eq_Z_index_list_cons in H0.
      invert H.
      cases dims1; cases dims2; propositional; auto.
      invert H. simpl in *. lia.
      invert H. simpl in *. lia.
    + invert H. simpl in *. lia.
    + invert H. simpl in *. lia.
    + simpl. eapply eq_zexpr_add.
      eapply eq_zexpr_mul. auto.
      eapply eq_Z_index_list_cons in H0. propositional.
      eapply eq_zexpr_fold_ZTimes. invert H. simpl in *. lia.
      eapply eq_Z_index_list_cons in H. propositional.
      eapply eq_Z_index_list_cons in H1. propositional.
      eapply eq_Z_index_list_cons in H. propositional.
      eapply eq_Z_index_list_cons in H1. propositional.
      eapply IHvars1. eapply eq_Z_index_list_cons in H. propositional.
      eapply eq_Z_index_list_cons in H0. propositional.
Qed.

Lemma eq_zexpr_flatten_index : forall index1 index2,
    eq_Z_tuple_index_list index1 index2 ->
    eq_zexpr (flatten_index index1) (flatten_index index2).
Proof.
  unfold eq_Z_tuple_index_list;
    induction index1; intros; cases index2; simpl in *; try lia; propositional.
  - unfold flatten_index. simpl.
    eapply eq_zexpr_id; eauto.
  - unfold flatten_index. simpl.
    eapply eq_zexpr_flatten_shape_index; auto.
Qed.

Ltac eq_match_discriminee :=
  match goal with
  | |- match ?A with _ => _ end = match ?B with _ => _ end =>
      assert (A = B) as HH; [ | rewrite HH; reflexivity ]
  end.

Lemma index_to_function_alt_cons : forall index1 index2 z z1 z0 z2,
    eq_Z_tuple_index_list index1 index2 ->
    index_to_function_alt index1 = index_to_function_alt index2 ->
    eq_zexpr z z1 ->
    eq_zexpr z0 z2 ->
    index_to_function_alt ((z, z0) :: index1) =
      index_to_function_alt ((z1, z2) :: index2).
Proof.
  unfold index_to_function_alt. unfold eq_Z_tuple_index_list.
  intros.
  eapply functional_extensionality. intros.
  unfold index_to_function_rec_alt in *.
  unfold flatten_index. simpl. eapply functional_extensionality. intros.
  propositional.
  eq_match_discriminee.
  eapply eq_eval_Zexpr_Z.
  eapply eq_zexpr_transitivity.
  eapply eq_zexpr_fold_accum.
  eapply eq_zexpr_flatten_shape_index with
    (vars2:=z2 :: map snd index2) (dims2:=z1 :: map fst index2).
  rewrite <- eq_Z_index_list_cons.
  propositional. 
  rewrite <- eq_Z_index_list_cons.
  propositional.
  intros.
  eapply eq_zexpr_subst_var_in_Zexpr. auto.
  assert (
      eq_zexpr
        (flatten_shape_index (z0 :: map snd index1) (z :: map fst index1))
        (flatten_shape_index (z2 :: map snd index2) (z1 :: map fst index2))
    ).
  {
    eapply eq_zexpr_flatten_shape_index.
    rewrite <- eq_Z_index_list_cons. propositional.
    rewrite <- eq_Z_index_list_cons. propositional.
  }
  eapply eq_zexpr_id. reflexivity.
Qed.

Lemma eq_index_to_function_alt :
  forall index1 index2,
    eq_Z_tuple_index_list index1 index2 ->
      index_to_function_alt index1 = index_to_function_alt index2.
Proof.
  unfold eq_Z_tuple_index_list; induction index1.
  - intros. cases index2; simpl in *; try lia. reflexivity.
  - intros. cases index2; simpl in *; try lia.
    propositional.
    cases a. cases p. simpl in *.
    eapply eq_Z_index_list_cons in H.
    eapply eq_Z_index_list_cons in H2. propositional. auto.
    eapply index_to_function_alt_cons; auto.
    unfold eq_Z_tuple_index_list. propositional. lia.
Qed.

Lemma eq_index_to_function_alt_app :
  forall index1 index2,
    eq_Z_tuple_index_list index1 index2 ->
      forall x,
      index_to_function_alt index1 x = index_to_function_alt index2 x.
Proof.
  intros.
  erewrite eq_index_to_function_alt with (index2:=index2) by eassumption.
  auto.
Qed.

Lemma eval_Zexpr_partially_eval_Zexpr_same_valuation : forall v e z,
    eval_Zexpr v (partially_eval_Zexpr v e) z <-> eval_Zexpr v e z.
Proof.
  induct e; split; intros; simpl in *; auto;
    try now (invert H; econstructor; try eapply IHe1; try eapply IHe2; eauto).
  - cases (v $? x); invert H; firstorder; econstructor; eauto.
  - invert H. rewrite H1. econstructor.
Qed.

Lemma in_bool_In : forall l x,
    in_bool l x = true <-> In x l.
Proof.
  induct l; intros; split; intros.
  - simpl in *. discriminate.
  - invert H.
  - simpl in *.
    cases (a =? x). simpl in *.
    eapply String.eqb_eq in Heq. subst. auto.
    simpl in *. right. eapply IHl. auto.
  - simpl in *. invert H.
    rewrite String.eqb_refl. auto.
    eapply IHl in H0. rewrite H0.
    rewrite orb_true_r. reflexivity.
Qed.

Lemma no_dup_filter {X} : forall l (f : X -> bool),
    no_dup l ->
    no_dup (filter f l).
Proof.
  induct 1. econstructor.
  simpl.
  cases (f x).
  - econstructor. eauto.
    unfold not. intros.
    eapply filter_In in H1. invs. propositional.
  - eauto.
Qed.

Lemma no_dup_app_no_dups : forall l1 l2,
    no_dup l1 ->
    no_dup l2 ->
    no_dup (l1 ++/ l2).
Proof.
  induct l1; intros.
  - rewrite app_no_dups_empty_l. auto.
  - invert H.
    unfold app_no_dups in *. simpl.
    econstructor.
    2: { unfold not. intros. eapply in_app_or in H.
         invert H. propositional.
         eapply filter_In in H1.
         invs. rewrite negb_orb in H2.
         rewrite String.eqb_refl in *. simpl in *. discriminate. }
    eapply no_dup_app. auto.
    2: { eapply Forall_forall. intros.
         eapply filter_In in H. invs.
         rewrite negb_orb in *.
         eapply andb_prop in H2. invs.
         eapply negb_true_iff in H5.
         unfold not. intros.
         eapply in_bool_In in H2.
         rewrite H2 in *. discriminate. }
    eapply no_dup_filter. eauto.
Qed.

Lemma vars_of_Zexpr_no_dups : forall e,
    no_dup (vars_of_Zexpr e).
Proof.
  induct e; intros; simpl; try eapply no_dup_app_no_dups; eauto.
  econstructor. econstructor; eauto. econstructor.
Qed.

Lemma vars_of_Zexpr_subst_var_in_Zexpr_cons : forall e l a,
    vars_of_Zexpr e = a::l ->
    forall z,
    vars_of_Zexpr (subst_var_in_Zexpr a z e) = l.
Proof.
  intros. erewrite vars_of_Zexpr_subst_var_in_Zexpr.
  pose proof (vars_of_Zexpr_no_dups e). rewrite H in *.
  invert H0. simpl.
  cases (a =? a). simpl.
  2: { rewrite String.eqb_refl in *. discriminate. }
  erewrite filter_ext_in with (g:= fun _ => true).
  apply filter_true_id.
  intros.
  cases (a0 =? a). eapply String.eqb_eq in Heq0. subst. propositional.
  reflexivity.
Qed.
  
Lemma eq_zexpr_partially_eval_subst_var_in_Zexpr :
  forall e a z v,
    v $? a = Some z ->
      eq_zexpr
        (partially_eval_Zexpr v e)
        (partially_eval_Zexpr v (subst_var_in_Zexpr a z e)).
Proof.
  induct e; intros; simpl in *;
    eapply eq_zexpr_transitivity;
    try eapply eq_zexpr_add;
    try eapply eq_zexpr_sub;
    try eapply eq_zexpr_mul;
    try eapply eq_zexpr_div;
    try eapply eq_zexpr_divc;
    try eapply eq_zexpr_mod;
    try eapply IHe1; try eassumption; try eapply IHe2;
    try eassumption; try eapply eq_zexpr_id; eauto.
  cases (x ==v a); subst; try rewrite H; auto;
    cases (v $? x); simpl in *; rewrite Heq; auto.
Qed.
  
Lemma eq_zexpr_eval_Zexpr : forall z1 z2,
    eq_zexpr z1 z2 ->
    forall v z,
      eval_Zexpr v z1 z ->
      eval_Zexpr v z2 z.
Proof.
  unfold eq_zexpr. propositional. eapply H0. auto.
Qed.

Lemma eval_Zexpr_partially_eval_Zexpr_not_in_valuation :
  forall e a l, 
    vars_of_Zexpr e = a::l ->
    forall v v0 z,
    eval_Zexpr v0 (partially_eval_Zexpr v e) z ->
    v $? a = None ->
    exists k, v0 $? a = Some k.
Proof.
  induct e; intros;
    simpl in *;
    try cases (vars_of_Zexpr e1); unfold app_no_dups in H; simpl in *;
    try rewrite @filter_true_id in *; invsZ; invert1 H; eauto;
    try rewrite H1 in H0; invsZ; eauto.
Qed.

Lemma vars_of_Zexpr_partially_eval_Zexpr : forall v e,
    vars_of_Zexpr (partially_eval_Zexpr v e) =
      filter (fun x => match v $? x with
                       | Some _ => false
                       | None => true
                       end) (vars_of_Zexpr e).
Proof.
  induct e; intros; simpl in *; try rewrite IHe1, IHe2;
    unfold app_no_dups; repeat rewrite filter_app;
    repeat rewrite filter_filter; repeat rewrite in_bool_filter;
    repeat f_equal; try apply functional_extensionality; intros;
    try cases (v $? x); simpl in *; try rewrite andb_true_r; try reflexivity.
Qed.

Lemma subst_var_in_Zexpr_partially_eval_Zexpr_comm : forall e a x v,
    v $? a = None ->
    subst_var_in_Zexpr a x (partially_eval_Zexpr v e) =
      partially_eval_Zexpr v (subst_var_in_Zexpr a x e).
Proof.
  induct e; intros; simpl in *;
    try rewrite IHe1, IHe2; auto.
  cases (x ==v a). 
  - subst. rewrite H. simpl in *.
    cases (a ==v a); firstorder.
  - simpl. cases (v $? x); simpl.
    + reflexivity.
    + cases (x ==v a); firstorder.
Qed.

Lemma filter_filter_comm {X} : forall f g (l : list X),
    filter f (filter g l) = filter g (filter f l).
Proof.
  induct l; intros.
  - reflexivity.
  - simpl.
    cases (f a); cases (g a); simpl; try rewrite Heq; try rewrite Heq0;
      try rewrite IHl; auto.
Qed.

Lemma eq_zexpr_partially_eval_Zexpr_helper : forall l z1 z2,
    l = vars_of_Zexpr z1 ->
    eq_zexpr z1 z2 ->
    forall v,
      eq_zexpr (partially_eval_Zexpr v z1) (partially_eval_Zexpr v z2).
Proof.
  unfold eq_zexpr in *.
  assert True as H by propositional. 
  induction l; propositional.
  - cases z1; simpl in *; invsZ; try symmetry in H0;
      try eapply app_no_dups_empty_args in H0; invert1 H0;
      try rewrite H1, H4 in *; try rewrite app_no_dups_empty_l in *;
      try eapply partially_eval_Zexpr_no_vars in H1;
      try eapply partially_eval_Zexpr_no_vars in H4;
      try rewrite H1 in H6; try rewrite H4 in H8;
      try symmetry in H3; try eapply partially_eval_Zexpr_no_vars in H3;
      try rewrite H3; try eapply H2; eauto.
  - cases z2; simpl in *; invsZ; rewrite <- H0 in *; symmetry in H3;
      try eapply app_no_dups_empty_args in H3; invert1 H3;
      try rewrite H1, H4 in *; try rewrite app_no_dups_empty_l in *;
      try eapply partially_eval_Zexpr_no_vars in H1;
      try eapply partially_eval_Zexpr_no_vars in H4;
      try rewrite H4 in H8; try rewrite H1 in H6; symmetry in H0;
      eapply partially_eval_Zexpr_no_vars in H0; rewrite H0; eapply H2; eauto.
  - pose proof H3. rewrite <- H0 in H3. symmetry in H0, H3.
    eapply partially_eval_Zexpr_no_vars in H0.
    eapply partially_eval_Zexpr_no_vars in H3.
    rewrite H0,H3. auto.
  - rewrite <- H0 in *. symmetry in H0,H3.
    cases (v $? a).
    + specialize (IHl (subst_var_in_Zexpr a z0 z1)
                      (subst_var_in_Zexpr a z0 z2)).
      pose proof H3.
      eapply vars_of_Zexpr_subst_var_in_Zexpr_cons in H4.
      pose proof H0.
      eapply vars_of_Zexpr_subst_var_in_Zexpr_cons in H5.
      rewrite H4, H5 in *. propositional.
      assert (forall (v : valuation) (z : Z),
        eval_Zexpr v (subst_var_in_Zexpr a z0 z1) z <->
          eval_Zexpr v (subst_var_in_Zexpr a z0 z2) z).
      {
        propositional.
        eapply eval_Zexpr_subst_var_in_Zexpr.
        eapply eval_Zexpr_subst_var_in_Zexpr in H6.
        eapply H2. auto.
        eapply eval_Zexpr_subst_var_in_Zexpr.
        eapply eval_Zexpr_subst_var_in_Zexpr in H6.
        eapply H2. auto.
      } 
      eapply H7 in H6. clear H7. 2: auto. invert H6.
      eapply eq_zexpr_eval_Zexpr.
      2: { eapply eq_zexpr_partially_eval_subst_var_in_Zexpr.
           apply Heq.
           rewrite <- H7.
           eapply eq_zexpr_eval_Zexpr.
           eapply eq_zexpr_partially_eval_subst_var_in_Zexpr. assumption.
           assumption. }
      unfold eq_zexpr. propositional.
    + pose proof H0.
      eapply eval_Zexpr_partially_eval_Zexpr_not_in_valuation in H4; eauto.
      invert H4.
      specialize (IHl (subst_var_in_Zexpr a x z1)
                      (subst_var_in_Zexpr a x z2)).
      pose proof H0.
      eapply vars_of_Zexpr_subst_var_in_Zexpr_cons in H4.
      rewrite H4 in *. propositional.
      propositional.
      assert (forall (v : valuation) (z : Z),
        eval_Zexpr v (subst_var_in_Zexpr a x z1) z <->
          eval_Zexpr v (subst_var_in_Zexpr a x z2) z).
      {
        propositional.
        eapply eval_Zexpr_subst_var_in_Zexpr.
        eapply eval_Zexpr_subst_var_in_Zexpr in H6.
        eapply H2. auto.
        eapply eval_Zexpr_subst_var_in_Zexpr.
        eapply eval_Zexpr_subst_var_in_Zexpr in H6.
        eapply H2. auto.
      }
      pose proof H3.
      eapply vars_of_Zexpr_subst_var_in_Zexpr_cons in H8.
      rewrite H8 in *.
      propositional.
      replace v0 with (v0 $+ (a,x)).
      eapply eval_Zexpr_subst_var_in_Zexpr.
      2: apply add_id; auto.
      rewrite subst_var_in_Zexpr_partially_eval_Zexpr_comm by auto.
      eapply H7.
      rewrite <- subst_var_in_Zexpr_partially_eval_Zexpr_comm by auto.
      eapply eval_Zexpr_subst_var_in_Zexpr.
      rewrite add_id by auto.
      auto.      
  - rewrite <- H0 in *.
    cases (v $? a).
    + specialize (IHl (subst_var_in_Zexpr a z0 z1)
                      (subst_var_in_Zexpr a z0 z2)).
      symmetry in H0, H3. pose proof H0. pose proof H3.
      eapply vars_of_Zexpr_subst_var_in_Zexpr_cons in H4.
      eapply vars_of_Zexpr_subst_var_in_Zexpr_cons in H5.
      rewrite H4, H5 in *. propositional.
      assert (forall (v : valuation) (z : Z),
        eval_Zexpr v (subst_var_in_Zexpr a z0 z1) z <->
          eval_Zexpr v (subst_var_in_Zexpr a z0 z2) z).
      {
        propositional.
        eapply eval_Zexpr_subst_var_in_Zexpr.
        eapply eval_Zexpr_subst_var_in_Zexpr in H6.
        eapply H2. auto.
        eapply eval_Zexpr_subst_var_in_Zexpr.
        eapply eval_Zexpr_subst_var_in_Zexpr in H6.
        eapply H2. auto.
      }
      eapply H7 in H6. clear H7. 2: auto. invert H6.
      eapply eq_zexpr_eval_Zexpr.
      2: { eapply eq_zexpr_partially_eval_subst_var_in_Zexpr.
           apply Heq.
           rewrite H7.
           eapply eq_zexpr_eval_Zexpr.
           eapply eq_zexpr_partially_eval_subst_var_in_Zexpr. assumption.
           assumption. }
      auto.
    + pose proof H3. symmetry in H4.
      eapply eval_Zexpr_partially_eval_Zexpr_not_in_valuation in H4; eauto.
      invert H4.
      specialize (IHl (subst_var_in_Zexpr a x z1)
                      (subst_var_in_Zexpr a x z2)).
      symmetry in H0,H3.
      pose proof H0. pose proof H3.
      eapply vars_of_Zexpr_subst_var_in_Zexpr_cons in H4. rewrite H4 in *.
      propositional.
      assert (forall (v : valuation) (z : Z),
        eval_Zexpr v (subst_var_in_Zexpr a x z1) z <->
          eval_Zexpr v (subst_var_in_Zexpr a x z2) z).
      {
        propositional.
        eapply eval_Zexpr_subst_var_in_Zexpr.
        eapply eval_Zexpr_subst_var_in_Zexpr in H7.
        eapply H2. auto.
        eapply eval_Zexpr_subst_var_in_Zexpr.
        eapply eval_Zexpr_subst_var_in_Zexpr in H7.
        eapply H2. auto.
      }
      eapply vars_of_Zexpr_subst_var_in_Zexpr_cons in H6. rewrite H6 in *.
      propositional.
      replace v0 with (v0 $+ (a,x)).
      eapply eval_Zexpr_subst_var_in_Zexpr.
      2: apply add_id; auto.
      rewrite subst_var_in_Zexpr_partially_eval_Zexpr_comm by auto.
      eapply H8.
      rewrite <- subst_var_in_Zexpr_partially_eval_Zexpr_comm by auto.
      eapply eval_Zexpr_subst_var_in_Zexpr.
      rewrite add_id by auto.
      auto.
  - pose proof H3 as Ht. rewrite <- H0 in H3.
    cases (v $? a).
    + specialize (IHl (subst_var_in_Zexpr a z z1)
                      (subst_var_in_Zexpr a z z2)).
      symmetry in H0.
      eapply vars_of_Zexpr_subst_var_in_Zexpr_cons in H0.
      rewrite H0 in IHl.
      propositional.
      pose proof Heq. pose proof Heq.
      eapply eq_zexpr_partially_eval_subst_var_in_Zexpr in Heq.
      unfold eq_zexpr in Heq. invsZ.
      rewrite H7.
      eapply eq_zexpr_partially_eval_subst_var_in_Zexpr in H1.
      unfold eq_zexpr in H1. invsZ.
      symmetry. rewrite H8.
      symmetry.
      clear H7. clear H6. clear H0. clear H8.
      eapply H4.
      propositional.
      assert (eq_zexpr z1 z2).
      unfold eq_zexpr. propositional.
      eapply eq_zexpr_subst_var_in_Zexpr in H1.
      unfold eq_zexpr in H1.
      invert H1.
      eapply H6. eauto. 
      assert (eq_zexpr z1 z2).
      unfold eq_zexpr. propositional.
      eapply eq_zexpr_subst_var_in_Zexpr in H1.
      unfold eq_zexpr in H1.
      invert H1. eapply H6. auto.
      assert (eq_zexpr z1 z2).
      unfold eq_zexpr. propositional.
      eapply eq_zexpr_subst_var_in_Zexpr in H0.
      unfold eq_zexpr in H0.
      invert H0. eapply H6.
    + repeat rewrite vars_of_Zexpr_partially_eval_Zexpr in *.
      rewrite Ht. reflexivity.
Qed.

Definition eq_Z_tup x y :=
  eq_zexpr (fst x) (fst y) /\ eq_zexpr (snd x) (snd y).             

Definition partially_eval_Z_tup v tp :=
  (partially_eval_Zexpr v (fst tp),partially_eval_Zexpr v (snd tp)).

Lemma eq_zexpr_partially_eval_Zexpr : forall z1 z2,
    eq_zexpr z1 z2 ->
    forall v,
      eq_zexpr (partially_eval_Zexpr v z1) (partially_eval_Zexpr v z2).
Proof.
  intros. eapply eq_zexpr_partially_eval_Zexpr_helper.
  reflexivity. auto.
Qed.

Lemma eq_Z_tup_partially_eval_tup : forall t1 t2,
    eq_Z_tup t1 t2 ->
    forall v,
      eq_Z_tup (partially_eval_Z_tup v t1) (partially_eval_Z_tup v t2).
Proof.
  intros. cases t1. cases t2. invert H.
  unfold partially_eval_Z_tup. unfold eq_Z_tup.
  simpl in *.
  split; eapply eq_zexpr_partially_eval_Zexpr; auto.
Qed.

Lemma eq_zexpr_list_fst : forall v (l1 l2 : list (Zexpr * Zexpr)),
    length l1 = length l2 ->
    Forall (fun tup => eq_zexpr (fst tup) (snd tup))
           (combine (map fst l1) (map fst l2)) ->
    Forall (fun tup => eq_zexpr (fst tup) (snd tup))
           (combine (map (fun x => partially_eval_Zexpr v (fst x)) l1)
                    (map (fun x => partially_eval_Zexpr v (fst x)) l2)).
Proof.
  induction l1; intros; cases l2; simpl in *; try lia.
  - constructor.
  - invert H0. invert H.
    constructor. simpl in *.
    eapply eq_zexpr_partially_eval_Zexpr. auto.
    eauto.
Qed.

Lemma eq_zexpr_vars_of_Zexpr : forall e1 e2,
    eq_zexpr e1 e2 ->
    vars_of_Zexpr e1 = vars_of_Zexpr e2.
Proof.
  intros.
  unfold eq_zexpr in *. propositional.
Qed.

Lemma eq_zexpr_list_snd : forall v (l1 l2 : list (Zexpr * Zexpr)),
    length l1 = length l2 ->
    Forall (fun tup => eq_zexpr (fst tup) (snd tup))
           (combine (map snd l1) (map snd l2)) ->
    Forall (fun tup => eq_zexpr (fst tup) (snd tup))
           (combine (map (fun x => partially_eval_Zexpr v (snd x)) l1)
                    (map (fun x => partially_eval_Zexpr v (snd x)) l2)).
Proof.
  induction l1; intros; cases l2; simpl in *; try lia.
  - constructor.
  - invert H0. invert H.
    constructor. simpl in *.    
    eapply eq_zexpr_partially_eval_Zexpr.
    auto. eauto.
Qed.        

Lemma partially_eval_Zexpr_empty_valuation : forall v z,
    eval_Zexpr_Z v z = eval_Zexpr_Z $0 (partially_eval_Zexpr v z).
Proof.
  induct z; intros; simpl;
    try cases (eval_Zexpr_Z v z1); try cases (eval_Zexpr_Z v z2);
    try rewrite <- IHz1; try rewrite <- IHz2; auto.
  cases (v $? x); simpl; auto.
  rewrite lookup_empty. reflexivity.
Qed.

Lemma vars_of_partially_eval_Zexpr : forall v e z,
    eval_Zexpr_Z v e = Some z ->
    vars_of_Zexpr (partially_eval_Zexpr v e) = [].
Proof.
  induct e; intros; simpl in *;
    try (cases (eval_Zexpr_Z v e1); try cases (eval_Zexpr_Z v e2);
      try discriminate; erewrite IHe1 by auto; erewrite IHe2 by auto); auto.
  rewrite H. reflexivity.
Qed.

Lemma eq_zexpr_sub_sub_distr : forall x1 x2 x3,
    eq_zexpr (x1 - x2 + x3)%z (x1 - (x2 - x3))%z.
Proof.
  intros.
  unfold eq_zexpr. propositional.
  - invert H. invert H2.
    rewrite <- Z.sub_sub_distr.
    eauto.
  - invert H. invert H4.
    rewrite Z.sub_sub_distr.
    eauto.
  - simpl.
    apply app_no_dups_assoc.
Qed.

Lemma eq_zexpr_mul_assoc : forall x1 x2 x3,
    eq_zexpr (x1 * x2 * x3)%z (x1 * (x2 * x3))%z.
Proof.
  intros.
  unfold eq_zexpr. propositional.
  - invert H. invert H2.
    replace (xz0 * yz0 * yz)%Z with (xz0 * (yz0 * yz))%Z by lia.
    econstructor. eauto. econstructor. eauto. eauto.
  - invert H. invert H4.
    replace (xz * (xz0 * yz0))%Z with (xz * xz0 * yz0)%Z by lia.
    repeat (econstructor; eauto).
  - simpl.
    eapply app_no_dups_assoc.
Qed.

Lemma eq_zexpr_mul_r : forall a b c,
    eq_zexpr b c ->
    eq_zexpr (a*b)%z (a*c)%z.
Proof.
  unfold eq_zexpr. propositional.
  - invert H. econstructor. auto. eapply H0. auto.
  - invert H. econstructor. auto. eapply H0. auto.
  - simpl. rewrite H1. reflexivity.
Qed.  

Lemma eq_zexpr_mul_l : forall a b c,
    eq_zexpr b c ->
    eq_zexpr (b*a)%z (c*a)%z.
Proof.
  unfold eq_zexpr. propositional.
  - invert H. econstructor. eapply H0. auto. auto.
  - invert H. econstructor. eapply H0. auto. auto.
  - simpl. rewrite H1. reflexivity.
Qed.  

Lemma eq_zexpr_fold_left_ZTimes_accum : forall dims acc1 acc2,
    eq_zexpr acc1 acc2 ->
    eq_zexpr (fold_left ZTimes dims acc1)
             (fold_left ZTimes dims acc2).
Proof.
  induct dims; intros.
  - simpl. auto.
  - simpl.
    eapply IHdims.
    eapply eq_zexpr_mul_l.
    auto.
Qed.

Lemma eq_zexpr_add_l : forall a b c,
    eq_zexpr b c ->
    eq_zexpr (b+a)%z (c+a)%z.
Proof.
  unfold eq_zexpr. propositional.
  - invert H. econstructor. eapply H0. auto. auto.
  - invert H. econstructor. eapply H0. auto. auto.
  - simpl. rewrite H1. reflexivity.
Qed.  

Lemma eq_zexpr_mul_fold_left_times : forall dims i z,
    eq_zexpr (i * fold_left ZTimes dims z)%z
             (fold_left ZTimes dims (i * z)%z).
Proof.
  induct dims; intros.
  - simpl. eapply eq_zexpr_id. auto.
  - simpl. eapply eq_zexpr_transitivity.
    2: {eapply eq_zexpr_fold_left_ZTimes_accum.
        eapply eq_zexpr_comm.
        eapply eq_zexpr_mul_assoc. }
    apply IHdims.
Qed.

Lemma eq_zexpr_flatten_shape_index_cons :
  forall vars i n dims,
    length dims = length vars ->
    eq_zexpr (flatten_shape_index (n::dims) (i::vars))
             (ZPlus (fold_left ZTimes dims i)
                    (flatten_shape_index dims vars)).
Proof.
  intros; cases vars; cases dims; simpl in *; try lia.
  - simpl in *. eapply eq_zexpr_add_0_r.
  - invert H.
    eapply eq_zexpr_add_l.
    eapply eq_zexpr_mul_fold_left_times.
Qed.    

Lemma eq_Z_tuple_index_list_empty : 
  eq_Z_tuple_index_list [] [].
Proof.
  unfold eq_Z_tuple_index_list. unfold eq_Z_index_list.
  propositional; simpl; auto.
Qed.

Lemma eq_Z_tuple_index_list_cons_tup : forall l1 l2 x1 x2 y1 y2,
    (eq_zexpr x1 x2 /\
    eq_zexpr y1 y2 /\
    eq_Z_tuple_index_list l1 l2) <->
    (eq_Z_tuple_index_list ((x1,y1)::l1) ((x2,y2)::l2)).
Proof.
  unfold eq_Z_tuple_index_list. unfold eq_Z_index_list.
  propositional; simpl in *.
  - lia.
  - lia.
  - econstructor. simpl. auto. auto.
  - lia.
  - econstructor. simpl. auto. auto.
  - invert H3. auto.
  - invert H4. auto.
  - lia.
  - lia.
  - invert H3. auto.
  - lia.
  - invert H4. auto.
Qed.

Lemma eq_Z_tuple_index_list_cons : forall l1 l2 x y,
    (eq_Z_tup x y /\
    eq_Z_tuple_index_list l1 l2) <->
    (eq_Z_tuple_index_list (x::l1) (y::l2)).
Proof.
  intros. cases x. cases y. unfold eq_Z_tup. simpl.
  split; intros.
  erewrite <- eq_Z_tuple_index_list_cons_tup. propositional.
  eapply eq_Z_tuple_index_list_cons_tup in H. propositional.
Qed.

Lemma eq_Z_tuple_index_list_id : forall l,
    eq_Z_tuple_index_list l l.
Proof.
  induct l.
  - eapply eq_Z_tuple_index_list_empty.
  - cases a. erewrite <- eq_Z_tuple_index_list_cons.
    unfold eq_Z_tup.
    propositional;auto.
Qed.

Lemma eq_Z_tuple_index_list_partially_eval_Z_tup : forall l1 l2 v,
    eq_Z_tuple_index_list l1 l2 ->
    eq_Z_tuple_index_list (map (partially_eval_Z_tup v) l1)
                          (map (partially_eval_Z_tup v) l2).
Proof.
  induct l1; intros; cases l2.
  - simpl. eapply eq_Z_tuple_index_list_id.
  - invert H. simpl in *. lia.
  - invert H. simpl in *. lia.
  - simpl. rewrite <- eq_Z_tuple_index_list_cons.
    rewrite <- eq_Z_tuple_index_list_cons in H. propositional.
    + unfold eq_Z_tup in *. propositional; simpl;
        eapply eq_zexpr_partially_eval_Zexpr; eauto.
    + eauto.
Qed.

Lemma eq_eval_Zexpr_partially_eval_Zexpr : forall e v x,
    eval_Zexpr v e x ->
    eq_zexpr (partially_eval_Zexpr v e) (| x |)%z.
Proof.
  induct 1; simpl in *.
  - eapply eq_zexpr_transitivity.
    eapply eq_zexpr_add; eassumption.
    unfold eq_zexpr; propositional. invert H1. invert H4. invert H6. eauto.
    invert H1. eauto. 
  - eapply eq_zexpr_transitivity.
    eapply eq_zexpr_sub; eassumption.
    unfold eq_zexpr; propositional. invert H1. invert H4. invert H6. eauto.
    invert H1. eauto. 
  - eapply eq_zexpr_transitivity.
    eapply eq_zexpr_mul; eassumption.
    unfold eq_zexpr; propositional. invert H1. invert H4. invert H6. eauto.
    invert H1. eauto. 
  - eapply eq_zexpr_transitivity.
    eapply eq_zexpr_div; eassumption.
    unfold eq_zexpr; propositional. invert H1. invert H4. invert H6. eauto.
    invert H1. eauto. 
  - eapply eq_zexpr_transitivity.
    eapply eq_zexpr_divc; eassumption.
    unfold eq_zexpr; propositional. invert H1. invert H4. invert H6. eauto.
    invert H1. eauto. 
  - eapply eq_zexpr_transitivity.
    eapply eq_zexpr_mod; eassumption.
    unfold eq_zexpr; propositional. invert H1. invert H4. invert H6. eauto.
    invert H1. eauto.
  - eauto.
  - rewrite H. eauto.
Qed.

Lemma eq_zexpr_div_literal : forall x y,
    eq_zexpr (|x| / |y|)%z (| x/ y |)%z.
Proof.
  unfold eq_zexpr.
  propositional. invert H.
  invert H2. invert H4.
  eauto. invert H. eauto.
Qed.
Lemma eq_zexpr_divc_literal : forall x y,
    eq_zexpr (|x| // |y|)%z (| div_ceil x y |)%z.
Proof.
  unfold eq_zexpr.
  propositional. invert H.
  invert H2. invert H4.
  eauto. invert H. eauto.
Qed.
Lemma eq_zexpr_mod_literal : forall x y,
    eq_zexpr (ZMod (|x|)%z  (|y|)%z) (| Zmod x y |)%z.
Proof.
  unfold eq_zexpr.
  propositional. invert H.
  invert H2. invert H4.
  eauto. invert H. eauto.
Qed.

Lemma eq_zexpr_sub_literal : forall x y,
    eq_zexpr (|x| - |y|)%z (| x - y |)%z.
Proof.
  unfold eq_zexpr.
  propositional. invert H.
  invert H2. invert H4.
  eauto. invert H. eauto.
Qed.

Lemma eq_zexpr_add_literal : forall x y,
    eq_zexpr (|x| + |y|)%z (| x + y |)%z.
Proof.
  unfold eq_zexpr.
  propositional. invert H.
  invert H2. invert H4.
  eauto. invert H. eauto.
Qed.

Lemma eq_zexpr_mul_literal : forall x y,
    eq_zexpr (|x| * |y|)%z (| x * y |)%z.
Proof.
  unfold eq_zexpr.
  propositional. invert H.
  invert H2. invert H4.
  eauto. invert H. eauto.
Qed.

Lemma eq_Z_index_list_transitivity :
  forall l1 l2 l3,
    eq_Z_index_list l1 l2 ->
    eq_Z_index_list l2 l3 ->
    eq_Z_index_list l1 l3.
Proof.
  induct l1; intros.
  - invert H. cases l2; cases l3; invert H0; simpl in *; try lia.
    eapply eq_Z_index_list_id.
  - invert H. cases l2; cases l3; invert H0; simpl in *; try lia.
    invert H3. invert H2. simpl in *.
    econstructor. simpl. lia.
    simpl. econstructor. simpl. eapply eq_zexpr_transitivity. eassumption.
    eassumption. unfold eq_Z_index_list in IHl1.
    invert H1. invert H.
    specialize (IHl1 l2 l3). propositional.
Qed.
  
Lemma eq_Z_tuple_index_list_transitivity :
  forall l1 l2 l3,
    eq_Z_tuple_index_list l1 l2 ->
    eq_Z_tuple_index_list l2 l3 ->
    eq_Z_tuple_index_list l1 l3.
Proof.
  unfold eq_Z_tuple_index_list. propositional.
  lia.
  eapply eq_Z_index_list_transitivity; eassumption.
  eapply eq_Z_index_list_transitivity; eassumption.
Qed.

Lemma eq_Z_index_list_sym : forall l1 l2,
    eq_Z_index_list l1 l2 ->    
    eq_Z_index_list l2 l1.
Proof.
  induct l1; intros; cases l2; auto;
    try now (invert H; simpl in *; lia);
    try now (invert H0; simpl in *; lia).
  eapply eq_Z_index_list_cons in H.
  rewrite <- eq_Z_index_list_cons.
  propositional.
  eauto. eapply eq_zexpr_comm. eassumption.
Qed.    

Lemma eq_Z_tuple_index_list_sym : forall l1 l2,
    eq_Z_tuple_index_list l1 l2 ->    
    eq_Z_tuple_index_list l2 l1.
Proof.
  unfold eq_Z_tuple_index_list.
  propositional; try lia; eapply eq_Z_index_list_sym; auto.
Qed.

Lemma partially_eval_Zexpr_fold_left_ZTimes : forall l z v,
    partially_eval_Zexpr v (fold_left ZTimes l z) =
      fold_left ZTimes (map (partially_eval_Zexpr v) l)
                (partially_eval_Zexpr v z).
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. rewrite IHl.
    simpl. auto.
Qed.

Lemma map_partially_eval_Z_tup_ZLit : forall args2 sh v,
    map (partially_eval_Z_tup v) (combine (map ZLit args2) (map ZLit sh)) =
      (combine (map ZLit args2) (map ZLit sh)).
Proof.
  induct args2; intros.
  - simpl in *. reflexivity.
  - simpl in *.
    cases sh.
    + simpl. reflexivity.
    + simpl. f_equal.
      auto.
Qed.

Lemma map_subst_var_in_Z_tup_combine_not_in :
  forall vars sh a z,
    ~ In a vars ->
    map (subst_var_in_Z_tup a z) (combine (map ZVar vars) (map ZLit sh)) =
      combine (map ZVar vars) (map ZLit sh) .
Proof.
  induct vars; intros.
  - reflexivity.
  - simpl. cases sh. reflexivity. simpl.
    unfold subst_var_in_Z_tup at 1. simpl.
    cases (a ==v a0). subst. sets. f_equal.
    eapply IHvars. sets.
Qed.

Lemma eval_Zexpr_Z_fold_left_eq_accum :
  forall sh a b v,
    eq_zexpr a b ->
    eval_Zexpr_Z v (fold_left ZTimes (map ZLit sh) a) =
      eval_Zexpr_Z v (fold_left ZTimes (map ZLit sh) b).
Proof.
  induct sh; intros.
  - simpl. eapply eq_eval_Zexpr_Z. auto.
  - simpl. eapply IHsh.
    eapply eq_zexpr_mul. auto. auto.
Qed.

Lemma eval_Zexpr_Z_fold_left_ZTimes_ZLit : forall sh z1 v,
    eval_Zexpr_Z v (fold_left ZTimes (map ZLit sh) (| z1 |)%z) =
      Some (fold_left (Z.mul) sh z1).
Proof.
  induct sh; intros.
  - reflexivity.
  - simpl.
    erewrite eval_Zexpr_Z_fold_left_eq_accum.
    2: eapply eq_zexpr_mul_literal.
    rewrite IHsh.
    reflexivity.
Qed.

Lemma eval_Zexpr_fold_app_end : forall l v val n s,
    eval_Zexpr v (ZTimes n (fold_left ZTimes l s)) val ->
    eval_Zexpr v (fold_left ZTimes (l ++ [n]) s) val.
Proof.
  induct l; intros; simpl in *.
  - invert H. rewrite Z.mul_comm. auto.
  - invert H. auto.
Qed.

Lemma fold_left_mul_distr : forall zs x y,
    fold_left Z.mul zs (x - y)%Z =
      (fold_left Z.mul zs x - fold_left Z.mul zs y)%Z.
Proof.
  induct zs; intros; simpl.
  - reflexivity.
  - rewrite Z.mul_sub_distr_r.
    eauto.
Qed.

Lemma eval_flatten_shape_index_cons :
  forall l n i offset iz v stride x xs val,
    eval_Zexpr v (flatten_shape_index (map snd l) (map fst l)) offset ->
    eval_Zexpr v i iz ->
    l = x :: xs ->
    val = (iz * stride + offset)%Z ->
    eval_Zexpr v (fold_left ZTimes (map snd xs) (snd x)) stride ->
    eval_Zexpr v (flatten_shape_index (n :: map snd l) (i :: map fst l)) val.
Proof.
  induct l; intros.
  - discriminate.
  - invert H1.
    simpl in *.
    cases xs.
    + simpl in *. eauto.
    + simpl in *.
      invert H.
      invert H4.
      pose proof H6.
      eapply IHl in H6. 4: reflexivity.
      5: eassumption.
      2: eassumption.
      2: eassumption.
      2: reflexivity.
      invert H6.
      eapply eval_Zexpr_deterministic in H; try eassumption. subst.
      invert H8.
      eapply eval_Zexpr_deterministic in H9; try eassumption. subst.
      eapply eval_Zexpr_deterministic in H10; try eassumption. subst.
      eauto.
Qed.

Lemma eval_flatten_shape_index_app_end : forall l n i offset nz iz v,
  eval_Zexpr v (flatten_shape_index (map snd l) (map fst l)) offset ->
  eval_Zexpr v n nz ->
  eval_Zexpr v i iz ->
  eval_Zexpr v (flatten_shape_index (map snd l ++ [n]) (map fst l ++ [i]))
             (offset*nz+iz).
Proof.
  induct l; intros.
  - simpl in *. invert H. rewrite Z.mul_0_l. rewrite Z.add_0_l. auto.
  - simpl map in *.
    cases l; try cases l; simpl map in *.
    + simpl in *.
      eauto.
    + simpl in *.
      invert H. invert H4.
      replace ((xz0 * yz0 + yz) * nz + iz)%Z with
        ((xz0 * (yz0 * nz)) + ((yz * nz) + iz))%Z by lia.
      eauto.
    + rewrite <- app_comm_cons.
      replace ((snd p :: snd p0 :: map snd l) ++ [n])%list with
        (map snd (p::p0::l++[(i,n)])).
      2: { simpl. rewrite map_app. reflexivity. }
      
      rewrite <- app_comm_cons.
      replace ((fst p :: fst p0 :: map fst l) ++ [i])%list with
        (map fst (p::p0::l++[(i,n)])).
      2: { simpl. rewrite map_app. reflexivity. }

      simpl in H.
      invert H.
      invert H4.
      invert H6.
      invert H4.

      eapply eval_flatten_shape_index_cons.
      3: reflexivity.
      4: { simpl. rewrite map_app. simpl.
           eapply eval_Zexpr_fold_app_end.
           econstructor. eassumption.
           eassumption. }
      simpl map. repeat rewrite map_app. simpl map.
      eapply IHl.  simpl.
      econstructor. econstructor. eassumption. eassumption.
      eassumption. eassumption. eassumption.
      eassumption. lia.
Qed.

Lemma partially_eval_Zexpr_flatten_shape_index : forall l1 l2 v,
    (partially_eval_Zexpr v (flatten_shape_index l1 l2))
    = flatten_shape_index
       (map (partially_eval_Zexpr v) l1)
       (map (partially_eval_Zexpr v) l2).
 Proof.
   induct l1; intros; cases l2.
   - simpl. auto.
   - simpl. auto.
   - simpl. unfold flatten_shape_index.
     cases l1; auto.
   - simpl.
     cases l1; cases l2.
     + simpl. auto.
     + simpl. auto.
     + simpl. unfold flatten_shape_index. cases l1; auto. simpl.
       f_equal. f_equal.
       eapply partially_eval_Zexpr_fold_left_ZTimes. 
     + simpl.
       f_equal. f_equal. eapply partially_eval_Zexpr_fold_left_ZTimes. 
       rewrite IHl1. simpl. auto.
Qed.

Fixpoint flatten (sh : list Z) (i : list Z) :=
  match sh with
  | n::m::ns =>
    match i with
    | x::xs =>
        let stride := fold_left Z.mul ns m in
        ((x * stride) + (flatten (m::ns) xs))%Z
    | _ => 0%Z
    end
  | [n] =>
    match i with
    | [z] => z
    | _ => 0%Z
    end
  | _ => 0%Z
  end.

Lemma eval_Zexpr_Z_flatten_index_ZLit_flatten : forall sh args v,
    eval_Zexpr_Z v (flatten_shape_index (map ZLit sh) (map ZLit args)) =
      Some (flatten sh args).
Proof.
  induct sh; intros.
  - simpl. cases args.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - simpl. cases sh.
    + simpl.
      cases args.
      * simpl. reflexivity.
      * simpl. unfold flatten_shape_index.
        cases args.
        simpl. reflexivity.
        simpl. reflexivity.
    + simpl.
      cases args.
      * simpl. reflexivity.
      * simpl.
        rewrite eval_Zexpr_Z_fold_left_ZTimes_ZLit.
        rewrite IHsh. reflexivity.
Qed.

Lemma subst_var_in_Zexpr_fold_left_Times :
  forall index k var p,
  subst_var_in_Zexpr var k (fold_left ZTimes index p) =
  fold_left ZTimes
            (map (fun x => subst_var_in_Zexpr var k x) index)
    (subst_var_in_Zexpr var k p).
Proof.
  induction index; intros.
  - reflexivity.
  - simpl. rewrite IHindex.
    reflexivity.
Qed.

Lemma subst_var_in_Zexpr_flatten_index :
  forall var k index, 
    subst_var_in_Zexpr var k (flatten_index index) =
      flatten_index (map (fun t => (subst_var_in_Z_tup var k t)) index).
Proof.
  unfold flatten_index.
  induction index.
  - reflexivity.
  - simpl. repeat rewrite map_map in *. simpl in *.
    cases index.
    + simpl in *. eauto.
    + simpl in *.
      f_equal. f_equal.
      rewrite subst_var_in_Zexpr_fold_left_Times.
      rewrite map_map. reflexivity.
      eauto.
Qed.

Lemma subst_var_in_Z_tup_partially_eval_Z_tup_comm : forall e a x v,
    ~ a \in dom v ->
    subst_var_in_Z_tup a x (partially_eval_Z_tup v e) =
      partially_eval_Z_tup v (subst_var_in_Z_tup a x e).
Proof.
  unfold subst_var_in_Z_tup. unfold partially_eval_Z_tup.
  intros. simpl.
  repeat rewrite subst_var_in_Zexpr_partially_eval_Zexpr_comm.  
  reflexivity.
  eapply None_dom_lookup. auto.
  eapply None_dom_lookup. auto.
Qed.

Lemma partially_eval_Zexpr_add :
  forall e v var k,
    ~ var \in dom v ->
    partially_eval_Zexpr (v $+ (var,k)) e =
      subst_var_in_Zexpr var k (partially_eval_Zexpr v e).
Proof.
  induct e; propositional; simpl; try rewrite IHe1, IHe2; auto.
  cases (x ==v var); subst.
  - rewrite lookup_add_eq by auto.
    rewrite None_dom_lookup by sets.
    simpl. cases (var ==v var). reflexivity. propositional.
  - rewrite lookup_add_ne by auto.
    cases (v $? x); simpl. reflexivity.
    cases (x ==v var); subst; propositional.
Qed.

Lemma partially_eval_Z_tup_add_partial :
  forall var k v,
    ~ var \in dom v ->
              partially_eval_Z_tup (v $+ (var, k)) =
                fun e => subst_var_in_Z_tup var k (partially_eval_Z_tup v e).
Proof.
  intros. unfold partially_eval_Z_tup. unfold subst_var_in_Z_tup.
  apply functional_extensionality. intros. cases x. simpl.
  f_equal; eapply partially_eval_Zexpr_add; auto.
Qed.

Lemma fold_left_subst_var_in_Z_tup_ZLit :
  forall z z0 vars x,
    fold_left
    (fun (a0 : Zexpr * Zexpr) (t0 : var * Z) =>
     subst_var_in_Z_tup (fst t0) (snd t0) a0) (combine vars x)
    ((| z |)%z, (| z0 |)%z) = ((| z |)%z, (| z0 |)%z).
Proof.
  induct vars; intros.
  - reflexivity.
  - simpl. cases x. simpl. reflexivity.
    eauto.
Qed.

Lemma partially_eval_Zexpr_add_partial :
  forall v var k,
    ~ var \in dom v ->
    partially_eval_Zexpr (v $+ (var,k)) =
      fun e => subst_var_in_Zexpr var k (partially_eval_Zexpr v e).
Proof.
  intros. eapply functional_extensionality. intros.
  induction x; propositional; simpl; try rewrite IHx1; try rewrite IHx2; auto.
  cases (x ==v var); subst.
  - rewrite lookup_add_eq by auto.
    rewrite None_dom_lookup by sets.
    simpl. cases (var ==v var). reflexivity. propositional.
  - rewrite lookup_add_ne by auto.
    cases (v $? x); simpl. reflexivity.
    cases (x ==v var); subst; propositional.
Qed.

Lemma partially_eval_Z_tup_add :
  forall e v var k,
    ~ var \in dom v ->
    partially_eval_Z_tup (v $+ (var,k)) e =
      subst_var_in_Z_tup var k (partially_eval_Z_tup v e).
Proof.
  unfold partially_eval_Z_tup. unfold subst_var_in_Z_tup.
  unfold partially_eval_Z_tup.
  intros. repeat rewrite partially_eval_Zexpr_add by auto.
  reflexivity.
Qed.

Lemma partially_eval_Zexpr_fold_left_Times :
  forall v l p,
    partially_eval_Zexpr v (fold_left ZTimes l p) =
      fold_left ZTimes (map (partially_eval_Zexpr v) l)
                (partially_eval_Zexpr v p).
Proof.
  induction l; intros.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Lemma flatten_index_partially_eval_Zexpr :
  forall (l : list (Zexpr * Zexpr)) v,
    partially_eval_Zexpr v (flatten_index l) =
      flatten_index (map (fun tp => (partially_eval_Zexpr v (fst tp),
                            partially_eval_Zexpr v (snd tp))) l).
Proof.
  unfold flatten_index.
  induct l; intros.
  - reflexivity.
  - specialize (IHl v).
    repeat rewrite map_map in *. simpl in *.
    cases l.
    + reflexivity.
    + simpl. f_equal. f_equal.
      rewrite partially_eval_Zexpr_fold_left_Times.
      rewrite map_map. reflexivity.
      eauto.
Qed.

Lemma flatten_index_partially_eval_Z_tup :
  forall (l : list (Zexpr * Zexpr)) v,
    partially_eval_Zexpr v (flatten_index l) =
      flatten_index (map (fun tp => partially_eval_Z_tup v tp) l).
Proof.
  intros. rewrite flatten_index_partially_eval_Zexpr. reflexivity.
Qed.

Lemma fold_left_subst_var_in_Zexpr_partially_eval_Zexpr_ :
  forall vars x e v,
    (Forall (fun x => ~ x \in dom v) vars) ->
    fold_left (fun z0 tup => subst_var_in_Zexpr (fst tup) (snd tup) z0)
              (combine vars x) (partially_eval_Zexpr v e) =
      partially_eval_Zexpr v
                           (fold_left
                              (fun z0 tup =>
                                 subst_var_in_Zexpr (fst tup) (snd tup) z0)
                              (combine vars x) e).
Proof.
  induct vars; intros; simpl in *.
  - reflexivity.
  - cases x.
    + simpl. reflexivity.
    + simpl. invert H.
      rewrite subst_var_in_Zexpr_partially_eval_Zexpr_comm.
      rewrite IHvars. reflexivity. auto.
      eapply None_dom_lookup. auto.
Qed.    

Lemma fold_left_subst_var_in_Zexpr_flatten_index :
  forall tups e,
  fold_left
    (fun z0 tup => subst_var_in_Zexpr (fst tup) (snd tup) z0) tups
    (flatten_index e) =
    flatten_index
      (map (fold_left
              (fun z0 tup =>
                 subst_var_in_Z_tup (fst tup) (snd tup) z0) tups) e).
Proof.
  induct tups; intros.
  - simpl. rewrite map_id. reflexivity.
  - simpl. rewrite subst_var_in_Zexpr_flatten_index.
    rewrite IHtups. rewrite map_map.
    reflexivity.
Qed.

Lemma partially_eval_Zexpr_empty_id : forall e,
    partially_eval_Zexpr $0 e = e.
Proof.
  induct e; simpl in *; try rewrite IHe1; try rewrite IHe2; try rewrite IHe3;
    auto.
  rewrite lookup_empty. auto.
Qed.

Lemma partially_eval_Z_tup_empty_id :
  partially_eval_Z_tup $0 = (fun e => e).
Proof.
  eapply functional_extensionality. intros.
  cases x. unfold partially_eval_Z_tup.
  simpl. f_equal; apply partially_eval_Zexpr_empty_id.
Qed.

Lemma not_In_in_bool_false : forall l1 i,
    ~ In i l1 <->
      Zexpr.in_bool l1 i = false.
Proof.
  induct l1; propositional.
  - simpl. cases (a ==v i). subst. simpl in *. propositional.
    eapply eqb_neq in n. rewrite n. simpl.
    simpl in H.
    eapply IHl1. auto.
  - simpl in *. invert H0.
    rewrite String.eqb_refl in H. simpl in *. discriminate.
    eapply IHl1. 2: eassumption. 
    eapply orb_false_iff in H. propositional.
Qed.    

Lemma combine_eq_id : forall l,
    Forall (fun t => eq_zexpr (fst t) (snd t))
           (combine l l).
Proof. induct l; simpl; auto. Qed.


Lemma index_to_function_alt_vars_cons :
  forall var vars k x
         (reindexer : list (Zexpr * Zexpr) -> list (Zexpr * Zexpr)) v l,
    ~ var \in dom v ->
    index_to_function_alt
      (map (partially_eval_Z_tup v)
           (reindexer l)) (var::vars) (k :: x) = 
      index_to_function_alt        
        (map (partially_eval_Z_tup v)
             (map (fun e => (subst_var_in_Z_tup var k e))
                  (reindexer l))) vars x.
Proof.
  intros. unfold index_to_function_alt.
  eq_match_discriminee.
  unfold index_to_function_rec_alt. simpl.
  rewrite subst_var_in_Zexpr_flatten_index.
  rewrite map_map.
  replace (fun x0 : Zexpr * Zexpr =>
             subst_var_in_Z_tup var k (partially_eval_Z_tup v x0)) with
    (fun x0 : Zexpr * Zexpr =>
       partially_eval_Z_tup v (subst_var_in_Z_tup var k x0)).
  2: { eapply functional_extensionality. intros.
       rewrite subst_var_in_Z_tup_partially_eval_Z_tup_comm. reflexivity.
       auto. }
  rewrite <- map_map. reflexivity.
Qed.

Lemma index_to_function_alt_subst_vars_partial :
  forall vars (rdxr : list (Zexpr * Zexpr) -> list (Zexpr * Zexpr)) l v,
    (Forall (fun var =>  ~ var \in dom v) vars) ->
    index_to_function_alt (map (partially_eval_Z_tup v) (rdxr l)) vars =
      fun x =>
        index_to_function_alt
        (map (partially_eval_Z_tup v)
             (map (fun y =>
                     fold_left (fun a t => subst_var_in_Z_tup
                                             (fst t) (snd t) a)
                               (combine vars x) y) (rdxr l))) [] [].
Proof.
  induct vars; intros; eapply functional_extensionality; intros.
  - rewrite map_map. reflexivity.
  - cases x.
    + unfold index_to_function_alt.
      eq_match_discriminee.
      rewrite map_map. reflexivity.
    + invert H.
      rewrite index_to_function_alt_vars_cons by auto.
      rewrite IHvars by (auto; lia).
      repeat rewrite map_map.
      reflexivity.
Qed.

Lemma index_to_function_alt_subst_vars :
  forall vars x (rdxr : list (Zexpr * Zexpr) -> list (Zexpr * Zexpr)) l v,
    (Forall (fun var =>  ~ var \in dom v) vars) ->
    index_to_function_alt (map (partially_eval_Z_tup v) (rdxr l)) vars x =
      index_to_function_alt
        (map (partially_eval_Z_tup v)
             (map (fun y =>
                     fold_left (fun a t => subst_var_in_Z_tup
                                             (fst t) (snd t) a)
                               (combine vars x) y) (rdxr l))) [] [].
Proof.
  induct vars; intros; cases x.
  - rewrite map_map. reflexivity.
  - unfold index_to_function_alt. eq_match_discriminee.
    simpl. rewrite map_map. reflexivity.
  - unfold index_to_function_alt. eq_match_discriminee.
    simpl. rewrite map_map. reflexivity.
  - invert H.
    rewrite index_to_function_alt_vars_cons by auto.
    rewrite IHvars by (auto; lia).
    repeat rewrite map_map.
    reflexivity.
Qed.

Fixpoint vars_of_reindexer cont :=
  match cont with
  | [] => constant nil
  | (i,n)::xs => constant (vars_of_Zexpr i) \cup constant (vars_of_Zexpr n)
                          \cup vars_of_reindexer xs
  end.

Lemma eq_Z_tuple_index_list_eq_vars_of_reindexer : forall l1 l2,
    eq_Z_tuple_index_list l1 l2 ->
    vars_of_reindexer l1 = vars_of_reindexer l2.
Proof.
  induct l1; intros; cases l2.
  - reflexivity.
  - invert H. simpl in *. lia.
  - invert H. simpl in *. lia.
  - rewrite <- eq_Z_tuple_index_list_cons in H. propositional.
    simpl. cases a. cases p.
    f_equal. 
    unfold eq_Z_tup in H0. invert H0. simpl in *.
    unfold eq_zexpr in H, H2.
    propositional. rewrite H3, H4. reflexivity.
    eauto.
Qed.
Lemma map_fold_left_subst_var_in_Z_tup_reindexer :
  forall reindexer vars x l,
    (forall (var : var) (k : Z) (l : list (Zexpr * Zexpr)),
       (var \in vars_of_reindexer (reindexer []) -> False) ->
       map (subst_var_in_Z_tup var k) (reindexer l) =
       reindexer (map (subst_var_in_Z_tup var k) l)) ->    
    (Forall (fun var => ~ var \in vars_of_reindexer (reindexer [])) vars) ->
    map
      (fun y =>
         fold_left
           (fun a t0 => subst_var_in_Z_tup (fst t0) (snd t0) a)
           (combine vars x) y)
      (reindexer l) = 
      (reindexer (map
                    (fun y =>
                       fold_left
                         (fun a t0 => subst_var_in_Z_tup (fst t0) (snd t0) a)
                         (combine vars x) y) l)).
Proof.
  induct vars; intros; cases x.
  - simpl. repeat rewrite map_id. reflexivity.
  - simpl. repeat rewrite map_id. reflexivity.
  - simpl. repeat rewrite map_id. reflexivity.
  - simpl. rewrite <- map_map. symmetry. rewrite <- map_map. symmetry.
    pose proof H. rewrite H1.
    erewrite IHvars. reflexivity. eassumption.
    invert H0. auto. invert H0. auto.
Qed.
 
Lemma length_eval_Zexprlist : forall l1 l2 v,
    eval_Zexprlist v l1 l2 ->
    length l1 = length l2.
Proof.
  induct 1; simpl; auto.
Qed.

Lemma eval_Zexprlist_map_ZLit : forall sh,
    eval_Zexprlist $0 (map ZLit sh) sh.
Proof.
  induct sh; simpl; eauto.
Qed.

Lemma eval_Zexpr_Z_fold_left_assoc : forall xs z4 x v,
    eval_Zexpr_Z v (fold_left ZTimes xs (z4 * x)%z) =
      eval_Zexpr_Z v ((fold_left ZTimes xs z4) * x)%z.
Proof.
  induct xs; intros.
  - reflexivity.
  - simpl fold_left. simpl eval_Zexpr_Z.
    rewrite IHxs. simpl.
    rewrite IHxs.
    rewrite IHxs.
    simpl.
    cases (eval_Zexpr_Z v (fold_left ZTimes xs z4)); auto.
    cases (eval_Zexpr_Z v x); cases (eval_Zexpr_Z v a); auto.
    f_equal. lia.
Qed.

Lemma eval_Zexpr_Z_fold_left_ZTimes :
  forall sh shz v,
    eval_Zexprlist v sh shz ->
    forall z4 z,
      eval_Zexpr v z4 z ->
      eval_Zexpr_Z v (fold_left ZTimes sh z4) = Some (fold_left Z.mul shz z).
Proof.
  induct 1; intros.
  - simpl. eapply eval_Zexpr_Z_eval_Zexpr. auto.
  - simpl. eapply IHeval_Zexprlist in H1.
    rewrite fold_left_mul_assoc.
    rewrite eval_Zexpr_Z_fold_left_assoc. simpl.
    rewrite H1.
    eapply eval_Zexpr_Z_eval_Zexpr in H. rewrite H. reflexivity.
Qed.
Arguments flatten : simpl nomatch.

Lemma eval_Zexpr_Z_flatten_index_flatten:
  forall (sh args : list Zexpr) shz argsz (v : valuation),
    eval_Zexprlist v sh shz ->
    eval_Zexprlist v args argsz ->
    eval_Zexpr_Z v (flatten_shape_index sh args) = Some (flatten shz argsz).
Proof.
  induct sh; intros; cases args; try invert H; try invert H0.
  - reflexivity.
  - reflexivity.
  - simpl. unfold flatten_shape_index.
    cases sh; cases zs; auto.
  - cases zs0; cases zs; cases sh; cases args;
      try invert H6; try invert H7.
    + eapply eval_Zexpr_Z_eval_Zexpr. auto.
    + simpl.
      eapply eval_Zexpr_Z_eval_Zexpr in H3. rewrite H3.
      erewrite eval_Zexpr_Z_fold_left_ZTimes; try eassumption.
      erewrite IHsh; try eauto.
    + reflexivity.
    + simpl. erewrite IHsh.
      2: { econstructor. eauto. eauto. }
      2: { econstructor. eauto. eauto. }
      eapply eval_Zexpr_Z_eval_Zexpr in H3. rewrite H3.
      erewrite eval_Zexpr_Z_fold_left_ZTimes; try eassumption.
      reflexivity.
Qed.      

Lemma In_app_no_dups : forall l1 l2 i,
    ~ In i (l1 ++/ l2) ->
    ~ In i l1 /\ ~ In i l2.
Proof.
  induct l1; intros.
  - simpl in *. rewrite app_no_dups_empty_l in H.
    propositional.
  - simpl in *. unfold not. split.
    + intros. eapply H. invert H0.
      left. auto. right.
      eapply in_or_app. left. auto.
    + intros. apply H. right.
      eapply in_or_app.
      pose proof (In_dec string_dec i l1). invert H1.
      * left. auto.
      * right. eapply In_iff_in.
        replace (fun v : var => negb ((a =? v) || Zexpr.in_bool l1 v)) with
          (fun v : var => negb (a =? v) && negb  (Zexpr.in_bool l1 v)).
        2: { eapply functional_extensionality.
             intros. rewrite negb_orb. reflexivity. }
        assert (a <> i). propositional.
        rewrite <- In_iff_in.
        eapply filter_In.
        split. auto.
        eapply eqb_neq in H1. rewrite H1. simpl.
        eapply not_In_in_bool_false in H2. rewrite H2. reflexivity.
Qed.

Lemma subst_var_in_Zexpr_id : forall lo i loz,
  ~ In i (vars_of_Zexpr lo) ->
  subst_var_in_Zexpr i loz lo = lo.
Proof.
  induct lo; intros; simpl in *; try eapply In_app_no_dups in H; invs;
    try rewrite IHlo1; try rewrite IHlo2; auto.
  cases (x ==v i); propositional.
Qed.

Lemma subst_var_in_Z_tup_id :
  forall lo (i : var) (loz : Z),
    ~ In i (vars_of_Zexpr (fst lo)) ->
    ~ In i (vars_of_Zexpr (snd lo)) ->
    subst_var_in_Z_tup i loz lo = lo.
Proof.
  intros. cases lo. unfold subst_var_in_Z_tup.
  simpl in *. f_equal; eapply subst_var_in_Zexpr_id; auto.
Qed.

Lemma fold_left_subst_var_in_Z_tup_id : forall a b l,
    vars_of_Zexpr a = [] ->
    vars_of_Zexpr b = [] ->
    fold_left
      (fun (a : Zexpr * Zexpr) (t0 : var * Z) =>
         subst_var_in_Z_tup (fst t0) (snd t0) a) l (a, b) = (a,b).
Proof.
  induct l; intros.
  - reflexivity.
  - propositional. simpl.
    rewrite subst_var_in_Z_tup_id. auto.
    simpl. rewrite H. sets. simpl. rewrite H0. sets.
Qed.

Lemma fold_left_mul_pos : forall l x,
    (Forall (fun z => 0 < z)%Z l) ->
    (0 < x)%Z ->
    (0 < fold_left Z.mul l x)%Z.
Proof.
  induct 1; intros; simpl.
  - lia.
  - rewrite fold_left_mul_assoc.
    eapply Z.mul_pos_pos; eauto.
Qed.

Lemma fold_left_mul_nonneg : forall l x,
    (Forall (fun z => 0 <= z)%Z l) ->
    (0 <= x)%Z ->
    (0 <= fold_left Z.mul l x)%Z.
Proof.
  induct 1; intros; simpl.
  - lia.
  - rewrite fold_left_mul_assoc.
    eapply Z.mul_nonneg_nonneg; eauto.
Qed.

Lemma map_fold_left_subst_var_in_Z_tup_combine :
  forall vars x sh,
    length vars = length x ->
    no_dup vars ->
    map
      (fun y : Zexpr * Zexpr =>
         fold_left
           (fun (a : Zexpr * Zexpr) (t0 : var * Z) =>
              subst_var_in_Z_tup (fst t0) (snd t0) a) (combine vars x) y)
      (combine (map ZVar vars) (map ZLit sh)) =
      combine (map ZLit x) (map ZLit sh).
Proof.
  induction vars; intros; cases x; simpl in *; try lia.
  - reflexivity.
  - cases sh.
    + reflexivity.
    + simpl.
      f_equal.
      unfold subst_var_in_Z_tup at 2. simpl.
      cases (a ==v a); propositional. clear e.
      eapply fold_left_subst_var_in_Z_tup_ZLit.
      rewrite <- map_map.
      invert H0.
      rewrite map_subst_var_in_Z_tup_combine_not_in by auto.
      eapply IHvars. lia. auto.
Qed.

Lemma eq_Z_tup_fold_left_subst_var_in_Z_tup : forall l1 vars idx,
    Forall (fun var => ~ In var vars) (vars_of_Zexpr (fst l1)) ->
    Forall (fun var => ~ In var vars) (vars_of_Zexpr (snd l1)) ->
      (fold_left
         (fun a t0 =>
            subst_var_in_Z_tup (fst t0) (snd t0) a)
         (combine vars idx) l1) = l1. 
Proof.
  induction vars; intros; simpl in *.
  - auto.
  - cases idx.
    + reflexivity.
    + simpl. rewrite subst_var_in_Z_tup_id.
      eapply IHvars.
      eapply Forall_impl. 2: eapply H.
      propositional. eapply H1. propositional.
      eapply Forall_impl. 2: eapply H0.
      propositional. eapply H1. propositional.
      unfold not. intros.
      eapply Forall_forall in H1. 2: apply H. simpl in *.
      propositional.
      unfold not. intros.
      eapply Forall_forall in H1. 2: apply H0. simpl in *.
      propositional.
Qed.      

Lemma constant_filter_negb_in_bool : forall l1 l2,
    constant l1 \cup
             constant
             (filter (fun x => negb (Zexpr.in_bool l1 x)) l2) =
       constant l1 \cup constant l2.
Proof.
  induct l1; intros.
  - simpl. rewrite filter_true_id.
    reflexivity.
  - simpl.
    replace (fun x : var => negb ((a =? x) || Zexpr.in_bool l1 x)) with
      (fun x : var => negb (Zexpr.in_bool l1 x) && negb (a =? x)).
    2: { eapply functional_extensionality. intros.
         rewrite negb_orb. rewrite andb_comm. reflexivity. }
    rewrite <- filter_filter.
    rewrite constant_cons. rewrite union_assoc.
    rewrite IHl1.
    rewrite <- union_assoc. repeat rewrite (union_comm (constant [a])).
    repeat rewrite union_assoc. f_equal.
    eapply constant_singleton_filter_neg_eq.
Qed.

Lemma constant_app_no_dups : forall l1 l2,
    constant (l1 ++/ l2) = constant l1 \cup constant l2.
Proof.
  induct l1; intros.
  - rewrite cup_empty_l.
    rewrite app_no_dups_empty_l.
    reflexivity.
  - rewrite constant_cons.
    unfold app_no_dups in *. simpl in *.
    rewrite union_constant. simpl.
    rewrite union_constant. simpl.
    replace (fun v : var => negb ((a =? v) || Zexpr.in_bool l1 v)) with
      (fun v : var => negb (Zexpr.in_bool l1 v) && negb (a =? v)).
    2: { eapply functional_extensionality. intros.
         rewrite negb_orb. rewrite andb_comm. reflexivity. }
    rewrite <- filter_filter.
    symmetry.
    rewrite constant_cons.
    symmetry.
    rewrite <- union_constant.
    rewrite <- IHl1.
    rewrite <- constant_cons.
    rewrite constant_cons.
    symmetry.
    rewrite constant_cons.
    symmetry.
    rewrite <- union_constant.
    rewrite <- union_constant.
    rewrite constant_filter_negb_in_bool.
    rewrite constant_filter_negb_in_bool.
    repeat rewrite <- union_assoc.
    rewrite (union_comm (constant [a])).
    repeat rewrite union_assoc.
    rewrite constant_singleton_filter_neg_eq.
    reflexivity.
Qed.

Lemma vars_not_in_vars_of_Zexpr :
  forall e v x i,
  eval_Zexpr v e x ->
  ~ i \in dom v ->
          ~ In i (vars_of_Zexpr e).
Proof.
  setoid_rewrite In_iff_in.
  induct e; intros; simpl; try rewrite constant_app_no_dups; try invert1 H;
    try eapply IHe1 in H3; try eapply IHe2 in H5; try eassumption; try sets.
  eapply lookup_Some_dom in H2. sets.
Qed.

Lemma eval_Zexpr_vars_in_valuation :
  forall e v r,
    eval_Zexpr v e r ->
    constant (vars_of_Zexpr e) \subseteq dom v.
Proof.
  induct 1; simpl; try rewrite constant_app_no_dups; auto.
  eapply lookup_Some_dom in H. sets.
Qed.

Lemma eval_Zexpr_forall_vars_of_Zexpr : forall e v ez,
  eval_Zexpr v e ez ->
  Forall (fun var => var \in dom v) (vars_of_Zexpr e).
Proof.
  induct 1; simpl; unfold app_no_dups; try apply Forall_app; try split;
    try now auto using forall_filter_weaken.
  econstructor; eauto.
  eapply lookup_Some_dom. eauto.
Qed.

Lemma eval_Zexprlist_add : forall l v lz,
    eval_Zexprlist v l lz ->
    forall x i,
    ~ i \in dom v ->
    eval_Zexprlist (v $+ (i,x)) l lz.
Proof.
  induct 1; intros.
  - econstructor.
  - econstructor.
    eapply eval_Zexpr_subst_var_in_Zexpr.
    rewrite subst_var_in_Zexpr_id. auto.
    eapply vars_not_in_vars_of_Zexpr. eassumption. auto.
    eauto.
Qed.    

Lemma eq_zexpr_literal_subst_var_in_Zexpr : forall x xz v k,
    eq_zexpr x (|xz|)%z ->
    eq_zexpr (subst_var_in_Zexpr v k x) (|xz|)%z.
Proof.
  unfold eq_zexpr. propositional; simpl in *.
  rewrite subst_var_in_Zexpr_id in H. eapply H0 in H. eauto.
  rewrite H1. sets.
  rewrite subst_var_in_Zexpr_id. eapply H0 in H. eauto.
  rewrite H1. sets.
  rewrite vars_of_Zexpr_subst_var_in_Zexpr. rewrite H1. reflexivity.
Qed.    

Lemma eval_Zexprlist_includes_valuation : forall v l lz v',
    eval_Zexprlist v l lz ->
    v $<= v' ->
    eval_Zexprlist v' l lz.
Proof.
  induct l; intros.
  - invert H. eauto.
  - invert H. econstructor.
    eapply eval_Zexpr_includes_valuation; eauto. eauto.
Qed.

Definition eval_Zexpr_Z_total v e :=
  match eval_Zexpr_Z v e with
  | Some x => x
  | _ => 0%Z
  end.

Lemma vars_of_Zexpr_empty_eval_Zexpr_literal :
  forall e,
    vars_of_Zexpr e = [] ->
    exists x,
    forall v,      
    eval_Zexpr v e x.
Proof.
  induct e; simpl in *; intros; try eapply app_no_dups_empty_args in H;
    propositional; invs; eauto.
  invert H.
Qed.

Lemma vars_of_Zexpr_empty_eq_eval_Zexpr : forall e v1 v2 x y,
    vars_of_Zexpr e = [] ->
    eval_Zexpr v1 e x ->
    eval_Zexpr v2 e y ->
    x = y.
Proof.
  intros.
  eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H. invs.
  pose proof (H2 v1). pose proof (H2 v2). eq_eval_Z.
  auto.
Qed.

Lemma forall_no_vars_eval_Zexpr_Z_total :
  forall l,
    Forall (fun z : Zexpr => vars_of_Zexpr z = []) l ->
    forall v,
  eval_Zexprlist v l (map (eval_Zexpr_Z_total $0) l).
Proof.
  induct l; intros.
  - econstructor.
  - simpl. invert H. propositional.
    econstructor.
    unfold eval_Zexpr_Z_total.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H2. invs.
    pose proof H0.
    specialize (H0 $0). eapply eval_Zexpr_Z_eval_Zexpr in H0. rewrite H0.
    eapply H1. eauto.
Qed.

Lemma vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total : forall n v,
  vars_of_Zexpr n = [] ->
  eq_zexpr n (| eval_Zexpr_Z_total v n |)%z.
Proof.
  unfold eq_zexpr.
  induct n; propositional.
  - invert H0. simpl in *.
    eapply app_no_dups_empty_args in H. invs.
    unfold eval_Zexpr_Z_total.
    simpl.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H0,H1. invs.
    pose proof (H v). pose proof (H1 v).
    pose proof (H v0). pose proof (H1 v0).
    eq_eval_Z.
    eapply eval_Zexpr_Z_eval_Zexpr in H0,H2. rewrite H0,H2 in *.
    eauto.
  - invert H0. simpl in *.
    eapply app_no_dups_empty_args in H. invs.
    unfold eval_Zexpr_Z_total.
    simpl.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H0,H1. invs.
    pose proof (H v). pose proof (H1 v).
    pose proof (H v0). pose proof (H1 v0).
    eq_eval_Z.
    eapply eval_Zexpr_Z_eval_Zexpr in H0,H2. rewrite H0,H2 in *.
    eauto.
  - invert H0. simpl in *.
    eapply app_no_dups_empty_args in H. invs.
    unfold eval_Zexpr_Z_total.
    simpl.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H0,H1. invs.
    pose proof (H v). pose proof (H1 v).
    pose proof (H v0). pose proof (H1 v0).
    eq_eval_Z.
    eapply eval_Zexpr_Z_eval_Zexpr in H0,H2. rewrite H0,H2 in *.
    eauto.
  - invert H0. simpl in *.
    eapply app_no_dups_empty_args in H. invs.
    unfold eval_Zexpr_Z_total.
    simpl.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H0,H1. invs.
    pose proof (H v). pose proof (H1 v).
    pose proof (H v0). pose proof (H1 v0).
    eq_eval_Z.
    eapply eval_Zexpr_Z_eval_Zexpr in H0,H2. rewrite H0,H2 in *.
    eauto.
  - invert H0. simpl in *.
    eapply app_no_dups_empty_args in H. invs.
    unfold eval_Zexpr_Z_total.
    simpl.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H0,H1. invs.
    pose proof (H v). pose proof (H1 v).
    pose proof (H v0). pose proof (H1 v0).
    eq_eval_Z.
    eapply eval_Zexpr_Z_eval_Zexpr in H0,H2. rewrite H0,H2 in *.
    eauto.
  - invert H0. simpl in *.
    eapply app_no_dups_empty_args in H. invs.
    unfold eval_Zexpr_Z_total.
    simpl.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H0,H1. invs.
    pose proof (H v). pose proof (H1 v).
    pose proof (H v0). pose proof (H1 v0).
    eq_eval_Z.
    eapply eval_Zexpr_Z_eval_Zexpr in H0,H2. rewrite H0,H2 in *.
    eauto.
  - invert H0. simpl in *.
    eapply app_no_dups_empty_args in H. invs.
    unfold eval_Zexpr_Z_total.
    simpl.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H0,H1. invs.
    pose proof (H v). pose proof (H1 v).
    pose proof (H v0). pose proof (H1 v0).
    eq_eval_Z.
    eapply eval_Zexpr_Z_eval_Zexpr in H0,H2. rewrite H0,H2 in *.
    eauto.
  - invert H0. simpl in *.
    eapply app_no_dups_empty_args in H. invs.
    unfold eval_Zexpr_Z_total.
    simpl.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H0,H1. invs.
    pose proof (H v). pose proof (H1 v).
    pose proof (H v0). pose proof (H1 v0).
    eq_eval_Z.
    eapply eval_Zexpr_Z_eval_Zexpr in H0,H2. rewrite H0,H2 in *.
    eauto.
  - invert H0. simpl in *.
    eapply app_no_dups_empty_args in H. invs.
    unfold eval_Zexpr_Z_total.
    simpl.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H0,H1. invs.
    pose proof (H v). pose proof (H1 v).
    pose proof (H v0). pose proof (H1 v0).
    eq_eval_Z.
    eapply eval_Zexpr_Z_eval_Zexpr in H0,H2. rewrite H0,H2 in *.
    eauto.
  - invert H0. simpl in *.
    eapply app_no_dups_empty_args in H. invs.
    unfold eval_Zexpr_Z_total.
    simpl.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H0,H1. invs.
    pose proof (H v). pose proof (H1 v).
    pose proof (H v0). pose proof (H1 v0).
    eq_eval_Z.
    eapply eval_Zexpr_Z_eval_Zexpr in H0,H2. rewrite H0,H2 in *.
    eauto.
  - invert H0. simpl in *.
    eapply app_no_dups_empty_args in H. invs.
    unfold eval_Zexpr_Z_total.
    simpl.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H0,H1. invs.
    pose proof (H v). pose proof (H1 v).
    pose proof (H v0). pose proof (H1 v0).
    eq_eval_Z.
    eapply eval_Zexpr_Z_eval_Zexpr in H0,H2. rewrite H0,H2 in *.
    eauto.
  - invert H0. simpl in *.
    eapply app_no_dups_empty_args in H. invs.
    unfold eval_Zexpr_Z_total.
    simpl.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H0,H1. invs.
    pose proof (H v). pose proof (H1 v).
    pose proof (H v0). pose proof (H1 v0).
    eq_eval_Z.
    eapply eval_Zexpr_Z_eval_Zexpr in H0,H2. rewrite H0,H2 in *.
    eauto.
  - simpl in *. invert H.
  - simpl in *. invert H.
Qed.

Lemma eval_Zexpr_ZTimes_no_vars :
  forall esh1 z v nz,
  Forall (fun z : Zexpr => vars_of_Zexpr z = []) (z :: esh1) ->
  eval_Zexpr v (fold_left ZTimes esh1 z) nz ->
  Forall (fun x : Z => (0 <= x)%Z)
         (eval_Zexpr_Z_total $0 z :: map (eval_Zexpr_Z_total $0) esh1) ->
  nz = fold_left Z.mul
                (map Z.of_nat
                     (filter_until (map Z.to_nat
                                        (map (eval_Zexpr_Z_total $0)
                                             (z :: esh1))) 0)) 1%Z.
Proof.
  induct esh1; intros.
  - simpl in *. invert H.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H4. invs.
    pose proof (H v). pose proof (H $0). eq_eval_Z.
    eapply eval_Zexpr_Z_eval_Zexpr in H3. unfold eval_Zexpr_Z_total in *.
    rewrite H3 in *. invert H1.
    cases (Z.to_nat x). simpl. lia. 
    simpl. lia.
  - simpl in *. invert H. invert H5.
    specialize (IHesh1 (ZTimes z a)).
    unfold eval_Zexpr_Z_total in *.
    pose proof H4. pose proof H3.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H4,H3. invs.
    pose proof (H3 $0). pose proof (H5 $0).
    pose proof (H3 v). pose proof (H5 v).
    eapply eval_Zexpr_Z_eval_Zexpr in H7,H4.
    rewrite H7,H4 in *.
    simpl in *.
    rewrite H7,H4 in *.
    cases (Z.to_nat x0). simpl.
    + eapply IHesh1 in H0.
      rewrite H0.
      invert H1. invert H13.
      rewrite Z2Nat.inj_mul by lia.
      rewrite Heq. simpl. reflexivity.
      econstructor. simpl. rewrite H,H2. sets. auto.
      invert H1. invert H13. econstructor. lia. auto.
    + simpl. invert H1. invert H13.
      cases (Z.to_nat x). simpl.
      eapply IHesh1 in H0.
      rewrite H0.
      rewrite Z2Nat.inj_mul by lia.
      rewrite Heq. rewrite Heq0. simpl.
      rewrite mul_0_r. simpl. lia.
      econstructor. simpl. rewrite H,H2. sets. auto.
      econstructor. lia. eauto.
      simpl.
      eapply IHesh1 in H0.
      rewrite H0.
      rewrite Z2Nat.inj_mul by lia.
      rewrite Heq0. rewrite Heq. simpl. posnats. f_equal. lia.
      econstructor. simpl. rewrite H,H2. sets. eauto.
      econstructor. lia. auto.
Qed.

Lemma reindexer_not_empty_vars_in_index :
  forall reindexer sh,
    (forall l : list (Zexpr * Zexpr),
        vars_of_reindexer (reindexer l) =
          vars_of_reindexer (reindexer []) \cup vars_of_reindexer l)->
    vars_of_reindexer sh <> constant [] ->
    reindexer sh <> [].
Proof.
  unfold not. intros.
  specialize (H sh).
  rewrite H1 in *.
  simpl in *.
  symmetry in H.
  eapply cup_empty in H. invs.
  sets.
Qed.

Definition eval_Zexpr_Z_tup v tup :=
  (eval_Zexpr_Z v (fst tup),eval_Zexpr_Z v (snd tup)).

Definition eval_Zexpr_Z_tup_total v tup :=
  match eval_Zexpr_Z_tup v tup with
  | (Some x, Some y) => Some (x,y)
  | _ => None
  end.

Lemma map_eval_Zexpr_Z_tup_total_ZLit : forall args2 sh,
    length args2 = length sh ->
    map (eval_Zexpr_Z_tup_total $0)
        (combine (map ZLit args2) (map ZLit sh)) =
      map Some (combine args2 sh).
Proof.
  induction args2; intros; cases sh; simpl in *; try lia; auto.
  unfold eval_Zexpr_Z_tup_total at 1.
  unfold eval_Zexpr_Z_tup at 1. simpl. f_equal. eapply IHargs2. lia.
Qed.

Fixpoint no_bounds (e : Zexpr) : Prop :=
  match e with
  | ZPlus x y => no_bounds x /\ no_bounds y
  | ZMinus x y => no_bounds x /\ no_bounds y
  | ZTimes x y => no_bounds x /\ no_bounds y
  | ZDivf x y => no_bounds x /\ no_bounds y
  | ZDivc x y => no_bounds x /\ no_bounds y
  | ZMod x y => no_bounds x /\ no_bounds y
  | ZLit _ => True
  | ZVar _ => True
  end.

Lemma fst_fold_left_subst_var_in_Z_tup :
  forall l z z0,
  fst
    (fold_left
       (fun (z3 : Zexpr * Zexpr) (tup : var * Z) =>
          subst_var_in_Z_tup (fst tup) (snd tup) z3) l (z, z0)) =
    fold_left
      (fun (z3 : Zexpr) (tup : var * Z) =>
         subst_var_in_Zexpr (fst tup) (snd tup) z3) l z.
Proof.
  induct l; intros. auto.
  simpl. cases a. simpl.
  unfold subst_var_in_Z_tup at 2. simpl. apply IHl.
Qed.

Lemma snd_fold_left_subst_var_in_Z_tup :
  forall l z z0,
    snd
    (fold_left
       (fun (z3 : Zexpr * Zexpr) (tup : var * Z) =>
          subst_var_in_Z_tup (fst tup) (snd tup) z3) l (z, z0)) =
    fold_left
      (fun (z3 : Zexpr) (tup : var * Z) =>
         subst_var_in_Zexpr (fst tup) (snd tup) z3) l z0.
Proof.
  induct l; intros. auto.
  simpl. cases a. simpl.
  unfold subst_var_in_Z_tup at 2. simpl. apply IHl.
Qed.

Fixpoint dedup {X} (l : list (var * X)) :=
  match l with
  | [] => []
  | (var,val)::ls => if in_bool (map fst ls) var
                     then dedup ls
                     else (var,val)::(dedup ls)
  end.

Lemma eval_Zexpr_Z_partially_eval_Zexpr :
  forall e v,
    eval_Zexpr_Z $0 (partially_eval_Zexpr v e) =
      eval_Zexpr_Z v e.
Proof.
  induct e; intros; simpl in *; try rewrite IHe1; try rewrite IHe2;
    try rewrite IHe3; eauto.
  cases (v $? x); simpl; eauto. apply lookup_empty.
Qed.

Lemma eq_zexpr_fold_left_subst_var_in_Zexpr :
  forall x x0 z1 z2 ,
  eq_zexpr z1 z2 ->
  eq_zexpr 
    (fold_left
       (fun (z3 : Zexpr) (tup : var * Z) =>
          subst_var_in_Zexpr (fst tup) (snd tup) z3) (combine x x0) z1)
    (fold_left
       (fun (z3 : Zexpr) (tup : var * Z) =>
          subst_var_in_Zexpr (fst tup) (snd tup) z3) (combine x x0) z2).
Proof.
  induct x; intros.
  - simpl. auto.
  - simpl. cases x0; auto.
    simpl.
    eapply IHx.
    eapply eq_zexpr_subst_var_in_Zexpr. auto.
Qed.

Lemma eq_zexpr_fold_left_subst_var_in_Z_tup :
  forall x x0 z1 z2 ,
  eq_Z_tup z1 z2 ->
  eq_Z_tup
    (fold_left
       (fun (z3 : Zexpr * Zexpr) (tup : var * Z) =>
          subst_var_in_Z_tup (fst tup) (snd tup) z3) (combine x x0) z1)
    (fold_left
       (fun (z3 : Zexpr * Zexpr) (tup : var * Z) =>
          subst_var_in_Z_tup (fst tup) (snd tup) z3) (combine x x0) z2).
Proof.
  intros. cases z1. cases z2. invert H. simpl in *.
  induct x; intros.
  - simpl. unfold eq_Z_tup. simpl. propositional.
  - simpl. cases x0; simpl; auto.
    unfold eq_Z_tup. simpl. propositional.
    eapply IHx.
    eapply eq_zexpr_subst_var_in_Zexpr. auto.
    simpl.
    eapply eq_zexpr_subst_var_in_Zexpr. auto.
Qed.

Lemma eval_Zexpr_Z_subst_var_in_Zexpr : forall e v i k,
    eval_Zexpr_Z (v $+ (i,k)) e =
    eval_Zexpr_Z v (subst_var_in_Zexpr i k e).
Proof.
  induct e; intros; simpl in *;
    try cases (eval_Zexpr_Z (v $+ (i, k)) e1);
    try cases (eval_Zexpr_Z (v $+ (i, k)) e2);
    try erewrite IHe1,IHe2 in *;
    try rewrite Heq0,Heq; eauto.
  cases (x ==v i); try rewrite lookup_add_eq by auto;
    try rewrite lookup_add_ne by auto; eauto.
Qed.

Lemma eval_Zexpr_Z_partially_eval_Zexpr_join :
  forall a0 v v0,
  eval_Zexpr_Z v0 (partially_eval_Zexpr v a0) =
    eval_Zexpr_Z (v $++ v0) a0.
Proof.
  induct a0; intros; simpl in *;
    try rewrite IHa0_1; try rewrite IHa0_2; try rewrite IHa0_3; auto.
  cases (v $? x). simpl. rewrite lookup_join1. auto.
  eapply lookup_Some_dom. eauto.
  simpl. rewrite lookup_join2. auto. eapply lookup_None_dom. auto.
Qed.

Lemma eval_Zexpr_Z_tup_total_partially_eval_Z_tup :
  forall a v,
    eval_Zexpr_Z_tup_total $0 (partially_eval_Z_tup v a) =
      eval_Zexpr_Z_tup_total v a.
Proof.
  unfold eval_Zexpr_Z_tup_total. unfold partially_eval_Z_tup.
  intros. cases a. simpl.
  repeat rewrite eval_Zexpr_Z_partially_eval_Zexpr.
  reflexivity.
Qed.

Lemma map_eval_Zexpr_Z_tup_total_map_partially_eval_Z_tup :
  forall l v,
  map (eval_Zexpr_Z_tup_total $0)
      (map (partially_eval_Z_tup v) l) = map (eval_Zexpr_Z_tup_total v) l.
Proof.  
  induct l; intros.
  - reflexivity.
  - simpl. f_equal.
    repeat rewrite eval_Zexpr_Z_tup_total_partially_eval_Z_tup. auto.
    eauto.
Qed.

Lemma map_eval_Zexpr_Z_tup_total_map_fold_left_subst_var_in_Z_tup :
  forall index1 index2 x x0,
    eq_Z_tuple_index_list index1 index2 ->
    map (eval_Zexpr_Z_tup_total $0)
        (map
           (fun tup : Zexpr * Zexpr =>
              (fold_left
                 (fun (z5 : Zexpr * Zexpr) (tup0 : var * Z) =>
                    subst_var_in_Z_tup (fst tup0) (snd tup0) z5) 
                 (combine x x0) tup)) index1) =
      map (eval_Zexpr_Z_tup_total $0)
          (map
             (fun tup : Zexpr * Zexpr =>
                (fold_left
                   (fun (z5 : Zexpr * Zexpr) (tup0 : var * Z) =>
                      subst_var_in_Z_tup (fst tup0) (snd tup0) z5) 
                   (combine x x0) tup)) index2). 
Proof.
  intros.
  induct index1; cases index2.
  - reflexivity.
  - invert H. simpl in *. lia.
  - invert H. simpl in *. lia.
  - repeat rewrite map_cons.
    f_equal.
    2: { eapply IHindex1. 
         eapply eq_Z_tuple_index_list_cons in H. propositional. }
    eapply eq_Z_tuple_index_list_cons in H. invs.
    unfold eval_Zexpr_Z_tup_total.
    eq_match_discriminee.
    cases a. cases p. simpl in *.
    eapply (eq_zexpr_fold_left_subst_var_in_Z_tup x x0) in H0.   
    unfold eval_Zexpr_Z_tup. simpl.
    unfold eq_Z_tup in H0. invs.
    repeat rewrite fst_fold_left_subst_var_in_Z_tup in *.
    repeat rewrite snd_fold_left_subst_var_in_Z_tup in *.
    f_equal; eapply eq_eval_Zexpr_Z; eauto.
Qed.

Lemma map_partially_eval_Z_tup_combine_ZLit :
  forall v idx sh,
  (map (partially_eval_Z_tup v)
       (combine (map ZLit idx) (map ZLit sh))) =
    (combine (map ZLit idx) (map ZLit sh)).
Proof.
  induct idx; intros.
  - simpl. reflexivity.
  - simpl. cases sh.
    + simpl. reflexivity.
    + simpl. unfold partially_eval_Z_tup at 1. simpl. f_equal. eauto.
Qed.

Lemma map_eval_Zexpr_Z_tup_total_map_subst_var_in_Z_tup :
  forall v i loz l,
    (map (eval_Zexpr_Z_tup_total (v $+ (i, loz))) l) =
      map (eval_Zexpr_Z_tup_total v) (map (subst_var_in_Z_tup i loz) l).
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. f_equal; auto.
    unfold eval_Zexpr_Z_tup_total.
    cases a. simpl.
    repeat rewrite eval_Zexpr_Z_subst_var_in_Zexpr. reflexivity.
Qed.

Lemma map_partially_eval_Z_tup_map_subst_var_in_Z_tup_comm :
  forall v l i k,
    ~ i \in dom v ->
            (map (subst_var_in_Z_tup i k)
                 (map (partially_eval_Z_tup v) l)) =
              map (partially_eval_Z_tup v)
                  (map (subst_var_in_Z_tup i k) l) .
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. f_equal; auto.
    rewrite subst_var_in_Z_tup_partially_eval_Z_tup_comm by auto.
    reflexivity.
Qed.

Lemma eval_Zexpr_Z_tup_partially_eval_Z_tup :
  forall a v,
    eval_Zexpr_Z_tup $0 (partially_eval_Z_tup v a) =
      eval_Zexpr_Z_tup v a.
Proof.
  intros. cases a. simpl. unfold partially_eval_Z_tup.
  unfold eval_Zexpr_Z_tup. simpl.
  repeat rewrite eval_Zexpr_Z_partially_eval_Zexpr.
  reflexivity.
Qed.

Lemma eval_Zexpr_Z_total_ceil_div_distr : forall x y v,
    eq_zexpr x (| eval_Zexpr_Z_total v x|)%z ->
    eq_zexpr y (| eval_Zexpr_Z_total v y|)%z ->
    eval_Zexpr_Z_total v (x // y)%z =
      (eval_Zexpr_Z_total v x // (eval_Zexpr_Z_total v y))%Z.
Proof.
  unfold eval_Zexpr_Z_total. intros. simpl.
  cases (eval_Zexpr_Z v x); cases (eval_Zexpr_Z v y); auto.
  invert H0.
  assert (eval_Zexpr v y 0%Z).
  eapply H1. eauto. eapply eval_Zexpr_Z_eval_Zexpr in H0.
  rewrite H0 in *. discriminate.
  assert (eval_Zexpr v x 0%Z).
  eapply H. eauto. eapply eval_Zexpr_Z_eval_Zexpr in H1.
  rewrite H1 in *. discriminate.
Qed.

Lemma eval_Zexpr_Z_total_sub_distr : forall x y v,
    eq_zexpr x (| eval_Zexpr_Z_total v x|)%z ->
    eq_zexpr y (| eval_Zexpr_Z_total v y|)%z ->
    eval_Zexpr_Z_total v (x - y)%z =
      (eval_Zexpr_Z_total v x - eval_Zexpr_Z_total v y)%Z.
Proof.
  unfold eval_Zexpr_Z_total. intros. simpl.
  cases (eval_Zexpr_Z v x); cases (eval_Zexpr_Z v y); auto.
  invert H0.
  assert (eval_Zexpr v y 0%Z).
  eapply H1. eauto. eapply eval_Zexpr_Z_eval_Zexpr in H0.
  rewrite H0 in *. discriminate.
  assert (eval_Zexpr v x 0%Z).
  eapply H. eauto. eapply eval_Zexpr_Z_eval_Zexpr in H1.
  rewrite H1 in *. discriminate.
Qed.

Lemma eval_Zexpr_Z_total_mul_distr : forall x y v,
    eq_zexpr x (| eval_Zexpr_Z_total v x|)%z ->
    eq_zexpr y (| eval_Zexpr_Z_total v y|)%z ->
    eval_Zexpr_Z_total v (x * y)%z =
      (eval_Zexpr_Z_total v x * eval_Zexpr_Z_total v y)%Z.
Proof.
  unfold eval_Zexpr_Z_total. intros. simpl.
  cases (eval_Zexpr_Z v x); cases (eval_Zexpr_Z v y); auto.
  invert H0.
  assert (eval_Zexpr v y 0%Z).
  eapply H1. eauto. eapply eval_Zexpr_Z_eval_Zexpr in H0.
  rewrite H0 in *. discriminate.
Qed.

Lemma eval_Zexpr_Z_total_add_distr : forall x y v,
    eq_zexpr x (| eval_Zexpr_Z_total v x|)%z ->
    eq_zexpr y (| eval_Zexpr_Z_total v y|)%z ->
    eval_Zexpr_Z_total v (x + y)%z =
      (eval_Zexpr_Z_total v x + eval_Zexpr_Z_total v y)%Z.
Proof.
  unfold eval_Zexpr_Z_total. intros. simpl.
  cases (eval_Zexpr_Z v x); cases (eval_Zexpr_Z v y); auto.
  invert H0.
  assert (eval_Zexpr v y 0%Z).
  eapply H1. eauto. eapply eval_Zexpr_Z_eval_Zexpr in H0.
  rewrite H0 in *. discriminate.
  assert (eval_Zexpr v x 0%Z).
  eapply H. eauto. eapply eval_Zexpr_Z_eval_Zexpr in H1.
  rewrite H1 in *. discriminate.
Qed.

Lemma fst_partially_eval_Z_tup : forall v t,
    fst (partially_eval_Z_tup v t) = partially_eval_Zexpr v (fst t).
Proof.
  intros. unfold partially_eval_Z_tup. reflexivity.
Qed.

Lemma map_fst_map_partially_eval_Z_tup : forall v l,
    map fst (map (partially_eval_Z_tup v) l) =
      map (partially_eval_Zexpr v) (map fst l).
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Lemma snd_partially_eval_Z_tup : forall v t,
    snd (partially_eval_Z_tup v t) = partially_eval_Zexpr v (snd t).
Proof.
  intros. unfold partially_eval_Z_tup. reflexivity.
Qed.

Lemma map_snd_map_partially_eval_Z_tup : forall v l,
    map snd (map (partially_eval_Z_tup v) l) =
      map (partially_eval_Zexpr v) (map snd l).
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Lemma join_empty_r {X} : forall (v : fmap var X),
    v $++ $0 = v.
Proof.
  intros. eapply fmap_ext. intros.
  cases (v $? k).
  rewrite lookup_join1. auto.
  eapply lookup_Some_dom in Heq. sets.
  rewrite lookup_join2. rewrite lookup_empty. auto.
  eapply lookup_None_dom. sets.
Qed.

Lemma eval_Zexpr_partially_eval_Zexpr : forall e v x,
    eval_Zexpr $0 (partially_eval_Zexpr v e) x <->
      eval_Zexpr v e x.
Proof.
  induct e; propositional; simpl in *; try invert1 H.
  - econstructor; try eapply IHe1; try eapply IHe2; eauto.
  - econstructor; try eapply IHe1; try eapply IHe2; eauto.
  - econstructor; try eapply IHe1; try eapply IHe2; eauto.
  - econstructor; try eapply IHe1; try eapply IHe2; eauto.
  - econstructor; try eapply IHe1; try eapply IHe2; eauto.
  - econstructor; try eapply IHe1; try eapply IHe2; eauto.
  - econstructor; try eapply IHe1; try eapply IHe2; eauto.
  - econstructor; try eapply IHe1; try eapply IHe2; eauto.
  - econstructor; try eapply IHe1; try eapply IHe2; eauto.
  - econstructor; try eapply IHe1; try eapply IHe2; eauto.
  - econstructor; try eapply IHe1; try eapply IHe2; eauto.
  - econstructor; try eapply IHe1; try eapply IHe2; eauto.
  - econstructor.
  - econstructor.
  - econstructor.
    cases (v $? x); auto. invert H. auto.
    invert H. rewrite lookup_empty in *. discriminate.
  - rewrite H1. econstructor.
Qed.
    
Lemma eval_Zexprlist_map_match_snd_map_eval_Zexpr_Z_tup_total :
  forall v l,
  eval_Zexprlist $0 (map (partially_eval_Zexpr v) (map snd l))
         (map (eval_Zexpr_Z_total v) (map snd l)) ->
  eval_Zexprlist $0 (map (partially_eval_Zexpr v) (map fst l))
         (map (eval_Zexpr_Z_total v) (map fst l)) ->
       (map
           (fun o : option (Z * Z) =>
            match o with
            | Some x => snd x
            | None => 0%Z
            end) (map (eval_Zexpr_Z_tup_total v) l)) =
         (map (eval_Zexpr_Z_total v) (map snd l)).
Proof.
  induct l; intros.
  - reflexivity.
  - simpl in *. invert H. invert H0. 
    cases a. simpl in *.
    unfold eval_Zexpr_Z_tup_total. unfold eval_Zexpr_Z_tup. simpl.
    erewrite -> eval_Zexpr_partially_eval_Zexpr in H5,H4.
    eapply eval_Zexpr_Z_eval_Zexpr in H5,H4.
    rewrite H5,H4. simpl. f_equal.
    eapply IHl. eauto. eauto.
Qed.

Lemma eval_Zexprlist_map_match_fst_map_eval_Zexpr_Z_tup_total :
  forall v l,
  eval_Zexprlist $0 (map (partially_eval_Zexpr v) (map snd l))
         (map (eval_Zexpr_Z_total v) (map snd l)) ->
  eval_Zexprlist $0 (map (partially_eval_Zexpr v) (map fst l))
         (map (eval_Zexpr_Z_total v) (map fst l)) ->
       (map
           (fun o : option (Z * Z) =>
            match o with
            | Some x => fst x
            | None => 0%Z
            end) (map (eval_Zexpr_Z_tup_total v) l)) =
         (map (eval_Zexpr_Z_total v) (map fst l)).
Proof.
  induct l; intros.
  - reflexivity.
  - simpl in *. invert H. invert H0. 
    cases a. simpl in *.
    unfold eval_Zexpr_Z_tup_total. unfold eval_Zexpr_Z_tup. simpl.
    erewrite -> eval_Zexpr_partially_eval_Zexpr in H5,H4.
    eapply eval_Zexpr_Z_eval_Zexpr in H5,H4.
    rewrite H5,H4. simpl. f_equal.
    eapply IHl. eauto. eauto.
Qed.

Lemma eval_Zexprlist_map_partially_eval_Zexpr :
  forall l lz v,
    eval_Zexprlist $0 (map (partially_eval_Zexpr v) l) lz <->
      eval_Zexprlist v l lz.
Proof.
  induct l; propositional; simpl in *.
  - invert H. econstructor.
  - invert H. econstructor.
  - invert H. econstructor.
    eapply eval_Zexpr_partially_eval_Zexpr; eauto.
    eapply IHl. eauto.
  - invert H. econstructor.
    eapply eval_Zexpr_partially_eval_Zexpr; eauto.
    eapply IHl. eauto.
Qed.

Lemma eval_Zexpr_Z_total_partially_eval_Zexpr_join : forall v1 v2 e,
    eval_Zexpr_Z_total v1 (partially_eval_Zexpr v2 e) =
      eval_Zexpr_Z_total (v2 $++ v1) e.
Proof.
  unfold eval_Zexpr_Z_total.
  intros.
  rewrite eval_Zexpr_Z_partially_eval_Zexpr_join. auto.
Qed.

Lemma map_eval_Zexpr_Z_total_map_partially_eval_Zexpr_join :
  forall v1 v2 l,
    map (eval_Zexpr_Z_total v1) (map (partially_eval_Zexpr v2) l) =
      map (eval_Zexpr_Z_total (v2 $++ v1)) l.
Proof.
  induct l; intros.
  - reflexivity.
  - simpl. rewrite eval_Zexpr_Z_total_partially_eval_Zexpr_join.
    f_equal. eauto.
Qed.

Lemma vars_of_Zexpr_subseteq_partially_eval_Zexpr : forall a0 v,
    constant (vars_of_Zexpr a0) \subseteq dom v ->
    vars_of_Zexpr (partially_eval_Zexpr v a0) = [].
Proof.
  induct a0; intros; simpl in *; try rewrite constant_app_no_dups in *;
    try erewrite IHa0_1 by sets; try erewrite IHa0_2 by sets; auto.
  cases (v $? x).
  reflexivity. eapply lookup_None_dom in Heq.
  simpl. exfalso. apply Heq. sets.
Qed.

Lemma vars_of_reindexer_subseteq_map_partially_eval_Z_tup : forall l v,
    vars_of_reindexer l \subseteq dom v ->
    Forall (fun x => vars_of_Zexpr x = [])
           (map fst (map (partially_eval_Z_tup v) l)) /\
      Forall (fun x => vars_of_Zexpr x = [])
             (map snd (map (partially_eval_Z_tup v) l)).
Proof.
  induct l; propositional.
  - econstructor.
  - econstructor.
  - simpl. econstructor.
    simpl in H.
    assert (constant (vars_of_Zexpr a0) \subseteq dom v) by sets.
    eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.
    auto.
    simpl in H.
    apply IHl. sets.
  - simpl. econstructor.
    simpl in H.
    assert (constant (vars_of_Zexpr a0) \subseteq dom v) by sets.
    eapply vars_of_Zexpr_subseteq_partially_eval_Zexpr.
    auto.
    simpl in H.
    apply IHl. sets.
Qed.

Lemma forall_map_pad_in_bound : forall sh0,
  Forall
    (fun tup : Z * Z * Z =>
     let (y, dim) := tup in let (l, r) := y in (l + r <= dim)%Z)
    (combine (map (fun x => (eval_Zexpr_Z_total $0 x, 0%Z)) sh0)
             (map Z.of_nat
                  (filter_until
                     (map Z.to_nat (map (eval_Zexpr_Z_total $0) sh0)) 0))).
Proof.
  induct sh0; simpl.
  econstructor.
  cases (Z.to_nat (eval_Zexpr_Z_total $0 a)).
  - simpl in *. econstructor. lia.
    rewrite combine_nil. eauto.
  - simpl. econstructor. lia.
    eauto.
Qed.

