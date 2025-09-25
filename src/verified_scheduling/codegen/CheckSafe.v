From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import micromega.Zify.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Zdiv.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.

Set Warnings "-omega-is-deprecated,-deprecated".

Import ListNotations.

From ATL Require Import ATL Tactics Div Common CommonTactics.
From Examples Require Import Blur. 

Generalizable All Variables.
(*
Inductive safe {X} `{TensorElem X} : X -> Prop :=
| acc : forall v i,
    safe' v ->
    safe (v _[i])
with
  safe' {X} `{TensorElem X} : list X -> Prop :=
| gen' : forall n f,
    (forall x, 0 <= x < Z.of_nat n -> safe (f x))%Z ->
    safe' (GEN [ i < Z.of_nat n ] f i)
| acc' : forall v i,
    safe' v ->
    safe' (v _[i]).
 *)
Ltac safe :=
  lazymatch goal with
  | |- let_binding ?x ?f = _ =>
    let tx := type of x in
    let ex := fresh "ex" in
    let Hx := fresh "Hx" in
    (evar (ex : tx);
    assert (x = ?ex) as Hx by
          (safe; reflexivity));
    eapply let_extensionality;
    [ subst; consistent_shape; try reflexivity; eauto with crunch
    | intros; safe ]
  | |- flatten _ = _ =>
    apply flatten_eq; safe
  | |- transpose _ = _ =>
    apply transpose_eq; safe
  | |- tile _ _ = _ =>
    apply tile_eq; safe
  | |- flatten_trunc _ _ = _ =>
    apply flatten_trunc_eq; safe
  | |- gen _ _ = _ =>
    apply gen_eq_bound; intros; safe
  | |- sum _ _ = _ =>
    apply sum_eq_bound; intros; safe
  | |- (_ * _)%R = _ =>
    idtac
  | |- (?a <+> ?b) = _ =>
    let t := type of a in
    let ae := fresh "ae" in
    let be := fresh "be" in
    evar (ae : t);
    assert (a = ?ae) by (safe; try reflexivity);
    evar (be : t);
    assert (b = ?be) by (safe; try reflexivity);
    reflexivity
  | |- (|[ _ ]| _) = _ =>
     eapply iverson_in; propnorm; unbool_hyp;
     autorewrite with crunch;
     first
     [ safe |
       subst; consistent_shape; eauto with crunch ]
  | |- get ?v ?i = _ =>
    assert (0 <= i)%Z by eauto with crunch;
    let t := type of v in
    let vsh := fresh "vsh" in
    let Hvsh := fresh "Hvsh" in
    evar (vsh : (@shape t _));
    assert (consistent v ?vsh) as Hvsh by
          (consistent_shape; subst; eauto with crunch);
    let cvsh := type of Hvsh in
    let n :=
        match cvsh with
        | consistent _ (?n,_) => n
        end in
    assert (i < Z.of_nat n)%Z by eauto with crunch; 
    apply get_eq_index;
    safe
  | |- _ = _ =>
    idtac
  end
.

Ltac check_safe := etransitivity; [ safe; try reflexivity | eauto ]; lazy beta.

Goal forall X (H : TensorElem X) N M (v : list (list R)) s,
    0 < N ->
    0 < M ->
    consistent v (N,(M,s)) ->
    blur_tiles_guarded v N M 4 4 = @nil _.
Proof.
  intros. autounfold with examples.
  check_safe.
Abort.
