From Coq Require Import Bool.Bool.
From Coq Require Import ZArith.Zdiv.
From Coq Require Import ZArith.Int.
From Coq Require Import ZArith.Znat.

Set Warnings "-deprecate-hint-without-locality,-deprecated".
From ATL Require Import FrapWithoutSets.
From Lower Require Import Zexpr.

Open Scope string_scope.

Inductive Bexpr :=
| And (a b : Bexpr)
| Lt (a b : Zexpr)
| Le (a b : Zexpr)
| Eq (a b : Zexpr).

Inductive eval_Bexpr (v : valuation) : Bexpr -> bool -> Prop :=
| EvalAnd : forall b1 b2 b1b b2b,
    eval_Bexpr v b1 b1b ->
    eval_Bexpr v b2 b2b ->
    eval_Bexpr v (And b1 b2) (b1b && b2b)
| EvalLt : forall x y xz yz,
    eval_Zexpr v x xz ->
    eval_Zexpr v y yz ->
    eval_Bexpr v (Lt x y) (xz <? yz)%Z
| EvalLe : forall x y xz yz,
    eval_Zexpr v x xz ->
    eval_Zexpr v y yz ->
    eval_Bexpr v (Le x y) (xz <=? yz)%Z
| EvalEq : forall x y xz yz,
    eval_Zexpr v x xz ->
    eval_Zexpr v y yz ->
    eval_Bexpr v (Eq x y) (xz =? yz)%Z.

Ltac invsB :=
  repeat
    match goal with
    | H : eval_Bexpr _ (And _ _) _ |- _ => invert H
    | H : eval_Bexpr _ (Lt _ _) _ |- _ => invert H
    | H : eval_Bexpr _ (Le _ _) _ |- _ => invert H
    | H : eval_Bexpr _ (Eq _ _) _ |- _ => invert H
  end.

Lemma eval_Bexpr_deterministic : forall v b b1 b2,
    eval_Bexpr v b b1 ->
    eval_Bexpr v b b2 ->
    b1 = b2.
Proof.
  induction b; intros; invsB; eq_eval_Z; f_equal; eauto.
Qed.

Ltac eq_eval_B :=
  repeat
    match goal with
    | H1 : eval_Bexpr ?v ?e ?a, H2 : eval_Bexpr ?v ?e ?b |- _ =>
      pose proof (eval_Bexpr_deterministic _ _ _ _ H1 H2); subst;
      clear H2
  end.
