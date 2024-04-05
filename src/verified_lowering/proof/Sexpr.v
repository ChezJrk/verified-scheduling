From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import ZArith.Zdiv.
From Coq Require Import ZArith.Int.
From Coq Require Import ZArith.Znat.
From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import Reals.Rpower.

Require Import Coq.Logic.FunctionalExtensionality.
From Coq Require Import Reals.Reals. Import Rdefinitions. Import RIneq.

Set Warnings "-deprecate-hint-without-locality,-deprecated".
Import ListNotations.

From ATL Require Import FrapWithoutSets Div Tactics.
From Lower Require Import Array Zexpr Result.

Definition context := fmap string (list Zexpr).
Definition expr_context := fmap string result.
Definition stack := fmap string R.

Inductive Sexpr :=
| Var (v : string)
| Get (v : string) (i : list Zexpr)
| Mul (x y : Sexpr)
| Add (x y : Sexpr)
| Div (x y : Sexpr)
| Sub (x y : Sexpr)
| Lit (r : R).

Inductive Sstmt :=
| SVar (v : string)
| SGet (v : string) (i : list (Zexpr * Zexpr))
| SMul (x y : Sstmt)
| SAdd (x y : Sstmt)
| SDiv (x y : Sstmt)
| SSub (x y : Sstmt)
| SLit (r : R).

Fixpoint lowerS (s : Sexpr) (sh : context) : Sstmt :=
  match s with
  | Lit r => SLit r
  | Var v => SVar v
  | Get v i =>
    match sh $? v with
    | Some str => SGet v (List.combine str i)
    | None => SVar v
    end    
  | Mul x y => SMul (lowerS x sh) (lowerS y sh)
  | Add x y => SAdd (lowerS x sh) (lowerS y sh)
  | Div x y => SDiv (lowerS x sh) (lowerS y sh)
  | Sub x y => SSub (lowerS x sh) (lowerS y sh)
  end.

Inductive eval_get (v : valuation) :
  list result -> list Zexpr -> scalar_result -> Prop :=
| EvalGetV : forall x xs i l l' r,
    eval_Zexpr v x i ->
    (0 <= i)%Z ->
    nth_error l (Z.to_nat i) = Some (V l') ->
    eval_get v l' xs r ->
    eval_get v l (x::xs) r
| EvalGetS : forall x i l r,
    eval_Zexpr v x i ->
    (0 <= i)%Z ->
    nth_error l (Z.to_nat i) = Some (S r) ->
    eval_get v l [x] r
.

Definition bin_scalar_result f r1 r2 :=
  match r1,r2 with
  | SS s1,SS s2 => SS (f s1 s2)
  | SX,SS s2 => SS (f 0%R s2)
  | SS s1,SX => SS (f s1 0%R)
  | SX,SX => SS (f 0%R 0%R)
  end.

Inductive eval_Sexpr (sh : context) :
  valuation -> expr_context -> Sexpr -> scalar_result -> Prop :=
| EvalVar : forall s v ec r,
    ec $? s = Some (S r) ->
    sh $? s = Some [] ->
    eval_Sexpr sh v ec (Var s) (match r with
                                | SS s => r
                                | _  => SS 0%R
                                end)
| EvalGet : forall x l v r ec rs s,
    ec $? x = Some (V rs) ->
    sh $? x = Some s ->
    length s = length l ->
    eval_get v rs l r ->
    eval_Sexpr sh v ec (Get x l) (match r with
                                | SS s => r
                                | _  => SS 0%R
                                end)
| EvalMul : forall ec s1 s2 v r1 r2,
    eval_Sexpr sh v ec s1 r1 ->
    eval_Sexpr sh v ec s2 r2 ->
    eval_Sexpr sh v ec (Mul s1 s2) (bin_scalar_result Rmult r1 r2)
| EvalAdd : forall ec s1 s2 v r1 r2,
    eval_Sexpr sh v ec s1 r1 ->
    eval_Sexpr sh v ec s2 r2 ->
    eval_Sexpr sh v ec (Add s1 s2) (bin_scalar_result Rplus r1 r2)
| EvalDiv : forall ec s1 s2 v r1 r2,
    eval_Sexpr sh v ec s1 r1 ->
    eval_Sexpr sh v ec s2 r2 ->
    match r2 with
    | SS s => s
    | SX => 0%R
    end <> 0%R ->
    eval_Sexpr sh v ec (Div s1 s2) (bin_scalar_result Rdiv r1 r2)
| EvalSub : forall ec s1 s2 v r1 r2,
    eval_Sexpr sh v ec s1 r1 ->
    eval_Sexpr sh v ec s2 r2 ->       
    eval_Sexpr sh v ec (Sub s1 s2) (bin_scalar_result Rminus r1 r2)
|EvalLit : forall v ec r,
    eval_Sexpr sh v ec (Lit r) (SS r).

Inductive eval_Sstmt :
  valuation -> stack -> heap -> Sstmt -> R -> Prop :=
| EvalSVar : forall v st h x r,
    st $? x = Some r ->
    eval_Sstmt v st h (SVar x) r
| EvalSGet : forall v st h x l r i tups,
    h $? x = Some l ->
    eval_Zexpr v (flatten_shape_index (map fst tups) (map snd tups)) i ->
    (0 <= i)%Z ->
    l $? i = Some r ->
    eval_Sstmt v st h (SGet x tups) r
| EvalSMul : forall v st h s1 s2 r1 r2 r,
    eval_Sstmt v st h s1 r1 ->
    eval_Sstmt v st h s2 r2 ->
    (r1 * r2 = r)%R ->
    eval_Sstmt v st h (SMul s1 s2) r
| EvalSAdd: forall v st h s1 s2 r1 r2 r,
    eval_Sstmt v st h s1 r1 ->
    eval_Sstmt v st h s2 r2 ->
    (r1 + r2 = r)%R ->
    eval_Sstmt v st h (SAdd s1 s2) r
| EvalSDiv: forall v st h s1 s2 r1 r2 r,
    eval_Sstmt v st h s1 r1 ->
    eval_Sstmt v st h s2 r2 ->
    (r1 / r2 = r)%R ->
    eval_Sstmt v st h (SDiv s1 s2) r
| EvalSSub: forall v st h s1 s2 r1 r2 r,
    eval_Sstmt v st h s1 r1 ->
    eval_Sstmt v st h s2 r2 ->
    (r1 - r2 = r)%R ->
    eval_Sstmt v st h (SSub s1 s2) r
| EvalSLit: forall v st h r,
    eval_Sstmt v st h (SLit r) r.

