From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Coq Require Import ZArith.Zdiv.
From Coq Require Import ZArith.Int.
From Coq Require Import ZArith.Znat.
From Coq Require Import Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import Reals.Rpower.

Import ListNotations.

Set Warnings "-omega-is-deprecated,-deprecated".

From ATL Require Import Div ATL.
From Examples Require Import Blur TensorAdd Im2col Convolution GatherScatter
  Matmul.
From Codegen Require Import IdentParsing NatToString IntToString Normalize.
From Lower Require Import ATLDeep Sexpr Zexpr Bexpr.
From Inferpad Require Import Reify.

Open Scope string_scope.
Hint Extern 6 (_ < _)%Z => lia : crunch.
Hint Extern 6 (_ < _) => lia : crunch.
Hint Extern 6 (_ <= _) => lia : crunch.
Hint Extern 6 (_ <= _)%Z => lia : crunch.
Hint Extern 6 (_ = _) => lia : crunch.
Hint Extern 6 (_ = _)%Z => lia : crunch.

Fixpoint count_gen e : nat :=
  match e with
  | Gen i lo hi body => S (count_gen body)
  | Sum i lo hi body => count_gen body
  | Guard b e' => count_gen e'
  | Lbind x e1 e2 => count_gen e1 + count_gen e2
  | Concat e1 e2 => count_gen e1 + count_gen e2
  | Flatten e' => count_gen e'
  | Split k e' => count_gen e'
  | Transpose e' => count_gen e'
  | Truncr k e' => count_gen e'
  | Truncl k e' => count_gen e'
  | Padr k e' => count_gen e'
  | Padl k e' => count_gen e'
  | Scalar _ => 0
  end.

Fixpoint count_concat e : nat :=
  match e with
  | Gen i lo hi body => count_concat body
  | Sum i lo hi body => count_concat body
  | Guard b e' => count_concat e'
  | Lbind x e1 e2 => count_concat e1 + count_concat e2
  | Concat e1 e2 => S (count_concat e1 + count_concat e2)
  | Flatten e' => count_concat e'
  | Split k e' => count_concat e'
  | Transpose e' => count_concat e'
  | Truncr k e' => count_concat e'
  | Truncl k e' => count_concat e'
  | Padr k e' => count_concat e'
  | Padl k e' => count_concat e'
  | Scalar _ => 0
  end.

Fixpoint count_truncate e : nat :=
  match e with
  | Gen i lo hi body => count_truncate body
  | Sum i lo hi body => count_truncate body
  | Guard b e' => count_truncate e'
  | Lbind x e1 e2 => count_truncate e1 + count_truncate e2
  | Concat e1 e2 => count_truncate e1 + count_truncate e2
  | Flatten e' => count_truncate e'
  | Split k e' => count_truncate e'
  | Transpose e' => count_truncate e'
  | Truncr k e' => S (count_truncate e')
  | Truncl k e' => S (count_truncate e')
  | Padr k e' => count_truncate e'
  | Padl k e' => count_truncate e'
  | Scalar _ => 0
  end.

Fixpoint count_transpose e : nat :=
  match e with
  | Gen i lo hi body => count_transpose body
  | Sum i lo hi body => count_transpose body
  | Guard b e' => count_transpose e'
  | Lbind x e1 e2 => count_transpose e1 + count_transpose e2
  | Concat e1 e2 => count_transpose e1 + count_transpose e2
  | Flatten e' => count_transpose e'
  | Split k e' => count_transpose e'
  | Transpose e' => S (count_transpose e')
  | Truncr k e' => count_transpose e'
  | Truncl k e' => count_transpose e'
  | Padr k e' => count_transpose e'
  | Padl k e' => count_transpose e'
  | Scalar _ => 0
  end.

Fixpoint count_flatten e : nat :=
  match e with
  | Gen i lo hi body => count_flatten body
  | Sum i lo hi body => count_flatten body
  | Guard b e' => count_flatten e'
  | Lbind x e1 e2 => count_flatten e1 + count_flatten e2
  | Concat e1 e2 => count_flatten e1 + count_flatten e2
  | Flatten e' => S (count_flatten e')
  | Split k e' => count_flatten e'
  | Transpose e' => count_flatten e'
  | Truncr k e' => count_flatten e'
  | Truncl k e' => count_flatten e'
  | Padr k e' => count_flatten e'
  | Padl k e' => count_flatten e'
  | Scalar _ => 0
  end.

Fixpoint count_split e : nat :=
  match e with
  | Gen i lo hi body => count_split body
  | Sum i lo hi body => count_split body
  | Guard b e' => count_split e'
  | Lbind x e1 e2 => count_split e1 + count_split e2
  | Concat e1 e2 => count_split e1 + count_split e2
  | Flatten e' => count_split e'
  | Split k e' => S (count_split e')
  | Transpose e' => count_split e'
  | Truncr k e' => count_split e'
  | Truncl k e' => count_split e'
  | Padr k e' => count_split e'
  | Padl k e' => count_split e'
  | Scalar _ => 0
  end.

Ltac print_counts name :=
  let e := Reify.R in
  let gen_count := constr:(count_gen e) in
  let gen_count := constr:(nat_to_string gen_count) in
  let concat_count := constr:(count_concat e) in
  let concat_count := constr:(nat_to_string concat_count) in
  let truncate_count := constr:(count_truncate e) in
  let truncate_count := constr:(nat_to_string truncate_count) in
  let transpose_count := constr:(count_transpose e) in
  let transpose_count := constr:(nat_to_string transpose_count) in
  let flatten_count := constr:(count_flatten e) in
  let flatten_count := constr:(nat_to_string flatten_count) in
  let split_count := constr:(count_split e) in
  let split_count := constr:(nat_to_string split_count) in
  let str := constr:((name++","
                        ++gen_count++","
                        ++concat_count++","
                        ++truncate_count++"," 
                        ++transpose_count++"," 
                        ++flatten_count++","
                        ++split_count)) in
  let str := eval unfold nat_to_string in str in
  let str := eval simpl in str in
    idtac str.

Goal True.
Proof.
  idtac "program,gen,concat,truncate,transpose,flatten,split".
Abort.

Goal forall (W C B K : Z) (x w : list (list (list R))) (RR : Z) (a b :nat),
    consistent w (a,(b,(Z.to_nat RR, tt))) ->
          (0 < C)%Z ->
          (0 < W)%Z ->
          (W <=C)%Z ->
          (0 < K)%Z ->
          (0 < RR)%Z ->
          (0 < B)%Z ->
          gather_full W C B K x w RR = scatter_full B K W C x w.
Proof.
  intros. autounfold with examples.
  print_counts "gather".
Abort.

Goal forall (W C B K : Z) (x w : list (list (list R))) (RR : Z) (a b :nat),
    consistent w (a,(b,(Z.to_nat RR, tt))) ->
          (0 < C)%Z ->
          (0 < W)%Z ->
          (W <=C)%Z ->
          (0 < K)%Z ->
          (0 < RR)%Z ->
          (0 < B)%Z ->
          scatter_full B K W C x w = gather_full W C B K x w RR.
Proof.
  intros. autounfold with examples.
  print_counts "scatter".
Abort.

Goal forall B C K W RR (w : list (list (list R))) (x : list (list (list R))),
    (0 < B)%Z ->
    (0 < C)%Z ->
    (0 < K)%Z ->
    (0 < W)%Z ->
    (0 < RR)%Z ->
    im2col B K W C RR w x =
      im2col_lifted B K W C RR w x.
Proof.
  intros. autounfold with examples.
  print_counts "im2col conv".
Abort.    

Goal forall B C K W RR (w : list (list (list R))) (x : list (list (list R))),
    (0 < B)%Z ->
    (0 < C)%Z ->
    (0 < K)%Z ->
    (0 < W)%Z ->
    (0 < RR)%Z ->
    im2col_lifted B K W C RR w x = im2col B K W C RR w x.
Proof.
  intros. autounfold with examples.
  print_counts "im2col mat".
Abort.    

Goal forall (A B C : nat) (m1 m2 : (list (list R))) (k : Z),
    (0 < k)%Z ->
    0 < A ->
    0 < B ->
    0 < C ->
    consistent m1 (A,(B,tt)) ->
    consistent m2 (B,(C,tt)) ->
    matmul (Z.of_nat A) (Z.of_nat B) (Z.of_nat C) m1 m2 =
      matmul_tiled A B C m1 m2 k.
Proof.
  intros. autounfold with examples.
  print_counts "matmul".
Abort.

Goal forall (A B C : nat) (m1 m2 : (list (list R))) (k : Z),
    (0 < k)%Z ->
    0 < A ->
    0 < B ->
    0 < C ->
    consistent m1 (64,(64,tt)) ->
    consistent m2 (64,(64,tt)) ->    
    matmul_tiled 64 64 64 m1 m2 4 =
      matmul 64 64 64 m1 m2.
Proof.
  intros. autounfold with examples.
  print_counts "tiled matmul".
Abort.

Goal forall (A B C : nat) (m1 m2 : (list (list R))) (k : Z),
    (0 < k)%Z ->
    0 < A ->
    0 < B ->
    0 < C ->
    consistent m1 (64,(64,tt)) ->
    consistent m2 (64,(64,tt)) ->    
    matmul_tiled_split 64 64 64 m1 m2 4 =
      matmul 64 64 64 m1 m2.
Proof.
  intros. autounfold with examples.
  print_counts "tiled+tails matmul".
Abort.

Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    blurtwostage N M v = blurimmediate v M N.
Proof.
  intros. autounfold with examples.
  print_counts "two-stage blur".
Abort.

Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->
    blurimmediate v M N = blurtwostage N M v.
Proof.
  intros. autounfold with examples.
  print_counts "fused blur".
Abort.

Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->
    blurimmediate_partition M N v = blurtwostage N M v.
Proof.
  intros. autounfold with examples.
  print_counts "fused+tails blur".
Abort.

Goal forall n m (l : list (list R)),
    0 < n ->
    0 < m ->
    consistent l (n,(m,tt)) ->
    blur_tiles_guarded l 64 64 4 4 = @nil _.
Proof. 
  intros. autounfold with examples.
  print_counts "tiled+tails+staged blur".
Abort.

Goal forall (A B C D : nat) (m1 m2 : (list (list (list (list R))))),
         0 < A ->
         0 < B ->
         0 < C ->
         0 < D ->
         consistent m1 (A,(B,(C,(D,tt)))) ->
         consistent m2 (A,(B,(C,(D,tt)))) ->
         add (Z.of_nat A) (Z.of_nat B) (Z.of_nat C) (Z.of_nat D) m1 m2 =
           add_split A B C D m1 m2.
Proof.
  intros. autounfold with examples.
  print_counts "tensor add".
Abort.  

Goal forall (A B C D : nat) (m1 m2 : (list (list (list (list R))))),
         consistent m1 (8,(8,(8,(8,tt)))) ->
         consistent m2 (8,(8,(8,(8,tt)))) ->         
         add_split 8 8 8 8 m1 m2 =
           add 8 8 8 8 m1 m2.
Proof.
  intros. autounfold with examples.
  print_counts "split tensor add".
Abort.  

