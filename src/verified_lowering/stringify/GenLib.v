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
From Coq Require Import micromega.Lia.
From Coq Require Import micromega.Zify.
From Coq Require Import Lists.List.

Import ListNotations.

Require Import Ltac2.Ltac2.
Require Import Ltac2.Option.

From ATL Require Import ATL Tactics Common CommonTactics Div Reshape Map.
From Codegen Require Import IdentParsing NatToString IntToString CodeGen Normalize CheckSafe.
From Examples Require Import GatherScatter Convolution Im2col Blur TensorAdd Matmul.
From Inferpad Require Import Reify.
From Lower Require Import Zexpr ATLDeep Bexpr Sexpr.
From Stringify Require Import Stringify.

Open Scope string_scope.

Set Default Proof Mode "Classic".

Definition SENTINEL := "!!!".

Ltac Llibfunc name context :=
  let args'' := args_for_decl in
  let args' := eval simpl in args'' in
    let args := match args' with
                | String _ ?s' => s'
                | EmptyString => EmptyString
                end in
  let ast := R in
    let _ := match goal with |- _ => intros end in
    let ast := constr:(lower ast
                         (fun i : list (Zexpr * Zexpr) => i) "output"
                         Assign context) in
    let _ := match goal with |- _ => assert (Hast : ast = ast) by eauto end in
    let Hast := match goal with
                  H : ?ast = ?ast |- _ => H
                end in
    let _ := match goal with
               |- _ =>
                 repeat (simpl in Hast;
                         first [ rewrite lookup_add_eq in Hast by auto |
                                 rewrite lookup_add_ne in Hast by
                                   (unfold not; intros Hneq; inversion Hneq)
                   ] );
                 simpl combine in Hast end in
  let ast := match goal with
               H : ?ast = ?ast |- _ => ast
             end in
  let ast := eval unfold flat_sizeof in ast in
  let ast := eval simpl in ast in
  let prog := match goal with |- ?prog = _ => prog end in
  let progty := type of prog in
  let tystr := type_to_str progty in
  let funcname := name in
  let progstr := stringify_stmt ast in  
  let progstr := eval simpl in progstr in
    let header := constr:([funcname++".h";
                           "#include <stdlib.h>";
                           "";
                           "void "++funcname++"("++args++","++scalar++"*output);"]) in 
    
    let func := constr:((funcname++".c")::
                          "#include <stdlib.h>"::
                          ("#include @"++funcname++".h@")::
                          ""::
                          ("void "++funcname++"("++args++","++scalar++"*output)"++"{")::
                          (progstr++
                             ["}"])%list) in

    let ret' := constr:(app ("!!!"::header) ("!!!"::func)) in
    let ret := eval simpl in ret' in
      ret. 

Goal forall A B C (m1 m2 : list (list R)),
     (0 < A)%Z ->
     (0 < B)%Z ->
     (0 < C)%Z ->
     consistent m1 (Z.to_nat A,(Z.to_nat B,tt)) ->
     consistent m2 (Z.to_nat B,(Z.to_nat C,tt)) ->
     matmul A B C m1 m2 = matmul_tiled (Z.to_nat A) (Z.to_nat B) (Z.to_nat C) m1 m2 4%Z.
Proof.
  intros.  
  let s := Llibfunc
             constr:("matmul")
             constr:(($0 $+ ("m1", [ZLit A;ZLit B])
                        $+ ("m2", [ZLit A;ZLit B])))
  in idtac_list s.
Abort.

Goal forall A B C (m1 m2 : list (list R)),
     (0 < A)%Z ->
     (0 < B)%Z ->
     (0 < C)%Z ->
     consistent m1 (Z.to_nat A,(Z.to_nat B,tt)) ->
     consistent m2 (Z.to_nat B,(Z.to_nat C,tt)) ->
     matmul_tiled (Z.to_nat A) (Z.to_nat B) (Z.to_nat C) m1 m2 4%Z =
       matmul A B C m1 m2.
Proof.
 intros.
 let s := Llibfunc
            constr:("matmul_tiled")
                     constr:(($0 $+ ("m1", [ZLit A;ZLit B])
                                $+ ("m2", [ZLit A;ZLit B])))
 in idtac_list s.
Abort.

Goal forall A B C (m1 m2 : list (list R)),
     (0 < A)%Z ->
     (0 < B)%Z ->
     (0 < C)%Z ->
     consistent m1 (Z.to_nat A,(Z.to_nat B,tt)) ->
     consistent m2 (Z.to_nat B,(Z.to_nat C,tt)) ->
     matmul_tiled_split (Z.to_nat A) (Z.to_nat B) (Z.to_nat C) m1 m2 4%Z =
       matmul A B C m1 m2.
Proof.
 intros.
 let s := Llibfunc
            constr:("matmul_tiled_split")
                     constr:(($0 $+ ("m1", [ZLit A;ZLit B])
                                $+ ("m2", [ZLit B;ZLit C])))
 in idtac_list s.
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
  intros.  
  let s := Llibfunc
             constr:("tensoradd")
             constr:(($0
                        $+ ("m1",
                          [ZLit (Z.of_nat A);ZLit (Z.of_nat B);ZLit (Z.of_nat C);ZLit (Z.of_nat A)])
                        $+ ("m2",
                          [ZLit (Z.of_nat A);ZLit (Z.of_nat B);ZLit (Z.of_nat C);ZLit (Z.of_nat A)])))
  in idtac_list s.
Abort.  

Goal forall (A B C D : nat) (m1 m2 : (list (list (list (list R))))),
         0 < A ->
         0 < B ->
         0 < C ->
         0 < D ->
         consistent m1 (A,(B,(C,(D,tt)))) ->
         consistent m2 (A,(B,(C,(D,tt)))) ->         
         add_split A B C D m1 m2 =
           add (Z.of_nat A) (Z.of_nat B) (Z.of_nat C) (Z.of_nat D) m1 m2.
Proof.
  intros.  
  let s := Llibfunc
             constr:("tensoradd_split")
             constr:(($0
                        $+ ("m1",
                          [ZLit (Z.of_nat A);ZLit (Z.of_nat B);ZLit (Z.of_nat C);ZLit (Z.of_nat A)])
                        $+ ("m2",
                          [ZLit (Z.of_nat A);ZLit (Z.of_nat B);ZLit (Z.of_nat C);ZLit (Z.of_nat A)])))
  in idtac_list s.
Abort.  

Goal forall (c : (list R)) n m,
    conv4 c n m = conv1 c n m.
Proof.
  intros.  
  let s := Llibfunc constr:("conv4")
                             constr:(($0 $+ ("c",[ZLit n])))
  in idtac_list s.
Abort.

Goal forall (c : (list R)) n m,
    conv4 c n m = conv1 c n m.
Proof.
  intros.  
  let s := Llibfunc constr:("conv4")
                             constr:(($0 $+ ("c",[ZLit n])))
  in idtac_list s.
Abort.

Goal forall (c : (list R)) (n m : Z),
    (0 < n)%Z ->
    (-m+1 < n)%Z ->
    consistent c (Z.to_nat n,tt) ->
    conv1 c n m = conv4 c n m.
Proof.
  intros.
  let s := Llibfunc constr:("conv1")
                             constr:(($0 $+ ("c",[ZLit n])))
  in idtac_list s.
Abort.
           
Goal forall n m (l : list (list R)),
    Common.transpose (
        (GEN [ j < 1 ]
            GEN [ i < n ]
            l _[i;j])
          <++>          
          (GEN [ 1 <= j < m ]
            (GEN [ i < 1 ]
                 l _[i;j])
            <++>
            (GEN [ 1 <= i < n - 1]
                 l _[i;j])
            <++>
            (GEN [ n - 1 <= i < n ]
                 l _[i;j])
          )
        )
 = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("concattest1")
                             constr:($0 $+ ("l",[ZLit n; ZLit m]))
  in idtac_list s.
Abort.

Goal forall n m (l : list (list R)),
    consistent l (n,(m,tt)) ->
    Common.transpose (
        (GEN [ j < 1 ]
            GEN [ i < Z.of_nat n ]
            l _[i;j])
          <++>          
          (GEN [ 1 <= j < Z.of_nat m ]
               GEN [ i < Z.of_nat n ]
            l _[i;j])
          )
 = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("concattest0")
                             constr:($0 $+ ("l",[ZLit (Z.of_nat n);
                                                 ZLit (Z.of_nat m)]))
  in idtac_list s.
Abort.

Goal forall n m (v : list (list R)),
    0 < n ->
    0 < m ->
    consistent v (n,(m,tt)) ->
    Common.transpose (
        (GEN [ j < 1 ]
           (GEN [ i < 1 ]
                 v _[i;j])
            <++>
            (GEN [ 1 <= i < Z.of_nat n ]
                 v _[i;j])             
            )
          <++>          
          (GEN [ 1 <= j < Z.of_nat m ]
               GEN [ i < Z.of_nat n ]
               v _[i;j]
          )
        )
 = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("concattest2")
                             constr:($0 $+ ("v",[ZLit (Z.of_nat n);
                                                 ZLit (Z.of_nat m)]))
  in idtac_list s.
Abort.

Goal forall n m (l : list (list R)),
    consistent l (n,(m,tt)) ->
    Common.transpose (
        GEN [ j < Z.of_nat m ]
            (GEN [ i < 1 ]
            l _[i;j])
            <++>
            (GEN [ 1 <= i < Z.of_nat n ]
            l _[i;j]))
 = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("concattest3")
                               constr:($0 $+ ("l",[ZLit (Z.of_nat n);
                                                 ZLit (Z.of_nat m)]))
  in idtac_list s.
Abort.

Goal forall n m (l : (list R)),
    consistent l (n*m,tt) ->
    Common.flatten (
        Common.transpose
          (
            (GEN [ i < 1 ]
             (GEN [ j < Z.of_nat n ]
                  l _[j * Z.of_nat m + i]))
              <++>
            (GEN [ 1 <= i < Z.of_nat m ]
             (GEN [ j < Z.of_nat n ]
                 l _[j * Z.of_nat m + i]))              
      ))

 = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("concattest4")
  constr:($0 $+ ("l",[ZLit (Z.of_nat n); ZLit (Z.of_nat m)])) in idtac_list s.
Abort.

 Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->
    blurimmediate v M N = blurtwostage N M v.
 Proof.
 intros.
   let s := Llibfunc constr:("blurim")
                     constr:($0 $+ ("v",[ZLit (Z.of_nat N);
                                         ZLit (Z.of_nat M)])) in idtac_list s.
Abort.
 
Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->
    blurtwostage N M v = blurimmediate v M N.
Proof.
  intros.
  let s := Llibfunc constr:("blurtwo")
                             constr:($0 $+ ("v",[ZLit (Z.of_nat N);
                                                 ZLit (Z.of_nat M)])) in
  idtac_list s.
Abort.
(*
Goal forall (n m : nat) (l : list (list R)),
  0 < n ->
  0 < m ->
  consistent l (n, (m, tt)) ->  
    ((Truncr
        (Z.of_nat 64 * Z.of_nat (n - 1 - 1) // (Z.of_nat 64) -
           Z.of_nat (n - 1 - 1))
          (flatten
             (
              (GEN [ Z.of_nat (n - 1 - 1) / Z.of_nat 64 <= i < 
                Z.of_nat (n - 1 - 1) // (Z.of_nat 64) ]
               transpose
                 (Truncr
                    (Z.of_nat 64 * Z.of_nat (m - 1 - 1) // (Z.of_nat 64) -
                     Z.of_nat (m - 1 - 1))
                    (flatten
                       (GEN [ i0 < Z.of_nat (m - 1 - 1) // (Z.of_nat 64) ]
                        GEN [ i1 < Z.of_nat 64 ]
                        GEN [ i2 < Z.of_nat 64 ]
                        (|[ i0 * Z.of_nat 64 + i1 <? Z.of_nat (m - 1 - 1) ]|
                          (|[ i * Z.of_nat 64 + i2 <? Z.of_nat (n - 1 - 1) ]|
                            l _[ i * Z.of_nat 64 + i2; i0 * Z.of_nat 64 + i1] <+>
                            l _[ i * Z.of_nat 64 + i2; i0 * Z.of_nat 64 + i1 + 1] <+>
                            l _[ i * Z.of_nat 64 + i2; i0 * Z.of_nat 64 + i1 + 2])))))))))) = []
.
Proof.
  autounfold with examples.
  let s := Llibfunc constr:("blurtiles") in idtac_list s.
*)

Goal forall n m (l : list (list R)),
    0 < n ->
    0 < m ->
    consistent l (n,(m,tt)) ->
    blur_tiles_guarded l n m 64 64
    = @nil _.
Proof.
  autounfold with examples. intros.
  let s := Llibfunc constr:("blurtiles")
  constr:($0 $+ ("l",[ZLit (Z.of_nat n); ZLit (Z.of_nat m)])) in idtac_list s.
Abort.

Goal forall n m (l : list (list R)),
    0 < n ->
    0 < m ->
    consistent l (n,(m,tt)) ->
    fusion_no_boundary n m l 
    = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("fusion_nb")
    constr:($0 $+ ("l",[ZLit (Z.of_nat n); ZLit (Z.of_nat m)])) in idtac_list s.
Abort.

Goal forall W RR (x w : list R),    
    consistent w (Z.to_nat RR, tt) ->
    consistent x (Z.to_nat RR, tt) ->
    (0 < W)%Z ->
    (Z.of_nat (length x) < W)%Z ->
    gather W x w = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("gather")
  constr:($0 $+ ("x",[ZLit RR]) $+ ("w",[ ZLit RR])) in idtac_list s.
Abort.      

Goal forall W RR (x w : list R),    
    consistent w (Z.to_nat RR, tt) ->
    consistent x (Z.to_nat RR, tt) ->
    (0 < W)%Z ->
    (Z.of_nat (length x) < W)%Z ->
    scatter W x w = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("scatter")
  constr:($0 $+ ("x",[ZLit RR]) $+ ("w",[ ZLit RR])) in idtac_list s.
Abort.

Goal forall A B K W RR (w : list (list R)) (x : list R),
    (0 < K)%Z ->
    (0 < W)%Z ->
    (0 < RR)%Z ->    
    consistent w (A,(B,tt))->
    consistent x (Z.to_nat K,tt) ->
    im2colminilifted K W RR w x = im2colmini K W RR w x.
Proof.
  intros.
  let s := Llibfunc constr:("im2collifted")
                             constr:($0 $+ ("x",[ZLit K]) $+
                                       ("w",[ ZLit (Z.of_nat A);
                                              ZLit (Z.of_nat B)]))
  in idtac_list s.                             
Abort.      

Goal forall A B K W RR (w : list (list R)) (x : list R),
    (0 < K)%Z ->
    (0 < W)%Z ->
    (0 < RR)%Z ->    
    consistent w (A,(B,tt))->
    consistent x (Z.to_nat K,tt) ->
    im2colminilifted K W RR w x = im2colmini K W RR w x.
Proof.
  intros.
  let s := Llibfunc constr:("im2col")
                             constr:($0 $+ ("x",[ZLit K]) $+
                                       ("w",[ ZLit (Z.of_nat A);
                                              ZLit (Z.of_nat B)]))
  in idtac_list s.                             
                             
Abort.

Goal forall n m (v : list (list R)),
    2 < n ->
    2 < m ->
    consistent v (n,(m,tt)) ->
    blurimmediate_partition n m v = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("blurpart")
                             constr:($0 $+ ("v",[ZLit (Z.of_nat n);
                                                 ZLit (Z.of_nat m)]))
  in idtac_list s.
Abort.

Goal forall n m (v : list (list R)),
    2 < n ->
    2 < m ->
    consistent v (n,(m,tt)) ->
    blurimmediate_isolate n m v = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("blurisolate")
                             constr:($0 $+ ("v",[ZLit (Z.of_nat n);
                                                 ZLit (Z.of_nat m)]))
  in idtac_list s.  
Abort.

Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    blurtwostage_partition N M v = @nil _.
Proof.
  intros.
  let s := Llibfunc constr:("blurtwopart")
                             constr:($0 $+ ("v",[ZLit (Z.of_nat N);
                                                 ZLit (Z.of_nat M)]))
  in idtac_list s.                             
Abort.
