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
From Coq Require Import omega.Omega.

Require Import Ltac2.Ltac2.
Require Import Ltac2.Option.

Set Warnings "-omega-is-deprecated,-deprecated".

From ATL Require Import ATL Tactics Common CommonTactics Div IdentParsing
     GatherScatter NatToString IntToString Convolution Im2col Blur CodeGen
     Normalize Reshape CheckSafe.

Open Scope string_scope.

Set Default Proof Mode "Classic".

Definition SENTINEL := "!!!\n".

Ltac Llibfunc name :=
  let _ := match goal with _ => intros;
                                try autounfold with examples(*;
                                try check_safe *)end in
  
  let args'' := args_for_decl in
  let args' := eval simpl in args'' in
  let args := match args' with
                   | String _ ?s' => s'
                   | EmptyString => EmptyString
              end in
  let _ := match goal with _ => intros end in

  let _ := match goal with _ =>
                           idtac; unfold bin; simpl (*normalize; normalize_shape_op*) end in
  
  let prog := match goal with |- ?prog = _ => prog end in
  let progty := type of prog in
  let tystr := type_to_str progty in
  let funcname := name in

  let size := alloc_size prog in
  
  let tup := L prog constr:("output")
                    constr:(fun (acc : indty) => acc)
                    constr:(true)
                    constr:(2%nat) in
  let allocs := fst tup in
  let lower := snd tup in
  let frees := thd tup in

  let header := constr:(funcname++".h\n"++
                        "#include <stdlib.h>\n\n"++
                        "void "++funcname++"("++args++","++scalar++"*output);\n") in 
  
  let func := constr:(funcname++".c\n"++
                      "#include <stdlib.h>\n"++
                      "#include @"++funcname++".h@\n\n"++
                      "void "++funcname++"("++args++","++scalar++"*output)"++"{\n"++
                      allocs++
                      lower++
                      frees++
                      "}\n") in

  let ret' := constr:(SENTINEL++header++SENTINEL++func) in
  let ret := eval simpl in ret' in
      ret.

Goal forall n m (l : list (list R)),
    consistent l (n,(m,tt)) ->
    transpose (
        (GEN [ j < 1 ]
            GEN [ i < Z.of_nat n ]
            l _[i;j])
          <++>          
          (GEN [ 1 <= j < Z.of_nat m ]
            (GEN [ i < 1 ]
                 l _[i;j])
            <++>
            (GEN [ 1 <= i < Z.of_nat n - 1]
                 l _[i;j])
            <++>
            (GEN [ Z.of_nat n - 1 <= i < Z.of_nat n ]
                 l _[i;j])
          )
        )
 = @nil _.
Proof.
  let s := Llibfunc constr:("concattest1") in idtac s.
Abort.

Goal forall n m (l : list (list R)),
    consistent l (n,(m,tt)) ->
    transpose (
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
  let s := Llibfunc constr:("concattest0") in idtac s.
Abort.

Goal forall n m (v : list (list R)),
    0 < n ->
    0 < m ->
    consistent v (n,(m,tt)) ->
    transpose (
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
  let s := Llibfunc constr:("concattest2") in idtac s.
Abort.

Goal forall n m (l : list (list R)),
    consistent l (n,(m,tt)) ->
    transpose (
        GEN [ j < Z.of_nat m ]
            (GEN [ i < 1 ]
            l _[i;j])
            <++>
            (GEN [ 1 <= i < Z.of_nat n ]
            l _[i;j]))
 = @nil _.
Proof.
  let s := Llibfunc constr:("concattest3") in idtac s.
Abort.

Goal forall n m (l : (list R)),
    consistent l (n*m,tt) ->
    flatten (
        transpose
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
  let s := Llibfunc constr:("concattest4") in idtac s.
Abort.

Goal forall n m (v : list (list R)),
    0 < n ->
    0 < m ->
    consistent v (n,(m,tt)) ->
flatten_trunc n
    (GEN [ i < Z.of_nat n // 64 ]
     transpose
       (flatten_trunc m
          (GEN [ xo < Z.of_nat m // 64 ]
                transpose
                (
                  (GEN [ i2 < 1 ]
                       (GEN [ i1 < 64 ]
                        (|[ xo * 64 + i1 <? Z.of_nat m ]|
                         (|[ i * 64 + i2 <? Z.of_nat n ]|
                          (v _[i * 64 + i2;xo * 64 + i1])))))
                    <++>
                  (GEN [ 1 <= i2 < 64 ]
                       (GEN [ i1 < 64 ]
                        (|[ xo * 64 + i1 <? Z.of_nat m ]|
                         (|[ i * 64 + i2 <? Z.of_nat n ]|
                          (v _[i * 64 + i2;xo * 64 + i1])))))
                    
                )
    )))
 = @nil _.
Proof.
    let s := Llibfunc constr:("concattest5") in idtac s.
Abort.

Goal forall (c : (list R)) (n m : Z),
    (0 < n)%Z ->
    (-m+1 < n)%Z ->
    consistent c (Z.to_nat n,tt) ->
    conv4 c n m = conv1 c n m.
Proof.
  let s := Llibfunc constr:("conv4") in idtac s.
Abort.

Goal forall (c : (list R)) (n m : Z),
    (0 < n)%Z ->
    (-m+1 < n)%Z ->
    consistent c (Z.to_nat n,tt) ->
    conv1 c n m = conv4 c n m.
Proof.
  let s := Llibfunc constr:("conv1") in idtac s.
Abort.
 
Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->
    blurimmediate N M v = blurtwostage N M v.
Proof.
  let s := Llibfunc constr:("blurim") in idtac s.
Abort.
 
Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->
    blurtwostage N M v = blurimmediate N M v.
Proof.
  let s := Llibfunc constr:("blurtwo") in idtac s.
Abort.

Goal forall n m (l : list (list R)),
    0 < n ->
    0 < m ->
    consistent l (n,(m,tt)) ->
    blur_tiles_guarded 64 64 n m l 
    = @nil _.
Proof.
   let s := Llibfunc constr:("blurtiles") in idtac s.
Abort.

Goal forall n m (l : list (list R)),
    0 < n ->
    0 < m ->
    consistent l (n,(m,tt)) ->
    fusion_no_boundary n m l 
    = @nil _.
Proof.
  let s := Llibfunc constr:("fusion_nb") in idtac s.
Abort.

Goal forall n m (l : list (list R)),
    0 < n ->
    0 < m ->
    consistent l (n,(m,tt)) ->
    tile_no_boundary 64 64 n m l 
    = @nil _.
Proof.
  let s := Llibfunc constr:("tile_nb") in idtac s.
Abort.

Goal forall W C (x w : list R),
    (0 < C)%Z ->
    (0 < W)%Z ->
    (W <= C)%Z ->
    consistent x (Z.to_nat W,tt) ->
    consistent w (Z.to_nat W,tt) ->
    gather1 W C x w = scatter W x w.
Proof.
  let s := Llibfunc constr:("gather") in idtac s.
Abort.      

Goal forall W C (x w : list R),
    (0 < C)%Z ->
    (0 < W)%Z ->
    (W <= C)%Z ->
    consistent x (Z.to_nat W,tt) ->
    consistent w (Z.to_nat W,tt) ->
    scatter W x w = gather1 W C x w.
Proof.
  let s := Llibfunc constr:("scatter") in idtac s.
Abort.      

Goal forall A B K W RR (w : list (list R)) (x : list R),
    (0 < K)%Z ->
    (0 < W)%Z ->
    (0 < RR)%Z ->    
    consistent w (A,(B,tt))->
    consistent x (Z.to_nat K,tt) ->
    im2colminilifted K W RR w x = im2colmini K W RR w x.
Proof.
  let s := Llibfunc constr:("im2collifted") in idtac s.
Abort.      

Goal forall A B K W RR (w : list (list R)) (x : list R),
    (0 < K)%Z ->
    (0 < W)%Z ->
    (0 < RR)%Z ->    
    consistent w (A,(B,tt))->
    consistent x (Z.to_nat K,tt) ->
    im2colminilifted K W RR w x = im2colmini K W RR w x.
Proof.
  let s := Llibfunc constr:("im2col") in idtac s.
Abort.

Goal forall n m (v : list (list R)),
    2 < n ->
    2 < m ->
    consistent v (n,(m,tt)) ->
    blurimmediate_partition n m v = @nil _.
Proof.
    let s := Llibfunc constr:("blurpart") in idtac s.
Abort.

Goal forall n m (v : list (list R)),
    2 < n ->
    2 < m ->
    consistent v (n,(m,tt)) ->
    blurimmediate_isolate n m v = @nil _.
Proof.
    let s := Llibfunc constr:("blurisolate") in idtac s.
Abort.

Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    blurtwostage_partition N M v = @nil _.
Proof.
  let s := Llibfunc constr:("blurtwopart") in idtac s.
Abort.
