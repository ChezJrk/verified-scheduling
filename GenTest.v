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

Require Import Ltac2.Ltac2.
Require Import Ltac2.Option.

Set Warnings "-omega-is-deprecated,-deprecated".

From ATL Require Import ATL Common CommonTactics Div IdentParsing GatherScatter NatToString IntToString Convolution Im2col Blur CodeGen.

Open Scope string_scope.

Set Default Proof Mode "Classic".

Definition SENTINEL := "!!!\n".

Ltac Ltime name default_dim reps :=
  let _ := match goal with _ => intros; try autounfold with examples end in
  let callocs_frees_args := allocs_for_call in
  let callocs := fst2 callocs_frees_args in
  let frees := snd2 callocs_frees_args in
  
  let arg_vals := args_for_call default_dim in
  let allocs := fst3 arg_vals in
  let call_vals' := snd3 arg_vals in
  let call_vals := match call_vals' with
                   | String _ ?s' => s'
                   | EmptyString => EmptyString
                   end in  
  let _ := match goal with _ => intros end in

  let prog := match goal with |- ?prog = _ => prog end in
  let progty := type of prog in
  let tystr := type_to_str progty in
  let funcname := name in

  let size := alloc_size prog in
    
  let _ := match goal with _ => assert Z by exact 0%Z end in
  let i := match goal with H : Z |- _ => constr:(ltac:(to_str H)) end in
  
  let main :=
      constr:(funcname++"_time.c\n"++
              HEADERS++
              "#include @"++funcname++".h@\n\n"++
              "int main() {\n"++
              "srandom(time(NULL));\n"++
              allocs++
              callocs++
              scalar++" *output = ("++scalar++"*) calloc(1,"++size++");\n"++
              "float accum = 0;\n"++
              "for (int "++i++" = 0; "++i++" < "++reps++"; "++i++"++) {\n"++
              "clock_t start = clock();\n"++
              funcname++"("++call_vals++",output);\n"++
              "clock_t end = clock();\n"++                       
              "double t = ((double) (end - start)/CLOCKS_PER_SEC);\n"++
              "accum += t;\n"++
              "}\n"++
              "free(output);\n"++              
              "float avg = accum / "++reps++";\n"++
              "printf(@"++funcname++"\t"++default_dim++"\t"++"%lfs~@,avg);\n"++
              frees++
              "return 0;\n"++
              "}") in
  let ret' := constr:(SENTINEL++main) in
  let ret := eval simpl in ret' in
      ret.

Ltac Leq lname rname default_dim :=
  let _ := match goal with _ => intros; try autounfold with examples end in
  let callocs_frees_args := allocs_for_call in
  let callocs := fst2 callocs_frees_args in
  let frees := snd2 callocs_frees_args in
  
  let arg_vals := args_for_call default_dim in
  let allocs := fst3 arg_vals in
  let call_vals' := snd3 arg_vals in
  let call_vals := match call_vals' with
                   | String _ ?s' => s'
                   | EmptyString => EmptyString
                   end in  
  let _ := match goal with _ => intros end in

  let lprog := match goal with |- ?prog = _ => prog end in
  let rprog := match goal with |- _ = ?prog => prog end in  
  let progty := type of lprog in
  let tystr := type_to_str progty in

  let src := fresh_str constr:(1%nat) in
  let size := alloc_size lprog in
  let pref := match progty with
              | R => constr:("(")
              | list _ => constr:("*(")
              end in

  let sh := get_shape lprog in
  let nums := alloc_dim sh in
  let _ := match goal with _ => assert Z by exact 0%Z end in
  let x' := match goal with H : Z |- _ => H end in
  let x := constr:(ltac:(to_str x')) in
  let _ := match goal with _ => clear x' end in
  let comp :=
      constr:("for (int "++x++" = 0; "++x++" < "++nums++"; "++x++"++) {\n"++
              "assert(loutput["++x++"] == routput["++x++"]);\n"++
              "}\n") in
              
  let main := constr:(lname++"_"++rname++"_eq.c\n"++
                       HEADERS++
                       "#include @"++lname++".h@\n"++
                       "#include @"++rname++".h@\n\n"++                       
                       "int main() {\n"++
                       "srandom(time(NULL));\n"++
                       allocs++
                       callocs++
                       tystr++" loutput = ("++scalar++"*) calloc(1,"++size++");\n"++
                       tystr++" routput = ("++scalar++"*) calloc(1,"++size++");\n"++
                       lname++"("++call_vals++",loutput);\n"++
                       rname++"("++call_vals++",routput);\n"++
                       comp++
                       frees++
                       "free(loutput);\n"++
                       "free(routput);\n"++                       
                       "return 0;\n"++
                       "}") in

  let ret' := constr:(SENTINEL++main) in
  let ret := eval simpl in ret' in
      ret.

Ltac Lid lname default_dim :=
  let _ := match goal with _ => intros; try autounfold with examples end in
  let callocs_frees_args := allocs_for_call in
  let callocs := fst2 callocs_frees_args in
  let frees := snd2 callocs_frees_args in
  
  let arg_vals := args_for_call default_dim in
  let allocs := fst3 arg_vals in
  let call_vals' := snd3 arg_vals in
  let call_vals := match call_vals' with
                   | String _ ?s' => s'
                   | EmptyString => EmptyString
                   end in  
  let _ := match goal with _ => intros end in

  let lprog := match goal with |- ?prog = _ => prog end in
  let progty := type of lprog in
  let tystr := type_to_str progty in

  let src := fresh_str constr:(1%nat) in
  let size := alloc_size lprog in
  let pref := match progty with
              | R => constr:("(")
              | list _ => constr:("*(")
              end in

  let sh := get_shape lprog in
  let nums := alloc_dim sh in
  let _ := match goal with _ => assert Z by exact 0%Z end in
  let x' := match goal with H : Z |- _ => H end in
  let x := constr:(ltac:(to_str x')) in
  let _ := match goal with _ => clear x' end in
  let comp :=
      constr:("for (int "++x++" = 0; "++x++" < "++nums++"; "++x++"++) {\n"++
              "assert(loutput["++x++"] == v["++x++"]);\n"++
              "}\n") in
              
  let main := constr:(lname++"_"++"id_eq.c\n"++
                       HEADERS++
                       "#include @"++lname++".h@\n\n"++
                       "int main() {\n"++
                       "srandom(time(NULL));\n"++
                       allocs++
                       callocs++
                       tystr++" loutput = ("++scalar++"*) calloc(1,"++size++");\n"++
                       lname++"("++call_vals++",loutput);\n"++
                       comp++
                       frees++
                       "free(loutput);\n"++
                       "return 0;\n"++
                       "}") in

  let ret' := constr:(SENTINEL++main) in
  let ret := eval simpl in ret' in
      ret.

Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->
    blurimmediate N M v = blurtwostage N M v.
Proof.
  let s := Leq constr:("blurim") constr:("blurtwo") constr:("50") in idtac s.
Abort.

Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    blurimmediate_partition N M v = blurimmediate N M v.
Proof.
  let s := Leq constr:("blurpart") constr:("blurim") constr:("50") in idtac s.
Abort.

Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    blurimmediate_partition N M v = blurimmediate_isolate N M v.
Proof.
  let s := Leq constr:("blurpart") constr:("blurisolate") constr:("50") in idtac s.
Abort.


Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    blurtwostage_partition N M v = blurtwostage N M v.
Proof.
  let s := Leq constr:("blurtwopart") constr:("blurtwo") constr:("50") in idtac s.
Abort.

Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    fusion_no_boundary N M v = tile_no_boundary 64 64 N M v.
Proof.
  let s := Leq constr:("fusion_nb") constr:("tile_nb") constr:("1000") in idtac s.
Abort.

Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    fusion_no_boundary N M v = tile_no_boundary 64 64 N M v.
Proof.
  let s := Ltime constr:("fusion_nb") constr:("2000") constr:("50") in idtac s.
Abort.

Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    tile_no_boundary 64 64 N M v = fusion_no_boundary N M v.
Proof.
  let s := Ltime constr:("tile_nb") constr:("2000") constr:("50") in idtac s.
Abort.

Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->
    blurimmediate N M v = blur_tiles_guarded 64 64 N M v.
Proof.
  let s := Leq constr:("blurim") constr:("blurtiles") constr:("2000") in idtac s.
Abort.

Goal forall W C (x w : list R),
    (0 < C)%Z ->
    (0 < W)%Z ->
    (W <= C)%Z ->
    consistent x (Z.to_nat W,tt) ->
    consistent w (Z.to_nat W,tt) ->
    gather1 W C x w = scatter W x w.
Proof.  
  let s := Leq constr:("gather") constr:("scatter") constr:("100") in idtac s.
Abort.      

Goal forall (c : (list R)) (n m : Z),
    (0 < n)%Z ->
    (-m+1 < n)%Z ->
    consistent c (Z.to_nat n,tt) ->
    conv4 c n m = conv1 c n m.
Proof.
  let s := Leq constr:("conv4") constr:("conv1") constr:("100") in idtac s.
Abort.

Goal forall A B K W RR (w : list (list R)) (x : list R),
    (0 < K)%Z ->
    (0 < W)%Z ->
    (0 < RR)%Z ->    
    consistent w (A,(B,tt))->
    consistent x (Z.to_nat K,tt) ->
    im2colminilifted K W RR w x = im2colmini K W RR w x.
Proof.
  let s := Leq constr:("im2collifted") constr:("im2col") constr:("50") in idtac s.
Abort.      

Goal forall n m (v : list (list R)),
    consistent v (n,(m,tt)) ->
    transpose (
        (GEN [ j < 1 ]
            GEN [ i < Z.of_nat n ]
            v _[i;j])
          <++>          
          (GEN [ 1 <= j < Z.of_nat m ]
               GEN [ i < Z.of_nat n ]
            v _[i;j])
          )
 = @nil _.
Proof.
  let s := Lid constr:("concattest0") constr:("10") in idtac s.
Abort.


Goal forall n m (v : list (list R)),
    0 < n ->
    0 < m ->
    consistent v (n,(m,tt)) ->
    transpose (
        (GEN [ j < 1 ]
            GEN [ i < Z.of_nat n ]
            v _[i;j])
          <++>          
          (GEN [ 1 <= j < Z.of_nat m ]
            (GEN [ i < 1 ]
                 v _[i;j])
            <++>
            (GEN [ 1 <= i < Z.of_nat n ]
                 v _[i;j])
          )
        )
 = @nil _.
Proof.
  let s := Lid constr:("concattest1") constr:("10") in idtac s.
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
  let s := Lid constr:("concattest2") constr:("10") in idtac s.
Abort.

Goal forall n m (v : list (list R)),
    consistent v (n,(m,tt)) ->
    transpose (
        GEN [ j < Z.of_nat m ]
            (GEN [ i < 1 ]
            v _[i;j])
            <++>
            (GEN [ 1 <= i < Z.of_nat n ]
            v _[i;j]))
 = @nil _.
Proof.
  let s := Lid constr:("concattest3") constr:("10") in idtac s.
Abort.

Goal forall n m (v : (list R)),
    consistent v (n*m,tt) ->
    flatten (
       (GEN [ j < Z.of_nat n ]
            (GEN [ i < Z.of_nat m ]
                 v _[j * Z.of_nat m + i]))
      )

 = @nil _.
Proof.
  let s := Lid constr:("concattest4") constr:("10") in idtac s.
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
    let s := Lid constr:("concattest5") constr:("10") in idtac s.
Abort.


(* - *)

Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->
    blurimmediate N M v = blurtwostage N M v.
Proof.
  let s := Ltime constr:("blurim") constr:("1000") constr:("3") in idtac s.
Abort.

Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    blurimmediate_partition N M v = blurimmediate_partition N M v.
Proof.
  let s := Ltime constr:("blurpart") constr:("1000") constr:("3") in idtac s.
Abort.

Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    blurtwostage_partition N M v = blurimmediate_partition N M v.
Proof.
  let s := Ltime constr:("blurtwopart") constr:("1000") constr:("3") in idtac s.
Abort.

Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->
    blurtwostage N M v = blurimmediate N M v.
Proof.
  let s := Ltime constr:("blurtwo") constr:("1000") constr:("3") in idtac s.  
Abort.


Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->
    blur_tiles_guarded 64 64 N M v = blurimmediate N M v.
Proof.
  let s := Ltime constr:("blurtiles") constr:("2000") constr:("10") in idtac s.  
Abort.

Goal forall W C (x w : list R),
    (0 < C)%Z ->
    (0 < W)%Z ->
    (W <= C)%Z ->
    consistent x (Z.to_nat W,tt) ->
    consistent w (Z.to_nat W,tt) ->
    gather1 W C x w = scatter W x w.
Proof.  
  let s := Ltime constr:("gather") constr:("100") constr:("10") in idtac s.
Abort.      

Goal forall W C (x w : list R),
    (0 < C)%Z ->
    (0 < W)%Z ->
    (W <= C)%Z ->
    consistent x (Z.to_nat W,tt) ->
    consistent w (Z.to_nat W,tt) ->
    scatter W x w = gather1 W C x w.
Proof.  
  let s := Ltime constr:("scatter") constr:("100") constr:("10") in idtac s.
Abort.      

Goal forall (c : (list R)) (n m : Z),
    (0 < n)%Z ->
    (-m+1 < n)%Z ->
    consistent c (Z.to_nat n,tt) ->
    conv4 c n m = conv1 c n m.
Proof.
  let s := Ltime constr:("conv4") constr:("100") constr:("10") in idtac s.
Abort.

Goal forall (c : (list R)) (n m : Z),
    (0 < n)%Z ->
    (-m+1 < n)%Z ->
    consistent c (Z.to_nat n,tt) ->
    conv1 c n m = conv4 c n m.
Proof.
  let s := Ltime constr:("conv1") constr:("100") constr:("10") in idtac s.
Abort.

Goal forall A B K W RR (w : list (list R)) (x : list R),
    (0 < K)%Z ->
    (0 < W)%Z ->
    (0 < RR)%Z ->    
    consistent w (A,(B,tt))->
    consistent x (Z.to_nat K,tt) ->
    im2colminilifted K W RR w x = im2colmini K W RR w x.
Proof.
  let s := Ltime constr:("im2collifted") constr:("50") constr:("10") in idtac s.
Abort.      

Goal forall A B K W RR (w : list (list R)) (x : list R),
    (0 < K)%Z ->
    (0 < W)%Z ->
    (0 < RR)%Z ->    
    consistent w (A,(B,tt))->
    consistent x (Z.to_nat K,tt) ->
    im2colmini K W RR w x = im2colminilifted K W RR w x.
Proof.
  let s := Ltime constr:("im2col") constr:("50") constr:("10") in idtac s.
Abort.      

