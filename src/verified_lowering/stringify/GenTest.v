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

Import ListNotations.

Require Import Ltac2.Ltac2.
Require Import Ltac2.Option.

Set Warnings "-omega-is-deprecated,-deprecated".

From ATL Require Import ATL Common CommonTactics Div.
From Examples Require Import GatherScatter Convolution Im2col Blur TensorAdd Matmul.
From Codegen Require Import IdentParsing NatToString IntToString CodeGen.

Open Scope string_scope.

Set Default Proof Mode "Classic".

Definition SENTINEL := "!!!".

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
      constr:(
              (app ((funcname++"_time.c")::
              HEADERS) 

              (app (("#include @"++funcname++".h@")::
              ""::
              "int main() {"::
              "srandom(time(NULL));"::
              allocs)
              
              (app callocs

              (app
              ((scalar++" *output = ("++scalar++"*) calloc(1,"++size++");")::
              "float accum = 0;"::
              ("for (int "++i++" = 0; "++i++" < "++reps++"; "++i++"++) {")::
              "clock_t start = clock();"::
              (funcname++"("++call_vals++",output);")::
              "clock_t end = clock();"::          
              "double t = ((double) (end - start)/CLOCKS_PER_SEC);"::
              "accum += t;"::
              "}"::
              "free(output);"::
              ("float avg = accum / "++reps++";")::
              ("printf(@"++funcname++"\t"++default_dim++"\t"++"%lfs~@,avg);")::
              frees)
              
              ["return 0;";
              "}"]))))) in
  let ret' := constr:("!!!"::main) in
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
      constr:(["for (int "++x++" = 0; "++x++" < "++nums++"; "++x++"++) {";
              "assert(loutput["++x++"] == routput["++x++"]);";
              "}"]) in
              
  let main := constr:(
                      (app ((lname++"_"++rname++"_eq.c")::
                       HEADERS)

                       (app (("#include @"++lname++".h@")::
                       ("#include @"++rname++".h@")::
                       ""::
                       "int main() {"::
                       "srandom(time(NULL));"::
                       allocs)

                       (app callocs

                       (app ((tystr++" loutput = ("++scalar++"*) calloc(1,"++size++");")::
                       (tystr++" routput = ("++scalar++"*) calloc(1,"++size++");")::
                       (lname++"("++call_vals++",loutput);")::
                       (rname++"("++call_vals++",routput);")::
                       comp)

                       (app frees

                       ["free(loutput);";
                       "free(routput);";
                       "return 0;";"}"])))))) in

  let ret' := constr:("!!!"::main) in
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
      constr:(["for (int "++x++" = 0; "++x++" < "++nums++"; "++x++"++) {";
              "assert(loutput["++x++"] == v["++x++"]);";
              "}"]) in
              
  let main := constr:(
                       (app ((lname++"_"++"id_eq.c")::
                       HEADERS)

                       (app (("#include @"++lname++".h@")::
                       ""::
                       "int main() {"::
                       "srandom(time(NULL));"::
                       allocs)
                       
                       (app callocs
                       
                       (app ((tystr++" loutput = ("++scalar++"*) calloc(1,"++size++");")::
                       (lname++"("++call_vals++",loutput);")::
                       comp)
                       
                       (app frees
                       
                       ["free(loutput);";
                       "return 0;";
                       "}"])))))) in

  let ret' := constr:("!!!"::main) in
  let ret := eval simpl in ret' in
      ret.

Goal forall A B C (m1 m2 : list (list R)),
    (0 < A)%Z ->
    (0 < B)%Z ->
    (0 < C)%Z ->
    consistent m1 (Z.to_nat A,(Z.to_nat B,tt)) ->
    consistent m2 (Z.to_nat B,(Z.to_nat C,tt)) ->
    matmul_tiled_split (Z.to_nat A) (Z.to_nat B) (Z.to_nat C) m1 m2 4 =
      matmul A B C m1 m2.
Proof.
  let s := Leq constr:("matmul_tiled_split") constr:("matmul") constr:("50")
  in idtac_list s.
Abort.

Goal forall A B C (m1 m2 : list (list R)),
     (0 < A)%Z ->
     (0 < B)%Z ->
     (0 < C)%Z ->
     consistent m1 (Z.to_nat A,(Z.to_nat B,tt)) ->
     consistent m2 (Z.to_nat B,(Z.to_nat C,tt)) ->
     matmul A B C m1 m2 = matmul_tiled (Z.to_nat A) (Z.to_nat B) (Z.to_nat C) m1 m2 4%Z.
Proof.
  let s := Leq constr:("matmul") constr:("matmul_tiled") constr:("50")
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
  let s := Leq constr:("tensoradd") constr:("tensoradd_split") constr:("50")
  in idtac_list s.
Abort.
           
Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->
    blurimmediate v M N = blurtwostage N M v.
Proof.
  let s := Leq constr:("blurim") constr:("blurtwo") constr:("50") in idtac_list s.
Abort.

Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    blurimmediate_partition N M v = blurimmediate v M N.
Proof.
  let s := Leq constr:("blurpart") constr:("blurim") constr:("50") in idtac_list s.
Abort.

Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    blurimmediate_partition N M v = blurimmediate_isolate N M v.
Proof.
  let s := Leq constr:("blurpart") constr:("blurisolate") constr:("50") in idtac_list s.
Abort.


Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    blurtwostage_partition N M v = blurtwostage N M v.
Proof.
  let s := Leq constr:("blurtwopart") constr:("blurtwo") constr:("50") in idtac_list s.
Abort.
(*
Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    fusion_no_boundary N M v = tile_no_boundary 64 64 N M v.
Proof.
  let s := Leq constr:("fusion_nb") constr:("tile_nb") constr:("1000") in idtac_list s.
Abort.

Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    fusion_no_boundary N M v = tile_no_boundary 64 64 N M v.
Proof.
  let s := Ltime constr:("fusion_nb") constr:("2000") constr:("50") in idtac_list s.
Abort.

Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    tile_no_boundary 64 64 N M v = fusion_no_boundary N M v.
Proof.
  let s := Ltime constr:("tile_nb") constr:("2000") constr:("50") in idtac_list s.
Abort.
*)
Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->    
    blurimmediate v M N = blur_tiles_guarded v N M 64 64.
Proof.
  let s := Leq constr:("blurim") constr:("blurtiles") constr:("2000") in idtac_list s.
Abort.

Goal forall W R0 (x w : list R),    
    consistent w (Z.to_nat R0, tt) ->
    consistent x (Z.to_nat R0, tt) ->
    (0 < W)%Z ->
    (Z.of_nat (length x) < W)%Z ->
    gather W x w = scatter W x w.
Proof.  
  let s := Leq constr:("gather") constr:("scatter") constr:("10") in idtac_list s.
Abort.

Goal forall (c : (list R)) (n m : Z),
    (0 < n)%Z ->
    (-m+1 < n)%Z ->
    consistent c (Z.to_nat n,tt) ->
    conv4 c n m = conv1 c n m.
Proof.
  let s := Leq constr:("conv4") constr:("conv1") constr:("100") in idtac_list s.
Abort.

Goal forall A B K W RR (w : list (list R)) (x : list R),
    (0 < K)%Z ->
    (0 < W)%Z ->
    (0 < RR)%Z ->    
    consistent w (A,(B,tt))->
    consistent x (Z.to_nat K,tt) ->
    im2colminilifted K W RR w x = im2colmini K W RR w x.
Proof.
  let s := Leq constr:("im2collifted") constr:("im2col") constr:("50") in idtac_list s.
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
  let s := Lid constr:("concattest0") constr:("10") in idtac_list s.
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
  let s := Lid constr:("concattest1") constr:("10") in idtac_list s.
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
  let s := Lid constr:("concattest2") constr:("10") in idtac_list s.
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
  let s := Lid constr:("concattest3") constr:("10") in idtac_list s.
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
  let s := Lid constr:("concattest4") constr:("10") in idtac_list s.
Abort.
(* - *)

Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->
    blurimmediate v M N = blurtwostage N M v.
Proof.
  let s := Ltime constr:("blurim") constr:("1000") constr:("3") in idtac_list s.
Abort.

Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    blurimmediate_partition N M v = blurimmediate_partition N M v.
Proof.
  let s := Ltime constr:("blurpart") constr:("1000") constr:("3") in idtac_list s.
Abort.

Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    blurtwostage_partition N M v = blurimmediate_partition N M v.
Proof.
  let s := Ltime constr:("blurtwopart") constr:("1000") constr:("3") in idtac_list s.
Abort.

Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->
    blurtwostage N M v = blurimmediate v M N.
Proof.
  let s := Ltime constr:("blurtwo") constr:("1000") constr:("3") in idtac_list s.  
Abort.


Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->
    blur_tiles_guarded v N M 64 64 = blurimmediate v M N.
Proof.
  let s := Ltime constr:("blurtiles") constr:("2000") constr:("10") in idtac_list s.  
Abort.

Goal forall W R0 (x w : list R),    
    consistent w (Z.to_nat R0, tt) ->
    consistent x (Z.to_nat R0, tt) ->
    (0 < W)%Z ->
    (Z.of_nat (length x) < W)%Z ->
    gather W x w = scatter W x w.
Proof.
  let s := Ltime constr:("gather") constr:("10") constr:("10") in idtac_list s.
Abort.      

Goal forall W R0 (x w : list R),    
    consistent w (Z.to_nat R0, tt) ->
    consistent x (Z.to_nat R0, tt) ->
    (0 < W)%Z ->
    (Z.of_nat (length x) < W)%Z ->
    scatter W x w = gather W x w.
Proof.  
  let s := Ltime constr:("scatter") constr:("10") constr:("10") in idtac_list s.
Abort.      

Goal forall (c : (list R)) (n m : Z),
    (0 < n)%Z ->
    (-m+1 < n)%Z ->
    consistent c (Z.to_nat n,tt) ->
    conv4 c n m = conv1 c n m.
Proof.
  let s := Ltime constr:("conv4") constr:("100") constr:("10") in idtac_list s.
Abort.

Goal forall (c : (list R)) (n m : Z),
    (0 < n)%Z ->
    (-m+1 < n)%Z ->
    consistent c (Z.to_nat n,tt) ->
    conv1 c n m = conv4 c n m.
Proof.
  let s := Ltime constr:("conv1") constr:("100") constr:("10") in idtac_list s.
Abort.

Goal forall A B K W RR (w : list (list R)) (x : list R),
    (0 < K)%Z ->
    (0 < W)%Z ->
    (0 < RR)%Z ->    
    consistent w (A,(B,tt))->
    consistent x (Z.to_nat K,tt) ->
    im2colminilifted K W RR w x = im2colmini K W RR w x.
Proof.
  let s := Ltime constr:("im2collifted") constr:("50") constr:("10") in idtac_list s.
Abort.      

Goal forall A B K W RR (w : list (list R)) (x : list R),
    (0 < K)%Z ->
    (0 < W)%Z ->
    (0 < RR)%Z ->    
    consistent w (A,(B,tt))->
    consistent x (Z.to_nat K,tt) ->
    im2colmini K W RR w x = im2colminilifted K W RR w x.
Proof.
  let s := Ltime constr:("im2col") constr:("50") constr:("10") in idtac_list s.
Abort.      

