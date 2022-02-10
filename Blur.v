From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import omega.PreOmega.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Reals.Reals.

Import ListNotations.

From ATL Require Import ATL Common Reshape Tactics LetLifting Div GenPushout
     CommonTactics.

Set Warnings "-omega-is-deprecated,-deprecated".
Definition pipeline {X} `{TensorElem X}
           n (f : list X) :=
  tlet buf := GEN [ i < n ] f _[i] in
        GEN [ i < n ] (|[ 0 <=? i-1 ]| buf _[i-1]) <+> buf _[i].

Example pipeline_schedule {X} `{TensorElem X} :
  forall (f : list X) n s m k,
    { prog |
      consistent f (m,s) ->
      (1 < n)%Z ->
      0 < k ->
      pipeline n f = prog }.
Proof.
  reschedule.
  unfold pipeline.

  inline let_binding.

  rw @get_gen_some.
  rw @get_gen_some.

  wrapid^ @flatten_trunc_tile_id around (GEN [ _ < _ ] _) with k.

  inline tile.

  rw<- @gp_iverson.
  rw @ll_get.
  rw @ll_iverson_.

  rw @get_gen_some.

  rw @lbind_helper for (fun x => |[ _ * Z.of_nat k + _ <? n]| x).

  rw @ll_gen.
  
  done.
Qed.

(* Breadth First
 * Compute and store every required point in blurx before evaluating any points
 * in out; lots of parallelism but little locality *)
Definition blurtwostage {X} `{TensorElem X}
           N M (v : list (list X)) : list (list X) :=
  tlet blurx' :=
    GEN [ y < Z.of_nat (N + 2) ]
        GEN [ x < Z.of_nat M ]
        (|[ (0<=?y-1) && (y-1<? Z.of_nat N) ]|
        (|[ 0 <=? x - 1 ]| v _[ y-1; x - 1]) <+>
        v _[ y-1; x] <+>
        (|[ x + 1 <? Z.of_nat M ]| v _[ y-1; x + 1]))
    in
      GEN [ y < Z.of_nat N ]
      GEN [ x < Z.of_nat M ]
      (blurx' _[ y; x] <+>
       blurx' _[ y+1; x] <+>
       blurx' _[ y+2; x]).

Definition blurtwostage_partition {X} `{TensorElem X}
           N M (v : list (list X)) : list (list X) :=
  tlet blurx' :=
    (GEN [ y < 1 ]
        GEN [ x < Z.of_nat M ]
        (|[(0<=?y-1) && (y-1 <? Z.of_nat N) ]|
        ((v _[ y-1; x - 1]) <+>
                            v _[ y-1; x]))
    )
      <++>
    (GEN [ 1 <= y < Z.of_nat (N+1) ]
         (GEN [ x < 1 ]
        ((|[0<=?x-1]| v _[y-1;x-1]) <+>
         v _[ y-1; x] <+>
        (|[x+1<? Z.of_nat M]| v _[ y-1; x + 1]) ))
         <++>
         (GEN [ 1 <= x < Z.of_nat (M-1) ]
        ((v _[ y-1; x - 1]) <+>
        v _[ y-1; x] <+>
        (v _[ y-1; x + 1])))
         <++>
         (GEN [ Z.of_nat M - 1 <= x < Z.of_nat M ]
              ((|[0<=?x-1]| v _[y-1;x-1]) <+>
         v _[ y-1; x] <+>
        (|[x+1<? Z.of_nat M]| v _[ y-1; x + 1]) )
         )         
    )
    <++>
    (GEN [ Z.of_nat N + 1 <= y < Z.of_nat N + 2 ]
         GEN [ x < Z.of_nat M ]
        (|[ (0<=?y-1) && (y-1 <? Z.of_nat N) ]|
        ((v _[ y-1; x - 1]) <+>
                            v _[ y-1; x]))
         
        )
    in
      GEN [ y < Z.of_nat N ]
      GEN [ x < Z.of_nat M ]
      (blurx' _[ y; x] <+>
       blurx' _[ y+1; x] <+>
       blurx' _[ y+2; x]).

(* Total Fusion
 * Compute each pixel independently to maximize locality but perform many
 * redundant computations *)
Definition blurimmediate {X} `{TensorElem X}
           n m (v : list (list X)) : list (list X) :=
  GEN [ y < Z.of_nat n ]
      GEN [ x2 < Z.of_nat m ]
      (|[ (0 <=? y - 1) && (y-1 <? Z.of_nat n) ]|
       (|[ 0 <=? x2 - 1 ]|
        v _[ y - 1; x2 - 1])
         <+> v _[ y - 1; x2]
         <+> (|[ x2 + 1 <? Z.of_nat m ]|
              v _[ y - 1; x2 + 1]))
      <+> (|[ 0 <=? y ]| (|[ 0 <=? x2 - 1 ]|
            v _[ y; x2 - 1])
             <+> v _[ y; x2]
             <+> (|[ x2 + 1 <? Z.of_nat m ]|
                  v _[ y; x2 + 1])) <+>
      (|[ (0 <=? y+1) && (y + 1 <? Z.of_nat n) ]|
       (|[ 0 <=? x2 - 1 ]|
        v _[ y + 1; x2 - 1])
         <+> v _[ y + 1; x2]
         <+> (|[ x2 + 1 <? Z.of_nat m ]|
              v _[ y + 1; x2 + 1])).

Definition blurimmediate_isolate {X} `{TensorElem X}
           n m (l : list (list X)) :=
    (GEN [ y < 1 ]
   GEN [ x2 < Z.of_nat m ]
   (|[ 0 <=? y - 1 ]| (|[ 0 <=? x2 - 1 ]| l _[ y - 1; x2 - 1]) <+> l _[ y - 1; x2] <+>
                      (|[ x2 + 1 <? Z.of_nat m ]| l _[ y - 1; x2 + 1])) <+>
   ((|[ 0 <=? x2 - 1 ]| l _[ y; x2 - 1]) <+> l _[ y; x2] <+>
    (|[ x2 + 1 <? Z.of_nat m ]| l _[ y; x2 + 1])) <+>
   ((|[ 0 <=? x2 - 1 ]| l _[ y + 1; x2 - 1]) <+> l _[ y + 1; x2] <+>
    (|[ x2 + 1 <? Z.of_nat m ]| l _[ y + 1; x2 + 1]))) <++>
  transpose
    (transpose
       (GEN [ 1 <= i < Z.of_nat (n - 1) ]
        GEN [ x2 < 1 ]
        (|[ 0 <=? x2 - 1 ]| l _[ i - 1; x2 - 1]) <+> l _[ i - 1; x2] <+>
        l _[ i - 1; x2 + 1] <+>
        ((|[ 0 <=? x2 - 1 ]| l _[ i; x2 - 1]) <+> l _[ i; x2] <+> l _[ i; x2 + 1]) <+>
        ((|[ 0 <=? x2 - 1 ]| l _[ i + 1; x2 - 1]) <+> l _[ i + 1; x2] <+>
         l _[ i + 1; x2 + 1])) <++>
     transpose
       (GEN [ 1 <= i < Z.of_nat (n - 1) ]
        GEN [ 1 <= x2 < Z.of_nat (m - 1) ]
        l _[ i - 1; x2 - 1] <+> l _[ i - 1; x2] <+> l _[ i - 1; x2 + 1] <+>
        (l _[ i; x2 - 1] <+> l _[ i; x2] <+> l _[ i; x2 + 1]) <+>
        (l _[ i + 1; x2 - 1] <+> l _[ i + 1; x2] <+> l _[ i + 1; x2 + 1])) <++>
     transpose
       (GEN [ 1 <= i < Z.of_nat (n - 1) ]
        GEN [ Z.of_nat m - 1 <= x2 < Z.of_nat m ]
        l _[ i - 1; x2 - 1] <+> l _[ i - 1; x2] <+>
        (|[ x2 + 1 <? Z.of_nat m ]| l _[ i - 1; x2 + 1]) <+>
        (l _[ i; x2 - 1] <+> l _[ i; x2] <+>
         (|[ x2 + 1 <? Z.of_nat m ]| l _[ i; x2 + 1])) <+>
        (l _[ i + 1; x2 - 1] <+> l _[ i + 1; x2]) <+>
        (|[ x2 + 1 <? Z.of_nat m ]| l _[ i + 1; x2 + 1]))) <++>
  (GEN [ Z.of_nat n - 1 <= y < Z.of_nat n ]
   GEN [ x2 < Z.of_nat m ]
   (|[ 0 <=? x2 - 1 ]| l _[ y - 1; x2 - 1]) <+> l _[ y - 1; x2] <+>
   (|[ x2 + 1 <? Z.of_nat m ]| l _[ y - 1; x2 + 1]) <+>
   ((|[ 0 <=? x2 - 1 ]| l _[ y; x2 - 1]) <+> l _[ y; x2] <+>
    (|[ x2 + 1 <? Z.of_nat m ]| l _[ y; x2 + 1])) <+>
   (|[ y + 1 <? Z.of_nat n ]| (|[ 0 <=? x2 - 1 ]| l _[ y + 1; x2 - 1]) <+>
                              l _[ y + 1; x2] <+>
                              (|[ x2 + 1 <? Z.of_nat m ]| l _[ y + 1; x2 + 1]))).
Definition blurimmediate_partition {X} `{TensorElem X}
           n m (v : list (list X)) : list (list X) :=
 (GEN [ y < 1 ]
      GEN [ x2 < Z.of_nat m ]
      (|[0<=?y-1]|
       ((|[0<=?x2-1]| v _[y-1;x2-1]) <+> v _[y-1;x2] <+> (|[x2+1<?Z.of_nat m]| v _[y-1;x2+1]))) <+>
 ((|[ 0 <=? x2 - 1 ]| v _[ y; x2 - 1]) <+> v _[ y; x2] <+>
  (|[ x2 + 1 <? Z.of_nat m ]| v _[ y; x2 + 1])) <+>
 ((|[ 0 <=? x2 - 1 ]| v _[ y + 1; x2 - 1]) <+> v _[ y + 1; x2] <+>
  (|[ x2 + 1 <? Z.of_nat m ]| v _[ y + 1; x2 + 1])))
<++>
(GEN [ 1 <= y < Z.of_nat (n - 1) ]

     (GEN [ x2 < 1 ]
      ((|[ 0<=?x2-1 ]| v _[y-1;x2-1]) <+> v _[ y - 1; x2]
         <+> (v _[ y - 1; x2 + 1]))
      <+> ((|[ 0<=?x2-1 ]| v _[y;x2-1]) <+> v _[ y; x2]
             <+> (v _[ y; x2 + 1])) <+>
      ((|[ 0<=?x2-1 ]| v _[y+1;x2-1]) <+> v _[ y + 1; x2]
         <+> (v _[ y + 1; x2 + 1])))
     <++>
      (GEN [ 1 <= x2 < Z.of_nat (m-1) ]
      ((v _[ y - 1; x2 - 1])
         <+> v _[ y - 1; x2]
         <+> (v _[ y - 1; x2 + 1]))
      <+> ((v _[ y; x2 - 1])
             <+> v _[ y; x2]
             <+> (v _[ y; x2 + 1])) <+>
      ((v _[ y + 1; x2 - 1])
         <+> v _[ y + 1; x2]
         <+> (v _[ y + 1; x2 + 1])))
      <++>
      (GEN [ Z.of_nat m - 1 <= x2 < Z.of_nat m ]
      ((v _[ y - 1; x2 - 1])
         <+> v _[ y - 1; x2] <+> (|[x2+1<?Z.of_nat m]| v _[y-1;x2+1]))
      <+> ((v _[ y; x2 - 1])
             <+> v _[ y; x2] <+> (|[x2+1<?Z.of_nat m]| v _[y;x2+1])) <+>
      ((v _[ y + 1; x2 - 1])
         <+> v _[ y + 1; x2]) <+> (|[x2+1<?Z.of_nat m]| v _[y+1;x2+1]))
      
)
<++>
(GEN [ Z.of_nat n - 1 <= y < Z.of_nat n ]
 GEN [ x2 < Z.of_nat m ]
 (|[ 0 <=? x2 - 1 ]| v _[ y - 1; x2 - 1]) <+> v _[ y - 1; x2] <+>
 (|[ x2 + 1 <? Z.of_nat m ]| v _[ y - 1; x2 + 1]) <+>
 ((|[ 0 <=? x2 - 1 ]| v _[ y; x2 - 1]) <+> v _[ y; x2] <+>
  (|[ x2 + 1 <? Z.of_nat m ]| v _[ y; x2 + 1])) <+>
(|[y+1<?Z.of_nat n]|
       ((|[0<=?x2-1]| v _[y+1;x2-1]) <+> v _[y+1;x2] <+> (|[x2+1<?Z.of_nat m]| v _[y+1;x2+1]))))
 .

(* Tiles *)

Definition blur_tiles_guarded {X} `{TensorElem X}
           (n_k m_k : nat) n m (l : list (list X)) :=
  (GEN [ y < 1 ]
   GEN [ x2 < Z.of_nat m ]
   (|[ 0 <=? y - 1 ]| (|[ 0 <=? x2 - 1 ]| l _[ y - 1; x2 - 1]) <+> l _[ y - 1; x2] <+>
                      (|[ x2 + 1 <? Z.of_nat m ]| l _[ y - 1; x2 + 1])) <+>
   ((|[ 0 <=? x2 - 1 ]| l _[ y; x2 - 1]) <+> l _[ y; x2] <+>
    (|[ x2 + 1 <? Z.of_nat m ]| l _[ y; x2 + 1])) <+>
   ((|[ 0 <=? x2 - 1 ]| l _[ y + 1; x2 - 1]) <+> l _[ y + 1; x2] <+>
    (|[ x2 + 1 <? Z.of_nat m ]| l _[ y + 1; x2 + 1]))) <++>
  transpose
    (transpose
       (GEN [ 1 <= i < Z.of_nat (n - 1) ]
        GEN [ x2 < 1 ]
        (|[ 0 <=? x2 - 1 ]| l _[ i - 1; x2 - 1]) <+> l _[ i - 1; x2] <+>
        l _[ i - 1; x2 + 1] <+>
        ((|[ 0 <=? x2 - 1 ]| l _[ i; x2 - 1]) <+> l _[ i; x2] <+> l _[ i; x2 + 1]) <+>
        ((|[ 0 <=? x2 - 1 ]| l _[ i + 1; x2 - 1]) <+> l _[ i + 1; x2] <+>
         l _[ i + 1; x2 + 1])) <++>
     transpose
       (flatten_trunc (n - 1 - 1)
          ((GEN [ i < (Z.of_nat (n - 1) - 1) / Z.of_nat n_k ]
            transpose
              (flatten_trunc (m - 1 - 1)
                 ((GEN [ i0 < Z.of_nat (m - 1 - 1) / Z.of_nat m_k ]
                   (tlet x2
                    := GEN [ i1 < Z.of_nat (n_k + 2) ]
                    GEN [ i2 < Z.of_nat m_k ]
                    l _[ i * Z.of_nat n_k + i1; i0 * Z.of_nat m_k + i2] <+>
                    l _[ i * Z.of_nat n_k + i1; i0 * Z.of_nat m_k + i2 + 1] <+>
                    l _[ i * Z.of_nat n_k + i1; i0 * Z.of_nat m_k + i2 + 2]
                    in transpose
                         (GEN [ i1 < Z.of_nat n_k ]
                          GEN [ i2 < Z.of_nat m_k ]
                          x2 _[ i1; i2] <+> x2 _[ i1 + 1; i2] <+> x2 _[ i1 + 2; i2]))) <++>
                  (GEN [ Z.of_nat (m - 1 - 1) / Z.of_nat m_k <= i0 < 
                    Z.of_nat (m - 1 - 1) / Z.of_nat m_k +
                    (Z.of_nat (m - 1 - 1) mod Z.of_nat m_k) // (Z.of_nat m_k) ]
                   GEN [ i1 < Z.of_nat m_k ]
                   GEN [ i2 < Z.of_nat n_k ]
                   (|[ i0 * Z.of_nat m_k + i1 <? Z.of_nat (m - 1 - 1) ]|
                     (|[ i * Z.of_nat n_k + i2 <? Z.of_nat (n - 1) - 1 ]|
                       l _[ i * Z.of_nat n_k + i2; i0 * Z.of_nat m_k + i1] <+>
                       l _[ i * Z.of_nat n_k + i2; i0 * Z.of_nat m_k + i1 + 1] <+>
                       l _[ i * Z.of_nat n_k + i2; i0 * Z.of_nat m_k + i1 + 1 + 1] <+>
                       (l _[ i * Z.of_nat n_k + i2 + 1; i0 * Z.of_nat m_k + i1] <+>
                        l _[ i * Z.of_nat n_k + i2 + 1; i0 * Z.of_nat m_k + i1 + 1] <+>
                        l _[ i * Z.of_nat n_k + i2 + 1;
                        i0 * Z.of_nat m_k + i1 + 1 + 1]) <+>
                       (l _[ i * Z.of_nat n_k + i2 + 1 + 1; i0 * Z.of_nat m_k + i1] <+>
                        l _[ i * Z.of_nat n_k + i2 + 1 + 1;
                        i0 * Z.of_nat m_k + i1 + 1] <+>
                        l _[ i * Z.of_nat n_k + i2 + 1 + 1;
                        i0 * Z.of_nat m_k + i1 + 1 + 1]))))))) <++>
           (GEN [ (Z.of_nat (n - 1) - 1) / Z.of_nat n_k <= i < 
             (Z.of_nat (n - 1) - 1) / Z.of_nat n_k +
             ((Z.of_nat (n - 1) - 1) mod Z.of_nat n_k) // (Z.of_nat n_k) ]
            transpose
              (flatten_trunc (m - 1 - 1)
                 (GEN [ i0 < Z.of_nat (m - 1 - 1) / Z.of_nat m_k +
                             (Z.of_nat (m - 1 - 1) mod Z.of_nat m_k) //
                             (Z.of_nat m_k) ]
                  GEN [ i1 < Z.of_nat m_k ]
                  GEN [ i2 < Z.of_nat n_k ]
                  (|[ i0 * Z.of_nat m_k + i1 <? Z.of_nat (m - 1 - 1) ]|
                    (|[ i * Z.of_nat n_k + i2 <? Z.of_nat (n - 1) - 1 ]|
                      l _[ i * Z.of_nat n_k + i2; i0 * Z.of_nat m_k + i1] <+>
                      l _[ i * Z.of_nat n_k + i2; i0 * Z.of_nat m_k + i1 + 1] <+>
                      l _[ i * Z.of_nat n_k + i2; i0 * Z.of_nat m_k + i1 + 1 + 1] <+>
                      (l _[ i * Z.of_nat n_k + i2 + 1; i0 * Z.of_nat m_k + i1] <+>
                       l _[ i * Z.of_nat n_k + i2 + 1; i0 * Z.of_nat m_k + i1 + 1] <+>
                       l _[ i * Z.of_nat n_k + i2 + 1;
                       i0 * Z.of_nat m_k + i1 + 1 + 1]) <+>
                      (l _[ i * Z.of_nat n_k + i2 + 1 + 1; i0 * Z.of_nat m_k + i1] <+>
                       l _[ i * Z.of_nat n_k + i2 + 1 + 1;
                       i0 * Z.of_nat m_k + i1 + 1] <+>
                       l _[ i * Z.of_nat n_k + i2 + 1 + 1;
                       i0 * Z.of_nat m_k + i1 + 1 + 1])))))))) <++>
     transpose
       (GEN [ 1 <= i < Z.of_nat (n - 1) ]
        GEN [ Z.of_nat m - 1 <= x2 < Z.of_nat m ]
        l _[ i - 1; x2 - 1] <+> l _[ i - 1; x2] <+>
        (|[ x2 + 1 <? Z.of_nat m ]| l _[ i - 1; x2 + 1]) <+>
        (l _[ i; x2 - 1] <+> l _[ i; x2] <+>
         (|[ x2 + 1 <? Z.of_nat m ]| l _[ i; x2 + 1])) <+>
        (l _[ i + 1; x2 - 1] <+> l _[ i + 1; x2]) <+>
        (|[ x2 + 1 <? Z.of_nat m ]| l _[ i + 1; x2 + 1]))) <++>
  (GEN [ Z.of_nat n - 1 <= y < Z.of_nat n ]
   GEN [ x2 < Z.of_nat m ]
   (|[ 0 <=? x2 - 1 ]| l _[ y - 1; x2 - 1]) <+> l _[ y - 1; x2] <+>
   (|[ x2 + 1 <? Z.of_nat m ]| l _[ y - 1; x2 + 1]) <+>
   ((|[ 0 <=? x2 - 1 ]| l _[ y; x2 - 1]) <+> l _[ y; x2] <+>
    (|[ x2 + 1 <? Z.of_nat m ]| l _[ y; x2 + 1])) <+>
   (|[ y + 1 <? Z.of_nat n ]| (|[ 0 <=? x2 - 1 ]| l _[ y + 1; x2 - 1]) <+>
                              l _[ y + 1; x2] <+>
                              (|[ x2 + 1 <? Z.of_nat m ]| l _[ y + 1; x2 + 1]))).
  
Hint Unfold blur_tiles_guarded blurimmediate blurimmediate_partition
     blurtwostage blurtwostage_partition blurimmediate_isolate : examples.

Definition fusion_no_boundary {X} `{TensorElem X}
  n m v :=
  GEN [ 1 <= i < Z.of_nat (n - 1) ]
  GEN [ 1 <= x2 < Z.of_nat (m - 1) ]
  v _[ i - 1; x2 - 1] <+> v _[ i - 1; x2] <+>
  v _[ i - 1; x2 + 1] <+>
  (v _[ i; x2 - 1] <+> v _[ i; x2] <+>
   v _[ i; x2 + 1]) <+>
  (v _[ i + 1; x2 - 1] <+> v _[ i + 1; x2] <+>
     v _[ i + 1; x2 + 1]).

Definition tile_no_boundary {X} `{TensorElem X}
           n_k m_k n m l :=
  flatten_trunc (n - 1 - 1)
    ((GEN [ i < (Z.of_nat (n - 1) - 1) / Z.of_nat n_k ]
      transpose
        (flatten_trunc (m - 1 - 1)
           ((GEN [ i0 < Z.of_nat (m - 1 - 1) / Z.of_nat m_k ]
             (tlet x2
              := GEN [ i1 < Z.of_nat (n_k + 2) ]
              GEN [ i2 < Z.of_nat m_k ]
              l _[ i * Z.of_nat n_k + i1; i0 * Z.of_nat m_k + i2] <+>
              l _[ i * Z.of_nat n_k + i1; i0 * Z.of_nat m_k + i2 + 1] <+>
              l _[ i * Z.of_nat n_k + i1; i0 * Z.of_nat m_k + i2 + 2]
              in transpose
                   (GEN [ i1 < Z.of_nat n_k ]
                    GEN [ i2 < Z.of_nat m_k ]
                    x2 _[ i1; i2] <+> x2 _[ i1 + 1; i2] <+> x2 _[ i1 + 2; i2]))) <++>
            (GEN [ Z.of_nat (m - 1 - 1) / Z.of_nat m_k <= i0 < 
              Z.of_nat (m - 1 - 1) / Z.of_nat m_k +
              (Z.of_nat (m - 1 - 1) mod Z.of_nat m_k) // (Z.of_nat m_k) ]
             GEN [ i1 < Z.of_nat m_k ]
             GEN [ n' < Z.of_nat n_k ]
             (|[ i0 * Z.of_nat m_k + i1 <? Z.of_nat (m - 1 - 1) ]|
               (|[ i * Z.of_nat n_k + n' <? Z.of_nat (n - 1) - 1 ]|
                 l _[ 1 + (i * Z.of_nat n_k + n') - 1;
                 1 + (i0 * Z.of_nat m_k + i1) - 1] <+>
                 l _[ 1 + (i * Z.of_nat n_k + n') - 1; 1 + (i0 * Z.of_nat m_k + i1)] <+>
                 l _[ 1 + (i * Z.of_nat n_k + n') - 1;
                 1 + (i0 * Z.of_nat m_k + i1) + 1] <+>
                 (l _[ 1 + (i * Z.of_nat n_k + n');
                  1 + (i0 * Z.of_nat m_k + i1) - 1] <+>
                  l _[ 1 + (i * Z.of_nat n_k + n'); 1 + (i0 * Z.of_nat m_k + i1)] <+>
                  l _[ 1 + (i * Z.of_nat n_k + n');
                  1 + (i0 * Z.of_nat m_k + i1) + 1]) <+>
                 (l _[ 1 + (i * Z.of_nat n_k + n') + 1;
                  1 + (i0 * Z.of_nat m_k + i1) - 1] <+>
                  l _[ 1 + (i * Z.of_nat n_k + n') + 1;
                  1 + (i0 * Z.of_nat m_k + i1)] <+>
                  l _[ 1 + (i * Z.of_nat n_k + n') + 1;
                  1 + (i0 * Z.of_nat m_k + i1) + 1]))))))) <++>
     (GEN [ (Z.of_nat (n - 1) - 1) / Z.of_nat n_k <= i < 
       (Z.of_nat (n - 1) - 1) / Z.of_nat n_k +
       ((Z.of_nat (n - 1) - 1) mod Z.of_nat n_k) // (Z.of_nat n_k) ]
      transpose
        (flatten_trunc (m - 1 - 1)
           (GEN [ i0 < Z.of_nat (m - 1 - 1) / Z.of_nat m_k +
                       (Z.of_nat (m - 1 - 1) mod Z.of_nat m_k) // (Z.of_nat m_k) ]
            GEN [ i1 < Z.of_nat m_k ]
            GEN [ n' < Z.of_nat n_k ]
            (|[ i0 * Z.of_nat m_k + i1 <? Z.of_nat (m - 1 - 1) ]|
              (|[ i * Z.of_nat n_k + n' <? Z.of_nat (n - 1) - 1 ]|
                l _[ 1 + (i * Z.of_nat n_k + n') - 1;
                1 + (i0 * Z.of_nat m_k + i1) - 1] <+>
                l _[ 1 + (i * Z.of_nat n_k + n') - 1; 1 + (i0 * Z.of_nat m_k + i1)] <+>
                l _[ 1 + (i * Z.of_nat n_k + n') - 1;
                1 + (i0 * Z.of_nat m_k + i1) + 1] <+>
                (l _[ 1 + (i * Z.of_nat n_k + n'); 1 + (i0 * Z.of_nat m_k + i1) - 1] <+>
                 l _[ 1 + (i * Z.of_nat n_k + n'); 1 + (i0 * Z.of_nat m_k + i1)] <+>
                 l _[ 1 + (i * Z.of_nat n_k + n'); 1 + (i0 * Z.of_nat m_k + i1) + 1]) <+>
                (l _[ 1 + (i * Z.of_nat n_k + n') + 1;
                 1 + (i0 * Z.of_nat m_k + i1) - 1] <+>
                 l _[ 1 + (i * Z.of_nat n_k + n') + 1; 1 + (i0 * Z.of_nat m_k + i1)] <+>
                 l _[ 1 + (i * Z.of_nat n_k + n') + 1;
                        1 + (i0 * Z.of_nat m_k + i1) + 1]))))))).

Hint Unfold fusion_no_boundary tile_no_boundary : examples.
  
Example total_fusion_to_tiled {X} `{TensorElem X} :
  forall n m (v : list (list X)) s n_k m_k,
    { prog |
      2 < n ->
      2 < m ->
      1 < n_k ->
      1 < m_k ->
      consistent v (n,(m,s)) ->
      blurimmediate_partition n m v = prog }.
Proof.
  reschedule.

  etransitivity.
  apply fuse_eq_l.
  apply fuse_eq_r.
  etransitivity.
  match goal with |- ?prog = _ => erewrite <- transpose_transpose_id with
      (V := prog) end.
  reflexivity. consistent_shape. rewrite Nat2Z.inj_sub. simpl. lia.
  lia. assert (0 < m-1). lia. eassumption.
  rewrite Z2Nat.inj_sub.
  rewrite Z2Nat.inj_sub.
  repeat rewrite Nat2Z.id.
  zify. lia. lia. lia.
  rewrite Z2Nat.inj_sub.
  rewrite Z2Nat.inj_sub.
  repeat rewrite Nat2Z.id.
  replace (m - (m- Z.to_nat 1)) with 1.
  rewrite Nat.sub_add. reflexivity. lia.
  zify. lia. lia. lia. zomega. rewrite Z2Nat.inj_sub.
  rewrite Nat2Z.id. zomega. lia.
  auto with crunch. lia. all: protect.
  rw @distrib_gen_concat.
  rw @distrib_gen_concat.

  apply transpose_eq.
  apply fuse_eq_l.
  apply fuse_eq_r.
  apply transpose_eq.

  wrapid @flatten_trunc_tile_id around (GEN [ _ <= _ < Z.of_nat (n-1) ] _)
    with n_k.

  rewrite Z2Nat.inj_sub.
  rewrite Nat2Z.id.
  replace (Z.to_nat 1) with 1.
  unfold tile.
  rw^ @consistent_length.
  rewrite Z2Nat.inj_sub.
  rewrite Nat2Z.id.
  replace (Z.to_nat 1) with 1.
  rewrite Nat2Z.inj_sub. replace (Z.of_nat 1) with 1%Z.
  rw @get_genr_some.
  rw @gp_genr_iverson.
  wrapid @transpose_transpose_id around (GEN [ _ < Z.of_nat n_k ] _).
  rw @unfold_inner_transpose.
  rw^ @consistent_length.
  rewrite Z2Nat.inj_sub.
  rewrite Nat2Z.id.
  replace (Z.to_nat 1) with 1.
  rw @get_gen_some.
  rw @get_genr_some.
  wrapid @flatten_trunc_tile_id around (GEN [ _ < Z.of_nat (m -1 -1)] _)
    with m_k.
  unfold tile.
  rw^ @consistent_length.
  rw @get_gen_some.
  rw^ @gp_gen_iverson.

  repeat rw^ (Z.add_comm 1%Z).
  repeat rw^ Z.add_simpl_r.
  
  remember ((x1::xs1)::xs) as l.

  rewrite ceil_floor_mod by zomega.
  rw ceil_floor_mod.

  etransitivity.
  erewrite split_gen_plus.
  reflexivity.
  apply Z.div_pos. zomega. lia.
  auto with crunch.
  intros. consistent_shape. all: protect.

  etransitivity.
  apply flatten_trunc_eq.
  apply fuse_eq_l.
  rw^ @split_gen_plus.
  reflexivity.
  reflexivity.

  etransitivity.
  apply flatten_trunc_eq.
  apply fuse_eq_l.
  apply gen_eq_bound; intros.
  apply transpose_eq.
  apply flatten_trunc_eq.
  apply fuse_eq_l.
  apply gen_eq_bound; intros.
  apply gen_eq_bound; intros.
  apply gen_eq_bound; intros.
  assert (i0* Z.of_nat m_k + i1 <? Z.of_nat (m-1-1) = true)%Z
    by (unbool; auto with crunch).
  rewrite H27. rewrite true_iverson.
  assert (i * Z.of_nat n_k + i2 <? Z.of_nat (n - 1) - 1 = true)%Z
    by (unbool; auto with crunch).
  rewrite H28. rewrite true_iverson.
  reflexivity.
  reflexivity.
  reflexivity.
  lazy beta.

  etransitivity.
  apply flatten_trunc_eq.
  apply fuse_eq_l.
  apply gen_eq_bound; intros.
  apply transpose_eq.
  apply flatten_trunc_eq.
  apply fuse_eq_l.
  apply gen_eq_bound; intros.
  
  repeat rw@ Z.add_simpl_l.

  rw @lbind_helper for (fun x => x <+> (_ <+> _ <+> _) <+> _).
  rw @ll_gen.
  rw @ll_gen.

  wrapid^ @transpose_transpose_id around (GEN [ _ < Z.of_nat m_k ] _).
  rw^ @tlet_f_bound_body.
  inline transpose.
  rw^ @consistent_length.
  rw^ @consistent_length.
  rw @get_gen_some.
  rw @get_gen_some.
  rw^ @get_gen_some.
  rw^ @get_gen_some.

  wrapid^ @trunc_r_pad_r_id around (GEN [ _ < Z.of_nat (n_k) ] _)
    with 2.
  rw^ @tlet_f_bound_body.
  inline pad_r.
  rw^ @get_gen_some.
  inline trunc_r.
  rw @get_gen_some.
  rw @lbind_helper for (fun x => |[ _ <? Z.of_nat n_k ]| x).
  rw @ll_gen.
  rw @let_let_flip.
  rw @get_gen_some.
  rw @gp_iverson.

  rw @lbind_helper for (fun x  => _ <+> x <+> (_ <+> _ <+> _)).
  rw @ll_gen.
  rw @ll_gen.
  wrapid^ @transpose_transpose_id around (GEN [ _ < Z.of_nat m_k ] _).
  rw^ @tlet_f_bound_body.
  inline transpose.
  rw^ @consistent_length.
  rw^ @consistent_length.
  rw @get_gen_some.
  rw @get_gen_some.
  rw^ @get_gen_some.
  rw^ @get_gen_some.

  wrapid^ @trunc_l_pad_l_id around (GEN [ _ < Z.of_nat n_k]
                                        GEN [ _ < Z.of_nat m_k ] _) with 1.
  rw^ @tlet_f_bound_body.
  inline pad_l.
  rw^ @get_gen_some.
  inline trunc_l.
  rw minus_plus.
  rw @get_gen_some. simpl.
  rw^ Z.add_sub_assoc.
  rw^ Zplus_minus.

  wrapid @trunc_r_pad_r_id around (GEN [ _ < Z.of_nat (n_k+1) ]
                                  |[ 1 <=? _ ]| GEN [ _ < Z.of_nat m_k ] _)
    with 1.
  rw^ @tlet_f_bound_body.
  inline pad_r.
  rw^ @get_gen_some.
  inline trunc_r.
  rw @get_gen_some.
  rw^ @lbind_helper for (fun x => |[ 1 <=? _ ]| x).
  rw @ll_iverson_.
  rw @ll_gen.
  rw @let_let_flip.
  rewrite <- Nat.add_assoc. simpl.
  rw^ Z.sub_add.
  rw^ @let_let_same.
  rw @get_gen_some.
  rw @gp_iverson.

  rw @lbind_helper for (fun x => (|[ _ ]| _) <+> _ <+> x).
  rw @ll_gen.
  rw @ll_gen.
  wrapid^ @transpose_transpose_id around (GEN [ _ < Z.of_nat m_k ] _).
  rw^ @tlet_f_bound_body.
  inline transpose.
  rw @consistent_length.
  rw @consistent_length.
  rw^ @get_gen_some.
  rw^ @get_gen_some.
  rw @get_gen_some.
  rw @get_gen_some.

  rw^<- Z.add_assoc.
  rw^<- Z.add_assoc.
  rw^<- Z.add_assoc.
  simpl.
  rw^<- Z.add_assoc.
  simpl.
  rw^<- Z.add_assoc.
  rw^<- Z.add_assoc.
  rw^<- Z.add_assoc.
  rw^<- Z.add_assoc.
  simpl.
  rw^ Z.add_assoc.
  rw^ Z.add_assoc.
  rw^ Z.add_assoc.
  rw^ Z.add_assoc.
  rw^ Z.add_assoc.
  
  rw^ @gen_trunc upto n_k at 2.
  rw^ @tlet_f_bound_body.
  rw^ Z.add_sub_assoc. simpl.
  rw^ Z.sub_add.
  rw^ Zplus_minus.
  inline trunc_l. simpl.
  rw @get_gen_some.
  rw minus_plus. simpl.

  rw^ @let_let_same.
  simpl_guard.
  simpl_guard.
  reflexivity.
  lazy beta.

  wrapid @transpose_transpose_id around (GEN [ _ < Z.of_nat m_k ] _).
  rw @unfold_inner_transpose.
  rw^ @consistent_length.
  rw @get_gen_some.
  rw @get_gen_some.
  
  reflexivity.
  reflexivity.
  reflexivity.

  rewrite Heql.
  reflexivity.

  done.
Qed.

Example twostageimmediate {X} `{TensorElem X} :
  forall (v : list (list X)) m n s k,
    { prog | 0 < k -> 0 < m -> 0 < n -> consistent v (n,(m,s)) ->
             blurtwostage n m v = prog}.
Proof.
  reschedule.

  unfold let_binding.

  rw @get_gen_some.
  rw @get_gen_some.
  rw @get_gen_some.
  rw @get_gen_some.
  rw @get_gen_some.
  rw @get_gen_some.

  rw^ Z.add_simpl_r.
  rw^<- Z.add_sub_assoc.
  simpl.
  simpl_guard.
  
  done.
Qed.

