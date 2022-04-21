From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import micromega.Lia.
From Coq Require Import Lists.List.
From Coq Require Import Reals.Reals.
Require Coq.derive.Derive.

Import ListNotations.

From ATL Require Import ATL Common Reshape Tactics LetLifting Div GenPushout
     CommonTactics Normalize.

Definition pipeline {X} `{TensorElem X}
           n (f : list X) :=
  tlet buf := GEN [ i < n ] f _[i] in
        GEN [ i < n ] (|[ 0 <=? i-1 ]| buf _[i-1]) <+> buf _[i].
Hint Unfold pipeline : examples.

Section Pipeline.
  Variables (f : list R) (n : Z) (m k : nat).
  Derive pipeline_sched SuchThat
         (consistent f (m,tt) ->
          (1 < n)%Z ->
          0 < k ->
          pipeline n f = pipeline_sched) As pipeline_correct.
  Proof.
    reschedule.

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
End Pipeline.
Hint Unfold pipeline_sched : examples.

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
Hint Unfold blurtwostage : examples.

Section two_to_part.
  Variables (X : Set) (H : TensorElem X) (N M : nat)
            (v : list (list X)) (s : @shape X _).
  Derive blurtwostage_partition SuchThat
         (2 < M ->
          0 < N ->
      consistent v (N,(M,s)) ->
      blurtwostage N M v = blurtwostage_partition) As twostagepart.
  Proof.
    reschedule.

    rw^ Nat2Z.inj_add. simpl.

    rw^ @split_gen upto (Z.of_nat N + 2)%Z at 1%Z.

    rw^ @split_genr upto (Z.of_nat N + 2)%Z at (Z.of_nat N + 1)%Z.

    etransitivity.
    apply tlet_eq_bound.
    apply concat_eq_r.
    rw^ split_gen upto (Z.of_nat M) at 1%Z.
    rw^ @split_genr upto (Z.of_nat M) at (Z.of_nat M - 1)%Z.
    reflexivity.

    simpl_guard.

    done.
  Qed.
End two_to_part.
Hint Unfold blurtwostage_partition : examples.
(* Total Fusion
 * Compute each pixel independently to maximize locality but perform many
 * redundant computations *)

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
Hint Unfold blurimmediate_isolate : examples.

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
Hint Unfold blurimmediate_partition : examples.

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
Hint Unfold fusion_no_boundary : examples.

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
Hint Unfold tile_no_boundary : examples.

Section total_tiled.
  Variables (X : Set) (H : TensorElem X)
            (v : list (list X)) (s : @shape X _) (n m n_k m_k : nat).
  Derive blur_tiles_guarded SuchThat
      (2 < n ->
      2 < m ->
      1 < n_k ->
      1 < m_k ->
      consistent v (n,(m,s)) ->
      blurimmediate_partition n m v = blur_tiles_guarded) As total_tiled.
  Proof.
    reschedule.

    wrapid^ @transpose_transpose_id around
                                    (GEN [ 1 <= _ < (Z.of_nat (n-1)) ] _).
    rw @distrib_gen_concat.
    rw @distrib_gen_concat.

    wrapid @flatten_trunc_tile_id around
           (GEN [ _ <= _ < Z.of_nat (n-1) ] GEN [ 1 <= _ < Z.of_nat (m-1)] _)
      with n_k.

    rw^ Z2Nat.inj_sub.
    rewrite Nat2Z.id.
    replace (Z.to_nat 1) with 1 by reflexivity.

    inline tile.
    rw @get_genr_some.
    rw @gp_genr_iverson.
    wrapid @transpose_transpose_id around (GEN [ _ < Z.of_nat n_k ] _).
    rw @unfold_inner_transpose.
    rw^ @consistent_length.
    rw^ Z2Nat.inj_sub.
    rewrite Nat2Z.id.
    replace (Z.to_nat 1) with 1 by reflexivity.
    rw @get_gen_some.
    rw @get_genr_some.
    wrapid @flatten_trunc_tile_id around (GEN [ _ < Z.of_nat (m -1 -1)] _)
      with m_k.
    inline tile.
    rw @get_gen_some.
    rw^ @gp_gen_iverson.    
    
    repeat rw^ (Z.add_comm 1%Z).
    repeat rw^ Z.add_simpl_r.
    remember ((x1::xs1)::xs) as l.

    rw^ ceil_floor_mod.
    rw^ (ceil_floor_mod (Z.of_nat (m-1-1))).

    rw^ @split_gen_plus.
    rw^ @split_gen_plus.

    simpl_guard.
    simpl_guard.

    rw @lbind_helper for
       (fun x =>
          x
            <+> ((_ _[_*Z.of_nat n_k + _ +1; _*Z.of_nat m_k + _]) <+> _ <+> _)
            <+> _).
    rw @ll_gen.
    rw @ll_gen.
    
    wrapid^ @transpose_transpose_id around (GEN [ _ < Z.of_nat m_k ] _).
    rw^ @tlet_f_bound_body.
    rw unfold_transpose around (GEN [ _ < _ ] _).
    rw @get_gen_some.
    rw @get_gen_some.
    rw @transpose_get_get.
    
    wrapid^ @trunc_r_pad_r_id around (GEN [ _ < Z.of_nat n_k ] _)
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

    rw @lbind_helper for
       (fun x  => (|[ _ <? Z.of_nat n_k]| _)
                    <+> x
                    <+> (_ <+> _ <+> _)).
    rw @ll_gen.
    rw @ll_gen.
    wrapid^ @transpose_transpose_id around
                                    (GEN [ _ < Z.of_nat m_k ] GEN [ _ < _ ] _).
    rw^ @tlet_f_bound_body.
    rw unfold_transpose around (GEN [ _ < _ ] _).
    rw @get_gen_some.
    rw @get_gen_some.
    rw @transpose_get_get.

    wrapid^ @trunc_l_pad_l_id around
                              (GEN [ _ < Z.of_nat n_k]
                                   GEN [ _ < Z.of_nat m_k ] _) with 1.
    rw^ @tlet_f_bound_body.
    inline pad_l.
    rw^ @get_gen_some.
    inline trunc_l.
    rw minus_plus.
    rw @get_gen_some. simpl.
    rw^ Z.add_sub_assoc.
    rw^ Zplus_minus.
    rw^ Z.sub_add.

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
    rw @lbind_helper for
       (fun x => (|[ _ ]| _)
                   <+> (|[ _ <? (Z.of_nat (n_k+1)) ]| _)
                   <+> x).
    rw @ll_gen.
    rw @ll_gen.
    wrapid^ @transpose_transpose_id around
                                    (GEN [ _ < Z.of_nat m_k ] _).
    rw^ @tlet_f_bound_body.
    rw unfold_transpose around (GEN [ _ < _ ] _).
    rw^ @get_gen_some.
    rw^ @get_gen_some.
    rw @transpose_get_get.

    repeat rw^<- (Zplus_assoc 1%Z 1%Z).
    simpl.    
    rw^ @gen_trunc upto n_k at 2.
    rw^ @tlet_f_bound_body.
    rw^ Z.add_sub_assoc. simpl.
    rw^ Z.sub_add.
    inline trunc_l. simpl.
    rw @get_gen_some.
    rw minus_plus. simpl.
    rw^ @let_let_same.
    
    simpl_guard.
    simpl_guard.

    wrapid @transpose_transpose_id around (GEN [ _ < Z.of_nat m_k ] _).
    rw @unfold_inner_transpose.
    rw^ @consistent_length.
    rw @get_gen_some.
    rw @get_gen_some.
   
    done.
  Qed.
End total_tiled.
Hint Unfold blur_tiles_guarded : examples.

Section fuse_twostage.
  Variables (X : Set) (H : TensorElem X)
            (v : list (list X)) (m n k : nat) (s : @shape X _).
  Derive blurimmediate SuchThat
         (0 < k -> 0 < m -> 0 < n -> consistent v (n,(m,s)) ->
          blurtwostage n m v = blurimmediate) As twostage_immediate.
  Proof.
    reschedule.

    inline let_binding.

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
End fuse_twostage.
Hint Unfold blurimmediate : examples.

Arguments blur_tiles_guarded {X H}.
Arguments blurimmediate {X H}.
Arguments blurtwostage_partition {X H}.

Goal forall v n m n_k m_k,
    blur_tiles_guarded v n m n_k m_k =
(GEN [ i < 1 ]
 GEN [ i0 < Z.of_nat m ]
 (|[ 0 <=? i - 1 ]| v _[ i - 1; i0 - 1] <+> v _[ i - 1; i0] <+> v _[ i - 1; i0 + 1]) <+>
 ((|[ 0 <=? i0 - 1 ]| v _[ i; i0 - 1]) <+> v _[ i; i0] <+>
  (|[ i0 + 1 <? Z.of_nat m ]| v _[ i; i0 + 1])) <+>
 ((|[ 0 <=? i0 - 1 ]| v _[ i + 1; i0 - 1]) <+> v _[ i + 1; i0] <+>
  (|[ i0 + 1 <? Z.of_nat m ]| v _[ i + 1; i0 + 1]))) <++>
transpose
  (transpose
     (GEN [ 1 <= i < Z.of_nat (n - 1) ]
      GEN [ x2 < 1 ]
      (|[ 0 <=? x2 - 1 ]| v _[ i - 1; x2 - 1]) <+> v _[ i - 1; x2] <+>
      v _[ i - 1; x2 + 1] <+>
      ((|[ 0 <=? x2 - 1 ]| v _[ i; x2 - 1]) <+> v _[ i; x2] <+> v _[ i; x2 + 1]) <+>
      ((|[ 0 <=? x2 - 1 ]| v _[ i + 1; x2 - 1]) <+> v _[ i + 1; x2] <+>
       v _[ i + 1; x2 + 1])) <++>
   transpose
     (flatten_trunc (n - 1 - 1)
        ((GEN [ i < (Z.of_nat (n - 1) - 1) / Z.of_nat n_k ]
          transpose
            (flatten_trunc (m - 1 - 1)
               ((GEN [ i0 < Z.of_nat (m - 1 - 1) / Z.of_nat m_k ]
                 (tlet x2
                  := GEN [ i1 < Z.of_nat (n_k + 2) ]
                  GEN [ i2 < Z.of_nat m_k ]
                  v _[ i * Z.of_nat n_k + i1; i0 * Z.of_nat m_k + i2] <+>
                  v _[ i * Z.of_nat n_k + i1; i0 * Z.of_nat m_k + i2 + 1] <+>
                  v _[ i * Z.of_nat n_k + i1; i0 * Z.of_nat m_k + i2 + 2]
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
                   v _[ i * Z.of_nat n_k + i2; i0 * Z.of_nat m_k + i1] <+>
                   v _[ i * Z.of_nat n_k + i2; i0 * Z.of_nat m_k + i1 + 1] <+>
                   v _[ i * Z.of_nat n_k + i2; i0 * Z.of_nat m_k + i1 + 2] <+>
                   (v _[ i * Z.of_nat n_k + i2 + 1; i0 * Z.of_nat m_k + i1] <+>
                    v _[ i * Z.of_nat n_k + i2 + 1; i0 * Z.of_nat m_k + i1 + 1] <+>
                    v _[ i * Z.of_nat n_k + i2 + 1; i0 * Z.of_nat m_k + i1 + 2]) <+>
                   (v _[ i * Z.of_nat n_k + i2 + 2; i0 * Z.of_nat m_k + i1] <+>
                    v _[ i * Z.of_nat n_k + i2 + 2; i0 * Z.of_nat m_k + i1 + 1] <+>
                    v _[ i * Z.of_nat n_k + i2 + 2; i0 * Z.of_nat m_k + i1 + 2])))))) <++>
         (GEN [ (Z.of_nat (n - 1) - 1) / Z.of_nat n_k <= i < 
           (Z.of_nat (n - 1) - 1) / Z.of_nat n_k +
           ((Z.of_nat (n - 1) - 1) mod Z.of_nat n_k) // (Z.of_nat n_k) ]
          transpose
            (flatten_trunc (m - 1 - 1)
               (GEN [ i0 < Z.of_nat (m - 1 - 1) / Z.of_nat m_k +
                           (Z.of_nat (m - 1 - 1) mod Z.of_nat m_k) // (Z.of_nat m_k) ]
                GEN [ i1 < Z.of_nat m_k ]
                GEN [ i2 < Z.of_nat n_k ]
                (|[ i0 * Z.of_nat m_k + i1 <? Z.of_nat (m - 1 - 1) ]|
                  (|[ i * Z.of_nat n_k + i2 <? Z.of_nat (n - 1) - 1 ]|
                    v _[ i * Z.of_nat n_k + i2; i0 * Z.of_nat m_k + i1] <+>
                    v _[ i * Z.of_nat n_k + i2; i0 * Z.of_nat m_k + i1 + 1] <+>
                    v _[ i * Z.of_nat n_k + i2; i0 * Z.of_nat m_k + i1 + 2] <+>
                    (v _[ i * Z.of_nat n_k + i2 + 1; i0 * Z.of_nat m_k + i1] <+>
                     v _[ i * Z.of_nat n_k + i2 + 1; i0 * Z.of_nat m_k + i1 + 1] <+>
                     v _[ i * Z.of_nat n_k + i2 + 1; i0 * Z.of_nat m_k + i1 + 2]) <+>
                    (v _[ i * Z.of_nat n_k + i2 + 2; i0 * Z.of_nat m_k + i1] <+>
                     v _[ i * Z.of_nat n_k + i2 + 2; i0 * Z.of_nat m_k + i1 + 1] <+>
                     v _[ i * Z.of_nat n_k + i2 + 2; i0 * Z.of_nat m_k + i1 + 2])))))))) <++>
   transpose
     (GEN [ 1 <= i < Z.of_nat (n - 1) ]
      GEN [ Z.of_nat m - 1 <= x2 < Z.of_nat m ]
      v _[ i - 1; x2 - 1] <+> v _[ i - 1; x2] <+>
      (|[ x2 + 1 <? Z.of_nat m ]| v _[ i - 1; x2 + 1]) <+>
      (v _[ i; x2 - 1] <+> v _[ i; x2] <+>
       (|[ x2 + 1 <? Z.of_nat m ]| v _[ i; x2 + 1])) <+>
      (v _[ i + 1; x2 - 1] <+> v _[ i + 1; x2]) <+>
      (|[ x2 + 1 <? Z.of_nat m ]| v _[ i + 1; x2 + 1]))) <++>
(GEN [ Z.of_nat n - 1 <= i < Z.of_nat n ]
 GEN [ i0 < Z.of_nat m ]
 (|[ 0 <=? i0 - 1 ]| v _[ i - 1; i0 - 1]) <+> v _[ i - 1; i0] <+>
 (|[ i0 + 1 <? Z.of_nat m ]| v _[ i - 1; i0 + 1]) <+>
 ((|[ 0 <=? i0 - 1 ]| v _[ i; i0 - 1]) <+> v _[ i; i0] <+>
  (|[ i0 + 1 <? Z.of_nat m ]| v _[ i; i0 + 1])) <+>
 (|[ i + 1 <? Z.of_nat n ]| v _[ i + 1; i0 - 1] <+> v _[ i + 1; i0] <+>
                            v _[ i + 1; i0 + 1])).
Proof. reflexivity. Qed.

Goal forall f n k, pipeline_sched f n k =
flatten_trunc (Z.to_nat n)
  (GEN [ i < n // (Z.of_nat k) ]
   (tlet x
    := GEN [ i0 < Z.of_nat k ]
    (|[ 0 <=? i * Z.of_nat k + i0 - 1 ]| f _[ i * Z.of_nat k + i0 - 1]) <+>
    f _[ i * Z.of_nat k + i0]
    in GEN [ n' < Z.of_nat k ]
           (|[ i * Z.of_nat k + n' <? n ]| x _[ n']))).
Proof. reflexivity. Qed.     

Goal forall v m n,
    blurimmediate v m n =
    GEN [ i < Z.of_nat n ]
        GEN [ i0 < Z.of_nat m ]
        (|[ 0 <=? i - 1 ]|
         (|[ 0 <=? i0 - 1 ]| v _[ i - 1; i0 - 1]) <+> v _[ i - 1; i0] <+>
         (|[ i0 + 1 <? Z.of_nat m ]| v _[ i - 1; i0 + 1])) <+>
        ((|[ 0 <=? i0 - 1 ]| v _[ i; i0 - 1]) <+> v _[ i; i0] <+>
           (|[ i0 + 1 <? Z.of_nat m ]| v _[ i; i0 + 1])) <+>
        (|[ i + 1 <? Z.of_nat n ]|
         (|[ 0 <=? i0 - 1 ]| v _[ i + 1; i0 - 1]) <+>
                             v _[ i + 1; i0] <+>
                             (|[ i0 + 1 <? Z.of_nat m ]| v _[ i + 1; i0 + 1])).
Proof. reflexivity. Qed.

Goal forall v M N,
    blurtwostage_partition N M v =
tlet blurx'
:= (GEN [ i < 1 ]
    GEN [ i0 < Z.of_nat M ]
    (|[ 0 <=? i - 1 ]| v _[ i - 1; i0 - 1] <+> v _[ i - 1; i0] <+>
                       v _[ i - 1; i0 + 1])) <++>
   ((GEN [ 1 <= i < Z.of_nat N + 1 ]
     (GEN [ i0 < 1 ]
      (|[ 0 <=? i0 - 1 ]| v _[ i - 1; i0 - 1]) <+> v _[ i - 1; i0] <+>
      v _[ i - 1; i0 + 1]) <++>
     ((GEN [ 1 <= i0 < Z.of_nat M - 1 ]
       v _[ i - 1; i0 - 1] <+> v _[ i - 1; i0] <+> v _[ i - 1; i0 + 1]) <++>
      (GEN [ Z.of_nat M - 1 <= i0 < Z.of_nat M ]
       v _[ i - 1; i0 - 1] <+> v _[ i - 1; i0] <+>
       (|[ i0 + 1 <? Z.of_nat M ]| v _[ i - 1; i0 + 1])))) <++>
    (GEN [ Z.of_nat N + 1 <= i < Z.of_nat N + 2 ]
     GEN [ i0 < Z.of_nat M ]
     (|[ i - 1 <? Z.of_nat N ]| v _[ i - 1; i0 - 1] <+> v _[ i - 1; i0] <+>
                                v _[ i - 1; i0 + 1])))
in GEN [ y < Z.of_nat N ]
GEN [ x < Z.of_nat M ]
blurx' _[ y; x] <+> blurx' _[ y + 1; x] <+> blurx' _[ y + 2; x]
.    
Proof. reflexivity. Qed.
