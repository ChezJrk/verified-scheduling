From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Zdiv.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import micromega.Zify.

Require Import Ltac2.Ltac2.
Require Import Ltac2.Option.

From ATL Require Import ATL Tactics Common CommonTactics Div GenPushout Reshape LetLifting.
From Codegen Require Import IdentParsing.

Open Scope string_scope.

Set Default Proof Mode "Classic".

Theorem trunc_r_gen {X} `{TensorElem X} : forall f n s k,
    (0 < n)%Z ->
    0 < k ->
    (Z.of_nat k < n)%Z ->
    (forall x, consistent (f x) s) ->
    trunc_r k (GEN [ i < n ] f i) = GEN [ i < Z.of_nat k ] f i.
Proof.
  unfold trunc_r.
  intros. rw @get_gen_some. reflexivity.
Qed.
(*
Theorem trunc_r_sum {X} `{TensorElem X} : forall f n s k,
    (0 < n)%Z ->
    0 < k ->
    (Z.of_nat k < n)%Z ->
    (forall x, consistent (f x) s) ->
    trunc_r k (SUM [ i < n ] f i) = SUM [ i < n ] (trunc_r k (f i)).
Proof.
  unfold trunc_r.
  intros.
  rw<- @get_sum.
  rw @sum_gen_swap.
  reflexivity.
Qed.
*)
Theorem trunc_r_guard {X} `{TensorElem X} : forall p e k,
    trunc_r k (|[ p ]| e) = |[ p ]| (trunc_r k e).
Proof.
  unfold trunc_r.
  intros.
  rw @gp_iverson.
  rw<- @gp_gen_iverson.
  reflexivity.
Qed.

Theorem normalize_gen {X} `{TensorElem X} : forall (l : list X) n s,
    consistent l (n,s) ->
    l = GEN [ i < Z.of_nat n ] l _[i].
Proof.
  intros.
  rewrite gen_get_id. auto.
  inversion H0.
  rewrite Nat2Z.id. auto.
Qed.

Theorem normalize_bin {X} `{TensorElem X} : forall (x y : list X) n s,
    consistent x (n,s) ->
    consistent y (n,s) ->
    tensor_add x y = GEN [ i < Z.of_nat n ] (x _[i]) <+> (y _[i]).
Proof.
  intros.
  unfold tensor_add.
  inversion H0. inversion H1. subst.
  rewrite H13. rewrite max_id.
  reflexivity.
Qed.

Theorem let_extensionality {X Y} `{TensorElem X} `{TensorElem Y} :
  forall (x : X) (f g : X -> Y) s,
    consistent x s ->
    (forall x, consistent x s -> f x = g x) ->
    let_binding x f = let_binding x g.
Proof.
  intros.
  unfold let_binding.
  apply H2. auto.
Qed.

Ltac normalize_rec :=
  repeat (unfold bin;
          lazymatch goal with
          | |- transpose _ = _ =>
            apply transpose_eq
          | |- (let_binding ?x ?f) = _ =>
            match type of x with
            | Z =>
              eapply tlet_eq_body; intros
            | ?tx =>
            let ex := fresh "ex" in
            let H := fresh "H" in
            evar (ex : tx);
            assert (x = ?ex) as H by
                  (normalize_rec);
            try rewrite H;
            eapply let_extensionality;
            [ consistent_shape; try reflexivity; eauto | intros ]
            end
          | |- GEN [ i < ?n ] @?f i = _ =>
            apply gen_eq_bound; intros
          | |- GEN [ _ <= _ < _ ] _ = _ =>
            apply genr_eq_bound; intros                                  
          | |- SUM [ i < ?n ] @?f i = _ =>
            apply sum_eq_bound; intros
          | |- (|[ _ ]| _) = _ =>
            apply iverson_weak
          | |- tensor_add ?x ?y = _ =>
            lift_evar;
            erewrite normalize_bin by
                (consistent_shape; eauto with crunch);
            drop_evar
          | |- (?a + ?b)%R = _ =>
             let ae := fresh "ae" in
             let Ha := fresh "Ha" in
             evar (ae : R);
             assert (a = ?ae) as Ha by normalize_rec;
             lift_evar;
             try rewrite Ha;
             drop_evar;
             let be := fresh "be" in
             let Hb := fresh "Hb" in
             evar (be : R);
             assert (b = ?be) as Hb by normalize_rec;
             lift_evar;
             try rewrite Hb;
             drop_evar;
             reflexivity
          | |- ?a <++> ?b = _ =>
             let ae := fresh "ae" in
             let Ha := fresh "Ha" in
             let t := type of a in
             evar (ae : t);
             assert (a = ?ae) as Ha by normalize_rec;
             lift_evar;
             try rewrite Ha;
             drop_evar;
             let be := fresh "be" in
             let Hb := fresh "Hb" in
             evar (be : t);
             assert (b = ?be) as Hb by normalize_rec;
             lift_evar;
             try rewrite Hb;
             drop_evar;
             reflexivity               
          | |- (?a * ?b)%R = _ =>
             let ae := fresh "ae" in
             let Ha := fresh "Ha" in
             evar (ae : R);
             assert (a = ?ae) as Ha by normalize_rec;
             lift_evar;
             try rewrite Ha;
             drop_evar;
             let be := fresh "be" in
             let Hb := fresh "Hb" in
             evar (be : R);
             assert (b = ?be) as Hb by normalize_rec;
             lift_evar;
             try rewrite Hb;
             drop_evar;
             reflexivity
          | |- trunc_r _ _ = _ =>
            apply trunc_r_eq
          | |- truncr _ _ = _ =>
            apply truncr_eq
          | |- truncl _ _ = _ =>
            apply truncl_eq
          | |- pad_l _ _ = _ =>
            apply pad_l_eq                  
          | |- pad_r _ _ = _ =>
            apply pad_r_eq                  
          | |- flatten_trunc _ _ = _ =>
            apply flatten_trunc_eq
          | |- flatten _ = _ =>
            apply flatten_eq                  
          | |- tile _  _ = _ =>
            apply tile_eq                  
          | |- transpose _ = _ =>
            apply transpose_eq
          | |- ?etc = _ =>
            lazymatch type of etc with
            | list _ =>
              lift_evar;
              erewrite (normalize_gen etc) by
                  (consistent_shape; eauto with crunch);
              drop_evar
            | _ => reflexivity
            end
          end).

Ltac normalize_types :=
  unfold bin; simpl;
  etransitivity; [ normalize_rec; auto with crunch | ]; simpl; lazy beta.

Ltac normalize_in_expr :=
  lazymatch goal with
  | |- ?v _[ _ ] = _ =>
    apply get_eq_index;
    normalize_in_expr
  | |- (?a * ?b)%R = _ =>
    let ae := fresh "ae" in
    let Ha := fresh "Ha" in
    evar (ae : R);
    assert (a = ?ae) as Ha by (normalize_in_expr; try reflexivity);
    lift_evar;
    try rewrite Ha;
    try clear Ha;
    try rewrite ll_mult_l;
    drop_evar;
    let be := fresh "be" in
    let Hb := fresh "Hb" in
    evar (be : R);
    assert (b = ?be) as Hb by (normalize_in_expr; try reflexivity);
    lift_evar;
    try rewrite Hb;
    try rewrite ll_mult_r;    
    try clear Hb;
    drop_evar;
    reflexivity
  | |- (?a / ?b)%R = _ =>
    let ae := fresh "ae" in
    let Ha := fresh "Ha" in
    evar (ae : R);
    assert (a = ?ae) as Ha by (normalize_in_expr; try reflexivity);
    lift_evar;
    try rewrite Ha;
    try rewrite ll_div_l;
    try clear Ha;
    drop_evar;
    let be := fresh "be" in
    let Hb := fresh "Hb" in
    evar (be : R);
    assert (b = ?be) as Hb by (normalize_in_expr; try reflexivity);
    lift_evar;
    try rewrite Hb;
    try rewrite ll_div_r;
    try clear Hb;
    drop_evar;
    reflexivity    
  | |- (?a + ?b)%R = _ =>
    let ae := fresh "ae" in
    let Ha := fresh "Ha" in
    evar (ae : R);
    assert (a = ?ae) as Ha by (normalize_in_expr; try reflexivity);
    lift_evar;
    try rewrite Ha;
    try rewrite ll_plus_l;
    try clear Ha;
    drop_evar;
    let be := fresh "be" in
    let Hb := fresh "Hb" in
    evar (be : R);
    assert (b = ?be) as Hb by (normalize_in_expr; try reflexivity);
    lift_evar;
    try rewrite Hb;
    try rewrite ll_plus_r;
    try clear Hb;
    drop_evar;
    reflexivity    
  | |- (|[ ?p ]| ?e) = _ =>
      let ee := fresh "ee" in
      let He := fresh "He" in
      let ty := type of e in
      evar (ee : ty);
      assert (e = ?ee) as He by (normalize_in_expr; try reflexivity);
      lift_evar;
      try rewrite He;
      drop_evar;
      match goal with
      | |- ?ex = _ => replace ex with (tlet x := ex in x) by
          (unfold let_binding; reflexivity)
      end;
      reflexivity
  | |- ?v = _ =>
    match v with
    | _ => is_var v; reflexivity
    | _ => (* Not the recursive case and not a var *)
      replace v with (tlet x := v in x) by
          (unfold let_binding; reflexivity)
    end
  end.             

Ltac normalize_get :=
  match goal with
  | |- flatten _ = _ =>
    apply flatten_eq;
    normalize_get
  | |- tile _ _ = _ =>
    apply tile_eq;
    normalize_get
  | |- flatten_trunc _ _ = _ =>
    apply flatten_trunc_eq;
    normalize_get
  | |- transpose _ = _ =>
    apply transpose_eq;
    normalize_get
  | |- pad_r _ _ = _ =>
    apply pad_r_eq;
    normalize_get
  | |- pad_l _ _ = _ =>
    apply pad_l_eq;
    normalize_get
  | |- trunc_l _ _ = _ =>
    apply trunc_l_eq;
    normalize_get
  | |- trunc_r _ _ = _ =>
    apply trunc_r_eq;
    normalize_get            
  | |- truncr _ _ = _ =>
    apply truncr_eq;
    normalize_get            
  | |- truncl _ _ = _ =>
    apply truncl_eq;
    normalize_get            
  | |- GEN [ _ < _ ] _ = _ =>
    apply gen_eq_bound; intros;
    normalize_get
  | |- GEN [ _ <= _ < _ ] _ = _ =>
    apply genr_eq_bound; intros;
    normalize_get
  | |- SUM [ _ < _ ] _ = _ =>
    apply sum_eq_bound; intros;
    normalize_get
  | |- (|[ _ ]| _) = _ =>
    apply iverson_weak;
    normalize_get
  | |- let_binding ?e ?f = _ =>
    let ee := fresh "ee" in
    let He := fresh "He" in
    let t := type of e in
    evar (ee : t);
    assert (e = ?ee) as He by (normalize_get; try reflexivity);
    lift_evar;
    try rewrite He;
    try clear He;
    drop_evar;
    eapply tlet_eq_body; intros;
    normalize_get
  | |- ?a <++> ?b = _ =>
    let ae := fresh "ae" in
    let Ha := fresh "Ha" in
    let ty := type of a in
    evar (ae : ty);
    assert (a = ?ae) as Ha by (normalize_get; try reflexivity);
    lift_evar;
    try rewrite Ha;
    drop_evar;
    let be := fresh "be" in
    let Hb := fresh "Hb" in
    evar (be : ty);
    assert (b = ?be) as Hb by (normalize_get; try reflexivity);
    lift_evar;
    try rewrite Hb;
    drop_evar;
    reflexivity
  | |- (?a + ?b)%R = _ =>
    normalize_in_expr
  | |- (?a / ?b)%R = _ =>
    normalize_in_expr
  | |- (?a * ?b)%R = _ =>
    normalize_in_expr
  | |- _ _[_] = _ =>
    normalize_in_expr
  | |- _ = _ => try reflexivity                  
  end.

Ltac let_lift :=
  match goal with
  | |- flatten _ = _ =>
    apply flatten_eq;
    let_lift
  | |- tile _ _ = _ =>
    apply tile_eq;
    let_lift
  | |- flatten_trunc _ _ = _ =>
    apply flatten_trunc_eq;
    let_lift
  | |- transpose _ = _ =>
    apply transpose_eq;
    let_lift
  | |- pad_r _ _ = _ =>
    apply pad_r_eq;
    let_lift
  | |- pad_l _ _ = _ =>
    apply pad_l_eq;
    let_lift
  | |- trunc_l _ _ = _ =>
    apply trunc_l_eq;
    let_lift
  | |- trunc_r _ _ = _ =>
    apply trunc_r_eq;
    let_lift                
  | |- GEN [ _ < _ ] _ = _ =>
    apply gen_eq_bound; intros;
    let_lift
  | |- GEN [ _ <= _ < _ ] _ = _ =>
    apply genr_eq_bound; intros;
    let_lift
  | |- SUM [ _ < _ ] _ = _ =>
    apply sum_eq_bound; intros;
    let_lift
  | |- (|[ _ ]| _) = _ =>
    apply iverson_weak;
    let_lift
  | |- let_binding ?e ?f = _ =>
    let ee := fresh "ee" in
    let He := fresh "He" in
    let t := type of e in
    evar (ee : t);
    assert (e = ?ee) as He by (let_lift; try reflexivity);
    lift_evar;
    try rewrite He;
    try clear He;
    drop_evar;
    try rewrite let_let_comm;
    eapply tlet_eq_body; intros;
    try rewrite let_let_comm;
    let_lift
  | |- ?a <++> ?b = _ =>
    let ae := fresh "ae" in
    let Ha := fresh "Ha" in
    let ty := type of a in
    evar (ae : ty);
    assert (a = ?ae) as Ha by (let_lift; try reflexivity);
    lift_evar;
    try rewrite Ha;
    drop_evar;
    let be := fresh "be" in
    let Hb := fresh "Hb" in
    evar (be : ty);
    assert (b = ?be) as Hb by (let_lift; try reflexivity);
    lift_evar;
    try rewrite Hb;
    drop_evar;
    repeat rewrite ll_concat_r;        
    repeat rewrite ll_concat_l;        
    try reflexivity
  | |- (?a + ?b)%R = _ =>
    let ae := fresh "ae" in
    let Ha := fresh "Ha" in
    evar (ae : R);
    assert (a = ?ae) as Ha by (let_lift; try reflexivity);
    lift_evar;
    try rewrite Ha;
    drop_evar;
    let be := fresh "be" in
    let Hb := fresh "Hb" in
    evar (be : R);
    assert (b = ?be) as Hb by (let_lift; try reflexivity);
    lift_evar;
    try rewrite Hb;
    drop_evar;
    repeat first [ rewrite ll_plus_r; let_lift | rewrite ll_plus_l; let_lift ];
    reflexivity
  | |- (?a / ?b)%R = _ =>
    let ae := fresh "ae" in
    let Ha := fresh "Ha" in
    evar (ae : R);
    assert (a = ?ae) as Ha by (let_lift; try reflexivity);
    lift_evar;
    try rewrite Ha;
    drop_evar;
    let be := fresh "be" in
    let Hb := fresh "Hb" in
    evar (be : R);
    assert (b = ?be) as Hb by (let_lift; try reflexivity);
    lift_evar;
    try rewrite Hb;
    drop_evar;
    repeat first [rewrite ll_div_r; let_lift | rewrite ll_div_l; let_lift ];
    reflexivity      
  | |- (?a * ?b)%R = _ =>
    let ae := fresh "ae" in
    let Ha := fresh "Ha" in
    evar (ae : R);
    assert (a = ?ae) as Ha by (let_lift; try reflexivity);
    lift_evar;
    try rewrite Ha;
    drop_evar;
    let be := fresh "be" in
    let Hb := fresh "Hb" in
    evar (be : R);
    assert (b = ?be) as Hb by (let_lift; try reflexivity);
    lift_evar;
    try rewrite Hb;
    drop_evar;
    repeat first [ rewrite ll_mult_r; let_lift | rewrite ll_mult_l; let_lift ];
    reflexivity      
  | |- _ _[_] = _ =>
    repeat rewrite ll_get;
    reflexivity
  | |- _ = _ =>
    try reflexivity
  end.

Ltac normalize_ssa :=
  etransitivity; [ normalize_get; try reflexivity | ];
  etransitivity; [ let_lift; try reflexivity | ]; lazy beta.

Ltac normalize := normalize_types; normalize_ssa.

Goal forall n m (v : list (list R)),
    2 < n ->
    2 < m ->
    consistent v (n,(m,tt)) ->
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
         <+> (v _[ y + 1; x2 + 1])))) = @nil _.
Proof.
  intros. normalize.
Abort.

Goal forall (f : list R) n m,
      consistent f (m,tt) ->
      (1 < n)%Z ->
      (tlet buf := GEN [ i < n ] f _[i] in
           GEN [ i < n ] (|[ 0 <=? i-1 ]| buf _[i-1]) <+> buf _[i])
      = @nil _.
Proof.
  intros. normalize.
Abort.

Goal forall n i j m c,
    ((GEN [ - m + 1 <= k < n ]
                               (|[ k =? 2 + (- m + 1) ]| 1)) _[ i - j ] *
     c _[ j ])%R = 0%R.
Proof. intros.
       normalize.
Abort.

Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
(tlet blurx'
:= (GEN [ i < 1 ]
    GEN [ j < Z.of_nat M ]
    0%R) <++> 
   (GEN [ y < Z.of_nat N ]
    GEN [ x < Z.of_nat M ]
    0%R) <++>
   (GEN [ y < 1 ]
    GEN [ x < Z.of_nat M ]
    0%R)
 in GEN [ y < Z.of_nat N ]
GEN [ x < Z.of_nat M ]
blurx' _[ y; x])
   = @nil _.
Proof.
  intros. normalize.
Abort.

Goal forall (v : list (list R)) n m,
    0 < n ->
    0 < m ->
    consistent v (n,(m,tt)) ->
    (GEN [ i < Z.of_nat n ] v _[i]) <++> (GEN [ i < Z.of_nat n ] v _[i])
    = @nil _.
Proof. intros. normalize.
Abort.

Goal forall m n (v : list (list R)),
    0 < n ->
    0 < m ->    
    consistent v (n,(m,tt)) ->
    v = v.
Proof.
  intros. normalize.
Abort.

Goal forall n m (v : list (list R)),
    0 < n ->
    0 < m ->
    consistent v (n,(m,tt)) ->
    (tlet x := v _[0] <+> v _[1] in
      x _[0]) <+> 0%R = 0%R.
Proof.
  intros. normalize.
Abort.

Goal forall n m (v : list (list R)),
    0 < n ->
    0 < m ->
    consistent v (n,(m,tt)) ->
    (tlet x := v _[0] in
      tensor_add x x) = @nil _.
Proof.
  intros. normalize.
Abort.

Goal forall n m (x2 : list (list R)) k,
    0 < k ->
    0 < n ->
    0 < m ->
    consistent x2 (n,(m,tt)) ->
                   (
           (GEN [ i2 < Z.of_nat k ]
                (|[ 3 * Z.of_nat k  <? Z.of_nat n ]|
                     0%R)))

 = @nil _.
Proof. intros. normalize. Abort.
