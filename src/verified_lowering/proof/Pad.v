From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Coq Require Import ZArith.Zdiv.
From Coq Require Import ZArith.Int.
From Coq Require Import ZArith.Znat.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.

Set Warnings "-deprecate-hint-without-locality,-deprecated".
Import ListNotations.

From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.
From Lower Require Import Zexpr Bexpr Array Range Sexpr Result ListMisc Meshgrid VarGeneration
     Constant ATLDeep ResultToArrayDelta.

Open Scope string_scope.

Inductive pad_type :=
| PadCons (l : nat)
          (l' : nat) (padl : pad_type)
          (r' : nat) (padr : pad_type)
          (r : nat)          
| PadNil (b : bool).

Fixpoint shape_to_pad_type sh :=
  match sh with
  | dim::dims => let inner := shape_to_pad_type dims in
                 PadCons (Z.to_nat dim) 0 inner 0 inner 0
  | _ => PadNil true
  end.
(*
Fixpoint is_get_pad pads lz rsh :=
  match pads with
  | PadCons l l' padl r' padr r =>
      match lz with
      | i::is =>
          match rsh with
          | dim::dims => (i < Z.of_nat l)%Z \/ (i >= dim - Z.of_nat r)%Z \/
                           (Z.of_nat l <= i < Z.of_nat l + Z.of_nat l' /\
                              is_get_pad padl is dims)%Z \/
                           (dim - Z.of_nat r - Z.of_nat r' <= i <
                              dim - Z.of_nat r /\ is_get_pad padr is dims)%Z
          | _ => False
          end
      | _ => False
      end
  | PadNil true => True
  | PadNil false => False
  end.

Inductive is_pad :
  context -> valuation -> fmap string pad_type -> Sexpr -> Prop :=
| IsPadVar : forall c x v g,
    g $? x = Some (PadNil true) ->
    is_pad c v g (Var x)
| IsPadGet : forall v g x pads l lz c size,
    g $? x = Some pads ->
    eval_Zexprlist v l lz ->
    is_get_pad pads lz (map (eval_Zexpr_Z_total $0) size) ->
    c $? x = Some size ->
    is_pad c v g (Get x l) 
| IsPadMul : forall e1 e2 v g c,
    is_pad c v g e1 ->
    is_pad c v g e2 ->
    is_pad c v g (Mul e1 e2)
  | IsPadAdd : forall e1 e2 v g c,
    is_pad c v g e1 ->
    is_pad c v g e2 ->
    is_pad c v g (Add e1 e2)
  | IsPadDiv : forall e1 e2 v g c,
    is_pad c v g e1 ->
    is_pad c v g e2 ->
    is_pad c v g (Div e1 e2)
  | IsPadSub : forall e1 e2 v g c,
    is_pad c v g e1 ->
    is_pad c v g e2 ->
    is_pad c v g (Sub e1 e2)
.
*)
(* We should only truncate program-introduced 0-values *)
Inductive has_pad :
  context -> valuation -> fmap string pad_type -> ATLexpr ->
  pad_type -> Prop :=
| HasPadGen : forall lo hi k c e (l : list Zexpr) v i g ctx pad1 pad2 ll rr,
    (k <= Z.to_nat (eval_Zexpr_Z_total $0 hi - eval_Zexpr_Z_total $0 lo)%Z) ->
    (c <= Z.to_nat (eval_Zexpr_Z_total $0 hi - eval_Zexpr_Z_total $0 lo)%Z) ->
    (k + c <=
       Z.to_nat (eval_Zexpr_Z_total $0 hi - eval_Zexpr_Z_total $0 lo)%Z) ->
    size_of e l ->
    (forall iz,
        (eval_Zexpr_Z_total $0 lo + Z.of_nat k <=
           iz < eval_Zexpr_Z_total $0 lo + Z.of_nat k + Z.of_nat ll)%Z ->
        has_pad ctx (v $+ (i,iz)) g e pad1) ->
    (forall iz,
        (eval_Zexpr_Z_total $0 hi - Z.of_nat c - Z.of_nat rr <=
           iz < eval_Zexpr_Z_total $0 hi - Z.of_nat c)%Z ->
        has_pad ctx (v $+ (i,iz)) g e pad2) ->
    (forall iz,
        (eval_Zexpr_Z_total $0 lo <= iz < eval_Zexpr_Z_total $0 hi)%Z ->
        (iz - eval_Zexpr_Z_total $0 lo < Z.of_nat k)%Z \/
          (eval_Zexpr_Z_total $0 hi - Z.of_nat c <= iz)%Z ->
        has_pad ctx (v $+ (i,iz)) g e (shape_to_pad_type
                                         (map (eval_Zexpr_Z_total $0) l))) ->
    ll + rr = (Z.to_nat (eval_Zexpr_Z_total $0 hi -
                        eval_Zexpr_Z_total $0 lo -
                        Z.of_nat k -
                        Z.of_nat c)) ->
    has_pad ctx v g (Gen i lo hi e) (PadCons
                                       k
                                       ll
                                       pad1 rr pad2 c)
| HasPadGuardFalse : forall v p e sh g ctx pads,
    eval_Bexpr v p false ->
    size_of e sh ->
    pads = shape_to_pad_type (map (eval_Zexpr_Z_total $0) sh) ->
    has_pad ctx v g (Guard p e) pads
| HasPadGuardTrue : forall v p e l g ctx,
    has_pad ctx v g e l ->
    has_pad ctx v g (Guard p e) l
| HasPadSumEmpty : forall v i lo hi e l g ctx pads,
    size_of e l ->
    (eval_Zexpr_Z_total $0 hi - eval_Zexpr_Z_total $0 lo <= 0)%Z ->
    pads = shape_to_pad_type (map (eval_Zexpr_Z_total $0) l) ->
    has_pad ctx v g (Sum i lo hi e) pads
| HasPadSum : forall v i lo hi e l g ctx,
    (forall iz,
        (eval_Zexpr_Z_total $0 lo <= iz < eval_Zexpr_Z_total $0 hi)%Z ->
        has_pad ctx (v $+(i,iz)) g e l) ->
    (0 < eval_Zexpr_Z_total $0 hi - eval_Zexpr_Z_total $0 lo)%Z ->
    has_pad ctx v g (Sum i lo hi e) l
| HasPadLbind : forall v x e1 e2 l1 l2 g ctx size,
    has_pad ctx v g e1 l1 ->
    size_of e1 size ->
    has_pad (ctx $+ (x,size)) v (g $+ (x,l1)) e2 l2 ->
    has_pad ctx v g (Lbind x e1 e2) l2
| HasPadConcat : forall v e1 e2 x y a b g l1 l2 r1 r2 pad1 pad2 pad3 pad4
                        ctx dim1 dim2 rest1 rest2,
    size_of e1 (dim1::rest1) ->
    size_of e2 (dim2::rest2) ->
    has_pad ctx v g e1 (PadCons x l1 pad1 r1 pad2 y) ->
    has_pad ctx v g e2 (PadCons a l2 pad3 r2 pad4 b) ->
    x+y <= Z.to_nat (eval_Zexpr_Z_total $0 dim1) ->
    a+b <= Z.to_nat (eval_Zexpr_Z_total $0 dim2) ->
    l1+r1 <= Z.to_nat (eval_Zexpr_Z_total $0 dim1) - x -y ->
    l2+r2 <= Z.to_nat (eval_Zexpr_Z_total $0 dim2) - a -b ->
    has_pad ctx v g (Concat e1 e2) (PadCons x l1 pad1 r2 pad4 b)
| HasPadFlattenStrong : forall v e x y n m sh g ctx xx yy a b l r c d
                         pad1 pad2 pad3 pad4 l1 l2 r1 r2 ll rr,
    has_pad ctx v g e (PadCons x l
                               (PadCons a l1 pad1 r1 pad2 c) r
                               (PadCons d l2 pad3 r2 pad4 b) y) ->
    size_of e (n::m::sh) ->
    x+y < Z.to_nat (eval_Zexpr_Z_total $0 n) ->
    l1+r1 <= Z.to_nat (eval_Zexpr_Z_total $0 m) - a - c ->
    l2+r2 <= Z.to_nat (eval_Zexpr_Z_total $0 m) - d - b ->
    a < Z.to_nat (eval_Zexpr_Z_total $0 m) ->
    b < Z.to_nat (eval_Zexpr_Z_total $0 m) -> 
    xx = x*(Z.to_nat (eval_Zexpr_Z_total $0 m)) + (min 1 l) * a ->
    yy = y*(Z.to_nat (eval_Zexpr_Z_total $0 m)) + (min 1 r) * b ->
    ll = min 1 l *
           match a,c,l1 =? Z.to_nat (eval_Zexpr_Z_total $0 m) with
           | 0,0,true => l*Z.to_nat (eval_Zexpr_Z_total $0 m)
           | _,_,_ => l1
           end ->
    rr = min 1 r *
           match d,b,r2 =? Z.to_nat (eval_Zexpr_Z_total $0 m) with
           | 0,0,true => r*Z.to_nat (eval_Zexpr_Z_total $0 m)
           | _,_,_ => r2
           end ->
    has_pad ctx v g (Flatten e) (PadCons xx ll pad1 rr pad4 yy)
| HasPadTruncr : forall v k e x y g ctx a l r pad1 pad2,
    has_pad ctx v g e (PadCons x l pad1 r pad2 y) ->
    (Z.to_nat (eval_Zexpr_Z_total $0 k) <= y) ->
    a = y- Z.to_nat (eval_Zexpr_Z_total $0 k) ->
    has_pad ctx v g (Truncr k e) (PadCons x l pad1 r pad2 a)
| HasPadTruncl : forall v k e x y g ctx b l r pad1 pad2,
    has_pad ctx v g e (PadCons x l pad1 r pad2 y) ->
    (Z.to_nat (eval_Zexpr_Z_total $0 k) <= x) ->
    b = x - Z.to_nat (eval_Zexpr_Z_total $0 k) ->
    has_pad ctx v g (Truncl k e) (PadCons b l pad1 r pad2 y)
| HasPadPadrEmpty : forall v k e g ctx dim rest pad,
    size_of e (dim::rest) ->
    has_pad ctx v g e pad ->
    (eval_Zexpr_Z_total $0 dim = 0)%Z ->
    has_pad ctx v g (Padr k e) (shape_to_pad_type
                                  (map (eval_Zexpr_Z_total $0) (k::rest)))
| HasPadPadlEmpty : forall k e v g ctx dim rest pad,
    size_of e (dim::rest) ->
    has_pad ctx v g e pad ->
    (eval_Zexpr_Z_total $0 dim = 0)%Z ->
    has_pad ctx v g (Padl k e) (shape_to_pad_type
                                  (map (eval_Zexpr_Z_total $0) (k::rest)))
| HasPadPadr : forall v k e x y g ctx dim rest l r pad1 pad2 yy,
    has_pad ctx v g e (PadCons x l pad1 r pad2 y) ->
    size_of e (dim::rest) ->
    (0 < eval_Zexpr_Z_total $0 dim)%Z ->
    yy = (y+ Z.to_nat (eval_Zexpr_Z_total $0 k)) ->
    x + y <= Z.to_nat (eval_Zexpr_Z_total $0 dim) ->
    l + r <= Z.to_nat (eval_Zexpr_Z_total $0 dim) - x -y ->
    has_pad ctx v g (Padr k e) (PadCons x l pad1 r pad2 yy)
| HasPadPadl : forall k e x y v g ctx dim rest l r pad1 pad2 xx,
    has_pad ctx v g e (PadCons x l pad1 r pad2 y) ->
    size_of e (dim::rest) ->
    (0 < eval_Zexpr_Z_total $0 dim)%Z ->
    xx = (x+ Z.to_nat (eval_Zexpr_Z_total $0 k)) ->
    x + y <= Z.to_nat (eval_Zexpr_Z_total $0 dim) ->
    l + r <= Z.to_nat (eval_Zexpr_Z_total $0 dim) - x -y ->
    has_pad ctx v g (Padl k e) (PadCons xx l pad1 r pad2 y)
(*| HasPadScalar : forall v g s ctx,
    is_pad ctx v g s ->
    has_pad ctx v g (Scalar s) (PadNil true) *)
| HasPadScalarNotPad : forall v g s ctx,
    has_pad ctx v g (Scalar s) (PadNil false)
| HasPadTransposeStrong : forall v e x y g ctx n xs l r a b c d pad1 pad2 pad3
                                 pad4 l1 l2 r1 r2 ll rr m lll rrr,
    has_pad ctx v g e (PadCons x l
                               (PadCons a l1 pad1 r1 pad2 c) r
                               (PadCons d l2 pad3 r2 pad4 b) y) ->
    size_of e (n::m::xs) ->
    l + r >= Z.to_nat (eval_Zexpr_Z_total $0 n) - x - y ->
    ll = min a d ->
    rr = min c b ->
    lll + rrr >=  Z.to_nat (eval_Zexpr_Z_total $0 m) - ll - rr ->
    x + y <= Z.to_nat (eval_Zexpr_Z_total $0 n) ->
    has_pad ctx v g (Transpose e)
            (PadCons ll lll
                     (PadCons x 0 pad1 0 pad1 y) rrr
                     (PadCons x 0 pad1 0 pad1 y) rr)
| HasPadTransposeWeak : forall v e x y g ctx n xs l r a b c d
                               pad1 pad2 pad3 pad4 l1 l2 r1 r2 ll rr lll rrr,
    has_pad ctx v g e (PadCons x l
                               (PadCons a l1 pad1 r1 pad2 c) r
                               (PadCons d l2 pad3 r2 pad4 b) y) ->
    size_of e (n::xs) ->
    ll = 0 ->
    rr = 0 ->
    lll = min a d ->
    rrr = min b c ->
    has_pad ctx v g (Transpose e)
            (PadCons ll lll
                     (PadCons (x+l) 0 pad1 0 pad1 (y+r)) rrr
                     (PadCons (x+l) 0 pad1 0 pad1 (y+r)) rr)
| HasPadSplit : forall ctx v g e n k c l r pad1 pad2 m sh nn mm,
    has_pad ctx v g e (PadCons k l pad1 r pad2 c) ->
    size_of e (m::sh) ->
    k + c <= Z.to_nat (eval_Zexpr_Z_total $0 m) ->
    l + r <= Z.to_nat (eval_Zexpr_Z_total $0 m) - k - c ->
    nn = (Z.to_nat (eval_Zexpr_Z_total $0 n)) ->
    mm = (Z.to_nat (eval_Zexpr_Z_total $0 m)) ->
    let cc := c + ((nn - mm mod nn) mod nn) in
    has_pad ctx v g (Split n e)
            (PadCons (k / nn)
                     (k//n nn - k / nn)
                     (PadCons (k mod nn)
                              (min l (nn - k mod nn)) pad1
                              0 pad1 0)
                     (cc//n nn - cc / nn)
                     (PadCons 0 0 pad2
                              (min r (nn - cc mod nn)) pad2
                              (cc mod nn))
                     (cc / nn)).

Fixpoint relate_pads (pad : pad_type) e sh :=
  match pad with
  | PadCons a ll pad1 rr pad2 b =>
      match e with
      | V l =>
          match sh with
          | _::xs => Forall (fun x => x = gen_pad xs) (firstn a l) /\
                       Forall (fun x => x = gen_pad xs) (firstn b (rev l)) /\
                       Forall (fun r' => relate_pads pad1 r' xs) 
                              (firstn ll (skipn a l)) /\
                       Forall (fun r' => relate_pads pad2 r' xs)
                              (firstn rr (skipn b (rev l)))
          | _ => False
          end
      | S _ => False
      end
  | PadNil true => sh = [] /\ e = S SX
  | PadNil false => sh = []
  end.

Lemma add_result_relate_pads :
  forall r1 r2 r3,
    add_result r1 r2 r3 ->
    forall pads rsh,
      relate_pads pads r1 rsh ->
      relate_pads pads r2 rsh ->
      relate_pads pads r3 rsh.
Proof.
  eapply (add_result_mut 
    (fun r1 r2 r3 H =>
       forall pads rsh,
         relate_pads pads r1 rsh ->
         relate_pads pads r2 rsh ->
         relate_pads pads r3 rsh)
    (fun l1 l2 l3 H =>
       forall pad1 rsh,
         forall a ll,
         Forall (fun r' => relate_pads pad1 r' rsh)
                (firstn ll (skipn a l1)) ->
         Forall (fun r' => relate_pads pad1 r' rsh)
                (firstn ll (skipn a l2)) ->
         Forall (fun r' => relate_pads pad1 r' rsh)
                (firstn ll (skipn a l3))));
    propositional.
  - cases pads; simpl in *; propositional.
    cases b; simpl in *; propositional. 
    invert H2. invert H3. invert a.
    propositional.
  - cases pads. simpl in *.
    2: { simpl in *. cases b. propositional; discriminate. auto. }
    cases rsh. propositional.
    invs.
    split. pose proof a.
    eapply add_list_firstn with (n:=l) in a.
    eapply forall_eq_gen_pad in H2,H4.
    rewrite H2,H4 in *.
    eapply add_list_repeat_gen_pad in a.
    2: { reflexivity. }
    2: { simpl. repeat rewrite firstn_length.
         eapply add_list_length in H7. rewrite H7. reflexivity. }
    rewrite a. eapply Forall_repeat. eauto.

    split.
    pose proof a. eapply add_list_rev in a.
    eapply add_list_firstn with (n:=r0) in a.
    eapply forall_eq_gen_pad in H0,H1.
    rewrite H0, H1 in *.
    eapply add_list_repeat_gen_pad in a.
    2: { reflexivity. }
    2: { repeat rewrite firstn_length. repeat rewrite rev_length.
         eapply add_list_length in H7. rewrite H7.
         reflexivity. }
    rewrite a. eapply Forall_repeat. eauto.

    split.
    eapply H. eauto. eauto. auto. auto. eauto. eauto.
    
    rewrite skipn_rev in H5,H8. rewrite skipn_rev.
    rewrite firstn_rev in H5,H8. rewrite firstn_rev.
    eapply Forall_rev. eapply Forall_rev in H5,H8.
    rewrite rev_involutive in *.
    rewrite skipn_firstn_comm in H5,H8. rewrite skipn_firstn_comm.
    repeat rewrite firstn_length in *. rewrite min_l in * by lia.
    pose proof a. pose proof a.
    eapply add_list_result_length in H9.
    eapply add_list_length in H7.
    rewrite H9,H7 in *.
    eapply H. eauto. eauto.
  - cases a1.
    + simpl in *. cases ll.
      * econstructor.
      * simpl. econstructor.
        eapply H. eauto. eauto. invert H1. eauto. invert H2. eauto.
        specialize H0 with (a:=0). simpl in *.
        eapply H0. eauto. eauto. invert H1. eauto. invert H2. eauto.
    + simpl in *.
      eapply H0. eauto. eauto. 
Qed.

Lemma relate_pads_gen_pad : forall xs_shape r l0,
    relate_pads (shape_to_pad_type (map (eval_Zexpr_Z_total $0) l0))
                r xs_shape->
    result_has_shape r xs_shape ->
    result_has_shape r (map Z.to_nat (map (eval_Zexpr_Z_total $0) l0)) ->
    r = gen_pad xs_shape.
Proof.
  induct xs_shape; intros.
  - invert H0. invert H1. simpl in *.
    cases l0; simpl in *; try discriminate. propositional.    
  - cases r. invert H0. cases l0. invert H1.
    repeat rewrite map_cons in *. simpl in *. invs.
    cases a.
    + invert H0. invert H1. simpl. reflexivity.
    + pose proof H0. pose proof H1.
      eapply result_has_shape_result_shape_nat in H4,H6.
      rewrite H4 in H6. clear H4.
      simpl in H6.
      cases (Z.to_nat (eval_Zexpr_Z_total $0 z)). simpl in H6. invert H6.
      simpl in H6. invert H6.
      simpl. rewrite <- repeat_cons. f_equal.
      cases v. invert H1. simpl in *.
      invert H2. f_equal.
      clear H3. clear H5. clear H. invert H0.
      rewrite firstn_all2 in H9 by lia.
      eapply forall_eq_gen_pad in H9. rewrite H9.
      simpl. rewrite repeat_length. reflexivity.
Qed.

Lemma relate_pads_gen_pad_id : forall size,
relate_pads (shape_to_pad_type (map (eval_Zexpr_Z_total $0) size))
    (gen_pad (map Z.to_nat (map (eval_Zexpr_Z_total $0) size)))
    (map Z.to_nat (map (eval_Zexpr_Z_total $0) size)).    
Proof.
  induct size; intros; simpl in *.
  - propositional.
  - split.
    eapply forall_firstn. eapply Forall_repeat. auto.
    split. econstructor. split. econstructor.
    eauto.
Qed.

Lemma relate_pads_filter_until_0 : forall pads r sh,
    result_has_shape r sh ->
    (relate_pads pads r (filter_until sh 0) <->
    relate_pads pads r sh).
Proof.
  induct pads; intros; propositional.
  - simpl in *. propositional. cases sh.
    cases r0. propositional. invert H.
    cases r0. propositional. simpl in *.
    cases n; simpl in *. invert H.
    simpl. repeat rewrite firstn_nil. repeat rewrite skipn_nil.
    repeat rewrite firstn_nil. propositional; econstructor.
    rewrite <- gen_pad_filter_until_0 in *.
    propositional.
    eapply Forall_forall. intros. eapply Forall_forall in H2.
    2: { eassumption. }
    eapply IHpads1. eapply result_has_shape_forall in H.
    eapply forall_skipn in H.
    eapply forall_firstn in H.
    eapply Forall_forall in H.
    2: apply H3. eauto. eauto.
    eapply Forall_forall. intros. eapply Forall_forall in H4.
    2: { eassumption. }
    eapply IHpads2. eapply result_has_shape_forall in H.
    eapply Forall_rev in H.
    eapply forall_skipn in H.
    eapply forall_firstn in H.
    eapply Forall_forall in H.
    2: apply H3. eauto. eauto.
  - simpl in *. cases r0. propositional.
    cases sh. simpl in *. propositional. invs.
    cases n. simpl in *. invert H.
    simpl. repeat rewrite firstn_nil. repeat rewrite skipn_nil.
    repeat rewrite firstn_nil. propositional; econstructor.
    simpl.
    rewrite <- gen_pad_filter_until_0 in *.
    propositional.
    eapply Forall_forall. intros. eapply Forall_forall in H2.
    2: { eassumption. }
    eapply IHpads1. eapply result_has_shape_forall in H.
    eapply forall_skipn in H.
    eapply forall_firstn in H.
    eapply Forall_forall in H.
    2: apply H3. eauto. eauto.
    eapply Forall_forall. intros. eapply Forall_forall in H4.
    2: { eassumption. }
    eapply IHpads2. eapply result_has_shape_forall in H.
    eapply Forall_rev in H.
    eapply forall_skipn in H.
    eapply forall_firstn in H.
    eapply Forall_forall in H.
    2: apply H3. eauto. eauto.
  - simpl in *. cases b; propositional.
    cases sh; simpl in *; try discriminate. auto.
    cases n; discriminate.
    cases sh; simpl in *; try discriminate. auto.
    cases n; discriminate.
  - simpl in *. cases b; simpl in *; invs. simpl. propositional.
    subst. reflexivity.
Qed.
(*
Lemma relate_pads_result_lookup_Z_pads_ :
  forall lz r pads,
    is_get_pad pads lz (result_shape_Z (V r)) ->
    relate_pads pads (V r) (result_shape_nat (V r)) ->
    result_has_shape (V r) (result_shape_nat (V r)) ->
    In lz (mesh_grid (result_shape_Z (V r))) ->
    (forall b, pads <> PadNil b) ->
    result_lookup_Z lz (V r) = SX.
Proof.
  induct lz; intros.
  - simpl in *. cases r. simpl in *. propositional.
    eapply empty_not_in_mesh_grid in H2. propositional.
  - simpl in *|-.
    cases r. simpl in *. propositional.
    unfold result_shape_Z in *|-. simpl in H,H0,H1.
    simpl result_shape_nat in H2. rewrite map_cons in *. decomp_index.
    posnats.
    cases pads.
    2: { specialize (H3 b). propositional. }
    remember (r::r0).
    simpl in H, H0. invs.
    simpl. cases a.
    3: lia.
    + simpl. clear H2. clear H6.
      invert H.
      { cases l. lia. simpl in *. invert H4. rewrite H8.
        eapply result_lookup_Z_gen_pad. eauto. }
      invert H2.
      { (* H0 *)
        cases r1. lia.
        simpl rev in H0. rewrite firstn_app in H0.
        rewrite rev_length in *.
        eapply Forall_app in H0. invs.
        rewrite firstn_all2 in H6.
        2: { simpl length. lia. } invert H6. rewrite H10.
        eapply result_lookup_Z_gen_pad. eauto. }
      invert H.
      { invs. simpl in *. rewrite skipn_app in *. rewrite firstn_app in *.
        rewrite skipn_length in *. rewrite rev_length in *.
        eapply Forall_app in H0. eapply Forall_app in H9. invs.
        cases l. 2: lia.
        simpl in *. clear H3. clear H4. clear H2.
        cases l'. lia. simpl in *. invert H7.
        cases r.
        - simpl in *. cases pads1. simpl in *.
          propositional. simpl in *. propositional. subst. simpl.
          cases b. 2: propositional.
          invs. invert H2. auto.
        - cases pads1.
          2: { simpl in *. cases b; simpl in *; invs; try discriminate.
               cases v. discriminate. simpl in *. propositional. }
          eapply IHlz. cases v. simpl in *. propositional.
          eauto. cases v. propositional. eauto.
          cases v. econstructor. invert H1. eauto.
          cases v. propositional. eauto.
          intros. inversion 1. }
      invs. simpl in *.
      rewrite skipn_app in *. rewrite firstn_app in *.
      rewrite skipn_length in *. rewrite rev_length in *.
      eapply Forall_app in H0. eapply Forall_app in H9. invs.
      replace (r1 - length r0) with 0 in * by lia. simpl in H10.
      rewrite firstn_all2 in H10 by (simpl; lia).
      invert H10.
      cases r.
      * simpl in *. propositional. subst.
        cases pads2. simpl in *. propositional.
        simpl in *. cases b. propositional. invert H5. auto. propositional.
      * cases pads2.
        2: { simpl in *. cases b; cases v; invs.
             discriminate. discriminate. propositional. propositional. }
        cases v. simpl in *. propositional.
        eapply IHlz. eauto. eauto. invert H1. eauto. eauto.
        intros. inversion 1.
    + cases (Z.to_nat (Z.pos p)). lia. simpl.
      cases (nth_error r0 n).
      2: { eapply nth_error_None in Heq0. lia. }      
      invert H.
      cases l. lia. simpl in H4. invert H4.
      { rewrite <- firstn_skipn with (n:=l) (l:=r0) in Heq0.
        rewrite nth_error_app1 in Heq0.
        2: { rewrite firstn_length. lia. }
        eapply nth_error_In in Heq0.
        eapply Forall_forall in H12.
        2: eassumption. subst.
        eapply result_lookup_Z_gen_pad. eauto. }
      invert H8.
      { simpl in H0.
        rewrite firstn_app in H0. eapply Forall_app in H0. invs.
        pose proof Heq0.
        eapply nth_error_firstn_rev with (n:=r1) in Heq0. 2: lia.
        eapply Forall_forall in H8. 2: eassumption. rewrite H8.
        eapply result_lookup_Z_gen_pad. eauto. }
      invert H.
      { invs. simpl in *. rewrite firstn_app in *.
        rewrite skipn_app in *. rewrite firstn_app in *.
        eapply Forall_app in H0,H9. invs. clear H13. clear H12.
        replace (nth_error r0 n) with (nth_error (r::r0) (Datatypes.S n))
          in Heq0 by auto.
        pose proof Heq0 as HH.
        rewrite <- firstn_skipn with (n:=l) (l:=r::r0) in HH.
        rewrite nth_error_app2 in HH.
        2: { rewrite firstn_length. lia. }
        rewrite firstn_length in *.
        rewrite <- firstn_skipn with (n:= l') (l:=(skipn l (r::r0))) in HH.
        rewrite nth_error_app1 in HH.
        2: { rewrite firstn_length. rewrite skipn_length.
             simpl length in *. lia. }
        eapply nth_error_In in HH.
        eapply Forall_forall in H7. 2: eassumption.
        

        cases r2.
        { eapply result_has_shape_forall in H1.
          eapply nth_error_In in Heq0.
          eapply Forall_forall in H1.
          2: { eassumption. }
          cases r.
          - cases pads1.
            + simpl in *. cases lz; propositional.
            + simpl in *. cases b. invs. invert H5.
              2: { contradiction. }
              invert H12. eauto. propositional.
          - invert H1. cases v; discriminate. }
        cases pads1.
        2: { simpl in *. cases b. invs. discriminate. propositional. }
        cases v.
        { eapply nth_error_In in Heq0.
          eapply result_has_shape_forall in H1.
          eapply Forall_forall in H1.
          2: { eapply Heq0. }
          invert H1. rewrite <- H0 in H5.
          simpl in *. propositional. }
        eapply nth_error_In in Heq0.
        pose proof H1 as Hsh.
        eapply result_has_shape_forall in H1.
        eapply Forall_forall in H1.
        2: { eapply Heq0. }
        invert H1. rewrite <- H13 in *.
        invert Hsh.
        pose proof H15 as Hshh.
        eapply result_has_shape_result_shape_nat in H15.
        rewrite map_cons in *. repeat decomp_index.
        rewrite filter_until_0_id in H15.
        2: { eapply mesh_grid_shape_pos in H1.
             erewrite Forall_map in H1.
             eapply Forall_impl. 2: eassumption. simpl. lia. }
        eapply IHlz.
        rewrite H15. eapply H10.
        rewrite H15. eauto.
        econstructor. eauto. eapply result_has_shape_self. eauto.
        rewrite H15. eauto.
        rewrite map_cons. repeat decomp_goal_index. rewrite H15.
        propositional. intros. inversion 1. }

      invs.
      invs. simpl in *. rewrite firstn_app in *.
        rewrite skipn_app in *. rewrite firstn_app in *.
        eapply Forall_app in H0,H9. invs. clear H13. clear H12.
        (* H *)
        pose proof Heq0 as HH.
        rewrite <- @rev_involutive with (l:=r0) in HH.
        erewrite <- nth_error_rev in HH.
        2: { rewrite rev_length. reflexivity. }
        rewrite <- firstn_skipn with (n:=r1) (l:=rev r0) in HH.
        rewrite nth_error_app2 in HH.
        2: { rewrite firstn_length. rewrite rev_length. lia. }
        rewrite firstn_length in *. rewrite rev_length in *.
        rewrite <- firstn_skipn with (n:= r') (l:=(skipn r1 (rev r0))) in HH.
        rewrite nth_error_app1 in HH.
        2: { rewrite firstn_length. rewrite skipn_length. rewrite rev_length.
             simpl length in *. lia. }
        eapply nth_error_In in HH.
        eapply Forall_forall in H. 2: eassumption.

        cases r2.
        { eapply result_has_shape_forall in H1.
          replace (nth_error r0 n) with (nth_error (r::r0) (Datatypes.S n))
                                        in Heq0 by auto.
          eapply nth_error_In in Heq0.
          eapply Forall_forall in H1.
          2: { eassumption. }
          cases r.
          - cases pads2.
            + simpl in *. cases lz; propositional.
            + simpl in *. cases b. invs. invert H5.
              2: { contradiction. }
              invert H12. eauto. propositional.
          - invert H1. cases v; discriminate. }
        cases pads2.
        2: { simpl in *. cases b. invs. discriminate. propositional. }
        cases v.
        { replace (nth_error r0 n) with (nth_error (r::r0) (Datatypes.S n))
                                        in Heq0 by auto.          
          eapply nth_error_In in Heq0.
          eapply result_has_shape_forall in H1.
          eapply Forall_forall in H1.
          2: { eapply Heq0. }
          invert H1. rewrite <- H0 in H5.
          simpl in *. propositional. }
        replace (nth_error r0 n) with (nth_error (r::r0) (Datatypes.S n))
                                        in Heq0 by auto.          
        eapply nth_error_In in Heq0.
        pose proof H1 as Hsh.
        eapply result_has_shape_forall in H1.
        eapply Forall_forall in H1.
        2: { eapply Heq0. }
        invert H1. rewrite <- H13 in *.
        invert Hsh.
        pose proof H15 as Hshh.
        eapply result_has_shape_result_shape_nat in H15.
        rewrite map_cons in *. repeat decomp_index.
        rewrite filter_until_0_id in H15.
        2: { eapply mesh_grid_shape_pos in H1.
             erewrite Forall_map in H1.
             eapply Forall_impl. 2: eassumption. simpl. lia. }
        eapply IHlz.
        rewrite H15. eapply H10.
        rewrite H15. eauto.
        econstructor. eauto. eapply result_has_shape_self. eauto.
        rewrite H15. eauto.
        rewrite map_cons. repeat decomp_goal_index. rewrite H15.
        propositional. intros. inversion 1. lia.
Qed.

Lemma is_pad_eval_Sexpr : forall sh v ec s g r,
    eval_Sexpr sh v ec s r ->
    (forall pads x r, g $? x = Some pads ->
                 ec $? x = Some r ->
                 relate_pads pads r (result_shape_nat r)) ->
    (forall x r size, sh $? x = Some size ->
                    ec $? x = Some r ->
                    result_has_shape
                      r
                      (map Z.to_nat (map (eval_Zexpr_Z_total $0) size))) ->
    is_pad sh v g s ->
    r = SX.
Proof.
  induct 1; intros.
  - invert H3.
    eapply H1 in H8. 2: eauto. simpl in *. propositional.
    invert H4. auto.
  - invert H5.
    eapply H3 in H8; eauto; clear H3.
    simpl in H8. cases rs.
    { invert H2; rewrite @nth_error_empty in *; discriminate. }
    cases pads.
    2: { simpl in *. cases b. invs. discriminate. propositional. }
    pose proof H2.
    eapply eval_get_lookup_result_Z in H3.
    2: { eauto. }
    pose proof H2.
    eapply eval_get_In_meshgrid in H5.
    2: { eapply result_has_shape_self.
         eapply H4. eauto. eauto. }
    2: { eauto. } subst.
    eapply relate_pads_result_lookup_Z_pads_.
    2: { eauto. }
    2: { eapply result_has_shape_self.
         eapply H4; eauto. }
    2: { eauto. }
    eapply H4 in H14; eauto.
    erewrite result_has_shape_result_shape_Z by eauto.
    erewrite result_has_shape_result_shape_Z in H5 by eauto. decomp_index.
    rewrite mesh_grid_map_Nat2Z_id in H5.
    rewrite filter_until_0_id.
    eauto.
    rewrite Z2Natid_list. eauto.
    eapply mesh_grid_shape_pos in H5.
    eapply Forall_impl.
    2: eassumption.
    simpl. lia. 
    eapply mesh_grid_shape_pos in H5.
    eapply Forall_map.
    eapply Forall_impl.
    2: eassumption.
    simpl. lia.  intros. inversion 1.
  - invert H3.
    eapply IHeval_Sexpr1 in H9; eauto.
    eapply IHeval_Sexpr2 in H10; eauto.
    subst.
    reflexivity.
  - invert H3.
    eapply IHeval_Sexpr1 in H9; eauto.
    eapply IHeval_Sexpr2 in H10; eauto.
    subst.
    reflexivity.
  - invert H4.
    eapply IHeval_Sexpr1 in H10; eauto.
    eapply IHeval_Sexpr2 in H11; eauto.
    subst.
    reflexivity.
  - invert H3.
    eapply IHeval_Sexpr1 in H9; eauto.
    eapply IHeval_Sexpr2 in H10; eauto.
    subst.
    reflexivity.
  - invert H1.
Qed.
*)
Lemma has_pad_size_of_relate_pads_gen_pad :
  forall e v size sh g pads,
    size_of e size ->
    constant_nonneg_bounds e ->
    has_pad sh v g e pads ->
    relate_pads pads
                (gen_pad (filter_until
                            (map Z.to_nat
                                 (map (eval_Zexpr_Z_total $0) size)) 0))
                (filter_until
                   (map Z.to_nat (map (eval_Zexpr_Z_total $0) size)) 0).
Proof.
  induct e; intros.
  - invert H. invert H0. invert H1. invs. 
    simpl. rewrite eval_Zexpr_Z_total_sub_distr.
    2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto. }
    2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto. }
    cases (Z.to_nat (eval_Zexpr_Z_total $0 hi - eval_Zexpr_Z_total $0 lo)).
    + simpl. repeat rewrite skipn_nil. repeat rewrite firstn_nil. eauto.
    + remember rev. simpl. 
      repeat rewrite <- repeat_cons. subst. rewrite rev_repeat.
      split. eapply forall_firstn. eapply Forall_repeat. eauto.
      split. eapply forall_firstn. eapply Forall_repeat. eauto.
      repeat rewrite skipn_repeat. repeat rewrite firstn_repeat. 
      cases ll.
      * rewrite min_0_r. split. econstructor. cases rr.
        rewrite min_0_r. econstructor.
        assert ((eval_Zexpr_Z_total $0 hi - Z.of_nat c -
                   Z.of_nat (Datatypes.S rr) <=
                   eval_Zexpr_Z_total $0 hi - Z.of_nat c -
                     Z.of_nat (Datatypes.S rr) <
                   eval_Zexpr_Z_total $0 hi - Z.of_nat c)%Z) by lia.
        eapply H16 in H1. eapply IHe in H1; eauto.
        eapply Forall_repeat.
        eq_size_of. eauto.
      * assert (eval_Zexpr_Z_total $0 lo + Z.of_nat k <=
                  eval_Zexpr_Z_total $0 lo + Z.of_nat k <
         eval_Zexpr_Z_total $0 lo + Z.of_nat k + Z.of_nat (Datatypes.S ll))%Z.
        lia.
        eapply H14 in H1.
        eapply IHe in H1; eauto.
        split. eapply Forall_repeat. eq_size_of. eauto.
        cases rr. rewrite min_0_r. econstructor.
        assert ((eval_Zexpr_Z_total $0 hi - Z.of_nat c -
                   Z.of_nat (Datatypes.S rr) <=
                   eval_Zexpr_Z_total $0 hi - Z.of_nat c -
                     Z.of_nat (Datatypes.S rr) <
                   eval_Zexpr_Z_total $0 hi - Z.of_nat c)%Z) by lia.
        eapply H16 in H4. eapply IHe in H4; eauto.
        eapply Forall_repeat. eq_size_of. eauto.
  - invert H. invs. invert H1.
    + eq_size_of. rewrite <- gen_pad_filter_until_0.
      eapply relate_pads_filter_until_0. eapply result_has_shape_gen_pad.
      eapply relate_pads_gen_pad_id.
    + invert H0. invs.
      eapply IHe. eauto. eauto. eapply (H10 (eval_Zexpr_Z_total $0 lo)).
      lia.
  - invert H. simpl in *. invert H1.
    + eq_size_of. rewrite <- gen_pad_filter_until_0.
      eapply relate_pads_filter_until_0. eapply result_has_shape_gen_pad.
      eapply relate_pads_gen_pad_id.
    + eapply IHe; eauto.
  - invert H. simpl in *. invs. invert H1. eq_size_of.
    eapply IHe2. eauto. eauto. eauto.
  - invert H0. invert H. invert H1.
    eq_size_of. invert H. invert H0.
    pose proof H5. pose proof H6.
    eapply constant_nonneg_bounds_size_of_no_vars in H,H0.
    invert H. invert H0. rewrite map_cons.
    rewrite eval_Zexpr_Z_total_add_distr.
    2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. }
    2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. }
    rewrite map_cons.
    pose proof H5. pose proof H6.
    eapply constant_nonneg_bounds_size_of_nonneg in H,H0; eauto.
    2: { eapply forall_no_vars_eval_Zexpr_Z_total with (v:=$0).
         econstructor; eauto. }
    2: { eapply forall_no_vars_eval_Zexpr_Z_total with (v:=$0).
         econstructor; eauto. }
    invert H. invert H0.
    rewrite Z2Nat.inj_add by lia.
    simpl.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 dim1)).
    * cases (Z.to_nat (eval_Zexpr_Z_total $0 dim2)).
      simpl. repeat rewrite skipn_nil. repeat rewrite firstn_nil. eauto.
      remember rev.
      simpl. repeat rewrite <- repeat_cons.  subst.
      rewrite rev_repeat. repeat rewrite skipn_repeat.
      repeat rewrite firstn_repeat. simpl in H16.
      replace l0 with 0 in * by lia. replace r1 with 0 in * by lia.
      replace x with 0 in * by lia. replace y with 0 in * by lia.
      repeat rewrite min_0_r.
      split. simpl. eauto.
      repeat rewrite min_r by lia. rewrite H8 in *.
      eapply IHe2 in H10; eauto. simpl in H10.
      remember rev.
      rewrite Heq0 in * . simpl in H10. invs.
      rewrite <- @repeat_cons in *. rewrite @rev_repeat in *.
      split. eapply Forall_repeat; eauto.
      split. econstructor.
      repeat rewrite @firstn_repeat in H21. 
      repeat rewrite @skipn_repeat in H21. 
      repeat rewrite @firstn_repeat in H21.
      rewrite min_r in H21 by lia. eauto.
    * eapply IHe1 in H5; eauto.
      eapply IHe2 in H6; eauto.
      cases (Z.to_nat (eval_Zexpr_Z_total $0 dim2)).
      -- simpl in H5,H6.
         rewrite Heq in *. rewrite Heq0 in *.
         remember rev. 
         simpl in H5,H6. clear H6.
         simpl.
         repeat rewrite <- @repeat_cons in *.
         subst. repeat rewrite @rev_repeat in *.
         repeat rewrite @skipn_repeat in *.
         repeat rewrite @firstn_repeat in *.
         repeat rewrite min_r in * by lia. invs.
         replace a with 0 in * by lia.
         replace b with 0 in * by lia.
         replace l3 with 0 in * by lia.
         replace r2 with 0 in * by lia.
         simpl in *.
         split. eapply Forall_repeat. eauto.
         split. eauto.
         split. eauto. econstructor.
      -- simpl in H5,H6.
         rewrite Heq in *. rewrite Heq0 in *.
         remember rev. 
         simpl in H5,H6. 
         simpl.
         repeat rewrite <- @repeat_cons in *.
         subst. repeat rewrite @rev_repeat in *.
         repeat rewrite @skipn_repeat in *.
         repeat rewrite @firstn_repeat in *.
         repeat rewrite min_r in * by lia. invs.
         rewrite H8 in *.
         split. eapply Forall_repeat. eauto.
         split. eapply Forall_repeat. eauto.
         split. eauto. eauto.
    * eauto.
    * eauto.
  - invert H. simpl in *. invs.
    pose proof H0. eapply constant_nonneg_bounds_size_of_nonneg in H; eauto.
    2: { eapply forall_no_vars_eval_Zexpr_Z_total with (v:=$0).
         eapply constant_nonneg_bounds_size_of_no_vars; eauto. }
    invert H. invert H6.
    pose proof H3.
    eapply constant_nonneg_bounds_size_of_no_vars in H; eauto.
    invert H. invert H9.
    rewrite eval_Zexpr_Z_total_mul_distr.
    2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. }
    2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. }
    rewrite Z2Nat.inj_mul by lia.
    invert H1. eq_size_of. invert H.
    eapply IHe in H2; eauto.
    simpl.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 n0)).
    + lia. 
    + cases (Z.to_nat (eval_Zexpr_Z_total $0 m0)).
      * lia.
      * simpl in H2. remember rev.
        rewrite Heq0,Heq in *.
        simpl in H2. simpl.
        repeat rewrite <- @repeat_cons.
        repeat rewrite <- repeat_cons in H2.
        subst.
        repeat rewrite @rev_repeat in *.
        repeat rewrite @skipn_repeat in *.
        repeat rewrite @firstn_repeat in *.
        invs.
        split. eapply Forall_repeat. eauto.
        split. eapply Forall_repeat. eauto.
        split.
        -- rewrite <- add_succ_l. cases l0.
           ++ rewrite min_0_r in *. simpl in*. econstructor.
           ++ rewrite (min_l 1) by lia. simpl mul. repeat rewrite add_0_r.
              cases a.
              { rewrite add_0_r. cases c.
                - cases (l1 =? Datatypes.S n1)%nat.
                  + eapply Nat.eqb_eq in Heq1. subst.
                    replace r1 with 0 in * by lia.
                    replace (Datatypes.S n1 + n * Datatypes.S n1) with
                      (Datatypes.S n * Datatypes.S n1) by lia.
                    rewrite <- mul_sub_distr_r.
                    pose proof H1.
                    cases (Datatypes.S n - x). lia.
                    rewrite <- succ_min_distr in H9.
                    rewrite repeat_cons in H9. invert H9.
                    clear H20.
                    repeat rewrite <- @repeat_cons in *.
                    repeat rewrite @rev_repeat in *.
                    invs. clear H20. simpl skipn in H17.
                    rewrite <- repeat_cons in H17.
                    rewrite firstn_all2 in H17.
                    2: { rewrite repeat_length. lia. }
                    invert H17. eapply Forall_repeat. eauto.
                  + eapply beq_nat_false in  Heq1.
                    replace (Datatypes.S n1 + n * Datatypes.S n1) with
                      (Datatypes.S n * Datatypes.S n1) by lia.
                    rewrite <- mul_sub_distr_r.
                    pose proof H1.
                    cases (Datatypes.S n - x). lia.
                    rewrite <- succ_min_distr in H9.
                    rewrite repeat_cons in H9. invert H9.
                    clear H20.
                    repeat rewrite <- @repeat_cons in *.
                    repeat rewrite @rev_repeat in *.
                    invs. clear H20. simpl skipn in H17.
                    rewrite <- repeat_cons in H17.
                    rewrite firstn_repeat in H17.
                    cases l1. econstructor.
                    rewrite <- succ_min_distr in H17. invert H17.
                    eapply Forall_repeat. eauto.
                - replace (Datatypes.S n1 + n * Datatypes.S n1) with
                      (Datatypes.S n * Datatypes.S n1) by lia.
                    rewrite <- mul_sub_distr_r.
                    pose proof H1.
                    cases (Datatypes.S n - x). lia.
                    rewrite <- succ_min_distr in H9.
                    rewrite repeat_cons in H9. invert H9.
                    clear H20.
                    repeat rewrite <- @repeat_cons in *.
                    repeat rewrite @rev_repeat in *.
                    invs. clear H20. simpl skipn in H17.
                    rewrite <- repeat_cons in H17.
                    rewrite firstn_repeat in H17.
                    cases l1. econstructor.
                    rewrite <- succ_min_distr in H17. invert H17.
                    eapply Forall_repeat. eauto.
              }
              repeat rewrite (min_r (Datatypes.S n) y) in * by lia.
              replace (Datatypes.S n1 + n * Datatypes.S n1) with
                (Datatypes.S n * Datatypes.S n1) by lia.
              rewrite sub_add_distr. rewrite <- mul_sub_distr_r.
              cases (Datatypes.S n - x). lia.
              clear H. clear H2.
              rewrite <-succ_min_distr in H1. invert H1.
              rewrite <- @repeat_cons in *.
              rewrite rev_repeat in H9.
              repeat rewrite @skipn_repeat in *.
              repeat rewrite @firstn_repeat in *.
              invs.
              cases (Datatypes.S n1 - Datatypes.S a). lia.
              cases l1. rewrite min_0_r. econstructor.
              rewrite <- succ_min_distr in H1. invert H1.
              eapply Forall_repeat. eauto.
        -- rewrite <- add_succ_l. cases r.
           ++ rewrite min_0_r in *. simpl in*. econstructor.
           ++ rewrite (min_l 1) by lia. simpl mul. repeat rewrite add_0_r.
              repeat rewrite (min_r (Datatypes.S n) y) in * by lia.
              repeat rewrite (min_r (Datatypes.S n) x) in * by lia.
              replace (Datatypes.S n1 + n * Datatypes.S n1) with
                (Datatypes.S n * Datatypes.S n1) by lia.
              rewrite sub_add_distr. rewrite <- mul_sub_distr_r.
              cases (Datatypes.S n - y). lia.
              clear H. clear H2.
              rewrite <-succ_min_distr in H16. invert H16.
              rewrite <- @repeat_cons in *.
              rewrite rev_repeat in H9.
              repeat rewrite @skipn_repeat in *.
              repeat rewrite @firstn_repeat in *.
              invs.
              cases (Datatypes.S n1 - b). lia.
              cases d.
              { cases b.
                - rewrite sub_0_r.
                  cases (r2 =? Datatypes.S n1)%nat.
                  + eapply Nat.eqb_eq in Heq3. subst.
                    rewrite <- succ_min_distr in H18. invert H18.
                    eapply Forall_repeat. eauto.
                  + cases r2. econstructor.
                    rewrite <- succ_min_distr in H18. invert H18.
                    eapply Forall_repeat; eauto.
                - cases r2. rewrite min_0_r. econstructor.
                  rewrite <- succ_min_distr in H18. invert H18.
                  eapply Forall_repeat; eauto.
              }              
              cases r2. rewrite min_0_r. econstructor.
              rewrite <- succ_min_distr in H18. invert H18.
              eapply Forall_repeat. eauto.
  - simpl in *. invs. invert H1. eq_size_of. invert H.
    pose proof H0. eapply constant_nonneg_bounds_size_of_no_vars in H; eauto.
    invert H. eapply IHe in H5; eauto. simpl in H5.
    repeat rewrite map_cons in *.
    erewrite eval_Zexpr_Z_total_ceil_div_distr.
    2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. }
    2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. }
    rewrite Z2Nat_div_distr.
    2: { lia. }
    2: { eapply constant_nonneg_bounds_size_of_nonneg in H0.
         2: { eauto. }
         2: { eapply forall_no_vars_eval_Zexpr_Z_total with (v:=$0); eauto. }
         invert H0. lia. }
    simpl in *. subst.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 m)).
    + simpl in *. unfold div_ceil_n at 1.
      rewrite div_small by lia. simpl.
      unfold div_ceil_n at 1.
      rewrite div_small by lia. simpl.
      unfold div_ceil_n. rewrite add_0_l.
      rewrite rev_repeat.
      rewrite (div_small (Z.to_nat (eval_Zexpr_Z_total $0 k) - 1)) by lia.
      simpl. repeat rewrite skipn_nil. repeat rewrite firstn_nil. eauto.
    + remember rev. simpl in H5. repeat rewrite <- @repeat_cons in *.
      subst. repeat rewrite @rev_repeat in *. subst cc.
      cases (Datatypes.S n //n (Z.to_nat (eval_Zexpr_Z_total $0 k))).
      assert (0 < Z.to_nat (eval_Zexpr_Z_total $0 k)) by lia.
      eapply ndiv_pos with (n:=Datatypes.S n) in H.
      2: { lia. } lia.
      remember rev. simpl in H5. simpl.
      cases (Z.to_nat (eval_Zexpr_Z_total $0 k)). lia.
      simpl gen_pad in *. repeat rewrite <- @repeat_cons in *. subst.
      repeat rewrite @rev_repeat in *. repeat rewrite @skipn_repeat in *.
      repeat rewrite @firstn_repeat in *.
      split. eapply Forall_repeat. reflexivity.
      split. eapply Forall_repeat. reflexivity.
      invs. 
      clear H. clear H3.
      rewrite <- Heq0 in *. rewrite <- Heq1 in *.
      rewrite <- Heq in *.
      rewrite Heq1 in *. 
      split.
      * remember modulo. remember div. remember sub.
        simpl. rewrite <- repeat_cons.
        subst. rewrite <- Heq1. 
        cases (k0 //n (Z.to_nat (eval_Zexpr_Z_total $0 k)) -
                 k0 / Z.to_nat (eval_Zexpr_Z_total $0 k)).
        -- rewrite min_0_r. econstructor.
        -- assert (n2 = 0).
           pose proof (ceil_sub_floor_le_1
                         k0
                         (Z.to_nat (eval_Zexpr_Z_total $0 k))).
           rewrite Heq2 in H. lia.
           subst.
           simpl in *.
           cases (k0 mod Z.to_nat (eval_Zexpr_Z_total $0 k)).
           pose proof Heq3 as HH.
           eapply mod_0_iff_ceil_sub_floor_0 in HH. lia. lia.
           (*k does not divide k0 *)
           cases (Z.to_nat (eval_Zexpr_Z_total $0 m) - k0).
           ++ assert (k0 = Z.to_nat (eval_Zexpr_Z_total $0 m)) by lia.
              assert (c = 0) by lia. subst. rewrite sub_0_r in *.
              rewrite Heq2. rewrite min_id.
              econstructor.
              split. eapply forall_firstn. eapply Forall_repeat. eauto.
              split. eauto.
              split; eauto.
              replace l0 with 0 in * by lia.
              replace r with 0 in * by lia.
              rewrite min_0_l. econstructor. econstructor.
           ++ cases (min
                       (Z.to_nat (eval_Zexpr_Z_total $0 m) //n
                                 (Z.to_nat (eval_Zexpr_Z_total $0 k)) -
                          k0 / Z.to_nat (eval_Zexpr_Z_total $0 k)) 1).
              econstructor.
              eapply Forall_repeat.
              split. eapply forall_firstn. eapply Forall_repeat. eauto.
              split. auto.
              split; auto.
              cases l0. rewrite min_0_l. econstructor.
              rewrite <- succ_min_distr in H1. invert H1.
              eapply forall_firstn. eapply forall_skipn. eapply Forall_repeat.
              eauto.
      * remember rev. remember sub. remember div. remember modulo.
        simpl. subst. rewrite <- repeat_cons.
        rewrite <- Heq1.
        remember (Z.to_nat (eval_Zexpr_Z_total $0 m)) as mm.
        remember (Z.to_nat (eval_Zexpr_Z_total $0 k)) as kk.
        rewrite min_r in H11 by lia.
        cases r.
        -- rewrite min_0_l. simpl firstn.
           eapply Forall_repeat. split; eauto. split; eauto.
           eapply forall_firstn. eapply Forall_rev. eapply Forall_repeat.
           eauto.
        -- simpl in H11. invert H11.
           remember (Z.to_nat (eval_Zexpr_Z_total $0 m)) as mm.
           remember (Z.to_nat (eval_Zexpr_Z_total $0 k)) as kk.
           eapply Forall_repeat.
           split. eauto. split.
           eapply forall_firstn. eapply Forall_rev. eapply Forall_repeat.
           eauto.
           split. eauto.
           eapply forall_firstn. eapply forall_skipn.
           eapply Forall_rev. eapply Forall_repeat. eauto.
  - invert H. simpl in *. invert H1.
    + eq_size_of. invert H.
      simpl.
      cases (Z.to_nat (eval_Zexpr_Z_total $0 m0)).
      * simpl in *. repeat rewrite skipn_nil.
        repeat rewrite firstn_nil. eauto.
      * cases (Z.to_nat (eval_Zexpr_Z_total $0 n0)).
        -- remember rev. simpl. rewrite <- repeat_cons.
           subst. rewrite rev_repeat.
           replace x with 0 in * by lia. replace y with 0 in * by lia.
           rewrite skipn_repeat. repeat rewrite firstn_repeat.
           split. eapply Forall_repeat. eauto.
           split. eapply Forall_repeat. eauto.
           split. eapply Forall_repeat. simpl. eauto.
           rewrite skipn_repeat. rewrite firstn_repeat.
           eapply Forall_repeat. simpl. eauto.
        -- remember rev. simpl. repeat rewrite <- repeat_cons.
           subst. repeat rewrite rev_repeat.
           repeat rewrite skipn_repeat. repeat rewrite firstn_repeat.
           split. eapply Forall_repeat. reflexivity.
           split. eapply Forall_repeat. reflexivity.
           split. eapply Forall_repeat.
           rewrite rev_repeat. repeat rewrite firstn_repeat.
           split. eapply Forall_repeat. reflexivity.
           split. eapply Forall_repeat. reflexivity.
           eauto.
           eapply Forall_repeat. rewrite rev_repeat.
           repeat rewrite firstn_repeat.
           split. eapply Forall_repeat. reflexivity.
           split. eapply Forall_repeat. reflexivity.
           eauto.
    + simpl.
      cases (Z.to_nat (eval_Zexpr_Z_total $0 m)).
      * simpl. repeat rewrite firstn_nil. eauto.
      * remember rev. simpl.
        cases (Z.to_nat (eval_Zexpr_Z_total $0 n)).
        -- simpl. repeat rewrite <- repeat_cons. subst.
           rewrite rev_repeat. repeat rewrite firstn_repeat.
           split. eauto. split. eauto.
           split. eapply Forall_repeat. simpl. repeat rewrite firstn_nil.
           eauto.
           eapply Forall_repeat. simpl. repeat rewrite firstn_nil.
           eauto.
        -- simpl. repeat rewrite <- repeat_cons. subst.
           repeat rewrite rev_repeat. repeat rewrite firstn_repeat.
           split. eauto. split. eauto. split.
           eapply Forall_repeat. rewrite rev_repeat.
           repeat rewrite firstn_repeat.
           split. eapply Forall_repeat. eauto.
           split. eapply Forall_repeat. eauto.
           eauto.
           eapply Forall_repeat. rewrite rev_repeat.
           repeat rewrite firstn_repeat.
           split. eapply Forall_repeat. eauto.
           split. eapply Forall_repeat. eauto. eauto.
  - simpl in *. invs. erewrite size_of_sizeof in * by eauto.
    simpl in *. invert H1.    
    eapply IHe in H6; eauto.
    eapply constant_nonneg_bounds_size_of_no_vars in H2; eauto. invert H2.
    repeat rewrite map_cons.
    rewrite eval_Zexpr_Z_total_sub_distr.
    2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. }
    2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. }
    rewrite Z2Nat.inj_sub by lia.
    cases ((Z.to_nat (eval_Zexpr_Z_total $0 m)
            - Z.to_nat (eval_Zexpr_Z_total $0 n))).
    { simpl. repeat rewrite skipn_nil. repeat rewrite firstn_nil. eauto. }
    remember gen_pad.
    simpl. remember rev. rewrite Heqr0. simpl.
    rewrite <- repeat_cons. subst. rewrite rev_repeat.
    repeat rewrite map_cons in H6.
    rewrite filter_until_cons in H6 by lia.
    simpl in H6.
    simpl.
    repeat rewrite <- repeat_cons.
    repeat rewrite @rev_repeat in *. repeat rewrite @skipn_repeat in *.
    repeat rewrite @firstn_repeat in *. invs.
    split. eapply Forall_repeat. eauto.
    split. eapply Forall_repeat. eauto.
    split. pose proof H1.
    { cases (Z.to_nat (eval_Zexpr_Z_total $0 m) - x).
      + rewrite <- Heq. simpl in *. rewrite min_l in H6 by lia.        
      replace (Z.to_nat (eval_Zexpr_Z_total $0 m) -
                 Z.to_nat (eval_Zexpr_Z_total $0 n) -
                 x) with 0 by lia.
      rewrite min_l by lia. econstructor.
    + cases l0. rewrite min_0_r in *. simpl. econstructor.
      rewrite <- succ_min_distr in H6. simpl in H6. invert H6.
      eapply Forall_repeat. eauto. }
    { cases (Z.to_nat (eval_Zexpr_Z_total $0 m) - y).
    + rewrite <- Heq. simpl in *. rewrite min_l in H9 by lia.
      replace (Z.to_nat (eval_Zexpr_Z_total $0 m) -
                 Z.to_nat (eval_Zexpr_Z_total $0 n) -
                 (y - Z.to_nat (eval_Zexpr_Z_total $0 n)))with 0 by lia.
      rewrite min_l by lia. econstructor.
    + cases r. rewrite min_0_r in *. simpl. econstructor.
      rewrite <- succ_min_distr in H9. simpl in H9. invert H9.
      eapply Forall_repeat. eauto. }
  - simpl in *. invs. erewrite size_of_sizeof in * by eauto.
    simpl in *. invert H1.    
    eapply IHe in H6; eauto.
    eapply constant_nonneg_bounds_size_of_no_vars in H2; eauto. invert H2.
    repeat rewrite map_cons.
    rewrite eval_Zexpr_Z_total_sub_distr.
    2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. }
    2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. }
    rewrite Z2Nat.inj_sub by lia.
    cases ((Z.to_nat (eval_Zexpr_Z_total $0 m)
            - Z.to_nat (eval_Zexpr_Z_total $0 n))).
    { simpl. repeat rewrite skipn_nil. repeat rewrite firstn_nil. eauto. }
    remember gen_pad.
    simpl. remember rev. rewrite Heqr0. simpl.
    rewrite <- repeat_cons. subst. rewrite rev_repeat.
    repeat rewrite map_cons in H6.
    rewrite filter_until_cons in H6 by lia.
    simpl in H6.
    simpl.
    repeat rewrite <- repeat_cons.
    repeat rewrite @rev_repeat in *. repeat rewrite @skipn_repeat in *.
    repeat rewrite @firstn_repeat in *. invs.
    split. eapply Forall_repeat. eauto.
    split. eapply Forall_repeat. eauto.
    split. pose proof H1.
    { cases (Z.to_nat (eval_Zexpr_Z_total $0 m) - x).
      + rewrite <- Heq. simpl in *. rewrite min_l in H6 by lia.        
        replace (Z.to_nat (eval_Zexpr_Z_total $0 m) -
                 Z.to_nat (eval_Zexpr_Z_total $0 n) -
                 (x-Z.to_nat (eval_Zexpr_Z_total $0 n))) with 0 by lia.
        rewrite min_l by lia. econstructor.
      + cases l0. rewrite min_0_r in *. simpl. econstructor.
        rewrite <- succ_min_distr in H6. simpl in H6. invert H6.
        eapply Forall_repeat. eauto. }
    { cases (Z.to_nat (eval_Zexpr_Z_total $0 m) - y).
      + rewrite <- Heq. simpl in *. rewrite min_l in H9 by lia.
        replace (Z.to_nat (eval_Zexpr_Z_total $0 m) -
                   Z.to_nat (eval_Zexpr_Z_total $0 n) - y)with 0 by lia.
      rewrite min_l by lia. econstructor.
    + cases r. rewrite min_0_r in *. simpl. econstructor.
      rewrite <- succ_min_distr in H9. simpl in H9. invert H9.
      eapply Forall_repeat. eauto. }
  - simpl in *. invs. invert H1.
    + eq_size_of. invert H.
      repeat rewrite map_cons.
      pose proof H2.
      eapply constant_nonneg_bounds_size_of_no_vars in H; eauto. invert H.
      erewrite eval_Zexpr_Z_total_add_distr.
      2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. }
      2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. }
      rewrite H12. simpl Z.to_nat.
      repeat rewrite <- map_cons.
      rewrite <- gen_pad_filter_until_0.
      eapply relate_pads_filter_until_0.
      eapply result_has_shape_gen_pad.
      eapply relate_pads_gen_pad_id.
    + eq_size_of. invert H.
      pose proof H2. 
      eapply constant_nonneg_bounds_size_of_no_vars in H; eauto. invert H.
      repeat rewrite map_cons.
      erewrite eval_Zexpr_Z_total_add_distr.
      2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. }
      2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. }
      eapply IHe in H5; eauto.      
      repeat rewrite map_cons in *.
      repeat rewrite filter_until_cons in * by lia.
      simpl in *.
      repeat rewrite @rev_repeat in *. repeat rewrite @skipn_repeat in *.
      repeat rewrite @firstn_repeat in *. invs.
      split. eapply Forall_repeat; eauto.
      split. eapply Forall_repeat; eauto.
      split. cases l0. rewrite min_0_r. econstructor.
      rewrite min_r by lia. rewrite min_r in H1 by lia. eauto.
      rewrite min_r by lia. rewrite min_r in H10 by lia. eauto.
  - simpl in *. invs. invert H1.
    + eq_size_of. invert H.
      repeat rewrite map_cons.
      pose proof H2.
      eapply constant_nonneg_bounds_size_of_no_vars in H; eauto. invert H.
      erewrite eval_Zexpr_Z_total_add_distr.
      2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. }
      2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. }
      rewrite H12. simpl Z.to_nat.
      repeat rewrite <- map_cons.
      rewrite <- gen_pad_filter_until_0.
      eapply relate_pads_filter_until_0.
      eapply result_has_shape_gen_pad.
      eapply relate_pads_gen_pad_id.
    + eq_size_of. invert H.
      pose proof H2. 
      eapply constant_nonneg_bounds_size_of_no_vars in H; eauto. invert H.
      repeat rewrite map_cons.
      erewrite eval_Zexpr_Z_total_add_distr.
      2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. }
      2: { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total; eauto. }
      eapply IHe in H5; eauto.      
      repeat rewrite map_cons in *.
      repeat rewrite filter_until_cons in * by lia.
      simpl in *.
      repeat rewrite @rev_repeat in *. repeat rewrite @skipn_repeat in *.
      repeat rewrite @firstn_repeat in *. invs.
      split. eapply Forall_repeat; eauto.
      split. eapply Forall_repeat; eauto.
      split. cases l0. rewrite min_0_r. econstructor.
      rewrite min_r by lia. rewrite min_r in H1 by lia. eauto.
      rewrite min_r by lia. rewrite min_r in H10 by lia. eauto.
  - simpl in *. invs. invert H1.
    + simpl. propositional.
Qed.

Lemma has_pad_gen_pad : forall sh v ec r e,
    eval_expr sh v ec e r ->
    constant_nonneg_bounds e ->
    forall rsh pads g,
    has_pad sh v g e pads ->
    result_has_shape r rsh ->
    (forall pads (x : var) (r0 : result),
        g $? x = Some pads ->
        ec $? x = Some r0 -> relate_pads pads r0 (result_shape_nat r0)) ->
    (forall (x : var) (r0 : result) (size0 : list Zexpr),
        sh $? x = Some size0 ->
        ec $? x = Some r0 ->
        result_has_shape r0 (map Z.to_nat
                                 (map (eval_Zexpr_Z_total $0) size0))) ->
    forall size,
      size_of e size ->
    relate_pads pads r rsh.
Proof.
  induct 1; intros Hconst rsh pads g Hpad Hsh (* Hpos *) Hrelate
                   Hhasshape size Hsize.
  11: { invert Hpad.
    invert Hsize. eq_size_of. invert H1.
    simpl in *|-.
    pose proof H3 as Hsize.
    eapply constant_nonneg_bounds_size_of_no_vars in Hsize; eauto.
    pose proof Hconst as Hconst'.
    eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape
      in Hconst'.
    2: { eauto. }
    2: { eauto. }
    pose proof Hconst as Hconst''.

    assert (0 < eval_Zexpr_Z_total $0 n0 \/ eval_Zexpr_Z_total $0 n0 <= 0)%Z
           as Hcasen by lia.
    assert (0 < eval_Zexpr_Z_total $0 m0 \/ eval_Zexpr_Z_total $0 m0 <= 0)%Z
           as Hcasem by lia.

    inversion Hcasen as [ Hcasen1 | Hcasen2 ]; clear Hcasen.
    2: { eapply constant_nonneg_bounds_size_of_nonneg in Hconst''; eauto.
         2: { eapply forall_no_vars_eval_Zexpr_Z_total
              with (v:=$0); eauto. }
         invert Hconst''. invert H11.
         assert (eval_Zexpr_Z_total $0 n0 = 0)%Z by lia. simpl in *.
         rewrite H1 in *. invert Hconst'. simpl in *. invert Hsh.
         repeat rewrite firstn_nil.
         repeat rewrite skipn_nil. simpl.
         repeat rewrite firstn_nil. simpl.
         propositional; econstructor. }

    inversion Hcasem as [ Hcasem1 | Hcasem2 ]; clear Hcasem.
    2: { eapply constant_nonneg_bounds_size_of_nonneg in Hconst''; eauto.
         2: { eapply forall_no_vars_eval_Zexpr_Z_total
              with (v:=$0); eauto. }
         invert Hconst''. invert H11.
         assert (eval_Zexpr_Z_total $0 m0 = 0)%Z by lia. simpl in *.
         rewrite H1 in *.
         eapply result_has_shape_flatten in Hconst'.
         simpl in *. rewrite mul_0_r in *.
         eapply result_has_shape_result_shape_nat in Hsh,Hconst'.
         rewrite Hsh in Hconst'. simpl in Hconst'.
         cases rsh. simpl in *. discriminate.
         simpl in *.
         rewrite mul_0_r.
         
         cases n.
         - simpl in *. 
           cases (flatten_result l).
           simpl in *. eauto. repeat rewrite firstn_nil.
           repeat rewrite skipn_nil. simpl.
           repeat rewrite firstn_nil. simpl.
           propositional; econstructor.
           simpl in *.
           invert Hsh.
         - invert Hconst'. }
    simpl in *|-.

    pose proof Hconst' as Hsh'.
    pose proof Hsh as Hsh''.
    
    eapply result_has_shape_flatten in Hsh'.
    eapply result_has_shape_result_shape_nat in Hsh', Hsh''.
    rewrite Hsh' in Hsh''.

    cases rsh. simpl in *.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 n0) *
             Z.to_nat (eval_Zexpr_Z_total $0 m0));
      simpl in *; try discriminate.
    cases n.
    simpl in Hsh''.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 n0) *
             Z.to_nat (eval_Zexpr_Z_total $0 m0)). lia. 
    simpl in Hsh''.
    invert Hsh''.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 n0) *
             Z.to_nat (eval_Zexpr_Z_total $0 m0)). lia.
    simpl in Hsh''. invert Hsh''.
    clear Hsh'.
    rewrite <- Heq in *. clear Heq. clear n.
    
    eapply IHeval_expr in Hconst''.
    3: { eauto. }
    3: { eauto. }
    3: { eauto. }
    2: { eauto. }
    2: { eauto. }

    repeat rewrite map_cons in *.
    simpl in Hconst''.
    invs.
    rewrite <- gen_pad_cons in *.

    simpl.
    rewrite gen_pad_filter_until_0.
    rewrite <- H10.
    rewrite <- gen_pad_filter_until_0.

    split.
    rewrite <- (firstn_skipn (x * Z.to_nat (eval_Zexpr_Z_total $0 m0))
                             (flatten_result l)).
    rewrite firstn_app. rewrite firstn_length.
    erewrite result_has_shape_length.
    2: { eauto. }
    rewrite mul_min_distr_r.
    replace (min x (Z.to_nat (eval_Zexpr_Z_total $0 n0))) with x by lia.
    rewrite minus_plus.
    rewrite firstn_all2.
    2: { rewrite firstn_length. erewrite result_has_shape_length by eauto.
         rewrite mul_min_distr_r.
         rewrite min_l by lia.
         eapply le_add_r. }

    eapply Forall_app.
    split.

    eapply forall_firstn_flatten_result. eauto. eauto.

    { erewrite skipn_stride_flatten_result by eauto.
      cases l0.
      - simpl in *. 
        rewrite min_r by lia. simpl. eauto.
      - rewrite min_l by lia. simpl. rewrite add_0_r.
        eapply forall_firstn_flatten_result_lt.
        eapply Forall_impl. 2: eassumption.
        simpl. intros. cases a0. propositional.
        invs. eauto.
        eapply forall_result_has_shape. eapply forall_skipn.
        eapply result_has_shape_forall. eauto. rewrite skipn_length. auto.
        lia. }
    split.

    rewrite <- (firstn_skipn (y * Z.to_nat (eval_Zexpr_Z_total $0 m0))
                             (rev (flatten_result l))).
    rewrite firstn_app. rewrite firstn_length. rewrite rev_length.
    erewrite result_has_shape_length.
    2: { eauto. }
    rewrite mul_min_distr_r.
    replace (min y (Z.to_nat (eval_Zexpr_Z_total $0 n0))) with y by lia.
    rewrite minus_plus.
    rewrite firstn_all2.
    2: { rewrite firstn_length.
         rewrite rev_length.
         erewrite result_has_shape_length by eauto.
         rewrite mul_min_distr_r.
         rewrite min_l by lia.
         eapply le_plus_l. }
    eapply Forall_app.
    split. eapply forall_firstn_rev_flatten_result. eauto. eauto.

    { rewrite skipn_rev. erewrite result_has_shape_length.
      2: eauto.
      rewrite <- mul_sub_distr_r.
      erewrite firstn_stride_flatten_result.
      2: { eauto. }
      rewrite <- (rev_involutive (firstn _ l)).
      replace (Z.to_nat (eval_Zexpr_Z_total $0 n0)) with (length l).
      2: { erewrite result_has_shape_length. reflexivity. eauto. }
      rewrite <- skipn_rev.
      cases r.
      - rewrite min_r by lia. simpl. eauto.
      - rewrite min_l by lia. simpl. rewrite add_0_r.
        eapply forall_firstn_rev_flatten_result_lt.
        eapply Forall_impl. 2: eassumption. simpl. intros.
        cases a0. propositional. invs. eauto.
        eapply forall_result_has_shape. eapply forall_skipn.
        eapply Forall_rev. eapply result_has_shape_forall. eauto.
        reflexivity. lia. }

    rewrite (Nat.add_comm _ (_*a)). rewrite (Nat.add_comm _ (_*b)).
    rewrite <- skipn_skipn. rewrite <- skipn_skipn.
    erewrite skipn_stride_flatten_result.
    2: { eassumption. }
    rewrite skipn_rev.
    erewrite result_has_shape_length.
    2: eauto.
    rewrite <- mul_sub_distr_r.
    erewrite firstn_stride_flatten_result by eauto.
    rewrite <- (rev_involutive (firstn _ l)).
    replace (Z.to_nat (eval_Zexpr_Z_total $0 n0)) with (length l).
    2: { erewrite result_has_shape_length. reflexivity. eauto. }
    rewrite <- skipn_rev.

    split.
    { cases l0.
      - rewrite min_r by lia. simpl. eauto.
      - simpl. rewrite min_l by lia. simpl. repeat rewrite add_0_r.
        cases a.
        { simpl. cases c.
          - simpl. cases (l1 =? Z.to_nat (eval_Zexpr_Z_total $0 m0))%nat.
            + eapply Nat.eqb_eq in Heq. subst.
              replace r1 with 0 in * by lia. clear H13.
              replace (Z.to_nat (eval_Zexpr_Z_total $0 m0) +
                         l0 * Z.to_nat (eval_Zexpr_Z_total $0 m0)) with
                (Datatypes.S l0 * Z.to_nat (eval_Zexpr_Z_total $0 m0)) by lia.
              erewrite firstn_stride_flatten_result.
              2: { eapply forall_result_has_shape. eapply forall_skipn.
                   eapply result_has_shape_forall. eauto. reflexivity. }
              simpl skipn in H9.
              eapply forall_flatten_result.
              eapply Forall_forall. intros. eapply Forall_forall in H9.
              2: eassumption. cases x0. propositional.
              invs.
              eapply result_has_shape_forall in Hconst'.
              eapply Forall_forall in H12.
              2: { eapply forall_firstn. eapply forall_skipn. eauto. }
              simpl in H12.
              rewrite firstn_all2 in H14.
              2: { erewrite result_has_shape_length by eauto. lia. }
              eapply result_has_shape_forall in H12.
              eapply Forall_forall. intros.
              eapply Forall_forall in H14.
              2: eassumption.
              eapply Forall_forall in H15. 2: apply H12.
              simpl in H15.
              eapply relate_pads_filter_until_0.
              eapply result_has_shape_filter_until_0. rewrite <- H10.
              erewrite <- result_has_shape_filter_until_0.  eauto.
              rewrite <- H10.
              eapply relate_pads_filter_until_0; eauto.
            + eapply beq_nat_false in Heq.
              replace (flatten_result (skipn x l)) with
                (skipn 0 (flatten_result (skipn x l))) by eauto.
              eapply forall_firstn_skipn_flatten_result.
              2: { eapply forall_result_has_shape.
                   eapply forall_skipn. eapply result_has_shape_forall. eauto.
                   reflexivity. }
              2: { lia. }
              2: { lia. }
              eapply Forall_forall. intros. eapply Forall_forall in H9.
              2: eassumption.
              cases x0. propositional. invs.
              eapply result_has_shape_forall in Hconst'.
              eapply Forall_forall in H12.
              2: { eapply forall_firstn. eapply forall_skipn.
                   eapply Hconst'. }
              simpl in *.
              eapply Forall_forall. intros. eapply Forall_forall in H15.
              2: eassumption. 
              eapply result_has_shape_forall in H12.
              eapply Forall_forall in H16.
              2: { eapply forall_firstn. eapply H12. }
              simpl in *.
              eapply relate_pads_filter_until_0.
              eapply result_has_shape_filter_until_0. rewrite <- H10.
              erewrite <- result_has_shape_filter_until_0. eauto.
              rewrite <- H10.
              eapply relate_pads_filter_until_0.
              eauto. eauto.
          - clear H1. clear H11.
              replace (flatten_result (skipn x l)) with
                (skipn 0 (flatten_result (skipn x l))) by eauto.
              eapply forall_firstn_skipn_flatten_result.
              2: { eapply forall_result_has_shape.
                   eapply forall_skipn. eapply result_has_shape_forall. eauto.
                   reflexivity. }
              2: { lia. }
              2: { lia. }
              eapply Forall_forall. intros. eapply Forall_forall in H9.
              2: eassumption.
              cases x0. propositional. invs.
              eapply result_has_shape_forall in Hconst'.
              eapply Forall_forall in H1.
              2: { eapply forall_firstn. eapply forall_skipn.
                   eapply Hconst'. }
              eapply Forall_forall. intros. eapply Forall_forall in H12.
              2: eassumption. 
              eapply result_has_shape_forall in H1.
              eapply Forall_forall in H14.
              2: { eapply forall_firstn. eapply forall_skipn. eapply H1. }
              simpl in H14.
              eapply relate_pads_filter_until_0.
              eapply result_has_shape_filter_until_0. rewrite <- H10.
              erewrite <- result_has_shape_filter_until_0. eauto.
              rewrite <- H10.
              eapply relate_pads_filter_until_0.
              eauto. eauto. }              
        eapply forall_firstn_skipn_flatten_result.
        eapply Forall_forall. intros. eapply Forall_forall in H9.
        2: { eassumption. }
        2: { eapply forall_result_has_shape. eapply forall_skipn.
             eapply result_has_shape_forall. eauto. reflexivity. }
        2: lia.
        2: { lia. }
        cases x0. propositional. invs.
        eapply Forall_forall. intros. eapply Forall_forall in H15.
        2: eassumption.
        eapply Forall_forall in H16.
        2: { eapply forall_firstn. eapply forall_skipn.
             eapply Forall_forall in H12.
             2: { eapply forall_firstn. eapply forall_skipn.
                  eapply result_has_shape_forall. apply Hconst'. }
             simpl in H12. eapply result_has_shape_forall.
             eapply H12. } simpl in H16.
        eapply relate_pads_filter_until_0.
        eapply result_has_shape_filter_until_0. rewrite <- H10.
        erewrite <- result_has_shape_filter_until_0. auto.
        rewrite <- H10.
        eapply relate_pads_filter_until_0. eauto. eauto. }
    
    cases r. simpl in *. rewrite min_r by lia. simpl. auto.
    rewrite min_l by lia. simpl. repeat rewrite add_0_r.

    cases d.
    { cases b.
      - cases (r2 =? Z.to_nat (eval_Zexpr_Z_total $0 m0))%nat.
        + eapply Nat.eqb_eq in Heq. subst. simpl.
          replace (Z.to_nat (eval_Zexpr_Z_total $0 m0) +
                     r * Z.to_nat (eval_Zexpr_Z_total $0 m0)) with
            (Datatypes.S r * Z.to_nat (eval_Zexpr_Z_total $0 m0)) by lia.
          clear H9. remember (skipn y (rev l)).
          rewrite firstn_rev.
          subst. erewrite result_has_shape_length.
          2: { eapply result_has_shape_flatten. eapply result_has_shape_rev.
               eapply forall_result_has_shape. eapply forall_skipn.
               eapply Forall_rev. eapply result_has_shape_forall. eauto.
               rewrite skipn_length. rewrite rev_length.
               erewrite result_has_shape_length by eauto.
               reflexivity. }
          rewrite <- mul_sub_distr_r.
          erewrite skipn_stride_flatten_result.
          2: { eapply forall_result_has_shape.
               eapply Forall_rev. eapply forall_skipn. eapply Forall_rev.
               eapply result_has_shape_forall. eauto.
               reflexivity. }
          eapply Forall_rev.
          rewrite skipn_rev.
          rewrite skipn_length. rewrite rev_length.
          erewrite result_has_shape_length by eauto.
          cases (Z.to_nat (eval_Zexpr_Z_total $0 n0) - y -
                   Datatypes.S r). simpl.
          * rewrite sub_0_r.
            rewrite firstn_all2 in H13.
            2: { rewrite skipn_length. rewrite rev_length.
                 erewrite result_has_shape_length by eauto. lia. }
            rewrite firstn_all2.
            2: { rewrite skipn_length. rewrite rev_length.
                 erewrite result_has_shape_length by eauto. lia. }
            eapply forall_flatten_result_rev.
            2: { eapply forall_result_has_shape. eapply forall_skipn.
                 eapply Forall_rev.
                 eapply result_has_shape_forall. eauto. reflexivity. }
            eapply Forall_forall. intros. eapply Forall_forall in H13.
            2: eassumption. cases x0. propositional. invs.
            eapply result_has_shape_forall in Hconst'.
            eapply Forall_forall in H9.
            2: { eapply forall_skipn. eapply Forall_rev. eapply Hconst'. }
            simpl in *.
            rewrite firstn_all2 in H16.
            2: { rewrite rev_length.
                 erewrite result_has_shape_length by eauto. lia. }
            eapply Forall_rev in H16. rewrite rev_involutive in H16.
            eapply Forall_forall. intros. eapply Forall_forall in H16.
            2: { eauto. }
            eapply result_has_shape_forall in H9.
            eapply Forall_forall in H15. 2: apply H9. simpl in H15.
            eapply relate_pads_filter_until_0.
            eapply result_has_shape_filter_until_0. rewrite <- H10.
            erewrite <- result_has_shape_filter_until_0. eauto.
            rewrite <- H10.
            eapply relate_pads_filter_until_0; eauto.
          * rewrite <- Heq.
            replace (Z.to_nat (eval_Zexpr_Z_total $0 n0) - y -
                     (Z.to_nat (eval_Zexpr_Z_total $0 n0) - y -
                        Datatypes.S r)) with
              (Datatypes.S r) by lia.            
            eapply forall_flatten_result_rev.
            2: { eapply forall_result_has_shape. eapply forall_firstn.
                 eapply forall_skipn. eapply Forall_rev.
                 eapply result_has_shape_forall. eauto. reflexivity. }
            eapply Forall_forall. intros. eapply Forall_forall in H13.
            2: eassumption. cases x0. propositional. invs.
            eapply result_has_shape_forall in Hconst'.
            eapply Forall_forall in H9.
            2: { eapply forall_firstn.
                 eapply forall_skipn. eapply Forall_rev. eapply Hconst'. }
            simpl in *.
            rewrite firstn_all2 in H16.
            2: { rewrite rev_length.
                 erewrite result_has_shape_length by eauto. lia. }
            eapply Forall_rev in H16. rewrite rev_involutive in H16.
            eapply Forall_forall. intros. eapply Forall_forall in H16.
            2: { eauto. }
            eapply result_has_shape_forall in H9.
            eapply Forall_forall in H15. 2: apply H9. simpl in H15.
            eapply relate_pads_filter_until_0.
            eapply result_has_shape_filter_until_0. rewrite <- H10.
            erewrite <- result_has_shape_filter_until_0. eauto.
            rewrite <- H10.
            eapply relate_pads_filter_until_0; eauto.
        + eapply forall_firstn_skipn_rev_flatten_result.
          2: { eapply forall_result_has_shape.
               eapply forall_skipn. eapply Forall_rev.
               eapply result_has_shape_forall. eauto. reflexivity. }
          2: lia. 2: lia.
          eapply Forall_forall. intros. eapply Forall_forall in H13.
          2: eassumption. cases x0. propositional.
          invs.
          eapply Forall_forall. intros. eapply Forall_forall in H17.
          2: eassumption.
          eapply result_has_shape_forall in Hconst'.
          eapply Forall_forall in H12.
          2: { eapply forall_firstn. eapply forall_skipn. eapply Forall_rev.
               eapply Hconst'. }
          simpl in H12. eapply result_has_shape_forall in H12.
          eapply Forall_forall in H16.
          2: { eapply forall_firstn. eapply forall_skipn. eapply Forall_rev.
               eapply H12. }
          simpl in H16.
          eapply relate_pads_filter_until_0.
          eapply result_has_shape_filter_until_0.
          rewrite <- H10. erewrite <- result_has_shape_filter_until_0.
          eauto.
          rewrite <- H10.
          eapply relate_pads_filter_until_0. eauto. eauto.
      - eapply forall_firstn_skipn_rev_flatten_result.
          2: { eapply forall_result_has_shape.
               eapply forall_skipn. eapply Forall_rev.
               eapply result_has_shape_forall. eauto. reflexivity. }
          2: lia. 2: lia.
          eapply Forall_forall. intros. eapply Forall_forall in H13.
          2: eassumption. cases x0. propositional.
          invs.
          eapply Forall_forall. intros. eapply Forall_forall in H17.
          2: eassumption.
          eapply result_has_shape_forall in Hconst'.
          eapply Forall_forall in H12.
          2: { eapply forall_firstn. eapply forall_skipn. eapply Forall_rev.
               eapply Hconst'. }
          simpl in H12. eapply result_has_shape_forall in H12.
          eapply Forall_forall in H16.
          2: { eapply forall_firstn. eapply forall_skipn. eapply Forall_rev.
               eapply H12. }
          simpl in H16.
          eapply relate_pads_filter_until_0.
          eapply result_has_shape_filter_until_0.
          rewrite <- H10. erewrite <- result_has_shape_filter_until_0.
          eauto.
          rewrite <- H10.
          eapply relate_pads_filter_until_0. eauto. eauto.
    }
    eapply forall_firstn_skipn_rev_flatten_result.
    eapply Forall_forall. intros. eapply Forall_forall in H13.
    2: { eassumption. }
    2: { eapply forall_result_has_shape. eapply forall_skipn.
         eapply result_has_shape_forall. eapply result_has_shape_rev.
         eauto. reflexivity. }
        2: lia.
        2: { lia. }
        cases x0. propositional. invs.
        eapply Forall_forall. intros. eapply Forall_forall in H17.
        2: eassumption.
        eapply Forall_forall in H16.
        2: { eapply forall_firstn. eapply forall_skipn. eapply Forall_rev.
             eapply Forall_forall in H12.
             2: { eapply forall_firstn. eapply forall_skipn.
                  eapply result_has_shape_forall.
                  eapply result_has_shape_rev. apply Hconst'. }
             simpl in H12. eapply result_has_shape_forall.
             eapply H12. } simpl in H16.
        eapply relate_pads_filter_until_0.
        eapply result_has_shape_filter_until_0. rewrite <- H10.
        erewrite <- result_has_shape_filter_until_0. auto.
        rewrite <- H10.
        eapply relate_pads_filter_until_0. eauto. eauto. }
  11: { (* SPLIT *)
    simpl in *. invs. invert Hpad. eq_size_of. invert H2.
    pose proof H3.
    eapply constant_nonneg_bounds_size_of_no_vars in H2; eauto. invert H2.
    pose proof H3.
    eapply constant_nonneg_bounds_size_of_nonneg in H2; eauto.
    2: { eapply forall_no_vars_eval_Zexpr_Z_total with (v:=$0).
         econstructor; eauto. }
    invert H2.
    pose proof H3.
    eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H2;
      eauto.
    repeat rewrite map_cons in *. pose proof H6 as HP.
    eapply IHeval_expr in H6; eauto.
    simpl in *. cases rsh. invert Hsh.
    pose proof Hsh as Hsh'. pose proof H2 as Hsh''.
    eapply result_has_shape_split_result in Hsh''.
    eapply result_has_shape_result_shape_nat in Hsh',Hsh''.
    rewrite Hsh' in Hsh''.
    pose proof H2 as Hlen.
    eapply result_has_shape_length in Hlen.
    symmetry in Hsh''.
    pose proof H2 as HH.
    eapply result_has_shape_split_result
      with (k:=(Z.to_nat (eval_Zexpr_Z_total $0 k))) in HH.
    pose proof HH as HHH.
    eapply result_has_shape_result_shape_nat in HHH.
    pose proof Hsh as HHHH.
    eapply result_has_shape_result_shape_nat in HHHH.
    rewrite HHH in HHHH.
    subst cc. 2: lia. 2: lia.
    cases l.
    { simpl. unfold split_result. simpl.      
      unfold div_ceil_n.
      rewrite (div_small (0 + Z.to_nat (eval_Zexpr_Z_total $0 k) - 1)) by lia.
      unfold nat_range. simpl.
      repeat rewrite skipn_nil. repeat rewrite firstn_nil. eauto. }
    erewrite filter_until_cons in Hsh''.
    2: { eapply ndiv_pos. simpl in *. lia. lia. }
    erewrite filter_until_cons in Hsh'' by lia.
    cases n. simpl in Hsh''. invert Hsh''.
    simpl in Hsh''. invert Hsh''.
    invs.
    erewrite gen_pad_filter_until_0. rewrite <- H15.
    rewrite <- filter_until_cons by lia.
    erewrite <- gen_pad_filter_until_0.
    split.
    { (* k0/k left padding *)
      eapply forall_gen_pad_flatten_result.
      eapply forall_result_has_shape.
      eapply forall_firstn. eapply result_has_shape_forall.
      pose proof Hsh. eapply result_has_shape_filter_until_0 in H17.
      rewrite filter_until_0_cons in H17 by lia.
      rewrite <- H15 in H17.
      rewrite <- filter_until_0_cons in H17 by lia.
      rewrite <- filter_until_0_cons in H17 by lia.
      erewrite <- result_has_shape_filter_until_0 in H17. eauto.
      reflexivity.
      erewrite firstn_split_result.
      2: lia.
      2: { erewrite result_has_shape_length by eauto.
           pose proof (div_mul_upper_bound
                         k0
                         (Z.to_nat (eval_Zexpr_Z_total $0 k))). lia. }
      2: { eauto. }
      eapply forall_firstn_ge. eassumption.
      eapply div_mul_upper_bound. lia. }
    split.
    { (* right padding *)
      eapply forall_gen_pad_flatten_result.
      eapply forall_result_has_shape.
      eapply forall_firstn. eapply Forall_rev.
      eapply result_has_shape_forall.
      pose proof Hsh. eapply result_has_shape_filter_until_0 in H17.
      rewrite filter_until_0_cons in H17 by lia.
      rewrite <- H15 in H17.
      rewrite <- filter_until_0_cons in H17 by lia.
      rewrite <- filter_until_0_cons in H17 by lia.
      erewrite <- result_has_shape_filter_until_0 in H17. eauto.
      reflexivity.
      unfold split_result. simpl. rewrite app_comm_cons. rewrite <- map_rev.
      erewrite (map_extensionality (rev _)).
      2: { intros. eapply in_rev in H17.
           rewrite skipn_app. rewrite firstn_app.
           rewrite skipn_repeat. rewrite firstn_repeat.
           replace (Z.to_nat (eval_Zexpr_Z_total $0 k) * x -
                      length (r0 :: l)) with 0.
           2: { eapply In_nat_range in H17. simpl length.
                erewrite (Nat.div_mod_eq
                            (Datatypes.S (length l))
                            (Z.to_nat (eval_Zexpr_Z_total $0 k))).
                rewrite sub_add_distr. rewrite <- mul_sub_distr_l.
                replace (x - Datatypes.S
                               (length l) /
                               Z.to_nat (eval_Zexpr_Z_total $0 k)) with 0.
                lia.
                pose proof (ceil_sub_floor_le_1
                              (Datatypes.S (Datatypes.length l))
                              (Z.to_nat (eval_Zexpr_Z_total $0 k))).
                lia. }
           rewrite sub_0_r. rewrite skipn_length.
           reflexivity. }
      rewrite firstn_map. unfold nat_range. rewrite firstn_rev_nat_range_rec.
      rewrite add_0_l.
      remember (Z.to_nat (eval_Zexpr_Z_total $0 k)) as kk.
      remember (Z.to_nat (eval_Zexpr_Z_total $0 m)) as mm.
      simpl length in *. rewrite map_rev.      
      cases (mm mod kk).
      2: { (* k does not divide m *)
        rewrite <- Heq. rewrite Hlen.
        rewrite min_l.
        2: { replace (mm //n kk) with (mm/kk + 1)%nat.
             rewrite (Nat.div_mod_eq c kk).
             rewrite <- add_assoc.
             rewrite mul_comm. rewrite div_add_l by lia.
             assert ((c mod kk + (kk - mm mod kk) mod kk) / kk <= 1).
             eapply add_mod_div_bound. lia.
             cases ((c mod kk + (kk - mm mod kk) mod kk) / kk).
             rewrite add_0_r. eapply le_trans.
             2: { eapply le_plus_l. }
             eapply div_le_mono. lia. lia.
             cases n1. 2: lia.
             eapply plus_le_compat_r.
             eapply div_le_mono. lia. lia. 
             cases (mm //n kk - mm / kk).
             eapply mod_0_iff_ceil_sub_floor_0 in Heq0. lia. lia.
             pose proof (ceil_sub_floor_le_1 mm kk). lia. }
        cases ((c + (kk - mm mod kk) mod kk) / kk). econstructor.
        rewrite succ_nat_range_rec_app_end. rewrite <- Heq0.
        rewrite map_app. rewrite rev_app_distr. simpl.
        replace n1 with (Datatypes.S n1 - 1) by lia. rewrite <- Heq0.
        rewrite (add_sub_assoc _ (mm//n kk)).
        2: { replace (mm //n kk) with (mm/kk + 1).
             2: { cases (mm //n kk - mm / kk).
                  eapply mod_0_iff_ceil_sub_floor_0 in Heq1. lia. lia.
                  pose proof (ceil_sub_floor_le_1 mm kk). lia. }
             rewrite (Nat.div_mod_eq c kk). rewrite <- add_assoc.
             rewrite mul_comm. rewrite div_add_l by lia.
             pose proof (add_mod_div_bound c (kk- mm mod kk) kk).
             assert (c <= mm) by lia.
             eapply div_le_mono with (c:=kk) in H19. 2: lia.
             lia.
        }
        rewrite <- add_sub_swap by lia.
        rewrite <- add_sub_assoc. 2: lia.
        rewrite minus_plus.
        replace (mm //n kk) with (mm/kk + 1).
        2: { cases (mm //n kk - mm / kk).
             eapply mod_0_iff_ceil_sub_floor_0 in Heq1. lia. lia.
             pose proof (ceil_sub_floor_le_1 mm kk). lia. }
        rewrite add_sub. rewrite <- mod_eq. 2: lia.
        rewrite min_l.
        2: { eapply mod_le. lia. }
        erewrite map_nat_range_rec_extensionality.
        2: { intros. cases H17.
             rewrite add_sub_assoc in H19.
        2: { rewrite (Nat.div_mod_eq c kk). rewrite <- add_assoc.
             rewrite mul_comm. rewrite div_add_l by lia.
             pose proof (add_mod_div_bound c (kk- mm mod kk) kk).
             assert (c <= mm) by lia.
             eapply div_le_mono with (c:=kk) in H21. 2: lia. lia. }
             rewrite <- add_sub_swap in H19 by lia.
             rewrite add_assoc in H19.
             rewrite add_sub in *. rewrite minus_plus in *.
             rewrite (Nat.div_mod_eq mm kk) at 2.
             rewrite add_sub_swap.
             2: { eapply mul_le_mono_l. lia. }
             rewrite <- mul_sub_distr_l.
             cases (mm / kk - x). lia.
             rewrite (mul_comm _ (Datatypes.S _)). simpl.
             repeat rewrite sub_add_distr.
             rewrite sub_diag. rewrite sub_0_l. rewrite min_0_r.
             simpl. rewrite app_nil_r. reflexivity. }
        repeat rewrite Forall_app.
        split. split.
        - replace (kk * (mm / kk))
            with (length (r0::l) - (length (r0::l) - (kk * (mm / kk)))).
          2: { rewrite sub_sub_distr.
               lia. simpl length. rewrite Hlen. 
               rewrite (Nat.div_mod_eq mm kk) at 2. lia. lia. }
          rewrite <- (rev_involutive (skipn _ _)).
          rewrite <- firstn_rev. simpl length. rewrite Hlen.
          rewrite <- mod_eq.
          rewrite firstn_all2.
          2: { rewrite rev_length. rewrite firstn_length.
               pose proof (Nat.mod_upper_bound mm kk). lia. }
          eapply Forall_rev. eapply forall_firstn_ge. eauto.
          assert ((c + (kk - mm mod kk) mod kk) < kk \/
                    kk <= (c + (kk - mm mod kk) mod kk)). lia.
          cases H17. eapply div_small_iff in H17. lia. lia.
          rewrite <- (mod_id mm kk) in H17 at 1. lia. lia. lia. lia.
        - invert H2. eapply result_has_shape_result_shape_nat in H23.
          rewrite H23. rewrite <- gen_pad_filter_until_0.
          eapply Forall_repeat. eauto.
        - eapply forall_flatten_result_rev_all. rewrite rev_involutive.
          2: { eapply Forall_rev. eapply Forall_map. eapply Forall_forall.
               auto. }
          rewrite flatten_result_nat_range_rec.
          rewrite <- (firstn_skipn (length (r0::l) - c) (r0::l)).
          rewrite skipn_app. rewrite firstn_app.
          rewrite skipn_length. rewrite firstn_length.
          rewrite <- (rev_involutive (skipn _ (r0::l))).
          rewrite <- firstn_rev. 
          rewrite Forall_app. split.
          2: { simpl length. rewrite Hlen.
               rewrite (min_l (mm-c)) by lia.
               eapply forall_firstn. eapply forall_skipn.
               eapply Forall_rev. eauto. }
          simpl length. rewrite Hlen.
          rewrite skipn_all2. rewrite firstn_nil. econstructor.
          rewrite firstn_length. simpl length. rewrite min_l by lia.
          rewrite mul_sub_distr_r. rewrite mul_add_distr_r.
          rewrite (Nat.div_mod_eq mm kk) at 1.
          rewrite mul_comm.
          assert ((c + (kk - mm mod kk) mod kk) < kk \/
                    kk <= (c + (kk - mm mod kk) mod kk)). lia.
          cases H17. eapply div_small_iff in H17. lia. lia.
          rewrite <- (mod_id mm kk) in H17 at 1.
          rewrite (Nat.add_comm (mm mod kk)) in H17.
          rewrite (Nat.add_comm c) in H17. 2: lia. 2: lia.
          eapply plus_le_reg_l in H17.
          rewrite mul_1_l.
          rewrite mul_comm. rewrite <- Nat.div_mod_eq.
          rewrite <- (mod_id mm kk) at 3 by lia.
          rewrite add_assoc. rewrite <- Nat.div_mod_eq.
          replace c with (mm mod kk + (c - mm mod kk)) at 2.
          2: { rewrite add_sub_assoc by lia. lia. }
          replace (mm mod kk + (c - mm mod kk) + (kk - mm mod kk) mod kk)
            with
            (mm mod kk + (kk - mm mod kk) mod kk + (c - mm mod kk)) by lia.
          rewrite mod_id by lia.
          eapply plus_le_reg_l with (p:=c). rewrite le_plus_minus_r by lia.
          rewrite Nat.add_comm.
          replace kk with (1*kk) at 4 by lia.
          rewrite div_add_l by lia.
          rewrite mul_add_distr_r. rewrite mul_1_l.
          rewrite sub_add_distr.
          replace (mm + (kk - mm mod kk) mod kk - kk) with (kk*(mm/kk)).
          2: { rewrite (Nat.div_mod_eq mm kk) at 2.
               rewrite <- add_assoc.
               rewrite mod_id. lia. lia. lia. }
          cut (mm - c <=kk * (mm / kk) - (c - mm mod kk) / kk * kk). lia.
          rewrite (Nat.div_mod_eq mm kk) at 1.
          rewrite mul_comm.
          eapply le_trans.
          2: { eapply sub_le_mono_l.
               eapply div_mul_upper_bound. lia. }
          lia. 
      }
      { (* k divides m *)        
        rewrite sub_0_r in *. rewrite mod_same by lia. rewrite add_0_r.
        rewrite Hlen.
        rewrite min_l.
        2: { eapply mod_0_iff_ceil_eq_floor_0 in Heq. rewrite Heq.
             eapply div_le_mono. lia. lia. lia. }
        cases (c / kk). simpl. econstructor.
        rewrite succ_nat_range_rec_app_end. rewrite map_app.
        simpl map at 4. 
        rewrite <- Heq0.
        erewrite map_nat_range_rec_extensionality.
        2: { intros. rewrite Heq. rewrite sub_0_r. rewrite mod_same by lia.
             rewrite min_0_l. simpl. rewrite app_nil_r. reflexivity. }
        repeat rewrite mul_add_distr_l. repeat rewrite mul_sub_distr_l.
        rewrite Heq. rewrite sub_0_r. rewrite mod_same. rewrite min_0_l.
        simpl repeat. rewrite app_nil_r.
        replace (mm //n kk) with (mm / kk).
        2: { eapply mod_0_iff_ceil_eq_floor_0 in Heq. rewrite Heq. auto.
             lia. }
        pose proof Heq.
        eapply div_exact in H17. rewrite <- H17. rewrite Heq0.
        rewrite (mul_comm _ (Datatypes.S _)). simpl.
        rewrite sub_add_distr. 2: lia.
        rewrite mul_comm.  rewrite <- Heq0.
        rewrite le_plus_minus_r.
        2: { rewrite H17.
             eapply plus_le_reg_l with (p:=kk).
             replace (kk + n0 * kk) with (Datatypes.S n0 * kk) by lia.
             rewrite <- Heq0.
             rewrite le_plus_minus_r.
             2: { rewrite <- H17.
                  assert (kk <= mm \/ mm < kk) by lia. inversion H19.
                  lia. eapply div_small in H20. rewrite H20 in H17.
                  rewrite mul_0_r in *. lia. }
             rewrite mul_comm.
             eapply mul_le_mono_l.
             eapply div_le_mono. lia. lia. }

        eapply forall_flatten_result_rev_all. rewrite rev_involutive.
        2: { eapply Forall_rev. eapply Forall_app.
             rewrite Forall_map. split.
             eapply Forall_forall. intros. auto.
             eauto. }
        2: { lia. }
        erewrite flatten_result_app.
        simpl. rewrite app_nil_r.
        rewrite flatten_result_nat_range_rec.
        rewrite mul_sub_distr_r.
        rewrite (mul_comm (mm/kk) kk). rewrite <- H17.
        rewrite <- Hlen at 1.
        replace (Datatypes.S (length l)) with (length (r0::l)) by reflexivity.
        rewrite <- (rev_involutive  (skipn  _ _)).        
        rewrite <- firstn_rev.
        rewrite Forall_app.
        split. eapply forall_firstn. eapply Forall_rev.
        eapply forall_firstn_ge. eauto. eapply div_mul_upper_bound. lia.
        rewrite <- Hlen at 1.
        replace (Datatypes.S (length l)) with (length (r0::l)) by reflexivity.
        rewrite <- (rev_involutive  (skipn  _ _)).        
        rewrite <- firstn_rev.
        rewrite firstn_all2.
        2: { rewrite rev_length. rewrite firstn_length. lia. }
        eapply Forall_rev.
        eapply forall_firstn_ge. eauto.
        assert (kk <= c \/ c < kk) by lia. cases H19. lia.
        eapply div_small_iff in H19. lia. lia.
        eapply Forall_map. eapply Forall_forall. intros. eauto. eauto. }
    }

    rewrite filter_until_0_cons in HHHH by lia.
    rewrite filter_until_0_cons in HHHH by lia.
    rewrite filter_until_0_cons in HHHH by lia.
    split.
    { (* middle part of split *)
      cases (k0 //n (Z.to_nat (eval_Zexpr_Z_total $0 k)) -
               k0 / Z.to_nat (eval_Zexpr_Z_total $0 k)). econstructor.
      pose proof (ceil_sub_floor_le_1
                    k0
                    (Z.to_nat (eval_Zexpr_Z_total $0 k))).
      assert (n0 = 0) by lia. subst.
      unfold split_result. simpl.
      rewrite skipn_map.
      rewrite skipn_nat_range.
      cases (Datatypes.S (Datatypes.length l) //n
            (Z.to_nat (eval_Zexpr_Z_total $0 k)) -
                 k0 / Z.to_nat (eval_Zexpr_Z_total $0 k)).
      { remember (Z.to_nat (eval_Zexpr_Z_total $0 k)). simpl length in *.
        rewrite <- Hlen in *. 
        assert (Datatypes.S (length l) //n n0 <= k0 /n0). lia.
        cases (Datatypes.S (length l) mod n0).
        - pose proof Heq1. eapply mod_0_iff_ceil_eq_floor_0 in H20. 2: lia.
          rewrite H20 in *.
          assert (k0 <= Datatypes.S (length l)) by lia.
          exfalso.
          rewrite (Nat.div_mod_eq k0 n0) in H21.
          eapply mul_le_mono_l with (p:=n0) in H19.
          cases (k0 mod n0).
          eapply mod_0_iff_ceil_eq_floor_0 in Heq2. lia. lia.
          eapply div_exact in Heq1. lia. lia.
        - cases (Datatypes.S (length l) //n n0 -
                   Datatypes.S (length l) /n0).
          eapply mod_0_iff_ceil_sub_floor_0 in Heq2. lia. lia.
          pose proof (ceil_sub_floor_le_1 (Datatypes.S (length l)) n0).
          assert (Datatypes.S (Datatypes.length l) //n n0 =
                    Datatypes.S (Datatypes.length l) / n0 + 1) by lia.
          exfalso.
          assert (k0 <= Datatypes.S (length l)) by lia.
          eapply div_le_mono with (c:=n0) in H22. lia. lia.
      } 
      simpl. econstructor. 2: eauto.
      cases rsh.
      { invert H15. }
      split. rewrite app_comm_cons. rewrite skipn_app. rewrite firstn_app.
      rewrite firstn_app. rewrite skipn_repeat. rewrite firstn_repeat.
      rewrite firstn_repeat. rewrite firstn_length. rewrite skipn_length.
      rewrite Forall_app.
      split.
      { rewrite firstn_firstn.
        rewrite min_l.
        2: { eapply lt_le_incl. eapply Nat.mod_upper_bound. lia. }
        rewrite (Nat.div_mod_eq k0
                                (Z.to_nat (eval_Zexpr_Z_total $0 k))) in H5.
        pose proof H5. rewrite firstn_add in H5.
        rewrite Forall_app in H5. invert H5.
        invert H2. eapply result_has_shape_result_shape_nat in H26.
        invert HHHH.
        cases n1. simpl in *. invert H22. lia. invert H22.
        erewrite gen_pad_filter_until_0.
        rewrite <- H25.
        erewrite gen_pad_filter_until_0 in H21. eauto. }
      { invert H2. eapply result_has_shape_result_shape_nat in H24.
        invert HHHH.
        cases n1. simpl in *. invert H20. lia. invert H20.
        rewrite H24.
        rewrite gen_pad_filter_until_0. rewrite <- H23.
        eapply Forall_repeat. eauto. }
      split. auto.
      split. rewrite app_comm_cons.
      rewrite skipn_app. rewrite firstn_app. rewrite skipn_app.
      rewrite firstn_app. rewrite Forall_app.
      split.
      { rewrite (Nat.div_mod_eq k0
                                (Z.to_nat (eval_Zexpr_Z_total $0 k))) in H16.
        rewrite Nat.add_comm in H16.
        rewrite <- skipn_skipn in H16.
        pose proof H16.
        rewrite skipn_firstn_comm.
        rewrite firstn_firstn.
        eapply forall_firstn_ge with (n:=l1).
        eapply Forall_forall. intros.
        eapply Forall_forall in H19.
        2: { eassumption. }
        invert H15. cases n1. invert H22. lia. invert H22.
        eapply result_has_shape_forall in H2.
        eapply Forall_forall in H20.
        2: { eapply forall_firstn. eapply forall_skipn. eapply forall_skipn.
             apply H2. } simpl in H20.
        eapply relate_pads_filter_until_0.
        eapply result_has_shape_filter_until_0. rewrite <- H23.
        erewrite <- result_has_shape_filter_until_0. eauto.
        rewrite <- H23.
        eapply relate_pads_filter_until_0.
        eauto.
        eauto.
        lia. }
      { rewrite skipn_repeat. rewrite firstn_repeat.
        rewrite skipn_repeat. rewrite firstn_repeat.
        pose proof H2. invert H19.
        eapply result_has_shape_result_shape_nat in H25. rewrite H25.
        eapply has_pad_size_of_relate_pads_gen_pad in H7.
        2: { eauto. }
        2: { eapply HP. }
        simpl in H7.
        cases (Z.to_nat (eval_Zexpr_Z_total $0 m)). lia.
        remember rev in H7. simpl in H7. rewrite <- repeat_cons in H7.
        subst. rewrite @rev_repeat in *. invs.
        rewrite @skipn_repeat in *. rewrite @firstn_repeat in *.
        rewrite <- Heq1 in *.
        rewrite min_r in H20 by lia.
        cases l1. simpl. rewrite min_0_l. rewrite sub_0_l.
        rewrite min_0_r. econstructor. 
        eapply Forall_repeat.
        invert H15. cases n1. invert H24. lia. invert H24.
        eapply relate_pads_filter_until_0.
        eapply result_has_shape_filter_until_0. rewrite <- H27.
        eapply result_has_shape_gen_pad.
        rewrite <- H27. invert H20. eauto. } 
      eauto. }
    
    (* last part of split *)
    remember (Z.to_nat (eval_Zexpr_Z_total $0 k)) as kk.
    remember (Z.to_nat (eval_Zexpr_Z_total $0 m)) as mm.
    unfold split_result. simpl length in * . rewrite Hlen.
    simpl.    
    cases ((c + (kk - mm mod kk) mod kk) //n kk -
              (c + (kk - mm mod kk) mod kk) / kk). econstructor.
    (* k doesn't divide c + added padding *)
    assert (n0 = 0).
    { pose proof (ceil_sub_floor_le_1
                    (c + (kk - mm mod kk) mod kk) kk). lia. }
    rewrite H17 in *. clear H17. clear n0.

    
    cases (mm mod kk).
    - (* kk divides mm *)
      rewrite sub_0_r in *. rewrite mod_same in * by lia.
      rewrite add_0_r in *.
      pose proof Heq0. eapply mod_0_iff_ceil_eq_floor_0 in H17. 2: lia.
      rewrite H17 in *.
      simpl repeat. rewrite app_nil_r.
      rewrite <- map_rev. rewrite skipn_map. rewrite firstn_map.
      unfold nat_range.
      replace (skipn (c / kk) (rev (nat_range_rec (mm / kk) 0))) with
        (rev (nat_range_rec (mm / kk - c / kk) 0)).
      2: { rewrite skipn_rev. rewrite length_nat_range_rec.
           rewrite firstn_nat_range_rec. rewrite min_l. reflexivity.
           lia. }
      rewrite firstn_rev_nat_range_rec.
      rewrite add_0_l.
      cases (mm / kk - c / kk). rewrite min_0_r. econstructor.
      rewrite (min_l 1) by lia. rewrite <- Heq1. simpl.
      econstructor. cases rsh. invert H15.
      split. auto.
      split.
      replace (kk * (mm / kk - c / kk - 1)) with
        (length (r0::l) - (length (r0::l) - (kk*(mm/kk- c / kk - 1)))) at 1.
      2: { rewrite sub_sub_distr. lia.
           simpl length. rewrite Hlen. rewrite (Nat.div_mod_eq mm kk) at 2.
           repeat rewrite mul_sub_distr_l. lia. lia. }
      rewrite <- (rev_involutive (skipn _ (r0::l))).
      rewrite <- firstn_rev. simpl length. rewrite Hlen.
      rewrite <- (firstn_skipn (length (r0::l) - c) (r0::l)).
      rewrite <- (rev_involutive (firstn _ (r0::l))).
      rewrite <- skipn_rev. simpl length. rewrite Hlen.
      rewrite rev_app_distr. rewrite firstn_app.
      rewrite rev_app_distr. rewrite firstn_app.
      rewrite rev_app_distr. rewrite firstn_app.
      repeat rewrite rev_length. repeat rewrite firstn_length.
      repeat rewrite skipn_length. repeat rewrite rev_length.
      repeat rewrite skipn_length. repeat rewrite firstn_length.
      repeat rewrite rev_length. rewrite skipn_length.
      simpl length. rewrite Hlen.
      rewrite (sub_sub_distr mm mm c) by lia.
      rewrite sub_diag. rewrite add_0_l. 
      rewrite rev_involutive. repeat rewrite mul_sub_distr_l.
      eapply div_exact in Heq0. rewrite <- Heq0.
      replace (skipn (mm - c) (r0 :: l)) with
        (rev (firstn c (rev (r0::l)))).
      2: { replace mm with (length (r0::l)) by (simpl; lia).
           rewrite firstn_rev.  rewrite rev_involutive. reflexivity. }
      rewrite rev_involutive.
      rewrite Forall_app. split.
      cases n1. invert H15. lia. invert H15.
      remember (Z.to_nat (eval_Zexpr_Z_total $0 m)) as mm.
      remember (Z.to_nat (eval_Zexpr_Z_total $0 k)) as kk.
      rewrite <- H20.
      rewrite gen_pad_filter_until_0. rewrite <- H21.
      rewrite <- gen_pad_filter_until_0.
      eapply forall_firstn. eapply Forall_rev.
      eapply forall_firstn. eapply Forall_rev.
      eapply forall_firstn. eauto. 2: lia.
      rewrite (min_l _ (mm-c)) by lia.
      cases (mm - (mm - kk * (c / kk) - kk * 1) - c).
      { simpl. rewrite firstn_nil. simpl. rewrite firstn_nil. eauto. }
      { rewrite (min_r _ c) by lia. rewrite <- Heq2.
        rewrite <- sub_add_distr in * by lia. rewrite mul_1_r in *.
        rewrite <- sub_add_distr.
        rewrite <- add_sub_swap.
        2: { rewrite Heq0.
             assert (mm / kk = Datatypes.S n0 + c /kk). lia.
             rewrite H19. rewrite mul_add_distr_l.
             rewrite (Nat.add_comm _ (kk*(c/kk))).
             rewrite (mul_comm _ (Datatypes.S _)). simpl.
             rewrite add_assoc. eapply le_plus_l. }
        replace (kk * (c / kk) + kk) with (c + ((kk - c  mod kk) mod kk)).
        2: { rewrite (Nat.div_mod_eq c kk) at 1.
             rewrite <- add_assoc. rewrite mod_id. auto. lia. unfold not.
             intros. eapply mod_0_iff_ceil_eq_floor_0 in H19. lia. lia. }
        rewrite sub_add_distr.
        rewrite add_sub.
        rewrite (sub_sub_distr mm).
        2: { assert (kk <= mm). lia.
             pose proof (Nat.mod_upper_bound (kk- c mod kk) kk). lia. }
        rewrite sub_diag. rewrite add_0_l.
        rewrite <- (mod_id c kk) at 2.
        rewrite add_sub. rewrite min_l.
        2: { eapply mod_le. lia. }
        rewrite sub_diag. econstructor. lia.
        unfold not. intros. eapply mod_0_iff_ceil_eq_floor_0 in H19. lia. lia.
        lia. 
      }
      split. auto.
      
      replace (kk * (mm / kk - c / kk - 1)) with
        (length (r0::l) - (length (r0::l) - (kk * (mm / kk - c / kk - 1)))).
      2: { repeat rewrite sub_sub_distr. lia.
           simpl length. rewrite Hlen. rewrite (Nat.div_mod_eq mm kk) at 2.
           repeat rewrite mul_sub_distr_l. lia. lia. }
      rewrite <- (rev_involutive (skipn _ (r0::l))).
      rewrite <- firstn_rev. simpl length. rewrite Hlen.
      rewrite <- (firstn_skipn c (rev (r0::l))).
      rewrite firstn_app. rewrite rev_app_distr. rewrite firstn_app.
      rewrite rev_app_distr. rewrite skipn_app.
      rewrite firstn_app. repeat rewrite rev_length. rewrite firstn_length.
      repeat rewrite firstn_length. repeat rewrite skipn_length.
      repeat rewrite rev_length. repeat rewrite firstn_length.
      repeat rewrite rev_length. repeat rewrite firstn_length.
      rewrite rev_length. simpl length. rewrite Hlen.
      rewrite (min_l c mm) by lia.
      rewrite (min_l (mm - kk * (mm / kk - c / kk - 1) - c) (mm-c)) by lia.
      2: eauto.
      eapply div_exact in Heq0. repeat rewrite mul_sub_distr_l.
      rewrite <- Heq0.      
      rewrite <- (sub_add_distr _ _ c).
      rewrite (Nat.add_comm _ c). rewrite (sub_add_distr _ c _). 2: lia.
      replace (kk * (c / kk)) with (c - c mod kk).
      2: { rewrite (Nat.div_mod_eq c kk) at 1. rewrite add_sub. lia. }
      rewrite (sub_sub_distr mm c).
      2: { eapply mod_le. lia. }
      2: lia.
      rewrite Forall_app.
      split. rewrite mul_1_r.
      rewrite (Nat.div_mod_eq c kk) at 4.
      repeat rewrite sub_add_distr.
      rewrite sub_add.
      2: { assert (c <= mm) by lia.
           rewrite (Nat.div_mod_eq c kk) in H19. lia. }
      rewrite <- (sub_add_distr _ _ kk).
      replace (kk * (c / kk) + kk) with (c + (kk - c mod kk)mod kk).
      2: { rewrite ( Nat.div_mod_eq c kk) at 1. rewrite <- add_assoc.
           rewrite mod_id. reflexivity. lia. unfold not.
           intros. eapply mod_0_iff_ceil_eq_floor_0 in H19. lia. lia. }       
      rewrite sub_add_distr.
      rewrite (sub_sub_distr (mm-c) (mm-c)).
      2: { assert (mm - c < kk \/ kk <= mm - c) by lia. cases H19.
           2: { pose proof (Nat.mod_upper_bound (kk- c mod kk) kk). lia. }
           rewrite (Nat.div_mod_eq c kk) at 2.
           rewrite sub_add_distr.
           cut (c mod kk + (kk - c mod kk) mod kk <= mm - kk * (c / kk)).
           lia. rewrite mod_id. rewrite Heq0. rewrite <- mul_sub_distr_l.
           rewrite Heq1. rewrite mul_comm. simpl. eapply le_plus_l. lia.
           unfold not. intros.
           eapply mod_0_iff_ceil_eq_floor_0 in H20. lia. lia. }
      rewrite sub_diag. rewrite add_0_l. 2: lia.
      rewrite <- (mod_id c kk) at 4. 2: lia.
      2: { unfold not. intros.
           eapply mod_0_iff_ceil_eq_floor_0 in H19. lia. lia. }
      rewrite add_sub.
      rewrite skipn_all2. rewrite firstn_nil.
      2: { rewrite rev_length. rewrite firstn_length. lia. }
      eauto.

      rewrite mul_1_r.
      rewrite (Nat.div_mod_eq c kk) at 3.
      rewrite (Nat.div_mod_eq c kk) at 6.
      rewrite (Nat.div_mod_eq c kk) at 13.
      rewrite (Nat.div_mod_eq c kk) at 16.
      rewrite (Nat.div_mod_eq c kk) at 21.
      repeat rewrite sub_add_distr.
      rewrite sub_add.
      2: { assert (c <= mm) by lia.
           rewrite (Nat.div_mod_eq c kk) in H19. lia. }
      rewrite <- (sub_add_distr _ _ kk).
      replace (kk * (c / kk) + kk) with (c + (kk - c mod kk)mod kk).
      2: { rewrite ( Nat.div_mod_eq c kk) at 1. rewrite <- add_assoc.
           rewrite mod_id. reflexivity. lia. unfold not.
           intros. eapply mod_0_iff_ceil_eq_floor_0 in H19. lia. lia. }
      rewrite sub_add_distr.
      rewrite (sub_sub_distr (mm-c) (mm-c)).
      2: { assert (mm - c < kk \/ kk <= mm - c) by lia. cases H19.
           2: { pose proof (Nat.mod_upper_bound (kk- c mod kk) kk). lia. }
           rewrite (Nat.div_mod_eq c kk) at 2.
           rewrite sub_add_distr.
           cut (c mod kk + (kk - c mod kk) mod kk <= mm - kk * (c / kk)).
           lia. rewrite mod_id. rewrite Heq0. rewrite <- mul_sub_distr_l.
           rewrite Heq1. rewrite mul_comm. simpl. eapply le_plus_l. lia.
           unfold not. intros.
           eapply mod_0_iff_ceil_eq_floor_0 in H20. lia. lia. }
      rewrite sub_diag. rewrite add_0_l. 2: lia.
      rewrite <- (mod_id c kk) at 4. 2: lia.
      2: { unfold not. intros.
           eapply mod_0_iff_ceil_eq_floor_0 in H19. lia. lia. }
      rewrite minus_plus.
      replace (kk - ((kk - c mod kk) mod kk) mod kk) with
        (c mod kk).
      2: { rewrite mod_mod by lia.
           rewrite <- (mod_id c kk) at 2. rewrite add_sub. auto. lia.
           unfold not. intros.
           eapply mod_0_iff_ceil_eq_floor_0 in H19. lia. lia. }
      replace (kk - (kk - c mod kk) mod kk) with (c mod kk).
      2: { rewrite <- (mod_id c kk) at 2. rewrite add_sub. auto. lia.
           unfold not. intros.
           eapply mod_0_iff_ceil_eq_floor_0 in H19. lia. lia. }
      rewrite <- sub_add_distr.
      replace (Init.Nat.min (c mod kk)
           (Init.Nat.min (mm - (mm - (c + (kk - c mod kk) mod kk))) c) - 
         c mod kk) with 0 by lia.
      rewrite sub_0_r.
      rewrite firstn_all2 with (n:=kk).
      2: { rewrite rev_length. rewrite firstn_length.
           pose proof (Nat.mod_upper_bound (kk - c mod kk) kk). lia. }
      rewrite rev_involutive.
      rewrite (min_comm _ c).
      rewrite min_assoc. rewrite (min_l _ c).
      2: { eapply mod_le. lia. }
      rewrite sub_sub_distr.
      2: { rewrite Heq0. rewrite (Nat.div_mod_eq c kk) at 1.
           rewrite <- add_assoc. rewrite mod_id.
           cut (kk <= (kk *(mm/kk) - kk*(c/kk))). lia.
           rewrite <- mul_sub_distr_l.
           rewrite Heq1. rewrite mul_comm. simpl. eapply le_plus_l. lia.
           unfold not.
           intros. eapply mod_0_iff_ceil_eq_floor_0 in H19. lia. lia. }
      2: lia.
      rewrite sub_diag. rewrite add_0_l. rewrite (min_l (c mod kk)).
      2: { eapply le_trans. eapply mod_le. lia. lia. }
      rewrite sub_diag. remember rev. simpl. subst l0.
      rewrite firstn_firstn.
      eapply forall_firstn_ge with (n:=r).
      2: { lia. }
      cases n1. invert H15. lia. invert H15.
      eapply result_has_shape_forall in H2.
      eapply Forall_forall. intros.
      eapply Forall_forall in H18.
      eapply Forall_forall in H2.
      2: { eapply In_rev. eapply in_skipn. eapply in_firstn. eauto. }
      eapply relate_pads_filter_until_0.
      eapply result_has_shape_filter_until_0. rewrite <-H21.
      rewrite <- result_has_shape_filter_until_0. eauto.
      rewrite <- H21.
      eapply relate_pads_filter_until_0. eauto. eauto. eauto.
    - (* k doesn't divide m *)
      rewrite <- Heq0 in *.
      assert (c < mm) as Hnew.
      { assert (c = mm \/ c < mm) by lia. cases H17. rewrite H17 in *.
        rewrite (Nat.div_mod_eq mm kk) in Heq at 3.
        rewrite (Nat.div_mod_eq mm kk) in Heq at 1.
        rewrite <- add_assoc in Heq. rewrite mod_id in Heq by lia.
        assert ((kk* (mm/kk) + kk ) mod kk = 0).
        rewrite <- mul_succ_r. rewrite mul_comm. rewrite mod_mul. lia. lia.
        eapply mod_0_iff_ceil_sub_floor_0 in H19. lia. lia. lia. }
      
      replace (mm //n kk) with (Datatypes.S (mm/kk)).
      2: { cases (mm //n kk - mm /kk).
           eapply mod_0_iff_ceil_sub_floor_0 in Heq1. lia. lia.
           pose proof (ceil_sub_floor_le_1 mm kk).
           lia. }
      unfold nat_range.
      rewrite succ_nat_range_rec_app_end.
      rewrite map_app. rewrite rev_app_distr.
      simpl rev. rewrite add_0_r.
      rewrite app_comm_cons.
      repeat rewrite skipn_app. simpl length.
      rewrite Hlen. replace (kk * (mm / kk) - mm) with 0.
      2: { rewrite (Nat.div_mod_eq mm kk) at 2.
           rewrite sub_add_distr. rewrite sub_diag. lia. }
      simpl skipn.
      erewrite map_nat_range_rec_extensionality.
      2: { intros. rewrite app_comm_cons.
           rewrite skipn_app. rewrite firstn_app.
           rewrite skipn_length. simpl length. rewrite Hlen.
           replace (kk - (mm - kk * x)) with 0.
           2: { rewrite (Nat.div_mod_eq mm kk).
                rewrite add_sub_swap .
                2: { eapply mul_le_mono_l. lia. }
                rewrite <- mul_sub_distr_l.
                cases (mm / kk - x). lia.
                rewrite mul_comm. simpl.
                repeat rewrite sub_add_distr. rewrite sub_diag. lia. }
           simpl. rewrite app_nil_r. reflexivity. }
      cases rsh. invert H15. cases n1. invert H15. lia. invert H15.
      rewrite <- H19. pose proof H2 as Hshs.
      invert H2.
      remember (Z.to_nat (eval_Zexpr_Z_total $0 k)) as kk.
      remember (Z.to_nat (eval_Zexpr_Z_total $0 m)) as mm.
      rewrite firstn_app. rewrite skipn_length. simpl length. rewrite Hlen.
      rewrite <- map_rev.
      rewrite skipn_map. rewrite firstn_map.
      rewrite skipn_rev_nat_range_rec.
      rewrite firstn_rev_nat_range_rec. rewrite add_0_l.
      cases ((c + (kk - mm mod kk) mod kk) / kk).
      { simpl. rewrite min_0_l. simpl.
        rewrite firstn_app. rewrite firstn_repeat. rewrite skipn_length.
        simpl length. rewrite Hlen. rewrite <- mod_eq by lia.
        rewrite (min_l (_ mod _)).
        2: { eapply mod_le. lia. }
        rewrite (mod_small (c + (kk - mm mod kk) mod kk)).
        2: { eapply div_small_iff. lia. lia. }
        econstructor.
        assert (c < mm mod kk).
        { eapply div_small_iff in Heq1.
          rewrite <- (mod_id mm kk) in Heq1 at 4. lia. lia. lia. lia. }
        rewrite gen_pad_filter_until_0. rewrite <- H20.
        rewrite <- gen_pad_filter_until_0.
        split. econstructor.
        split.
        { rewrite rev_app_distr. rewrite firstn_app.
          rewrite rev_length. rewrite rev_repeat. rewrite repeat_length.
          rewrite firstn_repeat. rewrite Forall_app.
          split. eapply Forall_repeat.
          eapply result_has_shape_result_shape_nat in H24.
          rewrite H24. rewrite <- gen_pad_filter_until_0. eauto.
          replace (kk * (mm / kk))
            with (length (r0::l) - (length (r0::l) - kk*(mm/kk))).
          2: { rewrite sub_sub_distr. lia. simpl length. rewrite Hlen.
               rewrite (Nat.div_mod_eq mm kk) at 2.
               lia. lia. }
          rewrite <- (rev_involutive (skipn _ _)).
          rewrite <- firstn_rev.
          simpl length. rewrite Hlen. rewrite add_sub.
          rewrite firstn_all2 with (n:=kk).
          2: { rewrite rev_length. rewrite firstn_length.
               rewrite rev_length. simpl length. rewrite Hlen.
               rewrite min_l by lia.
               rewrite (Nat.div_mod_eq mm kk) at 1.
               rewrite minus_plus. pose proof (Nat.mod_upper_bound mm kk).
               lia. }
          rewrite rev_involutive. rewrite firstn_firstn.
          eapply forall_firstn_ge. eauto.
          lia. }
        split. auto.
        rewrite rev_app_distr. rewrite skipn_app. rewrite firstn_app.
        rewrite rev_length. rewrite repeat_length. rewrite skipn_length.
        rewrite rev_length. rewrite repeat_length. rewrite rev_repeat.
        rewrite skipn_repeat. rewrite firstn_repeat.
        rewrite Forall_app.
        replace ((kk - mm mod kk) mod kk - (c + (kk - mm mod kk) mod kk))
          with 0 by lia.
        rewrite min_0_l. split. econstructor.
        rewrite sub_0_r.
        replace (kk * (mm / kk))
          with (length (r0::l) - (length (r0::l) - kk*(mm/kk))).
        2: { rewrite sub_sub_distr. lia. simpl length. rewrite Hlen.
             rewrite (Nat.div_mod_eq mm kk) at 2.
             lia. lia. }
        rewrite <- (rev_involutive (skipn _ (r0::l))).
        rewrite <- firstn_rev.
        simpl length. rewrite Hlen. rewrite add_sub.
        rewrite firstn_all2 with (n:=kk).
        2: { rewrite rev_length. rewrite firstn_length. rewrite rev_length.
             simpl length. rewrite Hlen.
             rewrite min_l by lia.
             rewrite (Nat.div_mod_eq mm kk) at 1.
             pose proof (Nat.mod_upper_bound mm kk). lia. }
        rewrite rev_involutive.
        rewrite skipn_firstn_comm.
        rewrite firstn_firstn.
        eapply forall_firstn_ge with (n:=r).
        2: { lia. }
        eapply Forall_forall. intros.
        eapply result_has_shape_forall in Hshs.
        eapply Forall_forall in H18.
        eapply Forall_forall in Hshs.
        2: { eapply In_rev. eapply in_skipn. eapply in_firstn. eauto. }
        eapply relate_pads_filter_until_0.
        eapply result_has_shape_filter_until_0.
        rewrite <- H20.
        erewrite <- result_has_shape_filter_until_0. eauto.        
        rewrite <- H20.
        eapply relate_pads_filter_until_0. eauto. eauto. eauto.
        auto.
      }
      { simpl skipn. rewrite skipn_nil. rewrite app_nil_l. rewrite sub_0_r.
        rewrite <- Heq1. rewrite map_rev. eapply Forall_rev.
        eapply Forall_map. eapply Forall_forall. intros.
        assert (mm mod kk <= c).
        { assert ( c < mm mod kk \/ mm mod kk <= c) by lia. cases H15.
          2: lia.
          rewrite div_small in Heq1. lia.
          rewrite <- (mod_id mm kk) at 4. lia. lia. lia. }
        rewrite <- Heq1 in *. eapply In_nat_range_rec in H2. cases H2.
        assert (x = mm / kk - ((c + (kk - mm mod kk) mod kk) / kk - 1) - 1).
        lia. rewrite H22 in *. clear H22. clear x. clear H2. clear H17.
        split. auto.
        (* k doesn't divide c *)
        (* k doesn't divide m *)
        (* k doesn't divide c + added padding *)
        (* c < m *)
        (* k < c + padding *)
        (* c/kk <= (c + padding) / kk <= c //kk *)
        split.
        { rewrite <- (firstn_skipn (length (r0::l) - c) (r0::l)).
          rewrite <- (rev_involutive (skipn _ (r0::l))).
          rewrite <- firstn_rev.
          rewrite skipn_app. rewrite firstn_app.
          rewrite firstn_length. rewrite skipn_length. rewrite firstn_length.
          simpl length. rewrite Hlen. rewrite (min_l (mm-c)) by lia.
          rewrite rev_app_distr. rewrite firstn_app.
          rewrite rev_length. rewrite firstn_length. rewrite skipn_length.
          rewrite rev_length.
          rewrite Forall_app. split.
          { eapply forall_firstn. eapply Forall_rev.
            eapply forall_firstn. eapply forall_skipn. eapply Forall_rev.
            rewrite gen_pad_filter_until_0. rewrite <- H20.
            rewrite <- gen_pad_filter_until_0. eauto. }
          rewrite firstn_length. rewrite rev_length. simpl length.
          rewrite Hlen. rewrite (min_l c mm) by lia.
          repeat rewrite <- sub_add_distr. rewrite sub_add by lia.
          repeat rewrite sub_add_distr.
          assert (kk * (mm / kk - (c + (kk - mm mod kk) mod kk) / kk) <=
                    mm - c).
          { rewrite (Nat.div_mod_eq mm kk) at 3.
            rewrite (Nat.div_mod_eq c kk) at 2. rewrite sub_add_distr.
            rewrite mul_sub_distr_l.
            rewrite (Nat.div_mod_eq c kk) at 1.
            rewrite <- add_assoc. rewrite (mul_comm kk (c/kk)).
            rewrite div_add_l by lia. rewrite mul_add_distr_l.
            rewrite sub_add_distr.
            rewrite add_sub_swap.
            2: { rewrite mul_comm. eapply mul_le_mono_l. eapply div_le_mono.
                 lia. lia. }
            rewrite (mul_comm (c/kk) kk).
            assert (c mod kk < mm mod kk \/ mm mod kk <= c mod kk) by lia.
            cases H2.
            rewrite (div_small (_ + _) kk).
            2: { rewrite <- (mod_id mm kk) at 5. lia. lia. lia. }
            rewrite mul_0_r. rewrite sub_0_r. lia.
            pose proof (add_mod_div_bound c (kk - mm mod kk) kk).
            cases ((c mod kk + (kk - mm mod kk) mod kk) / kk).
            { eapply div_small_iff in Heq2. 2: lia.
              rewrite <- (mod_id mm kk) in Heq2 at 5 by lia. lia. }
            assert (n3 = 0) by lia. rewrite H22 in *. clear H22. clear n3.
            rewrite mul_1_r.
            pose proof (Nat.mod_upper_bound c kk). lia. }
          replace (kk * (mm / kk - (c + (kk - mm mod kk) mod kk) / kk)
                   - (mm - c)) with 0 by lia.
          rewrite sub_0_r.
          assert (c mod kk <> mm mod kk).
          { unfold not. intros.
            rewrite (Nat.div_mod_eq c kk) in Heq.
            repeat rewrite <- add_assoc in Heq.
            rewrite H17 in Heq.
            rewrite mod_id in * by lia.
            replace (kk* (c/kk) + kk) with (kk * (c/kk + 1)) in * by lia.
            rewrite mul_comm in Heq.
            rewrite nat_mul_div_id in Heq by lia.
            rewrite div_mul in Heq by lia. lia. }
          assert (c mod kk < mm mod kk \/ mm mod kk < c mod kk) by lia.
          cases H22.
          - replace ((c + (kk - mm mod kk) mod kk) / kk) with (c/kk) in *.
            2: { rewrite (Nat.div_mod_eq c kk) at 2.
                 rewrite <- add_assoc. rewrite (mul_comm kk).
                 rewrite div_add_l by lia.
                 rewrite (div_small (_ + _) kk). lia.
                 pose proof (mod_id c kk). pose proof (mod_id mm kk). lia. }
            assert (kk <= c \/ c < kk) by lia. cases H23.
            2: { rewrite (mod_small c) in * by lia. lia. }
            rewrite mul_sub_distr_l.
            rewrite (Nat.div_mod_eq mm kk) at 2.
            rewrite (Nat.div_mod_eq c kk) at 2.
            rewrite sub_add_distr.
            rewrite add_sub_swap.
            2: { eapply mul_le_mono_l. eapply div_le_mono. lia. lia. }
            rewrite <- add_sub_assoc by lia.
            rewrite minus_plus.
            rewrite min_l by lia.
            rewrite add_mod_idemp_r by lia.
            rewrite add_mod by lia.
            rewrite add_mod_idemp_r by lia.
            rewrite (mod_small (c mod kk + _)).
            2: { cases (c mod kk). lia.
                 rewrite <- Heq2.
                 rewrite <- (mod_id c kk) at 4 by lia.
                 pose proof (mod_id c kk). pose proof (mod_id mm kk). lia. }
            rewrite (sub_sub_distr kk).
            2: lia.
            2: { pose proof (Nat.mod_upper_bound mm kk). lia. }
            rewrite (Nat.add_comm).
            rewrite sub_diag. econstructor.
          - replace ((c + (kk - mm mod kk) mod kk) / kk) with (c/kk + 1) in *.
            2: { rewrite (Nat.div_mod_eq c kk) at 2. rewrite <- add_assoc.
                 rewrite (mul_comm kk). rewrite div_add_l by lia.
                 f_equal.
                 pose proof (add_mod_div_bound c (kk - mm mod kk) kk).
                 cases ((c mod kk + (kk - mm mod kk) mod kk) / kk).
                 eapply div_small_iff in Heq2.
                 rewrite <- (mod_id c kk) in Heq2 at 5.
                 pose proof (mod_id c kk). pose proof (mod_id mm kk). lia.
                 lia. lia. lia. lia. }
            rewrite sub_add_distr.
            rewrite (Nat.div_mod_eq mm kk) at 2.
            rewrite (Nat.div_mod_eq c kk) at 2.
            rewrite mul_sub_distr_l. rewrite mul_1_r.
            rewrite mul_sub_distr_l.
            rewrite sub_add_distr.
            rewrite add_sub_swap.
            2: { eapply mul_le_mono_l. eapply div_le_mono. lia. lia. }
            rewrite sub_add_distr in *.
            rewrite <- mul_sub_distr_l.
            cases (mm / kk - c / kk).
            { rewrite mul_0_r. simpl.
              rewrite sub_0_r.
              replace (mm mod kk - c mod kk) with 0 by lia.
              rewrite sub_0_r.
              rewrite add_mod_idemp_r by lia.
              rewrite add_mod by lia.
              rewrite add_mod_idemp_r by lia.
              assert (c < kk \/ kk <= c) by lia. cases H23.
              + rewrite min_r by lia. rewrite (mod_small c) in * by lia.
                rewrite (div_small c kk) in * by lia.
                rewrite sub_0_r in *. simpl in *. rewrite mul_0_r in *.
                eapply div_small_iff in Heq2.
                2: { lia. }
                rewrite mod_small in H22 by lia. lia.
              + rewrite min_l by lia. 
                replace ((c mod kk + (kk - mm mod kk)) mod kk - kk) with 0.
                2: { pose proof (Nat.mod_upper_bound
                                   (c mod kk + (kk - mm mod kk)) kk). lia. }
                econstructor. }
            { rewrite <- Heq2 in *.
              rewrite add_sub_swap.
              2: { rewrite Heq2. rewrite mul_comm. simpl.
                   pose proof (Nat.mod_upper_bound c kk). lia. }
              rewrite <-sub_sub_distr.
              2: lia.
              2: { rewrite Heq2. rewrite mul_comm. simpl.
                   pose proof (Nat.mod_upper_bound c kk). lia. }
              remember (kk * (mm / kk - c / kk)).
              remember (c mod kk - mm mod kk).
              rewrite <- sub_add_distr.
              rewrite (Nat.add_comm n5).
              rewrite sub_add_distr.
              rewrite (sub_sub_distr n4).
              2: { rewrite Heqn4. rewrite Heq2. rewrite mul_comm. simpl.
                   eapply le_plus_l. }
              rewrite sub_diag. simpl.
              rewrite sub_sub_distr.
              2: { pose proof (Nat.mod_upper_bound c kk). lia. }
              rewrite sub_diag. simpl. rewrite min_l.
              2: { rewrite Heqn5. pose proof (mod_le c kk). lia. }
              rewrite Heqn5.
              rewrite (Nat.div_mod_eq c kk) at 1.
              rewrite add_mod_idemp_r by lia.
              rewrite add_mod by lia.
              rewrite add_mod_idemp_r by lia.
              rewrite (Nat.add_comm (_ * _)).
              rewrite (mul_comm kk (c/kk)).
              rewrite mod_add. 2: lia. 2: lia. 2: lia.
              rewrite mod_mod. 2: lia.
              replace (kk - mm mod kk) with
                ((kk - c mod kk) mod kk + (kk - mm mod kk - ((kk - c mod kk) mod kk))).
              2: { rewrite <- le_plus_minus. lia.
                   pose proof (mod_id c kk). pose proof (mod_id mm kk). lia. }
              
              rewrite add_assoc. rewrite mod_id.
              2: lia.
              2: { lia. }              
              rewrite <-sub_add_distr.
              replace kk with (1*kk) at 1 by lia. rewrite Nat.add_comm.
              rewrite mod_add by lia.
              rewrite (mod_small (kk - c mod kk)).
              2: { cases (c mod kk). lia. lia. }
              rewrite mod_small by lia.
              rewrite <- sub_add_distr.
              rewrite add_sub_assoc by lia.
              rewrite <- add_assoc.
              replace (kk - c mod kk + c mod kk) with kk.
              2: { rewrite <- (mod_id c kk) at 1 by lia.
                   rewrite (mod_small (_ - _)). lia. lia. }
              rewrite minus_plus.
              rewrite sub_diag. econstructor.
            }
        }
        split. auto.
        rewrite <- (firstn_skipn (length (r0::l) - c) (r0::l)).
        rewrite <- (rev_involutive (firstn _ (r0::l))).
        rewrite <- skipn_rev.          
        rewrite skipn_app. rewrite firstn_app. rewrite skipn_length.
        rewrite rev_length. rewrite skipn_length.
        rewrite rev_length. 
        simpl length. rewrite Hlen.
        rewrite rev_app_distr. rewrite skipn_app.
        rewrite rev_length. rewrite firstn_length.
        rewrite skipn_length. rewrite skipn_length. simpl length.
        rewrite Hlen. rewrite firstn_app.
        rewrite skipn_length. rewrite rev_length. rewrite firstn_length.
        rewrite skipn_length. rewrite skipn_length.
        simpl length. rewrite Hlen.
        rewrite (sub_sub_distr mm mm c).
        2: { lia. }
        2: { lia. }
        rewrite sub_diag. rewrite add_0_l. 
        repeat rewrite <- sub_add_distr.
        rewrite sub_add by lia.
        assert (kk * (mm / kk - (c + (kk - mm mod kk) mod kk) / kk) <=
                  mm - c).
        { rewrite (Nat.div_mod_eq mm kk) at 3.
          rewrite (Nat.div_mod_eq c kk) at 2. rewrite sub_add_distr.
          rewrite mul_sub_distr_l.
          rewrite (Nat.div_mod_eq c kk) at 1.
          rewrite <- add_assoc. rewrite (mul_comm kk (c/kk)).
          rewrite div_add_l by lia. rewrite mul_add_distr_l.
          rewrite sub_add_distr.
          rewrite add_sub_swap.
          2: { rewrite mul_comm. eapply mul_le_mono_l. eapply div_le_mono.
               lia. lia. }
          rewrite (mul_comm (c/kk) kk).
          assert (c mod kk < mm mod kk \/ mm mod kk <= c mod kk) by lia.
          cases H2.
          rewrite (div_small (_ + _) kk).
          2: { rewrite <- (mod_id mm kk) at 5. lia. lia. lia. }
          rewrite mul_0_r. rewrite sub_0_r. lia.
          pose proof (add_mod_div_bound c (kk - mm mod kk) kk).
          cases ((c mod kk + (kk - mm mod kk) mod kk) / kk).
          { eapply div_small_iff in Heq2. 2: lia.
            rewrite <- (mod_id mm kk) in Heq2 at 5 by lia. lia. }
          assert (n3 = 0) by lia. rewrite H22 in *. clear H22. clear n3.
          rewrite mul_1_r.
          pose proof (Nat.mod_upper_bound c kk). lia. }
        replace (kk * (mm / kk - (c + (kk - mm mod kk) mod kk) / kk)
                   - (mm - c)) with 0 by lia.
        rewrite sub_0_r.
        assert (c mod kk <> mm mod kk).
        { unfold not. intros.
          rewrite (Nat.div_mod_eq c kk) in Heq.
          repeat rewrite <- add_assoc in Heq.
          rewrite H17 in Heq.
          rewrite mod_id in * by lia.
          replace (kk* (c/kk) + kk) with (kk * (c/kk + 1)) in * by lia.
          rewrite mul_comm in Heq.
          rewrite nat_mul_div_id in Heq by lia.
          rewrite div_mul in Heq by lia. lia. }

        rewrite Forall_app.
        split.
        { simpl.
          assert (c mod kk < mm mod kk \/ mm mod kk < c mod kk) by lia.
          cases H22.
          - rewrite skipn_all2. rewrite firstn_nil. econstructor.
            rewrite rev_length. rewrite firstn_length.
            rewrite skipn_length. simpl length. rewrite H21.
            rewrite (sub_sub_distr mm mm c) by lia. rewrite sub_diag.
            rewrite add_0_l.          
            rewrite (Nat.div_mod_eq c kk) at 2.
            rewrite <- add_assoc. rewrite (mul_comm kk (c/kk)).
            rewrite div_add_l by lia.
            rewrite (Nat.div_mod_eq c kk) in H2 at 1.
            rewrite <- add_assoc in H2. rewrite (mul_comm kk (c/kk)) in H2.
            rewrite div_add_l in H2 by lia.
            rewrite sub_add_distr in *.
            replace ((c mod kk + (kk - mm mod kk) mod kk) / kk) with 0 in *.
            2: { rewrite div_small. lia.
                 cases (c mod kk).
                 pose proof (Nat.mod_upper_bound (kk - mm mod kk) kk). lia.
                 rewrite <- Heq2.
                 rewrite <- (mod_id mm kk) at 5 by lia.
                 lia. }
            rewrite add_0_r in *.
            rewrite sub_0_r in *.
            rewrite (Nat.div_mod_eq mm kk) at 1.
            rewrite (Nat.div_mod_eq c kk) at 1.
            cases (mm / kk - c /kk).
            + rewrite mul_0_r. rewrite sub_0_r.
              rewrite sub_add_distr.
              assert (mm / kk = c / kk).
              { assert (c / kk <= mm/ kk).
                eapply div_le_mono. lia. lia. lia. }
              rewrite H23. rewrite minus_plus.
              rewrite sub_sub_distr.
              2: { lia. }
              2: { pose proof (Nat.mod_upper_bound mm kk). lia. }
              cases (c / kk).
              { eapply div_small_iff in Heq3.
                rewrite (mod_small c kk) in * by lia.
                rewrite sub_0_r in *. eapply div_small_iff in Heq2.
                rewrite (mod_small mm kk) in * by lia. lia. lia. lia. }
              rewrite (Nat.div_mod_eq c kk) at 2.
              rewrite min_l.
              2: { eapply plus_le_compat_r. lia. }
              rewrite <- (mod_small (kk - mm mod kk + c mod kk) kk).
              2: { rewrite <- (mod_id mm kk) at 4 by lia.
                   rewrite (mod_small (kk - mm mod kk) kk) by lia.
                   lia. }
              rewrite (add_mod c).
              rewrite mod_mod. rewrite (mod_small (kk - mm mod kk)) by lia.
              rewrite Nat.add_comm. lia. lia. lia.
            + rewrite <- Heq2.
              cases (c/kk).
              eapply div_small_iff in Heq3.
              rewrite (mod_small c kk) in * by lia. lia. lia.
              rewrite <- Heq3. rewrite sub_add_distr.
              rewrite add_sub_swap.
              2: { eapply mul_le_mono_l. eapply div_le_mono. lia. lia. }
              rewrite <- mul_sub_distr_l. rewrite <- add_sub_assoc by lia.
              rewrite minus_plus.
              rewrite min_l.
              2: { assert (c < kk \/ kk <= c) by lia. cases H23.
                   eapply div_small_iff in H23. lia. lia. lia. }
              rewrite sub_sub_distr. 2: lia.
              2: { pose proof (Nat.mod_upper_bound mm kk). lia. }
              rewrite (Nat.div_mod_eq c kk) at 2.
              rewrite <- (mod_small (kk - mm mod kk + c mod kk) kk).
              2: { rewrite <- (mod_id mm kk) at 4 by lia.
                   rewrite (mod_small (kk - mm mod kk) kk) by lia.
                   lia. }
              rewrite <- add_assoc. rewrite (Nat.add_comm (_ * _)).
              rewrite (mul_comm kk). rewrite mod_add by lia.
              rewrite (add_mod (c mod kk)) by lia.
              repeat rewrite mod_mod by lia.
              rewrite (mod_small (kk - mm mod kk)) by lia.
              rewrite Nat.add_comm. lia. 
          - rewrite (Nat.div_mod_eq c kk) in H2 at 1.
            rewrite <- add_assoc in *.
            rewrite (mul_comm kk (c/kk)) in H2.
            rewrite div_add_l in H2 by lia.
            rewrite (Nat.div_mod_eq c kk) at 4.
            rewrite <- add_assoc.
            rewrite (mul_comm kk (c/kk)). rewrite div_add_l by lia.
            replace ((c mod kk + (kk - mm mod kk) mod kk) / kk) with 1 in *.
            2: { pose proof (add_mod_div_bound c (kk - mm mod kk) kk).
                 cases ((c mod kk + (kk - mm mod kk) mod kk) / kk). 2: lia.
                 eapply div_small_iff in Heq2.
                 rewrite <- (mod_id mm kk) in Heq2 at 5 by lia. lia. lia. }
            repeat rewrite sub_add_distr in *.
            rewrite add_mod.
            rewrite (Nat.div_mod_eq mm kk) at 3.
            rewrite (Nat.div_mod_eq c kk) at 3.
            rewrite sub_add_distr.
            rewrite add_sub_swap.
            2: { eapply mul_le_mono_l. eapply div_le_mono. lia. lia. }
            2: { lia. }
            rewrite mul_sub_distr_l. rewrite mul_1_r.
            rewrite <- mul_sub_distr_l.
            repeat rewrite <- sub_add_distr.
            rewrite (Nat.add_comm (c mod kk)).
            rewrite sub_add_distr.
            cases (mm / kk - c /kk).
            { rewrite (Nat.div_mod_eq c kk) in Hnew.
              rewrite (Nat.div_mod_eq mm kk) in Hnew.
              assert (mm / kk = c / kk).
              { assert (c / kk <= mm/ kk).
                eapply div_le_mono. lia. lia. lia. }
              rewrite H23 in *. lia. }
            rewrite <- Heq2.
            rewrite add_sub_swap.
            2: { pose proof (Nat.mod_upper_bound c kk). rewrite Heq2.
                 rewrite mul_comm. simpl. lia. }
            rewrite <- sub_sub_distr.
            2: { lia. }
            2: { rewrite Heq2. rewrite mul_comm. simpl.
                 pose proof (Nat.mod_upper_bound c kk). lia. }
            rewrite <- sub_add_distr.
            rewrite (Nat.add_comm (_ - _) (_ - _)).
            rewrite sub_add_distr.
            rewrite (sub_sub_distr _ _ kk).
            2: { rewrite Heq2. rewrite mul_comm. simpl. eapply le_plus_l. }
            2: lia.
            rewrite sub_diag. simpl.
            rewrite sub_sub_distr.
            2: { pose proof (Nat.mod_upper_bound c kk). lia. }
            rewrite sub_diag. simpl.
            rewrite mod_mod.
            rewrite skipn_all2. rewrite firstn_nil. econstructor.
            rewrite rev_length. rewrite firstn_length.
            rewrite skipn_length. simpl length. rewrite H21.
            rewrite sub_sub_distr by lia. rewrite sub_diag. simpl.
            rewrite min_l.
            2: { pose proof (mod_le c kk). lia. }
            2: lia.
            2: lia.
            rewrite (mod_small (kk - mm mod kk)) by lia.
            replace (kk - mm mod kk) with
              (kk - c mod kk + (kk - mm mod kk - (kk - c mod kk))).
            2: { rewrite le_plus_minus_r. lia. lia. }
            rewrite (Nat.add_comm).            
            repeat rewrite add_assoc.
            rewrite <- (mod_small (kk - c mod kk) kk) at 1 by lia.
            rewrite mod_id by lia.
            rewrite (Nat.add_comm).
            replace kk with (1*kk) at 7 by lia. rewrite mod_add by lia.
            rewrite (mod_small (_ - _) kk) by lia.
            rewrite <- (sub_add_distr).
            rewrite (Nat.add_comm). rewrite sub_add_distr.
            rewrite sub_sub_distr.
            2: { pose proof (Nat.mod_upper_bound c kk). lia. }
            2: lia.
            rewrite sub_diag. lia. }
        assert (c mod kk < mm mod kk \/ mm mod kk < c mod kk) by lia.
        cases H22.
        - rewrite (Nat.div_mod_eq c kk) at 10.
          rewrite (Nat.div_mod_eq c kk) at 8.
          rewrite (Nat.div_mod_eq c kk) at 3.
          rewrite <- add_assoc. rewrite (mul_comm kk (c/kk)).
          rewrite div_add_l by lia.
          rewrite (Nat.div_mod_eq c kk) in H2 at 1.
          rewrite <- add_assoc in H2. rewrite (mul_comm kk (c/kk)) in H2.
          rewrite div_add_l in H2 by lia.
          rewrite sub_add_distr in *.
          replace ((c mod kk + (kk - mm mod kk) mod kk) / kk) with 0 in *.
          2: { rewrite div_small. lia.
               cases (c mod kk).
               pose proof (Nat.mod_upper_bound (kk - mm mod kk) kk). lia.
               rewrite <- Heq2.
               rewrite <- (mod_id mm kk) at 5 by lia. lia. }
          rewrite add_0_r in *.
          rewrite sub_0_r in *.
          rewrite (Nat.div_mod_eq mm kk) at 6.
          rewrite (Nat.div_mod_eq mm kk) at 2.
          rewrite (Nat.div_mod_eq c kk) at 7.
          rewrite (Nat.div_mod_eq c kk) at 2.
          repeat rewrite sub_add_distr.
          rewrite add_sub_swap.
          2: { eapply mul_le_mono_l. eapply div_le_mono. lia. lia. }
          rewrite <- mul_sub_distr_l. rewrite <- add_sub_assoc by lia.
          rewrite minus_plus.
          rewrite (skipn_rev (_ *_)).
          rewrite firstn_rev.
          rewrite rev_involutive.
          rewrite skipn_skipn.
          rewrite firstn_skipn_comm. rewrite firstn_firstn.
          rewrite firstn_length. rewrite skipn_length.
          rewrite rev_length. simpl length. rewrite H21.
          rewrite (min_l (mm - c - _) (mm-c)). 2: eapply le_sub_l.
          cases (c / kk).
          eapply div_small_iff in Heq2. rewrite mod_small in H22 by lia. lia.
          lia.
          rewrite <- Heq2.
          assert (kk <= c).
          { assert (kk <= c \/ c < kk) by lia. cases H23. lia.
            eapply div_small_iff in H23. lia. lia. }
          rewrite (min_l _ c) by lia.
          rewrite add_mod by lia. rewrite mod_mod by lia.
          rewrite (mod_small (c mod kk + (kk - mm mod kk) mod kk) kk).
          2: { rewrite <- (mod_id mm kk) at 5 by lia. lia. }
          rewrite (mod_small (kk - mm mod kk)) by lia.
          rewrite (sub_sub_distr kk).
          2: lia.
          2: { pose proof (Nat.mod_upper_bound mm kk). lia. }
          rewrite (Nat.add_comm (c mod kk)).
          rewrite sub_diag. simpl. rewrite sub_0_r.
          rewrite sub_add_distr. rewrite sub_sub_distr.
          2: { pose proof (Nat.mod_upper_bound mm kk). lia. }
          2: lia. rewrite sub_diag. simpl.
          cases (mm / kk - c / kk).
          { rewrite mul_0_r. rewrite sub_0_r.
            rewrite (Nat.div_mod_eq mm kk).
            rewrite (Nat.div_mod_eq c kk) at 4.
            rewrite (Nat.div_mod_eq c kk) at 2.
            rewrite (Nat.div_mod_eq c kk) at 1.
            rewrite sub_add_distr. rewrite add_sub_swap.
            2: { eapply mul_le_mono_l. eapply div_le_mono. lia. lia. }
            rewrite <- mul_sub_distr_l. rewrite Heq3. rewrite mul_0_r.
            rewrite add_0_l.
            replace (mm mod kk - c mod kk - kk) with 0.
            2: { pose proof (Nat.mod_upper_bound mm kk). lia. }
            simpl. rewrite <- (Nat.div_mod_eq).
            rewrite <- min_assoc. rewrite min_id.
            replace (rev l ++ [ r0])%list with (rev (r0::l)) by reflexivity.
            eapply forall_firstn_ge.
            eapply result_has_shape_forall in Hshs.
            eapply Forall_forall. intros.
            eapply Forall_forall in Hshs.
            2: { eapply in_rev. eapply in_skipn. eapply in_firstn. eauto. }
            eapply Forall_forall in H18.
            2: { eassumption. }
            eapply relate_pads_filter_until_0.
            eapply result_has_shape_filter_until_0.
            rewrite <- H20.
            erewrite <- result_has_shape_filter_until_0. eauto.
            rewrite <- H20.
            eapply relate_pads_filter_until_0.
            eauto. eauto.
            lia. }
          { rewrite <- Heq3. rewrite <- Heq2 in *.
            rewrite (Nat.div_mod_eq mm kk) at 6.
            rewrite (Nat.div_mod_eq mm kk) at 3.
            rewrite (Nat.div_mod_eq mm kk) at 1.
            rewrite (Nat.div_mod_eq c kk) at 6.
            rewrite (Nat.div_mod_eq c kk) at 3.
            rewrite (Nat.div_mod_eq c kk) at 1.
            rewrite sub_add_distr. rewrite add_sub_swap.
            2: { eapply mul_le_mono_l. eapply div_le_mono. lia. lia. }
            rewrite <- mul_sub_distr_l. 
            rewrite <- add_sub_assoc.
            rewrite minus_plus.
            replace (mm mod kk - c mod kk - kk) with 0.
            2: { pose proof (Nat.mod_upper_bound mm kk). lia. }
            simpl. rewrite <- min_assoc. rewrite min_id.
            replace (rev l ++ [ r0])%list with (rev (r0::l)) by reflexivity.
            eapply forall_firstn_ge.
            eapply result_has_shape_forall in Hshs.
            eapply Forall_forall. intros.
            eapply Forall_forall in Hshs.
            2: { eapply in_rev. eapply in_skipn. eapply in_firstn. eauto. }
            eapply Forall_forall in H18.
            2: { eassumption. }
            eapply relate_pads_filter_until_0.
            eapply result_has_shape_filter_until_0.
            rewrite <- H20.
            erewrite <- result_has_shape_filter_until_0. eauto.
            rewrite <- H20.
            eapply relate_pads_filter_until_0.
            eauto. eauto.
            lia. lia. }
        - rewrite (Nat.div_mod_eq c kk) at 10.
          rewrite (Nat.div_mod_eq c kk) at 8.
          rewrite (Nat.div_mod_eq c kk) at 3.
          rewrite <- add_assoc. rewrite (mul_comm kk (c/kk)).
          rewrite div_add_l by lia.
          rewrite (Nat.div_mod_eq c kk) in H2 at 1.
          rewrite <- add_assoc in H2. rewrite (mul_comm kk (c/kk)) in H2.
          rewrite div_add_l in H2 by lia.
          rewrite sub_add_distr in *.
          replace ((c mod kk + (kk - mm mod kk) mod kk) / kk) with 1 in *.
          2: { pose proof (add_mod_div_bound c (kk - mm mod kk) kk).
               cases ((c mod kk + (kk - mm mod kk) mod kk) / kk).
               eapply div_small_iff in Heq2.
               rewrite <- (mod_id mm kk) in Heq2 at 5 by lia. lia. lia. lia. }
          replace (mm - c) with
            (kk * (mm /kk) + mm mod kk - (kk *(c/kk) + c mod kk)).
          2: { symmetry. rewrite (Nat.div_mod_eq mm kk) at 1.
               rewrite (Nat.div_mod_eq c kk) at 1. lia. }
          repeat rewrite sub_add_distr.
          rewrite add_sub_swap.
          2: { eapply mul_le_mono_l. eapply div_le_mono. lia. lia. }          
          rewrite mul_sub_distr_l. rewrite mul_1_r.
          repeat rewrite <- sub_add_distr.
          rewrite (Nat.add_comm (c mod kk)).
          cases (mm / kk - c / kk).
          { rewrite mul_0_r. rewrite sub_0_l. rewrite add_0_l.
            rewrite <- mul_sub_distr_l. rewrite Heq2. rewrite mul_0_r.
            simpl. replace (mm mod kk - c mod kk) with 0 by lia.
            rewrite sub_0_r.
            assert (c < kk \/ kk <= c) by lia. cases H23.
            rewrite (mod_small c kk) in * by lia.
            rewrite (div_small c kk) in * by lia.
            rewrite sub_0_r in *. eapply div_small_iff in Heq2.
            rewrite (mod_small mm kk) in * by lia. lia. lia.
            rewrite (min_l kk c) by lia.
            rewrite firstn_rev.
            rewrite rev_involutive. rewrite skipn_length.
            rewrite app_length. rewrite rev_length. simpl.
            rewrite add_succ_r. rewrite add_0_r. rewrite H21.
            replace (mm - c - kk) with 0.
            2: { rewrite (Nat.div_mod_eq mm kk).
                 rewrite (Nat.div_mod_eq c kk).
                 rewrite sub_add_distr. rewrite add_sub_swap.
                 2: { eapply mul_le_mono_l. eapply div_le_mono. lia. lia. }
                 rewrite <- mul_sub_distr_l. rewrite Heq2. rewrite mul_0_r.
                 lia. }
            simpl.
            replace ((c + (kk - mm mod kk) mod kk) mod kk - kk) with 0.
            2: { pose proof (Nat.mod_upper_bound
                               (c + (kk - mm mod kk) mod kk) kk). lia. }
            simpl.
            replace (rev l ++ [r0])%list with (rev (r0::l)) by auto.
            eapply result_has_shape_forall in Hshs.            
            eapply forall_firstn_ge.
            eapply Forall_forall. intros.
            eapply Forall_forall in Hshs.
            2: { eapply in_rev. eapply in_skipn. eapply in_firstn. eauto. }
            eapply Forall_forall in H18.
            2: { eassumption. }
            eapply relate_pads_filter_until_0.
            eapply result_has_shape_filter_until_0.
            rewrite <- H20.
            erewrite <- result_has_shape_filter_until_0. eauto.
            erewrite <- H20. eapply relate_pads_filter_until_0.
            eauto. eauto. lia. 
          }
          rewrite <- Heq2.
          rewrite add_sub_swap.
          2: { rewrite mul_sub_distr_l.
               pose proof (Nat.mod_upper_bound c kk).
               rewrite <- sub_sub_distr.
               2: { lia. }
               2: { rewrite <- mul_sub_distr_l. rewrite Heq2.
                    rewrite mul_comm. simpl . eapply le_plus_l. }
               lia. }
          rewrite <- mul_sub_distr_l.
          repeat rewrite sub_add_distr.
          rewrite (sub_sub_distr _ _ kk).
          2: { rewrite Heq2. rewrite mul_comm. simpl. eapply le_plus_l. }
          2: lia.
          rewrite sub_diag. simpl. rewrite (sub_sub_distr kk kk).
          2: { pose proof (Nat.mod_upper_bound c kk). lia. }
          2: lia.
          rewrite sub_diag. simpl.
          rewrite (min_l _ c).
          2: { pose proof (mod_le c kk). lia. }
          rewrite (skipn_rev (kk * (mm / kk - c / kk) - kk)).
          rewrite firstn_rev. rewrite rev_involutive.
          rewrite skipn_skipn. rewrite firstn_skipn_comm.
          rewrite firstn_firstn.
          rewrite firstn_length. rewrite skipn_length. rewrite app_length.
          rewrite rev_length. simpl. rewrite add_succ_r. rewrite add_0_r.
          rewrite H21. rewrite (min_l _ (mm -c)) by lia.           
          replace (mm - c) with
            (kk * (mm /kk) + mm mod kk - (kk *(c/kk) + c mod kk)).
          2: { symmetry. rewrite (Nat.div_mod_eq mm kk) at 1.
               rewrite (Nat.div_mod_eq c kk) at 1. lia. }
          repeat rewrite sub_add_distr.
          rewrite add_sub_swap.
          2: { eapply mul_le_mono_l. eapply div_le_mono. lia. lia. }
          rewrite add_mod by lia. rewrite mod_mod by lia.
          rewrite <- mul_sub_distr_l.          
          eapply forall_skipn.
          rewrite <- sub_add_distr.
          rewrite sub_add.
          2: { rewrite Heq2. rewrite mul_comm. simpl. eapply le_plus_l. }
          replace (kk * (mm / kk - c / kk) + mm mod kk - c mod kk - kk * (mm / kk - c / kk)) with 0.
          2: { symmetry. eapply sub_0_le. 
               rewrite add_sub_swap.
               rewrite <- sub_sub_distr.
               2: lia.
               2: { rewrite Heq2. rewrite mul_comm. simpl.
                    pose proof (Nat.mod_upper_bound c kk). lia. }
               2: { rewrite Heq2. rewrite mul_comm. simpl.
                    pose proof (Nat.mod_upper_bound c kk). lia. }
               eapply le_sub_l. }
          rewrite add_0_r.
          rewrite (mod_small (kk - mm mod kk)) by lia.          
          replace (rev l ++ [ r0])%list with (rev (r0::l)) by reflexivity.
          eapply forall_firstn_ge.
          eapply result_has_shape_forall in Hshs.
          eapply Forall_forall. intros.
          eapply Forall_forall in Hshs.
          2: { eapply in_rev. eapply in_skipn. eapply in_firstn. eauto. }
          eapply Forall_forall in H18.
          2: { eassumption. }
          eapply relate_pads_filter_until_0.
          eapply result_has_shape_filter_until_0.
          rewrite <- H20.
          erewrite <- result_has_shape_filter_until_0. eauto.
          rewrite <- H20.
          eapply relate_pads_filter_until_0.
          eauto. eauto.
          remember (min r _) as X.
          replace (kk - mm mod kk) with
            (kk - c mod kk + (kk - mm mod kk - (kk - c mod kk))).
          rewrite add_assoc.
          rewrite <- (mod_small (kk - c mod kk) kk) at 1 by lia.
          rewrite mod_id by lia.
          rewrite (Nat.add_comm kk).
          replace kk with (1*kk) at 5 by lia. rewrite mod_add by lia.
          rewrite <- (mod_small (kk - c mod kk) kk) at 2 by lia.
          rewrite mod_id by lia.
          rewrite (Nat.add_comm kk).
          replace kk with (1*kk) at 14 by lia. rewrite mod_add by lia.
          rewrite <- (sub_add_distr _ (c mod kk)).
          rewrite (Nat.add_comm (c mod kk)).
          rewrite sub_add_distr.
          rewrite (sub_sub_distr _ _ kk).
          2: { rewrite Heq2. rewrite mul_comm. simpl. eapply le_plus_l. }
          2: { lia. }
          rewrite minus_plus.
          remember ((kk - mm mod kk - (kk - c mod kk)) mod kk) as XX.
          remember (c mod kk - mm mod kk) as XXX.
          assert (XX - XXX = 0).
          { rewrite HeqXX,HeqXXX.
            rewrite (mod_small (kk - mm mod kk - (kk - c mod kk)) kk).
            2: { lia. }
            rewrite <- sub_add_distr. rewrite add_sub_assoc by lia.
            rewrite Nat.add_comm.
            rewrite <- (mod_small (kk - c mod kk) kk) by lia.
            rewrite mod_id by lia. rewrite sub_diag. reflexivity. }
          rewrite H23. rewrite add_0_l.
          rewrite HeqX, HeqXX, HeqXXX.
          lia.
          rewrite le_plus_minus_r. reflexivity.
          lia.
      }
  }

  - (* EMPTY GEN *)
    invert Hpad.
    invert Hsh.
    pose proof Hconst as Hconst'.
    eapply constant_nonneg_bounds_size_of_no_vars in Hconst'.
    2: { econstructor. eauto. }
    invert Hconst'.
    simpl in *.
    eapply app_no_dups_empty_args in H4. invs.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total with (v:=$0)
      in H2,H3.
    repeat rewrite skipn_nil.
    repeat rewrite firstn_nil. 
    propositional; econstructor.
  - (* STEP GEN *)
    invert Hsh.
    invert Hpad.
    pose proof Hconst as Hconst'.
    eapply constant_nonneg_bounds_size_of_no_vars in Hconst'.
    2: { econstructor. eauto. }
    simpl in Hconst'. invert Hconst'. simpl in H8.
    eapply app_no_dups_empty_args in H8. invs.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total with (v:=$0)
      in H7,H6.

    eq_size_of.
    assert (eval_Zexpr_Z_total $0 lo = loz).
    { invert H7.
      eapply eval_Zexpr_Z_eval_Zexpr in H.
      eapply H8 in H. invert H. reflexivity. }
    assert (eval_Zexpr_Z_total $0 hi = hiz).
    { invert H6.
      eapply eval_Zexpr_Z_eval_Zexpr in H0.
      eapply H16 in H0. invert H0. reflexivity. }
    subst.
    simpl in *.
    assert (result_has_shape (V l) (length l::xs_shape)) as Hsh'.
    { eapply forall_result_has_shape; eauto. }
    assert (k > 0 \/ k = 0) as Hcase by lia.
    inversion Hcase as [ Hcase1 | Hcase2 ]; clear Hcase.
    + (* 0 < k *)
      assert (has_pad sh v g (Gen i (lo + | 1 |)%z hi body)
                      (PadCons (k-1)
                               ll
                               pad1 rr pad2 c)).
      { econstructor.
        rewrite eval_Zexpr_Z_total_add_distr by eauto.
        unfold eval_Zexpr_Z_total at 3. simpl. lia.

        rewrite eval_Zexpr_Z_total_add_distr by eauto.
        unfold eval_Zexpr_Z_total at 3. simpl. lia.

        rewrite eval_Zexpr_Z_total_add_distr by eauto.
        unfold eval_Zexpr_Z_total at 3. simpl. lia.

        eassumption.

        rewrite eval_Zexpr_Z_total_add_distr by eauto.
        unfold eval_Zexpr_Z_total at 2. simpl.
        unfold eval_Zexpr_Z_total at 3. simpl.
        intros.
        apply H19. lia.

        auto.

        rewrite eval_Zexpr_Z_total_add_distr by eauto.
        unfold eval_Zexpr_Z_total at 2. simpl.
        unfold eval_Zexpr_Z_total at 4. simpl.
        intros.
        eapply H22. lia. lia.

        rewrite eval_Zexpr_Z_total_add_distr by eauto.
        unfold eval_Zexpr_Z_total at 3. simpl. lia. }

      cases l.
      { simpl in *. eapply length_eval_expr_gen in H5.
        2: { simpl. rewrite H,H0. reflexivity. }
        simpl in *.
        replace (eval_Zexpr_Z_total $0 hi - eval_Zexpr_Z_total $0 lo)%Z with
          1%Z in * by lia.
        assert (k = 1) by lia. subst. simpl.
        assert (c = 0) by lia. subst. simpl in *.
        assert (eval_Zexpr_Z_total $0 lo <=
                  eval_Zexpr_Z_total $0 lo < eval_Zexpr_Z_total $0 hi)%Z
          by lia.
        rewrite firstn_nil.
        replace ll with 0 in * by lia.
        replace rr with 0 in * by lia. simpl in *.
        split.
        2: { split. eauto. split; eauto. }
        econstructor. 2: eauto.
        eapply relate_pads_gen_pad.
        eapply IHeval_expr1.
        invs. eauto.
        eapply H22. lia. lia.
        eauto. eauto. eauto. eauto. eauto. 
        eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape;
          eauto. invs. eauto. }

      
      eapply IHeval_expr2 in Hsh'; clear IHeval_expr2.
      2: { invert H7. invert H6.
           rewrite H18,H17. simpl.
           rewrite app_no_dups_empty_r.
           rewrite eval_Zexpr_Z_total_add_distr.
           unfold eval_Zexpr_Z_total at 3. simpl.
           propositional. lia.
           econstructor; eauto. eauto. }
      2: { eauto. }
      simpl in Hsh'.
      invs. 
      cases k. lia. 
      replace (Datatypes.S k-1) with k in * by lia.
      simpl in *.
      2: { eauto. }
      propositional.
      * econstructor.
        
        eapply relate_pads_gen_pad.
        eapply H27.
        eapply H22. lia. 
        lia. eauto. eauto. eauto. eauto. eauto. 
        eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
        eauto. eauto. eauto. eauto.
      * rewrite firstn_app.
        rewrite app_length. rewrite rev_length. simpl.
        eapply Forall_app. propositional.
        cases (c - (Datatypes.length l + 1)). simpl in *. econstructor.
        simpl. rewrite firstn_nil. econstructor. 2: eauto.
        eapply relate_pads_gen_pad.
        eapply H27.
        eapply H22. lia. lia. eauto.
        eauto. eauto. 
        eauto.
        eauto.
        eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
        eauto. eauto. eauto.
      * posnats. pose proof H24.
        rewrite skipn_app in *.
        rewrite firstn_app in *. rewrite skipn_length in *.
        rewrite rev_length in *.
        eapply Forall_app in H29. invs.
        repeat erewrite Forall_app.
        rewrite skipn_app. rewrite firstn_app.
        rewrite Forall_app.
        rewrite skipn_length. rewrite rev_length.
        split. split. auto. eauto.
        repeat rewrite app_length. repeat rewrite rev_length.
        simpl.
        cases (c - (Datatypes.length l + 1)). simpl.
        2: { simpl. rewrite skipn_nil. rewrite firstn_nil. eauto. }
        assert (c <= Datatypes.S (length l)) by lia.
        cases (rr - (Datatypes.length l + 1 - c)). simpl. eauto.
        simpl. rewrite firstn_nil. econstructor. 2: eauto.
        pose proof H5.
        eapply length_eval_expr_gen in H32; eauto.
        2: { simpl. rewrite H,H0. reflexivity. }
        simpl in H32. lia.
      * eauto.
      * econstructor. eauto.
    + (* k = 0 *)
      subst. simpl. split. auto.
      assert (c = 0 \/ 0 < c) as Hcase by lia.
      inversion Hcase as [ Hcase1 | Hcase2 ]; clear Hcase.
      * (* c = 0 *)
        subst. simpl. split. econstructor.
        simpl in *.
        repeat rewrite Z.add_0_r in *.
        repeat rewrite Z.sub_0_r in *.

        cases ll.
        { simpl. split. auto.
          rewrite firstn_app. rewrite rev_length.
          cases (rr - length l).
          - simpl. rewrite app_nil_r.
            pose proof Hsh' as HH.
            eapply IHeval_expr2 in HH.
            2: { invert H6. invert H7. rewrite H16,H17. simpl.
                 rewrite eval_Zexpr_Z_total_add_distr.
                 unfold eval_Zexpr_Z_total at 3. simpl. propositional.
                 lia. econstructor; eauto. eauto. }
            2: { eapply HasPadGen with (k:=0) (ll:=0) (c:=0) (rr:=rr).
                 lia. lia. lia. eauto.

                 erewrite eval_Zexpr_Z_total_add_distr.
                 unfold eval_Zexpr_Z_total at 2.
                 unfold eval_Zexpr_Z_total at 3. simpl. intros. eapply H19.
                 lia. eauto. eauto.
                 intros. eapply H21. lia.

                 erewrite eval_Zexpr_Z_total_add_distr.
                 unfold eval_Zexpr_Z_total at 2.
                 unfold eval_Zexpr_Z_total at 4. simpl. intros. lia.
                 eauto. eauto.

                 erewrite eval_Zexpr_Z_total_add_distr.
                 unfold eval_Zexpr_Z_total at 3. simpl. 
                 eapply length_eval_expr_gen in H5.
                 2: { simpl. rewrite H,H0. reflexivity. }
                 lia. eauto. eauto. }
            2: eauto.
            2: eauto.
            2: { econstructor; eauto. }
            simpl in HH. invs. eauto.
          - eapply length_eval_expr_gen in H5.
            2: { simpl. rewrite H,H0. reflexivity. }
            rewrite H5 in *.
            assert (rr =Z.to_nat (eval_Zexpr_Z_total $0 hi -
                                    eval_Zexpr_Z_total $0 lo)) by lia.
            pose proof Hsh' as HH.
            eapply IHeval_expr2 in HH.
            2: { invert H6. invert H7. rewrite H8,H17. simpl.
                 rewrite eval_Zexpr_Z_total_add_distr.
                 unfold eval_Zexpr_Z_total at 3. simpl. propositional.
                 lia. econstructor; eauto. eauto. }
            2: { eapply HasPadGen with (k:=0) (ll:=0) (c:=0) (rr:=rr-1).
                 lia. lia. lia. eauto.

                 erewrite eval_Zexpr_Z_total_add_distr.
                 unfold eval_Zexpr_Z_total at 2.
                 unfold eval_Zexpr_Z_total at 3. simpl. intros. eapply H19.
                 lia. eauto. eauto.
                 intros. eapply H21. lia.

                 erewrite eval_Zexpr_Z_total_add_distr.
                 unfold eval_Zexpr_Z_total at 2.
                 unfold eval_Zexpr_Z_total at 4. simpl. intros. lia.
                 eauto. eauto.

                 erewrite eval_Zexpr_Z_total_add_distr.
                 unfold eval_Zexpr_Z_total at 3. simpl. 
                 lia. eauto. eauto. }
            2: eauto.
            2: eauto.
            2: { econstructor; eauto. }

            eapply IHeval_expr1 in H9.
            2: { propositional. }
            2: { eapply H21. lia. }
            2: { eauto. }
            2: { eauto. }
            2: eauto.
            simpl. rewrite firstn_nil.
            simpl in HH. invs. rewrite Forall_app. split.
            rewrite firstn_all2.
            2: { rewrite rev_length. lia. }
            rewrite firstn_all2 in H20.
            2: { rewrite rev_length. lia. }
            eauto. econstructor; eauto. }
        simpl. split.
        econstructor.
        eapply IHeval_expr1. invs. eauto.
        eapply H19. lia. eauto. auto. auto. eauto. 
        
        cases l.
        { rewrite firstn_nil. eauto. } 
        eapply IHeval_expr2
          with (pads:= PadCons 0
                               ll
                               pad1 rr pad2 0) in Hsh'.
        2: { invert H7. invert H6. rewrite H16,H17. simpl.
             rewrite eval_Zexpr_Z_total_add_distr.
             unfold eval_Zexpr_Z_total at 3. simpl.
             propositional. lia.
             econstructor; eauto. eauto. }
        2: { eapply eval_Zexpr_Z_eval_Zexpr in H,H0. invs.
             eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H8,H17. invs.
             pose proof H18. pose proof H17.
             specialize (H17 v). specialize (H18 v).
             specialize (H8 $0). specialize (H24 $0).
             eq_eval_Z. eapply eval_Zexpr_Z_eval_Zexpr in H,H0,H8,H24.
             econstructor.
             unfold eval_Zexpr_Z_total. simpl. rewrite H8,H24. lia.
             unfold eval_Zexpr_Z_total. simpl. rewrite H8,H24. lia.
             unfold eval_Zexpr_Z_total. simpl. rewrite H8,H24. lia.
             eauto.
             unfold eval_Zexpr_Z_total. simpl. rewrite H24. intros.
             eapply H19. lia.
             unfold eval_Zexpr_Z_total. simpl. rewrite H8. intros.
             eapply H21. lia.
             intros.
             unfold eval_Zexpr_Z_total in H17,H18. simpl eval_Zexpr_Z in *.
             rewrite H8,H24 in *.
             eapply H22. lia. lia.
             unfold eval_Zexpr_Z_total. simpl. rewrite H8,H24. lia. }
        2: { eauto. }
        2: { eauto. }
        2: { econstructor. eauto. }
        simpl in Hsh'. invs. eauto.

        rewrite firstn_app. rewrite rev_length.
        eapply IHeval_expr2
          with (pads:= PadCons 0
                               ll
                               pad1 rr pad2 0) in Hsh'.
        2: { invert H7. invert H6. rewrite H16,H17. simpl.
             rewrite eval_Zexpr_Z_total_add_distr.
             unfold eval_Zexpr_Z_total at 3. simpl.
             propositional. lia.
             econstructor; eauto. eauto. }
        2: { eapply eval_Zexpr_Z_eval_Zexpr in H,H0. invs.
             eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H8,H17. invs.
             pose proof H18. pose proof H17.
             specialize (H17 v). specialize (H18 v).
             specialize (H8 $0). specialize (H24 $0).
             eq_eval_Z. eapply eval_Zexpr_Z_eval_Zexpr in H,H0,H8,H24.
             econstructor.
             unfold eval_Zexpr_Z_total. simpl. rewrite H8,H24. lia.
             unfold eval_Zexpr_Z_total. simpl. rewrite H8,H24. lia.
             unfold eval_Zexpr_Z_total. simpl. rewrite H8,H24. lia.
             eauto.
             unfold eval_Zexpr_Z_total. simpl. rewrite H24. intros.
             eapply H19. lia.
             unfold eval_Zexpr_Z_total. simpl. rewrite H8. intros.
             eapply H21. lia.
             intros.
             unfold eval_Zexpr_Z_total in H17,H18. simpl eval_Zexpr_Z in *.
             rewrite H8,H24 in *.
             eapply H22. lia. lia.
             unfold eval_Zexpr_Z_total. simpl. rewrite H8,H24. lia. }
        2: { eauto. }
        2: { eauto. }
        2: { econstructor. eauto. }
        simpl in Hsh'. invs. eauto.
        eapply Forall_app. split. eauto.
        
        eapply length_eval_expr_gen in H5.
        2: { simpl. rewrite H,H0. reflexivity. }
        cases (rr - length l). 2: lia.
        simpl. eauto.
      * (* 0 < c *)
        assert (c = Z.to_nat
                      (eval_Zexpr_Z_total $0 hi-eval_Zexpr_Z_total $0 lo) \/
                  c < Z.to_nat
                        (eval_Zexpr_Z_total $0 hi-eval_Zexpr_Z_total $0 lo))
          as Hcase by lia.
        inversion Hcase as [ Hcase3 | Hcase4 ]; clear Hcase.
        -- (* entire thing is right padding *)
          subst.
          assert (has_pad sh v g (Gen i (lo + | 1 |)%z hi body)
                          (PadCons 0
                                   0
                                   pad1 0 pad2
                                   (Z.to_nat
                                      (eval_Zexpr_Z_total $0 hi-
                                         eval_Zexpr_Z_total $0 lo - 1)%Z))).
          { econstructor.
            rewrite eval_Zexpr_Z_total_add_distr.
            unfold eval_Zexpr_Z_total at 3. simpl. lia.
            eauto. eauto.

            rewrite eval_Zexpr_Z_total_add_distr.
            unfold eval_Zexpr_Z_total at 5. simpl. lia.
            eauto. eauto.

            rewrite eval_Zexpr_Z_total_add_distr.
            unfold eval_Zexpr_Z_total at 5. simpl. lia.
            eauto. eauto.

            eassumption.

            rewrite eval_Zexpr_Z_total_add_distr.
            unfold eval_Zexpr_Z_total at 2. simpl.
            unfold eval_Zexpr_Z_total at 3. simpl.
            intros. apply H19. lia.
            eauto. eauto.

            intros.
            eapply H21. lia.

            rewrite eval_Zexpr_Z_total_add_distr.
            unfold eval_Zexpr_Z_total at 2. simpl.
            unfold eval_Zexpr_Z_total at 4. simpl.
            intros. eapply H22. lia. lia.
            eauto. eauto.

            rewrite eval_Zexpr_Z_total_add_distr; eauto.            
            unfold eval_Zexpr_Z_total at 3. simpl.
            rewrite Z.sub_0_r. rewrite Z2Nat.id.
            2: lia. lia. }

          cases l.
          { simpl in *.
            clear Hsh'. invs.
            eapply length_eval_expr_gen in H5.
            2: { simpl. rewrite H. rewrite H0. reflexivity. }
            simpl in *.
            assert ((eval_Zexpr_Z_total $0 hi) =
                      (eval_Zexpr_Z_total $0 lo + 1))%Z by lia.
            rewrite H20 in *.
            replace (Z.to_nat (eval_Zexpr_Z_total $0 lo + 1 -
                                 eval_Zexpr_Z_total $0 lo))%Z with 1 by lia.
            simpl. split.
            econstructor.
            eapply relate_pads_gen_pad.
            eapply IHeval_expr1.
            eauto. eapply H22. lia. lia. eauto. eauto.
            eauto. eauto. eauto. 
            eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape;
              eauto. econstructor.

            rewrite firstn_nil. split; eauto.
            cases ll. simpl. eauto.
            simpl. rewrite firstn_nil. econstructor. 2: eauto.
            eapply IHeval_expr1.
            eauto. eapply H19. lia. auto. auto. auto. eauto. }
          eapply IHeval_expr2 in Hsh'; clear IHeval_expr2.
          2: { invert H7. invert H6.
               rewrite H18,H17.
               simpl.
               rewrite eval_Zexpr_Z_total_add_distr.
               unfold eval_Zexpr_Z_total at 3. simpl.
               rewrite app_no_dups_empty_r.
               propositional. lia.
               econstructor; eauto.
               eauto. }
          2: eauto. simpl in Hsh'. invs.
          cases (Z.to_nat (eval_Zexpr_Z_total $0 hi -
                             eval_Zexpr_Z_total $0 lo)). lia.
          2: { eauto. }
          2: { eauto. }
          2: { econstructor; eauto. }
          
          eapply result_shape_gen_length in H5.
          2: { simpl. rewrite H. reflexivity. }
          2: { rewrite H0. reflexivity. }
          rewrite firstn_all2 in H18.
          2: { rewrite app_length. rewrite rev_length. simpl in *. lia. }
          eapply Forall_app in H18. invs.
          simpl rev.
          repeat rewrite skipn_app.
          repeat rewrite firstn_app.
          repeat rewrite app_length. repeat rewrite skipn_length.
          repeat rewrite rev_length.
          repeat rewrite Forall_app.
          repeat rewrite sub_add_distr in *.
          split. split. split. eapply forall_firstn. eauto.
          eapply forall_firstn. eauto.
          simpl in H5.
          simpl length.
          replace (Datatypes.S n - length l - 1) with 1 by lia. simpl.
          econstructor.
          eapply relate_pads_gen_pad.
          eapply IHeval_expr1. eauto.
          eapply H22. lia. lia. eauto. eauto. eauto. eauto. eauto.
          eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape.
          eauto. eauto. eauto. eauto.
          simpl length.
          
          simpl in H5.
          assert (length l =
                    Z.to_nat (eval_Zexpr_Z_total $0 hi -
                                eval_Zexpr_Z_total $0 lo - 1) -1) by lia.
          rewrite skipn_all2.
          2: { rewrite rev_length. lia. }
          rewrite firstn_nil.
          replace (Datatypes.length l - Datatypes.S n) with 0 by lia.
          rewrite sub_0_r.
          rewrite skipn_all2.
          2: { simpl length. lia. }
          rewrite firstn_nil.
          replace (Datatypes.S n - Datatypes.length l - 1) with 1 by lia.
          simpl skipn. rewrite firstn_nil.

          split; eauto.

          cases ll. simpl. eauto. lia.
        -- cases ll.
           { simpl. pose proof H5.
             eapply length_eval_expr_gen in H8.
             2: { simpl. rewrite H,H0. reflexivity. }
             rewrite skipn_app. repeat rewrite firstn_app.
             rewrite skipn_length. rewrite rev_length.
             cases (c - length l).
             - simpl. rewrite app_nil_r.
               simpl in H23. rewrite Z.sub_0_r in H23.
               rewrite Z2Nat.inj_sub in H23 by lia.
               rewrite Z.sub_add_distr in H8.
               rewrite Z2Nat.inj_sub in H8 by lia. rewrite H8 in Heq.
               cases (rr - (Datatypes.length l - c)).
               + simpl. rewrite app_nil_r.
                 eapply IHeval_expr2 in Hsh'.
                 2: { invert H6. invert H7.
                      rewrite eval_Zexpr_Z_total_add_distr.
                      unfold eval_Zexpr_Z_total at 3. simpl.
                      rewrite H17,H18.
                      propositional. lia. econstructor; eauto. eauto. }
                 2: { eapply HasPadGen with (ll:=0) (k:=0) (rr:=rr) (c:=c).
                      lia.
                      erewrite eval_Zexpr_Z_total_add_distr.
                      unfold eval_Zexpr_Z_total at 3. simpl. lia.
                      eauto. eauto.
                      erewrite eval_Zexpr_Z_total_add_distr.
                      unfold eval_Zexpr_Z_total at 3. simpl. lia.
                      eauto. eauto. eauto.
                      erewrite eval_Zexpr_Z_total_add_distr.
                      unfold eval_Zexpr_Z_total at 2.
                      unfold eval_Zexpr_Z_total at 3. simpl. intros.
                      eapply H19. lia. eauto. eauto.
                      intros. eapply H21. lia.
                      erewrite eval_Zexpr_Z_total_add_distr.
                      unfold eval_Zexpr_Z_total at 2.
                      unfold eval_Zexpr_Z_total at 4. simpl. intros.
                      eapply H22. lia. lia. eauto. eauto.
                      erewrite eval_Zexpr_Z_total_add_distr.
                      unfold eval_Zexpr_Z_total at 3.
                      simpl. lia. eauto. eauto. }
                 2: { eauto. }
                 2: { eauto. }
                 2: econstructor; eauto.
                 simpl in Hsh'. invs.
                 split. eauto. eauto.
               + simpl. rewrite firstn_nil.
                 rewrite firstn_all2 with (n:=rr).
                 2: { rewrite skipn_length. rewrite rev_length. lia. }
                 rewrite <- H8 in *.
                 eapply IHeval_expr2 in Hsh'.
                 2: { invert H6. invert H7.
                      rewrite eval_Zexpr_Z_total_add_distr.
                      unfold eval_Zexpr_Z_total at 3. simpl.
                      rewrite H17,H18.
                      propositional. lia. econstructor; eauto. eauto. }
                 2: { eapply HasPadGen with (ll:=0) (k:=0) (rr:=rr-1) (c:=c).
                      lia.
                      erewrite eval_Zexpr_Z_total_add_distr.
                      unfold eval_Zexpr_Z_total at 3. simpl. lia.
                      eauto. eauto.
                      erewrite eval_Zexpr_Z_total_add_distr.
                      unfold eval_Zexpr_Z_total at 3. simpl. lia.
                      eauto. eauto. eauto.
                      erewrite eval_Zexpr_Z_total_add_distr.
                      unfold eval_Zexpr_Z_total at 2.
                      unfold eval_Zexpr_Z_total at 3. simpl. intros.
                      eapply H19. lia. eauto. eauto.
                      intros. eapply H21. lia.
                      erewrite eval_Zexpr_Z_total_add_distr.
                      unfold eval_Zexpr_Z_total at 2.
                      unfold eval_Zexpr_Z_total at 4. simpl. intros.
                      eapply H22. lia. lia. eauto. eauto.
                      erewrite eval_Zexpr_Z_total_add_distr.
                      unfold eval_Zexpr_Z_total at 3.
                      simpl. lia. eauto. eauto. }
                 2: { eauto. }
                 2: { eauto. }
                 2: econstructor; eauto.
                 simpl in Hsh'. invs.
                 split. eauto. split. eauto. rewrite Forall_app.
                 split. auto.
                 rewrite firstn_all2 in H23.
                 2: { rewrite skipn_length. rewrite rev_length.
                      rewrite H8. lia. }
                 eauto.
                 eauto. econstructor. 2: eauto.
                 eapply IHeval_expr1. eauto. eapply H21.
                 lia. eauto. eauto. eauto. eauto.
             - lia.  }
           assert (has_pad sh v g (Gen i (lo + | 1 |)%z hi body)
                           (PadCons 0 ll pad1 rr pad2 c)).
           { econstructor.
             rewrite eval_Zexpr_Z_total_add_distr.
             unfold eval_Zexpr_Z_total at 3. simpl. lia.
             eauto. eauto.

             rewrite eval_Zexpr_Z_total_add_distr.
             unfold eval_Zexpr_Z_total at 3. simpl. lia.
             eauto. eauto.

             rewrite eval_Zexpr_Z_total_add_distr.
             unfold eval_Zexpr_Z_total at 3. simpl. lia.
             eauto. eauto.

             eassumption.

             rewrite eval_Zexpr_Z_total_add_distr.
             unfold eval_Zexpr_Z_total at 2. simpl.
             unfold eval_Zexpr_Z_total at 3. simpl.
             intros. apply H19. lia.
             eauto. eauto.

             intros. eapply H21. lia.

             rewrite eval_Zexpr_Z_total_add_distr.
             unfold eval_Zexpr_Z_total at 2. simpl.
             unfold eval_Zexpr_Z_total at 4. simpl.
             intros. eapply H22. lia. lia.
             eauto. eauto.

             rewrite eval_Zexpr_Z_total_add_distr; eauto.
             unfold eval_Zexpr_Z_total at 3. simpl. lia. }
           
           cases l.
           { simpl in *.
             eapply length_eval_expr_gen in H5.
             2: { simpl. rewrite H,H0. reflexivity. }
             simpl in *. lia. }
           eapply IHeval_expr2 in Hsh'; eauto.
           2: { invert H7. invert H6.
                rewrite H18,H17.
                rewrite eval_Zexpr_Z_total_add_distr.
                simpl.
                unfold eval_Zexpr_Z_total at 3.
                simpl.
                propositional. lia.
                econstructor; eauto. eauto. }
           2: { econstructor; eauto. }
           simpl in Hsh'.
           invs. split. eauto.
           rewrite firstn_app in *. 
           repeat rewrite rev_length in *. simpl length.
           simpl rev. rewrite firstn_app.
           rewrite rev_length.
           eapply Forall_app in H18. invs.
           repeat rewrite Forall_app.
           split. split. eauto. eauto.
           eapply length_eval_expr_gen in H5.
           2: { simpl. rewrite H,H0. reflexivity. }
           simpl in H5.
           replace (c - Datatypes.S (Datatypes.length l)) with 0 by lia.
           simpl. eauto.

           pose proof H5 as HH.
           eapply length_eval_expr_gen in H5.
           2: { simpl. rewrite H,H0. reflexivity. }
           simpl in H5.           
           simpl. split.
           econstructor.
           2: { eauto. }
           eapply IHeval_expr1. eauto. eapply H19. lia. eauto. eauto.
           eauto. eauto.
           rewrite skipn_app.
           rewrite firstn_app. rewrite Forall_app.
           split. eauto.
           rewrite skipn_length. rewrite app_length. rewrite rev_length.
           simpl.

           replace (c - (Datatypes.length l + 1)) with 0 by lia. simpl.
           replace (rr - (Datatypes.length l + 1 - c)) with 0 by lia.
           simpl. econstructor.
  - (* STEP SUM *)
    simpl in *.
    inversion Hconst as [ Hconstlo [ Hconsthi Hconst' ] ]; clear Hconst.
    assert (eq_zexpr lo (| eval_Zexpr_Z_total $0 lo|)%z) as Hlo.
    { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto. }
    assert (eq_zexpr hi (| eval_Zexpr_Z_total $0 hi|)%z) as Hhi.
    { eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total. eauto. }
    pose proof Hconst' as Hconst.
    invert Hpad.
    { invert Hlo. invert Hhi.
      eapply eval_Zexpr_Z_eval_Zexpr in H,H0.
      eapply H7 in H. eapply H9 in H0. invert H. invert H0.
      lia. }
    eapply IHeval_expr1 in Hconst'.
    2: { eapply H15.
         eapply eval_Zexpr_Z_eval_Zexpr in H,H0.
         invert Hlo. eapply H7 in H. invert H. 
         invert Hhi. eapply H in H0. invert H0. lia. }
    2: { eapply result_has_shape_add_result_result in Hsh; eauto. invs.
         eauto. }
    assert (vars_of_Zexpr lo ++/ [] = [] /\
              vars_of_Zexpr hi = [] /\ constant_nonneg_bounds body)
      as Hconst''.
    { invert Hlo. invert Hhi. propositional. rewrite Hconstlo. reflexivity. }

    assert (0 < eval_Zexpr_Z_total $0 hi - (eval_Zexpr_Z_total $0 lo + 1) \/
              eval_Zexpr_Z_total $0 hi = eval_Zexpr_Z_total $0 lo + 1)%Z
      as Hcase by lia.
    inversion Hcase as [ Hcase1 | Hcase2 ]; clear Hcase.
    +  simpl in *. 
       eapply IHeval_expr2 in Hconst''.
       2: { eapply HasPadSum.
            intros. eapply H15.
            rewrite eval_Zexpr_Z_total_add_distr in *.
            unfold eval_Zexpr_Z_total in *. simpl in *. lia.
            eauto. eauto. 
            rewrite eval_Zexpr_Z_total_add_distr in *.
            unfold eval_Zexpr_Z_total at 3. simpl. lia.
            eauto. eauto. }
       2: { eapply result_has_shape_add_result_result in Hsh; eauto. invs.
            eauto. }
       2: { eauto. }

       eapply add_result_relate_pads. eauto.
       eauto. eauto. eauto. econstructor; eauto.
       invs. eauto.
     + invert H5.
      * simpl in *. rewrite H in H11. invs. rewrite H12 in *. invs.
        eapply eval_Zexpr_Z_eval_Zexpr in H12, H.
        invert Hlo. invert Hhi.
        eapply H0 in H. eapply H10 in H12. invert H. invert H12.
        rewrite Hcase2 in *. lia.
      * simpl in *. rewrite H in H11. invs. rewrite H14 in *. invs.
        eapply eval_Zexpr_Z_eval_Zexpr in H14, H.
        invert Hlo. invert Hhi.
        eapply H0 in H. eapply H10 in H14. invert H. invert H14.
        rewrite Hcase2 in *.
        pose proof H6. eapply result_has_shape_add_result_result in H; eauto.
        invs.
        pose proof (result_has_shape_gen_pad (map Z.to_nat lz)).
        eapply result_has_shape_result_shape_nat in H13,H.
        rewrite H in H13. clear H. symmetry in H13.

        eapply add_result_gen_pad_r in H6.
        2: { reflexivity. }
        2: { eapply result_has_shape_filter_until_0.
             rewrite <- H13.
             erewrite <- result_has_shape_filter_until_0.
             eauto. }
        subst. eauto.
     + eauto.
     + eauto.
     + invs. eauto.
  - (* EMPTY SUM *)
    pose proof Hpad as Hpad'. 
    invert Hpad.
    2: { simpl in *. invs.
         eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
           with (v:=$0) in H4,H6.
         invert H4. invert H6.
         eapply eval_Zexpr_Z_eval_Zexpr in H,H0.
         eapply H5 in H. eapply H4 in H0. invert H. invert H0. lia. }

    simpl in *. invs.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
      with (v:=$0) in H4,H6.
    pose proof H4. pose proof H6.
    invert H4. invert H6.
    eapply eval_Zexpr_Z_eval_Zexpr in H,H0.
    eapply H5 in H. eapply H4 in H0. invert H. invert H0.

    pose proof (result_has_shape_gen_pad (map Z.to_nat lz)).
    pose proof H as HH. pose proof Hsh as HshHsh.
    eapply result_has_shape_result_shape_nat in H,Hsh.
    eapply relate_pads_filter_until_0.
    eauto.

    rewrite H in Hsh.
    rewrite gen_pad_filter_until_0. rewrite <- Hsh.
    eq_size_of.
    
    pose proof H7. eapply constant_nonneg_bounds_size_of_no_vars in H0; eauto.
    eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H0.
    eq_eval_Zlist.
    eapply relate_pads_filter_until_0.
    rewrite <- gen_pad_filter_until_0.
    eapply result_has_shape_gen_pad.
    rewrite <- gen_pad_filter_until_0.    
    eapply relate_pads_gen_pad_id.
  - (* FALSE GUARD *)
    invert Hsize. pose proof H5 as Hsize.
    invert Hpad.
    + (* FALSE *) eq_size_of. pose proof Hconst as Hconst'.
      eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape
        with (sh:=sh) (v:=v) (ec:=ec) in Hconst'.
      2: { econstructor; eauto. }   
      2: { econstructor. eauto. eauto. eauto. }
      pose proof Hsh as Hsh'. pose proof Hconst' as Hsh''.
      eapply result_has_shape_result_shape_nat in Hsh',Hsh''.
      rewrite Hsh' in Hsh''. clear Hsh'.
      cases sh0. invert H1.
      simpl. propositional. simpl in Hsh''. cases rsh. reflexivity.
      simpl in *. cases n; simpl in *; try discriminate.
      invert H1. cases rsh. simpl in *. invert Hsh.
      pose proof H0.
      eapply constant_nonneg_bounds_size_of_no_vars in H1; eauto.
      eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H1.
      invert H1. eq_eval_Z. eq_eval_Zlist.
      pose proof Hsh.
      simpl in H1.
      eapply result_has_shape_length in H1.
      rewrite repeat_length in H1. subst.
      repeat rewrite <- map_cons.
      
      eapply relate_pads_filter_until_0.
      eapply result_has_shape_filter_until_0.
      rewrite gen_pad_filter_until_0.
      rewrite <- Hsh''.
      eapply result_has_shape_gen_pad.
      
      repeat rewrite <- map_cons.
      rewrite Hsh''.
      eapply relate_pads_filter_until_0.
      eapply result_has_shape_gen_pad.
      eapply relate_pads_gen_pad_id.
    + eq_size_of. clear H2. eapply relate_pads_filter_until_0. eauto.
      pose proof (result_has_shape_gen_pad (map Z.to_nat lz)).
      eapply result_has_shape_result_shape_nat in Hsh,H2.
      rewrite Hsh in H2.
      rewrite H2.
      rewrite gen_pad_filter_until_0. pose proof H0.
      eapply constant_nonneg_bounds_size_of_no_vars in H0; eauto.
      eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H0.
      eq_eval_Zlist.
      eapply has_pad_size_of_relate_pads_gen_pad. eauto. eauto. eauto.
  - (* TRUE GUARD *)
    invert Hsize. eq_size_of.      
    invert Hpad.
    + eq_eval_B. discriminate.
    + simpl in *. 
      eapply IHeval_expr; eauto.
  - (* LET SCALAR *)
    invert Hsize. eq_size_of.
    invert Hpad. simpl in *. invs.
    eq_size_of. 
    eapply IHeval_expr1 in H12.
    2: { eauto. }
    2: { econstructor. }
    2: { eauto. }
    2: { eauto. }
    2: { eauto. }
    eapply IHeval_expr2; eauto.
    { intros.
      cases (x0 ==v x); subst.
      + rewrite lookup_add_eq in * by auto. invert H10. invert H1.
        simpl. assumption.
      + rewrite lookup_add_ne in * by auto. eauto. }
    { intros.
      cases (x0 ==v x); subst.
      + rewrite lookup_add_eq in * by auto. invert H10. invert H1.
        simpl. econstructor.
      + rewrite lookup_add_ne in * by auto. eauto. }    
  - (* LET VECTOR *)
    invert Hsize. eq_size_of.
    invert Hpad. simpl in *. invs.
    eq_size_of.
    eapply IHeval_expr1 in H14.
    2: { eauto. }
    2: { eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape;
         try apply H5; eauto. }
    2: { eauto. }
    2: { eauto. }
    2: { eauto. }
    eapply IHeval_expr2; eauto.
    { intros.
      cases (x0 ==v x); subst.
      + rewrite lookup_add_eq in * by auto. invert H12. invert H3.
        erewrite result_has_shape_result_shape_nat.
        2: { eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape;
             try apply H5; eauto. }
        eapply relate_pads_filter_until_0; eauto.
        eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape
          in H0; eauto.
      + rewrite lookup_add_ne in * by auto. eauto. }
    { intros.
      cases (x0 ==v x); subst.
      + rewrite lookup_add_eq in * by auto. invert H12. invert H3.
        simpl.
        eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape;
          try apply H5; eauto.
      + rewrite lookup_add_ne in * by auto. eauto. }
  - (* CONCAT *)
    invert Hsize. pose proof H3 as Hsize1. pose proof H4 as Hsize2.
    clear H3. clear H4.
    invert Hpad.
    eq_size_of. invert H1. invert H2.
    simpl in *. invs.
    cases rsh. invert Hsh.
    
    pose proof Hsh as Hsh'.
    eapply result_has_shape_app_r in Hsh'.
    2: { reflexivity. }
    pose proof Hsh as Hsh''.
    eapply result_has_shape_app_l in Hsh''.
    2: { reflexivity. }
    pose proof H1. pose proof H2.

    pose proof H1 as Hsh1'. pose proof H2 as Hsh2'.
    eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in Hsh1';
      eauto.
    eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in Hsh2';
      eauto.
    eapply result_has_shape_length in Hsh. rewrite app_length in *.
    pose proof Hsh1' as Hsh1''. pose proof Hsh2' as Hsh2''.
    pose proof Hsh' as HH. pose proof Hsh'' as HHH.
    eapply result_has_shape_result_shape_nat in HH,HHH,Hsh1'',Hsh2''.
    rewrite Hsh1'',Hsh2'' in *. clear Hsh''. clear Hsh2''. subst.
    rewrite add_sub in *. rewrite minus_plus in *.
    pose proof Hsh1' as Hlen1. pose proof Hsh2' as Hlen2.
    eapply result_has_shape_length in Hlen1,Hlen2.
    repeat rewrite map_cons in *.
    rewrite <- Hlen1 in *. rewrite <- Hlen2 in *.
    
    cases l1; cases l2.
    { simpl in *. repeat rewrite firstn_nil.
      repeat rewrite skipn_nil. simpl.
      repeat rewrite firstn_nil. simpl.
      propositional; econstructor. }
    { simpl in *. 
      invert HHH. symmetry in H11.
      subst.
      eapply IHeval_expr2 in Hsh2'; eauto.
      simpl in *. invs.
      replace x with 0 in * by lia.
      replace y with 0 in * by lia.
      simpl. split. auto.
      split. rewrite gen_pad_filter_until_0.
      rewrite H11. rewrite <- gen_pad_filter_until_0. auto.

      replace (rev l2 ++ [r])%list with (rev (r::l2)) by auto.
      split.
      eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H3;
        eauto.
      invert H3.
      replace l4 with 0 by lia. simpl. econstructor.
      simpl.
      eapply Forall_forall. intros. eapply Forall_forall in H17.
      2: eassumption.
      eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H0;
        eauto.
      replace (rev l2 ++ [r])%list with (rev (r::l2)) in * by auto.
      simpl map in H0.
      eapply result_has_shape_forall in H0.      
      eapply relate_pads_filter_until_0.
      eapply Forall_rev in H0. eapply forall_skipn in H0.
      eapply forall_firstn in H0.
      eapply Forall_forall in H0.
      2: { apply H16. }
      eapply result_has_shape_filter_until_0. rewrite H11.
      erewrite <- result_has_shape_filter_until_0.  eauto.
      rewrite H11.
      eapply relate_pads_filter_until_0.
      eapply Forall_rev in H0. eapply forall_skipn in H0.
      eapply forall_firstn in H0.
      eapply Forall_forall in H0.
      2: { apply H16. }
      eauto.
      eauto. }
    { simpl in *. rewrite app_nil_r in *. 
      invert HH. symmetry in H11.
      eapply IHeval_expr1 in H1; eauto. simpl in *. invs.
      replace a with 0 in * by lia.
      replace b with 0 in * by lia.
      simpl. split.
      rewrite gen_pad_filter_until_0. rewrite H11.
      rewrite <- gen_pad_filter_until_0. auto.
      split. auto.
      split.
      eapply Forall_forall. intros. eapply Forall_forall in H12.
      2: eassumption.
      eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H;
        eauto.
      simpl map in H. eapply result_has_shape_forall in H.      
      eapply relate_pads_filter_until_0.
      eapply forall_skipn in H. eapply forall_firstn in H.
      eapply Forall_forall in H. 2: apply H14.
      eapply result_has_shape_filter_until_0.
      rewrite H11.
      erewrite <- result_has_shape_filter_until_0. eauto.
      rewrite H11.
      eapply relate_pads_filter_until_0.
      eapply forall_skipn in H. eapply forall_firstn in H.
      eapply Forall_forall in H. 2: apply H14.
      eauto.
      eauto.

      replace r2 with 0 by lia. simpl. econstructor. }

    invert HHH. invert HH.
    
    eapply IHeval_expr1 in H1; eauto.
    eapply IHeval_expr2 in H2; eauto.
    simpl in H1,H2. invs.

    rewrite firstn_app. replace (x - length (r::l1)) with 0 by lia.
    split. simpl. rewrite app_nil_r. auto.
    eapply Forall_forall. intros. eapply Forall_forall in H16.
    2: eassumption. subst.
    rewrite gen_pad_filter_until_0. rewrite H12.
    rewrite <- gen_pad_filter_until_0. auto.

    rewrite rev_app_distr. rewrite firstn_app.
    rewrite rev_length.
    replace (b - Datatypes.length (r0 :: l2)) with 0 by lia.
    split. simpl. rewrite app_nil_r.
    eapply Forall_forall. intros. eapply Forall_forall in H2.
    2: { eassumption. }
    subst.
    rewrite gen_pad_filter_until_0. rewrite H11.
    rewrite <- gen_pad_filter_until_0. auto.

    rewrite skipn_app. rewrite firstn_app.
    rewrite skipn_length.
    replace (l4 - (Datatypes.length (r :: l1) - x)) with 0 by lia.
    split. simpl. rewrite app_nil_r.
    eapply Forall_forall. intros. eapply Forall_forall in H18.
    2: { eassumption. }

    eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H;
      eauto.
    simpl map in H.
    eapply result_has_shape_forall in H.
    eapply relate_pads_filter_until_0.
    eapply forall_skipn in H. eapply forall_firstn in H.
    eapply Forall_forall in H. 2: eassumption.
    eapply result_has_shape_filter_until_0.
    rewrite <- H12. 
    erewrite <- result_has_shape_filter_until_0. eauto.
    rewrite <- H12.
    eapply relate_pads_filter_until_0.
    eapply forall_skipn in H. eapply forall_firstn in H.
    eapply Forall_forall in H. 2: eassumption.
    eauto.
    eauto.

    rewrite skipn_app. rewrite firstn_app.
    rewrite skipn_length. rewrite rev_length.
    replace (r2 - (Datatypes.length (r0 :: l2) - b)) with 0 by lia.
    simpl firstn at 2. rewrite app_nil_r.
    simpl.
    eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H0;
      eauto.
    simpl map in H0.
    eapply result_has_shape_forall in H0.
    eapply Forall_forall. intros. eapply Forall_forall in H17.
    2: eassumption.
    eapply relate_pads_filter_until_0.
    eapply Forall_rev in H0.
    eapply forall_skipn in H0. eapply forall_firstn in H0.
    eapply Forall_forall in H0. 2: eassumption.
    eapply result_has_shape_filter_until_0.
    rewrite <- H11. 
    erewrite <- result_has_shape_filter_until_0. eauto.
    rewrite <- H11.
    eapply relate_pads_filter_until_0.
    eapply Forall_rev in H0.
    eapply forall_skipn in H0. eapply forall_firstn in H0.
    eapply Forall_forall in H0. 2: eassumption. eauto.
    eauto.
  - (* TRANSPOSE *)
    invert Hpad; invert Hsize; eq_size_of.
    { (* STRONG *)
      invert H2. invert H6.
    simpl in *|-.
    pose proof Hconst as Hconst'.
    cases rsh.
    unfold transpose_result in Hsh. invert Hsh.
    eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape
      in Hconst'.
    2: { eauto. }
    2: { eauto. }

    pose proof Hconst as Hconst''.
    eapply constant_nonneg_bounds_size_of_no_vars in Hconst''; eauto.
    eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in Hconst''; eauto.
    eq_eval_Zlist. simpl map in *. invert H2.

    pose proof Hconst' as Hsh'.
    eapply result_has_shape_transpose_result in Hsh'.
    pose proof Hsh'. pose proof Hsh.
    eapply result_has_shape_result_shape_nat in H2,H4.
    rewrite H2 in H4. clear H2.

    unfold transpose_result in * |-.
    simpl.
    pose proof Hconst as Hconst''.
    eapply IHeval_expr in Hconst''; eauto.
    simpl in Hconst''.
    invs.

    simpl.

    cases l.
    { simpl. invert Hconst'. rewrite <- H1 in *.
      simpl in *.
      clear H2. clear H7. clear H10. clear H6.
      repeat rewrite rev_repeat in *. simpl.
      cases (Z.to_nat (eval_Zexpr_Z_total $0 m1)).
      - simpl in *. repeat rewrite skipn_nil.
        repeat rewrite firstn_nil. eauto.
      - simpl in H4. cases n. simpl in H4.
        invert H4. simpl in H4. invert H4.
        cases rsh. simpl in *. discriminate.
        simpl in H7. cases n0; invert H7.
        split. eapply forall_firstn. eapply Forall_repeat. reflexivity.
        split. eapply forall_firstn. eapply Forall_repeat. reflexivity.
        split. eapply forall_firstn. eapply forall_skipn.
        eapply Forall_repeat. simpl. repeat rewrite firstn_nil. eauto.
        eapply forall_firstn. eapply forall_skipn.
        eapply Forall_repeat. simpl. repeat rewrite firstn_nil. eauto. }
          
    erewrite result_has_shape_row_length in *.
    2: { inversion 1. }
    2: { eauto. }
    2: { inversion 1. }
    2: { eauto. }
    2: { inversion 1. }
    2: { eauto. }
    
    rewrite <- gen_pad_cons in *.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 m1)).
    { simpl. repeat rewrite skipn_nil. repeat rewrite firstn_nil. eauto. }
    rewrite filter_until_cons in * by lia.
    cases n. simpl in H4. invert H4.
    symmetry in H4.
    rewrite filter_until_cons in H4 by lia. invert H4.

    erewrite pad_list_result_shape_id in *; eauto.
    2: { invert Hconst'. lia. }
    2: { invert Hconst'. lia. }
    2: { invert Hconst'. lia. }
    
    erewrite firstn_transpose_result_list; eauto.
    2: { invert Hconst'. lia. }
    2: { invert Hconst'. lia. }

    rewrite sub_diag. 
    erewrite Forall_map.
    erewrite firstn_rev_transpose_result_list; eauto.
    2: { invert Hconst'. lia. }
    2: { invert Hconst'. lia. }
    erewrite Forall_map.

    invert Hconst'. 
    rewrite <- H9 in H11. simpl in H11.
    cases rsh. invert H11.
    cases n. invert H11. invert H11.
    
    split.
    {
      eapply Forall_forall. intros.
      eapply In_nat_range in H1.
      rewrite add_0_r. 
      erewrite <- (firstn_skipn x (r0::l)).
      erewrite get_col_app.
      2: { eapply forall_result_has_shape.
           eapply forall_firstn.
           econstructor. eauto. eauto.
           rewrite firstn_length. reflexivity. }
      2: { eapply forall_result_has_shape.
           eapply forall_skipn.
           econstructor. eauto. eauto.
           rewrite skipn_length. reflexivity. }
      2: lia.

      erewrite forall_gen_pad_get_col.
      2: { eauto. }
      2: lia.
      rewrite firstn_length.
      rewrite firstn_rev in H7. pose proof H7.
      eapply Forall_rev in H4. rewrite rev_involutive in H4.

      simpl length in *.
      erewrite <- (firstn_skipn (Datatypes.S (Datatypes.length l) - y)
                                (r0::l)).
      rewrite skipn_app.
      rewrite firstn_length. rewrite skipn_skipn.
      erewrite get_col_app.
      2: { eapply forall_result_has_shape.
           eapply forall_skipn. eapply forall_firstn.
           econstructor; eauto.
           rewrite skipn_length. rewrite firstn_length. simpl length.
           replace (min (Datatypes.S (length l) - y)
                        (Datatypes.S (length l))) with
             ((Datatypes.S (length l)) - y) by lia.
           reflexivity. }
      2: { eapply forall_result_has_shape.
           eapply forall_skipn. econstructor; eauto.
           rewrite skipn_length. simpl length.
           replace (min (Datatypes.S (length l) - y)
                        (Datatypes.S (length l))) with
             ((Datatypes.S (length l)) - y) by lia.
           replace (min (Datatypes.S (length l) - y)
                        (Datatypes.S (length l))) with
             ((Datatypes.S (length l)) - y) by lia.
           reflexivity. }
      2: { lia. }
      simpl length.
      replace (min (Datatypes.S (length l) - y)
                        (Datatypes.S (length l))) with
        ((Datatypes.S (length l)) - y) by lia.
      erewrite (forall_gen_pad_get_col (skipn _ (r0::l))).
      2: { eapply forall_skipn_le. eassumption.
           cases (x - (Datatypes.S (Datatypes.length l) - y)). lia.
           lia. }
      2: lia.
      rewrite skipn_length. simpl length.
      replace (x - (Datatypes.S (Datatypes.length l) - y)) with 0 by lia.
      rewrite add_0_l.
      replace (Datatypes.S (length l) - (Datatypes.S (length l) - y))
        with y by lia.
      clear H4.

      rewrite <- (rev_involutive (firstn _ _)).
      replace (Datatypes.S (length l)) with (length (r0::l)) by auto.
      rewrite <- skipn_rev.
      rewrite <- (firstn_skipn r (skipn y (rev (r0 :: l)))).
      rewrite rev_app_distr.
      rewrite skipn_app.
      rewrite rev_length. repeat rewrite skipn_length. rewrite rev_length.
      simpl length.
      replace (min x (Datatypes.S (Datatypes.length l))) with x by lia.
      erewrite get_col_app.
      2: { eapply forall_result_has_shape.
           eapply forall_skipn. eapply Forall_rev.
           eapply forall_skipn. eapply forall_skipn. eapply Forall_rev.
           econstructor; eauto.
           rewrite skipn_length. rewrite rev_length.
           repeat rewrite skipn_length. rewrite rev_length. reflexivity. }
      2: { eapply forall_result_has_shape.
           eapply forall_skipn. eapply Forall_rev.
           eapply forall_firstn. eapply forall_skipn. eapply Forall_rev.
           econstructor; eauto.
           rewrite skipn_length. rewrite rev_length.
           rewrite firstn_length. rewrite skipn_length.
           rewrite rev_length. reflexivity. }
      2: { lia. }
      erewrite <- (skipn_get_col (rev (firstn r (skipn y (rev (r0 :: l)))))).
      2: { eapply result_has_shape_rev.
           eapply forall_result_has_shape.
           eapply forall_firstn. eapply forall_skipn.
           eapply Forall_rev. econstructor; eauto.
           rewrite firstn_length. rewrite skipn_length.
           rewrite rev_length. simpl. reflexivity. }
      pose proof H10. eapply Forall_rev in H4.
      erewrite (forall_get_col_relate_pads_gen_pad
                  (rev (firstn r (skipn y (rev (r0 :: l)))))).
      4: { eapply forall_result_has_shape.
           eapply Forall_rev. eapply forall_firstn. eapply forall_skipn.
           eapply Forall_rev. econstructor; eauto.
           rewrite rev_length. rewrite firstn_length. rewrite skipn_length.
           rewrite rev_length. simpl length. reflexivity. }
      2: { eapply Forall_impl.
           2: { eapply H4. }
           simpl. intros. cases a0. propositional. invs. eassumption. }
      2: lia.
      
      rewrite rev_length. rewrite firstn_length. rewrite skipn_length.
      rewrite rev_length. simpl length.
      remember (Init.Nat.min r (Datatypes.S (Datatypes.length l) - y)).
      simpl gen_pad_list at 2.
      rewrite skipn_repeat.
      simpl (gen_pad_list (_::_)).
      repeat rewrite <- app_assoc.
      rewrite <- repeat_app.
      subst.
      clear H4. pose proof H6.

      rewrite skipn_skipn.
      rewrite <- rev_skipn_rev_skipn.
      rewrite skipn_rev. rewrite rev_involutive.
      rewrite skipn_length.
      rewrite sub_add_distr. simpl length.
      erewrite forall_get_col_relate_pads_gen_pad.
      4: { eapply forall_result_has_shape.
           eapply forall_firstn. eapply forall_skipn.
           econstructor; eauto.
           rewrite firstn_length. rewrite skipn_length. simpl length.
           rewrite min_l. reflexivity.
           lia. }
      2: { eapply forall_firstn_ge.
           eapply Forall_impl. 2:eassumption.
           simpl. intros. cases a0. propositional. invs.
           eassumption.
           lia. }
      rewrite firstn_length. rewrite skipn_length.
      remember (Init.Nat.min (Datatypes.S (Datatypes.length l) - x - r - y)
                             (Datatypes.length (r0 :: l) - x)).
      simpl (gen_pad_list (_::_)).
      repeat rewrite <- repeat_app.
      subst.
      simpl length. rewrite gen_pad_cons.
      rewrite gen_pad_filter_until_0. rewrite <- H13.
      rewrite <- gen_pad_filter_until_0. f_equal. f_equal.
      rewrite min_l by lia.
      repeat rewrite add_assoc.
      rewrite add_sub_assoc.
      2: { lia. }
      repeat rewrite <- sub_add_distr.
      rewrite (Nat.add_comm r y).
      rewrite (Nat.add_comm x (y+r)).
      rewrite <- add_assoc.
      rewrite sub_add_distr.
      rewrite sub_add_distr.
      assert (r <= (Datatypes.S (Datatypes.length l) - y) \/
                r > (Datatypes.S (Datatypes.length l) - y))
        as Hcase by lia.
      inversion Hcase as [ Hcase1 | Hcase2 ]; clear Hcase.
      - rewrite min_l by eauto.
        cases (x - (Datatypes.S (Datatypes.length l) - y - r)).
        + rewrite sub_0_r.
          rewrite <- add_sub_swap.
          2: { lia. }
          rewrite sub_add by auto.
          rewrite <- sub_add_distr.
          rewrite Nat.add_comm.
          rewrite add_assoc.
          rewrite le_plus_minus_r. reflexivity.
          rewrite Nat.add_comm. rewrite H9. auto.
        + rewrite <- Heq0.
          rewrite (not_le_minus_0 _ x).
          2: { lia. }
          rewrite add_0_l. rewrite add_sub_swap.
          replace (x - (x - (Datatypes.S (Datatypes.length l) - y - r))) with
            ((Datatypes.S (Datatypes.length l) - y - r)).
          2: { lia. }
          rewrite <- sub_add_distr.
          rewrite (Nat.add_comm y).
          rewrite <- add_assoc.
          rewrite sub_add. reflexivity.
          lia.
          eapply le_sub_l.
      - rewrite min_r by lia.
        rewrite (not_le_minus_0 _ r).
        2: { lia. }
        rewrite sub_0_r. rewrite sub_0_l. rewrite add_0_l.
        rewrite minus_plus.
        rewrite sub_add. reflexivity.
        lia.
      - lia. }
    split.
    { eapply Forall_forall. intros.
      eapply In_nat_range in H1.
      rewrite <- Heq in *.

      erewrite get_col_rev.
      2: { econstructor. reflexivity. eauto. eauto. }
      2: { lia. }

      erewrite <- (firstn_skipn x (r0::l)).
      rewrite map_app.
      erewrite get_col_app with (b:=(Z.to_nat (eval_Zexpr_Z_total $0 m1))).
      2: { eapply result_has_shape_map_rev.
           eapply forall_result_has_shape. eapply forall_firstn.
           econstructor; eauto. rewrite firstn_length. reflexivity. }
      2: { eapply result_has_shape_map_rev.
           eapply forall_result_has_shape. eapply forall_skipn.
           econstructor; eauto. rewrite skipn_length. reflexivity. }
      2: { lia. }
      erewrite forall_gen_pad_get_col.
      2: { eapply Forall_map.
           eapply Forall_impl. 2: eassumption.
           simpl. intros. subst. erewrite rev_repeat.
           reflexivity. }
      rewrite map_length. rewrite firstn_length.
      rewrite min_l.
      2: { simpl. lia. }
      rewrite <- (rev_involutive (r0::l)).
      rewrite <- (firstn_skipn y (rev (r0::l))).
      rewrite rev_app_distr. rewrite skipn_app. rewrite map_app.
      rewrite rev_length. rewrite skipn_length. rewrite rev_length.
      erewrite get_col_app with (b:=(Z.to_nat (eval_Zexpr_Z_total $0 m1))).
      2: { eapply result_has_shape_map_rev.
           eapply forall_result_has_shape. eapply forall_skipn.
           eapply Forall_rev. eapply forall_skipn. eapply Forall_rev.
           econstructor; eauto. rewrite skipn_length.
           rewrite rev_length. rewrite skipn_length. rewrite rev_length.
           reflexivity. }
      2: { eapply result_has_shape_map_rev.
           eapply forall_result_has_shape. eapply forall_skipn.
           eapply Forall_rev. eapply forall_firstn. eapply Forall_rev.
           econstructor; eauto. rewrite skipn_length.
           rewrite rev_length. rewrite firstn_length. rewrite rev_length.
           reflexivity. }
      2: lia.
      erewrite (forall_gen_pad_get_col (map (fun x1 : result => match x1 with
                                | S _ => x1
                                | V l4 => V (rev l4)
                                end)
          (skipn (x - (Datatypes.length (r0 :: l) - y))
                 (rev (firstn y (rev (r0 :: l))))))).
      2: { eapply Forall_map. eapply forall_skipn. eapply Forall_rev.
           eapply Forall_impl. 2: eassumption.
           simpl. intros. subst. rewrite rev_repeat.
           reflexivity. }
      2: lia.
      2: lia.
      rewrite map_length. rewrite skipn_length.
      rewrite rev_length. rewrite firstn_length. rewrite rev_length.
      rewrite min_l.
      2: simpl; lia.
      simpl length. pose proof H12. rewrite H9.
      eapply le_add_le_sub_r in H4.
      eapply sub_0_le in H4.
      rewrite H4. rewrite sub_0_r.

      rewrite <- (firstn_skipn r (skipn y (rev (r0 :: l)))).
      rewrite rev_app_distr. rewrite skipn_app.
      rewrite map_app.
      erewrite get_col_app with (b:=(Z.to_nat (eval_Zexpr_Z_total $0 m1))).
      2: { eapply result_has_shape_map_rev.
           eapply forall_result_has_shape. eapply forall_skipn.
           eapply Forall_rev. eapply forall_skipn. eapply forall_skipn.
           eapply Forall_rev.
           econstructor; eauto. rewrite skipn_length.
           rewrite rev_length. repeat rewrite skipn_length.
           rewrite rev_length. reflexivity. }
      2: { eapply result_has_shape_map_rev.
           eapply forall_result_has_shape. eapply forall_skipn.
           eapply Forall_rev. eapply forall_firstn. eapply forall_skipn.
           eapply Forall_rev.
           econstructor; eauto. rewrite skipn_length.
           repeat rewrite rev_length. repeat rewrite skipn_length.
           rewrite firstn_length. rewrite skipn_length.
           rewrite rev_length. reflexivity. }
      2: lia.

      rewrite rev_length. repeat rewrite skipn_length. rewrite rev_length.
      simpl length.
      erewrite (forall_get_col_relate_pads_gen_pad
               (map (fun x1 : result => match x1 with
                                 | S _ => x1
                                 | V l4 => V (rev l4)
                                 end)
           (skipn (x - (Datatypes.S (Datatypes.length l) - y - r))
                  (rev (firstn r (skipn y (rev (r0 :: l))))))))
               with (m:=(Z.to_nat (eval_Zexpr_Z_total $0 m1))).
      2: { eapply Forall_map.
           eapply forall_skipn. eapply Forall_rev.
           eapply Forall_impl. 2: eassumption. simpl.
           intros. cases a0. propositional.
           invs. eassumption. }
      2: { lia. }
      2: { eapply result_has_shape_map_rev.
           eapply forall_result_has_shape.
           eapply forall_skipn. eapply Forall_rev. eapply forall_firstn.
           eapply forall_skipn. eapply Forall_rev. econstructor; eauto.
           rewrite skipn_length. rewrite rev_length.
           rewrite firstn_length. rewrite skipn_length. rewrite rev_length.
           reflexivity. }
      rewrite map_length. rewrite skipn_length.
      rewrite rev_length. rewrite firstn_length. rewrite skipn_length.
      rewrite rev_length. simpl length.

      rewrite skipn_skipn.
      rewrite <- rev_skipn_rev_skipn.
      rewrite skipn_rev. rewrite rev_involutive.
      rewrite skipn_length. simpl length.
      pose proof H5.

      erewrite forall_get_col_relate_pads_gen_pad
               with (m:=(Z.to_nat (eval_Zexpr_Z_total $0 m1))).
      2: { eapply Forall_map.
           eapply forall_firstn_ge.
           eapply Forall_impl. 2: eassumption.
           simpl. intros. cases a0. propositional.
           invs. eassumption.
           rewrite Nat.add_comm.
           rewrite sub_add_distr.
           eapply le_sub_le_add_r.
           lia. }
      2: { lia. }
      rewrite map_length. rewrite firstn_length.
      rewrite skipn_length. simpl length.
      remember (Init.Nat.min (Datatypes.S (Datatypes.length l) - x - (r + y))
                             (Datatypes.S (Datatypes.length l) - x)).
      remember (Init.Nat.min r (Datatypes.S (Datatypes.length l) - y) -
                  (x - (Datatypes.S (Datatypes.length l) - y - r))).
      simpl.
      repeat rewrite <- repeat_app.
      subst.
      rewrite gen_pad_filter_until_0.
      rewrite <- H13.
      rewrite <- gen_pad_filter_until_0. f_equal. f_equal.
      rewrite <- H9 in *.
      rewrite min_l.
      2: { eapply le_sub_l. }

      cases (Datatypes.S (Datatypes.length l) - y - r).
      - rewrite sub_0_r. rewrite min_r.
        2: { lia. }
        repeat rewrite <- sub_add_distr.
        rewrite (Nat.add_comm r y). repeat rewrite add_assoc.
        rewrite (sub_add_distr _ _ r). rewrite (Nat.add_comm y x).
        rewrite <- (add_assoc x).
        rewrite Nat.add_comm. rewrite add_assoc. rewrite (Nat.add_comm y x).
        rewrite (Nat.add_comm (_ - _ - _)).
        rewrite add_assoc.
        rewrite le_plus_minus_r.
        2: { eauto. }
        rewrite <- sub_add_distr.
        rewrite <- (add_assoc x y r).
        rewrite (Nat.add_comm x).
        repeat rewrite sub_add_distr.
        rewrite Heq0. rewrite sub_0_l. rewrite add_0_r. reflexivity.
      - rewrite min_l.
        2: { lia. }
        rewrite <- Heq0. repeat rewrite add_assoc.
        rewrite <- sub_add_distr.
        rewrite (Nat.add_comm r y). rewrite add_assoc.
        rewrite sub_add_distr.
        rewrite (Nat.add_comm _ y).
        repeat rewrite add_assoc.
        rewrite (Nat.add_comm y).
        rewrite add_sub_assoc.
        2: { lia. }
        rewrite <- add_assoc.
        cases (Datatypes.S (length l) - (x + y) - r).
        + rewrite add_0_l.
          rewrite <- sub_add_distr.
          rewrite <- sub_add_distr in Heq1.
          rewrite <- add_assoc in Heq1.
          rewrite Nat.add_comm in Heq1.
          rewrite sub_add_distr in Heq1.
          rewrite <- add_assoc.
          rewrite add_sub_swap.
          2: { eapply le_sub_l. }
          lia.
        + rewrite <- Heq1.
          rewrite sub_add.
          2: { lia. }
          rewrite le_plus_minus_r.
          2: { lia. }
          rewrite <- sub_add_distr in Heq1.
          rewrite <- add_assoc in Heq1.
          rewrite Nat.add_comm in Heq1.
          rewrite sub_add_distr in Heq1.
          rewrite (not_le_minus_0 x).
          2: { lia. }
          rewrite sub_0_r. reflexivity.
      - eapply result_has_shape_map_rev.
        eapply forall_result_has_shape. eapply forall_firstn.
        eapply forall_skipn. econstructor; eauto.
        rewrite firstn_length. rewrite skipn_length. reflexivity. }

    erewrite skipn_transpose_result_list.
    2: { econstructor; eauto. }
    2: lia.
    2: lia.
    2: lia.
    rewrite firstn_map.

    rewrite firstn_skipn_comm.
    erewrite firstn_rev_transpose_result_list.
    2: { econstructor; eauto. }
    2: lia.
    2: lia.
    2: lia.
    rewrite skipn_map.

    rewrite firstn_nat_range_rec. rewrite sub_diag. rewrite add_0_l.
    rewrite skipn_nat_range. rewrite <- Heq. rewrite <- sub_min_distr_r.
    rewrite minus_plus.

    split.
    { eapply Forall_map.
      eapply Forall_forall. intros.
      eapply In_nat_range_rec in H1.
      erewrite firstn_get_col.
      2: { econstructor; eauto. }
      erewrite rev_get_col.
      2: { econstructor; eauto. }
      2: { lia. }
      erewrite firstn_get_col.
      2: { eapply result_has_shape_rev. econstructor; eauto. }
      split.
      2: split; eauto.
      erewrite forall_gen_pad_get_col.
      2: { eauto. }
      2: { lia. }
      simpl. eapply Forall_repeat. rewrite gen_pad_filter_until_0.
      rewrite <- H13. rewrite <- gen_pad_filter_until_0.
      reflexivity.
      erewrite forall_gen_pad_get_col.
      2: { eauto. }
      2: { lia. }
      simpl. eapply Forall_repeat. rewrite gen_pad_filter_until_0.
      rewrite <- H13. rewrite <- gen_pad_filter_until_0.
      reflexivity. }
    { eapply Forall_map.
      eapply Forall_forall. intros.
      eapply In_nat_range_rec in H1.
      split.
      2: split; eauto.
      erewrite get_col_rev.
      2: { econstructor. reflexivity.
           rewrite Heq in *. eauto. rewrite Heq in *. eauto. }
      2: { lia. }
      erewrite firstn_get_col.
      2: { eapply result_has_shape_map_rev. econstructor; eauto. }
      rewrite firstn_map.
      erewrite forall_gen_pad_get_col.
      rewrite map_length.
      2: { eapply Forall_map. eapply Forall_impl. 2: eassumption.
           simpl. intros. subst. rewrite <- repeat_cons. rewrite rev_repeat.
           reflexivity. }
      2: { lia. }
      eapply Forall_repeat. erewrite gen_pad_filter_until_0.
      rewrite <- H13. erewrite <- gen_pad_filter_until_0. reflexivity.

      erewrite rev_get_col.
      2: { econstructor; eauto. }
      2: { rewrite Heq. lia. }
      erewrite firstn_get_col.
      2: { eapply result_has_shape_rev. econstructor; eauto. }
      erewrite forall_gen_pad_get_col.
      2: { eauto. }
      2: { lia. }
      eapply Forall_repeat. rewrite gen_pad_filter_until_0.
      rewrite <- H13. rewrite <- gen_pad_filter_until_0. reflexivity. }
    }
    { (* WEAK *)
    invert H2. invert H5.
    simpl in *|-.
    pose proof Hconst as Hconst'.
    cases rsh.
    unfold transpose_result in Hsh. invert Hsh.
    eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape
      in Hconst'.
    2: { eauto. }
    2: { eauto. }

    pose proof Hconst as Hconst''.
    eapply constant_nonneg_bounds_size_of_no_vars in Hconst''; eauto.
    eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in Hconst''; eauto.
    eq_eval_Zlist. simpl map in *. invert H2.

    pose proof Hconst' as Hsh'.
    eapply result_has_shape_transpose_result in Hsh'.
    pose proof Hsh'. pose proof Hsh.
    eapply result_has_shape_result_shape_nat in H2,H4.
    rewrite H2 in H4. clear H2.

    unfold transpose_result in * |-.

    pose proof Hconst as Hconst''.
    eapply IHeval_expr in Hconst''; eauto.
    simpl in Hconst''.
    invs.

    simpl.
    cases l.
    { simpl. invert Hconst'.
      clear H2. clear H6. clear H5. clear H8.
      repeat rewrite rev_repeat in *. simpl.
      split. auto. split. auto.
      cases (Z.to_nat (eval_Zexpr_Z_total $0 m0)).
      - simpl in *. repeat rewrite firstn_nil. eauto.
      - simpl in H4. cases n. simpl in H4.
        invert H4. simpl in H4. invert H4.
        rewrite <- H1 in *. simpl in H6.
        cases rsh. simpl in *. discriminate.
        split. eapply forall_firstn. eapply Forall_repeat.
        simpl. repeat rewrite firstn_nil. eauto.
        eapply forall_firstn. eapply Forall_repeat.
        simpl. repeat rewrite firstn_nil. eauto. }
          
    erewrite result_has_shape_row_length in *.
    2: { inversion 1. }
    2: { eauto. }
    2: { inversion 1. }
    2: { eauto. }
    2: { inversion 1. }
    2: { eauto. }
    
    rewrite <- gen_pad_cons in *.
    split. auto. split. auto.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 m0)).
    { simpl. repeat rewrite firstn_nil. eauto. }
    rewrite filter_until_cons in * by lia.
    cases n. simpl in H4. invert H4.
    symmetry in H4.
    rewrite filter_until_cons in H4 by lia. invert H4.

    erewrite pad_list_result_shape_id in *; eauto.
    2: { invert Hconst'. lia. }
    2: { invert Hconst'. lia. }
    2: { invert Hconst'. lia. }
    
    erewrite firstn_transpose_result_list; eauto.
    2: { invert Hconst'. lia. }
    2: { invert Hconst'. lia. }

    rewrite sub_diag. 
    erewrite Forall_map.
    erewrite firstn_rev_transpose_result_list; eauto.
    2: { invert Hconst'. lia. }
    2: { invert Hconst'. lia. }
    erewrite Forall_map.

    invert Hconst'. 
    rewrite <- H7 in H9. simpl in H9.
    cases rsh. invert H9.
    cases n. invert H9. invert H9.
    
    split.
    {
      eapply Forall_forall. intros.
      eapply In_nat_range in H1.
      rewrite add_0_r.
      rewrite firstn_add.
      rewrite Forall_app.
      erewrite firstn_get_col.
      2: { econstructor; eauto. }
      erewrite forall_gen_pad_get_col.
      2: { eauto. }
      2: { lia. }
      rewrite firstn_add.
      erewrite rev_get_col.
      2: { econstructor; eauto. }
      2: lia.
      erewrite firstn_get_col.
      2: { eapply result_has_shape_rev. econstructor; eauto. }
      rewrite Forall_app.
      erewrite (forall_gen_pad_get_col (firstn y (rev (r0 :: l)))).
      2: { eauto. }
      2: { lia. }

      erewrite skipn_get_col.
      2: { econstructor; eauto. }
      erewrite skipn_get_col.
      2: { eapply result_has_shape_rev. econstructor; eauto. }
      erewrite firstn_get_col.
      2: { eapply forall_result_has_shape.
           eapply forall_skipn. econstructor; eauto.
           rewrite skipn_length. reflexivity. }
      erewrite firstn_get_col.
      2: { eapply forall_result_has_shape.
           eapply forall_skipn. eapply Forall_rev. econstructor; eauto.
           rewrite skipn_length. rewrite rev_length. reflexivity. }
      erewrite forall_get_col_relate_pads_gen_pad.
      2: { eapply Forall_impl. 2: eassumption. simpl.
           intros. cases a0. propositional. invs. eassumption. }
      3: { eapply forall_result_has_shape. eapply forall_firstn.
           eapply forall_skipn. econstructor. eauto. eauto.
           rewrite firstn_length. rewrite skipn_length. reflexivity. }
      2: { lia. }
      erewrite forall_get_col_relate_pads_gen_pad.
      2: { eapply Forall_impl. 2: eassumption. simpl.
           intros. cases a0. propositional. invs. eassumption. }
      3: { eapply forall_result_has_shape. eapply forall_firstn.
           eapply forall_skipn. eapply Forall_rev. econstructor. eauto. eauto.
           rewrite firstn_length. rewrite skipn_length. rewrite rev_length.
           reflexivity. }
      2: { lia. }
      rewrite gen_pad_filter_until_0. rewrite H10.
      rewrite <- gen_pad_filter_until_0.
      split.
      split. eapply Forall_repeat. auto. eapply Forall_repeat. auto.
      split.
      split. eapply Forall_repeat. auto. eapply Forall_repeat. auto.
      eauto. }

    { eapply Forall_forall. intros. eapply In_nat_range in H1.
      erewrite firstn_get_col.
      2: { econstructor; eauto. }
      erewrite rev_get_col.
      2: { econstructor; eauto. }
      2: { lia. }
      erewrite firstn_get_col.
      2: { eapply result_has_shape_rev; econstructor; eauto. }
      repeat rewrite firstn_add.
      repeat erewrite get_col_app.
      2: { eapply forall_result_has_shape. eapply forall_firstn.
           eapply Forall_rev. econstructor; eauto.
           rewrite firstn_length. rewrite rev_length. reflexivity. }
      2: { eapply forall_result_has_shape. eapply forall_firstn.
           eapply forall_skipn. eapply Forall_rev. econstructor; eauto.
           rewrite firstn_length. erewrite skipn_length. rewrite rev_length.
           reflexivity. }
      2: { lia. }
      2: { eapply forall_result_has_shape. eapply forall_firstn.
           econstructor; eauto. rewrite firstn_length. reflexivity. }
      2: { eapply forall_result_has_shape. eapply forall_firstn.
           eapply forall_skipn.
           econstructor; eauto. rewrite firstn_length.
           rewrite skipn_length. reflexivity. }
      2: lia.
      repeat rewrite Forall_app.

      erewrite forall_gen_pad_get_col.
      2: { eauto. }
      2: { lia. }
      erewrite (forall_gen_pad_get_col (firstn y (rev (r0 :: l)))).
      2: { eauto. }
      2: { lia. }

      erewrite get_col_rev.
      2: { eapply forall_result_has_shape.
           eapply forall_firstn. eapply forall_skipn.
           econstructor; eauto. rewrite firstn_length. rewrite skipn_length.
           reflexivity. }
      2: lia.
      erewrite get_col_rev.
      2: { eapply forall_result_has_shape.
           eapply forall_firstn. eapply forall_skipn. eapply Forall_rev.
           econstructor; eauto. rewrite firstn_length. rewrite skipn_length.
           rewrite rev_length. reflexivity. }
      2: lia.

      erewrite forall_get_col_relate_pads_gen_pad.
      2: { eapply Forall_map.
           eapply Forall_impl. 2: eassumption. simpl. intros. subst.
           cases a0. propositional. invs. eassumption. }
      3: { eapply result_has_shape_map_rev. eapply forall_result_has_shape.
           eapply forall_firstn. eapply forall_skipn.
           econstructor; eauto. rewrite firstn_length.
           rewrite skipn_length. reflexivity. }
      2: { lia. }
      erewrite forall_get_col_relate_pads_gen_pad.
      2: { eapply Forall_map.
           eapply Forall_impl. 2: eassumption. simpl. intros. subst.
           cases a0. propositional. invs. eassumption. }
      3: { eapply result_has_shape_map_rev. eapply forall_result_has_shape.
           eapply forall_firstn. eapply forall_skipn.
           eapply Forall_rev.
           econstructor; eauto. rewrite firstn_length.
           rewrite skipn_length. rewrite rev_length. reflexivity. }
      2: { lia. }

      rewrite gen_pad_filter_until_0. rewrite H10.
      rewrite <- gen_pad_filter_until_0.
      split. split. eapply Forall_repeat. auto. eapply Forall_repeat. auto.
      split. split. eapply Forall_repeat. auto. eapply Forall_repeat. auto.
      eauto.
    }
    }
  - (* TRUNCR *)
    invert Hpad. invert Hconst. invert Hsize. pose proof H9 as Hsize.
      erewrite size_of_sizeof in * by eauto. simpl in H3.
    assert (eval_Zexpr_Z_total $0 k = kz)%Z.
    { invs.
      eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
        with (v:=$0) in H5.
      eapply eval_Zexpr_Z_eval_Zexpr in H.
      invert H5. eapply H6 in H. invert H. reflexivity. }
    subst. invs.
    eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H9;
      eauto.
    cases rsh. invert Hsh.
    pose proof Hsh as Hsh'.
    eapply result_has_shape_rev in Hsh'.
    rewrite rev_involutive in Hsh'.
    pose proof H9 as Hsh''.
    eapply result_has_shape_filter_until_0 in Hsh''.
    repeat rewrite map_cons in Hsh''.
    eapply result_has_shape_rev in Hsh''.
    eapply result_has_shape_truncl_list
      with (k:=(Z.to_nat (eval_Zexpr_Z_total $0 k))) in Hsh''.
    eapply result_has_shape_result_shape_nat in Hsh',Hsh''.
    rewrite Hsh' in Hsh''. clear Hsh'.

    simpl in Hsh''.
    cases n. simpl in *.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 m) -
             Z.to_nat (eval_Zexpr_Z_total $0 k)).
    { simpl in *.
      pose proof (truncl_list_length_empty
                    (Z.to_nat (eval_Zexpr_Z_total $0 k)) (rev l)).
      rewrite rev_length in *.
      erewrite result_has_shape_length in H6.
      2: { eauto. }
      assert (Z.to_nat (eval_Zexpr_Z_total $0 m) <=
                Z.to_nat (eval_Zexpr_Z_total $0 k)) by lia.
      eapply H6 in H10. rewrite H10.
      simpl. repeat rewrite skipn_nil. repeat rewrite firstn_nil. eauto. }
    simpl in *. invert Hsh''.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 m) -
             Z.to_nat (eval_Zexpr_Z_total $0 k)).
    { simpl in *.
      pose proof (truncl_list_length_empty
                    (Z.to_nat (eval_Zexpr_Z_total $0 k)) (rev l)).
      rewrite rev_length in *.
      erewrite result_has_shape_length in H6.
      2: { eauto. }
      assert (Z.to_nat (eval_Zexpr_Z_total $0 m) <=
                Z.to_nat (eval_Zexpr_Z_total $0 k)) by lia.
      eapply H6 in H10. rewrite H10.
      simpl. repeat rewrite skipn_nil. repeat rewrite firstn_nil. eauto. }
    simpl in *. invert Hsh''.
    
    rewrite rev_involutive.
    eapply IHeval_expr in H2.
    2: eauto.
    2: eauto.
    2: eauto.
    2: eauto.
    2: eauto.
    simpl in *. invs.
    rewrite truncl_list_skipn.
    rewrite gen_pad_filter_until_0.
    rewrite H11.
    rewrite <- gen_pad_filter_until_0.
    split.
    eapply forall_firstn_sub. eauto.
    split.
    eapply forall_firstn_skipn. eauto.

    split.

    rewrite <- rev_involutive with (l:=l) in H10.
    rewrite <- firstn_skipn
      with (n:=(Z.to_nat (eval_Zexpr_Z_total $0 k))) (l:=rev l) in H10.
    rewrite rev_app_distr in H10.
    rewrite skipn_app in H10. rewrite firstn_app in H10.
    rewrite skipn_length in H10. rewrite rev_length in H10.
    rewrite skipn_length in H10. rewrite rev_length in H10.
    eapply Forall_app in H10. invs.
    eapply Forall_forall. intros. eapply Forall_forall in H12. 2: eauto.

    eapply result_has_shape_forall in H9.
    eapply Forall_rev in H9.
    eapply forall_skipn in H9.
    eapply Forall_rev in H9.
    eapply forall_skipn in H9.
    eapply forall_firstn in H9.
    eapply Forall_forall in H9.
    2: eassumption.
    eapply relate_pads_filter_until_0.
    eapply result_has_shape_filter_until_0.
    rewrite H11.
    erewrite <- result_has_shape_filter_until_0. eauto.
    rewrite H11.
    eapply relate_pads_filter_until_0. eauto. eauto.

    rewrite skipn_skipn.
    rewrite sub_add by lia.
    eapply Forall_forall. intros. eapply Forall_forall in H13. 2: eauto.
    eapply result_has_shape_forall in H9.
    eapply Forall_rev in H9.
    eapply forall_skipn in H9.
    eapply forall_firstn in H9.
    eapply Forall_forall in H9.
    2: eassumption.
    eapply relate_pads_filter_until_0.
    eapply result_has_shape_filter_until_0.
    rewrite H11.
    erewrite <- result_has_shape_filter_until_0. eauto.
    rewrite H11.
    eapply relate_pads_filter_until_0. eauto. eauto.
  - (* TRUNCL *)
    invert Hpad. invert Hconst. invert Hsize. pose proof H9 as Hsize.
      erewrite size_of_sizeof in * by eauto. simpl in H3.
    assert (eval_Zexpr_Z_total $0 k = kz)%Z.
    { invs.
      eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
        with (v:=$0) in H5.
      eapply eval_Zexpr_Z_eval_Zexpr in H.
      invert H5. eapply H6 in H. invert H. reflexivity. }
    subst. invs.
    eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H9;
      eauto.
    cases rsh. invert Hsh.
    pose proof Hsh as Hsh'.
    eapply result_has_shape_rev in Hsh'.
    pose proof H9 as Hsh''.
    eapply result_has_shape_filter_until_0 in Hsh''.
    repeat rewrite map_cons in Hsh''.
    eapply result_has_shape_truncl_list
      with (k:=(Z.to_nat (eval_Zexpr_Z_total $0 k))) in Hsh''.
    eapply result_has_shape_rev in Hsh''.
    eapply result_has_shape_result_shape_nat in Hsh',Hsh''.
    rewrite Hsh' in Hsh''. clear Hsh'.

    simpl in Hsh''.
    cases n. simpl in *.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 m) -
             Z.to_nat (eval_Zexpr_Z_total $0 k)).
    { simpl in *.
      pose proof (truncl_list_length_empty
                    (Z.to_nat (eval_Zexpr_Z_total $0 k)) l).
      erewrite result_has_shape_length in H6.
      2: { eauto. }
      assert (Z.to_nat (eval_Zexpr_Z_total $0 m) <=
                Z.to_nat (eval_Zexpr_Z_total $0 k)) by lia.
      eapply H6 in H10. rewrite H10.
      simpl. repeat rewrite skipn_nil. repeat rewrite firstn_nil. eauto. }
    simpl in *. invert Hsh''.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 m) -
             Z.to_nat (eval_Zexpr_Z_total $0 k)).
    { simpl in *.
      pose proof (truncl_list_length_empty
                    (Z.to_nat (eval_Zexpr_Z_total $0 k)) l).
      erewrite result_has_shape_length in H6.
      2: { eauto. }
      assert (Z.to_nat (eval_Zexpr_Z_total $0 m) <=
                Z.to_nat (eval_Zexpr_Z_total $0 k)) by lia.
      eapply H6 in H10. rewrite H10.
      simpl. repeat rewrite skipn_nil. repeat rewrite firstn_nil. eauto. }
    simpl in *. invert Hsh''.

    eapply IHeval_expr in H2.
    2: eauto.
    2: eauto.
    2: eauto.
    2: eauto.
    2: eauto.
    simpl in H2. invs.
    rewrite truncl_list_skipn in *.

    rewrite gen_pad_filter_until_0.
    rewrite H11.
    rewrite <- gen_pad_filter_until_0.
    split.
    eapply forall_firstn_skipn. eauto.
    split.

    replace l with (rev (rev l)).
    2: { rewrite rev_involutive. auto. }
    eapply forall_firstn_sub. eauto.
    rewrite skipn_skipn.
    rewrite sub_add by lia.

    split.
    eapply Forall_forall. intros. eapply Forall_forall in H10. 2: eassumption.
    eapply result_has_shape_forall in H9.
    eapply forall_skipn in H9.
    eapply forall_firstn in H9.
    eapply Forall_forall in H9. 2: eassumption.
    eapply relate_pads_filter_until_0.
    eapply result_has_shape_filter_until_0.
    rewrite H11.
    erewrite <-  result_has_shape_filter_until_0.
    eauto.
    rewrite H11.
    eapply relate_pads_filter_until_0. eauto. eauto.

    rewrite <- firstn_skipn
      with (l:=l) (n:=(Z.to_nat (eval_Zexpr_Z_total $0 k))) in H13.
    rewrite rev_app_distr in *. rewrite skipn_app in *.
    rewrite firstn_app in *.
    rewrite skipn_length in *. rewrite rev_length in *.
    rewrite skipn_length in *. eapply Forall_app in H13. invs.
    eapply Forall_forall. intros. eapply Forall_forall in H12.
    2: eassumption.

    eapply result_has_shape_forall in H9.
    eapply forall_skipn in H9. eapply Forall_rev in H9.
    eapply forall_skipn in H9. eapply forall_firstn in H9.
    eapply Forall_forall in H9. 2: eassumption.
    eapply relate_pads_filter_until_0.
    eapply result_has_shape_filter_until_0.
    rewrite H11.
    erewrite <- result_has_shape_filter_until_0. eauto.
    rewrite H11.
    eapply relate_pads_filter_until_0.
    eauto. eauto.
  - (* PADR *)
    invert Hsize. 
    invert Hpad.
    { simpl in Hconst. invs. eq_size_of. invert H5. invert H6.
      pose proof H2 as Hh.
      eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H2;
        eauto.
      simpl in H2. rewrite H13 in H2. simpl in H2.
      invert H2. rewrite app_nil_l in *.
      simpl gen_pad_list in *.
      rewrite <- gen_pad_cons in *.
      pose proof (result_has_shape_gen_pad (Z.to_nat kz :: map Z.to_nat sz)).
      eapply result_has_shape_result_shape_nat in Hsh,H2.
      rewrite Hsh in H2. clear Hsh.
      
      pose proof H1 as Hsize.
      eapply constant_nonneg_bounds_size_of_no_vars in Hsize; eauto.
      invert Hsize.
      eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H10.
      eq_eval_Zlist.
      eapply eval_Zexpr_Z_eval_Zexpr in H.
      eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
        with (v:=$0) in H; eauto. invert H.
      repeat rewrite <- map_cons.
      eapply relate_pads_filter_until_0.
      eapply result_has_shape_filter_until_0.
      rewrite H2.
      erewrite <- result_has_shape_filter_until_0.
      repeat rewrite map_cons. eapply result_has_shape_gen_pad.
      rewrite H2.
      repeat rewrite <- map_cons in *.
      eapply relate_pads_filter_until_0.
      eapply result_has_shape_gen_pad.
      eapply relate_pads_gen_pad_id. }
    
    subst. invert Hconst. eq_size_of. invert H8. invert H10.
    assert (eval_Zexpr_Z_total $0 k = kz)%Z.
    { invs.
      eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
        with (v:=$0) in H7. invert H7.
      eapply eval_Zexpr_Z_eval_Zexpr in H. eapply H5 in H. invert H.
      auto. }
    subst.
    cases rsh. invert Hsh.
    
    pose proof H4.
    eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H4.
    2: eauto.
    2: eauto.
    pose proof Hsh.
    pose proof Hsh.
    eapply result_has_shape_app_l in H8.
    eapply result_has_shape_app_r in H10.
    2: { simpl. rewrite repeat_length. reflexivity. }
    2: { reflexivity. }
    repeat rewrite map_cons in *.
    simpl in H8.
    simpl.
    pose proof H8.
    eapply result_has_shape_length in H11.
    rewrite repeat_length in H11.
    pose proof H7.
    eapply constant_nonneg_bounds_size_of_no_vars in H12.
    2: { eauto. }
    eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H12.
    invert H12.
    eq_eval_Z. eq_eval_Zlist.
    pose proof H4. pose proof H10.
    eapply result_has_shape_result_shape_nat in H12, H13.
    rewrite H13 in H12. clear H13.
    pose proof Hsh. eapply result_has_shape_length in H13.
    rewrite app_length in *. simpl length in *. rewrite repeat_length in *.
    subst.
    rewrite add_sub in *.
    rewrite minus_plus in *.
    pose proof H8.
    rewrite <- gen_pad_cons in *.
    pose proof (result_has_shape_gen_pad (Z.to_nat (eval_Zexpr_Z_total $0 k)
              :: map Z.to_nat (map (eval_Zexpr_Z_total $0) rest))).
    eapply result_has_shape_result_shape_nat in H13,H15.
    rewrite H13 in H15. clear H13.

    assert (length l = Z.to_nat (eval_Zexpr_Z_total $0 dim)) as Heqq.
    { simpl in H11.
      cases (Z.to_nat (eval_Zexpr_Z_total $0 dim)). simpl in *. lia.
      simpl in *. cases l. simpl in *. invert H12. simpl in *.
      invert H12. lia. }
    
    pose proof H7. eapply IHeval_expr in H13; eauto.
    simpl in H13. invs.

    rewrite rev_app_distr.
    repeat rewrite firstn_app.
    rewrite rev_length. rewrite repeat_length. rewrite rev_repeat.
    repeat rewrite skipn_app. rewrite repeat_length.
    rewrite add_sub.
    repeat rewrite firstn_app. repeat rewrite skipn_length.
    rewrite repeat_length.

    split.
    eapply Forall_app. split.
    auto.
    simpl in H15.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 k)). simpl.
    rewrite firstn_nil. eauto.
    eapply forall_firstn. eapply Forall_repeat.
    rewrite gen_pad_filter_until_0. invert H15.
    rewrite <- gen_pad_filter_until_0. auto.
    split.
    eapply Forall_app.
    split. 2: auto.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 k)). simpl.
    rewrite firstn_nil. eauto.
    eapply forall_firstn. eapply Forall_repeat.
    rewrite gen_pad_filter_until_0. invert H15.
    rewrite <- gen_pad_filter_until_0. auto.
    split.
    eapply Forall_app. split.
    eauto.
    eapply has_pad_size_of_relate_pads_gen_pad in H6; eauto.
    simpl in H6.
    remember rev. cases (Z.to_nat (eval_Zexpr_Z_total $0 dim)). lia.
    simpl in H6. repeat rewrite <- @repeat_cons in *.
    subst. rewrite @rev_repeat in *.
    rewrite skipn_repeat. rewrite firstn_repeat. invs. clear H25.
    rewrite skipn_repeat in H23. rewrite firstn_repeat in H23.
    rewrite min_r in H23 by lia.
    rewrite Heqq in *.
    replace (x - Datatypes.S n) with 0 by lia. rewrite sub_0_r.
    replace (l1 - (Datatypes.S n - x)) with 0 by lia. rewrite min_0_r.
    econstructor.
    rewrite Forall_app. rewrite skipn_repeat. rewrite firstn_repeat.
    replace (Z.to_nat (eval_Zexpr_Z_total $0 k) -
               (y + Z.to_nat (eval_Zexpr_Z_total $0 k))) with 0 by lia.
    rewrite min_0_l. split. econstructor. rewrite sub_0_r. eauto.
  - (* PADL *)
    invert Hsize.
    invert Hpad.
    { simpl in Hconst. invs. eq_size_of. invert H5. invert H6.
      pose proof H2 as Hh.
      eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H2;
        eauto.
      simpl in H2. rewrite H13 in H2. simpl in H2.
      invert H2. rewrite app_nil_r in *.
      simpl gen_pad_list in *.
      rewrite <- gen_pad_cons in *.
      pose proof (result_has_shape_gen_pad (Z.to_nat kz :: map Z.to_nat sz)).
      eapply result_has_shape_result_shape_nat in Hsh,H2.
      rewrite Hsh in H2. clear Hsh.

      pose proof H1 as Hsize.
      eapply constant_nonneg_bounds_size_of_no_vars in Hsize; eauto.
      invert Hsize.
      eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H10.
      eq_eval_Zlist.
      eapply eval_Zexpr_Z_eval_Zexpr in H.
      eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
        with (v:=$0) in H; eauto. invert H.
      repeat rewrite <- map_cons.

      eapply relate_pads_filter_until_0.
      eapply result_has_shape_filter_until_0.
      rewrite H2.
      erewrite <- result_has_shape_filter_until_0.
      repeat rewrite map_cons. eapply result_has_shape_gen_pad.
      rewrite H2.
      repeat rewrite <- map_cons.
      eapply relate_pads_filter_until_0.
      eapply result_has_shape_gen_pad.
      eapply relate_pads_gen_pad_id. }
    
    subst. invert Hconst. eq_size_of. invert H8. invert H10.
    assert (eval_Zexpr_Z_total $0 k = kz)%Z.
    { invs.
      eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
        with (v:=$0) in H7. invert H7.
      eapply eval_Zexpr_Z_eval_Zexpr in H. eapply H5 in H. invert H.
      auto. }
    subst.
    cases rsh. invert Hsh.
    
    pose proof H4.
    eapply constant_nonneg_bounds_size_of_eval_expr_result_has_shape in H4.
    2: eauto.
    2: eauto.
    pose proof Hsh.
    pose proof Hsh.
    eapply result_has_shape_app_l in H8.
    eapply result_has_shape_app_r in H10.
    2: { reflexivity. }
    2: { simpl. rewrite repeat_length. reflexivity. }
    repeat rewrite map_cons in *.
    simpl in H10.
    simpl.
    pose proof H10.
    eapply result_has_shape_length in H11.
    rewrite repeat_length in H11.
    pose proof H7.
    eapply constant_nonneg_bounds_size_of_no_vars in H12.
    2: { eauto. }
    eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H12.
    invert H12.
    eq_eval_Z. eq_eval_Zlist.
    pose proof H4. pose proof H8.
    eapply result_has_shape_result_shape_nat in H12, H13.
    rewrite H13 in H12. clear H13.
    pose proof Hsh. eapply result_has_shape_length in H13.
    rewrite app_length in *. simpl length in *. rewrite repeat_length in *.
    subst.
    rewrite add_sub in *.
    rewrite minus_plus in *.
    pose proof H10.
    rewrite <- gen_pad_cons in *.
    pose proof (result_has_shape_gen_pad (Z.to_nat (eval_Zexpr_Z_total $0 k)
              :: map Z.to_nat (map (eval_Zexpr_Z_total $0) rest))).
    eapply result_has_shape_result_shape_nat in H13,H15.
    rewrite H13 in H15. clear H13.

    assert (length l = Z.to_nat (eval_Zexpr_Z_total $0 dim)) as Heqq.
    { simpl in H12.
      cases (Z.to_nat (eval_Zexpr_Z_total $0 dim)). simpl in *. lia.
      simpl in *. cases l. simpl in *. invert H12. simpl in *.
      invert H12. lia. }
    
    pose proof H6. eapply IHeval_expr in H13; eauto.
    simpl in H13. invs.

    repeat rewrite firstn_app. repeat rewrite rev_app_distr.
    repeat rewrite firstn_app. rewrite rev_repeat. rewrite rev_length.
    repeat rewrite skipn_app. repeat repeat rewrite firstn_app.
    repeat rewrite rev_length. repeat rewrite skipn_length.
    rewrite repeat_length.
    repeat rewrite add_sub. rewrite rev_length.
    replace (Z.to_nat (eval_Zexpr_Z_total $0 k) -
               (x + Z.to_nat (eval_Zexpr_Z_total $0 k))) with 0 by lia.
    rewrite sub_0_r.

    split.
    rewrite firstn_all2.
    2: { rewrite repeat_length. lia. }
    eapply Forall_app. split.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 k)). econstructor.
    eapply Forall_repeat. invert H15.
    rewrite gen_pad_filter_until_0. rewrite <- H23.
    rewrite <- gen_pad_filter_until_0. auto.
    eauto.

    split. 
    eapply Forall_app. split. eauto.
    eapply forall_firstn.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 k)). econstructor.
    eapply Forall_repeat. invert H15.
    rewrite gen_pad_filter_until_0. rewrite <- H23.
    rewrite <- gen_pad_filter_until_0. auto.

    split.
    rewrite skipn_all2.
    2: { rewrite repeat_length. lia. }
    rewrite firstn_nil. simpl. eauto.

    eapply Forall_app.
    split. eauto.
    rewrite skipn_repeat. rewrite firstn_repeat.
    cases (Z.to_nat (eval_Zexpr_Z_total $0 k)). econstructor.
    replace (y - Datatypes.length l) with 0 by lia. rewrite sub_0_r.
    replace (r - (Datatypes.length l - y)) with 0 by lia.
    rewrite min_0_r. econstructor.
  - (* SCALAR *)
    invert Hconst. invert Hpad.
    + invert Hsh. simpl. reflexivity.
Qed.
