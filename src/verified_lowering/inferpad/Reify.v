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
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Reals.Rpower.

Import ListNotations.

Set Warnings "-omega-is-deprecated,-deprecated".

From Codegen Require Import IdentParsing NatToString IntToString Normalize CodeGen.
From Lower Require Import ATLDeep Sexpr Zexpr Bexpr.
From ATL Require Import ATL Common CommonTactics Div.

Open Scope string_scope.

Set Default Proof Mode "Classic".

Definition is_lit (z :Z) := True.

Ltac mark_lit :=
  repeat
    match goal with
    | z : Z |- _ =>
        assert (is_lit z) by (unfold is_lit; auto);
        generalize dependent z
    end; intros.

Ltac reify_Z z :=
  match z with
  | (?x * ?y)%Z =>
      let lx := reify_Z x in
      let ly := reify_Z y in
      constr:(ZTimes lx ly)
  | (?x + ?y)%Z =>
      let lx := reify_Z x in
      let ly := reify_Z y in
      constr:(ZPlus lx ly)
  | (?x - ?y)%Z =>
      let lx := reify_Z x in
      let ly := reify_Z y in
      constr:(ZMinus lx ly)
  | (?x / ?y)%Z =>
      let lx := reify_Z x in
      let ly := reify_Z y in
      constr:(ZDivf lx ly)               
  | (?x // ?y)%Z =>
      let lx := reify_Z x in
      let ly := reify_Z y in
      constr:(ZDivc lx ly)
  | (?x mod ?y)%Z =>
      let lx := reify_Z x in
      let ly := reify_Z y in
      constr:(ZMod lx ly)
  | Z.of_nat ?x =>
      constr:(ZLit z)
  | _ => let _ := match goal with _ => is_var z end in
         match goal with
         | H : is_lit z |- _ => constr:(ZLit z)
         | _ => constr:(ZVar ltac:(to_str z))
         end
  | _ => constr:(ZLit z)
  end.

(*
Goal forall i j, (i + j = 0)%Z.
  intros. mark_lit.
  let s := reify_Z (i / 0 + j // i * 1 - (i mod 1))%Z in
  idtac s.
 *)

Ltac reify_get g :=
  lazymatch g with
  | get ?v ?i =>
      let tup := reify_get v in
      let iz := reify_Z i in
      constr:(match tup with (var,idx) => (var,(idx++[iz])%list)end)
  | _ => let _ := match goal with _ => is_var g end in
         constr:((ltac:(to_str g), @nil Zexpr)) 
  end.
(*
Goal forall (i j : Z) (s : string) (v : list (list R)), True.
  intros.
  let s := reify_get constr:(v _[i;j]) in
  idtac s.
 *)  

Ltac reify_R s :=
  lazymatch s with
  | 1%R => constr:(Lit 1%R)
  | 0%R => constr:(Lit 0%R)
  | (?a * ?b)%R =>
      let la := reify_R a in
      let lb := reify_R b in
      constr:(Mul la lb)
  | (?a + ?b)%R =>
      let la := reify_R a in
      let lb := reify_R b in
      constr:(Add la lb)
  | (?a - ?b)%R =>
      let la := reify_R a in
      let lb := reify_R b in
      constr:(Sub la lb)
  | (?a / ?b)%R =>
      let la := reify_R a in
      let lb := reify_R b in
      constr:(Div la lb)
  | _ =>
      let tup := reify_get s in
      constr:(match tup with
              | (var,[]) => Var var
              | (var,idx) => Get var idx
              end)
  end.

Ltac reify_bool b :=
  lazymatch b with
  | ?a && ?b =>
      let ab := reify_bool a in
      let bb := reify_bool b in
      constr:(And ab bb)
  | (?a <? ?b)%Z =>
      let ab := reify_Z a in
      let bb := reify_Z b in
      constr:(Lt ab bb)
  | (?a <=? ?b)%Z =>
      let ab := reify_Z a in
      let bb := reify_Z b in
      constr:(Le ab bb)
  | (?a =? ?b)%Z =>
      let ab := reify_Z a in
      let bb := reify_Z b in
      constr:(Eq ab bb)
  end.
(*
Goal forall (i j : Z), True.
Proof.
  intros.
  let s := reify_bool constr:((i <? j)%Z && (j <=? i)%Z) in
  idtac s.
  *)

Ltac reify prog :=
  lazymatch prog with
  | |[ ?p ]| ?e =>
               let pr := reify_bool p in
               let body := reify e in
               constr:(Guard pr body)
  | GEN [ ii < ?nn ] @?f ii =>
      let _ := match goal with _ => assert Z by exact 0%Z end in
      let i' := match goal with H : Z |- _ => H end in
      let i := constr:(ltac:(to_str i')) in
      let rn := reify_Z nn in
    
      let body' := constr:(f i') in
      let body := eval lazy beta in body' in
      let rbody := reify body in
        
      constr:(Gen i (|0|)%z rn rbody)
  | GEN [ ?mm <= ii < ?nn ] @?f ii =>
      let _ := match goal with _ => assert Z by exact 0%Z end in
      let i' := match goal with H : Z |- _ => H end in
      let i := constr:(ltac:(to_str i')) in
      let rn := reify_Z nn in
      let rm := reify_Z mm in
      
      let body' := constr:(f i') in
      let body := eval lazy beta in body' in
      let rbody := reify body in
        
      constr:(Gen i rm rn rbody)
  | SUM [ ii < ?nn ] @?f ii =>
      let _ := match goal with _ => assert Z by exact 0%Z end in
      let i' := match goal with H : Z |- _ => H end in
      let i := constr:(ltac:(to_str i')) in
      let rn := reify_Z nn in
    
      let body' := constr:(f i') in
      let body := eval lazy beta in body' in
      let rbody := reify body in
        
      constr:(Sum i (|0|)%z rn rbody)
  | let_binding ?e1 ?e2 =>
    let e1t := type of e1 in

    let _ := match goal with _ =>
                             let tempH := fresh "tempH" in
                             (assert (exists temp, temp = e1) as tempH
                                 by eauto; destruct tempH)
             end in    
    let x := match goal with H : e1t |- _ => H end in
    let xstr := constr:(ltac:(to_str x)) in
    let re1 := reify e1 in

    let body' := constr:(e2 x) in
    let body := eval simpl in body' in
    let re2 := reify body in
      
    constr:(Lbind xstr re1 re2)
  | transpose ?e =>
      let re := reify e in
      constr:(Transpose re)
  | tile ?e ?k =>
      let re := reify e in
      let rk := reify_Z (Z.of_nat k) in
      constr:(Split rk re)
  | Common.flatten ?e =>
      let re := reify e in
      constr:(Flatten re)
  | truncr ?k ?e =>
      let rk := reify_Z constr:(Z.of_nat k) in
      let re := reify e in
      constr:(ATLDeep.Truncr rk re)
  | truncl ?k ?e =>
      let rk := reify_Z constr:(Z.of_nat k) in
      let re := reify e in
      constr:(Truncl rk re)
  | Truncr ?k ?e =>
      let rk := reify_Z constr:(k) in
      let re := reify e in
      constr:(ATLDeep.Truncr rk re)
  | truncl ?k ?e =>
      let rk := reify_Z constr:(Z.of_nat k) in
      let re := reify e in
      constr:(Truncl rk re)
  | pad_r ?k ?e =>
      let rk := reify_Z constr:(Z.of_nat k) in
      let re := reify e in
      constr:(Padr rk re)
  | pad_l ?k ?e =>
      let rk := reify_Z constr:(Z.of_nat k) in
      let re := reify e in
      constr:(Padl rk re)
  | ?a <++> ?b =>
      let ra := reify a in
      let rb := reify b in
      constr:(Concat ra rb)
  | _ => let s := reify_R prog in
         constr:(Scalar s)
  end.

Ltac R :=
  let _ := match goal with _ => intros;
                                try autounfold with examples;
                                mark_lit
           end in
  let _ := match goal with _ =>
                           normalize end in

  let prog := match goal with |- ?prog = _ => prog end in
  
  let ast := reify prog in
  let ast := eval simpl in ast in
  ast.
(*
Goal forall r p,
    tlet x := (|[ p ]| tlet x := r*r in (tlet x1 := r+x in x1 + 1))%R in (x+1)%R = 0%R.
Proof.
  intros.
  normalize.

  let prog := match goal with |- ?p = _ => p end in
  match prog with
    | let_binding ?e1 ?e2 =>
    let e1t := type of e1 in

    let _ := match goal with _ =>
                             let tempH := fresh "tempH" in
                             (assert (exists temp, temp = e1) as tempH
                                 by eauto; destruct tempH)
             end in

    let x := match goal with H : e1t |- _ => H end in
    let xstr := constr:(ltac:(to_str x)) in
    
    let body' := constr:(e2 x) in
    let body := eval simpl in body' in
      let re2 := reify body in
      idtac
  end      .
*)
