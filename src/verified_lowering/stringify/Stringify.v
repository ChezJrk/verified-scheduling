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

From ATL Require Import Div.
From Codegen Require Import IdentParsing NatToString IntToString.
From Lower Require Import ATLDeep Sexpr Zexpr Bexpr.
Require Import Ltac2.Ltac2.
Require Import Ltac2.Option.

Open Scope string_scope.

Set Default Proof Mode "Classic".

Definition HEADERS :=
  ["#include <stdlib.h>";
  "#include <stdio.h>";
  "#include <time.h>";
  "#include <assert.h>"].

Definition scalar := "float".
Definition align := "4".

Ltac to_str :=
  ltac2:(n |- let n := Option.get (Ltac1.to_constr n) in
              let str :=
                  match Constr.Unsafe.kind n with
                  | Constr.Unsafe.Var v => IdentParsing.coq_string_of_ident v 
                  | _ => constr:("")
                  end
              in
              exact $str).

Ltac stringify_nat n :=
  match n with
  | (?x + ?y)%nat =>
      let xstr := stringify_nat x in 
      let ystr := stringify_nat y in
      constr:((xstr++" + "++ystr)%string)
  | (?x - ?y)%nat =>
      let xstr := stringify_nat x in 
      let ystr := stringify_nat y in
      constr:((xstr++" - "++ystr)%string)
  | (?x * ?y)%nat =>
      let xstr := stringify_nat x in 
      let ystr := stringify_nat y in
      constr:((xstr++" * "++ystr)%string)
  | (?x //n ?y)%nat =>
      let xstr := stringify_nat x in 
      let ystr := stringify_nat y in
      constr:("((" ++ xstr ++ ") + (" ++ ystr ++ ") - 1 ) / (" ++ ystr ++")")
  | Z.to_nat ?z => stringify_int z
  | _ => let _ := match goal with _ => is_var n end in
         constr:(ltac:(to_str n))
  | _ => constr:(nat_to_string n)
  end with stringify_int z :=
    match z with
    | (?x + ?y)%Z =>
        let xstr := stringify_int x in
        let ystr := stringify_int y in
        constr:(xstr ++ " + " ++ ystr)
    | (?x * ?y)%Z =>
        let xstr := stringify_int x in
        let ystr := stringify_int y in
        constr:("("++xstr ++ ") * (" ++ ystr ++")")
    | (?x - ?y)%Z =>
        let xstr := stringify_int x in
        let ystr := stringify_int y in
        constr:(xstr ++ " - (" ++ ystr ++ ")")
    | (?x / ?y)%Z =>
        let xstr := stringify_int x in
        let ystr := stringify_int y in
        constr:("((" ++ xstr ++ ") / (" ++ ystr ++"))")
    | Z.opp ?x =>
        let xstr :=
          match x with
          | _ => let _ := match goal with _ => is_var x end in
                 constr:(ltac:(to_str x))
          | _ =>
              constr:(int_to_string x)
          end in
        constr:(("- "++xstr)%string)
    | Z.of_nat ?n => stringify_nat n
    | _ => let _ := match goal with _ => is_var z end in
           constr:(ltac:(to_str z))
    | _ => constr:(int_to_string z)
    end.

Ltac stringify_Zexpr z :=
  match z with
  | ZPlus ?x ?y =>
    let xstr := stringify_Zexpr x in
    let ystr := stringify_Zexpr y in
    constr:(xstr ++ " + " ++ ystr)
  | ZMinus ?x ?y =>
    let xstr := stringify_Zexpr x in
    let ystr := stringify_Zexpr y in
    constr:(xstr ++ " - (" ++ ystr ++ ")")
  | ZTimes ?x ?y =>
    let xstr := stringify_Zexpr x in
    let ystr := stringify_Zexpr y in
    constr:("("++xstr ++ ") * (" ++ ystr ++")")
  | ZDivc ?x ?y =>
    let xstr := stringify_Zexpr x in
    let ystr := stringify_Zexpr y in
    constr:("((" ++ xstr ++ ") + (" ++ ystr ++ ") - 1 ) / (" ++ ystr ++")")
  | ZDivf ?x ?y =>
    let xstr := stringify_Zexpr x in
    let ystr := stringify_Zexpr y in
    constr:("((" ++ xstr ++ ") / (" ++ ystr ++"))")
  | (ZMod ?x ?y)%Z =>
    let xstr := stringify_Zexpr x in
    let ystr := stringify_Zexpr y in
    constr:("((" ++ xstr ++ ") % (" ++ ystr ++"))")
  | ZVar ?s => s
  | ZLit ?z => stringify_int z
end.

Ltac stringify_Bexpr p :=
  match p with
  | And ?a ?b =>
    let astr := stringify_Bexpr a in
    let bstr := stringify_Bexpr b in
    constr:(astr ++ " && " ++ bstr)
  | Le ?a ?b %Z =>
    let xstr := stringify_Zexpr a in
    let ystr := stringify_Zexpr b in
    constr:(xstr ++ " <= " ++ ystr)
  | Eq ?x ?y =>
    let xstr := stringify_Zexpr x in
    let ystr := stringify_Zexpr y in
    constr:(xstr ++ " == " ++ ystr)
  | Lt ?x ?y =>
    let xstr := stringify_Zexpr x in
    let ystr := stringify_Zexpr y in
    constr:(xstr ++ " < " ++ ystr)
  end.

Fixpoint flatten_list_Zexpr_helper (l : list (Zexpr * Zexpr))
  : (Zexpr * Zexpr) :=
  match l with
  | [(i,d)] => (i,d)
  | (i,d)::l' =>
      let (i',d') := flatten_list_Zexpr_helper l' in
      (ZPlus (ZTimes i d') i', ZTimes d d')
  | _ => (ZLit 0%Z, ZLit 0%Z)
  end.

Definition flatten_list_Zexpr l := fst (flatten_list_Zexpr_helper l).

Fixpoint swap_tups {X Y} (l : list (X * Y)) : list (Y * X) :=
  match l with
  | (a,b)::l' => (b,a)::(swap_tups l')
  | _ => []
  end.

Ltac stringify_Sstmt s :=
  match s with
  | SVar ?v => v
  | SGet ?v ?idx =>
      let idx := constr:(swap_tups idx) in
      let idx := eval simpl in idx in
      let flat_idx_ := constr:((flatten_list_Zexpr idx)) in
      let flat_idx_ := eval unfold flatten_list_Zexpr in flat_idx_ in
      let flat_idx := eval simpl in flat_idx_ in
      let idxstr := stringify_Zexpr flat_idx in
      constr:((v++"["++idxstr++"]")%string)
  | SMul ?x ?y =>
      let xstr := stringify_Sstmt x in
      let ystr := stringify_Sstmt y in
      constr:((xstr ++ " * (" ++ ystr ++ ")")%string)
  | SAdd ?x ?y =>
      let xstr := stringify_Sstmt x in
      let ystr := stringify_Sstmt y in
      constr:((xstr ++ " + (" ++ ystr ++ ")")%string)
  | SDiv ?x ?y =>
      let xstr := stringify_Sstmt x in
      let ystr := stringify_Sstmt y in
      constr:((xstr ++ " / (" ++ ystr ++ ")")%string)
  | SSub ?x ?y =>
      let xstr := stringify_Sstmt x in
      let ystr := stringify_Sstmt y in
      constr:((xstr ++ " - (" ++ ystr ++ ")")%string)
  | SLit ?r => match r with
               | 0%R => constr:("0")
               | 1%R => constr:("1")
               | 2%R => constr:("2")
               | 3%R => constr:("3")
               end
  end.

Definition stringify_storetype s :=
  match s with
  | Assign => " = "
  | Reduce => " += "
  end.

Ltac stringify_stmt s :=
  match s with
  | Store ?redeq ?v ?idx ?sc =>
      match idx with
      | @nil (Zexpr * Zexpr) =>
          let redstr := constr:((stringify_storetype redeq)) in
          let str := stringify_Sstmt sc in
          constr:([v ++ redstr ++ str ++ ";"])
      | _ =>
          let redstr := constr:((stringify_storetype redeq)) in
          let flat_idx_ := constr:((flatten_list_Zexpr idx)) in
          let flat_idx_ := eval unfold flatten_list_Zexpr in flat_idx_ in
          let flat_idx := eval simpl in flat_idx_ in
          let idxstr := stringify_Zexpr flat_idx in
          let str := stringify_Sstmt sc in
          constr:([v ++ "[" ++ idxstr ++ "]" ++ redstr ++ str ++ ";"])
      end
  | If ?b ?s1 =>
      let bstr := stringify_Bexpr b in
      let sstr := stringify_stmt s1 in
      constr:( ( [("if ("++bstr++") {")%string]
                   ++ sstr
                   ++ ["}"])%list )
  | AllocV ?v ?size =>
      let sizestr := stringify_Zexpr size in
      constr:( ([("float *" ++ v ++ " = calloc("++ sizestr ++", sizeof(float));")%string])%list )
  | AllocS ?v =>
      constr:( ([("{ float " ++ v ++ " = 0;")%string])%list )
  | DeallocS ?v =>
      constr:( (["}"])%list )
  | Free ?v =>
      constr:( ([("free("++v++");")%string])%list )
  | For ?i ?lo ?hi ?body =>
      let lostr := stringify_Zexpr lo in
      let histr := stringify_Zexpr hi in
      let bodystr := stringify_stmt body in
      constr:(([("for (int "++i++" = "++lostr++"; "++i++" < "++histr++"; "
                   ++i++"++) {")%string]
                 ++ bodystr
                 ++ ["}"])%list)
  | Seq ?s1 ?s2 =>
      let str1 := stringify_stmt s1 in
      let str2 := stringify_stmt s2 in
      constr:((str1++str2)%list)
  end.

