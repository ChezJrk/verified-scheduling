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

Import ListNotations.

Require Import Ltac2.Ltac2.
Require Import Ltac2.Option.

Set Warnings "-omega-is-deprecated,-deprecated".

From ATL Require Import ATL Common CommonTactics Div.
From Codegen Require Import IdentParsing NatToString IntToString Normalize.

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

Ltac stringify_int z :=
  match z with
  | (- ?x)%Z =>
    let xstr := stringify_int x in
    constr:("(-("++xstr++"))")
  | (?x + ?y)%Z =>
    let xstr := stringify_int x in
    let ystr := stringify_int y in
    constr:(xstr ++ " + " ++ ystr)
  | (?x - ?y)%Z =>
    let xstr := stringify_int x in
    let ystr := stringify_int y in
    constr:(xstr ++ " - (" ++ ystr ++ ")")
  | (?x * ?y)%Z =>
    let xstr := stringify_int x in
    let ystr := stringify_int y in
    constr:("("++xstr ++ ") * (" ++ ystr ++")")
  | ?x // ?y =>
    let xstr := stringify_int x in
    let ystr := stringify_int y in
    constr:("((" ++ xstr ++ ") + (" ++ ystr ++ ") - 1 ) / (" ++ ystr ++")")
  | (?x / ?y)%Z =>
    let xstr := stringify_int x in
    let ystr := stringify_int y in
    constr:("((" ++ xstr ++ ") / (" ++ ystr ++"))")
  | (Zmod ?x ?y)%Z =>
    let xstr := stringify_int x in
    let ystr := stringify_int y in
    constr:("((" ++ xstr ++ ") % (" ++ ystr ++"))")
  | (Z.min ?x ?y)%Z =>
    let xstr := stringify_int x in
    let ystr := stringify_int y in
    constr:("((("++xstr++") < ("++ystr++")) ? ("++xstr++") : ("++ystr++"))")
  | (Z.max ?x ?y)%Z =>
    let xstr := stringify_int x in
    let ystr := stringify_int y in
    constr:("((("++xstr++") < ("++ystr++")) ? ("++ystr++") : ("++xstr++"))")
  | Z.of_nat ?n =>
    stringify_nat n
  | _ => let _ := match goal with _ => is_var z end in
         constr:(ltac:(to_str z))
  | _ =>
    constr:(int_to_string z)                  
  end
with stringify_nat n :=
    match n with
    | S ?nn => let s := stringify_nat nn in
               constr:("1 + "++s)
  | context[Pos.to_nat ?nn] =>
    let _ := match goal with _ =>
                             let stringifyme := fresh "stringifying" in
                             evar (newnat : nat);
                             assert (?newnat = Pos.to_nat nn)%nat as
                                 stringifyme by (cbv; reflexivity);
                             evar (rednat : nat);
                             assert (?rednat = n)%nat as newrednat by
                                   (symmetry; rewrite <- stringifyme; reflexivity)
  end in
      let cbved := match goal with
                   | H : (?evaled = _)%nat |- _ =>
                     evaled
                   end in
      stringify_nat cbved      
  | ?a //n ?b =>
    let astr := stringify_nat a in
    let bstr := stringify_nat b in
    constr:("(("++astr++" + "++bstr++" - 1) / "++bstr++")")
  | ?a * ?b =>
    let astr := stringify_nat a in
    let bstr := stringify_nat b in
    constr:("("++astr++" * "++bstr++")")
  | ?a + ?b =>
    let astr := stringify_nat a in
    let bstr := stringify_nat b in
    constr:("("++astr++" + "++bstr++")")
  | ?a - ?b =>
    let astr := stringify_nat a in
    let bstr := stringify_nat b in
    constr:("("++astr++" - ("++bstr++"))")                          
  | max ?a ?b =>
    let astr := stringify_nat a in
    let bstr := stringify_nat b in
    constr:("MAX("++astr++","++bstr++")")
  | Z.to_nat ?z => stringify_int z
  | _ => let _ := match goal with _ => is_var n end in
         constr:(ltac:(to_str n))
  | _ => (* let _ := match goal with _ => idtac n end in *)
    constr:(nat_to_string n)
  end.

Ltac stringify_bool p :=
  match p with
  | true => constr:("1")
  | false => constr:("0")
  | (?a && ?b)%bool =>
    let astr := stringify_bool a in
    let bstr := stringify_bool b in
    constr:(astr ++ " && " ++ bstr)
  | (?x <=? ?y)%Z =>
    let xstr := stringify_int x in
    let ystr := stringify_int y in
    constr:(xstr ++ " <= " ++ ystr)
  | (?x =? ?y)%Z =>
    let xstr := stringify_int x in
    let ystr := stringify_int y in
    constr:(xstr ++ " == " ++ ystr)
  | (?x <? ?y)%Z =>
    let xstr := stringify_int x in
    let ystr := stringify_int y in
    constr:(xstr ++ " < " ++ ystr)
  | _ => constr:(ltac:(to_str p))
  end.

Ltac fresh_str n :=
  let s := constr:("tmp" ++ nat_to_string n) in
  let ret := eval cbv in s in
      ret. 

Ltac fst quad :=
  let res' := constr:(fst (fst (fst quad))) in
  let res := eval simpl in res' in
      res.

Ltac snd quad :=
  let res' := constr:(snd (fst (fst quad))) in
  let res := eval simpl in res' in
      res.

Ltac thd quad :=
  let res' := constr:(snd (fst quad)) in
  let res := eval simpl in res' in
      res.

Ltac frt quad :=
  let res' := constr:(snd quad) in
  let res := eval simpl in res' in
      res.

Ltac type_to_str t :=
  lazymatch t with
  | R => scalar
  | Z => constr:("int")
  | nat => constr:("int")                  
  | list ?t' => constr:(scalar++"*")
  | _ => constr:("void")
  end.

Ltac shape_to_str t :=
  lazymatch t with
  | tt => scalar
  | (_,?t') => let tstr := shape_to_str t' in
                constr:(tstr++"*")
  | _ => constr:("void")
  end.

Ltac alloc_dim s :=
  lazymatch s with
  | tt => constr:("")
  | (?n,tt) =>
    let nstr := stringify_nat n in
    constr:("("++nstr++")")                   
  | (?n,?s') =>
    let nstr := stringify_nat n in
    let rest:= alloc_dim s' in
    constr:("("++nstr++") * "++rest)
  | _ => constr:("")
  end.
(*
Ltac get_shape_consistency e :=
  let t := type of e in
  let eshape := fresh "eshape" in  
  let _ := match goal with _ =>
                           evar (eshape : @shape t _) end in
  let _ := match goal with _ =>
                           (assert (consistent e ?eshape) by
                               repeat
                                 (progress
                                    (try unfold let_binding;
                                     subst;
                                     consistent_shape;
                                     try reflexivity;
                                 try eauto with crunch))) || idtac e end in
  let s := match goal with H : consistent e ?s |- _ => s end in
  let s' := eval lazy beta in s in
      s'.
*)
Ltac get_shape_rec prog :=
  lazymatch prog with
  | 1%R => constr:(tt)
  | 0%R => constr:(tt)
  | ?e _[_] =>
    let sh' := get_shape_rec e in
    let sh := match sh' with
              | (_,?sh) => sh
              end in
    sh
  | (?a + ?b)%R => constr:(tt)
  | |[ _ ]| ?e =>
     get_shape_rec e
  | GEN [ ii < ?nn ] @?f ii =>
      let _ := match goal with _ => assert Z by exact 0%Z end in
      let i' := match goal with H : Z |- _ => H end in
      let i := constr:(ltac:(to_str i')) in
    
      let body' := constr:(f i') in
      let body := eval lazy beta in body' in
      let n := match nn with
             | Z.of_nat ?n => n
             | _ => constr:(Z.to_nat nn)
             end in
      let innersh := get_shape_rec body in
      constr:((n, innersh))
  | GEN [ ?mm <= ii < ?nn ] @?f ii =>
    let _ := match goal with _ => assert Z by exact 0%Z end in
    let i' := match goal with H : Z |- _ => H end in
    let i := constr:(ltac:(to_str i')) in

    let body' := constr:(f i') in
    let body := eval lazy beta in body' in
    let n := match nn with
             | Z.of_nat ?n => n
             | _ => constr:(Z.to_nat nn)
             end in
    let m := match mm with
             | Z.of_nat ?m => m
             | _ => constr:(Z.to_nat mm)
             end in    
    let innersh := get_shape_rec body in
    constr:((n-m,innersh))
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
    get_shape_rec body
  | SUM [ ii < ?nn ] @?f ii =>
    let _ := match goal with _ => assert Z by exact 0%Z end in
    let i' := match goal with H : Z |- _ => H end in
    let i := constr:(ltac:(to_str i')) in
    
    let body' := constr:(f i') in
    let body := eval simpl in body' in
    get_shape_rec body
  | transpose ?e =>
    let sh' := get_shape_rec e in
    let sh := match sh' with
              | (?n,(?m,?s)) => constr:((m,(n,s)))
              end in
    sh
  | flatten_trunc ?n ?e =>
    let sh' := get_shape_rec e in
    let sh := match sh' with
              | (_,(_,?s)) => constr:((n,s))
              end in
    sh
  | flatten ?e =>
    let sh' := get_shape_rec e in
    let sh := match sh' with
              | (?n,(?m,?s)) => constr:((n*m,s))
              end in
    sh
  | trunc_r ?k ?e =>
    let sh' := get_shape_rec e in
    let sh := match sh' with
              | (_,?s) => constr:((k,s))
              end in
    sh    
  | Truncr ?k ?e =>
    let sh' := get_shape_rec e in
    let sh := match sh' with
              | (?m,?s) => constr:((m- Z.to_nat k,s))
              end in
    sh    
  | truncr ?k ?e =>
    let sh' := get_shape_rec e in
    let sh := match sh' with
              | (?m,?s) => constr:((m- k,s))
              end in
    sh    
  | trunc_l ?k ?e =>
    let sh' := get_shape_rec e in
    let sh := match sh' with
              | (_,?s) => constr:((k,s))
              end in
    sh    
  | pad_r ?k ?e =>
    let sh' := get_shape_rec e in
    let sh := match sh' with
              | (?m,?s) => constr:((m+k,s))
              end in
    sh        
  | pad_l ?k ?e =>
    let sh' := get_shape_rec e in
    let sh := match sh' with
              | (?m,?s) => constr:((m+k,s))
              end in
    sh        
  | ?a <++> ?b =>
    let ash := get_shape_rec a in
    let bsh := get_shape_rec b in
    let sh := match ash with
              | (?n,?s) => match bsh with
                           | (?m,_) => constr:((n+m,s))
                           end
              end in
    sh
  | ?etc =>
    (* SHOULD BE A VARIABLE *)
    match type of etc with
    | R => tt
    | _ => 
      match goal with
      | H : consistent etc ?s |- _ => s
      | H : etc = ?e |- _ => get_shape_rec e
      end
    end
  end.

Ltac get_shape e := get_shape_rec e.

(* Returns a tuple of the collective stride access as a string and
   the innermost expression that is being accessed as a constr *)
Ltac flatten_get e :=
  lazymatch e with
  | ?v _[?i] =>
    let s := get_shape v in
    let istr := stringify_int i in
    let innertup := flatten_get v in
    let inner := constr:(fst innertup) in
    let retv := constr:(snd innertup) in                   
    let acc := match s with
               | (_,tt) =>
                 istr
               | (?n,(?m,?s)) =>
                 let mstr := alloc_dim constr:((m,s)) in
                 constr:("(("++mstr++") * ("++istr++")) + ")
               end
    in constr:((inner++acc, retv))
  | _ => constr:(("",e))
  end.

Ltac alloc_size_shape s :=
  lazymatch s with
  | tt => constr:("sizeof ("++scalar++")")
  | (?n,?s') =>
    let nums := alloc_dim s in
    constr:(nums++" * sizeof ("++scalar++")")
  | _ => constr:("sizeof ("++scalar++")")
  end.

Ltac alloc_size e :=
  let s := get_shape e in
  alloc_size_shape s.

Ltac fst2 tup :=
  let ret' := constr:(fst tup) in
  let ret := eval simpl in ret' in
      ret.

Ltac snd2 tup :=
  let ret' := constr:(snd tup) in
  let ret := eval simpl in ret' in
      ret.

Ltac fst3 tupp :=
  let ret' := constr:(fst (fst tupp)) in
  let ret := eval simpl in ret' in
      ret.

Ltac snd3 tupp :=
  let ret' := constr:(snd (fst tupp)) in
  let ret := eval simpl in ret' in
      ret.

Ltac thd3 tupp :=
  let ret' := constr:(snd tupp) in
  let ret := eval simpl in ret' in
      ret.

Ltac fst5 tup :=
  let ret' := constr:(fst (fst (fst (fst tup)))) in
  let ret := eval simpl in ret' in
      ret.

Ltac snd5 tup :=
  let ret' := constr:(snd (fst (fst (fst tup)))) in
  let ret := eval simpl in ret' in
      ret.

Ltac thd5 tup :=
  let ret' := constr:(snd (fst (fst tup))) in
  let ret := eval simpl in ret' in
      ret.

Ltac frt5 tup :=
  let ret' := constr:(snd (fst tup)) in
  let ret := eval simpl in ret' in
      ret.

Ltac fth5 tup :=
  let ret' := constr:(snd tup) in
  let ret := eval simpl in ret' in
      ret.

Ltac wrap_gets sh :=
  match sh with
  | tt => constr:((@nil string,"",@nil string))
  | (?nn,tt) =>
    let _ := match goal with _ => assert Z by exact 0%Z end in
    let i' := match goal with H : Z |- _ => H end in
    let i := constr:(ltac:(to_str i')) in
    let n := stringify_nat nn in

    constr:((["for (int "++i++" = 0; "++i++" < "++n++"; "++i++"++) {"]
             , " + "++i
             , ["}"]))
  | (?nn,(?mm,?s)) =>
    let _ := match goal with _ => assert Z by exact 0%Z end in
    let i' := match goal with H : Z |- _ => H end in
    let i := constr:(ltac:(to_str i')) in
    let n := stringify_nat nn in
    let m := alloc_dim constr:((mm,s)) in

    let inner := wrap_gets constr:((mm,s)) in
    let heads := fst3 inner in
    let accum := snd3 inner in
    let tails := thd3 inner in

    constr:((("for (int "++i++" = 0; "++i++" < "++n++"; "++i++"++) {")::
               heads
             , " + ("++m++" * "++i++")"++accum
             , "}"::tails))
  end.

Inductive indty :=
| TUP : string -> string -> indty
| LIST : string -> list indty -> indty.

Definition transpose_indty (acc : indty) :=
  match acc with
  | LIST total l =>
    match l with
    | a::b::xs => LIST total (b::a::xs)
    | _ => acc
    end
  | _ => acc
  end.

Definition get_total (acc : indty) :=
  match acc with
  | LIST total _ => total
  | TUP _ d => d
  end.

Fixpoint get_total_from_list (accs : list indty) :=
  match accs with
  | nil => ""
  | x::nil => get_total x
  | x::xs => let xtot := get_total x in
             let resttot := get_total_from_list xs in
             xtot++" * "++resttot
  end.

Definition flatten_indty (acc : indty) :=
  match acc with
  | LIST total l =>
    match l with
    | a::b::xs =>
      match a,b with
      | TUP va da,TUP vb db =>
        LIST total ((TUP ("("++va++") * ("++db++") + "++vb)
                         ("("++da++") * ("++db++")") )::xs)  
      | _,_ => acc
      end
    | _ => acc
    end
  | _ => acc
  end.

Definition flatten_trunc_indty n (acc : indty) :=
  match acc with
  | LIST total l =>
    match l with
    | a::b::xs =>
      match a,b with
      | TUP va da,TUP vb db =>
        let newl := ((TUP ("("++va++") * ("++db++") + "++vb)
                          n )::xs) in
        let newtot := get_total_from_list newl in
        LIST newtot newl
      | _,_ => acc
      end
    | _ => acc
    end
  | _ => acc
  end.

Fixpoint pad_indty_dim acc kstr :=
  (* TODO: revisit logic for some of the list cases *)
  match acc with
  | TUP v d =>
    TUP v ("("++d++" + "++kstr++")")
  | LIST total l =>
    match l with
    | @nil _ => (* Should not happen *) acc
    | x::xs => LIST total ((pad_indty_dim x kstr)::xs)
    end
  end.

Ltac pad_indty_helper acc kstr :=
  match acc with
  | TUP ?v ?d =>
    constr:(TUP ("("++v++" + "++kstr++")") d)
  | LIST ?total ?l =>
    let lrev := constr:(List.rev l) in
    match lrev with
    | @nil _ => constr:(LIST total l)
    | ?x::?xs =>
      let replaced := pad_indty_helper x kstr in
      let replacedrev := constr:(replaced::xs) in
      constr:(LIST total (List.rev replacedrev))
    end
  end.

Fixpoint pad_indty_helper acc kstr n {struct n} :=
  match n with
  | O => acc
  | S n =>
    match acc with
    | TUP v d =>
      (TUP ("("++v++" + "++kstr++")") d)
    | LIST total l =>
      let lrev := (List.rev l) in
      match lrev with
      | @nil _ => (LIST total l)
      | x::xs =>
        let replaced := pad_indty_helper x kstr n in
        let replacedrev := (replaced::xs) in
        (LIST total (List.rev replacedrev))
      end
    end
  end.

Definition pad_indty acc kstr :=
  (* TODO: revisit logic for some of the list cases *)
  match acc with
  | TUP v d =>
    (TUP ("("++v++" + "++kstr++")") d)
  | LIST total l =>
    match l with
    | @nil _ => (* Should not happen *) acc
    | x::xs => let padded := pad_indty_helper x kstr 100 in
               (LIST total (padded::xs))
    end
  end.

Fixpoint trunc_indty acc kstr :=
  match acc with
  | TUP v d =>
      TUP ("("++v++" - ("++d++" - ("++kstr++")))") d 
  | LIST total l =>
    match l with
    | @nil _ => (* Should not happen *) acc
    | x::xs => LIST total ((trunc_indty x kstr)::xs)
    end
  end.

(* We gotta use Ltac because termination isn't obvious enough for Gallina *)
Ltac stringify_indty acc :=
  lazymatch acc with
  | TUP ?v ?d => v
  | LIST ?total ?l =>
    lazymatch l with
    | nil => constr:("")
    | ?x::nil => stringify_indty x
    | ?x::?xs =>
      let stride := constr:(get_total_from_list xs) in
      let xstr := stringify_indty x in
      let inner := stringify_indty constr:(LIST stride xs) in
      constr:("("++stride++") * ("++xstr++") + "++inner)
    end
  end.

Fixpoint swap_dim_indty newd acc :=
  match acc with
  | TUP v d => (TUP v newd)
  | LIST _ l =>
    match l with
    | nil => acc (* Shouldn't happen *)
    | acc'::xs =>
      let newacc := swap_dim_indty newd acc' in
      let l' := (newacc::xs) in
      let total := (get_total_from_list l') in
      (LIST total l')
    end
  end.

Ltac access_indty_expr acc :=
  let acc_eval := eval simpl in acc in
  match acc_eval with
  | LIST _ (@nil indty) => constr:("")
  | _ =>
    let accstr := stringify_indty acc_eval in
    constr:("["++accstr++"]")
  end.  

Ltac assign_indty src acc expr :=
  let accapp := constr:(acc (LIST "1" (@nil indty))) in
  let accexpr := access_indty_expr accapp in
  constr:(src++accexpr++" = "++expr++";").

Definition indty_cons x xs :=
  let xtot := get_total x in
  match xs with
  | TUP _ d => LIST (xtot++" * "++d) (x::xs::(@nil indty))
  | LIST total l => LIST (xtot++" * "++total) (x::l)
  end.

Ltac tensoradd aref bref sh src srcacc sumaccl sumaccr c :=
  lazymatch sh with
  | tt =>
    let sumacclapp := constr:(sumaccl (LIST "1" (@nil indty))) in
    let sumaccrapp := constr:(sumaccr (LIST "1" (@nil indty))) in
    let accl := access_indty_expr sumacclapp in
    let accr := access_indty_expr sumaccrapp in
    let assn := assign_indty src srcacc
                       constr:(aref++accl++" + "++bref++accr) in
    constr:(([assn], c))
  | (?nn,?s) =>
    let n := stringify_nat nn in
    let i := fresh_str c in
    let assntup := tensoradd aref bref s src
                   constr:(fun xs => srcacc (indty_cons (TUP i n) xs))
                   constr:(fun xs => sumaccl (indty_cons (TUP i n) xs))
                   constr:(fun xs => sumaccr (indty_cons (TUP i n) xs))
                            constr:(S c) in
    let assn := fst2 assntup in
    let c' := snd2 assntup in
    constr:((app (("for (int "++i++" = 0; "++i++" < "++n++"; "++i++"++) {")::
                        assn) ["}"], c'))
  end.

(* Lowering is meant to be executed on a normalized program *)
(* allocs, lowering, frees, state *)
(* To represent a list of shape lists *)
(*                      id   []       *)                                  
Ltac L prog src srcacc par c :=
  lazymatch prog with
  | 1%R =>
    let ret := assign_indty src srcacc constr:("1") in
    constr:((@nil string,[ret],@nil string,c))
  | 0%R =>
    let ret := assign_indty src srcacc constr:("0") in
    constr:((@nil string,[ret],@nil string,c))             
  | _ _[_] =>
    let gettup := flatten_get prog in
    let index := fst2 gettup in 
    let v := snd2 gettup in

    let vec_ref_alloc_free_c :=
        isvar_or_alloc v c in
    let vecref := fst5 vec_ref_alloc_free_c in
    let vecallocs := snd5 vec_ref_alloc_free_c in
    let veclower := thd5 vec_ref_alloc_free_c in
    let vecfrees := frt5 vec_ref_alloc_free_c in
    let c' := fth5 vec_ref_alloc_free_c in

    let ret := assign_indty src srcacc constr:(vecref++"["++index++"]") in
    constr:(( @nil string
             , (vecallocs++
               veclower++
               (ret :: vecfrees))%list
             , @nil string
             , c'))
    | (?a * ?b)%R =>
    let a_ref_alloc_free_c :=
        isvar_or_alloc a c in        
    let aref := fst5 a_ref_alloc_free_c in
    let aallocs := snd5 a_ref_alloc_free_c in
    let alower := thd5 a_ref_alloc_free_c in
    let afrees := frt5 a_ref_alloc_free_c in
    let c' := fth5 a_ref_alloc_free_c in

    let b_ref_alloc_free_c :=
        isvar_or_alloc b c' in        
    let bref := fst5 b_ref_alloc_free_c in
    let ballocs := snd5 b_ref_alloc_free_c in
    let blower := thd5 b_ref_alloc_free_c in
    let bfrees := frt5 b_ref_alloc_free_c in
    let c'' := fth5 b_ref_alloc_free_c in    

    let ret := assign_indty src srcacc constr:(aref++" * "++bref) in
    constr:(( @nil string
             , app (aallocs++
               ballocs++
               alower++
               blower)%list
               (ret::
               (afrees++bfrees)%list)
             , @nil string
             ,c''))
    | (?a / ?b)%R =>
    let a_ref_alloc_free_c :=
        isvar_or_alloc a c in        
    let aref := fst5 a_ref_alloc_free_c in
    let aallocs := snd5 a_ref_alloc_free_c in
    let alower := thd5 a_ref_alloc_free_c in
    let afrees := frt5 a_ref_alloc_free_c in
    let c' := fth5 a_ref_alloc_free_c in

    let b_ref_alloc_free_c :=
        isvar_or_alloc b c' in        
    let bref := fst5 b_ref_alloc_free_c in
    let ballocs := snd5 b_ref_alloc_free_c in
    let blower := thd5 b_ref_alloc_free_c in
    let bfrees := frt5 b_ref_alloc_free_c in
    let c'' := fth5 b_ref_alloc_free_c in    

    let ret := assign_indty src srcacc constr:("("++aref++") / ("++bref++")") in
    constr:(( @nil string
             , app (aallocs++
               ballocs++
               alower++
               blower)%list
               (ret::
               (afrees++
               bfrees)%list)
             , @nil string
             ,c''))             
    | (?a + ?b)%R =>
    let a_ref_alloc_free_c :=
        isvar_or_alloc a c in        
    let aref := fst5 a_ref_alloc_free_c in
    let aallocs := snd5 a_ref_alloc_free_c in
    let alower := thd5 a_ref_alloc_free_c in
    let afrees := frt5 a_ref_alloc_free_c in
    let c' := fth5 a_ref_alloc_free_c in

    let b_ref_alloc_free_c :=
        isvar_or_alloc b c' in        
    let bref := fst5 b_ref_alloc_free_c in
    let ballocs := snd5 b_ref_alloc_free_c in
    let blower := thd5 b_ref_alloc_free_c in
    let bfrees := frt5 b_ref_alloc_free_c in
    let c'' := fth5 b_ref_alloc_free_c in    
    let ret := assign_indty src srcacc constr:(aref++" + "++bref) in
    constr:(( @nil string
             , app (aallocs++
               ballocs++
               alower++
               blower)%list
               (ret::
               (afrees++
               bfrees)%list)
             , @nil string
             ,c''))
  | |[ ?p ]| ?e =>
    let pstr := stringify_bool p in

    let tup := L e src srcacc par c in
    let allocs := fst tup in
    let lower := snd tup in
    let frees := thd tup in
    let c' := frt tup in

    constr:(( @nil string
             ,
             app allocs
             (app (("if ("++pstr++") {")::lower)
                   ("}"::frees))
             , @nil string
             , c'))
  | GEN [ ii < ?nn ] @?f ii =>
      let _ := match goal with _ => assert Z by exact 0%Z end in
      let i' := match goal with H : Z |- _ => H end in
      let i := constr:(ltac:(to_str i')) in
      let n := stringify_int nn in
    
      let body' := constr:(f i') in
      let body := eval lazy beta in body' in
        
      let tup :=
          L body src
            constr:(fun s => srcacc (indty_cons (TUP i n) s))
            constr:(false)
            c
      in
      let allocs := fst tup in
      let lower := snd tup in
      let frees := thd tup in
      let c' := frt tup in
      let pragma := match par with
                    | true => constr:("#pragma omp parallel for")
                    | false => constr:("")
                    end in
      constr:((@nil string
               , app allocs
                (app (pragma::
                ("for (int "++i++" = 0; "++i++" < "++n++"; "++i++"++) {")::
                          lower)
                          ("}"::frees))
               , @nil string
               , c'))
  | GEN [ ?mm <= ii < ?nn ] @?f ii =>
    let _ := match goal with _ => assert Z by exact 0%Z end in
    let i' := match goal with H : Z |- _ => H end in
    let i := constr:(ltac:(to_str i')) in
    let n := stringify_int nn in
    let m := stringify_int mm in
    
    let body' := constr:(f i') in
    let body := eval lazy beta in body' in

    let tup :=
        L body src
          constr:(fun s => srcacc
                             (indty_cons
                                (TUP ("("++i++" - ("++m++"))")
                                     ("("++n++" - ("++m++"))")) s))
          constr:(false)
          c
    in
    let allocs := fst tup in
    let lower := snd tup in
    let frees := thd tup in
    let c' := frt tup in
    let pragma := match par with
                    | true => constr:("#pragma omp parallel for")
                    | false => constr:("")
                    end in    
    constr:((@nil string
             , app allocs
             (app (pragma::
             ("for (int "++i++" = "++m++"; "++i++" < "++n++"; "++i++"++) {")::
                        lower)
                        ("}"::frees) )
             , @nil string
             , c'))
  | let_binding ?e1 ?e2 =>
    match type of e1 with
    | Z =>

    let _ := match goal with _ =>
                             let tempH := fresh "tempH" in
                             (assert (exists temp, temp = e1) as tempH
                                 by eauto; destruct tempH)
             end in
    let x := match goal with H : Z |- _ => H end in
    let xstr := constr:(ltac:(to_str x)) in

    let e1str := stringify_int e1 in
    
    let body' := constr:(e2 x) in
    let body := eval simpl in body' in
        
    let tup := L body src srcacc par c in

    let allocs := fst tup in
    let lower := snd tup in
    let frees := thd tup in
    let c'' := frt tup in

    constr:((@nil string
             , app allocs
               (app (("int "++xstr++" = "++e1str++";")::
               lower)
               frees)
             , @nil string
             , c''))              
    
    | _ =>
    let e1_ref_alloc_free_c :=
        isvar_or_alloc e1 c in        
    let e1ref := fst5 e1_ref_alloc_free_c in
    let e1allocs := snd5 e1_ref_alloc_free_c in
    let e1lower := thd5 e1_ref_alloc_free_c in
    let e1frees := frt5 e1_ref_alloc_free_c in
    let c' := fth5 e1_ref_alloc_free_c in

    let e1t := type of e1 in
    let e1tstr := type_to_str e1t in

    let _ := match goal with _ =>
                             let tempH := fresh "tempH" in
                             (assert (exists temp, temp = e1) as tempH
                                 by eauto; destruct tempH)
             end in

    let x := match goal with H : e1t |- _ => H end in
    let xstr := constr:(ltac:(to_str x)) in
    
    let body' := constr:(e2 x) in
    let body := eval simpl in body' in
        
    let tup := L body src srcacc par c' in

    let allocs := fst tup in
    let lower := snd tup in
    let frees := thd tup in
    let c'' := frt tup in

    let ret :=
        assign_indty xstr
                     constr:(fun (acc : indty) => acc)
                              e1ref
    in
    
    constr:((@nil string
             , app (e1allocs++
               allocs++
               e1lower)%list
                   
               ((e1tstr++" "++ret)::
               (lower++
               e1frees++
               frees)%list)
             , @nil string
             , c''))              
    end
  | SUM [ ii < ?nn ] @?f ii =>
    let _ := match goal with _ => assert Z by exact 0%Z end in
    let i' := match goal with H : Z |- _ => H end in
    let i := constr:(ltac:(to_str i')) in
    let n := stringify_int nn in
    
    let body' := constr:(f i') in
    let body := eval simpl in body' in

    let b_ref_alloc_free_c :=
        isvar_or_alloc body c in        
    let bref := fst5 b_ref_alloc_free_c in
    let ballocs := snd5 b_ref_alloc_free_c in
    let blower := thd5 b_ref_alloc_free_c in
    let bfrees := frt5 b_ref_alloc_free_c in
    let c' := fth5 b_ref_alloc_free_c in

    let pshape := get_shape prog in

    let addtup := tensoradd src bref pshape src srcacc srcacc
                       constr:(fun (acc : indty) => acc) (*REVISIT*)
                       c' in
    let add := fst2 addtup in
    let c'' := snd2 addtup in
    constr:((@nil string
             , app ballocs
             (app (("for (int "++i++" = 0; "++i++" < "++n++"; "++i++"++) {")::
                       (blower++
                       add)%list)
                       ("}"::bfrees))
             , @nil string
             , c''))             
  | transpose ?e =>
    L e src constr:(fun s => srcacc (transpose_indty s)) par
            c
  | flatten_trunc ?n ?e =>
    let nstr := stringify_nat n in
    L e src constr:(fun s => srcacc (flatten_trunc_indty nstr s)) par
                     c
  | flatten ?e =>
    L e src constr:(fun s => srcacc (flatten_indty s)) par
                     c
  | Truncr ?k ?e =>
    let kstr := stringify_int k in
    let srcacc' := constr:(fun s => srcacc (swap_dim_indty kstr s)) in    
    L e src srcacc' par c
  | trunc_r ?k ?e =>
    let kstr := stringify_nat k in
    let srcacc' := constr:(fun s => srcacc (swap_dim_indty kstr s)) in    
    L e src srcacc' par c
  | trunc_l ?k ?e =>
    let kstr := stringify_nat k in
    let srcacc' := constr:(fun s =>
                             srcacc (swap_dim_indty kstr 
                                       (trunc_indty s kstr))) in
    L e src srcacc' par c
  | pad_r ?k ?e =>
    let kstr := stringify_nat k in
    let srcacc' := constr:(fun s => srcacc (pad_indty_dim s kstr)) in
    L e src srcacc' par c
  | pad_l ?k ?e =>
    let kstr := stringify_nat k in
    let srcacc' := constr:(fun s =>
                             srcacc (pad_indty_dim
                                       (pad_indty s kstr) kstr)) in
    L e src srcacc' par c
  | ?a <++> ?b =>
    let sh := get_shape prog in
    let newdim := match sh with
                  | (?n,_) => n
                  end in
    let dim := stringify_nat newdim in
    let ashape := get_shape a in
    let alengthstr := match ashape with
                   | (?n,_) => stringify_nat n
                   | _ => constr:("0")
                      end in

    let srcaccl := constr:(fun s => srcacc (swap_dim_indty dim s)) in
    let srcaccr := constr:(fun s =>
                             srcacc
                              (swap_dim_indty dim (pad_indty s alengthstr))) in
     (* (pad_indty s alengthstr))) in *)
    
    let atup := L a src srcaccl par c in
    let aallocs := fst atup in
    let alower := snd atup in
    let afrees := thd atup in
    let c' := frt atup in

    let btup := L b src srcaccr par c' in
    let ballocs := fst btup in
    let blower := snd btup in
    let bfrees := thd btup in
    let c'' := frt btup in

    constr:((@nil string
             , (aallocs++ballocs++
               alower++blower++
               afrees++bfrees)%list
             , @nil string
             , c''))
  | ?etc =>
    let s := constr:(ltac:(to_str etc)) in
    let ret := assign_indty src srcacc s in
    constr:((@nil string
             , [ret]
             , @nil string
             , c))
  end
with isvar_or_alloc e c :=
  (* returns ref, allocs, frees, c *)
  match goal with
  | _ => match e with
         | 0%R =>
           constr:(( "0.f"
                   , @nil string
                   , @nil string
                   , @nil string
                   , c))           
         | 1%R =>
           constr:(( "1.f"
                   , @nil string
                   , @nil string
                   , @nil string
                    , c))            
         | 2%R =>
           constr:(( "2.f"
                   , @nil string
                   , @nil string
                   , @nil string
                    , c))                       
         | 3%R =>
           constr:(( "3.f"
                   , @nil string
                   , @nil string
                   , @nil string
                    , c))            
         end           
  | _ => let _ := match goal with _ => is_var e end in
         let estr := constr:(ltac:(to_str e)) in
         constr:((estr
                   , @nil string
                   , @nil string
                   , @nil string
                  , c))
  | _ => let size := alloc_size e in
         let t := type of e in
         let tstr := type_to_str t in         
         let eref := fresh_str c in
         let etup := L e constr:(eref)
                         constr:(fun (acc : indty) => acc) constr:(false)
                                  constr:(S c) in
         let eallocs := fst etup in
         let elower := snd etup in
         let efrees := thd etup in
         let c' := frt etup in
         match t with
         | R =>
           constr:((eref
                    , eallocs
                    , (tstr++" "++eref++" = 0;")::elower
                    , efrees
                    , c'))           
         | list _ =>
           constr:((eref
                    , (tstr++" "++eref++
                           " = ("++scalar++"*) calloc(1,"++size++");")
                        ::eallocs
                    , elower
                    , ("free("++eref++");")::efrees
                    , c'))
         end
  end.

Ltac allocs_for_call :=
  match goal with
  | H : consistent ?v ?s |- _ =>
    let var := constr:(ltac:(to_str v)) in
    let t := type of v in
    let tstr := type_to_str t in
    let size := alloc_size_shape s in
    let _ := match goal with _ => generalize dependent H end in
    let rest := allocs_for_call in
    let allocs := fst2 rest in
    let frees := snd2 rest in
    let _ := match goal with _ => assert Z by exact 0%Z end in
    let x' := match goal with H : Z |- _ => H end in
    let x := constr:(ltac:(to_str x')) in
    let _ := match goal with _ => clear x' end in
    let dims := alloc_dim s in
    constr:((
             (scalar++" *"++var++" = ("++scalar++"*) calloc(1,"++size++");")::
             ("for (int "++x++" = 0; "++x++" < "++dims++"; "++x++"++) {")::
             (var++"["++x++"] = random() % 10;")::
             "}"::         
             allocs,
             ("free("++var++");")::frees))
  | _ => constr:((@nil string,@nil string))
  end.

Ltac args_for_call dim :=
  match goal with
  | H : ?T |- _ =>
    match type of T with
    | Set => 
      let var := constr:(ltac:(to_str H)) in
      let allocs_args_frees :=
          match T with
          | Z => constr:(("int "++var++" = "++dim++";"
                          , var,""))
          | nat => constr:(("int "++var++" = "++dim++";"
                            , var,""))
          | R => constr:((scalar++" "++var++" = "++dim++";"
                          , var,""))
          | _ => constr:(( ""
                           , var
                           , ""))
          end in
      
      let _ := match goal with _ => generalize dependent H end in
      
      let alloc := fst3 allocs_args_frees in
      let arg := snd3 allocs_args_frees in
      let free := thd3 allocs_args_frees in
      let rest := args_for_call dim in
      let allocs := fst3 rest in
      let args := snd3 rest in
      let frees := thd3 rest in
      constr:((alloc::allocs,","++arg++args,free::frees))
    end
  | _ => constr:((@nil string,"",@nil string))
  end.

Ltac args_for_decl :=
  match goal with
  | H : ?T |- _ =>
    match type of T with
    | Set => 
      let var := constr:(ltac:(to_str H)) in
      let tstr := type_to_str T in
      
      let _ := match goal with _ => generalize dependent H end in
      
      let rest := args_for_decl in

      constr:(","++tstr++" "++var++rest)
    end
  | _ => constr:("")
  end.


Ltac idtac_list l :=
  lazymatch l with
  | ?x::?xs => idtac x; idtac_list xs
  | _ => idtac
  end.
           
