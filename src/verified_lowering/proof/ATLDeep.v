From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Stdlib Require Import ZArith.Zdiv.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.

Set Warnings "-deprecate-hint-without-locality,-deprecated".
Import ListNotations.

From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.
From Lower Require Import Zexpr Bexpr Array Range Sexpr Result ListMisc
  Meshgrid VarGeneration Injective Constant InterpretReindexer
  WellFormedEnvironment.

Open Scope string_scope.

Inductive ATLexpr :=
| Gen (i : string) (lo hi : Zexpr) (body : ATLexpr)
| Sum (i : string) (lo hi : Zexpr) (body : ATLexpr)
| Guard (p : Bexpr) (body : ATLexpr)
| Lbind (x : string) (e1 e2 : ATLexpr)
| Concat (x y : ATLexpr)
| Flatten (e : ATLexpr)
| Split (k : Zexpr) (e : ATLexpr)
| Transpose (e : ATLexpr)
| Truncr (n : Zexpr) (e : ATLexpr)
| Truncl (n : Zexpr) (e : ATLexpr)
| Padr (n : Zexpr) (e : ATLexpr)
| Padl (n : Zexpr) (e : ATLexpr)
| Scalar (s : Sexpr).

Inductive StoreType :=
| Assign
| Reduce.

Inductive stmt :=
| Store (t : StoreType) (v : string) (i : list (Zexpr * Zexpr)) (rhs : Sstmt)
| If (cond : Bexpr) (body : stmt)
| AllocV (var : string) (size : Zexpr)
         (* var = calloc(size) *)
| AllocS (var : string)
         (* var = 0 *)
| DeallocS (var : string)
| Free (var : string)
| For (i : string) (lo hi : Zexpr) (body : stmt)
| Seq (s1 s2 : stmt).

Fixpoint vars_of (e : ATLexpr) : set var :=
  match e with
  | Gen _ _ _ body => (vars_of body)
  | Sum _ _ _ body => (vars_of body)
  | Guard _ body => (vars_of body)
  | Lbind x body1 body2 => (constant [x])
                             \cup (vars_of body1) \cup (vars_of body2)
  | Concat body1 body2 => (vars_of body1) \cup (vars_of body2)
  | Transpose body => vars_of body
  | Split _ body => vars_of body
  | Flatten body => vars_of body
  | Truncr _ body => vars_of body
  | Truncl _ body => vars_of body
  | Padr _ body => vars_of body
  | Padl _ body => vars_of body
  | Scalar _ => constant []
  end.

Fixpoint sizeof (e : ATLexpr) :=
  match e with
  | Gen i lo hi body =>
    (ZMinus hi lo)::(sizeof body)
  | Sum i lo hi body =>
    sizeof body
  | Guard p body =>
    sizeof body
  | Lbind x e1 e2 =>
    sizeof e2
  | Concat x y =>
    let sx := sizeof x in
    let sy := sizeof y in
    match sx with
    | n::rest =>
      match sy with
      | m::rest' =>
        (ZPlus n m)::rest
      | _ => sx
      end
    | _ =>
      match sy with
      | m::rest' =>
        sy
      | _ => [ZLit 0]
      end
    end
  | Flatten e =>
    match sizeof e with
    | a::b::rest => (ZTimes a b)::rest
    | [] => [ZLit 0]
    | s => s
    end
  | Split k e =>
    match sizeof e with
    | a::rest => (ZDivc a k)::k::rest
    | [] => [ZLit 0]
    end
  | Transpose e =>
    match sizeof e with
    | a::b::rest => b::a::rest
    | [] => [ZLit 0]
    | s => s
    end
  | Truncr n e =>
    match sizeof e with
    | m::rest  =>
      (ZMinus m n)::rest
    | [] => [ZLit 0]
    end
  | Truncl n e =>
    match sizeof e with
    | m::rest  =>
      (ZMinus m n)::rest
    | [] => [ZLit 0]
    end           
  | Padr n e =>
    match sizeof e with
    | m::rest  =>
      (ZPlus m n)::rest
    | [] => [ZLit 0]
    end         
  | Padl n e =>
    match sizeof e with
    | m::rest  =>
      (ZPlus m n)::rest
    | [] => [ZLit 0]
    end                  
  | Scalar s =>
    []
  end.    

Definition flat_sizeof e :=
  match sizeof e with
  | [] => ZLit 0
  | x::xs => fold_left ZTimes xs x
  end.

Fixpoint lower
         (e : ATLexpr)
         (f : list (Zexpr * Zexpr) -> list (Zexpr * Zexpr))
         p asn sh :=
  match e with
  | Gen i lo hi body =>
      For i lo hi
          (lower body (fun l =>
                         f ((ZMinus (ZVar i) lo,
                              ZMinus hi lo)::l)) p asn sh)
  | Sum i lo hi body =>
      For i lo hi
          (lower body f p Reduce sh)
  | Guard b body =>
      If b (lower body f p asn sh)
  | Scalar s =>
      Store asn p (f nil) (lowerS s sh)
  | Lbind x e1 e2 =>
    match sizeof e1 with
    | [] =>
        Seq (AllocS x)
            (Seq (lower e1 (fun l => l) x Assign sh)
                 (Seq (lower e2 f p asn (sh $+ (x,sizeof e1)))
                      (DeallocS x)))
    | _ =>
      Seq (AllocV x (flat_sizeof e1))
          (Seq (lower e1 (fun l => l) x Assign sh)
               (Seq (lower e2 f p asn (sh $+ (x,sizeof e1)))
                    (Free x)))
    end
  | Concat x y =>
    let xlen := match sizeof x with
                | n::_ => n
                | _ => ZLit 0
                end in 
    let ylen := match sizeof y with
                | n::_ => n
                | _ => ZLit 0
                end in   
    Seq (lower x (fun l =>
                    f (match l with
                     | (v,d)::xs =>
                         ((v,ZPlus d ylen)::xs)
                     | _ => l
                     end)) p asn sh)
        (lower y (fun l => f (match l with
                          | (v,d)::xs => ((ZPlus v xlen,ZPlus d xlen)::xs)
                          | _ => l
                          end)) p asn sh)
  | Transpose e =>
    lower e (fun l => f (match l with
                         | (v,d)::(vi,di)::xs => (vi,di)::(v,d)::xs
                         | _ => l
                         end)) p asn sh
  | Split k e =>
    lower e (fun l => f (match l with
                         | (v,d)::xs => (ZDivf v k,ZDivc d k)::(ZMod v k,k)::xs
                         | _ => l
                         end)) p asn sh
  | Flatten e =>
    lower e (fun l => f (match l with
                         | (v,d)::(vi,di)::xs =>
                           (ZPlus (ZTimes v di) vi,ZTimes d di)::xs
                         | _ => l
                         end)) p asn sh          
  | Truncr n e =>
    lower e (fun l => f (match l with
                         | (v,d)::xs =>
                           (v,ZMinus d n)::xs
                         | _ => l
                         end)) p asn sh
  | Truncl n e =>
    lower e (fun l => f (match l with
                         | (v,d)::xs =>
                             (ZMinus v n,
                               ZMinus d n)::xs
                         | _ => l
                         end)) p asn sh
  | Padr n e =>
    lower e (fun l => f (match l with
                         | (v,d)::xs =>
                           (v,ZPlus d n)::xs
                         | _ => l
                         end)) p asn sh
  | Padl n e =>
    lower e (fun l => f (match l with
                         | (v,d)::xs =>
                           (ZPlus v n,ZPlus d n)::xs
                         | _ => l
                         end)) p asn sh
  end.

Inductive size_of : ATLexpr -> list Zexpr -> Prop :=
| SizeOfGen : forall i lo hi body l,
    size_of body l ->
    size_of (Gen i lo hi body) ((ZMinus hi lo)::l)
| SizeOfSum : forall i lo hi body l,
    size_of body l ->
    size_of (Sum i lo hi body) l
| SizeOfGuard : forall p e l,
    size_of e l ->
    size_of (Guard p e) l
| SizeOfLBind : forall e1 e2 x l2,
    size_of e2 l2 ->
    size_of (Lbind x e1 e2) l2
| SizeOfConcat : forall e1 e2 l1 l2 n m,
    size_of e1 (n::l1) ->
    size_of e2 (m::l2) ->
    (forall v,
        map (eval_Zexpr_Z_total v) l1 = map (eval_Zexpr_Z_total v) l2) ->
    size_of (Concat e1 e2) ((ZPlus n m)::l1)
| SizeOfFlatten : forall e n m l,
    size_of e (n::m::l) ->
    size_of (Flatten e) ((ZTimes n m)::l)
| SizeOfSplit : forall e n l k,
    size_of e (n::l) ->
    size_of (Split k e) ((ZDivc n k)::k::l)
| SizeOfTranspose : forall e n m l,
    size_of e (n::m::l) ->
    size_of (Transpose e) (m::n::l)
| SizeOfTruncr : forall n e m l,
    size_of e (m::l) ->
    size_of (Truncr n e) (ZMinus m n::l)
| SizeOfTruncl : forall n e m l,
    size_of e (m::l) ->
    size_of (Truncl n e) (ZMinus m n::l)
| SizeOfPadr : forall n e m l,
    size_of e (m::l) ->
    size_of (Padr n e) ((ZPlus m n)::l)
| SizeOfPadl : forall n e m l,
    size_of e (m::l) ->
    size_of (Padl n e) ((ZPlus m n)::l)
| SizeOfScalar : forall s,
    size_of (Scalar s) [].
Local Hint Constructors eval_Zexpr eval_Bexpr eval_Sexpr size_of.

Inductive eval_stmt (v : valuation) :
  stack -> heap -> stmt -> stack -> heap -> Prop :=
| EvalAssignS :
    forall x st h rhs r cont a,
      eval_Sstmt v st h rhs r ->
      st $? x = Some a ->
      cont = [] ->
      eval_stmt v st h (Store Assign x cont rhs) (st $+ (x,r)) h
| EvalAssignV :
    forall x st h rhs r cont arr z a,
      eval_Sstmt v st h rhs r ->
      cont <> [] ->
      h $? x = Some arr ->
      eval_Zexpr_Z v (flatten_shape_index
                              (map snd cont)
                              (map fst cont)) = Some z ->
      arr $? z = Some a ->
      eval_stmt v st h (Store Assign x cont rhs) st (h $+ (x, arr $+ (z,r)))
| EvalReduceS :
    forall x st h rhs r old cont,
      eval_Sstmt v st h rhs r ->
      st $? x = Some old ->
      cont = [] ->
      eval_stmt v st h (Store Reduce x cont rhs) (st $+ (x,r+old)%R) h
| EvalReduceV :
    forall x st h rhs r cont arr z old,
      eval_Sstmt v st h rhs r ->
      cont <> [] ->
      h $? x = Some arr ->
      eval_Zexpr_Z v (flatten_shape_index
                              (map snd cont)
                              (map fst cont)) = Some z ->
      arr $? z = Some old ->
      eval_stmt v st h
                (Store Reduce x cont rhs) st (h $+ (x, arr $+ (z,r+old)%R))
| EvalIfTrue : forall b s st h st' h',
    eval_stmt v st h s st' h' ->
    eval_Bexpr v b true ->
    eval_stmt v st h (If b s) st' h'
| EvalIfFalse : forall b s st h,
    eval_Bexpr v b false ->
    eval_stmt v st h (If b s) st h
| EvalAllocS : forall x st h,
    eval_stmt v st h (AllocS x) (st $+ (x,0%R)) h
| EvalAllocV : forall x n st h nz,
    eval_Zexpr v n nz ->
    eval_stmt v st h (AllocV x n) st
              (alloc_array_in_heap [Z.to_nat nz] h x)
| EvalFree : forall x st h,
    eval_stmt v st h (Free x) st (h $- x)
| EvalDeallocS : forall x st h,
    eval_stmt v st h (DeallocS x) (st $- x) h
| EvalForStep : forall i st h lo hi body st' h' loz hiz st'' h'',
    eval_Zexpr_Z v lo = Some loz ->
    eval_Zexpr_Z v hi = Some hiz ->
    (loz < hiz)%Z ->
    eval_stmt (v $+ (i,loz)) st h body st' h' ->
    eval_stmt v st' h'
              (For i (ZPlus lo (ZLit 1%Z)) hi body)
              st'' h'' ->
    eval_stmt v st h (For i lo hi body) st'' h''
| EvalForBase : forall i st h lo hi body loz hiz,
    eval_Zexpr_Z v lo = Some loz ->
    eval_Zexpr_Z v hi = Some hiz ->
    (hiz <= loz)%Z ->
    eval_stmt v st h (For i lo hi body) st h
| EvalSeq : forall st h s1 s2 st' h' st'' h'',
    eval_stmt v st h s1 st' h' ->
    eval_stmt v st' h' s2 st'' h'' ->
    eval_stmt v st h (Seq s1 s2) st'' h''.
Local Hint Constructors eval_stmt.
Local Hint Constructors eval_Zexprlist.

Inductive eval_expr (sh : context) :
  valuation -> expr_context -> ATLexpr -> result -> Prop :=
| EvalGenBase : forall ec v lo hi loz hiz i body,
    eval_Zexpr_Z v lo = Some loz ->
    eval_Zexpr_Z v hi = Some hiz ->
    (hiz <= loz)%Z ->
    eval_expr sh v ec (Gen i lo hi body) (V [])
| EvalGenStep : forall ec v lo hi loz hiz i body l r,
    eval_Zexpr_Z v lo = Some loz ->
    eval_Zexpr_Z v hi = Some hiz ->
    (loz < hiz)%Z ->
    ~ i \in dom v ->
    ~ contains_substring "?" i ->
    eval_expr sh (v $+ (i,loz)) ec body r ->
    eval_expr sh v ec (Gen i (ZPlus lo (ZLit 1%Z)) hi body) (V l) ->
    eval_expr sh v ec (Gen i lo hi body) (V (r::l))
| EvalSumStep : forall v ec lo hi loz hiz i body r r' s,
    eval_Zexpr_Z v lo = Some loz ->
    eval_Zexpr_Z v hi = Some hiz ->
    (loz < hiz)%Z ->
    ~ i \in dom v ->
    ~ contains_substring "?" i ->
    eval_expr sh (v $+ (i,loz)) ec body r ->
    eval_expr sh v ec (Sum i (ZPlus lo (ZLit 1%Z)) hi body) r' ->
    add_result r r' s ->
    eval_expr sh v ec (Sum i lo hi body) s
| EvalSumBase : forall v ec lo hi loz hiz i body l lz,
    eval_Zexpr_Z v lo = Some loz ->
    eval_Zexpr_Z v hi = Some hiz ->
    (hiz <= loz)%Z ->
    size_of body l ->
    eval_Zexprlist v l lz ->
    eval_expr sh v ec (Sum i lo hi body) (gen_pad (List.map Z.to_nat lz))
| EvalGuardFalse : forall e v ec b l lz,
    eval_Bexpr v b false ->
    size_of e l ->
    eval_Zexprlist v l lz ->
    eval_expr sh v ec (Guard b e) (gen_pad (List.map Z.to_nat lz))
| EvalGuardTrue : forall e ec v b r,
    eval_Bexpr v b true ->
    eval_expr sh v ec e r ->
    eval_expr sh v ec (Guard b e) r
| EvalLbindS : forall v e1 e2 x r1 l2 ec,
    size_of e1 [] ->
    ec $? x = None ->
    ~ x \in vars_of e1 /\ ~ x \in vars_of e2 ->
    vars_of e1 \cap vars_of e2 = constant nil ->
    eval_expr sh v ec e1 (S r1) ->
    eval_expr (sh $+ (x,[])) v (ec $+ (x,S r1)) e2 l2 ->
    eval_expr sh v ec (Lbind x e1 e2) l2              
| EvalLbindV : forall v e1 e2 x l1 l2 ec esh1 esh1z,
    esh1 <> [] ->
    size_of e1 esh1 ->
    eval_Zexprlist v esh1 esh1z ->
    ec $? x = None ->
    ~ x \in vars_of e1 /\ ~ x \in vars_of e2 ->
    vars_of e1 \cap vars_of e2 = constant nil ->
    eval_expr sh v ec e1 (V l1) ->
    eval_expr (sh $+ (x, esh1)) v
              (ec $+ (x,V l1)) e2 l2 ->
    eval_expr sh v ec (Lbind x e1 e2) l2
| EvalConcat : forall ec v e1 e2 l1 l2,
    eval_expr sh v ec e1 (V l1) ->
    eval_expr sh v ec e2 (V l2) ->
    eval_expr sh v ec (Concat e1 e2) (V (l1++l2))
| EvalTranspose : forall e v ec l n nz m mz esh eshz,
    eval_expr sh v ec e (V l) ->
    size_of e (n::m::esh) ->
    eval_Zexprlist v (n::m::esh) (nz::mz::eshz) ->
    eval_expr sh v ec (Transpose e)
              (transpose_result l (map Z.to_nat (mz::nz::eshz)))
| EvalFlatten : forall e v ec l,
    eval_expr sh v ec e (V l) ->
    Forall (fun x => exists v, x = V v) l ->
    eval_expr sh v ec (Flatten e) (V (flatten_result l))
| EvalSplit : forall e v ec l k,
    eval_expr sh v ec e (V l) ->
    Forall (fun x => exists v, x = V v) l ->
    eval_expr sh v ec (Split k e) (V (split_result (Z.to_nat (eval_Zexpr_Z_total $0 k)) l))
| EvalTruncr : forall e v ec k kz l,
    eval_Zexpr_Z v k = Some kz ->
    (0 <= kz)%Z ->
    eval_expr sh v ec e (V l) ->
    eval_expr sh v ec (Truncr k e)
              (V (List.rev (truncl_list (Z.to_nat kz) (List.rev l))))
| EvalTruncl : forall e v ec k kz l,
    eval_Zexpr_Z v k = Some kz ->
    (0 <= kz)%Z ->
    eval_expr sh v ec e (V l) ->
    eval_expr sh v ec (Truncl k e) (V (truncl_list (Z.to_nat kz) l))
| EvalPadr : forall e v ec l s n k kz sz,
    eval_Zexpr_Z v k = Some kz ->
    (0 <= kz)%Z ->
    size_of e (n::s) ->
    eval_expr sh v ec e (V l) ->
    eval_Zexprlist v s sz ->
    eval_expr sh v ec (Padr k e)
              (V (l++gen_pad_list ((Z.to_nat kz)::(List.map Z.to_nat sz))))
| EvalPadl : forall e v ec l s n k kz sz,
    eval_Zexpr_Z v k = Some kz ->
    (0 <= kz)%Z ->
    size_of e (n::s) ->
    eval_expr sh v ec e (V l) ->
    eval_Zexprlist v s sz ->
    eval_expr sh v ec (Padl k e)
              (V (gen_pad_list ((Z.to_nat kz)::(List.map Z.to_nat sz))++l))
| EvalScalar : forall s v ec r,
    eval_Sexpr sh v ec s r ->
    eval_expr sh v ec (Scalar s) (S r).

Ltac invs :=
  repeat
    match goal with
    | H : _ /\ _ |- _ => invert H
    | H : exists _, _ |- _ => invert H
    | H : eval_Zexprlist _ _ [] |- _ => invert H
    | H : eval_Zexprlist _ [] _ |- _ => invert H
    | H : eval_Zexprlist _ _ (_::_) |- _ => invert H
    | H : eval_Zexprlist _ (_::_) _ |- _ => invert H
    | H : size_of _ _ |- _ => invert1 H
    | H : eval_Zexpr _ (ZPlus _ _) _ |- _ => invert H
    | H : eval_Zexpr _ (ZMinus _ _) _ |- _ => invert H
    | H : eval_Zexpr _ (ZTimes _ _) _ |- _ => invert H
    | H : eval_Zexpr _ (ZDivf _ _) _ |- _ => invert H
    | H : eval_Zexpr _ (ZDivc _ _) _ |- _ => invert H
    | H : eval_Zexpr _ (ZMod _ _) _ |- _ => invert H
    | H : eval_Zexpr _ (ZLit _) _ |- _ => invert H
    | H : eval_Zexpr _ (ZVar _) _ |- _ => invert H
    | H : eval_Bexpr _ (And _ _) _ |- _ => invert H
    | H : eval_Bexpr _ (Lt _ _) _ |- _ => invert H
    | H : eval_Bexpr _ (Le _ _) _ |- _ => invert H
    | H : eval_Bexpr _ (Eq _ _) _ |- _ => invert H
    | H : eval_stmt _ _ _ _ _ _ |- _ => invert1 H
    | H : _ = (_,_) |- _ => invert1 H
    | H : Some _ = Some _ |- _ => invert H
  end.

Lemma size_of_deterministic : forall e l1 l2,
    size_of e l1 ->
    size_of e l2 ->
    l1 = l2.
Proof.
  induction e; intros.
  - invert H. invert H0.
    eq_eval_Z.
    f_equal. eauto.
  - invert H. invert H0.
    eq_eval_Z.
    eauto.
  - invert H. invert H0. eauto.
  - invert H. invert H0. eauto.
  - invert H. invert H0.
    specialize (IHe1 _ _ H3 H2).
    specialize (IHe2 _ _ H4 H5).
    invert IHe1. invert IHe2. eauto.
  - invert H. invert H0.
    specialize (IHe _ _ H2 H1).
    invert IHe.
    eauto.
  - invert H. invert H0. simpl. eapply IHe in H4; eauto. invert H4.
    eauto.
  - invert H. invert H0.
    eapply IHe in H2. 2: apply H1. invert H2. auto.
  - invert H. invert H0.
    specialize (IHe _ _ H4 H3).
    invert IHe.
    reflexivity.
  - invert H. invert H0.
    specialize (IHe _ _ H4 H3).
    invert IHe.
    reflexivity.
  - invert H. invert H0.
    specialize (IHe _ _ H4 H3).
    invert IHe.
    reflexivity.
  - invert H. invert H0.
    specialize (IHe _ _ H4 H3).
    invert IHe.
    reflexivity.
  - invert H. invert H0.
    reflexivity.
Qed.

Ltac eq_size_of :=
  repeat
    match goal with
    | H1 : size_of ?e ?a, H2 : size_of ?e ?b |- _ =>
      pose proof (size_of_deterministic _ _ _ H1 H2); subst;
      clear H2
  end.

Theorem size_of_sizeof : forall e1 l,
    size_of e1 l ->
    sizeof e1 = l.
Proof.
  induction e1; intros; simpl; invert H; try f_equal; eauto.
  - destruct (sizeof e1_1) eqn:e;
      destruct (sizeof e1_2) eqn:ee.
    + eapply IHe1_1 in H2. discriminate.
    + eapply IHe1_1 in H2. discriminate.
    + eapply IHe1_2 in H3. discriminate.
    + eapply IHe1_1 in H2.
      eapply IHe1_2 in H3.
      invert H2. invert H3.
      reflexivity.
  - destruct (sizeof e1) eqn:e.
    eapply IHe1 in H1. discriminate.
    destruct l.
    eapply IHe1 in H1. discriminate.
    eapply IHe1 in H1. invert H1.
    reflexivity.
  - erewrite IHe1 by eassumption. reflexivity.
  - eapply IHe1 in H1; eauto. rewrite H1. reflexivity.
  - destruct (sizeof e1) eqn:e.
    eapply IHe1 in H3. discriminate.
    destruct l.
    eapply IHe1 in H3. invert H3.
    reflexivity.
    eapply IHe1 in H3. invert H3.
    reflexivity.
  - destruct (sizeof e1) eqn:e.
    eapply IHe1 in H3. discriminate.
    destruct l.
    eapply IHe1 in H3. invert H3.
    reflexivity.
    eapply IHe1 in H3. invert H3.
    reflexivity.
  - destruct (sizeof e1) eqn:e.
    eapply IHe1 in H3. discriminate.
    destruct l.
    eapply IHe1 in H3. invert H3.
    reflexivity.
    eapply IHe1 in H3. invert H3.
    reflexivity.
  - destruct (sizeof e1) eqn:e.
    eapply IHe1 in H3. discriminate.
    destruct l.
    eapply IHe1 in H3. invert H3.
    reflexivity.
    eapply IHe1 in H3. invert H3.
    reflexivity.
Qed.

Theorem dom_alloc_array_in_heap : forall h x l,
    l <> [] ->
    dom (alloc_array_in_heap l h x) = constant [x] \cup dom h.
Proof.
  intros. destruct l.
  contradiction.
  unfold alloc_array_in_heap.
  rewrite dom_add. reflexivity.
Qed.

Lemma length_eval_expr_gen : forall sh c v e l i lo hi,
    eval_expr sh v c (Gen i lo hi e) (V l) ->
    forall z,
      eval_Zexpr_Z v (ZMinus hi lo) = Some z ->
      length l = Z.to_nat z.
Proof.
  induct 1; intros.
  - simpl in *. invert H2. rewrite H,H0 in *. invert H4. lia. 
  - invert H6. rewrite H,H0 in *. invert H8.
    simpl.
    erewrite IHeval_expr2.
    2: { reflexivity. }
    2: eauto.
    2: { simpl. rewrite H,H0. reflexivity. }
    lia.
Qed.

Local Hint Resolve
      eval_Zexprlist_includes_valuation includes_add_new None_dom_lookup.

Hint Resolve no_dup_var_generation no_dup_mesh_grid
     forall_map_not_in_index forall_map_not_in_dom
     not_In_var_map2 not_In_var_map
     not_var_generation_in_dom2 not_var_generation_in_index2
     not_var_generation_in_index not_var_generation_in_dom : reindexers.
Hint Extern 3 (Datatypes.length _ = Datatypes.length _) =>
       rewrite map_length; rewrite length_nat_range_rec;
       eapply length_mesh_grid_indices; eassumption : reindexers.

Lemma result_shape_gen_length : forall i lo hi body c v sh l,
    eval_expr c v sh (Gen i lo hi body) (V l) ->
    forall hiz loz,
    eval_Zexpr_Z v lo = Some loz ->
    eval_Zexpr_Z v hi = Some hiz ->
    length l = Z.to_nat (hiz - loz).
Proof.
  induct 1; simpl in *; intros.
  - rewrite H,H0 in *. invert H2. invert H3. lia.
  - rewrite H,H0 in *. invert H6. invert H7.
    specialize IHeval_expr2 with
      (i:=i) (hi:=hi) (body:=body) (l:=l0) (lo:=(lo + | 1 |)%z).
    erewrite IHeval_expr2.
    2: { reflexivity. }
    2: { auto. }
    2: { simpl. rewrite H. reflexivity. }
    2: eauto.
    lia.
Qed.

Hint Extern 3 (Datatypes.length (map _ _) = Datatypes.length _) =>
       rewrite map_length; rewrite length_nat_range_rec;
rewrite map_length; eapply length_mesh_grid_indices; eassumption : reindexers.

Lemma eq_eval_stmt_for :
  forall v st h st' h' body1 body2 hi lo i,
    eval_stmt v st h (For i lo hi body1) st' h' ->
    forall hiz loz,
      eval_Zexpr_Z v lo = Some loz ->
      eval_Zexpr_Z v hi = Some hiz ->
      (forall x, (loz <= x < hiz)%Z ->
                 forall st_ h_ st_' h_',
                   eval_stmt (v $+ (i,x)) st_ h_ body1 st_' h_' ->
                   eval_stmt (v $+ (i,x)) st_ h_ body2 st_' h_') ->
      eval_stmt v st h (For i lo hi body2) st' h'.
Proof.
  induct 1; intros.
  - rewrite H,H0 in *. invert H4. invert H5.
    eapply EvalForStep; eauto.    
    eapply H6. lia. eassumption.
    eapply IHeval_stmt2. reflexivity.
    simpl. rewrite H. reflexivity.
    simpl. rewrite H0. reflexivity.
    intros. eapply H6.  lia. assumption.
  - rewrite H,H0 in *. invert H2. invert H3.
    eapply EvalForBase; eauto.
Qed.

Lemma eq_eval_stmt_lower_eq_reindexers:
  forall e reindexer1 reindexer2 p asn sh v st h st' h',
    eval_stmt v st h (lower e reindexer1 p asn sh) st' h' ->
    (forall l, eq_Z_tuple_index_list
                 (reindexer1 l) (reindexer2 l)) ->
    eval_stmt v st h (lower e reindexer2 p asn sh) st' h'.
Proof.
  induct e; intros; simpl in *; try now (eapply IHe; eauto); pose proof H.
  - invert H; eauto.
    eapply eq_eval_stmt_for; eauto.
  - invert H; eauto.
    eapply eq_eval_stmt_for; eauto.
  - invert H; eauto.
  - cases (sizeof e1).
    + invert H. invert H8. invert H9.
      repeat (econstructor; eauto).
    + invert H. invert H8. invert H9. invert H10.
      repeat (econstructor; eauto).
  - invert H. econstructor.
    eapply IHe1; intros; eauto;
      cases l; simpl; try cases p0; try eapply eq_Z_index_list_empty;
      try eapply H0.
    eapply IHe2; intros; eauto;
      cases l; simpl; try cases p0;
      try eapply eq_Z_tuple_index_list_empty;
      eapply H0.
  - invert H.
    + specialize (H0 []). econstructor. eauto. eauto.
      rewrite H11 in *. invert H0. invs.
      cases (reindexer2 []). auto. simpl in *. lia.
    + eapply EvalAssignV; eauto.
      * specialize (H0 []); simpl in *.
        unfold not in *. intros. apply H8.
        rewrite H in *. invert H0.
        cases (reindexer2 []); cases (reindexer1 []); simpl in *;
          try lia; try discriminate; propositional.
      * rewrite <- H12.
        eapply eq_eval_Zexpr_Z.
        eapply eq_zexpr_flatten_shape_index;
        eapply eq_Z_index_list_sym; apply H0. 
    + specialize (H0 []); simpl in *.
      pose proof H0. unfold eq_Z_tuple_index_list in *. invs.
      econstructor; eauto.
      cases (reindexer2 []); cases (reindexer1 []); simpl in *;
        try lia; try discriminate; propositional.
    + eapply EvalReduceV; eauto.
      * unfold not in *. intros. apply H8.        
        specialize (H0 []); simpl in *.
        invert H0. invs.
        rewrite H in *.
        cases (reindexer2 []); cases (reindexer1 []); simpl in *;
          try lia; try discriminate; propositional.
      * rewrite <- H12.
        eapply eq_eval_Zexpr_Z.
        eapply eq_zexpr_flatten_shape_index;
        eapply eq_Z_index_list_sym; apply H0. 
Qed.

Fixpoint constant_nonneg_bounds (e : ATLexpr) : Prop :=
  match e with
  | Gen i lo hi e =>
      vars_of_Zexpr lo = [] /\ vars_of_Zexpr hi = [] /\
        (0 <= eval_Zexpr_Z_total $0 hi - eval_Zexpr_Z_total $0 lo)%Z /\
        constant_nonneg_bounds e
  | Sum i lo hi e =>
      vars_of_Zexpr lo = [] /\ vars_of_Zexpr hi = [] /\
        constant_nonneg_bounds e
  | Guard p e => constant_nonneg_bounds e
  | Lbind x e1 e2 => constant_nonneg_bounds e1 /\ constant_nonneg_bounds e2
  | Concat e1 e2 => constant_nonneg_bounds e1 /\ constant_nonneg_bounds e2
  | Flatten e => constant_nonneg_bounds e
  | Split k e => vars_of_Zexpr k = [] /\ constant_nonneg_bounds e /\
                   (0 < eval_Zexpr_Z_total $0 k)%Z 
  | Transpose e => constant_nonneg_bounds e
  | Truncr k e => constant_nonneg_bounds e /\ vars_of_Zexpr k = [] /\
                    (0 <= eval_Zexpr_Z_total $0 k)%Z /\
                                    (0 <= match (sizeof e) with
                                          | dim::_ => eval_Zexpr_Z_total $0 dim
                                          | _ => 0%Z
                                          end -
                                            eval_Zexpr_Z_total $0 k)%Z
  | Truncl k e => constant_nonneg_bounds e /\ vars_of_Zexpr k = [] /\
                    (0 <= eval_Zexpr_Z_total $0 k)%Z /\
                                    (0 <= match (sizeof e) with
                                          | dim::_ => eval_Zexpr_Z_total $0 dim
                                          | _ => 0%Z
                                          end -
                                            eval_Zexpr_Z_total $0 k)%Z
  | Padr k e => constant_nonneg_bounds e /\ vars_of_Zexpr k = [] /\
                    (0 <= eval_Zexpr_Z_total $0 k)%Z
  | Padl k e => constant_nonneg_bounds e /\ vars_of_Zexpr k = [] /\
                  (0 <= eval_Zexpr_Z_total $0 k)%Z
  | Scalar s => True
  end.

Lemma eval_expr_for_gen_result_has_shape :
  forall n c v ec i lo hi loz hiz e v0,
    eval_Zexpr_Z v lo = Some loz ->
    eval_Zexpr_Z v hi = Some hiz ->
    (hiz -loz)%Z = Z.of_nat n ->
    eval_expr c v ec (Gen i lo hi e) (V v0) ->
    (forall ii,
        0 <= ii < n ->
        eval_expr c (v$+(i,Z.of_nat ii+loz))%Z ec e
                  (nth ii v0 (S (SS 0%R)))).
Proof.
  induct n; intros.
  - lia.
  - invert H2. rewrite H,H0 in *. invert H9. invert H12. lia.
    rewrite H,H0 in *. invert H9. invert H10.
    cases ii.
    simpl. eauto.
    simpl. posnats.
    replace (Z.of_nat (Datatypes.S ii) + loz0)%Z with
      (Z.of_nat ii + (loz0+1))%Z by lia.
    eapply IHn.
    4: eassumption.
    simpl. rewrite H. auto. eauto. lia. lia.
Qed.

Lemma constant_nonneg_bounds_size_of_no_vars :
  forall e l,
    constant_nonneg_bounds e ->    
    size_of e l ->
    Forall (fun z => vars_of_Zexpr z = []) l.
Proof.
  induct e; simpl; intros; propositional; invert H0; eauto.
  - econstructor. simpl. rewrite H,H1.
    rewrite app_no_dups_empty_r. auto. eauto.
  - eapply IHe1 in H1. 2: apply H4.
    eapply IHe2 in H2. 2: apply H5.
    invert H1. invert H2.
    econstructor. simpl. rewrite H3, H1. rewrite app_no_dups_empty_r. auto.
    auto.
  - eapply IHe in H. 2: apply H2. invert H. invert H4.
    econstructor. simpl. rewrite H3,H1. rewrite app_no_dups_empty_r. auto.
    auto.
  - eapply IHe in H6; eauto. invert H6.
    econstructor. simpl. rewrite H4,H1. eauto. eauto.
  - eapply IHe in H2; auto. invert H2. invert H4.
    eauto.
  - eapply IHe in H1. 2: eassumption. invert H1.
    econstructor. simpl. erewrite size_of_sizeof in * by eauto.
    simpl in *. rewrite H,H5.
    eauto. eauto.
  - eapply IHe in H1. 2: eassumption. invert H1.
    econstructor. simpl. rewrite H,H5.
    eauto. eauto.
  - eapply IHe in H1. 2: eassumption. invert H1.
    econstructor. simpl. rewrite H, H4.
    rewrite app_no_dups_empty_r. auto. auto.
  - eapply IHe in H1. 2: eassumption. invert H1.
    econstructor. simpl. rewrite H, H4.
    rewrite app_no_dups_empty_r. auto. auto.
Qed.

Lemma constant_nonneg_bounds_sizeof_no_vars :
  forall e,
    constant_nonneg_bounds e ->    
    Forall (fun z => vars_of_Zexpr z = []) (sizeof e).
Proof.
  induct e; simpl; intros; propositional.
  - econstructor. simpl. rewrite H,H0. 
    rewrite app_no_dups_empty_r. auto. eauto.
  - cases (sizeof e1); cases (sizeof e2).
    + econstructor. reflexivity. econstructor.
    + eauto.
    + eauto.
    + invert H. invert H2. econstructor. simpl.
      rewrite H4,H5. rewrite app_no_dups_empty_r. auto. auto.
  - cases (sizeof e).
    + econstructor. reflexivity. eauto.
    + invert H0. cases l. econstructor. rewrite H3. eauto. eauto.
      invert H4.
      econstructor. simpl. rewrite H2,H3.
      rewrite app_no_dups_empty_r. auto. auto.
  - cases (sizeof e).
    + econstructor. reflexivity. eauto.
    + econstructor. invert H1. simpl. rewrite H5,H0. reflexivity.
      invert H1. eauto.
  - cases (sizeof e).
    + econstructor. reflexivity. eauto.
    + invert H0. cases l. econstructor. rewrite H3. eauto. eauto.
      invert H4.
      econstructor. auto. econstructor. auto. eauto.
  - invs. cases (sizeof e). econstructor. reflexivity. eauto.
    invert H2.
    econstructor. simpl. rewrite H,H6. reflexivity.
    eauto.
  - invs. cases (sizeof e). econstructor. reflexivity. eauto.
    invert H2.
    econstructor. simpl. rewrite H,H6. reflexivity.
    eauto.
  - cases (sizeof e).
    + econstructor. reflexivity. eauto.
    + invert H1.
      econstructor. simpl. rewrite H,H5.
      rewrite app_no_dups_empty_r. auto. auto.
  - cases (sizeof e).
    + econstructor; eauto.
    + invert H1. econstructor.
      simpl. rewrite H,H5.
      rewrite app_no_dups_empty_r. auto. auto.
  - eauto.
Qed.

Lemma result_has_shape_for_sum :
  forall e lz v ,
    (forall l : list Zexpr,
        constant_nonneg_bounds e ->
        size_of e l ->
        forall v : valuation,
        eval_Zexprlist v l (map (eval_Zexpr_Z_total $0) l) ->
        forall (sh : context) (ec : expr_context) (r : result),
        eval_expr sh v ec e r ->
        result_has_shape r (map Z.to_nat (map (eval_Zexpr_Z_total $0) l))) ->
    forall n l r sh ec i lo hi loz hiz,
    constant_nonneg_bounds e ->
    size_of e l ->
    eval_Zexprlist v l lz ->
    eval_Zexpr_Z v lo = Some loz ->
    eval_Zexpr_Z v hi = Some hiz ->
    Z.of_nat n = (hiz - loz)%Z ->
    eval_expr sh v ec (Sum i lo hi e) r ->
    result_has_shape r (map Z.to_nat (map (eval_Zexpr_Z_total $0) l)).
Proof.
  intros ? ? ? ?.
  induct n; propositional.
  - invert H6.
    rewrite H3,H4 in *. invert H11. invert H12. lia.
    rewrite H3,H4 in *. invert H11. invert H14.
    eq_size_of. eq_eval_Zlist.
    eapply constant_nonneg_bounds_size_of_no_vars in H0; eauto.
    eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H0; eauto.
    eq_eval_Zlist.
    eapply result_has_shape_gen_pad.
  - invert H6.
    rewrite H3,H4 in *. invert H11. invert H12.
    pose proof H0.
    eapply constant_nonneg_bounds_size_of_no_vars in H0; eauto.
    eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H0; eauto.
    eq_eval_Zlist.
    eapply result_has_shape_add_result. eassumption.
    2: { eapply IHn in H20. auto. eassumption. eassumption. eassumption.
         eauto.
         simpl. rewrite H3. reflexivity.
         eauto. lia. } 
    eapply H. 4: eassumption. eassumption. eassumption.
    eapply eval_Zexprlist_add. eassumption. auto.
    eq_size_of. eq_eval_Zlist.
    eapply constant_nonneg_bounds_size_of_no_vars in H0; eauto.
    eapply forall_no_vars_eval_Zexpr_Z_total with (v:=v) in H0; eauto.
    eq_eval_Zlist.
    eapply result_has_shape_gen_pad.
Qed.      

Lemma constant_nonneg_bounds_size_of_nonneg :
  forall e,
    constant_nonneg_bounds e ->
    forall l,
    size_of e l ->
    forall v lz,
      eval_Zexprlist v l lz ->
      Forall (fun x => 0 <= x)%Z lz.
Proof.
  induct e; intros; simpl in *.
  - invert H0. invert H. invert H1. invs.
    econstructor. unfold eval_Zexpr_Z_total in *.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H0,H.
    invs.
    pose proof (H1 v). pose proof (H v). eq_eval_Z.
    specialize (H1 $0). specialize (H $0).
    eapply eval_Zexpr_Z_eval_Zexpr in H,H1.
    rewrite H,H1 in *. lia.
    eapply IHe; eauto.
  - invs. eauto.
  - invs. eauto.
  - invs. eauto.
  - invs. 
    eapply IHe1 in H2. 2: eassumption. 2: eauto.
    invert H2.
    econstructor. 2: eauto.
    pose proof H3 as Hc.
    eapply IHe2 in H3. 2: eassumption.
    2: { eapply forall_no_vars_eval_Zexpr_Z_total with (v:=$0).
         eapply constant_nonneg_bounds_size_of_no_vars. eauto. eauto. }
    invert H3.
    eapply constant_nonneg_bounds_size_of_no_vars in H6; eauto. invert H6.
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total with (v:=$0) in H3.
    eapply H3 in H9. invert H9. lia.
  - invs.
    eapply IHe in H.
    2: eassumption.
    2: econstructor; eauto.
    invert H. invert H5. econstructor. lia. auto.
  - invs. eq_eval_Z. eapply IHe in H.
    2: eauto. 2: econstructor.
    2: eauto. 2: eauto.
    invert H. 
    eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
      with (v:=$0) in H2.
    eapply H2 in H5. invert H5.
    econstructor. 2: eauto.
    eapply ceil_div_nonneg; lia.
    econstructor. lia. eauto.
  - invs. 
    eapply IHe in H. 2: eassumption.
    2: econstructor; eauto. invert H. invert H6.
    eauto.
  - invs. pose proof H2. erewrite size_of_sizeof in * by eauto. simpl in *.
    eapply IHe in H0. 2: eassumption.
    2: { econstructor. eassumption. eassumption. }
    eapply constant_nonneg_bounds_size_of_no_vars in H2.
    2: { eassumption. } invert H2.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H,H7. invs.
    pose proof (H1 $0). pose proof (H2 $0).
    pose proof (H1 v). pose proof (H2 v). eq_eval_Z.
    eapply eval_Zexpr_Z_eval_Zexpr in H,H6.
    unfold eval_Zexpr_Z_total in *.
    rewrite H6,H in *. invert H0.
    econstructor. lia. eauto.
  - invs. pose proof H2. erewrite size_of_sizeof in * by eauto. simpl in *.
    eapply IHe in H0. 2: eassumption.
    2: { econstructor. eassumption. eassumption. }
    eapply constant_nonneg_bounds_size_of_no_vars in H2.
    2: { eassumption. } invert H2.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H,H7. invs.
    pose proof (H1 $0). pose proof (H2 $0).
    pose proof (H1 v). pose proof (H2 v). eq_eval_Z.
    eapply eval_Zexpr_Z_eval_Zexpr in H,H6.
    unfold eval_Zexpr_Z_total in *.
    rewrite H6,H in *. invert H0.
    econstructor. lia. eauto.
  - invs. pose proof H2.
    eapply IHe in H2. 2: eassumption. 2: eauto. invert H2.
    unfold eval_Zexpr_Z_total in *.
    eapply constant_nonneg_bounds_size_of_no_vars in H0.
    2: eassumption. invert H0.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H,H5. invs.
    pose proof (H0 $0). pose proof (H1 $0).
    pose proof (H0 v). pose proof (H1 v). eq_eval_Z.
    eapply eval_Zexpr_Z_eval_Zexpr in H,H1.
    rewrite H1 in *.
    econstructor. lia. eauto.
  - invs. pose proof H2.
    eapply IHe in H2. 2: eassumption. 2: eauto. invert H2.
    unfold eval_Zexpr_Z_total in *.
    eapply constant_nonneg_bounds_size_of_no_vars in H0.
    2: eassumption. invert H0.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H,H5. invs.
    pose proof (H0 $0). pose proof (H1 $0).
    pose proof (H0 v). pose proof (H1 v). eq_eval_Z.
    eapply eval_Zexpr_Z_eval_Zexpr in H,H1.
    rewrite H1 in *.
    econstructor. lia. eauto.
  - invs. eauto.
Qed.

Lemma constant_nonneg_bounds_sizeof_nonneg :
  forall e,
    constant_nonneg_bounds e ->
    forall v lz,
      eval_Zexprlist v (sizeof e) lz ->
      Forall (fun x => 0 <= x)%Z lz.
Proof.
  induct e; intros; simpl in *.
  - invs. unfold eval_Zexpr_Z_total in *.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H1,H.
    invs.
    pose proof (H0 v). pose proof (H v). eq_eval_Z.
    specialize (H0 $0). specialize (H $0).
    eapply eval_Zexpr_Z_eval_Zexpr in H,H0.
    rewrite H,H0 in *. econstructor. lia. eauto.
  - invs. eauto.
  - invs. eauto.
  - invs. eauto.
  - invs. cases (sizeof e1); cases (sizeof e2).
    + invert H0. invert H5. invert H7. econstructor; eauto. lia.
    + invert H0. eapply IHe2 with (v:=v) in H2.
      2: econstructor; eauto. eauto.
    + invert H0.
      eapply IHe1 in H1. 2: econstructor; eauto. eauto.
    + invert H0. invert H5.
      eapply IHe1 in H1. 2: econstructor; eauto.
      invert H1.
      pose proof H2.
      eapply constant_nonneg_bounds_sizeof_no_vars in H. rewrite Heq0 in *.
      invert H.
      eapply IHe2 in H2.
      2: { econstructor. eassumption.
           eapply forall_no_vars_eval_Zexpr_Z_total. eauto. }
      invert H2.
      econstructor. lia. auto.
  - cases (sizeof e).
    + invert H0.
      invert H4. invert H6. econstructor; eauto. lia.
    + cases l. invert H0. eapply IHe in H. 2: econstructor; eauto.
      eauto. invert H0. invert H4.
      eapply IHe in H. 2: econstructor; eauto.
      invert H. invert H4. econstructor. lia. auto.
  - cases (sizeof e).
    + invert H0.
      invert H4. invert H6. econstructor; eauto. lia.
    + invert H0. invert H4. invert H6. invs.
      eapply IHe in H.
      2: econstructor; eauto. invert H.
      eapply vars_of_Zexpr_empty_eq_zexpr_eval_Zexpr_Z_total
        with (v:=$0) in H0; eauto. eapply H0 in H5. invert H5.
      econstructor.
      eapply ceil_div_nonneg. lia.
      lia.
      econstructor. eapply H0 in H4. invert H4. lia. eauto.
  - cases (sizeof e).
    + invert H0. invert H4. invert H6. econstructor; eauto. lia.
    + cases l.
      * invert H0. invert H6. econstructor.
        eapply IHe in H. 2: econstructor.
        2: eauto. 2: eauto. 2: econstructor. invert H. lia.
      * invert H0. invert H6.
        eapply IHe in H. 2: econstructor. 3: econstructor.
        2: eassumption. 2: eassumption. 2: eassumption.
        invert H. invert H5. eauto.
  - invs. cases (sizeof e). invert H0. invert H7. invert H9.
    econstructor. lia. eauto. 
    invert H0. invert H7.
    pose proof H1. eapply IHe in H1. 
    2: econstructor; eauto. invert H1. 
    pose proof H0.
    eapply constant_nonneg_bounds_sizeof_no_vars in H0; eauto.
    rewrite Heq in *.
    invert H0.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H,H11. invs.
    pose proof (H0 $0). pose proof (H3 $0).
    pose proof (H0 v). pose proof (H3 v). eq_eval_Z.
    unfold eval_Zexpr_Z_total in *.
    eapply eval_Zexpr_Z_eval_Zexpr in H,H6. rewrite H,H6 in *.
    econstructor. lia. eauto.
  - invs. cases (sizeof e). invert H0. invert H7. invert H9.
    econstructor. lia. eauto. 
    invert H0. invert H7.
    pose proof H1. eapply IHe in H1. 
    2: econstructor; eauto. invert H1. 
    pose proof H0.
    eapply constant_nonneg_bounds_sizeof_no_vars in H0; eauto.
    rewrite Heq in *.
    invert H0.
    eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H,H11. invs.
    pose proof (H0 $0). pose proof (H3 $0).
    pose proof (H0 v). pose proof (H3 v). eq_eval_Z.
    unfold eval_Zexpr_Z_total in *.
    eapply eval_Zexpr_Z_eval_Zexpr in H,H6. rewrite H,H6 in *.
    econstructor. lia. eauto.
  - invs. cases (sizeof e).
    + invs. econstructor; eauto; lia.
    + invs. pose proof H1.
      eapply constant_nonneg_bounds_sizeof_no_vars in H1.
      rewrite Heq in *. invert H1.
      eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H,H6. invs.
      pose proof (H1 $0). pose proof (H2 $0).
      pose proof (H1 v). pose proof (H2 v). eq_eval_Z.
      unfold eval_Zexpr_Z_total in *.
      eapply eval_Zexpr_Z_eval_Zexpr in H,H5. rewrite H5 in *.
      eapply IHe in H0. 2: econstructor; eauto. invert H0.
      econstructor. lia. eauto.
  - invs. cases (sizeof e).
    + invs. econstructor; eauto; lia.
    + invs. pose proof H1.
      eapply constant_nonneg_bounds_sizeof_no_vars in H1.
      rewrite Heq in *. invert H1.
      eapply vars_of_Zexpr_empty_eval_Zexpr_literal in H,H6. invs.
      pose proof (H1 $0). pose proof (H2 $0).
      pose proof (H1 v). pose proof (H2 v). eq_eval_Z.
      unfold eval_Zexpr_Z_total in *.
      eapply eval_Zexpr_Z_eval_Zexpr in H,H5. rewrite H5 in *.
      eapply IHe in H0. 2: econstructor; eauto. invert H0.
      econstructor. lia. eauto.
  -  invert H0. eauto.
Qed.

