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
From Stdlib Require Import Logic.FunctionalExtensionality.

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
| Store (t : StoreType) (v : string) (i : list (Zexpr * Z)) (rhs : Sstmt)
| If (cond : Bexpr) (body : stmt)
| AllocV (var : string) (size : nat)
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

Fixpoint sizeof (e : ATLexpr) : list nat :=
  match e with
  | Gen i lo hi body =>
      Z.to_nat (eval_Zexpr_Z_total $0 (ZMinus hi lo)) ::(sizeof body)
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
        n + m ::rest
      | _ => sx
      end
    | _ =>
      match sy with
      | m::rest' =>
        sy
      | _ => [0]
      end
    end
  | Flatten e =>
    match sizeof e with
    | a::b::rest => a * b :: rest
    | [] => [0]
    | s => s
    end
  | Split k e =>
    match sizeof e with
    | a::rest => (a //n (Z.to_nat (eval_Zexpr_Z_total $0 k))):: Z.to_nat (eval_Zexpr_Z_total $0 k) :: rest
    | [] => [0]
    end
  | Transpose e =>
    match sizeof e with
    | a::b::rest => b::a::rest
    | [] => [0]
    | s => s
    end
  | Truncr n e =>
    match sizeof e with
    | m::rest  =>
      m - Z.to_nat (eval_Zexpr_Z_total $0 n) ::rest
    | [] => [0]
    end
  | Truncl n e =>
    match sizeof e with
    | m::rest  =>
      m - Z.to_nat (eval_Zexpr_Z_total $0 n) ::rest
    | [] => [0]
    end           
  | Padr n e =>
    match sizeof e with
    | m :: rest => m + Z.to_nat (eval_Zexpr_Z_total $0 n) ::rest
    | [] => [0]
    end         
  | Padl n e =>
    match sizeof e with
    | m::rest  =>
      m + Z.to_nat (eval_Zexpr_Z_total $0 n)::rest
    | [] => [0]
    end                  
  | Scalar s =>
    []
  end.    

Definition flat_sizeof e :=
  match sizeof e with
  | [] => 0
  | x::xs => fold_left mul xs x
  end.

Fixpoint lower
         (e : ATLexpr)
         (f : list (Zexpr * Z) -> list (Zexpr * Z))
         p asn (sh : context) :=
  match e with
  | Gen i lo hi body =>
      For i lo hi
          (lower body (fun l =>
                         f (((! i ! - | eval_Zexpr_Z_total $0 lo |)%z,
                              eval_Zexpr_Z_total $0 (hi - lo)%z)::l)) p asn sh)
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
                | n::_ => Z.of_nat n
                | _ => 0%Z
                end in 
    let ylen := match sizeof y with
                | n::_ => Z.of_nat n
                | _ => 0%Z
                end in   
    Seq (lower x (fun l =>
                    f (match l with
                     | (v,d)::xs =>
                         ((v,(d + ylen)%Z)::xs)
                     | _ => l
                     end)) p asn sh)
        (lower y (fun l => f (match l with
                          | (v,d)::xs => ((ZPlus v (ZLit xlen),(d + xlen)%Z)::xs)
                          | _ => l
                          end)) p asn sh)
  | Transpose e =>
    lower e (fun l => f (match l with
                         | (v,d)::(vi,di)::xs => (vi,di)::(v,d)::xs
                         | _ => l
                         end)) p asn sh
  | Split k e =>
      let k := eval_Zexpr_Z_total $0 k in
      lower e (fun l => f (match l with
                        | (v,d)::xs => ((v / | k |)%z, (d // k)%Z) ::(ZMod v (ZLit k),k )::xs
                                     | _ => l
                                      end)) p asn sh
  | Flatten e =>
    lower e (fun l => f (match l with
                         | (v,d)::(vi,di)::xs =>
                           ((v * | di | + vi)%z, (d * di)%Z)::xs
                         | _ => l
                         end)) p asn sh          
  | Truncr n e =>
    lower e (fun l => f (match l with
                         | (v,d)::xs =>
                           (v,(d - eval_Zexpr_Z_total $0 n)%Z)::xs
                         | _ => l
                         end)) p asn sh
  | Truncl n e =>
    lower e (fun l => f (match l with
                         | (v,d)::xs =>
                             ((v - | eval_Zexpr_Z_total $0 n |)%z,
                               (d - eval_Zexpr_Z_total $0 n)%Z)::xs
                         | _ => l
                         end)) p asn sh
  | Padr n e =>
    lower e (fun l => f (match l with
                         | (v,d)::xs =>
                           (v, (d + eval_Zexpr_Z_total $0 n)%Z)::xs
                         | _ => l
                         end)) p asn sh
  | Padl n e =>
    lower e (fun l => f (match l with
                         | (v,d)::xs =>
                             ((v + | eval_Zexpr_Z_total $0 n |)%z,
                               (d + eval_Zexpr_Z_total $0 n)%Z)::xs
                         | _ => l
                         end)) p asn sh
  end.

Inductive size_of : ATLexpr -> list nat -> Prop :=
| SizeOfGen : forall i lo loz hi hiz body sh d,
    size_of body sh ->
    eval_Zexpr $0 lo loz ->
    eval_Zexpr $0 hi hiz ->
    d = Z.to_nat (hiz - loz) ->
    size_of (Gen i lo hi body) (d :: sh)
| SizeOfSum : forall i lo loz hi hiz body sh,
    eval_Zexpr $0 lo loz ->
    eval_Zexpr $0 hi hiz ->
    size_of body sh ->
    size_of (Sum i lo hi body) sh
| SizeOfGuard : forall p e sh,
    size_of e sh ->
    size_of (Guard p e) sh
| SizeOfLBind : forall e1 e2 x sh2,
    size_of e2 sh2 ->
    size_of (Lbind x e1 e2) sh2
| SizeOfConcat : forall e1 e2 sh n m d,
    size_of e1 (n::sh) ->
    size_of e2 (m::sh) ->
    d = n + m ->
    size_of (Concat e1 e2) (d::sh)
| SizeOfFlatten : forall e n m sh d,
    size_of e (n :: m :: sh) ->
    d = n * m ->
    size_of (Flatten e) (d :: sh)
| SizeOfSplit : forall e n sh k kz d1 d2,
    size_of e (n::sh) ->
    eval_Zexpr $0 k kz ->
    d1 = n //n (Z.to_nat kz) ->
    d2 = Z.to_nat kz ->
    (0 < kz)%Z ->
    size_of (Split k e) (d1 :: d2 :: sh)
| SizeOfTranspose : forall e n m sh,
    size_of e (n::m::sh) ->
    size_of (Transpose e) (m::n::sh)
| SizeOfTruncr : forall k kz e m sh d,
    size_of e (m::sh) ->
    eval_Zexpr $0 k kz ->
    (Z.to_nat kz <= m) ->
    d = m - Z.to_nat kz ->
    size_of (Truncr k e) (d :: sh)
| SizeOfTruncl : forall k kz e m sh d,
    size_of e (m :: sh) ->
    eval_Zexpr $0 k kz ->
    (Z.to_nat kz <= m) ->
    d = m - Z.to_nat kz ->
    size_of (Truncl k e) (d :: sh)
| SizeOfPadr : forall k kz e m sh d,
    size_of e (m :: sh) ->
    eval_Zexpr $0 k kz ->
    d = m + Z.to_nat kz ->
    size_of (Padr k e) (d :: sh)
| SizeOfPadl : forall k kz e m sh d,
    size_of e (m :: sh) ->
    eval_Zexpr $0 k kz ->
    d = m + Z.to_nat kz ->
    size_of (Padl k e) (d :: sh)
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
| EvalAllocV : forall x n st h,
    eval_stmt v st h (AllocV x n) st
              (alloc_array_in_heap [n] h x)
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
| EvalSumBase : forall v ec lo hi loz hiz i body sz,
    eval_Zexpr_Z v lo = Some loz ->
    eval_Zexpr_Z v hi = Some hiz ->
    (hiz <= loz)%Z ->
    size_of body sz ->
    eval_expr sh v ec (Sum i lo hi body) (gen_pad sz)
| EvalGuardFalse : forall e v ec b sz,
    eval_Bexpr v b false ->
    size_of e sz ->
    eval_expr sh v ec (Guard b e) (gen_pad sz)
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
| EvalLbindV : forall v e1 e2 x l1 l2 ec sz0 sz1,
    sz1 <> [] ->
    eval_Zexprlist v sz0 (map Z.of_nat sz1) ->
    size_of e1 sz1 ->
    ec $? x = None ->
    ~ x \in vars_of e1 /\ ~ x \in vars_of e2 ->
    vars_of e1 \cap vars_of e2 = constant nil ->
    eval_expr sh v ec e1 (V l1) ->
    eval_expr (sh $+ (x, sz1)) v
              (ec $+ (x,V l1)) e2 l2 ->
    eval_expr sh v ec (Lbind x e1 e2) l2
| EvalConcat : forall ec v e1 e2 l1 l2,
    eval_expr sh v ec e1 (V l1) ->
    eval_expr sh v ec e2 (V l2) ->
    eval_expr sh v ec (Concat e1 e2) (V (l1++l2))
| EvalTranspose : forall e v ec l n m esh,
    eval_expr sh v ec e (V l) ->
    size_of e (n::m::esh) ->
    eval_expr sh v ec (Transpose e)
              (transpose_result l (m::n::esh))
| EvalFlatten : forall e v ec l,
    eval_expr sh v ec e (V l) ->
    Forall (fun x => exists v, x = V v) l ->
    eval_expr sh v ec (Flatten e) (V (flatten_result l))
| EvalSplit : forall e v ec l k kz,
    eval_expr sh v ec e (V l) ->
    eval_Zexpr_Z $0 k = Some kz ->
    Forall (fun x => exists v, x = V v) l ->
    eval_expr sh v ec (Split k e) (V (split_result (Z.to_nat kz) l))
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
| EvalPadr : forall e v ec l s n k kz,
    eval_Zexpr_Z v k = Some kz ->
    (0 <= kz)%Z ->
    size_of e (n::s) ->
    eval_expr sh v ec e (V l) ->
    eval_expr sh v ec (Padr k e)
              (V (l++gen_pad_list ((Z.to_nat kz)::s)))
| EvalPadl : forall e v ec l s n k kz,
    eval_Zexpr_Z v k = Some kz ->
    (0 <= kz)%Z ->
    size_of e (n::s) ->
    eval_expr sh v ec e (V l) ->
    eval_expr sh v ec (Padl k e)
              (V (gen_pad_list ((Z.to_nat kz)::s)++l))
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

(*because invs is slow sometimes*)
Ltac invs' :=
  repeat match goal with
    | H:_ /\ _ |- _ => invert H
    | H:exists _, _ |- _ => invert H
    | H:Some _ = Some _ |- _ => invert H
    | H: _ :: _ = _ :: _ |- _ => invert H
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
  - invert H. invert H0. simpl. eapply IHe in H3; eauto. invert H3.
    eapply eval_Zexpr_deterministic in H4; eauto. subst. reflexivity.
  - invert H. invert H0.
    eapply IHe in H2. 2: apply H1. invert H2. auto.
  - invert H. invert H0. specialize (IHe _ _ H3 H2). invert IHe.
    eapply eval_Zexpr_deterministic in H4; eauto. subst. reflexivity.
  - invert H. invert H0. specialize (IHe _ _ H3 H2). invert IHe.
    eapply eval_Zexpr_deterministic in H4; eauto. subst. reflexivity.
  - invert H. invert H0. specialize (IHe _ _ H3 H2). invert IHe.
    eapply eval_Zexpr_deterministic in H4; eauto. subst. reflexivity.
  - invert H. invert H0. specialize (IHe _ _ H3 H2). invert IHe.
    eapply eval_Zexpr_deterministic in H4; eauto. subst. reflexivity.
  - invert H. invert H0. reflexivity.
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
  induction e1; intros; simpl; invert H; try f_equal; eauto;
    repeat match goal with
      | H: eval_Zexpr _ _ _ |- _ => apply eval_Zexpr_Z_eval_Zexpr in H
      end;
    cbv [eval_Zexpr_Z_total]; simpl;
    repeat match goal with
      | H: eval_Zexpr_Z _ _ = _ |- _ => rewrite H
      end; try lia;
    repeat match goal with
      | IHe: forall _, _ -> sizeof _ = _ |- _ => erewrite IHe by eauto; simpl
      end; reflexivity.
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
       rewrite length_map; rewrite length_nat_range_rec;
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
       rewrite length_map; rewrite length_nat_range_rec;
rewrite length_map; eapply length_mesh_grid_indices; eassumption : reindexers.

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
      cases (reindexer2 []). auto. simpl in *. invert H.
    + eapply EvalAssignV; eauto.
      * specialize (H0 []); simpl in *.
        unfold not in *. intros. apply H8.
        rewrite H in *. invert H0.
        cases (reindexer2 []); cases (reindexer1 []); simpl in *;
          try lia; try discriminate; propositional.
      * rewrite <- H12.
        eapply eq_eval_Zexpr_Z.
        apply eq_zexpr_flatten_shape_index.
        2: eapply eq_Z_index_list_sym; apply H0.
        edestruct H0; eauto.
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
        apply eq_zexpr_flatten_shape_index.
        2: eapply eq_Z_index_list_sym; apply H0.
        edestruct H0; eauto.
Qed.

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

Lemma result_has_shape_for_sum :
  forall e v ,
    (forall sz : list nat,
        size_of e sz ->
        forall v : valuation,
        forall (sh : context) (ec : expr_context) (r : result),
        eval_expr sh v ec e r ->
        result_has_shape r sz) ->
    forall n sz r sh ec i lo hi loz hiz,
    size_of e sz ->
    eval_Zexpr_Z v lo = Some loz ->
    eval_Zexpr_Z v hi = Some hiz ->
    Z.of_nat n = (hiz - loz)%Z ->
    eval_expr sh v ec (Sum i lo hi e) r ->
    result_has_shape r sz.
Proof.
  intros ? ? ? ?.
  induct n; propositional.
  - invert H4.
    rewrite H1, H2 in *. invert H9. invert H10. lia.
    rewrite H1, H2 in *. invert H11. invert H13.
    eq_size_of.
    eapply result_has_shape_gen_pad.
  - invert H4.
    rewrite H1,H2 in *. invert H9. invert H10.
    pose proof H0.
    eapply result_has_shape_add_result. eassumption.
    2: { eapply IHn in H18. auto. eassumption. eassumption.
         simpl. rewrite H1. reflexivity.
         eauto. lia. } 
    eapply H. 2: eassumption. eassumption.
    eq_size_of. apply result_has_shape_gen_pad.
Qed.      
