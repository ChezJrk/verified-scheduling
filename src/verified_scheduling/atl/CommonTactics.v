From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import micromega.Lia.
From Coq Require Import micromega.Zify.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Coq Require Import ZArith.Zdiv.
From Coq Require Import ZArith.Int.
From Coq Require Import ZArith.Znat.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Classes.Morphisms.

Set Warnings "-deprecate-hint-without-locality,-deprecated".

Import ListNotations.

From ATL Require Import ATL Tactics Div Common.

Generalizable All Variables.

Ltac consistent_shape :=
  repeat
    match goal with
    | |- context[ length ((_ :: _) _[_])] =>erewrite get_length by eassumption
    | |- _ = ?e => is_evar e; reflexivity
    | |- forall _, _ => intros
    | |- consistent ?E _ =>
      match type of E with
      | R => apply all_R_consistent
      end
    | |- consistent (trunc_r _ _) _ =>
      eapply @consistent_trunc_r
    | |- consistent (truncr _ _) _ =>
      eapply @consistent_truncr
    | |- consistent (trunc_l _ _) _ =>
      eapply @consistent_trunc_l
    | |- consistent (truncl _ _) _ =>
      eapply @consistent_truncl
    | |- consistent (pad_r _ _) _ =>
      eapply @consistent_pad_r
    | |- consistent (pad_l _ _) _ =>
      eapply @consistent_pad_l             
    | |- consistent (flatten _) _  =>
      eapply @consistent_flatten
    | |- consistent (tile _ _) _ =>
      eapply @consistent_tile
    | |- consistent (transpose _) _ =>
      eapply @consistent_transpose
    | |- consistent (flatten_trunc _ _) _ =>
      eapply @consistent_flatten_trunc
    | |- consistent (_ <++> _) _ =>
      eapply @consistent_concat             
    | |- consistent (let_binding _ _) _ =>
      apply @consistent_let
    | |- consistent (|[ _ ]| _) _ =>
      apply @consistent_iverson
    | |- consistent (_ _[_]) _ =>
      eapply @consistent_get
    | |- consistent (GEN [ _ < Z.of_nat _ ] _) _ =>
      apply @consistent_gen
    | |- consistent (GEN [ _ < _ ] _) _ =>
      apply @consistent_gen'
    | |- consistent (GEN [ _ <= _ < _ ] _) _ =>
      apply @consistent_genr
    | |- consistent (SUM [ _ < _ ] _) _ =>
      apply @consistent_sum
    | |- consistent (SUM [ _ <= _ < _ ] _) _ =>
      apply @consistent_sumr            
    | |- consistent (_ <+> _) _ => eapply @consistent_bin
    | |- consistent _ _ => eassumption
    end.

(* Like repeat but fails if tactic doesn't succeed at least once *)

Tactic Notation "rep" tactic(t) := t; repeat t.

Ltac ttt e :=
    let t := fresh "t" in
    let t' := fresh "t'" in
    match e with
    | context[ (GEN [ _ < ?V ] _) _[?I] ] =>
      first [
          (assert (0 <= I)%Z as t by (auto + lia); clear t)
        |
        (destruct (0 <=? I)%Z eqn:t;
         [ apply Zle_bool_imp_le in t | apply Z.leb_gt in t])
        ];
      first [
          (assert (I < V)%Z as t' by (auto + lia); clear t')
        |
        (destruct (I <? V)%Z eqn:t';
         [ apply Z.ltb_lt in t' | apply Z.ltb_ge in t'])
        (*let t'_type := type of t' in try ttt t'_type*)
        ]
    | context[ ?V _[?I] ] =>
      first [
          (assert (0 <= I)%Z as t by (auto + lia); clear t)
        |
        (destruct (0 <=? I)%Z eqn:t;
         [ apply Zle_bool_imp_le in t | apply Z.leb_gt in t])
        ];
      first [
          (assert (I < Z.of_nat (length V))%Z as t' by (auto + lia); clear t')
        |
        (destruct (I <? Z.of_nat (length V))%Z eqn:t';
         [ apply Z.ltb_lt in t' | apply Z.ltb_ge in t'])
        ]            
    end.

Hint Extern 0 (0 < length (_ :: _)) => simpl; lia : crunch.
Hint Rewrite iverson_bin_distr @collapse_iverson : reds.
Hint Rewrite andb_false_r andb_false_l : reds.      

Ltac red_get :=
  repeat
    (match goal with
     | H : (?I < 0)%Z |- _ =>
       repeat rewrite (get_neg_null I) by auto with crunch;
       rep rewrite (@get_gen_neg_null _ _ _ I) by auto with crunch;
       assert (I < 0 /\ True)%Z by auto; clear H
     | H : (Z.of_nat ?V <= ?I)%Z |- _ =>
       repeat rewrite (get_gen_null I) by auto with crunch;        
       rep rewrite (get_znlt_null I) by auto with crunch;
       assert (Z.of_nat V <= I /\ True)%Z by auto; clear H
     | H : (0 <= ?I)%Z |- _ =>
       rep rewrite (@get_gen_some _ _ I) by (auto with crunch + (subst; auto with crunch));
       assert (0 <= I /\ True)%Z by auto; clear H
     | H : (?I < ?V)%Z |- _ =>
       rep rewrite (@get_gen_some _ _ I) by auto with crunch;
       assert (I < V /\ True)%Z by auto; clear H
     | H : (0 <= ?I)%Z, H' : (?I < ?V)%Z |- _ =>
       rep rewrite (@get_gen_some _ _ I) by auto with crunch;
       assert (0 <= I /\ True)%Z by auto; clear H;
       assert (I < V /\ True)%Z by auto; clear H'
     end;
     try match goal with |- context [ ((_ :: _) _[0]) ] =>
                         try rewrite get_0_cons
         end;
     try match goal with |- context [ length ((_ :: _) _[_]) ] =>
                         try erewrite get_length by eassumption
         end;     
     autorewrite with crunch);
  repeat
    match goal with
    | H : _ /\ True |- _ =>
      destruct H as [ ? triv ]; clear triv
    end.

Ltac reduce_all_get' :=
    match goal with
    | |- GEN [ _ < _ ] _ = _ =>
     try match goal with |- context [ length ((_ :: _) _[_]) ] =>
                         try erewrite get_length by eassumption
         end;     
      apply gen_eq_bound; intros;
      reduce_all_get'
    | |- SUM [ _ < _ ] _ = _ =>
     try match goal with |- context [ length ((_ :: _) _[_]) ] =>
                         try erewrite get_length by eassumption
         end;     
      apply sum_eq_bound; intros;
      reduce_all_get'
    | |- (|[ _ ]| _) = _ =>
     try match goal with |- context [ length ((_ :: _) _[_]) ] =>
                         try erewrite get_length by eassumption
         end;     
      apply iverson_weak;
      reduce_all_get'
    | |- ?l <+> ?r = _ =>
      try match goal with |- context [ length ((_ :: _) _[_]) ] =>
                          try erewrite get_length by eassumption
          end;
      let hypl := fresh "hyp" in
      let lefteq := fresh "lefteq" in
      let tl := type of l in
      let hypr := fresh "hyp" in
      let righteq := fresh "righteq" in
      evar (lefteq : tl);
      evar (righteq : tl);
      assert (l = ?lefteq) as hypl by (reduce_all_get');
      assert (r = ?righteq) as hypr by (reduce_all_get');
      rewrite hypl; subst lefteq;
      rewrite hypr; subst righteq
    | |- ?G =>
      first
        [ ttt G;
          [ red_get; autorewrite with reds crunch; first [ reflexivity | lia ]
          | red_get; autorewrite with reds crunch; first [ reflexivity | lia ]]
        | red_get; autorewrite with reds crunch; subst; reflexivity ]
    end.

Ltac reduce_all_gets :=
  etransitivity; [ rep reduce_all_get' | ]; lazy beta.

(* Rewrite Automation *)

Ltac hook s := idtac.

Ltac b_abstract val :=
  let v := fresh "v" in
  match goal with
  | [ |- context[ (|[ _ ]| ?A) = _ ] ] =>
    set (v:=A); pattern val in v; subst v
  | [ |- context[ ?A = _ ] ] =>
    set (v:=A); pattern val in v; subst v
  end.

Ltac protect :=
  match goal with
  | [ |- ?A ] => first [ has_evar A | eauto with crunch ]
  end.

Ltac lift_evar :=
  let Ht := fresh "Ht" in
  match goal with
  | [ |- _ = ?A ] => has_evar A;
                     remember A eqn:Ht
  end.

Ltac drop_evar :=
  repeat match goal with
  | [ H : ?A = ?B |- _ ] =>
    has_evar B;
    match goal with
    | [ |- _ = A ] => rewrite H
    end
         end.

Inductive DiveAction := RW | RWREV | LET | WRAPID.

Ltac bind pat :=
  lift_evar;
  let pat := open_constr:(pat) in
  let T :=  match type of pat with ?T -> _ => T end in
  let e := fresh "e" in
  evar (e : T);
  let ee := fresh "e" in
  remember ?e as ee;
  let appd := open_constr:(pat ?e) in
  let app := eval lazy beta in appd in
  match goal with |- context[?G] => unify app G; hook string:("success") end;
  let x := fresh "x" in
                               (*
  let idlet := constr:(tlet x := ee in x) in
  let applet' := constr:(pat idlet) in
  let applet := eval lazy beta in applet' in
      replace app with applet; subst ee; [ | try reflexivity ]; drop_evar.
                                *)
  let applet' := constr:(tlet x := ee in pat x) in
  let applet := eval lazy beta in applet' in
      replace app with applet; subst ee; [ | try reflexivity ]; drop_evar.

Ltac propnorm :=
  repeat match goal with
         | |- _ -> _ => intros
         | |- _ /\ _ => split
         | H : _ \/ _ |- _ => destruct H
         | H : _ /\ _ |- _ => destruct H
         end.

Ltac wrap_id rule V K' :=
  try lift_evar;
  let K := open_constr:(K') in
  let V' := open_constr:(V) in
  lazymatch type of K with
  | unit => erewrite <- (rule _ _ V')
  | _ => erewrite <- (rule _ _ V' K)
  end;
  autorewrite with crunch; propnorm; consistent_shape; try reflexivity;
  (solve
   [ try drop_evar; try reflexivity
   | consistent_shape; subst; eauto with crunch typeclass_instances
   | eauto with crunch typeclass_instances
   | autorewrite with crunch; eauto with crunch typeclass_instances ]).

Ltac use_rewrite rule pat n' i' v' :=
  try lift_evar;
  let n := open_constr:(n') in
  let i := open_constr:(i') in
  let v := open_constr:(v') in
  lazymatch type of v with
  | unit =>
    lazymatch type of n with
    | unit =>
      lazymatch type of i with
      | unit =>
        let opat := open_constr:(pat) in
        lazymatch type of opat with
        | unit => erewrite rule; hook string:("b erw")
        | _ => erewrite rule with (body:=opat); hook string:("erw body")
        end
      | _ =>
        let opat := open_constr:(pat) in
        lazymatch type of opat with
        | unit => erewrite rule with (I:=i); hook string:("b erw")
        | _ => erewrite rule with (body:=opat) (I:=i); hook string:("erw body")
        end
      end
    | _ =>
      lazymatch type of i with
      | unit =>
        let opat := open_constr:(pat) in
        lazymatch type of opat with
        | unit => erewrite rule with (N:=n); hook string:("b erw")
        | _ => erewrite rule with (body:=opat) (N:=n); hook string:("erw body")
        end
      | _ =>
        let opat := open_constr:(pat) in
        lazymatch type of opat with
        | unit => erewrite rule with (N:=n) (I:=i); hook string:("b erw")
        | _ => erewrite rule with (body:=opat) (N:=n) (I:=i);
               hook string:("erw body")
        end
      end    
    end
  | _ =>
    lazymatch type of n with
    | unit =>
      lazymatch type of i with
      | unit =>
        let opat := open_constr:(pat) in
        lazymatch type of opat with
        | unit => erewrite rule with (V:=v); hook string:("b erw")
        | _ => erewrite rule with (V:=v) (body:=opat); hook string:("erw body")
        end
      | _ =>
        let opat := open_constr:(pat) in
        lazymatch type of opat with
        | unit => erewrite rule with (I:=i); hook string:("b erw")
        | _ => erewrite rule with (body:=opat) (V:=v) (I:=i);
               hook string:("erw body")   end
      end
    | _ =>
      lazymatch type of i with
      | unit =>
        let opat := open_constr:(pat) in
        lazymatch type of opat with
        | unit => erewrite rule with (N:=n); hook string:("b erw")
        | _ => erewrite rule with (V:=v) (body:=opat) (N:=n);
               hook string:("erw body")
        end
      | _ =>
        let opat := open_constr:(pat) in
        lazymatch type of opat with
        | unit => erewrite rule with (V:=v) (N:=n) (I:=i);
                  hook string:("b erw")
        | _ => erewrite rule with (body:=opat) (N:=n) (I:=i) (V:=v);
               hook string:("erw body")
        end
      end    
    end
  end;    
  autorewrite with crunch; propnorm; consistent_shape;
  solve [ try drop_evar; try reflexivity
        | consistent_shape; subst; eauto with crunch typeclass_instances
        | eauto with crunch typeclass_instances
        | autorewrite with crunch; eauto with crunch typeclass_instances].

Ltac use_rewrite_rev rule pat n' i' :=
  try lift_evar;
  let n := open_constr:(n') in
  let i := open_constr:(i') in  
  lazymatch type of n with
  | unit =>
    lazymatch type of i with
    | unit =>
      let opat := open_constr:(pat) in
      lazymatch type of opat with
      | unit => erewrite <- rule; hook string:("b erw")
      | _ => erewrite <- rule with (body:=opat); hook string:("erw body")
      end
    | _ =>
      let opat := open_constr:(pat) in
      lazymatch type of opat with
      | unit => erewrite <- rule with (I:=i); hook string:("b erw")
      | _ => erewrite <- rule with (body:=opat) (I:=i); hook string:("erw body")   end
    end
  | _ =>
     lazymatch type of i with
    | unit =>
      let opat := open_constr:(pat) in
      lazymatch type of opat with
      | unit => erewrite <- rule with (N:=n); hook string:("b erw")
      | _ => erewrite <- rule with (body:=opat) (N:=n); hook string:("erw body")
      end
    | _ =>
      let opat := open_constr:(pat) in
      lazymatch type of opat with
      | unit => erewrite <- rule with (N:=n) (I:=i); hook string:("b erw")
      | _ => erewrite <- rule with (body:=opat) (N:=n) (I:=i);
             hook string:("erw body")
      end
    end    
  end;
    autorewrite with crunch; propnorm; consistent_shape;
  solve [ try drop_evar; try reflexivity
        | consistent_shape; subst; eauto with crunch typeclass_instances
        | eauto with crunch typeclass_instances
        | autorewrite with crunch; eauto with crunch typeclass_instances].

Ltac dispatch action rule pat N I V :=
  lazymatch action with
  | RW => use_rewrite rule pat N I V
  | RWREV => use_rewrite_rev rule pat N I
  | LET => bind pat
  | WRAPID => wrap_id rule pat N
  end.

Ltac dive_topdown action rule pat N I V :=
  dispatch action rule pat N I V +
  lazymatch goal with
  | |- let_binding ?x ?f = _ =>
    first [
    let tx := type of x in
    let ex := fresh "ex" in
    let Hx := fresh "Hx" in
    (evar (ex : tx);
    assert (x = ex) as Hx by
          (dive_topdown action rule pat N I V;
           try reflexivity;
           solve [ lazy beta; eta_red; autorewrite with crunch; protect ]);
    subst ex;
    rewrite Hx) |
    eapply let_extensionality;
    [ subst; consistent_shape | intros; dive_topdown action rule pat N I V ]]
  | |- flatten _ = _ =>
    apply flatten_eq;
    dive_topdown action rule pat N I V
  | |- transpose _ = _ =>
    apply transpose_eq;
    dive_topdown action rule pat N I V
  | |- tile _ _ = _ =>
    apply tile_eq;
    dive_topdown action rule pat N I V
  | |- flatten_trunc _ _ = _ =>
    apply flatten_trunc_eq;
    [ dive_topdown action rule pat N I V | ]
  | |- trunc_r _ _ = _ =>
    apply trunc_r_eq;
    dive_topdown action rule pat N I V
  | |- truncr _ _ = _ =>
    apply truncr_eq;
    dive_topdown action rule pat N I V
  | |- gen _ _ = _ =>
    hook string:("gen");
    let i := fresh "i" in
    apply gen_eq_bound; intros i ? ?;
    dive_topdown action rule pat N I V
  | |- genr _ _ _ = _ =>
    hook string:("genr");
    let i := fresh "i" in
    apply genr_eq_bound; intros;
    dive_topdown action rule pat N I V
  | |- sum _ _ = _ =>
    hook string:("sum");
    let i := fresh "i" in    
    apply sum_eq_bound; intros i ? ?;
    dive_topdown action rule pat N I V
  | |- get _ _ = _ =>
    hook string:("get");
    apply get_eq_index;
    dive_topdown action rule pat N I V
  | |- (_ * _)%R = _ =>
    hook string:("mul");
    first
    [
    (hook string:("left of mul");
     apply Rmult_eq_compat_r;
     dive_topdown action rule pat N I V)
    |
    (hook string:("right of mul");
     apply Rmult_eq_compat_l;
     dive_topdown action rule pat N I V) ]
  | |- (_ <+> _) = _ =>
    hook string:("bin");
    first
    [
    (hook string:("left of bin");
     apply bin_eq_l;
     dive_topdown action rule pat N I V)
    |
    (hook string:("right of bin");
     apply bin_eq_r;
     dive_topdown action rule pat N I V) ]
  | |- (_ <++> _) = _ =>
    hook string:("concat");
    first
    [
    (apply concat_eq_l;
     dive_topdown action rule pat N I V)
    |
    (apply concat_eq_r;
     dive_topdown action rule pat N I V) ]   
  | |- (|[ _ ]| _) = _ =>
    first
      [
    (hook string:("guard in");
     eapply iverson_in; propnorm; unbool_hyp;
     autorewrite with crunch;
     [ dive_topdown action rule pat N I V |
       subst; consistent_shape | subst; consistent_shape ]) ]
  end.

Ltac dive action rule pat N I V :=
  lazymatch goal with
  | |- let_binding ?x ?f = _ =>
    first [
        eapply let_extensionality;
    [ subst; consistent_shape | intros; dive action rule pat N I V ] |        
    let tx := type of x in
    let ex := fresh "ex" in
    let Hx := fresh "Hx" in
    (evar (ex : tx);
    assert (x = ex) as Hx by
          (dive action rule pat N I V;
           try reflexivity;
           solve [ lazy beta; eta_red; autorewrite with crunch; protect ]);
    subst ex;
    rewrite Hx) 
    ]
  | |- flatten _ = _ =>
    apply flatten_eq;
    dive action rule pat N I V
  | |- transpose _ = _ =>
    apply transpose_eq;
    dive action rule pat N I V
  | |- tile _ _ = _ =>
    apply tile_eq;
    dive action rule pat N I V
  | |- flatten_trunc _ _ = _ =>
    apply flatten_trunc_eq;
    [ dive action rule pat N I V | ]
  | |- trunc_r _ _ = _ =>
    apply trunc_r_eq;
    dive action rule pat N I V
  | |- truncr _ _ = _ =>
    apply truncr_eq;
    dive action rule pat N I V
  | |- gen _ _ = _ =>
    hook string:("gen");
    let i := fresh "i" in
    apply gen_eq_bound; intros i ? ?;
    dive action rule pat N I V
  | |- genr _ _ _ = _ =>
    hook string:("genr");
    apply genr_eq_bound; intros;
    dive action rule pat N I V
  | |- sum _ _ = _ =>
    hook string:("sum");
    let i := fresh "i" in    
    apply sum_eq_bound; intros i ? ?;
    dive action rule pat N I V
  | |- get _ _ = _ =>
    hook string:("get");
    apply get_eq_index;
    dive action rule pat N I V
  | |- (_ * _)%R = _ =>
    hook string:("mul");
    first
    [
    (hook string:("left of mul");
     apply Rmult_eq_compat_r;
     dive action rule pat N I V)
    |
    (hook string:("right of mul");
     apply Rmult_eq_compat_l;
     dive action rule pat N I V) ]
  | |- (_ <+> _) = _ =>
    hook string:("bin");
    first
    [
    (hook string:("left of bin");
     apply bin_eq_l;
     dive action rule pat N I V)
    |
    (hook string:("right of bin");
     apply bin_eq_r;
     dive action rule pat N I V) ]
  | |- (_ <++> _) = _ =>
    hook string:("concat");
    first
    [
    (apply concat_eq_l;
     dive action rule pat N I V)
    |
    (apply concat_eq_r;
     dive action rule pat N I V) ]    
  | |- (|[ _ ]| _) = _ =>
    first
      [
    (hook string:("guard in");
     eapply iverson_in; propnorm; unbool_hyp;
     autorewrite with crunch;
     [ dive action rule pat N I V | subst; consistent_shape | subst; consistent_shape ]) ]
  end +
  dispatch action rule pat N I V.

Ltac solve_for_index_rec i' :=
  match goal with
  | |- flatten_trunc _ _ = _ =>
    apply @flatten_trunc_eq
  | |- trunc_r _ _ = _ =>
    apply @trunc_r_eq
  | |- truncr _ _ = _ =>
    apply @truncr_eq
  | [ |- sum _ _ = _ ] => hook string:("sum");
    let i := fresh "i" in
    apply sum_eq_bound; intros i ? ?;
      try solve_for_index_rec i
  | [ |- gen _ _ = _ ] => hook string:("gen");
    let i := fresh "i" in
    apply gen_eq_bound; intros i ? ?;
      try solve_for_index_rec i
  | [ |- (|[ _ ]| _) = _ ] => hook string:("guard");
    try solve_for i';
    apply iverson_weak; try solve_for_index_rec i'
  | [ |- tlet _ := _ in _ = _ ] => hook string:("let");
    try solve_for i';
    try (apply tlet_eq_bound; solve_for_index_rec i');
    try (apply tlet_eq_body; solve_for_index_rec i')
  end.

Ltac solve_for_index := etransitivity;
                        [ solve_for_index_rec 0; reflexivity | ]; lazy beta.


Ltac reduce_guard p :=
  hook p;(
  (let H := fresh "H" in
  assert (H : p = true) by
       (unbool; try split;
        try rewrite Z.add_simpl_r;
         try rewrite Nat2Z.inj_mul; try apply mul_add_lt; try lia; protect);
         rewrite H; clear H; simpl andb)
      +
          (match p with (?p1 && ?p2) =>
                        try reduce_guard p1; try reduce_guard p2;
                        first [ rewrite (bool_imp_elim p1 p2) by
                                  (intros; unbool; lia) |
                try rewrite andb_true_l; try rewrite andb_true_r ] end)).


Ltac simpl_guard_rec :=
  match goal with
  | |- let_binding ?x ?f = _ =>
    let tx := type of x in
    let ex := fresh "ex" in
    let Hx := fresh "Hx" in
    try (evar (ex : tx);
    assert (x = ex) as Hx by
          (simpl_guard_rec;
           subst ex;
           try reflexivity;
           solve [ lazy beta; eta_red; autorewrite with crunch; protect ]);
    subst ex;
    rewrite Hx);
    try (eapply let_extensionality;
    [ consistent_shape |
      intros; simpl_guard_rec ])
  | [ |- flatten_trunc _ _ = _ ] =>
    eapply flatten_trunc_eq; [simpl_guard_rec | ]
  | [ |- trunc_r _ _ = _ ] =>
    eapply trunc_r_eq; simpl_guard_rec
  | [ |- truncr _ _ = _ ] =>
    eapply truncr_eq; simpl_guard_rec
  | [ |- tile _ _ = _ ] =>
    eapply tile_eq; simpl_guard_rec
  | [ |- transpose _ = _ ] =>
    apply transpose_eq; simpl_guard_rec
  | [ |- flatten _ = _ ] =>
    apply flatten_eq; simpl_guard_rec
  | [ |- sum _ _ = _ ] => hook string:("sum");
    apply sum_eq_bound; intros;
      simpl_guard_rec
  | [ |- gen _ _ = _ ] => hook string:("gen");
    apply gen_eq_bound; intros;
    simpl_guard_rec
  | [ |- genr _ _ _ = _ ] => hook string:("gen");
    apply genr_eq_bound; intros;
    simpl_guard_rec      
  | [ |- (|[ ?p ]| ?e) = _ ] => hook string:("guard");
    try reduce_guard p;
    try (lift_evar;
         repeat rewrite true_iverson;
         repeat rewrite andb_true_r;
         repeat rewrite andb_true_l;
         drop_evar);
    first [ (eapply iverson_in; 
    [ intros; unbool_hyp; simpl_guard_rec; try reflexivity |
      intros; unbool_hyp; split; consistent_shape ]) | simpl_guard_rec ]
  | [ |- (?a <++> ?b) = _ ] =>
    let t := type of a in
    let ae := fresh "ae" in
    let be := fresh "be" in
    let Ha := fresh "Ha" in
    let Hb := fresh "Hb" in
    evar (ae : t);
    evar (be : t);
    assert (a = ?ae) as Ha by (simpl_guard_rec; protect; reflexivity);
    try rewrite Ha;
    assert (b = ?be) as Hb by (simpl_guard_rec; protect; reflexivity);
    try rewrite Hb
  | [ |- (?a <+> ?b) = _ ] =>
    let t := type of a in
    let ae := fresh "ae" in
    let be := fresh "be" in
    let Ha := fresh "Ha" in
    let Hb := fresh "Hb" in
    evar (ae : t);
    evar (be : t);
    assert (a = ?ae) as Ha by (simpl_guard_rec; reflexivity);
    try rewrite Ha;
    assert (b = ?be) as Hb by (simpl_guard_rec; reflexivity);
    try rewrite Hb
  | |- _ = _ => reflexivity
  end.

Ltac simpl_guard := etransitivity;
                    [ simpl_guard_rec; try reflexivity; eauto with crunch |];
                    lazy beta.

Ltac rewrite_action action rule pat N I V :=
  etransitivity;
  [ hook string:("etra");
    first
      [ dive action rule pat N I V;
        hook string:("return from rw") |
        hook string:("in failed");
        try dispatch action rule pat N I V;
        hook string:("tried top")];
    try reflexivity;
    solve [
    lazy beta; eta_red; autorewrite with crunch; protect ] | ]; lazy beta.

Ltac rewrite_action_topdown action rule pat N I V :=
  etransitivity;
  [ hook string:("etra");
    first
      [ dive_topdown action rule pat N I V;
        hook string:("return from rw") |
        hook string:("in failed");
        try dispatch action rule pat N I V;
        hook string:("tried top")];
    try reflexivity;
    solve [
    lazy beta; eta_red; autorewrite with crunch; protect ] | ]; lazy beta.

Tactic Notation "lbind" uconstr(pat) :=
  rewrite_action LET tt pat tt tt tt.

Tactic Notation "rw^" open_constr(rule) :=
  rewrite_action_topdown RW rule tt tt tt tt.

Tactic Notation "rw^" open_constr(rule) "for" uconstr(body) :=
  rewrite_action_topdown RW rule body tt tt tt.

Tactic Notation "rw^" open_constr(rule) "at" uconstr(I) :=
  rewrite_action_topdown RW rule tt tt I tt.

Tactic Notation "rw^" open_constr(rule) "up to" uconstr(N) :=
  rewrite_action_topdown RW rule tt N tt tt.

Tactic Notation "rw^" open_constr(rule)
       "for" uconstr(body) "up to" uconstr(N) :=
  rewrite_action_topdown RW rule body N tt tt.

Tactic Notation "rw^" open_constr(rule)
       "for" uconstr(body) "at" uconstr(I) :=
  rewrite_action_topdown RW rule body tt I tt.

Tactic Notation "rw^" open_constr(rule)
       "up to" constr(N) "at" constr(I) :=
  rewrite_action_topdown RW rule tt N I tt.

Tactic Notation "rw^" open_constr(rule)
       "for" uconstr(body) "up to" uconstr(N) "at" uconstr(I) :=
  rewrite_action_topdown RW rule body N I tt.

Tactic Notation "rw^<-" open_constr(rule) :=
  rewrite_action_topdown RWREV rule tt tt tt tt.

Tactic Notation "rw^<-" open_constr(rule) "for" uconstr(body) :=
  rewrite_action_topdown RWREV rule body tt tt tt.

Tactic Notation "rw^<-" open_constr(rule) "at" uconstr(I) :=
  rewrite_action_topdown RWREV rule tt tt I tt.

Tactic Notation "rw^<-" open_constr(rule) "up to" uconstr(N) :=
  rewrite_action_topdown RWREV rule tt N tt tt.

Tactic Notation "rw^<-" open_constr(rule)
       "for" uconstr(body) "up to" uconstr(N) :=
  rewrite_action_topdown RWREV rule body N tt tt.

Tactic Notation "rw^<-" open_constr(rule)
       "for" uconstr(body) "at" uconstr(I) :=
  rewrite_action_topdown RWREV rule body tt I tt.

Tactic Notation "rw^<-" open_constr(rule)
       "up to" constr(N) "at" uconstr(I) :=
  rewrite_action_topdown RWREV rule tt N I tt.

Tactic Notation "rw^<-" open_constr(rule)
       "for" uconstr(body) "up to" uconstr(N) "at" uconstr(I) :=
  rewrite_action_topdown RWREV rule body N I tt.

Tactic Notation "rw" open_constr(rule) :=
  rewrite_action RW rule tt tt tt tt.

Tactic Notation "rw" open_constr(rule) "for" uconstr(body) :=
  rewrite_action RW rule body tt tt tt.

Tactic Notation "rw" open_constr(rule) "at" uconstr(I) :=
  rewrite_action RW rule tt tt I tt.

Tactic Notation "rw" open_constr(rule) "up to" uconstr(N) :=
  rewrite_action RW rule tt N tt tt.

Tactic Notation "rw" open_constr(rule)
       "for" uconstr(body) "up to" uconstr(N) :=
  rewrite_action RW rule body N tt tt.

Tactic Notation "rw" open_constr(rule)
       "for" uconstr(body) "at" uconstr(I) :=
  rewrite_action RW rule body tt I tt.

Tactic Notation "rw" open_constr(rule)
       "up to" uconstr(N) "at" uconstr(I) :=
  rewrite_action RW rule tt N I tt.

Tactic Notation "rw" open_constr(rule)
       "for" uconstr(body) "up to" uconstr(N) "at" uconstr(I) :=
  rewrite_action RW rule body N I tt.

Tactic Notation "rw<-" open_constr(rule) :=
  rewrite_action RWREV rule tt tt tt tt.

Tactic Notation "rw<-" open_constr(rule) "for" uconstr(body) :=
  rewrite_action RWREV rule body tt tt tt.

Tactic Notation "rw<-" open_constr(rule) "at" uconstr(I) :=
  rewrite_action RWREV rule tt tt I tt.

Tactic Notation "rw<-" open_constr(rule) "up to" uconstr(N) :=
  rewrite_action RWREV rule tt N tt tt.

Tactic Notation "rw<-" open_constr(rule)
       "for" uconstr(body) "upto" uconstr(N) :=
  rewrite_action RWREV rule body N tt tt.

Tactic Notation "rw<-" open_constr(rule)
       "for" uconstr(body) "at" uconstr(I) :=
  rewrite_action RWREV rule body tt I tt.

Tactic Notation "rw<-" open_constr(rule)
       "up to" uconstr(N) "at" uconstr(I) :=
  rewrite_action RWREV rule tt N I tt.

Tactic Notation "rw<-" open_constr(rule)
       "for" uconstr(body) "up to" uconstr(N) "at" uconstr(I) :=
  rewrite_action RWREV rule body N I tt.

Tactic Notation "wrapid^" open_constr(rule) "around" uconstr(body) :=
  rewrite_action_topdown WRAPID rule body constr:(tt) constr:(tt) tt.

Tactic Notation "wrapid^" open_constr(rule) "around" uconstr(body) "with"
  constr(K) :=
  rewrite_action_topdown WRAPID rule body K constr:(tt) tt.

Tactic Notation "wrapid" open_constr(rule) "around" uconstr(body) :=
  rewrite_action WRAPID rule body constr:(tt) constr:(tt) tt.

Tactic Notation "wrapid" open_constr(rule) "around" uconstr(body) "with"
  constr(K) :=
  rewrite_action WRAPID rule body K constr:(tt) tt.

Tactic Notation "inline" reference(rule) := unfold rule;
                                            rw^ @consistent_length;
                                            rw^ Z2Nat.id.

Tactic Notation "rw" open_constr(rule) "around" uconstr(V) :=
  rewrite_action RW rule tt tt tt V.

Tactic Notation "rw" open_constr(rule) "for" uconstr(body) "around" uconstr(V)
  :=
  rewrite_action RW rule body tt tt V.

Tactic Notation "rw" open_constr(rule) "at" uconstr(I) "around" uconstr(V)
  :=
  rewrite_action RW rule tt tt I V.

Tactic Notation "rw" open_constr(rule) "up to" uconstr(N) "around" uconstr(V)
  :=
  rewrite_action RW rule tt N tt V.

Tactic Notation "rw" open_constr(rule)
       "for" uconstr(body) "up to" uconstr(N) "around" uconstr(V) :=
  rewrite_action RW rule body N tt V.

Tactic Notation "rw" open_constr(rule)
       "for" uconstr(body) "at" uconstr(I) "around" uconstr(V) :=
  rewrite_action RW rule body tt I V.

Tactic Notation "rw" open_constr(rule)
       "up to" uconstr(N) "at" uconstr(I) "around" uconstr(V) :=
  rewrite_action RW rule tt N I V.

Tactic Notation "rw" open_constr(rule)
       "for" uconstr(body) "up to" uconstr(N) "at" uconstr(I) "around" uconstr(V)
  :=
  rewrite_action RW rule body N I V.

Tactic Notation "rw<-" open_constr(rule) "around" uconstr(V) :=
  rewrite_action RWREV rule tt tt tt V.

Tactic Notation "rw<-" open_constr(rule) "for" uconstr(body) "around" uconstr(V)
  :=
  rewrite_action RWREV rule body tt tt V.

Tactic Notation "rw<-" open_constr(rule) "at" uconstr(I) "around" uconstr(V) :=
  rewrite_action RWREV rule tt tt I V.

Tactic Notation "rw<-" open_constr(rule) "up to" uconstr(N) "around" uconstr(V)
  :=
  rewrite_action RWREV rule tt N tt V.

Tactic Notation "rw<-" open_constr(rule)
       "for" uconstr(body) "upto" uconstr(N) "around" uconstr(V) :=
  rewrite_action RWREV rule body N tt V.

Tactic Notation "rw<-" open_constr(rule)
       "for" uconstr(body) "at" uconstr(I) "around" uconstr(V) :=
  rewrite_action RWREV rule body tt I V.

Tactic Notation "rw<-" open_constr(rule)
       "up to" uconstr(N) "at" uconstr(I) "around" uconstr(V) :=
  rewrite_action RWREV rule tt N I V.

Tactic Notation "rw<-" open_constr(rule)
       "for" uconstr(body) "up to" uconstr(N) "at" uconstr(I) "around" uconstr(V) :=
  rewrite_action RWREV rule body N I V.
