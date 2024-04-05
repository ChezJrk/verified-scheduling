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

From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics TensorAdd
     Zexpr Bexpr Array Range Sexpr Result ListMisc Meshgrid VarGeneration
     Constant ATLDeep Pad Reify Convolution Blur Common CommonTactics Matmul
     GatherScatter Im2col.

Open Scope string_scope.

Hint Constructors size_of.
Hint Unfold eval_Zexpr_Z_total.
Arguments sub : simpl nomatch.

Lemma all_nat_nonneg : forall x, 0 <= x. lia. Qed.

Fixpoint Bexpr_to_Prop v b :=
  match b with
  | And b1 b2 => Bexpr_to_Prop v b1 /\ Bexpr_to_Prop v b2
  | Lt x1 x2 => match eval_Zexpr_Z v x1, eval_Zexpr_Z v x2 with
                | Some x1z, Some x2z => (x1z < x2z)%Z
                | _,_ => False
                end
  | Le x1 x2 => match eval_Zexpr_Z v x1, eval_Zexpr_Z v x2 with
                | Some x1z, Some x2z => (x1z <= x2z)%Z
                | _,_ => False
                end
  | Eq x1 x2 => match eval_Zexpr_Z v x1, eval_Zexpr_Z v x2 with
                | Some x1z, Some x2z => (x1z = x2z)%Z
                | _,_ => False
                end
  end.

Fixpoint vars_of_Bexpr b :=
  match b with
  | And b1 b2 => vars_of_Bexpr b1 ++/ vars_of_Bexpr b2
  | Lt x1 x2 => vars_of_Zexpr x1 ++/ vars_of_Zexpr x2
  | Le x1 x2 => vars_of_Zexpr x1 ++/ vars_of_Zexpr x2
  | Eq x1 x2 => vars_of_Zexpr x1 ++/ vars_of_Zexpr x2
  end.

Lemma vars_of_Zexpr_eval_Zexpr : forall b v,
    constant (vars_of_Zexpr b) \subseteq dom v ->
    exists bb, eval_Zexpr v b bb.
Proof.
  induct b; intros; simpl in *; repeat rewrite constant_app_no_dups in *;
    try assert ( constant (vars_of_Zexpr b1) \subseteq dom v) by sets;
    try assert ( constant (vars_of_Zexpr b2) \subseteq dom v) by sets;
    try eapply IHb1 in H0; try eapply IHb2 in H1; invs;
    try now (eexists; econstructor; eauto).
  assert (x \in dom v). sets.
  eapply dom_lookup_Some in H0. invs.
  eexists. eauto.
Qed.

Lemma vars_of_Bexpr_eval_Bexpr : forall b v,
    constant (vars_of_Bexpr b) \subseteq dom v ->
    exists bb, eval_Bexpr v b bb.
Proof.
  induct b; intros; simpl in *; rewrite constant_app_no_dups in *;
    try assert ( constant (vars_of_Bexpr b1) \subseteq dom v) by sets;
    try assert ( constant (vars_of_Bexpr b2) \subseteq dom v) by sets;
    try assert ( constant (vars_of_Zexpr a) \subseteq dom v) by sets;
    try assert ( constant (vars_of_Zexpr b) \subseteq dom v) by sets;
    try eapply IHb1 in H0; try eapply IHb2 in H1; invs;
    try now (eexists; econstructor; eauto).
  all: eapply vars_of_Zexpr_eval_Zexpr in H0,H1; invs.
  eexists. econstructor; eauto.
  eexists. econstructor; eauto.
  eexists. econstructor; eauto.
Qed.

Lemma Bexpr_to_Prop_eval_Bexpr_false : forall b v,
    ~ Bexpr_to_Prop v b ->
    constant (vars_of_Bexpr b) \subseteq dom v ->
    eval_Bexpr v b false.
Proof.
  induct b; propositional.
  - simpl in *. rewrite constant_app_no_dups in H0.
    try assert ( constant (vars_of_Bexpr b1) \subseteq dom v) by sets;
      try assert ( constant (vars_of_Bexpr b2) \subseteq dom v) by sets.
    eapply vars_of_Bexpr_eval_Bexpr in H1,H2. invs.
    eapply Classical_Prop.not_and_or in H. invert H.
    + eapply IHb1 in H1. eq_eval_B.
      replace false with (false && x) by auto.
      econstructor; eauto.
      sets.
    + eapply IHb2 in H1. eq_eval_B.
      replace false with (x0 && false) by (rewrite andb_false_r;auto).
      econstructor; eauto.
      sets.
  - simpl in *.
    rewrite constant_app_no_dups in H0.
    try assert ( constant (vars_of_Zexpr a) \subseteq dom v) by sets;
      try assert ( constant (vars_of_Zexpr b) \subseteq dom v) by sets.
    eapply vars_of_Zexpr_eval_Zexpr in H1,H2. invs.
    eapply eval_Zexpr_Z_eval_Zexpr in H2,H3. rewrite H2,H3 in *.
    assert (x <= x0)%Z by lia.
    eapply Z.ltb_ge in H1. rewrite <- H1.
    econstructor; eapply eval_Zexpr_Z_eval_Zexpr; eauto.
  - simpl in *.
    rewrite constant_app_no_dups in H0.
    try assert ( constant (vars_of_Zexpr a) \subseteq dom v) by sets;
      try assert ( constant (vars_of_Zexpr b) \subseteq dom v) by sets.
    eapply vars_of_Zexpr_eval_Zexpr in H1,H2. invs.
    eapply eval_Zexpr_Z_eval_Zexpr in H2,H3. rewrite H2,H3 in *.
    assert (x < x0)%Z by lia.
    eapply Z.leb_gt in H1. rewrite <- H1.
    econstructor; eapply eval_Zexpr_Z_eval_Zexpr; eauto.
  - simpl in *.
    rewrite constant_app_no_dups in H0.
    try assert ( constant (vars_of_Zexpr a) \subseteq dom v) by sets;
      try assert ( constant (vars_of_Zexpr b) \subseteq dom v) by sets.
    eapply vars_of_Zexpr_eval_Zexpr in H1,H2. invs.
    eapply eval_Zexpr_Z_eval_Zexpr in H2,H3. rewrite H2,H3 in *.
    assert (x0 <> x)%Z by lia.
    eapply Z.eqb_neq in H1. rewrite <- H1.
    econstructor; eapply eval_Zexpr_Z_eval_Zexpr; eauto.
Qed.    

Ltac is_unspec_nat n :=
  match n with
  | 0 => idtac
  | _ => is_evar n
  end.

Ltac is_unspec_pad_ty p :=
  first [ is_evar p |
          match p with
          | PadCons ?k ?l ?p1 ?r ?p2 ?c =>
              is_unspec_nat k; is_unspec_nat l;
              is_unspec_nat r; is_unspec_nat c;
              is_unspec_pad_ty p1;
              is_unspec_pad_ty p2
          | PadNil ?b => is_evar b
          end
    ].

Ltac list_eq :=
  repeat
    match goal with
    | |- map _ _ = map _ _ => simpl
    | |- (?x::?xs)%list = (?y::?ys)%list =>
        f_equal; try now (autounfold; simpl; lia)
    | |- [] = [] => reflexivity
    end.

Lemma mod_div_0 : forall n k,
    0 < k ->
    (n mod k) / k = 0.
Proof. intros. rewrite div_small. lia. eapply Nat.mod_upper_bound. lia. Qed.

Lemma instantiate_0 : forall x,
    0 + 0 <= x - 0.
Proof. lia. Qed.
Hint Resolve instantiate_0 : crunch.

Ltac arith :=
  autounfold; simpl;
  repeat match goal with
         | |- context[min 0 _] => rewrite min_0_l
         | |- context[min _ 0] => rewrite min_0_r
         | |- context[ (0 / _)%nat ] => rewrite div_0_l
         | |- context[ (0 / _)%Z ] => rewrite Z.div_0_l
         | |- context[ (0 //n _)%nat ] => rewrite div_ceil_n_0
         | |- context[ (_ - 0)%Z ] => rewrite Z.sub_0_r
         | |- context[ (_ + 0)%nat ] => rewrite add_0_r
         | |- context[ (0 + _)%nat ] => rewrite add_0_l
         | |- context[ ((_ mod ?k) / ?k)%nat ] => rewrite mod_div_0
         | |- ?a = ?b => first [ reflexivity | lia ]
         | |- context[ match _ with _ => _ end ] => simpl
         | |- context[min ?x ?y ] => is_evar x; is_evar y; rewrite min_id
         | |- ?G => first [ has_evar G | lia ]
         end.

Ltac outer_dim e :=
  let outer_dim := constr:(match (sizeof e) with
                            | n::_ => eval_Zexpr_Z_total $0 n
                            | _ => 0%Z
                            end) in
  let outer_dim := eval unfold eval_Zexpr_Z_total in outer_dim in
    let outer_dim := eval simpl in outer_dim in
      outer_dim.

Ltac inner_dim e :=
  let inner_dim := constr:(match (sizeof e) with
                           | _::d::_ => eval_Zexpr_Z_total $0 d
                           | _ => 0%Z
                           end) in
  let inner_dim := eval unfold eval_Zexpr_Z_total in inner_dim in
    let inner_dim := eval simpl in inner_dim in
      inner_dim.
Ltac infer_pad left right :=
  match goal with
  | |- has_pad _ _ _ (Scalar _) _ =>
      eapply HasPadScalarNotPad
  | |- has_pad _ _ _ (Split _ _) _ =>
      infer_split left right 
  | |- has_pad _ _ _ (Truncr ?k _) _ =>
      infer_truncr left right 0%nat
  | |- has_pad _ _ _ (Truncl ?k _) _ =>
      infer_truncl left right 0%nat
  | |- has_pad _ _ _ (Padr ?k _) _ =>
      infer_padr left right
  | |- has_pad _ _ _ (Padl ?k _) _ =>
      infer_padl left right
  | |- has_pad _ _ _ (Gen ?i ?lo ?hi ?e) _ =>
      infer_gen left right
  | |- has_pad _ _ _ (Lbind ?x ?e1 ?e2) _ =>
      eapply HasPadLbind;
      [ solve [ infer_pad 0%Z 0%Z ] |
        repeat (econstructor; autounfold; try intros; simpl );
        try list_eq; eauto |
        solve [ infer_pad left right ] ]
  | |- has_pad ?ctx ?v ?g (Guard ?p ?e) _ =>
      first [ solve [ eapply HasPadGuardFalse;
                      [ eapply Bexpr_to_Prop_eval_Bexpr_false;
                        [ autounfold; simpl;
                          repeat first
                                 [ rewrite lookup_add_ne by inversion 1 |
                                   rewrite lookup_add_eq by auto ]; lia |
                          simpl; repeat rewrite dom_add; rewrite dom_empty; simpl; sets ] |
                repeat (econstructor; eauto) |
                reflexivity ] ] |
              eapply HasPadGuardTrue; infer_pad left right ]
  | |- has_pad ?ctx ?v ?g (Concat ?e1 ?e2) _ =>
      infer_concat left right
  | |- has_pad ?ctx ?v ?g (Sum ?i ?lo ?hi ?e) _ =>
      first [ eapply HasPadSumEmpty;
              [ repeat (econstructor; eauto) |
                autounfold; simpl; lia |
                reflexivity ] |
              eapply HasPadSum;
              [ autounfold; simpl; intros; infer_pad left right |
                autounfold; simpl; lia ] ]
  | |- has_pad ?ctx ?v ?g (Flatten ?e) _ =>
      infer_flatten left right 0%nat
  | |- has_pad _ _ _ (Transpose _) _ =>
      infer_transpose 0%Z 0%Z 0%nat 0%nat
  end with infer_padr left right :=
    match goal with
    | |- has_pad _ _ _ (Padr ?k ?e) _ =>
        let outer_dim := outer_dim e in
        let right' := constr:(Z.max (right-eval_Zexpr_Z_total $0 k)%Z 0%Z) in
        let right' := eval unfold eval_Zexpr_Z_total in right' in
          let right' := eval simpl in right' in
            first [ solve [ assert (0 < outer_dim)%Z as Hcheck by lia;
                            clear Hcheck;
                            eapply HasPadPadr;
                            [ autounfold; simpl; intros; try lia;
                                      infer_pad left right' |
                              repeat (econstructor; eauto) |
                              arith |
                              arith |
                              arith |
                              arith ] ] |
                    eapply HasPadPadrEmpty; [ repeat (econstructor; eauto) |
                                              infer_pad 0%Z 0%Z |
                                              arith ] ]
  end with infer_padl left right :=
    match goal with
    | |- has_pad _ _ _ (Padl ?k ?e) _ =>
        let outer_dim := outer_dim e in
        let left' := constr:(Z.max (left-eval_Zexpr_Z_total $0 k)%Z 0%Z) in
        let left' := eval unfold eval_Zexpr_Z_total in left' in
          let left' := eval simpl in left' in
            first [ solve [ assert (0 < outer_dim)%Z as Hcheck by lia;
                            clear Hcheck;
                            eapply HasPadPadl;
                            [ autounfold; simpl; intros; try lia;
                                      infer_pad left' right |
                              repeat (econstructor; eauto) |
                              arith |
                              arith |
                              arith |
                              arith ] ] |
                    eapply HasPadPadlEmpty; [ repeat (econstructor; eauto) |
                                              infer_pad 0%Z 0%Z |
                                              arith ] ]
end with infer_truncr left right offset :=
    match goal with
    | |- has_pad _ _ _ (Truncr ?k ?e) _ =>
        let outer_dim := outer_dim e in
        let right' := constr:((right+ eval_Zexpr_Z_total $0 k)%Z) in
        let right' := eval unfold eval_Zexpr_Z_total in right' in
          let right' := eval simpl in right' in
            first [ solve [ eapply HasPadTruncr
                    with (y:= Z.to_nat right' + offset);
                            [ infer_pad left right' |
                              arith |
                              arith ] ]
            ]
  end with infer_truncl left right offset :=
    match goal with
    | |- has_pad _ _ _ (Truncl ?k ?e) _ =>
        let outer_dim := outer_dim e in
        let left' := constr:((left+ eval_Zexpr_Z_total $0 k)%Z) in
        let left' := eval unfold eval_Zexpr_Z_total in left' in
          let left' := eval simpl in left' in
            first [ solve [ eapply HasPadTruncl
                    with (x:= Z.to_nat left' + offset);
                            [ infer_pad left' right |
                              arith |
                              arith ] ] |
                    assert (Z.to_nat left' + offset < Z.to_nat outer_dim) as
                    Hcheck by (arith; lia); clear Hcheck;
                    infer_truncl left right constr:(offset+1)
            ]
  end with infer_concat left right :=
    match goal with
    | |- has_pad _ _ _ (Concat _ _) _ =>
        first [ solve [ eapply HasPadConcat with
                    (x:=0) (y:=0) (a:=0) (b:=0)
                    (l1:=0) (r1:=0) (l1:=0) (r2:=0);
        [ repeat (econstructor; autounfold; try intros; simpl );
          try list_eq; eauto |
          repeat (econstructor; autounfold; try intros; simpl );
          try list_eq; eauto |
          autounfold; simpl; intros; try lia;
                  infer_pad 0%Z 0%Z |
          autounfold; simpl; intros; try lia;
                  infer_pad 0%Z 0%Z |
          arith |
          arith |
          arith |
          arith ] ] |
          solve [ eapply HasPadConcat;
        [ repeat (econstructor; autounfold; try intros; simpl );
          try list_eq; eauto |
          repeat (econstructor; autounfold; try intros; simpl );
          try list_eq; eauto |
          autounfold; simpl; intros; try lia;
                  infer_pad 0%Z 0%Z |
          autounfold; simpl; intros; try lia;
                  infer_pad 0%Z 0%Z |
          arith |
          arith |
          arith |
          arith ] ] ]
  end with infer_gen left right :=
    match goal with
    | |- has_pad _ _ _ (Gen ?i ?lo ?hi _) (PadCons ?kk ?l ?p1 ?r ?p2 ?cc) =>
        let kkk := match goal with
                   | |- _ => let _ :=
                               (* if it's an evar let's instantiate 
                                  it as left *)
                               match goal with _ => is_evar kk end in
                             constr:(Z.to_nat left)
                   | |- _ => (* if it's not an evar leave it as is *)
                       kk
                   end in
        let ccc := match goal with
                   | |- _ => let _ :=
                               match goal with _ => is_evar cc end in
                             constr:(Z.to_nat right)
                   | |- _ => cc
                   end in
        let lll := match goal with
                   | _ => let _ :=
                            (* if it's an evar *)
                            match goal with _ => is_evar l end in
                          match goal with
                          | _ =>
                              (* and there is no target structure
                               for   the padding within it *)
                              let _ :=
                                match goal with _ => is_unspec_pad_ty p1 end
                              in
                              (* we likely don't care about it *)
                              constr:(0)
                          | _ =>
                              (* if there is padding structure try
                                 and give it all of the padding *)
                              (* TODO: RETURN TO LOOP THROUGH SLICE
                                 POSSIBILITIES *)
                              constr:(Z.to_nat
                                        (eval_Zexpr_Z_total $0 hi-
                                          eval_Zexpr_Z_total $0 lo)%Z
                                      -kkk)
                        end
                   (* if it's not an evar it is what it is *)
                   | _ => l
                   end in
        let rrr := match goal with
                   | _ => let _ :=
                          match goal with _ => is_evar r end in
                          constr:(Z.to_nat
                                    (eval_Zexpr_Z_total $0 hi -
                                      eval_Zexpr_Z_total $0 lo)%Z
                                  -kkk -ccc -lll)
                   (* if it's not an evar it is what it is *)
                   | _ => r
                   end in
        (* idtac kkk; idtac lll; idtac rrr; idtac ccc; *)
        first [ solve [ eapply HasPadGen with
                (k:=kkk) (c:=ccc) (ll:=lll) (rr:=rrr);
                        [ arith |
                          arith |
                          arith |
                          repeat (econstructor; autounfold; try intros;simpl );
                          try list_eq; eauto |
                          autounfold; simpl; intros; try lia; infer_pad 0%Z 0%Z |
                          autounfold; simpl; intros; try lia; infer_pad 0%Z 0%Z |
                          autounfold;simpl;intros;
                          first [ lia|infer_pad 0%Z 0%Z ] |
                          try (autounfold; simpl;
                               try first [ lia | reflexivity]) ] ] |
                solve [ eapply HasPadGen
                    with (k:=kkk) (c:=ccc) (ll:=rrr) (rr:=lll);
                        [ arith |
                          arith |
                          arith |
                          repeat (econstructor; autounfold; try intros; simpl );
                          try list_eq; eauto |
                          autounfold; simpl; intros; try lia; infer_pad 0%Z 0%Z |
                          autounfold; simpl; intros; try lia; infer_pad 0%Z 0%Z |
                          autounfold;simpl;intros;first [ lia|infer_pad 0%Z 0%Z ] |
                          try (autounfold; simpl; try first [ lia | reflexivity]) ]
                ] ]
    | |- has_pad _ _ _ (Gen ?i ?lo ?hi ?e) _ =>
        (* if it doesn't have any pad type structure all bets are off *)
        let kk:= constr:(Z.to_nat left) in
        let cc:= constr:(Z.to_nat right) in
        let lll := constr:(Z.to_nat (eval_Zexpr_Z_total $0 hi-
                                       eval_Zexpr_Z_total $0 lo)%Z -kk) in
        let rrr := constr:(Z.to_nat (eval_Zexpr_Z_total $0 hi -
                                       eval_Zexpr_Z_total $0 lo)%Z
                                  -kk -cc -lll) in
        first [ solve [ eapply HasPadGen with
                (k:=kk) (c:=cc) (ll:=lll) (rr:=rrr);
                        [ arith |
                          arith |
                          arith |
                          repeat (econstructor; autounfold; try intros;simpl );
                          try list_eq; eauto |
                          autounfold; simpl; intros; try lia; infer_pad 0%Z 0%Z |
                          autounfold; simpl; intros; try lia; infer_pad 0%Z 0%Z |
                          autounfold;simpl;intros;
                          first [ lia|infer_pad 0%Z 0%Z ] |
                          try (autounfold; simpl;
                               try first [ lia | reflexivity]) ] ] |
                solve [ eapply HasPadGen
                    with (k:=kk) (c:=cc) (ll:=rrr) (rr:=lll);
                        [ arith |
                          arith |
                          arith |
                          repeat (econstructor; autounfold; try intros; simpl );
                          try list_eq; eauto |
                          autounfold; simpl; intros; try lia; infer_pad 0%Z 0%Z |
                          autounfold; simpl; intros; try lia; infer_pad 0%Z 0%Z |
                          autounfold;simpl;intros;first [ lia|infer_pad 0%Z 0%Z ] |
                          try (autounfold; simpl; try first [ lia | reflexivity]) ]
                ] ]
    end
with infer_flatten left right offset :=
  match goal with
  | |- has_pad _ _ _ (Flatten ?e) (PadCons ?xx ?ll ?p1 ?rr ?p4 ?yy) =>
      let inner_dim := inner_dim e in
      let outer_dim := outer_dim e in
      let xxx := match goal with
                 | |- _ => let _ := match goal with _ => is_evar xx end in
                           constr:(Z.to_nat left)
                 | |- _ => xx
                 end in
      let yyy := match goal with
                 | |- _ => let _ := match goal with _ => is_evar yy end in
                           constr:(Z.to_nat right)
                 | |- _ => yy
                 end in
      let aa := constr:(xxx mod Z.to_nat inner_dim) in
      let bb := constr:(yyy mod Z.to_nat inner_dim) in
      let x_ := constr:(xxx / Z.to_nat inner_dim) in
      let y_ := constr:(yyy / Z.to_nat inner_dim) in
      let ll := offset in
      (* idtac x_; idtac ll; idtac aa; idtac bb; idtac y_; *)
      first [ solve [ eapply HasPadFlattenStrong with (b:=bb) (a:=aa)
                                                      (x:=x_) (y:=y_) (l:=ll)
                      (l1:=0) (r1:=0) (c:=0) (l2:=0) (r2:=0) (d:=0);
              [ infer_pad x_ y_  |
                repeat econstructor; eauto |
                arith | arith | arith | arith | arith | arith | arith |
                arith | arith ] ] |
              solve [ eapply HasPadFlattenStrong with (b:=bb) (a:=aa)
                                                      (x:=x_) (y:=y_) (l:=ll)
                      (l1:=0) (r1:=0) (c:=0);
              [ infer_pad x_ y_  |
                repeat econstructor; eauto |
                arith | arith | arith | arith | arith | arith | arith |
                arith | arith ] ] |
              solve [ eapply HasPadFlattenStrong with (b:=bb) (a:=aa)
                                              (x:=x_) (y:=y_) (l:=ll);
              [ infer_pad x_ y_  |
                repeat econstructor; eauto |
                arith | arith | arith | arith | arith | arith | arith |
                arith | arith ] ] |
              solve [ eapply HasPadFlattenStrong with (b:=bb) (a:=aa)
                                              (x:=x_) (y:=y_);
              [ infer_pad x_ y_ |
                repeat econstructor; eauto |
                arith | arith | arith | arith | arith | arith | arith |
                arith | arith ] ] |
              assert (offset < Z.to_nat outer_dim - x_ - y_)
              as Hcheck by (arith; lia); clear Hcheck;
              solve [ infer_flatten left right constr:(offset+1) ] 
        ]
end with infer_transpose left right offset1 offset2 :=
    match goal with
    | |- has_pad _ _ _ (Transpose ?e) ?pi =>
          is_unspec_pad_ty pi;
          solve [ eapply HasPadTransposeWeak;
                  [ infer_pad 0%Z 0%Z |
                    repeat econstructor |
                    arith |
                    arith |
                    arith |
                    arith ]
            ]
    | |- has_pad _ _ _ (Transpose ?e)
                 (PadCons ?ll_ ?lll_ ?pi1 ?rrr_ ?pi2 ?rr_) =>
        let outer_dim := outer_dim e in
        let inner_dim := inner_dim e in
        let ll' := match goal with
                   | |- _ => let _ := match goal with _ => is_evar ll_ end in
                             constr:(Z.to_nat left)
                   | |- _ => ll_
                   end in
        let rr' := match goal with
                   | |- _ => let _ := match goal with _ => is_evar rr_ end in
                             constr:(Z.to_nat right)
                   | |- _ => rr_
                   end in
        let lll':= constr:(Z.to_nat inner_dim - ll' - rr' - offset1) in
        let rrr' := offset1 in
        let l' := constr:(Z.to_nat outer_dim - offset2) in
        let r' := offset2 in          
        idtac ll'; idtac rr'; idtac lll'; idtac rrr';
        first [ solve [ eapply HasPadTransposeStrong
                with (x:=0) (y:=0) (ll:=ll') (rr:=rr')
                     (lll:=lll') (rrr:=rrr') (l:=l') (r:=r');
                        cycle 1;
                        [ repeat (econstructor; eauto) |
                          arith |
                          arith |
                          arith |
                          arith |
                          arith |
              autounfold; simpl; intros; arith; try lia; infer_pad 0%Z 0%Z ] ] |
                assert (offset2 + 1 <= Z.to_nat outer_dim - ll' - rr')
                as Hcheck by (arith; try lia) ; clear Hcheck;
                infer_transpose left right offset1 constr:((offset2 + 1)%nat)
          ]
    end with infer_split left right :=
      match goal with
      | |- has_pad _ _ _ (Split _ _) _ =>
          eapply HasPadSplit;
          [ infer_pad 0%Z 0%Z |
            repeat econstructor |
            arith |
            arith |
            arith |
            arith ]
      end.

Goal forall v, Common.truncl 3 (GEN [ i < 10 ] (|[ 1 <? i ]| v _[i+4])) = [].
Proof.
  let ast := R in
  assert (exists pad, has_pad $0 $0 $0 ast pad).
  { eexists. Fail infer_pad 0%Z 0%Z.
Abort. 

Goal forall v, Common.truncl 3 (GEN [ i < 10 ] (v _[i])) = [].
Proof.
  let ast := R in
  assert (exists pad, has_pad $0 $0 $0 ast pad).
  { eexists. Fail infer_pad 0%Z 0%Z.
Abort.

Goal forall n m (v : list (list R)),
    2 < n ->
    2 < m ->
    consistent v (n,(m,tt)) ->
    blurimmediate_partition n m v = @nil _.
Proof.
  let ast := R in
  assert (exists pad, has_pad $0 $0 $0 ast pad).
  { eexists. infer_pad 0%Z 0%Z. }
Abort.

Goal forall (A B C D : nat) (m1 m2 : (list (list (list (list R))))),
         consistent m1 (8,(8,(8,(8,tt)))) ->
         consistent m2 (8,(8,(8,(8,tt)))) ->         
         add_split 8 8 8 8 m1 m2 =
           add 8 8 8 8 m1 m2.
Proof.
  autounfold.
  let ast := R in
  assert (exists pad, has_pad $0 $0 $0 ast pad).
  { eexists. infer_pad 0%Z 0%Z. }
Abort.  

Goal forall B C K W RR (w : list (list (list R))) (x : list (list (list R))),
    (0 < B)%Z ->
    (0 < C)%Z ->
    (0 < K)%Z ->
    (0 < W)%Z ->
    (0 < RR)%Z ->
    im2col B K W C RR w x =
      im2col_lifted B K W C RR w x.
Proof.
  let ast := R in
  assert (exists pad, has_pad $0 $0 $0 ast pad).
  { eexists. infer_pad 0%Z 0%Z. }
Abort.    

Goal forall B C K W RR (w : list (list (list R))) (x : list (list (list R))),
    (0 < B)%Z ->
    (0 < C)%Z ->
    (0 < K)%Z ->
    (0 < W)%Z ->
    (0 < RR)%Z ->
    im2col_lifted B K W C RR w x = im2col B K W C RR w x.
Proof.
  let ast := R in
  assert (exists pad, has_pad $0 $0 $0 ast pad).
  { eexists. infer_pad 0%Z 0%Z. }
Abort.    

Goal forall (W C B K : Z) (x w : list (list (list R))) (RR : Z) (a b :nat),
    consistent w (a,(b,(Z.to_nat RR, tt))) ->
          (0 < C)%Z ->
          (0 < W)%Z ->
          (W <=C)%Z ->
          (0 < K)%Z ->
          (0 < RR)%Z ->
          (0 < B)%Z ->
          scatter_full B K W C x w = gather_full W C B K x w RR.
Proof.
  intros. unfold scatter_full.
  let ast := R in
  assert (exists pad, has_pad $0 $0 $0 ast pad).
  { eexists. infer_pad 0%Z 0%Z. }
Abort.

Goal forall (W C B K : Z) (x w : list (list (list R))) (RR : Z) (a b :nat),
    consistent w (a,(b,(Z.to_nat RR, tt))) ->
          (0 < C)%Z ->
          (0 < W)%Z ->
          (W <=C)%Z ->
          (0 < K)%Z ->
          (0 < RR)%Z ->
          (0 < B)%Z ->
          gather_full W C B K x w RR = scatter_full B K W C x w.
Proof.
  intros. unfold gather_full.
  let ast := R in
  assert (exists pad, has_pad $0 $0 $0 ast pad).
  { eexists. infer_pad 0%Z 0%Z. }
Abort.
  
Goal forall (A B C : nat) (m1 m2 : (list (list R))) (k : Z),
    (0 < k)%Z ->
    0 < A ->
    0 < B ->
    0 < C ->
    consistent m1 (64,(64,tt)) ->
    consistent m2 (64,(64,tt)) ->    
    matmul_tiled_split 64 64 64 m1 m2 4 =
      matmul 64 64 64 m1 m2.
Proof.
  autounfold with examples.
  let ast := R in
  assert (exists pad, has_pad $0 $0 $0 ast pad).
  { eexists. infer_pad 0%Z 0%Z. }
Abort.

Goal forall n m (l : list (list R)),
    0 < n ->
    0 < m ->
    consistent l (n,(m,tt)) ->
    blur_tiles_guarded l 64 64 4 4 = @nil _.
Proof. 
  autounfold. unfold blur_tiles_guarded.
  let ast := R in
  assert (exists pad, has_pad $0 $0 $0 ast pad).
  eexists.
  { infer_pad 0%Z 0%Z. (* Takes ~10m to run *) }
Abort.

Goal forall n m (v : list (list R)),
    2 < n ->
    2 < m ->
    consistent v (n,(m,tt)) ->
    blurimmediate_isolate n m v = @nil _.
Proof.
  let ast := R in
  assert (exists pad, has_pad $0 $0 $0 ast pad).
  { eexists. infer_concat 0%Z 0%Z. }
Abort.

Goal forall N M (v : list (list R)),
    2 < N ->
    2 < M ->
    consistent v (N,(M,tt)) ->
    blurtwostage_partition N M v = @nil _.
Proof.
  let ast := R in
  assert (exists pad, has_pad $0 $0 $0 ast pad).
  { eexists. infer_pad 0%Z 0%Z. }
Abort.

Goal forall v, Common.truncl 3 (GEN [ i < 10 ] (|[ 2 <? i ]| v _[i+4])) = [].
Proof.
  let ast := R in
  assert (exists pad, has_pad $0 $0 $0 ast pad).
  { eexists. infer_pad 0%Z 0%Z. }
Abort.

Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->
    blurimmediate v M N = blurtwostage N M v.
Proof.
  let ast := R in
  assert (exists pad, has_pad $0 $0 $0 ast pad).
  { eexists. infer_pad 0%Z 0%Z. }
Abort.
 
Goal forall N M (v : list (list R)),
    0 < N ->
    0 < M ->
    consistent v (N,(M,tt)) ->
    blurtwostage N M v = blurimmediate v M N.
Proof.
  let ast := R in
  assert (exists pad, has_pad $0 $0 $0 ast pad).
  { eexists. infer_pad 0%Z 0%Z. }
Abort.

Goal forall n m (l : list (list R)),
    0 < n ->
    0 < m ->
    consistent l (n,(m,tt)) ->
    fusion_no_boundary n m l 
    = @nil _.
Proof.
  let ast := R in
  assert (exists pad, has_pad $0 $0 $0 ast pad).
  { eexists. infer_pad 0%Z 0%Z. }
Abort.

Goal forall W R0 (x w : list R),    
    consistent w (Z.to_nat R0, tt) ->
    consistent x (Z.to_nat R0, tt) ->
    (0 < W)%Z ->
    (Z.of_nat (length x) < W)%Z ->
    GatherScatter.gather W x w = @nil _.
Proof.
  let ast := R in
  assert (exists pad, has_pad $0 $0 $0 ast pad).
  { eexists. infer_pad 0%Z 0%Z. }
Abort.      

Goal forall W R0 (x w : list R),    
    consistent w (Z.to_nat R0, tt) ->
    consistent x (Z.to_nat R0, tt) ->
    (0 < W)%Z ->
    (Z.of_nat (length x) < W)%Z ->
    GatherScatter.scatter W x w = @nil _.
Proof.
  let ast := R in
  assert (exists pad, has_pad $0 $0 $0 ast pad).
  { eexists. infer_pad 0%Z 0%Z. }
Abort.

Goal forall (A B C D : nat) (m1 m2 : (list (list (list (list R))))),
         0 < A ->
         0 < B ->
         0 < C ->
         0 < D ->
         consistent m1 (A,(B,(C,(D,tt)))) ->
         consistent m2 (A,(B,(C,(D,tt)))) ->
         add (Z.of_nat A) (Z.of_nat B) (Z.of_nat C) (Z.of_nat D) m1 m2 =
           add_split A B C D m1 m2.
Proof.
  autounfold.
  let ast := R in
  assert (exists pad, has_pad $0 $0 $0 ast pad).
  { eexists. infer_pad 0%Z 0%Z. }
Abort.  

Goal forall (A B C : nat) (m1 m2 : (list (list R))) (k : Z),
    (0 < k)%Z ->
    0 < A ->
    0 < B ->
    0 < C ->
    consistent m1 (A,(B,tt)) ->
    consistent m2 (B,(C,tt)) ->
    matmul (Z.of_nat A) (Z.of_nat B) (Z.of_nat C) m1 m2 =
      matmul_tiled A B C m1 m2 k.
Proof.
  autounfold with examples.
  let ast := R in
  assert (exists pad, has_pad $0 $0 $0 ast pad).
  eexists. { infer_pad 0%Z 0%Z. }
Abort.

Goal forall (A B C : nat) (m1 m2 : (list (list R))) (k : Z),
    (0 < k)%Z ->
    0 < A ->
    0 < B ->
    0 < C ->
    consistent m1 (64,(64,tt)) ->
    consistent m2 (64,(64,tt)) ->    
    matmul_tiled 64 64 64 m1 m2 4 =
      matmul 64 64 64 m1 m2.
Proof.
  autounfold with examples.
  let ast := R in
  assert (exists pad, has_pad $0 $0 $0 ast pad).
  eexists. { infer_pad 0%Z 0%Z. }
Abort.

