From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Reals.Reals. Import Rdefinitions. Import RIneq.
From Coq Require Import ZArith.Int. Import Znat BinInt.Z.
From Coq Require Import Setoids.Setoid.
Import ListNotations.

From ATL Require Import ATL.

Set Warnings "-omega-is-deprecated,-deprecated".

Ltac zomega :=
  match goal with
  | |- context[ (Z.of_nat _ < _)%Z ] => zify; omega
  | |- context[ Z.neg _ ] => zify; omega
  | |- context[ Pos.to_nat _ ] => zify; omega
  | |- context[ Z.to_nat (Z.pos _) ] => simpl; zify; omega
  | |- context[ Z.pos _ ] => zify; omega
  | |- context[ Pos.of_succ_nat _ ] => zify; omega
  | |- context[ Z.to_nat < _ ] => zify; omega
  | |- context[ (Z.succ (Z.of_nat _)) ] => zify; omega
  | |- context[ (Z.of_nat (S _)) ] => zify; omega
  | |- (_ < Z.of_nat _)%Z => zify; omega
  end.

Ltac eta_reduce_all_private h := repeat change (fun x => ?h x) with h.

Ltac eta_red := eta_reduce_all_private idtac.

(* Takes a boolean conjunction in the goal and rewrites it right associated *)
Ltac andb_right :=
  repeat match goal with
         | [ |- context[(_ && _) && _] ] => rewrite <- andb_assoc
         end.

Lemma bool_prop : forall a b, a = b <-> (a = true <-> b = true).
Proof.
  destruct a; destruct b; split; intros; try (split; intros); auto; destruct H;
    assert (true = true) by reflexivity; intuition.
Qed.
Open Scope Z_scope.

Ltac unbool_hyp :=
  repeat match goal with                                             
         | [ H : (_ <? _ = true)%nat |- _ ] => apply Nat.ltb_lt in H
         | [ H : (_ <? _ = false)%nat |- _ ] => apply Nat.ltb_nlt in H
         | [ H : (_ =? _ = true)%nat |- _ ] => apply beq_nat_true in H
         | [ H : (_ =? _ = false)%nat |- _ ] => apply beq_nat_false in H

         | [ H : (true = _) |- _ ] => symmetry in H
         | [ H : (false = _) |- _ ] => symmetry in H
         | [ H : (_ =? _ = true)   |- _ ] => apply eqb_eq in H
         | [ H : (_ =? _ = false)  |- _ ] => apply eqb_neq in H
         | [ H : (_ <=? _ = true)  |- _ ] => apply Zle_is_le_bool in H
         | [ H : (_ <=? _ = false) |- _ ] => apply leb_gt in H
         | [ H : (_ <? _ = true)   |- _ ] => apply ltb_lt in H
         | [ H : (_ <? _ = false)   |- _ ] => apply ltb_ge in H
         | [ H : (_ <=? _ = false) |- _ ] => apply ltb_nlt in H

         | [ H : (_ && _ = true) |- _ ] => apply andb_true_iff in H;
                                           destruct H; unbool_hyp
         | [ H : (_ && _ = false) |- _ ] => apply andb_false_iff in H;
                                            destruct H; unbool_hyp
  end.

Ltac unbool_goal :=
  repeat match goal with        
         | [ |- context[ (true =? true) ]] => fail 1
         | [ |- context[ (false =? false) ]] => fail 1
         | [ |- context[ (false =? true) ]] => fail 1
         | [ |- context[ (true =? false) ]] => fail 1

         | [ |- context[(_ =? _ = true)] ] => rewrite eqb_eq
         | [ |- context[(_ =? _ = false)] ] => rewrite eqb_neq
         | [ |- context[(_ <=? _ = true)] ] => rewrite leb_le
         | [ |- context[(_ <=? _ = false)] ] => rewrite leb_gt
         | [ |- context[(_ <? _ = true)] ] => rewrite ltb_lt
         | [ |- context[(_ <? _ = false)] ] => rewrite ltb_ge
         | [ |- context[(_ <=? _ = false)] ] => rewrite ltb_nlt

         | [ |- context[(_ && _)]] => rewrite andb_true_iff
         | [ |- ?A = ?B ] => rewrite (bool_prop A B)
         end.

Ltac unbool := unbool_hyp; unbool_goal.

Example ex1 : forall a b c, ((a =? b) && (b =? c) = (c =? a) && (b =? a)).
Proof. intros. unbool. omega. Qed.

Ltac app_in_crush H H' := apply H in H';
        try assumption; try reflexivity; try omega; try ring.

Ltac contra_crush := try (simpl in *;
  repeat match goal with
         | [ H : (_ < 0)%nat |- _ ] => inversion H
         | [ H : _ < 0 |- _ ] => now inversion H
         | [ H : _ <= 0 |- _ ] => now inversion H
         | [ H : ~ ?A |- _] =>
           (assert A by (try assumption; try omega; try ring)); contradiction
		 | [ H : 0 <= Z.neg ?A |- _ ] => 
				 specialize (Zlt_neg_0 A); intros; contradiction
		 | [ H : 0 < Z.neg _ |- _ ] => now inversion H
		 | [ H : Z.pos _ < Z.neg _ |- _ ] => now inversion H
         end).

Ltac peel_hyp :=
  repeat match goal with
         | [ H : ?A -> _ |- _ ] => assert (H' : A)
                                     by (try assumption; try reflexivity;
                                         try omega; try zomega; try ring);
                                   apply H in H'; clear H; rename H' into H
         end.

Close Scope Z_scope.

Ltac analyze_bool := try lazy beta;
  repeat match goal with
         | [ |- context[ (?A =? ?B)%Z ] ] =>
           let v := fresh "H" in
           destruct (A =? B)%Z eqn:v; subst; unbool_hyp;
           try omega; try ring; try auto with crunch
         | [ |- context[ (?A <? ?B)%Z ] ] =>
           let v := fresh "H" in
           destruct (A <? B)%Z eqn:v; subst; unbool_hyp;
           try omega; try ring; try auto with crunch
         | [ |- context[ (?A <=? ?B)%Z ] ] =>
           let v := fresh "H" in
           destruct (A <=? B)%Z eqn:v; subst; unbool_hyp;
           try omega; try ring; try auto with crunch
  end.

Ltac solve_for var :=
  match goal with
  | [ |- context[(?A =? ?B)%Z]] => 
    let ev := fresh "ev" in
    let H := fresh "H" in
    let H' := fresh "H" in
    let e := fresh "e" in
    evar (ev : Z);
    assert (H' : (A =? B)%Z = (var =? ?ev)%Z) by
        (remember (var =? ?ev)%Z eqn:e;         
         unbool_goal;
         rewrite <- Z.sub_move_0_r;
         split; intros H;
         [ rewrite e;
           unbool_goal;
           ring_simplify in H;
           match type of H with             
           | context [ (_ - var)%Z ] => apply (Z.add_cancel_r _ _ var) in H
           | context [ (_ + var)%Z ] => apply (Z.sub_cancel_r _ _ var) in H
           | context [ (var + ?a)%Z ] => apply (Z.sub_cancel_r _ _ a) in H
           | context [ (var - ?a)%Z ] => apply (Z.add_cancel_r _ _ a) in H
           | _ => apply (Z.add_cancel_r _ _ var)%Z in H
           end;
           ring_simplify in H;
           (apply H + (symmetry; apply H)) |
           rewrite e in H; unbool_hyp; omega]);
    rewrite H'
  end.

Ltac reschedule := intros; eexists; intros;
                   repeat
                     match goal with
                     | H : consistent ?V ?S |- _ =>
                       let x := fresh "x" in
                       let xs := fresh "xs" in
                       destruct V as [| x xs]; inversion H;
                       assert (consistent (x::xs) S /\ True) by auto;
                       clear H
                     end;
                   repeat
                     match goal with
                     | H : _ /\ True |- _ =>
                       destruct H as [ ? triv ]; clear triv
                     end;
                   try autounfold with examples.

Ltac done := reflexivity.
