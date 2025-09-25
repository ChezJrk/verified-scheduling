From Stdlib Require Import Ascii String.
From Stdlib Require Import ZArith.Zdiv.
From Stdlib Require Import ZArith.Int.
From Stdlib Require Import ZArith.Znat.

From Stdlib Require Import Strings.String.

Open Scope Z_scope.

Definition int_to_ascii (n : Z) : ascii :=
  match n with
  | 0 => "0"
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | 4 => "4"
  | 5 => "5"
  | 6 => "6"
  | 7 => "7"
  | 8 => "8"
  | _ => "9"
  end.

Fixpoint int_to_string' (time: nat) (n : Z) (acc : string) : string :=
  let acc' := String (int_to_ascii (Stdlib.ZArith.BinIntDef.Z.modulo n 10)) acc in
  match time with
  | 0%nat => acc'
  | S time' =>
    match n / 10 with
    | 0 => acc'
    | n' => int_to_string' time' n' acc'
    end
  end.

Definition int_to_string (n : Z) : string :=
  match n with
  | Zneg _ => "-" ++(int_to_string' (Z.to_nat (- n)) (-n) "")
  | _ => int_to_string' (Z.to_nat n) n ""
  end.

Close Scope Z_scope.
