From Coq Require Import Ascii String Arith.
Require Import Coq.Strings.String.

Definition nat_to_ascii (n : nat) : ascii :=
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

Fixpoint nat_to_string' (time n : nat) (acc : string) : string :=
  let acc' := String (nat_to_ascii (n mod 10)) acc in
  match time with
  | 0 => acc'
  | S time' =>
    match n / 10 with
    | 0 => acc'
    | n' => nat_to_string' time' n' acc'
    end
  end.

Definition nat_to_string (n : nat) : string :=
    nat_to_string' n n "".


