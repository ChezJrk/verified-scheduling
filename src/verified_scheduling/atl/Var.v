Require Import String.
From Stdlib Require Import Lists.List.
Import ListNotations.

Notation var := string.
Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.

Infix "==v" := var_eq (no associativity, at level 50).

Fixpoint in_bool (l : list var) (v : var) : bool :=
  match l with
  | x::xs => orb (String.eqb x v) (in_bool xs v)
  | [] => false
  end.

Definition contains_substring (needle haystack : string) :=
  exists n, substring n (String.length needle) haystack = needle.

