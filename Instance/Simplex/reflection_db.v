(* Reflection database. *)

From Ltac2 Require Import Ltac2.

(* Want to design a database such that I can query it with a term like *)
(*  "i < j" and it returns an element of type  \  *)
(*    reflect (i < j)%nat (i < j) *)
