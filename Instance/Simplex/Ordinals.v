Require Import Category.Lib.
Require Import Category.Instance.Simplex.NaturalNumberArithmetic.

Require Import ssreflect.
Require Import ssrfun.
Require Import ssrbool.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finfun.
Require Import mathcomp.ssreflect.tuple.

(* Require Import Coq.Logic.FinFun. *)

Local Notation "''I_' n" := (ordinal n).
Open Scope nat_scope.


(* Definition least_st {n : nat} (P : pred 'I_n) : pred 'I_n := *)
(*     fun x => (P x && [forall y, P y ==> (y <= x)]). *)

Close Scope nat.
