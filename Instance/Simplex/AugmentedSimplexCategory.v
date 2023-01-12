(* Require Import Category.Lib. *)
(* Require Import Category.Theory.Category. *)

Require Import Arith.
From Hammer Require Import Hammer Tactics.

Local Open Scope nat.

Proposition ex_pair (A B : Type) (P : A -> Prop) (Q : B -> Prop)
  : (exists x : A, P x) -> (exists y : B, Q y) ->
    exists a : A * B, P (fst a ) /\ Q (snd a).
Proof.
  intros [x pfx] [y pfy].
  exists (x, y).
  hauto.
Qed.

Goal
  forall (x : nat * nat),
  exists y : nat * nat, (fst y) = snd x /\ (snd y) = fst x.
Proof.
  Abort.


