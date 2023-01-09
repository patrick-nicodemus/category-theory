Require Import Category.Lib.
Require Import Theory.Category.
Require Import StrictProp.
Require Import ssreflect.
Require Import ssrfun.
Require Import ssrbool.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrnat.

Definition sis_true (b : bool) : SProp :=
  match b with
  | true => sUnit
  | false => sEmpty
  end.

Proposition is_true_to_sis_true (b : bool) : b -> sis_true b.
Proof.
  intro H.
  unfold is_true in H.
  symmetry in H.
  destruct H.
  exact stt.
Qed.

Proposition sis_true_to_is_true (b : bool) : sis_true b -> b.
Proof.
  intro H; destruct b; [ reflexivity | contradiction H ].
Qed.

Local Open Scope nat.

Record DNat := {
    DNatfn : nat -> nat;
    afflin : forall n : nat,
      sis_true (DNatfn n == DNatfn 0 + n)
  }.

Search compose.
Definition addnD (n m : DNat) : DNat.
Proof.
  destruct n as [nf a], m as [mf b].
  exists (fun x => nf (mf x)).
  intro k.
  apply is_true_to_sis_true.
  specialize b with k; apply sis_true_to_is_true in b.
  move/eqP : b -> .
  assert (H := sis_true_to_is_true _ (a (mf 0))).
  move/eqP : H ->.
  specialize a with (mf 0 + k).
  apply sis_true_to_is_true in a.
  apply/eqP; move/eqP : a ->.
  now rewrite addnA.
Defined.

Proposition addn_assoc (a b c : DNat) : addnD (addnD a b) c = addnD a (addnD b c).
Proof.
  reflexivity.
Defined.  

Definition zeroD : DNat.
Proof.
  exists (fun z => z).
  intro; now apply is_true_to_sis_true.
Defined.

Proposition zeroD_left_unit (a : DNat) : addnD a zeroD = a.
Proof.
  reflexivity.
Defined.

Proposition zeroD_right_unit (a : DNat) : addnD zeroD a = a.
Proof.
  reflexivity.
Defined.
