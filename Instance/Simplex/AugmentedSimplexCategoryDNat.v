Require Import Category.Lib.
Require Import Theory.Category.

Require Import Category.Instance.Simplex.NaturalNumberArithmetic.
Require Import Category.Instance.Simplex.DNat.
(* Require Import Category.Instance.Simplex.Ordinals. *)

Require Import ssreflect.
Require Import ssrfun.
Require Import ssrbool.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finfun.
Require Import mathcomp.ssreflect.tuple.

Require Import Coq.Logic.FinFun.

From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
Set Primitive Projections.
Set Universe Polymorphism.

Definition DNat_reify : DNat -> nat := fun x => DNatfn x 0.

Coercion DNat_reify : DNat >-> nat.
           
Section stdfinsetD.
Program Definition stdfinsetD : Category :=
  {|
    obj     := DNat;
    hom     := fun n m => ('I_m)^n;
    homset  := fun _ _ => {| equiv := eq |}; 
    Category.id      := fun n => [ffun k => k];
    compose := fun _ _ _ f g => [ffun x => f (g x)]
  |}.
Next Obligation.
  Set Hammer Debug.
  hammer.
