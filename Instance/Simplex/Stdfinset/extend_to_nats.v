Require Import Category.Lib.
Require Import Theory.Category.
Require Import Instance.Coq.
Require Import Category.Theory.Functor.

Require Import Category.Instance.Simplex.NaturalNumberArithmetic.
Require Import Category.Instance.Simplex.FinType.
Require Import Category.Instance.Simplex.Stdfinset.Stdfinset.

Require Import ssreflect.
Require Import ssrfun.
Require Import ssrbool.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.tuple.
Require Import mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finfun.

Set Primitive Projections.
Set Universe Polymorphism.

Notation "''I_' n" := (ordinal n).

Open Scope nat_scope.

Definition extend_to_nats_mor (n m : nat) (f : 'I_m^n) : nat -> nat :=
  fun k => match @idP (k < n) with
           | @ReflectT _ p => val (f (@Sub _ _ _ k p))
           | _ => k - n + m
           end.

Definition extend_to_nats : @Functor stdfinset Coq.
Proof.
  refine(
 {|
   fobj := fun _ : obj[stdfinset] => nat;
   fmap x y f := extend_to_nats_mor x y f;
   fmap_respects x y := ltac:(congruence);
   fmap_id := _;
   fmap_comp := _;
   
 |}).
  {
    intro o.
    cbn delta iota beta.
    intro x.
    cbv delta [extend_to_nats_mor] beta.
    destruct idP.
    { rewrite ffunE. exact erefl. }
    { rewrite -addnABC;
        [ rewrite subnn; apply addn0
        | move/negP : n; rewrite -ltnNge; firstorder
        | done ].
    }
  }
  {
    intros x y z f g. unfold extend_to_nats_mor,
      equiv, homset, Coq. intro k.
    destruct idP. {
      cbv delta [val ordinal_subType stdfinset compose] beta iota.
      rewrite -> ffunE.
      destruct idP as [tt | ff];
        destruct idP as [ | ff1].
        { now do 2 (do 2 (apply f_equal); apply val_inj; simpl). }
        { now contradiction ff1. }
        { now contradiction ff. }
        { contradiction ff1. }
    }
    cbv delta [compose obj val ordinal_subType Sub] beta iota.
    destruct idP; destruct idP; try contradiction.
    { (have H : (~ (k - x + y < y)) by auto with arith);
      contradiction H. }
    { rewrite -(@addnBA (k - x) y y); [ rewrite subnn | auto].
      now rewrite addn0. }
  }
Defined.
