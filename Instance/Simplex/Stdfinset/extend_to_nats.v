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
Check @Sub.

Definition extend_to_nats_mor (n m : nat) (f : 'I_m^n) : nat -> nat.
Proof.
    intro k.
    destruct (@idP (k < n)) as [i |].
    {  
        exact (val (f (@Sub _ _ _ k i))).
    }
    {
        exact (k - n + m).
    }
Defined.
Print extend_to_nats_mor.

Definition extend_to_nats : @Functor stdfinset Coq.
Proof.
    unshelve eapply Build_Functor.
    {
        exact (fun _ => nat).
    }
    {
        exact (fun x y f => extend_to_nats_mor x y f).
    }
    { 
        intros x y f g t ; simpl in t; now destruct t.
    }
    {
        simpl; intro n.
        unfold extend_to_nats_mor.
        debug auto.
        intro.
        destruct idP.
        {
            now rewrite ffunE.
        }
        {
            Search (?x - ?n + ?n).
            rewrite subnK; [ done | ].
            auto with arith.
            done.
            Set Printing All.
        }
    }