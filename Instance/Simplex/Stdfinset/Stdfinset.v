Require Import Category.Lib.
Require Import Theory.Category.

Require Import Category.Instance.Simplex.NaturalNumberArithmetic.
Require Import Category.Instance.Simplex.FinType.

Require Import ssreflect.
Require Import ssrfun.
Require Import ssrbool.

Require Import mathcomp.ssreflect.seq.
Set Warnings "-notation-overridden".
Require Import mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.fintype.

Require Import mathcomp.ssreflect.tuple.
Require Import mathcomp.ssreflect.finfun.

Set Primitive Projections.
Set Universe Polymorphism.

Notation "''I_' n" := (ordinal n).

(** In this file we define the category whose objects are "standard finite sets" [[n] = { 0, ... n-1}] and whose morphisms are all functions between them. We define the coface and codegeneracy maps δi, σj in this category, but we do not prove they are monotonic. *)

Local Open Scope type_scope.

Program Definition stdfinset : Category :=
  {|
    obj     := nat;
    hom     := fun n m => ('I_m)^n;
    homset  := fun _ _ => {| equiv := eq |}; 
    Category.id      := fun n => [ffun k => k];
    compose := fun _ _ _ f g => [ffun x => f (g x)]
  |}.

(** Right identity law - The main lemma of this proof is function extensionality [ffunP]. [ffunE] simplifies [ [ffun x => t] a] to [t[x/a]]; presumably the reason this needs to be explicitly called as lemma is to prevent term explosion through unnecessary simplification. *)
Next Obligation. apply/ffunP; intro i; rewrite ! ffunE; done. Qed.
(* Left identity law, same proof as before *)
Next Obligation. apply/ffunP; intro i; rewrite ! ffunE; done. Qed.
(* Associativity of composition law, same proof as before *)
Next Obligation. apply/ffunP; intro i; rewrite ! ffunE; done. Qed.
(* Associativity of composition law, same proof as before *)
Next Obligation. apply/ffunP; intro i; rewrite ! ffunE; done. Qed.
Open Scope nat_scope.

Proposition predn_subproof (n : nat) (i : 'I_(n.+2)) : predn i < n.+1.
Proof.
  destruct i as [ival ibd]; destruct ival; done.
Qed.

Definition ord_predn {n : nat} (i : 'I_(n.+2)) : 'I_(n.+1)
  := Sub (predn i) (predn_subproof n i).

Definition ord_upcast {n : nat} (i : 'I_n) : 'I_n.+1 :=
  widen_ord (leqnSn n) i.
(* Proof. *)
(*   destruct i as [ival ibd]; exists ival; auto with arith. *)
(* Defined. *)

Local Remove Hints ltnW : core.

Ltac stdfinset_simpl :=
  do ! (match goal with
        | [ |- @eq (ordinal _) _ _] => apply: val_inj; simpl
        | [ |- eqfun _ _ ] => unfold eqfun
        | [ |- @eq (@finfun_of _ _ _) _ _ ] => apply: eq_ffun
        | [ |- _ ] => fail_if_unchanged ltac:(rewrite ! ffunE)
        | [ |- _ ] => fail_if_unchanged simpl
         end).

Local Create HintDb stdfinset discriminated.
Local Hint Extern 0 => stdfinset_simpl : stdfinset.
Local Hint Extern 5 => (fail_if_unchanged ltac:(simpl)) : simplex.

Lemma injective_neq (A B : Type) (f : A -> B) (p : injective f) (x y : A)
  : x ≠ y -> (f x) ≠ f y.
Proof.
  intros neq fs; apply neq. by apply p in fs.
Qed.

Lemma ord_neq_nat_neq (n : nat) (x y : 'I_n)
  : x ≠ y -> nat_of_ord x ≠ nat_of_ord y.
Proof.
  apply injective_neq; exact: val_inj.
Qed.

(* Reduce hypotheses/goals on ordinal arithmetic to goals on natural_number arithmetic *)
Ltac ord_to_arith :=
match goal with
| [ |- context[ @eq_op (Finite.eqType (exp_finIndexType _)) ?X ?Y ]] =>
    rewrite - (inj_eq val_inj X Y)
| [ H : is_true (@eq_op (ordinal_eqType _ ) ?X ?Y) |- _ ] =>
    rewrite -(@inj_eq _ _ val val_inj) in H
| [ H : not (@eq (Equality.sort (Finite.eqType (ordinal_finType _))) _ _ ) |- _]
    => apply ord_neq_nat_neq in H
end.

Local Hint Extern 1 => ord_to_arith : arith.

Proposition surjective_card {n m : nat} (f : 'I_m^n) (p : surjective f)
  : m <= n.
Proof.
  rewrite -(card_ord n).
  cut (m = #|image f 'I_n|);
    [ intro RW; rewrite RW ; exact: leq_image_card |].
  rewrite -{1}(size_enum_ord m); symmetry; apply eq_cardT.
  intro x; unfold surjective in p;
    move/(rwP forallP):p => p;specialize p with x; by rewrite p.
Qed.

Definition not_surjective_cd_nonzero {n : nat} (f : 'I_0^n) : surjective f.
Proof.
  apply (rwP (surjectiveP f)); intros [yval ybd]; discriminate.
Qed.
