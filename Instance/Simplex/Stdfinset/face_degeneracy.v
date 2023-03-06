Require Import Category.Lib.
Require Import Theory.Category.

Require Import Category.Instance.Simplex.NaturalNumberArithmetic.
Require Import Category.Instance.Simplex.FinType.
Require Import Category.Instance.Simplex.Stdfinset.Stdfinset.

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

Definition δ_stdfinset {n : nat} (i : 'I_(n.+1))
  : @hom stdfinset n n.+1 := [ffun j : 'I_n => lift i j].

Lemma σ_subproof (n : nat) (i : 'I_(n.+1)) (j : 'I_(n.+2))
  : unbump i j < n.+1. 
Proof.
  rewrite ltnS -leq_bump. unfold bump.
  destruct i as [ival ibd]; simpl.
  rewrite -[ival <= n]ltnS ibd -ltnS; unfold addn; simpl.
  by (destruct j).
Qed.

Definition σ_stdfinset {n : nat} (i : 'I_(n.+1))
  : @hom stdfinset n.+2 n.+1 :=
  [ffun j : 'I_(n.+2) => Ordinal (σ_subproof n i j)].

Proposition predn_subproof (n : nat) (i : 'I_(n.+2)) : predn i < n.+1.
Proof.
  destruct i as [ival ibd]; destruct ival; done.
Qed.

Definition ord_predn {n : nat} (i : 'I_(n.+2)) : 'I_(n.+1)
  := Sub (predn i) (predn_subproof n i).

Definition ord_upcast {n : nat} (i : 'I_n) : 'I_n.+1 :=
  widen_ord (leqnSn n) i.

  (* Definitions of the face and degeneracy maps *)
Local Notation δ := δ_stdfinset.

(*   δ_j ∘ δ_i = δ_i ∘ δ_(j-1)   ;  i < j *)
Proposition δi_δj_stdfinset {n : nat}
  (i : 'I_(n.+1)) (j : 'I_(n.+2)) 
  : i < j ->
    @compose stdfinset n n.+1 n.+2 (δ j) (δ i) =
      @compose stdfinset n n.+1 n.+2
        (δ (ord_upcast i)) (δ (ord_predn j)).
Proof.
  destruct i as [ival ibd], j as [jval jbd];
    intro ineq; simpl in ineq.
  stdfinset_simpl; intros [xval xbd]; stdfinset_simpl.
  exact: δi_δj_nat.
Qed.

(*   σ_j ∘ σ_i = σ_i ∘ σ_(j+1)   ;  i <= j *)
Local Notation σ := σ_stdfinset.
Proposition σi_σj {n : nat} (i j : 'I_(n.+1))
  : i <= j ->
    @compose stdfinset n.+3 n.+2 n.+1 (σ j) (σ (ord_upcast i)) =
    @compose stdfinset n.+3 n.+2 n.+1 (σ i) (σ (lift ord0 j)).
Proof.
  stdfinset_simpl.
  destruct i as [ival ibd], j as [jval jbd];
    intro ineq; simpl in ineq; stdfinset_simpl.
  intros [xval xbd]. stdfinset_simpl.
  unfold bump. arith_simpl.
  exact: σi_σj_nat.
Qed.

Proposition δi_σj_1 {n : nat} (i : 'I_n.+2) (j : 'I_n.+2) 
  : (i < j) ->
    @compose stdfinset n.+2 n.+3 n.+2 (σ j) (δ (ord_upcast i)) =
      @compose stdfinset n.+2 n.+1 n.+2 (δ i) (σ (ord_predn j)).
Proof.
  intro ineq; destruct i as [ival ibd], j as [jval jbd]; simpl in ineq.
  stdfinset_simpl. intros [xval xbd].
  stdfinset_simpl.
  exact: δi_σj_iltj_nat.
Qed.

Proposition σi_δi {n : nat} (i : 'I_n.+1)
  : @compose stdfinset n.+1 n.+2 n.+1 (σ i) (δ (ord_upcast i)) =
      @Category.id stdfinset n.+1.
Proof.
  destruct i as [ival ibd].
  stdfinset_simpl. intros [xval xbd]. stdfinset_simpl.
  exact: bumpK.
Qed.

Proposition σSi_δi {n : nat} (i : 'I_n.+1)
  : @compose stdfinset n.+1 n.+2 n.+1 (σ i) (δ (lift ord0 i)) =
      @Category.id stdfinset n.+1.
Proof.
  destruct i as [ival ibd].
  stdfinset_simpl. intros [xval xbd]. stdfinset_simpl.
  rewrite {2}/bump; stdfinset_simpl.
  exact: δSi_σi_eq_id_nat.
Qed.

Proposition δi_σj_2 {n : nat} (i : 'I_(n.+3)) (j : 'I_(n.+1))
  : i > j.+1 ->
    @compose stdfinset n.+2 n.+3 n.+2 (σ (ord_upcast j)) (δ i) =
      @compose stdfinset n.+2 n.+1 n.+2 (δ (ord_predn i)) (σ j).
Proof.
  destruct i as [ival ibd], j as [jval jbd].
  simpl; intro ineq.
  stdfinset_simpl; intros [xval xbd].
  stdfinset_simpl.
  exact: δi_σj_i_gt_Sj_nat.
Qed.