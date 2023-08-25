From Ltac2 Require Import Ltac2.
Require Import Category.Lib.
Require Import Nat PeanoNat.
From Hammer Require Import Hammer Tactics.
Search le "trans".

#[export] Hint Resolve Nat.le_trans : arith.

Open Scope nat.

Notation "n .-1" := (pred n) (at level 2, left associativity,
                        format "n .-1").
Notation "n .+1" := (S n) (at level 2, left associativity,
                        format "n .+1").
 
Proposition nlek_nm1lek : forall (n m : nat), (n <= m) -> (n.-1 <= m).
Proof.
  ltac1:(sfirstorder).
Qed.

Proposition nltk_nm1ltk : forall (n m : nat), (n < m) -> (n.-1 < m).
Proof.
  ltac1:(sfirstorder).
Qed.

Proposition prednlek_nleSk (n k : nat) : n.-1 <= k <-> n <= k.+1.
Proof.
  ltac1:(sfirstorder).
Qed.

Proposition nlek_nm1lekm1 : forall (n m : nat), (n <= m) -> (n.-1 <= m.-1).
Proof.
  ltac1:(sfirstorder).
Qed.

Global Hint Resolve nlek_nm1lek : arith.
Global Hint Resolve nltk_nm1ltk : arith.
Global Hint Resolve nlek_nm1lekm1 : arith.

Proposition nltm_nltmk : forall n m k: nat, n <= m -> n <= m + k.
Proof.
  ltac1:(sfirstorder).
Qed.

Proposition nltk_nltmk : forall n m k: nat, n <= k -> n <= m + k.
Proof.
  ltac1:(sfirstorder).
Qed.

Proposition nltm_nneqm : forall n m : nat, n < m -> n ≠ m.
Proof.
  ltac1:(hauto use:Nat.lt_irrefl).
Qed.

Proposition neq_sym `{A : Type} (x y : A) : x ≠ y <-> y ≠ x.
Proof.
  ltac1:(hauto).
Qed.

Proposition nltm_mneqn : forall n m : nat, m < n -> n ≠ m.
Proof.
  ltac1:(hauto use:Nat.lt_irrefl).
Qed.

Global Hint Resolve nltm_nltmk : arith.
Global Hint Resolve nltk_nltmk : arith.
Global Hint Resolve nltm_nneqm : arith.
Global Hint Resolve nltm_mneqn : arith.

(* My automation strategy in this file is that if I think a tactic 
   should *always* be applied 
   if it can (i.e. it should be applied eagerly and without backtracking)
   then I will put the tactic in a block repeat-match-goal script like this;

   and if I think that it should only *sometimes* be applied, then I will
   add it to a hint database for auto, so that it can be applied with backtracking.

   The main downside I can think of to this approach is that it is not
   easy to add new "hints" to the repeat-match-goal block this way.
 *)

Global Hint Extern 10 (_ <= _) => (eapply Nat.le_trans) : arith.

Proposition n_leq_m_n_lt_msub1 (n m : nat) : n < m -> n <= m.-1.
Proof.
  ltac1:(hauto).
Qed.

Fixpoint δ (i : nat) (j : nat) :=
  match i with
  | O => S j
  | S i' => match j with
            | O => O
            | S j' => S (δ i' j')
            end
  end.

Definition pointwise_eq {A B : Type} (f g : A -> B) := forall a, f a = g a.
Notation "f =1 g" := (pointwise_eq f g) (at level 54).

(*   δ_j ∘ δ_i = δ_i ∘ δ_(j-1)   ;  i < j *)

Proposition δi_δj_nat :
  forall (i j : nat), i < j ->
                      ((δ j) ∘ (δ i)) =1 (δ i) ∘ (δ (j.-1)).
Proof.
  induction i, j; try ltac1:(sauto).
  intros H a; destruct a; apply Arith_prebase.lt_S_n_stt in H.
  { ltac1:(sauto lq:on). }
  { ltac1:(sauto b: on). }
Qed.

(**   σ_j ∘ σ_i = σ_i ∘ σ_(j+1)   ;  i <= j *)
Fixpoint σ i j :=
  match i with
  | O => pred j
  | S i' => match j with
            | O => O
            | S j' => S (σ i' j')
            end
  end.        

Proposition σi_σj_nat :
  forall (i j : nat), i <= j -> 
                      (σ j) ∘ (σ i) =1 (σ i) ∘ (σ j.+1).
Proof.
  induction i, j; intros H k; try ltac1:(hauto).
  ltac1:(hfcrush).
Qed.

Proposition δi_σj_iltj_nat :
  forall (i j : nat), i < j -> (σ j) ∘ (δ i) =1 (δ i) ∘(σ j.-1).
Proof.
  induction i, j; intros H k; try ltac1:(sfirstorder).
  apply Arith_prebase.lt_S_n_stt in H.
  destruct k; ltac1:(sauto b:on).
Qed.

Proposition δi_σi_eq_id_nat :
  forall (i : nat), (σ i) ∘ (δ i) =1 id.
Proof.
  induction i; intro k; destruct k; ltac1:(sfirstorder).
Qed.

Proposition δSi_σi_eq_id_nat : forall i : nat,
    (σ i) ∘ (δ i.+1) =1 id.
Proof.
  induction i; intro k; destruct k; ltac1:(sfirstorder).
Qed.

Proposition δi_σj_i_gt_Sj_nat {n : nat} :
  forall i j : nat, i > j.+1 ->
                   (σ j) ∘ (δ i) =1 (δ i.-1) ∘ (σ j).
Proof.
  induction i, j; intros ineq k;  destruct k;
    try ltac1:(sfirstorder).
  { ltac1:(sauto lq:on use:Arith_prebase.lt_S_n_stt). }
  { ltac1:(sauto lq:on use:Arith_prebase.lt_S_n_stt). }
  { ltac1:(sauto b:on use:Arith_prebase.lt_S_n_stt). }
Qed.

Lemma σ_i_ge_x (i x : nat) :
  x <= i -> σ i x = x.
Proof.
  revert x; induction i, x; unfold σ; try ltac1:(sfirstorder).
      ltac1:(hfcrush).
Qed.

Lemma σ_i_lt_x (i x : nat) :
  i < x -> σ i x = pred x.
Proof.
  revert x; induction i, x; unfold σ; try ltac1:(sfirstorder).
      ltac1:(hfcrush).
Qed.

Lemma σ_i_eq_i_nat ( i x : nat ) :
  σ i x = i <-> (i = x \/ i.+1 = x).
Proof.
  split.
  {
    destruct (Compare_dec.le_lt_dec x i).
    { ltac1:(sfirstorder use: σ_i_ge_x). }
    { ltac1:(sfirstorder use: σ_i_lt_x). }
  }
  {
    intro a; destruct a as [ eq | eqS ].
    { destruct eq; induction i; ltac1:(hauto). }
    { destruct eqS; induction i; ltac1:(hauto). }
  }    
Qed.

Inductive rgeq (m: nat) : nat -> Set :=
| rgeq_refl : rgeq m
| rgeq_succ n : rgeq (S n) -> rgeq n.

Proposition rgeq_SS (n m : nat) : rgeq n m -> rgeq (S n) (S m).
Proof.
  intro H; induction H; ltac1:(sauto lq:on).
Qed.

Lemma rgeq_sub : forall m n k, rgeq m n -> rgeq m (n - k).
Proof.
  intros m; induction n, k; try ltac1:(sfirstorder).
  ltac1:(sauto q:on).
Qed.

Proposition rgeq_0_n {n : nat} : rgeq 0 n -> n =0 .
Proof.
  intro H; induction H; ltac1:(sauto lq:on).
Qed.

Proposition rgeq_n_0 {n : nat} : rgeq n 0.
Proof.
  induction n.
  { constructor. }
  { constructor. apply rgeq_SS. assumption. }
Qed.

(* PeanoNat.Nat.leb_refl: ∀ x : nat, (x <=? x) = true *)
                                                
Proposition leb_down { n m: nat } : leb (S m) n = true -> leb m n = true.
Proof.
  revert m; induction n; ltac1:(sauto lq:on).
Qed.

Proposition reflect_rgeq_to (n m : nat) : rgeq n m -> leb m n = true.
Proof.
  intro H; induction H;
    ltac1:(sfirstorder use:Nat.leb_refl use:leb_down).
Qed.

Search leb.

Proposition reflect_rgeq_from (n m : nat) :
  is_true (leb m n) -> rgeq n m.
Proof.
  revert m; induction n; try ltac1:(sauto lq:on).
  intro m; destruct m.
  { ltac1:(sfirstorder use:rgeq_n_0). }
  { ltac1:(sfirstorder use:rgeq_SS). }
Qed.

Proposition rgeq_SS' (n m : nat) : rgeq (S n) (S m) -> rgeq n m.
Proof.
  intro H.
  apply reflect_rgeq_from.
  apply reflect_rgeq_to in H.
  trivial.
Qed.

Proposition rgeq_implies_lgeq (n m : nat) : rgeq n m -> m <= n.
Proof. 
  intro H; induction H.
  { constructor. }
  { now apply Le.le_Sn_le_stt. }
Qed.

Close Scope nat_scope.
