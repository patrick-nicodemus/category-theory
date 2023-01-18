(* -*- mode: coq; mode: visual-line -*-  *)
Require Import Category.Lib.
Require Import Theory.Category.

Require Import Category.Instance.Simplex.NaturalNumberArithmetic.
Require Import Category.Instance.Simplex.Stdfinset.
Require Import Category.Instance.Simplex.FinType.

(* Require Import Category.Instance.Simplex.Ordinals. *)

Require Import ssreflect.
Require Import ssrfun.
Require Import ssrbool.

Require Import mathcomp.ssreflect.seq.
Set Warnings "-notation-overridden".
Require Import mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finfun.
Require Import mathcomp.ssreflect.tuple.

From Hammer Require Import Hammer Tactics Reflect.

Set Primitive Projections.
Set Universe Polymorphism.

(* Unset Transparent Obligations. *)

(** This file defines the coface and codegeneracy maps of the simplex category [Δ], (including the proofs that they are monotonic) and proves that the simplicial identities hold. It builds on the contents of stdfinset.v to incorporate monotonicity conditions. *)

(** Letting [ [n] ] denote the n-th finite ordinal [{0,... n-1}], and letting [i ∈ [n+1] ], the [i]-th coface map [δ_i : [n] -> [n+1]] is the unique monotonic injection whose image does not contain [i]; that is, [δ_i(x) = x] if [x < i], else [δ_i(x) = x+1 if x >= i]. *)

(** We define [δ_i] in terms of the [lift] and [bump] functions from the ssreflect fintype library. *)

(** Again, letting [i ∈ [n+1]], the [i]-th codegeneracy map [σ_i : [n+2] -> [n+1]], (denoted [σ_i]), is the unique monotonic surjection such that the preimage of [i] contains two elements; that is, [σ_i(x) = x] if [x <= i]; else, [σ_i(x) = x-1] if [x > i]. These functions satisfy the following equations, called the simplicial identities. *)
   
(**  $\delta_j \circ \delta_i = \delta_i \circ \delta_{j-1} ;\;  i < j $ *)

(**   $\sigma_j \circ \sigma_i = \sigma_i \circ \sigma_{j+1}  ;\;  i \leq j$ *)

(**   $\sigma_j \circ \delta_i = \delta_i \circ \sigma_(j-1)   ;  i < j $ *)

(**   $\sigma_j \circ \delta_j = id = \sigma_j \circ \delta_{j+1}$ *)

(**   $\sigma_j \circ \delta_i = \delta_{i-1} ;\; i > j+1$  *)

(** which we prove in this file. References for this material include "Simplicial Objects in Algebraic Topology" by Peter May, or "Simplicial Homotopy Theory" by Goerss and Jardine. The above five equations are taken from page 1 of May's book, except that in his book they occur dualized, i.e., they are meant to be interpreted in the opposite category to our simplex category. *)
  
(* Open Scope nat_scope. *)

Definition monotonic {n m : nat} (f : 'I_m^n) : bool :=
  pairwise (fun i j : 'I_m => leq i j) (tuple_of_finfun f).

Definition strictly_monotonic {n m : nat} (f : 'I_m^n) : bool :=
  pairwise (fun i j : 'I_m => i < j) (tuple_of_finfun f).

Definition monotonicP {n m : nat} (f : 'I_m^n)
  : reflect (forall i j : 'I_n, i <= j -> f i <= f j) (monotonic f).
Proof.
  rewrite /monotonic.
  (* There is already a logical specification of the behavior of the 
     pairwise function in the standard library so we just have to prove 
     our specificiation is equivalent to that one. *)
  apply/(iffP (tuple_pairwiseP _ _ _ _)); intro H.
  { intros i j ineq.
    assert (k := (H i j (mem_ord_enum i) (mem_ord_enum j))).
    (* Go by cases on the disjunction i <= j -> i = j or i < j. *)
    (* Bookkeeping to convert between Boolean/logical disjunction. *)
    rewrite leq_eqVlt in ineq ; move/orP : ineq; intro ineq;
      destruct ineq as [eq | lt].
    { (* Case i = j. *)
      (* N. b. - Since the type bool satisfies UIP, 
         if P : A -> bool is a predicate on A, 
         given two elements (x,e) and (x', e') of { x : A | P x = true },
         (x, e) = (x', e') iff x = x' because e = e' always,
         as there is a unique proof of true = true. 
         Thus the inclusion of a subtype into the parent type is
         always injective. This is recorded in the lemma val_inj. *)
      move/eqP: eq; intro eq; by rewrite (val_inj eq). }
    assert (z := k lt).
    rewrite 2! tnth_tuple_of_finfun in z.
    exact: z.
  }
  intros i j _ _ ineq.
  rewrite 2! tnth_tuple_of_finfun. apply: H; exact: ltnW.
Qed.

Proposition strictly_monotonicP {n m : nat} (f : 'I_m^n) :
  reflect (forall i j : 'I_n, i < j -> f i < f j) (strictly_monotonic f).
Proof.
  rewrite /monotonic.
  apply/(iffP (tuple_pairwiseP _ _ _ _)); intro H.
  { 
    intros i j ineq.
    have k := (H i j (mem_ord_enum i) (mem_ord_enum j)) ineq.
    now rewrite 2! tnth_tuple_of_finfun in k.
  }
  {
   intros i j _ _ ineq.
   rewrite 2! tnth_tuple_of_finfun. now apply: H.
  }
Qed.

Proposition monotonic_fold_equiv (n m : nat) (f : 'I_m^n) :
  monotonic f =
    let fg := tuple.tval (tuple_of_finfun f) in
    if fg is x :: xs then
      foldr andb true (pairmap (fun i j : 'I_m => leq i j) x xs)
    else true.
Proof.
  apply: pairmap_trans_pairwise; rewrite /nat_of_ord; by apply: leq_trans.
Qed.

Proposition idmap_monotonic (n : nat) : @monotonic n _ (finfun id).
Proof.
  apply/monotonicP => i j.
  by rewrite 2! ffunE.
Qed.

Record monotonic_fn_sig (n m : nat) :=
  { fun_of_monotonic_fn :> 'I_m^n ;
    _ : monotonic fun_of_monotonic_fn }.
Arguments fun_of_monotonic_fn {n} {m} _.

(** The following definition records monotonic_fn with the hint database for subtypes, which means that we can apply lemmas about general subtypes to monotonic functions. For example, we can "apply val_inj" to conclude that two monotonic functions are equal if the underlying (finite) functions are equal after the monotonicity property is forgotten. Monotonic functions are also equipped with a Boolean comparison function "==" automatically which is inherited from the underlying comparison function for finfuns. *)

Canonical Structure monotonic_fn (n m : nat) :=
  [subType for (@fun_of_monotonic_fn n m) ].
Definition monotonic_fn_eqMixin (n m : nat) :=
  [eqMixin of (monotonic_fn n m) by <:].
Canonical Structure monotonic_fn_eqType (n m : nat) :=
  EqType (monotonic_fn n m) (monotonic_fn_eqMixin n m).

Definition comp {aT : finType} {rT sT : Type} (f : {ffun aT -> rT})
  (g : rT -> sT) 
  : {ffun aT -> sT}
  :=  [ffun x => g (f x)].

Proposition comp_assoc {aT : finType} {rT sT mT: Type}
  (f : {ffun aT -> rT}) (g : rT -> sT) (h : sT -> mT)
  : comp f (g \; h) = comp (comp f g) h.
Proof.
  apply: eq_ffun; simpl; intro; apply: f_equal; by rewrite ffunE.
Qed.

Definition comp_mon (n m k : nat) (g : @monotonic_fn m k)
  (f : @monotonic_fn n m)
  :  @monotonic_fn n k.
Proof.
  exists (comp (fun_of_monotonic_fn f) (fun_of_monotonic_fn g)).
  apply/monotonicP.
  intros i j ineq; simpl.
  rewrite 2! ffunE.
  (* We make use of our logical specification of the "monotonic" function. *)
  move/monotonicP : (valP g). intro H; apply: H.
  by move/monotonicP : (valP f); intro H; apply H.
Defined.

Definition id_mon (n : nat) : @monotonic_fn n n :=
  Sub (finfun (@id 'I_n)) (idmap_monotonic n).


Program Definition finord : Category :=
  {|
    obj := nat;
    hom := fun n m => @monotonic_fn n m;
    homset := fun _ _ => {| equiv := eq |};
    Category.id := id_mon;
    compose := comp_mon;
    |}.
Next Obligation.
  apply: val_inj; simpl; apply ffunP; intro i; rewrite 2! ffunE; done. Qed.
Next Obligation.
  apply: val_inj; simpl; apply ffunP; intro i; rewrite 2! ffunE; done. Qed.
Next Obligation.
  apply: val_inj; simpl; apply ffunP; intro i; rewrite 4! ffunE; done. Qed.
Next Obligation.
  apply: val_inj; simpl; apply ffunP; intro i; rewrite 4! ffunE; done. Qed.
(* Done. *)

Notation Δ := finord.

(** Definitions of the face and degeneracy maps *)

Proposition δ_monotonic : forall (n : nat) (i : 'I_(n.+1)),
    monotonic [ffun j : 'I_n => lift i j].
Proof.
  intros n i; apply/monotonicP.
  intros x y ineq. rewrite 2! ffunE; unfold lift; simpl; unfold bump.
  destruct (@leP i x); arith_simpl.
  {  assert (z : i <= y) by eauto using leq_trans; rewrite z; by auto with arith. }
  { destruct (@leP i y); by auto with arith. }
Qed.

Definition δ (n : nat) (i : 'I_(n.+1)) : monotonic_fn n n.+1 :=
  @Sub {ffun 'I_n -> 'I_(n.+1)} monotonic _ _ (δ_monotonic n i).

Lemma σ_subproof (n : nat) (i : 'I_(n.+1))
  : forall j : 'I_(n.+2), unbump i j < n.+1.
Proof.
  intro j; rewrite ltnS -leq_bump. unfold bump.
  destruct i as [ival ibd]; simpl.
  rewrite -[ival <= n]ltnS ibd -ltnS; unfold addn; simpl.
  by (destruct j).
Qed.

Ltac by_cases_on_leq_goal :=
  match goal with
  | [ |- context[ nat_of_bool (leq ?n ?m) ] ] =>
      let var1 := fresh "LEQ" in
      let var2 := fresh "GT" in 
      destruct (@leqP n m) as [var1 | var2]
  end.

Local Hint Extern 11 => by_cases_on_leq_goal : arith.

Proposition σ_monotonic n i
  : monotonic [ffun j : 'I_(n.+2) => Ordinal (σ_subproof n i j)].
Proof.
  destruct i as [ival ibd]; apply (rwP (monotonicP _)).
  intros [xval xbd] [yval ybd]; simpl. intro ineq.
  rewrite ! ffunE; simpl; unfold unbump; clear xbd ybd.
  destruct (@ltP ival xval) as [l | eq]; arith_simpl. 
  {  rewrite (leq_trans l ineq); auto with arith. }
  {  rewrite -ltnNge ltnS in eq. 
     destruct (@ltP ival yval) as [i_lt_y | i_ge_y]; arith_simpl;
       [ | assumption ].
     by eapply leq_trans; eauto with arith. 
  }
Qed.   

Definition σ (n : nat) (i : 'I_(n.+1))
  : monotonic_fn (n.+2) (n.+1) :=
  @Sub {ffun 'I_(n.+2) -> 'I_(n.+1)} monotonic _ _ (σ_monotonic n i).

Program Definition lshift_m (m n : nat)
  : monotonic_fn n (n + m):=
  Sub (finfun (fun i => lshift m i)) _.
Next Obligation.
  by apply (rwP (monotonicP _)); intros; rewrite ! ffunE. Qed.

Program Definition rshift_m (m n : nat)
  : monotonic_fn m (n + m) :=
  Sub (finfun (fun i => rshift n i)) _.
Next Obligation.
  by apply (rwP (monotonicP _ )); intros; rewrite ! ffunE;
    unfold rshift; simpl; autorewrite with arith.
Qed.  


Arguments δ {n} i.
Arguments σ {n} i.

(** My automation strategy in this file is that if I think a tactic should *always* be applied if it can (i.e. it should be applied eagerly and without backtracking) then I will put the tactic in a block repeat-match-goal script like this;

   and if I think that it should only *sometimes* be applied, then I will add it to a hint database for auto, so that it can be applied with backtracking.

   The main downside I can think of to this approach is that it is not easy to add new "hints" to the repeat-match-goal block this way.
 *)

Ltac simplex_simpl :=
  do ! (match goal with
        | [ |- @eq (@hom finord _ _) _ _ ]  => apply: val_inj; simpl
        | [ |- @eq (ordinal _) _ _] => apply: val_inj; simpl
        | [ |- @eq (monotonic_fn_sig _ _) _ _] => apply:val_inj; simpl
        | [ |- context[AugmentedSimplexCategory.comp _ _]] =>
            fail_if_unchanged ltac:(unfold AugmentedSimplexCategory.comp)
        | [ |- eqfun _ _ ] => unfold eqfun
        | [ |- @eq (@finfun_of _ _ _) _ _ ] => apply: eq_ffun
        | [ |- _ ] => fail_if_unchanged ltac:(rewrite ! ffunE)
        | [ |- _ ] => fail_if_unchanged simpl
        end).

Create HintDb simplex discriminated.

#[export] Hint Extern 0 => simplex_simpl : simplex.
#[export] Hint Extern 5 => (fail_if_unchanged ltac:(simpl)) : simplex.

(** Simplicial identities, this time for the simplex category  *)
(*   δ_j ∘ δ_i = δ_i ∘ δ_(j-1)   ;  i < j *)
Proposition δi_δj {n : nat} : forall i : 'I_(n.+1), forall j : 'I_(n.+2),
  forall (t : i < j),
    @compose finord n n.+1 n.+2 (δ j) (δ i) =
      @compose finord n n.+1 n.+2 (δ (ord_upcast i))
                                     (δ (ord_predn j)).
Proof.
  intros [ival ibd] [jval jbd] ineq; simpl in ineq.
  simplex_simpl. intros [xval xbd]; simplex_simpl.
  exact: δi_δj_nat.
Qed.

Proposition σi_σj (n : nat) (i : 'I_(n.+2)) (j : 'I_(n.+1))
  : (i <= j) ->
    @compose finord n.+3 n.+2 n.+1 (σ j) (σ i) =
      @compose finord n.+3 n.+2 n.+1 
        (σ (inord i)) (σ (inord j.+1)).
Proof.
  intro H.
  destruct i as [ival ibd]; destruct j as [jval jbd]. simpl in H.
  simplex_simpl. intros [xval xbd]. simplex_simpl.
  assert (A := σi_σj_nat ival jval H xval).
  rewrite -> 2 inordK; [  apply A | auto | auto with arith ].
Qed.

Proposition δi_σj_iltj {n : nat} :
  forall (i : 'I_n.+2) (j : 'I_n.+2), (i < j) ->
    @compose finord n.+2 n.+3 n.+2 (σ j) (δ (ord_upcast i)) =
      @compose finord n.+2 n.+1 n.+2 (δ i) (σ (ord_predn j)).
Proof.
  intros i j ineq; destruct i as [ival ibd], j as [jval jbd]; simpl in ineq.
  simplex_simpl. intros [xval xbd].
  simplex_simpl.
  exact: δi_σj_iltj_nat.
Qed.

Proposition δi_σi_eq_id {n : nat} : forall i : 'I_n.+1,
    @compose finord n.+1 n.+2 n.+1 (σ i) (δ (ord_upcast i)) =
      @Category.id finord (n.+1).
Proof.
  intros [ival ibd]; apply val_inj; simpl;
    unfold comp.
  apply eq_ffun; intro x. rewrite ! ffunE; apply val_inj; simpl;
    exact: δi_σi_eq_id_nat.
Qed.

Proposition δSi_σi_eq_id {n : nat} : forall i : 'I_n.+1,
    @compose finord n.+1 n.+2 n.+1 (σ i) (δ (lift ord0 i)) = @Category.id finord (n.+1).
Proof.
  intros [ival ibd]; apply val_inj; simpl;
    unfold AugmentedSimplexCategory.comp;
    apply eq_ffun; intro x; rewrite ! ffunE; apply val_inj; simpl.
  rewrite {2}/bump; arith_simpl. exact: δSi_σi_eq_id_nat.
Qed.

Proposition δi_σj_i_gt_Sj {n : nat}
  : forall (i : 'I_(n.+3))
           (j : 'I_(n.+1))
           (t : i > j.+1),
    @compose finord n.+2 n.+3 n.+2 (σ (ord_upcast j)) (δ i) =
      @compose finord n.+2 n.+1 n.+2 (δ (ord_predn i)) (σ j).
Proof. 
  intros [ival ibd] [jval jbd]; simpl; intro ineq.
  simplex_simpl; intros [xval xbd].
  simplex_simpl.
  exact: δi_σj_i_gt_Sj_nat.
Qed.

Definition rwP_surjectiveP (A : finType) (B : finType)
  (f : {ffun A -> B})
  := rwP (surjectiveP f).

Definition rwP_ltP (n m : nat) := rwP (@ltP n m).
Definition rwP_injectiveP (A B : finType) (f : A -> B)
  := rwP (injectiveP f).

#[export] Hint Rewrite <- rwP_surjectiveP : brefl.
#[export] Hint Rewrite <- rwP_ltP : brefl.
#[export] Hint Rewrite <- rwP_injectiveP : brefl.
#[export] Hint Rewrite <- leB : brefl.

Lemma surj_preserves_top (n m: nat) (f : n.+1 ~{ Δ }~> m.+1)
  (p : surjective f) : f ord_max = ord_max.
Proof.
  move: p.
  breflect.
  move => p.
  rewrite /FinFun.Surjective in p.
  destruct (p ord_max) as [x pf].
  have t: x <= @ord_max n by destruct x; auto.
  (* breflect doesn't work so good here 
                because of the dependent types. *)
  (* For example, an ordinal is a pair (x; p) where p : x < n.
       It's not easy to change the form of p without destroying the
       ordinal. Here we have f (x; p) so we cannot really get rid of
       the ordinal without killing this thing which depends on it. *)
  apply val_inj.
  apply/eqP.
  now rewrite
    eqn_leq
    -{2}pf
    ((snd (rwP (monotonicP (val f)))) (valP f) _ _ t)
    /=
    -ltnS
       (valP (f ord_max)).
Qed.

Lemma injectiveb_strictly_monotonic (n m : nat) (f : n ~{ Δ }~> m)
  : injectiveb f = strictly_monotonic f.
Proof.
  rewrite -iff_equiv -(rwP (injectiveP _)) -(rwP (strictly_monotonicP _)).
  split.
  { move => a i j ineq.
    have: (f i <= f j). {
      apply ltnW in ineq.
      have k:= (valP f).
      rewrite -(rwP (monotonicP _)) in k.
      now apply: k.
    }
    rewrite leq_eqVlt.
    case/orP; [ | done ].
    move => fi_eq_fj.
    apply: False_rect.
    cut (i = j). {
      move/eqP => t; move: t.
      apply: (elimF idP); now apply: ltn_eqF.
    }
    apply: a.
    now apply/eqP.
  }
  move => a i j eq.
  apply/eqP.
  rewrite -(negb_involutive (i == j)).
  apply/negP => neq.
  rewrite neq_ltn in neq.
  rewrite (rwP eqP) in eq.
  move: eq. apply/negP.
  rewrite neq_ltn.
  rewrite -(rwP orP) in neq. case: neq.
  { move => iltj.
    have d := a i j iltj.
    rewrite d; done. }
  { move => jlti.
    have d := a j i jlti.
    rewrite d orbT; done. }
Qed.

Lemma injective_increasing (n m : nat) (f : n ~{ Δ }~> m) 
  : (injectiveb f) -> [forall x : 'I_n, x <= f x].
Proof.
  move => j.
  apply/forallP.
  case => xval xbd /=.
  induction xval.
  { done. }
  { have mon := valP f.
    rewrite injectiveb_strictly_monotonic in j.
    rewrite -(rwP (strictly_monotonicP f)) in j.
    have xbd0 : (xval < n). {
      auto with arith.
    }
    set x : 'I_n := Sub xval xbd0.
    set Sx : 'I_n := Sub xval.+1 xbd.
    have tm : x < S x by (auto with arith).
    have jxSxtm := j x Sx tm.
    specialize IHxval with xbd0.
    now apply: (@leq_ltn_trans (f x)).
  } 
Qed.
  
Lemma surjective_decreasing (n m : nat) (f : n ~{ Δ }~> m) 
  : (surjective f) -> [forall x : 'I_n, x >= f x].
Proof.
  move => j.
  apply/forallP.
  case => xval xbd /=.
  (* Case m = 0 is trivial. *)
  destruct m; [ destruct (f (Ordinal xbd)); auto with arith |].
  (* mon  = f is monotonic. *)
  have mon := (snd (rwP (monotonicP f))) (valP f).
  (* g is a section of f. p states that g is a section of f. *)
  have p := surjection_splitting_spec f j.
  set g := surjection_splitting f j in p; clearbody g.
  rewrite -(rwP (splitsP _ _)) /splits_spec in p.

  induction xval.
  {
    
    (* Want to show f(0) <= 0. 
       Certainly 0 <= g 0;
       so f 0 <= f g 0 = 0. *)
    have t := p ord0.
    have b := (f_equal val t); simpl in b.
    rewrite -{2}b.
    apply: mon; auto with arith.
  } 
  {
    (* Want to show f(x.+1) <= x.+1. *)
    have xbd0 : xval < n by auto with arith.
    (* We prove that f(x.+1) <= f(x).+1 <= x.+1. *)
    apply: (@leq_trans (f (Ordinal xbd0)).+1 ).
    { (* First, f(x.+1) <= f(x).+1. *)
      have fx_lt_n := valP (f (Ordinal xbd0)).
      rewrite ltnS leq_eqVlt in fx_lt_n.
      (* We break into cases depending on whether f(x)=m 
         or f(x) < m. *)      
      move/orP : fx_lt_n; case.
      {
        (* If f(x) = m, then f(x).+1 = m.+1.
           But f(x.+1) < m.+1 by the assumption that f : n -> m.+1.
           So f(x.+1) < f(x).+1, thus a fortiori f(x.+1) <= f(x).+1. *)
        move/eqP => eq_n.
        rewrite eq_n.
        have t := valP (f (Ordinal xbd)).
        auto with arith.
      } 
      {
        (* Otherwise if f(x) < m then f(x).+1 is in m.+1, *)
        (* so g(f(x).+1) is defined. *)
        (* I claim x.+1 <= g(f(x).+1). *)
        (* Proof: For the sake of a contradiction,
           assume g(fx+1)< x.+1;  
           equivalently g(fx+1) <= x. *)
        (* Then by monotonicity f(g(fx+1))= (fx).+1 <= f(x);
           a contradiction.*)
        (* In what follows the proof above has been 
            "reversed" from bottom to top to be more appropriate
            for the backwards reasoning style of Coq. *)
        move => xbd'.
        rewrite -ltnS in xbd'.
        set y := Ordinal xbd'.
        change (f (Ordinal xbd) <= _ .+1) with
          (f (Ordinal xbd) <= val y).
        cut (is_true (xval.+1 <= g y)). {
          move => a.
          have tm := mon (Ordinal xbd) (g y) a.
          now rewrite -(p y).
        }
        rewrite ltnNge.
        apply/negP => t.
        cut (is_true ((f (Ordinal xbd0)).+1 <= f (Ordinal xbd0))). {
          now rewrite ltnn.
        }
        change ((f (Ordinal xbd0)).+1) with (val y).
        rewrite -(p y).
        apply: mon.
        exact: t.
      }
    }
    specialize IHxval with xbd0.
    now rewrite ltnS.
  } 
Qed.

Lemma identity_unique_surjection (n : nat) (f : n ~{ Δ }~> n)
  (p : surjective f)
  : Build_monotonic_fn_sig n n [ffun x => x] (idmap_monotonic n) = f.
Proof.
  apply: val_inj => /=.
  apply/ffunP => x.
  rewrite ffunE.
  apply val_inj.
  apply/eqP.
  rewrite eqn_leq.
  have p' := p.
  rewrite -injective_iff_surjective in p'.
  (* rewrite -(rwP (injectiveP f)) in p'. *)
  have inj_incr := injective_increasing _ _ _ p'.
  rewrite -(rwP forallP) in inj_incr.
  rewrite inj_incr.
  have surj_decr := surjective_decreasing _ _ _ p.
  rewrite -(rwP forallP) in surj_decr.
  rewrite surj_decr.
  done.
Qed.

(** The degeneracy factoring map constructed in stdfinset sends monotonic maps to monotonic maps. *)

Proposition degenerate_factor_monotonic {n m : nat} (f : n ~{ Δ }~> m.+1)
  (i : 'I_m.+1) ( p: hitstwice f i )
  : monotonic (degeneracy_factoring_map f i p).
Proof.
  rewrite -(rwP (monotonicP _)).
  move => x y x_le_y.
  unfold degeneracy_factoring_map.
  set j := existsPS _ _ _ .
  destruct j as [j lj].
  do 2 rewrite ffunE.
  have t : (y <= j) || (y > j) by rewrite leqNgt orNb.
  have mon := (snd (rwP (monotonicP f)) (valP f) x y x_le_y).
  case/orP: t => ineq.
  {
    have -> : x <= j by exact: (leq_trans x_le_y ineq).
    rewrite ineq; do 2 rewrite andTb.
    
    set fy_eq_i := f y == i.
    set fx_eq_i := f x == i.
    destruct (@idP fy_eq_i) as [y_eq | y_diseq];
    destruct (@idP fx_eq_i) as [x_eq | x_diseq ].
    { done. }
    { simpl.
      unfold bump.
      have -> : (i <= f x) = false. {
        apply negbTE.
        rewrite -ltnNge ltn_neqAle.
        have -> : (f x <=i) by now move/eqP: y_eq => <-.
        rewrite andbT.
        rewrite negE.
        exact: x_diseq.
      }
      rewrite add0n.
      now move/eqP: y_eq => <-.
    }
    {
      (* Case: f x = i, f y > i *)
      simpl; unfold bump.
      cut (is_true (i <= f y)). {
        move => a.
        rewrite a add1n.
        exact: (leq_trans a).
      }
      apply: (leq_trans _ mon).
      now move/eqP: x_eq => ->.
    }
    {
      now rewrite leq_bump2.
    }
  }
  (* We now consider the case j < y . *)
  {
    rewrite [y  <= j]leqNgt .
    rewrite ineq /=.
    unfold bump.
    have t1 : (i <= f y). {
      apply ltnW in ineq.
      apply (snd (rwP (monotonicP f)) (valP f) j y) in ineq.
      rewrite -(rwP existsP) in lj; case: lj => [j' a].
      do 2 rewrite -(rwP andP) in a.
      case: a => [[j_lt_j' fj_eq_i] fjp_eq_i].
      now move/eqP: fj_eq_i => <-.
    }
    rewrite t1 add1n.
    destruct (@leP x j) as [x_le_j | x_gt_j].
    {
      rewrite /=.
      set fx_eq_i := (f x == i).
      destruct fx_eq_i.
      { exact: (leq_trans t1). }
      { simpl. unfold bump.
        set abc := (i <= f x). destruct abc.
        { auto. }
        { rewrite add0n. exact: (leq_trans mon). }
      }
    }
    simpl.
    unfold bump.
    set abc := (i <= f x). destruct abc.
        { auto. }
        { rewrite add0n. exact: (leq_trans mon). }
  }
Qed.


Proposition face_factor_monotonic
   {n m : nat} (f : n ~{ Δ }~> m.+1)
  (i : 'I_m.+1) (p : i \notin (image f 'I_n))
      : monotonic (facemap_factoring_map f i p).
Proof.
  have mon := valP f.
  rewrite -(rwP (monotonicP _)) in mon.
  rewrite -(rwP (monotonicP _)) => x y x_le_y.
  apply mon in x_le_y.
  unfold facemap_factoring_map; do 2 rewrite ffunE /=.
  rewrite -leq_bump unbumpKcond.
  set k := (a in _ <= a + _).
  refine (@leq_trans (f y) _ _ x_le_y _).
  auto with arith.
Qed.

Proposition forgetful_functorial {n m k}
  (f : n ~{ Δ }~> m) (g : m ~{ Δ }~> k)
  : val (g ∘ f) = (val g) ∘[stdfinset] (val f).
Proof.
  reflexivity.
Qed.
