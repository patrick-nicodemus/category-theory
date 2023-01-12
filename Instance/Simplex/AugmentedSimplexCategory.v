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
  
(* Open Scope nat_scope.  *)

Definition monotonic {n m : nat} (f : 'I_m^n) : bool :=
  pairwise (fun i j : 'I_m => leq i j) (tuple_of_finfun f).

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

Local Create HintDb simplex discriminated.

Local Hint Extern 0 => simplex_simpl : simplex.
Local Hint Extern 5 => (fail_if_unchanged ltac:(simpl)) : simplex.

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
  intros [ival ibd]; apply val_inj; simpl; unfold AugmentedSimplexCategory.comp;
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
Locate ord0.

Definition rwP_surjectiveP (A : finType) (B : finType)
  (f : {ffun A -> B})
  := rwP (surjectiveP f).

Definition rwP_ltP (n m : nat) := rwP (@ltP n m).

#[export] Hint Rewrite <- rwP_surjectiveP : brefl.
#[export] Hint Rewrite <- rwP_ltP : brefl.
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

(** The unique surjection n -> n in Δ is the identity. *)
(** Why the hell is this proof so long? *)
(** The proof heavily uses negative reasoning (proof by contradiction). Given this, it seems plausible that I might try rewriting the proof to use cut statements heavily, so that I can still take advantage of the backwards proof style of coq. *)

Lemma identity_unique_surjection (n : nat) (f : n ~{ Δ }~> n)
  (p : surjective f)
  : Build_monotonic_fn_sig n n [ffun x => x] (idmap_monotonic n) = f.
Proof.
  apply: val_inj => /=.
  apply/ffunP => x.
  rewrite ffunE.
  destruct (findP [ffun a => a != f a ] (enum 'I_n))
    as [ i | i iltn fi_neq_i i_is_least].
  { 
    rewrite has_exists negb_exists in i.
    rewrite -(rwP forallP) in  i.
    specialize i with x.
    now rewrite ffunE negbK -(rwP eqP) in i.
  }
  {
    rewrite size_enum_ord in iltn.
    set i' := Ordinal iltn.
    specialize fi_neq_i with i'.
    rewrite (nth_ord_enum i' i') ffunE in fi_neq_i.
    rewrite neq_ltn in fi_neq_i.
    move/orP: fi_neq_i => [ i_lt_fi | i_gt_fi].
    {
      rewrite -(rwP (surjectiveP f)) in p.
      destruct (p i') as [a pfeq].
      have a_lt_i' : a < i'.
      {
        rewrite ltnNge.
        rewrite -(rwP negP) => i_leq_a.
        have t := (snd (rwP (monotonicP (val f)))) (valP f) _ _ i_leq_a.
        rewrite pfeq in t.
        rewrite ltnNge in i_lt_fi.
        rewrite -(rwP negP) in i_lt_fi.
        done.
      }
      specialize i_is_least with i' a.
      have k:= i_is_least a_lt_i'.
      rewrite nth_ord_enum in k.
      rewrite ffunE in k. 
      apply (negbFE ) in k.
      rewrite -(rwP eqP) in  k.
      rewrite -k in pfeq.
      rewrite pfeq in a_lt_i'.
      now rewrite ltnn in a_lt_i'.
    }
    {
      have k := snd (rwP (@image_injP _ _ f (mem 'I_n))).
      have m : #|[seq f x | x in mem 'I_n]| == #|'I_n|. {
        apply/eqP; apply: eq_card.
        move => a.
        apply/idP.
        set t := a \in 'I_n.
        destruct (@idP t) as [| n0].
        {
          rewrite /surjective in p; move/forallP: p => p.
          now specialize p with a.
        }
        {
          intro m. contradiction n0. rewrite /t.
          easy.
        }
      }
      have km := k m.
      cut ( ~ (injective f)). {
        move=> a. contradiction a.
        move =>  s0 s1.
        exact: (km s0 s1 _ _).
      }
      cut (f (f i') = f i'). {
        move=> a b.
        cut(~ f i' = i'). {
          move => Z; contradiction Z; exact (b (f i') i' a).
        }
        move =>e .
        rewrite e in i_gt_fi. rewrite ltnn in i_gt_fi. done.
      }
      have r:= i_is_least i' (f i') i_gt_fi.
      rewrite ffunE in r.
      rewrite nth_ord_enum in r.
      apply negbFE in r.
      symmetry.
      apply/eqP.
      done.
    }
  } 
Qed.   
        
