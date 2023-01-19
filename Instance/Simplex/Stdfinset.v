Require Import Category.Lib.
Require Import Theory.Category.

Require Import Category.Instance.Simplex.NaturalNumberArithmetic.
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

Require Import mathcomp.ssreflect.tuple.
Require Import mathcomp.ssreflect.finfun.

Set Primitive Projections.
Set Universe Polymorphism.

Notation "''I_' n" := (ordinal n).

(** In this file we define the category whose objects are "standard finite sets" [[n] = { 0, ... n-1}] and whose morphisms are all functions between them. We define the coface and codegeneracy maps δi, σj in this category, but we do not prove they are monotonic. *)

(** We start to do some work towards factorization. In particular we have:

- if [ f : n -> m.+1 ] and [i ∉ im f], then there is [g : n -> m] with δi ∘ g = f.  ( [facemap_factoring_eq], [facemap_factoring_eq] )

- We define [hitstwice f i := [exists x, y, x < y & f x = i & f y = i ]. We show that [f] is injective iff [hitstwice f] is the constant predicate at False.

- We define [not_injective_hitstwice_val] which associates to each non-injective function a value which it hits twice.

- Based on this we define [degeneracy_factoring_map], which, given f : n -> .+1 such that [f] hits [i] twice, gives a factoring of f through the degeneracy [σi].

- [factoring_preserves_surjectivity] : If f is surjective then so is the [degeneracy_factoring_map].

- [surjective_card] - if [f : 'I_m -> 'I_n] is surjective, then n <= m.

We define [findlast] which behaves opposite to [find] in ssreflect. We define the expected dual theorems for [findlast] as for [find].

We define [find_ord] and [findlast_ord] which are the expected variants of [find] and [findlast] for ordinals, except that in [find_ord] and [findlast_ord] we explicitly assume that the element we are looking for exists, whereas for [find] and [findlast] the search may fail.

We define predicates [least_st] and [gtest_st] which say that a given element of ['I_n] is the least / greatest element satisfying a certain predicate, and use these to write specifications for [find_ord] and [findlast_ord].
*)

Section stdfinset.

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

Definition gtest_not_in_img {n m: nat} (f : 'I_m^n) (p : ~~ surjective f)
  : 'I_m.
Proof.
  unfold surjective in p; rewrite negb_forall in p.
  apply existsPS in p; destruct p as [x Px].
  exact: [ arg max_ ( i > x | i \notin (image f 'I_n) ) (nat_of_ord i) ].
Defined.

Proposition facemap_factors_subpf {n m : nat} (f : 'I_(m.+1)^n)
  (i : 'I_m.+1)
  (p : i \notin (image f 'I_n))
  (x : 'I_n)
  : unbump i (f x) < m.
Proof.
  assert (am1 : ~ i = f x );
    [ intro r; rewrite r in p; apply (rwP negP) in p;
      contradiction p; exact: image_f |].
  destruct (f x) as [yval ybd]; unfold unbump; simpl.
  remember (i < yval) as b eqn:Heqn; apply symmetry in Heqn; destruct b.
  { rewrite subn1; clear am1; rewrite ltnS in ybd. 
    by rewrite (ltn_predK Heqn). }
  { apply (negbT) in Heqn. rewrite -ltnNge ltnS leq_eqVlt in Heqn.
    apply (rwP orP) in Heqn; destruct Heqn as [eq | lt].
    { apply (rwP eqP) in eq. contradiction am1; by apply: val_inj. }
    { destruct i as [ival ibd];
        clear p am1. simpl in lt; rewrite ltnS in ibd.
      rewrite subn0. by apply (@leq_trans ival). }
  }
Qed.

(* ∃ g : 'I_m^n, f = compose (δ i) g. *)
Definition facemap_factoring_map {n m : nat} (f : 'I_(m.+1)^n)
  (i : 'I_m.+1) (p : i \notin (image f 'I_n)) : 'I_m^n.
Proof.
  apply finfun; intro x; set y := f x; simpl in y.
  refine (Sub (unbump i y) _); exact: facemap_factors_subpf.
Defined.

Proposition facemap_factoring_eq {n m : nat} (f : 'I_(m.+1)^n) (i : 'I_m.+1)
  (p : i \notin (image f 'I_n))
  : let g := facemap_factoring_map f i p in
    f = compose (δ i) g.
Proof.
  simpl.
  apply ffunP; intro x; simpl; rewrite ! ffunE.
  unfold lift; apply val_inj; simpl. 
  rewrite unbumpKcond.
  set z:= ( _ == _ ); cut (z = false);
          [ intro RW; by rewrite RW |]; unfold z; clear z.
  apply (introF (eqP)); intro eq; apply val_inj in eq.
  apply (rwP negP) in p; apply p; rewrite -eq.
  exact: image_f.
Qed.

Definition hitstwice {n m : nat} (f : 'I_(m.+1)^n) (i : 'I_m.+1) :=
  [exists x : 'I_n, exists y : 'I_n, (x < y) && (f x == i) && (f y == i) ].

Proposition nltm_not_injective {n m : nat} (f : 'I_(m.+1)^n) (p : m.+1 < n)
  : ~~ (injectiveb f).
    simpl. apply (rwP negP); intro H; revert p. apply (rwP negP).
    rewrite -ltnNge ltnS. rewrite -(card_ord m.+1) -(card_ord n).
    apply (leq_card f); by apply/injectiveP.
Qed.

(** TODO - come back to this proof later and see if it can be edited shorter. The main sources of bureaucratic overhead in these proofs are boolean reflection stuff and reducing arguments about ordinals in 'I_n to arguments about natural numbers *)
Proposition not_injective_hitstwice {n m : nat} (f : 'I_(m.+1)^n) :
  (injectiveb f) <-> (hitstwice f =1 xpred0).
Proof.
  unfold injectiveb, dinjectiveb.
  split.
  { intro H. move/uniqPn : H => H.
    specialize H with ord0. intro y. unfold hitstwice.
    apply negbTE; apply/existsPn; intro x1; apply/existsPn; intro x2.
    apply/negP; intro k. contradiction H.
    exists x1, x2. move/andP in k; destruct k as [conj fx2eqy].
    move/andP in conj; destruct conj as [x1_lt_x2 fx1eqy].
    split; [ done
           | rewrite size_map size_enum_ord; by destruct x2
           | simpl
      ].
    rewrite (nth_map x1 ord0); [ | rewrite size_enum_ord; by destruct x1].
    rewrite (nth_map x2 ord0); [ | rewrite size_enum_ord; by destruct x2].
    do 2! rewrite nth_ord_enum.
    apply (rwP eqP) in fx1eqy, fx2eqy. rewrite fx1eqy fx2eqy; done.
  }
  {
    intro H. unfold injectiveb, dinjectiveb. apply/(uniqPn ord0).
    intro K. destruct K as [i [j [lt bd eq]]].
    rewrite size_map size_enum_ord in bd. set j' := Ordinal bd.
    assert (ibd : i < n) by  (apply (@leq_ltn_trans j);
                              [ exact : ltnW |]; done).
    set i' := Ordinal ibd.
    pose Mp := H (f i'); unfold hitstwice in Mp; simpl in Mp.
    refine (Bool.eq_true_false_abs _ _ Mp).
    apply/existsP; exists i'.
    apply/existsP; exists j'.
    rewrite lt eq_refl; simpl.
    rewrite (@nth_map _ i' _ ord0 f) in eq;
      [ | rewrite size_enum_ord; exact: ibd].
    rewrite (@nth_map _ j' _ ord0 f) in eq;
      [ | rewrite size_enum_ord; done].
    simpl in eq.
    change i with (nat_of_ord i') in eq.
    change j with (nat_of_ord j') in eq.
    rewrite (@nth_ord_enum n i' i') in eq.
    rewrite (@nth_ord_enum n j' j') in eq.
    apply/eqP; by symmetry.
  }
Qed.
    
Definition not_injective_hitstwice_val {n m : nat} (f : 'I_(m.+1)^n)
 : 'I_m.+1.
Proof.
  set z := [ pick i | hitstwice f i].
  destruct (@pickP _ (hitstwice f)) as [x | e].
  { exact [ arg min_(i < x | hitstwice f i ) (nat_of_ord i) ]. }
  { exact ord0. }
Defined.
    
Proposition not_injective_hitstwice_spec {n m : nat} (f : 'I_(m.+1)^n)
  : ~~ (injectiveb f) -> hitstwice f (not_injective_hitstwice_val f).
Proof.
  intro p.
  unfold not_injective_hitstwice_val.
  destruct (@pickP _ (hitstwice f)) as [x ht | e].
  { pose z := (@arg_minnP _ x (hitstwice f) (@nat_of_ord m.+1) ht).
    set k := [ arg min_ (i < x | _ ) i] in z *;
             destruct z as [? hty ?]; exact: hty. }
  { apply not_injective_hitstwice in e; rewrite e in p; discriminate. }
Qed.

Definition degeneracy_factoring_map {n m : nat} (f : 'I_(m.+1)^n)
  (i : 'I_m.+1) (p : hitstwice f i) : 'I_(m.+2)^n.
Proof.
  apply finfun; intro x.
  unfold hitstwice in p.
  apply existsPS in p; destruct p as [x1 p].
  assert (z : i < m.+2) by abstract(destruct i as [ival ibd];
                                      by apply (@leq_trans m.+1)).
  set i' := Ordinal z.
  exact: (if (x <= x1) && (f x == i) then i' else (lift i' (f x))).
Defined.

Proposition degeneracy_factoring_map_eq {n m : nat}
  (f : 'I_(m.+1)^n) (i : 'I_m.+1)
  (p : hitstwice f i) 
  : let g := degeneracy_factoring_map f i p in
    f = compose (σ i) g. 
Proof.
  simpl. apply ffunP; intro x; rewrite ! ffunE;
    apply val_inj; unfold degeneracy_factoring_map;
    simpl.
  set k := existsPS _ _ _; destruct k as [x1 k'].
  
  remember ((x <= x1) && (f x == i)) as b eqn:Heqn; apply symmetry in Heqn;
    destruct b; rewrite Heqn.
  { simpl.
    move/andP : Heqn => [Heqn1 Heqn2]; move/eqP :Heqn2  ->.
    unfold unbump.
    now rewrite ltnn subn0. }
  { by symmetry; apply: bumpK. }
Qed.

Lemma σ_i_eq_i { n : nat } (i : 'I_n.+1 ) (x : 'I_n.+2)
  : ( σ i x == i ) =
      ( x == (ord_upcast i)) || (x == (lift (ord_upcast i) i)).
Proof.
  unfold σ; rewrite ffunE.
  unfold lift, ord_upcast; destruct x as [xval xbd], i as [ival ibd].
  do ! ( rewrite -(@inj_eq _ _ val); [ | exact: val_inj ]; simpl).
     unfold bump; rewrite leqnn.
     exact: σ_i_eq_i_nat.
Qed.

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

(* This proof is unpleasantly long, but at least it seems stepwise simple enough to follow. *)
(* I hope it can be shortened. *)
Proposition factoring_preserves_surjectivity {n m : nat} (f : 'I_(m.+1)^n)
  (i : 'I_m.+1) (p : hitstwice f i) ( issurj : surjective f )
  : surjective (degeneracy_factoring_map f i p).
 Proof.
  unfold surjective; apply (rwP forallP); intro y; apply (rwP imageP).
  unfold degeneracy_factoring_map.
  set k := existsPS _ _ _; destruct k as [x1 k].
  (* Proof summary:
    In the following commments let g := degeneracy_factoring_map f i. *)
  (* The assumption "hitstwice" gives us x1 and x2, x1 < x2, such that f x1 = f x2 = i. *)
  (* g is defined by :  g x = if (x == x1) then i else (bump i (f x)). *)
  (* Let y ∈ [n+2]. Then we argue the surjectivity of g as follows : 
     - if y = i, then g x1 = y; done.
     - else, if y = i+1, then g x2 = y, because x2 ≠ x1 (x1 < x2),
                                  so g x2 = bump i (f x2) = i + 1.
     - else, y ≠ i and y ≠ i+1. Use surjectivity of f to choose x such that 
       f x = unbump i y; then g x = bump i (unbump i y) = y (because x ≠ x1). *)
  (* By cases on whether y = i. *)
  destruct (eq_comparable y (ord_upcast i)) as [y_eq_i | y_neq_i].
  { exists x1; [ done |].
    rewrite ffunE leqnn /= .
    have k' := k.
    rewrite -(rwP existsP) in k'.
    destruct k' as [x2 H].
    do 2 rewrite -(rwP andP) in H.
    destruct H as [[x1_lt_x2 fx1_eq_i] fx2_eq_i].
    rewrite fx1_eq_i. apply val_inj.
    destruct i.
    unfold ord_upcast in y_eq_i. 
    exact: (f_equal val y_eq_i).
  }
  { set z := (degeneracy_factoring_map_subproof _ _ _ _ _ _); clearbody z.
    apply (rwP existsP) in k; destruct k as [x2 cong1].
      apply (rwP andP) in cong1; destruct cong1 as [cong2 fx2eqi].
      apply (rwP andP) in cong2; destruct cong2 as [x1ltx2 fx1eqi].
      destruct (eq_comparable y (lift (ord_upcast i) i)) as
        [y_eq_si | y_neq_si].
      { exists x2; [ done |]; rewrite ffunE.
        rewrite leqNgt x1ltx2 /=.
      rewrite y_eq_si; apply val_inj; simpl.
      do ! ord_to_arith; apply (rwP eqP) in fx2eqi; rewrite fx2eqi;
         destruct i; done.
    }
    { apply (rwP (surjectiveP f)) in issurj.
      destruct (issurj (σ i y)) as [x fx_eq_y].
      exists x; [ done |]; rewrite ffunE.
      (* y = i *)
      assert (H: (f x == i) = false ). {
        (* x1 ≠ x because f x1 = i but f x ≠ i. 
           In turn f x ≠ i because f x = unbump i y and 
           y is neither i nor i+1, so unbump i y ≠ i. *)
        apply (introF eqP); intro c.
        rewrite c in fx_eq_y.
        unfold σ in fx_eq_y. rewrite ffunE in fx_eq_y.
        have t := (f_equal val fx_eq_y).
        simpl in t.
        unfold unbump in t.
        destruct (@ltP i y) as [i_lt_y | i_ge_y].
        { 
          contradiction y_neq_si.
          unfold lift, ord_upcast.
          apply val_inj; simpl.
          unfold bump.
          destruct i as [i ibd], y as [yval ybd].
          simpl in *.
          destruct yval.
          { apply False_rect. move/ltP :i_lt_y. done. }
          rewrite subn1 /= in t.
          rewrite leqnn add1n.
          now destruct t.
        }
        {
          rewrite subn0 in t.
          contradiction y_neq_i.
          apply val_inj.
          destruct i as [ival ibd], y as [yval ybd].
          simpl in *.
          symmetry; exact: t.
        } 
      }
      rewrite H andbF; apply val_inj;
        rewrite fx_eq_y; unfold σ; rewrite ffunE; simpl.
      rewrite unbumpKcond.
      set s := ( _ == _ ); assert (RW : s = false). {
        unfold s. ord_to_arith.
        apply (introF eqP). 
        destruct i;
          apply ord_neq_nat_neq in y_neq_i; simpl in y_neq_i.
        done.
      } by rewrite RW.
    }
  } 
Qed.      

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

End stdfinset.

Section findlast.
  Variable A : Type.
  Variable P : pred A.

  Definition findlast (l : seq A) := size l - (find P (rev l)).+1.
  Proposition has_findlast l : has P l -> findlast l < size l.
  Proof.
    intro H. unfold findlast. 
    assert (z : has predT l) by (unshelve eapply (@sub_has _ P); done).
    rewrite has_predT in z; by rewrite ltn_subrL z.
  Qed.
  Proposition findlast_size s : findlast s <= size s. 
  Proof.
    unfold findlast; exact: leq_subr.
  Qed.
  Lemma findlast_cat s1 s2 :
    findlast (s1 ++ s2) = if has P s2 then size s1 + findlast s2
                          else findlast s1.
  Proof.
    remember (has P s2) as b eqn:Heqn; apply symmetry in Heqn; destruct b.
    { assert (z := has_findlast s2 Heqn).
      unfold findlast.
      erewrite (@addnBA (size s1) (size s2) (find P (rev s2)).+1); 
        [ | by rewrite -size_rev -has_find has_rev].
      rewrite size_cat.
      cut (find P (rev (s1 ++ s2)) = (find P (rev s2)));
        [ intro RW; by rewrite RW |
          by rewrite rev_cat find_cat has_rev Heqn ].
    } {
      unfold findlast.
      cut (find P (rev (s1 ++ s2)) = (size s2 + find P (rev s1))); 
        [ intro H; rewrite size_cat H;
            by rewrite addnC -addnS (subnDl (size s2)) |].
      by rewrite rev_cat find_cat has_rev Heqn size_rev.
    } 
  Qed.

  Definition has_default (l : seq A) (p : has P l) : A.
  Proof.
    unfold has in p; destruct l; done.
  Defined.

  Lemma findlast_rcons (s : seq A) (x : A) :
    findlast (rcons s x) = if P x then size s else findlast s.
  Proof.
    remember (P x) as b eqn:Heqn; destruct b; unfold findlast;
      rewrite rev_rcons;
      simpl; rewrite -Heqn size_rcons; 
      [  by  rewrite subn1 | by rewrite subSS ].
  Qed.

  Lemma after_findlast (x : A) (s : seq A) (i : nat) :
    findlast s < i < size s -> P (nth x s i) = false.
  Proof.
    intro H; apply (rwP andP) in H; destruct H as [fls_lt_i i_lt_size].
    unfold findlast in fls_lt_i. 
    rewrite -(revK s) nth_rev size_rev; [ | done].
    apply: before_find.
    destruct s; [ discriminate |].
    assert (z : find P (rev (a :: s )) <= size (a :: s))
      by ( rewrite -size_rev; exact: find_size).
    rewrite (ltn_subCl i_lt_size z).
    simpl size in *.
    rewrite subnS in fls_lt_i; rewrite ltnS.
    set m := ( a in a <= _). apply (@leq_trans m.-1.+1);
      [ exact: leqSpred| assumption].
  Qed.
    
  Lemma nth_findlast (a : A) (s : seq A)
    : has P s -> P (nth a s (findlast s)).
  Proof.
    revert s. apply: last_ind; [ done | ].
    intros s x IH H.
    rewrite findlast_rcons.
    rewrite nth_rcons.
    remember (P x) as b eqn:Heqn; apply symmetry in Heqn; destruct b;
      [ by rewrite ltnn eq_refl |
        rewrite has_rcons Heqn in H; simpl in H;
        rewrite has_findlast; [ exact: (IH H) | assumption]
      ].
  Qed.
End findlast.

Definition find_ord { n : nat } (P : pred 'I_n )
  : has P (enum 'I_n) -> 'I_n.
Proof.
  intro H; exists (find P (enum 'I_n));
    rewrite has_find in H;
    by rewrite size_enum_ord in H.
Defined.

Definition least_st {n : nat} (P : pred 'I_n) : pred 'I_n :=
  fun x => (P x && [forall y, P y ==> (x <= y)]).

Proposition find_ord_spec {n : nat} (P : pred 'I_n)
  (p : has P (enum 'I_n))
  : least_st P (find_ord P p).
Proof.
  set k := (has_default _ P _ p).
  unfold least_st; apply/andP; split.
  { cut (nth k (enum 'I_n) (find P (enum 'I_n)) = find_ord P p);
      [ intro A; rewrite -A; by apply nth_find |].
    rewrite [find P (enum 'I_n)]/(val (find_ord P p));
      exact: nth_ord_enum.
  }
  {
    apply (rwP forallP); intro x; apply/implyP; intro Px.
    rewrite -[_ <= _]negbK -ltnNge; apply (rwP negP); intro H; simpl in H.
    assert (z := (before_find k H)).
    cut ( nth k (enum 'I_n) x = x).
    { intro R; rewrite R in z; rewrite Px in z; discriminate. }
    exact: nth_ord_enum.
  }
Qed.

Definition findlast_ord {n : nat} (P : pred 'I_n) :
  has P (enum 'I_n) -> 'I_n.
Proof.
  intro;  exists (findlast _ P (enum 'I_n)); rewrite -{7}(size_enum_ord n).
  exact: has_findlast.
Defined.

Definition gtest_st {n : nat} (P : pred 'I_n) :=
  fun x : 'I_n => P x && [forall y : 'I_n, P y ==> (y <= x)].

Proposition gtest_st_spec {n : nat} (P : pred 'I_n) (p : has P (enum 'I_n))
  : gtest_st P (findlast_ord P p).
Proof.
  unfold gtest_st. set k := (has_default _ P _ p).
  apply/andP; split.
  {
    cut (nth k (enum 'I_n) (findlast _ P (enum 'I_n)) = findlast_ord P p);
      [ intro H; rewrite <- H; by apply nth_findlast |].
    rewrite [findlast 'I_n P (enum 'I_n)]/(val (findlast_ord P p)).
    exact: nth_ord_enum.
  }
  { 
    apply (rwP forallP); intro x. apply/implyP; intro Px.
    simpl. rewrite leqNgt. apply (rwP negP); intro fltx.
    cut (P x = false). { intro H; rewrite Px in H; discriminate. }
    rewrite -(nth_ord_enum k x).
    apply: after_findlast; rewrite fltx; simpl.
    rewrite size_enum_ord; by destruct x.
  }
Qed.
