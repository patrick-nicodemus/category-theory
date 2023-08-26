Require Import Category.Lib.
Require Import Theory.Category.

Require Import Category.Instance.Simplex.NaturalNumberArithmetic.
Require Import Category.Instance.Simplex.FinType.
Require Import Category.Instance.Simplex.Stdfinset.Stdfinset.
Require Import Category.Instance.Simplex.Stdfinset.face_degeneracy.

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

(** We start to do some work towards factorization. In particular we have:

- if [ f : n -> m.+1 ] and [i ∉ im f], then there is [g : n -> m] with δi ∘ g = f.  ( [facemap_factoring_eq], [facemap_factoring_eq] )

- We define [hitstwice f i := [exists x, y, x < y & f x = i & f y = i ]. We show that [f] is injective iff [hitstwice f] is the constant predicate at False.

- We define [not_injective_hitstwice_val] which associates to each non-injective function a value which it hits twice.

- Based on this we define [degeneracy_factoring_map], which, given f : n -> .+1 such that [f] hits [i] twice, gives a factoring of f through the degeneracy [σi].

- [factoring_preserves_surjectivity] : If f is surjective then so is the [degeneracy_factoring_map].

- [surjective_card] - if [f : 'I_m -> 'I_n] is surjective, then n <= m.

*)


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

Local Notation δ := δ_stdfinset.

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
  apply (introF (eqP)); intro eq.
  change (nat_of_ord (f x)) with (val (f x)) in eq;
    change (nat_of_ord i) with (val i) in eq.
  apply val_inj in eq.
  apply (rwP negP) in p; apply p; rewrite -eq.
  exact: image_f.
Qed.


Definition hitstwice {n m : nat} (f : 'I_(m)^n) (i : 'I_m) :=
  [exists x : 'I_n, exists y : 'I_n, (x < y) && (f x == i) && (f y == i) ].

Proposition nltm_not_injective {n m : nat} (f : 'I_(m.+1)^n) (p : m.+1 < n)
  : ~~ (injectiveb f).
    simpl. apply (rwP negP); intro H; revert p. apply (rwP negP).
    rewrite -ltnNge ltnS. rewrite -(card_ord m.+1) -(card_ord n).
    apply (leq_card f); by apply/injectiveP.
Qed.

Lemma empty_type_seq (A : finType) (l : seq A) : #|A|=0 -> l = [::].
Proof.
  move => H.
  case l; [ by [] | move => s].
  now move: (fintype0 s H).
Qed.

(** TODO - come back to this proof later and see if it can be edited shorter. The main sources of bureaucratic overhead in these proofs are boolean reflection stuff and reducing arguments about ordinals in 'I_n to arguments about natural numbers *)
Proposition not_injective_hitstwice {n m : nat} (f : 'I_m^n) :
  (injectiveb f) <-> (hitstwice f =1 xpred0).
Proof.
  unfold injectiveb, dinjectiveb.
  split. {
    move => H a.
    apply negbTE.
    apply/negP => hits2x.
    move : H. 
    apply/negP.
    unfold hitstwice in hits2x.
    move/existsP : hits2x => [x exy].
    apply/(@uniqPn _ a). 
    move/existsP : exy => [y exprop].
    exists x, y.
    move/andP : exprop => [t1 fy_eq_a].
    move/andP : t1 => [x_lt_y fx_eq_a].
    rewrite x_lt_y.
    rewrite size_map.
    rewrite size_enum_ord.
    rewrite (@nth_map _ x);
      [ | case x as [xval xbd];
          simpl; by rewrite size_enum_ord].
    rewrite (@nth_map _ x _ a);  [ | case x as [xval xbd]];
      [ | case y as [yval ybd];
          simpl; by rewrite size_enum_ord].
    do 2 rewrite nth_ord_enum.
    move/eqP : fx_eq_a => -> .
    move/eqP : fy_eq_a => -> .
    case y as [yval ybd]; simpl.
    rewrite ybd.
    done.
  }
  {
    intros.
    destruct m.
    { have -> :([seq f i | i <- _] = [::]).
      { move => ?.
        apply empty_type_seq, card_ord.
      }
      done.
    }
    rewrite -[uniq _]negbK.
    apply/negP.
    rewrite -(rwP (uniqPn ord0)).
    move => [i [j [i_lt_j j_lt_size]]].
    rewrite size_map size_enum_ord in j_lt_size.
    have j0 : 'I_n by exact (Sub j j_lt_size).
    rewrite (nth_map j0 ord0 f); last first.
    { rewrite size_enum_ord; auto with arith. }
    rewrite (nth_map j0 ord0 f); [ | now rewrite size_enum_ord ].
    have i_lt_n : (i < n). { auto with arith. }
    change i with (nat_of_ord (Sub i i_lt_n)).
    rewrite nth_ord_enum.
    change j with (nat_of_ord (Sub j j_lt_size)).
    rewrite nth_ord_enum.
    set ii := (Sub i i_lt_n).
    set jj := (Sub j j_lt_size).
    move => A.
    have: hitstwice f (f ii). 
    { rewrite /hitstwice.
      apply/existsP. exists ii.
      apply/existsP. exists jj.
      simpl. rewrite i_lt_j eq_refl eq_sym /=.
      now apply/eqP.
    }
    rewrite H.
    done.
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

Local Notation σ := σ_stdfinset.

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
      apply ord_neq_nat_neq in y_neq_i.
      apply (rwP eqP) in fx2eqi; now rewrite fx2eqi.
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
        unfold s. 
        apply (introF eqP). 
        destruct i;
          apply ord_neq_nat_neq in y_neq_i; simpl in y_neq_i.
        done.
      } by rewrite RW.
    }
  } 
Qed.      
