From Ltac2 Require Import Ltac2.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Instance.Simplex.NaturalNumberArithmetic.
Require Import stdpp.finite stdpp.vector.

From Hammer Require Import Hammer Tactics.
Require Import Arith.

Open Scope nat.
Definition ord_fn_equiv (n : nat) (f g : nat -> nat)
  := forall x, x < n -> f x = g x.

Require Import ssreflect.

Set Primitive Projections.
Set Universe Polymorphism.


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

Definition ordinal (n : nat) := { x | x < n }.

Section stdfinset.

  Local Open Scope type_scope.
  
  #[export] Instance eq_dec_ord {n : nat} : EqDecision (ordinal n).
  Proof.
    ltac1:(typeclasses eauto).
  Qed.

  Definition ord_incl {n m: nat} `{H : n <= m} : ordinal n -> ordinal m.
  Proof.
    refine '(fun a =>  match a with
                      | exist _ x v => exist _ x _
                      end).
    abstract(ltac1:(sfirstorder)).
  Defined.

  (* Fixpoint ordlist' (n m: nat) (t : rgeq n m):  list (ordinal n) := *)
  (*   match t with *)
  (*   | rgeq_refl _ => [] *)
  (*   | rgeq_succ _ k t' => *)
  (*       (exist _ k (rgeq_implies_lgeq _ _ t') ) :: ordlist' _ k.+1 t' *)
  (*   end. *)

  (* Definition ordlist (n : nat) := ordlist' n 0 rgeq_n_0. *)

  Definition ordlist (n: nat) := list_filter_sig (fun x => x < n) (seq 0 n).


  Proposition nodup_ordlist {n : nat} : NoDup (ordlist n).
  Proof.
    apply (NoDup_fmap_1 proj1_sig).
    unfold ordlist.
    rewrite list_filter_sig_filter.
    apply NoDup_filter.
    exact (NoDup_seq _ _).
  Defined.
  
  #[export] Instance fin_ord {n : nat} : Finite (ordinal n).
  Proof.
    exists (ordlist n).
    { exact nodup_ordlist. }
    { intros [xval xbd].
      unfold ordlist.
      apply (elem_of_list_fmap_2_inj proj1_sig); simpl.
      rewrite list_filter_sig_filter.
      apply elem_of_list_filter.
      split. { assumption. } { apply elem_of_seq. auto with arith. }
    } 
  Defined.

  (* Locate equiv. *)
  (* Search list. *)
  (* Print Coq.Logic.FinFun. *)
  (* Search list. *)
  (* Search vec. *)
  (* Print Vector.t.
   *)
  Print stdpp.vector.
  Locate fin.

  Definition vector_composition {n m k : nat}
    (f : vec (fin m) n) (g : vec (fin k) m) : vec (fin k) n
    := (fun_to_vec (fun x : fin n => (g !!! (f !!! x)))).

  Definition vector_id (n : nat) : vec (fin n) n := fun_to_vec (fun x => x).
  
Program Definition stdfinset : Category :=
  {|
    obj     := nat;
    hom     := fun n m => vec (fin m) n;
    homset  := fun _ _ => {| Setoid.equiv := eq |}; 
    Category.id      := fun n => vector_id n ;
    Category.compose := fun _ _ _ f g => vector_composition g f
  |}.

(** Right identity law - The main lemma of this proof is function extensionality [ffunP]. [ffunE] simplifies [ [ffun x => t] a] to [t[x/a]]; presumably the reason this needs to be explicitly called as lemma is to prevent term explosion through unnecessary simplification. *)
Next Obligation.
  intros n m f; simpl in f; simpl.
  apply vec_eq. intro i.
  unfold vector_composition.
  simpl.
  rewrite lookup_fun_to_vec.
  unfold vector_id.
  rewrite lookup_fun_to_vec.
  reflexivity.
Qed.
(* Left identity law, same proof as before *)
Next Obligation.
  simpl.
  intros n m f.
  unfold vector_composition, vector_id.
  apply vec_eq; intro i;
    now rewrite 2 lookup_fun_to_vec.
Qed.
(* Associativity of composition law, same proof as before *)
Next Obligation.
  simpl.
  intros a b c d f g h.
  apply vec_eq; intro i.
  unfold vector_composition.
  now rewrite 4 lookup_fun_to_vec.
Qed.
(* Associativity of composition law, same proof as before *)
Next Obligation.
  simpl.
  intros a b c d f g h.
  apply vec_eq; intro i.
  unfold vector_composition.
  now rewrite 4 lookup_fun_to_vec.
Qed.

Open Scope nat_scope.

Definition δ_stdfinset {n : nat} (i : fin n.+1)
  : @hom stdfinset n n.+1.
  
  := [ffun j : 'I_n => lift i j].

Lemma σ_subproof (n : nat) (i : 'I_(n.+1)) (j : 'I_(n.+2))
  : unbump i j < n.+1.
Proof.
  rewrite /unbump.
  destruct (@idP (i < j)).
  {
    arith_simpl.
    
    destruct (ltnP i j).
    {
      have t := valP j.
      auto with arith.
      
      time
        
      
      j < n.+2  ->  j - 1 < n.+1 

      hammer.
      
      sauto.
    Print Bool.reflect.
    rdestruct (i < j)
    Set Printing All.
   
    (* 
      Idea: Intelligent case analysis.
            Whenever we have a 
     *)

    sauto lq:on. }
  
  
  hammer.

           
  hammer.
  
  sfirstorder.
Qed.

Definition monotonic (n : nat) (f : nat -> nat)
  := forall i j, i <= j -> j < n -> f i <= f j.

Definition isordmap (n m : nat) (f : nat -> nat)
  := forall i, i < n -> f i < m.

Print Category.

Definition stdfinset : Category.
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
  {
    intro n. exists (fun x => x).
    abstract(sfirstorder).
  }
  { 
    intros n m k [ffun fpfs] [gfun gpfs].
    exists (fun x => ffun (gfun x)).
    abstract(sfirstorder).
  } 
  {
    abstract(
    intros x y z [gffun [gmon gisordmap]] [ffun [fmon fisordmap]] H;
    simpl in H;
    intros [gffun' [gmon' gisordmap']] [ffun' [fmon' fisordmap']] H1;
    simpl in H1;
    simpl;
    sfirstorder).
  }
  all: abstract(hauto lq: on).
Defined.
Print stdfinset.
