Require Import Category.Lib.
Require Import Theory.Category.

(* Require Import Category.Instance.Simplex.NaturalNumberArithmetic. *)
(* Require Import Category.Instance.Simplex.Ordinals. *)

Require Import ssreflect.
Require Import ssrfun.
Require Import ssrbool.

Require Import mathcomp.ssreflect.seq.
Set Warnings "-notation-overridden".
Require Import mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finfun. (*  *)
Require Import mathcomp.ssreflect.tuple.
Require Import Coq.Logic.FinFun.
(* From Hammer Require Import Tactics Hammer Reflect. *)

Open Scope nat_scope.

(** Definition of surjective. Reflection property of surjectivity. *)
Definition surjective {A B : finType} (f : {ffun A -> B}) := 
  [forall y : B, y \in (image f A)].

Proposition surjectiveP {A B : finType} (f : {ffun A -> B})
  : reflect (Surjective f) (surjective f).
Proof.
  unfold surjective, Surjective.
  apply: (iffP forallP).
  { intros H y. set in_img := H y.
    exists (iinv in_img). exact: f_iinv. }
  { intros H x. simpl. apply (rwP mapP).
    set z:= (H x); destruct z as [a pf].
    unshelve eapply ex_intro2;
      [ exact: a
      | exact: mem_enum
      | symmetry; rewrite -pf; by apply: f_equal ]. }
Defined.

Proposition existsPS (A : finType) (P : pred A) :
  [exists x, P x] -> { x : A & P x }.
Proof.
  (* set j := [pick x : A | P x]. *)
  intro H.
  destruct (pickP P) as [x i | e].
  { exists x; exact: i. }
  { apply (rwP existsP) in H.
    apply False_rect; induction H;
      rewrite ( e x) in H; discriminate. }
Defined.

(* first argument is the section, second argument is the retraction *)
Definition splits {A : finType} {B : Type} (f: A -> B) (g : B -> A)
  := [forall x, g (f x) == x].

Definition splits_spec {A B : Type} (f : A -> B) (g : B -> A) :=
  g \o f =1 id.

Definition splitsP {A : finType} {B : Type} (f : A -> B) (g : B -> A)
  : reflect (splits_spec f g) (splits f g).
Proof.
  exact eqfunP.
Qed.

(* Search Injective. *)
(* Endo_Injective_Surjective:
  ∀ [A : Type],
  Finite A
  → ListDec.decidable_eq A → ∀ f : A → A, Injective f <-> Surjective f
Injective_map_NoDup:
  ∀ [A B : Type] [f : A → B] [l : seq A],
  Injective f → List.NoDup l → List.NoDup (List.map f l)
Fin2Restrict.extend_injective:
  ∀ [n : nat] (f : Fin.t n → Fin.t n),
  bInjective n (Fin2Restrict.extend f) <-> Injective f
Injective_Surjective_Bijective:
  ∀ [A B : Type],
  Finite A
  → EqDec B → ∀ [f : A → B], Injective f → Surjective f → Bijective f
Fin2Restrict.restrict_injective:
  ∀ [n : nat] [f : nat → nat] (h : bFun n f),
  Injective (Fin2Restrict.restrict h) <-> bInjective n f
Injective_carac:
  ∀ [A B : Type] [l : seq A],
  Listing l → ∀ f : A → B, Injective f <-> List.NoDup (List.map f l)
Injective_list_carac:
  ∀ [A B : Type],
  ListDec.decidable_eq A
  → ∀ f : A → B,
    Injective f <->
    (∀ l : seq A, List.NoDup l → List.NoDup (List.map f l))
 *)

Proposition splits_implies_injective {A B : Type} {f : A -> B} {g : B -> A}
  : splits_spec f g -> Injective f.
Proof. 
  move => p x y a.
  have tx := p x; have ty := p y.
  (* unfold comp in tx, ty. *)
  destruct tx, ty.
  unfold comp.
  destruct a.
  reflexivity.
Defined.

(** Every surjection between finite types has a section. *)
Definition surjection_splitting {A B : finType} (f : {ffun A -> B})
  : surjective f -> { ffun B -> A }.
Proof.
  move/forallP => p.
  apply: finfun => b.
  specialize p with b.
  destruct (iinv_proof p) as [i _].
  exact: i.
Defined.

Proposition surjection_splitting_spec {A B : finType} (f : {ffun A -> B})
  (p : surjective f)
  : splits (surjection_splitting f p) f.
Proof.
  apply/splitsP.
  intro x.
  rewrite /surjection_splitting.
  cbn.
  rewrite ffunE.
  set j := (iinv_proof _).
  destruct j as [x0 x0pf].
  exact: e.
Qed.

Proposition iff_equiv (b c : bool) : (b <-> c) <-> b = c.
Proof.
  split.
  { move => [bc cb]; apply/(sameP idP); apply/(iffP idP); done. }
  { move ->; done. }
Qed.

#[export] Hint Rewrite <- iff_equiv : brefl.

Proposition has_exists {A : finType} (P : pred A)
  : has P (enum A) = [exists a, P a].
Proof.
  apply/iff_equiv; split.
  { move/hasP => H. apply/existsP.
    destruct H as [x _ pf]; exists x; exact: pf. }
  { move/existsP => H; destruct H as [x pf]; apply/hasP.
    exists x. { apply: mem_enum. } exact pf. }
Qed.
  
Proposition not_surj_has {A B : finType} (f : {ffun A -> B})
  : has (λ y : B, y \notin (image f A)) (enum B) =
      ~~ surjective f.
Proof.
    rewrite /surjective.
    rewrite negb_forall.
    rewrite -has_exists.
    reflexivity.
Qed.

(** For t a tuple, we have pairwise R t iff forall i j : 'I_n with i < j, R (tnth t i) (tnth t j) *)

(* fgraph f := sequence of elements of f, viewed as a tuple. *)
(* pairmap f a s := [f a x1, f x1 x2, .... ] *)

(* If R is a transitive relation, then for any list xs, 
   (forall i j, i < i -> R xs[i] xs[j]) iff (forall i,  R (xs[i]) (xs[i+1]). *)

Proposition pairmap_trans_pairwise (A : Type) (R : rel A)
  (tr : transitive R) (xs : seq A)
  : pairwise R xs = if xs is x :: xs then
                      foldr andb true (pairmap R x xs) else true.
Proof.
  (* Convert boolean equality to logical bi-implication*)
  apply/idP/idP;
  (* reduce to the nontrivial case where the list xs is nonempty. *)
  destruct xs as [ | a l]; [ done | | done | ];
  (* Write xs := [a :: l] and induct on the tail list l; again, the 
     case where l is empty is trivial so solve that case and 
     write l := [b :: l] to reduce to the case [a :: b :: l]. *)
    revert a; induction l as [ | b l IH]; [ done | | done | ].
  (* Left-to-right implication *)
  { intro a.
    (* bookkeeping to translate Boolean conjunction into propositional conjunction *)
    move/andP; intros [H1 H2'];
      move/andP : H2' => [H2 H3]; simpl; apply/andP; split.
    (* First goal, R a b, is already in the assumption H1. *)
    { simpl in H1. move/andP: H1 => [ X ?]; exact: X. }
    { apply: IH. simpl; apply/andP; split.
      { exact: H2. }
      { exact: H3. }
    }
  }
  (* Right-to-left implication *)
  intros a. simpl.
     (* There are three goals here. 
        - R a b, which is an assumption 
        - all (R a) l, which we address last
        - pairwise R [b :: l] which follows immediately from the
          induction hypothesis on l and an assumption. 
        We do some bookkeeping to convert Boolean conjunction to 
        logical conjunction, and 
        take care of the first and third goals. *)
  move/andP; intros [Rab H2]; rewrite Rab; simpl.
  apply IH in H2; apply/andP; split; [ | exact: H2 ].
     (* This leaves only all (R a) l. 
        The lemma sub_all states that if P and Q are predicates, 
        and P => Q (P is a subpredicate of Q)
        then (all P) => (all Q), i.e, P holds for all elements in a list
        only if Q does. Thus it suffices to prove that (R b _) => (R a _).
        But this is immediate by the transitivitity of R.
        *) 
     rewrite /= in H2; move/andP : H2 => [] z _; apply: sub_all z.
     rewrite /subpred => x; apply: tr; done.
Qed.

(** For t a tuple, we have pairwise R t iff forall i j : 'I_n with i < j, R (tnth t i) (tnth t j) *)

Proposition tuple_pairwiseP (A : Type) (n : nat)
  (t : n.-tuple A) (R : rel A) :
  reflect {in ord_enum n &, { homo @tnth n _ t : i j / i < j >-> R i j } } (pairwise R t). 
Proof.
  revert n t; destruct n.
  (* We address the case of a 0-tuple separately because some math-comp
     lemmas are defined only for tuples of length n.+1. *)
  { intro t; rewrite tuple0; simpl; apply: ReflectT; done. }
  intro t.
  (* There is already a Boolean reflection lemma which 
     provides a logical specification of the behavior of the function
     pairwise, so all we have to do is prove that our logical specification
     is equivalent to the one already in the standard library.
   *)
  apply: (iffP (pairwiseP (thead t))); intros H i j.
  {
    intros i_in_enum j_in_enum ineq.
    assert (z := H i j). rewrite size_tuple in z.
    assert (k := (z (ltn_ord i) (ltn_ord j) ineq)).
    rewrite 2! (tnth_nth (thead t)). done.
  }
  { 
    rewrite size_tuple; intros ibd jbd;
      set i' := Ordinal ibd; set j' := Ordinal jbd.
    rewrite -[i]/(nat_of_ord i') -[j]/(nat_of_ord j') - 2! tnth_nth;
      intro ineq.
    apply: H; [ | | exact: ineq];
      apply: mem_ord_enum.
  } 
Qed.

Proposition tnth_tuple_of_finfun (A : Type) (n : nat) (f : A^n) (i : 'I_n)
  : tnth (tuple_of_finfun f) i = f i.
Proof.
  by rewrite -{2}(tuple_of_finfunK f) /finfun_of_tuple ffunE. 
Qed.  

Proposition tuple_of_finfun_fgraph (T : Type) (n : nat) (f : T^n)
  : tuple_of_finfun f = (tcast (card_ord _) (fgraph f)).
Proof.
  apply eq_from_tnth; intro i.
  by rewrite tnth_tuple_of_finfun tcastE -enum_rank_ord
                                            tnth_fgraph enum_rankK.
Qed.

(** Equivalence with notions in Coq.Logic.FinFun *)
Proposition List_In_iff_mem (A : eqType) (l : seq A) (a : A)
  : List.In a l <-> a \in l.
Proof.
  split.
  {
    revert a; induction l; [ move => ? listin; contradiction listin |].
    move => a0 listin.
    simpl in listin. 
    case: listin. { move ->. exact: mem_head. }
    move => t.
    apply IHl in t.
    rewrite in_cons t.
    exact: orbT.
  }
  {
    revert a; induction l; [ move => ?; now rewrite in_nil | ].
    move => a0; rewrite in_cons; case/orP.
    { move/eqP -> . rewrite /List.In. left. done. }
    { move => ? ; simpl; right; now apply IHl. }
  }
Defined.

Proposition Finfun_Finite_of_SSReflect_Finite ( A: finType)
  : Finite A.
Proof.
  exists (enum A).
  rewrite /Full.
  move => a.
  rewrite List_In_iff_mem.
  exact: mem_enum.
Qed.

Proposition ListDec_decidable_eq_of_eqtype (A : eqType)
  : ListDec.decidable_eq A.
Proof.
  rewrite /ListDec.decidable_eq.
  move => x y.
  rewrite /Decidable.decidable.
  destruct (@idP (x == y)) as [i | n].
  { move/eqP : i => i; left; done. }
  { right. now move/eqP => n'. }
Qed.

Lemma injective_iff_surjective {A : finType} (f : {ffun A -> A})
  : (injectiveb f = surjective f).
Proof.
  rewrite <- iff_equiv.
  rewrite <- (rwP (injectiveP f)).
  rewrite <- (rwP (surjectiveP f)).
  have t := Endo_Injective_Surjective.
  apply: t;
    [ exact: Finfun_Finite_of_SSReflect_Finite | ].
  exact: ListDec_decidable_eq_of_eqtype.
Qed.
