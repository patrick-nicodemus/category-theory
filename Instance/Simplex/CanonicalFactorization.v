(* -*- mode: coq; mode: visual-line -*-  *)
Require Import ssreflect.
Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Theory.Category Theory.Functor.
Require Category.Lib.Setoid.
Require Coq.Setoids.Setoid.
Require Import Instance.Simplex.FinType.
Require Import Instance.Simplex.NaturalNumberArithmetic.
Require Import Instance.Simplex.Stdfinset.
Require Import Instance.Simplex.AugmentedSimplexCategory.

Require Import Arith.
Require Import Construction.Free.Quiver.
Require Import Construction.Quotient.

Require Import ssrfun.
Require Import ssrbool.
Require Import mathcomp.ssreflect.seq.
Set Warnings "-notation-overridden".
Require Import mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finfun.

From Hammer Require Import Hammer Reflect Tactics.

Open Scope nat_scope.
Notation "''I_' n" := (ordinal n).

Section FreelyGenerated.
  Variant face_map (n : nat) :=
    | δ : 'I_(n.+1) -> face_map.

  Variant degeneracy_map (n : nat) :=
    | σ : 'I_(n.+1) -> degeneracy_map.

  Arguments δ {n} i.
  Arguments σ {n} i.

  Definition sd_edges : nat -> nat -> Type :=
    fun n m =>
      match m with
      | O => void
      | S m' => if n == m' then face_map m' else
                  if n == m'.+2 then degeneracy_map m' else
                    void
      end.
    
  Definition sd_quiver : Quiver :=
    {| nodes := nat ;
      edges := sd_edges;
      edgeset := fun _ _ => eq_Setoid _ 
    |}.

  Definition free_cat_on_sd := FreeOnQuiver sd_quiver.

  Local Notation ASC_δ := AugmentedSimplexCategory.δ.
  Local Notation ASC_σ := AugmentedSimplexCategory.σ.
  
  Arguments sd_edges /.
  
  Definition sd_quiverhom
    : QuiverHomomorphism sd_quiver (QuiverOfCat finord).
    unshelve eapply Build_QuiverHomomorphism. 
    { exact @id. } 
    { simpl.
      intros x y; destruct y; [ now trivial |].
      destruct (@eqP _ x y) as [ x_eq_y | x_neq_y ].
      { destruct x_eq_y;
          intro di; destruct di as [ i ];
          exact (ASC_δ i). }
      { destruct (@eqP _ x y.+2) as [x_eq_SSy | x_neq_SSy].
        { apply symmetry in x_eq_SSy. destruct x_eq_SSy.
          intro si; destruct si as [ i].
          exact (ASC_σ i). }
        now trivial. } }
    abstract(intros x y a b eq; simpl in eq; destruct eq;
    reflexivity).
  Defined.

  Definition sd_induced_functor :=
    Quiver.InducedFunctor sd_quiver sd_quiverhom.

  (* δf = δ in the _free_ simplex category  *)
  (* Definition δf (n : nat) (i : 'I_(n.+1)) : @hom free_cat_on_sd n n.+1. *)
  (* Proof. *)
  (*   simpl. refine (tlist_singleton _).  *)
  (*   destruct (@eqP _ n n). *)
  (*   { exact (δ i). } *)
  (*   { now contradiction n0. } *)
  (* Defined. *)
  Definition δf (n : nat) (i : 'I_(n.+1)) : @edges sd_quiver n n.+1.
  Proof.
    simpl. 
    destruct (@eqP _ n n).
    { exact (δ i). }
    { abstract(now contradiction n0). }
  Defined.

  (* Definition σf (n : nat) (i : 'I_(n.+1)) : @hom free_cat_on_sd n.+2 n.+1. *)
  (* Proof. *)
  (*   simpl. refine (tlist_singleton _). simpl. *)
  (*   destruct (@eqP _ n.+2 n); [ now trivial |]. *)
  (*   destruct (@eqP _ n.+2 n.+2); [ exact (σ i) | now trivial]. *)
  (* Defined. *)
  Definition σf (n : nat) (i : 'I_(n.+1)) : @edges sd_quiver n.+2 n.+1.
  Proof.
    simpl.
    destruct (@eqP _ n.+2 n); [ abstract(now trivial) |].
    destruct (@eqP _ n.+2 n.+2); [ exact (σ i) | abstract(now trivial)].
  Defined.

  Proposition δf_mapsto_δ (n : nat) (i : 'I_(n.+1))
    : @fedgemap _ _ sd_quiverhom _ _ (δf _ i) = ASC_δ i.
  Proof.
    simpl.
    unfold δf. 
    destruct eqP;
      [ now rewrite (Peano_dec.UIP_nat n n e Logic.eq_refl) |].
    now contradiction n0.
  Qed.

  (* Proposition δf_mapsto_δ (n : nat) (i : 'I_(n.+1))  *)
  (*   : fmap[sd_induced_functor] (δf _ i) = ASC_δ i. *)
  (* Proof. *)
  (*   rewrite /sd_induced_functor *)
  (*     /Quiver.InducedFunctor *)
  (*     /fmap *)
  (*     /δf *)
  (*     /tlist_singleton *)
  (*     /tlist'_rect. *)
  (*   rewrite -> (@id_left Δ). *)
  (*   rewrite /sd_quiverhom. *)
  (*   rewrite /fedgemap. *)
  (*   unfold fedgemap. *)
  (*   now destruct eqP; *)
  (*   [ rewrite (Peano_dec.UIP_nat n n e Logic.eq_refl) | ]. *)
  (* Qed. *)

  Proposition σf_mapsto_σ (n : nat) (i : 'I_(n.+1)) 
    : @fedgemap _ _ sd_quiverhom _ _ (σf _ i) = ASC_σ i.
  Proof.
    simpl.
    unfold σf.
    destruct eqP.
    { now contradiction (Plus.n_SSn_stt n). }
    { destruct eqP;
      [ now rewrite (Peano_dec.UIP_nat  _ _ (symmetry e) Logic.eq_refl) |].
      now contradiction n1.
    }
  Qed.
  
  (* Proposition σf_mapsto_σ (n : nat) (i : 'I_(n.+1))  *)
  (*   : fmap[sd_induced_functor] (σf _ i) = ASC_σ i. *)
  (* Proof. *)
  (*   rewrite /sd_induced_functor *)
  (*     /Quiver.InducedFunctor *)
  (*     /fmap *)
  (*     /σf *)
  (*     /tlist_singleton *)
  (*     /tlist'_rect; *)
  (*   rewrite -> (@id_left Δ); *)
  (*   rewrite /sd_quiverhom; *)
  (*   rewrite /fedgemap; *)
  (*   unfold fedgemap; *)
  (*     destruct eqP. *)
  (*   { now contradiction (Plus.n_SSn_stt n). } *)
  (*   { destruct eqP. *)
  (*     { now rewrite (Peano_dec.UIP_nat (n.+2) (n.+2) *)
  (*                      (symmetry e) (erefl)) . } *)
  (*     { contradiction. } *)
  (*     }  *)
  (* Qed.       *)
  
  Variant basic_morphism_rel
    : forall (n m : nat) (f g : @hom free_cat_on_sd n m), Type :=
    (*  d_i d_j = d_{j-1} d_i   (i < j)
        δ_j ∘ δ_i = δ_i ∘ δ_{j-1} *)
    | law1 : forall (n : nat) (i : 'I_(n.+1)) (j : 'I_(n.+2)),
        i < j ->  basic_morphism_rel n n.+2
                    ((δf _ i) ::: (δf _ j)::: tnil)
                    ((δf _ (ord_predn j)) 
                       ::: (δf _ (ord_upcast i))
                       ::: tnil)
    (*  s_i s_j = s_{j+1} s_i (i <= j) 
        σ_j σ_i = σ_i σ_{j+1}, i <= j *)
    | law2 : forall (n : nat) (i : 'I_(n.+2)) (j : 'I_(n.+1)),
        i <= j -> basic_morphism_rel n.+3 n.+1
                    ((σf _ i) ::: (σf _ j) ::: tnil)
                    ((σf _ (inord (j.+1))) ::: 
                    ((σf _ (inord i))) ::: tnil)
    | law3i : forall (n : nat) (i j: 'I_(n.+2)),
        i < j -> basic_morphism_rel n.+2 n.+2
                   ((δf _ (ord_upcast i)) :::
                      (σf _ j) ::: tnil)
                   (σf _ (ord_predn j) :::
                   (δf _ i) ::: tnil)
    | law3ii : forall (n : nat) (i : 'I_(n.+1)),
        basic_morphism_rel n.+1 n.+1
          (δf _ (ord_upcast i) ::: (σf _ i) ::: tnil)
          tnil
    | law3iii : forall (n : nat) (i : 'I_(n.+1)),
        basic_morphism_rel n.+1 n.+1
          (δf _ (lift ord0 i) :::
             (σf _ i) ::: tnil)
          tnil
    | law3iv : forall (n : nat) (i : 'I_(n.+3)) (j : 'I_(n.+1)),
        i > j.+1 -> basic_morphism_rel n.+2 n.+2
                      ( δf _ i ::: σf _ (ord_upcast j) ::: tnil)
                      ( σf _ j ::: δf _ (ord_predn i) ::: tnil).

  Definition InductivelyGeneratedSimplexCat :=
    @Quotient free_cat_on_sd basic_morphism_rel.

  Proposition functor_respects :
    ∀ (c c' : obj[free_cat_on_sd])
      (f g : c ~{ free_cat_on_sd }~> c'),
      basic_morphism_rel c c' f g →
      @fmap _ _ sd_induced_functor _ _ f ≈
        @fmap _ _ sd_induced_functor _ _ g.
  Proof.
    intros c c' f g a.
    destruct a;
      repeat rewrite InducedFunctor_Rewrite;
      repeat rewrite δf_mapsto_δ;
      repeat rewrite σf_mapsto_σ;
      repeat rewrite -> id_left.
    { exact: δi_δj. }
    { exact: σi_σj. }
    { exact: (δi_σj_iltj i j i0). }
    { exact: δi_σi_eq_id. }
    { exact: δSi_σi_eq_id. }
    { exact: δi_σj_i_gt_Sj. }
  Qed.

  (** First half of the equivalence. *)
  Definition evaluationFunctor :=
    Quotient.InducedFunctor
    free_cat_on_sd
    finord
    basic_morphism_rel
    sd_induced_functor
    functor_respects.

End FreelyGenerated.

  Lemma rleq_nm_notinj {n m : nat} (f : 'I_m ^n)
    (p : rgeq n m.+1)
    : ~~ injectiveb f.
  Proof.
    apply rgeq_implies_leq in p.
    destruct n.
    { rewrite (ltn0 m) in p; discriminate p. }
    { destruct m.
      { have t := valP (f ord0).
        rewrite ltn0 in t.
        discriminate t. }
      exact: nltm_not_injective f p. }
  Qed.

  Definition factorization_surj_finset' {n m : nat}
    (f : 'I_m ^n)
    (p : rgeq n m) : @hom free_cat_on_sd n m.
  Proof.
    induction p as [| m].
    { exact TList.tnil. }
    destruct n; [ abstract(
                      apply rgeq_implies_leq in p;
                      rewrite ltn0 in p; discriminate p)|].
    destruct m; [ abstract(
                      have t := valP (f ord0); 
                                rewrite ltn0 in t;
                                discriminate t) |].
     
    have z := rleq_nm_notinj f p.
    set i := not_injective_hitstwice_val f.
    unshelve apply (@tlist_rcons sd_quiver edges _ m.+2);
    [ exact: (IHp (degeneracy_factoring_map f i
                     (not_injective_hitstwice_spec f z)))
    | exact: (σf _ i) ].
  Defined.

  Proposition factorization_surj_finset_rewrite
    {n m : nat} (f : 'I_m.+1 ^n) (p : rgeq n m.+2)
    :
    factorization_surj_finset' f (rgeq_succ _ _ p) =
      let i := (not_injective_hitstwice_val f) in
        tlist_rcons
        (factorization_surj_finset'
             (degeneracy_factoring_map f
                i
                (not_injective_hitstwice_spec f (rleq_nm_notinj f p)))
             p)
        (σf _ i).
  Proof.
    destruct n.
    { apply False_rect.
      apply rgeq_implies_leq in p;
        rewrite ltn0 in p; discriminate p. }
    reflexivity.
  Qed.
    
  Definition factorization_surj_finset {n m : nat} (f : 'I_ m ^n) 
    (p : surjective f) : @hom free_cat_on_sd n m.
  Proof.
    assert (z : rgeq n m) by
      abstract(apply: leq_implies_rgeq; exact: (surjective_card f)).
    exact: factorization_surj_finset'.
  Defined.

  (** In this code we directly deal with a lot of objects defined in Stdfinset.v. But we probably should not go down to that level of abstraction. Instead we probably want to define new things in AugmentedSimplexCategory.v on top of those and use them in the proof instead. *)
  (** The theorem is only true for f monotonic so when proving this kind of theorem about the factorization algorithm one should only work with objects in the simplex category. *)

  Proposition factorization_surj_spec (n m : nat) 
    (f : @hom finord n m) (p : surjective f)
    : fmap[evaluationFunctor] (factorization_surj_finset f p) = f.
  Proof.
    unfold factorization_surj_finset.
    set z := (factorization_surj_finset_subproof _ _ _ _).
    induction z as [ | m]; [ exact: identity_unique_surjection |].
    (* The case m=0 is absurd so we do it separately. *)
    destruct m; [
      destruct n;
        [ discriminate (rgeq_implies_leq _ _ z)
        | discriminate (valP (f ord0))]  |].

    rewrite factorization_surj_finset_rewrite.
    cbn zeta.
    unfold evaluationFunctor, InducedFunctor, fmap.
    rewrite (@InducedFunctor_Rewrite_rcons _ _ sd_quiverhom).
    set r := rleq_nm_notinj f z.
    set ht := not_injective_hitstwice_spec f r.
    set i := not_injective_hitstwice_val f in ht *.
    have fps := factoring_preserves_surjectivity f i ht p.
    set g := (degeneracy_factoring_map _ _ _) in fps *.
    set g0 : (@hom finord n m.+2) :=
      @Sub {ffun 'I_n -> 'I_m.+2} monotonic
        _ g (degenerate_factor_monotonic _ _ _).
    rewrite (IHz g0 fps).
    rewrite σf_mapsto_σ.
    apply val_inj; simpl.
    unfold AugmentedSimplexCategory.comp.
    apply ffunP => x.
    rewrite ffunE ffunE.
    rewrite (degeneracy_factoring_map_eq f i).
    apply val_inj => /=.
    rewrite [in a in _ = a]ffunE.
    unfold σ_stdfinset.
    symmetry.
    rewrite ffunE. 
    reflexivity.
  Qed.
  
  (* Definition factorization {n m : nat} (f : 'I_ m ^n)  *)
  (*   (p : surjective f) : *)
  (*   @hom free_cat_on_sd n m. *)
  (* Proof. *)
  (*   assert (z : rgeq n m) by *)
  (*     (apply: leq_implies_rgeq; exact: (surjective_card f)).  *)
  (*   induction z as [| m ineq IH ]; [ exact TList.tnil |]. *)
  (*   destruct m as [ | m];  *)
  (*     [ by destruct n; *)
  (*       [ exact TList.tnil *)
  (*       | abstract(destruct (f ord0); discriminate) ] |]. *)
  (*   apply rgeq_implies_leq in ineq. *)
  (*   assert (z := nltm_not_injective f ineq). *)
  (*   set i := not_injective_hitstwice_val f. *)
  (*   unshelve apply (@tlist_rcons sd_quiver edges _ m.+2). *)
  (*   { apply (IH (degeneracy_factoring_map f i *)
  (*                  (not_injective_hitstwice_spec f z))). *)
  (*     apply (factoring_preserves_surjectivity); exact: p. } *)
  (*   { simpl. do 2! resolve_boolean. exact (σ i). } *)
  (* Defined. *)
  Definition factorization {n m : nat} (f : 'I_ m ^n) :
    @hom free_cat_on_sd n m.
  Proof.
    induction m;
      [ destruct n as [ |n'];
        [ exact: TList.tnil
        | destruct (f (@ord0 n')); auto with arith] | ].
    destruct (@idP (surjective f)) as [surj |not_surj];
      [ exact: (factorization_surj_finset f surj) |].
    set P := fun y : ordinal_finType m.+1 =>
               y \notin [seq f x | x : exp_finIndexType n].
    unshelve refine (let t := (gtest_st_spec P _) in _ ).
    {   abstract(move/negP: not_surj => not_surj;
             now rewrite/surjective -not_surj_has in not_surj). }
    set i := (findlast_ord _ _) in t; clearbody t i.
    refine (tlist_rcons (IHm (facemap_factoring_map f i _)) (δf _ i)).
    abstract(now move/andP: t => [notin _]).
  Defined.    

  Proposition factorization_spec {n m :nat} (f : n ~{ Δ }~> m) :
    fmap[evaluationFunctor] (factorization f) = f.
  Proof.
    induction m.
    { destruct n.
      { apply: val_inj; rewrite -ffunP /=.
        move => [xval xbd]; discriminate xbd. }
      destruct (f ord0) as [? ybd]; discriminate ybd. }
    unfold factorization.
    (* set j := [eta _ ]; clearbody j. *)
    simpl nat_rect.
    destruct idP as [p | np];
      [ exact: factorization_surj_spec |]. 
    rewrite (@InducedFunctor_Rewrite_rcons _ _ sd_quiverhom).
    rewrite δf_mapsto_δ.
    set g0 := facemap_factoring_map f _ _ .
    set P := (fun y => y \notin [seq f x | x in 'I_n]) in g0 *.
    set pf : has P (enum 'I_m.+1)
      := (a in findlast_ord _ a) in g0 *.
    set gs := (gtest_st_spec P _) in g0 *.
    set i := (findlast_ord _ _) in gs g0 *.
    set pf0 := (pf in facemap_factoring_map f i pf) in g0 *.
    set g : @hom finord n m
      := Sub g0 (face_factor_monotonic f i pf0).
    rewrite (IHm g).
    apply: val_inj.
    (* set f1 := (a in a ∘ g). *)
    change (val(AugmentedSimplexCategory.δ i ∘[ Δ ] g)) with
      (val (AugmentedSimplexCategory.δ i) ∘[stdfinset] (val g)).
    symmetry.
    exact: facemap_factoring_eq.
  Qed.

  (** This concludes the proof that every morphism in the simplex category can be factored into a composition of face and degeneracy maps in a canonical way. Thus, we conclude that the simplex category is generated by the face and degeneracy maps. *)

  (** We now turn to the task of proving that there is a unique factorization subject to certain conditions. This is essentially equivalent to showing that the simplex category is *freely* generated by the face and degeneracy maps, *modulo* simplicial identities. *)

  (** In order to make our lives easier and reduce some of the complexities that come with dependent types, we will try to reduce computations with words in the simplex category to computations in the set of all lists of terms "d i", "s i" where i is an arbitrary natural number. We define a forgetful function from @hom sd_quiver n m into the set of such words, which forgets the domain and codomain of the morphism and moreover forgets that the indices for the d i and s i are supposed to be bounded above by  some given finite ordinal. 

To the extent that definitions or proofs can be given using such words, we choose to do so.

*)

  Variant sd_no_obj :=
    | dA : nat -> sd_no_obj
    | sA : nat -> sd_no_obj.

  Definition forget_objects'
    {n m : nat} (e : @edges sd_quiver n m)
    : sd_no_obj.
  Proof.
    simpl in e.
    unfold sd_edges in e.
    destruct m; [ contradiction |].
    destruct (n == m).
    { destruct e as [e_index]. exact (dA e_index). }
    { destruct (n == m.+2).
      { destruct e as [e_index]. exact (sA e_index). }
      contradiction e. }
  Defined.

  Proposition forget_obj_face {n : nat} (i : 'I_n.+1):
    forget_objects' (δf _ i) = dA i.
  Proof.
    simpl.
    unfold δf.
    destruct (@eqP _ n n) as [|n0]; [ reflexivity |].
    now contradiction n0.
  Qed.

  Proposition forget_obj_degen {n : nat} (i : 'I_n.+1):
    forget_objects' (σf _ i) = sA i.
  Proof.
    simpl.
    unfold σf.
    destruct (@eqP _ n.+2 n) as [a |].
    { now contradiction (Plus.n_SSn_stt n). }
    destruct eqP; [ reflexivity | done ].
  Qed.
  
  Fixpoint forget_objects
    {n m : nat} (f : @hom free_cat_on_sd n m) : seq sd_no_obj :=
    match f with
    | tnil => nil
    | tcons _ _ e f => (forget_objects' e) :: forget_objects f
    end.

  Definition cf_compare : sd_no_obj -> sd_no_obj -> bool :=
    fun f g =>
      match f with
      | dA i => match g with
                | dA j => i < j
                | sA _ => false
                end
      | sA i => match g with
                | dA j => true
                | sA j => i > j
                end
      end.

  Definition sorted_no_obj := pairwise cf_compare.

  Definition sorted {n m : nat} (f: @hom free_cat_on_sd n m) : bool
    := sorted_no_obj (forget_objects f).

  (** Here n is meant to be interpreted as the domain of the morphism *)
  Fixpoint well_formed (f : seq sd_no_obj) (n : nat) : bool :=
    match f with
    | nil => true
    | cons e g => match e with
                  | dA i => (i < n.+1) && well_formed g n.+1
                  | sA i => (i < n.-1) && well_formed g n.-1
                  end
    end.
  
  (** This function is "unsafe", it will not give a reasonable answer if f is not well-formed. *) 
  Fixpoint cod (f : seq sd_no_obj) (n : nat) : nat :=
    match f with
    | nil => n
    | cons e g => match e with
                  | dA i => cod g n.+1
                  | sA i => cod g n.-1
                  end
    end.

  Proposition free_cat_sd_maps_are_well_formed
    {n m : nat} (f : n ~{ free_cat_on_sd }~> m)
    : well_formed (forget_objects f) n.
  Proof.
    induction f.
    { reflexivity. }
    { cbn. simpl in b. unfold sd_edges in b.
      destruct j; [ contradiction b |].
      unfold forget_objects'.
      destruct (@eqP _ i j) as [i_eq_j | i_neq_j].
      {
        (* i = j *)
        destruct b as [b0].
        rewrite i_eq_j IHf andbT.
        exact (valP b0). }
      {
        destruct (@eqP _ i j.+2) as [i_eq_SSj | i_neq_SSj].
        {
          destruct b as [b0].
          rewrite i_eq_SSj /= IHf andbT.
          exact (valP b0).
        }
        {
          contradiction b.
        }
      }
    }
  Qed.

  (* Proposition forget_obj_helper *)
  (*   (P : sd_no_obj -> Type) *)
  (*   : *)
  (*   P nil -> *)
  (*     (forall i g, P (cons (dA i) g)) -> *)
  (*     (forall j g, P (cons (sA j) g)) -> *)
  (*     forall (n m: nat) *)
  (*            (f : @hom free_cat_on_sd n m), *)
  (*       P (forget_objects f). *)
  (* Proof. *)
  (*   intros Pnil i g P_dAi_g m f. *)
  (*   induction f. *)
  (*   { exact Pnil. } *)
  (*   { simpl. *)
  
  Proposition forget_get_cod_from_dom {n m: nat}
    (f: @hom free_cat_on_sd n m)
    : cod (forget_objects f) n = m.
  Proof.
    (** Want to show P (forget_objects f), 
         where P := fun f => cod f n = m  *)
    induction f.
    { (* Know P nil *)
      reflexivity. }
    {
      simpl; simpl in b. unfold sd_edges in b.
      destruct j; [contradiction b |].
      unfold forget_objects'.
      { destruct (@eqP _ i j) as [i_eq_j | i_neq_j].
        { destruct b as [b0].
          destruct i_eq_j. exact: IHf. }
        { destruct (@eqP _ i j.+2) as [i_eq_SSj | i_neq_SSj].
          { destruct b as [b0].
            { rewrite i_eq_SSj.
              cbn. exact: IHf. }
          }
          contradiction b.
        }
      }
    }
  Qed.

  Definition lift_wf_to_freecat
    (n : nat) (f : seq sd_no_obj) (p : well_formed f n)
    : @hom free_cat_on_sd n (cod f n).
  Proof.
    revert n p.
    induction f.
    { move => ? ? ; exact tnil. }
    { move => n p.
      simpl cod. destruct a as [a0 | a0].
      { simpl in p.
        move/andP: p => [a0_le_n wf_f].
        exact: tcons _ (δf _ (Ordinal a0_le_n)) (IHf _ wf_f). }
      { simpl in p.
        move/andP: p => [a0_le_n wf_f].
        destruct n.
        { simpl in a0_le_n. rewrite ltn0 in a0_le_n.
          discriminate a0_le_n. }
        destruct n.
        { simpl in a0_le_n. rewrite ltn0 in a0_le_n.
          discriminate a0_le_n. }
        exact: tcons _ (σf _ (Ordinal a0_le_n)) (IHf _ wf_f). }
    }
  Defined.
  
  Proposition lift_wf_forget_obj_linv
    (n : nat) (f : seq sd_no_obj) (p : well_formed f n)
    : forget_objects (lift_wf_to_freecat n f p) = f.
  Proof.
    revert n p.
    induction f.
    { reflexivity. }
    { move => n p.
      destruct a as [a0 | a0].
      { simpl lift_wf_to_freecat.
        simpl well_formed in p.
        move/andP: p => [a0_lt_Sn wf_f].
        simpl forget_objects.
        { unfold δf.
          destruct (@eqP _ n n) as [ | n_diseq_n].
          { simpl; now rewrite IHf. }
          { now contradiction n_diseq_n. }
        }
      }
      {
        simpl lift_wf_to_freecat.
        simpl well_formed in p.
        move/andP: p => [a0_lt_Sn wf_f].
        destruct n. { apply False_rect.
                      rewrite ltn0 in a0_lt_Sn.
                      discriminate a0_lt_Sn. }
        destruct n. { apply False_rect.
                      rewrite ltn0 in a0_lt_Sn.
                      discriminate a0_lt_Sn. }
        simpl.
        unfold σf.
        destruct (@eqP _ n.+2 n).
        { now contradiction (Plus.n_SSn_stt n). }
        { destruct (@eqP _ n.+2 n.+2) as [| n_diseq_n].
          { now rewrite IHf. }
          { now contradiction n_diseq_n. }
        }
      }
    }
  Qed.

  (** High level proof strategy:
      We have constructed a functor [evaluationFunctor] from    [InductivelyGeneratedSimplexCat] to [finord] which sends each formal path of face and degeneracy maps in the simplex category to its composite. We would like to show that this functor is an equivalence of categories. It would be sufficient to show that it is fully faithful, as it is an isomorphism on homsets. We have shown that the map on hom-sets is surjective, by constructing a canonical factorization of each morphism in the simplex category into faces and degeneracies, [factorization], and verified that it is a section of the evaluation map in [factorization_spec].

It remains to prove that the evaluation map is injective, that is, if two morphisms in [free_cat_on_sd] map to the same morphism in [finord], they are related in [InductivelyGeneratedSimplexCat], i.e., related by the smallest equivalence relation containing [basic_morphism_rel] such that composition respects the equivalence relation.

An [sd_no_obj] is either [d i] or [s i], where [i] is any natural number. In what follows, we will replace morphisms in free_cat_on_sd with sequences from [sd_no_obj] because removing the rigid type structure from paths in the quiver makes them easier to work with and manipulate.

If [f : seq sd_no_obj] and [n :nat], we define a criterion for [f] to be [well_formed] if it is meant to be interpreted as a morphism in [hom free_cat_on_sd] with domain [n]. We also give a function [cod], which, given [f : seq sd_no_obj] and [n], returns [m] which is supposed to be the codomain of the morphism [f].

1. If [f : seq sd_no_obj] and [n : nat], and [f] is [well_formed], then there is a morphism [lift_wf_to_freecat f] in [@hom free_cat_on_sd n (cod f n)] which is in the fiber of [forget_objects] over [f] ( [lift_wf_forget_obj_linv] ).

We define a sorting algorithm [sort_no_obj] on [seq sd_no_obj].

2. If [f : seq sd_no_obj]] starting at [n] is [well_formed], then [sort_no_obj f] starting at [n] is [well_formed]. ([sort_no_obj'_preserves_well_formed]) Moreover they have the same [cod]. ([sort_no_obj'_preserves_cod])

3. It follows that there is a function [sort : @hom free_on_ord n m -> @hom free_on_ord n m] given by forgetting the objects of [f], sorting by [sort_no_obj], and lifting this along [forget_objects] using [lift_wf_forget_obj]. 

4. Two morphisms [f], [g] in [@hom free_on_ord n m] become equal in [InductivelyGeneratedSimplexCat] only if [sort f = sort g].

5. If [f], [g] are two [well_formed] sequences in sd_no_obj rooted at [n] with [cod f = cod g = m], then [f] and [g] denote the same morphism in [finord] only if [sort f] = [sort g].

6. If [sort f = sort g] then their lifts are related in [InductivelyGeneratedSimplexCat]. (It suffices to show that [f] is related to the lift of [sort f].

 *)
  
  Fixpoint sort_no_obj' (e : sd_no_obj)
    (f: seq sd_no_obj) : seq sd_no_obj :=
    match f with
    | nil => e :: nil
    | cons e2 g =>
        match e with
        | dA i => match e2 with
                  | dA j =>
                      if i < j then
                        dA i :: (sort_no_obj' (dA j) g)
                      else (* i >= j *)
                        dA j.-1 :: (sort_no_obj' (dA i) g)
                  | sA j =>
                      if i < j then
                        sA j.-1 ::
                          (sort_no_obj' (dA i) g)
                      else (
                         if (i == j) || (i == j.+1) then
                           match g with
                            | nil => nil
                            | x :: y =>
                                (sort_no_obj' x y)
                           end
                         else
                           (* Must have i > j.+1 *)
                           sA j ::
                             (sort_no_obj' (dA i.-1) g))
                  end
        | sA i => match e2 with
                  | dA j => sA i :: (sort_no_obj' (dA j) g)
                  | sA j => if i <= j then
                              sA j.+1 :: (sort_no_obj' (sA i) g)
                            else
                              sA i :: (sort_no_obj' (sA j) g)
                  end
        end
    end.

  Fixpoint sort_no_obj (f : seq sd_no_obj) : seq sd_no_obj :=
    match f with
    | nil => nil
    | cons e g => sort_no_obj' e (sort_no_obj g)
    end.

  Lemma nat_Si_lt_j (i j : nat) :
    (i <= j) -> ~ ((i == j) || (i.+1 == j)) -> (i.+1 < j).
  Proof.
    move => i_le_j /negP nor.
    rewrite leq_eqVlt in i_le_j.
    rewrite negb_or in nor.
    move/andP : nor => [i_neq_j i_neq_Sj].
    apply negbTE in i_neq_j.
    rewrite i_neq_j in i_le_j; simpl in i_le_j.
    rewrite leq_eqVlt in i_le_j.
    apply negbTE in i_neq_Sj.
    rewrite i_neq_Sj in i_le_j; simpl in i_le_j.
    assumption.
  Qed.

  Proposition sort_no_obj'_preserves_well_formed
    (e : sd_no_obj)
    (f : seq sd_no_obj) (n : nat) (p : well_formed (cons e f) n)
    : well_formed (sort_no_obj' e f) n.
  Proof. 
    revert e n p.
    set z' := length f. 
    remember z' as z eqn:Hz.
    revert f z' Hz.
    induction z as [z IHz] using lt_wf_ind => f.
    simpl; simpl in IHz.
    move => Hz.
    case => [e0 | e0].
    { move => n /= /andP [e0_lt_Sn wf_f].
      destruct f; [ now rewrite /= e0_lt_Sn |].
      have zineq: (length f < z)%coq_nat.
      { apply/ltP; now rewrite Hz. }
      pose IHz' := IHz (length f) zineq f erefl.
      simpl sort_no_obj'.
      destruct s as [s0 | s0].
      { destruct (leqP s0 e0) as [s0_le_e0 | e0_lt_s0 ].
        { simpl. apply/andP; split.
          { auto with arith. }
          { 
            apply: IHz'; simpl in wf_f.
            move/andP: wf_f => [s0_lt_SSn wf_f].
            now rewrite wf_f andbT (ltn_trans e0_lt_Sn).
          }
        }
        simpl; rewrite e0_lt_Sn /=. apply: IHz'; exact: wf_f.
      }
      { 
        destruct (@leqP s0 e0) as [s0_le_e0 | e0_lt_s0].
        { destruct (@idP ((e0 == s0) || (e0 == s0.+1))) as [| neq_e0s0].
          {
            destruct f; [ done |].
            apply: (IHz _ _ f erefl).
            { symmetry in Hz; destruct Hz. simpl; auto with arith. }
            { move/andP: wf_f; case; done. }
          }
          {
            simpl in wf_f; move/andP : wf_f => [s0ineq wf_f].
            rewrite [in bb in ~ ( _ || bb)]eq_sym eq_sym in neq_e0s0.
            have s0lt := nat_Si_lt_j s0 e0 s0_le_e0 neq_e0s0.
            simpl; apply/andP; split.
            {
              rewrite ltn_predRL. apply (@leq_trans e0); assumption.
            }
            {
              apply: IHz'.
              rewrite (ltn_predK s0ineq) /=.
              rewrite (ltn_predK s0lt).
              rewrite ltnS in e0_lt_Sn.
              now rewrite e0_lt_Sn.
            }
          }
        }
        simpl.
        simpl in wf_f.
          move/andP: wf_f => [s0_lt_n wf_f].
        apply/andP; split.
        {
          rewrite ltn_predRL.
          rewrite (ltn_predK e0_lt_s0).
          exact: s0_lt_n.
        }
        apply IHz'; apply/andP; split.
        {  auto with arith. }
        { now rewrite (ltn_predK s0_lt_n). }
      }
    }
    {
      move => n /andP [e0_lt_predn wf_f].
      destruct f as [| e f].
      { now rewrite /= e0_lt_predn. }
      have zineq : (length f < z)%coq_nat by rewrite Hz.
      pose IHz' := IHz _ zineq f erefl.
      simpl; destruct e as [b0 | b0].
      { rewrite /= e0_lt_predn /=.
        apply: IHz'.
        exact: wf_f. }
      {
        destruct (@leqP e0 b0) as [e0_le_b0 | b0_lt_e0].
        {
          simpl. simpl in wf_f.
          move/andP: wf_f => [ineq wf_f].
          rewrite ltn_predRL in ineq.
          rewrite ineq /=.
          apply: IHz'.
          apply/andP; split.
          { rewrite /= -ltn_predRL in ineq.
            now rewrite (leq_ltn_trans e0_le_b0 ineq). }
          { exact wf_f. }
        }
        rewrite /= e0_lt_predn /=.
        apply: IHz'. exact: wf_f.
      }
    }
  Qed.

  Proposition sort_no_obj'_preserves_cod
    (e : sd_no_obj)
    (f : seq sd_no_obj) (n : nat) (p : well_formed (cons e f) n)
    : cod (sort_no_obj' e f) n = cod (cons e f) n.
  Proof.
    revert e n p.
    set z' := length f. 
    remember z' as z eqn:Hz.
    revert f z' Hz.
    induction z as [z IHz] using lt_wf_ind => f.
    simpl; simpl in IHz.
    move => Hz.
    destruct f;    
      [by case => [e0 | e0] n /andP [e0ineq wf_f] |].
    have zineq : (length f < z)%coq_nat by (apply/ltP; rewrite Hz).
    pose IHz' := IHz _ zineq f erefl.
    move => [e0 | e0] n.
    { move/andP => [e0_lt_Sn wf_sf].
      destruct s as [s0 | s0].
      { simpl. destruct (@leqP s0 e0) as [s0_le_s0 | e0_lt_s0].
        { simpl. apply: (IHz' (dA e0)).
          simpl in wf_sf.
          apply/andP; split.
          { auto with arith. }
          { move/andP:wf_sf; by case. }
        }
        simpl.
        simpl in wf_sf; move/andP : wf_sf => [e0s0ineq wf_f].
        apply: (IHz' (dA s0)).
        apply/andP; now split.
      }
      {
        simpl.
        simpl in wf_sf; move/andP : wf_sf => [s0_lt_n wf_f].
        
        destruct (@leqP s0 e0) as [s0_le_e0 | s0_gt_e0].
        { 
          destruct (@idP ((e0 == s0) || (e0 == s0.+1 ))) as [| e0_neq_s0].
          { 
            destruct f; [ done |].
            unshelve refine (IHz _ _ f erefl s _ _); [ | done].
            rewrite Hz; apply/ltP; simpl; auto with arith.               
          }
          {
            have IHz0 := (IHz _ zineq f erefl (dA e0.-1) n.-1).
            rewrite (ltn_predK s0_lt_n) in IHz0. 
            simpl; apply IHz0.
            rewrite wf_f andbT.
            rewrite leq_eqVlt in s0_le_e0.
            have rw : (s0 == e0 = false). {
              apply: negbTE.
              rewrite eq_sym.
              move/negP: e0_neq_s0.
              rewrite negb_or.
              by case/andP => e0_ne_s0 e0_ne_Ss0.
            }
            rewrite rw /= in s0_le_e0.
            rewrite (ltn_predK s0_le_e0).
            now rewrite -ltnS.
          }
        }
        {
          simpl.
          have IHz0 := IHz _ zineq f erefl (dA e0) n.-1.
          rewrite (ltn_predK s0_lt_n) in IHz0.
          apply IHz0.
          rewrite wf_f andbT.
          exact: ltn_trans s0_gt_e0 s0_lt_n.
        }
      }
    }
    {
      move/andP => [e0_lt_predn wf_sf].
      simpl.
      destruct s as [s0 | s0].
      { apply IHz'; exact wf_sf. }
      { simpl.
        simpl in wf_sf.
        move/andP: wf_sf => [s0_lt_predpredn wf_sf].
        destruct (@leqP e0 s0) as [e0_le_s0 | e0_gt_s0];
          apply: IHz'; rewrite wf_sf andbT.
        { exact: leq_ltn_trans e0_le_s0 s0_lt_predpredn. }
        { assumption. }
      }
    }
  Qed.    

  (** Therefore, sort_no_obj' sends well-formed sequences n-> m
      to well-formed sequences n->m *)
  
  Proposition sort_no_obj_preserves_well_formed
    (f : seq sd_no_obj) (n : nat) (p : well_formed f n)
    : well_formed (sort_no_obj f) n.
  Proof.
    revert n p.
    induction f; [ done |].
    move => /= n.
    case: a;
    move => m /andP [ineq1 wf_f];
    apply: sort_no_obj'_preserves_well_formed => /=;
    rewrite ineq1 /=;
    now apply: IHf.
  Qed.

  Proposition sort_no_obj_preserves_cod
    (f : seq sd_no_obj) (n : nat) (p : well_formed f n)
    : cod (sort_no_obj f) n= cod f n.
  Proof.
    revert n p.
    induction f; [ done |].
    simpl sort_no_obj.
    move => n wf.
    simpl; simpl in wf.
    destruct a as [a0 | a0];
      move/andP: wf => [ineq wf_f];
                       rewrite sort_no_obj'_preserves_cod;
                       [ now rewrite /= IHf
                       | rewrite /= ineq /=;
                           now apply sort_no_obj_preserves_well_formed
                       | now rewrite /= IHf
                       | rewrite /= ineq /=;
                           now apply sort_no_obj_preserves_well_formed
                       ].
  Qed.

  (** It is now easy to see that the sort_no_obj operation lifts to an operation on morphisms in free_cat_on_sd. *)

  Definition evaluation_sd_no_obj (n : nat) (f : seq sd_no_obj)
    (p : well_formed f n) : n ~{ Δ }~> (cod f n).
  Proof.
    revert n p.
    induction f.
    { exact ( fun n _ => @Category.id finord n). }
    { move => n.
      simpl. destruct a as [a0 | a0].
      { move/andP => [a0_lt_Sn wf_f].
        refine ((IHf n.+1 wf_f) ∘ _).
        exact (AugmentedSimplexCategory.δ (Ordinal a0_lt_Sn)).
      }
      { move/andP => [a0_lt_predn wf_f].
        refine ((IHf n.-1 wf_f) ∘ _).
        destruct n; [ done |].
        destruct n; [ done |].
        exact (AugmentedSimplexCategory.σ (Ordinal a0_lt_predn)).
      }
    }
  Defined.
  Check sort_no_obj'_preserves_well_formed.
  Proposition sort_no_obj'_preserves_evaluation
    (n : nat) (e : sd_no_obj) (f : seq sd_no_obj)
    (p : well_formed (e :: f) n) :
    evaluation_sd_no_obj n (e :: f) p
    = evaluation_sd_no_obj
        n (sort_no_obj' e f)
        (sort_no_obj'_preserves_well_formed e f n p).
      
  (* Not sure this is as useful as the one which starts from the other
  end.. *)
  Local Fixpoint forget_displacement
    (m :nat) (l : seq sd_no_obj) : nat
    := match l with
       | nil => m
       | cons e l' => match e with
                      | dA _ => (forget_displacement m l').-1
                      | sA _ => (forget_displacement m l').+1
                      end
       end.

  
  
  Proposition sort_no_obj'_dom_cod {n m k: nat}
    (e : @edges sd_quiver n k) (f : @hom free_cat_on_sd k m)
    : n =forget_displacement m
           (sort_no_obj' (forget_objects' e) (forget_objects f)).
  Proof.
    set z' := tlist_length f.
    remember z' as z eqn:Hz.
    move: n e.
    revert k f z' Hz.
    induction z as [z IHz] using lt_wf_ind.
    simpl. move => k f zeq n e. destruct f as [| i j b f IHf].
    {
      simpl. unfold sd_edges in e.
      destruct m; [ contradiction |].
      cbn. change (eqn n m) with (n == m). set eq_nm := n == m.
      destruct (@eqP _ n m) as [eq_nm' | diseq_nm].
      { destruct e as [e0]; exact eq_nm'. }
      { unfold eq_nm.
        change (eqn n m.+2) with (n == m.+2).
        destruct (@eqP _ n m.+2) as [eq_nSSm | diseq_nSSm].
        { destruct e as [e0]; exact eq_nSSm. }
        { contradiction e. }
      }
    }
    {
      simpl in zeq; simpl.
      unfold sd_edges in e.
      destruct i; [contradiction |].
      unfold forget_objects' at 1.
      destruct (@eqP _ n i) as [n_eq_i | n_diseq_i].
      { (* n = i, e = d i *)
        destruct e as [e0].
        unfold sd_edges in b; destruct j; [contradiction |].
        unfold forget_objects'.
        destruct (@eqP _ i.+1 j) as [Si_eq_j | Si_neq_j ].
        {
          destruct b as [b0].
          destruct (e0 < b0).
          { simpl.
            set e' := (δf _ b0). 
            unshelve refine
              (let a := IHz (tlist_length f) _ _ f _ _ e' in _).
            { rewrite zeq. done. }
            { reflexivity. }
            clearbody a.
            rewrite forget_obj_face in a.
            now rewrite -a n_eq_i -Si_eq_j.
          }
          { (* e0 >= b0 *)
            simpl.
            set e' := (δf _ (ord_upcast e0)).
            destruct Si_eq_j.
            unshelve refine
              (let a := IHz (tlist_length f) _ _ f _ _ e' in _).
            { rewrite zeq; done. }
            { reflexivity. }
            clearbody a.
            rewrite forget_obj_face in a.
            simpl in a.
            rewrite -a.
            exact n_eq_i.
          }
        }
        { (* i+1 ≠ j *)
          destruct (@eqP _ i.+1 j.+2) as [Si_eq_SSj | Si_neq_SSj].
          { (* i+1 = j+2 *)
            destruct b as [b0].
            destruct (leqP b0 e0) as [b0_le_e0 | e0_lt_b0].
            { 
              set eq_or := ((_ == _) || (_ == _)).
              destruct eq_or.
              { (* e0 = b0 or e0 = b0.+1 *)
                destruct f;
                  [ simpl; rewrite n_eq_i;
                    now apply succn_inj in Si_eq_SSj|].
                simpl.
                unshelve refine
                  (let a := IHz (tlist_length f) _ _ f _ _ s in _).
                { rewrite zeq. simpl. apply/ltP. done. }
                { reflexivity. }
                clearbody a.
                rewrite -a n_eq_i. now apply succn_inj in Si_eq_SSj.
              }
              { (* e0 is not b0 or b0+1; e0 > b0 + 1 *)
                simpl.
                apply succn_inj, symmetry in Si_eq_SSj.
                destruct Si_eq_SSj.
                set e' := (δf _ (ord_predn e0)). 
                unshelve refine
                  (let a := IHz (tlist_length f) _ _ f _ _ e' in _).
                { rewrite zeq. done. }
                { reflexivity. }
                clearbody a.
                rewrite forget_obj_face in a.
                rewrite -a.
                exact: n_eq_i.
              }
            }
            {
              
              simpl.
              apply succn_inj, symmetry in Si_eq_SSj.
              destruct Si_eq_SSj.
              have e0lt : e0 < j.+1 := ltn_trans e0_lt_b0 (valP b0).
              set e' := δf _ (Ordinal e0lt).
              unshelve refine
                (let a := IHz (tlist_length f) _ _ f _ _ e' in _).
              { rewrite zeq. done. }
              { reflexivity. }
              clearbody a.
              now rewrite forget_obj_face in a; simpl in a; rewrite -a.
            }
          }
          contradiction b.
        }
      }
      { (* n not equal to i *)
        destruct (@eqP _ n i.+2) as [n_eq_SSi | n_neq_SSi].
        {  (* n not equal to i.+2 *)
          destruct e as [e0].
          unfold forget_objects'.
          destruct j. { contradiction b. }
          simpl in b.
          destruct (@eqP _ i.+1 j).
          { (* i.+1 = j *)
            destruct b as [b0].
            simpl.
            set b' := (δf _ b0).
            unshelve refine
              (let a := IHz (tlist_length f) _ _ f _ _ b' in _ ).
            { rewrite zeq. done. }
            { reflexivity. }
            clearbody a.
            rewrite forget_obj_face in a.
            rewrite -a -e. exact n_eq_SSi.
          }
          {
            destruct (@eqP _ i.+1 j.+2) as [Si_eq_SSj | Si_neq_SSj].
            {
              destruct b as [b0].
              apply succn_inj, symmetry in Si_eq_SSj.
              destruct Si_eq_SSj.
              destruct (leqP e0 b0) as [e0_le_b0 | e0_gt_b0].
              {
                simpl.
                have e0lt : e0 < j.+1 :=
                  leq_ltn_trans e0_le_b0 (valP b0).
                set e' := σf _ (Ordinal e0lt).
                unshelve refine
                  (let a := IHz (tlist_length f) _ _ f _ _ e' in _).
                { rewrite zeq. done. }
                { reflexivity. }
                clearbody a.
                rewrite forget_obj_degen in a.
                rewrite -a.
                exact n_eq_SSi.
              }
              {
                simpl.
                have b0lt : b0 < j.+1. {
                  apply: (leq_trans e0_gt_b0).
                  rewrite -ltnS.
                  exact: (valP e0).
                }
                set e' := σf _ (Ordinal b0lt).
                unshelve refine
                  (let a := IHz (tlist_length f) _ _ f _ _ e' in _).
                { rewrite zeq; done. }
                { reflexivity. }
                clearbody a.
                rewrite forget_obj_degen in a.
                rewrite -a.
                exact n_eq_SSi.
              }
            }
            contradiction b.
          }
        }
        contradiction e.
      } 
    }            
  Qed.

  (* Proposition sorting_lifts_to_morphisms' {n m k: nat} *)
  (*   (f : @hom free_cat_on_sd n m) *)
  (*   : { g : @hom free_cat_on_sd n m & *)
  (*             sort_no_obj' (forget_objects f) = forget_objects g }. *)
  (* Proof. *)
  (*   (* TODO *) *)
  (*   Abort. *)

  Proposition sorting_lifts_to_morphisms {n m : nat}
    (f : @hom free_cat_on_sd n m)
    : { g : @hom free_cat_on_sd n m &
              sort_no_obj (forget_objects f) = forget_objects g }.
  Proof.
    (* TODO *)
    Abort.








  (*******************************************************)
  (***** NOT PART OF CURRENT DEVELOPMENT *****************)










  
  


  (* Definition sorted_head {n m k : nat} *)
  (*   (f1 : @edges sd_quiver n m) (f2 : @edges sd_quiver m k) : bool. *)
  (* Proof. *)
  (*   unfold sd_quiver in f1, f2. simpl in f1, f2. *)
  (*   unfold sd_edges in f1, f2. *)
  (*   destruct k; [ contradiction f2 |]. *)
  (*   destruct m; [ contradiction f1 |]. *)
  (*   destruct (n == m). *)
  (*   { (* n = m, and f1 is a face map *) *)
  (*     destruct (m.+1 == k). *)
  (*     { (* m.+1 = k *) *)
  (*       destruct f1 as [f1_index], f2 as [f2_index]. *)
  (*       (* In the case of two face maps, δ_i ∘ δ_j is  *)
  (*          considered sorted exactly when i > j. *) *)
  (*       exact: (f1_index < f2_index). *)
  (*     } *)
  (*     { (* m.+1 ≠ k, so f2 is a degeneracy. *) *)
  (*       (* A face map should never be followed by a degeneracy.*) *)
  (*       exact false. } *)
  (*   } *)
  (*   { (* n = m.+2 and f1 is a degeneracy *) *)
  (*     destruct (m.+1 == k). *)
  (*     { (* m.+1 = k and f2 is a face map *) *)
  (*       (* A degeneracy followed by a face map is always sorted. *) *)
  (*       exact true. } *)
  (*     { destruct (n == m.+2); [| contradiction]. *)
  (*       destruct (m.+1 == k.+2); [| contradiction]. *)
  (*       destruct f1 as [f1_index], f2 as [f2_index]. *)
  (*       (* In the case of two degeneracies, σ_i ∘ σ_j is considered *)
  (*          sorted exactly when i < j. *) *)
  (*       exact (f1_index > f2_index). *)
  (*     } *)
  (*   } *)
  (* Defined. *)
        
  (* Fixpoint sorted_helper' *)
  (*   {n m : nat}  (f : @hom free_cat_on_sd n m) *)
  (*   : forall (k : nat) (e : @edges sd_quiver k n),  bool := *)
  (*   match f with (* return (forall e' : @edges sd_quiver k n) *) *)
  (*   | tnil => fun _ _ => true *)
  (*   | tcons _ _ b g => *)
  (*       fun _ e' => (sorted_head e' b) && (sorted_helper' g _ b) *)
  (*   end. *)
  
  (* Definition sorted (n m : nat) (f : @hom free_cat_on_sd n m) : bool := *)
  (*   match f with *)
  (*   | tnil => true *)
  (*   | tcons _ _ e f => sorted_helper' f _ e *)
  (*   end. *)

  
