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
  (** This defines what it means for a morphism to be sorted*)
  Definition sorted {n m : nat} (f: @hom free_cat_on_sd n m) : bool
    := sorted_no_obj (forget_objects f).

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
                    
            
            
              

              
            
                
               
                  

              simpl.
              (* f : j+1 -> n *)
              (* so e0 should be from j -> j.+1 *)
              (* Currently dA e0 : i -> i.+1 *)
              (* i = 
              set e' := 
            
            
            
            
            
            

            Check IHz (tlist_length f).

            rewrite -IHz.


      
      
      
      
      

    
    
    induction f as [| i j b f IHf ].
    { simpl. move => n e.
      unfold sd_edges in e.
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
      simpl. move => n e.
      unfold sd_edges in e. 
      destruct i; [ contradiction | ].
      unfold forget_objects'.
      simpl.
      destruct (@eqP _ n i) as [eq_ni | diseq_ni].
      { destruct e as [e0]. simpl in b. unfold sd_edges in b.
        destruct j; [ contradiction |].
        simpl. 
        destruct (@eqP _ i.+1 j) as [Si_eq_j | Si_neq_j].
        { (* i.+1 = j *)
          destruct b as [b0].
          destruct (e0 < b0) as [e0_lt_b0 | e0_nlt_b0].
          {
            simpl.
            have a := IHf _ (δf _ b0).
            rewrite forget_obj_face in a.
            now rewrite -a -Si_eq_j eq_ni.
          }
          { (* e0 >= b0 *)
            simpl.
            destruct eq_ni, Si_eq_j.
            have a := IHf _ (δf _ (ord_upcast e0)).
            rewrite forget_obj_face in a.
            simpl in a.
            now rewrite -a.
          }
        }
        {  
          destruct (@eqP _ i.+1 j.+2) as [Si_eq_SSj | Si_neq_SSj ].
          { 
            destruct b as [b0].
            (* Check leqP. *)
            destruct (leqP b0 e0) as [b0_leq_e0 | e0_lt_b0 ].
            {
              set eqor := ((_ == _) || (_ == _)).
              destruct eqor.
              { (* e0 = b0 or e0 = b0.+1 *)
                simpl.
                
                destruct f.
                {
                  simpl. apply succn_inj in Si_eq_SSj.
                  rewrite -Si_eq_SSj; exact eq_ni.
                }
                { 
                  simpl.
                  have
                  rewrite -IHf.
                
                
              destruct ((val e0 == val b0) || (val e0 == b0.+1)).
              
            
          
            [ contradiction Si_neq_j; apply: succn_inj |] .
      
  
  Proposition sort_no_obj'_dom_cod {n m : nat} (f : @hom free_cat_on_sd n m)
    : match forget_objects f with
      | nil => n = m
      | cons e f' => n = forget_displacement m
                                (sort_no_obj' e f')
      end.
  Proof.
    induction f; [ reflexivity |].
    cbn. 
    unfold forget_objects'.
    destruct j; [ contradiction |].
    simpl in b.
    destruct (@eqP _ i j).
    { (* i = j *)
       destruct b. 
      destruct (forget_objects f).
      { (* f is nil (tnil) *)
        unfold sort_no_obj'. simpl.
        set g := forget_objects f in IHf *.
        now destruct g, e, IHf. }
      { (* f is a cons *)
        
    

    { 

    
      { (* i = j *)
        destruct b.
        simpl.
        simpl sort_no_obj'.
        
      

    
    simpl sort_no_obj'.
    
    
  
                         
  (* The sorting algorithm sends morphisms in free_cat_on_sd to
     morphisms in free_cat_on_sd. *)
  Definition sort_no_obj'_lift {n m : nat}
    (f : @hom free_cat_on_sd n m)
    : @hom free_cat_on_sd n m.
  Proof.
    destruct f; [ exact tnil |].
    set e0 := forget_objects' e.
    set f0 := forget_objects f.
    set sf := sort_no_obj' e0 f0.
    remember sf as sf' eqn:heqnsf.
    induction sf'.
    { have a : i = m.
      { 

      
      unfold sort_no_obj' in sf.
      
    
    simpl in e. unfold sd_edges in e.
    destruct j; [ contradiction e |].
        
    set sf := forget_objects f; 
    induction sf'.
    { induction f.
      { exact tnil. }
      { simpl in sf. destruct j; [contradiction |].
    
  
  
  Definition sort_no_obj'_lift {n m : nat}
    (f : @hom free_cat_on_sd n m)
    : @hom free_cat_on_sd n m.
  Proof.
    induction f as [| i j e f]; [exact tnil |].
    destruct j; [ contradiction |].
    set sf := forget_objects f; unfold forget_objects in sf.
    destruct f as [ | i' j' e2 g]; 
      [ exact (tlist_singleton e) |].

    cbn in sf. 
    destruct j'; [ contradiction |].
    destruct (eqn i' j') in sf.
    (* set eqn_ij := eqn i' j' in sf. *)
    set (eq_reflect := (@eqP _ i' j')).
    change (eqn i' j') with (i' == j') in sf.
    set ij := i' == j' in eq_reflect, sf.
    
    destruct eq_reflect.
    { 

    

    change (@Equality.Pack nat nat_eqMixin) with eqn.






















    
    set eq_i'j' := i' == j' in sf.

    
    simpl in sf.
    
    unfold tlist'_rec, tlist'_rect in sf.
    
    unfold forget_objects in sf.
    simpl in sf.
    simpl in sf.    
    
    
    remember sf as sf' eqn:Heqsf.
    induction s.
    { 
      
    destruct f as [ | i j e f]; [exact tnil |].

    set sf := sort_no_obj' e (forget_objects f).

  Proposition sorting_lifts_to_morphisms' {n m : nat}
    (f : @hom free_cat_on_sd n m)
    : { g : @hom free_cat_on_sd n m &
              sort_no_obj' (forget_objects f) = forget_objects g }.
  Proof.
    (* TODO *)
    Abort.

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

  
