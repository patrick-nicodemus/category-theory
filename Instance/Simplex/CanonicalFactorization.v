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

Require Import Construction.Free.Quiver.
Require Import Construction.Quotient.

Require Import ssrfun.
Require Import ssrbool.
Require Import mathcomp.ssreflect.seq.
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
  Definition δf (n : nat) (i : 'I_(n.+1)) : @hom free_cat_on_sd n n.+1.
  Proof.
    simpl. refine (tlist_singleton _). 
    destruct (@eqP _ n n).
    { exact (δ i). }
    { now contradiction n0. }
  Defined.

  Definition σf (n : nat) (i : 'I_(n.+1)) : @hom free_cat_on_sd n.+2 n.+1.
  Proof.
    simpl. refine (tlist_singleton _). simpl.
    destruct (@eqP _ n.+2 n); [ now trivial |].
    destruct (@eqP _ n.+2 n.+2); [ exact (σ i) | now trivial].
  Defined.
  
  Arguments fedgemap : clear implicits .
  Proposition δf_mapsto_δ (n : nat) (i : 'I_(n.+1)) 
    : fmap[sd_induced_functor] (δf _ i) = ASC_δ i.
  Proof.
    rewrite /sd_induced_functor
      /Quiver.InducedFunctor
      /fmap
      /δf
      /tlist_singleton
      /tlist'_rect.
    rewrite -> (@id_left Δ).
    rewrite /sd_quiverhom.
    rewrite /fedgemap.
    unfold fedgemap.
    now destruct eqP;
    [ rewrite (Peano_dec.UIP_nat n n e Logic.eq_refl) | ].
  Qed.

  Proposition σf_mapsto_σ (n : nat) (i : 'I_(n.+1)) 
    : fmap[sd_induced_functor] (σf _ i) = ASC_σ i.
  Proof.
    rewrite /sd_induced_functor
      /Quiver.InducedFunctor
      /fmap
      /σf
      /tlist_singleton
      /tlist'_rect;
    rewrite -> (@id_left Δ);
    rewrite /sd_quiverhom;
    rewrite /fedgemap;
    unfold fedgemap;
      destruct eqP.
    { now contradiction (Plus.n_SSn_stt n). }
    { destruct eqP.
      { now rewrite (Peano_dec.UIP_nat (n.+2) (n.+2)
                       (symmetry e) (erefl)) . }
      { contradiction. }
      } 
  Qed.      
  
  Variant basic_morphism_rel
    : forall (n m : nat) (f g :  @hom free_cat_on_sd n m), Type :=
    (*  d_i d_j = d_{j-1} d_i   (i < j)
        δ_j ∘ δ_i = δ_i ∘ δ_{j-1} *)
    | law1 : forall (n : nat) (i : 'I_(n.+1)) (j : 'I_(n.+2)),
        i < j ->  basic_morphism_rel n n.+2
                    ((δf _ j) ∘ (δf _ i))
                    ((δf _ (ord_upcast i)) ∘
                       (δf _ (ord_predn j)))
    (*  s_i s_j = s_{j+1} s_i (i <= j) 
        σ_j σ_i = σ_i σ_{j+1}, i <= j *)
    | law2 : forall (n : nat) (i : 'I_(n.+2)) (j : 'I_(n.+1)),
        i <= j -> basic_morphism_rel n.+3 n.+1
                    ((σf _ j) ∘ (σf _ i))
                    ((σf _ (inord i)) ∘ (σf _ (inord (j.+1))))
    | law3i : forall (n : nat) (i j: 'I_(n.+2)),
        i < j -> basic_morphism_rel n.+2 n.+2
                   ((σf _ j) ∘ (δf _ (ord_upcast i)))
                   ((δf _ i) ∘ (σf _ (ord_predn j)))
    | law3ii : forall (n : nat) (i : 'I_(n.+1)),
        basic_morphism_rel n.+1 n.+1
          ((σf _ i) ∘ (δf _ (ord_upcast i)))
          tnil
    | law3iii : forall (n : nat) (i : 'I_(n.+1)),
        basic_morphism_rel n.+1 n.+1
          ((σf _ i) ∘ (δf _ (lift ord0 i)))
          tnil
    | law3iv : forall (n : nat) (i : 'I_(n.+3)) (j : 'I_(n.+1)),
        i > j.+1 -> basic_morphism_rel n.+2 n.+2
                    ((σf _ (ord_upcast j) ∘ (δf _ i)))
                    ((δf _ (ord_predn i)) ∘ (σf _ j)).

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
    destruct a.
    { rewrite -> 2 fmap_comp, -> 4 δf_mapsto_δ;
      now apply δi_δj.  }
    { rewrite -> 2 fmap_comp, -> 4 σf_mapsto_σ.
      now apply σi_σj. }
    { rewrite -> 2 fmap_comp, -> 2 σf_mapsto_σ, -> 2 δf_mapsto_δ;
        now apply (δi_σj_iltj i j i0). }
    { rewrite -> fmap_comp, -> σf_mapsto_σ, -> δf_mapsto_δ, -> fmap_id.
      now apply δi_σi_eq_id. }
    { rewrite -> fmap_comp, -> σf_mapsto_σ, -> δf_mapsto_δ, -> fmap_id.
      now apply δSi_σi_eq_id. }
    { rewrite -> 2 fmap_comp, -> 2 σf_mapsto_σ, -> 2 δf_mapsto_δ.
      now apply δi_σj_i_gt_Sj. }
  Qed.

  (** First half of the equivalence. *)
  Definition evaluationFunctor :=
    Quotient.InducedFunctor
    free_cat_on_sd
    finord
    basic_morphism_rel
    sd_induced_functor
    functor_respects.

  Definition factorization_surj {n m : nat} (f : 'I_ m ^n) 
    (p : surjective f) :
    @hom free_cat_on_sd n m.
  Proof.
    assert (z : rgeq n m) by
      abstract(apply: leq_implies_rgeq; exact: (surjective_card f)). 
    induction z as [| m ineq IH ]; [ exact TList.tnil |].
    destruct m as [ | m]; 
      [ by destruct n;
        [ exact TList.tnil
        | abstract(destruct (f ord0); discriminate) ] |].
    apply rgeq_implies_leq in ineq.
    assert (z : ~~ injectiveb f) by
      abstract(exact:(nltm_not_injective f ineq)).
    set i := not_injective_hitstwice_val f.
    unshelve apply (@tlist_rcons sd_quiver edges _ m.+2).
    {
      rapply (IH (degeneracy_factoring_map f i
                    (not_injective_hitstwice_spec f z))).
      abstract(apply (factoring_preserves_surjectivity); exact: p). }
    {
      simpl.
      destruct (@eqP _  m.+2 m). {
        abstract(contradiction (Plus.n_SSn_stt m);
          symmetry; assumption). }
      destruct (@eqP _  m.+2 m.+2) as [eq | diseq].
      { exact (σ i). }
      { abstract(now contradiction diseq). }
    }
  Defined.
        
  Proposition factorization_surj_spec (n m : nat) 
    (f : @hom finord n m) (p : surjective f)
    : fmap[evaluationFunctor] (factorization_surj f p) = f.
  Proof.
    rewrite /evaluationFunctor /InducedFunctor; unfold fmap.
    rewrite /sd_induced_functor.
    rewrite /factorization_surj.
    set z := (factorization_surj_subproof _ _ _ _).
    induction z.
    {
      cbn. hammer.
    
    

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
      [ exact: (factorization_surj f surj) |].

    move/negP: not_surj => not_surj.
    rewrite/surjective -not_surj_has in not_surj.
    have t := gtest_st_spec _ not_surj.
    set i := (findlast_ord _ not_surj) in t.
    refine (_ +++ (δf _ i)).
    apply: IHm.
    rewrite /gtest_st in t.
    move/andP: t => [notin _].
    exact: facemap_factoring_map f i notin.
  Defined.    


