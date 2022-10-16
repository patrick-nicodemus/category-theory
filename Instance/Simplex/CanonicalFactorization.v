Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Theory.Category.
Require Import Instance.Simplex.AugmentedSimplexCategory.
Require Import Instance.Simplex.NaturalNumberArithmetic.
Require Import Instance.Simplex.FaceAndDegeneracyMaps.

Require Import Construction.Free.Quiver.

Require Import ssreflect.
Require Import ssrfun.
Require Import ssrbool.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finfun.

Open Scope nat_scope.
Notation "''I_' n" := (ordinal n).

Section FreelyGenerated.
  Variant face_map (n : nat) :=
    | d : 'I_(n.+1) -> face_map.

  Variant degeneracy_map (n : nat) :=
    | s : 'I_(n.+1) -> degeneracy_map.

  Definition sd_edges : nat -> nat -> Type :=
    fun n m =>
      match m with
      | O => void
      | S m' => if n == m' then face_map m' else
                  if n == m'.+2 then degeneracy_map m' else
                    void
      end.
    
  Definition sd_quiver : Quiver := {| nodes := nat ; edges := sd_edges |}.

  Definition free_cat_on_sd := FreeOnQuiver sd_quiver.

  Arguments sd_edges /.
  Definition sd_quiverhom : QuiverHomomorphism sd_quiver (QuiverOfCat finord).
    unshelve eapply Build_QuiverHomomorphism.
    { exact: @id. }
    { simpl. intros x y; destruct y; [ done |].
      destruct (@eqP _ x y) as [ x_eq_y | x_neq_y ].
      { destruct x_eq_y;
        intro di; destruct di as [ i ]; exact (δ i). }
      { destruct (@eqP _ x y.+2) as [x_eq_SSy | x_neq_SSy].
        { apply symmetry in x_eq_SSy. destruct x_eq_SSy.
          intro si; destruct si as [ i]. exact (σ i). }
        done. } }
  Defined.

  Definition sd_induced_functor := InducedFunctor _ _ sd_quiverhom.

  
  
  Definition InductivelyGeneratedSimplexCat := Quotient free_cat_on_sd
  
  

  Definition factorization_surj {n m : nat} (f : 'I_ m ^n) 
    (p : surjective f) :
    @hom free_cat_on_sd n m.
  Proof.
    assert (z : rgeq n m) by (apply: leq_implies_rgeq; exact: (surjective_card f)). 
    induction z as [| m ineq IH ]; [ exact TList.tnil |].
    destruct m as [ | m]; 
      [ by destruct n; [ exact TList.tnil | abstract(destruct (f ord0); discriminate) ] |].
    apply rgeq_implies_leq in ineq.
    assert (z := nltm_not_injective f ineq).
    set i := not_injective_hitstwice_val f.
    unshelve apply (@tlist_rcons sd_quiver edges _ m.+2).
    { apply (IH (degeneracy_factoring_map f i (not_injective_hitstwice_spec f z))).
      apply (factoring_preserves_surjectivity); exact: p. }
    { simpl. do 2! resolve_boolean. exact (s m i). }
  Defined.

  Definition factorization {n m : nat} (f : 'I_ m ^n) 
    (p : surjective f) :
    @hom free_cat_on_sd n m.
  Proof.
    assert (z : rgeq n m) by (apply: leq_implies_rgeq; exact: (surjective_card f)). 
    induction z as [| m ineq IH ]; [ exact TList.tnil |].
    destruct m as [ | m]; 
      [ by destruct n; [ exact TList.tnil | abstract(destruct (f ord0); discriminate) ] |].
    apply rgeq_implies_leq in ineq.
    assert (z := nltm_not_injective f ineq).
    set i := not_injective_hitstwice_val f.
    unshelve apply (@tlist_rcons sd_quiver edges _ m.+2).
    { apply (IH (degeneracy_factoring_map f i (not_injective_hitstwice_spec f z))).
      apply (factoring_preserves_surjectivity); exact: p. }
    { simpl. do 2! resolve_boolean. exact (s m i). }
  Defined.

  
  Program Definition factorization {n m : nat} (f : 'I_ m ^n) :
    @hom free_cat_on_sd n m :=
    match m with
    | O => match n with
           | O => (TList.tnil)
           | _ => _
           end
    | S n' => _
    end.
  Next Obligation. destruct n; [ contradiction |].
                   set x := (@ord0 n); destruct (f x);
                            auto with arith. Qed.
  Next Obligation.
                   

  
  (* TList.tlist sd_edges n m *)
  simpl.
    
  

  
