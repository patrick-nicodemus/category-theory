Require Import Category.Lib.
Require Import Category.Theory.Category.
From Hammer Require Import Hammer Tactics.
Require Import Arith.

Open Scope nat.
Definition ord_fn_equiv (n : nat) (f g : nat -> nat)
  := forall x, x < n -> f x = g x.

(** Not bad. *)
Definition ord_fn_equivalence (n : nat) : Equivalence (ord_fn_equiv n).
Proof.
  sfirstorder.
Qed.

Definition monotonic (n : nat) (f : nat -> nat)
  := forall i j, i <= j -> j < n -> f i <= f j.

Definition isordmap (n m : nat) (f : nat -> nat)
  := forall i, i < n -> f i < m.

Print Category.

Definition stdfinset : Category.
Proof.
  Print ex.
  Search ex.
  unshelve eapply
    (@Build_Category
    nat
    (fun n m => { f : nat -> nat | (monotonic n f /\ isordmap n m f ) } )).
  { intros n m.
    unshelve eapply Build_Setoid.
    { exact ((fun f g => ord_fn_equiv n (proj1_sig f) (proj1_sig g))). }
    { abstract(sfirstorder). }
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
