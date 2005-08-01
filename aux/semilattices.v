  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : semilattices.v				         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content :   implementation of semi-lattices.	         *)
  (***************************************************************)

Section semilattices.

  Require Export relations.

  (* base set *)
  Variable Alpha : Set.
  (* order relation and sup operator on Alpha : *)
  Variables (r : relation Alpha) (sup : binop Alpha).
  (* semilattice : set equiped with an order and a sup operator *)
  Definition semilattice :=
    order Alpha r /\ lub Alpha r sup.

  Ltac Semi s := inversion s as [O L]; inversion_clear O; 
    inversion_clear L as [lub1 d]; 
      inversion_clear d as [lub2 lub3].

  Lemma monotone_lub :
    forall a a' b b' : Alpha,
      semilattice ->
      r a a' -> r b b' -> r (sup a b) (sup a' b').
  Proof.
    intros a a' b b' semi raa' rbb'.
    Semi semi.
    apply lub3; try assumption.
    split.
    apply ord_trans with (y:=a'); [assumption | apply lub1; assumption].
    apply ord_trans with (y:=b'); [assumption | apply lub2; assumption].
  Qed.

  Theorem idempotent_lub :
    forall a b : Alpha, semilattice -> sup a (sup a b) = sup a b.
  Proof.
    intros a b semi.
    Semi semi.
    apply ord_antisym.
    apply lub3; try assumption.
    split.
    apply lub1; assumption.
    apply ord_refl.
    apply lub2; try assumption.
  Qed.

  Theorem lub_circ : forall a b c : Alpha, semilattice -> 
    sup a (sup b c) = sup b (sup a c).
  Proof.
    intros a b c semi.
    Semi semi.
    apply ord_antisym.
    apply lub3; try assumption.
    split.
    apply ord_trans with (y:=(sup a c)); [apply lub1 | apply lub2]; try assumption.
    apply monotone_lub; try assumption.
    apply ord_refl.
    apply lub2; assumption.
    apply lub3; try assumption.
    split.
    apply ord_trans with (y:=(sup b c)); [apply lub1 | apply lub2]; try assumption.
    apply monotone_lub; try assumption.
    apply ord_refl.
    apply lub2; assumption.
  Qed.

  Lemma lub_r_sup :
    forall a b : Alpha, semilattice -> sup b a = a -> r b a.
  Proof.
    intros a b semi Heq.
    Semi semi.
    rewrite <- Heq.
    apply lub1; assumption.
  Qed.

  Lemma lub_r_sup2 :
    forall a b : Alpha, semilattice -> r b a -> sup b a = a.
  Proof.
    intros a b semi rba.
    Semi semi.
    apply ord_antisym.
    apply lub3; try assumption.
    split; [assumption | apply ord_refl].
    apply lub2; assumption.
  Qed.

  Lemma lub_refl : 
    forall a b : Alpha, semilattice -> sup a b = sup b a.
  Proof.
    intros a b semi.
    Semi semi.
    apply ord_antisym.
    apply lub3; try assumption.
    split.
    apply lub2; assumption.
    apply lub1; assumption.
    apply lub3; try assumption.
    split.
    apply lub2; assumption.
    apply lub1; assumption.
  Qed.

End semilattices.

Ltac Semi s := inversion s as [O L]; inversion_clear O; 
  inversion_clear L as [lub1 d]; inversion_clear d as [lub2 lub3].
