  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : relations.v			                 *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : relation definitions, including	         *)
  (*             lexicographic product			         *)
  (***************************************************************)

Section relations.

  Require Export Relations.
  Require Export Arith.
  (* base set : *)
  Variable Alpha : Set.
  Variable r : relation Alpha.
  (* binary operator : *)
  Definition binop := Alpha -> Alpha -> Alpha.
  (* sup operator : *)
  Variable (sup : binop).
  (* what sup is supposed to conform to to be a real "sup" : *)
  Definition lub :=
    (forall a b : Alpha, r a (sup a b)) /\
    (forall a b : Alpha, r b (sup a b)) /\
    (forall a b c : Alpha, r a c /\ r b c -> r (sup a b) c).

  (* inverse of a relation : *)
  Definition inv (R : relation Alpha) : relation Alpha := fun a b => R b a.

  (* strict relation : *)
  Definition strict (R : relation Alpha) : relation Alpha :=
    fun a b => R a b /\ a <> b.

  (* ascending chain condition : strict inverse realtion is well-founded *)
  Definition ascending_chain := well_founded (strict (inv r)).

  (* lexicographic product of two relations : *)
  Inductive nondep_lexprod (A1 A2 : Set) (ra : relation A1) 
    (rb : relation A2) : relation (A1 * A2) :=
    | lexprod_inf :
      forall a1 a2 : A1,
        ra a1 a2 ->
        forall b1 b2 : A2, nondep_lexprod A1 A2 ra rb (a1, b1) (a2, b2)
    | lexprod_eq :
      forall b1 b2 : A2,
        rb b1 b2 -> forall a : A1, nondep_lexprod A1 A2 ra rb (a, b1) (a, b2).

End relations.

Arguments strict [Alpha].
Arguments inv [Alpha].
Arguments ascending_chain [Alpha].
