  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*						  	         *)
  (*   File : itera.v					         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : definition of function iterate		         *)
  (***************************************************************)

Section iter.

  Require Export iteraterme.

  Variable Sigma : Set. (* state set *)
  Variable n : nat. (* bytecode size *)
  Variable succs : forall p:nat, p<n->nb_list n. (* successor function *)
  Variable step : forall p:nat, p<n->Sigma->list Sigma. (* flow function *)
  Variable r : relation Sigma. (* order on state set *)
  Variable sup : binop Sigma. (* sup on state set *)

  Hypothesis step_succs_same_length : forall (q:nat) (C:q<n) (s : Sigma), 
    nb_length (succs q C) = length (step q C s).
  Hypothesis eq_Sigma_dec : forall x y : Sigma, {x = y} + {x <> y}.
  Hypothesis r_is_semilattice : semilattice Sigma r sup.
  Hypothesis wfr : ascending_chain r.

  Notation Step' := (step' Sigma n succs step step_succs_same_length).

  Notation Iteraterme := (iteraterme Sigma n succs step r sup eq_Sigma_dec 
    step_succs_same_length r_is_semilattice wfr).

  (* stability of an instruction with respect to a given function state *) 
  Definition stable (ss : vector Sigma n) (p : nat) (C : p<n): Prop :=
    forall (q:nat) (t:Sigma) (H:(q,t) INm (Step' p C (ss[p|C]))),
      r t (ss[q|(m_list_get_witness (Step' p C (ss[p|C])) (q,t) H)]).

  Definition stables (ss : vector Sigma n) : Prop :=
    forall (p : nat) (C : p < n), stable ss p C.

  (* step 4 of defining function iterate *)
  Definition itera (ssw : vector Sigma n * nb_list n) : vector Sigma n :=
    match Iteraterme ssw with
      | exist ss h => ss
    end.

End iter.
