  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : itera_eq.v				         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : proof that function iterate complies to its     *)
  (*	       specification				         *)
  (***************************************************************)

Section itera_eq.

  Require Export itera.

  Variable Sigma : Set. (* state set *)
  Variable n : nat. (* bytecode size *)
  Variable succs : forall p:nat, p<n-> nb_list n. (* successor function *)
  Variable step : forall p:nat, p<n->Sigma->list Sigma. (* flow function *)
  Variable r : relation Sigma. (* order on state set *)
  Variable sup : binop Sigma. (* sup on state set *)

  Hypothesis step_succs_same_length : forall (q:nat) (C:q<n) (s : Sigma), 
    nb_length (succs q C) = length (step q C s).
  Notation Step' := (step' Sigma n succs step step_succs_same_length).

  Hypothesis eq_Sigma_dec : forall x y : Sigma, {x = y} + {x <> y}.
  Hypothesis r_is_semilattice : semilattice Sigma r sup.
  Hypothesis wfr : ascending_chain r.	 

  Notation Propa := (propagate sup eq_Sigma_dec).
  Notation Itera := (itera Sigma n succs step r sup step_succs_same_length 
    eq_Sigma_dec r_is_semilattice wfr).

  (* step 5 in defining function iterate : *)
  Theorem itera_eq :
    forall ssw : vector Sigma n * nb_list n,
      match ssw with
        | (ss, w) =>
          match w with
            | pred_nil => Itera (ss, pred_nil (P n)) = ss
            | pred_cons p C w' =>
              Itera (ss, pred_cons (P n) p C w') =
              Itera (Propa n ss w' (Step' p C (ss[p|C])))
          end
      end.
  Proof.
    intro ssw; destruct ssw as [ss w].
    destruct w as [ | p C w].
    (* case w empty : *)
    unfold itera.
    case (iteraterme Sigma n succs step r sup eq_Sigma_dec step_succs_same_length 
      r_is_semilattice wfr (ss, pred_nil (P n))).
    simpl.
    intros ss1 He.
    elim He.
    intros x H'.
    symmetry.
    generalize (H' (S x)); intro H.
    simpl in H; apply H; trivial.
    auto with arith.
    (* case w = (p,C)::w : *)
    unfold itera.
    case (iteraterme Sigma n succs step r sup eq_Sigma_dec step_succs_same_length 
      r_is_semilattice wfr (ss, pred_cons (P n) p C w)).
    case (iteraterme Sigma n succs step r sup eq_Sigma_dec step_succs_same_length 
      r_is_semilattice wfr (Propa n ss w (Step' p C (ss[p|C])))).
    intros x H' x0 H1.
    elim H'; clear H'; intros q H'.
    elim H1; clear H1; intros q0 H1.
    simpl in H1.
    replace x0 with
      (compose (vector Sigma n* nb_list n -> vector Sigma n)
        (fl Sigma n succs step sup eq_Sigma_dec step_succs_same_length)
        (fun ssb : vector Sigma n* nb_list n => match ssb with
                                                     | (sb, wb) => sb
                                                   end) (S (q + q0))
        (Propa n ss w (Step' p C (ss[p|C])))).
    apply H'.
    auto with arith.
    generalize (H1 (S (S (q+q0)))); clear H1; intro H1.
    simpl; simpl in H1.
    apply H1.
    auto with arith.
  Qed.

End itera_eq.

Implicit Arguments itera_eq [Sigma n step r sup].
