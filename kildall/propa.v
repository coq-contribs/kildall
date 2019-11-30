  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : propa.v					         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : specification of function propagate             *)
  (***************************************************************)

Section propa.

  Require Export vector_results.
  Require Export Wf_nat.
  Require Export m_list.

  Variable Sigma : Set. (* state set *)
  Variable r : relation Sigma. (* order on state set *)
  Variable sup : binop Sigma. (* sup on state set *)

  Hypothesis eq_Sigma_dec : forall x y : Sigma, {x = y} + {x <> y}.
  Hypothesis r_is_semilattice : semilattice Sigma r sup.
  Hypothesis wfr : ascending_chain r.

  Fixpoint propagate (n : nat) (ss : vector Sigma n) (wlist : nb_list n) 
    (l : m_list n Sigma) {struct l} : (vector Sigma n) * (nb_list n):=
    match l return (vector Sigma n)*(nb_list n) with
      | pred_nil=> (ss, wlist)
      | pred_cons (q,s) C l1 =>
        let u := sup s (ss[q|C]) in
          match eq_Sigma_dec u (ss[q|C]) with
            | left _ => propagate n ss wlist l1 
            | right _ => propagate n (ss[q<-u]) (nb_list_add_element wlist q C) l1
          end
    end. 

  Notation ra:=(SI_vector_pointwise Sigma r).

  Remark ra_replace :
    forall (n : nat) (ss : vector Sigma n) (p : nat) (t : Sigma) (C : p<n),
      sup t (ss[p|C]) <> ss[p|C]-> ra n (ss[p<-(sup t (ss[p|C]))]) ss.
  Proof.
    intros n' ss p t C H.
    Semi r_is_semilattice.
    split.
    unfold inv.
    apply (vector_pointwise_replace Sigma r ord_refl n' ss p C (sup t (ss[p|C]))).
    apply lub2; assumption.
    apply neq_replace with C.
    assumption.
  Qed.

  (* either first component of propagate result is less than its sized list
     argument, or nothing changes *) 
  Lemma propa_case :
    forall (n:nat) (ss ss':vector Sigma n) (w w':nb_list n) (l:m_list n Sigma),
      (ss', w') = propagate n ss w l -> ra n ss' ss \/ (ss, w) = (ss', w').
  Proof.
    inversion r_is_semilattice as [O L].
    intros n ss ss' w w' l.
    generalize ss ss' w w'.
    clear ss ss' w w'.
    elim l; simpl. 
    intros; right; symmetry; assumption.
    intro a; elim a; clear a.
    intros a b p d Hrec ss ss' w w'.
    elim (eq_Sigma_dec (sup b (ss[a|p])) (ss[a|p])); intro comp.
    apply Hrec; assumption.
    intro H.
    cut (ra n ss' (ss[a<-(sup b (ss[a|p]))])\/ 
      ((ss[a<-(sup b (ss[a|p]))]),(pred_list_add_element eq_nat_dec w a p))=
      (ss',w')).
    intros ra_rep; elim ra_rep. 
    left.
    apply (transitive_SI_vector_pointwise Sigma r n O eq_Sigma_dec ss' 
      (ss[a<-(sup b (ss[a|p]))]) ss).
    assumption.
    apply ra_replace; try assumption.
    intro eq; left; inversion eq.
    apply ra_replace; try assumption.
    apply Hrec; try assumption.
  Qed.

  (* propagate does not remove any element from the work list *)
  Lemma inc_w_propa_w :
    forall (n:nat) (l:m_list n Sigma) (ss:vector Sigma n) (p:nat) (w:nb_list n),
      p INnb w -> p INnb (snd (propagate n ss w l)).
  Proof.
    intros n l; elim l; simpl.
    trivial.
    intro a; elim a; clear a.
    intros a b C d Hrec ss p w H. 
    elim (eq_Sigma_dec (sup b (ss[a|C])) (ss[a|C])); 
      intro; apply Hrec.
    assumption.
    apply (nb_list_belong_add w a p C).
    assumption.
  Qed.

End propa.

Arguments propagate [Sigma] _ _ [n].
