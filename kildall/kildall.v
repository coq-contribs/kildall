  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*						  	         *)
  (*   File : kildall.v					         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content :	specification of kildall's algorithm     *)
  (***************************************************************)

Section kildall.

  Require Export itera.

  Variable Sigma : Set. (* state set *)
  Variable n : nat. (* bytecode size *)
  Variable succs : forall p:nat, p<n->nb_list n. (* successor function *)
  Variable step : forall p:nat, p<n->Sigma->list Sigma. (* flow function *)
  Variable wi : vector Sigma n -> nat -> Prop. (* correct state for instruction predicate *)
  Variable r : relation Sigma. (* order on state set *)
  Variable T : Sigma. 		(* Top element *)
  Variable sup : binop Sigma. (* sup on state set *)

  Hypothesis step_succs_same_length : forall (q:nat) (C:q<n) (s : Sigma), 
    nb_length (succs q C) = length (step q C s).
  Hypothesis eq_Sigma_dec : forall x y : Sigma, {x = y} + {x <> y}.
  Hypothesis r_is_semilattice : semilattice Sigma r sup.
  Hypothesis wfr : ascending_chain r.
  Hypothesis succs_equiv : forall (p : nat) (C C' : p<n), 
    (succs p C) =nb= (succs p C').
  Hypothesis step_equiv : forall (p:nat) (C C' : p<n) (s:Sigma), 
    (step p C s) = (step p C' s).

  Notation Itera := (itera Sigma n succs step r sup step_succs_same_length 
    eq_Sigma_dec r_is_semilattice wfr).
  Notation Step' := (step' Sigma n succs step step_succs_same_length).

  (* returns true if the list ss is stable *)
  Fixpoint is_stable (ss:vector Sigma n) (p:nat) (C:p < n) (succs':m_list n Sigma)
    {struct succs'} : bool :=
    match succs' with
      | pred_nil => true
      | pred_cons (q,t) Cq succsq =>
        match
          eq_Sigma_dec (sup t (ss[q|Cq])) (ss[q|Cq])
          with
      	  | left _ => is_stable ss p C succsq
      	  | right _ => false
        end
    end.

  Require Import Arith.

  Definition le_lt_Sn_m (p n:nat) (C:le (S p) n) := lt_S_n p n (le_lt_n_Sm (S p) n C).

  (* computes work list, i.e. list of unstable elements *)
  Fixpoint work_list (ss : vector Sigma n) (l : nat) {struct l} : 
    (le l n)->nb_list n :=
    match l return (le l n)->(nb_list n) with
      | O => fun (h: le 0 n)=>(pred_nil (P n))
      |  S p => fun (C : le (S p) n)=> match (is_stable ss p (le_lt_Sn_m p n C) 
        (Step' p (le_lt_Sn_m p n C) (ss[p|(le_lt_Sn_m p n C)]))) with 
      	                                 | true => work_list ss p (le_Sn_le p n C)
       	                                 | false => nb_cons p (le_lt_Sn_m p n C) (work_list ss p (le_Sn_le p n C))
	                               end
    end.

  (* results about stable : *)
  Lemma is_stable_irrel : 
    forall (ss:vector Sigma n) (p:nat) (l:m_list n Sigma) (C C':p<n),  
      is_stable ss p C l=is_stable ss p C' l.
  Proof.
    induction l.
    intros.
    simpl; trivial.
    intros.
    simpl.
    rewrite (IHl C C').
    trivial.
  Qed.

  Lemma is_stable_list_irrel : 
    forall (ss:vector Sigma n) (p:nat) (l l':m_list n Sigma) (C:p<n), 
      m_list_equiv l l' -> is_stable ss p C l'=is_stable ss p C l.
  Proof.
    induction l; destruct l'; simpl. 
    trivial.
    intros C Hsame.
    inversion Hsame.
    intros C Hsame.
    inversion Hsame.
    destruct a as [qa ta].
    destruct a0 as [qa0 ta0].
    intros C Hsame.
    inversion Hsame.
    subst qa0 ta0.
    rewrite (element_at_irrel Sigma n ss qa p0 q).
    elim (eq_Sigma_dec (sup ta (ss[qa|q])) (ss[qa|q])); intro comp.
    apply IHl.
    assumption.
    trivial.
  Qed.

  (* results about work list : *)
  Lemma  work_list_irrel_inc : forall (ss:vector Sigma n) (p q:nat) (C0 C1:p <= n),
    q INnb (work_list ss p C0) -> q INnb (work_list ss p C1).
  Proof.
    induction p; simpl.
    intros; trivial.
    intros q C0 C1.
    rewrite (is_stable_irrel ss p (Step' p (le_lt_Sn_m p n C0) 
      (ss[p|(le_lt_Sn_m p n C0)])) (le_lt_Sn_m p n C0) (le_lt_Sn_m p n C1)).
    rewrite (element_at_irrel Sigma n ss p (le_lt_Sn_m p n C0) (le_lt_Sn_m p n C1)).
    rewrite (is_stable_list_irrel ss p (Step' p (le_lt_Sn_m p n C0) 
      (ss[p|(le_lt_Sn_m p n C1)])) (Step' p (le_lt_Sn_m p n C1) 
        (ss[p|(le_lt_Sn_m p n C1)]))).
    elim (is_stable ss p (le_lt_Sn_m p n C1) (Step' p (le_lt_Sn_m p n C0) 
      (ss[p|(le_lt_Sn_m p n C1)]))).
    apply IHp.
    simpl.
    compare p q; intro comp.
    intros; left.
    symmetry; assumption.
    intro H.
    right.
    elim H.
    intro h; symmetry in h; contradiction.
    apply IHp.
    unfold step'; unfold m_list_equiv; apply m_list_equiv_combine; try auto.
    apply succs_equiv.
  Qed.

  Lemma aug_wl : forall (ss : vector Sigma n) (l : nat) (k:nat) 
    (C : l<=n) (Ck:k>=0) (Ckl:k+l<=n) (q : nat), 
    q INnb (work_list ss l C) ->q INnb (work_list ss (k+l) Ckl).
  Proof.
    induction k.
    simpl.
    intros until q.
    apply work_list_irrel_inc.
    simpl.
    intros.
    elim (is_stable ss (k + l) (le_lt_Sn_m (k + l) n Ckl) 
      (Step' (k + l) (le_lt_Sn_m (k+l) n Ckl) (ss[k+l|(le_lt_Sn_m (k + l) n Ckl)]))).
    cut (k>=0).
    intro h.
    apply (IHk C h (le_Sn_le (k + l) n Ckl)).
    assumption.
    auto with arith.
    simpl.
    right.
    cut (k>=0).
    intro h.
    apply (IHk C h (le_Sn_le (k + l) n Ckl)).
    assumption.
    auto with arith.
  Qed.


  Remark aux : forall (ss : vector Sigma n) (l q : nat) (C : l<=n),
    l = n -> q INnb (work_list ss l C) -> q INnb (work_list ss n (le_refl n)).
  Proof.
    intros ss l q C H.
    subst l.
    apply work_list_irrel_inc.
  Qed.

  Remark aux2 : forall p q : nat, p=q->p<=q.
  Proof.
    intros p q H; rewrite H; apply le_refl.
  Qed.

  Lemma up_wl : forall (ss : vector Sigma n) (l : nat) (C : l<=n) (q : nat), 
    q INnb (work_list ss l C) -> q INnb (work_list ss n (le_refl n)).
  Proof.
    intros.
    cut ((n-l)+l<=n).
    intro h.
    cut (q INnb (work_list ss ((n-l)+l) h)).
    apply aux.
    rewrite plus_comm.
    apply le_plus_minus_r.
    assumption.
    apply (aug_wl ss l (n-l) C).
    auto with arith.
    assumption.
    apply aux2.
    rewrite plus_comm.
    apply le_plus_minus_r.
    assumption.
  Qed.


  (* definition of function kildall : *)
  Definition Kildall (ss : vector Sigma n) : vector Sigma n :=
    Itera (ss, work_list ss n (le_refl n)).

End kildall.
