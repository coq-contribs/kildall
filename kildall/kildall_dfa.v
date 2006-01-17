  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : kildall_dfa.v				         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : proof that kildall's algorithm is a dfa         *)
  (***************************************************************)

Section kildall_data_flow_analizer.

  Require Export itera_property.
  Require Export dfa.

  Variable Sigma : Set. (* state set *)
  Variable n : nat. (* bytecode size *)
  Variable succs : forall p:nat, p<n -> nb_list n. (* successor function *)
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

  Notation Step' := (step' Sigma n succs step step_succs_same_length).

  Notation KIldall := (Kildall Sigma n succs step r sup step_succs_same_length 
    eq_Sigma_dec r_is_semilattice wfr).

  Notation IS_data_flow_analyser := (Is_data_flow_analyser Sigma n succs step 
    r step_succs_same_length).

  Notation MonotoneStep := (monotonestep Sigma n step r).

  Lemma contrap : forall (P:Prop) (Q:bool), 
    (Q=false->P)->(~P->Q=true).
  Proof.
    intros P Q H h.
    induction Q.
    trivial.
    elim h.
    apply H; trivial.
  Qed.

  Lemma work_list_not_stable :
    forall (ss : vector Sigma n) (p : nat) (Cp : p < n),
      ~ p INnb (work_list Sigma n succs step sup step_succs_same_length eq_Sigma_dec ss n (le_refl n)) ->
      is_stable Sigma n sup eq_Sigma_dec ss p Cp (Step' p Cp (ss[p|Cp])) = true.
  Proof.
    intros ss p Cp.
    apply contrap.
    intro H.
    cut (p INnb (work_list Sigma n succs step sup step_succs_same_length 
      eq_Sigma_dec ss (S p) (le_lt_Sn_m p n Cp))).
    apply up_wl.
    apply succs_equiv.
    apply step_equiv.
    simpl.
    rewrite (element_at_irrel Sigma n ss p (le_lt_Sn_m p n (le_lt_Sn_m p n Cp)) Cp).
    rewrite (is_stable_irrel Sigma n sup eq_Sigma_dec ss p 
      (Step' p (le_lt_Sn_m p n (le_lt_Sn_m p n Cp)) (ss[p|Cp])) 
      (le_lt_Sn_m p n (le_lt_Sn_m p n Cp)) Cp).
    rewrite <- (is_stable_list_irrel Sigma n sup eq_Sigma_dec ss p 
      (Step' p (le_lt_Sn_m p n (le_lt_Sn_m p n Cp)) (ss[p|Cp])) 
      (Step' p Cp (ss[p|Cp])) Cp).
    induction (is_stable Sigma n sup eq_Sigma_dec ss p Cp (Step' p Cp (ss[p|Cp]))).
    inversion H.
    left.
    trivial.
    unfold step'; unfold m_list_equiv; apply m_list_equiv_combine; try auto.
    apply succs_equiv.
  Qed.


  Lemma is_stable_stable :
    forall (ss : vector Sigma n) (p : nat) (Cp : p<n),
      is_stable Sigma n sup eq_Sigma_dec ss p Cp (Step' p Cp (ss[p|Cp]))=true ->
      stable Sigma n succs step r step_succs_same_length ss p Cp.
  Proof.
    intros ss p Cp.
    unfold stable.
    elim (Step' p Cp (ss[p|Cp])).
    simpl.
    intros dd ddd dddd H; inversion H.
    simpl.
    intro a; elim a; clear a; intros a b Ca d Hrec His q t H.
    elim H; intro case.
    cut (a=q).
    intro Haq.
    cut (b=t).
    intro Hbt.
    replace (ss[q|(m_list_get_witness (pred_cons (Q n Sigma) (a,b) Ca d) (q, t) H)]) 
      with (ss[a|Ca]).
    apply (lub_r_sup Sigma r sup).
    assumption.
    rewrite <- Hbt; trivial.
    generalize His.
    elim (eq_Sigma_dec (sup b (ss[a|Ca])) (ss[a|Ca])).
    trivial.
    intros HC I; inversion I.
    subst q. 
    apply element_at_irrel.
    replace b with (snd (a,b)); [rewrite <- case | simpl]; trivial.
    replace a with (fst (a,b)); [rewrite <- case | simpl]; trivial.
    rewrite (element_at_irrel Sigma n ss q (m_list_get_witness (pred_cons (Q n Sigma)
      (a,b) Ca d) (q,t) H) (m_list_get_witness d (q,t) case)).
    generalize His.
    elim (eq_Sigma_dec (sup b (ss[a|Ca])) (ss[a|Ca])).
    intros; apply Hrec; try assumption.
    intros h h'; inversion h'.
  Qed.

  Theorem monotone_step_imp_kildall_dfa : 
    MonotoneStep -> IS_data_flow_analyser KIldall.
  Proof.
    intro monostep.
    unfold Is_data_flow_analyser.
    unfold Kildall.
    intros ss.
    apply
      (Theorem_iter Sigma n succs step r sup step_succs_same_length eq_Sigma_dec 
        r_is_semilattice wfr succs_equiv step_equiv
        (ss, work_list Sigma n succs step sup step_succs_same_length eq_Sigma_dec 
          ss n (le_refl n))); auto.
    simpl.
    intros p C H'.
    apply is_stable_stable.
    apply work_list_not_stable.
    assumption.
  Qed.


End kildall_data_flow_analizer.
