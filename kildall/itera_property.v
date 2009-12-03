  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : itera_property.v			                 *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : properties of function iterate needed to        *)
  (*	       establish that Kildall's algorithm is a dfa       *)
  (***************************************************************)

Section itera_property.

  Require Export itera_eq.
  Require Export propa_property2.

  Variable Sigma : Set. (* state set *)
  Variable n : nat. (* bytecode size *)
  Variable succs : forall p:nat, p<n -> nb_list n. (* successor function *)
  Variable step : forall p:nat, p<n->Sigma->list Sigma. (* flow function *)
  Variable wi : vector Sigma n-> nat -> Prop. (* correct state for instruction predicate *)
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

  Notation Propa := (propagate sup eq_Sigma_dec).
  Notation Itera := (itera Sigma n succs step r sup step_succs_same_length 
    eq_Sigma_dec r_is_semilattice wfr).
  Notation Itera_eq := (itera_eq succs step_succs_same_length 
    eq_Sigma_dec r_is_semilattice wfr).
  Notation Propa_nondep_lexprod := (propa_nondep_lexprod Sigma n succs step 
    r sup step_succs_same_length eq_Sigma_dec r_is_semilattice).
  Notation ra := (SI_vector_pointwise Sigma r).
  Notation Acc_ssw := (acc_ssw Sigma n r eq_Sigma_dec wfr).


  Lemma iter_preserves_stable :
    forall (x : vector Sigma n * nb_list n), 
      (forall (p : nat) (C : p < n),
        ~ p INnb (snd x) ->
        stable Sigma n succs step r step_succs_same_length (fst x) p C) ->
      stables Sigma n succs step r step_succs_same_length (Itera x).
  Proof.
    intro x.
    elim (Acc_ssw x).
    clear x.
    intros x Hrec.
    destruct x as [ss w].
    destruct w.
    cut (Itera (ss, pred_nil (P n)) = ss).
    simpl; intros Heq H Hstable.
    intros p C; rewrite <- Heq in Hstable.
    apply Hstable.
    unfold not; trivial.
    generalize (Itera_eq (ss, pred_nil (P n))); trivial.
        (* w "=" a "::" w *)
    intros H Hstable.
    intros p0 C0; cut (stable  Sigma n succs step r
      step_succs_same_length (Itera (Propa ss w (Step' a p (ss[a|p])))) p0 C0).
    replace (Itera (Propa ss w (Step' a p (ss[a|p]))))
      with (Itera (ss, pred_cons (P n) a p w)).
    trivial.
    generalize (Itera_eq (ss, pred_cons (P n) a p w)); trivial.
    cut (nondep_lexprod (vector Sigma n) (nb_list n)
      (SI_vector_pointwise Sigma r n) (rb n)
      (Propa ss w (Step' a p (ss[a|p]))) (ss, pred_cons (P n)a p w));
    [intro Hpropa | apply (propa_nondep_lexprod Sigma n succs step r sup
      step_succs_same_length eq_Sigma_dec r_is_semilattice ss a w p); trivial].
    cut ((forall (p' : nat) (C' : p' < n),
      ~ p' INp (snd (Propa ss w (Step' a p (ss[a|p])))) -> 
      stable Sigma n succs step r step_succs_same_length (fst (Propa
        ss w (Step' a p (ss[a|p])))) p' C')); [intro Hstab | idtac].
    apply (H (Propa ss w (Step' a p (ss[a|p]))) Hpropa Hstab p0 C0); auto.
    (intros p' C' H').
    compare p' a; intro e.
    (*p' = a*)
    subst a.
    unfold stable.
    intros q t H0.
    apply (stable_p_by_propa Sigma n succs step r sup
      step_succs_same_length eq_Sigma_dec  r_is_semilattice p' q (ss[p'|p]) t ss w p); trivial.
    rewrite (no_change_at_p_not_in_w Sigma n r sup eq_Sigma_dec r_is_semilattice) in H0; trivial.
    generalize H0.
    rewrite (element_at_irrel Sigma n ss p' C' p).
    unfold m_list_belong; apply pred_list_equiv_belong.
    unfold step'; apply m_list_equiv_combine.
    apply (succs_equiv p' C' p).
    apply step_equiv.
    (* p' <> a *)
    inversion_clear r_is_semilattice as [O LC].
    inversion_clear O.
    intros q t H0.
    cut ((q,t) INm (Step' p' C' ((fst (ss, pred_cons (P n) a p w))[p'|C']))).
    intro H1.
    apply ord_trans with (y := (fst (ss, pred_cons (P n) a p w))[q| 
      (m_list_get_witness
        (Step' p' C' ((fst (ss, pred_cons (P n) a p w))[p'|C'])) (q, t) H1)]).
    apply Hstable.
    intro h; elim h.
    apply e.
    intro; apply H'.
    apply inc_w_propa_w.
    assumption.
    generalize H0 H1 (r_ss_propa_ss Sigma n r sup eq_Sigma_dec
      r_is_semilattice (Step' a p (ss[a|p]))
      q (fst (ss, pred_cons (P n) a p w)) w
      (m_list_get_witness
        (Step' p' C' ((fst (ss, pred_cons (P n) a p w))[p'|C'])) 
        (q, t) H1)).
    simpl.
    destruct (Propa ss w (Step' a p (ss[a|p]))); simpl.
    clear H0 H1.
    intros H0 H1.
    generalize (m_list_get_witness (Step' p' C' (ss[p'|C'])) (q, t) H1).
    intros Cq H'0.
    rewrite <- (element_at_irrel Sigma n v q Cq (m_list_get_witness
      (Step' p' C' (v[p'|C'])) (q, t) H0)); assumption.
    rewrite (no_change_at_p_not_in_w Sigma n r sup eq_Sigma_dec) in H0; auto.
  Qed.


  Remark transition :
    forall (ss : vector Sigma n) (a : nat) (w : nb_list n) (C : a < n),
      let PSS := (Propa ss w (Step' a C (ss[a|C]))) in
        let IPSS := (Itera PSS) in
          ra n (fst PSS) (fst (ss, pred_cons (P n) a C w)) \/ 
          (fst PSS = fst (ss, pred_cons (P n) a C w))  ->
          ra n IPSS (fst PSS) \/ (IPSS = (fst PSS))
          -> ra n IPSS (fst (ss, pred_cons (P n) a C w)) \/ 
          IPSS=(fst (ss, pred_cons (P n) a C w)).
  Proof.
    intros.
    inversion_clear r_is_semilattice as [O LC].
    inversion O.
    case H; case H0; intros.
    left.
    generalize H1 H2.
    generalize (fst (ss, pred_cons (P n) a C w)); generalize (fst PSS); 
      generalize IPSS.
    apply transitive_SI_vector_pointwise; try assumption.
    left.
    rewrite H1.
    assumption.
    left.
    rewrite <- H2.
    assumption.
    right.
    rewrite  H1.
    assumption.
  Qed.

  Lemma iter_decrease :
    forall (x : vector Sigma n * nb_list n),
      ra n (Itera x) (fst x) \/ Itera x = fst x.
  Proof.
    intro x.
    generalize (Acc_ssw x).
    intro Hacc; elim Hacc; clear Hacc x.
    intros x H Hrec.
    generalize (Itera_eq x).
    CaseEq x.
    intros ss' w'.
    case w'.
    simpl; intros Heq1 Heq2.
    right; trivial.
    intros a Ca wa ex Heq.
    rewrite <- ex.
    replace (Itera x) with (Itera (Propa ss' wa (Step' a Ca (ss'[a|Ca])))).
    subst x; apply transition.
    apply (propa_decrease Sigma n succs step r sup step_succs_same_length 
      eq_Sigma_dec r_is_semilattice ss' a wa Ca).
    apply Hrec.
    apply (Propa_nondep_lexprod ss' a wa Ca).
    subst x; symmetry; trivial.
  Qed.


  Lemma iter_lub :
    forall (x:vector Sigma n * nb_list n) (ts:vector Sigma n),
      (monotonestep Sigma n step r)->
      (ra n ts (fst x) \/ ts = fst x) /\ 
      stables Sigma n succs step r step_succs_same_length ts ->
      ra n ts (Itera x) \/ ts = Itera x.
  Proof.
    intro x.
    generalize (Acc_ssw x).
    intro Hacc; elim Hacc; clear Hacc x.
    intros x H Hrec.
    generalize (Itera_eq x).
    CaseEq x.
    intros ss w.
    case w.
    simpl; intros eq H' ts monostep H''.
    cut (ra n ts ss \/ ts = ss); 
      [intro H'''; rewrite <- H' in H'''; trivial | idtac].
    elim H''; trivial.
    intros a Ca wa ex Heq ts monostep H'.
    cut (ra n ts (Itera (Propa ss wa (Step' a Ca (ss[a|Ca])))) \/
      ts = Itera (Propa ss wa (Step' a Ca (ss[a|Ca])))); 
    [intro H'''; rewrite <- Heq in H'''; trivial | idtac].
    apply Hrec; auto.
    rewrite ex.
    apply (Propa_nondep_lexprod ss a wa Ca).
    inversion_clear H' as [H0 H1].
    split; auto.
    inversion r_is_semilattice as [O LC]; inversion O.
    apply vector_pointwise_imp_SI_vector_pointwise_or_eq; try assumption.
    apply forall_element_to_vector_pointwise.
    intros q Cq.
    apply (r_propa_ss_ts Sigma n succs step r sup step_succs_same_length eq_Sigma_dec r_is_semilattice); auto.
  Qed.


  Theorem Theorem_iter :
    forall (x : vector Sigma n * nb_list n),
      ascending_chain r ->
      (monotonestep Sigma n step r)->
      (forall (p : nat) (C : p < n),
        ~ p INnb (snd x) ->
        stable Sigma n succs step r step_succs_same_length (fst x) p C) ->
      stables Sigma n succs step r step_succs_same_length (Itera x) /\
      vector_pointwise Sigma r n (fst x) (Itera x) /\
      (forall ts : vector Sigma n,
        vector_pointwise Sigma r n (fst x) ts /\ 
        stables Sigma n succs step r step_succs_same_length ts ->
        vector_pointwise Sigma r n (Itera x) ts).
  Proof.
    Semi r_is_semilattice.
    intro x; CaseEq x.
    intros ss w; intros eq asc_r monostep H'.
    split.
    apply (iter_preserves_stable (ss, w)); assumption.
    split.
    apply  SI_vector_pointwise_or_eq_imp_vector_pointwise; try assumption.
    apply (iter_decrease (ss,w)).
    intros ts H''.
    apply  SI_vector_pointwise_or_eq_imp_vector_pointwise; try assumption.
    apply (iter_lub (ss,w) ts).
    assumption.
    split.
    inversion H'' as [h h'].
    apply (vector_pointwise_imp_SI_vector_pointwise_or_eq Sigma r n ts (fst (ss,w))); try assumption.
    elim H''; trivial.
  Qed.

End itera_property.
