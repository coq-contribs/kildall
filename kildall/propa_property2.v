  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : propa_property2.v				         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : properties of function propagate needed to      *)
  (*	       prove kildall's algorithm is a dfa	         *)
  (***************************************************************)

Section propa_property2.

  Require Export itera.

  Variable Sigma : Set. (* state set *)
  Variable n : nat. (* bytecode size *)
  Variable succs : forall p:nat, p<n -> nb_list n. (* successor function *)
  Variable step : forall p:nat, p<n->Sigma->list Sigma. (* flow function *)
  Variable r : relation Sigma. (* order on state set *)
  Variable sup : binop Sigma. (* sup on state set *)

  Hypothesis step_succs_same_length : forall (q:nat) (C:q<n) (s : Sigma), 
    nb_length (succs q C) = length (step q C s).
  Hypothesis eq_Sigma_dec : forall x y : Sigma, {x = y} + {x <> y}.
  Hypothesis r_is_semilattice : semilattice Sigma r sup.

  Notation Step' := (step' Sigma n succs step step_succs_same_length).
  Notation Propa := (propagate sup eq_Sigma_dec).
  Notation ra := (SI_vector_pointwise Sigma r).
  Notation sup_iter := (sup_iter Sigma n sup).

  (* monotonicity of flow function : *) 
  Definition monotonestep : Prop := 
    forall (p : nat) (C : p<n) (s t : Sigma), 
      r s t -> list_pointwise Sigma r (step p C s) (step p C t).

  (* *)
  Lemma propa_decrease :
    forall (ss : vector Sigma n) (a : nat) (w : nb_list n) (C : a < n),
      ra n (fst (Propa ss w (Step' a C (ss[a|C]))))
      (fst (ss, nb_cons a C w)) \/
      fst (Propa ss w (Step' a C (ss[a|C]))) = fst (ss, nb_cons a C w).
  Proof.
    intros ss a w C.
    intros.
    replace (fst (ss, nb_cons a C w)) with (fst (ss, w)).
    case (propa_case Sigma r sup eq_Sigma_dec r_is_semilattice n ss
      (fst (Propa ss w (Step' a C (ss[a|C])))) w
      (snd (Propa ss w (Step' a C (ss[a|C]))))
      (Step' a C (ss[a|C]))).
    symmetry; apply surjective_pairing.
    left; assumption.
    simpl; intro H.
    right.
    injection H.
    intros e e'; rewrite <- e'.
    trivial.
    simpl; trivial.
  Qed.

  Remark prod_eq : forall (a q : nat) (b t : Sigma), 
    (a,b)=(q,t) -> a=q /\ b=t. 
  Proof.
    intros a q b t H; split.
    replace a with (fst (a,b)); [rewrite H | auto]; auto.
    replace b with (snd (a,b)); [rewrite H | auto]; auto.
  Qed.


  Lemma no_change_at_p_not_in_succs :
    forall (l : m_list n Sigma) (q : nat) (ss : vector Sigma n) (w : nb_list n) (Cq : q<n),
      ~ q INfst l -> (fst (Propa ss w l))[q|Cq] = ss[q|Cq].
  Proof.
    intro l; elim l; simpl.
    trivial.
    intro a; elim a; clear a; intros a b Ca d Hrec q ss w Cq Hbelong.
    elim (eq_Sigma_dec (sup b (ss[a|Ca])) (ss[a|Ca])); intro case.
  (* sup b ss[a] = ss[a] *)
    apply Hrec; try assumption.
    intro; apply Hbelong; right; assumption.
  (* sup b ss[a] <> ss[a] *)
    rewrite (propa_replace_commut Sigma n r sup eq_Sigma_dec r_is_semilattice d ss a
      (nb_list_add_element w a Ca) (nb_list_add_element w a Ca) Ca b); try assumption.
    compare a q; intro comp.
  (* a = q *)
    subst a; elim Hbelong; left; trivial.
  (* a <> q *)
    rewrite (element_at_in_replaced'); try assumption.
    apply Hrec; try assumption.
    intro; elim Hbelong; right; assumption.
  Qed.


  Lemma propa_lub : forall (l : m_list n Sigma) (q :nat) (ss : vector Sigma n) (w : nb_list n) (Cq : q<n), 
    q INfst l -> r ((fst (Propa ss w l))[q|Cq]) (sup_iter (ss[q|Cq]) l q).
  Proof. 
    Semi r_is_semilattice.
    intro l; elim l; simpl.
    intros q ss w Cq  F; inversion F.
    intro a; elim a; clear a; intros a b Ca d Hrec q ss w Cq Hbelong.
    elim (eq_Sigma_dec (sup b (ss[a|Ca])) (ss[a|Ca])); intro case.
  (* case : sup b (ss[a|C]a) = ss[a|C]a *)
    elim (eq_nat_dec q a); intro comp.
  (* q = a *)
    subst a.
    elim (m_list_belong_fst_dec n Sigma d q); intro case_fst.
  (* q in fst d *) 
    rewrite (element_at_irrel Sigma n ss q Ca Cq) in case.
    rewrite (lub_refl Sigma r sup (ss[q|Cq]) b); auto.
    rewrite case; apply Hrec; auto.
  (* q not in fst d *)
    rewrite no_change_at_p_not_in_succs; try assumption.
    apply ord_trans with (sup (ss[q|Cq]) b).
    apply lub1; assumption.
    apply (sup_iter_r Sigma n r sup); auto.
  (* q <> a *)
    elim Hbelong; clear Hbelong; intro Hbelong.
    elim comp; subst a; trivial.
    apply Hrec; auto.
  (* case : sup b (ss[a|C]a) <> ss[a|C]a *)
    rewrite (propa_replace_commut Sigma n r sup eq_Sigma_dec r_is_semilattice d ss a (nb_list_add_element w a Ca) w Ca b); try assumption.
    elim (eq_nat_dec q a); intro comp.
  (* q = a *)
    subst a.
    rewrite (element_at_in_replaced).
    rewrite (element_at_irrel Sigma n ss q Ca Cq).
    rewrite (lub_refl Sigma r sup b (ss[q|Cq])); auto.
  (* q <> a *)
    rewrite element_at_in_replaced'; auto.
    elim Hbelong; clear Hbelong; intro Hbelong.
    elim comp; subst a; trivial.
    apply Hrec; auto.
  Qed.


  Lemma stable_equality :
    forall (ss : vector Sigma n) (p q : nat) (t  : Sigma) (Cp : p < n) (Cq : q < n),
      (q,t) INm (Step' p Cp (ss[p|Cp])) ->
      stable Sigma n succs step r step_succs_same_length ss p Cp->
      sup t (ss[q|Cq]) = ss[q|Cq].
  Proof.
    intros ss p q t Cp Cq q_t_Step'_p stable_p.
    unfold stable in stable_p.
    Semi r_is_semilattice.
    apply ord_antisym.
    apply lub3; try assumption.
    split.
    rewrite (element_at_irrel Sigma n ss q Cq (m_list_get_witness (Step' p Cp (ss[p|Cp])) (q, t) q_t_Step'_p)).
    apply stable_p.
    apply ord_refl.
    apply lub2; try assumption.
  Qed.


  Lemma r_propa_ss_ts :
    forall (a : nat) (ss ts : vector Sigma n) (q : nat) (w : nb_list n) (Ca : a < n) (Cq : q < n),
      monotonestep -> ra n ts ss \/ ts = ss -> stables Sigma n succs step r step_succs_same_length ts ->
      r ((fst (Propa ss w (Step' a Ca (ss[a|Ca]))))[q|Cq]) (ts[q|Cq]).
  Proof.
    intros a ss ts q wa  Ca Cq monostep H Hstable.
    Semi r_is_semilattice.
    elim (m_list_belong_fst_dec n Sigma (Step' a Ca (ts[a|Ca])) q); intro case.
  (* q in (step' a ts[a]) *)
    apply ord_trans with (y:=(sup_iter (ss[q|Cq]) (Step' a Ca (ss[a|Ca])) q)).
    apply propa_lub; try assumption.
    unfold step' in *.
    apply in_fst_in_fst_combine.
    apply (in_fst_combine_in_fst n Sigma (succs a Ca) (step a Ca (ts[a|Ca])) (step_succs_same_length a Ca (ts[a|Ca]))).
    assumption.
  (* m_r *)
    apply ord_trans with (sup_iter (ts[q|Cq]) (Step' a Ca (ss[a|Ca])) q).
    apply (sup_iter_r_arg Sigma n r sup); auto.
    apply (vector_pointwise_to_element Sigma r n ss ts q Cq).
    apply SI_vector_pointwise_or_eq_imp_vector_pointwise; try auto.
    apply ord_trans with (sup_iter (ts[q|Cq]) (Step' a Ca (ts[a|Ca])) q).
    apply (sup_iter_m_r Sigma n r sup r_is_semilattice); auto.
    unfold step'; apply list_pointwise_to_m_list_pointwise.
    apply monostep; auto.
    apply (vector_pointwise_to_element Sigma r n ss ts a Ca).
    apply SI_vector_pointwise_or_eq_imp_vector_pointwise; try auto.
    rewrite (sup_iter_stable Sigma n r sup); auto.
    intros t Hbelong.
    rewrite (lub_refl Sigma r sup (ts[q|Cq]) t); auto.
    apply (stable_equality ts a q t Ca Cq); auto.
  (* q not in (step' a ts[a]) *)
    rewrite no_change_at_p_not_in_succs; auto.
    apply (vector_pointwise_to_element Sigma r n ss ts q Cq).
    apply SI_vector_pointwise_or_eq_imp_vector_pointwise; try auto.
    unfold step' in *.
    cut (~ q INnb (succs a Ca)).
    intros h h'.
    apply h; apply (in_fst_combine_in_fst n Sigma (succs a Ca) (step a Ca (ss[a|Ca])) (step_succs_same_length a Ca (ss[a|Ca]))).
    assumption.
    intro h; apply case.
    apply in_fst_in_fst_combine.
    assumption.
  Qed.


End propa_property2.
