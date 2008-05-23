  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : kildall_bv.v				         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : Proof kildall's algorithm is a bytecode verifier*)
  (***************************************************************)

Section kildall_bytecode_verifier.


  Require Export kildall_dfa.

  Variable Sigma : Set. (* state set *)
  Variable n : nat. (* bytecode size *)
  Variable succs : forall p:nat, p<n -> nb_list n. (* successor function *)
  Variable step : forall p:nat, p<n->Sigma->list Sigma. (* flow function *)
  Variable wi : vector Sigma n -> forall p : nat, p<n -> Prop. (* correct state for instruction predicate *)
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
  Notation IS_bytecode_verifier := (Is_bytecode_verifier Sigma n wi r T).
  Notation Wi_and_stable_agree := (wi_and_stable_agree Sigma n succs step 
    wi r T step_succs_same_length).
  

  Theorem Kildall_is_bytecode_verifier :
    MonotoneStep ->
    is_top_element Sigma r T ->
    Wi_and_stable_agree -> IS_bytecode_verifier KIldall.
  Proof.
    intros monostep istop wieqstable.
    inversion r_is_semilattice.
    apply (dfa_is_bv Sigma n succs step wi r T step_succs_same_length H); auto.
    apply monotone_step_imp_kildall_dfa; auto.
  Qed.

  
  (* proposition (1) is immediate from kildall being a dfa : *) 
  Lemma top_free_to_wi : MonotoneStep -> Wi_and_stable_agree ->
    forall (ss : vector Sigma n), ~ (T INv (KIldall ss)) -> 
      forall (p : nat) (C : p < n), wi (KIldall ss) p C.
  Proof.
    intros Hmono H ss no_top p C.
    elim (H (KIldall ss) p C no_top); clear H; intros H1 H2.
    apply H2.
    (* show kildall ss is stable at p : *)
    cut (IS_data_flow_analyser KIldall).
    unfold Is_data_flow_analyser.
    intro H; elim H with ss.
    clear H; intros H dd; apply (H p C).
    (* show kildall is a dfa : *)
    apply monotone_step_imp_kildall_dfa; auto.
  Qed.

  (* proposition (2) is a corrolary of kildall being a bytecode verifier, 
     provided not function state containing top element satisfies wi :*)
  Lemma top_free_dominates_args_implies_top_free_kildall :  MonotoneStep -> is_top_element Sigma r T ->
    (forall (ss : vector Sigma n) (p : nat) (C : p<n), wi ss p C -> ~ (T INv ss)) ->
    Wi_and_stable_agree -> forall (ss : vector Sigma n), 
    ex (fun (ts : vector Sigma n) => Vector_pointwise Sigma r n ss ts /\ (forall (p : nat) (C :p < n), wi ts p C)) ->
    ~ (T INv (KIldall ss)).
  Proof.
    intros Hmono Htop H' H ss Hex.
    elim (Kildall_is_bytecode_verifier Hmono Htop H ss); intros H1 H2.
    apply H2.
    unfold welltyping.
    elim Hex; clear Hex; intros ts Hts.
    elim Hts; clear Hts; intros Hts1 Hts2.
    exists ts; split; trivial.
    intros p C; split; trivial.
    apply does_not_belong_is_not_element.
    apply H' with p C; trivial.
  Qed.

End kildall_bytecode_verifier.
