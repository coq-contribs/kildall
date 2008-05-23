  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : dfa.v					         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : proof that kildall's algorithm is a dfa         *)
  (***************************************************************)

Section Data_flow_analysis.


  Require Export kildall.

  Variable Sigma : Set. (* state set *)
  Variable n : nat. (* bytecode size *)
  Variable succs : forall p:nat, p<n-> nb_list n. (* successor function *)
  Variable step : forall p:nat, p<n->Sigma->list Sigma. (* flow function *)
  Variable wi : vector Sigma n -> forall p:nat, p<n -> Prop. (* correct state for instruction predicate *)
  Variable r : relation Sigma. (* order on state set *)
  Variable T : Sigma. 		(* Top element *)

  Hypothesis step_succs_same_length : forall (q:nat) (C:q<n) (s : Sigma), 
    nb_length (succs q C) = length (step q C s).
  Hypothesis r_is_order : order Sigma r. 
  
  Definition is_top_element : Prop := forall s : Sigma, r s T.
  
  Definition welltyping (ss : vector Sigma n) : Prop :=
    forall (p : nat) (C : p < n), wi ss p C /\ ss[p|C] <> T.
  
  Definition dfa_type := vector Sigma n -> vector Sigma n.
  
  Notation Stables := (stables Sigma n succs step r step_succs_same_length).
  Notation Stable := (stable Sigma n succs step r step_succs_same_length).

  (* definition of dfa : *)
  Definition Is_data_flow_analyser (dfa : dfa_type) : Prop :=
    forall (ss : vector Sigma n),
      Stables (dfa ss) /\
      Vector_pointwise Sigma r n ss (dfa ss) /\
      (forall ts : vector Sigma n,
        Vector_pointwise Sigma r n ss ts /\ Stables ts -> Vector_pointwise Sigma r n (dfa ss) ts).

  (* definition of bv : *)
  Definition Is_bytecode_verifier (bcv : dfa_type) : Prop :=
    forall (ss : vector Sigma n),
      (~ T INv (bcv ss) ->
        exists ts : vector Sigma n,
          Vector_pointwise Sigma r n ss ts /\ welltyping ts) /\
      ((exists ts : vector Sigma n,
        Vector_pointwise Sigma r n ss ts /\ welltyping ts) ->
      ~ T INv (bcv ss)).

  Definition wi_and_stable_agree : Prop :=
    forall ss : vector Sigma n,
      forall (p : nat) (C : p < n),
        ~ T INv ss ->
        (wi ss p C -> Stable ss p C) /\ (Stable ss p C -> wi ss p C).	


  (* list less than a list who does not contain top element does not contain top element *)
  Lemma T_free :
    forall ds ts : vector Sigma n,
      is_top_element ->
      Vector_pointwise Sigma r n ds ts ->
      ~ T INv ts -> ~ T INv ds.
  Proof.
    intros ds ts is_top ds_le_ts tsTfree.
    apply is_not_element_does_not_belong.
    intros p C H.
    apply tsTfree.
    replace T with (ts[p|C]).
    apply element_at_belong.
    inversion r_is_order.
    apply ord_antisym.
    apply is_top.
    rewrite <- H.
    apply (vector_pointwise_to_element Sigma r n ds ts p C ds_le_ts).
  Qed.

  (* if there is a top element and wi and stable agree on top-free function states, 
    then a data flow analyzer  is a bitecode verifier *)
  Theorem dfa_is_bv :
    forall dfa : dfa_type,
      is_top_element ->
      wi_and_stable_agree ->
      Is_data_flow_analyser dfa -> Is_bytecode_verifier dfa.
  Proof.
    intros dfa is_top wi_eq_stable is_dfa.
    unfold Is_bytecode_verifier.
    unfold welltyping.
    unfold Is_data_flow_analyser in is_dfa.
    intro ss.
    split.
    intro H.
    exists (dfa ss).
    generalize (is_dfa ss).
    intro H2. 
    elim H2; intros H3 H4.
    elim H4; intros H5 H6.
    split.
    assumption.
    unfold wi_and_stable_agree in wi_eq_stable.
    intros p C.
    elim (wi_eq_stable (dfa ss) p C).
    intros H9 H10.
    split.
    apply H10.
    unfold stables in H3.
    apply H3.
    apply does_not_belong_is_not_element.
    assumption.
    assumption.
    intro H.
    inversion H.
    apply T_free with x.
    assumption.
    clear H.
    elim (is_dfa ss). 
    intros H1 H2.
    elim H2.
    clear H2.
    intros H2 H3.
    elim H0; clear H0; intros H5 H6.
    apply (H3 x).
    split.
    assumption.
    unfold wi_and_stable_agree in wi_eq_stable.
    generalize (wi_eq_stable x).
    intros H8 p C.
    elim (H8 p C).
    intros H9 H10.
    apply H9.
    elim (H6 p C).
    trivial.
    apply is_not_element_does_not_belong.
    intros p0 C0.
    elim (H6 p0 C0).
    trivial.
    apply is_not_element_does_not_belong.
    intros p0 C0.
    elim H0.
    intros H1 H2.
    elim (H2 p0 C0).
    trivial.
  Qed.

End Data_flow_analysis.
