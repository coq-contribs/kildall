  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : iteraterme.v				         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : results needed to specify function iterate      *)
  (***************************************************************)

Section iteraterme.

  Require Export propa_property.
  Require Export well_founded.
  Require Export product_results.

  Variable Sigma : Set. (* state set *)
  Variable n : nat. (* bytecode size *)
  Variable succs : forall p:nat, p<n -> nb_list n. (* successor function *)
  Variable step : forall p:nat, p<n -> Sigma -> list Sigma. (* flow function *)
  Variable r : relation Sigma. (* order on state set *)
  Variable sup : binop Sigma. (* sup on state set *)

  Hypothesis eq_Sigma_dec : forall x y : Sigma, {x = y} + {x <> y}.
  Hypothesis step_succs_same_length : forall (q:nat) (C:q<n) (s : Sigma), 
    nb_length (succs q C) = length (step q C s).
  Hypothesis r_is_semilattice : semilattice Sigma r sup.
  Hypothesis wfr : ascending_chain r.	 

  Notation Propa := (propagate sup eq_Sigma_dec).
  Notation ra := (SI_vector_pointwise Sigma r).
  Notation Step' := (step' Sigma n succs step step_succs_same_length).

  (* iterates f on bot n times :*)
  Fixpoint compose (A : Set) (f : A -> A) (bot : A) (n : nat) {struct n} : A :=
    match n with
      | O => bot
      | S p => f (compose A f bot p)
    end.

  (* the function iterate is a fixpoint of : *)
  Definition fl (f0 : (vector Sigma n) * (nb_list n)-> vector Sigma n)
    (ssw : (vector Sigma n) * (nb_list n)) :=
    match ssw with
      | (ss, w) =>
        match w with
          | pred_nil => ss
          | pred_cons p C w1 => f0 (Propa n ss w1 (Step' p C (ss[p|C])))
        end
    end.

  Theorem wf_lt_dep_length : forall n:nat, well_founded (lt_nb_length (n:=n)).
  Proof.
    unfold lt_nb_length.
    unfold lt_pred_length.
    intro n'.
    apply (well_founded_ltof (nb_list n') (nb_length (n:=n'))).
  Qed.

  (* step 1 in defining function iterate : *)
  Lemma acc_ssw : forall (ssw : (vector Sigma n) * (nb_list n)),
    Acc (nondep_lexprod (vector Sigma n) (nb_list n) (ra n) (rb n)) ssw.
  Proof.     
    intro ssw.
    apply wf_nondep_lexprod.
    cut (ascending_chain (Vector_pointwise Sigma r n)).
    unfold ascending_chain; trivial.
    unfold Vector_pointwise; apply asc_vector_pointwise; trivial.
    intros a a'; elim (eq_Sigma_dec a' a); intro case_a_a'; [left | right]; trivial.
    unfold rb; apply (wf_lt_dep_length n).
  Qed.

  (* step 3 in defining function iterate : *)
  Theorem iteraterme :
    forall (ssw : (vector Sigma n) * (nb_list n)),
      {v : (vector Sigma n) |
        exists p : nat,
          (forall k : nat,
            p < k ->
            forall bot : (vector Sigma n) * (nb_list n) -> (vector Sigma n),
              compose ((vector Sigma n) * (nb_list n) -> (vector Sigma n)) 
              fl bot k (ssw) = v)}.
  Proof.     
    intro ssw.
    generalize (acc_ssw ssw).
    intro Hacc.
    elim Hacc; clear Hacc ssw.
    intros ssw Hrec.
    destruct ssw as [ss w].
    CaseEq w.
    (* w = nil *)
    intros Heq1 Heq2.
    exists ss.
    exists 0.
    intros k Ck; destruct k; [inversion Ck | simpl; trivial].
    (* w = q::w1 *)
    intros q C w1 Heq1 Hrec2.
    elim (Hrec2 (Propa n ss w1 (Step' q C (ss[q|C])))).
    intros ss1 Hex.
    exists ss1.
    elim Hex.
    intros p H.
    exists (S p).
    intros k Hlt bot.
    destruct k; [inversion Hlt | simpl].
    cut (p<k); [clear Hlt | generalize Hlt; auto with arith].
    case k.
    (* k = 0 *)
    intros Hl.
    inversion Hl.

    (* k(') = S k *)
    clear k; intros k Hlt.
    apply H.
    assumption.
    apply (propa_nondep_lexprod Sigma n succs step r sup step_succs_same_length 
      eq_Sigma_dec r_is_semilattice ss q w1 C).
  Qed.


End iteraterme.

