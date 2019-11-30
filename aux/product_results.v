  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : product_results.v				         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : well-foundedness of the lexicographic product   *)
  (*             of two well-founded relations		         *)
  (***************************************************************)

Section product_results.

  Require Export relations.
  Require Export Wellfounded.

  Variables (Alpha : Set) (Beta : Set).
  Variables (ra : relation Alpha) (rb : relation Beta).

  (* coq's (dependend) lexicographic product *)
  Let R := lexprod Alpha (fun a : Alpha => Beta) ra (fun a : Alpha => rb).

  (* lexicographic product *)
  Let r := nondep_lexprod Alpha Beta ra rb.

  Remark wf_dep_nodep_lexprod :
    well_founded ra -> well_founded rb -> well_founded R.
  Proof.
    intros.
    unfold R in |- *.
    apply wf_lexprod; trivial.

  Qed.

  Definition nodep_prod_of_dep (c : sigT (fun a : Alpha => Beta)) :
    Alpha * Beta := let (x, y) := c in (x, y).

  (* comparison of the two lexicographic products : *)
  Lemma strongest_r_R :
    forall (a a0 : Alpha) (b b0 : Beta),
      r (a0, b0) (a, b) ->
      R (existT (fun _ : Alpha => Beta) a0 b0)
      (existT (fun _ : Alpha => Beta) a b).
  Proof.
    intros a1 a2 b1 b2.
    intro H.
    inversion_clear H.
    constructor 1; assumption.
    constructor 2; assumption.
  Qed.

  (* from accessibility by R to accessibility by r : *)
  Remark R_to_r :
    forall x : sigT (fun a : Alpha => Beta),
      Acc R x -> Acc r (nodep_prod_of_dep x).
  Proof.
    simple induction 1.
    clear H x; intro x.
    case x.
    clear x; intros a b H1 H2.
    constructor.
    intro y; case y; clear y.
    intros a0 b0 Infr.
    replace (a0, b0) with
      (nodep_prod_of_dep (existT (fun a : Alpha => Beta) a0 b0)).
    apply H2.
    apply strongest_r_R; assumption.
    simpl; reflexivity.
  Qed.

  (* R well-founded implies r well-founded : *)
  Lemma wf_R_to_r : well_founded R -> well_founded r.
  Proof.
    unfold well_founded.
    intros H c.
    case c; clear c.
    intros a b.
    replace (a, b) with (nodep_prod_of_dep (existT (fun _ : Alpha => Beta) a b)).
    apply R_to_r.
    apply H.
    simpl; reflexivity.
  Qed.

  (* well-foundedness of r : *)
  Theorem wf_nondep_lexprod :
    well_founded ra -> well_founded rb -> well_founded r.
  Proof.
    intros Ha Hb.
    apply wf_R_to_r.
    apply wf_dep_nodep_lexprod; assumption.
  Qed.

End product_results.
