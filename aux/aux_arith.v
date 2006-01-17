  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : aux_arith.v				         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content :	elementary arithmetic results	         *)
  (***************************************************************)

Section aux_arith.

  Require Export Arith.

  Remark lt_S_neq_lt : forall (p q:nat), p<S q -> p<>q->p<q.
    Proof.
    intros p q.
    unfold lt.
    intros H1 H2.
    elim (le_lt_eq_dec (S p) (S q) H1); intro case.
    auto with arith.
    elim H2.
    auto with arith.
  Qed.

  Remark lt_not_ge : forall (k p : nat), p < k -> k <= p -> False.
    Proof.
    induction k; intros p H1 H2. 
    inversion H1.
    destruct p.
    inversion H2.
    apply (IHk p); auto with arith.
  Qed.


  Remark not_pred_lt_S_lt : forall (p n : nat), 0 < n -> p <> pred n ->  p < n -> S p < n.
    Proof.
    intros p n Cn neq Cp.
    destruct n; inversion Cp.
    subst p.
    elim neq; simpl in |- *; trivial.
    auto with arith.
  Qed.

  Remark not_S_le : forall (n : nat), S n <= n -> False.
    Proof.
    induction n. 
    intro F; inversion F.
    intro H; apply IHn.
    generalize H; auto with arith.
  Qed.


  Lemma not_lt_S : forall (n : nat), ~ S n < n.
    Proof.
    induction n; intro C.
    inversion C.
    apply IHn; generalize C; apply lt_S_n.
  Qed.


  Lemma neq_n_Sn : forall (n : nat), ~ S n = n.
    Proof.
    induction n; intro F.
    inversion F.
    apply IHn; generalize F; auto with arith.
  Qed.


End aux_arith.
