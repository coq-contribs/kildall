  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : well_founded.v				         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel		         *)
  (*   Content : well-foundedness of the pointwise order	 *)
  (*   on vectors					         *)
  (***************************************************************)


Require Export vector_results.
Require Export Wellfounded.
Require Export Relation_Definitions.

Section wf_list.

  Variable A : Set.
  Variable ra : relation A.

  Hypothesis R_wf : (well_founded  ra).

  Inductive lexicographic : forall n:nat, (vector A n)->(vector A n)->Prop:=
    | lexicographic_intro1:forall (a a': A) (n:nat) (l l':(vector A n)), (ra a a')->
      (lexicographic (S n) (vector_cons   a l) (vector_cons   a' l'))
    | lexicographic_intro2:forall (a:A) (n:nat) (l l': (vector  A n)), (lexicographic n l l')-> 
      (lexicographic (S n) (vector_cons  a l) (vector_cons  a l')).

  Lemma lexicographic_wf_step: 
    forall (n:nat),(forall l:vector A n,Acc (lexicographic n) l)->
      (forall (a:A) (l:(vector A  n)), Acc (lexicographic (S n)) (vector_cons  a l) ).
  Proof.
    intros n Hn a.
    elim (R_wf a);clear a.
    intros a H Hind1; clear H.
    intro l.
    elim (Hn l); clear l.
    intros l H Hind2;clear H.
    constructor.
    intros l';Split l'.
    intro inf; inversion inf.
    apply Hind1;auto.
    rewrite H3.
    apply Hind2.
    replace l with l'0.
    replace (tail l') with l0.
    assumption.
    apply (inj_pair2 nat (fun x:nat=>vector A x)); assumption.
    apply (inj_pair2 nat (fun x:nat=>vector A x)); assumption.
  Qed.

  Lemma wf_lexicographic0 : well_founded (lexicographic 0).
  Proof.
    unfold well_founded. 
    intro l.
    elim (empty l).
    constructor.
    intro y; elim (empty y).
    intro h.
    inversion h.
  Qed.

  Lemma wf_lexicographic_step : forall (n:nat), well_founded (lexicographic n)->well_founded (lexicographic (S n)).
  Proof.
    unfold well_founded.
    intros.
    Split a.
    apply lexicographic_wf_step.
    simpl.
    apply H.
  Qed.

  Theorem wf_lexicographic : forall (n:nat), well_founded (lexicographic n).
  Proof.
    induction n.
    apply wf_lexicographic0.
    exact (wf_lexicographic_step n IHn).
  Qed.

End wf_list.  

Section asc_list.  
  
  Variable A : Set.  
  Variable ra : relation A.  

  Hypothesis eq_A_dec : forall a a0 : A, a0 = a \/ a0 <> a.  
  
  Lemma vector_pointwise_to_lexicographic_inv :
    forall (n : nat) (l l' : vector A n),
      strict (inv (vector_pointwise A ra n)) l l' ->
      lexicographic A (strict (inv ra)) n l l'.
  Proof.  
    intros n l l'.
    induction l.
    elim (empty l').
    intro c; elim c; intros d e; elim e; trivial.
    Split l'.
    intro H.
    unfold inv in *; unfold strict in *.
    elim H; clear H; intros h h'.
    case (eq_A_dec a (head l')); intro comp.
    rewrite comp.
    apply lexicographic_intro2.
    simpl.
    apply IHl.
    rewrite comp in h.
    split.
    inversion h.
    replace (tail l') with v. 
    replace l with v'. 
    assumption.
    apply (inj_pair2 nat (fun x : nat => vector A x)); assumption.
    apply (inj_pair2 nat (fun x : nat => vector A x)); assumption.
    intro ltl'.
    apply h'.
    rewrite comp; rewrite ltl'; trivial.
    apply lexicographic_intro1.
    split.
    inversion h.
    assumption.
    intro neq.
    elim comp.
    symmetry.
    assumption.
  Qed.
  
  Lemma asc_vector_pointwise : forall (n:nat),
    ascending_chain ra->ascending_chain (vector_pointwise A ra n).  
  Proof.  
    unfold ascending_chain.  
    intros n H.
    apply wf_incl with (lexicographic A (strict (inv ra)) n).
    unfold inclusion.
    exact (vector_pointwise_to_lexicographic_inv n).
    apply wf_lexicographic; assumption.
  Qed.

End asc_list.  

