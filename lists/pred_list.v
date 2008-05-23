  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : pred_list.v			  	         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel	                 *)
  (*   Content : list of elements satisfying a certain predicate *)
  (***************************************************************)

Section pred_list.
  

  Require Export Peano_dec.
  Require Export relations.
  Require Export List.

  (* base set *)
  Variable A : Set.
  (* predicate : *)
  Variable P : A->Prop.
  Hypothesis eq_A_dec : forall (a a' : A), {a = a'} + {a <> a'}.

  Inductive pred_list : Set :=
    | pred_nil : pred_list
    | pred_cons : forall (a:A), (P a)->pred_list->pred_list.

  (* adding an element to a pred_list : *)
  Fixpoint pred_list_add_element (l : pred_list) (a:A) {struct l} : 
    (P a)->(pred_list):=
    match l return (P a)->(pred_list) with
      | (pred_nil) => fun C : (P a) => (pred_cons a C pred_nil)
      | (pred_cons h C t) => 
        match (eq_A_dec a h) with
          | (left _) => fun Ca : P a=>pred_cons h C t
          | (right _) => fun Ca : P a=>	
      	    (pred_cons h C (pred_list_add_element t a Ca))
        end
    end.

  (* returns True if element a belongs to the pred_list : *)
  Fixpoint pred_list_belong (l : pred_list) (a : A) {struct l} : Prop :=
    match l with
      | (pred_nil) => False
      | (pred_cons h C t) => a=h \/ pred_list_belong t a
    end.

  Notation "a 'INp' l" := (pred_list_belong l a) (at level 50).

  (* removes an element form pred_the list; leaves list unchanged if element
     does not belong to the list *)
  Fixpoint pred_list_remove (l : pred_list) (a : A) {struct l} : pred_list :=
    match l with 
      | pred_nil => pred_nil 
      | pred_cons h C t => 
        match (eq_A_dec a h) with 
      	  | left _ => t
	  | right _ => pred_cons h C (pred_list_remove t a)
	end
    end.
  
  Notation "l '\' a" := (pred_list_remove l a) (at level 50).

  (* computes length of the pred_list *)
  Fixpoint pred_length (l : pred_list) {struct l} : nat :=
    match l with 
      | pred_nil => 0
      | pred_cons _ _ t => S (pred_length t)
    end.

  Definition lt_pred_length (l l' : pred_list) : Prop :=
    pred_length l < pred_length l'.

  (* pointwise order on pred_lists : *)
  Inductive pred_pointwise (r:relation A): pred_list -> pred_list -> Prop :=
    | pred_pointwise_nil : pred_pointwise r pred_nil pred_nil
    | pred_pointwise_cons : forall (a a' : A) (C : P a) (C' : P a') (l l' : pred_list),
      (r a a')->pred_pointwise r l l'->pred_pointwise r (pred_cons a C l) (pred_cons a' C' l').

  (* projection from pred_list to regular lists : *)
  Fixpoint pred_list_to_list (l : pred_list) : list A :=
    match l with 
      | pred_nil => nil
      | pred_cons h C t => h :: (pred_list_to_list t)
    end.

  Fact list_to_pred_list_convert_hyp : forall (h : A) (t : list A)
    (H : forall (a:A), In a (h::t) -> P a),
    forall (a : A), In a t -> P a.
  Proof.
    intros; apply H; trivial; try right; trivial.
  Qed.

  (* converts a list to a pred_list, given a proof that each element of
     the list satisfies predicate P *)
  Fixpoint list_to_pred_list (l : list A) : (forall (a:A), In a l -> P a) -> pred_list :=
    match l return ((forall (a:A), In a l -> P a) -> pred_list) with 
      | nil => fun (H : forall (a:A), In a nil -> P a) => pred_nil
      | h :: t => fun (H : forall (a:A), In a (h::t) -> P a) =>
        pred_cons h (H h (in_eq h t)) (list_to_pred_list t (list_to_pred_list_convert_hyp h t H)) 
    end.

  (* facts about convertions : *)
  Lemma list_to_pred_list_to_list : forall (l : list A) (H : forall (a : A), In a l -> P a), 
    pred_list_to_list (list_to_pred_list l H) = l.
  Proof.
    induction l; simpl.
    trivial.
    intro H.
    rewrite (IHl (list_to_pred_list_convert_hyp a l H)).
    trivial.
  Qed.

  Lemma list_to_pred_list_length : forall (l : list A) (H : forall (a : A), In a l -> P a), 
    pred_length (list_to_pred_list l H) = length l.
  Proof.
    induction l; simpl.
    trivial.
    intro H.
    apply eq_S.
    apply IHl.
  Qed.


  Lemma pred_list_to_list_length : forall (l : pred_list), 
    length (pred_list_to_list l) = pred_length l.
  Proof.
    induction l; simpl.
    trivial.
    apply eq_S; apply IHl.
  Qed.

  Lemma pred_list_to_list_belong : forall (l : pred_list) (a : A), 
    a INp l -> In a (pred_list_to_list l).
  Proof.
    induction l as [ | h C t IHl] ; intro a; simpl.
    trivial.
    intro H; elim H; clear H; intro H.
    left; symmetry; assumption.
    right; apply IHl; assumption.
  Qed.

  Lemma belong_pred_list_to_list : forall (l : pred_list) (a : A), 
    In a (pred_list_to_list l) -> a INp l .
  Proof.
    induction l as [ | h C t IHl]; intro a; simpl.
    trivial.
    intro H; elim H; clear H; intro H.
    left; symmetry; assumption.
    right; apply IHl; assumption.
  Qed.

  Lemma list_to_pred_list_belong : forall (l : list A) 
    (H : forall (a : A), In a l -> P a) (a : A), 
    In a l -> a INp (list_to_pred_list l H).
  Proof.
    induction l as [ | h t IHl]; intros H a; simpl.
    trivial.
    intro H'; elim H'; clear H'; intro H'.
    left; symmetry; assumption.
    right; apply IHl; assumption.
  Qed.

  Lemma belong_list_to_pred_list : forall (l : list A) 
    (H : forall (a : A), In a l -> P a) (a : A), 
    a INp (list_to_pred_list l H) -> In a l.
  Proof.
    induction l as [ | h t IHl]; intros H a; simpl.
    trivial.
    intro H'; elim H'; clear H'; intro H'.
    left; symmetry; assumption.
    right; apply (IHl (list_to_pred_list_convert_hyp h t H)); assumption.
  Qed.

  (* belong results : *)
  Lemma pred_list_belong_remove : forall (l : pred_list) (a a' : A),
    a INp l -> a<>a' -> a INp (l \ a').
  Proof.
    induction l as [ | h C t IHl]; simpl; intros a a' a_in_l a_neq_a'.
    trivial.
    elim (eq_A_dec a' h); intro case_a'_h.
    elim a_in_l; clear a_in_l; intro a_in_l; trivial.
    elim a_neq_a'; subst a; symmetry; assumption.
    elim a_in_l; clear a_in_l; intro a_in_l; trivial.
    left; assumption.
    right; apply IHl; assumption.
  Qed.

  Lemma pred_list_belong_dec : forall (l : pred_list) (a : A), 
    {a INp l} + {~ (a INp l)}.
  Proof.
    intros l a.
    induction l as [ | h C t IHl].
    simpl; right.
    unfold not; trivial.
    simpl.
    elim (eq_A_dec a h); intro comp.
    left; left; assumption.
    case IHl; intro comp'.
    left; right; assumption.
    right.
    intro H.
    apply comp'.
    elim H.
    intro H'; elim (comp H').
    trivial.
  Qed.

  Lemma pred_list_get_witness : forall (l : pred_list) (a : A), 
    a INp l -> P a.
  Proof.
    induction l as [ | h C t IHl].
    simpl.
    intros a H; inversion H.
    intros a H.
    simpl in H.
    elim H.
    intro H'.
    rewrite H'; assumption.
    exact (IHl a).
  Qed.

  Lemma pred_list_belong_add : forall (l : pred_list) (a a' : A) (C : P a), 
    a' INp l-> a' INp (pred_list_add_element l a C).
  Proof.
    induction l as [ | h C t IHl]; simpl; intros a a' Ca H.
    inversion H.
    elim (eq_A_dec a h); intro comp_a_h.
    simpl; assumption.
    simpl; elim H; clear H; intro H.
    left; assumption.
    right.
    apply IHl.
    assumption.
  Qed.

  Lemma pred_list_belong_rem : forall (l : pred_list) (a a' : A) (C : P a), 
    a' INp (pred_list_add_element l a C) -> a<>a' -> a' INp l.
  Proof.
    induction l as [ | h C t IHl]; simpl; intros a a' Ca. 
    intros a'_in_la a_neq_a'; elim a'_in_la; auto.
    elim (eq_A_dec a h); intro comp_a_h.
    intros a'_in_la a_neq_a'; elim a'_in_la; intro H; [left | right]; trivial.
    intros a'_in_la a_neq_a'; elim a'_in_la.    
    left; trivial.
    right; apply IHl with a Ca; trivial.
  Qed.

  (* add results : *)
  Lemma pred_list_add_already_there : forall (l : pred_list) (a : A) (C C' : P a), 
    pred_list_add_element (pred_list_add_element l a C) a C'=pred_list_add_element l a C.
  Proof.
    induction l as [ | h C t IHl]; simpl; intros a Ca Ca'.
    elim (eq_A_dec a a); intro comp; [simpl | elim comp]; trivial.
    elim (eq_A_dec a h); intro comp_a_h.
    subst h; simpl; elim (eq_A_dec a a); intro comp; [simpl | elim comp]; trivial.
    simpl; elim (eq_A_dec h a); intro comp_h_a. 
    subst; elim comp_a_h; trivial.
    elim (eq_A_dec a h); intro comp. 
    contradiction.
    rewrite (IHl a Ca Ca'); trivial.
  Qed.


  Lemma pred_list_belong_added : forall (l : pred_list) (a : A) (C : P a),
    a INp (pred_list_add_element l a C).
  Proof.
    induction l as [ | h C t IHl]; simpl.
    left; trivial.
    intros a Ca; elim (eq_A_dec a h); intro comp; simpl.
    left; trivial.
    right; apply IHl.
  Qed.

  Lemma pred_list_add_already_there_added : 
    forall (l : pred_list) (a' a'' : A) (C' : P a') (C'' : P a''),
      pred_list_add_element (pred_list_add_element (pred_list_add_element l a'' C'') a' C') a'' C'' = 
      pred_list_add_element (pred_list_add_element l a'' C'') a' C'.
  Proof.
    induction l; intros a' a'' C' C''; simpl. 
    elim (eq_A_dec a' a''); intro comp.
    simpl.
    elim (eq_A_dec a'' a''); intro comp'.
    trivial.
    elim comp'; trivial.
    simpl.
    elim (eq_A_dec a'' a''); intro comp'.
    trivial.
    elim comp'; trivial.
    elim (eq_A_dec a'' a); intro comp.
    simpl.
    elim (eq_A_dec a' a); intro comp'; simpl.
    elim (eq_A_dec a'' a); intro comp''; [trivial | contradiction].
    elim (eq_A_dec a'' a); intro comp''; [trivial | contradiction].
    simpl.
    elim (eq_A_dec a' a); intro comp'; simpl.
    elim (eq_A_dec a'' a); intro comp''.
    trivial.
    rewrite (pred_list_add_already_there l a'' C'' C''); trivial.
    elim (eq_A_dec a'' a); intro comp''; [contradiction | simpl].
    rewrite (IHl a' a'' C' C''); trivial.
  Qed.

  (* if a list results from a convertion from a pred_list, then each of
     its elements satisfies predicate P *) 
  Lemma list_from_pred_convertion : forall (l : list A) (dl : pred_list), 
    l = pred_list_to_list dl -> (forall (a : A), In a l -> P a).
  Proof.
    intros l dl; generalize l; clear l; induction dl; simpl; intros l Heq e Hin.
    subst l; inversion Hin. 
    subst l; elim Hin; clear Hin; intro Hin.
    subst e; assumption.
    apply (IHdl (pred_list_to_list dl)); trivial.
  Qed.

End pred_list.


Implicit Arguments pred_nil [A].
Implicit Arguments pred_cons [A].
Implicit Arguments pred_list_add_element [A P].
Implicit Arguments pred_list_belong [A P].
Implicit Arguments pred_list_to_list [A P].
Implicit Arguments list_to_pred_list [A P].
Implicit Arguments pred_list_belong_dec [A P].
Implicit Arguments pred_list_get_witness [A P].
Implicit Arguments pred_list_belong_add [A P].
Implicit Arguments pred_list_belong_rem [A P].
Implicit Arguments pred_list_add_already_there [A P].
Implicit Arguments pred_list_add_already_there_added [A P].
Implicit Arguments pred_list_belong_added [A P].
Implicit Arguments pred_list_remove [A P].
Implicit Arguments pred_length [A P].
Implicit Arguments lt_pred_length [A P].

  Notation "a 'INp' l" := (pred_list_belong l a) (at level 50).

  Notation "l '\' a" := (pred_list_remove l a) (at level 50).

  (* equivalence on pred_lists : two pred_lists are equivalent iff their
     projections on regular lists are the same *)  
Section pred_list_equivalence.

  Variable A : Set.

  Definition pred_list_equiv (P Q : A->Prop) (l : pred_list A P) (l' : pred_list A Q) : Prop :=
    pred_list_to_list l = pred_list_to_list l'.

  Notation "l '=p=' m" := (pred_list_equiv _ _ l m) (at level 50).

  (* it is an equivalence relation : *)
  Lemma pred_list_equiv_refl : forall (P : A-> Prop) (l : pred_list A P), l =p= l. 
  Proof.
    unfold pred_list_equiv; trivial.
  Qed.


  Lemma pred_list_equiv_trans : forall (P Q R : A->Prop) 
    (lp : pred_list A P) (lq : pred_list A Q) (lr : pred_list A R), 
    lp =p= lq -> lq =p= lr -> lp =p= lr.
  Proof.
    unfold pred_list_equiv; intros P Q R lp lq lr Hpq Hqr.
    rewrite Hpq; assumption.
  Qed.


  Lemma pred_list_equiv_sym : forall (P Q : A->Prop) (lp : pred_list A P) (lq : pred_list A Q), 
    lp =p= lq -> lq =p= lp.
  Proof.
    unfold pred_list_equiv; intros; symmetry; assumption.
  Qed.

  (* results on equivalence : *)
  Lemma pred_list_equiv_split : forall (P Q : A->Prop) (a a' : A) 
    (lp : pred_list A P) (lq : pred_list A Q) (C : P a) (C' : Q a'), 
    (pred_cons P a C lp) =p= (pred_cons Q a' C' lq) -> a = a' /\ lp =p= lq.
  Proof.
    intros P Q a a' lp lq C C'.
    unfold pred_list_equiv.
    simpl; intro H.
    inversion H.
    split; trivial.
  Qed.

  Lemma pred_list_split_equiv : forall (P Q : A->Prop) (a a' : A) 
    (lp : pred_list A P) (lq : pred_list A Q) (C : P a) (C' : Q a'), 
    a = a' /\ (lp =p= lq) -> (pred_cons P a C lp) =p= (pred_cons Q a' C' lq).
  Proof.
    intros P Q a a' lp lq C C'.
    unfold pred_list_equiv.
    simpl; intro H.
    inversion_clear H as [H1 H2].
    rewrite H1; rewrite H2; trivial.
  Qed.


  Lemma pred_list_equiv_belong : forall (P Q : A->Prop) (a : A) 
    (lp : pred_list A P) (lq : pred_list A Q), 
    lp =p= lq -> a INp lp -> a INp lq.
  Proof.
    intros P Q a l l' Heq Hinl.
    cut (In a (pred_list_to_list l')).
    apply belong_pred_list_to_list.
    unfold pred_list_equiv in Heq.
    rewrite <- Heq.
    apply pred_list_to_list_belong.
    assumption.
  Qed.


End pred_list_equivalence.

Implicit Arguments pred_list_equiv [A P Q].
Implicit Arguments pred_list_equiv_refl [A P].
Implicit Arguments pred_list_equiv_trans [A P Q R].
Implicit Arguments pred_list_equiv_sym [A P Q].
Implicit Arguments pred_list_equiv_split [A P Q].
Implicit Arguments pred_list_split_equiv [A P Q].
Implicit Arguments pred_list_equiv_belong [A P Q].

  Notation "l '=p=' m" := (pred_list_equiv l m) (at level 50).

  (* pred_list convertion *)
Section pred_list_convertion.

  Variable A : Set.
  Variables P Q : A->Prop.

  Hypothesis eq_A_dec : forall (a a' : A), {a=a'} + {a<>a'}.

  Lemma hyp_belong_convert : forall (l : pred_list A P) 
    (H : forall (a : A), a INp l -> Q a) (a : A), 
    In a (pred_list_to_list l) -> Q a.
  Proof.
    intros l H a Hin.
    apply (H a).
    induction l as [ | h C t IHl]; simpl; trivial.
    elim Hin; [left | right].
    symmetry; assumption.
    apply IHl.
    intros a' a'_in_t; apply (H a').
    right; assumption.
    assumption.
  Qed.

  Definition pred_list_convert (l : pred_list A P) 
    (H : forall (a : A), a INp l -> Q a) : pred_list A Q :=
    list_to_pred_list (pred_list_to_list l) (hyp_belong_convert l H).

  Lemma pred_list_convert_equiv : forall (l : pred_list A P) 
    (H : forall (a : A), a INp l -> Q a),
    l =p= (pred_list_convert l H).
  Proof.
    unfold pred_list_equiv; unfold pred_list_convert.
    intros l H.
    rewrite (list_to_pred_list_to_list A Q (pred_list_to_list l) (hyp_belong_convert l H)); trivial.
  Qed.


  Lemma pred_list_convert_length : forall (l : pred_list A P) 
    (H : forall (a : A), a INp l -> Q a),
    pred_length l = pred_length (pred_list_convert l H).
  Proof.
    unfold pred_list_equiv; unfold pred_list_convert.
    intros l H.
    transitivity (length (pred_list_to_list l)).
    symmetry; apply pred_list_to_list_length.
    symmetry; apply list_to_pred_list_length.
  Qed.

  Lemma pred_list_belong_convert : forall (a :A) (l : pred_list A P)
    (H : forall (a : A), a INp l -> Q a),
    a INp l -> a INp (pred_list_convert l H).
  Proof.
    unfold pred_list_convert.
    intros a l H Hbelong.
    cut (In a (pred_list_to_list l)).
    apply list_to_pred_list_belong.
    apply pred_list_to_list_belong.
    assumption.
  Qed.

  Lemma pred_list_convert_belong : forall (a : A) (l : pred_list A P) 
    (H : forall (a : A), a INp l -> Q a),
    a INp (pred_list_convert l H) -> a INp l.
  Proof.
    unfold pred_list_convert.
    intros a l H Hbelong.
    cut (In a (pred_list_to_list l)).
    apply belong_pred_list_to_list.
    apply (belong_list_to_pred_list A Q (pred_list_to_list l) (hyp_belong_convert l H)).
    assumption.
  Qed.

End pred_list_convertion.


Implicit Arguments pred_list_convert [A P Q].
Implicit Arguments pred_list_convert_equiv [A P Q].
Implicit Arguments pred_list_convert_length [A P Q].
Implicit Arguments pred_list_belong_convert [A P Q].
Implicit Arguments pred_list_convert_belong [A P Q].


