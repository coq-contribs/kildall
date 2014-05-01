  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : m_list.v					         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : instanciation of pred_list to list of elements  *)
  (*             of nat*Alpha, where first elements of the       *)
  (*   	         couples are less than a certain bound	         *)
  (***************************************************************)

Local Unset Injection On Proofs.

Section m_list.

  Require Export nat_bounded_list.
  (* bound *)
  Variable n : nat.
  (* base set *)
  Variable A : Set.
  Hypothesis eq_A_dec : forall (a a':A), {a=a'} + {a<>a'}.
  Variable r : relation A.

  Lemma eq_prod_dec : forall (a b : nat*A), {a=b}+{a<>b}.
  Proof.
    intros a b; elim a; elim b; clear a b; intros b1 b2 a1 a2.
    elim (eq_nat_dec a1 b1); intro comp.
    subst a1.
    elim (eq_A_dec a2 b2); intro comp'.
    subst a2.
    left; trivial.
    right.
    injection.
    assumption.
    right; injection.
    intro h; assumption.
  Qed.

  Definition Q := fun (e:nat*A)=>lt (fst e) n.
  Definition m_list := pred_list (nat*A) Q.
  Definition m_nil := pred_nil Q.
  Definition m_cons := pred_cons Q.

  Definition m_list_add_element := pred_list_add_element eq_prod_dec (P:=Q).
  Definition m_list_belong := pred_list_belong (P:=Q).
  Definition m_list_belong_dec := pred_list_belong_dec eq_prod_dec (P:=Q).
  Definition m_list_get_witness := pred_list_get_witness (P:=Q).
  Definition m_list_remove := pred_list_remove eq_prod_dec (P:=Q).
  Definition m_length := pred_length (P:=Q).
  Definition lt_m_length := lt_pred_length (P:=Q).
  Definition m_list_equiv := pred_list_equiv (P:=Q) (Q:=Q).

  Notation "e 'INm' l" := (m_list_belong l e) (at level 50).

  (* returns true if there exists a element a of A such that (p,a)
     belongs to the m_list : *)

  Fixpoint m_list_belong_fst (l:m_list) (p:nat) {struct l} : Prop :=
    match l with
      | pred_nil=> False
      | pred_cons (hn,ha) C t => hn = p \/ m_list_belong_fst t p
    end.

  Notation "e 'INfst' l" := (m_list_belong_fst l e) (at level 50).

  (* returns true if there exists a natural p such that (p,a)
     belongs to the m_list : *)
  Fixpoint m_list_belong_snd (l:m_list) (a:A) {struct l} : Prop :=
    match l with
      | pred_nil=> False
      | pred_cons (hn,ha) C t => ha = a \/ m_list_belong_snd t a
    end.
   
  Notation "e 'INsnd' l" := (m_list_belong_snd l e) (at level 50).

  Lemma m_list_belong_fst_dec : forall (l : m_list) (p : nat), 
    {p INfst l} + {~ (p INfst l)}.
  Proof.
    intro l; elim l; simpl.
    intro; right; unfold not; trivial.
    intro a; elim a; clear a; intros a b C d Hrec p.
    elim (Hrec p); intro case.
    left; right; assumption.
    compare a p; intro comp.
    left; left; assumption.
    right; intro H.
    unfold not in *; elim H; assumption.
  Qed.

  (* auxiliary facts needed to specify combination *)
  Lemma combaux1 : forall (q : nat) (C : P n q) (tn : nb_list n), 
    nb_length (nb_cons q C tn) = length (A:=A) nil -> False.
  Proof.
    intros; simpl in H; inversion H. 
  Qed.

  Lemma combaux2 : forall (a : A) (ta : list A),
    nb_length (nb_nil (n:=n)) = length (a::ta) -> False.
  Proof.
    intros; simpl in H; inversion H. 
  Qed.

  Lemma tail_length : forall (q : nat) (C : P n q) (tn : nb_list n) (a : A) (ta : list A),
    nb_length (nb_cons q C tn) = length (a :: ta)-> nb_length tn = length ta.
  Proof.
    simpl; intros; auto with arith.
  Qed.

  (* combines a nb_list and a list of elements of A into a m_list, 
     given a proof the two argument lists are of same length  *)
  Fixpoint combine (ln:nb_list n) (la:list A) {struct ln} : (nb_length ln = length la)->m_list :=
    match ln, la return (nb_length ln = length la)->m_list with 
      | pred_nil,nil => 
        fun (H:(nb_length (pred_nil (P n))) = length (A:=A) nil) => m_nil
      | pred_nil, a :: ta => 
        fun (H:nb_length (pred_nil (P n)) = length (a::ta)) => False_rec m_list (combaux2 a ta H)
      | pred_cons q C tn, nil => 
        fun (H:(nb_length (pred_cons (P n) q C tn) = length (A:=A) nil)) => False_rec m_list (combaux1 q C tn H)
      | pred_cons q C tn, a::ta => 
        fun (H:(nb_length (pred_cons (P n) q C tn) = length (a::ta))) => m_cons (q,a) C (combine tn ta (tail_length q C tn a ta H))
    end.

  (* combination results : *)
  Lemma in_fst_combine_in_fst : forall (l : nb_list n) (la : list A) (H : nb_length l = length la) (q : nat), 
    q INfst (combine l la H) -> q INnb l.
  Proof.
    intro l; elim l; simpl. 
    intro la; destruct la; simpl.
    trivial.
    intro H.
    inversion H.
    intros a p d Hrec.
    intro la; destruct la; simpl.
    intro H.
    inversion H.
    intros H q H'.
    elim H'; intro case; [left | right].
    symmetry; assumption.
    apply (Hrec la (tail_length  a p d a0 la H) q).
    assumption.
  Qed.

  Lemma in_fst_in_fst_combine : forall (l : nb_list n) (la : list A) (H : nb_length l = length la) (q : nat), 
    q INnb l -> q INfst (combine l la H).
  Proof.
    intro l; elim l; simpl. 
    intro la; destruct la; simpl.
    trivial.
    intro H.
    inversion H.
    intros a p d Hrec.
    intro la; destruct la; simpl.
    intro H.
    inversion H.
    intros H q H'.
    elim H'; intro case; [left | right].
    symmetry; assumption.
    apply (Hrec la (tail_length  a p d a0 la H) q).
    assumption.
  Qed.

  Lemma in_snd_combine_in_snd : forall (l : nb_list n) (la : list A) (H : nb_length l = length la) (t : A), 
    t INsnd (combine l la H) -> In t la.
  Proof.
    intro l; elim l; simpl. 
    intro la; destruct la; simpl.
    trivial.
    intro H.
    inversion H.
    intros a p d Hrec.
    intro la; destruct la; simpl.
    intro H.
    inversion H.
    intros H t H'.
    elim H'; intro case; [left | right].
    assumption.
    apply (Hrec la (tail_length  a p d a0 la H) t).
    assumption.
  Qed.

  Lemma in_snd_in_snd_combine : forall (l : nb_list n) (la : list A) (H : nb_length l = length la) (t : A), 
    In t la -> t INsnd (combine l la H).
  Proof.
    intro l; elim l; simpl. 
    intro la; destruct la; simpl.
    trivial.
    intro H.
    inversion H.
    intros a p d Hrec.
    intro la; destruct la; simpl.
    intro H.
    inversion H.
    intros H t H'.
    elim H'; intro case; [left | right].
    assumption.
    apply (Hrec la (tail_length  a p d a0 la H) t).
    assumption.
  Qed.

  (* belong / belong_fst / belong_snd results : *)
  Lemma belong_and_fst :  forall (l : m_list) (q:nat) (t:A), 
    (q, t) INm l -> q INfst l.
  Proof.
    intro l; elim l.
    simpl; trivial.
    intro a; elim a; clear a.
    intros a b p d Hrec q t.
    simpl.
    intro h; elim h; [left | right].
    replace a with (fst (a,b)).
    rewrite <- H.
    simpl; trivial.
    simpl; trivial.
    apply Hrec with t.
    assumption.
  Qed.

  Lemma belong_and_snd : forall (l : m_list) (q:nat) (t:A), 
    (q, t) INm l -> t INsnd l.
  Proof.
    intro l; elim l.
    simpl; trivial.
    intro a; elim a; clear a.
    intros a b p d Hrec q t.
    simpl.
    intro h; elim h; [left | right].
    replace b with (snd (a,b)). 
    rewrite <- H.
    simpl; trivial.
    simpl; trivial.
    apply Hrec with q.
    assumption.
  Qed.


  Lemma m_list_get_first_element : forall (l:m_list) (t:A), 
    t INsnd l -> {q : nat | (q,t) INm l}.
  Proof.
    intro l; elim l; simpl.
    intros t H; inversion H.
    intro a; elim a; clear a; intros a b p d Hrec.
    intros t h.
    elim (eq_A_dec b t); intro comp.
    exists a; subst b; left; trivial.
    elim (Hrec t). 
    intros x H.
    exists x; right; assumption.
    inversion h; [contradiction | assumption].
  Qed.

  Lemma m_list_get_second_element : forall (l:m_list) (q:nat),
    q INfst l -> {t : A | (q,t) INm l}.
  Proof.
    intro l; elim l; simpl.
    intros q H; inversion H.
    intro a; elim a; clear a; intros a b p d Hrec.
    intros q h.
    elim (eq_nat_dec a q); intro case.
    subst a; exists b; left; trivial.
    elim (Hrec q).
    intros x H.
    exists x; right; assumption.
    inversion h; [contradiction | assumption].
  Qed.


  Lemma remove_compat : forall (ln : nb_list n) (la:list A) (H : nb_length ln = length la) (p q : nat) (dummy:A),  
    (forall (q : nat), q INnb ln -> ~ (q INnb (nb_list_remove ln q))) -> 
    (forall (t:A), p INfst (m_list_remove (combine ln la H) (q,t))) -> p INnb (nb_list_remove ln q).
  Proof.
    induction ln; intros la H; destruct la; simpl.
    intros p q dummy H0 H1; apply (H1 dummy).
    inversion H.
    inversion H.
    intros p' q dummy set H'.
    elim (eq_nat_dec q a); intro comp.
    apply (in_fst_combine_in_fst ln la (tail_length a p ln a0 la H)).
    cut {t : A | m_list_belong (combine ln la (tail_length a p ln a0 la H)) (p', t)}.
    intro Hex; elim Hex; clear Hex.
    intros t Ht.
    generalize (H' a0).
    subst a.
    elim (eq_prod_dec (q, a0) (q, a0)); intro case.
    trivial.
    elim case.
    trivial.
    apply m_list_get_second_element.
    generalize (H' a0).
    subst a.
    elim (eq_prod_dec (q, a0) (q, a0)); intro case.
    trivial.
    elim case.
    trivial.
    simpl.
    compare p' a; intro comp'.
    left; assumption.
    right.
    apply (IHln la (tail_length a p ln a0 la H) p' q dummy).
    intro q'.
    generalize (set q').
    elim (eq_nat_dec q' a); intro case.
    subst a.
    intros H0 H1 h.
    apply H0.
    left; trivial.
    assumption.
    simpl.
    intros H0 H1 h.
    apply H0.
    right; assumption.
    right; assumption.
    intro t.
    generalize (H' t).
    elim (eq_prod_dec (q, t) (a, a0)); intro case.
    elim comp.
    replace q with (fst (q, t)); [ rewrite case; auto | auto ].
    simpl.
    intro H0; elim H0.
    intro h; symmetry  in h; contradiction.
    trivial.
  Qed.

  (* pointwise order on m_list, ignoring the nat part of elements : *)
  Inductive m_list_pointwise : m_list -> m_list -> Prop :=
    | m_list_pointwise_nil  : m_list_pointwise m_nil m_nil
    | m_list_pointwise_cons : forall (p:nat) (a a' : A) (C : Q (p,a)) (C' : Q (p,a')) (l l' : m_list), 
      r a a' -> m_list_pointwise l l' -> m_list_pointwise (m_cons (p,a) C l) (m_cons (p,a') C' l').

  Inductive list_pointwise : list A -> list A -> Prop :=
    | list_pointwise_nil : list_pointwise nil nil
    | list_pointwise_cons : forall (a a' : A) (l l' : list A), 
      r a a' -> list_pointwise l l' -> list_pointwise (a::l) (a'::l').


  Lemma list_pointwise_to_m_list_pointwise : forall (ln : nb_list n) (la1 la2 : list A) 
    (H1 : nb_length ln = length la1) (H2 : nb_length ln = length la2), 
    list_pointwise la1 la2 -> m_list_pointwise (combine ln la1 H1) (combine ln la2 H2).
  Proof.
    induction ln.
    intros la1 la2 H1 H2.
    destruct la1.
    destruct la2.
    simpl; constructor.
    inversion H2.
    inversion H1.
    intros la1 la2 H1 H2.
    destruct la1.
    inversion H1.
    destruct la2.
    inversion H2.
    simpl.
    intro depr.
    constructor.
    inversion depr.
    subst; assumption.
    apply IHln.
    inversion depr.
    assumption.
  Qed.


  Lemma alt_monostep_aux1 : forall (l l' : m_list),  
    m_list_pointwise l l' -> 
    (forall (i : nat) (a a' : A), (i,a) INm l -> (i,a') INm l -> a = a') ->
    (forall (i : nat) (a a' : A), (i,a) INm l' -> (i,a') INm l' -> a = a') ->
    forall (i : nat) (a a' : A), (i,a) INm l -> (i,a') INm l' -> r a a'.
  Proof.
    intro l; induction l as [ | h C t IHl]; simpl; intros l' r_l_l' fcn_l fcn_l' i a a' ia_in_l ia_in_l'.
    inversion ia_in_l.
    destruct l' as [ | h' C' t'].
    inversion ia_in_l'. 
    destruct h as [ih ah]; destruct h' as [ih' ah'].
    elim ia_in_l; clear ia_in_l; intro ia_in_l.
    inversion ia_in_l; subst i a.
    elim ia_in_l'; clear ia_in_l'; intro ia_in_l'.
    inversion ia_in_l'; subst a'.
    inversion r_l_l'; subst; trivial.
    assert (H : ah' = a').
    apply (fcn_l' ih ah' a'); [left | right]; trivial. 
    inversion r_l_l'; subst; trivial.
    inversion r_l_l'; subst; trivial.
    elim ia_in_l'; clear ia_in_l'; intro ia_in_l'.
    inversion ia_in_l'; subst i a'.
    assert (H : ah = a).
    apply (fcn_l ih' ah a); [left | right]; trivial. 
    inversion r_l_l'; subst; trivial.
    inversion r_l_l'; subst; trivial.
    apply (IHl t') with i; try right; trivial.
    inversion r_l_l'; subst; trivial.
    intros; apply fcn_l with i0; right; trivial.
    intros; apply fcn_l' with i0; right; trivial.
  Qed.


  Lemma alt_monostep_aux2 : forall (st : A -> m_list),  
    (forall (s t : A), r s t -> m_list_pointwise (st s) (st t))  ->
    (forall (s : A) (q : nat) (t u : A),  m_list_belong (st s) (q,t) ->
      m_list_belong (st s) (q,u) -> t = u) ->
    (forall (q : nat) (s t c d : A), r s t -> m_list_belong (st s) (q,c) ->
      m_list_belong (st t) (q,d) -> r c d).
  Proof.
    intros st mono fcn q s t c d rst Hb1 Hb2.
    intros; apply (alt_monostep_aux1 (st s) (st t)) with q; try assumption. 
    apply (mono s t); try assumption.
    intros q0 t0 u; apply (fcn s q0 t0 u); try assumption.
    intros q0 t0 u; apply (fcn t q0 t0 u); try assumption.
  Qed.

End m_list.

Implicit Arguments m_nil [A n].
Implicit Arguments m_cons [A n].
Implicit Arguments m_list_add_element [A n].
Implicit Arguments m_list_belong [A n].
Implicit Arguments m_list_belong_fst [A n].
Implicit Arguments m_list_belong_snd [A n].
Implicit Arguments m_list_belong_dec [A n].
Implicit Arguments m_list_get_witness [A n].
Implicit Arguments m_length [A n].
Implicit Arguments lt_m_length [A n].
Implicit Arguments combine [A n].
Implicit Arguments m_list_remove [A n].
Implicit Arguments m_list_equiv [A n].

  Notation "e 'INm' l" := (m_list_belong l e) (at level 50).
  Notation "e 'INfst' l" := (m_list_belong_fst l e) (at level 50).
  Notation "e 'INsnd' l" := (m_list_belong_snd l e) (at level 50).
  Notation "l '=m=' m" := (m_list_equiv l m) (at level 50).
  
  (* equivalence results : *)

Lemma m_list_equiv_combine :  forall (A : Set) (n m : nat) 
  (ln : nb_list n) (lm : nb_list m) (la la':list A) 
  (H : nb_length ln = length la) (H' : nb_length lm = length la'), 
  ln =p= lm -> la = la'-> (combine ln la H) =p= (combine (n:=m) lm la' H').
Proof.
  induction ln; intro lm; destruct lm; intro la; destruct la; intro la'; destruct la'; simpl.
  unfold pred_list_equiv; trivial.
  intros H H'; inversion H'.
  intro H; inversion H.
  intro H; inversion H.
  intros H H'; inversion H'.
  intros H H' H''; inversion H''.
  intro H; inversion H.
  intro H; inversion H.
  intro H; inversion H.
  intro H; inversion H.
  intros H H' H''; inversion H''.
  intros H H'; inversion H'.
  intro H; inversion H.
  intro H; inversion H.
  intros H H'; inversion H'.
  intros H H' H1 H2.
  inversion H1; inversion H2.
  subst.
  apply (pred_list_split_equiv (a0,a2) (a0,a2) 
    (combine ln la' (tail_length n A a0 p ln a2 la' H))
    (combine lm la' (tail_length m A a0 p0 lm a2 la' H'))
    p p0).
  split.
  trivial.
  apply IHln; trivial.
Qed.


Lemma m_list_belong_convert : forall (n : nat) (A : Set) 
  (la : list A) (m :nat) (lm : nb_list m) (q : nat) (t : A) 
  (Hlm : nb_length lm = length la) (Hconv : (forall p : nat, p INp lm -> p < n)) 
  (Hlconv : nb_length (nb_list_convert m n lm Hconv) = length la), 
  (q,t) INm (combine lm la Hlm) -> (q,t) INm (combine (nb_list_convert m n lm Hconv) la Hlconv).
Proof.
  intros n A la m lm q t Hlm Hconv Hlconv.
  unfold m_list_belong.
  apply pred_list_equiv_belong.
  apply m_list_equiv_combine.
  unfold nb_list_convert.
  apply pred_list_convert_equiv.
  trivial.
Qed.


Lemma m_list_convert_belong : forall (n : nat) (A : Set)
  (la : list A) (m :nat) (lm : nb_list m) (q : nat) (t : A) 
  (Hlm : nb_length lm = length la) (Hconv : (forall p : nat, p INp lm -> p < n)) 
  (Hlconv : nb_length (nb_list_convert m n lm Hconv) = length la), 
  (q,t) INm (combine (nb_list_convert m n lm Hconv) la Hlconv) -> (q,t) INm (combine lm la Hlm).
Proof.
  intros n A la m lm q t Hlm Hconv Hlconv.
  unfold m_list_belong.
  apply pred_list_equiv_belong.
  apply m_list_equiv_combine.
  unfold nb_list_convert.
  apply pred_list_equiv_sym.
  apply pred_list_convert_equiv.
  trivial.
Qed.

  (* m_list inclusion : l1 is included in l2 if there exists l and l' such that : 
     - l2 = l++l'
     - l' is equivalent to l1 *)
Inductive m_list_inc (Sigma : Set) (n n' : nat) : m_list n Sigma -> m_list n' Sigma -> Prop :=
  | m_equiv_inc : forall (l : m_list n Sigma) (l' : m_list n' Sigma), l =p= l' -> m_list_inc Sigma n n' l l'
  | m_cons_inc : forall (pt : nat * Sigma) (Cpt : Q n' Sigma pt) (l : m_list n Sigma) (l' : m_list n' Sigma), 
    m_list_inc Sigma n n' l l' -> m_list_inc Sigma n n' l (m_cons pt Cpt l').

Notation "l 'INC' L" := (m_list_inc _ _ _ l L) (at level 50).

Lemma m_list_inc_equiv : forall (Sigma : Set) (n n' n'' : nat) (l : m_list n Sigma) 
  (l' : m_list n' Sigma) (l'' : m_list n'' Sigma), 
  l' =p= l'' -> l INC l' -> l INC l''.
Proof.
  intros Sigma n n' n'' l l' l''; generalize n n' l l'; clear n n' l l'.
  (induction l''); intros n n' l l' Heq Hinc.
  replace l with (pred_nil (Q n Sigma)).
  constructor; unfold pred_list_equiv; trivial.
  inversion Heq.
  (induction l'); simpl; trivial.
  inversion Hinc.
  subst.
  inversion H.
  induction l; simpl; trivial.
  inversion H2.
  inversion H0.
  inversion Heq.
  destruct l'; inversion H0.
  subst.
  inversion Hinc.
  subst.
  destruct l; simpl; inversion H; subst.
  apply m_equiv_inc.
  unfold m_list_equiv; unfold pred_list_equiv; simpl.
  rewrite H4.
  rewrite H2; trivial.
  subst.
  apply (m_cons_inc Sigma n n'' a p l l'').
  apply (IHl'' n n' l l').
  apply H2.
  assumption.
Qed.


Lemma m_list_inc_trans : forall (Sigma : Set) (n : nat) (l'' l l' : m_list n Sigma), 
  l INC l' -> l' INC l'' ->  l INC l''.
Proof.
  induction l''; intros l l'; simpl.
  intros h1 h2.
  inversion h2; subst.
  cut (l' = (pred_nil (Q n Sigma))); [intro h; rewrite h in h1; apply h1 | induction l'; simpl].
  trivial.
  inversion H.
  intros h1 h2.
  inversion h2.
  subst.
  apply (m_list_inc_equiv Sigma n n n l l' (pred_cons (Q n Sigma) a p l'')); trivial.
  subst.
  apply (m_cons_inc Sigma n n a p l l'').
  apply (IHl'' l l'); trivial.
Qed.


Lemma m_list_inc_refl : forall (Sigma : Set) (n : nat) (l : m_list n Sigma), l INC l.
Proof.
  induction l.
  constructor.
  apply pred_list_equiv_refl.
  constructor.
  apply pred_list_equiv_refl.
Qed.



