  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : propa_property.v				         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : some basic properties of function propagate     *)
  (***************************************************************)

Local Unset Injection On Proofs.

Section propa_property.

  Require Export propa.

  Variable Sigma:Set. (* state set *)
  Variable n:nat. (* bytecode size *)
  Variable succs:forall p:nat, p<n->nb_list n. (* successor function *)
  Variable step:forall p:nat, p<n->Sigma->list Sigma. (* flow function *)
  Variable r:relation Sigma. (* order on state set *)
  Variable sup:binop Sigma. (* sup on state set *)

  Hypothesis step_succs_same_length:forall (q:nat) (C:q<n) (s:Sigma), 
    nb_length (succs q C)=length (step q C s).
  Hypothesis eq_Sigma_dec:forall x y:Sigma, {x=y} + {x <> y}.
  Hypothesis r_is_semilattice:semilattice Sigma r sup.

  Definition step' (p:nat) (C:p < n) (s:Sigma):=
    (combine (succs p C) (step p C s) (step_succs_same_length p C s)).

  Notation Propa:=(propagate sup eq_Sigma_dec).
  Notation ra:=(SI_vector_pointwise Sigma r).
  Definition rb (n:nat):relation (nb_list n):=lt_nb_length (n:=n).

  (* sup_iter : computes the sup of all (snd) elements in a m_list *)
  Fixpoint sup_iter (s : Sigma) (l : m_list n Sigma) (b : nat) {struct l} : Sigma :=
    match l with 
      | pred_nil => s
      | pred_cons (q,t) _ l' => 
        match eq_nat_dec b q with 
          | left _ => sup_iter (sup s t) l' b	
          | right _ => sup_iter s l' b
        end
    end.

  (* results about sup_iter : *)
  Lemma sup_iter_r : forall (l : m_list n Sigma) (s : Sigma) (b : nat), r s (sup_iter s l b).
  Proof.
    Semi r_is_semilattice.
    induction l; intros s b; simpl.
    apply ord_refl.
    destruct a as [q t].
    elim (eq_nat_dec b q); intro comp.
    apply ord_trans with (sup s t).
    apply lub1.
    apply IHl.
    apply IHl.
  Qed.


  Lemma sup_iter_r_arg : forall (l : m_list n Sigma) (s t : Sigma) (b : nat), 
    r s t -> r (sup_iter s l b) (sup_iter t l b).
  Proof.
    Semi r_is_semilattice.
    induction l; intros s t b rst; simpl.
    assumption.
    destruct a as [q u].
    elim (eq_nat_dec b q); intro comp.
    apply IHl; trivial.
    apply (monotone_lub Sigma r sup); trivial.
    apply IHl; trivial.
  Qed.


  Lemma sup_iter_r_in : forall (l : m_list n Sigma) (s t : Sigma) (b : nat), 
    (b,t) INm l -> r t (sup_iter s l b).
  Proof.
    Semi r_is_semilattice.
    induction l; intros s t b Hbelong; simpl.
    inversion Hbelong.
    destruct a as [q u].
    elim (eq_nat_dec b q); intro comp.
    subst q.
    elim Hbelong; clear Hbelong; intro Hbelong.
    inversion Hbelong; subst t.
    apply ord_trans with (sup_iter u l b).
    apply sup_iter_r; trivial.
    apply sup_iter_r_arg; trivial.
    apply ord_trans with (sup_iter s l b).
    apply IHl; assumption.
    apply sup_iter_r_arg; trivial.
    elim Hbelong; clear Hbelong; intro Hbelong.
    inversion Hbelong; subst b; elim comp; trivial.
    apply IHl; trivial.
  Qed.

  Lemma sup_iter_stable : forall (l : m_list n Sigma) (s : Sigma) (b : nat), 
    (forall (t : Sigma), (b,t) INm l -> sup s t = s) ->
    sup_iter s l b = s.
  Proof.
    Semi r_is_semilattice.
    induction l; simpl; intros s b Hstable.
    trivial.
    destruct a as [q t].
    elim (eq_nat_dec b q); intro comp.
    cut (sup_iter (sup s t) l b = sup_iter s l b).
    intro H; rewrite H.
    apply IHl.
    intros t' Ht'; apply (Hstable t').
    right; assumption.
    replace (sup s t) with s.
    trivial.
    symmetry; apply Hstable.
    left; subst q; trivial.
    apply IHl.
    intros t' H; apply (Hstable t').
    right; assumption.
  Qed.


  Lemma sup_iter_m_r : forall (l l' : m_list n Sigma) (s : Sigma) (b : nat), 
    m_list_pointwise n Sigma r l l' -> r (sup_iter s l b) (sup_iter s l' b).
  Proof.
    Semi r_is_semilattice.
    induction l; simpl; intros l' s b Hmr.
    inversion Hmr; simpl.
    apply ord_refl.
    destruct a as [q t].
    destruct l'; inversion Hmr.
    subst; simpl.
    elim (eq_nat_dec b q); intro case.
    apply ord_trans with (sup_iter (sup s t) l' b).
    apply IHl; auto.
    apply sup_iter_r_arg; auto.
    apply (monotone_lub Sigma r sup); auto.
    apply IHl; auto.
  Qed.

  (* Proof of step 2 in defining of function iterate *)
  Lemma propa_nondep_lexprod:
    forall (ss:vector Sigma n) (q:nat) (w:nb_list n) (C:q < n),
      nondep_lexprod (vector Sigma n) (nb_list n) (ra n) (rb n)
      (Propa ss w (step' q C (ss[q|C]))) (ss, nb_cons q C w).
  Proof.
    intros ss q w C.
    CaseEq (Propa ss w (step' q C (ss[q|C]))).
    intros ss' w' Heq.
    cut (ra n ss' ss \/ (ss, w)=(ss', w')).
    intro H; elim H.
    (* case ra ss' ss : *)
    constructor.
    assumption.
    (* case (ss, w)=(ss', w') : *)
    elim (eq_dec_to_list_eq_dec Sigma eq_Sigma_dec n ss' ss); intro case_ss'_ss.
    rewrite case_ss'_ss.
    (* case ss' = ss : *)
    intro H0; constructor 2.
    inversion H0.
    constructor.
    (* case ss' <> ss : contradiction *)
    intro h; elim case_ss'_ss; replace ss with (fst (ss,w)); [rewrite h; auto | auto].
    (* prooving ra n ss' ss \/ (ss, w)=(ss', w') : *)
    apply propa_case with sup eq_Sigma_dec (step' q C (ss[q|C])); 
      try assumption.
    symmetry; assumption.
  Qed.


  Lemma propa_replace_commut :
    forall  (l:m_list n Sigma) (ss:vector Sigma n) (b:nat) (w w':nb_list n) 
      (C:b < n) (c:Sigma), 
      fst (Propa (ss[b<-(sup c (ss[b|C]))]) w l)=
      (fst (Propa ss w' l))[b<-(sup_iter (sup c (ss[b|C])) l b)].
  Proof.
    Semi r_is_semilattice.
    intro l; elim l. 
    simpl; intros; trivial.
  (* l <> nil *)
    simpl; intro a; elim a; clear a.
    intros q s p d Hrec ss b w w' C c.
    elim (eq_nat_dec b q); intro comp; simpl.
  (* b=q *)
    subst q.
    rewrite element_at_in_replaced.
    elim (eq_Sigma_dec (sup s (sup c (ss[b|C]))) (sup c (ss[b|C]))); intro case.
    rewrite (element_at_irrel Sigma n ss b p C).
    elim (eq_Sigma_dec (sup s (ss[b|C])) (ss[b|C])); intro case'.
    rewrite (Hrec ss b w w' C c).
    cut ((sup_iter (sup c (ss[b|C])) d b) = (sup_iter (sup (sup c (ss[b|C])) s) d b)). 
    intro case''.
    rewrite case''; trivial.
    cut (sup (sup c (ss[b|C])) s = sup s (sup c (ss[b|C]))).
    intro case''; rewrite <- case'' in case; rewrite case; trivial.
    apply (lub_refl Sigma r sup); try assumption.
    rewrite (Hrec ss b w w' C c).
    rewrite (Hrec ss b (nb_list_add_element w' b p) w' C s).
    rewrite overwrite_replace.
    cut (sup c (ss[b|C]) = sup (sup c (ss[b|C])) s).
    intro case''; rewrite <- case''; trivial.
    symmetry.
    rewrite (lub_refl Sigma r sup (sup c (ss[b|C])) s); try assumption.
    rewrite overwrite_replace.
    elim (eq_Sigma_dec (sup s (ss[b|p])) (ss[b|p])); intro case'.
    elim case.
    rewrite (lub_circ Sigma r sup s c (ss[b|C])); try assumption.
    rewrite (element_at_irrel Sigma n ss b p C) in case'.
    rewrite case'; trivial.
    rewrite (lub_refl Sigma r sup (sup c (ss[b|C])) s); try assumption.
    rewrite (lub_circ Sigma r sup s c (ss[b|C])); try assumption.
    rewrite (element_at_irrel Sigma n ss b p C).
    generalize (Hrec (ss[b<-(sup s (ss[b|C]))]) b (nb_list_add_element w b p) (nb_list_add_element w' b p) C c).
    rewrite element_at_in_replaced.
    rewrite overwrite_replace.
    trivial.
    rewrite element_at_in_replaced'; trivial.
    elim (eq_Sigma_dec (sup s (ss[q|p])) (ss[q|p])); intro case.
    apply Hrec; try assumption.
    rewrite (commutative_replace Sigma n ss b q).
    generalize (Hrec (ss[q<-(sup s (ss[q|p]))]) b (nb_list_add_element w q p) (nb_list_add_element w' q p) C c).
    rewrite element_at_in_replaced'; trivial.
    intro; apply comp; symmetry; assumption.
    left; assumption.
  Qed.


  Lemma r_ss_propa_ss:
    forall (l:m_list n Sigma) (q:nat) (ss:vector Sigma n) (w:nb_list n) (C:q < n),
      r (ss[q|C]) ((fst (Propa ss w l))[q|C]).
  Proof.
    Semi r_is_semilattice.
    intro l; elim l.
    simpl; intros; apply ord_refl.
    intro a; elim a; clear a.
    intros a b p d Hrec q ss w Cq.
    simpl.
    elim (eq_Sigma_dec (sup b (ss[a|p])) (ss[a|p])); intro comp.
  (* sup b ss[a]=ss[a] *)
    apply Hrec; assumption.
  (* sup b ss[a]=ss[a] *)
    compare a q; intro comp'.
  (* a=q *)
    subst a.
    apply ord_trans with (y:=((ss[q<-(sup b (ss[q|p]))])[q|Cq])).
    rewrite (element_at_irrel Sigma n ss q p Cq).
    rewrite (element_at_in_replaced Sigma n ss q (sup b (ss[q|Cq])) Cq).
    apply lub2; assumption.
    apply Hrec.
  (* a <> q *)
    rewrite<-(element_at_in_replaced' Sigma n ss a q (sup b (ss[a|p])) Cq comp').
    apply Hrec.
  Qed.


  Lemma inc_propa_w_propa_replace_ss_w:
    forall (l:m_list n Sigma) (a p:nat) (ss:vector Sigma n) (w:nb_list n) (new:Sigma) (Ca:a<n),
      p INnb (snd (Propa ss (nb_list_add_element w a Ca) l)) ->
      p INnb (snd (Propa (ss[a<-new]) (nb_list_add_element w a Ca) l)).
  Proof.
    intro l; elim l.
    simpl; intros; trivial.
    intro a; elim a; clear a.
    intros a b C d Hrec a' p' ss w new Ca'.
    simpl.
    elim (eq_Sigma_dec (sup b (ss[a|C])) (ss[a|C])); intro comp.
  (* sup b ss[a]=ss[a] *)
    compare a a'; intro comp'.
  (* a=a' *)
    subst a'.
    rewrite (element_at_in_replaced Sigma n ss a new).
    elim (eq_Sigma_dec (sup b new) new); intro comp'.
  (* sup b new=new *)
    apply Hrec.
  (* sup b new <> new *)
    rewrite (overwrite_replace Sigma n ss a new (sup b new)).
    unfold nb_list_add_element.
    rewrite (nb_list_add_already_there n w a Ca' C).
    apply (Hrec a p' ss w (sup b new) Ca').
  (* a <> a' *)
    elim (eq_Sigma_dec (sup b ((ss[a'<-new])[a|C])) ((ss[a'<-new])[a|C])); intro comp''.
    apply Hrec.
    rewrite (element_at_in_replaced' Sigma n ss a' a new C) in comp''.
    contradiction.
    auto.
  (* sup b ss[a] <> ss[a] *)
    elim (eq_Sigma_dec (sup b ((ss [a' <- new]) [a | C]))
                ((ss [a' <- new]) [a | C])); intro comp'.
  (* sup b ss[a'<-new][a]=ss[a'<-new][a] *)
    compare a a'; intro comp''.
  (* a=a' *)
    subst a'.
    replace (ss[a<-new]) with ((ss[a<-(sup b (ss[a|C]))])[a<-new]).
    unfold nb_list_add_element.
    rewrite (nb_list_add_already_there n w a Ca' C).
    unfold nb_list_add_element in Hrec.
    apply Hrec.
    apply (overwrite_replace).
  (* a <> a' *)
    rewrite (element_at_in_replaced' Sigma n ss a' a new C) in comp'.
    contradiction.
    auto.
  (* sup b ss[a'<-new][a] <> ss[a'<-new][a] *)
    compare a a'; intro comp''.
  (* a=a' *)
    subst a'.
    rewrite (element_at_in_replaced Sigma n ss a new).
    rewrite (overwrite_replace Sigma n ss a new (sup b new)).
    replace (ss[a<-(sup b new)]) with 
      ((ss[a<-(sup b (ss[a|C]))])[a<-(sup b new)]).
    apply Hrec.
    apply (overwrite_replace).
  (* a <> a' *)
    rewrite (element_at_in_replaced' Sigma n ss a' a new C).
    cut (a' <> a \/ new=sup b (ss[a|C])); [intro H | left; auto].
    rewrite (commutative_replace Sigma n ss a' a new (sup b (ss[a|C])) H).
    replace (nb_list_add_element (nb_list_add_element w a' Ca') a C) with 
      (nb_list_add_element (nb_list_add_element (nb_list_add_element w a' Ca') a C) a' Ca').
    apply Hrec.
    unfold nb_list_add_element.
    apply nb_list_add_already_there_added.
    auto.
  Qed.

  Lemma no_change_at_p_not_in_w:
    forall (l:m_list n Sigma) (p:nat) (ss:vector Sigma n) (w:nb_list n) (Cp:p<n),
      ~ (p INnb (snd (Propa ss w l))) ->
      (fst (Propa ss w l))[p|Cp] = ss[p|Cp].
  Proof.
    Semi r_is_semilattice.
    intro l; elim l.
    simpl; trivial.
    intro a; elim a; clear a.
    intros a b p d Hrec p' ss w Cp'.
    simpl.
    elim (eq_Sigma_dec (sup b (ss[a|p])) (ss[a|p])); intro comp.
  (* sup b ss[a]=ss[a] *)
    apply Hrec; assumption.
  (* sup b ss[a] <> ss[a] *)
    intro H.
    compare a p'; intro comp'.
  (* a=p' *)
    subst a.
    elim H; clear H; elim d.
    simpl.
    apply (nb_list_belong_added n w p' p).
    intros.
    apply inc_w_propa_w.
    apply (nb_list_belong_added n w p' p).
  (* a <> p' *)
    rewrite<-(element_at_in_replaced' Sigma n ss a p' (sup b (ss[a|p])) Cp' comp').
    apply Hrec; try assumption.
  Qed.


  Remark prod_eq:forall (a q:nat) (b t:Sigma), 
    (a,b)=(q,t)->a=q /\ b=t. 
    intros a q b t H; split.
    replace a with (fst (a,b)); [rewrite H | auto]; auto.
    replace b with (snd (a,b)); [rewrite H | auto]; auto.
  Qed.

  Lemma stable_p_by_propa:
    forall (p q:nat) (s t:Sigma) (ss:vector Sigma n) (w:nb_list n) 
      (Cp:p < n) (Cq:q < n),
      s=ss[p|Cp]->
      ~ (p INnb (snd (Propa ss w (step' p Cp s)))) ->
      (q,t) INm (step' p Cp s) ->
      r t ((fst (Propa ss w (step' p Cp s)))[q|Cq]).
  Proof.
    Semi r_is_semilattice.
    intros p q s t ss w Cp Cq s_eq.
    generalize ss s_eq w; clear ss s_eq w; elim (step' p Cp s); simpl.
    intros ss s_eq w h  F; inversion F.
    intro a; elim a; clear a; intros a b Ca d Hrec ss s_eq w H H'.
    generalize H; clear H.
    elim (eq_Sigma_dec (sup b (ss[a|Ca])) (ss[a|Ca])); intro case.
  (*  case:sup b (ss[a|Ca])=ss[a|Ca] *)
    elim (eq_prod_dec Sigma eq_Sigma_dec (a,b) (q,t)); intros comp H.
  (* (a,b)=(q,t) *)
    apply ord_trans with (y:=ss[q|Cq]).
    elim (prod_eq a q b t comp); intros; subst a b.
    rewrite (element_at_irrel Sigma n ss q Cq Ca).
    rewrite <- case.
    apply lub1.
    apply r_ss_propa_ss; try assumption.
  (* (a,b) <> (q,t) *)
    apply Hrec; try assumption.
    elim H'; intro h.
    symmetry in h; contradiction.
    assumption.
  (*  case:sup b (ss[a|Ca]) <> ss[a|Ca] *)
    rewrite (propa_replace_commut d ss a (nb_list_add_element w a Ca) (nb_list_add_element w a Ca) Ca b); try auto.
    elim (eq_prod_dec Sigma eq_Sigma_dec (a,b) (q,t)); intros comp H.
  (* (a,b)=(q,t) *)
    elim (prod_eq a q b t comp); intros; subst a; subst b.
    rewrite element_at_in_replaced.
    apply ord_trans with (sup t (ss[q|Ca])).
    apply lub1.
    apply sup_iter_r; try assumption.
  (* (a,b) <> (q,t) *)
    elim H'; clear H'; intro H'.
    symmetry in H'; contradiction.
    compare a q; intro comp'.
    subst a.
    rewrite (element_at_in_replaced).
    apply sup_iter_r_in; trivial.
    rewrite (element_at_in_replaced').
    apply Hrec; trivial.
    intro h; apply H. 
    apply inc_propa_w_propa_replace_ss_w; try assumption.
    assumption.
  Qed.

End propa_property.
