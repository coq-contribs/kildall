  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : instructions.v				         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : definition of instructions, frames, Succs,      *)
  (*	       configurations, functions, constructors...        *)
  (***************************************************************)

Section instructions.

  Add LoadPath "../aux".
  Add LoadPath "../lists".
  Add LoadPath "../kildall".
  Require Export lists.
  Require Export vector_results.
  Require Export nat_bounded_list. 
  Require Export tree.
  Require Export aux_arith.

  (* set of functions, constructors and type names :*)
  Parameter name : Set.
  Axiom eq_name_dec : forall (n n' : name), {n = n'} + {n <> n'}.

  (* set of instructions :*)
  Inductive instruction (n:nat) : Set :=
    | i_return : instruction n
    | i_stop : instruction n
    | i_load : nat->instruction n
    | i_call : name->nat->instruction n
    | i_build : name->nat->instruction n
    | i_branch : forall (c:name) (i:nat), i<n->instruction n. 

  (* constructors : *)
  Record constr : Set := mkconstr {cons_name : name; cons_args : list name; cons_ret : name}.
  (* functions : *)
  Record function : Set := mkfunction {fcn_name : name; fcn_args : list name; fcn_ret : name;
    fcn_size : nat; fcn_bytecode : vector (instruction fcn_size) fcn_size}.

  Definition value : Set := tree name name.

  Record frame : Set := mkframe {frm_fun : name; frm_pc : nat; frm_stack : list value; frm_args : list value}.

  Notation configuration := (list frame).

  (* returns the first function in the list whose name matches its
     parameter, None if no matching function was found *)
  Fixpoint get_function_by_name (l : list function) (f : name) {struct l} : option function :=
    match l with 
      | nil => None
      | h :: t => 
        match (eq_name_dec (fcn_name h) f) with 
          | left _ => Some h
	  | right _ => get_function_by_name t f
	end
    end.

  (* analog to get_function_by_name for constructors *)
  Fixpoint get_constr_by_name (l : list constr) (c : name) {struct l} : option constr :=
    match l with 
      | nil => None 
      | h :: t => match (eq_name_dec (cons_name h) c) with 
                    | left _ => Some h
	            | right _ => get_constr_by_name t c
	          end
    end.


  Lemma get_some_in_functions : forall (fcn : function) (f : name) (l : list function), 
    get_function_by_name l f = Some fcn -> In fcn l.
  Proof.
    induction l.
    intro H; inversion H.
    simpl.
    elim (eq_name_dec (fcn_name a) f); intros case H; [left | right].
    inversion H; trivial.
    apply IHl; assumption.
  Qed.

      (* last instruction in the bytecode is either return or stop : *)
  Definition last_return_or_stop (n : nat) (bc : vector (instruction n) n) := forall (C : 0<n), 
    bc[pred n|lt_pred_n_n n C] = i_return n \/ bc[pred n|lt_pred_n_n n C] = i_stop n.

  Notation eq_value_dec := (eq_tree_dec name eq_name_dec).

      (* defining function successor : *)
  Definition Succs_aux (n : nat) (bc : vector (instruction n) n) (p:nat) (C : p < n) : nb_list (S n) :=
    match (bc[p|C]) with 
      | i_return => nb_cons p (lt_trans p n (S n) C (lt_n_Sn n)) (pred_nil (P (S n)))
      | i_stop => pred_nil (P (S n))
      | i_branch c q Cq => nb_cons (S p) (lt_n_S p n C) (nb_cons q (lt_trans q n (S n) Cq (lt_n_Sn n)) (pred_nil (P (S n))))
      | _ => nb_cons (S p) (lt_n_S p n C) (pred_nil (P (S n)))
    end.


  Lemma Succs_better_bound : forall (n : nat) (bc : vector (instruction n) n) (p:nat) (C : p<n), 
    last_return_or_stop n bc -> forall (q:nat), q INnb (Succs_aux n bc p C) -> q<n.
  Proof.
    intros n bc p C.
    unfold Succs_aux.
    CaseEq (bc[p|C]); simpl.
    intros case Hrs q H; elim H; clear H; intro H.
    subst q; assumption.
    inversion H.
    intros d dd ddd h; inversion h.
    intros a case Hrs q H; elim H; clear H; intro H.
    apply lt_S_neq_lt.
    subst q; auto with arith.
    subst q; intro h.
    generalize Hrs; clear Hrs; unfold last_return_or_stop; subst n.
    intro Hrs; generalize (Hrs (lt_O_Sn p)). 
    simpl; replace (bc[p|lt_pred_n_n (S p) (lt_O_Sn p)]) with (bc[p|C]); [intro H | apply element_at_irrel].
    elim H; clear Hrs H; intro H; rewrite H in case; inversion case.
    inversion H.
    intros fcn ar case Hrs q H; elim H; clear H; intro H.
    apply lt_S_neq_lt.
    subst q; auto with arith.
    subst q; intro h.
    generalize Hrs; clear Hrs; unfold last_return_or_stop; subst n.
    intro Hrs; generalize (Hrs (lt_O_Sn p)).
    simpl; replace (bc[p|lt_pred_n_n (S p) (lt_O_Sn p)])  with (bc[p|C]); [intro H | apply element_at_irrel].
    elim H; clear Hrs H; intro H; rewrite H in case; inversion case.
    inversion H.
    intros c ar case Hrs q H; elim H; clear H; intro H.
    apply lt_S_neq_lt.
    subst q; auto with arith.
    subst q; intro h.
    generalize Hrs; clear Hrs; unfold last_return_or_stop; subst n.
    intro Hrs; generalize (Hrs (lt_O_Sn p)).
    simpl; replace (bc[p|lt_pred_n_n (S p) (lt_O_Sn p)])  with (bc[p|C]); [intro H | apply element_at_irrel].
    elim H; clear Hrs H; intro H; rewrite H in case; inversion case.
    inversion H.
    intros c i Ci case Hrs q H; elim H; clear H; intro H.
    apply lt_S_neq_lt.
    subst q; auto with arith.
    subst q; intro h.
    cut (p = pred n).
    intro; subst p.
    cut (0<n).
    intro Cn.
    generalize (Hrs Cn).
    simpl; replace (bc[pred n|lt_pred_n_n n Cn])  with (bc[pred n|C]); [intro H | apply element_at_irrel].
    elim H; clear H; intro H; rewrite H in case; inversion case.
    inversion h.
    auto with arith.
    rewrite <- h.
    simpl; trivial.
    elim H; clear H; intro H.
    subst q.
    assumption.
    inversion H.
  Defined.

  Definition Succs (n : nat) (bc : vector (instruction n) n) (H:last_return_or_stop n bc) (p:nat) (C : p<n) := 
    nb_list_convert (S n) n (Succs_aux n bc p C) (Succs_better_bound n bc p C H).

  Lemma Succs_aux_equiv : forall (n : nat) (bc : vector (instruction n) n) (p:nat) (C C' : p<n), 
    (Succs_aux n bc p C) =nb= (Succs_aux n bc p C').
  Proof.
    intros; unfold Succs_aux.
    rewrite (element_at_irrel (instruction n) n bc p C' C).
    elim (bc[p|C]); simpl; try split; trivial.
  Qed.

  Lemma Succs_equiv : forall (n : nat) (bc : vector (instruction n) n) (lr : last_return_or_stop n bc) (p:nat) (C C' : p<n), 
    (Succs n bc lr p C) =nb= (Succs n bc lr p C').
  Proof.
    intros; unfold Succs; unfold nb_list_convert.
    apply pred_list_equiv_trans with 
      (lp := (pred_list_convert (Q:=fun p0 : nat => p0 < n) (Succs_aux n bc p C) (Succs_better_bound n bc p C lr))) 
      (lq := (Succs_aux n bc p C)) 
      (lr := (pred_list_convert (Q:=fun p : nat => p < n) (Succs_aux n bc p C') (Succs_better_bound n bc p C' lr))).
    apply pred_list_equiv_sym.
    apply (nb_list_convert_equiv (S n) n (Succs_aux n bc p C) (Succs_better_bound n bc p C lr)).
    apply pred_list_equiv_trans with 
      (lp := (Succs_aux n bc p C))
      (lq := (Succs_aux n bc p C'))
      (lr := (pred_list_convert (Q:=fun p : nat => p < n) (Succs_aux n bc p C') (Succs_better_bound n bc p C' lr))).
    apply Succs_aux_equiv.
    apply (nb_list_convert_equiv (S n) n).
  Qed.


End instructions.
