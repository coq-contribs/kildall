  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*						  	         *)
  (*   File : fresh_variables.v		  		         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : (Huge) Lemma about fresh variables needed	 *)
  (*			to perform shape analysis                *)
  (***************************************************************)

Local Unset Injection On Proofs.

Section fresh_variables.
  

  Require Export inst_types.
  Require Export machine_types.
  Require Export inst_shapes.
  
  Notation configuration := (list (frame)).
  Notation Get_function := (get_function_by_name functions).
  Notation Get_constr := (get_constr_by_name constructors).
  Notation Frm := (mkframe).
  Notation Substitution := (list subst_elem).
  Notation Expression := (tree Name Name).
  
  (* initial shape for function fcn : *)
  Definition Sss_init (fcn : function) := 
    (constant_list (fcn_size fcn) Bot_S)[0<-(Shapes nil (init_vars fcn))].
  
  (* result of the shape analysis algorithm : *)
  Definition Kildall_Shapes (fcn : function) (Hin : In fcn functions) := 
    Kildall_shapes fcn (lrs_functions fcn Hin) (Sss_init fcn).
  

  Definition itera_shapes (fcn : function) (Hin : In fcn functions) : 
    forall (ssw : (vector Sigma_S (fcn_size fcn)) * (nb_list (fcn_size fcn))), 
      vector Sigma_S (fcn_size fcn)  := itera Sigma_S (fcn_size fcn) 
      (Succs (fcn_size fcn) (fcn_bytecode fcn) (lrs_functions fcn Hin)) 
      (Step_S fcn) r_S sup_S (Step_S_Succs_same_length fcn (lrs_functions fcn Hin)) 
      eq_Sigma_S_dec r_S_is_semilattice wfr_S.
  

  Definition propagate_shapes (fcn : function) (Hin : In fcn functions) : 
    vector Sigma_S (fcn_size fcn) -> nb_list (fcn_size fcn) -> m_list (fcn_size fcn) Sigma_S -> 
    vector Sigma_S (fcn_size fcn) * nb_list (fcn_size fcn) := 
    propagate sup_S eq_Sigma_S_dec (n:=fcn_size fcn).
  
  
  Definition Step_S' (fcn : function) (Hin : In fcn functions) : 
    forall (p : nat), p < fcn_size fcn -> Sigma_S -> m_list (fcn_size fcn) Sigma_S := 
      step' Sigma_S (fcn_size fcn) (Succs (fcn_size fcn) (fcn_bytecode fcn) (lrs_functions fcn Hin)) 
      (Step_S fcn) (Step_S_Succs_same_length fcn (lrs_functions fcn Hin)).

  Definition Hvars (n : nat) (ss : vector Sigma_S n) : Prop := 
    forall (p : nat) (C : p < n) (ls : Substitution) (le : list Expression), 
      ss[p|C] = Shapes ls le -> 
      (forall (e : Expression), In e le -> (forall (h p' : nat), p' > p -> var_not_in_tree e p' h))
      /\ 
      (forall (s : subst_elem), In s ls -> (forall (h p' : nat), p' > p -> ~var_in_subst_elem s p' h)).

  Hypothesis fwd_jmp : forall (fcn : function) (Hin : In fcn functions) (p : nat) (C : p < fcn_size fcn) 
    (cnm : name) (j: nat) (Cj : j < fcn_size fcn), 
    (fcn_bytecode fcn)[p|C] = i_branch (fcn_size fcn) cnm j Cj -> j > p.


  Definition ss_init (fcn : function) := 
    (constant_list (fcn_size fcn) Bot_T)[0<-(Types (rev (fcn_args fcn)))].


  Hypothesis Passed_Kildall_Types : forall (fcn : function) (Hin : In fcn functions),
    ~ Top_T INv (machine_types.Kildall_Types fcn Hin).


  Hypothesis Passed_Kildall : forall (fcn : function) (Hin : In fcn functions),
    ~ Top_S INv (Kildall_Shapes fcn Hin).


(*  Hypothesis Pattern_branch : forall (fcn : function) (Hin : In fcn functions) 
    (p : nat) (C : p < fcn_size fcn) (cnm : name) 
    (j: nat) (Cj : j < fcn_size fcn) 
    (s : Substitution) (e : Expression) (le : list Expression), 
    (fcn_bytecode fcn)[p|C] = i_branch (fcn_size fcn) cnm j Cj -> 
    (Kildall_Shapes fcn Hin)[p|C] = Shapes s (e::le) -> 
    tree_is_pattern e.*)

  Lemma m_list_inc_1 : forall (Sigma : Set) (n n': nat) (l : m_list n' Sigma) (a a' : nat*Sigma) (C : Q n Sigma a) (C' : Q n' Sigma a'),
    (pred_cons (Q n' Sigma) a' C' l) INC (m_cons a C (m_nil)) -> a' = a /\ l = m_nil.
  Proof.    
    intros Sigma n n' l a a' C C' Hinc.
    inversion Hinc.
    subst; inversion H.
    split; trivial.
    destruct l; trivial.
    inversion H.
    inversion H1.
    inversion H3.
  Qed.


  Lemma m_list_inc_2 : forall (Sigma : Set) (n n': nat) (l : m_list n' Sigma) (a a0 a' a'0 : nat*Sigma) (C : Q n Sigma a) (C0 :
    Q n Sigma a0) (C' : Q n' Sigma a') (C'0 : Q n' Sigma a'0),
  (pred_cons (Q n' Sigma) a' C' (pred_cons (Q n' Sigma) a'0 C'0 l)) INC (m_cons a C (m_cons a0 C0 m_nil)) -> a'
  = a /\ a'0 = a0 /\ l = m_nil.
  Proof.    
    intros Sigma n n' l a a0 a' a'0 C C0 C' C'0 Hinc.
    inversion Hinc.
    subst; inversion H.
    repeat split; trivial.
    destruct l; trivial.
    inversion H.
    inversion H1.
    inversion H3.
    inversion H5.
    inversion H7.
  Qed.


  Lemma Hvars_replace_Top : forall (n : nat) (ss : vector Sigma_S n) (p : nat),
    Hvars n ss -> Hvars n (ss[p<-Top_S]).
  Proof.
    intros n ss p Hv p0 C0 ls le case_shapes_p0.
    elim (eq_nat_dec p p0); intro comp.
    subst p0; rewrite element_at_in_replaced in case_shapes_p0; inversion case_shapes_p0.
    rewrite element_at_in_replaced' in case_shapes_p0; trivial; apply (Hv p0 C0 ls le case_shapes_p0).
  Qed.

  Lemma Hvars_replace_Bot : forall (n : nat) (ss : vector Sigma_S n) (p : nat),
    Hvars n ss -> Hvars n (ss[p<-Bot_S]).
  Proof.
    intros n ss p Hv p0 C0 ls le case_shapes_p0.
    elim (eq_nat_dec p p0); intro comp.
    subst p0; rewrite element_at_in_replaced in case_shapes_p0; inversion case_shapes_p0.
    rewrite element_at_in_replaced' in case_shapes_p0; trivial; apply (Hv p0 C0 ls le case_shapes_p0).
  Qed.

  Ltac TrivCase H h := elim (H h h); intro ddd; [clear ddd | elim ddd; trivial].


  Lemma Hvars_Top_S :  forall (n : nat) (ss : vector Sigma_S n) (w : nb_list n)
    (p : nat) (C : p < n) (a : (nat * Sigma_S)) (q : Q n Sigma_S a)
    (l : pred_list (nat * Sigma_S) (Q n Sigma_S)),
    Hvars n ss -> ss [p | C] = Top_S ->
    (pred_cons (Q n Sigma_S) a q l) INC 
    (m_cons (p, Top_S) (lt_trans p n (S n) C (lt_n_Sn n)) m_nil) ->
    Hvars n (fst (propagate sup_S eq_Sigma_S_dec ss w (pred_cons (Q n Sigma_S) a q l))).
  Proof.
    intros n ss w p C a q l Hvarss case_shapes_p Hinc.
    generalize (m_list_inc_1 _ _ _ _ _ _ _ _ Hinc).
    intro h; elim h; clear h; intros h1 h2.
    subst; simpl.
    replace (ss[p|q]) with (ss[p|C]).
    rewrite case_shapes_p.
    TrivCase eq_Sigma_S_dec Top_S.
    simpl; trivial.
    apply element_at_irrel.
  Qed. 

  Lemma Hvars_Bot_S :  forall (n : nat) (ss : vector Sigma_S n) (w : nb_list n)
    (p : nat) (C : p < n) (a : (nat * Sigma_S)) (q : Q n Sigma_S a)
    (l : pred_list (nat * Sigma_S) (Q n Sigma_S)),
    Hvars n ss -> ss [p | C] = Bot_S ->
    (pred_cons (Q n Sigma_S) a q l) INC 
    (m_cons (p, Bot_S) (lt_trans p n (S n) C (lt_n_Sn n)) m_nil) ->
    Hvars n (fst (propagate sup_S eq_Sigma_S_dec ss w (pred_cons (Q n Sigma_S) a q l))).
  Proof.
    intros n ss w p C a q l Hvarss case_shapes_p Hinc.
    generalize (m_list_inc_1 _ _ _ _ _ _ _ _ Hinc).
    intro h; elim h; clear h; intros h1 h2.
    subst; simpl.
    replace (ss[p|q]) with (ss[p|C]).
    rewrite case_shapes_p.
    TrivCase eq_Sigma_S_dec Bot_S.
    simpl; trivial.
    apply element_at_irrel.
  Qed. 

  Lemma Hvars_Sp_Top :  forall (n : nat) (ss : vector Sigma_S n) (w : nb_list n)
    (p : nat) (C : p < n) (a : (nat * Sigma_S)) (q : Q n Sigma_S a)
    (l : pred_list (nat * Sigma_S) (Q n Sigma_S)),
    Hvars n ss -> (pred_cons (Q n Sigma_S) a q l) INC 
    (m_cons (S p, Top_S) (lt_n_S p n C) m_nil) ->
    Hvars n (fst (propagate sup_S eq_Sigma_S_dec ss w (pred_cons (Q n Sigma_S) a q l))).
  Proof.
    intros n ss w p C a q l Hvarss Hinc.
    generalize (m_list_inc_1 _ _ _ _ _ _ _ _ Hinc).
    intro h; elim h; clear h; intros h1 h2.
    subst; simpl.
    CaseEq (ss[S p|q]).
    elim (eq_Sigma_S_dec Top_S Bot_S); intro h; [inversion h | clear h].
    simpl; intro dd; apply Hvars_replace_Top; trivial.
    TrivCase eq_Sigma_S_dec Top_S.
    simpl; trivial.
    intros l0 l1 case_shapes_Sp.
    elim (eq_Sigma_S_dec Top_S (Shapes l0 l1)); intro h; [inversion h | clear h].
    simpl; apply Hvars_replace_Top; trivial.
  Qed. 

  Lemma Hvars_Sp_Bot :  forall (n : nat) (ss : vector Sigma_S n) (w : nb_list n)
    (p : nat) (C : p < n) (a : (nat * Sigma_S)) (q : Q n Sigma_S a)
    (l : pred_list (nat * Sigma_S) (Q n Sigma_S)),
    Hvars n ss -> (pred_cons (Q n Sigma_S) a q l) INC 
    (m_cons (S p, Bot_S) (lt_n_S p n C) m_nil) ->
    Hvars n (fst (propagate sup_S eq_Sigma_S_dec ss w (pred_cons (Q n Sigma_S) a q l))).
  Proof.
    intros n ss w p C a q l Hvarss Hinc.
    generalize (m_list_inc_1 _ _ _ _ _ _ _ _ Hinc).
    intro h; elim h; clear h; intros h1 h2.
    subst; simpl.
    CaseEq (ss[S p|q]).
    TrivCase eq_Sigma_S_dec Bot_S.
    simpl; trivial.
    TrivCase eq_Sigma_S_dec Top_S.
    simpl; trivial.
    intros l l0; TrivCase eq_Sigma_S_dec (Shapes l l0).
    simpl; trivial.
  Qed. 

  Lemma Hvars_Shapes :  forall (n : nat) (ss : vector Sigma_S n) (w : nb_list n)
    (p : nat) (C : p < n) (a : (nat * Sigma_S)) (q : Q n Sigma_S a)
    (l : pred_list (nat * Sigma_S) (Q n Sigma_S)) (le : list Expression)
    (ls : Substitution),
    Hvars n ss -> ss [p | C] = Shapes ls le ->
    (pred_cons (Q n Sigma_S) a q l) INC 
    (m_cons (p, Top_S) (lt_trans p n (S n) C (lt_n_Sn n)) m_nil) ->
    Hvars n (fst (propagate sup_S eq_Sigma_S_dec ss w (pred_cons (Q n Sigma_S) a q l))).
  Proof.
    intros n ss w p C a q l le ls Hvarss case_shapes_p Hinc.
    generalize (m_list_inc_1 _ _ _ _ _ _ _ _ Hinc).
    intro h; elim h; clear h; intros h1 h2.
    subst; simpl.
    replace (ss[p|q]) with (ss[p|C]).
    rewrite case_shapes_p.
    elim (eq_Sigma_S_dec Top_S (Shapes ls le)); intro h; [inversion h | clear h; simpl]. 
    apply Hvars_replace_Top; trivial.
    apply element_at_irrel.
  Qed. 


  Lemma propa_shapes_hvars : forall (fcn : function) (Hin : In fcn functions) (ss : vector Sigma_S (fcn_size fcn)) 
    (w : nb_list (fcn_size fcn)) (p : nat) (C : p < fcn_size fcn) (l : m_list (fcn_size fcn) Sigma_S), 
    l INC (Step_S' fcn Hin p C (ss[p|C])) ->
    Hvars (fcn_size fcn) ss -> Hvars (fcn_size fcn) (fst (propagate_shapes fcn Hin ss w l)).
  Proof.
    intros fcn Hin ss w p C l Hinc Hvarsss.
    unfold Step_S' in Hinc; unfold step' in Hinc.
    cut (l INC (combine (Succs_aux (fcn_size fcn) (fcn_bytecode fcn) p C) 
      (Step_S fcn p C (ss[p|C])) (Step_S_Succs_aux_same_length fcn p C (ss[p|C])))).
    clear Hinc; unfold Step_S_Succs_aux_same_length; unfold Succs_aux; unfold Step_S.
    CaseEq ((fcn_bytecode fcn)[p|C]); simpl.
    Focus 1.
  (* return *)
    intro case_instr; destruct l; simpl.
    trivial.
    CaseEq (ss[p|C]); simpl.
  (* bot *)
    unfold propagate_shapes; apply Hvars_Bot_S; trivial.
  (* top *)
    unfold propagate_shapes; apply Hvars_Top_S; trivial.
  (* Shapes l0 l1 *)
    intros l0 l1 case_shapes_p.
    destruct l1.
  (* l1 = m_nil *)
    unfold propagate_shapes; apply (Hvars_Shapes (fcn_size fcn) ss w p C a q l nil l0); trivial.
  (* l1 = t :: l1 *)
    intro Hinc; generalize (m_list_inc_1 _ _ _ _ _ _ _ _ Hinc).
    intro h; elim h; clear h; intros h1 h2.
    subst.
    unfold propagate_shapes; simpl.
    replace (ss[p|q]) with (ss[p|C]).
    rewrite case_shapes_p.
    TrivCase eq_Substitution_dec l0.
    TrivCase eq_list_Expression_dec (t::l1).
    TrivCase eq_Sigma_S_dec (Shapes l0 (t :: l1)).
    simpl; trivial.
    apply element_at_irrel.

    Focus 1.
  (* stop *)
    intros case_instr Hinc; inversion Hinc.
    subst; destruct l; simpl; trivial.
    inversion H.

    Focus 1.
  (* load *)
    intros j case_instr; destruct l; simpl.
    trivial.
    CaseEq (ss[p|C]); simpl. 
    intro; unfold propagate_shapes; apply Hvars_Sp_Bot; trivial.
    intro; unfold propagate_shapes; apply Hvars_Sp_Top; trivial.
  (* Shapes l0 l1 *)
    intros l0 l1 case_shapes_p.
    CaseEq ((rev_lin l1)[j]).
    intros t case_t Hinc.
    generalize (m_list_inc_1 _ _ _ _ _ _ _ _ Hinc).
    intro h; elim h; clear h; intros h1 h2.
    subst.
    unfold propagate_shapes; simpl.
    CaseEq (ss[S p|q]).
    intro case_shapes_Sp.
    elim (eq_Sigma_S_dec  (Shapes l0 (t :: l1)) Bot_S); intro h; [inversion h | clear h; simpl].
    intros p0 C0 le ls case_shapes_p0.
    elim (eq_nat_dec (S p) p0); intro comp.
  (* S p = p 0 *)
    subst; rewrite (element_at_in_replaced) in case_shapes_p0.
    inversion case_shapes_p0.
    subst le ls.
    elim (Hvarsss p C l0 l1 case_shapes_p).
    intros Hvars1 Hvars2.
    cut (In t l1).
    intro Hint; split.
    intros e Hine; elim Hine; clear Hine; intro Hine.
    subst e.
    intros h p' Cp'; apply (Hvars1 t Hint h p').
    generalize Cp'; auto with arith.
    intros h p' Cp'; apply (Hvars1 e Hine h p').
    generalize Cp'; auto with arith.
    intros s Hins.
    intros h p' Cp'; apply (Hvars2 s Hins h p').
    generalize Cp'; auto with arith.
    cut (In t (rev l1)); [apply lists.In_rev | generalize case_t; rewrite rev_lin_is_rev; apply element_at_list_in].
  (* S p <> p 0 *)
    rewrite (element_at_in_replaced') in case_shapes_p0; trivial.
    apply (Hvarsss p0 C0 le ls case_shapes_p0).
    TrivCase eq_Sigma_S_dec Top_S.
    simpl; trivial.
    intros l l2 case_shapes_Sp.
    elim (eq_Substitution_dec  l0 l); intro case_l0_l.
    elim (eq_list_Expression_dec  (t :: l1) l2); intro case_tl1_l2.
    subst l l2.
    TrivCase eq_Sigma_S_dec  (Shapes l0 (t :: l1)).
    simpl; trivial.
    elim (eq_Sigma_S_dec  Top_S (Shapes l l2)); intro h; [inversion h | clear h].
    simpl; apply Hvars_replace_Top; trivial.
    elim (eq_Sigma_S_dec  Top_S (Shapes l l2)); intro h; [inversion h | clear h].
    simpl; apply Hvars_replace_Top; trivial.
  (* rev l [j] = None : *)
    intro; unfold propagate_shapes; apply Hvars_Sp_Top; trivial.

  (* call *)
    Focus 1.
    intros gnm gar case_instr. 
    destruct l; simpl.
    trivial.
    CaseEq (ss[p|C]).
  (* Bot_S *)
    intro; unfold propagate_shapes; apply Hvars_Sp_Bot; trivial.
  (* Top_S *)
    intro; unfold propagate_shapes; apply Hvars_Sp_Top; trivial.
  (* Shapes l0 l1 *)
    intros l0 l1 case_shapes_p.
    simpl; CaseEq (split_k_elements gar l1).
  (* some lk lr *)
    intro p0; destruct p0 as [lk lr].
    intros case_split Hinc.
    generalize (m_list_inc_1 _ _ _ _ _ _ _ _ Hinc).
    intro h; elim h; clear h; intros h1 h2; subst a l.
    unfold propagate_shapes; simpl.
    CaseEq (ss[S p|q]).
    intro case_shapes_Sp; elim (eq_Sigma_S_dec  (Shapes l0 (Node (symbol gnm) (rev_lin lk) :: lr)) Bot_S); intro h; [elim h; trivial | clear h].
    simpl; intros p0 C0 ls le case_shapes_p0.
    elim (eq_nat_dec (S p) p0); intro comp.
  (* S p = p0 *)
    subst p0; rewrite element_at_in_replaced in case_shapes_p0; inversion case_shapes_p0.
    subst ls le.
    elim (Hvarsss p C l0 l1 case_shapes_p).
    intros Hvars1 Hvars2.
    cut (l1 = lk ++ lr); [intro case_l1 | generalize case_split; apply split_k_elements_ok].
    split.
    intros e Hine; elim Hine; clear Hine; intro Hine.
    subst e.
    simpl; rewrite rev_lin_is_rev.
    intros h p' Cp'.
    cut (forall (e : Expression), In e lk -> var_not_in_tree e p' h).
    intro H; assert (H' : forall (e : Expression), In e (rev lk) -> var_in_tree_bool e p' h = false).
    intros e e_in_rev_lk. 
    assert (e_in_lk : In e lk).
    generalize e_in_rev_lk; apply lists.In_rev.
    generalize (H e e_in_lk); unfold var_not_in_tree; simpl; trivial.
    unfold var_not_in_tree.
    simpl; elim (fold_bool_or_false 
      (f:=fun (e : Expression) => var_in_tree_bool e p' h) (rev lk)); intros H1 H2. 
    apply H2; trivial.
    intros e Hine.
    cut (In e l1); [intro Hinel1 | rewrite case_l1; apply concat_In; left; trivial].
    apply Hvars1; trivial.
    generalize Cp'; auto with arith.
    cut (In e l1); [intro Hinel1 | rewrite case_l1; apply concat_In; right; trivial].
    intros h p' Cp'; apply Hvars1; trivial.
    generalize Cp'; auto with arith.
    intros s Hins.
    intros h p' Cp'; apply Hvars2; trivial.
    generalize Cp'; auto with arith.
  (* S p <> p0 *)
    rewrite element_at_in_replaced' in case_shapes_p0; trivial.
    apply (Hvarsss p0 C0 ls le case_shapes_p0).
    TrivCase eq_Sigma_S_dec Top_S.
    simpl; trivial.
    intros l l2 case_shapes_Sp.
    elim (eq_Substitution_dec l0 l); simpl; intro case_l_l0.
    elim (eq_list_Expression_dec (Node (symbol gnm) (rev_lin lk) :: lr) l2); simpl; intro case_l2.
    subst l l2.
    TrivCase eq_Sigma_S_dec (Shapes l0 (Node (symbol gnm) (rev_lin lk) :: lr)).
    simpl; trivial.
    elim (eq_Sigma_S_dec Top_S (Shapes l l2)); intro h; [inversion h | clear h].
    simpl; apply Hvars_replace_Top; trivial.
    elim (eq_Sigma_S_dec  Top_S (Shapes l l2)); intro h; [inversion h | clear h].
    simpl; apply Hvars_replace_Top; trivial.
  (* split = none  : *)
    intro case_split.
    unfold propagate_shapes; apply Hvars_Sp_Top; trivial.

    Focus 1.
  (* build *)
    intros cnm car case_instr.
    destruct l; simpl; trivial.
    CaseEq (ss[p|C]).
  (* Bot_S *)
    intro; unfold propagate_shapes; apply Hvars_Sp_Bot; trivial.
  (* Top_S *)
    intro; unfold propagate_shapes; apply Hvars_Sp_Top; trivial.
  (* shapes l0 l1 *)
    intros l0 l1 case_shapes_p.
    simpl; CaseEq (split_k_elements car l1).
  (* l1 = lk ++ lr *)
    intros p0 case_split; destruct p0 as [lk lr].
    intro Hinc; generalize (m_list_inc_1 _ _ _ _ _ _ _ _ Hinc).
    intro h; elim h; clear h; intros h1 h2; subst a l.
    unfold propagate_shapes; simpl.
    CaseEq (ss[S p|q]).
    intro case_shapes_Sp; elim (eq_Sigma_S_dec  (Shapes l0 (Node (symbol cnm) (rev_lin lk) :: lr)) Bot_S); intro h; [inversion h | clear h; simpl].
    intros p0 C0 ls le case_shapes_p0.
    elim (eq_nat_dec (S p) p0); intro comp.
  (* S p = p0 *)
    subst p0; rewrite element_at_in_replaced in case_shapes_p0; inversion case_shapes_p0.
    subst ls le.
    clear Hinc case_shapes_p0.
    elim (Hvarsss p C l0 l1 case_shapes_p); intros Hvars1 Hvars2.
    split.
    intros e Hine; elim Hine; clear Hine; intro Hine.
    intros h p' Cp'; cut (forall (e : Expression), In e lk -> var_not_in_tree e p' h).
    subst e.
    simpl.
    unfold var_not_in_tree; simpl.
    intro H; elim (fold_bool_or_false (f := fun (e : Expression) => var_in_tree_bool e p' h) (rev_lin lk)).
    intros H1 H2; apply H2.
    intros a Ha; apply H.
    generalize Ha; rewrite rev_lin_is_rev; apply lists.In_rev.
    clear Hine e.
    intros e Hine.
    cut (In e l1); [intro Hinel1 | idtac].
    apply Hvars1; trivial.
    generalize Cp'; auto with arith.
    replace l1 with (lk ++ lr).
    apply concat_In.
    left; trivial.
    symmetry; generalize case_split; apply split_k_elements_ok.
    cut (In e l1).
    intros Hinel1 h p' Cp'; apply Hvars1; trivial.
    generalize Cp'; auto with arith.
    replace l1 with (lk ++ lr).
    apply concat_In; right; trivial.
    symmetry; generalize case_split; apply split_k_elements_ok.
    intros s Hins.
    intros h p' Cp'; apply Hvars2; trivial.
    generalize Cp'; auto with arith.
    rewrite element_at_in_replaced' in case_shapes_p0; trivial.
    apply (Hvarsss p0 C0 ls le case_shapes_p0).
    TrivCase eq_Sigma_S_dec Top_S; trivial.
    intros l l2 case_shapes_Sp.
    elim (eq_Substitution_dec l0 l); intro case_l0_l.
    elim (eq_list_Expression_dec  (Node (symbol cnm) (rev_lin lk) :: lr) l2); intro case_l2.
    subst l2 l.
    TrivCase eq_Sigma_S_dec (Shapes l0 (Node (symbol cnm) (rev_lin lk) :: lr)); trivial.
    elim (eq_Sigma_S_dec  Top_S (Shapes l l2)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; trivial.
    elim (eq_Sigma_S_dec  Top_S (Shapes l l2)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; trivial.
  (* split = none *)
    intro case_split; unfold propagate_shapes; apply Hvars_Sp_Top; trivial.

  (* branch (arg!!!!) *)
    intros cnm j Cj case_instr.
    destruct l; simpl.
    trivial.
    generalize (fwd_jmp fcn Hin p C cnm j Cj case_instr).
    intro Cjp; CaseEq (ss[p|C]).

  (* Bot_S *)
    intros case_shapes_p Hinc.
    destruct l.
    cut (a = (j , Bot_S)).
    intro h; subst a; unfold propagate_shapes; simpl.
    CaseEq (ss[j|q]).
    TrivCase eq_Sigma_S_dec Bot_S;trivial.
    TrivCase eq_Sigma_S_dec Top_S; trivial. 
    intros l1 l2 case_shapes_j.
    TrivCase eq_Sigma_S_dec (Shapes l1 l2); trivial.
    inversion Hinc; subst.
    inversion H.
    inversion H1; subst.
    inversion H.
    trivial.
    inversion H2.
    subst; inversion H.
    generalize (m_list_inc_2 _ _ _ _ _ _ _ _ _ _ _ _ Hinc).
    intro h; elim h; clear h; intros h1 h2; elim h2; clear h2; intros h2 h3.
    subst a a0 l.
    unfold propagate_shapes; simpl.
    CaseEq (ss[S p|q]).
    intro case_shapes_Sp; TrivCase eq_Sigma_S_dec Bot_S; trivial. 
    CaseEq (ss[j|q0]).
    TrivCase eq_Sigma_S_dec Bot_S; trivial.
    TrivCase eq_Sigma_S_dec Top_S; trivial. 
    intros l l0 case_shapes_j.
    TrivCase eq_Sigma_S_dec (Shapes l l0); trivial.
    TrivCase eq_Sigma_S_dec Top_S; trivial. 
    intro case_shapes_Sp; CaseEq (ss[j|q0]).
    TrivCase eq_Sigma_S_dec Bot_S; trivial.
    TrivCase eq_Sigma_S_dec Top_S; trivial. 
    intros l l0 case_shapes_j.
    TrivCase eq_Sigma_S_dec (Shapes l l0); trivial.
    intros l l0 case_shapes_Sp.
    TrivCase eq_Sigma_S_dec (Shapes l l0); trivial.
    CaseEq (ss[j|q0]).
    TrivCase eq_Sigma_S_dec Bot_S; trivial.
    TrivCase eq_Sigma_S_dec Top_S; trivial. 
    intros l1 l2; TrivCase eq_Sigma_S_dec (Shapes l1 l2); trivial.
  (* Top_S *)
    intros case_shapes_p Hinc; destruct l.
    cut (a = (j, Top_S)).
    intro h; subst a.
    unfold propagate_shapes; simpl.
    CaseEq (ss[j|q]).
    elim (eq_Sigma_S_dec Top_S Bot_S); intro h; [inversion h | clear h; simpl].
    intro case_shapes_j; apply Hvars_replace_Top; trivial.
    TrivCase eq_Sigma_S_dec Top_S; trivial.
    intros l l0 case_shapes_j.
    elim (eq_Sigma_S_dec  Top_S (Shapes l l0)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; trivial.
    inversion Hinc.
    inversion H.
    subst; inversion H1.
    inversion H; trivial.
    subst; inversion H2.
    inversion H.

    generalize (m_list_inc_2 _ _ _ _ _ _ _ _ _ _ _ _ Hinc).
    intro h; elim h; clear h; intros h1 h2; elim h2; clear h2; intros h2 h3.
    subst a a0 l.
    unfold propagate_shapes; simpl.
    CaseEq (ss[S p|q]).
    intro case_shapes_Sp; elim (eq_Sigma_S_dec  Top_S Bot_S); intro h; [inversion h | clear h; simpl]. 
    elim (eq_nat_dec (S p) j); intro comp.
    subst j; rewrite element_at_in_replaced.
    TrivCase eq_Sigma_S_dec Top_S; trivial.
    simpl; apply Hvars_replace_Top; trivial.
    rewrite element_at_in_replaced'; trivial.
    CaseEq (ss[j|q0]).
    intro case_shapes_j; elim (eq_Sigma_S_dec  Top_S Bot_S); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; apply Hvars_replace_Top; trivial.
    TrivCase eq_Sigma_S_dec Top_S; trivial.
    simpl; intros case_shapes_j; apply Hvars_replace_Top; trivial.
    intros l l0 case_shapes_j.
    elim (eq_Sigma_S_dec  Top_S (Shapes l l0)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; apply Hvars_replace_Top; trivial.
    TrivCase eq_Sigma_S_dec Top_S; trivial.
    intro case_shapes_Sp; CaseEq (ss[j|q0]).
    elim (eq_Sigma_S_dec  Top_S Bot_S); intro h; [inversion h | clear h; simpl].
    intros case_shapes_j; apply Hvars_replace_Top; trivial.
    TrivCase eq_Sigma_S_dec Top_S; trivial.
    intros l l0 case_shapes_j; elim (eq_Sigma_S_dec  Top_S (Shapes l l0)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; trivial.
    intros l l0 case_shapes_Sp.
    elim (eq_Sigma_S_dec  Top_S (Shapes l l0)); intro h; [inversion h | clear h; simpl].
    elim (eq_nat_dec (S p) j); intro comp.
    subst j; rewrite element_at_in_replaced.
    TrivCase eq_Sigma_S_dec Top_S; trivial.
    simpl; apply Hvars_replace_Top; trivial.
    rewrite element_at_in_replaced'; trivial.
    CaseEq (ss[j|q0]).
    elim (eq_Sigma_S_dec  Top_S Bot_S); intro h; [inversion h | clear h; simpl].
    intros case_shapes_j; apply Hvars_replace_Top; apply Hvars_replace_Top; trivial.
    TrivCase eq_Sigma_S_dec Top_S; trivial.
    simpl; intros case_shapes_j; apply Hvars_replace_Top; trivial.
    intros l1 l2 case_shapes_j.
    elim (eq_Sigma_S_dec  Top_S (Shapes l1 l2)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; apply Hvars_replace_Top; trivial.

  (* shapes l0 l1 *)
    intros l0 l1 case_shapes_p.
    destruct l; simpl.
    destruct l1.
    intro Hinc; cut (a = (j, Top_S)).
    intro h; subst a; unfold propagate_shapes; simpl.
    CaseEq (ss[j|q]).
    elim (eq_Sigma_S_dec  Top_S Bot_S); intro h; [inversion h | clear h; simpl].
    intros case_shapes_j; apply Hvars_replace_Top; trivial.
    TrivCase eq_Sigma_S_dec Top_S; trivial.
    simpl; trivial.
    intros l l1 case_shapes_j; elim (eq_Sigma_S_dec  Top_S (Shapes l l1)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; trivial.
    inversion Hinc.
    subst; inversion H.
    inversion H1.
    inversion H3.
    trivial.
    inversion H5.
    inversion H7.

    destruct t.
    (* case t Leaf : *)
    
    intro Hinc; inversion Hinc.
    unfold propagate_shapes; simpl.
    inversion H; subst.
    elim (m_list_inc_1 _ _ _ _ _ _ _ _ H1); intros H3 H4; clear H1 H4.
    subst; unfold propagate_shapes; simpl.
    destruct (ss[j|q]).
    elim (eq_Sigma_S_dec Top_S Bot_S); intro case; [inversion case | simpl; apply Hvars_replace_Top]; trivial.
    TrivCase eq_Sigma_S_dec Top_S.
    simpl; trivial.
    elim (eq_Sigma_S_dec Top_S (Shapes l l2)); intro case; [inversion case | simpl; apply Hvars_replace_Top]; trivial.
    (* case t node : *)
    destruct n.
    (* case n variable : *)
    destruct l.
    CaseEq (Get_constr cnm).
    intros c case_s Hinc.
    cut (a = (j, Shapes l0 (Node (x n n0) nil :: l1))).
    intros h; subst a.
    unfold propagate_shapes; simpl.
    CaseEq (ss[j|q]).
    elim (eq_Sigma_S_dec  (Shapes l0 (Node (x n n0) nil :: l1)) Bot_S); intro h; [inversion h | clear h; simpl].
    intros case_shapes_j p0 C0 ls le case_shapes_p0.
    elim (eq_nat_dec j p0); intro comp.
    subst j; rewrite element_at_in_replaced in case_shapes_p0; inversion case_shapes_p0.
    subst ls le; simpl.
    clear Hinc case_shapes_p0.
    elim (Hvarsss p C l0 (Node (x n n0) nil :: l1) case_shapes_p).
    intros Hvars1 Hvars2.
    split.
    intros e Hine h p' Cp'; apply Hvars1.
    simpl; trivial.
    generalize Cp' Cjp; apply gt_trans.
    intros s Hins h p' Cp'; apply Hvars2; simpl; trivial.
    generalize Cp' Cjp ; apply gt_trans.
    rewrite element_at_in_replaced' in case_shapes_p0; trivial.
    apply (Hvarsss p0 C0 ls le case_shapes_p0).
    TrivCase eq_Sigma_S_dec Top_S; simpl; trivial.
    intros l l2 case_shapes_j.
    elim (eq_Substitution_dec  l0 l); intro case_l0. 
    elim (eq_list_Expression_dec  (Node (x n n0) nil :: l1) l2); intro case_l2.
    subst l l2.
    TrivCase eq_Sigma_S_dec (Shapes l0 (Node (x n n0) nil :: l1)); simpl; trivial.
    elim (eq_Sigma_S_dec  Top_S (Shapes l l2)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; trivial.
    elim (eq_Sigma_S_dec  Top_S (Shapes l l2)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; trivial.
    inversion Hinc.
    subst; inversion H.
    inversion H1.
    inversion H3.
    trivial.
    inversion H5.
    inversion H7.
    intros dd Hinc; unfold propagate_shapes; simpl.
    cut (a = (j, Top_S)).
    intro h; subst a; simpl.
    CaseEq (ss[j|q]).
    elim (eq_Sigma_S_dec  Top_S Bot_S); intro h; [inversion h | clear h; simpl].
    intro case_shapes_j; apply Hvars_replace_Top; trivial.
    TrivCase eq_Sigma_S_dec Top_S; simpl; trivial.
    intros l l2 case_shapes_j.
    elim (eq_Sigma_S_dec  Top_S (Shapes l l2)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; trivial.
    inversion Hinc.
    inversion H.
    inversion H1.
    inversion H3.
    trivial.
    inversion H5.
    inversion H7.
    intro Hinc; cut (a = (j, Top_S)).
    intro h; subst a; unfold propagate_shapes; simpl.
    replace (match ss [j | q] with | Bot_S => Top_S | Top_S => Top_S | Shapes _ _ => Top_S end) with (Top_S).
    elim (eq_Sigma_S_dec Top_S (ss [j | q])); simpl; trivial.
    intro; apply Hvars_replace_Top; trivial.    
    destruct (ss[j|q]); trivial.
    inversion Hinc.
    subst; inversion H.
    inversion H1.
    subst; inversion H3; trivial.
    inversion H5.
    inversion H7.
    (* case n name : *)
    elim (eq_name_dec cnm n); intro case_cnm.
  (* cnm = n *)
    subst n; intro Hinc; cut (a = (j, Bot_S)).
    intro h; subst a; unfold propagate_shapes; simpl.
    replace (match ss [j|q] with | Bot_S => ss [j|q] | Top_S => Top_S | Shapes _ _ => ss [j|q] end) with (ss[j|q]).
    TrivCase eq_Sigma_S_dec (ss [j | q]); simpl; trivial.
    destruct (ss[j|q]); trivial.
    inversion Hinc.
    subst; inversion H.
    inversion H1.
    subst; inversion H3; trivial.
    inversion H5.
    inversion H7.
  (* cnm <> n *)
    intro Hinc; cut (a = (j, Shapes l0 (Node (symbol n) l :: l1))).
    intro; subst a; unfold propagate_shapes; simpl.
    CaseEq (ss[j|q]).

    elim (eq_Sigma_S_dec (Shapes l0 (Node (symbol n) l :: l1)) Bot_S); intro h; [inversion h | clear h; simpl].
    intros case_shapes_j p0 C0 ls le case_shapes_p0.
    elim (eq_nat_dec j p0); intro comp.
    subst j; rewrite element_at_in_replaced in case_shapes_p0.
    inversion case_shapes_p0; subst le ls.
    clear Hinc case_shapes_p0.
    elim (Hvarsss p C l0 (Node (symbol n) l :: l1) case_shapes_p); intros Hvars1 Hvars2.
    split.
    intros e Hine h p' Cp'; apply (Hvars1 e Hine h p'); trivial.
    apply gt_trans with (m := p0); trivial.
    intros s Hins h p' Cp'; apply (Hvars2 s Hins h p'); trivial.
    apply gt_trans with (m := p0); trivial.
    rewrite element_at_in_replaced' in case_shapes_p0; trivial.
    apply (Hvarsss p0 C0 ls le case_shapes_p0).
    TrivCase eq_Sigma_S_dec Top_S; simpl; trivial.

    intros l3 l2 case_shapes_j.
    elim (eq_Substitution_dec  l0 l3); intro case_l0.
    elim (eq_list_Expression_dec  (Node (symbol n) l :: l1) l2); intro case_l2.
    subst l3 l2.
    TrivCase eq_Sigma_S_dec (Shapes l0 (Node (symbol n) l :: l1)); simpl; trivial.
    elim (eq_Sigma_S_dec  Top_S (Shapes l3 l2)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; trivial.
    elim (eq_Sigma_S_dec  Top_S (Shapes l3 l2)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; trivial.
    inversion Hinc.
    subst; inversion H.
    inversion H1.
    subst; inversion H3; trivial.
    inversion H5.
    inversion H7.
  (* case a a0 l *)
    destruct l1.
    intro Hinc; generalize (m_list_inc_2 _ _ _ _ _ _ _ _ _ _ _ _ Hinc); clear Hinc.
    intro h; elim h; clear h; intros h1 h2; elim h2; clear h2; intros h2 h3; subst a a0 l.
    unfold propagate_shapes; simpl.
    replace (match ss [S p|q] with | Bot_S => Top_S | Top_S => Top_S | Shapes _ _ => Top_S end) with (Top_S).
    CaseEq (ss[S p|q]).
    elim (eq_Sigma_S_dec  Top_S Bot_S); intro h; [inversion h | clear h; simpl].
    elim (eq_nat_dec (S p) j); intro comp.
    subst j; rewrite element_at_in_replaced.
    TrivCase eq_Sigma_S_dec Top_S; simpl; trivial.
    intros case_shapes_Sp; apply Hvars_replace_Top; trivial.
    rewrite (element_at_in_replaced'); trivial.
    replace (match ss [j | q0] with | Bot_S => Top_S | Top_S => Top_S | Shapes _ _ => Top_S end) with (Top_S).
    CaseEq (ss[j|q0]).
    elim (eq_Sigma_S_dec Top_S Bot_S); intro h; [inversion h | clear h; simpl].
    intros case_shapes_j case_shapes_Sp; apply Hvars_replace_Top; apply Hvars_replace_Top; trivial.
    TrivCase eq_Sigma_S_dec Top_S; simpl; trivial.
    intros case_shapes_j case_shapes_Sp; apply Hvars_replace_Top; trivial.
    intros l l1 case_shapes_j case_shapes_Sp.
    elim (eq_Sigma_S_dec  Top_S (Shapes l l1)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; apply Hvars_replace_Top; trivial.
    TrivCase eq_Sigma_S_dec Top_S; simpl; trivial.
    destruct (ss[j|q0]); trivial.
    replace (match ss [j | q0] with | Bot_S => Top_S | Top_S => Top_S | Shapes _ _ => Top_S end) with (Top_S).
    replace (match (ss[S p <- Top_S]) [j | q0] with | Bot_S => Top_S | Top_S => Top_S | Shapes _ _ => Top_S end) with (Top_S).
    TrivCase eq_Sigma_S_dec Top_S; simpl; trivial.
    elim (eq_Sigma_S_dec Top_S (ss[j|q0])); intro h; simpl;[idtac| intros; apply Hvars_replace_Top]; trivial.
    destruct ((ss [S p <- Top_S]) [j | q0]); trivial.
    destruct (ss[j | q0]); trivial.
    intros l l1 case_shapes_Sp.
    replace (match ss [j | q0] with | Bot_S => Top_S | Top_S => Top_S | Shapes _ _ => Top_S end) with (Top_S).
    replace (match (ss[S p <- Top_S]) [j | q0] with | Bot_S => Top_S | Top_S => Top_S | Shapes _ _ => Top_S end) with (Top_S).
    elim (eq_Sigma_S_dec  Top_S (Shapes l l1)); intro h; [inversion h | clear h; simpl].
    elim (eq_Sigma_S_dec Top_S ((ss [S p <- Top_S]) [j | q0])); intro case; simpl; apply Hvars_replace_Top; trivial.
    apply Hvars_replace_Top; trivial.
    destruct ((ss [S p <- Top_S]) [j | q0]); trivial.
    destruct (ss[j | q0]); trivial.
    destruct (ss [S p | q]); trivial.

    destruct t.
    (* case t Leaf : *)
    intro Hinc; generalize (m_list_inc_2 _ _ _ _ _ _ _ _ _ _ _ _ Hinc); clear Hinc.
    intro h; elim h; clear h; intros h1 h2; elim h2; clear h2; intros h2 h3; subst a a0 l.
    unfold propagate_shapes; simpl.
    replace (match ss [S p|q] with | Bot_S => Top_S | Top_S => Top_S | Shapes _ _ => Top_S end) with (Top_S).
    replace (match ss [j | q0] with | Bot_S => Top_S | Top_S => Top_S | Shapes _ _ => Top_S end) with (Top_S).
    replace (match (ss[S p <- Top_S]) [j | q0] with | Bot_S => Top_S | Top_S => Top_S | Shapes _ _ => Top_S end) with (Top_S).
    elim (eq_Sigma_S_dec Top_S (ss [S p | q])); intro.
    elim (eq_Sigma_S_dec Top_S (ss [j | q0])); simpl; trivial.
    intro; apply Hvars_replace_Top; trivial.
    elim (eq_Sigma_S_dec Top_S ((ss [S p <- Top_S]) [j | q0])); simpl; intro; apply Hvars_replace_Top; trivial.
    apply Hvars_replace_Top; trivial.
    destruct ((ss [S p <- Top_S]) [j | q0]); trivial.
    destruct (ss[j | q0]); trivial.
    destruct (ss [S p | q]); trivial.

    destruct n.
    (* case n var : *)
    destruct l2.
    destruct (Get_constr cnm).
    intro Hinc; generalize (m_list_inc_2 _ _ _ _ _ _ _ _ _ _ _ _ Hinc); clear Hinc.
    intro h; elim h; clear h; intros h1 h2; elim h2; clear h2; intros h2 h3; subst a a0 l.
    unfold propagate_shapes; simpl.
    CaseEq (ss[S p|q]).
    elim (eq_Sigma_S_dec (Shapes (mksubst n n0 (Node (symbol cnm) (fresh (S p) (S (length l1)) (length (cons_args c)))) :: l0)
      (push_list (fresh (S p) (S (length l1)) (length (cons_args c))) 
        (map (apply_elem_tree (mksubst n n0 (Node (symbol cnm) (fresh (S p) (S (length l1)) (length (cons_args c)))))) l1))) 
    Bot_S); intro h; [inversion h | clear h; simpl].
    elim (eq_nat_dec (S p) j); intro comp.
    (* case (S p = j) *)
    subst j; rewrite element_at_in_replaced.
    elim (eq_Substitution_dec l0 
      (mksubst n n0 (Node (symbol cnm) (fresh (S p) (S (length l1)) (length (cons_args c)))) :: l0)); intro case_l0.
    cut (False); [intro F; inversion F | generalize case_l0].
    apply tail_neq.
    elim (eq_Sigma_S_dec Top_S (Shapes (mksubst n n0 (Node (symbol cnm) (fresh (S p) (S (length l1)) (length (cons_args c)))) 
      :: l0) 
    (push_list (fresh (S p) (S (length l1)) (length (cons_args c))) 
      (map (apply_elem_tree (mksubst n n0 (Node (symbol cnm) (fresh (S p) (S (length l1)) (length (cons_args c)))))) l1)))); 
    intro h; [inversion h | clear h; simpl].
    rewrite overwrite_replace.
    intros case_shapes_Sp; apply Hvars_replace_Top; trivial. 
    (* case Sp <> j *)
    rewrite element_at_in_replaced'; trivial.
    CaseEq (ss[j|q0]).
    elim (eq_Sigma_S_dec  (Shapes l0 (Node (x n n0) nil :: l1)) Bot_S); intro h;
      [inversion h | clear h; simpl].
    intros case_shapes_j case_shapes_Sp p0 C0 ls le case_shapes_p0.
    elim (eq_nat_dec j p0); intro comp2.
    subst j; rewrite element_at_in_replaced in case_shapes_p0; inversion case_shapes_p0.
    subst le ls; elim (Hvarsss p C l0 (Node (x n n0) nil :: l1) case_shapes_p); intros Hvars1 Hvars2.
    split.
    intros e Hine h p' Cp'; apply Hvars1; trivial.
    apply gt_trans with (m := p0); trivial.
    intros s Hins h p' Cp'; apply Hvars2; trivial.
    apply gt_trans with (m := p0); trivial.
    rewrite element_at_in_replaced' in case_shapes_p0; trivial.
    elim (eq_nat_dec (S p) p0); intro comp3.
    subst p0; rewrite element_at_in_replaced in case_shapes_p0; inversion case_shapes_p0.
    subst le ls; elim (Hvarsss p C l0 (Node (x n n0) nil :: l1) case_shapes_p); intros Hvars1 Hvars2.
    split.
    rewrite push_list_is_app_rev.
    intros e Hine.
    elim (In_concat _ _ _ _ Hine); clear Hine; intro Hine.
    intros h p' Cp'; generalize Hine; rewrite <- rev_lin_is_rev; apply In_fresh; trivial.
    elim (In_mapped _ _ _ l1 e Hine).
    intros e' He'; elim He'; clear He'; intros He'1 He'2.
    intros h p' Cp'.
    rewrite He'2.
    apply var_in_apply_elem_tree_aux2.
    apply Hvars1; trivial.
    right; assumption.
    generalize Cp'; auto with arith.
    unfold var_not_in_tree; simpl.
    elim (fold_bool_or_false (f := fun (e : Expression) => var_in_tree_bool e p' h) (fresh (S p) (S (length l1)) (length (cons_args c)))); intros H1 H2.
    apply H2; clear H1 H2.
    intros a Ha; apply (In_fresh a (length (cons_args c)) (S p) (S (length l1)) h p'); trivial.
    rewrite rev_lin_is_rev; rewrite <- (rev_involutive (fresh (S p) (S (length l1)) (length (cons_args c)))) in Ha.
    generalize Ha; apply lists.In_rev.
    intros s Hins; elim Hins; clear Hins; intros Hins.
    cut (forall h p' : nat, p' > p -> var_not_in_tree (Node (x n n0) nil) p' h).
    intros Hvars1' h p' Cp'; subst s; simpl.
    intro F; elim F; clear F; intro F.
    assert (F2 : fold_left
        (fun (p : bool) (e : Expression) => p || var_in_tree_bool e p' h)
        (fresh (S p) (S (length l1)) (length (cons_args c))) false = false).
    (* proof of F2 : *)
    elim (fold_bool_or_false (f := fun (e : Expression) => var_in_tree_bool e p' h) (fresh (S p) (S (length l1)) (length (cons_args c)))); intros H1 H2.
    apply H2; clear H1 H2.
    intros a Ha; apply (In_fresh a (length (cons_args c)) (S p) (S (length l1)) h p'); trivial.
    rewrite rev_lin_is_rev; rewrite <- (rev_involutive (fresh (S p) (S (length l1)) (length (cons_args c)))) in Ha.
    generalize Ha; apply lists.In_rev.
    (* F2 prooved *)
    rewrite F in F2; inversion F2.
    elim F; clear F; intros dd ddd; subst p' h.
    cut (In (Node (x n n0) nil) (Node (x n n0) nil :: l1)); [intro Hine | left; trivial].
    cut (n > p); [intro Cn | generalize Cp'; auto with arith].
    generalize (Hvars1 _ Hine n0 n Cn).
    unfold var_not_in_tree; simpl.
    elim (eq_nat_dec n n); intro case; [clear case | elim case; trivial].
    elim (eq_nat_dec n0 n0); intro case; [clear case | elim case; trivial].
    simpl; intro F; inversion F.
    apply Hvars1; trivial.
    left; trivial.
    intros h p' Cp'; apply Hvars2; trivial.
    auto with arith.
    rewrite element_at_in_replaced' in case_shapes_p0; trivial.
    apply (Hvarsss p0 C0 ls le case_shapes_p0).

    TrivCase eq_Sigma_S_dec Top_S; simpl; trivial.
    intros case_shapes_j case_shapes_Sp p0 C0 ls le case_shapes_p0.
    elim (eq_nat_dec (S p) p0); intro comp2.
    subst p0; rewrite element_at_in_replaced in case_shapes_p0.
    inversion case_shapes_p0.

    subst le ls; elim (Hvarsss p C l0 (Node (x n n0) nil :: l1) case_shapes_p); intros Hvars1 Hvars2.
    split.
    rewrite push_list_is_app_rev; intros e Hine.
    elim (In_concat _ _ _ _ Hine); clear Hine; intro Hine.
    intros h p' Cp';  generalize Hine; rewrite <- rev_lin_is_rev; apply In_fresh; trivial.
    elim (In_mapped _ _ _ l1 e Hine).
    intros e' He'; elim He'; clear He'; intros He'1 He'2.
    intros h p' Cp'; rewrite He'2.
    cut (In e' (Node (x n n0) nil :: l1)); [intro Hine' | right; trivial].
    cut (p'>p); [intro C' | generalize Cp'; auto with arith].
    apply var_in_apply_elem_tree_aux2; trivial.
    apply (Hvars1 e' Hine' h p' C').
    unfold var_not_in_tree; simpl.
    elim (fold_bool_or_false (f := fun (e: Expression) => var_in_tree_bool e p' h) (fresh (S p) (S (length l1)) (length (cons_args c)))); intros H1 H2.
    apply H2; clear H1 H2.
    intros a Ha; apply (In_fresh a (length (cons_args c)) (S p) (S (length l1)) h p' Cp').
    rewrite rev_lin_is_rev; apply lists.In_rev; rewrite rev_involutive; trivial.

    intros s Hins; elim Hins; clear Hins; intros Hins.
    cut (forall h p' : nat, p' > p -> var_not_in_tree (Node (x n n0) nil) p' h).
    intro Hvars1'.
    intros h p' Cp'; subst s; simpl.
    intro F; elim F; clear F; intro F.
    elim (fold_bool_or_true (f:= fun (e : Expression) => var_in_tree_bool e p' h) 
      (fresh (S p) (S (length l1)) (length (cons_args c)))); intros H1 H2.
    elim (H1 F); intros a Ha; elim Ha; clear Ha H1 H2 F; intros Ha1 Ha2.
    cut (var_in_tree_bool a p' h = false).
    intro H; rewrite H in Ha2; inversion Ha2.
    apply (In_fresh a (length (cons_args c)) (S p) (S (length l1)) h p' Cp').
    rewrite rev_lin_is_rev; apply lists.In_rev; rewrite rev_involutive; trivial.

    elim F; clear F; intros; subst p' h.
    cut (n > p); [intro Cn | generalize Cp'; auto with arith].
    generalize (Hvars1' n0 n Cn); unfold var_not_in_tree.
    simpl; TrivCase eq_nat_dec n; TrivCase eq_nat_dec n0.
    simpl; intro F; inversion F.
    intros h p' Cp'; apply Hvars1; trivial.
    left; trivial.
    intros h p' Cp'; apply Hvars2; trivial.
    generalize Cp'; auto with arith.
    rewrite element_at_in_replaced' in case_shapes_p0; trivial.
    apply (Hvarsss p0 C0 ls le case_shapes_p0).

    intros l l2 case_shapes_j case_shapes_Sp; elim (eq_Substitution_dec  l0 l); intro case_l.
    elim (eq_list_Expression_dec  (Node (x n n0) nil :: l1) l2); intro case_l2.
    subst l l2.
    TrivCase eq_Sigma_S_dec (Shapes l0 (Node (x n n0) nil :: l1)); simpl.
    intros p0 C0 ls le case_shapes_p0.
    elim (eq_nat_dec (S p) p0); intro comp2.
    subst p0;  rewrite element_at_in_replaced in case_shapes_p0; inversion case_shapes_p0.
    subst le ls; elim (Hvarsss p C l0 (Node (x n n0) nil :: l1) case_shapes_p); intros Hvars1 Hvars2.
    split.
    rewrite push_list_is_app_rev; intros e Hine.
    elim (In_concat _ _ _ _ Hine); clear Hine; intro Hine.
    intros h p' Cp'; generalize Hine; rewrite <- rev_lin_is_rev; apply In_fresh; trivial.
    elim (In_mapped _ _ _ l1 e Hine).
    intros e' He'; elim He'; clear He'; intros He'1 He'2.
    intros h p' Cp'; subst e; apply var_in_apply_elem_tree_aux2.
    apply Hvars1; trivial.
    right; assumption.
    generalize Cp'; auto with arith.
    unfold var_not_in_tree; simpl.
    elim (fold_bool_or_false (f := fun (e : Expression) => var_in_tree_bool e p' h) (fresh (S p) (S (length l1)) (length (cons_args c)))); intros H1 H2.
    apply H2; clear H1 H2.
    intros a Ha; apply (In_fresh a (length (cons_args c)) (S p) (S (length l1)) h p'); trivial.
    rewrite rev_lin_is_rev; rewrite <- (rev_involutive (fresh (S p) (S (length l1)) (length (cons_args c)))) in Ha.
    generalize Ha; apply lists.In_rev.

    intros s Hins; elim Hins; clear Hins; intros Hins.
    intros h p' Cp'; subst s; simpl.
    intro F; elim F; clear F; intro F.
    elim (fold_bool_or_true (f := fun (e : Expression) => var_in_tree_bool e p' h) (fresh (S p) (S (length l1)) (length (cons_args c)))); intros H1 H2.
    elim (H1 F); intros a Ha; elim Ha; clear Ha H1 H2; intros Ha1 Ha2.
    cut (In a (rev_lin (fresh (S p) (S (length l1)) (length (cons_args c))))).
    intro dd; generalize (In_fresh a (length (cons_args c)) (S p) (S (length l1)) h p' Cp' dd); clear dd.
    unfold var_not_in_tree; rewrite Ha2; intro F2; inversion F2.
    rewrite rev_lin_is_rev; apply lists.In_rev; rewrite rev_involutive; trivial.
    cut (In (Node (x n n0) nil) (Node (x n n0) nil :: l1)).
    elim F; clear F; intros F1 F2; subst p' h.
    cut (n>p); [intro Cp'2|auto with arith].
    intro Hin'; generalize (Hvars1 _ Hin' n0 n Cp'2).
    unfold var_not_in_tree; simpl.
    TrivCase eq_nat_dec n; TrivCase eq_nat_dec n0.
    simpl; intro F; inversion F. 
    left; trivial.
    intros; apply Hvars2; trivial.
    auto with arith.

    simpl in case_shapes_p0; rewrite element_at_in_replaced' in case_shapes_p0; trivial.
    apply (Hvarsss p0 C0 ls le case_shapes_p0).

    elim (eq_Sigma_S_dec  Top_S (Shapes l l2)); intro h; [inversion h | clear h; simpl].
    subst l; intros p0 C0 ls le case_shapes_p0.
    elim (eq_nat_dec j p0); intro comp2.
    subst p0; rewrite element_at_in_replaced in case_shapes_p0.
    inversion case_shapes_p0.
    rewrite element_at_in_replaced' in case_shapes_p0; trivial.
    elim (eq_nat_dec (S p) p0); intro comp3.
    subst p0; rewrite element_at_in_replaced in case_shapes_p0.
    inversion case_shapes_p0.
    subst le ls; elim (Hvarsss p C l0 (Node (x n n0) nil :: l1) case_shapes_p); intros Hvars1 Hvars2.
    split.
    rewrite push_list_is_app_rev.
    intros e Hine.
    elim (In_concat _ _ _ _ Hine); clear Hine; intro Hine.
    intros h p' Cp'; generalize Hine; rewrite <- rev_lin_is_rev; apply In_fresh; trivial.
    elim (In_mapped _ _ _ l1 e Hine).
    intros e' He'; elim He'; clear He'; intros He'1 He'2.
    intros h p' Cp'.
    subst e; apply var_in_apply_elem_tree_aux2.
    apply Hvars1; trivial; auto with arith.
    right; assumption.
    unfold var_not_in_tree; simpl.    
    elim (fold_bool_or_false (f:= fun (e : Expression) => var_in_tree_bool e p' h) 
      (fresh (S p) (S (length l1)) (length (cons_args c)))); intros H1 H2.
    apply H2; clear H1 H2.
    intros a Ha; apply (In_fresh a (length (cons_args c)) (S p) (S (length l1)) h p' Cp').
    rewrite rev_lin_is_rev; apply lists.In_rev; rewrite rev_involutive; trivial.

    intros s Hins; elim Hins; clear Hins; intros Hins.
    cut (forall h p' : nat, p' > p -> var_not_in_tree (Node (x n n0) nil) p' h).
    intro Hvars1'.
    intros h p' Cp'; subst s; simpl.
    intro F; elim F; clear F; intro F.
    elim (fold_bool_or_true (f:= fun (e : Expression) => var_in_tree_bool e p' h) 
      (fresh (S p) (S (length l1)) (length (cons_args c)))); intros H1 H2.
    elim (H1 F); intros a Ha; elim Ha; clear Ha H1 H2 F; intros Ha1 Ha2.
    cut (var_in_tree_bool a p' h = false).
    intro H; rewrite H in Ha2; inversion Ha2.
    apply (In_fresh a (length (cons_args c)) (S p) (S (length l1)) h p' Cp').
    rewrite rev_lin_is_rev; apply lists.In_rev; rewrite rev_involutive; trivial.
    elim F; clear F; intros; subst p' h.
    cut (n > p); [intro Cn | generalize Cp'; auto with arith].
    generalize (Hvars1' n0 n Cn); unfold var_not_in_tree.
    simpl; TrivCase eq_nat_dec n; TrivCase eq_nat_dec n0.
    simpl; intro F; inversion F.
    intros h p' Cp'; apply Hvars1; trivial.
    left; trivial.
    intros h p' Cp'; apply Hvars2; trivial.
    generalize Cp'; auto with arith.

    rewrite element_at_in_replaced' in case_shapes_p0; trivial.
    apply (Hvarsss p0 C0 ls le case_shapes_p0).
    elim (eq_Sigma_S_dec  Top_S (Shapes l l2)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top.
    intros p0 C0 ls le case_shapes_p0.
    elim (eq_nat_dec (S p) p0); intro comp3.
    subst p0; rewrite element_at_in_replaced in case_shapes_p0.
    inversion case_shapes_p0.
    subst le ls; elim (Hvarsss p C l0 (Node (x n n0) nil :: l1) case_shapes_p); intros Hvars1 Hvars2.
    split.
    rewrite push_list_is_app_rev; intros e Hine.
    elim (In_concat _ _ _ _ Hine); clear Hine; intro Hine.
    intros h p' Cp'; generalize Hine; rewrite <- rev_lin_is_rev; apply In_fresh; trivial.
    elim (In_mapped _ _ _ l1 e Hine).
    intros e' He'; elim He'; clear He'; intros He'1 He'2.
    intros h p' Cp'; subst e; apply var_in_apply_elem_tree_aux2; trivial.
    cut (In e' (Node (x n n0) nil :: l1)); [intro Hine' | right; trivial].
    apply (Hvars1 e' Hine' h p'); trivial.
    apply gt_trans with (m := S p); trivial.
    auto with arith.
    unfold var_not_in_tree; simpl.
    elim (fold_bool_or_false (f := fun (e: Expression) => var_in_tree_bool e p' h) (fresh (S p) (S (length l1)) (length (cons_args c)))); intros H1 H2.
    apply H2; clear H1 H2.
    intros a Ha; apply (In_fresh a (length (cons_args c)) (S p) (S (length l1)) h p' Cp').
    rewrite rev_lin_is_rev; apply lists.In_rev; rewrite rev_involutive; trivial.

    intros s Hins; elim Hins; clear Hins; intros Hins.
    cut (forall h p' : nat, p' > p -> var_not_in_tree (Node (x n n0) nil) p' h).
    intro Hvars1'.
    intros h p' Cp'; subst s; simpl.
    intro F; elim F; clear F; intro F.
    elim (fold_bool_or_true (f:= fun (e : Expression) => var_in_tree_bool e p' h) 
      (fresh (S p) (S (length l1)) (length (cons_args c)))); intros H1 H2.
    elim (H1 F); intros a Ha; elim Ha; clear Ha H1 H2 F; intros Ha1 Ha2.
    cut (var_in_tree_bool a p' h = false).
    intro H; rewrite H in Ha2; inversion Ha2.
    apply (In_fresh a (length (cons_args c)) (S p) (S (length l1)) h p' Cp').
    rewrite rev_lin_is_rev; apply lists.In_rev; rewrite rev_involutive; trivial.
    elim F; clear F; intros; subst p' h.
    cut (n > p); [intro Cn | generalize Cp'; auto with arith].
    generalize (Hvars1' n0 n Cn); unfold var_not_in_tree.
    simpl; TrivCase eq_nat_dec n; TrivCase eq_nat_dec n0.
    simpl; intro F; inversion F.
    intros h p' Cp'; apply Hvars1; trivial.
    left; trivial.
    intros h p' Cp'; apply Hvars2; trivial.
    generalize Cp'; auto with arith.
    rewrite element_at_in_replaced' in case_shapes_p0; trivial.
    apply (Hvarsss p0 C0 ls le case_shapes_p0).

    TrivCase eq_Sigma_S_dec Top_S; simpl; trivial.
    intro case_shapes_Sp; CaseEq (ss[j|q0]).
    elim (eq_Sigma_S_dec  (Shapes l0 (Node (x n n0) nil :: l1)) Bot_S); intro h; [inversion h | clear h; simpl].
    intros case_shapes_j p0 C0 ls le case_shapes_p0.
    elim (eq_nat_dec j p0); intro comp.
    subst p0; rewrite element_at_in_replaced in case_shapes_p0.
    inversion case_shapes_p0; subst ls le.
    elim (Hvarsss p C l0 (Node (x n n0) nil :: l1) case_shapes_p); intros Hvars1 Hvars2.
    split.
    intros e Hine h p' Cp'; apply Hvars1; trivial.
    apply gt_trans with (m := j); trivial.
    intros s Hins h p' Cp'; apply Hvars2; trivial.
    apply gt_trans with (m := j); trivial.

    rewrite element_at_in_replaced' in case_shapes_p0; trivial.
    apply (Hvarsss p0 C0 ls le case_shapes_p0).

    TrivCase eq_Sigma_S_dec Top_S; trivial.

    intros l l2 case_shapes_j.
    elim (eq_Substitution_dec  l0 l); intro case_l.
    elim (eq_list_Expression_dec  (Node (x n n0) nil :: l1) l2); intro case_l2.
    subst l l2.
    TrivCase eq_Sigma_S_dec (Shapes l0 (Node (x n n0) nil :: l1)); simpl; trivial. 
    elim (eq_Sigma_S_dec  Top_S (Shapes l l2)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; trivial.
    elim (eq_Sigma_S_dec  Top_S (Shapes l l2)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; trivial.

    intros l l2 case_shapes_Sp.
    elim (eq_Substitution_dec (mksubst n n0 (Node (symbol cnm) (fresh (S p) (S (length l1)) (length (cons_args c)))) :: l0) l); intro case_l.
    elim (eq_list_Expression_dec (push_list (fresh (S p) (S (length l1)) (length (cons_args c))) 
      (map (apply_elem_tree (mksubst n n0 (Node (symbol cnm) (fresh (S p) (S (length l1)) (length (cons_args c)))))) l1)) l2); intro case_l2.

    subst l l2; TrivCase eq_Sigma_S_dec 
      (Shapes (mksubst n n0 (Node (symbol cnm) (fresh (S p) (S (length l1)) (length (cons_args c)))) :: l0) 
        (push_list (fresh (S p) (S (length l1)) (length (cons_args c))) 
          (map (apply_elem_tree (mksubst n n0 (Node (symbol cnm) (fresh (S p) (S (length l1)) (length (cons_args c)))))) l1))); 
      simpl; trivial.

    CaseEq (ss[j|q0]).
    elim (eq_Sigma_S_dec (Shapes l0 (Node (x n n0) nil :: l1)) Bot_S); intro h; [inversion h | simpl; clear h].
    intros case_shapes_j p0 C0 ls le case_shapes_p0.
    elim (eq_nat_dec j p0); intro comp.
    subst p0; rewrite element_at_in_replaced in case_shapes_p0; inversion case_shapes_p0.
    elim (Hvarsss p C l0 (Node (x n n0) nil :: l1) case_shapes_p); intros Hvars1 Hvars2.
    split.
    intros e Hine h p' Cp'; apply Hvars1; trivial.
    apply gt_trans with (m := j); trivial.
    subst ls.
    intros s Hins h p' Cp'; apply Hvars2; trivial.
    apply gt_trans with (m := j); trivial.
    rewrite element_at_in_replaced' in case_shapes_p0; trivial.
    apply (Hvarsss p0 C0 ls le case_shapes_p0).
    TrivCase eq_Sigma_S_dec Top_S; simpl; trivial.

    intros l l2 case_shapes_j.
    elim (eq_Substitution_dec l0 l); intro case_l.
    elim (eq_list_Expression_dec (Node (x n n0) nil :: l1) l2); intro case_l2.
    subst l l2.
    TrivCase eq_Sigma_S_dec (Shapes l0 (Node (x n n0) nil :: l1)); simpl; trivial.
    elim (eq_Sigma_S_dec  Top_S (Shapes l l2)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; trivial.
    elim (eq_Sigma_S_dec  Top_S (Shapes l l2)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; trivial.

    elim (eq_Sigma_S_dec Top_S (Shapes l l2)); intro h; [inversion h | clear h; simpl].
    elim (eq_nat_dec (S p) j); intro comp.
    subst j; rewrite element_at_in_replaced.
    TrivCase eq_Sigma_S_dec Top_S; simpl; trivial.
    apply Hvars_replace_Top; trivial.

    rewrite element_at_in_replaced'; trivial.
    CaseEq (ss[j|q0]).
    elim (eq_Sigma_S_dec  (Shapes l0 (Node (x n n0) nil :: l1)) Bot_S); intro h; [inversion h | clear h; simpl].
    intros case_shapes_j p0 C0 ls le case_shapes_p0; elim (eq_nat_dec j p0); intro comp2.
    subst p0; rewrite element_at_in_replaced in case_shapes_p0; inversion case_shapes_p0.
    elim (Hvarsss p C l0 (Node (x n n0) nil :: l1) case_shapes_p); intros Hvars1 Hvars2.
    split.
    intros e Hine h p' Cp'; apply Hvars1; trivial.
    apply gt_trans with (m := j); trivial.
    subst ls.
    intros s Hins h p' Cp'; apply Hvars2; trivial.
    apply gt_trans with (m := j); trivial.
    rewrite element_at_in_replaced' in case_shapes_p0; trivial.
    elim (eq_nat_dec (S p) p0); intro comp3.
    subst p0; rewrite element_at_in_replaced in case_shapes_p0; inversion case_shapes_p0.
    rewrite element_at_in_replaced' in case_shapes_p0; trivial.
    apply (Hvarsss p0 C0 ls le case_shapes_p0).
    TrivCase eq_Sigma_S_dec Top_S; simpl; trivial.
    intro; apply Hvars_replace_Top; trivial.

    intros l3 l4 case_shapes_j.
    elim (eq_Substitution_dec  l0 l3); intro case_l3.
    elim (eq_list_Expression_dec  (Node (x n n0) nil :: l1) l4); intro case_l4.
    subst l3 l4; simpl.
    TrivCase eq_Sigma_S_dec (Shapes l0 (Node (x n n0) nil :: l1)); simpl.
    apply Hvars_replace_Top; trivial.
    elim (eq_Sigma_S_dec  Top_S (Shapes l3 l4)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; apply Hvars_replace_Top; trivial.

    elim (eq_Sigma_S_dec  Top_S (Shapes l3 l4)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; apply Hvars_replace_Top; trivial.

    elim (eq_Sigma_S_dec  Top_S (Shapes l l2)); intro h; [inversion h | clear h].
    elim (eq_nat_dec (S p) j); intro comp.
    subst j; rewrite element_at_in_replaced.
    TrivCase eq_Sigma_S_dec Top_S; simpl; trivial.
    apply Hvars_replace_Top; trivial.
    rewrite element_at_in_replaced'; trivial.
    CaseEq (ss[j|q0]).
    elim (eq_Sigma_S_dec  (Shapes l0 (Node (x n n0) nil :: l1)) Bot_S); intro h; [inversion h | clear h; simpl].
    intros case_shapes_j p0 C0 ls le case_shapes_p0; elim (eq_nat_dec j p0); intro comp2.
    subst p0; rewrite element_at_in_replaced in case_shapes_p0; inversion case_shapes_p0.
    elim (Hvarsss p C l0 (Node (x n n0) nil :: l1) case_shapes_p); intros Hvars1 Hvars2.
    split.
    intros e Hine h p' Cp'; apply Hvars1; trivial.
    apply gt_trans with (m := j); trivial.
    subst ls.
    intros s Hins h p' Cp'; apply Hvars2; trivial.
    apply gt_trans with (m := j); trivial.
    rewrite element_at_in_replaced' in case_shapes_p0; trivial.
    elim (eq_nat_dec (S p) p0); intro comp3.
    subst p0; rewrite element_at_in_replaced in case_shapes_p0; inversion case_shapes_p0.
    rewrite element_at_in_replaced' in case_shapes_p0; trivial.
    apply (Hvarsss p0 C0 ls le case_shapes_p0).
    TrivCase eq_Sigma_S_dec Top_S; simpl; trivial.
    intro; apply Hvars_replace_Top; trivial.

    intros l3 l4 case_shapes_j.
    elim (eq_Substitution_dec  l0 l3); intro case_l3.
    elim (eq_list_Expression_dec  (Node (x n n0) nil :: l1) l4); intro case_l4.
    subst l3 l4; simpl.
    TrivCase eq_Sigma_S_dec (Shapes l0 (Node (x n n0) nil :: l1)); simpl.
    apply Hvars_replace_Top; trivial.
    elim (eq_Sigma_S_dec  Top_S (Shapes l3 l4)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; apply Hvars_replace_Top; trivial.

    elim (eq_Sigma_S_dec  Top_S (Shapes l3 l4)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; apply Hvars_replace_Top; trivial.
(* THERE *)
    intro Hinc; generalize (m_list_inc_2 _ _ _ _ _ _ _ _ _ _ _ _ Hinc); clear Hinc.
    intro h; elim h; clear h; intros h1 h; elim h; clear h; intros h2 h3; subst a a0 l.
    unfold propagate_shapes; simpl.
    replace (match ss [S p | q] with | Bot_S => Top_S | Top_S => Top_S | Shapes _ _ => Top_S end) with (Top_S).
    replace (match ss [j | q0] with | Bot_S => Top_S | Top_S => Top_S | Shapes _ _ => Top_S end) with (Top_S).
    replace (match (ss[S p<-Top_S]) [j | q0] with | Bot_S => Top_S | Top_S => Top_S | Shapes _ _ => Top_S end) with (Top_S).
    elim (eq_Sigma_S_dec Top_S (ss [S p | q])); intro case1.
    elim (eq_Sigma_S_dec Top_S (ss [j | q0])); simpl; trivial; intro; apply Hvars_replace_Top; trivial.
    elim (eq_Sigma_S_dec Top_S ((ss [S p <- Top_S]) [j | q0])); intro case2.
    simpl; intro; apply Hvars_replace_Top; trivial.
    simpl; intro; apply Hvars_replace_Top; apply Hvars_replace_Top; trivial.
    destruct ((ss [S p <- Top_S]) [j | q0]); trivial.
    destruct (ss [j | q0]); trivial.
    destruct ( ss [S p | q]); trivial.   

    intro Hinc; generalize (m_list_inc_2 _ _ _ _ _ _ _ _ _ _ _ _ Hinc); clear Hinc.
    intro h; elim h; clear h; intros h1 h; elim h; clear h; intros h2 h3; subst a a0 l.
    unfold propagate_shapes; simpl.
    replace (match ss [S p | q] with | Bot_S => Top_S | Top_S => Top_S | Shapes _ _ => Top_S end) with (Top_S).
    replace (match ss [j | q0] with | Bot_S => Top_S | Top_S => Top_S | Shapes _ _ => Top_S end) with (Top_S).
    replace (match (ss[S p<-Top_S]) [j | q0] with | Bot_S => Top_S | Top_S => Top_S | Shapes _ _ => Top_S end) with (Top_S).
    elim (eq_Sigma_S_dec Top_S (ss [S p | q])); intro case1.
    elim (eq_Sigma_S_dec Top_S (ss [j | q0])); simpl; trivial; intro; apply Hvars_replace_Top; trivial.
    elim (eq_Sigma_S_dec Top_S ((ss [S p <- Top_S]) [j | q0])); intro case2.
    simpl; intro; apply Hvars_replace_Top; trivial.
    simpl; intro; apply Hvars_replace_Top; apply Hvars_replace_Top; trivial.
    destruct ((ss [S p <- Top_S]) [j | q0]); trivial.
    destruct (ss [j | q0]); trivial.
    destruct ( ss [S p | q]); trivial.   

    elim (eq_name_dec cnm n); intro case_cnm.
    subst n; intro Hinc; generalize (m_list_inc_2 _ _ _ _ _ _ _ _ _ _ _ _ Hinc); clear Hinc.
    intro h; elim h; clear h; intros h1 h; elim h; clear h; intros h2 h3; subst a a0 l.
    unfold propagate_shapes; simpl.
    CaseEq (ss[S p|q]).
    elim (eq_Sigma_S_dec  (Shapes l0 (push_list l2 l1)) Bot_S); intro h; [inversion h | clear h; simpl].
    elim (eq_nat_dec (S p) j); intro comp.
    subst j; rewrite element_at_in_replaced.
    TrivCase eq_Sigma_S_dec  (Shapes l0 (push_list l2 l1)).
    intros case_shapes_Sp p0 C0 ls le case_shapes_p0.
    elim (eq_nat_dec (S p) p0); intro comp2.
    subst p0; simpl in case_shapes_p0; rewrite element_at_in_replaced in case_shapes_p0.
    inversion case_shapes_p0.
    elim (Hvarsss p C l0 (Node (symbol cnm) l2 :: l1) case_shapes_p); intros Hvars1 Hvars2.
    split.
    rewrite push_list_is_app_rev; intros e Hine.
    elim (In_concat _ _ _ _ Hine); clear Hine; intro Hine.

    intros h p' Cp'.
    cut (forall (h p' : nat), p' > p -> var_not_in_tree (Node (symbol cnm) l2) p' h).
    intro Hvars1'; elim (fold_bool_or_false (f:= fun (e : Expression) => var_in_tree_bool e p' h) l2); intros H2 H3.
    unfold var_not_in_tree; apply H2; clear H2 H3.
    unfold var_not_in_tree in Hvars1'; simpl in Hvars1'.
    apply Hvars1'; trivial.
    auto with arith.
    apply lists.In_rev; trivial.
    apply Hvars1; left; trivial.
    intros; apply Hvars1; try right; trivial.
    auto with arith.   
    
    subst ls; intros s Hins h p' Cp'; apply Hvars2; trivial.
    apply gt_trans with (m := S p); trivial.

    simpl in case_shapes_p0; rewrite element_at_in_replaced' in case_shapes_p0; trivial.
    apply (Hvarsss p0 C0 ls le case_shapes_p0).
    rewrite (element_at_in_replaced'); trivial.
    replace (match ss [j | q0] with | Bot_S => ss [j | q0] | Top_S => Top_S | Shapes _ _ => ss [j | q0] end) with (ss[j|q0]).
    TrivCase eq_Sigma_S_dec (ss[j|q0]); simpl.
    intros case_shapes_Sp p0 C0 ls le case_shapes_p0.
    elim (eq_nat_dec (S p) p0); intro comp2.
    subst p0; rewrite element_at_in_replaced in case_shapes_p0.
    inversion case_shapes_p0.
    elim (Hvarsss p C l0 (Node (symbol cnm) l2 :: l1) case_shapes_p); intros Hvars1 Hvars2.
    split.
    rewrite push_list_is_app_rev; intros e Hine.
    elim (In_concat _ _ _ _ Hine); clear Hine; intro Hine.
    intros h p' Cp'.
    cut (forall (h p' : nat), p' > p -> var_not_in_tree (Node (symbol cnm) l2) p' h).
    intro Hvars1'; elim (fold_bool_or_false (f:= fun (e : Expression) => var_in_tree_bool e p' h) l2); intros H2 H3.
    unfold var_not_in_tree; apply H2; clear H2 H3.
    unfold var_not_in_tree in Hvars1'; simpl in Hvars1'.
    apply Hvars1'; trivial.
    auto with arith.
    apply lists.In_rev; trivial.
    apply Hvars1; left; trivial.
    intros; apply Hvars1; try right; trivial.
    auto with arith.   

    subst ls; intros s Hins h p' Cp'; apply Hvars2; trivial.
    apply gt_trans with (m := S p); trivial.
    auto with arith.    

    rewrite element_at_in_replaced' in case_shapes_p0; trivial.
    apply (Hvarsss p0 C0 ls le case_shapes_p0).
    destruct (ss [j | q0]); trivial.

    TrivCase eq_Sigma_S_dec Top_S; simpl.
    replace (match ss [j | q0] with | Bot_S => ss [j | q0] | Top_S => Top_S | Shapes _ _ => ss [j | q0] end) with (ss[j|q0]).
    TrivCase eq_Sigma_S_dec (ss[j|q0]); simpl.
    trivial.
    destruct (ss [j | q0]); trivial.
    replace (match ss [j | q0] with | Bot_S => ss [j | q0] | Top_S => Top_S | Shapes _ _ => ss [j | q0] end) with (ss[j|q0]).

    intros l l3 case_shapes_Sp; elim (eq_Substitution_dec  l0 l); intro case_l.
    elim (eq_list_Expression_dec  (push_list l2 l1) l3); intro case_l2.
    subst l l3; TrivCase eq_Sigma_S_dec (Shapes l0 (push_list l2 l1)); simpl.
    TrivCase eq_Sigma_S_dec (ss[j|q0]).
    simpl; trivial.

    elim (eq_Sigma_S_dec  Top_S (Shapes l l3)); intro h; [inversion h | clear h; simpl].
    replace (match (ss [S p <- Top_S]) [j | q0] with
              | Bot_S => (ss [S p <- Top_S]) [j | q0]
              | Top_S => Top_S
              | Shapes _ _ => (ss [S p <- Top_S]) [j | q0]
              end) with ((ss [S p <- Top_S]) [j | q0]).
    TrivCase eq_Sigma_S_dec ((ss [S p <- Top_S]) [j | q0]).
    simpl; apply Hvars_replace_Top; trivial.
    destruct ((ss [S p <- Top_S]) [j | q0]); trivial.

    elim (eq_Sigma_S_dec  Top_S (Shapes l l3)); intro h; [inversion h | clear h; simpl].
    replace (match (ss [S p <- Top_S]) [j | q0] with
              | Bot_S => (ss [S p <- Top_S]) [j | q0]
              | Top_S => Top_S
              | Shapes _ _ => (ss [S p <- Top_S]) [j | q0]
              end) with ((ss [S p <- Top_S]) [j | q0]).
    TrivCase eq_Sigma_S_dec ((ss [S p <- Top_S]) [j | q0]).
    simpl; apply Hvars_replace_Top; trivial.
    destruct ((ss [S p <- Top_S]) [j | q0]); trivial.
    destruct (ss [j | q0]); trivial.

    intro Hinc; generalize (m_list_inc_2 _ _ _ _ _ _ _ _ _ _ _ _ Hinc); clear Hinc.
    intro h; elim h; clear h; intros h1 h; elim h; clear h; intros h2 h3; subst a a0 l.
    unfold propagate_shapes; simpl.
    replace (match ss [S p | q] with
              | Bot_S => ss [S p | q]
              | Top_S => Top_S
              | Shapes _ _ => ss [S p | q]
              end) with (ss [S p | q]).
    TrivCase eq_Sigma_S_dec (ss [S p | q]).

    destruct (ss[j|q0]).
    elim (eq_Sigma_S_dec  (Shapes l0 (Node (symbol n) l2 :: l1)) Bot_S); intro h; [inversion h | clear h; simpl].

    intros p0 C0 ls le case_shapes_p0.
    elim (eq_nat_dec j p0); intro comp2.
    subst p0; rewrite element_at_in_replaced in case_shapes_p0.
    inversion case_shapes_p0.
    elim (Hvarsss p C l0 (Node (symbol n) l2 :: l1) case_shapes_p); intros Hvars1 Hvars2.
    split.
    intros e Hine.
    intros h p' Cp'; apply Hvars1; trivial.
    apply gt_trans with (m := j); trivial.
    subst ls; intros s Hins h p' Cp'; apply Hvars2; trivial.
    apply gt_trans with (m := j); trivial.
    rewrite element_at_in_replaced' in case_shapes_p0; trivial.
    apply (Hvarsss p0 C0 ls le case_shapes_p0).
    TrivCase eq_Sigma_S_dec Top_S; simpl; trivial.

    elim (eq_Substitution_dec  l0 l); intro case_l.
    elim (eq_list_Expression_dec  (Node (symbol n) l2 :: l1) l3); intro case_l2.
    subst l l3.
    TrivCase eq_Sigma_S_dec (Shapes l0 (Node (symbol n) l2 :: l1)); simpl; trivial.
    elim (eq_Sigma_S_dec  Top_S (Shapes l l3)); intro h; [inversion h | clear h; simpl].
    simpl; apply Hvars_replace_Top; trivial.
    elim (eq_Sigma_S_dec  Top_S (Shapes l l3)); intro h; [inversion h | clear h; simpl].
    apply Hvars_replace_Top; trivial.

    destruct (ss[S p|q]); trivial.

    generalize Hinc; apply m_list_inc_equiv.
    apply m_list_equiv_combine.
    unfold Succs.
    apply pred_list_equiv_sym.
    unfold nb_list_convert; apply pred_list_convert_equiv.
    trivial.
  Qed.


  Lemma itera_shapes_nil : forall (fcn : function) (Hin : In fcn functions) (ss : vector Sigma_S (fcn_size fcn)), 
    itera_shapes fcn Hin (ss, pred_nil (P (fcn_size fcn))) = ss.
  Proof.
    intros fcn Hin ss.
    generalize (itera_eq (Succs (fcn_size fcn) (fcn_bytecode fcn) (lrs_functions fcn Hin)) 
      (Step_S_Succs_same_length fcn (lrs_functions fcn Hin)) eq_Sigma_S_dec r_S_is_semilattice wfr_S 
      (ss,pred_nil (P (fcn_size fcn)))).
    unfold itera_shapes; trivial.
  Qed.


  Lemma itera_shapes_cons : forall (fcn : function) (Hin : In fcn functions) (ss : vector Sigma_S (fcn_size fcn)) (p : nat) (C : p < fcn_size fcn) (w' : nb_list (fcn_size fcn)), 
    itera_shapes fcn Hin (ss,pred_cons (P (fcn_size fcn)) p C w') = 
    itera_shapes fcn Hin (propagate_shapes fcn Hin ss w' (Step_S' fcn Hin p C (ss[p|C]))).
  Proof.
    (intros fcn Hin ss p C w').
    generalize (itera_eq (Succs (fcn_size fcn) (fcn_bytecode fcn) (lrs_functions fcn Hin)) 
      (Step_S_Succs_same_length fcn (lrs_functions fcn Hin)) eq_Sigma_S_dec r_S_is_semilattice wfr_S 
      (ss,pred_cons (P (fcn_size fcn)) p C w')).
    unfold itera_shapes; unfold propagate_shapes; trivial.
  Qed.


  Lemma itera_shapes_Hvars : forall (fcn : function) (Hin : In fcn functions) (ssw : vector Sigma_S (fcn_size fcn) * nb_list (fcn_size fcn)), 
    Hvars (fcn_size fcn) (fst ssw) -> Hvars (fcn_size fcn) (itera_shapes fcn Hin ssw).
  Proof.
    intros fcn Hin ssw.
    generalize (acc_ssw Sigma_S (fcn_size fcn) r_S eq_Sigma_S_dec wfr_S ssw).
    intro Hacc; elim Hacc; clear Hacc ssw.
    intros ssw H Hrec Hvarsss.
    destruct ssw as [ss w]; simpl in Hvarsss.
    destruct w.
    rewrite <- (itera_shapes_nil fcn Hin ss) in Hvarsss; trivial.
    rewrite (itera_shapes_cons fcn Hin).
    apply Hrec; trivial.
    unfold propagate_shapes; apply (propa_nondep_lexprod Sigma_S (fcn_size fcn) 
      (Succs (fcn_size fcn) (fcn_bytecode fcn) (lrs_functions fcn Hin)) 
      (Step_S fcn) r_S sup_S (Step_S_Succs_same_length fcn (lrs_functions fcn Hin)) 
      eq_Sigma_S_dec r_S_is_semilattice ss a w p).
    apply (propa_shapes_hvars fcn Hin ss w a p).
    apply m_list_inc_refl.
    assumption.
  Qed.


  Lemma Sss_init_Hvars : forall (fcn : function), Hvars (fcn_size fcn) (Sss_init fcn).
  Proof.
    intros fcn p0 C0 ls le case_shapes_p0. 
    unfold Sss_init in case_shapes_p0.
    elim (eq_nat_dec 0 p0); intro comp.
    subst p0; rewrite element_at_in_replaced in case_shapes_p0.
    inversion case_shapes_p0; subst le ls.
    split.
    unfold init_vars.
    intros e Hine h p' Cp'; generalize Cp' Hine; apply In_fresh.
    intros s Hins; inversion Hins.
    rewrite element_at_in_replaced' in case_shapes_p0; trivial.
    rewrite element_at_constant_list in case_shapes_p0.
    inversion case_shapes_p0.
  Qed.


  Lemma Hvars_Kildall_Shapes : forall (fcn : function) (Hin : In fcn functions), Hvars (fcn_size fcn) (Kildall_Shapes fcn Hin).
  Proof.
    intros fcn Hin; unfold Kildall_Shapes.
    unfold Kildall_shapes; unfold Kildall.
    generalize (itera_shapes_Hvars fcn Hin (Sss_init fcn,
      work_list Sigma_S (fcn_size fcn)
      (Succs (fcn_size fcn) (fcn_bytecode fcn) (lrs_functions fcn Hin))
      (Step_S fcn) sup_S
      (Step_S_Succs_same_length fcn (lrs_functions fcn Hin))
      eq_Sigma_S_dec (Sss_init fcn) 
      (fcn_size fcn) (le_refl (fcn_size fcn)))).
    intro H; unfold itera_shapes in H; apply H.
    simpl.
    apply Sss_init_Hvars.
  Qed.


  Lemma Really_fresh : forall (fcn : function) (Hin : In fcn functions) (p : nat) (C : p < fcn_size fcn) (ls : Substitution) (le : list Expression), 
    (Kildall_Shapes fcn Hin)[p|C] = Shapes ls le -> 
    (forall (e : Expression), In e le -> (forall (h : nat), var_not_in_tree e (S p) h)) /\ 
    (forall (s : subst_elem), In s ls -> (forall (h : nat), ~ var_in_subst_elem s (S p) h)).
  Proof.
    intros fcn Hin p C ls le case_shapes_p.
    elim (Hvars_Kildall_Shapes fcn Hin p C ls le case_shapes_p); intros Hvars1 Hvars2.
    split.
    intros e Hine h; apply (Hvars1 e Hine h (S p)); trivial.
    auto with arith.
    intros s Hins h; apply (Hvars2 s Hins h (S p)); trivial.
    auto with arith.
  Qed.


  Lemma really_fresh_alt : forall (fcn : function) (Hin : In fcn functions) (p : nat) (C : p < fcn_size fcn) (ls : Substitution) (le : list Expression), 
    (Kildall_Shapes fcn Hin)[p|C] = Shapes ls le -> 
    forall (e : Expression), In e (map (apply ls) (init_vars fcn)) -> forall (j : nat), var_not_in_tree e (S p) j.
  Proof.
    intros fcn Hin p C ls le Hshapes e Hine j.
    elim (Really_fresh fcn Hin p C ls le Hshapes); intros Hrf1 Hrf2.
    elim (In_mapped _ _ _ _ _ Hine); intros a Ha; elim Ha; clear Ha; intros Ha1 Ha2.
    subst e; apply var_not_in_subst_not_in_apply.
    intros s Hins; apply (Hrf2 s Hins j); trivial. 
    unfold init_vars in Ha1.
    generalize Ha1; apply In_fresh.
    auto with arith.
  Qed.

End fresh_variables.
