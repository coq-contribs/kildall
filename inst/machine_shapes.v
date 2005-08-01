  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*						  	         *)
  (*   File : machine_shapes.v		  		         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : shape verification                              *)
  (***************************************************************)


Section machine_shapes.
  
  Add LoadPath "../aux".
  Add LoadPath "../lists".
  Add LoadPath "../kildall".

  Require Export fresh_variables.
  
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


  Hypothesis Pattern_branch : forall (fcn : function) (Hin : In fcn functions) 
    (p : nat) (C : p < fcn_size fcn) (cnm : name) 
    (j: nat) (Cj : j < fcn_size fcn) 
    (s : Substitution) (e : Expression) (le : list Expression), 
    (fcn_bytecode fcn)[p|C] = i_branch (fcn_size fcn) cnm j Cj -> 
    (Kildall_Shapes fcn Hin)[p|C] = Shapes s (e::le) -> 
    tree_is_pattern e.


  Definition wellshaped_plus_frame (f : frame) : Prop :=
    forall (fcn : function) (Hget : Get_function (frm_fun f) = Some fcn) 
      (C : (frm_pc f) < (fcn_size fcn)), 
      ex (fun (s : Substitution) => (ex (fun (lexpr : list Expression) => ex (fun (rho : Substitution) =>   
        (Kildall_Shapes fcn (get_some_in_functions fcn (frm_fun f) functions Hget))[(frm_pc f)|C] = Shapes s lexpr /\
        stack_shaping (map (apply s) (init_vars fcn)) (frm_args f) rho /\
        (forall (j : nat) (e : Expression) (v : value),
          lexpr[j] = Some e -> (frm_stack f)[j] = Some v -> tree_is_pattern e ->
          tree_name_to_tree_Name v = apply rho e) /\ length lexpr = length (frm_stack f))))).


  Inductive wellshaped_configuration : configuration -> Prop :=
    wellshaped_conf : forall (M : configuration) , welltyped_configuration M -> 
      ( (* top frame well shaped *)
        (forall (f : frame), element_at_list M 0 = Some f -> wellshaped_plus_frame f)
        /\
      (* stack i @ args i-1 wellshaped *)
        (forall (i : nat) (fi fpi : frame), M[i] = Some fi -> M[S i] = Some fpi ->
          wellshaped_plus_frame (mkframe ((frm_fun fpi)) ((frm_pc fpi)) ((frm_args fi)++(frm_stack fpi)) (frm_args fpi)))) ->
      wellshaped_configuration M.



  Lemma Wshi_Kildall : forall (fcn : function) (Hin : In fcn functions) (p : nat) (C : p < (fcn_size fcn)), 
    Wshi fcn (Kildall_Shapes fcn Hin) p C.
  Proof.    
    intros fcn Hin p C.
    cut (Is_data_flow_analyser Sigma_S ((fcn_size fcn)) 
      (Succs ((fcn_size fcn)) ((fcn_bytecode fcn)) (lrs_functions fcn Hin)) 
      (Step_S fcn) r_S 
      (Step_S_Succs_same_length fcn (lrs_functions fcn Hin)) 
      (Kildall_shapes fcn (lrs_functions fcn Hin))).
    unfold Is_data_flow_analyser; unfold Kildall_Shapes.
    intro is_dfa; generalize (is_dfa (Sss_init fcn)); clear is_dfa; intro is_dfa.
    elim is_dfa; clear is_dfa; intros dfa1 H.
    elim H; clear H; intros dfa2 H.
    apply (stable_imp_Wshi fcn (lrs_functions fcn Hin)).
    apply (Passed_Kildall fcn Hin). 
    apply dfa1.
    apply (monotone_step_imp_kildall_dfa Sigma_S (fcn_size fcn) (Succs (fcn_size fcn) (fcn_bytecode fcn) (lrs_functions fcn Hin)) 
      (Step_S fcn) r_S sup_S (Step_S_Succs_same_length fcn (lrs_functions fcn Hin)) eq_Sigma_S_dec  r_S_is_semilattice  wfr_S).
    apply Succs_equiv.
    apply Step_S_equiv.
    apply monotone_Step_S.
  Qed.
  
  
  Lemma Kildall_Shapes_0 : forall (fcn : function) (Hin : In fcn functions), 
    (Kildall_Shapes fcn Hin)[0|nonvoidfcn fcn Hin] = (Sss_init fcn)[0|nonvoidfcn fcn Hin].
  Proof.    
    intros fcn Hin.
    cut (Is_data_flow_analyser Sigma_S ((fcn_size fcn)) 
      (Succs ((fcn_size fcn)) ((fcn_bytecode fcn)) (lrs_functions fcn Hin)) 
      (Step_S fcn) r_S 
      (Step_S_Succs_same_length fcn (lrs_functions fcn Hin)) 
      (Kildall_shapes fcn (lrs_functions fcn Hin))).
    unfold Is_data_flow_analyser.
    intro is_dfa; generalize (is_dfa (Sss_init fcn)); clear is_dfa; intro is_dfa.
    elim is_dfa; clear is_dfa; intros dfa1 H.
    elim H; clear H; intros dfa2 dfa3.
    cut (r_S (element_at (Sss_init fcn) 0 (nonvoidfcn fcn Hin)) (element_at (Kildall_Shapes fcn Hin) 0 (nonvoidfcn fcn Hin))).
    intro Hr.
    CaseEq (element_at (Kildall_Shapes fcn Hin) 0 (nonvoidfcn fcn Hin)).
    intro case; generalize Hr; clear Hr; rewrite case.
    intro Hr; destruct (element_at (Sss_init fcn) 0 (nonvoidfcn fcn Hin)); inversion Hr.
    trivial.
    intro case; elim (Passed_Kildall fcn Hin); rewrite <- case; apply element_at_belong.
    intros l lexpr case.
    generalize Hr; clear Hr; rewrite case.
    unfold Sss_init.
    rewrite element_at_in_replaced.
    intro Hr; inversion Hr.
    trivial.
    unfold Kildall_Shapes; generalize dfa2; unfold Vector_pointwise; apply vector_pointwise_to_element.
    apply (monotone_step_imp_kildall_dfa Sigma_S ((fcn_size fcn)) (Succs ((fcn_size fcn)) ((fcn_bytecode fcn)) (lrs_functions fcn Hin)) 
      (Step_S fcn) r_S (sup_S ) (Step_S_Succs_same_length fcn (lrs_functions fcn Hin)) eq_Sigma_S_dec r_S_is_semilattice wfr_S).
    apply Succs_equiv.
    apply Step_S_equiv.
    apply monotone_Step_S.
  Qed.


  Lemma reduction_keeps_wellshaped : Invariant (fun (M : configuration) => wellshaped_configuration M /\ frames_args_length M).
  Proof.    
    intros M M' PM Hred.
    elim PM; intros Hws Hfal; clear PM; split.
    InversionRed Hred.
    Focus 1.
  (* return *) 
    cut (frm_pc f < fcn_size fcn).
    inversion Hws; subst; generalize H; elim H0; clear H H0; intros Hwstop Hwsvirtual. 
    cut (element_at_list (f :: g :: M0) 0 = Some f); [intro Hf | trivial].
    intros Hwt C; elim (Hwstop f Hf fcn Hfcn C); intros s h.
    elim h; clear Hwstop h; intros lexpr h.
    elim h; clear h; intros rho h.
    elim h; clear h; intros case_shapes_f h.
    elim h; clear h; intros Hshapingf h.
    elim h; clear h; intros Hpattern Hlengthf.
    generalize (Wshi_Kildall fcn (get_some_in_functions  fcn (frm_fun f) functions Hfcn) (frm_pc f) C).
    unfold Wshi.
    rewrite case_shapes_f.
    replace (element_at (fcn_bytecode fcn) (frm_pc f) C) with (i_return (fcn_size fcn)).
    intro Hnotnil.
    destruct lexpr.
    elim Hnotnil; trivial.
    clear Hnotnil.
    constructor.
    generalize Hred; apply reduction_keeps_welltyped; trivial.
    split.
    intros f' Hf' gcn Hgetg Cg.
    simpl in Hf'; inversion Hf'; subst f'; (clear Hf').
    cut (frm_pc g < fcn_size gcn); [intro Cg' | generalize Cg; simpl; auto with arith].
    generalize (Wshi_Kildall gcn (get_some_in_functions  gcn (frm_fun g) functions Hgetg) (frm_pc g) Cg').
    unfold Wshi.
    CaseEq (element_at (Kildall_Shapes gcn (get_some_in_functions  gcn (frm_fun g) functions Hgetg)) (frm_pc g) Cg').
    intro case_shapes_g; cut False; [intro F; inversion F | generalize (Hwsvirtual 0 f g)].
    simpl.
    clear Hf; cut (Some f = Some f); [intro Hf | trivial].
    cut (Some g = Some g); [intro Hg | trivial].
    intro h; generalize (h Hf Hg gcn); clear h; intro h.
    generalize (h Hgetg Cg'); clear h Hf Hg; intro wspf1.
    inversion_clear wspf1 as [s1 h].
    inversion_clear h as [lexpr1 h1].
    inversion_clear h1 as [rho1 h].
    elim h; clear h; simpl.
    intros case_shapes_f1 h; rewrite case_shapes_f1 in case_shapes_g; inversion case_shapes_g.
    intros dd F; inversion F.
    intros l0 l1 case_shapes_g.
    cut (element_at (fcn_bytecode gcn) (frm_pc g) Cg' = i_call (fcn_size gcn) (frm_fun f) (length (frm_args f))).
    intro case_instr_g; rewrite case_instr_g.
    CaseEq (split_k_elements (length (frm_args f)) l1).
    intros p case_split_l1; destruct p.
    CaseEq (element_at_unsafe (Kildall_Shapes gcn (get_some_in_functions  gcn (frm_fun g) functions Hgetg)) (S (frm_pc g))).
    intros s0 case_shapes_g_s; destruct s0.
    intro F; inversion F.
    intro F; inversion F.
    intro h; elim h; clear h; intros h1 h2; subst.
    exists l0.
    exists (Node (symbol (frm_fun f)) (rev_lin l2) :: l3).

    clear Hf; cut (Some f = Some f); [intro Hf | trivial].
    cut (Some g = Some g); [intro Hg | trivial].
    generalize (Hwsvirtual 0 f g Hf Hg gcn); intro Hh; simpl in Hh.
    generalize (Hh Hgetg Cg'); clear Hh.
    intro Hh; inversion_clear Hh as [sg h]. 
    inversion_clear h as [lexprg h1].
    inversion_clear h1 as [rhog h2].
    exists rhog.
    simpl in h2.
    clear Hf Hg.

    CaseEq (frm_stack f).
    intro h; rewrite h in Hlengthf; simpl in Hlengthf; inversion Hlengthf.
    intros v l4 Hstackf.
    elim h2; clear h2; intros h2 h3.
    elim h3; clear h3; intros h3 h4.
    elim h4; clear h4; intros h4 h5.
    rewrite case_shapes_g in h2; inversion h2.

    subst; repeat split.
    simpl; simpl in Cg; simpl in Hgetg; simpl in case_shapes_g_s.
    generalize case_shapes_g_s; apply element_at_unsafe_to_safe.
    simpl; assumption.
    intros j ej vj Hej Hvj.
    destruct j.
    inversion Hej; inversion Hvj.
    subst ej vj.
    clear Hej Hvj h2.
    unfold tree_is_pattern.
    simpl; rewrite Hfcn. 
    simpl; intro h; inversion h.
    simpl in Hej; simpl in Hvj.
    generalize (h4 (length l2 + j) ej vj); clear h4; intro h4.
    cut (element_at_list (l2 ++ l3) (length l2 + j) = element_at_list l3 j); [intro Hlej | apply element_at_list_concat].
    cut (length l2 = length (frm_args f)); [intro h6 | generalize case_split_l1; apply split_k_elements_length].
    apply h4.
    replace lexprg with (l2 ++ l3).
    rewrite Hlej; generalize Hej; destruct (element_at_list l3 j); trivial.
    symmetry; generalize case_split_l1; apply split_k_elements_ok.
    replace (element_at_list (frm_args f ++ frm_stack g) (length l2 + j)) with (element_at_list (frm_stack g) j).
    generalize Hvj; destruct (element_at_list (frm_stack g) j); trivial.
    symmetry; rewrite h6; apply element_at_list_concat.
    simpl.
    cut (length l3 = length (frm_stack g)); [auto with arith | idtac].
    rewrite concat_length in h5.
    replace lexprg with (l2 ++ l3) in h5.
    rewrite concat_length in h5.
    generalize h5; replace (length (frm_args f)) with (length l2); [apply plus_reg_l | generalize case_split_l1; apply split_k_elements_length].
    symmetry; generalize case_split_l1; apply split_k_elements_ok.
    intros dd F; inversion F.
    intros dd F; inversion F.
    inversion Hwt; subst.
    elim (H 0 f g fcn gcn); simpl; trivial.
    intros dd h; elim h; clear dd h.
    intros dd h; cut (Some g = Some g); [intro hg | trivial].
    simpl in Hgetg; generalize (h hg Hgetg); apply element_at_unsafe_to_safe.
    assumption.

  (* part 2 *)
    intros i fi fpi Hfi Hfpi.
    destruct i.
    inversion Hfi; subst.
    simpl; apply (Hwsvirtual 1 g fpi); simpl; trivial.
    apply (Hwsvirtual (S (S i))).
    simpl; simpl in Hfi; rewrite Hfi; trivial.
    simpl; simpl in Hfpi; rewrite Hfpi; trivial.
    symmetry; generalize case_instr; apply element_at_unsafe_to_safe.
    generalize case_instr; apply element_at_unsafe_some.

  (* stop *)
    constructor.
    constructor.
    apply wellformed_epsilon.
    split.
    intros dd F; inversion F.
    intros i fi fpi F; inversion F.
    split.
    intros dd F; inversion F.
    intros i fi fpi F; inversion F.

  (* load *)
    Focus 1.
    inversion Hws; subst.
    generalize H; elim H0; intros Hwstop Hwsvirtual Hwt.
    cut (element_at_list (f :: M0) 0 = Some f); [intro Hf | trivial].
    generalize (Hwstop f Hf); clear Hwstop H H0; intro Hwstop.
    inversion Hwt; subst.
    generalize H; elim H0; intros Hwttop Hwtvirtual Hwf.
    generalize (Hwttop f Hf); clear Hwttop H H0 Hf; intro Hwttop.
    constructor.
    generalize Hwt Hred ; apply reduction_keeps_welltyped; trivial.
    cut (frm_pc f < fcn_size fcn).
    intro C.
    split.
    intros f' Hf' fcn' Hfcn' C'; inversion Hf'; subst f'; (clear Hf').
    simpl in C'; simpl in Hfcn'; cut (fcn' = fcn); [intro ; subst | rewrite Hfcn' in Hfcn; inversion Hfcn; trivial].
    elim (Hwstop fcn Hfcn' C); intros s h.
    elim h; clear Hwstop h; intros lexpr h.
    elim h; clear h; intros rho h.
    elim h; clear h; intros case_shapes_f h.
    elim h; clear h; intros Hshapingf h.
    elim h; clear h; intros Hpattern Hlengthf.
    generalize (Wshi_Kildall fcn (get_some_in_functions  fcn (frm_fun f) functions Hfcn') (frm_pc f) C).
    unfold Wshi.
    rewrite case_shapes_f.
    replace (element_at (fcn_bytecode fcn) (frm_pc f) C) with (i_load  (fcn_size fcn) j).
    CaseEq (element_at_unsafe (Kildall_Shapes fcn (get_some_in_functions  fcn (frm_fun f) functions Hfcn')) (S (frm_pc f))).
    intros s' case_shapes_f_s; destruct s'.
    intro F; inversion F.
    intro F; inversion F.
    CaseEq (element_at_list (rev_lin lexpr) j).
    intros ej case_ej h; elim h; clear h; intros h hh; subst.
    exists s; exists (ej :: lexpr); exists rho.
    repeat split; simpl; trivial.
    generalize case_shapes_f_s; apply element_at_unsafe_to_safe.
    intros j' ej' vj' Hej' Hvj'; destruct j'.
    inversion Hej'; inversion Hvj'; subst.
    cut (j < length (rev lexpr)).
    intro Cj.
    apply (Hpattern (length (rev lexpr) - S j) ej' vj').
    cut (element_at_list (rev (rev lexpr)) (length (rev lexpr) - S j) = Some ej'); [rewrite rev_involutive; trivial | rewrite <- case_ej].
    symmetry; rewrite rev_lin_is_rev; apply element_at_list_rev; trivial.
    generalize Cj; rewrite rev_length; rewrite Hlengthf; rewrite <- rev_length; clear Cj; intro Cj.
    replace (Some vj') with (element_at_list (rev (rev (frm_stack f))) (length (rev (frm_stack f)) - S j)).
    rewrite rev_involutive; trivial.
    rewrite <- Hvj; symmetry; rewrite rev_lin_is_rev; apply element_at_list_rev; trivial.
    generalize case_ej; rewrite rev_lin_is_rev; apply element_at_list_some.
    apply (Hpattern j').
    generalize Hej'; destruct (element_at_list lexpr j'); trivial.
    generalize Hvj'; destruct (element_at_list (frm_stack f) j'); trivial.
    generalize Hlengthf; auto with arith.
    intros dd F; inversion F.
    intros dd F; inversion F.
    symmetry; generalize case_instr; apply element_at_unsafe_to_safe.
  (* part 2 *)
    intros i fi fpi Hfi Hfpi; destruct i.
    inversion Hfi; subst; simpl.
    apply (Hwsvirtual 0 f fpi); trivial.
    simpl in Hfi; simpl in Hfpi; apply (Hwsvirtual (S i) fi fpi); simpl; trivial.
    generalize case_instr; apply element_at_unsafe_some.

  (* call *)
    Focus 1.
    inversion Hws; subst.
    generalize H; elim H0; intros Hwstop Hwsvirtual Hwt.
    cut (element_at_list (f :: M0) 0 = Some f); [intro Hf | trivial].
    generalize (Hwstop f Hf); clear Hwstop H H0; intro Hwstop.
    inversion Hwt; subst.
    generalize H; elim H0; intros Hwttop Hwtvirtual Hwf.
    generalize (Hwttop f Hf); clear Hwttop H H0 Hf; intro Hwttop.
    constructor.
    generalize Hwt Hred ; apply reduction_keeps_welltyped; trivial.
    split.
    intros g' Hg' gcn' Hgcn' Cg; simpl.
    inversion Hg'; subst g'; (clear Hg').
    simpl; rewrite (element_at_irrel Sigma_S (fcn_size gcn') (Kildall_Shapes gcn' (get_some_in_functions  gcn' gnm functions Hgcn')) 0 Cg (nonvoidfcn gcn' (get_some_in_functions  gcn' gnm functions Hgcn'))).
    rewrite Kildall_Shapes_0; unfold Sss_init; rewrite element_at_in_replaced.
    exists (nil (A := subst_elem)); exists (init_vars gcn').
    cut (length (init_vars gcn') = length vargs).
    intro Hlengthg.
    CaseEq (init_subst (rev_lin vargs)).
    intros l0 case_init_subst.
    exists l0.
    repeat split; trivial.
    simpl; rewrite map_id.

    unfold stack_shaping; unfold init_vars. 
    rewrite <- (rev_involutive vargs).
    rewrite <- rev_lin_is_rev.
    apply (init_stack_shaping (length (fcn_args gcn')) 0 (rev vargs) l0); trivial.
    generalize case_init_subst; unfold init_subst; rewrite rev_lin_is_rev.
    rewrite rev_length; rewrite <- Hlengthg; rewrite init_vars_length; trivial.
    
    unfold init_vars; intros j ej vj Hej Hvj Hpattern.
    generalize (element_at_init_vars  (length (fcn_args gcn')) 0 0 j ej Hej); intro Hejeq.
    rewrite plus_comm in Hejeq; simpl in Hejeq.
    cut ((rev vargs)[(length vargs) - (S j)] = Some vj); [clear Hvj; intro Hvj |  rewrite <- element_at_list_rev; trivial].
    rewrite rev_lin_is_rev in case_init_subst; unfold init_subst in case_init_subst.
    rewrite rev_length in case_init_subst; rewrite <- Hlengthg in case_init_subst. 
    rewrite init_vars_length in case_init_subst.
    rewrite <- (init_subst_apply (length (fcn_args gcn')) 0 (length vargs - S j) l0 (rev vargs) vj Hvj case_init_subst).
    simpl; subst; rewrite <- Hlengthg.
    rewrite init_vars_length; trivial.
    generalize Hvj; apply element_at_list_some.
    intro F; elim (subst_length (length (fcn_args gcn')) 0 (rev vargs)).
    rewrite rev_length; rewrite <- (init_vars_length gcn'); symmetry; assumption.
    rewrite <- F; unfold init_subst; rewrite rev_lin_is_rev.
    rewrite rev_length; rewrite <- Hlengthg; rewrite init_vars_length; trivial.

    symmetry; replace vargs with (frm_args (Frm gnm 0 vargs vargs)). 
    rewrite (init_vars_length gcn').
    cut (frames_args_length (mkframe gnm 0 vargs vargs :: mkframe (frm_fun f) (frm_pc f) l (frm_args f) :: M0)).
    intro Hfal'; apply Hfal'; trivial.
    left; trivial.
    cut (welltyped_configuration (mkframe gnm 0 vargs vargs :: mkframe (frm_fun f) (frm_pc f) l (frm_args f) :: M0) /\ frames_args_length (mkframe gnm 0 vargs vargs :: mkframe (frm_fun f) (frm_pc f) l (frm_args f) :: M0)).
    intro H; elim H; trivial.
    generalize Hred; apply reduction_length; trivial.
    split; trivial.
    simpl; trivial.

  (* part 2 *)
    intros i fi fpi Hfi Hfpi.
    destruct i; simpl.
    inversion Hfi; inversion Hfpi; subst.
    simpl.
    replace (vargs ++ l) with (frm_stack f).
    apply Hwstop.
    generalize case_split_stack; apply split_k_elements_ok.
    destruct i.
    inversion Hfi.
    simpl.
    apply (Hwsvirtual 0 f fpi); simpl; trivial.
    apply (Hwsvirtual (S i) fi fpi); simpl; trivial.

  (* build *)
    Focus 1.
    inversion Hws; subst.
    generalize H; elim H0; intros Hwstop Hwsvirtual Hwt.
    cut (element_at_list (f :: M0) 0 = Some f); [intro Hf | trivial].
    generalize (Hwstop f Hf); clear Hwstop H H0; intro Hwstop.
    inversion Hwt; subst.
    generalize H; elim H0; intros Hwttop Hwtvirtual Hwf.
    generalize (Hwttop f Hf); clear Hwttop H H0 Hf; intro Hwttop.
    constructor.
    generalize Hwt Hred ; apply reduction_keeps_welltyped; trivial.
    split.

    intros g' Hg' gcn Hgcn Cg; simpl.
    inversion Hg'; subst g'; (clear Hg').
    cut (fcn = gcn).
    intro; subst fcn; simpl; simpl in Hgcn; simpl in Cg.
    cut (frm_pc f < fcn_size gcn).
    intro C.
    elim (Hwstop gcn Hgcn C).
    intros s h; elim h; clear h.
    intros lexpr h; elim h; clear h.
    intros rho h; elim h; clear h.
    intros h1 h; elim h; clear h.
    intros h2 h; elim h; clear h; intros h3 h4.
    generalize (Wshi_Kildall gcn (get_some_in_functions  gcn (frm_fun f) functions Hgcn) (frm_pc f) C).
    unfold Wshi.
    replace (element_at (fcn_bytecode gcn) (frm_pc f) C) with (i_build (fcn_size gcn) cnm car). 
    rewrite h1.
    CaseEq (split_k_elements car lexpr).
    intros p case_split_lexpr; destruct p as [sargs slexpr].
    CaseEq (element_at_unsafe (Kildall_Shapes gcn (get_some_in_functions  gcn (frm_fun f) functions Hgcn)) (S (frm_pc f))).
    intros s0 case_shapes_f_s.
    destruct s0.
    intro F; inversion F.
    intro F; inversion F.
    intro h; elim h; clear h; intros h5 h6; subst l0 l1.
    exists s; exists (Node (symbol cnm) (rev_lin sargs) :: slexpr).
    cut ((Kildall_Shapes gcn (get_some_in_functions  gcn (frm_fun f) functions Hgcn))[S (frm_pc f)|Cg] = Shapes s (Node (symbol cnm) (rev_lin sargs) :: slexpr)); [intro case_shapes_f_s'; rewrite case_shapes_f_s' | generalize case_shapes_f_s; apply element_at_unsafe_to_safe].
    exists rho.
    repeat split.
    assumption.
    intros j ej vj Hej Hvj Hpattern; destruct j.
    inversion Hej; inversion Hvj; subst.
    rewrite (apply_cons cnm rho (rev vargs) (rev_lin sargs)).
    simpl; trivial.
    rewrite rev_length; rewrite rev_lin_is_rev; rewrite rev_length.
    replace (length sargs) with car.
    generalize case_split_stack; apply split_k_elements_length.
    symmetry; generalize case_split_lexpr; apply split_k_elements_length.
    intros vj ej j Hvj2 Hej2; symmetry; apply (h3 (length sargs - S j) ej vj).
    replace lexpr with (sargs ++ slexpr).
    rewrite <- (element_at_list_concat').
    replace sargs with (rev (rev sargs)).
    rewrite rev_length.
    generalize Hej2; rewrite rev_lin_is_rev; rewrite (element_at_list_rev _ (rev sargs) j); trivial.
    generalize Hej2; rewrite rev_lin_is_rev; apply element_at_list_some.
    apply rev_involutive.
    (* SHOULD BE A LEMMA *)
    cut (0 < length sargs); [generalize (length sargs); intro k | destruct sargs; simpl].
    generalize j; induction k.
    intros dd F; inversion F.
    intros j0 Ck.
    destruct j0.
    simpl.
    rewrite <- minus_n_O.
    auto with arith.
    simpl.
    destruct k.
    simpl; trivial.
    apply lt_trans with (S k).
    apply IHk; trivial.
    auto with arith.
    auto with arith.
    simpl in Hej2.
    inversion Hej2.
    auto with arith.
    (* END LEMMA *)
    symmetry; generalize case_split_lexpr; apply split_k_elements_ok.
    replace (frm_stack f) with (vargs ++ l).
    rewrite <- (element_at_list_concat').
    replace (length sargs) with (length vargs).
    replace vargs with (rev (rev vargs)).
    rewrite rev_length.
    rewrite <- (element_at_list_rev _ (rev vargs) j).
    assumption.
    generalize Hvj2; apply element_at_list_some.
    apply rev_involutive.
    replace (length vargs) with car; symmetry.
    generalize case_split_lexpr; apply split_k_elements_length.
    generalize case_split_stack; apply split_k_elements_length.
    replace (length vargs) with (length sargs).
    cut (0 < length sargs); [generalize (length sargs); intro k | destruct sargs; simpl].
    generalize j; induction k.
    intros dd F; inversion F.
    intros j0 Ck.
    destruct j0.
    simpl.
    rewrite <- minus_n_O.
    auto with arith.
    simpl.
    destruct k.
    simpl; trivial.
    apply lt_trans with (S k).
    apply IHk; trivial.
    auto with arith.
    auto with arith.
    simpl in Hej2.
    inversion Hej2.
    auto with arith.
    replace (length sargs) with car; symmetry.
    generalize case_split_stack; apply split_k_elements_length.
    generalize case_split_lexpr; apply split_k_elements_length.
    symmetry; generalize case_split_stack; apply split_k_elements_ok.
    rewrite rev_lin_is_rev in Hpattern; rewrite rev_lin_is_rev in Hej2; apply (sub_pattern cnm (rev sargs) Hpattern j ej Hej2).
    apply (h3 (car+j) ej vj).
    replace car with (length sargs).
    replace lexpr with (sargs++slexpr).
    rewrite element_at_list_concat.
    generalize Hej; simpl; destruct (element_at_list slexpr j); trivial.
    symmetry; generalize case_split_lexpr; apply split_k_elements_ok.
    generalize case_split_lexpr; apply split_k_elements_length.
    replace car with (length vargs).
    replace (frm_stack f) with (vargs ++ l).
    rewrite element_at_list_concat.
    generalize Hvj; simpl; destruct (element_at_list l j); trivial.
    symmetry; generalize case_split_stack; apply split_k_elements_ok.
    generalize case_split_stack; apply split_k_elements_length.
    assumption.
    simpl; cut (length slexpr = length l); [auto with arith | idtac].
    generalize h4; replace lexpr with (sargs ++ slexpr).
    rewrite concat_length.
    replace (frm_stack f) with (vargs++l).
    rewrite concat_length.
    replace (length sargs) with car.
    replace (length vargs) with car.
    apply plus_reg_l.
    symmetry; generalize case_split_stack; apply split_k_elements_length.
    symmetry; generalize case_split_lexpr; apply split_k_elements_length.
    symmetry; generalize case_split_stack; apply split_k_elements_ok.
    symmetry; generalize case_split_lexpr; apply split_k_elements_ok.
    intros dd F; inversion F.
    intros dd F; inversion F.
    symmetry; generalize case_instr; apply element_at_unsafe_to_safe.
    generalize case_instr; apply element_at_unsafe_some.
    simpl in Hgcn; rewrite Hgcn in Hfcn; inversion Hfcn; trivial.
  (* part 2 *)
    subst; intros i fi fpi Hfi Hfpi; destruct i.
    inversion Hfi; subst; simpl.
    apply (Hwsvirtual 0 f fpi).
    simpl; trivial.
    simpl; simpl in Hfpi; trivial.
    simpl in Hfi; simpl in Hfpi; apply (Hwsvirtual (S i) fi fpi); simpl; trivial.

  (* branch then *)
    Focus 1.
    cut (frm_pc f < fcn_size fcn).
    intro C.
    inversion Hws; subst.
    generalize H; elim H0; intros Hwstop Hwsvirtual Hwt.
    cut (element_at_list (f :: M0) 0 = Some f); [intro Hf | trivial].
    generalize (Hwstop f Hf); clear Hwstop H H0; intro Hwstop.
    inversion Hwt; subst.
    generalize H; elim H0; intros Hwttop Hwtvirtual Hwf.
    generalize (Hwttop f Hf); clear Hwttop H H0 Hf; intro Hwttop.
    constructor.
    generalize Hwt Hred ; apply reduction_keeps_welltyped; trivial.
    split.
    intros g' Hg'; inversion Hg'; subst g'; (clear Hg').
    intros gcn Hgcn Cg; simpl; simpl in Hgcn; simpl in Cg.
    cut (fcn = gcn). 
    intro; subst.
    elim (Hwstop gcn Hgcn C); intros s h.
    elim h; clear h; intros lexpr h.
    elim h; clear h; intros rho h.
    elim h; clear h; intros h1 h.
    elim h; clear h; intros h2 h.
    elim h; clear h; intros h3 h4.
    generalize (Wshi_Kildall gcn (get_some_in_functions  gcn (frm_fun f) functions Hgcn) (frm_pc f) C).
    unfold Wshi.
    replace (element_at (fcn_bytecode gcn) (frm_pc f) C) with (i_branch (fcn_size gcn) cnm j Cj).
    rewrite h1.
    destruct lexpr.
    intro F; inversion F.
    destruct t.
    intro F; inversion F.
    destruct n.
    
  (* n is a variable*)
    destruct l0; [idtac| intro F; inversion F].
    CaseEq (Get_constr cnm).
    intros c case_c.
    CaseEq (element_at_unsafe (Kildall_Shapes gcn (get_some_in_functions  gcn (frm_fun f) functions Hgcn)) (S (frm_pc f))).
    intros s0 case_f_s; destruct s0.
    intro F; elim F; clear F; intros dd F; inversion F.
    intro F; elim F; clear F; intros dd F; inversion F.
    intro h; elim h; intro dd; clear dd h. (* part wshi j cleared *)
    intro h; elim h; clear h; intros h h'; subst.
    exists (mksubst n n0 (Node (symbol cnm) (fresh (S (frm_pc f)) (S (length lexpr)) (length (cons_args c)))) :: s).
    exists (push_list (fresh (S (frm_pc f)) (S (length lexpr)) (length (cons_args c)))
     (map (apply_elem_tree (mksubst n n0 (Node (symbol cnm) (fresh (S (frm_pc f)) (S (length lexpr)) (length (cons_args c)))))) lexpr)).
    cut (tree_name_to_tree_Name (Node cnm vf) = apply  rho (Node (x  n n0) nil)); [intro Hrho_head | apply (h3 0); simpl; trivial].
    cut (length vf = length (cons_args c)); [intro Hlenvf | idtac].
    CaseEq (make_substitution (fresh (S (frm_pc f)) (S (length lexpr)) (length (cons_args c))) vf).
    intros svf case_svf.
    exists (rho ++ svf). 
    repeat split.
    generalize case_f_s; apply element_at_unsafe_to_safe.
    unfold stack_shaping; rewrite (map_apply_substitution_concat). 
    rewrite (map_apply_substitution_cons). 
    generalize h2; unfold stack_shaping.
    cut (forall (e : Expression) (j : nat), In e (map (apply s) (init_vars gcn)) -> var_not_in_tree e (S (frm_pc f)) ((S (length lexpr))+j)).
    generalize (frm_args f) (map (apply s) (init_vars gcn)); intros lv le.
  (* MAKE IT A LEMMA *)
    generalize case_svf; generalize (S (frm_pc f)) (S (length lexpr)) (length (cons_args c)) Hrho_head.
    intros p h m.
    generalize lv; clear lv; induction le; simpl; intro lv; trivial. 
    destruct lv; simpl; trivial.
    intros dd ddd dddd F; inversion F.
    intros.
    rewrite <- IHle; trivial.
    simpl.
    rewrite <- (make_substitution_simpl_in_branch_then_elem cnm n n0 m p h svf rho vf a v nil); trivial.
    intro j0; apply (H a j0). 
    left; trivial.
    inversion h0; trivial.
    intros e j0 He; apply (H e j0).
    right; assumption.
    inversion h0; trivial.
    intros e j0 Hine; generalize (really_fresh_alt fwd_jmp gcn (get_some_in_functions  gcn (frm_fun f) functions Hgcn) (frm_pc f) C s (Node (x n n0) nil :: lexpr) h1 e Hine (S (length lexpr) + j0)); simpl; trivial.
    
    intros j0 e v; elim (le_gt_dec (length (cons_args c)) j0); intro case_elem.
    rewrite (le_plus_minus (length (cons_args c)) j0 case_elem).
    rewrite push_list_is_app_rev.
    cut (length (rev (fresh (S (frm_pc f)) (S (length lexpr)) (length (cons_args c)))) + (j0 - length (cons_args c)) = length (cons_args c) + (j0 - length (cons_args c))).
    intros Hlene He; rewrite <- Hlene in He.
    rewrite (element_at_list_concat) in He.
    rewrite push_list_is_app_rev.
    cut (length (rev vf) + (j0 - length (cons_args c)) = length (cons_args c) + (j0 - length (cons_args c))).
    intros Hlenv Hv; rewrite <- Hlenv in Hv.
    rewrite element_at_list_concat in Hv.
    generalize (h3 (S (j0 - length (cons_args c)))); intro h3j0.
    elim (element_at_list_map' _ _ _ _ _ e He).
    intros ae Hae; elim Hae; clear Hae; intros Hae1 Hae2.
    rewrite Hstack in h3j0.
    intro Hpate.
    symmetry.
    rewrite apply_substitution_concat.
    rewrite Hae2.
    generalize (make_substitution_simpl_in_branch_then_elem cnm n n0 (length (cons_args c)) (S (frm_pc f)) (S (length lexpr)) svf rho vf ae v nil).
    intro h; apply h; clear h; trivial.
    elim (Really_fresh fwd_jmp gcn (get_some_in_functions  gcn (frm_fun f) functions Hgcn) (frm_pc f) C s (Node (x n n0) nil :: lexpr) h1); intros rf1 rf2.
    simpl in rf1.
    cut (Node (x n n0) nil = ae \/ In ae lexpr); [intro Hinae | right].
    intro j1; apply (rf1 ae Hinae (S (length lexpr + j1))).
    generalize Hae1; apply element_at_list_in.
    symmetry; apply (h3j0 ae v); simpl; trivial.

    generalize Hpate; rewrite Hae2; apply apply_elem_pattern.
    replace (length (rev vf)) with (length (cons_args c)); trivial.
    rewrite rev_length; symmetry; trivial.
    replace (length (rev (fresh  (S (frm_pc f)) (S (length lexpr)) (length (cons_args c))))) with (length (cons_args c)); trivial.
    rewrite rev_length; rewrite aux_init_vars_length; trivial.
    
    cut (j0 < length (cons_args c)); [clear case_elem; intro case_elem | generalize case_elem; auto with arith]. 
    rewrite push_list_is_app_rev; rewrite push_list_is_app_rev.
    rewrite <- (element_at_list_concat' _ (rev (fresh (S (frm_pc f)) (S (length lexpr)) (length (cons_args c))))).
    rewrite <- (element_at_list_concat' _ (rev  vf)).
    intros He Hv Hpate.
    symmetry.
    rewrite apply_substitution_concat.
    rewrite (make_substitution_apply _ _ _ _ _ ((length (rev (cons_args c))) - S j0) e v case_svf); trivial.
    apply apply_unchanged.
    replace (length (rev (cons_args c))) with (length (fresh (S (frm_pc f)) (S (length lexpr)) (length (cons_args c)))).
    rewrite element_at_list_rev; simpl.
    replace (length (fresh (S (frm_pc f)) (S (length lexpr)) (length (cons_args c))) -
      S (length (fresh (S (frm_pc f)) (S (length lexpr)) (length (cons_args c))) - S j0)) with j0; trivial.
    rewrite aux_init_vars_length; trivial.
    apply plus_minus.
    cut (S j0 <= length (cons_args c)); [intro Hj0 | generalize case_elem; auto with arith].
    rewrite minus_Sn_m; trivial.
    rewrite plus_comm.
    simpl.
    rewrite <- le_plus_minus; trivial.
    generalize Hj0; auto with arith.
    rewrite aux_init_vars_length; trivial.
    auto with arith.
    rewrite aux_init_vars_length; trivial.
    symmetry; apply rev_length.
    rewrite element_at_list_rev.

    replace j0 with (length vf - S (length (rev (cons_args c)) - S j0)) in Hv; trivial.
    rewrite rev_length.
    rewrite <- Hlenvf.
    symmetry; apply plus_minus.
    cut (S j0 <= length vf); [intro Hj0 | generalize case_elem; auto with arith].
    rewrite minus_Sn_m; trivial.
    rewrite plus_comm.
    simpl.
    rewrite <- le_plus_minus; trivial.
    generalize Hj0; auto with arith.
    rewrite <- Hlenvf; auto with arith. 
    rewrite rev_length.
    generalize case_elem; rewrite <- Hlenvf; auto with arith.
    rewrite rev_length; rewrite Hlenvf; trivial.
    rewrite rev_length; rewrite aux_init_vars_length; trivial.
    rewrite push_list_is_app_rev.
    rewrite concat_length.
    rewrite push_list_is_app_rev.
    rewrite concat_length.
    rewrite <- map_length.
    rewrite Hstack in h4.
    simpl in h4.
    rewrite rev_length.
    rewrite aux_init_vars_length.
    rewrite rev_length; rewrite  Hlenvf.
    replace (length lexpr) with (length l).
    trivial.
    symmetry; generalize h4; auto with arith.
    intro F; elim (make_substitution_some (length (cons_args c)) (S (frm_pc f)) (S (length lexpr)) vf); trivial.
    clear Hrho_head case_f_s h1 h2 h3 h4.
    generalize (Hwttop gcn Hgcn C); clear Hwttop; intro Hwttop.
    rewrite Hstack in Hwttop.
    destruct (element_at (Kildall_Types gcn (get_some_in_functions  gcn (frm_fun f) functions Hgcn)) (frm_pc f) C). 
    inversion Hwttop.
    inversion Hwttop.
    destruct l0.
    inversion Hwttop.
    unfold stack_typing in Hwttop; inversion Hwttop; subst.
    apply tree_typing_args_length with (cnm := cnm) (t := cons_ret const); trivial.
    generalize H6; apply args_to_tree_typing; trivial.
    rewrite Hstack; simpl; trivial.
    unfold tree_is_pattern; simpl; trivial.
    intros dd Hd; elim Hd; intros ddd F; inversion F.
    intros dd F; inversion F.
    
  (* n is of the form d(e1,  ,em)*)
        
    elim (eq_name_dec cnm n); intro case_eq.
    
  (* constructors c and  d  are equal*)
    
    CaseEq (element_at_unsafe (Kildall_Shapes gcn (get_some_in_functions  gcn (frm_fun f) functions Hgcn)) (S (frm_pc f))).
    intros s0 case_f_s; destruct s0.
    intro F; inversion F.
    intro F; inversion F.
    intro h; elim h; clear h; intros h h'; subst n; subst.
    exists s.
    exists (push_list l0 lexpr).
    exists rho.
    cut (length l0 = length vf).
    
  (* it is assumed that lengths are equal *)

     (* THERE *)    
    intro Hlenvf.
    repeat split.
    generalize case_f_s; apply element_at_unsafe_to_safe.
    assumption.
    intros j0 e v.
    rewrite push_list_is_app_rev; rewrite push_list_is_app_rev.
    elim (le_gt_dec (length (rev l0)) j0); intro case_j0.
    rewrite (le_plus_minus (length (rev l0)) j0 case_j0).
    rewrite element_at_list_concat.
    cut (length (rev l0) + (j0 - length (rev l0)) = length (rev vf) + (j0 - length (rev l0))); [intro dd; rewrite dd; clear dd | rewrite rev_length;rewrite rev_length; rewrite <- Hlenvf; trivial].
    rewrite element_at_list_concat.
    intros He Hv; apply (h3 (S (j0 - length l0))).
    simpl; rewrite <- rev_length; rewrite He; trivial.
    rewrite Hstack; simpl; rewrite <- rev_length; rewrite <- Hv.
    CaseEq (l[j0 - length (rev l0)]); symmetry; trivial.
    cut (j0 < length (rev l0)); [clear case_j0; intro case_j0 | generalize case_j0; auto with arith].
    rewrite <- (element_at_list_concat' _ (rev l0)); trivial.
    rewrite <- (element_at_list_concat' _ (rev vf)); trivial.
    intros He Hv Hpat.
    rewrite Hstack in h3.
    cut ((Node (symbol cnm) l0 :: lexpr)[0] = Some (Node (symbol cnm) l0)); [intro He' | simpl; trivial].
    cut ((Node cnm vf :: l)[0] = Some (Node cnm vf)); [intro Hv' | simpl; trivial].
    cut (tree_is_pattern (Node (symbol cnm) l0)); [intro Hpat' | idtac].
    generalize (h3 0 (Node (symbol cnm) l0) (Node cnm vf) He' Hv' Hpat').
    generalize (apply_to_forest cnm rho l0).
    intro dd; inversion dd as [Heq]; clear dd He' Hv' Hpat' Hpat.
    rewrite Heq; intro H.
    inversion H.
    assert (H' : map tree_name_to_tree_Name (rev vf) = map (apply rho) (rev l0)).
    rewrite map_rev_commut; rewrite map_rev_commut.
    rewrite <- H1; trivial.
    cut (Some (tree_name_to_tree_Name v) = Some (apply rho e)).
    intro dd; inversion dd; trivial.
    rewrite <- (element_at_list_map _ _ (rev vf) tree_name_to_tree_Name j0 v Hv).
    rewrite <- (element_at_list_map _ _ (rev l0) (apply rho) j0 e He).
    rewrite <- H'; trivial.
    cut ((fcn_bytecode gcn)[frm_pc f|C] = i_branch (fcn_size gcn) cnm j Cj); [intro Hinstr | generalize case_instr; apply element_at_unsafe_to_safe].
    apply (Pattern_branch gcn (get_some_in_functions  gcn (frm_fun f) functions Hgcn) (frm_pc f) C cnm j Cj _ _ _ Hinstr h1).
    rewrite rev_length; rewrite <- Hlenvf; trivial.
    rewrite <- rev_length; trivial.
    rewrite push_list_is_app_rev; rewrite push_list_is_app_rev.
    rewrite concat_length; rewrite concat_length.
    rewrite rev_length; rewrite rev_length; rewrite Hlenvf; replace (length lexpr) with (length l); trivial.
    symmetry; rewrite Hstack in h4; simpl in h4; generalize h4; auto with arith.
    
  (* proving that lengths are equal*)
    
    rewrite Hstack in h3.
    cut (tree_name_to_tree_Name (Node cnm vf) = apply rho (Node (symbol cnm) l0)); [idtac | apply (h3 0); trivial].
    rewrite apply_to_forest.
    simpl.
    intro Heq; inversion Heq.
    rewrite (map_length _ _ (apply rho) l0).
    rewrite <- H0; symmetry; apply map_length.
    cut ((fcn_bytecode gcn)[frm_pc f|C] = i_branch (fcn_size gcn) cnm j Cj); [intro Hinstr | generalize case_instr; apply element_at_unsafe_to_safe].
    apply (Pattern_branch gcn (get_some_in_functions  gcn (frm_fun f)
    functions Hgcn) (frm_pc f) C cnm j Cj _ _ _ Hinstr h1).

    intros dd F; inversion F.
    cut False; [intro F; inversion F | trivial].
    rewrite Hstack in h3.
    cut (tree_name_to_tree_Name (Node cnm vf) = apply rho (Node (symbol n) l0)); [idtac | apply (h3 0); trivial].
    rewrite apply_to_forest.
    simpl.
    intro Heq; inversion Heq; subst; elim case_eq; trivial.
    cut ((fcn_bytecode gcn)[frm_pc f|C] = i_branch (fcn_size gcn) cnm j Cj); [intro Hinstr | generalize case_instr; apply element_at_unsafe_to_safe].
    apply (Pattern_branch gcn (get_some_in_functions  gcn (frm_fun f) functions Hgcn) (frm_pc f) C cnm j Cj _ _ _ Hinstr h1).
    symmetry; generalize case_instr; apply element_at_unsafe_to_safe.
    rewrite Hfcn in Hgcn; inversion Hgcn; trivial.
  (* part 2 *)
    intros i fi fpi Hfi Hfpi.
    destruct i; simpl.
    inversion Hfi; inversion Hfpi; subst.
    simpl.
    apply (Hwsvirtual 0 f fpi); simpl; trivial.
    apply (Hwsvirtual (S i) fi fpi); simpl; trivial.
    generalize case_instr; apply element_at_unsafe_some; trivial.
    
  (* branch else *)
    cut (frm_pc f < fcn_size fcn).
    intro C.
    inversion Hws; subst.
    generalize H; elim H0; intros Hwstop Hwsvirtual Hwt.
    cut ((f :: M0)[0] = Some f); [intro Hf | trivial].
    generalize (Hwstop f Hf); clear Hwstop H H0; intro Hwstop.
    inversion Hwt; subst.
    generalize H; elim H0; intros Hwttop Hwtvirtual Hwf.
    generalize (Hwttop f Hf); clear Hwttop H H0 Hf; intro Hwttop.
    constructor.
    generalize Hwt Hred ; apply reduction_keeps_welltyped; trivial.
    split.
    intros g' Hg' gcn Hgcn Cg; simpl; simpl in Hgcn; simpl in Cg.
    inversion Hg'; subst g'; clear Hg'; simpl in Hgcn.
    cut (fcn = gcn);[intro; subst | rewrite Hgcn in Hfcn; inversion Hfcn; trivial].
    elim (Hwstop gcn Hgcn C); intros s h.
    elim h; clear h; intros lexpr h.
    elim h; clear h; intros rho h.
    elim h; clear h; intros h1 h.
    elim h; clear h; intros h2 h.
    elim h; clear h; intros h3 h4.
    generalize (Wshi_Kildall gcn (get_some_in_functions  gcn (frm_fun f) functions Hgcn) (frm_pc f) C).
    unfold Wshi.
    replace ((fcn_bytecode gcn)[frm_pc f|C]) with (i_branch (fcn_size gcn) cnm j Cj).
    rewrite h1.
    destruct lexpr.
    intro F; inversion F.
    destruct t.
    intro F; inversion F.
    destruct n.
    destruct l0.
    CaseEq (Get_constr cnm).
    intros c case_c.
    CaseEq (element_at (Kildall_Shapes gcn (get_some_in_functions  gcn (frm_fun f) functions Hgcn)) j Cj).
    intros case_f_j HF; elim HF; intro F; inversion F.
    intros case_f_j HF; elim HF; intro F; inversion F.
    intros l0 l1 case_f_j h; elim h; clear h; intros h dd; clear dd.
    exists l0; exists l1.
    exists rho; elim h; clear h; intros; subst.
    repeat split; trivial.
    rewrite <- case_f_j; apply element_at_irrel.
    intros dd F; inversion F.
    intro F; inversion F.
    
    elim (eq_name_dec cnm n); intro case_eq.
    subst.
    elim neq_cnm_dnm; rewrite Hstack in h3.
    cut (tree_name_to_tree_Name (Node dnm vf) = apply rho (Node (symbol n) l0)); [idtac | apply (h3 0); trivial].
    rewrite apply_to_forest.
    simpl; intro Heq; inversion Heq; trivial.
    cut (element_at (fcn_bytecode gcn) (frm_pc f) C = i_branch (fcn_size gcn) n j Cj); 
      [intro Hinstr | generalize case_instr; apply element_at_unsafe_to_safe].
    apply (Pattern_branch gcn 
      (get_some_in_functions  gcn (frm_fun f) functions Hgcn) 
      (frm_pc f) 
      C n j Cj _ _ _ Hinstr h1).

    CaseEq (element_at (Kildall_Shapes gcn (get_some_in_functions  gcn (frm_fun f) functions Hgcn)) j Cj).
    intros dd F; inversion F.
    intros dd F; inversion F.
    intros l1 l2 case_shapes_j Hshapesj.
    exists l1; exists l2; exists rho.
    elim Hshapesj; intros; subst.
    repeat split; trivial.
    rewrite <- case_shapes_j; apply element_at_irrel.
    symmetry; generalize case_instr; apply element_at_unsafe_to_safe.
  (* part 2 *)
    intros i fi fpi Hfi Hfpi.
    destruct i; simpl.
    inversion Hfi; inversion Hfpi; subst.
    simpl.
    apply (Hwsvirtual 0 f fpi); simpl; trivial.
    apply (Hwsvirtual (S i) fi fpi); simpl; trivial.
    generalize case_instr; apply element_at_unsafe_some.
    cut (welltyped_configuration M' /\ frames_args_length M'); [intro H; elim H; trivial | generalize Hred; apply reduction_length; trivial].
    split.
    inversion Hws; trivial.
    assumption.
  Qed.


  Lemma wellshaped_init_configuration : forall (fexec : name) (argsexec : list value) (fcnexec : function),
    Get_function fexec = Some fcnexec -> 
    tree_list_typing argsexec (rev (fcn_args fcnexec)) ->
    wellshaped_configuration (Init_configuration fexec argsexec).
  Proof.
    intros fexec argsexec fcnexec Hfexec Htyping.
    constructor.
    apply welltyped_init_configuration with fcnexec; trivial.
    rewrite rev_lin_is_rev; trivial.
    split.
    intros f Hf; inversion Hf; subst f; clear Hf.
    exists (nil (A := subst_elem)).
    exists (init_vars fcnexec).
    simpl in Hget; rewrite Hget in Hfexec; inversion Hfexec; subst fcn.
    cut (length argsexec = length (rev (fcn_args fcnexec))); [intro Hlen; rewrite rev_length in Hlen| apply (list_typing_length argsexec (rev (fcn_args fcnexec)))].
    CaseEq (init_subst (rev argsexec)).
    intros rho case_rho.
    exists rho.
    simpl; repeat split.
    rewrite (element_at_irrel _ _ (Kildall_Shapes fcnexec (get_some_in_functions  fcnexec fexec functions Hget)) 0 C (nonvoidfcn fcnexec (get_some_in_functions  fcnexec fexec functions Hget))).
    rewrite Kildall_Shapes_0.
    unfold Sss_init; rewrite element_at_in_replaced; trivial.
    rewrite map_id.
    unfold init_vars; simpl.
    rewrite <- (rev_involutive argsexec). 
    rewrite <- rev_lin_is_rev.
    apply init_stack_shaping.
    rewrite <- Hlen ; trivial.
    rewrite <- case_rho; unfold init_subst.
    rewrite rev_length; trivial.
    intros j e v He Hv Hpat.
    unfold init_vars in He.
    rewrite (element_at_init_vars (length (fcn_args fcnexec)) 0 0 j e He).
    symmetry; rewrite <- (init_subst_apply (length (fcn_args fcnexec)) 0 (length argsexec - S j) rho (rev argsexec) v); trivial.
    rewrite plus_comm; simpl; trivial.
    rewrite <- Hlen; trivial.
    rewrite <- element_at_list_rev; trivial.
    generalize Hv; apply element_at_list_some.
    rewrite <- Hlen; trivial.
    rewrite <- case_rho; unfold init_subst.
    rewrite rev_length; trivial.
    rewrite Hlen; apply init_vars_length.
    intro F.
    elim (subst_length (length argsexec) 0 (rev argsexec)); trivial.
    apply rev_length.
    rewrite <- F; unfold init_subst; rewrite rev_length; trivial.
    assumption.
    intros i fi fpi Hfi Hfpi; inversion Hfpi.
  Qed.


  Lemma wellshaped_execution : forall (fexec : name) (argsexec : list value) (fcnexec : function) (L : list configuration), 
    Get_function fexec = Some fcnexec -> 
    tree_list_typing argsexec (rev (fcn_args fcnexec)) ->
    execution fexec argsexec L -> 
    forall  (M : configuration), In M L -> wellshaped_configuration M /\ frames_args_length M.
  Proof.    
    intros fexec argsexec fcnexec L Hget Htyping; apply (reduction_to_execution (fun (M : configuration) => wellshaped_configuration M /\ frames_args_length M)).
    split.
    apply wellshaped_init_configuration with fcnexec; trivial.
    intros f fcn Hin Hfcn.
    elim Hin; clear Hin; intro Hin.
    subst f; (simpl in *).
    rewrite Hget in Hfcn; inversion Hfcn; subst fcn.
    rewrite <- (rev_length _ (fcn_args fcnexec)).
    generalize Htyping; apply list_typing_length.
    inversion Hin.
    apply reduction_keeps_wellshaped.
  Qed.


End machine_shapes.
