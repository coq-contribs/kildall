  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : machine_types.v				         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : Type verification                               *)
  (***************************************************************)


Section machine_types.


  Add LoadPath "../aux".
  Add LoadPath "../lists".
  Add LoadPath "../kildall".

  Require Export machine.
  Require Export typing.
  Require Export inst_types.

  Notation configuration := (list frame).
  Notation Get_function := (get_function_by_name functions).
  Notation Get_constr := (get_constr_by_name constructors).
  Notation Frm := (mkframe).
  
  (* initial function state = [(Types argsuments_types); bot;...; bot] *)
  Definition ss_init (fcn : function) := 
    (constant_list (fcn_size fcn) Bot_T)[0<-(Types (rev (fcn_args fcn)))].
  
  (* result of type analysis algorithm run on the initial function state *)
  Definition Kildall_Types (fcn : function) (Hin : In fcn functions) := 
    Kildall_types fcn (lrs_functions fcn Hin) (ss_init fcn).
  
  (* every function in the list functions passed type verification *)
  Hypothesis Passed_Kildall : forall (fcn : function) (Hin : In fcn functions),
    ~ Top_T INv (Kildall_Types fcn Hin).
  
  (* definition of a well-typed frame : type of the elements in the stack are those computed by Kildall_types *)
  Definition welltyped_frame (f : frame) : Prop :=
    forall (fcn : function) (Hget : Get_function (frm_fun f) = Some fcn) 
      (C : (frm_pc f) < (fcn_size fcn)), 
      stack_typing (frm_stack f) ((Kildall_Types fcn (get_some_in_functions fcn (frm_fun f) functions Hget))[frm_pc f|C]).
  
  (* extention of well-typedness to configurations *)
  Inductive welltyped_configuration : configuration -> Prop :=
    welltyped_conf : forall (M : configuration) , wellformed_configuration M -> 
      (* top frame well typed *)
      (forall (f : frame), element_at_list M 0 = Some f -> welltyped_frame f) /\
      (* stack i @ args i-1 well typed *)
      (forall (i : nat) (fi fpi : frame), 
        element_at_list M i = Some fi -> element_at_list M (S i) = Some fpi ->
        welltyped_frame (Frm (frm_fun fpi) (frm_pc fpi) ((frm_args fi)++(frm_stack fpi)) (frm_args fpi))) ->
      welltyped_configuration M.
  
  (* type verifications algorithm produces a function state ss for which, for all p<|ss|, Wti ss p holds *) 
  

  Lemma Wti_Kildall : forall (fcn : function) (Hin : In fcn functions) (p : nat) (C : p < (fcn_size fcn)), 
    Wti fcn (Kildall_Types fcn Hin) p C.
  Proof.
    intros fcn Hin p C.
(*    apply (top_free_to_wti Sigma (fcn_size fcn) 
      (Succs ((fcn_size fcn)) (fcn_bytecode fcn) (lrs_functions fcn Hin)) 
      (Step fcn) (Wti fcn) r (Top_T) f (Step_Succs_same_length fcn (lrs_functions fcn Hin))
      eq_Sigma_dec r_is_semilattice wfr (Succs_equiv (fcn_size fcn) (fcn_bytecode fcn) (lrs_functions fcn Hin))
      (Step_equiv fcn) (monotone_Step fcn)).*)
    generalize (monotone_step_imp_kildall_dfa Sigma (fcn_size fcn) 
      (Succs ((fcn_size fcn)) (fcn_bytecode fcn) (lrs_functions fcn Hin)) 
      (Step fcn) r f (Step_Succs_same_length fcn (lrs_functions fcn Hin)) 
      eq_Sigma_dec r_is_semilattice wfr 
      (Succs_equiv (fcn_size fcn) (fcn_bytecode fcn) (lrs_functions fcn Hin)) 
      (Step_equiv fcn) (monotone_Step fcn) (ss_init fcn)).
    unfold Is_data_flow_analyser;  unfold Kildall_Types.
    intro is_dfa; elim is_dfa; clear is_dfa; intros dfa1 H.
    elim H; clear H; intros dfa2 H; clear H.
    apply (stable_imp_Wti fcn (lrs_functions fcn Hin)).
    apply (Passed_Kildall fcn Hin). 
    apply dfa1.
  Qed.

  (* state of the entry point is left unchanged by algorithm Kildall_types *)
  Lemma Kildall_Types_0 : forall (fcn : function) (Hin : In fcn functions), 
    (Kildall_Types fcn Hin)[0|nonvoidfcn fcn Hin] = 
    (ss_init fcn)[0|nonvoidfcn fcn Hin].
  Proof.
    intros fcn Hin.
    generalize (monotone_step_imp_kildall_dfa Sigma (fcn_size fcn) 
      (Succs ((fcn_size fcn)) (fcn_bytecode fcn) (lrs_functions fcn Hin)) 
      (Step fcn) r f (Step_Succs_same_length fcn (lrs_functions fcn Hin)) 
      eq_Sigma_dec r_is_semilattice wfr 
      (Succs_equiv (fcn_size fcn) (fcn_bytecode fcn) (lrs_functions fcn Hin)) 
      (Step_equiv fcn) (monotone_Step fcn) (ss_init fcn)).
    unfold Is_data_flow_analyser.
    intro is_dfa; elim is_dfa; clear is_dfa; intros dfa1 H.
    elim H; clear H; intros dfa2 dfa3.
    cut (r ((ss_init fcn)[0|nonvoidfcn fcn Hin]) 
      ((Kildall_Types fcn Hin)[0|nonvoidfcn fcn Hin])).
    intro Hr.
    CaseEq ((Kildall_Types fcn Hin)[0|nonvoidfcn fcn Hin]).
  (* case (Kildall_Types fcn)[0] = Top_T : contradiction  with passed_kildall *)
    intro case; elim (Passed_Kildall fcn Hin); rewrite <- case; apply element_at_belong.
  (* case (Kildall_Types fcn)[0] = Bot_T, impossible with Hr and definition of ss_init *)
    intro case; generalize Hr; clear Hr; rewrite case.
    intro Hr; destruct ((ss_init fcn)[0|nonvoidfcn fcn Hin]); inversion Hr.
    trivial.
    intros l case.
    generalize Hr; clear Hr; rewrite case.
    unfold ss_init.
    rewrite element_at_in_replaced.
    intro Hr; inversion Hr.
    trivial.
    unfold Kildall_Types; generalize dfa2; unfold Vector_pointwise; apply vector_pointwise_to_element.
  Qed.

  Lemma red_return_keeps_welltyped : forall (M0 : configuration) (f g : frame) (fcn : function)
    (v0 : value) (l : list value),
    Get_function (frm_fun f) = Some fcn ->
    (fcn_bytecode fcn)[frm_pc f|_] = Some (i_return (fcn_size fcn)) ->
    frm_stack f = v0 :: l -> wellformed_configuration (f :: g :: M0) ->
    reduction (f :: g :: M0)
    (mkframe (frm_fun g) (S (frm_pc g)) (v0 :: frm_stack g) (frm_args g) :: M0) ->
    welltyped_frame f ->  (forall (i : nat) (fi fpi : frame),
      element_at_list (f :: g :: M0) i = Some fi ->
      element_at_list (f :: g :: M0) (S i) = Some fpi ->
      welltyped_frame
      (mkframe (frm_fun fpi) (frm_pc fpi)
        (frm_args fi ++ frm_stack fpi)(frm_args fpi))) ->
    welltyped_configuration
    (mkframe (frm_fun g) (S (frm_pc g)) (v0 :: frm_stack g) (frm_args g) :: M0).
  Proof.    
    intros M0 f g fcn v0 l Hfcn case_instr Hstack Hwf Hred Hwttop Hwtvirtual.
    constructor.
  (* M' is well-formed : *)
    apply (reduction_keeps_wellformed (f::g::M0)); trivial.
    cut (element_at_list (f :: g :: M0) 0 = Some f); [intro H1 | simpl; trivial].
    cut (element_at_list (f :: g :: M0) (S 0) = Some g); [intro H1' | simpl; trivial].
    split.
  (* top frame of M is well-typed : *)
    intros f' Hf' fcn' Hfcn' C.
    inversion Hf'; subst f'; trivial.
    cut (frm_pc g < fcn_size fcn'); [intro C' | generalize C; auto with arith].
    generalize (Hwtvirtual 0 f g H1 H1' fcn' Hfcn' C'); simpl.
    generalize (Passed_Kildall fcn' (get_some_in_functions fcn' (frm_fun g) functions Hfcn')); intro notop'.
    generalize (Wti_Kildall fcn' (get_some_in_functions fcn' (frm_fun g) functions Hfcn') (frm_pc g) C'). 
    unfold Wti.
    CaseEq ((Kildall_Types fcn' (get_some_in_functions fcn' (frm_fun g) functions Hfcn'))[frm_pc g|C']).
    (* case (Kildall_Types fcn')[pcg] = Top_T *) 
    intro case; elim notop'; rewrite <- case; apply element_at_belong.
  (* case (Kildall_Types fcn')[pcg] = Bot_T *) 
    unfold stack_typing; simpl.
    intros case dd F; inversion F.
  (* case (Kildall_Types fcn')[pcg] = Types l' *) 
    intros l' casel'.
    cut ((fcn_bytecode fcn')[frm_pc g|C'] = 
      i_call (fcn'.(fcn_size)) ((frm_fun f)) (length (frm_args f))).
    intro Hcall; rewrite Hcall; simpl. (* frame g created frame f *)
    CaseEq (split_k_elements (length (frm_args f)) l'); [idtac | intros dd F; inversion F].
    intros p casesplit; destruct p as [lk lr].
    rewrite Hfcn; simpl.
    elim (eq_list_name_dec (rev lk) (fcn_args fcn)); [intro caseeq | intros dd F; inversion F].
    CaseEq (element_at_unsafe (Kildall_Types fcn' 
      (get_some_in_functions  fcn' (frm_fun g) functions Hfcn')) (S (frm_pc g))); 
    [intros s casegS | intros dd F; inversion F].
    destruct s.
    intro F; inversion F.
    intro F; inversion F.
    elim (eq_list_name_dec  ((fcn_ret fcn) :: lr) l0); intros caseeq' F; [clear F | inversion F].
    rewrite (element_at_unsafe_to_safe Sigma (fcn_size fcn') 
      (Kildall_Types fcn' (get_some_in_functions  fcn' (frm_fun g) functions Hfcn')) 
      (S (frm_pc g)) C (Types l0) casegS).
    subst l0; simpl.
    generalize (split_k_elements_ok name (length (frm_args f)) l' lk lr casesplit); intro; subst l'.
    intro surtype.
    assert (H_return_type : tree_typing v0 (fcn_ret fcn)).
    (* return type *)
    cut (frm_pc f < fcn_size fcn); [intro Cf | generalize case_instr; apply element_at_unsafe_some].
    generalize (Hwttop fcn Hfcn Cf). (* frame f is well-typed *)
    rewrite Hstack.
    generalize (Wti_Kildall fcn (get_some_in_functions  fcn (frm_fun f) functions Hfcn) (frm_pc f) Cf). 
    unfold Wti.
    generalize (Passed_Kildall fcn (get_some_in_functions  fcn (frm_fun f) functions Hfcn)); intros notopf.
    CaseEq ((Kildall_Types fcn (get_some_in_functions fcn (frm_fun f) functions Hfcn))[frm_pc f|Cf]).
    intros h F; inversion F.
    unfold stack_typing; simpl; intros case dd F; inversion F.
    intros l2 casef.
    cut ((fcn_bytecode fcn)[frm_pc f|Cf] = i_return (fcn_size fcn)); 
      [intro case_f_pc | generalize case_instr; apply element_at_unsafe_to_safe].
    rewrite case_f_pc; simpl.
    destruct l2; simpl.
    intro F; inversion F.
    elim (eq_name_dec n (fcn_ret fcn)); intros caseeqf F; [clear F | inversion F] .
    subst n; intro h; inversion h.
    constructor 2 with const; trivial.
    constructor.
    assert (H_stack_g : tree_list_typing (frm_stack g) lr).
    (* stack g : *)
    generalize surtype; apply sub_list_typing_right.
    symmetry; apply (split_k_elements_length name (length (frm_args f)) (lk ++ lr) lk lr); assumption.
    apply cons_list_typing; trivial.
    (* from call *)
    cut (element_at_list (f :: g :: M0) 0 = Some f); [intro Hfin | simpl; trivial]. 
    elim (Hwf 0 f g fcn fcn' Hfin); clear Hwf; intros dd Hwf.
    elim (Hwf Hfcn); clear dd Hwf; intros dd Hwf.
    apply element_at_unsafe_to_safe.
    apply Hwf; simpl; trivial.
    (* Part 2 : virtual frames in M' are well-typed *)
    intros i fi fpi Hfi Hfpi.
    destruct i.
  (* i = 0 *)
    simpl in Hwttop; simpl in Hwtvirtual.
    cut (element_at_list (f :: g :: M0) 1 = Some g); [intro Hgin | simpl; trivial].
    cut (element_at_list (f :: g :: M0) 2 = Some fpi); 
      [intro Hfpiin | simpl; simpl in Hfpi; rewrite Hfpi; trivial].
    generalize (Hwtvirtual 1 g fpi Hgin Hfpiin).
    inversion Hfi.
    cut (frm_args g = frm_args fi); [intro h; rewrite h; trivial | inversion Hfi; trivial].
  (* i > 0 *)
    apply (Hwtvirtual (S (S i)) fi fpi).
    simpl; simpl in Hfi.
    rewrite Hfi; simpl; trivial.
    simpl; simpl in Hfpi.
    rewrite Hfpi; simpl; trivial.
  Qed.


  Lemma red_load_keeps_welltyped : forall (M0 : configuration) (f : frame) (fcn : function)
    (j : nat) (vj : value),  
    Get_function (frm_fun f) = Some fcn ->
    (fcn_bytecode fcn)[frm_pc f|_] = Some (i_load (fcn_size fcn) j) ->
    element_at_list (rev_lin (frm_stack f)) j = Some vj ->
    wellformed_configuration (f :: M0) ->
    reduction (f :: M0)
    (mkframe (frm_fun f) (S (frm_pc f)) (vj :: frm_stack f) (frm_args f) :: M0) ->
    welltyped_frame f -> (forall (i : nat) (fi fpi : frame),
      element_at_list (f :: M0) i = Some fi ->
      element_at_list (f :: M0) (S i) = Some fpi ->
      welltyped_frame
      (mkframe (frm_fun fpi) (frm_pc fpi)
        (frm_args fi ++ frm_stack fpi) (frm_args fpi))) ->
    welltyped_configuration
    (mkframe (frm_fun f) (S (frm_pc f)) (vj :: frm_stack f) (frm_args f) :: M0).
  Proof.    
    intros M0 f fcn j vj Hfcn case_instr Hvj Hwf Hred Hwttop Hwtvirtual.
    split.
  (* M' is well-formed *)
    apply (reduction_keeps_wellformed (f::M0)); trivial.
    split.
  (* top frame well-typed *)
    generalize Hwttop; unfold welltyped_frame; simpl.
    clear Hwttop; intros Hwttop f' Hf' fcn' Hfcn' C.
    inversion Hf'; subst f'; clear Hf'.
    cut (frm_pc f < fcn_size fcn'); [intro C' | generalize C; auto with arith].
    generalize (Hwttop fcn' Hfcn' C'); clear Hwttop.
    generalize (Wti_Kildall fcn' (get_some_in_functions  fcn' (frm_fun f) functions Hfcn') (frm_pc f) C'). 
    unfold Wti.
    generalize (Passed_Kildall fcn' (get_some_in_functions  fcn' (frm_fun f) functions Hfcn')); 
      intros notop'.
    CaseEq ((Kildall_Types fcn' (get_some_in_functions fcn' (frm_fun f) functions Hfcn'))[frm_pc f|C']).
  (* (Kidall_Types fcn')[pc f] = Top_T *)
    intros case F; inversion F.
  (* (Kidall_Types fcn')[pc f] = Bot_T *)
    unfold stack_typing; simpl; intros case dd F; inversion F.
  (* (Kidall_Types fcn')[pc f] = Types l *)
    intros l case.
    cut ((fcn_bytecode fcn')[frm_pc f|C'] = i_load (fcn_size fcn') j). 
    intro case_load; rewrite case_load; simpl.
    CaseEq (element_at_unsafe (Kildall_Types fcn' 
      (get_some_in_functions  fcn' (frm_fun f) functions Hfcn')) (S (frm_pc f))); 
    [intros s caseS; destruct s | intros dd F; inversion F].
    intro F; inversion F.
    intro F; inversion F.
    CaseEq (element_at_list (rev l) j); [intros tj casetj | intros dd F; inversion F].
    elim (eq_list_name_dec  (tj :: l) l0); intros case' F; [clear F | inversion F].
    rewrite (element_at_unsafe_to_safe Sigma (fcn_size fcn') 
      (Kildall_Types fcn' (get_some_in_functions  fcn' (frm_fun f) functions Hfcn')) 
      (S (frm_pc f)) C (Types l0) caseS).
    subst l0; simpl.
    intro h; apply cons_list_typing; [idtac | assumption].
    apply (element_at_list_typing j (rev (frm_stack f)) (rev l)). 
    rewrite <- rev_lin_is_rev; rewrite <- rev_lin_is_rev.
    apply rev_list_typing.
    assumption.
    assumption.
    rewrite <- rev_lin_is_rev; assumption.
    apply element_at_unsafe_to_safe.
    simpl in Hfcn'; rewrite Hfcn' in Hfcn; inversion Hfcn; subst fcn'; assumption.
    (* Part 2 : virtual frames from M' are well-typed *)
    intros i fi fpi Hfi Hfpi.
    destruct i.
    cut (element_at_list (f :: M0) 0 = Some f); [intro Hf | simpl; trivial].
    cut (element_at_list (f :: M0) 1 = Some fpi).
    intro Hfpi'; generalize (Hwtvirtual 0 f fpi Hf Hfpi').
    replace (frm_args f) with (frm_args fi).
    trivial.
    simpl in Hfi.
    inversion Hfi.
    simpl; trivial.
    simpl; simpl in Hfpi.
    rewrite Hfpi.
    trivial.
    cut (element_at_list (f :: M0) (S i) = Some fi).
    cut (element_at_list (f :: M0) (S (S i)) = Some fpi).
    intros Hfpi' Hfi'.
    apply (Hwtvirtual (S i) fi fpi Hfi' Hfpi').
    simpl; simpl in Hfpi.
    assumption.
    simpl; simpl in Hfi; assumption.
  Qed.


  Lemma red_call_keeps_welltyped : forall (M0 : configuration) (f : frame) (fcn gcn : function)
    (gnm : name) (gar : nat) (vargs l : list value), 
    Get_function (frm_fun f) = Some fcn->
    (fcn_bytecode fcn)[frm_pc f|_] = Some (i_call (fcn_size fcn) gnm gar) ->
    Get_function gnm = Some gcn -> split_k_elements gar (frm_stack f) = Some (vargs, l)->
    wellformed_configuration (f :: M0)->
    reduction (f :: M0)
    (mkframe gnm 0 vargs vargs :: mkframe (frm_fun f) (frm_pc f) l (frm_args f) :: M0) ->
    welltyped_frame f -> (forall (i : nat) (fi fpi : frame),
      element_at_list (f :: M0) i = Some fi ->
      element_at_list (f :: M0) (S i) = Some fpi ->
      welltyped_frame (mkframe (frm_fun fpi) (frm_pc fpi)
        (frm_args fi ++ frm_stack fpi) (frm_args fpi))) ->
    welltyped_configuration (mkframe gnm 0 vargs vargs 
      :: mkframe (frm_fun f) (frm_pc f) l (frm_args f) :: M0).
  Proof.    
    intros M0 f fcn gcn gnm gar vargs l Hfcn case_instr Hgcn case_split_stack Hwf Hred Hwttop Hwtvirtual.
    constructor.
  (* M' is well-formed : *)
    apply (reduction_keeps_wellformed (f::M0)); trivial.
    split.
  (* top frame of M' is well-typed : *)
    unfold welltyped_frame.
    simpl; intros f' Hf' fcn' Hfcn' C.
    inversion Hf'; subst f'; clear Hf'; simpl.
    rewrite (element_at_irrel Sigma (fcn_size fcn') 
      (Kildall_Types fcn' (get_some_in_functions  fcn' gnm functions Hfcn')) 
      0 C (nonvoidfcn fcn' (get_some_in_functions  fcn' gnm functions Hfcn'))).
    rewrite (Kildall_Types_0 fcn' (get_some_in_functions  fcn' gnm functions Hfcn')).
    unfold ss_init.
    rewrite element_at_in_replaced.
    unfold welltyped_frame in Hwttop.
    cut (frm_pc f < fcn_size fcn); [intro Cf | generalize case_instr; apply element_at_unsafe_some].
    generalize (Hwttop fcn Hfcn Cf).
    generalize (Wti_Kildall fcn (get_some_in_functions fcn (frm_fun f) functions Hfcn) (frm_pc f) Cf). 
    unfold Wti.
    CaseEq ((Kildall_Types fcn (get_some_in_functions fcn (frm_fun f) functions Hfcn))[frm_pc f|Cf]).
  (* case (Kildall_Types)fcn [pc f] = Top_T *)
    intros dd F; inversion F.
  (* case (Kildall_Types)fcn [pc f] = Bot_T *)
    generalize (Passed_Kildall fcn (get_some_in_functions  fcn (frm_fun f) functions Hfcn)); intros P1 case.
    unfold stack_typing; simpl; intros dd F; inversion F.
  (* case (Kildall_Types)fcn [pc f] = Types l0 *)
    intros l0 case.
    replace ((fcn_bytecode fcn)[frm_pc f|Cf]) with (i_call (fcn_size fcn) gnm gar).
    CaseEq (split_k_elements gar l0); 
    [intros p case_split; destruct p as [lk lr]| intros dd F; inversion F].
    simpl in Hfcn'; (rewrite Hfcn').
    elim (eq_list_name_dec  (rev lk) (fcn_args fcn')); intros case' F; [clear F | inversion F].
    cut (l0 = lk ++ lr); [intro Hl0 | generalize case_split; apply split_k_elements_ok].
    subst l0.
    cut (frm_stack f = vargs ++ l); [intro Hstack | generalize case_split_stack; apply split_k_elements_ok].
    rewrite Hstack.
    unfold stack_typing.
    rewrite <- case'.
    rewrite rev_involutive.
    apply sub_list_typing_left.
    cut (length lk = gar); 
      [intro dd; rewrite dd; clear dd | generalize case_split; apply split_k_elements_length].
    generalize case_split_stack; apply split_k_elements_length.
    symmetry; generalize case_instr; apply element_at_unsafe_to_safe.
    (* part 2 : virtual frames from M' are well-typed *)
    intros i fi fpi.
    destruct i; simpl.
  (* i = 0 *)
    intros Hfi Hfpi; inversion Hfi; inversion Hfpi.
    subst fi fpi.
    simpl.
    rewrite <- (split_k_elements_ok value gar (frm_stack f) vargs l case_split_stack).
    apply Hwttop; destruct f; simpl; trivial.
  (* i > 0 *)
    intros Hfi Hfpi.
    destruct i.
    replace (frm_args fi) with (frm_args f).
    apply (Hwtvirtual 0 f fpi).
    simpl; trivial.
    simpl; destruct (element_at_list M0 0); trivial.
    inversion Hfi; simpl; trivial.
    generalize (Hwtvirtual (S i) fi fpi); simpl.
    destruct (element_at_list M0 i).
    destruct (element_at_list M0 (S i)).
    intro h; apply (h Hfi Hfpi).
    intro h; apply (h Hfi Hfpi).
    destruct (element_at_list M0 (S i)).
    intro h; apply (h Hfi Hfpi).
    intro h; apply (h Hfi Hfpi).
  Qed.

  Lemma red_build_keeps_welltyped : forall (M0 : configuration) (f : frame) (fcn : function)
    (c : constr) (cnm : name) (car : nat) (vargs l : list value), 
    Get_function (frm_fun f) = Some fcn ->
    (fcn_bytecode fcn)[frm_pc f|_] = Some (i_build (fcn_size fcn) cnm car) ->
    Get_constr cnm = Some c -> split_k_elements car (frm_stack f) = Some (vargs, l) ->
    wellformed_configuration (f :: M0) ->
    reduction (f :: M0)
    (mkframe (frm_fun f) (S (frm_pc f))
      (Node cnm (rev_lin vargs) :: l) (frm_args f) :: M0) ->
    welltyped_frame f -> (forall (i : nat) (fi fpi : frame),
      element_at_list (f :: M0) i = Some fi ->
      element_at_list (f :: M0) (S i) = Some fpi ->
      welltyped_frame (mkframe (frm_fun fpi) (frm_pc fpi)
        (frm_args fi ++ frm_stack fpi) (frm_args fpi))) ->
    welltyped_configuration
    (mkframe (frm_fun f) (S (frm_pc f))
      (Node cnm (rev_lin vargs) :: l) (frm_args f) :: M0).
  Proof.
    intros M0 f fcn c cnm car vargs l Hfcn case_instr Hc case_split_stack Hwf Hred Hwttop Hwtvirtual.
    constructor.
  (* M' is well-formed : *)
    apply (reduction_keeps_wellformed (f::M0)); trivial.
    split.
  (* top frame of M' well-typed : *)
    unfold welltyped_frame; simpl; intros f' Hf' fcn' Hfcn' C.
    (inversion Hf'; subst f'; clear Hf').
    (simpl in Hfcn'; rewrite Hfcn' in Hfcn; inversion Hfcn; subst fcn').
    simpl in C.
    cut (frm_pc f < fcn_size fcn); [intro C' | generalize C; auto with arith].
    cut (element_at_list (f :: M0) 0 = Some f); [intro Hf | trivial].
    generalize (Hwttop fcn Hfcn' C').
    generalize (Wti_Kildall fcn (get_some_in_functions  fcn (frm_fun f) functions Hfcn') (frm_pc f) C'). 
    unfold Wti.
    CaseEq ((Kildall_Types fcn (get_some_in_functions fcn (frm_fun f) functions Hfcn'))[frm_pc f|C']).
  (* (Kildall_Types fcn)[pc f] = Top_T *)
    intros dd F; inversion F.
  (* (Kildall_Types fcn)[pc f] = Bot_T *)
    generalize (Passed_Kildall fcn (get_some_in_functions  fcn (frm_fun f) functions Hfcn')); 
      intros P1 case.
    unfold stack_typing; simpl; intros dd F; inversion F.
  (* (Kildall_Types fcn)[pc f] = Types l0 *)
    intros l0 case.
    replace ((fcn_bytecode fcn)[frm_pc f|C']) with (i_build (fcn_size fcn) cnm car).
    CaseEq (split_k_elements car l0); 
    [intros p case_split; destruct p | intros dd F; inversion F].
    rewrite Hc.
    elim (eq_list_name_dec  (rev l1) (cons_args c)); [intro case_eq | intros dd F; inversion F].
    CaseEq (element_at_unsafe 
      (Kildall_Types fcn (get_some_in_functions  fcn (frm_fun f) functions Hfcn')) (S (frm_pc f))); 
    [intros s case_ss | intros dd F; inversion F].
    cut (((Kildall_Types fcn (get_some_in_functions fcn (frm_fun f) functions Hfcn'))[S (frm_pc f)|C]) = s); 
    [intro case' | generalize case_ss; apply element_at_unsafe_to_safe].
    (simpl; rewrite case').
    destruct s.
    intro F; inversion F.
    intro F; inversion F.
    elim (eq_list_name_dec  (cons_ret c :: l2) l3); intros case_c F; [clear F | inversion F].
    subst l3.
    unfold stack_typing.
    intro Htype.
    cut (frm_stack f = vargs ++ l); [intro Hstack | generalize case_split_stack; apply split_k_elements_ok].
    cut (l0 = l1 ++ l2); [intro Hl0 | generalize case_split; apply split_k_elements_ok].
    cut (length l1 = car); 
      [intro Hlength | generalize case_split; apply split_k_elements_length].
    cut (length vargs = length l1); 
      [intro Hlength2 | rewrite Hlength; generalize case_split_stack; apply split_k_elements_length].
    apply cons_list_typing.
  (* built tree's type is ok *)
    apply args_to_tree_typing; trivial.
    rewrite <- case_eq.
    cut (tree_list_typing vargs l1); [rewrite <- rev_lin_is_rev; apply rev_list_typing | generalize Htype].
    rewrite Hstack; rewrite Hl0.
    apply sub_list_typing_left; trivial.

  (* remaining part of the stack's typing ok *)
    generalize Htype.
    rewrite Hstack; rewrite Hl0.
    apply sub_list_typing_right; trivial.
  (* instruction *)
    symmetry; generalize case_instr; apply element_at_unsafe_to_safe.
    (* part 2  : virtual frames from M' are well-typed *)
    intros i fi fpi.
    subst.
    intros Hfi Hfpi.
    destruct i.
  (* i = 0 *)
    cut (element_at_list (f :: M0) 0 = Some f); [intro Hf | simpl; trivial].
    cut (element_at_list (f :: M0) 1 = Some fpi).
    intro Hfpi'; generalize (Hwtvirtual 0 f fpi Hf Hfpi').
    replace (frm_args f) with (frm_args fi).
    trivial.
    simpl in Hfi.
    inversion Hfi.
    simpl; trivial.
    simpl; simpl in Hfpi.
    rewrite Hfpi.
    trivial.
  (* i > 0 *)
    cut (element_at_list (f :: M0) (S i) = Some fi).
    cut (element_at_list (f :: M0) (S (S i)) = Some fpi).
    intros Hfpi' Hfi'.
    apply (Hwtvirtual (S i) fi fpi Hfi' Hfpi').
    simpl; simpl in Hfpi.
    assumption.
    simpl; simpl in Hfi; assumption.
  Qed.

  Lemma red_branch_then_keeps_welltyped : forall (M0 : configuration) (f : frame) (fcn : function)
    (cnm : name) (j : nat) (l : list value) (vf : list value) (Cj : j < fcn_size fcn), 
    Get_function (frm_fun f) = Some fcn ->
    (fcn_bytecode fcn)[frm_pc f|_] = Some (i_branch (fcn_size fcn) cnm j Cj) ->
    frm_stack f = Node cnm vf :: l -> wellformed_configuration (f :: M0) ->
    reduction (f :: M0) (mkframe (frm_fun f) (S (frm_pc f))
      (push_list vf l) (frm_args f) :: M0) ->
    welltyped_frame f -> (forall (i : nat) (fi fpi : frame),
      element_at_list (f :: M0) i = Some fi ->
      element_at_list (f :: M0) (S i) = Some fpi ->
      welltyped_frame (mkframe (frm_fun fpi) (frm_pc fpi)
        (frm_args fi ++ frm_stack fpi) (frm_args fpi))) ->
    welltyped_configuration
    (mkframe (frm_fun f) (S (frm_pc f)) (push_list vf l) (frm_args f) :: M0).
  Proof.
    intros M0 f fcn cnm j l vf Cj Hfcn case_instr Hstack Hwf Hred Hwttop Hwtvirtual.
    constructor.
  (* M' is well-formed : *)
    apply (reduction_keeps_wellformed (f::M0)); trivial.
    split.
  (* top frame of M' is well-typed : *)
    simpl.
    unfold welltyped_frame; intros f' Hf' fcn' Hfcn' C.
    (inversion Hf'; subst f'; clear Hf').
    simpl in Hfcn'.
    rewrite Hfcn' in Hfcn; inversion Hfcn; subst fcn'.
    simpl in C.
    cut (frm_pc f < fcn_size fcn); [intro C' | generalize C; auto with arith].
    cut (element_at_list (f :: M0) 0 = Some f); [intro Hf | trivial].
    generalize (Hwttop fcn Hfcn' C').
    generalize (Wti_Kildall fcn (get_some_in_functions  fcn (frm_fun f) functions Hfcn') (frm_pc f) C'). 
    unfold Wti.
    CaseEq ((Kildall_Types fcn (get_some_in_functions  fcn (frm_fun f) functions Hfcn')) [frm_pc f|C']).
  (* Kildall_Types fcn) [pc f] = Top_T *)
    intros dd F; inversion F.
  (* Kildall_Types fcn) [pc f] = Bot_T *)
    generalize (Passed_Kildall fcn (get_some_in_functions  fcn (frm_fun f) functions Hfcn')); 
      intros P1 case.
    unfold stack_typing; simpl; intros dd F; inversion F.
  (* Kildall_Types fcn) [pc f] = Types l0 *)
    intros l0 case.
    replace ((fcn_bytecode fcn)[frm_pc f|C']) with (i_branch (fcn_size fcn) cnm j Cj).
    intro h; elim h; clear h.
    elim (eq_Sigma_dec  (Types l0) 
      ((Kildall_Types fcn (get_some_in_functions fcn (frm_fun f) functions Hfcn'))[j|Cj])); intros case_ssj F; 
    [clear F | inversion F].
    CaseEq (Get_constr cnm); [intros c Hc | intros dd F; inversion F].
    destruct l0; [intro F; inversion F | idtac].
    elim (eq_name_dec (cons_ret c) n); [intro case_n |intros dd F; inversion F].
    CaseEq (element_at_unsafe (Kildall_Types fcn (get_some_in_functions  fcn (frm_fun f) functions Hfcn'))
      (S (frm_pc f))); [intros s case_ss_s | intros dd F; inversion F].
    cut ((Kildall_Types fcn (get_some_in_functions  fcn (frm_fun f) functions Hfcn'))[S (frm_pc f)|C] = s); 
    [intro Hss | generalize case_ss_s; apply element_at_unsafe_to_safe].
    simpl; rewrite Hss.
    destruct s.
    intro F; inversion F.
    intro F; inversion F.
    elim (eq_list_name_dec  (rev (cons_args c) ++ l0) l1); intros case' F; [clear F | inversion F].
    rewrite Hstack.
    intro Htype; assert (H : (tree_typing (Node cnm vf) n) /\ tree_list_typing l l0).
    (* Prooving H : *)
    inversion Htype.
    split; trivial.
    unfold tree_typing; constructor 2 with const; subst; trivial.
    constructor.
    (* H proved *)
    subst l1.
    elim H; clear H; intros Htype1 Htype2.
    rewrite push_list_is_app_rev.
    cut (tree_list_typing (rev vf) (rev (cons_args c))).
    intro dd; generalize dd Htype2.
    unfold stack_typing.
    apply app_list_typing.
    subst n.
    cut (tree_list_typing vf (cons_args c)); 
      [rewrite <- rev_lin_is_rev; rewrite <- rev_lin_is_rev; apply rev_list_typing 
        | generalize Htype1; apply tree_to_args_typing].
    assumption.
    symmetry; generalize case_instr; apply element_at_unsafe_to_safe.
    (* part 2 : virtual frames from M' are well-typed *)
    intros i fi fpi Hfi Hfpi.
    destruct i.
  (* i = 0 : *)
    cut (element_at_list (f :: M0) 0 = Some f); [intro Hf | simpl; trivial].
    cut (element_at_list (f :: M0) 1 = Some fpi).
    intro Hfpi'; generalize (Hwtvirtual 0 f fpi Hf Hfpi').
    replace (frm_args f) with (frm_args fi).
    trivial.
    simpl in Hfi.
    inversion Hfi.
    simpl; trivial.
    simpl; simpl in Hfpi.
    rewrite Hfpi.
    trivial.
  (* i > 0 *)
    cut (element_at_list (f :: M0) (S i) = Some fi).
    cut (element_at_list (f :: M0) (S (S i)) = Some fpi).
    intros Hfpi' Hfi'.
    apply (Hwtvirtual (S i) fi fpi Hfi' Hfpi').
    simpl; simpl in Hfpi.
    assumption.
    simpl; simpl in Hfi; assumption.
  Qed.


  Lemma red_branch_else_keeps_welltyped : forall (M0 : configuration) (f : frame) (fcn : function) 
    (cnm dnm : name) (j : nat) (l : list value) (vf : list value) (Cj : j < fcn_size fcn), 
    Get_function (frm_fun f) = Some fcn ->
    (fcn_bytecode fcn)[frm_pc f|_] = Some (i_branch (fcn_size fcn) cnm j Cj) ->
    frm_stack f = Node dnm vf :: l -> dnm <> cnm -> wellformed_configuration (f :: M0) ->
    reduction (f :: M0) (mkframe (frm_fun f) j (frm_stack f) (frm_args f) :: M0) ->
    welltyped_frame f -> (forall (i : nat) (fi fpi : frame),
      element_at_list (f :: M0) i = Some fi ->
      element_at_list (f :: M0) (S i) = Some fpi ->
      welltyped_frame (mkframe (frm_fun fpi) (frm_pc fpi)
        (frm_args fi ++ frm_stack fpi) (frm_args fpi))) ->
    welltyped_configuration (mkframe (frm_fun f) j (frm_stack f) (frm_args f) :: M0).
  Proof.    
    intros M0 f fcn cnm dnm j l vf Cj Hfcn case_instr Hstack neq_cnm_dnm Hwf Hred Hwttop Hwtvirtual.
    constructor.
  (* M' is well-formed : *)
    apply (reduction_keeps_wellformed (f::M0)); trivial.
    split.
  (* top frame of M' well-typed : *)
    unfold welltyped_frame; intros f' Hf' fcn' Hfcn' C.
    simpl.
    (simpl in Hf'; inversion Hf'; subst f'; clear Hf'; simpl in Hfcn').
    rewrite Hfcn' in Hfcn; inversion Hfcn; subst fcn'.
    simpl in C.
    cut (frm_pc f < fcn_size fcn); [intro C' | generalize case_instr; apply element_at_unsafe_some].
    cut (element_at_list (f :: M0) 0 = Some f); [intro Hf | trivial].
    generalize (Hwttop fcn Hfcn' C'); clear Hf.
    generalize (Wti_Kildall fcn (get_some_in_functions  fcn (frm_fun f) functions Hfcn') (frm_pc f) C'). 
    unfold Wti.
    CaseEq ((Kildall_Types fcn (get_some_in_functions fcn (frm_fun f) functions Hfcn'))[frm_pc f|C']).
  (* (Kildall_Types fcn)[pc f] = Top_T *)
    intros dd F; inversion F.
  (* (Kildall_Types fcn)[pc f] = Bot_T *)
    generalize (Passed_Kildall fcn (get_some_in_functions  fcn (frm_fun f) functions Hfcn')); 
      intros P1 case.
    unfold stack_typing; simpl; intros dd F; inversion F.
  (* (Kildall_Types fcn)[pc f] = Types l0 *)
    intros l0 case.
    replace ((fcn_bytecode fcn)[frm_pc f|C']) with (i_branch (fcn_size fcn) cnm j Cj).
    intro h; elim h; clear h.
    elim (eq_Sigma_dec  (Types l0) 
      ((Kildall_Types fcn (get_some_in_functions fcn (frm_fun f) functions Hfcn'))[j|Cj])); 
    intros case_ssj F; [clear F | inversion F].
    CaseEq (Get_constr cnm); [intros c Hc | intros dd F ; inversion F].
    destruct l0; [intro F; inversion F| idtac].
    elim (eq_name_dec (cons_ret c) n); intro case_n; [idtac | intro F; inversion F].
    CaseEq (element_at_unsafe (Kildall_Types fcn (get_some_in_functions  fcn (frm_fun f) functions Hfcn')) 
      (S (frm_pc f))); [intros s case_ss_s | intros dd F; inversion F].
    destruct s.
    intro F; inversion F.
    intro F; inversion F.
    elim (eq_list_name_dec  (rev (cons_args c) ++ l0) l1); intros case' F; [clear F | inversion F].
    simpl; rewrite (element_at_irrel Sigma (fcn_size fcn) 
      (Kildall_Types fcn (get_some_in_functions  fcn (frm_fun f) functions Hfcn')) j C Cj).
    rewrite <- case_ssj.
    trivial.
    symmetry; generalize case_instr; apply element_at_unsafe_to_safe.
    (* part 2 : virtual frames from M' are well-typed *)
    intros i fi fpi Hfi Hfpi.
    destruct i.
  (* i = 0 *)
    cut (element_at_list (f :: M0) 0 = Some f); [intro Hf | simpl; trivial].
    cut (element_at_list (f :: M0) 1 = Some fpi).
    intro Hfpi'; generalize (Hwtvirtual 0 f fpi Hf Hfpi').
    replace (frm_args f) with (frm_args fi).
    trivial.
    simpl in Hfi.
    inversion Hfi.
    simpl; trivial.
    simpl; simpl in Hfpi.
    rewrite Hfpi.
    trivial.
  (* i > 0 *)
    cut (element_at_list (f :: M0) (S i) = Some fi).
    cut (element_at_list (f :: M0) (S (S i)) = Some fpi).
    intros Hfpi' Hfi'.
    apply (Hwtvirtual (S i) fi fpi Hfi' Hfpi').
    simpl; simpl in Hfpi.
    assumption.
    simpl; simpl in Hfi; assumption.
  Qed.

  (* well-typedness is invariant  *)
  Lemma reduction_keeps_welltyped : Invariant welltyped_configuration.
  Proof.    
    intros M M' Hwt Hred.
    InversionRed Hred; inversion Hwt; subst; generalize H; elim H0; 
      clear H H0; intros Hwttop Hwtvirtual Hwf.
  (* return *)
    cut (Some f = Some f); [intro Hf | trivial].
    generalize (Hwttop f Hf); clear Hwttop; intro Hwttop.
    apply (red_return_keeps_welltyped M0 f g fcn v0 l Hfcn); trivial.
  (* stop *)
    constructor.
    apply wellformed_epsilon.
    split.
    intros f0 Hf0; inversion Hf0.
    intros i fi fpi Hfi; inversion Hfi.
  (* load *)
    cut (Some f = Some f); [intro Hf | trivial].
    generalize (Hwttop f Hf); clear Hwttop; intro Hwttop.
    apply (red_load_keeps_welltyped M0 f fcn j vj Hfcn); trivial.
  (* call *)
    cut (Some f = Some f); [intro Hf | trivial].
    generalize (Hwttop f Hf); clear Hwttop; intro Hwttop.
    apply (red_call_keeps_welltyped M0 f fcn gcn gnm gar vargs l Hfcn); trivial.
  (* build *)
    cut (Some f = Some f); [intro Hf | trivial].
    generalize (Hwttop f Hf); clear Hwttop; intro Hwttop.
    rewrite <- rev_lin_is_rev.
    apply (red_build_keeps_welltyped M0 f fcn c cnm car vargs l Hfcn); trivial.
    rewrite rev_lin_is_rev; trivial.
  (* BranchThen *)
    cut (Some f = Some f); [intro Hf | trivial].
    generalize (Hwttop f Hf); clear Hwttop; intro Hwttop.
    apply (red_branch_then_keeps_welltyped M0 f fcn cnm j l vf Cj Hfcn); trivial.
  (* BranchElse *)
    cut (Some f = Some f); [intro Hf | trivial].
    generalize (Hwttop f Hf); clear Hwttop; intro Hwttop.
    apply (red_branch_else_keeps_welltyped M0 f fcn cnm dnm j l vf Cj Hfcn); trivial.
  Qed.

  (* init configuration is well-typed provided arguments given to fexec are of correct types *)
  Lemma welltyped_init_configuration : forall (fexec : name) (argsexec : list value) (fcnexec : function), 
    Get_function fexec = Some fcnexec -> 
    tree_list_typing argsexec (rev_lin (fcn_args fcnexec)) ->
    welltyped_configuration (Init_configuration fexec argsexec).
  Proof.
    intros fexec argsexec fcnexec Hget Htyping; constructor.
    apply wellformed_init_configuration.
    rewrite Hget; intro F; inversion F.
    split; simpl.
    intros f Hf; inversion Hf; subst f; clear Hf.
    unfold welltyped_frame; simpl; intros fcn Hfcn C.
    cut (fcn=fcnexec); [intro; subst fcnexec; clear Hget| rewrite Hget in Hfcn; inversion Hfcn; trivial].
    rewrite (element_at_irrel Sigma (fcn_size fcn) 
      (Kildall_Types fcn (get_some_in_functions  fcn fexec functions Hfcn)) 
      0 C (nonvoidfcn fcn (get_some_in_functions  fcn fexec functions Hfcn))).
    generalize (Passed_Kildall fcn (get_some_in_functions  fcn fexec functions Hfcn)); intros notop.

    CaseEq ((Kildall_Types fcn (get_some_in_functions fcn fexec functions Hfcn)) 
      [0|nonvoidfcn fcn (get_some_in_functions fcn fexec functions Hfcn)]).
    intro case; apply notop; rewrite <- case; apply element_at_belong.
    rewrite (Kildall_Types_0 fcn (get_some_in_functions  fcn fexec functions Hfcn)).
    unfold ss_init.
    rewrite element_at_in_replaced.
    intro case; inversion case.
    intro l.
    rewrite (Kildall_Types_0 fcn (get_some_in_functions  fcn fexec functions Hfcn)).
    unfold ss_init.
    rewrite element_at_in_replaced.
    intro case; inversion case.
    rewrite <- rev_lin_is_rev; assumption.
    intros i fi fpi Hfi Hfpi; destruct i; simpl; inversion Hfpi.
  Qed.


  (* each configuration in a correct execution is well-typed *)
  Lemma welltyped_execution : forall (fexec : name) (argsexec : list value) (fcnexec : function) 
    (Hin : In fcnexec functions) (L : list configuration), 
    Get_function fexec = Some fcnexec -> 
    tree_list_typing argsexec (rev_lin (fcn_args fcnexec)) ->
    execution fexec argsexec L -> 
    forall  (M : configuration), In M L -> welltyped_configuration M.
  Proof.    
    intros fexec argsexec fcnexec Hin L Hget Htyping; apply reduction_to_execution.
    apply welltyped_init_configuration with fcnexec; trivial.
    apply reduction_keeps_welltyped.
  Qed.


  (* progress : any well-typed configuration is either a result, reducts, or empty. *)
  Lemma reduction_progress : forall (M : configuration) (Hwt : welltyped_configuration M), 
    sumor (sum {v : value | config_result M v} {M' : configuration | reduction M M'}) (M = nil).
  Proof.
    intros M Hwt.
    destruct M; simpl; [right; trivial | left].
    cut (wellformed_configuration (f::M)); [intro Hwf | inversion Hwt; auto].

    cut (welltyped_frame f /\ (forall (i : nat) (fi fpi : frame), 
      element_at_list (f::M) i = Some fi -> 
      element_at_list (f::M) (S i) = Some fpi ->
      welltyped_frame (mkframe ((frm_fun fpi)) ((frm_pc fpi)) 
        ((frm_args fi)++(frm_stack fpi)) (frm_args fpi)))); 
    [intro Hwtalt | inversion Hwt; split; auto].
    elim Hwtalt; clear Hwtalt; intros Hwtf Hwtvirtual.
    clear Hwt.
    unfold welltyped_frame in Hwtf.
    unfold wellformed_configuration in Hwf.
    destruct f as [fnm pc stack args]; (simpl in *).
    CaseEq (Get_function fnm).
    intros fcn case.
    
    cut (Some (Frm fnm pc stack args) = Some (Frm fnm pc stack args)); [intro Hf | trivial].
    generalize (Hwf 0 (Frm fnm pc stack args) (Frm fnm pc stack args) fcn fcn Hf); clear Hwf Hf; intro Hwf.
    elim Hwf; clear Hwf; intros dd Hwf.
    elim (Hwf case); simpl; intros Cpc H; clear Hwf.
    
    generalize (Hwtf fcn case Cpc); clear Hwtf.
    generalize (Wti_Kildall fcn (get_some_in_functions  fcn fnm functions case) pc Cpc).
    generalize (Passed_Kildall fcn (get_some_in_functions  fcn fnm functions case)); intro notop.
    unfold Wti.
    CaseEq ((Kildall_Types fcn (get_some_in_functions fcn fnm functions case))[pc|Cpc]); simpl.
    intros casess F; inversion F.
    intros casess ddd F; inversion F.
    intros l case_ss.
    CaseEq ((fcn_bytecode fcn)[pc|Cpc]).
  (* return *)
    intro case_i; destruct l.
    intro F; inversion F.
    elim (eq_name_dec n (fcn_ret fcn)); intros case_n ddd; [clear ddd | inversion ddd].
    destruct stack; simpl.
    intro F; cut (False); [intro F'; inversion F' | inversion F].
    destruct M.
  (* Real Result *)
    intro; left.
    exists v.
    apply (config_is_result (Frm fnm pc (v :: stack) args :: nil) v stack (Frm fnm pc (v :: stack) args) fcn); auto.
    simpl.
    apply element_at_to_unsafe with Cpc; auto.
  (* Return *)
    intro Htype; right.
    exists ((Frm (frm_fun f) (S (frm_pc f)) (v::(frm_stack f)) (frm_args f))::M).
    apply (red_return  M (Frm fnm pc (v::stack) args) f fcn v stack); simpl; auto.
    apply element_at_to_unsafe with Cpc; trivial.
  (* stop *)
    intros case_bc ddd Htype; right.
    clear ddd.
    exists (nil (A:=frame)).
    apply red_stop with fcn; auto.
    simpl; apply element_at_to_unsafe with Cpc; auto.
    
  (* load *)
    intros j case_bc.
    CaseEq (element_at_unsafe (Kildall_Types fcn (get_some_in_functions  fcn fnm functions case)) (S pc)).
    intros s case_s; destruct s; simpl.
    intro h; inversion h.
    intro h; inversion h.
    CaseEq (element_at_list (rev l) j).
    intros vj case_vj.
    elim (eq_list_name_dec  (vj :: l) l0); intros case_eq ddd; [clear ddd | inversion ddd].
    intro Htype; right.
    CaseEq (element_at_list (rev stack) j).
    intros v case_v.
    exists ((Frm (frm_fun (Frm fnm pc stack args)) (S (frm_pc (Frm fnm pc stack args))) (v::(frm_stack (Frm fnm pc stack args))) (frm_args (Frm fnm pc stack args))) :: M).
    apply (red_load M (Frm fnm pc stack args) fcn j v); simpl; auto.
    apply element_at_to_unsafe with Cpc.
    assumption.
    rewrite rev_lin_is_rev; assumption.
    intro F.
    cut (tree_list_typing (rev stack) (rev l)); [intro Hrev | generalize Htype; rewrite <- rev_lin_is_rev; rewrite <- rev_lin_is_rev; apply rev_list_typing].
    cut (length (rev stack) = length (rev l)); [intro Hlength | generalize Hrev; apply list_typing_length]. 
    cut (j < length (rev l)).
    intro Hn; rewrite <- Hlength in Hn. 
    cut (~ j < length (rev stack)).
    intro Hn2.
    elim Hn2; assumption.
    cut (j >= length (rev stack)); auto with arith.
    apply element_at_list_none; assumption.
    apply element_at_list_some with vj; assumption.
    
    intros ddd F; inversion F.
    intros ddd F; inversion F.
    
  (* call *)
    intros gnm ar case_bc.
    CaseEq (split_k_elements ar l).
    intros p Hsplit; destruct p as [lar l'].
    CaseEq (Get_function gnm).
    intros gcn Hget.
    elim (eq_list_name_dec (rev lar) (fcn_args gcn)); intro case_eq.
    CaseEq (element_at_unsafe (Kildall_Types fcn (get_some_in_functions  fcn fnm functions case)) (S pc)).
    intros s case_s; destruct s.
    intro F; inversion F.
    intro F; inversion F.
    elim (eq_list_name_dec  ((fcn_ret gcn) :: l') l0); intros case_l0 ddd ; [clear ddd | inversion ddd].
    intro Htype.
    subst; (simpl in *).
    right.
    CaseEq (split_k_elements ar stack).
    intros p Hsplitstack; destruct p as [args' stack'].
    exists ((Frm gnm 0 args' args')::(Frm fnm pc stack' args)::M).
    apply (red_call M (Frm fnm pc stack args) fcn gcn gnm ar); simpl; auto.
    apply element_at_to_unsafe with Cpc; assumption.
    intro F; cut (length stack = length l); [intro Hlength | generalize Htype; apply list_typing_length].
    cut (length stack < ar); [intro Hlstack | generalize F; apply split_k_elements_none].
    cut (~length stack < ar); [intro Hlstack2; elim Hlstack2; assumption |idtac].
    cut (ar <= length stack); [auto with arith | generalize Hsplit; rewrite Hlength; apply split_k_elements_some].
    intros ddd F; inversion F.
    intro F; inversion F.
    intros ddd F; inversion F.
    intros ddd F; inversion F.
    
  (* build *)
    intros cnm ar case_bc.
    CaseEq (split_k_elements ar l).
    intros p Hsplit; destruct p as [lk lr].
    CaseEq (Get_constr cnm).
    intros c case_c.
    elim (eq_list_name_dec  (rev lk) (cons_args c)); intro case_eq.
    CaseEq (element_at_unsafe (Kildall_Types fcn (get_some_in_functions  fcn fnm functions case)) (S pc)).
    intros s case_ss_spc; destruct s. 
    intro F; inversion F.
    intro F; inversion F.
    elim (eq_list_name_dec  (cons_ret c :: lr) l0); intros case_eq2 F Htype.
    clear F.
    right.
    CaseEq (split_k_elements ar stack). 
    intros p case_split; destruct p as [argsc stack'].
    exists ((Frm (frm_fun (Frm fnm pc stack args)) (S (frm_pc (Frm fnm pc stack args))) 
      ((Node cnm (rev argsc)) :: stack') (frm_args (Frm fnm pc stack args)))::M).
    apply (red_build M (Frm fnm pc stack args) fcn c cnm ar argsc stack'); simpl; trivial.
    apply element_at_to_unsafe with Cpc; trivial.
    intro F.
    cut (length stack = length l); [intro Hlength | generalize Htype; apply list_typing_length].
    cut (length stack < ar); [intro Hlstack | generalize F; apply split_k_elements_none].
    cut (~length stack < ar); [intro Hlstack2; elim Hlstack2; assumption |idtac].
    cut (ar <= length stack); [auto with arith | generalize Hsplit; rewrite Hlength; apply split_k_elements_some].
    inversion F.
    intros ddd F; inversion F.
    intro F; inversion F.
    intros ddd F; inversion F.
    intros ddd F; inversion F.
  (* branch *)
    intros cnm j Cj case_bc.
    destruct (eq_Sigma_dec  (Types l) ((Kildall_Types fcn (get_some_in_functions fcn fnm functions case))[j|Cj])).
    intro h; elim h; intro h'; clear h' h.
    CaseEq (Get_constr cnm).
    intros c case_c.
    destruct l.
    intro F; inversion F.
    elim (eq_name_dec (cons_ret c) n); intro case_n.
    CaseEq (element_at_unsafe (Kildall_Types fcn (get_some_in_functions  fcn fnm functions case)) (S pc)).
    intros s case_ss_spc; destruct s. 
    intro F; inversion F.
    intro F; inversion F.
    elim (eq_list_name_dec  (rev (cons_args c) ++ l) l0); intros case_eq F Htype; [clear F | inversion F]. 
    right.
    destruct stack.
    assert (H0 : False).
    inversion Htype.
    inversion H0.
    destruct v.
    (* case v leaf : *)
    assert (H0 : False).
    inversion Htype.
    inversion H0.
    (* case v node : *)
    
    elim (eq_name_dec n0 cnm); intro case_eq2.
    subst n0.
    exists ((Frm (frm_fun (Frm fnm pc (Node cnm l1 :: stack) args)) (S (frm_pc (Frm fnm pc (Node cnm l1 :: stack) args))) 
      ((rev l1) ++ stack) (frm_args (Frm fnm pc ((Node cnm l1) :: stack) args)))::M).
    rewrite <- push_list_is_app_rev.
    apply (red_branch_then M (Frm fnm pc (Node cnm l1 :: stack) args) fcn cnm j stack l1 Cj); simpl; trivial.
    apply element_at_to_unsafe with Cpc; trivial.
    exists ((Frm (frm_fun (Frm fnm pc (Node n0 l1 :: stack) args)) j (frm_stack (Frm fnm pc (Node n0 l1 :: stack) args)) 
      (frm_args (Frm fnm pc (Node n0 l1 :: stack) args))) :: M). 
    apply (red_branch_else M (Frm fnm pc (Node n0 l1 :: stack) args) fcn cnm n0 j stack l1 Cj); simpl; trivial.
    apply element_at_to_unsafe with Cpc; trivial.
    intros ddd F; inversion F.
    intro F; inversion F.
    intros ddd F; inversion F.
    intro F; elim F; clear F; intro F; inversion F.
    cut (Some (mkframe fnm pc stack args) = Some (mkframe fnm pc stack args)); [intro Hf | trivial].
    cut (function); [intro fcn | apply (mkfunction fnm nil fnm 0 vector_nil)].
    elim (Hwf 0 (mkframe fnm pc stack args) (mkframe fnm pc stack args) fcn fcn Hf). 
    simpl; intros H ddd F.
    elim H; assumption.
    subst.
    elim H0; intros H1 H2.
    apply H1; trivial.
    subst; elim H0; intros H1 H2; apply H2; trivial.
  Qed.

  Lemma nonempty_progress : forall (f : frame) (M : configuration) (MWellTyped : welltyped_configuration (f::M)), 
    {v : value | config_result (f::M) v} + {M' : configuration | reduction (f::M) M'}.
  Proof.
    intros f M  fMWellTyped.
    elim (reduction_progress (f::M) fMWellTyped).
    trivial.
    intro H; inversion H.
  Qed.

  Lemma nonempty_progress' : forall (M : configuration) (MWellTyped : welltyped_configuration M), 
    M <> nil -> {v : value | config_result M v} + {M' : configuration | reduction M M'}.
  Proof.
    intros  M  MWellTyped MNotEmpty.
    elim (reduction_progress M MWellTyped).
    trivial.
    intro H; elim MNotEmpty; trivial.
  Qed.

  Fact eq_configuration_nil_dec : forall (M : configuration), {M = nil} + {M <> nil}.
  Proof.
    intro M; destruct M; [left | right]; trivial.
    intro H; inversion H.
  Qed.
    

  Inductive config_wrap : Set :=
    | config_wrap_error : config_wrap
    | config_wrap_result : value -> config_wrap
    | config_wrap_wt_list : forall (M : configuration) (WTM : welltyped_configuration M), config_wrap.

  Definition fonctionnal_reduction (WM : config_wrap) : config_wrap := 
    match WM with 
      | config_wrap_wt_list M WTM => 
        match eq_configuration_nil_dec M with 
          | left _ => config_wrap_error
          | right MNotEmpty => 
            match nonempty_progress' M WTM MNotEmpty with 
              | inl H => 
                match H with 
                  | exist v Hred => config_wrap_result v
                end
              | inr H => 
                match H with 
                  | exist Mred Hred => 
                    config_wrap_wt_list Mred 
                    (reduction_keeps_welltyped M Mred WTM Hred)
                end
            end
        end
      | x => x
    end.

  (* length of frame args is the arity of the function evaluated in the frame for each frame in the configuration *)
  Definition frames_args_length (M : configuration) : Prop := forall (f : frame) (fcn : function), 
    In f M -> Get_function (frm_fun f) = Some fcn -> length (frm_args f) = length (fcn_args fcn).
  
  (* frame_args_length is invariant on well-typed configurations*)
  Lemma reduction_length : Invariant (fun (M : configuration) => welltyped_configuration M /\ frames_args_length M).
  Proof.    
    intros M M' Hwtfal Hred.
    elim Hwtfal; clear Hwtfal; intros Hwt Hfal.
    split.
    apply (reduction_keeps_welltyped M M'); trivial.
    (InversionRed Hred; intros f' fcn' Hin' Hget').
    Focus 1.
  (* return *)
    (elim Hin'; clear Hin'; intro Hin').
    subst.
    (simpl in *).
    apply (Hfal g fcn'); trivial.
    right; left; trivial.
    apply (Hfal f' fcn'); trivial.
    right; right; trivial.
    Focus 1.
  (* stop *)
    subst.
    (inversion Hin').
    Focus 1.
  (* load *)
    (elim Hin'; clear Hin'; intro Hin').
    (subst; simpl in *).
    apply (Hfal f fcn'); trivial.
    left; trivial.
    apply (Hfal f' fcn'); trivial.
    right; trivial.
    Focus 1.
  (* call *)
    (elim Hin'; clear Hin'; intro Hin').
    (subst; simpl in *).
    cut (frm_pc f < fcn_size fcn); [intro C | generalize case_instr; apply element_at_unsafe_some].
    generalize (Wti_Kildall fcn (get_some_in_functions  fcn (frm_fun f) functions Hfcn) (frm_pc f) C).
    inversion Hwt; subst.
    generalize H; elim H0; clear H H0; intros Hwttop Hwtvirtual Hwf.
    cut (element_at_list (f::M0) 0 = Some f); [intro Hf | trivial].
    generalize (Hwttop f Hf fcn Hfcn C); trivial.
    unfold Wti.
    CaseEq ((Kildall_Types fcn (get_some_in_functions  fcn (frm_fun f) functions Hfcn))[frm_pc f|C]).
    intros case Hs F; inversion F.
    intros case Hs; inversion Hs.
    intros l0 case Hs.
    replace ((fcn_bytecode fcn)[frm_pc f|C]) with (i_call (fcn_size fcn) gnm gar).
    CaseEq (split_k_elements gar l0).
    intros p Hsplit; destruct p.
    destruct (Get_function gnm).
    elim (eq_list_name_dec  (rev l1) (fcn_args f0)); intro caseeq.
    intro dd; clear dd.
    inversion Hget'; subst.
    rewrite <- caseeq.
    rewrite rev_length.
    replace (length l1) with gar.
    generalize case_split_stack; apply split_k_elements_length.
    symmetry; generalize Hsplit; apply split_k_elements_length.
    intro F; inversion F.
    intro F; inversion F.
    intros dd F; inversion F.
    symmetry; generalize case_instr; apply element_at_unsafe_to_safe.
    (elim Hin'; clear Hin'; intro Hin').
    (subst; simpl in *).
    apply (Hfal f fcn'); trivial.
    left; trivial.
    apply (Hfal f' fcn'); trivial.
    right; assumption.
    Focus 1.
  (* build *)
    (elim Hin'; clear Hin'; intro Hin').
    (subst; simpl in *).
    apply (Hfal f fcn'); trivial.
    left; trivial.
    apply (Hfal f' fcn'); trivial.
    right; trivial.
  (* branch then *)
    (elim Hin'; clear Hin'; intro Hin').
    (subst; simpl in *).
    apply (Hfal f fcn'); trivial.
    left; trivial.
    apply (Hfal f' fcn'); trivial.
    right; trivial.
  (* branch else *)
    (elim Hin'; clear Hin'; intro Hin').
    (subst; simpl in *).
    apply (Hfal f fcn'); trivial.
    left; trivial.
    apply (Hfal f' fcn'); trivial.
    right; trivial.
  Qed.


  Lemma execution_length : forall (fexec : name) (argsexec : list value) (fcnexec : function) (L : list configuration), 
    Get_function fexec = Some fcnexec -> 
    tree_list_typing argsexec (rev_lin (fcn_args fcnexec)) ->
    execution fexec argsexec L -> 
    forall  (M : configuration), In M L -> frames_args_length M.
  Proof.    
    intros fexec argsexec fcnexec L Hget Htyping Hexec M Hin. 
    cut (welltyped_configuration M /\ frames_args_length M); [intro H; elim H; trivial | generalize Hexec M Hin; clear Hexec Hin M].
    apply (reduction_to_execution (fun (M : configuration) => welltyped_configuration M /\ frames_args_length M)); trivial.
    split.
    apply welltyped_init_configuration with fcnexec; trivial.
    intros f fcn Hin Hfcn.
    elim Hin; clear Hin; intro Hin.
    subst f; (simpl in *).
    rewrite Hget in Hfcn; inversion Hfcn; subst fcn.
    rewrite <- (rev_length _ (fcn_args fcnexec)).
    generalize Htyping; rewrite <- rev_lin_is_rev; apply list_typing_length.
    inversion Hin.
    apply reduction_length.
  Qed.


End machine_types.


