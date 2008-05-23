  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : machine.v					         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : definitions of the reduction relation of        *)
  (*	       configurations, result, error, wellformed         *)
  (*	       confgurations, proof it is an invariant	         *)
  (***************************************************************)

Section machine.


  Require Export instructions.

  Parameter constructors : list constr. (* all constructors declared in the program *)
  Parameter functions : list function. (* all functions declared in the program *)

  Notation configuration := (list frame).
  Notation Get_function := (get_function_by_name functions).
  Notation Get_constr := (get_constr_by_name constructors).

  (* last instruction in a function's bytecode should be return or stop *)
  Axiom lrs_functions : forall (fcn : function), 
    In fcn functions -> last_return_or_stop (fcn_size fcn) (fcn_bytecode fcn).

  (* no function is empty *) 
  Axiom nonvoidfcn : forall (fcn : function), 
    In fcn functions -> 0 < (fcn_size fcn).

  (* reduction relation on configurations *)
  Inductive reduction : relation configuration := 
    | red_return : 
      forall (M : configuration) (f g : frame) (fcn : function) (v0 : value) (l : list value), 
        Get_function (frm_fun f) = Some fcn -> 
        (fcn_bytecode fcn)[frm_pc f|_] = Some (i_return (fcn_size fcn)) ->
        frm_stack f = v0 :: l ->
        reduction (f::g::M) ((mkframe (frm_fun g) (S (frm_pc g)) (v0::(frm_stack g)) (frm_args g))::M)
          (* M (gcn, pcg, lg) (fcn, pc, l::v0) -> M (gcn, pcg+1, lg::v0) *)
    | red_stop : 
      forall (M : configuration) (f : frame) (fcn : function), 
        Get_function (frm_fun f) = Some fcn -> 
        (fcn_bytecode fcn)[frm_pc f|_] = Some (i_stop (fcn_size fcn)) ->
        reduction (f::M) nil
      (* M.(fcn, pc, l) -> empty *)
    | red_load : (* M.(fcn, pc, l) -> M.(fcn, pc+1, l.l[j]) *)
      forall (M : configuration) (f : frame) (fcn : function) (j : nat) (vj : value),
        Get_function (f.(frm_fun)) = Some fcn -> 
        (fcn_bytecode fcn)[frm_pc f|_] =  Some (i_load (fcn_size fcn) j) ->
        (rev_lin (frm_stack f))[j] = Some vj ->			           (* l[j] exists *)
        reduction (f::M) ((mkframe (frm_fun f) (S (frm_pc f)) (vj :: (frm_stack f)) (frm_args f))::M)
    | red_call : 
      forall (M : configuration) (f : frame) (fcn gcn : function) (gnm : name) (gar : nat)
        (vargs l : list value), 
        Get_function (frm_fun f) = Some fcn ->  
        (fcn_bytecode fcn)[frm_pc f|_] = Some (i_call (fcn_size fcn) gnm gar) ->
        Get_function gnm = Some gcn -> 
        split_k_elements gar (frm_stack f) = Some (vargs, l) ->                           (* v1...vn.l *)
        reduction (f::M) 
            ((mkframe gnm 0 vargs vargs)::(mkframe (frm_fun f) (frm_pc f) l (frm_args f))::M) 
       (* M.(fcn, pc, v1...vn.l) -> M.(fcn, pc, l).(gcn, 0, v1...vn) *)
    | red_build : 
      forall (M : configuration) (f : frame) (fcn : function) (c : constr) 
        (cnm : name) (car : nat) (vargs l : list value),
        Get_function (frm_fun f) = Some fcn -> 
        (fcn_bytecode fcn)[frm_pc f|_] = Some (i_build (fcn_size fcn) cnm car) ->
        Get_constr cnm = Some c -> 
        split_k_elements car (frm_stack f) = Some (vargs, l) ->				(* v1...vn.l *)
        reduction (f::M) 
            ((mkframe (frm_fun f) (S (frm_pc f)) ((Node cnm (rev vargs)) :: l) 
                      ((frm_args f)))::M)
        (* M.(fcn, pc, v1...vn.l) -> M.(fcn, pc, c(v1...vn).l) *)
    | red_branch_then : 
      forall (M : configuration) (f : frame) (fcn : function) (cnm : name) (j : nat)
        (l : list value) (vf : list value) (Cj : j < (fcn_size fcn)),
        Get_function (frm_fun f) = Some fcn -> 
        (fcn_bytecode fcn)[frm_pc f|_] = Some (i_branch (fcn_size fcn) cnm j Cj) ->
        (frm_stack f) = (Node cnm vf) :: l ->				                 (* c(v1...vn).l *)
        reduction (f::M) 
            ((mkframe (frm_fun f) (S (frm_pc f)) (push_list vf l) (frm_args f))::M)
        (* M.(fcn, pc, c(v1...vn).l) -> M.(fcn, pc+1, v1...vn.l) *)
    | red_branch_else : (* M.(fcn, pc, d(v1...vn).l) -> M.(fcn, j, d(v1...vn).l) *)
      forall (M : configuration) (f : frame) (fcn : function) (cnm : name) (dnm : name) (j : nat)
        (l : list value) (vf : list value) (Cj : j < (fcn_size fcn)),
        Get_function (frm_fun f) = Some fcn -> 
        (fcn_bytecode fcn)[frm_pc f|_] = Some (i_branch (fcn_size fcn) cnm j Cj) ->
        (frm_stack f) = (Node dnm vf) :: l ->						(* d(v1...vn).l *)
        dnm <> cnm ->										(* d <> c *)
        reduction (f::M) ((mkframe (frm_fun f) j (frm_stack f) (frm_args f))::M).
        

                        Ltac InversionRed H := inversion H as [M0 f g fcn v0 l Hfcn case_instr Hstack 
                          | M0 f fcn Hfcn case_instr 
            | M0 f fcn j vj Hfcn case_instr Hvj 
            | M0 f fcn gcn gnm gar vargs l Hfcn 
              case_instr Hgcn case_split_stack 
            | M0 f fcn c cnm car vargs l Hfcn 
	      case_instr Hc case_split_stack 
            | M0 f fcn cnm j l vf Cj Hfcn case_instr Hstack 
            | M0 f fcn cnm dnm j l vf Cj Hfcn case_instr Hstack neq_cnm_dnm];
          subst.
          
          Ltac InversionRed' H := inversion H as [M0' f' g' fcn' v0' l' Hfcn' case_instr' Hstack' 
            | M0' f' fcn' Hfcn' case_instr' 
            | M0' f' fcn' j' vj' Hfcn' case_instr' Hvj' 
            | M0' f' fcn' gcn' gnm' gar' vargs' l' Hfcn' 
              case_instr' Hgcn' case_split_stack' 
            | M0' f' fcn' c' cnm' car' vargs' l' Hfcn' 
              case_instr' Hc' case_split_stack' 
            | M0' f' fcn' cnm' j' l' vf' Cj' Hfcn' 
              case_instr' Hstack' 
            | M0' f' fcn' cnm' dnm' j' l' vf' Cj' Hfcn' 
              case_instr' Hstack' neq_cnm_dnm']; 
          subst.
          
          
          Lemma reduction_determinism : forall (M M' M'' : configuration), 
            reduction M M' -> reduction M M'' -> M' = M''.
          Proof.
            intros M M' M'' Hred' Hred''.
  InversionRed Hred'; InversionRed' Hred''; rewrite Hfcn in Hfcn'; inversion Hfcn'; 
    subst; rewrite case_instr in case_instr'; inversion case_instr'; subst; trivial.
  rewrite Hstack' in Hstack; inversion Hstack; trivial.
  rewrite Hvj' in Hvj; inversion Hvj; trivial.
  rewrite case_split_stack' in case_split_stack; inversion case_split_stack; trivial.
  rewrite case_split_stack' in case_split_stack; inversion case_split_stack; trivial.
  rewrite Hstack' in Hstack; inversion Hstack; subst; trivial.
  rewrite Hstack' in Hstack; inversion Hstack; elim neq_cnm_dnm'; trivial.
  rewrite Hstack' in Hstack; inversion Hstack.
  elim neq_cnm_dnm; subst; trivial.
Qed.

(* Invariant P : P is preserved through reduction *)
Definition Invariant (P : configuration -> Prop) : Prop := 
  forall (M M' : configuration), P M -> reduction M M' -> P M'. 

  (* initial configuration *)
Definition Init_configuration (fexec : name) (argsexec : list value) : configuration := 
  (mkframe fexec 0 argsexec argsexec) :: nil.

(* execution fcn args (M0 --- Mn)  iff  M0... Mn are configurations 
   obtained by evaluating function fcn on arguments args *) 
Inductive execution : name -> list value -> list configuration -> Prop :=
  | execution_init : forall (fexec : name) (argsexec : list value),  
    execution fexec argsexec ((Init_configuration fexec argsexec)::nil)
  | execution_step : forall (fexec : name) (argsexec : list value) 
    (L : list configuration) (M M' : configuration), 
    execution fexec argsexec (M::L) -> reduction M M' -> execution fexec argsexec (M'::M::L).


(* config_result M v iff configuration M is a result whise value is v *)
Inductive config_result (M : configuration) (v : value) : Prop :=
  | config_is_result : forall (l : list value) (f : frame) (fcn : function) (pc : nat), 
    Get_function (frm_fun f)  = Some fcn -> 
    (frm_pc f) < (fcn_size fcn) -> 
    (fcn_bytecode fcn)[frm_pc f|_] = Some (i_return (fcn_size fcn)) ->
    (frm_stack f) = v::l ->
    M = f::nil -> 
    config_result M v.


(* config_error M iff configuration M stands for an error : either the empty configuration, 
   or a configuration that is not a result and cannot be reduced *)
Inductive config_error : configuration->Prop :=
  | config_stopped : config_error nil
  | config_runtime : forall (M M' : configuration), 
    ~ (reduction M M') -> (forall (v : value), ~ (config_result M v)) -> config_error M.

(* An invariant property valid on an initial configuration is valid 
   on every configuration of the corresponding execution *)
Lemma reduction_to_execution : forall (P : configuration->Prop) (fexec : name) (argsexec : list value), 
  P (Init_configuration fexec argsexec) -> 
  Invariant P ->
  forall (L : list configuration), 
    execution fexec argsexec L -> forall (M : configuration), In M L ->  P M.
Proof.
  intros P fexec argsexec Pinit Hinvariant L Hexec.
  induction Hexec; intros M0 Hin.
  elim Hin; clear Hin; intro Hin.
  subst; trivial.
  inversion Hin.
  elim Hin; clear Hin; intro Hin.
  subst.
  apply (Hinvariant M M0); trivial.
  apply (IHHexec Pinit M); trivial.
  left; trivial.
  apply IHHexec; trivial.
Qed.

(* well-formed configuration M  : 
- each frame (f,pc,l,args) in M is s.t. pc < |f|
- each pair of consecutive frames (f,pc,l,args) (g,pc',l',args') in M is s.t. g[pc'] = call |g| f |args|
*)
Definition wellformed_configuration (M : configuration) : Prop :=
  forall (i : nat) (fi fpi : frame) (fcni fcnpi : function), 
    M[i] = Some fi ->
    (Get_function (frm_fun fi) <> None /\
      (Get_function (frm_fun fi) = Some fcni ->
        (frm_pc fi) < (fcn_size fcni)
        /\
        (M[S i] = Some fpi -> 
          Get_function (frm_fun fpi) = Some fcnpi -> 
          (fcn_bytecode fcnpi)[frm_pc fpi|_] = Some (i_call (fcn_size fcnpi) (frm_fun fi) (length (frm_args fi)))))).


Lemma wellformed_epsilon : wellformed_configuration nil.
Proof.
  intros i fi fpi fcni fcnpi H.
  inversion H.
Qed.


Lemma red_return_keeps_wellformed : forall (M0 : configuration) (f g : frame) 
  (fcn : function) (v0 : value) (l : list value), Get_function (frm_fun f) = Some fcn ->
  (fcn_bytecode fcn)[frm_pc f|_] = Some (i_return (fcn_size fcn)) ->
  frm_stack f = v0 :: l -> wellformed_configuration (f :: g :: M0)
  -> reduction (f :: g :: M0)
  (mkframe (frm_fun g) (S (frm_pc g)) (v0 :: frm_stack g) (frm_args g) :: M0) ->
   wellformed_configuration
   (mkframe (frm_fun g) (S (frm_pc g)) (v0 :: frm_stack g) (frm_args g) :: M0).
Proof.
  intros M0 f g fcn vO l Hfcn case_instr Hstack Hwf Hred.
  intros i fi fpi fcni fcnpi Hfi.
  destruct i.
  (* i = 0 *)
  inversion Hfi; subst fi.
  simpl.
  split.
  (* Get_function (frm_fun g) <> None function *)
  cut (Some g = Some g); [intro Hg | trivial].
  elim (Hwf 1 g f fcn fcni Hg); trivial.
  intro Hfcni; split.
  (* S pcg < |fcni| *)
  generalize (Hwf 0 f g fcn fcni); intro Hwf'; simpl in Hwf'.
  cut (In fcni functions); [intro Hfcnidec | idtac].
  cut (0 < fcn_size fcni); [intro C | apply (nonvoidfcn fcni Hfcnidec)].
  cut (Some g = Some g); [intro Hg | trivial].
  cut (Some f = Some f); [intro Hf | trivial].
  elim (Hwf' Hf); clear Hwf'; intros Hwf1 Hwf2.
  elim (Hwf2 Hfcn); clear Hwf2; intros Hwf2 Hwf3.
  generalize (Hwf3 Hg Hfcni); clear Hwf3; intro Hwf3.
  elim (eq_nat_dec (frm_pc g) (pred (fcn_size fcni))); intro eq.
  elim (lrs_functions fcni Hfcnidec C); intro case.
  rewrite eq in Hwf3; generalize (element_at_unsafe_to_safe _ _ (fcn_bytecode fcni) 
    (pred (fcn_size fcni)) (lt_pred_n_n (fcn_size fcni) C) 
    (i_call (fcn_size fcni) (frm_fun f) (length (frm_args f))) Hwf3); 
  (intro eq').
  rewrite case in eq'; (inversion eq').
  rewrite eq in Hwf3; generalize (element_at_unsafe_to_safe _ _ (fcn_bytecode fcni) 
    (pred (fcn_size fcni)) (lt_pred_n_n (fcn_size fcni) C) 
    (i_call (fcn_size fcni) (frm_fun f) (length (frm_args f))) Hwf3);
  (intro eq').
  rewrite case in eq'; (inversion eq').
  apply not_pred_lt_S_lt; try assumption.
  generalize Hwf3; apply element_at_unsafe_some.
  apply get_some_in_functions with (f:=frm_fun g); assumption.
  (* fcnpi[pc fpi] = call g |argsg|*) 
  destruct M0; simpl; intro F; inversion F.
  intro Hfcnpi; subst f0.
  cut (Some g = Some g); [intro Hg | trivial].
  elim (Hwf 1 g fpi fcni fcnpi Hg); simpl; intros Hwf1 Hwf2.
  elim (Hwf2 Hfcni); clear Hwf2; intros Hwf2 Hwf3.
  apply Hwf3; try assumption; trivial.
  (* S i *)
  cut ((f :: g :: M0)[S (S i)] = Some fi); [intro Hssi | simpl]. 
  elim (Hwf (S (S i)) fi fpi fcni fcnpi Hssi); clear Hwf; intros Hwf1 Hwf2.
  split; auto.
  simpl in Hfi; destruct (M0[i]); auto.
Qed.

Lemma red_load_keeps_wellformed : forall (M0 : configuration) (f : frame)
 (fcn : function) (j : nat) (vj : value),
 Get_function (frm_fun f) = Some fcn ->
(fcn_bytecode fcn)[frm_pc f|_] = Some (i_load (fcn_size fcn) j) -> 
 element_at_list (rev_lin (frm_stack f)) j = Some vj ->
 wellformed_configuration (f :: M0)->
 reduction (f :: M0)
 (mkframe (frm_fun f) (S (frm_pc f)) (vj :: frm_stack f) (frm_args f) :: M0) ->
 wellformed_configuration
 (mkframe (frm_fun f) (S (frm_pc f)) (vj :: frm_stack f) (frm_args f) :: M0).
Proof.
  intros M0 f fcn j vj Hfcn case_instr Hvj Hwf Hred i fi fpi fcni fcnpi Hfi.
  destruct i.
  (* i = 0 *)
  inversion Hfi; subst fi.
  simpl.
  cut (Some f = Some f); [intro Hf | trivial].
  elim (Hwf 0 f fpi fcn fcnpi Hf); intros Hwf1 Hwf2.
  split; trivial.
  intro Hfcni; elim (Hwf2 Hfcn); clear Hwf2; intros Hwf2 Hwf3.
  split.
  (* S pc f < |fcni| *)
  rewrite Hfcn in Hfcni; inversion Hfcni.
  subst fcni.
  cut (In fcn functions); [intro Hin | apply get_some_in_functions with (frm_fun f); trivial].
  cut (0 < fcn_size fcn); [intro Hnonvoid | apply nonvoidfcn; trivial].
  cut (frm_pc f < fcn_size fcn); 
    [apply not_pred_lt_S_lt | generalize case_instr; apply element_at_unsafe_some]; trivial.
  generalize (lrs_functions fcn Hin Hnonvoid); intros lrs pc_f_is_pred_size_f.
  destruct f as [fnm pcf stack args]; (simpl in *); subst pcf.
  elim lrs; intro case.
  cut (i_return (fcn_size fcn) = (i_load (fcn_size fcn) j)); [intro F; inversion F | rewrite <- case].
  generalize case_instr; apply element_at_unsafe_to_safe.
  cut (i_stop (fcn_size fcn) = (i_load (fcn_size fcn) j)); [intro F; inversion F | rewrite <- case].
  generalize case_instr; apply element_at_unsafe_to_safe.
  
  (* fcnpi[pc fpi] = call g |argsg|*) 
  intros; apply Hwf3; trivial.
  (* S i *)
  cut (element_at_list (f :: M0) (S i) = Some fi); [intro Hsi | simpl; simpl in Hfi; apply Hfi].
  elim (Hwf (S i) fi fpi fcni fcnpi Hsi); clear Hwf; intros Hwf1 Hwf2.
  split; auto.
Qed.

Lemma red_call_keeps_wellformed : forall (M0 : configuration) (f : frame)
 (fcn gcn : function) (gnm : name) (gar : nat) (vargs l : list value),
 Get_function (frm_fun f) = Some fcn ->
(fcn_bytecode fcn)[frm_pc f|_] = Some (i_call (fcn_size fcn) gnm gar) ->
 Get_function gnm = Some gcn ->
 split_k_elements gar (frm_stack f) = Some (vargs, l) ->
 wellformed_configuration (f :: M0) ->
 reduction (f :: M0)
 (mkframe gnm 0 vargs vargs :: mkframe (frm_fun f) (frm_pc f) l (frm_args f) :: M0) ->
 wellformed_configuration
 (mkframe gnm 0 vargs vargs :: mkframe (frm_fun f) (frm_pc f) l (frm_args f) :: M0).
Proof.
  intros M0 f fcn gcn gnm gar vargs l Hfcn case_instr Hgcn case_split_stack Hwf Hred i fi fpi fcni fcnpi Hfi.
  destruct i.
  (* i = 0 *)
  inversion Hfi; subst fi.
  split.
  simpl; rewrite Hgcn; intro F; inversion F.
  intro Hfcni; simpl in Hfcni; split.
  simpl; apply nonvoidfcn.
  apply get_some_in_functions with gnm; auto.
  rewrite Hgcn in Hfcni; inversion Hfcni; subst gcn.
  intro h; inversion h; subst fpi.
  clear h; simpl; intro h.
  rewrite Hfcn in h; inversion h; subst fcnpi.
  cut (length vargs = gar); 
    [intro h'; subst gar | generalize case_split_stack; apply split_k_elements_length].
  assumption.
  destruct i.
  (* i = 1 *)
  inversion Hfi; subst fi.
  simpl.
  cut (Some f = Some f); [intro Hf | trivial].
  elim (Hwf 0 f fpi fcn fcnpi Hf); intros Hwf1 Hwf2.
  elim (Hwf2 Hfcn); clear Hwf2; intros Hwf2 Hwf3.
  split; trivial.
  intro Hfcni; split.
  rewrite Hfcn in Hfcni; inversion Hfcni; subst fcni; trivial.
  simpl; simpl in Hwf3.
  destruct (M0[0]).
  assumption.
  intro h; inversion h.
  (* S i *)
  elim (Hwf (S i) fi fpi fcni fcnpi); auto.
Qed.

Lemma red_build_keeps_wellformed : forall (M0 : configuration) (f : frame) (fcn : function)
  (c : constr) (cnm : name) (car : nat) (vargs l : list value),
  Get_function (frm_fun f) = Some fcn ->
 (fcn_bytecode fcn)[frm_pc f|_] = Some (i_build (fcn_size fcn) cnm car) ->
  Get_constr cnm = Some c ->
  split_k_elements car (frm_stack f) = Some (vargs, l) ->
  wellformed_configuration (f :: M0) ->
  reduction (f :: M0)
  (mkframe (frm_fun f) (S (frm_pc f)) 
    (Node cnm (rev vargs) :: l) (frm_args f) :: M0) ->
  wellformed_configuration
  (mkframe (frm_fun f) (S (frm_pc f))
    (Node cnm (rev vargs) :: l) 
    (frm_args f) :: M0).
Proof.
  intros M0  f fcn c cnm car vargs l Hfcn case_instr Hc case_split_stack Hwf Hred.
  intros i fi fpi fcni fcnpi Hfi.
  destruct i.
  (* i = 0 *)
  inversion Hfi; subst fi.
  cut (Some f = Some f); [intro Hf | trivial].
  elim (Hwf 0 f fpi fcn fcnpi Hf); intros Hwf1 Hwf2.
  simpl; split; trivial.
  intro Hfcni; elim (Hwf2 Hfcn); clear Hwf2; intros Hwf2 Hwf3; split.
  (* S (pc f)  < |fcni| *)
  rewrite Hfcn in Hfcni; inversion Hfcni.
  subst fcni.
  cut (In fcn functions); [intro Hin | apply get_some_in_functions with (frm_fun f); trivial].
  cut (0 < fcn_size fcn); [intro Hnonvoid | apply nonvoidfcn; trivial].
  cut (frm_pc f < fcn_size fcn); 
    [apply not_pred_lt_S_lt | generalize case_instr; apply element_at_unsafe_some]; trivial.
  generalize (lrs_functions fcn Hin Hnonvoid); intros lrs pc_f_is_pred_size_f.
  destruct f as [fnm pcf stack args]; (simpl in *); subst pcf.
  elim lrs; intro case.
  cut (i_return (fcn_size fcn) = (i_build (fcn_size fcn) cnm car)); [intro F; inversion F | rewrite <- case].
  generalize case_instr; apply element_at_unsafe_to_safe.
  cut (i_stop (fcn_size fcn) = (i_build (fcn_size fcn) cnm car)); [intro F; inversion F | rewrite <- case].
  generalize case_instr; apply element_at_unsafe_to_safe.
  (* fcnpi[pc fpi] = call f |argsf| *)
  apply Hwf3; assumption.
  (* S i *)
  cut ((f :: M0)[S i] = Some fi); [intro Hsi | simpl].
  elim (Hwf (S i) fi fpi fcni fcnpi Hsi); clear Hwf; intros Hwf1 Hwf2.
  split; auto.
  apply Hfi.
Qed.

Lemma red_branch_then_keeps_wellformed : forall (M0 : configuration) (f : frame)
  (fcn : function) (cnm : name) (j : nat) (l : list value) (vf : list value)
  (Cj : j < fcn_size fcn), Get_function (frm_fun f) = Some fcn ->
  (fcn_bytecode fcn)[frm_pc f|_] = Some (i_branch (fcn_size fcn) cnm j Cj) ->
  frm_stack f = Node cnm vf :: l ->
  wellformed_configuration (f :: M0) ->
  reduction (f :: M0)
  (mkframe (frm_fun f) (S (frm_pc f))
    (push_list vf l) (frm_args f) :: M0) ->
  wellformed_configuration
  (mkframe (frm_fun f) (S (frm_pc f)) (push_list vf l)
    (frm_args f) :: M0).
Proof.
  intros M0 f fcn cnm j l vf Cj Hfcn case_instr Hstack Hwf Hred i fi fpi fcni fcnpi Hfi.
  destruct i.
  (* i = 0 *)
  inversion Hfi; subst fi.
  simpl.
  cut (Some f = Some f); [intro Hf | trivial].
  elim (Hwf 0 f fpi fcn fcnpi Hf); intros Hwf1 Hwf2.
  split; trivial.
  intro Hfcni; elim (Hwf2 Hfcn); clear Hwf2; intros Hwf2 Hwf3.
  rewrite Hfcn in Hfcni; inversion Hfcni.
  subst fcni; split.
  (* S (frm_pc f) < fcn_size fcn *)
  cut (In fcn functions); [intro Hin | apply get_some_in_functions with (frm_fun f); trivial].
  cut (0 < fcn_size fcn); [intro Hnonvoid | apply nonvoidfcn; trivial].
  cut (frm_pc f < fcn_size fcn); 
    [apply not_pred_lt_S_lt | generalize case_instr; apply element_at_unsafe_some]; trivial.
  generalize (lrs_functions fcn Hin Hnonvoid); intros lrs pc_f_is_pred_size_f.
  destruct f as [fnm pcf stack args]; (simpl in *); subst pcf.
  elim lrs; intro case.
  cut (i_return (fcn_size fcn) = (i_branch (fcn_size fcn) cnm j Cj)); [intro F; inversion F | rewrite <- case].
  generalize case_instr; apply element_at_unsafe_to_safe.
  cut (i_stop (fcn_size fcn) = (i_branch (fcn_size fcn) cnm j Cj)); [intro F; inversion F | rewrite <- case].
  generalize case_instr; apply element_at_unsafe_to_safe.
  (* fcnpi[pc fpi] = call g |argsg|*) 
  apply Hwf3; assumption.
  (* S i *)
  cut ((f :: M0)[S i] = Some fi); [intro Hsi | simpl].
  elim (Hwf (S i) fi fpi fcni fcnpi Hsi); clear Hwf; intros Hwf1 Hwf2.
  split; auto.
  apply Hfi.
Qed.

Lemma red_branch_else_keeps_wellformed : forall (M0 : configuration) (f : frame)
  (fcn : function) (cnm : name) (dnm : name) (j : nat) (l : list value)
  (vf : list value) (Cj : j < fcn_size fcn),
  Get_function (frm_fun f) = Some fcn ->
  (fcn_bytecode fcn)[frm_pc f|_] = Some (i_branch (fcn_size fcn) cnm j Cj) ->
  frm_stack f = Node dnm vf :: l-> dnm <> cnm-> wellformed_configuration (f :: M0) ->
  reduction (f :: M0) (mkframe (frm_fun f) j (frm_stack f) (frm_args f) :: M0) ->
   wellformed_configuration (mkframe (frm_fun f) j (frm_stack f) (frm_args f) :: M0).
Proof.
  intros M0 f fcn cnm dnm j l vf Cj Hfcn case_instr Hstack neq_cnm_dnm Hwf Hred i fi fpi fcni fcnpi Hfi.
  destruct i.
  (* i = 0 *)
  inversion Hfi; subst fi.
  cut (Some f = Some f); [intro Hf | trivial].
  elim (Hwf 0 f fpi fcn fcnpi Hf); intros Hwf1 Hwf2.
  simpl; split; trivial.
  intro Hfcni; rewrite Hfcn in Hfcni; inversion Hfcni.
  subst fcni; split; trivial.
  elim (Hwf2 Hfcn); clear Hwf2; intros Hwf2 Hwf3.
  apply Hwf3; assumption.
  (* S i *)
  cut ((f :: M0)[S i] = Some fi); [intro Hsi | simpl].
  elim (Hwf (S i) fi fpi fcni fcnpi Hsi); clear Hwf; intros Hwf1 Hwf2.
  split; auto.
  apply Hfi.
Qed.

Lemma reduction_keeps_wellformed : Invariant wellformed_configuration.
  Proof.
  intros M M' Hwf Hred.
  InversionRed Hred.
  (* Return *)
  apply (red_return_keeps_wellformed M0 f g fcn v0 l Hfcn); trivial.
  (* Stop *)
  intros i fi fpi fcni fcnpi F; inversion F.
  (* Load *)
  apply (red_load_keeps_wellformed M0 f fcn j vj Hfcn); trivial.
  (* Call *)
  apply (red_call_keeps_wellformed M0 f fcn gcn gnm gar vargs l Hfcn); trivial.
  (* Build *)
  apply (red_build_keeps_wellformed M0 f fcn c cnm car vargs l Hfcn); trivial.
  (* BranchThen *)
  apply (red_branch_then_keeps_wellformed M0 f fcn cnm j l vf Cj Hfcn); trivial. 
  (* BranchElse *)
  apply (red_branch_else_keeps_wellformed M0 f fcn cnm dnm j l vf Cj Hfcn); trivial.
Qed.


(* init configurations are well-formed : *)
Lemma wellformed_init_configuration : forall (fexec : name) (argsexec : list value), 
  Get_function fexec <> None -> wellformed_configuration (Init_configuration fexec argsexec).
Proof.
  intros fexec argsexec Hexec i fi fpi fcni fcnpi Hini.
  destruct i.
  (* i =0 *)
  inversion Hini; subst; simpl.
  split; trivial.
  intro Hgeti; split; [apply nonvoidfcn | intro F; inversion F].
  simpl in Hgeti; apply get_some_in_functions with fexec; assumption.
  (* i > 0 *)
  inversion Hini.
Qed.

(* each configuration in an execution is well-formed *)
Lemma wellformed_execution : forall (fexec : name) (argsexec : list value) (L : list configuration),
  Get_function fexec <> None ->
  execution fexec argsexec L -> forall (M : configuration), In M L -> wellformed_configuration M.
Proof.  
  intros fexec argsexec L Hget Hexec M Hin. 
  generalize (wellformed_init_configuration fexec argsexec Hget); intro Hwf0.
  apply (reduction_to_execution wellformed_configuration fexec argsexec 
    Hwf0 reduction_keeps_wellformed L); assumption.
Qed.


End machine.


Ltac InversionRed H := inversion H as [M0 f g fcn v0 l Hfcn case_instr Hstack 
                                       | M0 f fcn Hfcn case_instr 
                                       | M0 f fcn j vj Hfcn case_instr Hvj 
                                       | M0 f fcn gcn gnm gar vargs l Hfcn 
                                         case_instr Hgcn case_split_stack 
                                       | M0 f fcn c cnm car vargs l Hfcn 
					 case_instr Hc case_split_stack 
                                       | M0 f fcn cnm j l vf Cj Hfcn case_instr Hstack 
                                       | M0 f fcn cnm dnm j l vf Cj Hfcn case_instr Hstack neq_cnm_dnm];
                       subst.

Ltac InversionRed' H := inversion H as [M0' f' g' fcn' v0' l' Hfcn' case_instr' Hstack' 
                                        | M0' f' fcn' Hfcn' case_instr' 
                                        | M0' f' fcn' j' vj' Hfcn' case_instr' Hvj' 
                                        | M0' f' fcn' gcn' gnm' gar' vargs' l' Hfcn' 
                                          case_instr' Hgcn' case_split_stack' 
                                        | M0' f' fcn' c' cnm' car' vargs' l' Hfcn' 
                                          case_instr' Hc' case_split_stack' 
                                        | M0' f' fcn' cnm' j' l' vf' Cj' Hfcn' 
                                          case_instr' Hstack' 
                                        | M0' f' fcn' cnm' dnm' j' l' vf' Cj' Hfcn' 
                                          case_instr' Hstack' neq_cnm_dnm']; 
                        subst.
