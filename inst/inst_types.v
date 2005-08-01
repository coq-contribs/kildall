  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : inst_types.v				         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : instanciation of kildall's algorithm for        *)
  (*             type analysis                                   *)
  (***************************************************************)

Section inst_types.

  Require Export machine.
  Require Export kildall_bv.

  Variable fcn : function. (* the function on which verification is performed *)
  Notation n := (fcn_size fcn).
  Notation bc := (fcn_bytecode fcn).
  Notation Rt := (fcn_ret fcn).
  Notation Instruction := (instruction n).
  Notation Get_function := (get_function_by_name functions).
  Notation Get_constr := (get_constr_by_name constructors).

  (* set of the instructions' states *)
  Inductive Sigma : Set :=
    | Top_T : Sigma (* top element *)
    | Bot_T : Sigma (* bottom element *)
    | Types : list name->Sigma. (* list of type names, one for each element on the actual stack *)

  (* order on Sigma *)
  Definition r (a : Sigma) (b : Sigma) : Prop :=
    match a,b with
      _, Top_T => True 
      |
        Top_T, _ => False
      |
        Bot_T, _ => True
      |
        _, Bot_T => False
      |
        a, b => a=b
    end.

  Lemma eq_list_name_dec : forall (a b : list name), {a=b}+{a<>b}.
  Proof.
    apply list_eq_dec.
    apply eq_name_dec.
  Qed.

  (* sup on Sigma *)
  Definition f (a : Sigma) (b : Sigma) : Sigma :=
    match a,b with
      _, Top_T => Top_T
      |
        Top_T, _ => Top_T
      |
        Bot_T, x => x
      |
        x, Bot_T => x
      |
        Types a, Types b => match (eq_list_name_dec a b) with 
      	       	              left _ => Types a
		              |
		                right _ => Top_T
		            end
    end.

  (************************************************************************)
  (*                     Results on (Sigma, r, f)                         *)
  (************************************************************************)

  Lemma eq_Sigma_dec : forall (t t' : Sigma), {t=t'} + {t<>t'}.
  Proof.
    induction t.
    intro t'; destruct t'; [left | right | right]; try (intro h; inversion h).
    trivial.
    intro t'; destruct t'; [right | left | right]; try (intro h; inversion h).
    trivial.
    intro t'; destruct t'; [right | right | idtac]; try (intro h; inversion h).
    elim (eq_list_name_dec l l0); intro case; [left | right].
    subst l; trivial.
    intro h; inversion h; apply case; trivial.
  Qed.

  Lemma Top_T_top : forall (a : Sigma), r a Top_T.
  Proof.
    intro a; destruct a; constructor.
  Qed.

  Lemma Bot_T_bot : forall (a : Sigma), r Bot_T a.
  Proof.
    intro a; destruct a; constructor.
  Qed.

  Lemma r_is_order : order Sigma r.
  Proof.
    split.
  (*refl*)
    intro x.
    elim x; constructor.
  (*trans*)
    intros x y z.
    elim x.
    elim y.
    intro H; clear H; elim z; trivial.
    intro H; inversion H.
    intros l H; inversion H.
    elim z; constructor.
    intro l; elim y.
    elim z.
    trivial.
    intros h H; inversion H.
    intros l' h H; inversion H.
    intro H; inversion H.
    intros l0 H.
    inversion H.
    subst l0.
    trivial.
  (*antisym*)
    intros x y.
    elim x; elim y; try trivial; intros H1 H2.
    inversion H1.
    inversion H2.
    inversion H2.
    intro H; inversion H.
    intro H; inversion H.
    inversion H2.
  Qed.

  Lemma f_is_lub : lub Sigma r f.
  Proof.
    split.
  (* lub1 *)
    intros a b.
    elim a.
    elim b; constructor.
    apply Bot_T_bot.
    elim b; try constructor.
    unfold f; intros l l0; elim (eq_list_name_dec l0 l); constructor.
    split; intros a b.
  (* lub2 *)
    elim b.
    elim a; constructor.
    apply Bot_T_bot.
    elim a; try constructor.
    unfold f; intros l l0; elim (eq_list_name_dec l l0); intro case.
    subst l; constructor.
    constructor.
  (* lub3 *)
    intros c H; elim H; clear H; intros rac rbc.
    destruct c.
    apply Top_T_top.
    destruct a; destruct b; try inversion rac; try inversion rbc.
    constructor.
    unfold f; destruct a; destruct b; try inversion rac; try inversion rbc; try constructor.
    elim (eq_list_name_dec l l); intro case; [constructor | elim case]; trivial.
  Qed.

  Lemma r_is_semilattice : semilattice Sigma r f.
  Proof.
    split.
    apply r_is_order.
    apply f_is_lub.
  Qed.

  Lemma AccTop_T : Acc (strict (inv r)) Top_T.
  Proof.
    constructor.
    intros y H; elim H; clear H; intros H1 H2.
    destruct y; try inversion H1.
    elim H2; trivial.
  Qed.

  Lemma AccSl : forall (l : list name), Acc (strict (inv r)) (Types l).
  Proof.
    intro l; constructor.
    intros y H; elim H; clear H; intros H1 H2.
    destruct y; try inversion H1.
    apply AccTop_T.
    subst l0; elim H2; trivial.
  Qed.

  Lemma wfr : ascending_chain r.
  Proof.
    unfold ascending_chain.
    unfold well_founded.
    induction a.
    apply AccTop_T.
    constructor; intros y H; elim H; clear H; intros H1 H2.
    destruct y.
    apply AccTop_T.
    elim H2; trivial.
    apply AccSl.
    apply AccSl.
  Qed.


  (************************************************************************)
  (*                       Definition of Step                             *)
  (************************************************************************)

  Definition Step (p:nat) (C: p <n) (s:Sigma) :  list Sigma := 
    match bc[p|C] with 
    (* Return *)
      | i_return => 
        match s with 
          | Bot_T => Bot_T :: nil
          | Top_T => Top_T :: nil
          | Types l => 
      	    match l with 
      	      | nil => Top_T :: nil
      	      | e::t => 	
      	        match (eq_name_dec e Rt) with 
      	          | left _ => (Types (e::t)) :: nil
      	          | right _ => Top_T :: nil
      	        end
      	    end
        end
    (* Stop *)
      | i_stop => nil
    (* Load *)
      | i_load i => 
        match s with 
          | Bot_T => Bot_T :: nil
          | Top_T => Top_T :: nil
          | Types l => 
      	    match (rev l)[i] with
	      | Some h => (Types (h::l)) :: nil
	      |  _ => Top_T :: nil
	    end
        end
    (* Call *)
      | i_call g ar => 	
        match s with 
          | Bot_T => Bot_T :: nil
          | Top_T => Top_T :: nil
          | Types l => 
      	    match (split_k_elements ar l) with 
      	      | Some (lk, lr) => 
      	        match (Get_function g) with
      	          | Some gcn => 
      	       	    match (eq_list_name_dec (rev lk) (fcn_args gcn)) with 
      	       	      | left _ => (Types ((fcn_ret gcn)::lr)) :: nil
      	       	      | right _ => Top_T :: nil
      	       	    end
      	          | _ => Top_T :: nil
      	        end
      	      | _ => Top_T :: nil
      	    end
        end
    (* Build *)
      | i_build c ar => 
        match s with 
          | Bot_T => Bot_T :: nil
          | Top_T => Top_T :: nil
          | Types l => 
      	    match (split_k_elements ar l) with 
      	      | Some (lk,lr) => 
      	        match (Get_constr c) with
      	          | Some const => 
      	       	    match eq_list_name_dec (rev lk) (cons_args const) with 
                      | left _ => (Types ((cons_ret const)::lr)) :: nil
      	       	      | right _ => Top_T :: nil
      	       	    end
                  | _ => Top_T :: nil
      	        end
              | _ => Top_T :: nil
      	    end
        end
    (* Branch *)
      | i_branch c _ _ => 
        match s with 
        | Bot_T => Bot_T :: (Bot_T :: nil)
        | Top_T => Top_T :: (Top_T :: nil)
        |  Types l => 
      	  match (Get_constr c) with
      	    | Some const => 
      	      match l with
      	       | h::t => 
      	         match eq_name_dec h (cons_ret const) with
      	       	  | left _ => (Types ((rev (cons_args const))++t)) :: ((Types l) :: nil)
      	       	  | right _ => Top_T :: (Top_T :: nil)
      	         end
      	       | nil => Top_T :: (Top_T :: nil)
      	      end
            | _ => Top_T :: (Top_T :: nil)
      	   end                    
        end
    end.

  (* Step does not vary upon its second argument *)
  Lemma Step_equiv : forall (p:nat) (C C': p <n) (s:Sigma), 
    (Step p C s) = (Step p C' s).
  Proof.
    intros; unfold Step.
    rewrite (element_at_irrel Instruction n bc p C' C).
    trivial.
  Qed.

  
  Lemma Step_Succs_aux_same_length : forall (p:nat) (C: p <n) (s:Sigma), 
    nb_length (Succs_aux n bc p C) = length (Step p C s).
  Proof.
    intros p C s.
    unfold Succs_aux ; unfold Step.
    destruct (bc[p|C]) as [ | | j | fnm ar | cnm ar | cnm j Cj]; try elim s; simpl; trivial.
    (* return *)
    intro l; destruct l as [ | e l']; simpl.
    trivial.
    elim (eq_name_dec e Rt); simpl; trivial.
    (* load *)
    intro l.
    CaseEq ((rev l)[j]); simpl; trivial.
    (* call *)
    intros l.
    elim (split_k_elements ar l); elim (Get_function fnm); simpl; try trivial.
    intros a a0; elim a0; simpl; try trivial.
    intros a1 b; elim (eq_list_name_dec (rev a1) (fcn_args a)); simpl; trivial.
    intro a; destruct a; simpl; trivial.
    (* build *)
    intro l.
    elim (split_k_elements ar l); elim (Get_constr cnm); simpl; try trivial.
    intros a a0; elim a0; simpl; try trivial.
    intros a1 b; elim (eq_list_name_dec (rev a1) (cons_args a)); simpl; trivial.
    intro a; destruct a; simpl; trivial.
    (* branch *)
    intros l.
    elim (Get_constr cnm); simpl; try trivial.
    destruct l; simpl; try trivial.
    intros a; elim (eq_name_dec n (cons_ret a)); simpl; trivial.
  Defined.

    (* Step and Succs produce same length lists *)
  Lemma Step_Succs_same_length : forall (lr : last_return_or_stop n bc) (p:nat) (C: p <n) (s:Sigma), 
    nb_length (Succs n bc lr p C) = length (Step p C s).
  Proof.
    intros lr p C s.
    replace (nb_length (Succs n bc lr p C)) with (nb_length (Succs_aux n bc p C)).
    apply Step_Succs_aux_same_length; assumption.
    unfold Succs.
    apply nb_list_convert_length with (l:=Succs_aux n bc p C) (H:=Succs_better_bound n bc p C lr).
  Defined.


  Lemma refl_dep_r : forall (l : list Sigma), 
    list_pointwise Sigma r l l.
  Proof.
    induction l; try constructor.
    elim a; constructor.
    apply IHl.
  Qed.


  Lemma dep_r_Bot_T_1 : forall (l : list Sigma), 
    1 = length l -> list_pointwise Sigma r (Bot_T :: nil) l.
  Proof.
    induction l; simpl; intro H. 
    inversion H.
    constructor.
    apply Bot_T_bot.
    destruct l; try constructor; simpl in H.
    inversion H.
  Qed.

  Lemma dep_r_Top_T_1 : forall (l : list Sigma), 
    1 = length l -> list_pointwise Sigma r l (Top_T :: nil).
  Proof.
    induction l; simpl; intro H. 
    inversion H.
    constructor.
    apply Top_T_top.
    destruct l; try constructor; simpl in H.
    inversion H.
  Qed.

  Lemma dep_r_Bot_T_2 : forall (l : list Sigma), 
    2 = length l -> list_pointwise Sigma r (Bot_T :: (Bot_T :: nil)) l.
  Proof.
    induction l; simpl; intro H. 
    inversion H.
    destruct l; simpl.
    inversion H.
    constructor.
    apply Bot_T_bot.
    constructor.
    apply Bot_T_bot.
    destruct l; try constructor; simpl in H.
    inversion H.
  Qed.

  Lemma dep_r_Top_T_2 : forall (l : list Sigma), 
    2 = length l -> list_pointwise Sigma r l (Top_T :: (Top_T :: nil)).
  Proof.
    induction l; simpl; intro H. 
    inversion H.
    destruct l; simpl.
    inversion H.
    constructor.
    apply Top_T_top.
    constructor.
    apply Top_T_top.
    destruct l; try constructor; simpl in H.
    inversion H.
  Qed.

    (* monotonicity of Step : *)
  Lemma monotone_Step : monotonestep Sigma n Step r.
  Proof.
    intros p C s t rst.
    destruct s; destruct t; try inversion rst.
    apply refl_dep_r.
    unfold Step; CaseEq (bc[p|C]); simpl; auto; try constructor; auto; try constructor.
    assumption.
    constructor.
    apply refl_dep_r.
    (* list_pointwise Sigma r (Step p C Bot_T) (Step p C (Types l)) : *)
    unfold Step; CaseEq (bc[p|C]); simpl; auto; try constructor; auto; try constructor.
    (* return *)
    intro; apply dep_r_Bot_T_1. 
    destruct l as [ | e t]; simpl.
    trivial.
    elim (eq_name_dec e Rt); simpl; trivial.
    (* load *)
    intros j case; apply dep_r_Bot_T_1.
    CaseEq ((rev l)[j]); simpl; trivial.
    (* call *)
    intros g ar case; apply dep_r_Bot_T_1.
    elim (split_k_elements ar l); elim (Get_function g); simpl; try trivial.
    intros gcn p0; destruct p0 as [lk lr].
    elim (eq_list_name_dec (rev lk) (fcn_args gcn)); simpl; trivial.
    intro p0; destruct p0; simpl; trivial.
    (* build *)
    intros c ar case; apply dep_r_Bot_T_1.
    elim (split_k_elements ar l); elim (Get_constr c); simpl; trivial.
    intros cnst p0; destruct p0 as [lk lr].
    elim (eq_list_name_dec (rev lk) (cons_args cnst)); simpl; trivial.
    intro a; destruct a; simpl; trivial.
    (* branch *)
    intros c i Ci case; apply dep_r_Bot_T_2.
    elim (Get_constr c); simpl; try trivial.
    intro cnst; destruct l as [|h t]; simpl; trivial.
    elim (eq_name_dec h (cons_ret cnst)); simpl; try trivial.
    (* list_pointwise Sigma r (Step p C (Types l)) (Step p C Top_T)  : *)
    unfold Step; CaseEq (bc[p|C]); simpl; auto; try constructor; auto; try constructor.
    (* return *)
    intro; apply dep_r_Top_T_1. 
    destruct l as [| h t]; simpl.
    trivial.
    elim (eq_name_dec h Rt); simpl; trivial.
    (* load *)
    intros j case; apply dep_r_Top_T_1.
    destruct ((rev l)[j]); simpl; trivial.
    (* call *)
    intros g ar case; apply dep_r_Top_T_1.
    elim (split_k_elements ar l); elim (Get_function g); simpl; trivial. 
    intros gcn p0; destruct p0 as [lk lr].
    elim (eq_list_name_dec (rev lk) (fcn_args gcn)); simpl; trivial.
    intro a; destruct a; simpl; trivial.
    (* build *)
    intros c ar case; apply dep_r_Top_T_1.
    elim (split_k_elements ar l); elim (Get_constr c); simpl; trivial. 
    intros cnst p0; destruct p0 as [lk lr].
    elim (eq_list_name_dec (rev lk) (cons_args cnst)); simpl; trivial.
    intro a; destruct a; simpl; trivial.
    (* branch *)
    intros c i Ci case; apply dep_r_Top_T_2.
    elim (Get_constr c); destruct l as [|h t]; simpl; trivial.
    intro cnst; elim (eq_name_dec h (cons_ret cnst)); simpl; trivial.
    (* list_pointwise Sigma r (Step p C (Types l0)) (Step p C (Types l0)) : *)
    apply refl_dep_r.
  Qed.


    (************************************************************************)
    (*                          Definition of Wti                           *)
    (************************************************************************)

  Definition Wti (ss : vector Sigma n) (p : nat) (C : p < n): Prop :=
    match (ss[p|C]) with 
      Top_T => False
      |
        Bot_T => True
      | 
        Types l => 
        match (bc[p|C]) with
         (* Return *)
          i_return => 
          match l with 
            Ret::t => 	
            match (eq_name_dec Ret Rt) with 	
      	      left _ => True 
      	      | 
      	        right _ => False
      	    end 
      	    |
      	      _ => False
          end
          |
         (* Stop *)
            i_stop => True
          |
         (* Load *)
            i_load i => 
            match (ss[S p|_]) with
	      Some (Types l') => 
      	      match ((rev l)[i]) with
      	        Some li => 
      	        match (eq_list_name_dec (li::l) l') with
      	       	  left _ => True
      	       	  |
      	       	    right _ => False
	        end 
	        |
	          None => False
	      end
      	      |
      	        _ => False
            end
          |
         (* Call *)
            i_call g ar => 
            match (split_k_elements ar l) with 
      	      Some (lk, lr) => 
      	      match (Get_function g) with
      	        Some gcn => 
      	        match (eq_list_name_dec (rev lk) (fcn_args gcn)) with 
      	       	  left _ => 
      	       	    match (ss[S p|_]) with
      	       	      Some (Types l') => 	
      	       	      match (eq_list_name_dec ((fcn_ret gcn)::lr) l') with
      	       	       	left _ => True
      	       	       	|
      	       	       	  right _ => False
      	       	      end 
      	       	      |
      	       	        _ => False
      	       	    end
      	       	  |
      	       	    right _ => False
      	        end
      	        |
      	          _ => False
      	      end
      	      |
      	        _ => False
            end
          |
         (* Build *)
            i_build c ar => 
            match (split_k_elements ar l) with 
      	      Some (lk, lr) => 
      	      match (Get_constr c) with
      	        Some const => 	
      	        match (eq_list_name_dec (rev lk) (cons_args const)) with 
      	       	  left _ => 
      	       	    match (ss[S p|_]) with
      	       	      Some (Types l') => 
      	       	      match (eq_list_name_dec ((cons_ret const)::lr) l') with
      	       	       	left _ => True
      	       	       	|
      	       	       	  right _ => False
      	       	      end 
      	       	      |
      	       	        _ => False
      	       	    end
      	       	  |
      	       	    right _ => False
      	        end
      	        |
      	          _ => False
      	      end
      	      |
      	        _ => False
            end
          |
         (* Branch *)
            i_branch c i Ci => 
            (match eq_Sigma_dec (ss[p|C]) (ss[i|Ci]) with 
	       left _ => True 
      	       |
      	         right _ => False
             end) 
            /\
            (match (Get_constr c) with
      	       Some const => 
      	       match l with
      	         h::t => 
      	         match (eq_name_dec (cons_ret const) h) with 
      	       	   left _ =>
      	       	     match (ss[S p|_]) with
      	       	       Some (Types l') => 
      	       	       match (eq_list_name_dec ((rev (cons_args const))++t) l') with
      	       	       	 left _ => True
      	       	       	 |
      	       	       	   right _ => False
      	       	       end 
      	       	       |
      	       	         _ => False
      	       	     end
      	       	   |
      	       	     right _ => False
      	         end
      	         |
      	           _ => False
      	       end
      	       |
      	         _ => False
             end)
        end
    end.

    (* Program states for which Wti holds at rank p are stable at rank p *)
  Lemma Wti_imp_stable : forall (lrs_bc : last_return_or_stop n bc) (ss : vector Sigma n) 
    (p : nat) (C : p < n) (Tfree : ~ Top_T INv ss), 
    Wti ss p C -> stable Sigma n (Succs n bc lrs_bc) Step r (Step_Succs_same_length lrs_bc) ss p C.
  Proof.

    unfold stable.
    intros lrs_bc ss p C Tfree Wt q t H .
    cut (q <n); [intro Cq | apply (m_list_get_witness (step' Sigma n (Succs n bc lrs_bc) Step
      (Step_Succs_same_length lrs_bc) p C (ss[p|C])) (q, t) H)].
    rewrite (element_at_irrel Sigma n ss q (m_list_get_witness (step' Sigma n (Succs n bc lrs_bc) Step
      (Step_Succs_same_length lrs_bc) p C (ss[p|C])) (q, t) H)Cq).
    cut (m_list_belong (combine (Succs_aux n bc p C) (Step p C (ss[p|C])) 
      (Step_Succs_aux_same_length p C (ss[p|C]))) (q, t)); 
    [clear H | generalize H; unfold step'; unfold Succs; apply m_list_convert_belong].
    clear lrs_bc.
    generalize Wt; clear Wt. 
    CaseEq (ss[p|C]).
    (* Top_T *)
    unfold Wti; intros case H; rewrite case in H; inversion H. 
    (* Bot_T *)
    intros case dd Hbelong; clear dd; 
      cut (m_list_belong_snd (combine (Succs_aux n bc p C) (Step p C Bot_T) (Step_Succs_aux_same_length p C Bot_T)) t).
    clear Hbelong; intro Hbelong; generalize (in_snd_combine_in_snd _ _ _ _ _ _ Hbelong).
    intro Hin; replace t with Bot_T.
    apply Bot_T_bot.
    unfold Step in Hin; destruct (bc[p|C]); inversion Hin; trivial; try inversion H; trivial.
    inversion H0.
    generalize Hbelong; apply belong_and_snd.
    (* Some l *)
    intros l case.
    unfold Wti; unfold Step; unfold Succs_aux; unfold Step_Succs_aux_same_length; 
      rewrite case; destruct (bc[p|C]); simpl.
    (* return *)
    CaseEq l; [intros case' H; inversion H | intros n0 l0 case']. 
    elim (eq_name_dec n0 Rt); intros case'' H' H.
    subst n0. 
    inversion H; inversion H0.
    subst q; rewrite (element_at_irrel Sigma n ss p Cq C); rewrite case; rewrite case'; constructor.
    inversion H'.
    (* stop *)
    intros dd H; inversion H.
    (* load *)
    CaseEq (ss[S p|_]).

    intros l0 case'.
    destruct l0.
    intro F; inversion F.
    intro F; inversion F.
    destruct ((rev l)[n]).
    elim (eq_list_name_dec (n0 :: l) l0); intros case'' H; [clear H | inversion H].
    intro H; inversion H; inversion H0.
    subst q; subst l0; subst t.
    rewrite (element_at_unsafe_to_safe Sigma _ ss (S p) Cq (Types (n0 :: l)) case').
    constructor.
    intro F; inversion F.

    intros case' H; inversion H.

    (* call *)
    generalize (split_k_elements_ok name n0 l); intro Hsplit_ok.
    destruct (split_k_elements n0 l); [idtac | intro F; inversion F].
    destruct p0.
    CaseEq (Get_function n); [idtac | intros dd F; inversion F].
    intros f0 case_fun.
    cut (l = l0 ++ l1); [intro; subst l | apply (Hsplit_ok l0 l1); trivial].
    clear Hsplit_ok.
    CaseEq (ss[S p|_]). 
    intros s case_ss_S_p; destruct s.
    intro H; cut False; [intro F; inversion F | idtac]. 
    generalize H; elim (eq_list_name_dec (rev l0) (fcn_args f0)); trivial.
    intro H; cut False; [intro F; inversion F | idtac]. 
    generalize H; elim (eq_list_name_dec (rev l0) (fcn_args f0)); trivial.
    elim (eq_list_name_dec ((fcn_ret f0) :: l1) l).
    intro; subst l.
    destruct f0.
    simpl in *.
    elim (eq_list_name_dec (rev l0) fcn_args).
    intros case_sign d H; inversion H; inversion H0.
    subst q t.
    rewrite (element_at_unsafe_to_safe Sigma _ ss (S p) Cq (Types (fcn_ret :: l1)) case_ss_S_p).
    constructor.
    intros dd F; inversion F.
    intros dd H; cut False; [intro F; inversion F | idtac]. 
    generalize H; elim (eq_list_name_dec (rev l0) (fcn_args f0)); trivial.
    intros dd H; cut False; [intro F; inversion F | idtac]. 
    generalize H; elim (eq_list_name_dec (rev l0) (fcn_args f0)); trivial.

    (* build *)
    generalize (split_k_elements_ok name n0 l); intro Hsplit_ok.
    destruct (split_k_elements n0 l).
    destruct p0.
    CaseEq (Get_constr n).
    intros c case_constr.
    destruct c; simpl in *.
    elim (eq_list_name_dec (rev l0) cons_args).
    CaseEq (ss[S p|_]).
    intros s case_ss_S_p case_cons.
    destruct s.
    intro F; inversion F.
    intro F; inversion F.
    elim (eq_list_name_dec (cons_ret :: l1) l2); intro case_eq.
    intros dd H; clear dd; inversion H; inversion H0; subst l2 cons_args q t.
    rewrite (element_at_unsafe_to_safe Sigma _ ss (S p) Cq (Types (cons_ret :: l1)) case_ss_S_p).
    constructor.
    intro F; inversion F.
    intros H H' F; inversion F.
    intros H F; inversion F.
    intros H F; inversion F.
    intro F; inversion F.

    (* branch *)
    elim (eq_Sigma_dec (Types l) (ss[i|l0])); intro case2.
    intro H; elim H; clear H; intro H; clear H.
    destruct (Get_constr c).
    destruct c0; simpl in *.
    destruct l.
    intro H; inversion H.
    simpl.
    elim (eq_name_dec cons_ret n); intro comp3.
    CaseEq (ss[S p|_]).
    intros s case_ss_S_p; destruct s.
    intro H; inversion H.
    intro H; inversion H.
    elim (eq_list_name_dec (rev cons_args ++ l) l1); intro comp.
    intro dd; clear dd.
    simpl.
    elim (eq_name_dec n cons_ret); intro comp2.
    intro H; inversion H; clear H.
    inversion H0.
    subst q t n l1.
    rewrite (element_at_unsafe_to_safe Sigma _ ss (S p) Cq (Types (rev cons_args ++ l)) case_ss_S_p).
    constructor.
    subst n.
    inversion H0.
    inversion H.
    subst q t.
    rewrite (element_at_irrel Sigma n ss i Cq l0).
    rewrite <- case2.
    constructor.
    inversion H.
    elim comp2; symmetry; assumption.
    intro H; inversion H.
    intros dd H; inversion H.
    intro H; inversion H.
    intro H; inversion H.
    intro H; elim H; clear H; intro H; inversion H.
  Qed.


  Lemma stable_imp_Wti : forall (lrs_bc : last_return_or_stop n bc) (ss : vector Sigma n) 
    (p : nat) (C : p < n) (Tfree : ~ Top_T INv ss), 
    stable Sigma n (Succs n bc lrs_bc) Step r (Step_Succs_same_length lrs_bc) ss p C -> Wti ss p C.
  Proof.
    unfold stable.
    intros lrs_bc ss p C Tfree H.
    cut (forall (q : nat) (Cq : q < n) (t : Sigma)
      (H : m_list_belong (combine (Succs_aux n bc p C) (Step p C (ss[p|C])) 
      	(Step_Succs_aux_same_length p C (ss[p|C]))) (q,t)), 
      r t (ss[q|Cq])).
    clear H.
    unfold Wti; unfold Step; unfold Succs_aux. 
    CaseEq (ss[p|C]).
    (* Top_T *)
    intro case; elim Tfree; rewrite <- case; apply element_at_belong. 
    (* Bot_T *)
    intro case; unfold Step_Succs_aux_same_length; destruct (bc[p|C]); simpl; trivial.
    (* Some l *)
    intros l case.
    cut ((p = pred n) -> (bc[p|C] = i_return n \/ bc[p|C] = i_stop n)).
    intro alt_lrsbc.
    unfold Step_Succs_aux_same_length; destruct (bc[p|C]) as [| |j|g ar|c ar|c j Cj]; simpl.
    (* return *)
    CaseEq l.
    intros case' H.
    generalize (H p C Top_T); clear H; intro H.
    simpl in H.
    cut ((p, Top_T) = (p, Top_T) \/ False).
    intro H1.
    generalize (H H1); clear H.
    CaseEq (ss[p|C]).
    rewrite case.
    intro H2; inversion H2.
    intros; assumption.
    intros; assumption.
    left; trivial.
    intros n0 l0 casel.
    elim (eq_name_dec n0 Rt); intro comp; simpl.
    trivial.
    intro H; generalize (H p C Top_T); clear H; intro H.
    cut ((p, Top_T) = (p, Top_T) \/ False).
    intro H1; generalize (H H1); clear H.
    rewrite case; intro H.
    inversion H.
    left; trivial.
    (* stop *)
    trivial.
    (* load *)
    destruct ((rev l)[j]) as [lj| ].
    cut (S p < n).
    intro Csp.
    cut ((S p, Top_T) = (S p, Top_T) \/ False).
    intro casebelong.

    CaseEq (ss[S p|_]).
    intros s case_ss_S_p.
    simpl; cut ((S p, Types (lj :: l)) = (S p, Types (lj :: l)) \/ False); [intro casebelong' | left; trivial]. 
    intro H; generalize (H (S p) Csp (Types (lj :: l)) casebelong'); clear H; intro H.
    destruct s.
    apply Tfree.
    replace Top_T with ((ss[S p|Csp])).
    apply element_at_belong.
    apply (element_at_unsafe_to_safe Sigma n ss (S p) Csp Top_T case_ss_S_p). 
    replace (ss[S p|Csp]) with Bot_T in H.
    inversion H.
    symmetry; apply (element_at_unsafe_to_safe Sigma n ss (S p) Csp Bot_T case_ss_S_p).
    elim (eq_list_name_dec (lj :: l) l0); intro comp.
    trivial.
    elim comp.
    replace (ss[S p|Csp]) with (Types l0) in H.
    inversion H; trivial.
    symmetry; apply (element_at_unsafe_to_safe Sigma n ss (S p) Csp (Types l0) case_ss_S_p).

    intros case_ss_S_p H.

    generalize (element_at_unsafe_none Sigma n ss (S p) case_ss_S_p).
    apply lt_not_ge; assumption.
    left; trivial.

    compare p (pred n); intro comp.
    elim (alt_lrsbc comp); intro cc; inversion cc.
    clear alt_lrsbc lj case l Tfree ss lrs_bc.
    destruct n.
    inversion C.
    cut (p < n).
    auto with arith.
    simpl in comp.
    apply lt_S_neq_lt; assumption.

    simpl.
    cut (S p < n).
    intro Csp.
    intro H; CaseEq (ss[S p|_]).
    destruct s; intro case_ss_S_p.
    apply Tfree.
    replace Top_T with ((ss[S p|Csp])).
    apply element_at_belong.
    apply (element_at_unsafe_to_safe Sigma n ss (S p) Csp Top_T case_ss_S_p). 
    cut ((S p, Top_T) = (S p, Top_T) \/ False); [intro case_belong | left; trivial].
    generalize (H (S p) Csp Top_T case_belong); clear H; intro H.
    replace (ss[S p|Csp]) with Bot_T in H.
    inversion H.
    symmetry; apply (element_at_unsafe_to_safe Sigma n ss (S p) Csp Bot_T case_ss_S_p).
    cut ((S p, Top_T) = (S p, Top_T) \/ False); [intro case_belong | left; trivial].
    generalize (H (S p) Csp Top_T case_belong); clear H; intro H.
    replace (ss[S p|Csp]) with (Types l0) in H.
    inversion H.
    symmetry; apply (element_at_unsafe_to_safe Sigma n ss (S p) Csp (Types l0) case_ss_S_p).
    intro case_ss_S_p; generalize (element_at_unsafe_none Sigma n ss (S p) case_ss_S_p).
    apply lt_not_ge; assumption.

    compare p (pred n); intro comp.
    elim (alt_lrsbc comp); intro cc; inversion cc.
    clear alt_lrsbc j case l Tfree ss lrs_bc.
    destruct n.
    inversion C.
    cut (p < n).
    auto with arith.
    simpl in comp.
    apply lt_S_neq_lt; assumption.

    (* call *)
    cut (S p < n).
    intro Csp.
    cut ((S p, Top_T) = (S p, Top_T) \/ False); [intro casebelong | left; trivial].
    destruct (split_k_elements ar l); simpl.
    destruct p0.
    destruct (Get_function g).
    destruct f0; simpl.
    elim (eq_list_name_dec (rev l0) fcn_args); intro case_fcn.
    CaseEq (ss[S p|_]).
    cut ((S p, Types (fcn_ret :: l1)) = (S p, Types (fcn_ret :: l1)) \/ False); [intro case_belong | left; trivial].
    intros s case_ss_S_p H; generalize (H (S p) Csp (Types (fcn_ret :: l1)) case_belong); 
      clear H; intro H; destruct s.
    apply Tfree.
    replace Top_T with (ss[S p|Csp]). 
    apply element_at_belong.
    apply element_at_unsafe_to_safe; assumption.
    replace (ss[S p|Csp]) with Bot_T in H.
    inversion H.
    symmetry; apply element_at_unsafe_to_safe; assumption.
    elim (eq_list_name_dec (fcn_ret :: l1) l2); intro comp.
    trivial.
    apply comp.
    replace (ss[S p|Csp]) with (Types l2) in H.
    inversion H; trivial.
    symmetry; apply element_at_unsafe_to_safe; assumption.

    intros case_ss_S_p H; generalize (element_at_unsafe_none Sigma n ss (S p) case_ss_S_p).
    apply lt_not_ge; assumption.
    simpl; intro H; generalize (H (S p) Csp Top_T casebelong); clear H.
    CaseEq (ss[S p|Csp]). 
    intros case_ss_S_p dd; clear dd; apply Tfree.
    replace Top_T with (ss[S p|Csp]). 
    apply element_at_belong.
    intros H' H; inversion H.
    intros l' H' H; inversion H.

    simpl; intro H; generalize (H (S p) Csp Top_T casebelong); clear H.
    CaseEq (ss[S p|Csp]). 
    intros case_ss_S_p dd; clear dd; apply Tfree.
    replace Top_T with (ss[S p|Csp]). 
    apply element_at_belong.
    intros H' H; inversion H.
    intros l' H' H; inversion H.

    simpl; intro H; generalize (H (S p) Csp Top_T casebelong); clear H.
    CaseEq (ss[S p|Csp]). 
    intros case_ss_S_p dd; clear dd; apply Tfree.
    replace Top_T with (ss[S p|Csp]). 
    apply element_at_belong.
    intros H' H; inversion H.
    intros l' H' H; inversion H.

    compare p (pred n); intro comp.
    elim (alt_lrsbc comp); intro cc; inversion cc.
    clear alt_lrsbc ar case l Tfree ss lrs_bc.
    destruct n.
    inversion C.
    cut (p < n).
    auto with arith.
    simpl in comp.
    apply lt_S_neq_lt; assumption.

    (* build *)
    cut (S p < n).
    intro Csp.
    cut ((S p, Top_T) = (S p, Top_T) \/ False); [intro casebelong | left; trivial].
    destruct (split_k_elements ar l); simpl.
    destruct p0.
    destruct (Get_constr c).
    destruct c0; simpl.
    elim (eq_list_name_dec (rev l0) cons_args); intro case_cons.
    CaseEq (ss[S p|_]).
    cut ((S p, Types (cons_ret :: l1)) = (S p, Types (cons_ret :: l1)) \/ False); [intro case_belong | left; trivial].
    intros s case_ss_S_p H; generalize (H (S p) Csp (Types (cons_ret :: l1)) case_belong); 
      clear H; intro H; destruct s.
    apply Tfree.
    replace Top_T with (ss[S p|Csp]). 
    apply element_at_belong.
    apply element_at_unsafe_to_safe; assumption.
    replace (ss[S p|Csp]) with Bot_T in H.
    inversion H.
    symmetry; apply element_at_unsafe_to_safe; assumption.
    elim (eq_list_name_dec (cons_ret :: l1) l2); intro comp.
    trivial.
    apply comp.
    replace (ss[S p|Csp]) with (Types l2) in H.
    inversion H; trivial.
    symmetry; apply element_at_unsafe_to_safe; assumption.

    intros case_ss_S_p H; generalize (element_at_unsafe_none Sigma n ss (S p) case_ss_S_p).
    apply lt_not_ge; assumption.
    simpl; intro H; generalize (H (S p) Csp Top_T casebelong); clear H.
    CaseEq (ss[S p|Csp]). 
    intros case_ss_S_p dd; clear dd; apply Tfree.
    replace Top_T with (ss[S p|Csp]). 
    apply element_at_belong.
    intros H' H; inversion H.
    intros l' H' H; inversion H.

    simpl; intro H; generalize (H (S p) Csp Top_T casebelong); clear H.
    CaseEq (ss[S p|Csp]). 
    intros case_ss_S_p dd; clear dd; apply Tfree.
    replace Top_T with (ss[S p|Csp]). 
    apply element_at_belong.
    intros H' H; inversion H.
    intros l' H' H; inversion H.

    simpl; intro H; generalize (H (S p) Csp Top_T casebelong); clear H.
    CaseEq (ss[S p|Csp]). 
    intros case_ss_S_p dd; clear dd; apply Tfree.
    replace Top_T with (ss[S p|Csp]). 
    apply element_at_belong.
    intros H' H; inversion H.
    intros l' H' H; inversion H.

    compare p (pred n); intro comp.
    elim (alt_lrsbc comp); intro cc; inversion cc.
    clear alt_lrsbc ar case l Tfree ss lrs_bc.
    destruct n.
    inversion C.
    cut (p < n).
    auto with arith.
    simpl in comp.
    apply lt_S_neq_lt; assumption.

    (* branch *)
    cut (S p < n).
    intro Csp.
    destruct (Get_constr c); simpl.
    destruct c0; simpl.
    cut ((j, Top_T) = (S p, Top_T) \/ (j, Top_T) = (j, Top_T) \/ False).
    intro Hbelong2.

    destruct l; simpl.
    intro H; generalize (H j Cj Top_T Hbelong2); intro H1.
    elim Tfree.
    replace Top_T with (ss[j|Cj]); [apply element_at_belong | symmetry].
    destruct (ss[j|Cj]); try inversion H1; trivial.
    elim (eq_name_dec n cons_ret); intro case_ret; simpl.
    subst n.
    elim (eq_name_dec cons_ret cons_ret); intro d_case; [clear d_case | elim d_case; trivial].
    elim (eq_Sigma_dec (Types (cons_ret :: l)) (ss[j|Cj])); intros case_ss_j H.
    split; trivial.

    CaseEq (ss[S p|_]).
    intros s case_ss_S_p; destruct s.
    apply Tfree; replace Top_T with (ss[S p|Csp]).
    apply element_at_belong.
    apply element_at_unsafe_to_safe; assumption.
    cut ((S p, Types (rev cons_args ++ l)) = (S p, Types (rev cons_args ++ l)) \/ (S p, Types (rev cons_args ++ l)) = (j, Types (cons_ret :: l)) \/ False); [intro Hbelong | left; trivial].
    generalize (H (S p) Csp (Types (rev cons_args ++ l)) Hbelong).
    replace (ss[S p|Csp]) with Bot_T; [clear H; intro H; inversion H | symmetry].
    apply element_at_unsafe_to_safe; assumption.
    elim (eq_list_name_dec (rev cons_args ++ l) l0); trivial.
    intro dd; apply dd; clear dd.
    cut ((S p, Types (rev cons_args ++ l)) = (S p, Types (rev cons_args ++ l)) \/ (S p, Types (rev cons_args ++ l)) = (j, Types (cons_ret :: l)) \/ False); [intro Hbelong | left; trivial].
    generalize (H (S p) Csp (Types (rev cons_args ++ l)) Hbelong).
    replace (ss[S p|Csp]) with (Types l0); [clear H; intro H; inversion H | symmetry].
    trivial.
    apply element_at_unsafe_to_safe; assumption.
    intro Hnone; generalize (element_at_unsafe_none Sigma n ss (S p) Hnone).
    apply lt_not_ge; trivial.

    cut ((j,Types (cons_ret :: l)) = (S p, Types (rev cons_args ++ l)) \/ (j,Types (cons_ret :: l)) = (j,Types (cons_ret :: l)) \/ False); [intro Hbelong | right; left; trivial].
    elim (case_ss_j); symmetry.
    generalize (H j Cj (Types (cons_ret :: l)) Hbelong); CaseEq (ss[j|Cj]).
    intro Htop; elim Tfree; rewrite <- Htop; apply element_at_belong.
    intros Hbot H'; inversion H'.
    intros l1 dd H'; inversion H'; trivial.

    intro H; generalize (H j Cj Top_T Hbelong2); intro H1.
    elim Tfree.
    replace Top_T with (ss[j|Cj]); [apply element_at_belong | destruct (ss[j|Cj]); inversion H1; trivial].
    right; left; trivial.
    cut ((S p, Top_T) = (S p, Top_T) \/ (S p, Top_T) = (j, Top_T) \/ False); [intros Hbelong H | left; trivial].
    generalize (H (S p) Csp Top_T Hbelong); clear H; intro H.
    elim Tfree.
    replace Top_T with (ss[S p|Csp]); [apply element_at_belong | destruct (ss[S p|Csp]); trivial; inversion H].

    compare p (pred n); intro comp.
    elim (alt_lrsbc comp); intro cc; inversion cc.
    clear alt_lrsbc case l Tfree ss lrs_bc.
    destruct n.
    inversion C.
    cut (p < n).
    auto with arith.
    simpl in comp.
    apply lt_S_neq_lt; assumption.



    cut (0<n).
    intros Cn peq; subst p.
    rewrite (element_at_irrel Instruction n bc (pred n) C (lt_pred_n_n n Cn)).
    apply lrs_bc.
    clear case l Tfree ss lrs_bc. 
    destruct n.
    inversion C.
    auto with arith.

    intros q Cq t Hbelong.
    cut (m_list_belong (step' Sigma n (Succs n bc lrs_bc) Step (Step_Succs_same_length lrs_bc) p C (ss[p|C])) (q, t)).
    intro Hb.
    generalize (H q t Hb).
    clear H; intro H.
    rewrite (element_at_irrel Sigma n ss q Cq (m_list_get_witness (step' Sigma n (Succs n bc lrs_bc) Step (Step_Succs_same_length lrs_bc) p C (ss[p|C])) (q, t) Hb)); assumption.
    generalize Hbelong; unfold step'; unfold Succs.
    apply m_list_belong_convert.

  Qed.


  Lemma Wti_and_stable_agree : forall (lrs_bc : last_return_or_stop n bc), 
    wi_and_stable_agree Sigma n (Succs n bc lrs_bc) Step Wti r Top_T (Step_Succs_same_length lrs_bc).

    intro lrs_bc.
    unfold wi_and_stable_agree.
    intros ss p Cp Tfree; split.
    apply Wti_imp_stable; assumption.
    apply stable_imp_Wti; assumption.
  Qed.


    (************************************************************************)
    (*                              Kildall                                 *)
    (************************************************************************)

  Definition Kildall_types (lrs_bc : last_return_or_stop n bc) := 
    (Kildall Sigma n (Succs n bc lrs_bc) Step r f (Step_Succs_same_length lrs_bc) eq_Sigma_dec r_is_semilattice wfr).

  Theorem Kildall_Is_Bytecode_Verifier : forall (lrs_bc : last_return_or_stop n bc),
    Is_bytecode_verifier Sigma n Wti r Top_T (Kildall_types lrs_bc).
  Proof.
    intro lrs_bc.
    unfold Kildall_types.
    apply Kildall_is_bytecode_verifier.
    apply Succs_equiv.
    apply Step_equiv.
    apply monotone_Step.
    unfold is_top_element; apply Top_T_top.
    apply Wti_and_stable_agree; assumption.
  Qed.


End inst_types.

    (*
    Kildall_types
         : forall fcn : function,
           last_return_or_stop (fcn_size fcn) (fcn_body fcn) ->
           vector Sigma (fcn_size fcn) -> vector Sigma (fcn_size fcn)
    *)