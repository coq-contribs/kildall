    (***************************************************************)
    (*   This file is part of the static analyses developement -   *)
    (*   specification of kildall's algorithm, and proof it is a   *)
    (*   bytecode verifier -                                       *)
    (*							           *)
    (*   File : inst_shapes.v		 		           *)
    (*   Authors : S. Coupet-Grimal, W. Delobel 	           *)
    (*   Content : instanciation of kildall's algorithm for        *)
    (*             shape analysis                                  *) 
    (***************************************************************)

Section inst_shapes.

  Add LoadPath "../aux".
  Add LoadPath "../lists".
  Add LoadPath "../kildall".

  Require Export substitutions.
  Require Export kildall_bv.

  Variable fcn : function.
  Notation n := (fcn_size fcn).
  Notation bc := (fcn_bytecode fcn).
  Notation Expression := (tree Name Name).
  Notation Instruction := (instruction n).
  Notation Get_function := (get_function_by_name functions).
  Notation Get_constr := (get_constr_by_name constructors).
  Notation Substitution := (list subst_elem).


  Inductive Sigma_S : Set := 
    |Bot_S : Sigma_S
    |Top_S : Sigma_S
    |Shapes : Substitution -> list Expression -> Sigma_S.


  Definition r_S (a : Sigma_S) (b : Sigma_S) : Prop :=
    match a,b with
      | _, Top_S => True
      | Top_S, _ => False
      | Bot_S, _ => True
      | _, Bot_S => False
      | a, b => a = b
    end.


  Definition sup_S (a : Sigma_S) (b : Sigma_S) : Sigma_S :=
    match a,b with 
      | _, Top_S => Top_S
      | Top_S, _ => Top_S
      | Bot_S, y => y
      | y, Bot_S => y
      | Shapes s e, Shapes s' e' => 
        match eq_Substitution_dec s s' with 
          | left _ => 
      	    match eq_list_Expression_dec e e' with
              | left _ => Shapes s e
              | right _ => Top_S
      	    end
          | right _ => Top_S
        end
    end.


  (************************************************************************)
  (*                  Results on (Sigma_S, r_S, sup_S)                    *)
  (************************************************************************)

  Lemma eq_Sigma_S_dec : forall (t t' : Sigma_S), {t=t'} + {t<>t'}.
  Proof.
    induction t.
    intro t'; destruct t'; [left | right | right]; try (intro h; inversion h).
    trivial.
    intro t'; destruct t'; [right | left | right]; try (intro h; inversion h).
    trivial.
    intro t'; destruct t'; [right | right | idtac]; try (intro h; inversion h).
    elim (eq_Substitution_dec l l1); intro case_s; subst.
    elim (eq_list_Expression_dec l0 l2); intro case_e; subst; [left | right].
    trivial.
    injection.
    apply case_e.
    right; injection; intros; apply case_s; trivial.
  Qed.


  Fact Top_S_top : forall (a : Sigma_S), r_S a Top_S.
  Proof.
    intro a; destruct a; constructor.
  Qed.


  Fact Bot_S_bot : forall (a : Sigma_S), r_S Bot_S a.
  Proof.
    intro a; destruct a; constructor.
  Qed.


  Lemma r_S_is_order : order Sigma_S r_S.
  Proof.
    split.
  (*refl*)
    intro a.
    elim a; constructor.
  (*trans*)
    intros a b c.
    elim a.
    elim b.
    intro H; clear H; elim c; trivial.
    intro H; inversion H.
    inversion H.
    elim c; intro; constructor.
    intros l l' H H'; elim c; constructor.
    elim b; intro H; inversion H.
    trivial.
    intros l h; inversion h.
    intros l h; inversion h.
    intros l l0; destruct b; intro H; inversion H.
    destruct c; intro h; inversion h; trivial.
    trivial.
  (*antisym*)
    intros a b.
    destruct a; destruct b; try trivial; intros H1 H2.
    inversion H2.
    inversion H2.
    inversion H1.
    inversion H1.
    inversion H1.
    inversion H2.
  Qed.

  Lemma sup_S_is_lub : lub Sigma_S r_S sup_S.
  Proof.
    repeat split.
  (* lub1 *)
    intros a b.
    destruct a.
    destruct b; constructor.
    destruct b; constructor.
    destruct b; trivial.
    simpl; trivial.
    simpl; trivial.
    simpl.
    elim (eq_Substitution_dec l l1); intro case1; subst.
    elim (eq_list_Expression_dec l0 l2); intro case2; subst.
    trivial.
    trivial.
    trivial.
  (* lub2 *)
    intros a b; destruct b.
    destruct a; constructor.
    destruct a; simpl; trivial.
    destruct a; simpl; trivial.
    elim (eq_Substitution_dec  l1 l); intro case; subst; trivial.
    elim (eq_list_Expression_dec  l2 l0); intro case; subst; trivial.
  (* lub3 *)
    intros a b c H; elim H; clear H; intros rac rbc.
    destruct c.
    destruct a; destruct b; try inversion rac; try inversion rbc.
    constructor.
    apply Top_S_top.
    destruct a; destruct b; try inversion rac; try inversion rbc; try constructor.
    subst; simpl.
    elim (eq_Substitution_dec  l l); intro case; [clear case | elim case; trivial].
    elim (eq_list_Expression_dec  l0 l0); intro case; [clear case | elim case; trivial].
    constructor.
  Qed.

  Lemma r_S_is_semilattice : semilattice Sigma_S r_S sup_S.
  Proof.
    split.
    apply r_S_is_order.
    apply sup_S_is_lub.
  Qed.

  Lemma AccTop_S : Acc (strict (inv r_S)) Top_S.
  Proof.
    constructor.
    intros y H; elim H; clear H; intros H1 H2.
    destruct y; try inversion H1.
    elim H2; trivial.
  Qed.

  Lemma AccSSE : forall (s : Substitution) (e : list Expression), Acc (strict (inv r_S)) (Shapes s e).
  Proof.
    intros s e; constructor.
    intros y H; elim H; clear H; intros H1 H2.
    destruct y; try inversion H1.
    apply AccTop_S.
    subst; elim H2; trivial.
  Qed.

  Lemma wfr_S : ascending_chain r_S.
  Proof.
    unfold ascending_chain.
    unfold well_founded.
    induction a.
    constructor; intros y H; elim H; clear H; intros H1 H2.
    destruct y.
    elim H2; trivial.
    apply AccTop_S.
    apply AccSSE.
    apply AccTop_S.
    apply AccSSE.
  Qed.


  (************************************************************************)
  (*                       Definition of Step_S                            *)
  (************************************************************************)

  Definition Step_S (p:nat) (C: p <n) (s:Sigma_S) : list Sigma_S := 
    match (bc[p|C]) with 
    (* Return *)
      | i_return => 
      match s with 
        | Bot_S => Bot_S :: nil
        | Top_S => Top_S :: nil
        | Shapes substi l => 
      	  match l with 
      	    | nil => Top_S :: nil
      	    | e::t => (Shapes substi l) :: nil	
      	  end
      end
      |
    (* Stop *)
        i_stop => nil
      |
    (* Load *)
        i_load i => 
        match s with 
          Bot_S => Bot_S :: nil
          |
            Top_S => Top_S :: nil
          | 
            Shapes substi l => 
      	    match (element_at_list (rev_lin l) i) with
	      Some h => (Shapes substi (h::l)) :: nil
	      |
	        _ => Top_S :: nil
	    end
        end
      |
    (* Call *)
        i_call g ar => 	
        match s with 
          Bot_S => Bot_S :: nil
          |
            Top_S => Top_S :: nil
          | 
            Shapes substi l => 
      	    match (split_k_elements ar l) with 
      	      Some (lk, lr) => 
 	      (Shapes substi ((Node (symbol g) (rev_lin lk))::lr)) :: nil
       	      |
      	        _ => Top_S :: nil
      	    end
        end
      |
    (* Build *)
        i_build c ar => 
        match s with 
          Bot_S => Bot_S :: nil
          |
            Top_S => Top_S :: nil
          | 
            Shapes substi l => 
      	    match (split_k_elements ar l) with 
      	      Some (lk, lr) => 
       	      (Shapes substi ((Node (symbol c) (rev_lin lk))::lr)) :: nil
      	      |
	        _ => Top_S :: nil
      	    end
        end
      |
    (* Branch *)
        i_branch c _ _ => 
        match s with 
          Bot_S => Bot_S :: (Bot_S :: nil)
          |
            Top_S => Top_S :: (Top_S :: nil)
          | 
            Shapes substi l =>
            match l with
	      (Node (symbol d) forst)::l' => 
	      match (eq_name_dec c d) with 
	        left _ => (Shapes substi (push_list forst l')) :: (Bot_S :: nil) 
	        |
	          right _ => Bot_S :: ((Shapes substi l) :: nil)
              end
	      |
	        (Node (x i j) nil)::l' => 
      	        match (Get_constr c) with
      	          Some const => 
	          let vars := (fresh (S p) (S (length l')) (length (cons_args const))) in
	            let sub := (mksubst i j (Node (symbol c) vars)) in
		      (Shapes (sub :: substi) (push_list vars 
                        (map (apply_elem_tree sub) l')))::((Shapes substi l) :: nil)
	          |
	            None => Top_S :: (Top_S :: nil)
                end
	      |
	        _ => Top_S :: (Top_S :: nil)
            end
        end
    end.


  Lemma Step_S_equiv : forall (p:nat) (C C': p <n) (s:Sigma_S), 
    (Step_S p C s) = (Step_S p C' s).
  Proof.
    intros; unfold Step_S.
    rewrite (element_at_irrel Instruction n bc p C' C).
    trivial.
  Qed.


  Lemma Step_S_Succs_aux_same_length : forall (p:nat) (C: p <n) (s:Sigma_S), 
    nb_length (Succs_aux n bc p C) = length (Step_S p C s).
  Proof.
    intros p C s.
    unfold Succs_aux ; unfold Step_S.
    elim (bc[p|C]); try elim s; simpl; trivial.
  (* return *)
    intros ls le; destruct le; simpl; trivial.
  (* load *)
    intros ls le j.
    destruct (element_at_list (rev_lin le) j); simpl; trivial.
  (* call *)
    intros ls le g ar.
    elim (split_k_elements ar le);  simpl; try trivial.
    intro a; destruct a; simpl; trivial.
  (* build *)
    intros ls le  c ar.
    elim (split_k_elements ar le); simpl; try trivial.
    intro a; destruct a; simpl; trivial.
  (* branch *)
    intros ls le c.
    destruct le; simpl; try trivial.
    intros i; destruct t; simpl; trivial.
    destruct n; simpl; trivial.
    destruct l; simpl; trivial.
    destruct (Get_constr c); simpl; trivial.
    elim (eq_name_dec c n); simpl; trivial.
  Defined.


  Lemma Step_S_Succs_same_length : forall (lr : last_return_or_stop n bc) (p:nat) (C: p <n) (s:Sigma_S), 
    nb_length (Succs n bc lr p C) = length (Step_S p C s).
  Proof.
    intros lr p C s.
    replace (nb_length (Succs  n bc lr p C)) with (nb_length (Succs_aux n bc p C)).
    apply Step_S_Succs_aux_same_length; assumption.
    unfold Succs.
    apply nb_list_convert_length with (l:=Succs_aux  n bc p C) (H:=Succs_better_bound n bc p C lr).
  Defined.


  Lemma refl_dep_r : forall (l : list Sigma_S), 
    list_pointwise Sigma_S r_S l l.
  Proof.
    induction l; try constructor.
    elim a; constructor.
    apply IHl.
  Qed.


  Lemma dep_r_Bot_1 : forall (l : list Sigma_S), 
    1 = length l -> list_pointwise Sigma_S r_S (Bot_S :: nil) l.
  Proof.
    induction l; simpl; intro H. 
    inversion H.
    constructor.
    apply Bot_S_bot.
    destruct l; try constructor; simpl in H.
    inversion H.
  Qed.

  Lemma dep_r_Top_1 : forall (l : list Sigma_S), 
    1 = length l -> list_pointwise Sigma_S r_S l (Top_S :: nil).
  Proof.
    induction l; simpl; intro H. 
    inversion H.
    constructor.
    apply Top_S_top.
    destruct l; try constructor; simpl in H.
    inversion H.
  Qed.

  Lemma dep_r_Bot_2 : forall (l : list Sigma_S), 
    2 = length l -> list_pointwise Sigma_S r_S (Bot_S :: (Bot_S :: nil)) l.
  Proof.
    induction l; simpl; intro H. 
    inversion H.
    destruct l; simpl.
    inversion H.
    constructor.
    apply Bot_S_bot.
    constructor.
    apply Bot_S_bot.
    destruct l; try constructor; simpl in H.
    inversion H.
  Qed.

  Lemma dep_r_Top_2 : forall (l : list Sigma_S), 
    2 = length l -> list_pointwise Sigma_S r_S l (Top_S :: (Top_S :: nil)).
  Proof.
    induction l; simpl; intro H. 
    inversion H.
    destruct l; simpl.
    inversion H.
    constructor.
    apply Top_S_top.
    constructor.
    apply Top_S_top.
    destruct l; try constructor; simpl in H.
    inversion H.
  Qed.


  Lemma monotone_Step_S : monotonestep Sigma_S n Step_S r_S.
  Proof.
    intros p C s t rst.
    destruct s; destruct t; try inversion rst.
    apply refl_dep_r.
    unfold Step_S; CaseEq (bc[p|C]); simpl; auto; try constructor; auto; try constructor.
    assumption.
    constructor.
    unfold Step_S; CaseEq (bc[p|C]); simpl; auto; try constructor; auto; try constructor.
  (* return *)
    intro; apply dep_r_Bot_1. 
    destruct l0; simpl; trivial.
  (* load *)
    intros j case; apply dep_r_Bot_1.
    CaseEq (element_at_list (rev_lin l0) j); simpl; trivial.
  (* call *)
    intros g ar case; apply dep_r_Bot_1.
    elim (split_k_elements ar l0); simpl; try trivial.
    intro a; destruct a; simpl; trivial.
  (* build *)
    intros c ar case; apply dep_r_Bot_1.
    elim (split_k_elements ar l0); simpl; trivial.
    intro a; destruct a; simpl; trivial.
  (* branch *)
    intros c i Ci case; apply dep_r_Bot_2.
    destruct l0; simpl; trivial.
    destruct t; simpl; trivial.
    destruct n; simpl; trivial.
    destruct l1; simpl; trivial.
    destruct (Get_constr c); simpl; try trivial.
    elim (eq_name_dec c n); simpl; trivial.

    unfold Step_S; CaseEq (bc[p|C]); simpl; auto; try constructor; auto; try constructor.
    constructor.
    constructor.
    unfold Step_S; CaseEq (bc[p|C]); simpl; auto; try constructor; auto; try constructor.
    destruct l0; trivial.
    intro; apply dep_r_Top_1; simpl; trivial.
    intro; apply dep_r_Top_1; simpl; trivial.
    intros; apply dep_r_Top_1; simpl; trivial.
    destruct (element_at_list (rev_lin l0) n); simpl; trivial.
    intros; apply dep_r_Top_1.
    destruct (split_k_elements n0 l0); simpl; trivial.
    destruct p0; simpl; trivial.
    intros.
    destruct (split_k_elements n0 l0); simpl; trivial.
    destruct p0; simpl; trivial.
    constructor; constructor.
    constructor; constructor.
    intros; destruct l0.
    apply refl_dep_r.
    destruct t;  simpl; trivial.
    apply refl_dep_r.
    destruct n; simpl; trivial.
    destruct l2; simpl; trivial.
    destruct (Get_constr c); trivial.
    constructor.
    constructor.
    constructor; constructor.
    apply refl_dep_r.
    apply refl_dep_r.
    elim (eq_name_dec c n); intro; constructor.
    constructor.
    constructor; constructor.
    constructor.
    constructor; constructor.
    apply refl_dep_r.
  Qed.


  (************************************************************************)
  (*                         Definition of Wshi                           *)
  (************************************************************************)

  Definition Wshi (ss : vector Sigma_S n) (p : nat) (C : p < n) : Prop :=
    match (ss[p|C]) with
      | Top_S => False
      | Bot_S => True
      | Shapes ls lex => 	
        match bc[p|C] with 
          | i_return => lex <> nil (* ADDED *)
          | i_stop => True
          | i_load j => 
      	    match ss[S p|_] with 
	      | Some (Shapes ls' lex') => 
	        match element_at_list (rev_lin lex) j with
	          | Some ej => ls' = ls /\ lex' = ej :: lex
	          |  _ => False
	        end
	      | _ => False
	    end
          | i_call g ar => 
            match split_k_elements ar lex with
	      | Some (lexk, lexr) => 
	        match ss[S p|_] with 
	          | Some (Shapes ls' lex') => 
	            ls' = ls /\ lex' = (Node (symbol g) (rev_lin lexk)) :: lexr
	          | _ => False
	        end
	      | _ => False
	    end 
          | i_build c ar => 
            match split_k_elements ar lex with
	      | Some (lexk, lexr) => 
	        match ss[S p|_] with 
	          | Some (Shapes ls' lex') => 
	            ls' = ls /\ lex' = (Node (symbol c) (rev_lin lexk)) :: lexr
	          | _ => False
	        end
	      | _ => False
	    end 
          | i_branch c j Cj =>
            match lex with 
	      | pe :: lexr => 
	        match pe with 
	          | Node (x i k) nil => 
	            match Get_constr c with
		      | Some const => 
		        (match ss[j|Cj] with 
		           Shapes lsj lexj => 
       	       	           lsj = ls /\ lexj = lex
      	       	           | _ => False
		         end
		        /\
	                match ss[S p|_] with 
		          | Some (Shapes ls' lex') => 
      	       	            let vars := (fresh (S p) (S (length lexr)) (length (cons_args const))) in
	                      let sub := (mksubst i k (Node (symbol c) vars)) in
			        lex' = (push_list vars (map (apply_elem_tree sub) lexr))
			        /\
			        ls' = sub :: ls
		          | _ => False
		        end)
		      | _ => False
		    end
	          | Node (symbol d) forst =>
	            match eq_name_dec c d with 
		      | left _ => 
		        match ss[S p|_] with
		          | Some (Shapes ls' lex') => 
		            ls' = ls /\ (lex' = push_list forst lexr)
		          | _ => False
		        end
		      | right _ => 	
    		        match ss[j|Cj] with 
		          | Shapes lsj lexj => 
       	       	            lsj = ls /\ lexj = lex
      	       	          | _ => False
			end
		    end
	          | _ => False
	        end
	      | _ => False
	    end
        end
    end.


  Lemma Wshi_imp_stable : forall (lrs_bc : last_return_or_stop n bc) (ss : vector Sigma_S n) 
    (p : nat) (C : p < n) (Tfree : ~ Top_S INv ss), 
    Wshi ss p C -> stable Sigma_S n (Succs n bc lrs_bc) Step_S r_S (Step_S_Succs_same_length lrs_bc) ss p C.
  Proof.
    unfold stable.
    intros lrs_bc ss p C Tfree Wsh q t H .
    cut (q <n); [intro Cq | apply (m_list_get_witness (step' Sigma_S n (Succs  n bc lrs_bc) Step_S
      (Step_S_Succs_same_length lrs_bc) p C (ss[p|C])) (q, t) H)].
    rewrite (element_at_irrel Sigma_S n ss q (m_list_get_witness (step' Sigma_S n (Succs n bc lrs_bc) Step_S
      (Step_S_Succs_same_length lrs_bc) p C (ss[p|C])) (q, t) H) Cq).
    cut (m_list_belong (combine (Succs_aux n bc p C) (Step_S p C (ss[p|C])) (Step_S_Succs_aux_same_length p C (ss[p|C]))) (q, t));
      [clear H | generalize H; unfold step'; unfold Succs; apply m_list_convert_belong].
    clear lrs_bc.
    generalize Wsh; clear Wsh; unfold Wshi; unfold Step_S; unfold Succs_aux. 
    CaseEq (ss[p|C]).
  (* Bot_S *)
    intros case d; clear d; unfold Step_S_Succs_aux_same_length; destruct (bc[p|C]); simpl; intro H.
    elim H; clear H; intro H; inversion H. 
    apply Bot_S_bot.
    inversion H.
    elim H; clear H; intro H; inversion H.
    apply Bot_S_bot.
    elim H; clear H; intro H; inversion H.
    apply Bot_S_bot.
    elim H; clear H; intro H; inversion H.
    apply Bot_S_bot.
    elim H; clear H; intro H; inversion H.
    apply Bot_S_bot.
    inversion H0; apply Bot_S_bot.
    inversion H0.
  (* Top_S *)
    intros case F; inversion F.
  (* Shapes ls lex *)
    intros ls lex case_ss.
    unfold Step_S_Succs_aux_same_length; destruct (bc[p|C]); simpl.
    Focus 1.
  (* return *)
    intro Hwsh; destruct lex.
    elim Hwsh; trivial.
    intro H; elim H; clear H; intro H.
    inversion H.
    subst.
    rewrite (element_at_irrel Sigma_S n ss p Cq C).
    rewrite case_ss; constructor.
    inversion H.
    Focus 1.
  (* stop *)
    intros dd F; inversion F.
    Focus 1.
  (* load *)
    CaseEq (ss[S p|_]).
    intros s case_ss_s; destruct s.
    intro F; inversion F.
    intro F; inversion F.
    destruct (element_at_list (rev_lin lex) n).
    intro H; elim H; clear H; intros h1 h2; subst.
    intro H; elim H; clear H; intro H.
    inversion H; subst.
    rewrite (element_at_unsafe_to_safe Sigma_S _ ss (S p) Cq (Shapes ls (t0 :: lex))); trivial.
    constructor.
    inversion H.
    intro F; inversion F.
    intros case F; inversion F.
    Focus 1.
  (* call *)
    destruct (split_k_elements n0 lex).
    destruct p0.
    CaseEq (ss[S p|_]).
    intros s case_ss_s; destruct s; [intro F; inversion F | intro F; inversion F | intro H].
    elim H; clear H; intros h1 h2; subst.
    intro H; elim H; clear H; intro H.
    inversion H; subst.
    rewrite (element_at_unsafe_to_safe Sigma_S _ ss (S p) Cq (Shapes ls (Node (symbol n) (rev_lin l) :: l0))); trivial.
    constructor.
    inversion H.
    intros dd F; inversion F.
    intro F; inversion F.
    Focus 1. 
  (* build *)
    destruct (split_k_elements n0 lex).
    destruct p0.
    CaseEq (ss[S p|_]).
    intros s case_ss_s; destruct s; [intro F; inversion F | intro F; inversion F | intro H].
    elim H; clear H; intros h1 h2; subst.
    intro H; elim H; clear H; intro H.
    inversion H; subst.
    rewrite (element_at_unsafe_to_safe Sigma_S _ ss (S p) Cq (Shapes ls (Node (symbol n) (rev_lin l) :: l0))); trivial.
    constructor.
    inversion H.
    intros dd F; inversion F.
    intro F; inversion F.
    Focus 1.
  (* branch *)
    destruct lex as [| pe lexpr].
    intro F; inversion F.
    destruct pe.
    intro F; inversion F.
    destruct n.
    destruct l0.
    destruct (Get_constr c).
    CaseEq (ss[i|l]).
    intros case_ss_i H; elim H; clear H; intro H; inversion H.
    intros case_ss_i H; elim H; clear H; intro H; inversion H.
    intros l0 l1 case_ss_i H; elim H; clear H; intro H; elim H; clear H; intros h1 h2; subst.
    CaseEq (ss[S p|_]).
    intros s case_ss_s; destruct s; [intro F; inversion F | intro F; inversion F | idtac].
    intro H; elim H; clear H; intros h1 h2; subst.
    intro H; elim H; clear H; intro H.
    inversion H; subst.
    rewrite (element_at_unsafe_to_safe Sigma_S _ ss (S p) Cq _ case_ss_s); trivial.
    constructor.
    elim H; clear H; intro H.
    inversion H; subst.
    rewrite (element_at_irrel Sigma_S _ ss i Cq l); rewrite case_ss_i.
    constructor.
    inversion H.
    intros case F; inversion F.
    intro F; inversion F.
    intro F; inversion F.
    elim (eq_name_dec c n); intro case_eq.
    CaseEq (ss[S p|_]).
    intros s case_ss_s; destruct s.
    intro F; inversion F.
    intro F; inversion F.
    intro H; elim H; clear H; intros h1 h2; subst.
    intro H; elim H; clear H; intro H.
    inversion H; subst.
    rewrite (element_at_unsafe_to_safe Sigma_S _ ss (S p) Cq _ case_ss_s); trivial.
    constructor.
    elim H; clear H; intro H.
    inversion H; subst.
    apply Bot_S_bot.
    inversion H.
    intros case F; inversion F.
    CaseEq (ss[i|l]).
    intros case F; inversion F.
    intros case F; inversion F.
    intros l1 l2 case_ss_i H; elim H; intros h1 h2; subst.
    clear H; intro H; elim H; clear H; intro H.
    inversion H; subst.
    apply Bot_S_bot.
    elim H; clear H; intro H.
    inversion H; subst.
    rewrite (element_at_irrel Sigma_S _ ss i Cq l); rewrite case_ss_i.
    constructor.
    inversion H.
  Qed.


  Lemma stable_imp_Wshi : forall (lrs_bc : last_return_or_stop n bc) (ss : vector Sigma_S n) (p : nat) (C : p < n) (Tfree : ~ Top_S INv ss), 
    stable Sigma_S n (Succs n bc lrs_bc) Step_S r_S (Step_S_Succs_same_length lrs_bc) ss p C -> Wshi ss p C.
  Proof.
    unfold stable.
    intros lrs_bc ss  p C Tfree H.
    cut (forall (q : nat) (Cq : q < n) (t : Sigma_S)
      (H : m_list_belong (combine (Succs_aux  n bc p C) (Step_S p C (ss[p|C])) 
      	(Step_S_Succs_aux_same_length p C (ss[p|C]))) (q,t)), 
      r_S t (ss[q|Cq])).
    clear H.
    unfold Wshi; unfold Step_S; unfold Succs_aux. 
    CaseEq (ss[p|C]).
  (* Bot_S *)
    trivial.
  (* Top_S *)
    intro case_ss; elim Tfree; rewrite <- case_ss; apply element_at_belong.
  (* Shapes ls lex *)
    intros ls lex case_ss.
    cut ((p = pred n) -> (bc[p|C] = i_return n \/ bc[p|C] = i_stop n)).
    intro alt_lrsbc.
    unfold Step_S_Succs_aux_same_length; destruct (bc[p|C]) as [ | | j| g ar |c ar | c j Cj]; simpl.
    Focus 1.
  (* return *)
    destruct lex; simpl.
    cut ((p,Top_S) = (p,Top_S) \/ False); [intro h | left; trivial].
    intro H; generalize (H p C Top_S h); clear H; intro H.
    rewrite case_ss in H; inversion H.
    intros H F; inversion F.
    Focus 1.
  (* stop *)
    trivial.
    Focus 1.
  (* load *)
    destruct (element_at_list (rev_lin lex) j); simpl.
    cut ((S p, Shapes ls (t :: lex)) = (S p, Shapes ls (t :: lex)) \/ False); [intros h H | left; trivial].
    cut (S p < n); [intro Cs | idtac].
    generalize (H (S p) Cs (Shapes ls (t :: lex)) h); clear H; intro H.
    CaseEq (ss[S p|_]).
    intro s; destruct s.
    intro case_ss_s.
    rewrite (element_at_unsafe_to_safe Sigma_S n ss (S p) Cs Bot_S case_ss_s) in H.
    inversion H.
    intro case_ss_s.
    cut (ss[S p|Cs] = Top_S); [intro case_ss_s' | apply (element_at_unsafe_to_safe Sigma_S n ss (S p) Cs Top_S case_ss_s)].
    elim Tfree; rewrite <- case_ss_s'; apply element_at_belong.
    intros case_ss_s.
    cut (ss[S p|Cs] = Shapes l l0); [intro case_ss_s' | apply (element_at_unsafe_to_safe Sigma_S n ss (S p) Cs _ case_ss_s)].
    rewrite case_ss_s' in H; inversion H.
    split; trivial.
    intro F; generalize Cs.
    apply le_not_lt.
    apply (element_at_unsafe_none Sigma_S n ss (S p) F).

    compare p (pred n); intro comp.
    elim (alt_lrsbc comp); intro cc; inversion cc.
    clear h H alt_lrsbc j case_ss ls lex Tfree ss lrs_bc.
    destruct n.
    inversion C.
    cut (p < n).
    auto with arith.
    simpl in comp.
    apply lt_S_neq_lt; assumption.

    cut (S p < n); [intro Cs | idtac].
    cut ((S p, Top_S) = (S p, Top_S) \/ False); [intro h | left; trivial]. 
    intro H; generalize (H (S p) Cs Top_S h); clear H; intro H.
    CaseEq (ss[S p|_]).
    intro s; destruct s.
    intro case_ss_s.
    rewrite (element_at_unsafe_to_safe Sigma_S n ss (S p) Cs Bot_S case_ss_s) in H.
    inversion H.
    intro case_ss_s.
    cut (ss[S p|Cs] = Top_S); [intro case_ss_s' | apply (element_at_unsafe_to_safe Sigma_S n ss (S p) Cs Top_S case_ss_s)].
    elim Tfree; rewrite <- case_ss_s'; apply element_at_belong.
    intros case_ss_s.
    cut (ss[S p|Cs] = Shapes l l0); [intro case_ss_s' | apply (element_at_unsafe_to_safe Sigma_S n ss (S p) Cs _ case_ss_s)].
    rewrite case_ss_s' in H; inversion H.
    intro F; generalize Cs.
    apply le_not_lt.
    apply (element_at_unsafe_none Sigma_S n ss (S p) F).

    compare p (pred n); intro comp.
    elim (alt_lrsbc comp); intro cc; inversion cc.
    clear alt_lrsbc Tfree case_ss ss lrs_bc.
    destruct n.
    inversion C.
    cut (p < n).
    auto with arith.
    simpl in comp.
    apply lt_S_neq_lt; assumption.
    Focus 1.
  (* call *)
    cut (S p < n); [intro Cs | idtac].
    destruct (split_k_elements ar lex).
    destruct p0; simpl.
    cut ((S p, Shapes ls ((Node (symbol g) (rev_lin l)) :: l0)) = (S p, Shapes ls ((Node (symbol g) (rev_lin l)) :: l0)) \/  False); [idtac | left; trivial].
    intros h H; generalize (H (S p) Cs _ h); clear H; intro H.
    CaseEq (ss[S p|_]).
    intros s case_ss'; destruct s.
    rewrite (element_at_unsafe_to_safe Sigma_S n ss (S p) Cs Bot_S case_ss') in H.
    inversion H.
    cut (ss[S p|Cs] = Top_S); [intro case_ss_s' | apply (element_at_unsafe_to_safe Sigma_S n ss (S p) Cs Top_S case_ss')].
    elim Tfree; rewrite <- case_ss_s'; apply element_at_belong.
    cut (ss[S p|Cs] = Shapes l1 l2); [intro case_ss_s' | apply (element_at_unsafe_to_safe Sigma_S n ss (S p) Cs _ case_ss')].
    rewrite case_ss_s' in H; inversion H.
    split; trivial.
    intro F; generalize Cs.
    apply le_not_lt.
    apply (element_at_unsafe_none Sigma_S n ss (S p) F).
    simpl.
    cut ((S p,Top_S) = (S p, Top_S) \/ False); [intro h | left; trivial].
    intro H; generalize (H (S p) Cs _ h); clear H.
    CaseEq (ss[S p|Cs]).
    intros cas H; inversion H.
    intros cas H; elim Tfree; rewrite <- cas; apply element_at_belong.
    intros l0 l1 cas H; inversion H.

    compare p (pred n); intro comp.
    elim (alt_lrsbc comp); intro cc; inversion cc.
    clear alt_lrsbc Tfree case_ss ss lrs_bc.
    destruct n.
    inversion C.
    cut (p < n).
    auto with arith.
    simpl in comp.
    apply lt_S_neq_lt; assumption.
    Focus 1.
  (* build *)
    cut (S p < n); [intro Cs | idtac].
    destruct (split_k_elements ar lex).
    destruct p0; simpl.
    cut ((S p, Shapes ls (Node (symbol c) (rev_lin l) :: l0)) = (S p, Shapes ls (Node (symbol c) (rev_lin l) :: l0)) \/  False); [idtac | left; trivial].
    intros h H; generalize (H (S p) Cs _ h); clear H; intro H.
    CaseEq (ss[S p|_]).
    intros s case_ss'; destruct s.
    rewrite (element_at_unsafe_to_safe Sigma_S n ss (S p) Cs Bot_S case_ss') in H.
    inversion H.
    cut (ss[S p|Cs] = Top_S); [intro case_ss_s' | apply (element_at_unsafe_to_safe Sigma_S n ss (S p) Cs Top_S case_ss')].
    elim Tfree; rewrite <- case_ss_s'; apply element_at_belong.
    cut (ss[S p|Cs] = Shapes l1 l2); [intro case_ss_s' | apply (element_at_unsafe_to_safe Sigma_S n ss (S p) Cs _ case_ss')].
    rewrite case_ss_s' in H; inversion H.
    split; trivial.
    intro F; generalize Cs.
    apply le_not_lt.
    apply (element_at_unsafe_none Sigma_S n ss (S p) F).
    simpl.
    cut ((S p,Top_S) = (S p, Top_S) \/ False); [intro h | left; trivial].
    intro H; generalize (H (S p) Cs _ h); clear H.
    CaseEq (ss[S p|Cs]).
    intros cas H; inversion H.
    intros cas H; elim Tfree; rewrite <- cas; apply element_at_belong.
    intros l0 l1 cas H; inversion H.

    compare p (pred n); intro comp.
    elim (alt_lrsbc comp); intro cc; inversion cc.
    clear alt_lrsbc Tfree case_ss ss lrs_bc.
    destruct n.
    inversion C.
    cut (p < n).
    auto with arith.
    simpl in comp.
    apply lt_S_neq_lt; assumption.
    Focus 1.

  (* branch *)
    cut (S p < n).
    intro Cs.
    destruct lex as [| pe lexpr].
    (* case lex empty : *)
    intro H.
    cut (r_S Top_S (ss[j|Cj])).
    CaseEq (ss[j|Cj]).
    (* case ss[j] = bot : *)
    intros cas Hr; inversion Hr.
    (* case ss[j] = top : *)
    intro cas; elim Tfree; rewrite <- cas; apply element_at_belong.
    (* case ss[j] = Shapes l l0 : *)
    intros l0 l1 cas Hr; inversion Hr.
    apply (H j Cj Top_S).
    right; left; trivial.
    (* case lex = pe :: lexpr : *)
    destruct pe.
      (* case pe Leaf : *)
    intro H; generalize (H (S p) Cs Top_S); clear H.
    CaseEq (ss[S p|Cs]); simpl.
    intros dd H; apply H; left; trivial.
    intros Htop H; apply Tfree; rewrite <- Htop; apply element_at_belong.
    intros l l' Hl H; apply H; left; trivial.
      (* case pe = Node n l : *)
    destruct n.
    (* case n variable : *)
    destruct (Get_constr c).
    destruct l.
    (* case l empty : *)
    CaseEq (ss[j|Cj]).
    intros case_ss_i H.
    simpl in H.
    cut (r_S (Shapes ls (Node (x n n0) nil :: lexpr)) (ss[j|Cj])).
    rewrite case_ss_i; intro Hr; inversion Hr.
    apply (H j Cj (Shapes ls (Node (x n n0) nil :: lexpr))).
    right; left; trivial.
    intro case_ss_i; elim Tfree; rewrite <- case_ss_i; apply element_at_belong.
    intros l0 l1 case_ss_i.
    CaseEq (ss[S p|_]).
    intros s case_ss_s; destruct s.
    intro H.
    cut (r_S (Shapes (mksubst n n0 (Node (symbol c) (fresh (S p) (S (length lexpr)) (length (cons_args c0)))) :: ls) (push_list (fresh (S p) (S (length lexpr)) (length (cons_args c0)))  (map (apply_elem_tree (mksubst n n0 (Node (symbol c) (fresh (S p) (S (length lexpr)) (length (cons_args c0)))))) lexpr))) (ss[S p|Cs])).
    clear H.
    rewrite (element_at_unsafe_to_safe Sigma_S _ ss (S p) Cs _ case_ss_s).
    intro Hr; inversion Hr.
    apply (H (S p) Cs).
    left; trivial.
    elim Tfree.
    replace Top_S with (ss[S p|Cs]).
    apply element_at_belong.
    generalize case_ss_s; apply element_at_unsafe_to_safe.
    intro H; cut (r_S (Shapes ls (Node (x n n0) nil :: lexpr)) (ss[j|Cj])).
    rewrite case_ss_i; intro Hr; inversion Hr; subst.
    split.
    split; trivial.
    clear Hr; cut (r_S (Shapes (mksubst n n0 (Node (symbol c) (fresh (S p) (S (length lexpr)) (length (cons_args c0)))) :: l0) (push_list (fresh (S p) (S (length lexpr)) (length (cons_args c0))) (map (apply_elem_tree (mksubst n n0 (Node (symbol c) (fresh (S p) (S (length lexpr)) (length (cons_args c0)))))) lexpr))) (ss[S p|Cs])).
    replace (ss[S p|Cs]) with (Shapes l l2).
    intro Hr; inversion Hr; subst.
    split; trivial.
    symmetry; generalize case_ss_s; apply element_at_unsafe_to_safe.
    apply H; left; trivial.
    apply H; right; left; trivial.
    intro F; cut (False); [intro F'; inversion F' | generalize Cs].
    apply le_not_lt.
    apply (element_at_unsafe_none Sigma_S _ ss (S p) F).
    (* case l not empty : *)
    CaseEq (ss[j|Cj]).
    intros case_ss_i H; cut (r_S Top_S Bot_S).
    intro F; inversion F.
    rewrite <- case_ss_i; apply (H j Cj Top_S).
    right; left; trivial.
    intro case_ss_i; elim Tfree; rewrite <- case_ss_i; apply element_at_belong.
    intros l0 l1 case_ss_i H; cut (r_S Top_S (ss[j|Cj])).
    rewrite case_ss_i; intro Hr; inversion Hr.
    apply H; right; left; trivial.
    
    (* case constructor does not exists : *)
    destruct l.
    CaseEq (ss[j|Cj]).
    intros case_ss_i H; cut (r_S Top_S Bot_S).
    intro F; inversion F.
    rewrite <- case_ss_i; apply (H j Cj Top_S).
    right; left; trivial.
    intro case_ss_i; elim Tfree; rewrite <- case_ss_i; apply element_at_belong.
    intros l0 l1 case_ss_i H; cut (r_S Top_S (ss[j|Cj])).
    rewrite case_ss_i; intro Hr; inversion Hr.
    apply H; right; left; trivial.

    CaseEq (ss[j|Cj]).
    intros case_ss_i H; cut (r_S Top_S Bot_S).
    intro F; inversion F.
    rewrite <- case_ss_i; apply (H j Cj Top_S).
    right; left; trivial.
    intro case_ss_i; elim Tfree; rewrite <- case_ss_i; apply element_at_belong.
    intros l0 l1 case_ss_i H; cut (r_S Top_S (ss[j|Cj])).
    rewrite case_ss_i; intro Hr; inversion Hr.
    apply H; right; left; trivial.
    (* case n name : *)
    
    elim (eq_name_dec c n); intro case_c_n; simpl.    
    (* case c and n are the same name : *)
    CaseEq (ss[S p|_]).
    intros s case_s H; destruct s. 
    assert (H' : r_S (Shapes ls (push_list l lexpr)) (ss[S p|Cs])).
    apply H.
    left; trivial.
    generalize H'; simpl.
    replace (ss[S p|Cs]) with Bot_S.
    trivial.
    symmetry; generalize case_s; apply element_at_unsafe_to_safe.
    assert (H' : ss[S p|Cs] = Top_S).
    generalize case_s; apply element_at_unsafe_to_safe.
    apply Tfree; rewrite <- H'; apply element_at_belong.
    assert (H' : r_S (Shapes ls (push_list l lexpr)) (ss[S p|Cs])).
    apply H.
    left; trivial.
    generalize H'; simpl.
    replace (ss[S p|Cs]) with (Shapes l0 l1).
    intro H''; inversion H''; split; trivial.
    symmetry; generalize case_s; apply element_at_unsafe_to_safe.
    
      (* case element_at_unsafe S p = None : contradiction with S p < n *)
    intro F; generalize (element_at_unsafe_none _ _ _ _ F).
    intros H dd.
    generalize Cs H; apply lt_not_ge. 
    
    intro H; cut (r_S (Shapes ls (Node (symbol n) l :: lexpr)) (ss[j|Cj])).
    CaseEq (ss[j|Cj]).
    intros case_ss_i Hr; inversion Hr.
    intros case_ss_i; elim Tfree; rewrite <- case_ss_i; apply element_at_belong.
    intros l0 l1 case_ss_i Hr; inversion Hr; subst; split; trivial.
    apply H; right; left; trivial.

    compare p (pred n); intro comp.
    elim (alt_lrsbc comp); intro cc; inversion cc.
    clear alt_lrsbc lrs_bc Tfree case_ss ss. 
    destruct n.
    inversion C.
    cut (p < n).
    auto with arith.
    simpl in comp.
    apply lt_S_neq_lt; assumption.
    intro; subst p.
    unfold last_return_or_stop in lrs_bc.
    cut (0<n).
    intro C'.
    rewrite (element_at_irrel Instruction n bc (pred n) C (lt_pred_n_n n C')).
    apply lrs_bc.
    clear lrs_bc Tfree case_ss ss. 
    destruct n.
    inversion C.
    auto with arith.

    intros q Cq t Hbelong.
    cut (m_list_belong (step' Sigma_S n (Succs n bc lrs_bc) Step_S (Step_S_Succs_same_length lrs_bc) p C (ss[p|C])) (q, t)).
    intro Hb.
    generalize (H q t Hb).
    clear H; intro H.
    rewrite (element_at_irrel Sigma_S n ss q Cq (m_list_get_witness (step' Sigma_S n (Succs n bc lrs_bc) Step_S (Step_S_Succs_same_length lrs_bc) p C (ss[p|C])) (q, t) Hb)); assumption.
    generalize Hbelong; unfold step'; unfold Succs.
    apply m_list_belong_convert.
  Qed.


  Lemma Wshi_and_stable_agree : forall (lrs_bc : last_return_or_stop n bc), 
    wi_and_stable_agree Sigma_S n (Succs n bc lrs_bc) Step_S Wshi r_S Top_S (Step_S_Succs_same_length lrs_bc).
  Proof.
    intro lrs_bc.
    unfold wi_and_stable_agree.
    intros ss p Cp Tfree; split.
    apply Wshi_imp_stable; assumption.
    apply stable_imp_Wshi; assumption.
  Qed.


  Definition Kildall_shapes (lrs_bc : last_return_or_stop n bc) := 
    (Kildall Sigma_S n (Succs n bc lrs_bc) Step_S r_S sup_S (Step_S_Succs_same_length lrs_bc) eq_Sigma_S_dec r_S_is_semilattice wfr_S).


  Theorem Kildall_Shape_Is_Bytecode_Verifier : forall (lrs_bc : last_return_or_stop n bc),
    Is_bytecode_verifier Sigma_S n Wshi r_S Top_S (Kildall_shapes lrs_bc).
  Proof.
    intro lrs_bc.
    unfold Kildall_shapes.
    apply Kildall_is_bytecode_verifier.
    apply Succs_equiv.
    apply Step_S_equiv.
    apply monotone_Step_S.
    unfold is_top_element; apply Top_S_top.
    apply Wshi_and_stable_agree; assumption.
  Qed.


End inst_shapes. 
