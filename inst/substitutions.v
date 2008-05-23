
  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : substitutions.v			 	         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : definition and properties of substitutions      *)
  (***************************************************************)

Section substitutions.


  Require Export machine.

  (* Name = name U {variables x_{i,j} / i,j : nat}.*)
  Inductive Name : Set :=
    | x : nat -> nat -> Name
    | symbol : name -> Name.

  Notation Get_function := (get_function_by_name functions).

  (* an expression is a tree whose nodes and leaves are marked with elements of name. 
   note that in this definition, nothing prevents a node from being marked with a variable 
  - functions dealing with expressions will filter these cases out 
   *)
  Notation Expression := (tree Name Name).

  (* elementary substitution : xi and xj represent variable x_{xi,xj}, 
   the last field is the expression to be substituted to the variable; 
   substituted variable may appear in that expression 
   *)
  Record subst_elem : Set := mksubst {xi : nat; xj : nat; subst_expr : Expression}.

  (* substitutions : list of elementary substitutions *)
  Notation Substitution := (list subst_elem).
  Notation value := (tree name name).


  (* applying an elementary substitution to an expression; 
     (apply_elem_tree {i;j;es} e) returns a copy of e where all occurences of x_{i,j} have been replaced by es; 
     es itself is copied and left unchanged, that is (apply_elem_tree {i;j;es} e) may contain variable x_{i,j} 
     - in case x_{i,j} appears in es -
   *)
  Fixpoint apply_elem_tree (s : subst_elem) (e : Expression) {struct e} : Expression :=
    match e with
      | Node (x i j) nil => 
        match eq_nat_dec (xi s) i with 
          | left _ => 
	    match eq_nat_dec (xj s) j with
	      | left _ => (subst_expr s) 
	      | right _ => e
	    end
          | right _ => e
        end
      | Node (symbol dft) forst => Node (symbol dft) (map (apply_elem_tree s) forst)
      | _ => e
    end.

  (* (apply [s1,...,sn] e) <=> (apply_elem_tree s1 (apply_elem_tree (s2 (...(apply_elem_tree sn e)...)*)
  Fixpoint apply (S : Substitution) (e : Expression) {struct S} : Expression :=
    match S with 
      | nil => e
      | s :: S' => apply_elem_tree s (apply S' e)
    end.

  (* fresh p h m returns a forest whose trees are single nodes x_{p,h}, ... , x_{p,h+m-1} *)
  Fixpoint fresh (p h m : nat) {struct m} : list Expression :=
    match m with 
      | 0 => nil
      | (S m') => (Node (x p h) nil) :: (fresh p (S h) m')
    end.


  Lemma eq_Name_dec : forall (n n' : Name), {n = n'} + {n <> n'}.
  Proof.
    intros n n'; destruct n as [xn yn | n]; destruct n' as [xn' yn' | n'].
    elim (eq_nat_dec xn xn'); intro case_x.
    elim (eq_nat_dec yn yn'); intro case_y; [left | right].
    subst; trivial.
    intro H; apply case_y; inversion H; trivial.
    right; intro H; apply case_x; inversion H; trivial.
    right; intro H; inversion H.
    right; intro H; inversion H.
    elim (eq_name_dec n n'); intro case_n; 
      [left; subst | right; intro H; apply case_n; inversion H]; trivial.
  Qed.

  Lemma eq_Expression_dec : forall (e e' : Expression), {e=e'} + {e<>e'}.
  Proof.    
    intros e' e.
    apply eq_tree_dec; apply eq_Name_dec.
  Qed.

  Lemma eq_list_Expression_dec : forall (e e' : list Expression), {e=e'} + {e<>e'}.
  Proof.
    apply list_eq_dec.
    apply eq_Expression_dec.
  Qed.


  Lemma eq_Substitution_dec : forall (s s' : Substitution), {s=s'} + {s<>s'}.
  Proof.
    apply list_eq_dec.
    intros s s'; destruct s as [i j expr]; destruct s' as [i' j' expr'].
    elim (eq_nat_dec i i'); intro casei.
    elim (eq_nat_dec j j'); intro casej.
    elim (eq_Expression_dec expr expr'); intro case; subst; [left; trivial | right].
    injection; intros; apply case; trivial.
    right; injection; intros; apply casej; trivial.
    right; injection; intros; apply casei; trivial.
  Qed.


  (* (tree_is_pattern e) means no function name appears in e *) 
  Fixpoint tree_is_pattern_bool (e : Expression) : bool :=
    match e with 
      | Node (x i j) nil => true
      | Node (symbol dft) forst => 
        (match Get_function dft with 
           | None => true 
           | _ => false
         end) && 
        (fold_left (fun (p : bool) (e : Expression) => p && (tree_is_pattern_bool e)) forst true) 
      | _ => false
    end.

  Definition tree_is_pattern (e : Expression) := (tree_is_pattern_bool e = true).

  (* convertion *)
  Fixpoint tree_name_to_tree_Name (t : value) : Expression :=
    match t with 
      | Leaf l => Leaf (symbol l)
      | Node n f => Node (symbol n) (map tree_name_to_tree_Name f) 
    end.

  (*  *)
  Definition stack_shaping (lexpr : list Expression) (stack : list value) (rho : Substitution) : Prop :=
    map (apply rho) lexpr = map tree_name_to_tree_Name stack.

  (* initial variables of a function *)
  Definition init_vars (fcn : function) := rev_lin (fresh 0 0 (length (fcn_args fcn))).


   (* builds a substitution from the variables in le and values in lv; returns None if |le|<>|lv|, 
      or le contains an element that isn't a variable 
      order in the substitution is the order of variables in le
   *)
  Fixpoint make_substitution (le : list Expression) (lv : list value) {struct le} : option Substitution :=
    match le,lv with
      | nil, nil => Some nil
      | (Node (x i j) nil)::le', v :: lv' => 
        match make_substitution le' lv' with 
          | Some s => Some ((mksubst i j (tree_name_to_tree_Name v))::s)
          | _ => None
        end
      | _,_ => None
    end.

  (* initial substitution of a function : let [v_1,...v_k] be arguments of f s.t. ar(f) = ar; 
     (init_subst 0 ar [v_1, ..., v_k]) is Some [x_{0,1}/v_1, ..., x_{0,ar}/v_k] 
     or None if k <> ar
   *)  
  Definition init_subst (args : list value) := 
    make_substitution (fresh 0 0 (length args)) args.

   (* (var_in_tree i j e) means variable x_{i,j} appears in expression e *) 
  Fixpoint var_in_tree_bool (e : Expression) (i j : nat) {struct e} : bool :=
    match e with 
      | Node (x i' j') nil => 
        (match eq_nat_dec i i' with 
           | left _ => true 
           | right _ => false
         end) && 
        (match eq_nat_dec j j' with 
           | left _ => true 
           | right _ => false
         end)
      | Node (symbol _) forst => 
        fold_left (fun (p : bool) (e : Expression) => p || (var_in_tree_bool e i j)) forst false 
      | _ => false
    end.

  Definition var_not_in_tree (e : Expression) (i j : nat) : Prop :=
    var_in_tree_bool e i j = false.
  
   (* (var_in_subst_elem s i j) means x_{i,j} is the substituted variable in s, or appears in the substituted expression *) 
  Definition var_in_subst_elem (s : subst_elem) (i j : nat) : Prop :=
    match s with 
      | mksubst i' j' e => var_in_tree_bool e i j = true \/ (i' = i /\ j' = j)
    end.


  Lemma var_not_in_subst_elem : forall (si sj : nat) (se : Expression) (i j : nat), 
    ~ var_in_subst_elem (mksubst si sj se) i j -> var_in_tree_bool se i j = false /\ (si <> i \/ sj <> j).
  Proof.
    simpl; intros si sj se i j H_not_in_subst.
    elim (Decidable.not_or _ _ H_not_in_subst).
    intros H1 H2; split.
    destruct (var_in_tree_bool se i j); [elim H1 | idtac]; trivial.
    assert (Hdec : Decidable.decidable (si = i)).
    unfold Decidable.decidable.
    elim (eq_nat_dec si i); [left | right]; trivial.
    elim (Decidable.not_and _ _ Hdec H2); [left | right]; assumption.
  Qed.

  Lemma aux_init_vars_length : forall (p h m : nat), 
    length (fresh p h m) = m.
  Proof.
    intros p h m; generalize h; clear h; induction m; simpl.
    trivial.
    intro h; rewrite (IHm (S h)).
    trivial.
  Qed.


  Lemma init_vars_length : forall (fcn : function), length (init_vars fcn) = length (fcn_args fcn).
  Proof.
    intro fcn; unfold init_vars.
    rewrite (rev_lin_is_rev).
    rewrite rev_length.
    rewrite (aux_init_vars_length 0 0 (length (fcn_args fcn))).
    trivial.
  Qed.


  Lemma element_at_init_vars : forall (n p h j : nat) (ej : Expression), 
    (rev_lin (fresh p h n))[j] = Some ej -> ej = Node (x p (n+h-(S j))) nil.
  Proof.
    intros n p h; rewrite rev_lin_is_rev; generalize n p h; clear n p h.
    induction n; simpl.
    intros p h j ej F; inversion F.
    intros p h j ej;simpl.
    destruct n.
    simpl.
    destruct j; intro H; inversion H.
    replace (h-0) with (h); [trivial | auto with arith].
    intro H.
    compare j (S n); intro comp.
    subst.
    rewrite plus_comm; simpl.
    replace (h+S n - S n) with h; [idtac | rewrite plus_comm; auto with arith].
    cut (((rev (fresh p (S h) (S n))) ++  Node (x p h) nil :: nil)[S n] = (Node (x p h) nil :: nil)[0]).
    intro H1.
    rewrite H1 in H.
    simpl in H.
    inversion H; trivial.
    replace ((rev (fresh p (S h) (S n)) ++ Node (x p h) nil :: nil)[S n]) with 
      ((rev (fresh p (S h) (S n)) ++ Node (x p h) nil :: nil)[length (rev (fresh p (S h) (S n))) + 0]).
    apply element_at_list_concat.
    rewrite rev_length.
    replace (length (fresh p (S h) (S n))) with (S n); simpl; trivial.
    rewrite plus_comm; simpl; trivial.
    cut (n = (length (fresh p (S (S h)) n))); [auto with arith | symmetry].
    apply aux_init_vars_length.
    rewrite (IHn p (S h) j ej).
    rewrite plus_comm; simpl.
    rewrite plus_comm; trivial.
    rewrite <- H.
    apply element_at_list_concat'.
    rewrite rev_length.
    cut (length (fresh p (S h) (S n)) = S n); 
      [intro Hlen; rewrite Hlen; trivial | idtac].
    cut (S j < S (S n)); [auto with arith | idtac].
    cut (j < S (S n)).
    apply not_pred_lt_S_lt.
    auto with arith.
    simpl; assumption.
    replace (S (S n)) with (length (rev (fresh p (S h) (S n)) ++
      Node (x p h) nil :: nil)).
    generalize H; apply element_at_list_some.
    rewrite concat_length.
    rewrite rev_length; rewrite Hlen; simpl.
    rewrite plus_comm; simpl; trivial.
    apply aux_init_vars_length.
  Qed.


  Lemma subst_length : forall (n h : nat) (args : list value),
    length args = n -> make_substitution (fresh 0 h n) args <> None.
  Proof.
    induction n; simpl; trivial.
    intros h args Hl; destruct args.
    intro F; inversion F.
    inversion Hl.
    intros h args Hl; destruct args.
    inversion Hl.
    simpl.
    CaseEq (make_substitution (fresh 0 (S h) n) args).
    intros l H F; inversion F.
    intros H dd; apply (IHn (S h) args).
    generalize Hl; simpl; auto with arith.
    assumption.
  Qed.


  Lemma subst_unchanged : forall (l : Substitution) (i j : nat),
    (forall (s : Expression), ~ In (mksubst i j s) l) -> apply l (Node (x i j) nil) = (Node (x i j) nil).
  Proof.
    induction l; simpl; trivial.
    intros i j Hnotin.
    destruct a; simpl; trivial.
    rewrite (IHl i j); simpl.
    unfold apply_elem_tree; simpl.
    elim (eq_nat_dec xi0 i); intro case_i; simpl; trivial.
    elim (eq_nat_dec xj0 j); intro case_j; simpl; trivial.
    subst.
    elim (Hnotin subst_expr0); left; trivial.
    intros s H; apply (Hnotin s).
    right; assumption.
  Qed.


  Lemma element_at_init_subst : forall (n h j : nat) (l : Substitution) (args : list value) (v : value), 
    args[j] = Some v -> 
    make_substitution (fresh 0 h n) args = Some l -> 
    l[j] = Some (mksubst 0 (h+j) (tree_name_to_tree_Name v)).
  Proof.
    induction n; simpl; trivial.
    intros h j l args v; destruct args; simpl.
    intro F; inversion F.
    intros dd F; inversion F.
    intros h j l args v; destruct args; simpl.
    intros dd F; inversion F.
    destruct j; simpl.
    intro H; inversion H; clear H; subst.
    rewrite plus_comm; simpl.
    CaseEq (make_substitution (fresh 0 (S h) n) args).
    intros l0 case_l0 H; inversion H.
    simpl; trivial.
    intros H F; inversion F.
    CaseEq (args[j]).
    intros v1 case H; inversion H; clear H; subst.
    CaseEq (make_substitution (fresh 0 (S h) n) args).
    intros l0 case_l0 H; inversion H; clear H.
    generalize (IHn (S h) j l0 args v case case_l0).
    replace (S h + j) with (h + S j).
    simpl; destruct (l0[j]); trivial.
    simpl.
    rewrite plus_comm; simpl.
    rewrite plus_comm; trivial.
    intros dd F; inversion F.
    intros dd F; inversion F.
  Qed.


  Lemma init_subst_member : forall (n h h' : nat) (s : Expression) (l : Substitution) (args : list value), 
    make_substitution (fresh 0 h' n) args = Some l -> In (mksubst 0 h s) l -> h' <= h.
  Proof.
    induction n; simpl; intros h h' s l args.
    destruct args; intro H; inversion H.
    intro F; inversion F.
    destruct args.
    intro F; inversion F.
    CaseEq (make_substitution (fresh 0 (S h') n) args).
    intros l0 case H Hin; inversion H.
    clear H; subst.
    elim Hin; clear Hin; intro Hin.
    inversion Hin; subst; clear Hin.
    auto with arith.
    generalize (IHn h (S h') s l0 args case Hin).
    auto with arith.
    intros H F; inversion F.
  Qed.


  Lemma apply_elem_unchanged : forall (s : subst_elem) (v : value), 
    apply_elem_tree s (tree_name_to_tree_Name v) = (tree_name_to_tree_Name v).
  Proof.
    intro s.
    intro v; induction v as [l | n l IHv] using tree_ind. 
    simpl; trivial.
    simpl.
    assert (H : (map (apply_elem_tree s) (map tree_name_to_tree_Name l)) = (map tree_name_to_tree_Name l)).
    induction l; simpl; trivial.
    rewrite (IHv a); try left; trivial.
    rewrite IHl; trivial.
    intros t t_in_l; apply (IHv t); right; assumption.
    rewrite H; trivial.
  Qed.

  Lemma apply_elem_forest_unchanged : forall (s : subst_elem) (l : list value), 
    map (apply_elem_tree s) (map tree_name_to_tree_Name l) = (map tree_name_to_tree_Name l).
  Proof.
    induction l as [ | h t IHl].
    (* case l = nil : *)
    simpl; trivial.
    (* case l = h :: t : *)
    simpl; rewrite IHl; rewrite apply_elem_unchanged; trivial.
  Qed.


  Lemma apply_unchanged : forall (S : Substitution) (v : value), 
    apply S (tree_name_to_tree_Name v) = (tree_name_to_tree_Name v).
  Proof.
    induction S; simpl.
    trivial.
    intro v; rewrite (IHS v).
    apply apply_elem_unchanged.
  Qed.


  Lemma init_subst_apply : forall (n h j : nat) (l : Substitution) (args : list value) (v : value), 
    args[j] = Some v -> make_substitution (fresh 0 h n) args = Some l -> 
    apply l (Node (x 0 (h+j)) nil) = tree_name_to_tree_Name v.
  Proof.
    induction n; simpl; intros h j l args v.
    destruct args; simpl.
    intro F; inversion F.
    intros dd F; inversion F.
    destruct args; simpl.
    intro F; inversion F.
    destruct j; simpl.
    intro H; inversion H; clear H; subst.
    CaseEq (make_substitution (fresh 0 (S h) n) args).
    intros l0 case_l0 H; inversion H; clear H; subst.
    rewrite plus_comm; simpl.
    rewrite (subst_unchanged l0 0 h).
    unfold apply_elem_tree; simpl.
    elim (eq_nat_dec h h); [trivial | intro H; elim H; trivial].
    intros s Hin; generalize (init_subst_member n h (S h) s l0 args case_l0 Hin).
    apply not_S_le.
    intros dd F; inversion F.
    CaseEq (args[j]).
    intros v1 case_argsj H; inversion H; subst.
    CaseEq (make_substitution (fresh 0 (S h) n) args).
    clear H; intros l0 case_l0 H; inversion H; clear H.
    simpl.
    replace (h + S j) with (S h + j).
    rewrite (IHn (S h) j l0 args v case_argsj case_l0).
    apply apply_elem_unchanged.
    simpl; rewrite plus_comm; simpl; rewrite plus_comm; trivial.
    intros dd F; inversion F.
    intros dd F; inversion F.
  Qed.


  Lemma init_stack_shaping : forall (n h : nat) (args : list value) (rho : Substitution),
    make_substitution (fresh 0 h n) args = Some rho -> stack_shaping (rev_lin (fresh 0 h n)) (rev_lin args) rho.
  Proof.
    intros n h args rho Hinit.
    rewrite rev_lin_is_rev; rewrite rev_lin_is_rev.
    unfold stack_shaping.
    assert (H : map (apply rho) ((fresh 0 h n)) =
      map tree_name_to_tree_Name (args)).
    generalize n h args rho Hinit; clear Hinit rho args h n.
    induction n; intros h args rho; simpl.
    destruct args; simpl; trivial.
    intro H; inversion H; subst; unfold stack_shaping; simpl; trivial.
    destruct args; simpl; trivial.
    intro F; inversion F.
    CaseEq (make_substitution (fresh 0 (S h) n) args).
    intros rho' case_rho' H; inversion H; subst.
    generalize (IHn (S h) args rho' case_rho'); unfold stack_shaping; simpl.
    replace (apply rho' (Node (L:=Name) (x 0 h) nil)) with (Node (L := Name) (x 0 h) nil).
    simpl; elim (eq_nat_dec h h); intro case_eq; [clear case_eq | elim case_eq; trivial].
    intro Heq; rewrite <- Heq.
    cut (map (fun e : Expression => apply_elem_tree (mksubst 0 h (tree_name_to_tree_Name t)) (apply rho' e)) (fresh 0 (S h) n) = 
      map (apply rho') (fresh 0 (S h) n)); [intro H'; rewrite H'; trivial | idtac].
    clear IHn case_rho' H.
    generalize args Heq; clear Heq args.
    induction (fresh 0 (S h) n); simpl; intros args Heq.
    trivial.
    destruct args; simpl; simpl in Heq.
    inversion Heq.
    simpl; rewrite (IHl args).
    inversion Heq.
    rewrite H0.
    rewrite H1.
    rewrite apply_elem_unchanged; trivial.
    inversion Heq; trivial.
    symmetry; apply subst_unchanged.
    intros s Hin; generalize (init_subst_member n h (S h) s rho' args case_rho' Hin); apply not_S_le.
    intros dd F; inversion F.
    rewrite map_rev_commut.
    rewrite  H.
    symmetry; apply map_rev_commut.
  Qed.


  Lemma sub_pattern : forall (cnm : name) (args : list Expression), 
    tree_is_pattern (Node (symbol cnm) args) ->
    forall (j : nat) (t : Expression), args[j] = Some t -> tree_is_pattern t.
  Proof.
    induction args; simpl; intros Hpattern j tj Htj.
    inversion Htj.
    destruct j.
    generalize Hpattern.
    unfold tree_is_pattern; simpl.
    CaseEq (Get_function cnm).
    simpl; intros f Hget H; inversion H.
    intro Hnone; simpl; intro H.
    inversion Htj; subst.
    CaseEq (tree_is_pattern_bool tj); trivial.
    intro HF; rewrite HF in H.
    clear IHargs Hpattern; induction args; simpl in H; trivial.
    apply IHargs; trivial.
    CaseEq (element_at_list args j).
    intros tj' case_tj; rewrite case_tj in Htj.
    inversion Htj; generalize case_tj; subst; apply IHargs.
    unfold tree_is_pattern in *; simpl in Hpattern.
    CaseEq (Get_function cnm); simpl in Hpattern.
    intros f Hget; rewrite Hget in Hpattern; inversion Hpattern.
    intro Hget; rewrite Hget in Hpattern.
    unfold tree_is_pattern_bool.
    rewrite Hget; simpl.
    destruct (tree_is_pattern_bool a).
    simpl in Hpattern ;apply Hpattern.
    simpl in Hpattern.
    cut (False); [intro F; inversion F | clear IHargs case_tj].
    induction args; simpl in Hpattern.
    inversion Hpattern.
    apply IHargs; trivial.
    intro F; rewrite F in Htj; inversion Htj.
  Qed.


  Lemma apply_elem_to_forest :  forall (cnm : name) (s : subst_elem) (args : list Expression), 
    apply_elem_tree s (Node (symbol cnm) args) = Node (symbol cnm) (map (apply_elem_tree s) args).
  Proof.
    induction args as [ | hargs targs]; simpl; trivial.
  Qed.

  Lemma apply_to_forest : forall (cnm : name) (rho : Substitution) (args : list Expression), 
    apply rho (Node (symbol cnm) args) = Node (symbol cnm) (map (apply rho) args).
  Proof.
    induction rho; simpl.
    (* case rho nil : *)
    intro args; rewrite (map_id Expression args); trivial.
    (* case rho not nil : *)
    intro args.
    rewrite (IHrho args).
    rewrite apply_elem_to_forest.
    replace (map (apply_elem_tree a) (map (apply rho) args)) with (map (fun e : Expression => apply_elem_tree a (apply rho e)) args).
    trivial.
    clear IHrho; induction args; simpl.
    trivial.
    rewrite IHargs.
    trivial.
  Qed.


  Lemma apply_cons : forall (cnm : name) (rho : Substitution) (args : list value) (sargs : list Expression), 
    length args = length sargs ->
    (forall (vj : value) (ej : Expression) (j : nat), args[j] = Some vj -> sargs[j] = Some ej -> apply rho ej = tree_name_to_tree_Name vj) ->
    apply rho (Node (symbol cnm) sargs) = Node (symbol cnm) (map tree_name_to_tree_Name args).
  Proof.
    intros cnm rho args sargs Hlength H; rewrite (apply_to_forest cnm rho sargs).
    replace (map tree_name_to_tree_Name args) with (map (apply rho) sargs); trivial.
    generalize args Hlength H; clear H Hlength args; induction sargs.
    simpl; intros args Hlength H.
    destruct args; simpl.
    trivial.
    inversion Hlength.
    simpl; intros args Hlength H.
    destruct args; simpl.
    inversion Hlength.
    cut (length args = length sargs); [intro Hlen | generalize Hlength; simpl; auto with arith].
    cut (forall (vj : value) (ej : Expression) (j : nat),
      args[j] = Some vj -> sargs[j] = Some ej ->
      apply rho ej = tree_name_to_tree_Name vj); [intro H' | intros vj ej j Hej Hvj; apply (H vj ej (S j)); simpl; trivial].
    rewrite (IHsargs args Hlen H').
    cut (apply rho a = tree_name_to_tree_Name t); [intro Hav | apply (H t a 0); simpl; trivial].
    rewrite Hav; trivial.
  Qed.


  Lemma apply_substitution_cons : forall (s0 : subst_elem) (s : Substitution) (e : Expression), 
    apply (s0::s) e = apply (s0::nil) (apply s e).
  Proof.
    intros s0 s; generalize s0; clear s0; induction s; simpl; intros s0 e; trivial.
  Qed.


  Lemma apply_substitution_concat : forall (s0 s : Substitution) (e : Expression), 
    apply (s0++s) e = apply s0 (apply s e).
  Proof.
    induction s0; simpl; intros s e.
    trivial.
    rewrite (IHs0 s e); trivial.
  Qed.


  Lemma map_apply_substitution_cons : forall (s0 : subst_elem) (s : Substitution) (le : list Expression), 
    map (apply (s0::s)) le = map (apply (s0::nil)) (map (apply s) le).
  Proof.
    intros s0 s le; generalize s0 s; clear s0 s; induction le; intros s0 s.
    simpl; trivial.
    generalize (IHle s0 s); simpl.
    intro h; rewrite h.
    trivial.
  Qed.


  Lemma map_apply_substitution_concat : forall (s0 s : Substitution) (le : list Expression), 
    map (apply (s0++s)) le = map (apply s0) (map (apply s) le).
  Proof.
    intros s0 s le; generalize s0 s; clear s0 s; induction le; intros s0 s.
    simpl; trivial.
    generalize (IHle s0 s); simpl; intro h; rewrite h.
    rewrite (apply_substitution_concat s0 s a); trivial.
  Qed.


  Lemma make_substitution_some : forall (m p h : nat) (lv : list value), 
    length lv = m -> make_substitution (fresh p h m) lv <> None.
  Proof.
    induction m; simpl; intros p h lv.
    destruct lv; simpl; intro Hlen.
    intro F; inversion F.
    inversion Hlen.
    destruct lv; simpl; intro Hlen.
    inversion Hlen.
    CaseEq (make_substitution (fresh p (S h) m) lv).
    intros; intro F; inversion F.
    intros F dd; generalize F; clear dd F.
    apply IHm.
    generalize Hlen; auto with arith.
  Qed.


  Lemma var_not_in_subst_not_in_apply_elem : forall (e : Expression) (s : subst_elem) (i j : nat), 
    ~ var_in_subst_elem s i j -> var_not_in_tree e i j -> var_not_in_tree (apply_elem_tree s e) i j.
  Proof.
    intros e s i j Hnot.
    destruct s as [si sj sexpr]; simpl.
    elim (var_not_in_subst_elem si sj sexpr i j Hnot).
    generalize e si sj sexpr i j; clear Hnot e si sj sexpr i j.
    induction e as [l | n l IHe]; intros si sj se i j Hnots1 Hnots2 Hnote.
    (* case e is a leaf : *)
    simpl; trivial.
    (* case e = Node n l : *)
    simpl; destruct n as [ni nj | n].
      (* case n is a variable : *)
    destruct l; trivial.
      (* remaining case l = nil : *)
    elim (eq_nat_dec si ni); intro case_si.
        (* case si = ni : *)
    elim (eq_nat_dec sj nj); intro case_sj.
          (* case sj = nj : *)
    subst.
    unfold var_not_in_tree; trivial.
          (* case sj <> nj : *)
    assumption.
        (* case si <> ni : *)
    assumption.
      (* case n is a name : *)
    unfold var_not_in_tree; simpl.
    elim (fold_bool_or_false (f:=fun (e : Expression) => var_in_tree_bool e i j) (map (apply_elem_tree (mksubst si sj se)) l)).
    simpl; intros H1 H2.
    apply H2; clear H1 H2.
    intros a Ha ; elim (In_mapped _ _ _ _ _ Ha); intros e He. 
    elim He; clear He; intros e_in_l a_eq.
    subst a; apply (IHe e e_in_l si sj se i j); trivial.
    unfold var_not_in_tree.
    elim (fold_bool_or_false (f:=fun (e : Expression) => var_in_tree_bool e i j) l).
    simpl; intros H1 H2.
    apply H1; clear H1 H2; trivial.
  Qed.


  Lemma var_not_in_subst_not_in_apply : forall (S : Substitution) (e : Expression) (i j : nat), 
    (forall (s : subst_elem), In s S -> ~ var_in_subst_elem s i j) -> var_not_in_tree e i j -> var_not_in_tree (apply S e) i j.
  Proof.
    induction S; simpl; trivial.
    intros e i j HS Hnote; apply var_not_in_subst_not_in_apply_elem; trivial.
    apply (HS a).
    left; trivial.
    apply IHS; trivial.
    intros s Hin; apply (HS s); right; assumption.
  Qed.


  Lemma not_var_in_tree_value : forall (v : value) (p h : nat), 
     var_not_in_tree (tree_name_to_tree_Name v) p h.
  Proof.
    induction v as [ l | n l IHv].
    (* case v leaf : *)
    intros p h; unfold var_not_in_tree; simpl; trivial.
    (* case v node : *)
    unfold var_not_in_tree in *; simpl.
    intros p h.
    elim (fold_bool_or_false (f:=fun (e : Expression) => var_in_tree_bool e p h) (map tree_name_to_tree_Name l)).
    simpl; intros H1 H2.
    apply H2; clear H1 H2.
    intros a Ha; elim (In_mapped _ _ _ _ _ Ha).
    intros t Ht; elim Ht; clear Ht; intros t_in_l Ht.
    subst a; apply (IHv t t_in_l p h).
  Qed.


  Lemma apply_elem_var_not_in_unchanged : forall (e es : Expression) (i j : nat), 
    var_not_in_tree e i j -> apply_elem_tree (mksubst i j es) e = e.
  Proof.
    induction e as [ l | n l IHe]; simpl.
    (* case e leaf : *)
    trivial.
    (* case e node : *)
    intros es i j; unfold var_not_in_tree; simpl; destruct n as [ni nj | n].
      (* case n variable *)
    destruct l as [ | h t].
        (* case l empty : *)
    elim (eq_nat_dec i ni); elim (eq_nat_dec j nj); intros case_j_nj case_i_ni; try subst i j; simpl; trivial.
          (* remaining case i = ni /\ j = nj : *) 
    intro H; inversion H.
        (* case l = h :: t : *)
    trivial.
      (* case n is a name : *)
    intro Hfold; cut ((map (apply_elem_tree (mksubst i j es)) l) = l).
    intro H; rewrite H; trivial.
    elim (fold_bool_or_false (f:=fun (e : Expression) => var_in_tree_bool e i j) l).
    simpl; intros H1 H2.
    assert (H : forall a : Expression, In a l -> var_in_tree_bool a i j = false).
    apply H1; trivial.
    clear Hfold H1 H2.
    elim (map_unchanged_elements (f := (apply_elem_tree (mksubst i j es))) l).
    intros H1 H2; apply H2.
    intros a a_in_l; apply IHe;trivial.
    unfold var_not_in_tree; apply H; trivial.
  Qed.


  Lemma var_not_in_subst_elem_unchanged : forall (s : subst_elem) (i j : nat),
    ~ var_in_subst_elem s i j ->
    apply_elem_tree s (Node (x i j) nil) = Node (x i j) nil.
  Proof.
    intros s i j Hnot; destruct s as [si sj se].
    elim (var_not_in_subst_elem si sj se i j Hnot); simpl.
    elim (eq_nat_dec si i); elim (eq_nat_dec sj j); intros H1 H2; subst; trivial.
    (* remaining case : si =i /\ sj =j *)
    intros H1 H2; elim H2; clear H2; intro H2; elim H2; trivial.
  Qed.

  
  Lemma var_not_in_subst_unchanged : forall (S : Substitution) (i j : nat),
    (forall (s : subst_elem), In s S -> ~ var_in_subst_elem s i j) ->
    apply S (Node (x i j) nil) = Node (x i j) nil.
  Proof.
    induction S as [ | hS tS IHS]; intros i j HS; simpl.
    (* case S = nil : *)
    trivial.
    (* case S = hS :: tS : *)
    rewrite IHS; trivial.
    apply var_not_in_subst_elem_unchanged.
    apply HS; left; trivial.
    intros s s_in_tS; apply HS; right; trivial.
  Qed.

  Lemma make_substitution_vars :  forall (S : Substitution) (vf : list value) (p h n : nat) ,
   make_substitution (fresh p h n) vf = Some S ->
   forall (s : subst_elem), In s S -> 
     forall (i j : nat), var_in_subst_elem s i j -> i = p /\ h <= j /\ j < h + n.
  Proof.
    induction S as [ | hS tS IHS].
    (* case S = nil : *)
    intros vf p h n Hsubst s s_in_nil; inversion s_in_nil.
    (* case S = hS :: tS : *)
    intro vf; destruct vf as [ | hvf tvf].
      (* case vf = nil : *)
    destruct n as [ | n]; simpl; intro H; inversion H.
      (* case vf = hvf :: tvf : *)
    destruct n as [ | n]; simpl.
        (* case n = 0 : *)
    intro H; inversion H.
        (* case n > 0 : *)
    CaseEq (make_substitution (fresh p (S h) n) tvf).
          (* case substitution exists : *)
    intros S' Hs' H s s_in_S.
    assert (H' : mksubst p h (tree_name_to_tree_Name hvf) :: S' = hS :: tS).
    (* Proof of H' : *)
    inversion H; trivial.
    (* H' prooved *)
    elim (cons_eq _ _ _ _ _ H'); clear H H'; intros H1 H2.
    subst hS tS; elim s_in_S; clear s_in_S; intro case_s.
            (* case s = mksubst p h (tree_name_to_tree_Name hvf) : *)
    subst s; simpl; intros i j H.
    elim H; clear H; intro H.
    generalize (not_var_in_tree_value hvf i j); unfold var_not_in_tree; simpl.
    intro H'; rewrite H' in H; inversion H.
    elim H; intros; subst; split; trivial.
    split; auto with arith.
    rewrite plus_comm; simpl.
    apply lt_le_trans with (S j); auto with arith.
            (* case s in S' : *)
    assert (H : forall i j : nat, var_in_subst_elem s i j -> i = p /\ (S h) <= j < (S h) + n).
    (* Proof of H : *)
    intros i j; apply (IHS tvf p (S h) n); trivial.
    (* H prooved *)
    intros i j Hij; elim (H i j Hij).
    intros H1 H2; clear H; elim H2; clear H2; intros H2 H3.
    repeat split; auto with arith.
    rewrite plus_comm; simpl; rewrite plus_comm.
    simpl in H3; assumption.
          (* case substitution does not exist : contradiction *)
    intros dd F; inversion F.
  Qed.


  Lemma make_substitution_apply : forall (m p h : nat) (vf : list value) (svf : Substitution) (j : nat) (e : Expression) (v : value), 
    make_substitution (fresh p h m) vf = Some svf -> 
    (fresh p h m)[j] = Some e -> vf[j] = Some v ->
    apply svf e = tree_name_to_tree_Name v.
  Proof.
    induction m as [ | n]; simpl; intros p h vf svf j e v.
    (* case m = 0 : *)
    intros dd F; inversion F.
    (* case m = S n : *)
    destruct vf as [ | hvf tvf].
      (* case vf = nil : *)
    intro F; inversion F.
      (* case vf = hvf::tvf : *)
    CaseEq (make_substitution (fresh p (S h) n) tvf).
        (* case substitution exists : *)
    intros l Hl H; inversion H.
    destruct j as [ | j].
          (* case j = 0 : *)
    clear H; intro H; inversion H; subst; simpl.
    clear H; intro H; inversion H; clear H; subst.
    replace (apply l (Node (L := Name) (x p h) nil)) with (Node (L := Name) (x p h) nil).
    simpl.
    elim (eq_nat_dec p p); intro case_p; [clear case_p | elim case_p; trivial].
    elim (eq_nat_dec h h); intro case_h; [clear case_h | elim case_h; trivial].
    trivial.
    symmetry.
    apply var_not_in_subst_unchanged.
    (* prooving forall s : subst_elem, In s l -> ~ var_in_subst_elem s p h : *)
    intros s Hin H.
    elim (make_substitution_vars l tvf p (S h) n Hl s Hin p h H).
    intros H1 H2; elim H2; clear H1 H2; intros H1 H2.
    generalize H1; apply not_S_le.
          (* case j > 0 : *)
    CaseEq (((fresh p (S h) n))[j]).
    intros varj case_varj H2 case_v.
    inversion H2; clear H2; subst.
    simpl.
    rewrite (IHn p (S h) tvf l j e v Hl); trivial.
    apply apply_elem_unchanged.
    intros dd F; inversion F.
        (* case substitution does not exist : *)
    intros dd F; inversion F.
  Qed.


  Lemma apply_elem_in_subst : forall (e : Expression) (i j : nat) (v : value) (is js : nat) (es : Expression),  
    var_not_in_tree e i j -> 
    apply_elem_tree (mksubst i j (tree_name_to_tree_Name v)) (apply_elem_tree (mksubst is js es) e) = 
    apply_elem_tree (mksubst is js (apply_elem_tree (mksubst i j (tree_name_to_tree_Name v)) es)) e.
  Proof.
    induction e as [n | n l IHe].
    (* case e is a leaf : *)
    simpl; trivial.
    (* case e is Node n l : *)
    intros i j v si sj sexpr. 
    unfold var_not_in_tree; simpl.
    destruct n as [ni nj | n].
      (* case n is a variable : *)
    destruct l as [ | h t].
        (* case l = nil : *)
    elim (eq_nat_dec i ni); intro case_i_ni.
    elim (eq_nat_dec j nj); intro case_j_nj; subst; simpl.
          (* case ni = i /\ nj = j : *) 
    intro H; inversion H.
          (* case ni = i /\ nj <> j : *) 
    intro dd; clear dd.
    elim (eq_nat_dec si ni); intro case_si_ni; subst; simpl.
            (* case si = ni : *)
    elim (eq_nat_dec sj nj); intro case_sj_nj;  subst; simpl; trivial.
    elim (eq_nat_dec ni ni); intro H; [clear H | elim H; trivial].
    elim (eq_nat_dec j nj); [intro H; subst; elim case_j_nj | idtac]; trivial.
            (* case si <> ni : *)
    elim (eq_nat_dec ni ni); intro H; [clear H | elim H; trivial].
    elim (eq_nat_dec j nj); [intro H; subst; elim case_j_nj | idtac]; trivial.
          (* case ni <> i : *)
    simpl; intro dd; clear dd.
    elim (eq_nat_dec si ni); intro case_si_ni; subst; simpl.
            (* case si = ni : *)
    elim (eq_nat_dec sj nj); intro case_sj_nj;  subst; simpl; trivial.
    elim (eq_nat_dec i ni); [intro; subst; elim case_i_ni | idtac]; trivial.
            (* case si <> ni : *)
    elim (eq_nat_dec i ni); [intro; subst; elim case_i_ni | idtac]; trivial.
        (* case l = h :: t : *)
    intro dd; clear dd; simpl; trivial.
      (* case n is a name : *)
    simpl; intro Hfold.
    assert (H : (map (apply_elem_tree (mksubst i j (tree_name_to_tree_Name v)))
      (map (apply_elem_tree (mksubst si sj sexpr)) l)) = (map
        (apply_elem_tree (mksubst si sj
          (apply_elem_tree (mksubst i j (tree_name_to_tree_Name v)) sexpr))) l)).
    (* Proof of H : *)
    rewrite compose_map.
    elim (map_to_elements Expression Expression (fun a : Expression =>
      apply_elem_tree (mksubst i j (tree_name_to_tree_Name v)) (apply_elem_tree (mksubst si sj sexpr) a))
    (apply_elem_tree (mksubst si sj (apply_elem_tree (mksubst i j (tree_name_to_tree_Name v)) sexpr))) l).
    intros H1 H2; apply H1; clear H1 H2.
    intros a a_in_l; apply IHe; trivial.
    unfold var_not_in_tree; simpl.
    elim (fold_bool_or_false (f:= fun (e : Expression) => var_in_tree_bool e i j) l).
    simpl; intros H1 H2; apply H1; trivial.
    (* H prooved *)
    rewrite H; trivial.
  Qed.


  Lemma apply_applied : forall (e : Expression) (i j : nat) (v : value) (rho : Substitution), 
    apply rho (Node (x i j) nil) = tree_name_to_tree_Name v ->
      apply rho (apply_elem_tree (mksubst i j (tree_name_to_tree_Name v)) e) = apply rho e.
  Proof.
    intros e i j v rho Hrho.
    generalize e; clear e.
    induction e as [l | n l IHe].
    (* case e is a leaf : *)
    simpl; trivial.
    (* case e = Node n l : *)
    simpl.
    destruct n as [ni nj | n].
      (* case n variable : *)
    destruct l as [ | h t].
        (* case l = nil : *)
    elim (eq_nat_dec i ni); elim (eq_nat_dec j nj); intros H1 H2; simpl; trivial.
          (* remaining case : i = ni, j = nj : *)
    subst; rewrite Hrho; apply apply_unchanged.
        (* case l = h :: t : *)
    trivial.
      (* case n name : *)
    rewrite apply_to_forest.
    rewrite apply_to_forest.
    assert (H : (map (apply rho) (map (apply_elem_tree (mksubst i j (tree_name_to_tree_Name v))) l)) =
      map (apply rho) l).
    (* Proof of H : *)
    rewrite compose_map.
    elim (map_to_elements Expression Expression (fun a : Expression =>
      apply rho (apply_elem_tree (mksubst i j (tree_name_to_tree_Name v)) a))
    (apply rho) l).
    simpl; intros H1 H2; apply H1; clear H1 H2.
    apply IHe.
    (* H proved *)
    rewrite H; trivial.
  Qed.


  Lemma apply_elem_commut : forall (e : Expression) (i j k l : nat) (t v : value), 
    (i<>k \/ j <> l \/ t = v) -> 
    apply ((mksubst i j (tree_name_to_tree_Name t))::(mksubst k l (tree_name_to_tree_Name v))::nil) e = 
      apply ((mksubst k l (tree_name_to_tree_Name v))::(mksubst i j (tree_name_to_tree_Name t))::nil) e.
  Proof.
    induction e as [l | n l IHe].
    (* case e leaf : *)
    simpl; trivial.
    (* case e = Node n l : *)
    intros i j k m t v Heqneq.
    simpl.
    destruct n as [ni nj | n].
      (* case n variable : *)
    elim (eq_nat_dec k ni); intro case_k_ni.
        (* case k = ni : *)
    elim (eq_nat_dec m nj); intro case_m_nj.
          (* case m = nj : *)
    elim (eq_nat_dec i ni); intro case_i_ni.
            (* case i = ni : *)
    elim (eq_nat_dec j nj); intro case_j_nj.
              (* case j = nj *)
    subst.
    elim Heqneq; clear Heqneq; intro Heqneq; elim Heqneq; trivial.
    intro H; elim H; trivial.
    intro H; subst; trivial.
              (* case j <> nj : *)
    destruct l as [ | h tl].
                (* case l = nil : *)
    subst; simpl. 
    elim (eq_nat_dec ni ni); intro H; [clear H | elim H; trivial].
    elim (eq_nat_dec nj nj); intro H; [clear H | elim H; trivial].
    apply apply_elem_unchanged.
                (* case l <> nil : *)
    subst; simpl; trivial.
            (* case i <> ni : *)
    destruct l as [ | h tl].
              (* case l = nil : *)
    subst; simpl. 
    elim (eq_nat_dec ni ni); intro H; [clear H | elim H; trivial].
    elim (eq_nat_dec nj nj); intro H; [clear H | elim H; trivial].
    apply apply_elem_unchanged.
            (* case l <> nil : *)
    subst; simpl; trivial.
          (* case m <> nj : *)
    elim (eq_nat_dec i ni); intro case_i_ni.
            (* case i = ni : *)
    elim (eq_nat_dec j nj); intro case_j_nj.
              (* case j = nj *)
    subst.
    destruct l as [ | h tl]; simpl.
                (* case l = nil : *)
    elim (eq_nat_dec ni ni); intro H; [clear H | elim H; trivial].
    elim (eq_nat_dec nj nj); intro H; [clear H | elim H; trivial].
    symmetry; apply apply_elem_unchanged.
                (* case l = h ::tl : *)
    trivial.
              (* case j <> nj : *)
    subst.
    destruct l as [ | h tl]; simpl.
                (* case l = nil : *)
    elim (eq_nat_dec ni ni); intro H; [clear H | elim H; trivial].
    elim (eq_nat_dec j nj); intro H; [elim case_j_nj; subst; trivial | clear H].
    elim (eq_nat_dec m nj); intro H; [elim case_m_nj; subst; trivial | clear H].
    trivial.
                 (* case l = h ::tl : *)
    trivial.   
            (* case i <> ni : *)
    subst; destruct l as [ | h tl]; simpl.
              (* case l = nil : *)
    elim (eq_nat_dec ni ni); intro H; [clear H | elim H; trivial].
    elim (eq_nat_dec i ni); intro H; [elim case_i_ni; subst; trivial | clear H].
    elim (eq_nat_dec m nj); intro H; [elim case_m_nj; subst; trivial | clear H].
    trivial.
              (* case l = h ::tl : *)
    trivial.   
        (* case k <> ni : *)
    destruct l as [ | h tl]; simpl; trivial.
    elim (eq_nat_dec i ni); intro case_i_ni.
          (* case i = ni : *)
    elim (eq_nat_dec j nj); intro case_j_nj.
            (* case j = nj : *)
    symmetry; apply apply_elem_unchanged.
            (* case j <> nj : *)
    simpl; subst.
    elim (eq_nat_dec k ni); intro H; [elim case_k_ni; subst | clear H]; trivial.
          (* case i <> ni : *)
    simpl; elim (eq_nat_dec k ni); intro H; [elim case_k_ni; subst | clear H]; trivial.

      (* case n name : *)
    rewrite apply_elem_to_forest.
    rewrite apply_elem_to_forest.
    assert (H : map (apply_elem_tree (mksubst i j (tree_name_to_tree_Name t)))
      (map (apply_elem_tree (mksubst k m (tree_name_to_tree_Name v))) l) =
      map (apply_elem_tree (mksubst k m (tree_name_to_tree_Name v)))
      (map (apply_elem_tree (mksubst i j (tree_name_to_tree_Name t))) l)).
    (* Proof of H : *)
    rewrite compose_map.
    rewrite compose_map.
    elim (map_to_elements Expression Expression (fun a : Expression =>
      apply_elem_tree (mksubst i j (tree_name_to_tree_Name t))
        (apply_elem_tree (mksubst k m (tree_name_to_tree_Name v)) a))
    (fun a : Expression =>
      apply_elem_tree (mksubst k m (tree_name_to_tree_Name v))
      (apply_elem_tree (mksubst i j (tree_name_to_tree_Name t)) a)) l).
    simpl; intros H1 H2; apply H1; clear H1 H2.
    intros a a_in_l.
    generalize (IHe a a_in_l i j k m t v Heqneq); simpl; trivial.
    (* H proved *)
    rewrite H; trivial.
  Qed.


  Lemma reverse_apply : forall (S : Substitution) (n p h : nat) (e : Expression) (l : list value), 
    make_substitution (fresh p h n) l = Some S ->
    apply S e = apply (rev_lin S) e.
  Proof.
    induction S as [ | s S IHS].
    (* case S nil : *)
    simpl; trivial.
    (* case S = s :: S : *)
    simpl; intros n p h e l.
    destruct n as [ | n].
    (* case n = 0 : *)
    simpl; intro H.
    destruct l; inversion H.
    (* case n>0 : *)
    destruct l as [ | hl tl]; simpl.
    intro F; inversion F.
    CaseEq (make_substitution (fresh p (Datatypes.S h) n) tl).
    intros S' case_S'.
    intro H; inversion H; subst.
    clear H.
    rewrite rev_lin_is_rev; simpl.
    rewrite apply_substitution_concat.
    simpl.
    rewrite <- rev_lin_is_rev.
    rewrite <- (IHS n p (Datatypes.S h) (apply_elem_tree (mksubst p h (tree_name_to_tree_Name hl)) e) tl); trivial.
    cut (h < Datatypes.S h); [idtac | auto with arith].
    generalize n p h e tl (Datatypes.S h) case_S'; clear IHS case_S' n p h e tl.
    induction S as [ | s S' IHS].
    simpl; trivial.
    intros n p h e tl m; simpl.
    destruct n; simpl.
    destruct tl; intro H; inversion H.
    destruct tl.
    intro F; inversion F.
    CaseEq (make_substitution (fresh p (S m) n) tl).
    intros stl case_stl H; inversion H; subst.
    clear H; generalize (apply_elem_commut (apply S' e) p h p m hl t); simpl; intros H Hpn.
    rewrite H.
    rewrite (IHS n p h e tl (S m) case_stl).
    trivial.
    generalize Hpn; auto with arith.
    right; left; intro; subst.
    apply lt_irrefl with m; trivial.
    intros dd F; inversion F.
    intros dd F; inversion F.
  Qed.


  Lemma make_substitution_invariant : forall (m p h k : nat) (t : value), k < h ->
    map (apply_elem_tree (mksubst p k (tree_name_to_tree_Name t))) (fresh p h m) = fresh p h m.
  Proof.
    induction m; simpl; trivial.
    intros p h k t lt_k_h.
    elim (eq_nat_dec p p); intro H; [clear H | elim H; trivial].
    elim (eq_nat_dec k h); intro H; [cut False; [intro F; inversion F | subst; generalize lt_k_h; apply lt_irrefl] | clear H].
    rewrite IHm; trivial.
    generalize lt_k_h; auto with arith.
  Qed.

  Lemma make_substitution_simpl_in_branch_then_elem : forall (cnm : name) (n n0 m p h : nat) (svf rho : Substitution) 
    (vf : list value) (e : Expression) (v : value) (f : list value), 
    (forall (j : nat), var_not_in_tree e p (h+j)) ->
    tree_name_to_tree_Name (Node cnm (f ++ vf)) = apply rho (Node (x n n0) nil) ->
      make_substitution (fresh p h m) vf = Some svf -> apply rho e = tree_name_to_tree_Name v ->
        apply rho (apply svf (apply_elem_tree (mksubst n n0 (Node (symbol cnm) ((map tree_name_to_tree_Name f)++(fresh p h m)))) e)) = tree_name_to_tree_Name v.
  Proof.
    intros cnm n n0 m p h svf rho vf e v f Hnotin Hrho Hsvf Hv.
    rewrite (reverse_apply svf m p h (apply_elem_tree (mksubst n n0 (Node (symbol cnm) ((map tree_name_to_tree_Name f)++(fresh p h m)))) e) vf).
    generalize cnm n n0 m p h rho vf e v f Hnotin Hrho Hsvf Hv; clear Hnotin Hrho Hsvf Hv cnm n n0 m p h rho vf e v f.
    induction svf; simpl; intros cnm n n0 m p h rho vf e v f Hnotin Hrho Hsvf Hv.
    cut (fresh p h m = nil /\ vf = nil).
    intro H; elim H; clear H; intros h1 h2.
    rewrite h1.
    replace (Node (symbol cnm) ((map tree_name_to_tree_Name f) ++ nil)) with (tree_name_to_tree_Name (Node cnm f)).
    rewrite apply_applied.
    assumption.
    rewrite <- Hrho; rewrite h2; simpl; trivial.
    rewrite list_concat_nil; trivial.
    simpl; rewrite list_concat_nil; trivial.
    destruct vf.
    destruct m; simpl in Hsvf.
    simpl; split; trivial.
    inversion Hsvf.
    destruct m; simpl in Hsvf.
    inversion Hsvf.
    destruct (make_substitution (fresh p (S h) m) vf); inversion Hsvf.

    rewrite rev_lin_is_rev; simpl.
    rewrite apply_substitution_concat; simpl.
    destruct vf.
    destruct m; simpl; inversion Hsvf.
    destruct m; simpl; inversion Hsvf.
    generalize H0; clear H0; CaseEq (make_substitution (fresh p (S h) m) vf); [intros l Hl H0 | intros Hl H0; inversion H0].
    inversion H0; subst; clear H0.
    rewrite apply_elem_in_subst.
    simpl.
    rewrite concat_map; simpl. 
    elim (eq_nat_dec p p); intro H; [clear H | elim H; trivial].
    elim (eq_nat_dec h h); intro H; [clear H | elim H; trivial].
    replace (map (apply_elem_tree (mksubst p h (tree_name_to_tree_Name t))) (fresh p (S h) m)) with (fresh p (S h) m).
    replace (map (apply_elem_tree (mksubst p h (tree_name_to_tree_Name t))) (map tree_name_to_tree_Name f)) with (map tree_name_to_tree_Name f).
    replace ((map tree_name_to_tree_Name f)++((tree_name_to_tree_Name t)::(fresh p (S h) m))) with ((map tree_name_to_tree_Name (f++(t::nil)))++(fresh p (S h) m)).
    rewrite <- rev_lin_is_rev.
    apply (IHsvf cnm n n0 m p (S h) rho vf e v); trivial. 
    intro j; replace (S h + j) with (h + (S j)).
    apply (Hnotin (S j)).
    rewrite plus_comm; simpl; rewrite plus_comm; trivial.
    rewrite <- Hrho; rewrite <- list_concat_cons; simpl; trivial.
    rewrite concat_map; simpl; rewrite <- list_concat_cons; trivial.
    symmetry; apply apply_elem_forest_unchanged.
    symmetry; apply make_substitution_invariant.
    apply (lt_n_Sn h).
    generalize (Hnotin 0).
    rewrite plus_comm; simpl; trivial.
    assumption.
  Qed.


  Lemma apply_elem_pattern : forall (e : Expression) (s : subst_elem), tree_is_pattern (apply_elem_tree s e) -> tree_is_pattern e.
  Proof.
    induction e as [n | n l IHe].
    (* case e leaf : *)
    simpl; trivial.
    (* case e node : *)
    simpl; intro s; destruct n as [ni nj | n].
    (* case n variable : *)
    destruct l as [ | h t].
      (* case l empty : *)
    intro H; clear H; unfold tree_is_pattern; simpl; trivial.
      (* case l not empty : *)
    trivial.
    (* case n name : *)
    unfold tree_is_pattern; simpl.
    destruct (Get_function n); simpl.
    trivial.
    intro H.
    elim (fold_bool_and_true (f := tree_is_pattern_bool) l); intros H1 H2.
    apply H2; clear H1 H2.
    intros a a_in_l; fold tree_is_pattern_bool; apply (IHe a a_in_l s).
    elim (fold_bool_and_true (f:=tree_is_pattern_bool) (map (apply_elem_tree s) l)); intros H1 H2.
    unfold tree_is_pattern; apply (H1 H (apply_elem_tree s a)).
    clear H1 H2.
    apply in_map; trivial.
  Qed.


  Lemma map_apply_to_element : forall (l : list Expression) (vf : list value) (rho : Substitution) (e : Expression) (v : value) (j : nat),
    map tree_name_to_tree_Name vf = (map (apply rho) l) -> element_at_list (rev_lin l) j = Some e ->
    (rev_lin vf)[j] = Some v -> tree_name_to_tree_Name v = apply rho e.
  Proof.
    induction l; simpl; intros vf rho e v j Heq He Hv.
    inversion He.
    cut (j < length (rev_lin l ++ a :: nil)); [intro Cj | generalize He; rewrite rev_lin_is_rev; rewrite rev_lin_is_rev; apply element_at_list_some].
    rewrite concat_length in Cj; rewrite plus_comm in Cj; simpl in Cj.
    rewrite rev_lin_is_rev in Cj; compare j (length (rev l)); intro comp.
    subst.
    replace (length (rev l)) with (length (rev l) + 0) in He.
    rewrite rev_lin_is_rev in He; simpl in He; rewrite element_at_list_concat in He.
    inversion He; subst; clear He.
    rewrite rev_lin_is_rev in Hv; destruct vf.
    simpl in Hv; inversion Hv.
    simpl in Heq.
    inversion Heq; trivial.
    simpl in Hv.
    replace (length (rev l)) with (length (rev vf) + 0) in Hv.
    rewrite element_at_list_concat in Hv.
    inversion Hv; trivial.
    rewrite plus_comm; simpl.
    rewrite rev_length; rewrite rev_length.
    rewrite (lists.map_length _ _ (apply rho) l).
    rewrite <- H1; apply lists.map_length.
    rewrite plus_comm; simpl; trivial.
    cut (j < length (rev l)).
    clear Cj; intro Cj.
    rewrite rev_lin_is_rev in He; simpl in He; rewrite <- element_at_list_concat' in He; trivial.
    destruct vf.
    simpl in Hv; inversion Hv.
    simpl in Heq; inversion Heq.
    rewrite rev_lin_is_rev in Hv; simpl in Hv; rewrite <- element_at_list_concat' in Hv.
    apply (IHl vf rho e v j H1); rewrite rev_lin_is_rev; trivial.
    replace (length (rev vf)) with (length (rev l)); trivial.
    rewrite rev_length; rewrite rev_length.
    rewrite (lists.map_length _ _ (apply rho) l).
    rewrite <- H1; symmetry; apply lists.map_length.
    generalize Cj comp; apply lt_S_neq_lt.
  Qed.


  Lemma In_fresh_not_var_in : forall (m p h h' : nat) (e : Expression), 
    In e (fresh p h m) -> var_not_in_tree e p (h' + h + m).
  Proof.
    induction m; simpl; intros p h h' e Hin.
    inversion Hin.
    elim Hin; clear Hin; intro Hin.
    subst e; simpl.
    unfold var_not_in_tree; simpl.
    elim (eq_nat_dec p p); intro H; simpl; [clear H | elim H; trivial].
    elim (eq_nat_dec (h' + h + S m) h); intro case.
    cut False; [intro F; inversion F | generalize case; clear case].
    rewrite plus_comm.
    rewrite plus_assoc.
    rewrite plus_comm.
    cut (0 < S m + h'). 
    generalize (S m + h'); clear IHm h' p m; induction h.
    simpl; intros n H H'; subst; inversion H.
    simpl; intros n H H'.
    apply (IHh n H).
    generalize H'; auto with arith.
    (* Proof of 0 < S m + h' : *)
    simpl; auto with arith.
    trivial.
    replace  (h' + h + S m) with (h' + S h + m).
    apply IHm; trivial.
    rewrite (plus_comm h' (S h)); simpl. 
    rewrite (plus_comm (h' + h) (S m)); simpl. 
    replace (h + h' + m) with (m + (h' + h)); trivial.
    rewrite plus_comm; simpl.
    rewrite (plus_comm h h'); trivial.
  Qed.


  Lemma In_fresh : forall (e : Expression) (m p h h' p': nat),  
    p' > p -> In e (rev_lin (fresh p h m)) -> var_not_in_tree e p' h'.
  Proof.
    induction m; intros p h h' p' Cp' Hin.
    simpl in Hin; inversion Hin.
    rewrite rev_lin_is_rev in Hin; simpl in Hin.
    cut (In e (rev (fresh p (S h) m)) \/ In e (Node (x p h) nil :: nil)).
    clear Hin; intro Hin; inversion Hin.
    (* case e in fresh p (S h) m : *)
    apply (IHm p (S h)); trivial.
    rewrite rev_lin_is_rev; trivial.
    (* case e in (Node (x p h) nil :: nil) : *)
    inversion H.
    subst e; simpl.
    unfold var_not_in_tree; simpl.
    elim (eq_nat_dec p' p); intro case_p'_p; simpl.
      (* case p = p' : *)
    subst p'; elim (gt_irrefl p); trivial.
    trivial.
    inversion H0.
    generalize Hin; apply In_concat.
  Qed.

(*
  Lemma var_in_fresh : forall (m p h p' h': nat), var_in_tree (fresh p h m) p' h' -> p' = p.
  Proof.
    induction m; simpl; intros p h p' h' Hin.
    inversion Hin.
    elim Hin; clear Hin; intro Hin.
    symmetry; elim Hin; trivial.
    generalize Hin; apply IHm; trivial.
  Qed.

  
  Lemma var_in_forest_concat : forall (f f' : forest Name) (p h : nat), 
    var_in_forest (forest_concat f f') p h -> var_in_forest f p h \/ var_in_forest f' p h.
  Proof.
    induction f; simpl; intros f' p h.
    unfold forest_concat; simpl.
    rewrite tree_list_to_forest_forest_to_tree_list.
    right; trivial.
    intro H; elim H; clear H; intro H.
    left; left; trivial.
    cut (var_in_forest f p h \/ var_in_forest f' p h).
    intro H2; elim H2; clear H2; intro H2.
    left; right; assumption.
    right; assumption.
    apply IHf.
    apply H.
  Qed.
*)


  Lemma var_in_apply_elem_tree_aux : forall (e e' : Expression) (n n0 p h : nat), 
    var_in_tree_bool (apply_elem_tree (mksubst n n0 e') e) p h = true -> var_in_tree_bool e p h = true \/ var_in_tree_bool e' p h = true.
  Proof.
    induction e as [n | n l IHe]; simpl.
    (* case e leaf : *)
    left; trivial.
    (* case e node : *)
    destruct n as [ni nj | n].
      (* case n variable : *)
    intros e' n n0 p h.
    destruct l; simpl.
    elim (eq_nat_dec n ni); intro case_n_ni.
    elim (eq_nat_dec n0 nj); intro case_n0nj.
    subst; right; assumption.
    simpl; left; trivial.
    simpl; left; trivial.
    simpl; left; trivial.
      (* case n name : *)
    simpl; intros e' n0 n1 p h H.
    elim (fold_bool_or_true (f:=fun (e : Expression) => var_in_tree_bool e p h) (map (apply_elem_tree (mksubst n0 n1 e')) l)). 
    simpl; intros H1 H2; elim (H1 H).
    intros y Hy; elim Hy; clear Hy; intros Hy1 Hy2.
    elim (In_mapped _ _ _ _ _ Hy1).
    intros x' Hx'; elim Hx'; clear Hx'; intros Hx'1 Hx'2.
    assert (H3 : var_in_tree_bool (apply_elem_tree (mksubst n0 n1 e') x') p h = true).
    rewrite <- Hx'2; trivial.
    elim (IHe x' Hx'1 e' n0 n1 p h H3); intro caseIHe; [left | right; trivial].
    elim (fold_bool_or_true (f:=fun (e : Expression) => var_in_tree_bool e p h) l).
    clear H1 H2; intros H1 H2; apply H2.
    exists x'; split; trivial.
  Qed.

  Lemma var_in_apply_elem_tree_aux2 : forall (e e' : Expression) (n n0 p h : nat), 
    var_not_in_tree e p h -> var_not_in_tree e' p h -> var_not_in_tree (apply_elem_tree (mksubst n n0 e') e) p h.
  Proof.
    unfold var_not_in_tree; intros e e' n n0 p h Hnot_in_e Hnot_in_e'.
    CaseEq (var_in_tree_bool (apply_elem_tree (mksubst n n0 e') e) p h); intro H; trivial.
    elim (var_in_apply_elem_tree_aux _ _ _ _ _ _ H); clear H; intro H.
    rewrite H in Hnot_in_e; inversion Hnot_in_e.
    rewrite H in Hnot_in_e'; inversion Hnot_in_e'.
  Qed.

End substitutions.

