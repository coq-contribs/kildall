  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : typing.v					         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : tree (thus expression) typing                   *)
  (***************************************************************)


Section typing.



  Require Export inst_types.

  Notation Get_constr := (get_constr_by_name constructors).
  
  Fixpoint fold_left2 (A B C : Set) (f : C -> A -> B -> C) (la : list A) (lb : list B) (c err : C) 
    {struct la} : C :=
    match la,lb with 
      | nil,nil => c
      | ha::ta,hb::tb => fold_left2 A B C f ta tb (f c ha hb) err
      | _,_ => err
    end.
    
  Implicit Arguments fold_left2 [A B C].
  Require Export Bool.  

  Inductive tree_list_typing : list value -> list name -> Prop :=
    | tree_list_typing_nil : tree_list_typing nil nil
    | tree_list_typing_cons : forall (c : name) (const : constr) (l : list value) (l' : list value) (t : name) (t' : list name), 
      Get_constr c = Some const -> cons_ret const = t -> tree_list_typing l (cons_args const) -> 
      tree_list_typing l' t' -> tree_list_typing ((Node c l)::l') (t::t').
       
  (* (tree_typing v t) means  value v has type t according to parameter constructors *)
  Definition tree_typing (v : value) (t : name) : Prop := tree_list_typing (v::nil) (t::nil).

  
  (* *)
  Definition stack_typing (l : list value) (t : Sigma) : Prop :=
    match t with 
      | Top_T => False
      | Bot_T => False
      | Types typ => tree_list_typing l typ
    end.

  Lemma cons_list_typing : forall (v : value) (t : name) (l : list value) (lt : list name), 
    tree_typing v t -> tree_list_typing l lt -> tree_list_typing (v::l) (t::lt).
  Proof.
    intros v t l lt Hvt Hllt.
    inversion Hvt; subst.
    constructor 2 with const; trivial.
  Qed.

  Lemma sub_list_typing_right : forall (l l' : list value) (t t' : list name), 
    length l = length t -> tree_list_typing (l++l') (t++t') ->
    tree_list_typing l' t'.
  Proof.
    induction l; intros l' t t' Hlength.
    destruct t; simpl; [trivial | inversion Hlength].
    destruct t; [inversion Hlength | simpl in *].
    intro H; inversion H.
    apply (IHl l' t t'); auto.
  Qed.

  Lemma sub_list_typing_left : forall (l l' : list value) (t t' : list name), 
    length l = length t -> tree_list_typing (l++l') (t++t') ->
    tree_list_typing l t.
  Proof.
    induction l; intros l' t t' Hlength.
    destruct t; simpl; [constructor | inversion Hlength].
    destruct t; [inversion Hlength | simpl in *].
    intro H; inversion H.
    constructor 2 with const; subst; trivial.
    apply (IHl l' t t'); auto.
  Qed.

  Lemma app_list_typing : forall (l l' : list value) (t t' : list name), 
    tree_list_typing l t ->
    tree_list_typing l' t' ->
    tree_list_typing (l++l') (t++t').
  Proof.
    induction l; intros l' t t' Ht Ht'.
    inversion Ht; subst t.
    simpl.
    assumption.
    destruct t; simpl.
    inversion Ht.
    inversion Ht.
    constructor 2 with const; subst; trivial.
    apply (IHl l' t t'); auto.
  Qed.


  Lemma rev_list_typing : forall (l : list (value)) (t : list name), 
    tree_list_typing l t ->
    tree_list_typing (rev_lin l) (rev_lin t).
  Proof.
    induction l; intros t H; destruct t. 
    trivial.
    inversion H.
    inversion H.
    rewrite rev_lin_is_rev; simpl; rewrite rev_lin_is_rev; simpl.
    apply app_list_typing.
    rewrite <- rev_lin_is_rev; rewrite <- rev_lin_is_rev; apply IHl; trivial.
    inversion H; trivial.
    inversion H.
    constructor 2 with const; subst; trivial.
    constructor.
  Qed.


  Lemma args_to_tree_typing : forall (cnm : name) (c : constr) (Hget : Get_constr cnm = Some c) (vargs : list value),
    tree_list_typing vargs (cons_args c) -> 
    tree_typing (Node cnm vargs) (cons_ret c).
  Proof.
    intros cnm c Hget vargs.
    unfold tree_typing.
    intro H; constructor 2 with c; trivial.
    constructor.
  Qed.

  Lemma tree_to_args_typing : forall (cnm ret : name) (c : constr) (Hget : Get_constr cnm = Some c) (vargs : list value),
    tree_typing (Node cnm vargs) ret ->
    tree_list_typing vargs (cons_args c).
  Proof.
    intros cnm ret c Hget vargs.
    unfold tree_typing.
    intro H; inversion H; subst.
    rewrite Hget in H5; inversion H5.
    subst; assumption.
  Qed.


  Lemma element_at_list_typing : forall (j : nat) (l : list value) (t : list name) (v : value) (t' : name), 
    tree_list_typing l t -> t[j] = Some t' -> l[j] = Some v ->
    tree_typing v t'.
  Proof.
    unfold tree_typing.
    induction j; intros l t v t' Hlist Helt Hell.
    induction l; (simpl in *).
    inversion Hell.
    destruct t.
    inversion Hlist.
    (simpl in *).
    inversion Hell; inversion  Helt.
    subst a n.
    inversion Hlist; subst.
    constructor 2 with const; trivial.
    constructor.
    destruct l.
    inversion Hell.
    destruct t.
    inversion Helt.
    apply (IHj l t v t').
    inversion Hlist; trivial.
    simpl in Helt.
    destruct (t[j]); simpl.
    assumption.
    inversion Helt.
    simpl in Hell.
    destruct (element_at_list l j); simpl.
    assumption.
    inversion Hell.
  Qed.


  Lemma list_typing_length : forall (l : list value) (t : list name), 
    tree_list_typing l t -> length l = length t.
  Proof.    
    induction l; intro t; destruct t; intro H.
    trivial.
    inversion H.
    inversion H.
    simpl.
    cut (length l = length t).
    auto with arith.
    apply IHl; inversion H; trivial.
  Qed.


  Lemma tree_typing_args_length : forall (cnm :name) (vf : list value) (t : name) (c : constr),  
    Get_constr cnm = Some c -> tree_typing (Node cnm vf) t -> length vf = length (cons_args c).
  Proof.
    intros cnm vf t c Hc Htyping.
    cut (tree_list_typing vf (cons_args c)).
    clear Htyping.
    generalize (cons_args c); induction vf; simpl; intro types.
    intros H; inversion H; simpl; trivial.
    destruct types; simpl.
    intro F; inversion F.
    intro Htype; rewrite (IHvf types).
    trivial.
    inversion Htype; trivial.
    inversion Htyping; subst; trivial.
    rewrite Hc in H4; inversion H4; trivial.
  Qed.

End typing.
