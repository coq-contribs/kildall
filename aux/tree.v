  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : tree.v					         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : definition of type tree and facts about trees   *)
  (*             and forests				         *) 
  (***************************************************************)


Section tree.

  Require Export aux_arith.
  Require Export relations.
  Require Export Max.
  Require Import List.

  (* sets of node and leaves labels : *)
  Variables N L : Set.
  (* decidable equality on N and L are needed to have decidable equality on trees *)
  Hypothesis eq_N_dec : forall (n n' : N), {n=n'} + {n<>n'}.
  Hypothesis eq_L_dec : forall (l l' : L), {l=l'} + {l<>l'}.

  Unset Elimination Schemes.

  Inductive tree : Set :=
    | Leaf : L -> tree
    | Node : N -> (list tree) -> tree.

  Set Elimination Schemes.

  Notation forest := (list tree).
 
  (* computes the number of nodes in the tree : *)
  Fixpoint tree_size (t : tree) : nat := 
    match t with 
      | Leaf _ => 0
      | Node _ l => S (fold_left (fun (s : nat) (t : tree) => s + (tree_size t)) l 0)
    end.

  (* proving a (useful) induction principle on trees : *)
  Lemma fold_dom : forall (l : forest) (a : nat),  
    a <= fold_left (fun (s : nat) (t : tree) => s + (tree_size t)) l a.
  Proof.
    induction l as [ | hl tl IHl]; simpl.
          (* case l empty  *)
    auto with arith.
          (* case l = hl::tl *)
    intro a; generalize (IHl (a + tree_size hl)); clear IHl; intro IHl.
    apply le_trans with (a + tree_size hl); trivial.
    auto with arith.
  Qed.

        (* fold monotone wrt initial value : *)
  Lemma fold_inc : forall (l : forest) (a b : nat), a <= b -> 
    fold_left (fun (s : nat) (t : tree) => s + (tree_size t)) l a <= 
    fold_left (fun (s : nat) (t : tree) => s + (tree_size t)) l b.
  Proof.
    induction l as [ | hl tl IHl]; simpl.
          (* case l empty : *)
    trivial.
          (* case l = hl :: tl : *)
    intros a b a_le_b.
    apply IHl.
    generalize a_le_b; auto with arith.
  Qed.

      (* immediate strict subtree size is less than tree size : *)
  Lemma immediate_subtree_size : forall (n : N) (l : forest) (t : tree), 
    In t l -> tree_size t < tree_size (Node n l).
  Proof.
    intros n l; induction l as [ | hl tl IHl].
          (* case l empty : *)
    intros t Hin; inversion Hin.
          (* case l = hl :: tl *)
    intros t Hin; elim Hin; clear Hin; intro Hin.
            (* case hl = t *)
    subst hl; simpl.
    apply le_lt_n_Sm.
    apply fold_dom.
            (* case t in tl : *)
    apply lt_le_trans with (tree_size (Node n tl)).
    apply IHl; trivial.
    simpl.
    apply le_n_S.
    apply fold_inc.
    destruct (tree_size hl); auto with arith.
  Qed.

  Require Import Wf_nat. (* => lt_wf_ind *)

  Lemma tree_ind_aux : forall (P : tree -> Prop),    
    (forall (leaf : L), P (Leaf leaf)) ->
    (forall (node : N) (l : forest), (forall (t : tree), In t l -> P t) -> P (Node node l)) ->
    forall (n : nat) (t : tree), tree_size t = n ->  P t.
  Proof.
    intros P Hleaf Hnode n. 
    apply (lt_wf_ind n (fun (k : nat) => forall (t : tree), tree_size t = k -> P t)).
    clear n; intros n IHn t Hsize.
    destruct t as [leaf | node l]; [apply Hleaf | idtac].
    apply Hnode.
    intros t t_in_l.
    apply (IHn (tree_size t)).
    rewrite <- Hsize.
    apply immediate_subtree_size; assumption.
    trivial.
  Qed.

  Lemma tree_rec_aux : forall (P : tree -> Set),    
    (forall (leaf : L), P (Leaf leaf)) ->
    (forall (node : N) (l : forest), (forall (t : tree), In t l -> P t) -> P (Node node l)) ->
    forall (n : nat) (t : tree), tree_size t = n ->  P t.
  Proof.
    intros P Hleaf Hnode n. 
    apply (lt_wf_rec n (fun (k : nat) => forall (t : tree), tree_size t = k -> P t)).
    clear n; intros n IHn t Hsize.
    destruct t as [leaf | node l]; [apply Hleaf | idtac].
    apply Hnode.
    intros t t_in_l.
    apply (IHn (tree_size t)).
    rewrite <- Hsize.
    apply immediate_subtree_size; assumption.
    trivial.
  Qed.
  
  (* induction principles for tree : *)
  Lemma tree_ind : forall (P : tree -> Prop),    
    (forall (leaf : L), P (Leaf leaf)) ->
    (forall (node : N) (l : forest), (forall (t : tree), In t l -> P t) -> P (Node node l)) ->
    forall (t : tree), P t.
  Proof.
    intros P Pleaf Pnode t.
    apply (tree_ind_aux P Pleaf Pnode (tree_size t) t); trivial.
  Qed.

  Lemma tree_rec : forall (P : tree -> Set),    
    (forall (leaf : L), P (Leaf leaf)) ->
    (forall (node : N) (l : forest), (forall (t : tree), In t l -> P t) -> P (Node node l)) ->
    forall (t : tree), P t.
  Proof.
    intros P Pleaf Pnode t.
    apply (tree_rec_aux P Pleaf Pnode (tree_size t) t); trivial.
  Qed.
  

  Lemma eq_tree_dec : forall (t t' : tree), {t = t'} + {t <> t'}.
  Proof.
    induction t as [l | n l IHt] using tree_rec.
      (* case t leaf : *)
    destruct t' as [l' | n' l'].
    elim (eq_L_dec l l'); intro case_l_l'; [left | right].
    subst; trivial.
    intro H; apply case_l_l'; inversion H; trivial.
    right; intro H; inversion H.
      (* case t = Node n l : *)
    intro t'; destruct t' as [l' | n' l'].
    right; intro H; inversion H.
    elim (eq_N_dec n n'); intro case_n_n'.
       (* case n = n' : *)
    subst n'; assert (H : {l = l'} + {l <> l'}).
    generalize l'; clear l'.
    induction l as [ | hl tl]; intro l'; destruct l' as [ | hl' tl']. 
    left; trivial.
    right; intro H; inversion H.
    right; intro H; inversion H.
    cut (In hl (hl :: tl)); [intro Hhl | left; trivial].
    assert (H : forall t : tree, In t tl -> forall t' : tree, {t = t'} + {t <> t'}).
    intros t t_in_tl; apply IHt.
    right; assumption.
    generalize (IHtl H); clear IHtl; intro IHtl.
    elim (IHt hl Hhl hl'); intro case_hl_hl'.
    subst; elim (IHtl tl'); intro case_tl_tl'.
    subst; left; trivial.
    right; injection; intros; apply case_tl_tl'; trivial.
    right; injection; intros; apply case_hl_hl'; trivial.
    elim H; clear H; intro H; [left | right].
    subst; trivial.
    intro H'; inversion H'; apply H; trivial.
        (* case n <> n' : *)
    right; intro H; inversion H; apply case_n_n'; trivial.
  Qed.
 
  (* subtree relation : *)
  Inductive subtree : relation tree := 
    | subtree_refl : forall (t : tree), subtree t t
    | subtree_cons : forall (n : N) (l : forest) (t t' : tree), 
        subtree t t' -> subtree t (Node n (t' :: l)).

  (* results about subtree : *)
  Lemma subtree_size : forall (t t' : tree), 
    subtree t t' -> tree_size t <= tree_size t'.
  Proof.
    intros t t' stt'.
    apply (subtree_ind (fun (t t' : tree) => tree_size t <= tree_size t')); trivial.
    clear stt' t t'; intros n f t t' stt' Hs; simpl.
    apply le_trans with (m:=tree_size t'); try assumption.
    apply le_trans with (fold_left (fun (s : nat) (t0 : tree) => s + tree_size t0) f
      (tree_size t')); auto with arith.
    apply fold_dom.
  Qed.


  (* strict subtree : *)
  Inductive strict_subtree : relation tree := 
    strict_subtree_cons : forall (n : N) (l : forest) (t t' : tree), 
      subtree t t' -> strict_subtree t (Node n (t' :: l)).
  

  Lemma strict_subtree_size : forall (t t' : tree), 
    strict_subtree t t' -> tree_size t < tree_size t'.
  Proof.
    intros t t' stt'.
    apply (strict_subtree_ind (fun (t t' : tree) => tree_size t < tree_size t')); trivial.
    simpl; clear stt' t t'; intros n f t t' stt'.
    apply le_lt_trans with (m:=tree_size t').
    apply subtree_size; assumption. 
    apply lt_le_trans with (m:=S (tree_size t')); auto with arith.
    apply le_n_S; apply fold_dom.
  Qed.

  Lemma strict_subtree_is_subtree_neq : forall (t t' : tree), 
    strict_subtree t t' <-> subtree t t' /\ t <> t'.
  Proof.
    intros t t'; split.
      (* => : *)
    intro stt'; inversion stt' as [n l t0 t'0 H]; subst.
    split.
    constructor; assumption.
    cut (strict_subtree t (Node n (t'0 :: l))); [intro Hsub | constructor; assumption]. 
    generalize (strict_subtree_size t (Node n (t'0 :: l)) Hsub); intros Hsize Heq.
    rewrite <- Heq in Hsize; generalize Hsize; apply lt_irrefl.
      (* <= : *)
    intro H; elim H; clear H; intro stt'.
    apply (subtree_ind (fun (t t' : tree) => t <> t' -> strict_subtree t t')).
    clear stt' t t'; intros t H; elim H; trivial.
    clear stt' t t'; intros n f t t' stt' H1 H2. 
    constructor; assumption.
    assumption.
  Qed.
  

  (* a tree cannot contain itself : *)
  Lemma no_loop_tree : forall (t : tree) (n : N) (f : forest), 
    t <> Node n (t :: f).
  Proof.
    intros t n f; cut (strict_subtree t (Node n (t :: f))). 
    intro H; generalize (strict_subtree_size t (Node n (t :: f)) H); clear H; intros H H'.
    rewrite <- H' in H; generalize H; apply lt_irrefl.
    constructor; constructor.
  Qed.

  (* a forest cannot contain itself : *)
  Lemma no_loop_forest : forall (t : tree) (f : forest), 
    f <> t :: f.
  Proof.
    intros t f H.
    assert (H' : length (t :: f) = length f).
    rewrite <- H; trivial.
    simpl in H'.
    apply neq_n_Sn with (length f); trivial.
  Qed.

  (* subtree is an order on trees : *)
  Lemma order_subtree : order tree subtree.
  Proof.
    split.
    (* reflexive : *)
    intro t; constructor.
    (* transitive : *)
    intros x y z sxy syz.
    apply (subtree_ind (fun (t t' : tree) => forall (y : tree), subtree y t-> subtree y t')) with y; try assumption.
    intros; assumption.
    clear sxy syz x y z.
    intros n f z y Hzy H1 x H2.
    constructor.
    apply H1; assumption.
    (* antisymmetric : *)
    intros x y Hxy Hyx.
    elim (eq_tree_dec x y); intro case; trivial.
    elim (lt_irrefl (tree_size x)).
    assert (H : strict_subtree x y). 
    elim (strict_subtree_is_subtree_neq x y); intros H H'; apply H'; split; assumption. 
    cut (tree_size x < tree_size y); [intro Hsxy | apply strict_subtree_size; assumption].
    cut (tree_size y <= tree_size x); [intro Hsyx | apply subtree_size; assumption].
    apply lt_le_trans with (tree_size y); assumption.
  Qed.


End tree.

Arguments Node [N L].
Arguments Leaf [N L].


