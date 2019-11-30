  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : list.v					         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel 		         *)
  (*   Content : elementary functions on (classical) lists,      *) 
  (*             and related results			         *)
  (***************************************************************)

Global Set Asymmetric Patterns.

Ltac CaseEq f:=generalize (refl_equal f); pattern f at -1 in |- *; case f.

Section lists.

  Require Export List.
  Require Export Arith.
  (* base set : *)
  Variable A : Set.

  (* splits a list into its first k elements and the remaining part;
     returns None if there are not enough elements  *)
  Fixpoint split_k_elements (k : nat) (l : list A) {struct l} : option (list A * list A) :=
    match l, k with 	
      | _, 0 => Some (nil,l)
      | h :: t, S k' => 
        match split_k_elements k' t with
      	  | Some (l', r') => Some ((h :: l'), r')
	  | None => None
	end
      | _, _ => None
    end.    

  (* conformance of split_k_element to its specifications : *)
  Lemma split_k_elements_ok : forall (k : nat) (l lk lr: list A), 
    split_k_elements k l = Some (lk, lr) -> l = lk ++ lr.
  Proof.
    intros k l; generalize k; clear k.
    induction l; simpl.
    destruct k; intros lk lr H; inversion H.
    simpl; trivial.
    destruct k; intros lk lr.
    intro H; inversion H; simpl; trivial.
    generalize (IHl k); destruct (split_k_elements k l).
    destruct p as [lk' lr'].
    intro H; cut (l = lk'++lr').
    intro; subst l.
    intro H'; inversion H'; simpl; trivial.
    apply (H lk' lr'); trivial.
    intros H H'; inversion H'.
  Qed.

  (* conformance of split_k_element to its specifications (continued) : *)
  Lemma split_k_elements_length : forall (k : nat) (l lk lr : list A), 
    split_k_elements k l = Some (lk, lr) -> length lk = k.
  Proof.
    intros k l; generalize k; clear k; induction l; intros k lk lr; simpl.
    destruct k; intro H; inversion H.
    simpl; trivial.
    destruct k.
    intro H; inversion H; simpl; trivial.
    simpl; generalize (IHl k); clear IHl; intro IHl.
    destruct (split_k_elements k l).
    destruct p.
    intro h; inversion h; subst lk; subst lr.
    simpl; generalize (IHl l0 l1).
    auto with arith.
    intro h; inversion h.
  Qed.

  (* if split_k_elements returns a result different from None, 
     then k is <= length of the splitted list *) 
  Lemma split_k_elements_some : forall (k : nat) (l lk lr : list A), 
    split_k_elements k l = Some (lk, lr) -> k <= length l.
  Proof.
    intros k l; generalize k; clear k; induction l.
    intros k lk lr H; cut (length lk = k); [intro Hlen | generalize H; apply split_k_elements_length].
    simpl in H; destruct k.
    simpl; auto with arith.
    inversion H.
    intros k lk lr H; destruct k; simpl.
    auto with arith.
    simpl in H; generalize H; clear H.
    CaseEq (split_k_elements k l); simpl.
    intros p case; destruct p as [lk' lr'].
    intro H; inversion H; subst.
    cut (k <= length l); [auto with arith | apply (IHl k lk' lr)].
    assumption.
    intros dd F; inversion F.
  Qed.

  (* if split_k_elements returns None, 
     then k is > length of the splitted list *) 
  Lemma split_k_elements_none : forall (k : nat) (l : list A), 
    split_k_elements k l = None -> length l < k.
  Proof.
    intros k l; generalize k; clear k; induction l.
    intro k; destruct k; simpl.
    intro H; inversion H.
    auto with arith.
    intro k; destruct k; simpl.
    intro H; inversion H.
    CaseEq (split_k_elements k l).
    intros p case; destruct p as [lk lr].
    intro F; inversion F.
    intros case dd; clear dd; cut (length l < k); [auto with arith | apply IHl; auto].
  Qed.

  (* returns, if it exists, the k th element of the list *)
  Fixpoint element_at_list (l : list A) (k : nat) {struct l} : option A :=
    match l with 
      | nil => None
      | h :: t => 
        match k with 
	  | 0 => Some h
	  | S k' => element_at_list t k' 
	end
    end.

  Notation "l '[' k ']'" := (element_at_list l k) (at level 50).

  (* if element_at_list returns a result different from None, 
     then k is < length of the list *)
  Lemma element_at_list_some : forall (l : list A) (k : nat) (e : A), 
    l[k] = Some e -> k < length l.
  Proof.
    induction l; simpl; intros k e H.
    inversion H.
    destruct k.
    inversion H; subst a.
    auto with arith.
    cut (k < length l); [auto with arith | CaseEq (l[k])].
    intros a0 He.
    rewrite He in H; inversion H; subst a0.
    apply (IHl k e); auto.
    intro He; rewrite He in H; inversion H.
  Qed.

  (* if element_at_list returns None, 
     then k is >= length of the list *)
  Lemma element_at_list_none : forall (l : list A) (k : nat), 
    l[k] = None -> k >= length l.
  Proof.
    induction l; simpl; intros k H.
    auto with arith.
    destruct k.
    inversion H.
    cut (k >= length l); [auto with arith | CaseEq (l[k])].
    intros ao Ha0.
    rewrite Ha0 in H; inversion H.
    apply IHl.
  Qed.

  (* compatibility with In : *)
  Lemma element_at_list_in : forall (l : list A) (k : nat) (e : A), 
    l[k] = Some e -> In e l.
  Proof.
    induction l; simpl; intros k e H.
    inversion H.
    destruct k.
    inversion H; left; trivial.
    right; generalize H; clear H; CaseEq (l[k]).
    intros a0 case_a0 H; inversion H; subst; apply (IHl k); trivial.
    intros dd F; inversion F.
  Qed.

  (* *)
  Lemma element_at_list_concat : forall (l l' : list A) (k : nat), 
    (l++l')[length l + k] = l'[k].
  Proof.
    induction l.
    simpl; trivial.
    intros l' k.
    simpl.
    rewrite (IHl l' k).
    destruct (l'[k]); simpl; trivial.
  Qed.

  Lemma element_at_list_concat' : forall (l l' : list A) (k : nat),
    k < length l -> l[k] = (l++l')[k].
  Proof.
    induction l; simpl.
    intros l' k Ck; inversion Ck.
    intros l' k Ck; destruct k.
    trivial.
    cut (k < length l); [intro C | generalize Ck; auto with arith].
    rewrite (IHl l' k C).
    trivial.
  Qed.

  
  Remark list_concat_cons : forall (l l' : list A) (t : A),
     l ++ (t :: l') = (l ++ (t::nil)) ++ l'.
  Proof.
    induction l; simpl.
    trivial.
    intros l' t'; rewrite <- IHl.
    trivial.
  Qed.

  (* each non-empty list has a last element : *)
  Lemma list_tail : forall (l : list A), l <> nil -> 
    ex (fun (t : A) => ex (fun (l' : list A) => l = l' ++ (t::nil))).
  Proof.
    induction l as [|t l IHl].
    intro F; elim F; trivial.
    intro H.
    destruct l as [|t' l']; simpl.
    exists t; exists (nil (A := A)).
    simpl; trivial.
    clear H.
    cut (t' :: l' <> nil); [intro h; generalize (IHl h); clear h IHl | intro F; inversion F].
    intro h; elim h; clear h; intros t1 h; elim h; clear h; intros l1 h.
    rewrite h.
    exists t1.
    exists (t :: l1).
    simpl; trivial.
  Qed.


  Remark list_concat_nil : forall (l : list A), l ++ nil = l.
  Proof.
    induction l; simpl; trivial.
    rewrite IHl; trivial.
  Qed.


  (* push  [a1,... an] [b1,...bn] = [an,...,a1,b1,..bn] *)
  Fixpoint push_list (l stack : list A) {struct l} : list A :=
    match l with 
      | nil => stack 
      | h :: t => push_list t (h :: stack)
    end.

  Lemma push_list_is_app_rev : forall (l stack : list A), 
    push_list l stack = (rev l) ++ stack.
  Proof. 
    intro l; induction l as [ | h t IHl]; simpl; intro stack. 
    trivial.
    rewrite (IHl (h :: stack)).
    apply list_concat_cons.
  Qed.

  (* linear version of rev : *)
  Definition rev_lin (l : list A) := push_list l nil.

  Lemma rev_lin_is_rev : forall (l : list A), rev_lin l = rev l.
  Proof.
    intro l; unfold rev_lin; rewrite push_list_is_app_rev.
    apply list_concat_nil.
  Qed.

  Fact rev_length : forall (l : list A), length (rev l) = length l.
  Proof.
    induction l; simpl; trivial.
    rewrite <- IHl.
    clear IHl; induction (rev l); simpl; trivial.
    rewrite IHl0; trivial.
  Qed.

  Lemma element_at_list_rev : forall (l : list A) (k : nat), 
    k < length l -> l[k] = (rev l)[length l - (S k)].
  Proof.
    induction l; simpl.
    trivial.
    intros k Ck.
    destruct k.
    simpl.
    clear IHl.
    generalize (element_at_list_concat (rev l) (a::nil) 0).
    replace (length (rev l) + 0) with (length l - 0).
    intro H; rewrite H.
    simpl; trivial.
    rewrite plus_comm; simpl.
    rewrite <- minus_n_O.
    symmetry; apply rev_length.
    cut (k < length l); [intro C | generalize Ck; auto with arith].
    rewrite (IHl k C).
    rewrite (element_at_list_concat' (rev l) (a::nil) (length l - S k)). 
    destruct ((rev l ++ a :: nil)[length l - S k]); simpl; trivial.
    clear Ck.
    rewrite rev_length.
    auto with arith.
  Qed.


  Lemma concat_length : forall (l l' : list A), length (l++l') = length l + length l'.
  Proof.
    induction l; simpl.
    trivial.
    intro l'; rewrite (IHl l').
    trivial.
  Qed.

  Lemma map_id : forall (l : list A),
    map (fun e : A => e) l = l.
  Proof.
    induction l.
    trivial.
    simpl; rewrite IHl; trivial.
  Qed.
  
  Fact cons_eq : forall (h h' : A) (t t' : list A), 
    h :: t = h' :: t' -> h = h' /\ t = t'.
  Proof.
    intros h h' t t' H; inversion H; split; trivial.
  Qed.

  Lemma map_unchanged_elements : forall (f : A -> A) (l : list A), 
    map f l = l <-> (forall (a : A), In a l -> f a = a).
  Proof.
    intro f; split. 
    (* => : *)
    induction l as [ | h t IHl].
      (* case l nil : *)
    intros Hmap a a_in_nil; inversion a_in_nil.
      (* case l =h :: t : *)
    simpl; intros Hmap a Ha.
    elim (cons_eq _ _ _ _ Hmap); intros H1 H2.
    elim Ha; clear Ha; intro Ha.
        (* case a = h : *)
    subst h;  trivial.
        (* case a in t : *)
    apply IHl; trivial.
    (* <= : *)
    induction l as [ | h t IHl].
      (* case l nil : *)
    simpl; trivial.
      (* case l =h :: t : *)
    intro Helems; simpl.
    rewrite (Helems h); try left; trivial.
    rewrite IHl; trivial.
    intros a a_in_t; apply Helems; try right; trivial.
  Qed.


End lists.

Arguments split_k_elements [A].
Arguments element_at_list [A].
Arguments push_list [A].
Arguments rev_lin [A].
Arguments map_unchanged_elements [A f].

  Notation "l '[' k ']'" := (element_at_list l k) (at level 50).

Section fold_bool.
  (* Results about folding a function returning bool on a list : *)

  Require Export Bool.
  Variable A : Set.
  Variable f : A -> bool.
  
  Lemma fold_bool_and_first_false : forall (l : list A), 
    fold_left (fun (p : bool) (a : A) => p && (f a)) l false = false.
  Proof.
    induction l as [ | h t IHl]; simpl; trivial.
  Qed.

  Lemma fold_bool_and_false : forall (l : list A), 
    fold_left (fun (p : bool) (a : A) => p && (f a)) l true = false <-> ex (fun (a : A) => In a l /\ f a = false).
  Proof.
    intro l; split.
    (* => : *)
    induction l as [ | h t IHl]; simpl.
      (* case l = nil : *)
    intro H; inversion H.
      (* case l = h :: t : *)
    CaseEq (f h); intro case_f_h; simpl.
        (* case f h = true : *)
    intro Hfold; elim (IHl Hfold); intros a Ha; elim Ha; clear Ha; intros a_in_t f_a_false.
    exists a; split; trivial.
    right; assumption.
        (* case f h = false : *)
    intro; exists h; split; trivial.
    left; trivial.
    (* <= : *)
    induction l as [ | h t IHl]; simpl.
      (* case l = nil : *)
    intro H; elim H; clear H; intros a Ha; elim Ha; intro F; inversion F.
      (* case l = h :: t : *)
    intro Ha; elim Ha; clear Ha; intros a Ha.
    elim Ha; clear Ha; intros Ha f_a_false.
    elim Ha; clear Ha; intro Ha.
        (* case a = h : *)
    subst a.
    rewrite f_a_false; apply fold_bool_and_first_false.
        (* case a in t : *)
    destruct (f h).
          (* case f h = true : *)
    apply IHl; exists a; split; trivial.
          (* case f h = false : *)
    apply fold_bool_and_first_false.
  Qed.


  Lemma fold_bool_and_true : forall (l : list A), 
    fold_left (fun (p : bool) (a : A) => p && (f a)) l true = true <-> forall (a : A), In a l -> f a = true.
  Proof.
    split.
    (* => : *)
    induction l as [ | h t IHl]; simpl.
      (* case l nil : *)
    intros dd a F; inversion F.
      (* case l = h::t : *)
    CaseEq (f h); intro case_f_h; simpl.
        (* case f h = true : *)
    intros Hfold a H; elim H; clear H; intro H. 
          (* case a = h : *)
    subst a; assumption.
          (* case a in t : *)
    apply (IHl Hfold a H).
        (* case f h = false : *)
    intro H; rewrite fold_bool_and_first_false in H. 
    inversion H.
    (* <= : *)
    induction l as [ | h t IHl]; simpl.
      (* case l nil : *)
    trivial.
      (* case l = h::t : *)
    intro H; assert (H' : forall a : A, In a t -> f a = true).
    intros a a_in_t; apply H; right; assumption.
    rewrite (H h).
    apply IHl; trivial.
    left; trivial.
  Qed.
    
  Lemma fold_bool_or_first_true : forall (l : list A), 
    fold_left (fun (p : bool) (a : A) => p || (f a)) l true = true.
  Proof.
    induction l as [ | h t IHl]; simpl; trivial.
  Qed.

  Lemma fold_bool_or_false : forall (l : list A), 
    fold_left (fun (p : bool) (a : A) => p || (f a)) l false = false <-> forall (a : A), In a l -> f a = false.
  Proof.
    split.
    (* => : *)
    induction l as [ | h t IHl]; simpl.
      (* case l nil : *)
    intros dd a F; inversion F.
      (* case l = h::t : *)
    CaseEq (f h); intro case_f_h; simpl.
        (* case f h = true : *)
    intros Hfold; rewrite fold_bool_or_first_true in Hfold; inversion Hfold.
        (* case f h = false : *)
    intros Hfold a Ha; elim Ha; clear Ha; intro Ha.
          (* case a = h : *)
    subst a; assumption.
          (* case a in t : *)
    apply (IHl Hfold a Ha).
    (* <= : *)
    induction l as [ | h t IHl]; simpl.
      (* case l nil : *)
    trivial.
      (* case l = h::t : *)
    intro H; assert (H' : forall a : A, In a t -> f a = false).
    intros a a_in_t; apply H; right; assumption.
    rewrite (H h).
    apply IHl; trivial.
    left; trivial.
  Qed.
    
  
  Lemma fold_bool_or_true : forall (l : list A), 
    fold_left (fun (p : bool) (a : A) => p || (f a)) l false = true <-> ex (fun (a : A) => In a l /\ f a = true).
  Proof.
    split.
    (* => : *)
    induction l as [ | h t IHl]; simpl.
      (* case l = nil : *)
    intro H; inversion H.
      (* case l = h :: t : *)
    CaseEq (f h); intro case_f_h; simpl.
        (* case f h = true : *)
    intro; exists h; split; trivial.
    left; trivial.
        (* case f h = false : *)
    intro Hfold; elim (IHl Hfold); intros a Ha; elim Ha; clear Ha; intros a_in_t f_a_false.
    exists a; split; trivial.
    right; assumption.
    (* <= : *)
    induction l as [ | h t IHl]; simpl.
      (* case l = nil : *)
    intro H; elim H; clear H; intros a Ha; elim Ha; intro F; inversion F.
      (* case l = h :: t : *)
    intro Ha; elim Ha; clear Ha; intros a Ha.
    elim Ha; clear Ha; intros Ha f_a_false.
    elim Ha; clear Ha; intro Ha.
        (* case a = h : *)
    subst a.
    rewrite f_a_false; apply fold_bool_or_first_true.
        (* case a in t : *)
    destruct (f h).
          (* case f h = true : *)
    apply fold_bool_or_first_true.
          (* case f h = false : *)
    apply IHl; exists a; split; trivial.
  Qed.

End fold_bool.

Arguments fold_bool_and_first_false  [A f].
Arguments fold_bool_and_false [A f].
Arguments fold_bool_and_true  [A f].
Arguments fold_bool_or_first_true  [A f].
Arguments fold_bool_or_false  [A f].
Arguments fold_bool_or_true  [A f].


Lemma map_length : forall (A B : Set) (f : A -> B) (l : list A), 
  length l = length (map f l).
Proof.
  induction l; simpl; trivial.
  rewrite IHl; trivial.
Qed.

  (* element_at_list applied to a list obtained from map : *)
Lemma element_at_list_map : forall (A B : Set) (l : list A) (f : A->B) (k : nat) (e : A),
  l[k] = Some e -> 
  (map f l)[k] = Some (f e).
Proof.
  induction l; simpl.
  intros f k e F; inversion F.
  intros f k e; destruct k.
  intro H; inversion H; trivial.
  CaseEq (l[k]). 
  intros a0 case_a0 H; inversion H; subst; clear H.
  rewrite (IHl f k e case_a0); trivial.
  intros dd F; inversion F.
Qed.

  (* element_at_list applied to a list obtained from map (continued) : *)
Lemma element_at_list_map' : forall (A B : Set) (l : list A) (f : A->B) (k : nat) (fe : B),
  (map f l)[k] = Some fe -> ex (fun (e : A) => l[k] = Some e /\ fe = f e).
Proof.
  induction l; simpl.
  intros f k e F; inversion F.
  intros f k fe; destruct k.
  intro H; inversion H; exists a; split; trivial.
  CaseEq ((map f l)[k]). 
  intros b case_b H; inversion H; subst; clear H.
  elim (IHl f k fe case_b); intros e He.
  elim He; clear He; intros He1 he2.
  subst; exists e; rewrite He1; split; trivial. 
  intros dd F; inversion F.
Qed.


Lemma map_to_elements : forall (A B : Set) (f g : A -> B) (l : list A), 
  (forall (a: A), In a l -> f a = g a) <-> map f l = map g l.
Proof.
  intros A B f g l; split.
  (* => : *)
  induction l as [ | h t IHl]; intro Helems.
    (* case l = nil : *)
  simpl; trivial.
    (* case l = h :: t : *)
  simpl.
  rewrite IHl.
  rewrite Helems; try left; trivial.
  intros a a_in_t; apply Helems; right; trivial.
  (* <= : *)
  induction l as [ | h t IHl]; intro Hmap.
    (* case l = nil : *)
  intros a a_in_nil; inversion a_in_nil.
    (* case l = h :: t : *)
  intros a Ha; simpl in Hmap; elim (cons_eq _ _ _ _ _ Hmap); intros H1 H2.
  elim Ha; clear Ha; intro Ha.
      (* case a = h : *)
  subst; trivial.
      (* case a in t : *)
  apply IHl; trivial.
Qed.


Fact In_concat : forall (A : Set) (l l' : list A) (e : A), 
  In e (l++l') -> In e l \/ In e l'.
Proof.
  induction l; simpl; intros l' e Hincat.
  right; trivial.
  elim Hincat; clear Hincat; intro Hincat.
  subst; left; left; trivial.
  elim (IHl l' e Hincat); intro H.
  left; right; trivial.
  right; trivial.
Qed.


Fact In_rev : forall (A : Set) (l : list A) (e : A), 
  In e (rev l) -> In e l.
Proof.
  induction l; simpl; intros e Hinrev.
  trivial.
  elim (In_concat A (rev l) (a::nil) e Hinrev); clear Hinrev; intro Hinrev.
  right; apply IHl; trivial.
  inversion Hinrev.
  left; trivial.
  inversion H.
Qed.


Fact concat_In : forall (A : Set) (l l' : list A) (e : A), 
  In e l \/ In e l' -> In e (l++l').
Proof.
  induction l; simpl; intros l' e Hincat.
  elim Hincat; clear Hincat; intro Hincat.
  inversion Hincat.
  assumption.
  elim Hincat; clear Hincat; intro Hincat.
  elim Hincat; clear Hincat; intro Hincat.
  left; trivial.
  right; apply IHl.
  left; trivial.
  right; apply IHl.
  right; trivial.
Qed.


Lemma tail_neq : forall (A : Set) (l : list A) (e : A), l <> e :: l.
Proof.
  induction l; simpl; intros e H; inversion H.
  apply (IHl e); trivial.
Qed.


Lemma In_mapped : forall (A B : Set) (fcn : A -> B) (l : list A) (e : B), 
  In e (map fcn l) -> ex (fun (e' : A) => In e' l /\ e = fcn e').
Proof.
  induction l; simpl; intros e Hin.
  inversion Hin.
  elim Hin; clear Hin; intro Hin.
  exists a.
  split.
  left; trivial.
  symmetry; trivial.
  elim (IHl e Hin).
  intros x Hx; elim Hx; clear Hx; intros Hx1 Hx2.
  exists x.
  split.
  right; assumption.
  assumption.
Qed.

Lemma concat_map : forall (A B : Set) (f : A -> B) (l l' : list A),
  map f (l++l') = (map f l)++(map f l').
Proof.
  induction l.
  simpl; trivial.
  intro l'; simpl.
  rewrite (IHl l'); trivial.
Qed.


Lemma map_rev_commut : forall (A B : Set) (f : A -> B) (l : list A),
  map f (rev l) = rev (map f l).
Proof.
  induction l; simpl; trivial.
  rewrite <- IHl.
  rewrite concat_map; simpl; trivial.
Qed.

Lemma rev_map : forall (A B : Set) (f g : A -> B) (l l' : list A), 
  map f (rev l) = map g (rev l') -> map f l = map g l'.    
Proof.
  intros A B f g l l' H.      
  assert (H' : rev (map f l) = rev (map g l')).      
  rewrite <- map_rev_commut.
  rewrite <- map_rev_commut.
  assumption.
  generalize (map f l) (map g l')  H'; clear H H' l l'; intros l l' H.
  rewrite <- rev_involutive.
  rewrite <- (rev_involutive l).
  generalize (rev l) (rev l') H; intros L L' H'; subst; trivial.
Qed.

Lemma compose_map : forall (A B C : Set) (f : A -> B) (g : B -> C) (l : list A), 
  map g (map f l) = map (fun (a : A) => g (f a )) l.
Proof.
  induction l as [ | h t IHl].
  (* case l = nil : *)
  simpl; trivial.
  (* case l = h :: t : *)
  simpl; rewrite IHl; trivial.
Qed.

