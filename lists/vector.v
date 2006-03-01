  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : vector.v		   		                 *)
  (*   Authors : S. Coupet-Grimal, W. Delobel		         *)
  (*   Content : specification of lists of fixed length (vector) *)
  (*             and related functions.			         *)
  (***************************************************************)

Section Vector.

  Add LoadPath "../aux".

  Require Export Eqdep.
  Require Export Arith.
  Require Export semilattices.

  (* base set : *)
  Variable A : Set.

  Inductive vector : nat->Set:=
    | vector_nil : (vector 0)
    | vector_cons : forall (n:nat), A->vector n->(vector (S n)).

  Definition eq_list:=(eq_dep nat vector).

  Definition head':=
    fun (n:nat) (v:(vector n)) =>  
      match v in (vector x) return (lt 0 x)-> A with
	vector_nil => fun h:(lt O O) => (False_rec A (lt_irrefl O h)) |
	  (vector_cons n' h _) => fun H : (lt 0 (S n')) => h
      end.

  (* returns head (first element) of the list *)
  Definition head:=
    fun (n:nat)(v:(vector (S n))) =>  (head' (S n) v (lt_O_Sn n)).

  Definition tail:= 
    fun (n:nat)(v:vector n) =>  
      match v in (vector x) return (vector (pred x)) with
	vector_nil => vector_nil|
	  (vector_cons n' h v')=> v' end.

  Lemma empty_dep:forall (n:nat)(v:(vector n)), n=O->(eq_list O vector_nil n v).
  Proof.
    unfold eq_list; intros n v.
    dependent inversion v; auto.
    intro h; absurd  ((S n0)=0); auto.
  Save.

  Hint Resolve empty_dep.

  Lemma empty:forall (v:(vector O)), vector_nil=v.
  Proof.
    intro v.
    apply (eq_dep_eq nat vector O).
    apply empty_dep; auto.
  Save.

  Hint Resolve empty.

  Remark non_empty_dep:
    forall (n m : nat), m=(S n)->forall (v:(vector (S n))),
      {h:A & {t:(vector n) | (eq_list (S n) v (S n) (vector_cons n h t))}}.
  Proof.
    intros.
    generalize H.
    dependent inversion_clear v with 
      (fun (n':nat)(v:(vector n')) =>
        m=n'-> {a:A & {v':(vector n)|(eq_list n' v (S n) (vector_cons n a v'))}}).
    unfold eq_list.
    intro H'.
    exists a.
    exists v0.
    constructor.
  Qed.

  Lemma non_empty:forall (n:nat)(v:(vector (S n))),
    {a:A &{t:(vector n)|v=(vector_cons n a t)}}. 
  Proof.
    intros n v.
    cut (sigS (fun a:A=>
      (sig (fun t:(vector n)=>(eq_list (S n) v (S n) (vector_cons n a t)))))).
    intros H; elim H; clear H.
    intros a H; elim H; clear H.
    intros t H.
    exists a; exists t.
    apply (eq_dep_eq nat vector (S n)) .
    unfold eq_list in H; auto.
    apply (non_empty_dep n (S n)); auto.
  Defined.

  Lemma split_vector :forall (n:nat)(v:(vector (S n))),
    v=(vector_cons n (head n v) (tail (S n) v)).
  Proof.
    intros n v.
    elim (non_empty n v).
    intros h H; elim H; clear H.
    intros t e.
    rewrite e; simpl.
    auto.
  Save.

  Definition hd' := fun  (n:nat)(v:(vector (S n))) =>
    let (a, H):= (non_empty n v) in a.
  
  Lemma Non_empty_Hd : 
    forall (n:nat)(a:A)(v:(vector n)), (hd' n (vector_cons n a v))=a.
  Proof.
    intros n a v; unfold hd'.
    elim (non_empty n (vector_cons n a v)).
    intros x H; elim H.
    clear H; intros X H.
    injection H; auto.
  Save.

  (* pointwise order on vectors : *)
  Inductive vector_pointwise (r:relation A):
    forall n:nat, (vector n)->(vector n) -> Prop :=
    | le_nil: vector_pointwise r 0 vector_nil vector_nil
    | le_cons: forall (a a' : A) (n : nat) (v v' : (vector n)), 
      (r a a')->vector_pointwise r n v v'->vector_pointwise r (S n) (vector_cons n a v) (vector_cons n a' v').

  Definition Vector_pointwise (r:relation A) (n:nat) : relation (vector n) := 
    vector_pointwise r n.
  Definition SI_vector_pointwise (r:relation A) (n:nat) : relation (vector n) := 
    strict (inv (vector_pointwise r n)).

  (* replaces element at rank p with element a; 
     leaves list unchanged if rank is greater than the size of the list *)
  Fixpoint vector_replace (n:nat) (v:vector n) (i:nat) (a:A) {struct v}: 
    (vector n) :=
    match v in vector n return vector n with 
      | vector_nil => vector_nil 
      | vector_cons n' h t => 
       	match i with 
          | 0 => vector_cons n' a t 
          | (S i') => vector_cons  n' h (vector_replace n' t i' a) 
        end
    end.

  (* returns True if element a belongs to the vector *)
  Fixpoint belong_element_vector (n:nat) (l : vector n) (a:A) {struct l} : Prop :=
    match l in vector n return Prop with 
      | vector_nil => False
      | vector_cons n' h t => h=a \/ belong_element_vector n' t a
    end.

  (* extracts element at rank i, given a proof i is less than the size *) 
  Fixpoint element_at (n:nat) (v : vector n) (i:nat) {struct v} : 
    (lt i n)->A :=
    match v in vector n, i return (lt i n)->A with 
      | vector_nil, _ => fun x : (lt i 0) => (False_rec A (lt_n_O i x))
      | (vector_cons p h t), 0 => fun (x : (lt 0 (S p)))=> h    
      | (vector_cons p h t), (S i') => 
        fun (x : (lt (S i') (S p))) => (element_at p t i') (lt_S_n i' p x)
    end.

  (* unsafe version of element_at *)
  Fixpoint element_at_unsafe (n : nat) (v : vector n) (i : nat) {struct v} : option A :=
    match v with 
      | vector_nil => None
      | vector_cons p h t => 
        match i with 
       	  | 0 => Some h
	  | S i' => element_at_unsafe p t i'
	end
    end.

  (* build a constant list containing element e *)
  Fixpoint constant_list (n : nat) (a : A) {struct n} : vector n :=
    match n return vector n with
      | 0 => vector_nil
      | (S p) => vector_cons p a (constant_list p a)
    end.

End Vector.

  (* map on a vector : *)
Fixpoint vector_map (A B:Set) (g:A->B) (n:nat) (v:vector A n) {struct v} : 
  vector B n :=
  match v in (vector _ n) return (vector _ n) with 
    | vector_nil => vector_nil B
    | vector_cons p h t => vector_cons B p (g h) (vector_map A B g p t)
  end.

Fixpoint map2 (A B C : Set) (f : A-> B -> C) (n : nat) {struct n}:
  (vector A n)->(vector B n)-> (vector C n):=
  match n return (vector _ n)->(vector _ n)-> (vector _ n) with
    | 0 =>  (fun (v:(vector _ 0))(v':(vector _ 0)) =>  (vector_nil _))
    | (S p)=> (fun  (v:(vector _ (S p))) (v':(vector _ (S p))) =>
        (vector_cons _ p (f (head A p v) (head B p v'))
          (map2 _ _ _  f _ (tail _ _ v) (tail _ _ v'))))
  end.

Definition Map2 (A : Set) (f : binop A) (n:nat):= map2 A A A f n.


Implicit Arguments vector_cons [A n].
Implicit Arguments vector_nil [A].
Implicit Arguments head [A n].
Implicit Arguments tail [A n].
Implicit Arguments empty [A].
Implicit Arguments split_vector [A n].
Implicit Arguments vector_replace [A n].
Implicit Arguments belong_element_vector [A n].
Implicit Arguments element_at [A n].
Implicit Arguments vector_map [A B n].
Implicit Arguments map2 [A B C n].
Implicit Arguments Map2 [A].
Implicit Arguments constant_list [A].
Implicit Arguments element_at_unsafe [A n].

Ltac Split x:= replace x with (vector_cons (head x) (tail x)); 
  [trivial(*idtac?*) | symmetry; exact (split_vector x)].

Ltac CaseEq f:=generalize (refl_equal f); pattern f at -1 in |- *; case f.

Notation "v '[' p '<-' e ']'" := (vector_replace v p e) (at level 50).
Notation "e 'INv' v" := (belong_element_vector v e) (at level 50).
Notation "v '[' p '|' C ']'" := (element_at v p C) (at level 50).
Notation "v '[' p '|_]'" := (element_at_unsafe v p) (at level 50).