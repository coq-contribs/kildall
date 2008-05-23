  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : vector_results.v			                 *)
  (*   Authors : S. Coupet-Grimal, W. Delobel		         *)
  (*   Content : facts about vectors               	         *)
  (***************************************************************)

Section Vector_results.

  Require Export vector.
  Require Export relations.
  
  (* base set : *)
  Variable A : Set.
  Variable r : relation A.
  Variable sup : binop A.

  (* replace lemmas : *)
  Lemma idempotent_replace : 
    forall (n:nat) (v : vector A n) (i : nat) (a : A), 
      (v[i<-a])[i<-a] = v[i<-a].
  Proof.
    intros n v; induction v as [ | n' hv tv IHv]; simpl.
    trivial.
    intro i; destruct i as [ | i]; [trivial | intro a].
    simpl; rewrite (IHv i a); trivial.
  Qed.

  Lemma overwrite_replace : 
    forall (n:nat) (v : vector A n) (i : nat) (a a': A), 
      (v[i<-a])[i<-a'] = v[i<-a'].
  Proof.
    intros n v; induction v as [ | n' hv tv IHv]; simpl.
    trivial.
    intro i; destruct i as [ | i]; [trivial | intros a a'].
    simpl; rewrite (IHv i a a'); trivial.
  Qed.

  Lemma commutative_replace : 
    forall (n:nat) (v:vector A n) (i j : nat) (a a':A),
      (i<>j \/ a=a') -> (v[i<-a])[j<-a'] = (v[j<-a'])[i<-a].
  Proof.
    intros n v i j a a' H.
    compare i j; intro comp_i_j.
    elim H; clear H; [intro i_neq_j | intro a_eq_a'].
    elim i_neq_j; trivial.   
    subst; trivial.
    clear H.
    generalize i j comp_i_j; clear comp_i_j i j.
    induction v as [ | n' hv tv IHv]; simpl.
    trivial.
    intros i j comp_i_j; destruct i as [ | i]; destruct j as [ | j]; simpl; trivial.
    elim comp_i_j; trivial.
    cut (i <> j); [intro i_neq_j | auto with arith].
    rewrite (IHv i j i_neq_j); trivial.
  Qed.

  Lemma element_at_in_replaced : 
    forall (n : nat) (v : vector A n) (i : nat) (a:A) (C : i < n), 
      (v[i<-a])[i|C] = a.
  Proof.
    induction v as [ | n' hv tv IHv]; simpl; intros i a C.
    inversion C.
    destruct i as [ | i]; simpl.
    trivial.
    apply IHv.
  Qed.

  Lemma element_at_in_replaced' : 
    forall (n : nat) (v : vector A n) (i j : nat) (a:A) (C : j < n), 
      i<>j->(v[i<-a])[j|C] = v[j|C].
  Proof.
    induction v as [ | n' hv tv IHv]; simpl; intros i j a C i_neq_j.
    inversion C.
    destruct i; destruct j; simpl; trivial.
    elim i_neq_j; trivial.
    apply IHv; auto with arith.
  Qed.

  (* belonging to a vector is decidable provided 
     equality on the base set is : *)
  Lemma dec_belong :
    forall (n:nat) (v : vector A n) (a : A),
      (forall a a' : A, {a = a'} + {a <> a'})->
      a INv v \/ ~ (a INv v).
  Proof.
    induction v as [ | n' hv tv IHv]; simpl; intros a eq_A_dec.
    right; unfold not; trivial.
    elim (eq_A_dec hv a); intro comp_hv_a.
    subst; left; left; trivial.
    elim (IHv a eq_A_dec); intro case_belong_a_tv.
    left; right; assumption.
    right; intro H; elim H; trivial.
  Qed.

  (* pointwise order results : *)
  Remark split_vector_pointwise : forall (n:nat) (v v':vector A (S n)), 
    vector_pointwise A r (S n) v v'->
    (vector_pointwise A r n (tail v) (tail v')) /\ (r (head v) (head v')).
  Proof.
    intros n v v' le_vv'.
    inversion le_vv' as [| hv hv' n' tv tv' r_hv_hv' r_tv_tv' dd H H']; subst n'.
    replace v with (vector_cons hv tv).
    replace v' with (vector_cons hv' tv').
    split; simpl; assumption.
    apply (inj_pair2 nat (fun x:nat=>vector A x)); assumption.
    apply (inj_pair2 nat (fun x:nat=>vector A x)); assumption.
  Qed.

  Lemma reflexive_vector_pointwise :
    reflexive A r -> 
    forall n:nat, reflexive (vector A n) (Vector_pointwise A r n).
  Proof.
    intros refl_r n.
    unfold reflexive.
    induction x as [ | n' hv tv IHv].
    constructor.
    constructor.
    apply refl_r.
    exact IHv.
  Qed.

  Lemma transitive_vector_pointwise :
    transitive A r -> 
    forall n:nat, transitive (vector A n) (Vector_pointwise A r n).
  Proof.
    unfold transitive.
    intros trans_r n x y z.
    induction x as [ | n' hv tv IHv].
    elim (empty z).
    constructor.
    Split z.
    intros h1 h2.
    constructor.
    apply (trans_r hv (head y) (head z)).
    elim (split_vector_pointwise n' (vector_cons hv tv) y h1).
    simpl; trivial.
    elim (split_vector_pointwise n' y (vector_cons (head z) (tail z)) h2).
    simpl; trivial.
    unfold Vector_pointwise in IHv.
    apply (IHv (tail y) (tail z)).
    elim (split_vector_pointwise n' (vector_cons hv tv) y h1).
    simpl; trivial.
    elim (split_vector_pointwise n' y (vector_cons (head z) (tail z)) h2).
    simpl; trivial.
  Qed.

  Lemma antisymmetric_vector_pointwise :
    antisymmetric A r -> 
    forall n:nat, antisymmetric (vector A n) (Vector_pointwise A r n).
  Proof.
    unfold antisymmetric.
    intros anti_r n x y.
    induction x as [ | n' hv tv IHv].
    intros; exact (empty y).

    Split y; intros h h'.
    replace tv with (tail y).
    replace hv with (head y).
    trivial.
    inversion h; inversion h'.
    apply anti_r; assumption.
    elim (split_vector_pointwise n' (vector_cons hv tv) (vector_cons (head y) (tail y)) h).
    intros.
    elim (split_vector_pointwise n' (vector_cons (head y) (tail y)) (vector_cons hv tv) h').
    intros.
    symmetry; apply IHv; assumption.
  Qed.


  Lemma sl_order_to_list_sl_order : order A r -> 
    forall n:nat, order (vector A n) (Vector_pointwise A r n).
  Proof.
    intros order_r n.
    inversion_clear order_r. 
    constructor.
    exact (reflexive_vector_pointwise ord_refl n).
    exact (transitive_vector_pointwise ord_trans n).
    exact (antisymmetric_vector_pointwise ord_antisym n).
  Qed.


  Lemma sl_lub_to_list_sl_lub :
    lub A r sup -> forall (n:nat), 
      lub (vector A n) (Vector_pointwise A r n) (Map2 sup n).
  Proof.
    intros lubrasup n.
    inversion_clear lubrasup as [r_a_fab h]; inversion_clear h as [r_b_fab r_fab_c].
    unfold lub.
    induction n as [ | n IHn].
  (* n = 0 *)
    repeat split.
    intros a b; elim (empty a); elim (empty b).
    unfold Map2; simpl; constructor.
    intros a b; elim (empty a); elim (empty b).
    unfold Vector_pointwise,Map2; simpl; constructor.
    intros a b c; elim (empty a); elim (empty b); elim (empty c).
    unfold Vector_pointwise,Map2; simpl; constructor.
  (* n > 0 *)
    unfold Map2,Vector_pointwise in IHn.
    elim IHn; clear IHn; intros IHn1 H'.
    elim H'; clear H'; intros IHn2 IHn3.
    repeat split.
    intros a b; Split a; Split b.
    unfold Vector_pointwise,Map2.
    simpl; constructor.
    apply r_a_fab.
    apply IHn1.
    intros a b; Split a; Split b.
    unfold Vector_pointwise,Map2.
    simpl; constructor.
    apply r_b_fab.
    apply IHn2.
    intros a b c H; Split a; Split b; Split c.
    elim H; clear H; intros H1 H2.
    unfold Map2, Vector_pointwise; simpl.
    constructor.
    apply r_fab_c.
    split.
    elim (split_vector_pointwise n a c H1); trivial.
    elim (split_vector_pointwise n b c H2); trivial.
    apply IHn3.
    elim (split_vector_pointwise n a c H1).
    elim (split_vector_pointwise n b c H2).
    split; trivial.
  Qed.

  Theorem sl_to_list_sl :
    semilattice A r sup -> forall (n:nat),
      semilattice (vector A n) (Vector_pointwise A r n) (Map2 sup n).
  Proof.
    unfold semilattice.
    intros semi n.
    inversion_clear semi as [order lub].
    split.
    exact (sl_order_to_list_sl_order order n). 
    exact (sl_lub_to_list_sl_lub lub n). 
  Qed.

  (* equality on vectors is decidable provided 
     equality on base set is : *)
  Lemma eq_dec_to_list_eq_dec : 
    (forall (a a' : A), {a=a'} + {a<>a'}) -> 
    (forall (n:nat) (v v' : vector A n), {v=v'} + {v<>v'}).
  Proof.
    intros eq_A_dec n v v'.
    induction v as [ | n' hv tv IHv].
    elim (empty v'); left; trivial.
    elim (IHv (tail v')); elim (eq_A_dec hv (head v')); intros case_heads case_tails; 
      [left | right | right | right].
    subst; symmetry; apply split_vector. 
    Split v'; injection; trivial.
    Split v'; injection; intros; apply case_tails.
    apply (inj_pair2 nat (fun x : nat => vector A x)); assumption.
    Split v'; injection ; trivial.
  Qed.

  Lemma vector_pointwise_replace : 
    reflexive A r->
    forall (n : nat) (v: vector A n) (i : nat) (C : i<n) (a : A), 
      r (v[i|C]) a -> vector_pointwise A r n v (v[i<-a]). 
  Proof.
    intros refl_r n v.
    induction n as [ | n IHn]; intros i C a. 
    inversion C.
    Split v; destruct i as [ | i].
    simpl.
    intro H; constructor.
    assumption.
    apply reflexive_vector_pointwise; assumption.
    simpl.
    intro H; constructor.
    apply refl_r.
    apply IHn with (lt_S_n i n C).
    assumption.
  Qed.

  Lemma neq_replace : 
    forall (n : nat) (v: vector A n) (i : nat) (C : i<n) (a : A), 
      a<>(v[i|C])->(v[i<-a])<>v. 
  Proof.
    induction v as [ | n' hv tv IHv]; intros i C a H.
    inversion C.
    destruct i as [ | i]; simpl.
    injection.
    simpl in H; trivial.
    simpl; simpl in H; intro H'.
    apply (IHv i (lt_S_n i n' C) a H).
    injection H'; apply (inj_pair2 nat (fun x : nat => vector A x)).
  Qed.

  (* element_at results : *)
  Lemma element_at_irrel : 
    forall (n:nat) (v : vector A n) (i:nat) (C C': i<n), 
      v[i|C] = v[i|C'].
  Proof.
    induction n as [ | n]; intros v i C C'.
    inversion C.
    Split v.
    destruct i; simpl.
    trivial.
    apply IHn.
  Qed.

  Remark element_at_belong : 
    forall (n : nat) (v : vector A n) (i : nat) (C : i<n), 
      (v[i|C]) INv v.
  Proof.
    induction v as [ | n' hv tv IHv]; intros i C.
    inversion C.
    destruct i; simpl; auto.
  Qed.

  Remark vector_pointwise_to_element :
    forall (n : nat) (v v' : vector A n) (i : nat) (C : i<n),
      vector_pointwise A r n v v' ->
      r (v[i|C]) (v'[i|C]).
  Proof.
    induction v as [ | n' hv tv IHv]; intros v' i C.
    inversion C.
    Split v'; destruct i as [ | i]; simpl; intro H.
    inversion H; trivial.
    apply IHv.
    inversion H.
    replace tv with v.
    replace (tail v') with v'0.
    assumption.
    apply (inj_pair2 nat (fun (x:nat)=>vector A x)); assumption.
    apply (inj_pair2 nat (fun (x:nat)=>vector A x)); assumption.
  Qed.

  Lemma forall_element_to_vector_pointwise : 
    forall (n : nat) (v v' : vector A n),  
      (forall (i : nat) (C : i < n), r (v[i|C]) (v'[i|C])) -> 
      vector_pointwise A r n v v'.
  Proof.
    induction v as [ | n' hv tv IHv]; intro v'.
    elim (empty v'); constructor.
    Split v'; intro Helems; constructor.
    apply (Helems 0 (lt_O_Sn n')). 
    apply IHv.
    intros i C.
    generalize (Helems (S i) (lt_n_S i n' C)); simpl.
    rewrite (element_at_irrel n' tv i C (lt_S_n i n' (lt_n_S i n' C))).
    rewrite (element_at_irrel n' (tail v') i C (lt_S_n i n' (lt_n_S i n' C))).
    trivial.
  Qed.


  Lemma does_not_belong_is_not_element : 
    forall (n : nat) (v : vector A n) (a : A),
      ~ (a INv v) -> 
      forall (i : nat) (C : i < n), v[i|C] <> a.
  Proof.
    induction v as [ | n' hv tv IHv]; intros a a_not_in_v i C.
    inversion C.
    destruct i as [ | i]; simpl.
    intro eq; apply a_not_in_v; simpl.
    left; assumption.
    apply IHv.
    intro Hin; apply a_not_in_v; right; trivial.
  Qed.


  Lemma is_not_element_does_not_belong : 
    forall (n : nat) (v : vector A n) (a : A),
      (forall (i : nat) (C : i < n), v[i|C] <> a)-> 
      ~ (a INv v).
  Proof.
    induction v as [ | n' hv tv IHv]; intros a Helems.
    simpl; unfold not; trivial.
    intro F; elim F; clear F; intro F.
    apply (Helems 0 (lt_O_Sn n')).
    simpl; trivial.
    apply (IHv a); trivial.
    clear F; intros i C F; apply (Helems (S i) (lt_n_S i n' C)).
    simpl; rewrite <- F; apply element_at_irrel; trivial.
  Qed.

  Fact element_at_0_is_head : forall (n : nat) (v : vector A (S n)), 
    head v = v[0|(lt_O_Sn n)].
  Proof.
    intros n v.
    Split v.
  Qed.

  (* strict inverse of pointwise order results : *)
  Remark SI_vector_pointwise_or_eq_imp_vector_pointwise : forall (n : nat) (v v': vector A n), 
    reflexive A r -> (forall (a a' : A), {a=a'} + {a<>a'}) -> 
    SI_vector_pointwise A r n v v' \/ v=v'->Vector_pointwise A r n v' v.
  Proof.
    intros n v v' refl_r eq_A_dec H.
    elim (eq_dec_to_list_eq_dec eq_A_dec n v v'); intro comp.
    rewrite comp; apply reflexive_vector_pointwise; assumption.
    elim H; intro case.
    elim case; intros; assumption.
    contradiction.
  Qed.

  Remark vector_pointwise_imp_SI_vector_pointwise_or_eq : forall (n : nat) (v v': vector A n), 
    reflexive A r -> (forall (a a' : A), {a=a'} + {a<>a'}) -> 
    vector_pointwise A r n v' v -> SI_vector_pointwise A r n v v' \/ v=v'.
  Proof.
    intros n v v' refl_r eq_A_dec H.
    elim (eq_dec_to_list_eq_dec eq_A_dec n v v'); intro comp.
    right; assumption.
    left; unfold inv; split; assumption.
  Qed.


  Lemma transitive_SI_vector_pointwise : forall (n : nat), 
    order A r -> (forall (a a' : A), {a=a'} + {a<>a'}) -> 
    transitive (vector A n) (SI_vector_pointwise A r n).
  Proof.
    intros n order eq_A_dec x y z Hxy Hyz.
    inversion_clear order.
    cut (SI_vector_pointwise A r n x z \/ x=z).
    intro H; elim H; clear H; intro H; [assumption | subst x].
    elim Hxy; intros H neqzy; clear H.
    elim neqzy; apply (antisymmetric_vector_pointwise ord_antisym n z y); 
      unfold Vector_pointwise; apply (SI_vector_pointwise_or_eq_imp_vector_pointwise n); try assumption.
    left; assumption.
    left; assumption.
    apply vector_pointwise_imp_SI_vector_pointwise_or_eq; try assumption.
    apply transitive_vector_pointwise with (y:=y); try assumption.
    elim Hyz; unfold inv; trivial.
    elim Hxy; unfold inv; trivial.
  Qed.


  Lemma element_at_constant_list : forall (n : nat) (a : A) (i : nat) (C : i < n),
    (constant_list n a)[i|C] = a.
  Proof.
    induction n; simpl; intros a i C.
    inversion C.
    destruct i; simpl; trivial.
  Qed.

  (* element_at_unsafe results : *)
  Lemma element_at_unsafe_to_safe : 
    forall (n : nat) (v : vector A n) (i : nat) (C : i < n) (a : A),
      v[i|_] = Some a -> v[i|C] = a.
  Proof.
    induction v as [ | n' hv tv IHv]; intros i C; [inversion C | idtac].
    destruct i; simpl.
    intros a H; inversion H; trivial.
    apply IHv.
  Qed.

  Lemma element_at_to_unsafe : 
    forall (n : nat) (v : vector A n) (i : nat) (C : i < n) (a : A),
      v[i|C] = a -> v[i|_] = Some a.
  Proof.
    induction v as [ | n' hv tv IHv]; intros i C; [inversion C | idtac].
    destruct i; simpl.
    intros a H; inversion H; trivial.
    apply IHv.
  Qed.


  Lemma element_at_unsafe_none : forall (n : nat) (v : vector A n) (i : nat), 
    v[i|_] = None -> n <= i.
  Proof.
    induction v as [ | n' hv tv IHv]; intros i H.
    auto with arith.
    destruct i.
    inversion H.
    generalize (IHv i H); auto with arith.
  Qed.


  Lemma element_at_unsafe_some : forall (n : nat) (v : vector A n) (i : nat) (a : A), 
    v[i|_] = Some a -> i < n.
  Proof.
    induction v as [ | n' hv tv IHv]; intros i a.
    intro F; inversion F.
    destruct i.
    auto with arith.
    intro H; generalize (IHv i a H); auto with arith.
  Qed.


End Vector_results.

Notation "v '[' i '|' C '->' C2 ']'" := (element_at_irrel _ _ v i C C2) (at level 50).