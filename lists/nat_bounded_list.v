  (***************************************************************)
  (*   This file is part of the static analyses developement -   *)
  (*   specification of kildall's algorithm, and proof it is a   *)
  (*   bytecode verifier -                                       *)
  (*							         *)
  (*   File : nat_bounded_list.v			         *)
  (*   Authors : S. Coupet-Grimal, W. Delobel		         *)
  (*   Content : instanciation of pred_list to list of natural   *)
  (*             numbers less than a certain bound               *)
  (***************************************************************)

Section nat_bounded_list.
  
  Add LoadPath "../aux".
  
  Require Export pred_list.
  (* bound : *)
  Variable n : nat.
  
  Definition P := fun (e:nat)=>lt e n.
  Definition nb_list := pred_list nat P.
  Definition nb_nil := pred_nil P.
  Definition nb_cons := pred_cons P.

  Definition nb_list_add_element := pred_list_add_element eq_nat_dec (P:=P).
  Definition nb_list_belong := pred_list_belong (P:=P).
  Definition nb_list_belong_dec := pred_list_belong_dec eq_nat_dec (P:=P).
  Definition nb_list_get_witness := pred_list_get_witness (P:=P).
  Definition nb_list_belong_add := pred_list_belong_add eq_nat_dec (P:=P).
  Definition nb_list_belong_rem := pred_list_belong_rem eq_nat_dec (P:=P).
  Definition nb_list_add_already_there := pred_list_add_already_there 
    eq_nat_dec (P:=P).
  Definition nb_list_add_already_there_added := pred_list_add_already_there_added 
    eq_nat_dec (P:=P).
  Definition nb_list_belong_added := pred_list_belong_added eq_nat_dec (P:=P).
  Definition nb_list_remove := pred_list_remove eq_nat_dec (P:=P).
  Definition nb_length := pred_length (P:=P).
  Definition nb_list_equiv := pred_list_equiv (P:=P) (Q:=P).
  Definition lt_nb_length := lt_pred_length (P:=P).

  Definition nb_list_convert (m:nat) := pred_list_convert (P:=P) (Q := fun p:nat => p<m).
  Definition nb_list_convert_equiv (m:nat) := pred_list_convert_equiv (P:=P) 
    (Q := fun p:nat => p<m).
  Definition nb_list_convert_length (m:nat) := pred_list_convert_length (P:=P) 
    (Q := fun p:nat => p<m).

  Definition nb_list_belong_convert (m:nat) := pred_list_belong_convert (P:=P) 
    (Q:=fun p:nat => p<m).
  Definition nb_list_convert_belong (m:nat) := pred_list_convert_belong (P:=P) 
    (Q:=fun p:nat => p<m).


End nat_bounded_list.

Implicit Arguments nb_nil [n].
Implicit Arguments nb_cons [n].
Implicit Arguments nb_list_add_element [n].
Implicit Arguments nb_list_belong [n].
Implicit Arguments nb_list_belong_dec [n].
Implicit Arguments nb_list_get_witness [n].
Implicit Arguments nb_list_belong_add [n].
Implicit Arguments nb_list_belong_rem [n].
Implicit Arguments nb_list_remove [n].
Implicit Arguments nb_length [n].
Implicit Arguments lt_nb_length [n].
Implicit Arguments nb_list_equiv [n].
Implicit Arguments nb_list_belong_convert [n].
Implicit Arguments nb_list_convert_belong [n].

Notation "a 'INnb' l" := (nb_list_belong l a) (at level 50).
Notation "l =nb= m" := (nb_list_equiv l m) (at level 50).

