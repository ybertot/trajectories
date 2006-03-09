Require Import Tactic.
Require Import CAD_types.
Require Import Utils.
Require Import Setoid.
Require Import ZArith.
Require Import Even.
Require Import Pol_ring.
(*Require Import phi.*)
Require Import Mylist.
Require Import PDet.
Require Import PolMonOSum.
(* version setoid de In *)
(* on generalise lus que ca dans Myllist?*)
Fixpoint PIn(P:Pol)(l:list Pol){struct l}:Prop:=
  match l with
   |nil => False
   |b :: m => b != P \/ PIn P m
  end.



(* ca sert ca?oui*)
Add Morphism (@cons Pol)
 with signature Pol_Eq ==> Pol_list_equiv ==>Pol_list_equiv as cons_comp.
intros.
constructor;trivial.
Qed.


(* trivial lemma specifying the In predicate of st lib List*)
Lemma PIn_app :forall a l, PIn a l -> exists l1, exists l2, l *= app l1 (a::l2).
Proof with (trivial;reflexivity).
intros  a l H_In.
induction l.
elim H_In.
elim H_In;intro G.
exists (@nil Pol);exists l.
simpl;rewrite G...
elim (IHl G);intros l3 Hex.
elim Hex.
intros l4 Heq.
exists (a0:: l3).
exists l4.
simpl.
rewrite Heq...
Qed.

Lemma PIn_PIn_app_r : forall P l1, PIn P l1 -> forall l2, PIn P (app l1 l2).
Proof.
intros P;induction l1;intros H l2;elim  H;rewrite <- app_comm_cons;intro G.
left;trivial.
right.
apply (IHl1 G).
Qed.

Lemma PIn_PIn_app_l : forall P l2 l1, PIn P l1 -> PIn P (app l2 l1).
Proof.
intros P;induction l2;intros l1 H.
auto.
rewrite <- app_comm_cons.
right.
apply (IHl2 l1 H).
Qed.



Add Morphism PIn with signature Pol_Eq ==> Pol_list_equiv ==> iff as PIn_comp.
intros P Q Heq  l1 l2 Hequiv.
induction Hequiv;simpl.
reflexivity.
split;intro G;inversion G.
left.
rewrite <- H.
rewrite <- Heq;auto.
right.
rewrite <- IHHequiv;auto.
left.
rewrite  H.
rewrite  Heq;auto.
right.
rewrite  IHHequiv;auto.
Qed.



Notation "| l |":= (length l)(at level 30, no associativity).


Section DET_TRIG.

Variable phi : nat -> nat ->Pol ->Pol.


Hypothesis phi_m: forall deg n a b c d,
 phi deg n (add (scal a b) (scal c  d)) != a !* phi deg n b + c !* phi deg n d.

Add Morphism phi  with signature (@eq nat) ==>(@eq nat) ==> Pol_Eq ==> Pol_Eq as phi_Morphism.
Admitted.


(* on veut generaliser pour avoir la formule du developpement d'un  determinant triangulaire *)

Theorem det_trig : forall l l'  deg Q,
(* bloc gauche : tous les polys de l' on un degre plus petit que d - |l'| *)
 (forall P, PIn P l'-> (forall i, (1 < i)%nat -> (i <= | l |+ 1)%nat -> phi  deg i P != P0))->
 (* bloc droit : il est triangulaire*)
 (forall P, PIn P l -> (forall i j, (j < i)%nat-> (i < | l | + 1)%nat -> phi deg (S (S i)) (nth j l P) != P0))->
(* sur la diagonale auu dessus du bloc gauche il n'y a que des q*)
(forall P, PIn P l ->  (forall i, (i < | l |)%nat-> phi deg (S (S i)) (nth i l P) != Q))->
(* alors on peut developper...*)
   det phi deg (app l l') != (Pol_pow Q (N_of_nat( | l|))) * (det (fun d n => phi d (n + | l |)) deg l').
Admitted.



End DET_TRIG.