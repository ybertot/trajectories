Require Import Tactic.
Load phi.


Notation  ZCoef:=Pol.
Notation  pol:= Pol.
Notation add :=Pol_add.
Notation "a !* x" := (Pol_mul_Rat  x a )(at level 40, left associativity).

Section det.
Fixpoint rec_det (f: pol -> Pol) (rec: list pol -> Pol)  (l1 l2: list pol)  {struct l1}: Pol :=
  match l1 with
    nil =>  P0 
  | a:: l3 => f a * rec (app l2 l3)  - rec_det f  rec  l3 (app l2 (a::nil)) 
  end.

Variable deg:nat.

Fixpoint det_aux (n: nat) (l: list pol) {struct n}: Pol :=
  match n with
    O => P1
  | S n1 => rec_det (phi deg n) (det_aux n1) l nil
  end.



Definition det l :=  det_aux(length l) l.

Theorem rec_det_m: forall f rec a b c d l1 l2,
  (forall a b c d l, (1 + length l = length l1 + length l2)%nat ->
    rec ((add (scal a b) (scal c d)):: l) != a !* rec (b :: l) + c !* rec (d :: l)) ->
  rec_det f rec l1 ((add (scal a b) (scal c d)):: l2)  != a !* rec_det f rec l1 (b :: l2) + c !* rec_det f rec  l1 (d :: l2).
intros f rec a b c d l1 l2; generalize l2; elim l1; simpl; clear l1 l2.

intros;Pcsimpl;setoid ring.

intros a1 l3 Rec l2 H.
repeat rewrite Pscal_Pmul_l.
repeat (rewrite Rec||rewrite H);try rewrite length_app;try omega.
intros;rewrite H.
rewrite H0.
simpl.
omega.
setoid ring.
repeat rewrite Pscal_Pmul_l.
setoid ring.
Qed.

Theorem det_aux_m: forall n a b c d l,
  (n= 1 + length l)%nat ->  det_aux n (((add (scal a b) (scal c d))) :: l) != a !* det_aux n (b :: l) + c !* det_aux n (d :: l).
intros n; elim n; simpl; auto.
intros; discriminate.
intros n1 Rec  a b c d l H; injection H; clear H; intros H.
generalize (phi_m  deg (S n1)); intro Hphi.
simpl in Hphi.


repeat (rewrite Rec || rewrite Hphi|| rewrite rec_det_m); auto; repeat rewrite Pscal_Pmul_l.
intros a1 b1 c1 d1 l1.
simpl.

rewrite plus_0_r.
intros H1; rewrite Rec.
rewrite H; auto.
repeat rewrite Pscal_Pmul_l;try setoid ring.
setoid ring.
Qed.

Theorem det_m0: forall a b c d l, det ((add (scal a b) (scal c d)) :: l) != a !* det (b :: l) + c !* det (d :: l).
intros; unfold det; rewrite det_aux_m; auto.
simpl length.

case ( even_odd_dec (S (length l)));intro;try rewrite det_aux_m;
auto;setoid ring.
Qed.

(*
il n'y avait pas besoin de Pscla_Pmul et du coup ca va plus vite

case ( even_odd_dec (S (length l1)));intro;
rewrite det_aux_m; auto;
simpl; repeat rewrite Pscal_Pmul_l;try Pring.
*)


Theorem rec_det_r: forall f rec a b  l1 l2 l3,
  (forall a b l'1 l'2, (1 + length l'1 + length l'2 = length l1 + length l2 + length l3)%nat ->
               rec (app l'2( a :: b :: l'1)) != -  rec (app l'2 ( b :: a :: l'1))) ->
  rec_det f rec l1 (app l2 ( a :: b :: l3)) != - rec_det f rec l1 (app l2 (b :: a :: l3)).
intros f rec a b l1; elim l1; simpl; auto; clear l1.

intros;constructor;setoid ring.

intros a1 l1 Rec l2 l3 H.
assert (tmp: forall a b l4, ( app (app l2 ( a :: b :: l3))  l4) = ((app l2 (a :: b :: (app l3  l4))))).

intros; rewrite app_ass; auto;setoid ring.

repeat rewrite tmp; simpl.
rewrite H; auto with arith.
rewrite length_app; simpl; auto with arith.
rewrite <- (plus_comm (length l3));auto with arith.
rewrite Rec.
 intros a2 b1 l'1 l'2; rewrite length_app; simpl.
rewrite (fun x => plus_comm x 1).
intros H1; apply H.
rewrite H1; auto with zarith.
setoid ring.
Qed.


Theorem rec_det_t: forall f rec a b  l1 l2 l3,
  (forall a b  l'1 l'2 , (1 + length l'1 + length l'2 = length l1 + length l2 + length l3)%nat -> 
rec (app l'2 (a :: b :: l'1)) != -  rec (app l'2 ( b :: a :: l'1))) ->
  rec_det f rec (app l1 (a :: b :: l2)) l3 != - rec_det f rec (app l1 (b :: a :: l2)) l3.
intros f rec a b l1; elim l1; simpl; auto; clear l1.
intros l2 l3 H.
repeat rewrite app_ass; simpl.
rewrite rec_det_r; auto.
intros a0 b0 l'1 l'2; simpl; rewrite plus_0_r.
intros H1; apply H; auto.
setoid ring.
intros a1 l1 Rec l2 l3 H.
assert (tmp: forall a b l4, (app (app l2(  a :: b :: l3))  l4) = ((app l2  (a :: b :: (app l3  l4))))).
intros; rewrite app_ass; auto.
repeat rewrite <- app_ass; rewrite H.
rewrite length_app; auto with zarith.
rewrite Rec.
intros a2 b1 l'1 l'2; rewrite length_app; simpl.
rewrite (fun x => plus_comm x 1).
intros H1; apply H.
rewrite H1; auto with zarith.
setoid ring.
Qed.

Theorem det_aux_t0: forall n a b  l1 l2, (n = 2 + length l1 + length l2)%nat  -> 
    det_aux n (app l1  (a :: b :: l2))!= - det_aux n (app l1   (b :: a :: l2)).
intros n; elim n; simpl; auto.
intros; discriminate.
intros n1 Rec a b l1 l2 H.
rewrite rec_det_t; auto.
intros a2 b1 l'1 l'2; simpl; rewrite plus_0_r.
intros H1; rewrite <- H1 in H; clear H1.

rewrite Rec; auto.

injection H; intros; rewrite plus_comm; auto.
setoid ring.
setoid ring.
Qed.

Theorem det_aux_t: forall n a b  l1 l2 l3, (n = 2 + length l1 + length l2 + length l3)%nat  -> 
    det_aux n (app l1 (app  (a :: l2)  (b :: l3))) != - det_aux n (app l1 (app   (b :: l2) ( a :: l3))).
intros n a b l1 l2; generalize a b l1; elim l2; clear a b l1 l2; simpl; auto.
intros a b l1 l2; rewrite plus_0_r; intros H1; apply det_aux_t0; auto.
intros a1 l2 Rec a2 b1 l1 l3 H.
rewrite (@det_aux_t0 n a2 a1 l1 (app l2 (b1::l3))).
rewrite length_app; simpl; auto with zarith.
assert (h1: det_aux n (app l1 (b1 :: a1 :: app l2 (a2 :: l3))) !=
- det_aux n (app l1 (a1 :: b1 :: app l2 (a2 :: l3))));
[apply det_aux_t0 with (b := a1)| rewrite h1].
rewrite length_app; simpl; auto with zarith.

generalize (Rec a2 b1 (app l1 ( a1 ::   nil)) l3); repeat rewrite app_ass; simpl.
intros H1.
rewrite H1 ; auto.

rewrite length_app; simpl; auto with zarith.
setoid ring.
Qed.

Theorem det_t: forall a b l1 l2 l3, det (app l1 (app  (a :: l2)  (b :: l3))) != 
- det (app l1 (app   (b :: l2)  (a :: l3))).
intros; unfold det.
repeat rewrite length_app;simpl length.
case ( even_odd_dec ( length l1 + (S (length l2) + S (length l3))));intro;
repeat (rewrite <- det_aux_t; auto;try omega; try setoid ring).
Qed.

Theorem det_m: forall a b c d l1 l2, 
    det (app l1  (add (scal a b) (scal c d):: l2)) != a !* det (app l1 ( b :: l2))  + c !* det ( app l1  (d :: l2)).
intros a b c d l1 l2; case l1.
simpl; apply det_m0 .
intros a1 l3.
generalize (det_t a1 (add (scal a b) (scal c d))   nil l3 l2); simpl; intros tmp; rewrite tmp; clear tmp.
rewrite det_m0.
generalize (det_t b a1   nil l3 l2); simpl; intros tmp; rewrite tmp; clear tmp.
generalize (det_t d a1   nil l3 l2); simpl; intros tmp; rewrite tmp; clear tmp.
repeat rewrite Pscal_Pmul_l;try setoid ring.
Qed.

Theorem det_zero: forall a l1 l2 l3, det (app l1 (app  (a :: l2)  (a :: l3))) != P0.
intros a l1 l2 l3.
case (Pmul_integral (P1+P1) (det (app l1 (app  (a :: l2) (a :: l3))))); auto.
assert (tmp: forall x, (P1 + P1)* x != x + x).
intros;setoid ring.
rewrite tmp; clear tmp.
assert (det (app l1 (app (a :: l2) (a :: l3))) + det (app l1 (app (a :: l2) (a :: l3))) != 
det (app l1 (app (a :: l2) (a :: l3))) + - det (app l1 (app (a :: l2) (a :: l3)))).
apply Padd_ext; [setoid ring| apply det_t].
rewrite H;setoid ring.
intros; absurd (P1 + P1 != P0 );auto; apply P2_diff_P0.
Qed.





(*

Lemma Pol_sub_c0 : forall c, Pol_subC c c0 != c.
intros;unfold Pol_subC.
case c;intros;try Pring.
constructor;cring.
constructor;[cring|Pring].
Qed.
(* We start the proof of the fact the determinant with 1 on
   the diagonal is 1 *)

Lemma Pmul_0_l : forall x : pol, P0 * x!= P0.
intro; rewrite Pmul_sym; Pring.
Qed.

Lemma Popp_opp: forall P , - - P != P.
induction P;simpl.
constructor; cring.
rewrite mkPX_PX_c.
simpl.
rewrite mkPX_PX_c.
constructor;trivial;cring.
Qed.*)

Theorem rec_det_diag: forall f rec l1 l2 a1 a2,
  (forall a, In a l1 -> f a != P0) -> f a2 != P0 ->
   rec_det f rec (app l1  (a1::a2::nil)) l2 != match even_odd_dec (length l1) with 
      left _ => (f a1) * rec (app l2 (app l1 (a2::nil)))
    | right _ => - (f a1) * rec (app l2 (app l1 ( a2::nil))) end.
intros f rec l1 l2 a1 a2; generalize l2; elim l1; clear l1 l2.
intros l2 H1 H2.
simpl.
Pcsimpl.
(*rewrite Pol_sub_c0.*)
rewrite H2;rewrite Psub_def;setoid ring.
intros a l3 Rec l2 H1 H2.
simpl rec_det.
rewrite Rec; auto with datatypes zarith.
rewrite (H1 a); auto with datatypes zarith.
rewrite app_ass.
simpl length.
case (even_odd_dec (length l3));intros.
case(even_odd_dec (S (length l3))).
intros.
inversion e0.
absurd (even (length l3));auto.
red;intros;apply (not_even_and_odd (length l3));auto.
intros;simpl;setoid ring.
case(even_odd_dec (S (length l3)));intros.
simpl;setoid ring.
inversion o0.
absurd (even(length l3));auto.
red;intros;apply (not_even_and_odd (length l3));auto.
Qed.
(*
Theorem Zpower_nat_S: forall a n, Zpower_nat a (S n) = a * Zpower_nat a n.
intros; reflexivity.
Qed.*)

Theorem list_last_element: 
  forall (A: Set) (l : list A),
  l = nil \/ exists l1, exists a1, l = (app l1 (a1 :: nil)).
intros A l; elim l; simpl; auto.
intros a1 l1 [HH | (l2, (a2, HH))]; auto; right.
exists l1; exists a1; rewrite HH; auto.
exists (a1::l2); exists a2; rewrite HH; auto.
Qed.




(*Theorem Zpower_nat_m1_square:
  forall n, Zpower_nat (-1) n * Zpower_nat (-1) n = 1.
intros n; elim n; simpl; auto.
intros n1 Rec; rewrite <- Rec; rewrite Zpower_nat_S; ring.
Qed.
*)
Theorem nth_app_l: forall (A: Set) a n (l1 l2: list A), (n < length l1)%nat -> nth n (app l1  l2) a = nth n l1 a.
intros A a n l1; generalize n; elim l1; clear n l1.
simpl; intros n l2 H;contradict H; auto with arith.
intros a1 l1 Rec n l2; case n; simpl; auto.
intros n1 H; apply Rec; auto with arith.
Qed.

Theorem nth_app_r: forall (A: Set) a n (l1 l2: list A), (length l1 <= n)%nat -> nth n (app l1 l2) a = nth (n - length l1) l2 a.
intros A a n l1; generalize n; elim l1; clear n l1.
simpl; intros n l2 H; eq_tac; auto with zarith.
intros a1 l1 Rec n l2; case n; simpl.
intros H; contradict H; auto with arith.
intros n1 H; apply Rec; auto with arith.
Qed.

Theorem in_nth_inv: forall (A: Set) (a: A) l p, (In a l) -> exists i, (i < length l)%nat /\  a = nth i l p.
intros A a l p; elim l; simpl; clear l.
intros tmp; case tmp.
intros a1 l1 Rec1 [HH1 | HH1].
exists 0%nat; auto with arith.
case Rec1; auto.
intros i (Hi1, Hi2).
exists (S i); auto with arith.
Qed.

Definition Zpolpower_nat (i:nat):= match (even_odd_dec i) with
   left _ => Pc c1
   | right _ => - (Pc c1) end.

Opaque phi.

(*Axiom Cheat : forall A:Prop, A.*)

Theorem det_aux_diag: forall l a n p,
  (forall i:nat, (1 < i)%nat -> (i <= n)%nat -> phi deg  i a != P0) -> 
  (forall (i j:nat), (j < i)%nat  -> (i < n)%nat -> phi deg (S (S i)) (nth j l p) != P0) ->
  (forall i:nat, (i < n)%nat -> (i < length l )%nat -> phi deg (S (S i)) (nth i l p) != (Zpolpower_nat  i))->
  (length l + 1 = n)%nat -> det_aux n (app l  (a :: nil)) != phi deg 1 a.
intros l a n p; generalize l; elim n;simpl;clear l n. 
intros l _ _ _ H1; rewrite plus_comm in H1; discriminate.
intros n Rec l H0 H2 H3 H4.
case (list_last_element _ l); intros H5.
rewrite H5; simpl.
replace n with 0%nat;simpl.
Pcsimpl.
(*rewrite Pol_sub_c0;rewrite Pmul_Rat_c1;setoid ring.*)
apply eq_add_S.
rewrite <- H4; rewrite H5; simpl; auto.
case H5; clear H5; intros l2 (a1, H5).
subst l.
assert (Eq0: n = (S (pred n))).
generalize H4; rewrite length_app; repeat (rewrite plus_comm; simpl); auto.
case n; simpl; auto with zarith.
assert (Eq1: pred n = (length l2)).
apply eq_add_S; apply eq_add_S.
rewrite <- Eq0; rewrite <- H4; rewrite length_app; repeat (rewrite plus_comm; simpl); auto.
rewrite app_ass;simpl.
rewrite rec_det_diag; simpl; auto with zarith.



intros a2 HH.
case (in_nth_inv _ a2 l2 p); auto.
intros i (Hi1, Hi2).
rewrite Eq0.
replace a2 with (nth i (app l2 ( a1 :: nil)) p).
apply H2; auto with arith.
rewrite Eq1; auto.
rewrite nth_app_l; auto with arith.
case (even_odd_dec (length l2));intros.

rewrite Rec; auto.

intros i j HH HH1.
rewrite <- (H2 i j); auto with arith.
rewrite  (@f_equal3 _ _ _ _ phi deg deg (S(S i)) (S(S i)) (nth j l2 p) (nth j (app l2 (a1 :: nil)) p)); auto.
setoid ring.

apply sym_equal; apply nth_app_l.
apply lt_le_trans with (1 := HH).
rewrite <- Eq1; clear Eq1; rewrite Eq0 in HH1; auto with arith.

intros i HH HH1; rewrite <- H3; auto. 
rewrite length_app; simpl; auto with arith.
rewrite  (@f_equal3 _ _ _ _ phi deg deg (S(S i)) (S(S i)) (nth i l2 p) (nth i (app l2 (a1 :: nil)) p)); auto.
setoid ring.
apply sym_equal; apply nth_app_l; auto.
apply eq_add_S; auto with arith.
rewrite <- H4; rewrite length_app; repeat (rewrite plus_comm; simpl); auto.

rewrite Eq0.
replace a1 with (nth (pred n) (app l2 (a1 :: nil)) p).
rewrite H3; auto with zarith.
rewrite Eq1.
unfold Zpolpower_nat.
case (even_odd_dec (length l2));intros.
apply Pmul_1_l.
elim  (not_even_and_odd (length l2));trivial.
rewrite nth_app_r.
rewrite Eq1; rewrite <- minus_n_n; auto.
rewrite Eq1; auto with arith.



rewrite Rec; auto.

intros i j HH HH1.
rewrite <- (H2 i j); auto with arith.
rewrite  (@f_equal3 _ _ _ _ phi deg deg (S(S i)) (S(S i)) (nth j l2 p) (nth j (app l2 (a1 :: nil)) p)); auto.
setoid ring.

apply sym_equal; apply nth_app_l.
apply lt_le_trans with (1 := HH).
rewrite <- Eq1; clear Eq1; rewrite Eq0 in HH1; auto with arith.

intros i HH HH1; rewrite <- H3; auto. 
rewrite length_app; simpl; auto with arith.
rewrite  (@f_equal3 _ _ _ _ phi deg deg (S(S i)) (S(S i)) (nth i l2 p) (nth i (app l2 (a1 :: nil)) p)); auto.
setoid ring.
apply sym_equal; apply nth_app_l; auto.
apply eq_add_S; auto with arith.
rewrite <- H4; rewrite length_app; repeat (rewrite plus_comm; simpl); auto.

rewrite Eq0.
replace a1 with (nth (pred n) (app l2 (a1 :: nil)) p).
rewrite H3; auto with zarith.
rewrite Eq1.
unfold Zpolpower_nat.
case (even_odd_dec (length l2));intros.
elim  (not_even_and_odd (length l2));trivial.
setoid ring.
(*rewrite Popp_opp.
apply Pmul_1_l.*)
rewrite nth_app_r.
rewrite Eq1; rewrite <- minus_n_n; auto.
rewrite Eq1; auto with arith.
Qed.

Theorem det_diag: forall l a p,
  (forall i, (1 < i)%nat -> (i <= length l + 1)%nat -> phi  deg i a != P0)-> 
  (forall i j, (j < i)%nat-> (i < length l + 1)%nat -> phi deg (S (S i)) (nth j l p) != P0)->
  (forall i, (i < length l )%nat-> phi deg (S (S i)) (nth i l p) != (Zpolpower_nat i))->
   det (app l ( a :: nil)) != phi deg 1 a.
intros l a p H2 H3 H4.
unfold det; rewrite length_app.
apply det_aux_diag with p; simpl; auto with arith.
Qed.









End det.



