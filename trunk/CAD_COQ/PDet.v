Load phi.


Notation  ZCoef:=Pol.
Notation  pol:= Pol.
Notation add :=Pol_add.
Notation "a !* x" := (Pol_mul_Rat  x a )(at level 40, left associativity).

Section det.

Fixpoint rec_det (f: pol -> ZCoef) (rec:  list pol -> ZCoef)  (l1 l2:  list pol)  {struct l1}: ZCoef :=
  match l1 with
     nil =>  P0 
  | a:: l3 => f a * rec (app l2 l3)  - rec_det f rec l3 (app l2 (a::nil)) 
  end.

Variable deg:nat.

Fixpoint det_aux (n: nat) (l:  list pol) {struct n}: ZCoef :=
  match n with
    O => P1
  | S n1 => rec_det (phi deg n) (det_aux n1) l nil 
  end.

Definition det l :=  det_aux(length l) l.


Theorem rec_det_m: forall f rec a b c d l1 l2,
  (forall a b c d l, (1 + length l = length l1 + length l2)%nat ->
    rec ((add (scal a b) (scal c d)):: l) != a !* (rec (b :: l)) + c !* (rec (d :: l))) ->
  rec_det f rec l1 ((add (scal a b) (scal c d)):: l2)  != a !* rec_det f rec l1 (b :: l2) + c !* rec_det f rec  l1 (d :: l2).
intros f rec a b c d l1 l2; generalize l2; elim l1; simpl; clear l1 l2.
intros; repeat  rewrite Pmul_Rat_P0;try Pring.
intros a1 l3 Rec l2 H.
repeat (rewrite Rec || rewrite H); try Pring.
rewrite length_app; auto with arith.
intros a2 b1 c1 d1 l1.
intros H1; apply H.
rewrite H1; rewrite (fun x y => (S_to_plus_one (plus x y)));ring.
simpl; omega.
rewrite length_app; simpl.
auto with arith.
repeat rewrite Pscal_Pmul_l.
Pring.
Qed.


Theorem det_aux_m: forall n a b c d l,
  (n= 1 + length l)%nat ->  det_aux n (((add (scal a b) (scal c d))) :: l) != a !* det_aux n (b :: l) + c !* det_aux n (d :: l).
intros n; elim n; simpl; auto.
intros; discriminate.
intros n1 Rec  a b c d l H; injection H; clear H; intros H.
generalize (phi_m  deg (S n1)); intro Hphi.
simpl in Hphi.

repeat (rewrite Rec || rewrite Hphi|| rewrite rec_det_m); auto; repeat rewrite Pscal_Pmul_l;try Pring.

intros a1 b1 c1 d1 l1; simpl.
rewrite plus_0_r.
intros H1; rewrite Rec.
rewrite H; auto.
repeat rewrite Pscal_Pmul_l;try Pring.
Qed.


Theorem det_m0: forall a b c d l1, det (  cons (add (scal a b) (scal c d))  l1) != a !* det (cons b l1) + c !* det (  cons d  l1).
intros ; unfold det.
simpl length.
case ( even_odd_dec (S (length l1)));intro;
rewrite det_aux_m; auto;
simpl; repeat rewrite Pscal_Pmul_l;try Pring.
Qed.

Theorem rec_det_r: forall f rec a b  l1 l2 l3,
  (forall a b l'1 l'2, (1 + length l'1 + length l'2 = length l1 + length l2 + length l3)%nat ->
               rec (app l'2 (a :: b :: l'1)) != -  rec (app l'2  (b :: a :: l'1))) ->
  rec_det f rec l1 (app l2  (a :: b :: l3)) != - rec_det f rec l1 (app l2  (b :: a :: l3)).
intros f rec a b l1; elim l1; simpl; auto; clear l1.
 intros ; unfold P0;Pring.
constructor;cring.
intros a1 l1 Rec l2 l3 H.
assert (tmp: forall a b l4, ( app (app l2 ( a :: b :: l3))  l4) = ((app l2 (a :: b :: (app l3  l4))))).
intros; rewrite app_ass; auto;cring.
repeat rewrite tmp; simpl.
rewrite H; auto with arith.
rewrite length_app; simpl; auto with arith.
rewrite <- (plus_comm (length l3));auto with arith.
rewrite Rec.
 intros a2 b1 l'1 l'2; rewrite length_app; simpl.
rewrite (fun x => plus_comm x 1).
intros H1; apply H.
rewrite H1; auto with zarith.
Pring.
Qed.

Theorem rec_det_t: forall f rec a b  l1 l2 l3,
  (forall a b  l'1 l'2 , (1 + length l'1 + length l'2 = length l1 + length l2 + length l3)%nat -> 
rec (app l'2 (a :: b :: l'1)) != -  rec (app l'2 ( b :: a :: l'1))) ->
  rec_det f rec (app l1 (a :: b :: l2)) l3 != - rec_det f rec (app l1 (b :: a :: l2)) l3.
intros f rec a b l1; elim l1; simpl; auto; clear l1.
intros l2 l3 H.
repeat rewrite app_ass; simpl.
rewrite rec_det_r; auto; try Pring.
intros a0 b0 l'1 l'2; simpl; rewrite plus_0_r.
intros H1; apply H; auto.
intros a1 l1 Rec l2 l3 H.
assert (tmp: forall a b l4, (app (app l2(  a :: b :: l3))  l4) = ((app l2  (a :: b :: (app l3  l4))))).
intros; rewrite app_ass; auto.
repeat rewrite <- app_ass; rewrite H.
rewrite length_app; auto with zarith.
rewrite Rec; try Pring.
intros a2 b1 l'1 l'2; rewrite length_app; simpl.
rewrite (fun x => plus_comm x 1).
intros H1; apply H.
rewrite H1; auto with zarith.
Qed.

 
Theorem det_aux_t0: forall n a b  l1 l2, (n = 2 + length l1 + length l2)%nat  -> 
    det_aux n (app l1   (a :: b :: l2)) !=  - det_aux n (app l1  (b :: a :: l2)).
intros n; elim n; simpl; auto.
intros; discriminate.
intros n1 Rec a b l1 l2 H.
rewrite rec_det_t; auto; try cring.
intros a2 b1 l'1 l'2; simpl; rewrite plus_0_r.
intros H1; rewrite <- H1 in H; clear H1.
rewrite Rec; auto; try Pring.
injection H; intros; rewrite plus_comm; auto.
Pring.
Qed.

Theorem det_aux_t: forall n a b  l1 l2 l3, (n = 2 + length l1 + length l2 + length l3)%nat  -> 
    det_aux n (app l1   ( app (a :: l2) (b :: l3))) != -det_aux n (app l1  (app (b :: l2)(a :: l3))).
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
rewrite H1 ; auto; try Pring.
rewrite length_app; simpl; auto with zarith.
Qed.

Theorem det_t: forall a b l1 l2 l3, det (app l1 (app  (a :: l2)  (b :: l3))) != 
- det (app l1 (app   (b :: l2)  (a :: l3))).
intros; unfold det.
repeat rewrite length_app;simpl length.
case ( even_odd_dec ( length l1 + (S (length l2) + S (length l3))));intro;
repeat (rewrite <- det_aux_t; auto;try omega; try Pring).
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
repeat rewrite Pscal_Pmul_l;try Pring.
Qed.

Theorem det_zero: forall a l1 l2 l3, det (app l1 (app  (a :: l2)  (a :: l3))) != P0.
intros a l1 l2 l3.
case (Pmul_integral (P1+P1) (det (app l1 (app  (a :: l2) (a :: l3))))); auto.
assert (tmp: forall x, (P1 + P1)* x != x + x).
intros;Pring.
rewrite tmp; clear tmp.
assert (det (app l1 (app (a :: l2) (a :: l3))) + det (app l1 (app (a :: l2) (a :: l3))) != 
det (app l1 (app (a :: l2) (a :: l3))) + - det (app l1 (app (a :: l2) (a :: l3)))).
apply Padd_ext; [Pring| apply det_t].
rewrite H;Pring.
intros; absurd (P1 + P1 != P0 );auto; apply P2_diff_P0.
Qed.
End det.
