Require Import QArith List Omega ZArith pol.

Ltac expand_Zpos_mult := 
  repeat match goal with |- context [Zpos(?a * ?b)] => 
     change (Zpos(a*b)) with ((Zpos a)*(Zpos b))%Z
  end.

Definition Qmax (x y:Q) := if Qlt_le_dec x y then y else x.

Lemma Qmax_le_l : forall x y, x <= Qmax x y.
intros x y; unfold Qmax; case (Qlt_le_dec x y); intro; apply Qle_refl ||
  apply Qlt_le_weak; assumption.
Qed.

Lemma Qmax_le_r : forall x y, y <= Qmax x y.
intros x y; unfold Qmax; case (Qlt_le_dec x y); intro; apply Qle_refl || auto.
Qed.

Definition Qabs (x:Q) := Qmax x (-x).

Lemma Qabs_le : forall x, x <= Qabs x.
intros x; unfold Qabs, Qmax; case (Qlt_le_dec x (-x)); intro;
 apply Qle_refl || apply Qlt_le_weak; auto.
Qed.

Lemma Qplus_le_lt_compat :
  forall a b c d, a <= b -> c < d -> a + c < b + d.
intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] H1 H2.
  apply Qlt_le_trans with ((a1#a2) + (d1#d2)). 
unfold Qle, Qlt, Qplus in *; simpl in *.
repeat rewrite Zmult_plus_distr_l.
replace (a1* 'd2 * '(a2 * c2))%Z with (a1 * 'c2 * '(a2*d2))%Z.
apply Zplus_lt_compat_l.
replace (c1*'a2*'(a2*d2))%Z with  (('a2*'a2) *(c1*'d2))%Z.
replace (d1*'a2*'(a2*c2))%Z with (('a2*'a2)*(d1*'c2))%Z.
apply Zmult_lt_compat_l; auto.
compute; apply refl_equal.
replace ('(a2*c2))%Z with ('a2 *'c2)%Z by auto; ring.
replace ('(a2*d2))%Z with ('a2 *'d2)%Z by auto; ring.
replace ('(a2*d2))%Z with ('a2 *'d2)%Z by auto.
replace ('(a2*c2))%Z with ('a2 *'c2)%Z by auto; ring.
unfold Qlt, Qle, Qplus in *; simpl in *.
repeat rewrite Zmult_plus_distr_l.
replace (d1* 'b2 * '(a2 * d2))%Z with (d1 * 'a2 * '(b2*d2))%Z.
apply Zplus_le_compat_r.
replace (a1*'d2*'(b2*d2))%Z with  (('d2*'d2) *(a1*'b2))%Z.
replace (b1*'d2*'(a2*d2))%Z with (('d2*'d2)*(b1*'a2))%Z.
apply Zmult_le_compat_l; auto.
compute; intros; discriminate.
replace ('(a2*d2))%Z with ('a2 *'d2)%Z by auto; ring.
replace ('(b2*d2))%Z with ('b2 *'d2)%Z by auto; ring.
replace ('(b2*d2))%Z with ('b2 *'d2)%Z by auto.
replace ('(a2*d2))%Z with ('a2 *'d2)%Z by auto; ring.
Qed.

Lemma lt_opp_pos : forall x, -x < x -> 0 < x.
intros x ltx; assert (H02 : 0 == 0*/(2#1)) by ring;
assert (half_pos:0 < /(2#1)) by (unfold Qlt; simpl; omega).
rewrite H02.
assert (H1 : x == (x+x)*/(2#1))
  by (unfold Qeq; simpl; expand_Zpos_mult; ring); rewrite H1; clear H1.
apply Qmult_lt_compat_r; auto.
assert (H0 : 0 == x + (-x)) by ring; rewrite H0; clear H0.
apply Qplus_le_lt_compat; try apply Qle_refl; auto.
Qed.

Lemma le_opp_pos : forall x, -x <= x -> 0 <= x.
intros x lex; assert (H02 : 0 == 0*/(2#1)) by ring;
assert (half_pos:0 <= /(2#1)) by (unfold Qle; simpl; omega).
rewrite H02.
assert (H1 : x == (x+x)*/(2#1))
  by (unfold Qeq; simpl; expand_Zpos_mult; ring); rewrite H1; clear H1.
apply Qmult_le_compat_r; auto.
assert (H0 : 0 == x + (-x)) by ring; rewrite H0; clear H0.
apply Qplus_le_compat; try apply Qle_refl; auto.
Qed.

Lemma Qabs_le_0 : forall x, 0 <= Qabs x.
intros x; unfold Qabs, Qmax.
case (Qlt_le_dec x (-x));[intros xneg | intros xpos].
apply Qlt_le_weak; apply lt_opp_pos; rewrite Qopp_opp; auto.
apply le_opp_pos; auto.
Qed.

Lemma Qopp_lt_compat : forall x y, x < y -> -y < -x.
intros x y xy; rewrite <- (Qplus_0_r (-x));
 setoid_replace (-y) with (-x + (-y+x)) by ring.
setoid_replace 0 with (-y + y) by ring.
do 2 (apply Qplus_le_lt_compat; try apply Qle_refl); auto.
Qed.

Lemma pos_Qabs : forall x, 0 <= x -> Qabs x = x.
intros x xpos; unfold Qabs, Qmax; case (Qlt_le_dec x (-x)); auto.
intros xmx; assert (abs: 0 < -x) 
  by (apply lt_opp_pos; rewrite Qopp_opp; assumption).
apply Qopp_lt_compat in abs; change (-0) with 0 in abs;
 rewrite Qopp_opp in abs; apply Qlt_not_le in abs; contradiction.
Qed.

Lemma neg_Qabs : forall x, x <= 0 -> Qabs x = -x.
intros x xneg; unfold Qabs, Qmax; case (Qlt_le_dec x (-x)); auto.
intros mxx; unfold Qopp.
assert (Hx0 : x==0) by (apply Qle_antisym; auto; apply le_opp_pos; auto).
destruct x; unfold Qeq in Hx0; simpl in Hx0 |- *; rewrite Zmult_1_r in Hx0.
rewrite Hx0; simpl; auto.
Qed.

Fixpoint Qabs_pol (l:list Q) :list Q :=
 match l with nil => nil | a::tl => Qabs a::Qabs_pol tl end.

Lemma opp_Qabs_le :  forall x, -x <= Qabs x.
intros x; unfold Qabs, Qmax; case (Qlt_le_dec x (-x)); intro; auto;
 apply Qle_refl.
Qed.

Lemma Qabs_pol_bound :
  forall l x, Qabs (eval_pol l x) <= eval_pol (Qabs_pol l) (Qabs x).
induction l; intros x; simpl; unfold Qabs, Qmax.
case (Qlt_le_dec 0 (-0)); simpl; intros; apply Qle_refl.
destruct (Qlt_le_dec (a + x * eval_pol l x) (-(a+x*eval_pol l x))) as
 [test|test]; (case_eq (Qlt_le_dec a (-a)); [intros aneg ta | intros apos ta]);
(case_eq (Qlt_le_dec x (-x)); [intros xneg tx | intros xpos tx]).
rewrite Qopp_plus; apply Qplus_le_compat; try apply Qle_refl.
assert (H0 : -(x*eval_pol l x)== -x *eval_pol l x) by ring;
  rewrite H0;clear H0.
repeat rewrite (Qmult_comm (-x));apply Qmult_le_compat_r.
replace (-x) with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto).
apply Qle_trans with (Qabs (eval_pol l x)); auto.
apply Qabs_le.
replace (-x) with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto).
apply Qabs_le_0.
rewrite Qopp_plus; apply Qplus_le_compat; try apply Qle_refl.
assert (H0 : -(x*eval_pol l x)== x *-eval_pol l x) by ring;
  rewrite H0;clear H0.
repeat rewrite (Qmult_comm x);apply Qmult_le_compat_r.
set (u:=-eval_pol l x);
  replace x with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto); unfold u.
apply Qle_trans with (Qabs (eval_pol l x)); auto.
apply opp_Qabs_le.
replace x with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto).
apply Qabs_le_0.
rewrite Qopp_plus; apply Qplus_le_compat; auto.
assert (H0 : -(x*eval_pol l x)== -x *eval_pol l x) by ring;
  rewrite H0;clear H0.
repeat rewrite (Qmult_comm (-x));apply Qmult_le_compat_r.
replace (-x) with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto).
apply Qle_trans with (Qabs (eval_pol l x)); auto.
apply Qabs_le.
replace (-x) with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto).
apply Qabs_le_0.
rewrite Qopp_plus; apply Qplus_le_compat; auto.
assert (H0 : -(x*eval_pol l x)== x *-eval_pol l x) by ring;
  rewrite H0;clear H0.
repeat rewrite (Qmult_comm x);apply Qmult_le_compat_r.
set (u:=-eval_pol l x);
  replace x with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto); unfold u.
apply Qle_trans with (Qabs (eval_pol l x)); auto.
apply opp_Qabs_le.
replace x with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto);
  apply Qabs_le_0.
apply Qplus_le_compat; try (apply Qlt_le_weak; assumption).
assert (H0 : x*eval_pol l x== -x *-eval_pol l x) by ring;
  rewrite H0;clear H0.
repeat rewrite (Qmult_comm (-x));apply Qmult_le_compat_r.
replace (-x) with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto).
apply Qle_trans with (Qabs (eval_pol l x)); auto.
apply opp_Qabs_le.
replace (-x) with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto).
apply Qabs_le_0.
apply Qplus_le_compat; try (apply Qlt_le_weak; assumption).
repeat rewrite (Qmult_comm x);apply Qmult_le_compat_r.
set (u:=eval_pol l x);
  replace x with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto); unfold u.
apply Qle_trans with (Qabs (eval_pol l x)); auto.
apply Qabs_le.
replace x with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto);
  apply Qabs_le_0.
apply Qplus_le_compat; try apply Qle_refl.
assert (H0 : x*eval_pol l x== -x *-eval_pol l x) by ring;
  rewrite H0;clear H0.
repeat rewrite (Qmult_comm (-x));apply Qmult_le_compat_r.
replace (-x) with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto).
apply Qle_trans with (Qabs (eval_pol l x)); auto.
apply opp_Qabs_le.
replace (-x) with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto).
apply Qabs_le_0.
apply Qplus_le_compat; try apply Qle_refl.
repeat rewrite (Qmult_comm x);apply Qmult_le_compat_r.
set (u:=eval_pol l x);
  replace x with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto); unfold u.
apply Qle_trans with (Qabs (eval_pol l x)); auto.
apply Qabs_le.
replace x with (Qabs x) by (unfold Qabs, Qmax; rewrite tx; auto);
  apply Qabs_le_0.
Qed.

Lemma neg_opp_pos : forall x, x < 0 -> 0 < - x.
intros x; unfold Qlt, Qopp; simpl; intro; omega.
Qed.

Lemma Qabs_interval : forall x y z, x < y -> y < z ->
  Qabs y < Qmax (Qabs x) (Qabs z).
intros x y z xy yz; unfold Qabs at 1, Qmax at 1; case (Qlt_le_dec y (-y)).
intros yneg; apply Qlt_le_trans with (Qabs x); try apply Qmax_le_l.
assert (yneg': 0 < -y) by (apply lt_opp_pos; rewrite Qopp_opp; assumption).
assert (yneg'' : y < 0).
assert (H0 : 0 == y + -y) by ring; rewrite H0; clear H0.
set (u:= y + -y); 
 assert (H0 : y == y + 0) by ring; rewrite H0; clear H0; unfold u.
apply Qplus_le_lt_compat; auto; apply Qle_refl.
assert (xneg: x < 0) by (apply Qlt_trans with y; auto).
assert (xneg' : x < -x).
apply Qlt_trans with 0; auto; apply neg_opp_pos; auto.
unfold Qabs, Qmax; case (Qlt_le_dec x (-x)).
intros _; setoid_replace (-x) with ((-y + -x)+y) by ring.
set (u:= (-y+-x)+y); setoid_replace (-y) with ((-y + -x)+x) by ring;
 unfold u; clear u.
apply Qplus_le_lt_compat; try apply Qle_refl; auto.
intro; case (Qlt_not_le _ _ xneg'); auto.
intros ypos; apply le_opp_pos in ypos; 
 assert (zpos : 0 < z) by (apply Qle_lt_trans with y; auto).
apply Qlt_le_trans with (Qabs z); try apply Qmax_le_r.
rewrite pos_Qabs; auto; apply Qlt_le_weak; auto.
Qed.

Lemma cm1 :
  forall l x, eval_pol l x < 0 -> exists a, exists l', l = a::l'.
intros l; case l.
simpl;intros x abs; case (Qlt_not_le _ _ abs); apply Qle_refl.
intros a l' x _; exists a; exists l'; auto.
Qed.

(* 
Lemma cm2 :
  forall a l x y, x < y -> eval_pol l x < eval_pol l y ->
  eval_pol l y - eval_pol l x < (y - x) *
*)