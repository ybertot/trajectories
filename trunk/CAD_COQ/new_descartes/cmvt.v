Require Import QArith List Omega ZArith pol.

(* After a use of simpl, products of positive integers are replaced by
 products of positive numbers encapsulated in a Zpos constructor.  This
 precludes uses of some theorems.  We can undo this using the following
 tactic. *)

Ltac expand_Zpos_mult := 
  repeat match goal with |- context [Zpos(?a * ?b)] => 
     change (Zpos(a*b)) with ((Zpos a)*(Zpos b))%Z
  end.

(* We want to prove a simple and contructive approximation of the
 middle value theorem: if a polynomial is negative in a and positive in b,
 and a < b, then for any positive epsilon, there exists c and d, so that 
 a <= c < d <= b, the polynomial is negative in c and positive and d,
 and the variation between c and d is less than epsilon.  To prove this,
 we use a second polynomial, obtained by taking the the absolute value
 of each coefficient.

  We will use absolute values on rational numbers, the
  absolute value is defined using a max function, called Qmax.

  We first need a host of lemmas on the type of rational numbers, which
  is rather bare. *)

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

(* This is a basic decomposition lemma, already present for most other
 numeric types. *)

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

(* Polynomial are only represented by the list of their coefficients.
  To any polynomial, we associate the absolute polynomial, whose
  coefficients are the absolute values of the initial coefficients. *)

Fixpoint Qabs_pol (l:list Q) :list Q :=
 match l with nil => nil | a::tl => Qabs a::Qabs_pol tl end.

Lemma opp_Qabs_le :  forall x, -x <= Qabs x.
intros x; unfold Qabs, Qmax; case (Qlt_le_dec x (-x)); intro; auto;
 apply Qle_refl.
Qed.

Lemma Qabs_mult : forall x y, Qabs (x * y) == Qabs x * Qabs y.
intros x y; unfold Qabs, Qmax.
destruct (Qlt_le_dec x (- x)) as [hx | hx];
destruct (Qlt_le_dec y (- y)) as [hy | hy];
destruct (Qlt_le_dec (x * y) (-(x*y))) as [hp | hp]; try ring.
assert (nx:0 < -x) by (apply lt_opp_pos; rewrite Qopp_opp; auto).
assert (ny:0 < -y) by (apply lt_opp_pos; rewrite Qopp_opp; auto).
case Qlt_not_le with (1:=hp).
assert (q : -(x*y) == x * (-y)) by ring; rewrite q; clear q.
assert (q : x*y == (-x * (-y))) by ring; rewrite q; clear q.
apply Qmult_le_compat_r; apply Qlt_le_weak; auto.
assert (nx:0 < -x) by (apply lt_opp_pos; rewrite Qopp_opp; auto).
assert (py:0 <= y) by (apply le_opp_pos; auto).
case (Qle_lt_or_eq _ _ py); intros hy'.
case Qle_not_lt with (1:=hp).
assert (q : -(x*y) == (-x) * y) by ring; rewrite q; clear q.
apply Qmult_lt_compat_r; auto.
rewrite <- hy'; ring.
assert (px:0<=x) by (apply le_opp_pos; auto).
case (Qle_lt_or_eq _ _ px); intros hx'.
case Qle_not_lt with (1:=hp).
assert (q : -(x*y) == x * (-y)) by ring; rewrite q; clear q.
repeat rewrite (Qmult_comm x); apply Qmult_lt_compat_r; auto.
rewrite <- hx'; ring.
case (Qlt_not_le _ _ hp).
assert (q : -(x*y) == (-x)*y) by ring; rewrite q; clear q.
apply Qmult_le_compat_r; auto; apply le_opp_pos; auto.
Qed.


(* The value of the absolute polynomial is always larger than the value
 of the initial polynomial. *)

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

(* A polynomial that has a negative value necessarily is not the null
 polynomial. *)

Lemma cm1 :
  forall l x y, eval_pol l x < eval_pol l y  -> exists a, l = a::(tail l).
intros l; case l.
simpl;intros x y abs; case (Qlt_not_le _ _ abs); apply Qle_refl.
intros a l' x y _; exists a; auto.
Qed.

Lemma add_exists :
  forall l1 l2, exists l', forall x, eval_pol l1 x + eval_pol l2 x ==
  eval_pol l' x.
induction l1 as [ | a l1 IHl1]; destruct l2 as [ | b l2].
exists (@nil Q); simpl; intros; ring.
exists (b::l2); simpl; intros; ring.
exists (a::l1); simpl; intros; ring.
destruct (IHl1 l2) as [l' q].
exists ((a+b)::l'); simpl; intros; rewrite <- q; ring.
Qed.

Lemma s_mult_exists :
  forall a l, exists l', forall x, a * eval_pol l x == eval_pol l' x.
intros a; induction l as [ | b l IHl]; simpl.
exists (@nil Q); simpl; intros; ring.
destruct IHl as [l' q]; exists ((a*b)::l'); simpl; intros; rewrite <- q; ring.
Qed.

Lemma mult_exists :
  forall l1 l2, exists l', forall x, eval_pol l1 x * eval_pol l2 x ==
   eval_pol l' x.
induction l1 as [ | a l1 IHl1].
exists (@nil Q); simpl; intros; ring.
simpl.
intros l2; destruct (s_mult_exists a l2) as [l2a q].
destruct (IHl1 (0::l2)) as [l1l2x q1].
destruct (add_exists l1l2x l2a) as [l' q2].
exists l'; simpl; intros.
rewrite <- q2; rewrite <- q1; rewrite <- q; simpl; ring.
Qed.

Lemma compose_exists :
  forall l a, exists l', forall x, eval_pol l x == eval_pol l' (x - a).
induction l as [ | b l IHl]; intros a; simpl.
exists (@nil Q); simpl; intros; ring.
destruct (IHl a) as [l' q].
destruct (mult_exists (a::1::nil) l') as [l2 q2].
destruct (add_exists (b::nil) l2) as [l3 q3].
exists l3; intros x; rewrite <- q3; simpl;
   rewrite <- q2; rewrite q; simpl; ring.
Qed.

Lemma Qabs_pol_pos :
  forall l x, 0 <= x -> 0 <= eval_pol (Qabs_pol l) x.
induction l; intros x px; simpl;
  [apply Qle_refl | apply Qle_trans with (0+0*x)].
ring_simplify; apply Qle_refl.
apply Qplus_le_compat; [apply Qabs_le_0 | rewrite (Qmult_comm x)].
apply Qmult_le_compat_r; auto.
Qed.

Lemma Qabs_pol_increase :
  forall l x y, 0 <= x -> x <= y ->
    eval_pol (Qabs_pol l) x <= eval_pol (Qabs_pol l) y.
induction l; intros x y px xy; simpl.
apply Qle_refl.
apply Qplus_le_compat; 
  [apply Qle_refl | apply Qle_trans with (x*eval_pol (Qabs_pol l) y)].
repeat rewrite (Qmult_comm x); apply Qmult_le_compat_r; auto.
apply Qmult_le_compat_r; auto.
apply Qabs_pol_pos; apply Qle_trans with x; auto.
Qed.

Add Morphism Qabs with signature Qeq ==> Qeq as Qabs_mor.
intros x1 x2 x1x2; unfold Qabs, Qmax; 
  destruct (Qlt_le_dec x1 (-x1)) as [hx1 | hx1];
  destruct (Qlt_le_dec x2 (-x2)) as [hx2 | hx2];
  rewrite x1x2 in hx1 |- *; intros; try apply Qeq_refl.
case Qlt_not_le with (1:= hx1); auto.
case Qlt_not_le with (1:= hx2); auto.
Qed.

Lemma cm2 :
  forall l b, exists c,
  forall x, 0 <= x -> x <= b -> Qabs (eval_pol l x - eval_pol l 0) <= c * x.
intros l b.
destruct l as [ | a l].
exists 0; simpl; intros; ring_simplify; apply Qle_refl.
simpl; exists (eval_pol (Qabs_pol l) b); intros x px xb; simpl.
match goal with |- Qabs(?v) <= _ =>
  assert (q: v == x*eval_pol l x) by ring; rewrite q
end.
rewrite Qabs_mult; rewrite (pos_Qabs x); auto; rewrite (Qmult_comm x).
apply Qmult_le_compat_r; auto.
apply Qle_trans with (2 := Qabs_pol_increase l x b px xb).
pattern x at 2; replace x with (Qabs x); [apply Qabs_pol_bound | idtac].
apply pos_Qabs; auto.
Qed.

Lemma QZ_bound : forall x:Q, 0 <= x -> exists n, x <= n#1.
intros [n d]; exists(Zdiv n (Zpos d)+1)%Z.
assert (dpos : (('d) > 0)%Z) by apply (refl_equal Gt).
unfold Qle; simpl; rewrite Zmult_1_r; rewrite Zmult_plus_distr_l.
pattern n at 1; rewrite (Z_div_mod_eq n ('d)); auto.
rewrite (Zmult_comm ('d)); apply Zplus_le_compat; auto with zarith.
rewrite Zmult_1_l; destruct (Z_mod_lt n ('d)) as [_ H2]; auto; 
apply Zlt_le_weak; apply H2.
Qed.

Lemma Qdiv_lt_0_compat : forall x y, 0 < x -> 0 < y -> 0 < x / y.
intros x [[ | p | p] d] Hx Hy; unfold Qdiv, Qinv; simpl.
unfold Qlt in Hy; simpl in Hy; elimtype False; omega.
rewrite Qmult_comm;
assert (H0 : 0 == 0 * x) by ring; rewrite H0.
apply Qmult_lt_compat_r; auto.
unfold Qlt in Hy; simpl in Hy; discriminate Hy.
Qed.

(* 
Lemma constructive_mvt :
  forall l x y, x < y -> eval_pol l x < 0 -> 0 < eval_pol l y  ->
       forall epsilon, 0 < epsilon ->
       exists x', exists y',  -epsilon < eval_pol l x' /\
         eval_pol l x' < 0 /\ 0 < eval_pol l y' /\
         eval_pol l y' < epsilon /\ x < x' /\ x' < y' /\ y' < y.
intros l a b ab nla plb.
destruct (compose_exists l a) as [l' q].
destruct (cm2 l' (b-a)) as [c pc].
intros epsilon pe; destruct (QZ_bound ((b-a)*c/epsilon)) as [n qn].
assert (alb : 0 < b -a ).
assert (d0 : 0 == a - a) by ring; rewrite d0; unfold Qminus.
repeat rewrite <- (Qplus_comm (-a)); apply Qplus_le_lt_compat; auto.
apply Qle_refl.
assert (ba:~ b-a == 0).
intros abs; case (Qlt_not_eq 0 (b-a) alb).
rewrite abs; apply Qeq_refl.
assert (pc' : 0 <= c).
assert (c': c == c * (b-a) * (1/(b-a))).
rewrite <- Qmult_assoc; rewrite Qmult_div_r; auto.
ring.
rewrite c'; clear c'.
assert (d0 : 0 == 0 *(1/(b-a))) by ring; rewrite d0; clear d0.
apply Qmult_le_compat_r.
assert (pc' := pc (b-a) (Qlt_le_weak _ _ alb) (Qle_refl _)).
apply Qle_trans with (2:= pc'); apply Qabs_le_0.
apply Qlt_le_weak; apply Qdiv_lt_0_compat; auto.
unfold Qlt; simpl; omega.
destruct (Qle_lt_or_eq _ _ pc') as [pc1 | pc1]; clear pc'; rename pc1 into pc'.
apply Qlt_le_weak; apply Qdiv_lt_0_compat; auto.
assert (q':0==0*c) by ring; rewrite q'; apply Qmult_lt_compat_r; auto.
rewrite <- pc'; unfold Qdiv; ring_simplify; apply Qle_refl.
assert (exists p:Z, eval_pol l (a + (p#1) * (epsilon/c)) < 0 /\
         (exists b', 0 < eval_pol l b' /\ b' <= a + ((p+1)#1)*(epsilon/c))).

*)