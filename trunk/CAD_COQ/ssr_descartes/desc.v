Require Import QArith List Omega ZArith (* sos *).
Require Import ssreflect eqtype ssrbool ssrnat div fintype seq ssrfun.
Require Import bigops groups choice .
Require Export ssralg orderedalg infra pol cmvt.

(* Defining function over lists of rationals that find lists containing
  exactly one alternation, from negative to positive values. *)

Import GroupScope .
Import GRing.Theory .
Import OrderedRing.Theory.
Open Local Scope ring_scope .

Fixpoint all_zero (l:seq Qcb) : bool :=
  match l with nil => true
  | a::tl => if a == 0 then all_zero tl else false
 end.

Fixpoint all_pos_or_zero (l:seq Qcb) : bool :=
  if l is a::tl then (0 <= a) && all_pos_or_zero tl else true.


Fixpoint all_neg_or_zero (l:seq Qcb) : bool :=
  match l with nil => true
  | a::tl => if 0 < a then false else all_neg_or_zero tl
  end.

(* alternate_1 is true for lists containing at least one strictly positive
  value followed by only positive values, and preceeded by only negative
  or zero values. but negative values are not guaranteed. *)
Fixpoint alternate_1 (l:seq Qcb) : bool :=
  if l is a::tl then
     if 0 < a then all_pos_or_zero tl else alternate_1 tl
  else false.

(* alternate is true for lists that contain one negative value, followed
 by an arbitrary number of non-positive values, followed
 by one strictly positive value, followed by only non-negative values.
*)
Fixpoint alternate (l:seq Qcb) : bool :=
 match l with nil => false
 | a::tl => if a < 0 then alternate_1 tl else 
   if  a == 0 then alternate tl else false
 end.


Lemma ltr_ler_2compat0l :
  forall x y z t:Qcb, 0 <= x -> x < y ->
     0< t -> z <= t -> x * z < y * t.
Proof.
move => x y z t x0 xy t0 zt.
have m : x * t < y * t by rewrite lter_mulpr.
by apply: ler_lte_trans m; rewrite lter_mulpl.
Qed.

Lemma ler_2compat0l :
  forall x y z t:Qcb, 0 <= x -> x <= y ->
     0<= t -> z <= t -> x * z <= y * t.
Proof.
move => x y z t x0 xy t0 zt.
have m : x * t <= y * t by rewrite lter_mulpr.
by apply: ler_trans m; rewrite lter_mulpl.
Qed.

Lemma all_pos_positive : forall l, all_pos_or_zero l = true ->
  forall x, 0 <= x -> 0 <= eval_pol l x.
Proof.
move => l; elim: l; first by []. 
move => a l IHl /=; case Ha: (0 <= a) => Hl x Hx; last discriminate.
apply: lter_addpr; first by rewrite Ha.
apply: mulr_ge0pp=> //; exact: IHl.
Qed.

Lemma all_pos_increasing : forall l, all_pos_or_zero l = true ->
  forall x y, 0 <= x -> x <= y -> eval_pol l x <= eval_pol l y.
move => l; elim: l => [ | a l IHl] //=. 
case Ha : (0 <= a) => Hl x y Hx Hy; last discriminate.
have y0 : 0 <= y by apply: ler_trans Hy.
apply: lter_add; rewrite /= ?lerr //; apply: (@ler_trans _ (x * eval_pol l y)).
  by apply: lter_mulpl=> //; apply: IHl.
by apply: lter_mulpr=> //; apply: all_pos_positive.
Qed.

Definition inv (l:seq Qcb) : Prop :=
  forall epsilon, 0 < epsilon ->
    exists x,
      (forall y, 0 <= y -> y <= x -> eval_pol l y <= eval_pol l x) /\
      (forall y z, x <= y -> y <= z ->  eval_pol l y <= eval_pol l z) /\
      0 < x /\ x * eval_pol l x < epsilon.

Lemma all_pos_inv : forall l, all_pos_or_zero l = true -> inv l.
Proof.
move => l Hl eps Heps.
move: (all_pos_positive l Hl) (all_pos_increasing l Hl) => H1 H2.
move: (pol_cont (0::l) 0 _ Heps) => [x [xp lx]].
move: (cut_epsilon _ xp) => [x1 [_ [x1p [_ [_ [xx1 _]]]]]].
exists x1; split; first by move => y; apply: H2.
split; first by move => y z x1y; apply: H2; apply: ltrW (lter_le_trans _ x1y).
split; first by [].
apply: lter_abs=> /=.
have -> : x1 * eval_pol l x1 = (eval_pol (0 :: l) x1 - eval_pol (0 :: l) 0).
  by rewrite /= !add0r mul0r subr0.
apply: lx; rewrite subr0; apply: ler_lte_trans xx1=> /=.
by rewrite ger0_abs ?lerr // ltrW.
Qed.

Lemma slope_product_x :
  forall (f : Qcb -> Qcb) x kf, 0 <= x -> 0 <= kf ->
    (forall y z, x <= y -> y < z -> kf * (z - y) <= f z - f y) ->
    forall y z, x <= y -> y < z ->
     (x * kf + f y) * (z - y) <= z * f z - y * f y.
move => f x kf x0 kf0 incf y z xy yz.
rewrite -[z * _] (addrNK (z * f y)) -mulr_subr -addrA -mulr_subl mulr_addl.
set v:= f _ - _.
have xz : x < z by apply: ler_lte_trans yz.
have f1: 0 <= v.
  apply: ler_trans (incf _ _ xy yz).
  by repeat apply: mulr_ge0pp; last rewrite subr_gte0 /= ltrW.
apply: lter_add => /=.
  apply: ler_trans (_ : z * (kf * (z - y)) <= _).
    rewrite -mulrA; apply: lter_mulpr => /=.
      by apply mulr_ge0pp; last rewrite subr_gte0 /= ltrW.
    by apply: ltrW.
  apply: lter_mulpl; first by apply:ler_trans (ltrW xz). 
  by apply: incf.
by rewrite (mulrC (f y)) lerr.
Qed.

Definition inv2_internal l epsilon :=
      exists x, (forall y, 0 <= y -> y <= x -> eval_pol l y <= eval_pol l x) /\
      (forall y z, x <= y -> y <= z ->  eval_pol l y <= eval_pol l z) /\
      0 < x /\ 0 < eval_pol l x /\ x * eval_pol l x < epsilon.

Definition inv2 (l:seq Qcb) : Prop :=
  forall epsilon, 0 < epsilon -> inv2_internal l epsilon.

Lemma double_cont_pos_ltr :
  forall l1 l2 x,
     0 < eval_pol l1 x -> 0 < eval_pol l2 x ->
     exists x', x < x' /\ 0 < eval_pol l1 x' /\ 0 < eval_pol l2 x'.
Proof.
move => p1 p2 x v1 v2.
move: (pol_cont p1 x _ v1) (pol_cont p2 x _ v2) => [d1 [q1 pd1]] [d2 [q2 pd2]].
have : exists d, 0 < d /\ d <= d1 /\ d <= d2.
  case cmp: (d1 < d2).
    by exists d1; split; first done; split; first apply: lerr; apply: ltrW.
  by exists d2; split=> //; split; rewrite ?lerr //; move/negbFE: cmp.
move => [d' [dp' [dd1 dd2]]].
move: (cut_epsilon _ dp') => [d [_ [dp [_ [_ [dd' _]]]]]].
 exists (x + d).
split; first by rewrite lter_addrr.
split.
  rewrite -(lter_add2l (- eval_pol p1 (x + d) + eval_pol p1 x)) add0r addrA.
  rewrite /= addrN add0r addrC lter_abs //= absr_subC; apply: pd1.
  rewrite addrAC addrN add0r; apply: lter_le_trans dd1=> //=.
  rewrite gtr0_abs //.
rewrite -(lter_add2l (- eval_pol p2 (x + d) + eval_pol p2 x)) add0r addrA.
rewrite addrN add0r lter_abs // addrC -absr_subC.
apply: pd2; rewrite [x + _]addrC addrK ger0_abs; last by apply: ltrW.
by apply: lter_le_trans dd2.
Qed.

Lemma l5 : forall a l, a < 0 -> inv2 l -> inv2 (a::l).
move => a l aneg il. 
have aneg' := aneg; rewrite lter_opp2 oppr0 /= in aneg.
move: (il _ aneg) => /= inv_i.
move: inv_i => [x [H1 [H2 [H3 [H4 h5]]]]].
have pxn : eval_pol (a::l) x < 0.
  by rewrite /= -(addrN a) lter_add2r. 
have max_x_val : exists b, (x < b) && (-a/eval_pol l x < b).
  have p1 : forall x, x < x + 1.
    by move=> A t; rewrite lter_addrr; exact: ltr01.
  case cmp: (x < (-a/eval_pol l x)).
    exists (-a/eval_pol l x + 1); rewrite p1 andbC /=.
    by apply: lter_trans cmp _; apply: p1.
  exists (x + 1); rewrite p1 /=.
  move/negbFE:cmp=> cmp.
    by apply: ler_lte_trans cmp _; apply: p1.
move: max_x_val => [y]; move/andP => [yx val]; have yx':= ltrW yx.
have pyp: 0 < eval_pol l y.
  by apply: lter_le_trans H4 _; apply: H2; first apply: lerr.
have posval : 0 <= eval_pol (a::l) y.
  rewrite -(addrN a) /= lter_add2r /=.
  rewrite -(@ltef_mulpr _ (eval_pol l y)^-1) /=; last by rewrite invf_gte0.
  have pyn0 : eval_pol l y != 0 by rewrite eq_sym ltrWN.
  rewrite mulrK; last by [].
  apply: ltrW; apply: ler_lte_trans val.
  rewrite ltef_mulpl ?oppr_le0 //=.
  have pxp : eval_pol l x != 0 by rewrite eq_sym ltrWN.
    by apply: ltef_invpp=> //; apply: H2=> //; rewrite lerr.
move=>  epsilon Hepsilon /=.
have posval' : 0 <= eval_pol (0::a::l) y.
  rewrite /= add0r mulr_ge0pp //; apply: ltrW; apply: lter_trans  yx => //.
move: (cut_epsilon _ Hepsilon) => [e1 [e2 [He1 [He2 [s12 [e1e e2e]]]]]].
have negval' :  eval_pol (0::a::l) x < 0.
  rewrite /= add0r lter_opp2 oppr0 -mulrN /= mulr_gte0pp //=; last first.
  by rewrite -oppr0 -lter_opp2. 
move: (constructive_ivt (0::a::l) x y yx negval' posval' e1 He1) =>
  [dummy [v' [_ [_ [posv' [smallv' [xd [dv' v'y]]]]]]]].
have {xd dv'} xv' : x < v'  by apply: ler_lte_trans xd dv'.
move: posv' smallv'; rewrite /= !add0r => posv' smallv'.
have pv' : 0 < v' by apply:lter_trans xv'.
move: (pol_cont (0::a::l) v' e2 He2) => [d' [dp' pd']].
move: (cut_epsilon _ dp') => [d [_ [dp [_ [_ [dd _]]]]]].
have vvd : v' <= v' + d by rewrite lter_addrr /= ltrW.
have xvd : x <= v' + d by apply:ltrW; apply: lter_le_trans vvd.
have v'0 : 0 < v' by apply: lter_trans xv'.
have lv'd : 0 < eval_pol l (v' + d).
  by apply: lter_le_trans H4 _; apply: H2; first apply: lerr.
have pv'd0 : 0 < eval_pol (a::l) (v' + d).
  rewrite /= mulr_addl addrA; apply: lter_addpr=> /=.
    rewrite -(ltef_mulpl _ _ _ pv') /= mulr0.
    apply: (lter_trans posv')=> /=; rewrite ltef_mulpl //=.
    rewrite lter_add2r //= lter_mulpl //= ?(ltrW v'0) //; apply: H2=> //=.
    by rewrite ltrW.
    by apply: mulr_gte0pp=> //; apply: mulf_gt0pp.
exists (v' + d).
move => {y yx val yx' pyp posval posval' v'y}.
split.
  move => y y0 yvd; rewrite /= lter_add2r /=.
  case cmp: (y <= x); last first.
    apply: ler_trans (_ : y * eval_pol l (v' + d) <= _).
      by apply: lter_mulpl=> //=; apply: H2=> //; rewrite ltrW // -lerNgt cmp.
    by apply: lter_mulpr=> //=; apply: ltrW.
  apply: ler_trans (_ : y * eval_pol l x <= _).
    apply: lter_mulpl=> //=; apply: H1=> //.
  apply: lter_trans (_ : (v' + d) * eval_pol l x <= _)=> /=.
    by apply: lter_mulpr=> //=; apply: ltrW.
   apply: lter_mulpl=> //=; first by apply: lter_trans yvd.
   by apply: H2; rewrite ?lterr.
split.
  move => y z vdy yz /=; rewrite lter_add2r /=; apply: ler_2compat0l => //.
      by apply: ler_trans (ltrW pv') (ler_trans vvd vdy).
    apply: ltrW (lter_le_trans H4 _); apply: H2; first apply lerr.
    by apply: ler_trans _ (ler_trans vdy _).
  by apply: H2; first apply: ler_trans vdy.
split; first by apply: lter_le_trans _ vvd.
split; first by [].
apply: lter_le_trans s12.
apply: ler_lte_trans (_ : e1 + (v'+d)*eval_pol (a::l) (v'+d) -
                               v'*eval_pol (a::l) v' < _).
  rewrite -{1}[(v'+d)*_](addrK (v'*eval_pol (a::l) v')) {1}[(v'+d)*_ + _]addrC.
  by rewrite -!addrA ler_add2l.
rewrite -!addrA lter_add2r -[v' * _]add0r -[(v'+d) * _]add0r /=; apply: lter_abs=> /=.
by apply: pd'; rewrite [v' + _]addrC addrK  ger0_abs // ltrW.
Qed.


Lemma l4 : forall l, alternate_1 l = true -> inv2 l.
Proof.
move => l; elim: l => /= [  | a l IHl]; first by move => *; discriminate.
case a0: (0 < a).
  move => alp.
  have alp':  all_pos_or_zero (a::l) by rewrite /= ltrW.
  move => e ep; move: (all_pos_inv _ alp' _ ep) => [x [H1 [H2 [H3 H4]]]].
  exists x; split => //; split => //; split => //; split => //.
  rewrite /= lter_le_addpl // mulr_ge0pp // ?(ltrW H3) // all_pos_positive //.
  by apply: ltrW.
move/negbFE: a0; rewrite  ler_eqVlt; case/orP=> a0 alp; last first.
   by apply: l5 a0 (IHl alp).
move => e ep; move: (cut_epsilon _ ep) => [e1 [e2 [e1p [e2p [s12 [d1 d2]]]]]].
move: (IHl alp _ (ltr01 _)) => [x [H1 [H2 [H3 [H4 H5]]]]].
have e1px : 0 < e1 / x by apply: mulr_gte0pp=> //=; rewrite invf_gte0.
move: (IHl alp _ e1px) => [v [H6 [H7 [H8 [H9 H10]]]]].
without loss: v H6 H7 H8 H9 H10 / (v <= x) .
  move => gen; case xv : (x <= v).
    have H5': x * eval_pol l x < e1/x.
      apply: ler_lte_trans H10; apply: ler_2compat0l => //.
          by apply: ltrW.
        by apply: ltrW.
      by apply: H2; first apply: lerr.
    by apply: (gen x H1 H2 H3 H4 H5' (lerr _)).
  move/negbT: xv; move/ltrW => vlex.
  by apply: (gen v H6 H7 H8 H9 H10 vlex).
move => vx.
exists v; split.
  move => y y0 yx /=; rewrite lter_add2r.
  have : y * eval_pol l v <= v * eval_pol l v.
    by rewrite lter_mulpr //; apply: ltrW.
  move => tmp; apply: ler_trans tmp; rewrite lter_mulpl //.
  by apply: H6.
split.
  move => y z vy yz /=; have y0: 0 <= y by apply: ltrW (lter_le_trans H8 vy).
  rewrite lter_add2r; apply: ler_2compat0l => //.
    apply: ltrW (lter_le_trans H9 _); apply: H7; first apply: lerr.
    by apply: ler_trans yz.
  by apply: H7.
split; first by [].
rewrite /= (eqP a0) add0r; split; first by rewrite mulr_gte0pp.
apply: lter_trans d1 => /=.
apply: ler_lte_trans (_ : x * (v * eval_pol l v) < _).
  by rewrite /= ltef_mulpr //= mulr_gte0pp.
by rewrite mulrC -ltef_divpr /=.
Qed.

Lemma above_slope :
  forall (x k a: Qcb) f, 0 < k ->
    (forall y z, x <= y -> y < z -> k * (z - y) <= f z - f y) ->
    exists x':Qcb, a < f x' /\ x < x'.
Proof.
intros x k a f k0 sl.
case tst : (a <= f x).
  exists (x + 1).
  split.
    apply: ler_lte_trans tst _; rewrite -subr_gte0.
    have df : 0 < k * (x + 1 - x) by rewrite (addrC x) addrK mulr1.
    apply: lter_le_trans df _; apply:sl; first by apply:lerr.
    by rewrite lter_addrr.
  by rewrite lter_addrr.
exists (x + (a - f x)/k + 1).
set u :=  x + _.
have xu : x < u.
  rewrite /u lter_addrr; apply: mulr_gte0pp.
    by rewrite /= /OrderedRing.ltr subr_lte0 /= tst.
  by rewrite invf_gte0.
have xu1 : x < u + 1.
  by apply: lter_trans xu _; rewrite lter_addrr.
split; last by [].
  apply: ler_lte_trans (_ : f u < _).
  rewrite -[f _](addrNK (f x)).
  rewrite lter_addrA; apply: ler_trans (_ : k * (u - x) <= _).
  rewrite /u (addrC x) addrK (mulrC k) mulrVK ?lerr //.
    by apply/negP; move/eqP=>q; rewrite q lterr in k0. 
  by apply: sl; first apply: lerr.
rewrite -subr_gte0 /=.
have tmp: (u < u + 1) by rewrite lter_addrr.
have t2: 0 < k * (u + 1 - u) by apply:mulr_gte0pp => //; rewrite subr_gte0.
apply: lter_le_trans t2 _; apply: sl; last by [].
by apply: ltrW.
Qed.

Lemma desc : forall l, alternate l = true ->
  exists x1, exists k, 0 < x1 /\ 0 < k /\
   (forall x, 0 < x -> x <= x1 -> eval_pol l x < 0) /\
   (forall x y, x1 <= x -> x < y -> 
       k * (y - x) <= eval_pol l y - eval_pol l x ).
Proof.
move => l; elim: l => /= [ | a l IHl]; first by move => *; discriminate.
case: ltrP=> [aneg alt1 |apos].
  have aneg': (0 < -a) by rewrite oppr_gte0.
  move: (l4 _ alt1 _ aneg') => [x [H1 [H2 [H3 [H4 H5]]]]].
  have uv: GRing.unit (eval_pol l x)
    by apply/negP; move/eqP=> q; rewrite q lterr in H4.
  exists x; exists (eval_pol l x).
  split; first done; split; first done; split.
    move => y posy yx; rewrite -(addrN a) lter_add2r; apply: ler_lte_trans H5.
    apply ler_2compat0l => // ; first by [apply:ltrW]; first by [apply:ltrW].
    by apply H1; first apply: ltrW.
  move => y z xy yz; rewrite [a + _]addrC oppr_add addrA addrK.
  have: (x * 0 + eval_pol l y) * (z - y) <= z * eval_pol l z - y * eval_pol l y.
    apply: (slope_product_x _ x 0 (ltrW _)) => //.
    by move => t u xt tu; rewrite mul0r subr_gte0; apply: H2; last apply:ltrW.
    rewrite mulr0 add0r; apply: ler_trans; apply: lter_mulpr => /=.
       by rewrite subr_gte0 /= ltrW.
    by apply: H2 => //; first apply: lerr.
case a0 : (a == 0)=> // alt1.
move: (IHl alt1) => [v1 [k [v1pos [kpos [low incr]]]]] {IHl}.
have negval : (eval_pol l v1 < 0) by apply low; rewrite ?lterr.
set k':=k * v1 / Qcb_make 2.
have posk' : 0 < k' by repeat apply: mulr_gte0pp => //.
have [v2 [pos v1v2]] := above_slope v1 k 0 (eval_pol l) kpos incr.
move: (constructive_ivt l v1 v2 v1v2 negval (ltrW pos) _ posk') =>
  [x1 [x2 [x1close [px1neg [_ [_ [v1x1 _]]]]]]].
have x1pos : 0 < x1 by apply: lter_le_trans v1x1. 
have Plow : forall x, 0 < x -> x <= x1 -> a + x * eval_pol l x < 0.
  move=> x xpos xx1; rewrite (eqP a0) add0r; apply: mulr_lte0pn=> //.
  case: (ltrP x v1)=> xv1; first by apply: low=> //; apply: ltrW.
  apply: ler_lte_trans px1neg.
  move: xx1; rewrite ler_eqVlt; move/orP => [xx1 | xlx1];
    first by rewrite (eqP xx1) lterr.
  rewrite -subr_gte0; move: (incr _ _ xv1 xlx1); apply: ler_trans.
  by apply: mulr_ge0pp; last rewrite subr_gte0; apply: ltrW.
exists x1; exists k'; split; first done; split; first done; split; first done.
move => x y x1x xy.
rewrite [a + _]addrC oppr_add addrA addrK.
have: (v1 * k + eval_pol l x) * (y - x) <= y * eval_pol l y - x * eval_pol l x.
  by apply: slope_product_x => //; last apply: ler_trans v1x1 x1x; apply: ltrW.
apply: ler_trans.
have Hv1k2: v1*k == k*v1/Qcb_make 2 + k*v1/Qcb_make 2.
  have: Qcb_make 2 = 1 + 1 by apply/eqP.
  move=> ->; rewrite -mulr_addl [k * _]mulrC -{2 3}[v1 * _]mulr1.
  by rewrite -mulr_addr mulrK.
apply: lter_mulpr => /=; first by rewrite subr_gte0 /= ltrW.
rewrite (eqP Hv1k2) -addrA lter_addrr /= -[_ / _]opprK addrC subr_gte0 /=.
apply: ler_trans x1close _.
move: x1x; rewrite ler_eqVlt; case/orP; first by move/eqP => ->; rewrite lerr.
move => x1x; rewrite -subr_gte0 /=.
have: k * (x - x1) <= eval_pol l x - eval_pol l x1 by apply: incr.
apply : ler_trans; apply: mulr_gte0pp; first by apply: ltrW.
by rewrite subr_gte0 /= ltrW.
Qed.
