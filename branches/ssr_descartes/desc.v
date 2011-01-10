(*Require Import QArith List Omega ZArith (* sos *).*)
Require Import ssreflect eqtype ssrbool ssrnat div fintype seq ssrfun.
Require Import bigop fingroup choice .
Require Export ssralg zint orderedalg (*infra*) pol cmvt.

(* Defining function over lists of rationals that find lists containing
  exactly one alternation, from negative to positive values. *)
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope .
Import GRing.Theory .
Import OrderedRing.Theory.
Open Local Scope ring_scope .

(*
Section  ExtraPresentInBranch.

Variable Q : oIdomainType.


Lemma ler_pexp2 : forall n (x y : Q),  0 <= x -> 0 <= y 
  -> (x ^+ n.+1 <= y ^+ n.+1) = (x <= y).
Proof.
Admitted.
End ExtraPresentInBranch.
*)

Section DescOnAbstractRationals.

Variable Q : oFieldType.

Hypothesis Q_arch : forall x:Q, 0 <= x -> {n : nat | x <= n%:R}.


Definition all_zero (l : seq Q) := all (fun x => x == 0) l.

Definition all_pos_or_zero (l : seq Q) := all (fun x => 0 <= x) l.

Definition all_neg_or_zero (l : seq Q) := all (fun x => x <= 0) l.

(* alternate_1 is true for lists containing at least one strictly positive
  value followed by only positive values, and preceeded by only negative
  or zero values. but negative values are not guaranteed. *)
Fixpoint alternate_1 (l:seq Q) : bool :=
  if l is a::tl then
     if 0 < a then all_pos_or_zero tl else alternate_1 tl
  else false.

(* alternate is true for lists that contain one negative value, followed
 by an arbitrary number of non-positive values, followed
 by one strictly positive value, followed by only non-negative values.
*)
Fixpoint alternate (l:seq Q) : bool :=
 match l with nil => false
 | a::tl => if a < 0 then alternate_1 tl else 
   if  a == 0 then alternate tl else false
 end.

Lemma all_pos_positive : forall (p : {poly Q}) x,
  all_pos_or_zero p -> 0 <= x -> p.[x] >= 0.
Proof.
move=> p x h x0; rewrite horner_coef. 
apply: sumr_ge0 => [] [i his] /=.
apply: mulr_ge0; rewrite ?exprn_ge0 //; apply: (allP h); exact: mem_nth.
Qed.

Lemma all_pos_increasing : forall (l : {poly Q}), all_pos_or_zero l ->
  forall x y, 0 <= x -> x <= y -> l.[x] <= l.[y].
Proof.
move=> p posp x y le0x lexy; rewrite !horner_coef.
apply: ler_sum => [] [i ihs] /= _.
apply: ler_pmul2rW => //; first by apply: (allP posp); exact: mem_nth.
exact: ler_le_pexp2.
Qed.

Definition inv (l:seq Q) : Prop :=
  forall epsilon, 0 < epsilon ->
    exists x,
      (forall y, 0 <= y -> y <= x -> l.[y] <= l.[x]) /\
      (forall y z, x <= y -> y <= z ->  l.[y] <= l.[z]) /\
      0 < x /\ x * l.[x] < epsilon.

Lemma all_pos_inv : forall l : {poly Q}, all_pos_or_zero l -> inv l.
Proof.
move=> p posp eps peps.
case: (pol_cont ('X * p) 0 peps) => [e [ep le]].
exists (e / 2%:R); split.
- by move=> *; apply: all_pos_increasing.
have he : 0 < e / 2%:R.
(* ? *)
  by rewrite mulr_gt0 // invr_gt0; have:= (ltr0Sn Q 1).
split => //.
  move=> y ? he2; apply: all_pos_increasing => //; apply: ler_trans he2.
  by rewrite ltrW.
split => //.
have -> :  e / 2%:R * p.[e / 2%:R] = ('X * p).[e / 2%:R] - ('X * p).[0].
  by rewrite !horner_mul !hornerX mul0r subr0.
have: `|(e / 2%:R) - 0| < e.
  rewrite subr0 ger0_abs ?(ltrW he) // ltr_ipmulr // invr_lt1; last first. 
  - by have:= (ltr0Sn Q 1).
  admit (* 1 > 2 *).
by move/le; case/absr_lt.
Qed.

Lemma slope_product_x :
  forall (f : Q -> Q) x kf, 0 <= x -> 0 <= kf ->
    (forall y z, x <= y -> y < z -> kf * (z - y) <= f z - f y) ->
    forall y z, x <= y -> y < z ->
     (x * kf + f y) * (z - y) <= z * f z - y * f y.
move => f x kf x0 kf0 incf y z xy yz.
rewrite -[z * _] (addrNK (z * f y)) -mulr_subr -addrA -mulr_subl mulr_addl.
set v:= f _ - _.
have xz : x < z by apply: ler_lt_trans yz.
have f1: 0 <= v.
  apply: ler_trans (incf _ _ xy yz).
  by apply: mulr_ge0 => //; rewrite subr_ge0 ltrW.
apply: ler_add => /=.
  apply: ler_trans (_ : z * (kf * (z - y)) <= _).
    rewrite -mulrA ler_pmul2lW //; last exact: ltrW.
    by apply: mulr_ge0 => //; rewrite subr_ge0 ltrW.
  rewrite ler_pmul2rW //; first by apply: ltrW; exact: ler_lt_trans xz.
  exact: incf.
by rewrite (mulrC (f y)) lerr.
Qed.

Definition inv2_internal (l : seq Q) (epsilon : Q) :=
      exists x, (forall y, 0 <= y -> y <= x -> l.[y] <= l.[x]) /\
      (forall y z, x <= y -> y <= z ->  l.[y] <= l.[z]) /\
      0 < x /\ 0 < l.[x] /\ x * l.[x] < epsilon.

Definition inv2 l : Prop :=
  forall epsilon, 0 < epsilon -> inv2_internal l epsilon.

Lemma double_cont_pos_ltr :
  forall (l1 l2 : {poly Q}) x,
     0 < l1.[x] -> 0 < l2.[x] ->
     exists x', x < x' /\ 0 < l1.[x'] /\ 0 < l2.[x'].
Proof.
move => p1 p2 x v1 v2.
move: (pol_cont p1 x v1) (pol_cont p2 x v2) => [d1 [q1 pd1]] [d2 [q2 pd2]].
have le02 : (0 : Q) < 2%:R by have:= ltr0Sn Q 1.
have lt12 : (1 : Q) < 2%:R by admit (* 1 < 2 *).
have [d' [dp' [dd1 dd2]]] : exists d, 0 < d /\ d < d1 /\ d < d2.
  exists ((minr d1 d2) / 2%:R).
  rewrite ltr_pdivl_mulr // mul0r ltr_minr q1 q2; split => //.
  by rewrite !ltr_pdivr_mulr // !ltr_minl !ltr_epmulr /= ?orbT.
exists (x + d'); split; first by rewrite ltr_addr.
split.
- have : `|(x + d') - x| < d1 by rewrite addrAC subrr add0r gtr0_abs.
  move/pd1; case/absr_lt => h1 h2; move: h1; rewrite oppr_sub gtr_addr.
  by rewrite oppr_lt0.
- have : `|(x + d') - x| < d2 by rewrite addrAC subrr add0r gtr0_abs.
  move/pd2; case/absr_lt => h1 h2; move: h1; rewrite oppr_sub gtr_addr.
  by rewrite oppr_lt0.
Qed.

Lemma l4 : forall l : {poly Q}, alternate_1 l -> inv2 l.
Proof.
elim/poly_ind => [| p a ih]; first by rewrite /alternate_1 seq_poly0.
case sp : (size p == 0%N) => /=; rewrite -poly_cons_def polyseq_cons sp /=.
  rewrite !polyseqC; case: (ltrgtP 0 a) => ha.
  + move=> _ eps eps0; rewrite eq_sym ltrWN //=; exists (eps / (2%:R * a)) => /=; split; last split.
    * by move=> ?; rewrite !mul0r add0r lerr.
    * by move=> ? ? /=; rewrite !mul0r add0r lerr.
    * rewrite mul0r add0r ha ltr_pdivl_mulr; last by rewrite mulr_gt0 //; have:= ltr0Sn Q 1.
      rewrite mul0r; split => //; split => //.
      rewrite invf_mul -!mulrA mulVf 1?eq_sym ?ltrWN // mulr1.
      (* 1 < 2 *) admit.
   + by rewrite ltrWN //= ltrNge ltrW.
   + by rewrite -ha eqxx.
case: (ltrgtP 0 a) => ha.
+ rewrite ha => posp eps eps0; rewrite /inv2_internal /=.
  have : all_pos_or_zero (p * 'X + a%:P).
    by rewrite -poly_cons_def polyseq_cons sp /= ltrW.
  move/all_pos_inv; case/(_ eps eps0) => x [h1x [h2x [h3x h4x]]]; exists x.
  rewrite h3x; split; last split; last split => //; last split.
  * by move=> y y0 xy; move: (h1x _ y0 xy); rewrite !horner_lin_com.
  * by move=> y z xy yz; move: (h2x _ _ xy yz); rewrite !horner_lin_com.
  * apply: addr_ge0_gt0 => //; apply: mulr_ge0; last by apply: ltrW.
    by apply: all_pos_positive => //; rewrite ltrW.
  * by move: h4x; rewrite !horner_lin.
+ rewrite ltrNge (ltrW ha) /=; move/ih => il; move: (ha); rewrite -oppr_gt0.
move/il => /= [x [H1 [H2 [H3 [H4 h5]]]]].
have pxn : (p * 'X + a%:P).[x] < 0. 
  by rewrite !horner_lin mulrC -(opprK a) subr_lt0.
have max_x_val : exists b, (x < b) && (-a / p.[x] < b).
  have p1 : forall x : Q, x < x + 1 by move=> t; rewrite ltr_addr ltr01.
  case cmp: (x < (-a / p.[x])).
    exists (-a / p.[x] + 1); rewrite p1 andbC /=.
    by apply: ltr_trans cmp _; apply: p1.
  exists (x + 1); rewrite p1 /=.
  by apply: ler_lt_trans (p1 _); rewrite // lerNgt cmp.
move: max_x_val => [y]; move/andP => [yx val]; have yx':= ltrW yx.
have pyp: 0 < p.[y].
  by apply: ltr_le_trans H4 _; apply: H2; first apply: lerr.
have posval : 0 <= (p * 'X + a%:P).[y].
  rewrite !horner_lin -ler_subl_addl sub0r -ler_pdivr_mull //.
  apply: ltrW; apply: ler_lt_trans val; rewrite mulrC ler_pmul2rW ?oppr_ge0 ?(ltrW ha) //.
  (* too long *)
  rewrite -(ler_pmul2r _ _ pyp) mulfV ?ltrNW // -(ler_pmul2l _ _ H4).
  rewrite mul1r -mulrA mulVf ?ltrNW // mulr1; apply: H2 => //; exact: lerr.
move=>  epsilon Hepsilon /=.
(* have posval' : 0 <= (0::a::l) y. *)
(*   rewrite /= add0r mulr_ge0pp //; apply: ltrW; apply: lter_trans  yx => //. *)
pose e1 := epsilon / 2%:R.
(*move: (cut_epsilon _ Hepsilon) => [e1 [e2 [He1 [He2 [s12 [e1e e2e]]]]]].
have negval' :  (0::a::l) x < 0.
  rewrite /= add0r lter_opp2 oppr0 -mulrN /= mulr_gte0pp //=; last first.
  by rewrite -oppr0 -lter_opp2. *)
have He1 : 0 < e1.
  by rewrite /e1 ltr_pdivl_mulr ?mul0r //; have := (ltr0Sn Q 1%N).
have negval' : ('X * (p * 'X + a%:P)).[x] < 0.
  by rewrite !horner_lin mulr_gt0_lt0 // -(opprK a) subr_lt0 mulrC.
have posval' : 0 <= ('X * (p * 'X + a%:P)).[y].
  by rewrite horner_mul hornerX mulr_ge0 // ltrW //; apply: ltr_trans yx.
move: (constructive_ivt Q_arch yx negval' posval' He1) =>
  [dummy [v' [_ [_ [posv' [smallv' [xd [dv' v'y]]]]]]]].
have {xd dv'} xv' : x < v'  by apply: ler_lt_trans xd dv'.
move: posv' smallv'; rewrite !horner_lin => posv' smallv'.
have pv' : 0 < v' by apply: ltr_trans xv'.
move: (pol_cont ('X * (p * 'X + a%:P)) v' He1) => [d' [dp' pd']].
pose d := d' / 2%:R.
have dp : d > 0.
  by rewrite /d ltr_pdivl_mulr ?mul0r //; have := (ltr0Sn Q 1%N).
have dd' : d < d'. admit (* 1 < 2 *).
have vvd : v' < v' + d by rewrite ltr_addr /=.
have xvd : x < v' + d by apply: ltr_trans vvd.
have v'0 : 0 < v' by apply: ltr_trans xv'.
have lv'd : 0 < p.[v' + d].
  apply: ltr_le_trans H4 _; apply: H2; first by apply: lerr.
  exact: ltrW.
exists (v' + d).
move => {y yx val yx' pyp posval posval' v'y}; split.
  move => y y0 yvd; rewrite /= ler_add2l /=.  
  case cmp: (y <= x); last first.
    apply: ler_trans (_ : p.[v' + d] * y <= _).
      by apply: ler_pmul2lW => //; apply: H2 => //; rewrite ltrW // ltrNge cmp.
    by rewrite ler_pmul2rW // ltrW.
  apply: ler_trans (_ : p.[x] * y <= _).
    by rewrite ler_pmul2lW //; apply: H1.
  apply: ler_trans (_ : p.[x] * (v' + d) <= _); last first.
    rewrite ler_pmul2lW //; first exact: ler_trans yvd.
    by apply: H2 => //; rewrite ?lerr // ltrW.
  by rewrite ler_pmul2rW // ltrW.
split.
   move => y z vdy yz /=; rewrite lter_add2l. 
   apply: ler_trans (_ : _ <= p.[y] * z ) _.
     rewrite ler_pmul2rW //.
     apply: ltrW; apply: (ltr_le_trans H4 _); apply: H2; first apply lerr.
     by apply: ler_trans _ (ler_trans vdy _); rewrite ?lerr // ltrW.
   rewrite ler_pmul2lW //.
     apply: ler_trans yz; apply: ler_trans vdy; apply: ltrW.
     by apply: ltr_trans xvd.
   by apply: H2 => //; apply: ltrW; apply: ltr_le_trans vdy.
split; first by apply: ltr_trans _ vvd.
split.
  rewrite /= -(ltr_pmul2r _ _  pv') mulr0.
  apply: ler_lt_trans posv' _; rewrite ltr_pmul2r //.  
  rewrite ltr_add2l; apply: ler_lt_trans (_ : _ <= p.[v' + d] * v') _.
    rewrite ler_pmul2l // ?(ltrW vvd); apply H2; exact: ltrW.
  by rewrite ltr_pmul2r.
apply: ler_lt_trans (_ : e1 + (v' + d) * (a :: p).[v' + d] -
                               v' * (a :: p).[v'] < _).
  by rewrite [e1 + _]addrC -addrA ler_addr subr_ge0.
rewrite -!addrA /=.
have t : e1 + e1 <= epsilon. (* 1 < 2 *) admit.
apply: ltr_le_trans t; rewrite ltr_add2r.
have: `|v' + d - v'| < d' by rewrite addrAC subrr add0r gtr0_abs.
by move/pd'; rewrite !horner_lin; case/absr_lt => _.
* rewrite ha ltrr /= -ha => halt1 eps eps0.
case: ((ih halt1) _ (ltr01 _)) =>  [x [H1 [H2 [H3 [H4 H5]]]]].
have e1px : 0 < eps / x by apply: mulr_gt0=> //=; rewrite invr_gt0.
move: ((ih halt1) _ e1px) => [v [H6 [H7 [H8 [H9 H10]]]]].
without loss: v H6 H7 H8 H9 H10 / (v <= x) .
  move => gen; case xv : (x <= v).
  - have H5': x * p.[x] < eps / x.
      apply: ler_lt_trans H10. 
      have := (H2 _ _ (lerr x) xv); move/(ler_pmul2rW (ltrW H8)) => tmp.
      by apply: ler_trans tmp; rewrite ler_pmul2lW // ltrW.
    by apply: (gen x H1 H2 H3 H4 H5' (lerr _)).
  move/negbT: xv; rewrite lerNgt negbK; move/ltrW => vlex.
  by apply: (gen v H6 H7 H8 H9 H10 vlex).
move => vx; exists v; split; last split; last split => //; last split.
* move=> y y0 yv /=; rewrite ler_add2l.
  have tmp : p.[v] * y <= p.[v] * v by rewrite ler_pmul2rW // ltrW.
  by apply: ler_trans tmp; rewrite ler_pmul2lW //; apply: H6.
* move=> y z vy yz /=.
  have y0: 0 <= y by apply: ltrW (ltr_le_trans H8 vy).
  rewrite ler_add2l.
  have tmp : p.[y] * y <= p.[y] * z.
    rewrite ler_pmul2rW //; apply: ltrW.
    by apply: ltr_le_trans H9 _; apply: H7; rewrite ?lerr.
  apply: ler_trans tmp _; rewrite ler_pmul2lW //; last by apply: H7.
  by apply: ler_trans yz. 
* by rewrite /= addr0 mulr_gt0.
* rewrite /= addr0; apply: ler_lt_trans (_ : x * (p.[v] * v) < _).
    by rewrite ler_pmul2l // mulr_gt0.
  by rewrite mulrC -ltr_pdivl_mulr // mulrC.
Qed.

Lemma above_slope :
  forall (x k a: Q) f, 0 < k ->
    (forall y z, x <= y -> y < z -> k * (z - y) <= f z - f y) ->
    exists x':Q, a < f x' /\ x < x'.
Proof.
move=> x k a f k0 sl.
case tst : (a <= f x).
  exists (x + 1); split; last by rewrite ltr_addr ltr01.
  apply: ler_lt_trans tst _; rewrite -subr_gte0.
  have df : 0 < k * (x + 1 - x) by rewrite (addrC x) addrK mulr1.
  apply: ltr_le_trans df _; apply:sl; first by apply:lerr.
  by  rewrite ltr_addr ltr01.
exists (x + (a - f x)/k + 1).
set u :=  x + _.
have xu : x < u.
  rewrite /u ltr_addr mulr_gt0 // ?invr_gt0 //.
  by rewrite subr_gt0 ltrNge tst.
have xu1 : x < u + 1.
  by apply: ltr_trans xu _; rewrite ltr_addr ltr01.
split; last by [].
  apply: ler_lt_trans (_ : f u < _).
  rewrite -[f _](addrNK (f x)) -ler_subl_addl.
  apply: ler_trans (_ : k * (u - x) <= _).
    rewrite /u (addrC x) addrK (mulrC k) mulfVK ?lerr //.
    by rewrite ltrNW.
  by apply: sl; first apply: lerr.
rewrite -subr_gt0. apply: ltr_le_trans (sl _ _ _ _); rewrite ?(ltrW xu) //.
  by rewrite addrAC addrN add0r mulr1.
by rewrite ltr_addr ltr01.
Qed.

Lemma desc : forall l : {poly Q}, alternate l ->
  exists x1, exists k, 0 < x1 /\ 0 < k /\
   (forall x, 0 < x -> x <= x1 -> l.[x] < 0) /\
   (forall x y, x1 <= x -> x < y -> 
       k * (y - x) <= l.[y] - l.[x] ).
Proof.
elim/poly_ind => [| l a IHl]; first by rewrite seq_poly0.
rewrite -poly_cons_def polyseq_cons.
case sl: (size  l == 0%N) => /=.
  rewrite polyseqC; case: (a == 0) => //=.
  case: (ltrP a 0) => ha; first by rewrite ha.
  rewrite ltrNge ha /=; case: (a == 0) => //.
case: (ltrP a 0) => ha. 
  rewrite ha => alt1.
  have aneg': (0 < -a) by rewrite oppr_gt0.
  move: (l4 alt1 aneg') => [x [H1 [H2 [H3 [H4 H5]]]]].
  exists x; exists l.[x].
  do 2 (split => //); split.
    move => y posy yx; rewrite -(opprK a) subr_lt0; apply: ler_lt_trans H5.
    rewrite mulrC; apply: ler_trans (_ : y * l.[x] <= _).
      apply: ler_pmul2rW; first exact: ltrW.
      apply: H1 => //; exact: ltrW.
    apply: ler_pmul2lW => //; exact: ltrW.
  move => y z xy yz; rewrite oppr_add addrCA addrK.
  rewrite [_ + _ * _]addrC [_ * z]mulrC [_ * y]mulrC.
  have: (x * 0 + l.[y]) * (z - y) <= z * l.[z] - y * l.[y].
    apply: (@slope_product_x _ x 0 (ltrW _)) => //; first exact: lerr.
    by move => t u xt tu; rewrite mul0r subr_gte0; apply: H2; last apply:ltrW.
  rewrite mulr0 add0r; apply: ler_trans.
  apply: ler_pmul2lW; first by rewrite subr_ge0 ltrW.
  by apply: H2 => //; first apply: lerr.
rewrite ltrNge ha /=; case a0 : (a == 0) => // alt1.
move: (IHl alt1) => [v1 [k [v1pos [kpos [low incr]]]]] {IHl}.
have negval : (l.[v1] < 0) by apply low; rewrite ?lerr.
set k':=k * v1 / 2%:R.
have posk' : 0 < k'.
  by rewrite ?mulr_gt0 ?invr_gt0 //; have:= (ltr0Sn Q 1).
have [v2 [pos v1v2]] := above_slope 0 kpos incr.
move: (constructive_ivt Q_arch v1v2 negval (ltrW pos) posk') =>
  [x1 [x2 [x1close [px1neg [_ [_ [v1x1 _]]]]]]].
have x1pos : 0 < x1 by apply: ltr_le_trans v1x1. 
have Plow : forall x, 0 < x -> x <= x1 -> a + x * l.[x] < 0.
  move=> x xpos xx1; rewrite (eqP a0) add0r.
  apply: mulr_gt0_lt0 => //; case: (ltrP x v1)=> xv1; first by apply: low=> //; apply: ltrW.
  apply: ler_lt_trans px1neg.
  move: xx1; rewrite ler_eqVlt; move/orP => [xx1 | xlx1];
    first by rewrite (eqP xx1) lterr.
  rewrite -subr_gte0; move: (incr _ _ xv1 xlx1); apply: ler_trans.
  by apply: ltrW; apply: mulr_gt0 => //; rewrite subr_gt0.
exists x1; exists k'; do 2 (split => //); split.
  by move=> x x0 xx1; rewrite addrC mulrC; apply: Plow.
move => x y x1x xy.
 rewrite oppr_add addrCA addrK [_ + _ * _]addrC [_ * x]mulrC [_ * y]mulrC.
have: (v1 * k + l.[x]) * (y - x) <= y * l.[y] - x * l.[x].
  by apply: slope_product_x => //; last apply: ler_trans v1x1 x1x; apply: ltrW.
apply: ler_trans.
have Hv1k2: v1 * k == k * v1/ 2%:R + k * v1 / 2%:R.
  have e: 2%:R = 1 + 1 :>Q by rewrite -[2%N]/(1 + 1)%N natr_add.
  rewrite e -mulr_addl [k * _]mulrC -{2 3}[v1 * _]mulr1.
  rewrite -mulr_addr mulfK; first by rewrite mulrC eqxx.
  by rewrite -e (mulSn1r_eq0 Q 1).
rewrite ler_pmul2lW //; first by rewrite subr_ge0 ltrW.
rewrite (eqP Hv1k2) -addrA ler_addr /= -[_ / _]opprK addrC subr_gte0 /=.
apply: ler_trans x1close _.
move: x1x; rewrite ler_eqVlt; case/orP; first by move/eqP => ->; rewrite lerr.
move => x1x; rewrite -subr_gte0 /=.
have: k * (x - x1) <= l.[x] - l.[x1] by apply: incr.
apply : ler_trans; apply: ltrW; apply: mulr_gt0 => //.
by rewrite subr_gt0.
Qed.

End DescOnAbstractRationals.
