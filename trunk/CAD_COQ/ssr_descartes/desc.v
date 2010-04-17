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
  match l with nil => true
  | a::tl => if a < 0 then false else all_pos_or_zero tl
  end.

Fixpoint all_neg_or_zero (l:seq Qcb) : bool :=
  match l with nil => true
  | a::tl => if 0 < a then false else all_neg_or_zero tl
  end.

(* alternate_1 is true for lists containing at least one strictly positive
  value followed by only positive values, and preceeded by only negative
  or zero values. but negative values are not guaranteed. *)
Fixpoint alternate_1 (l:seq Qcb) : bool :=
  match l with nil => false
  | a::tl => if 0 < a then all_pos_or_zero tl else alternate_1 tl
  end.

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
have m : x * t < y * t by rewrite ltf_mulpr.
by apply: ler_lt_trans m; rewrite ler_mulpl.
Qed.

Lemma ler_2compat0l :
  forall x y z t:Qcb, 0 <= x -> x <= y ->
     0<= t -> z <= t -> x * z <= y * t.
Proof.
move => x y z t x0 xy t0 zt.
have m : x * t <= y * t by rewrite ler_mulpr.
by apply: ler_trans m; rewrite ler_mulpl.
Qed.

Lemma ltr_mul2C : forall  x y z t:Qcb, (x * y < z * t) = (y * x < t * z).
by move => x y z t; rewrite [x * _]mulrC [z * _]mulrC.
Qed.

Lemma alternate1_decompose :
  forall l, alternate_1 l = true ->
    (exists l1, exists l2, exists l3, exists a, exists b,
      l = l1 ++ a::l2 ++ b::l3 /\
      all_neg_or_zero l1 = true /\ a < 0 /\ all_zero l2 = true /\ 0 < b /\
      all_pos_or_zero l3 = true) \/
    exists l2, exists l3, exists b,
      l = l2++b::l3 /\
      all_zero l2 = true /\ 0 < b /\ all_pos_or_zero l3 = true.
Proof.
move => l; elim: l;[ move => al; discriminate | move => /= a l IHl].
case cmp: (0 < a) => h; first by right; exists [::]; exists l; exists a => //.
move: (IHl h) => [[l1 [l2 [l3 [a' [b [H1 [H2 [H3 [H4 [H5 H6]]]]]]]]]] |
                  [l2 [l3 [b [H1 [H2 [H3 H4]]]]]]] {IHl h}.
  left; exists (a::l1); exists l2; exists l3; exists a'; exists b.
  by rewrite H1 /= cmp.
case Ha1: (a == 0).
  by right; exists (a::l2); exists l3; exists b; rewrite H1 /= Ha1.
left; exists [::]; exists l2; exists l3; exists a; exists b.
have tmp: a < 0 by move/negbFE: cmp; rewrite  ler_eqVlt Ha1.
by rewrite H1; repeat split; done.
Qed.

Lemma l1 : forall l, all_pos_or_zero l = true ->
  forall x, 0 <= x -> 0 <= eval_pol l x.
Proof.
move => l; elim: l; first by []. 
move => a l IHl /=; case Ha: (a < 0) => Hl x Hx; first discriminate.
apply: ler_addpr; last by move/negbFE: Ha.
by apply: mulr_ge0pp; last apply: IHl.
Qed.

Lemma l2 : forall l, all_pos_or_zero l = true ->
  forall x y, 0 <= x -> x <= y -> eval_pol l x <= eval_pol l y.
move => l; elim: l => [ | a l IHl] //=. 
case Ha : (a < 0) => Hl x y Hx Hy; first discriminate.
have y0 : 0 <= y by apply: ler_trans Hy.
apply: ler_add; rewrite ?lerr //; apply: (@ler_trans _ (x * eval_pol l y)).
  by apply: ler_mulpl=> //; apply: IHl.
by apply: ler_mulpr=> //; apply: l1.
Qed.

Definition inv (l:seq Qcb) : Prop :=
  forall epsilon, 0 < epsilon ->
    exists x,
      (forall y, 0 <= y -> y <= x -> eval_pol l y <= eval_pol l x) /\
      (forall y z, x <= y -> y <= z ->  eval_pol l y <= eval_pol l z) /\
      0 <= x /\ x * eval_pol l x < epsilon.

Lemma l3 : forall l, all_pos_or_zero l = true -> inv l.
Proof.
move => l Hl eps Heps; move: (l1 l Hl) (l2 l Hl) => H1 H2.
move: (pol_cont (0::l) 0 _ Heps) => [x [xp lx]].
move: (cut_epsilon _ xp) => [x1 [_ [x1p [_ [_ [xx1 _]]]]]].
exists x1; split; first by move => y; apply: H2.
split; first by move => y z x1y; apply: H2; apply: ltrW (ltr_le_trans _ x1y).
split; first by apply: ltrW.
suff: |x1 * eval_pol l x1| < eps by rewrite absr_lt ?(ltrW Heps) //; case/andP.
have -> : x1 * eval_pol l x1 = (eval_pol (0 :: l) x1 - eval_pol (0 :: l) 0).
  by rewrite /= !add0r mul0r subr0.
apply: lx; rewrite subr0 absr_lt ?(ltrW xp) // xx1 andbT; apply: ltr_trans x1p.
by rewrite oppr_ge0.
Qed.

Definition inv2_internal l epsilon P :=
      exists x, (forall y, 0 <= y -> y <= x -> eval_pol l y <= eval_pol l x) /\
      (forall y z, x <= y -> y <= z ->  eval_pol l y <= eval_pol l z) /\
      P x /\ 0 < eval_pol l x /\ x * eval_pol l x < epsilon.

Definition inv2 (l:seq Qcb) : Prop :=
  forall epsilon, 0 < epsilon -> inv2_internal l epsilon (<=%R 0).

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
split; first by rewrite ler_addlr.
split.
  rewrite -(ler_add2l (- eval_pol p1 (x + d) + eval_pol p1 x)) add0r addrA.
  rewrite addrN add0r ltr_abs // addrC -absr_subC.
  apply: pd1; rewrite [x + _]addrC addrK ger0_abs; last by apply: ltrW.
  by apply: ltr_le_trans dd1.
rewrite -(ler_add2l (- eval_pol p2 (x + d) + eval_pol p2 x)) add0r addrA.
rewrite addrN add0r ltr_abs // addrC -absr_subC.
apply: pd2; rewrite [x + _]addrC addrK ger0_abs; last by apply: ltrW.
by apply: ltr_le_trans dd2.
Qed.

Lemma inv2_shift : forall l epsilon, 0 < epsilon ->
  inv2_internal l epsilon (<=%R 0) -> inv2_internal l epsilon (fun x => 0 < x).
Proof.
move => l epsilon Hepsilon [x [H1 [H2 [H3 [H4 H5]]]]].
move: (s_mult_pol (-1) l) => [l' pl'].
have t: 0 < eval_pol (epsilon::l') x.
  by rewrite /= -pl' -(addrN epsilon) mulNr mul1r mulrN ler_add2r -ler_opp2.
move: (double_cont_pos_ltr _ _ _ H4 t) => {H4 H5}[x' [xx' [H4' H5']]].
rewrite /= -pl' -(addrN epsilon) mulNr mul1r mulrN ler_add2r -ler_opp2 in H5'.
have {H1} H1': forall y, 0 <= y -> y <= x' -> eval_pol l y <= eval_pol l x'.
  move => y y0 yx'.
  case cmp: (y <= x); last (move/negbT: cmp; move/ltrW=>cmp).
    apply: ler_trans (_ : eval_pol l x <= _); first by apply: H1.
    by apply: H2; first apply: lerr; apply:ltrW.
  by apply: H2.
have {H2}H2':= fun y z h h' => H2 y z (ltrW(ltr_le_trans xx' h)) h'.
exists x'; split; first exact H1'; split; first exact H2'.
by split => //; apply: ler_lt_trans xx'.
Qed.

Lemma l5 : forall a l, a < 0 -> inv2 l -> inv2 (a::l).
move => a l aneg il. 
have aneg' := aneg; rewrite ler_opp2 oppr0 in aneg.
move: (il _ aneg) => inv_i.
move: (inv2_shift l _ aneg inv_i) => [x [H1 [H2 [H3 [H4 H5]]]]].
have pxn : eval_pol (a::l) x < 0.
  by rewrite /= -(addrN a) ler_add2r. 
have max_x_val : exists b, (x < b) && (-a/eval_pol l x < b).
  have p1 : forall x, x < x + 1.
    by move=> A x0; rewrite -{2}(addr0 x0) ler_add2r ltr01.
  case cmp: (x < (-a/eval_pol l x)).
    exists (-a/eval_pol l x + 1); rewrite p1 andbC /=.
    by apply: ltr_trans cmp _; apply: p1.
  exists (x + 1); rewrite p1 /=.
  move/negbFE:cmp=> cmp.
    by apply: ler_lt_trans cmp _; apply: p1.
move: max_x_val => [y]; move/andP => [yx val]; have yx':= ltrW yx.
have pyp: 0 < eval_pol l y.
  by apply: ltr_le_trans H4 _; apply: H2; first apply: lerr.
have posval : 0 <= eval_pol (a::l) y.
  rewrite -(addrN a) /= ler_add2r.
  rewrite -(@ltf_mulpr _ (eval_pol l y)^-1); last by rewrite -invf_le0.
  have pyn0 : eval_pol l y != 0.
    by apply/negP; move/eqP => q; rewrite q lerr in pyp. 
  rewrite mulrK; last by [].
  apply: ltrW; apply: ler_lt_trans val.
  rewrite ltf_mulpl ?oppr_le0 //.
  have pxp : eval_pol l x != 0.
    by apply/negP; move/eqP => q; rewrite q lerr in H4.
  by apply: lef_invpp=> //; apply: H2=> //; rewrite lerr.
move=>  epsilon Hepsilon.
have posval' : 0 <= eval_pol (0::a::l) y.
  rewrite /= add0r mulr_ge0pp //; apply: ltrW; apply: ltr_trans  yx => //.
move: (cut_epsilon _ Hepsilon) => [e1 [e2 [He1 [He2 [s12 [e1e e2e]]]]]].
have negval' :  eval_pol (0::a::l) x < 0.
  rewrite /= add0r ler_opp2 oppr0 -mulrN mulf_gt0pp //; last first.
  by rewrite -oppr0 -ler_opp2. 
move: (constructive_mvt (0::a::l) x y yx negval' posval' e1 He1) =>
  [dummy [v' [_ [_ [posv' [smallv' [xd [dv' v'y]]]]]]]].
have {xd dv'} xv' : x < v'  by apply: ler_lt_trans xd dv'.
move: posv' smallv'; rewrite /= !add0r => posv' smallv'.
have pv' : 0 < v' by apply:ltr_trans xv'.
move: (pol_cont (0::a::l) v' e2 He2) => [d' [dp' pd']].
move: (cut_epsilon _ dp') => [d [_ [dp [_ [_ [dd _]]]]]].
have vvd : v' <= v' + d by rewrite ler_addrr ltrW.
have xvd : x <= v' + d by apply:ltrW; apply: ltr_le_trans vvd.
have v'0 : 0 < v' by apply: ltr_trans xv'.
have lv'd : 0 < eval_pol l (v' + d).
  by apply: ltr_le_trans H4 _; apply: H2; first apply: lerr.
have pv'd0 : 0 < eval_pol (a::l) (v' + d).
  rewrite -(ltf_mulpl _ _ pv') mulr0 /=  mulr_addl addrA mulr_addr.
  apply: ltr_addpr.
    apply: ler_trans posv' _.
    rewrite ltf_mulpl // ler_add2r ltf_mulpl //; apply: H2=> //.
    by apply: ltrW.
  by apply: mulf_gt0pp=> //; apply: mulf_gt0pp.
exists (v' + d).
move => {y yx val yx' pyp posval posval' v'y}.
split.
  move => y y0 yvd.
  case cmp: (y <= x); last (move/negbT: cmp => cmp).
    apply: ler_trans (_ : eval_pol (a::l) x <= _).
      rewrite /= ler_add2r; apply: ler_2compat0l=> //; first by apply: ltrW.
      exact: H1.
    rewrite /= ler_add2r; apply: ler_2compat0l => //; first by apply: ltrW.
      by apply:ltrW.
    by apply: H2; first apply: lerr.
  rewrite /= ler_add2r; apply: ler_2compat0l => //.
    by apply: ltrW.
  by apply: H2; first apply:ltrW.
split.
  move => y z vdy yz /=; rewrite ler_add2r; apply: ler_2compat0l => //.
      by apply: ler_trans (ltrW pv') (ler_trans vvd vdy).
    apply: ltrW (ltr_le_trans H4 _); apply: H2; first apply lerr.
    by apply: ler_trans _ (ler_trans vdy _).
  by apply: H2; first apply: ler_trans vdy.
split; first by apply: ltrW (ltr_le_trans _ vvd).
split; first by [].
apply: ltr_le_trans s12.
apply: ler_lt_trans (_ : e1 + (v'+d)*eval_pol (a::l) (v'+d) -
                               v'*eval_pol (a::l) v' < _).
  rewrite -{1}[(v'+d)*_](addrK (v'*eval_pol (a::l) v')) {1}[(v'+d)*_ + _]addrC.
  by rewrite -!addrA ler_add2l.
rewrite -!addrA ler_add2r -[v' * _]add0r -[(v'+d) * _]add0r; apply: ltr_abs.
by apply: pd'; rewrite [v' + _]addrC addrK  ger0_abs // ltrW.
Qed.


Lemma l4 : forall l, alternate_1 l = true -> inv2 l.
Proof.
move => l; elim: l => /= [  | a l IHl]; first by move => *; discriminate.
case a0: (0 < a).
  move => alp; have alp':  all_pos_or_zero (a::l) by rewrite /= ltrW.
  move => e ep; move: (l3 _ alp' _ ep) => [x [H1 [H2 [H3 H4]]]].
  exists x; split => //; split => //; split => //; split => //.
  by rewrite /= ltr_le_addpl // mulr_ge0pp // l1.
move/negbFE: a0; rewrite  ler_eqVlt; case/orP=> a0 alp; last first.
   by apply: l5 a0 (IHl alp).
move => e ep; move: (cut_epsilon _ ep) => [e1 [e2 [e1p [e2p [s12 [d1 d2]]]]]].
move: (IHl alp _ (ltr01 _)) => inv_i.
move: (inv2_shift _ _ (ltr01 _) inv_i) => [x [H1 [H2 [H3 [H4 H5]]]]].
have e1px : 0 < e1/x by apply: mulf_gt0pp=> //; rewrite -invf_le0.
move: (IHl alp _ e1px) => inv_i'.
move: (inv2_shift _ _ e1px inv_i') => [v [H6 [H7 [H8 [H9 H10]]]]].
without loss: v H6 H7 H8 H9 H10 / (v <= x) .
  move => gen; case xv : (x <= v).
    have H5': x * eval_pol l x < e1/x.
      apply: ler_lt_trans H10; apply: ler_2compat0l => //.
          by apply: ltrW.
        by apply: ltrW.
      by apply: H2; first apply: lerr.
    by apply: (gen x H1 H2 H3 H4 H5' (lerr _)).
  move/negbT: xv; move/ltrW => vlex.
  by apply: (gen v H6 H7 H8 H9 H10 vlex).
move => vx.
exists v; split.
  move => y y0 yx /=; rewrite ler_add2r.
  have : y * eval_pol l v <= v * eval_pol l v.
    by rewrite ler_mulpr //; apply: ltrW.
  move => tmp; apply: ler_trans tmp; rewrite ler_mulpl //.
  by apply: H6.
split.
  move => y z vy yz /=; have y0: 0 <= y by apply: ltrW (ltr_le_trans H8 vy).
  rewrite ler_add2r; apply: ler_2compat0l => //.
    apply: ltrW (ltr_le_trans H9 _); apply: H7; first apply: lerr.
    by apply: ler_trans yz.
  by apply: H7.
split; first by apply: ltrW.
rewrite /= (eqP a0) add0r; split; first by rewrite mulf_gt0pp.
apply: ltr_trans d1.
have u:  0 < v^-1 by rewrite -invf_le0.
have uv: GRing.unit v by apply/negP; move/eqP => q;rewrite q lerr in H8.
rewrite -(ltf_mulpr _ _ u); rewrite [v * _]mulrC mulrK //.
apply: ltr_le_trans H10 _; rewrite ler_mulpl //; first by apply:ltrW.
have xv0 : 0 < x * v by apply: mulf_gt0pp.
have ux: GRing.unit x by apply/negP; move/eqP => q; rewrite q lerr in H3.
by rewrite lef_invpp.
Qed.

Lemma desc : forall l, alternate l = true ->
  exists x1, exists x2, exists k, 0 < x1 /\ x1 < x2 /\ 0 < k /\
   (forall x, 0 < x -> x <= x1 -> eval_pol l x < 0) /\
   (forall x y, x1 <= x -> x < y -> 
       k * (y - x) <= eval_pol l y - eval_pol l x ) /\ 
  0 < eval_pol l x2.
Proof.
move => l; elim: l => /= [ | a l IHl]; first by move => *; discriminate.
case aneg: (a < 0) => alt1;
   last (move/negbT: aneg; rewrite -ltrNge => apos).
  have aneg': (0 < -a) by rewrite -oppr0 -ler_opp2.
  move: (l4 _ alt1 _ aneg') => inv_i.
  move: (inv2_shift _ _ aneg' inv_i) => [x1 [H1 [H2 [H3 [H4 H5]]]]].
  have uv: GRing.unit (eval_pol l x1)
    by apply/negP; move/eqP=> q; rewrite q lerr in H4.
  exists x1.
  have [x2 [x1x2 vx2]]: exists x2, x1 <= x2 /\ -a/eval_pol l x1 + 1 <= x2.
    case vx1: (-a/eval_pol l x1 + 1 < x1); last  move/negbFE: vx1 => vx1.
      by exists x1; rewrite lerr ltrW.
     by exists (-a/eval_pol l x1 + 1); rewrite lerr; split.
  have x1x2': x1 < x2.
    apply: ltr_le_trans vx2; rewrite ltr_addspr //.
    by rewrite -(ltf_mulpr _ _ H4); rewrite mulrVK.
  exists x2; exists (eval_pol l x1).
  split; first done; split; first done; split; first done.
  split.
    move => x posx xx1; rewrite -(addrN a) ler_add2r; apply: ler_lt_trans H5.
    apply ler_2compat0l => // ; first apply:ltrW => //; first apply:ltrW => //.
    by apply H1; first apply: ltrW.
  split.
    move => x y x1x xy; rewrite [a + _]addrC oppr_add addrA addrK.
    have y0: 0 <= y
      by apply: ler_trans (ltrW xy); apply: ler_trans (ltrW H3) x1x.
    apply: (@ler_trans _ (y * eval_pol l x - x * eval_pol l x)); last first.
      by rewrite ler_add2l ler_mulpl //; apply: H2=> //; apply: ltrW.
    rewrite -(mulNr x) -mulr_addl [(y - x) * _]mulrC.
    rewrite ler_mulpr //; first by rewrite -(addrN x) ler_add2l ltrW.
    by apply: H2; first apply: lerr.
  have vx2' : x2 * eval_pol l x1 <= x2 * eval_pol l x2.
    rewrite ler_mulpl //; first by apply: ltrW; apply: ltr_trans x1x2'.
    by apply: H2; first apply lerr; last apply: ltrW.
    rewrite -(addrN a) ler_add2r.
  apply: ltr_le_trans (_ : x2 * eval_pol l x1 <= _); last by [].
  have t: 0 < (eval_pol l x1)^-1 by rewrite -invf_le0.
  rewrite -(ltf_mulpr _ _ t); rewrite mulrK //; apply: ltr_le_trans vx2.
  by rewrite ler_addlr.
case a0 : (a == 0); rewrite a0 in alt1 => //.
move: (IHl alt1) => [v1 [v2 [k [v1pos [v1v2 [kpos [low [incr pos]]]]]]]] {IHl}.
have negval : (eval_pol l v1 < 0) by apply low; rewrite ?lerr.
have v2pos : (0 < v2) by apply: ltr_trans v1v2.
have epsv2 : (0 < k * v1 / Qcb_make 2). 
  apply: mulf_gt0pp; last  by rewrite -invf_le0.
  by apply: mulf_gt0pp.
move: (constructive_mvt l v1 v2 v1v2 negval (ltrW pos) _ epsv2) =>
  [x1 [x2 [x1close [px1neg [px2pos [px2close [v1x1 [x1x2 x2v2]]]]]]]].
set k':=k * v1 / Qcb_make 2.
have x1pos : 0 < x1 by apply: ltr_le_trans v1x1. 
have Plow : forall x, 0 < x -> x <= x1 -> a + x * eval_pol l x < 0.
  move=> x xpos xx1; rewrite (eqP a0) add0r; apply: mulf_lt0pn=> //.
  case: (ltrP x v1)=> xv1; first by apply: low=> //; apply: ltrW.
  rewrite -/k' in x1close.
  apply: ler_lt_trans px1neg.
  rewrite ler_eqVlt in xx1; move/orP: xx1 => [xx1 | xlx1]; last first.
    have t:= incr _ _ xv1 xlx1.
    rewrite -(@ler_add2l _ (-eval_pol l x)) addrN; apply: ler_trans t.
    apply: mulr_ge0pp; first by apply: ltrW.
    by rewrite subr_ge0; apply: ltrW.
  by rewrite (eqP xx1) lerr.
exists x1; exists v2; exists k'; split; first done; split.
  case x1v2: (x1 < v2); first by [].
  have u: 0 < a + v2 * eval_pol l v2.
    by rewrite (eqP a0) add0r mulf_gt0pp.
  have t : (0:Qcb) < 0.
    apply:ltr_trans u _; apply: Plow => //.
    by move/negbT: x1v2; rewrite ltrNge.
  by rewrite lerr in t.
split; first done; split; first done; split.
  move => x y x1x xy.
  rewrite [a + _]addrC oppr_add addrA addrK -mulrN -[-eval_pol l x]add0r
    -(addNr (eval_pol l y)) -addrA [x * _]mulr_addr mulrN -mulNr addrA 
    -mulr_addl (mulrC k').
  apply: ler_trans(_:(y - x) * eval_pol l y + x * k * (y - x) <= _);
    last first.
    rewrite ler_add2r; rewrite -mulrA; rewrite ler_mulpl //;
      first by apply: ler_trans x1x; apply: ltrW.
    by apply: incr; first apply: ler_trans x1x.
  apply : ler_trans (_ : eval_pol l x1 * (y - x) + x * k * (y - x) <= _).
    apply: ler_trans (_ : eval_pol l x1 * (y - x) + v1 * k * (y - x) <= _).
      rewrite /k' -mulr_addl [(y - x) * _]mulrC.
      rewrite ler_mulpr //; first by rewrite -(addrN x) ler_add2l; apply:ltrW.
      have t: - (k * v1 / Qcb_make 2) + v1 * k <= eval_pol l x1 + v1 * k.
        by rewrite ler_add2l.
      apply: ler_trans t.
      have Hv1k2: v1*k == k*v1/Qcb_make 2 + k*v1/Qcb_make 2.
        have: Qcb_make 2 = 1 + 1 by apply/eqP.
        move=> ->; rewrite -mulr_addl [k * _]mulrC -{2 3}[v1 * _]mulr1.
      by rewrite -mulr_addr mulrK //.
    by rewrite (eqP Hv1k2) addrA addNr add0r lerr.
    rewrite ler_add2r; rewrite -!mulrA ltf_mulpr; last first.
      by rewrite mulf_gt0pp // subr_le0.
    by apply: ler_trans x1x.
  rewrite ler_add2l; rewrite [_ * (y - x)]mulrC.
  rewrite ler_mulpl // ?subr_ge0; first by apply: ltrW.
  rewrite -[eval_pol l x1]add0r -[eval_pol l y]addr0 -{2}(addNr(eval_pol l x1))
    addrA ler_add2l; apply: ler_trans (_ : (k * (y - x1)) <= _).
    rewrite  mulr_ge0pp // ?subr_ge0 //; first by apply: ltrW.
    by apply: ler_trans x1x _; apply: ltrW.
  by apply: (incr x1 y) => //; apply: ler_lt_trans xy.
by rewrite (eqP a0) add0r  mulf_gt0pp.
Qed.

