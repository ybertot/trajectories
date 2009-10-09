Require Import QArith List Omega ZArith (* sos *) pol cmvt.
Require Import ssreflect eqtype ssrbool ssrnat div fintype seq ssrfun pol.
Require Import bigops groups choice .
Require Export ssralg xssralg infra .

(* Defining function over lists of rationals that find lists containing
  exactly one alternation, from negative to positive values. *)

Import GroupScope .
Import GRing.Theory .
Import GOrdered.
Open Local Scope ring_scope .

Fixpoint all_zero (l:seq Qcb) : bool :=
  match l with nil => true
  | a::tl => if a == 0 then all_zero tl else false
 end.

Fixpoint all_pos_or_zero (l:seq Qcb) : bool :=
  match l with nil => true
  | a::tl => if a <<! 0 then false else all_pos_or_zero tl
  end.

Fixpoint all_neg_or_zero (l:seq Qcb) : bool :=
  match l with nil => true
  | a::tl => if 0 <<! a then false else all_neg_or_zero tl
  end.

(* alternate_1 is true for lists containing at least one strictly positive
  value followed by only positive values, and preceeded by only negative
  or zero values. but negative values are not guaranteed. *)
Fixpoint alternate_1 (l:seq Qcb) : bool :=
  match l with nil => false
  | a::tl => if 0 <<! a then all_pos_or_zero tl else alternate_1 tl
  end.

(* alternate is true for lists that contain one negative value, followed
 by an arbitrary number of non-positive values, followed
 by one strictly positive value, followed by only non-negative values.
*)
Fixpoint alternate (l:seq Qcb) : bool :=
 match l with nil => false
 | a::tl => if a <<! 0 then alternate_1 tl else 
   if  a == 0 then alternate tl else false
 end.

Lemma ltr_ler_2compat0l :
  forall x y z t:Qcb, 0 <<= x -> x <<! y ->
     0<<! t -> z <<= t -> x * z <<! y * t.
Proof.
move => x y z t x0 xy t0 zt.
have m : x * t <<! y * t by apply: ltr_rcompat t0 xy.
by apply: ler_ltr_trans m; apply: ler_lcompat.
Qed.

Lemma ler_2compat0l :
  forall x y z t:Qcb, 0 <<= x -> x <<= y ->
     0<<= t -> z <<= t -> x * z <<= y * t.
Proof.
move => x y z t x0 xy t0 zt.
have m : x * t <<= y * t by apply: ler_rcompat t0 xy.
by apply: ler_trans m; apply: ler_lcompat.
Qed.

Lemma ltr_mul2C : forall  x y z t:Qcb, (x * y <<! z * t) = (y * x <<! t * z).
by move => x y z t; rewrite [x * _]mulrC [z * _]mulrC.
Qed.

Lemma alternate1_decompose :
  forall l, alternate_1 l = true ->
    (exists l1, exists l2, exists l3, exists a, exists b,
      l = l1 ++ a::l2 ++ b::l3 /\
      all_neg_or_zero l1 = true /\ a <<! 0 /\ all_zero l2 = true /\ 0 <<! b /\
      all_pos_or_zero l3 = true) \/
    exists l2, exists l3, exists b,
      l = l2++b::l3 /\
      all_zero l2 = true /\ 0 <<! b /\ all_pos_or_zero l3 = true.
Proof.
move => l; elim: l;[ move => al; discriminate | move => /= a l IHl].
case cmp: (0 <<! a) => h; first by right; exists [::]; exists l; exists a => //.
move: (IHl h) => [[l1 [l2 [l3 [a' [b [H1 [H2 [H3 [H4 [H5 H6]]]]]]]]]] |
                  [l2 [l3 [b [H1 [H2 [H3 H4]]]]]]] {IHl h}.
  left; exists (a::l1); exists l2; exists l3; exists a'; exists b.
  by rewrite H1 /= cmp.
case Ha1: (a == 0).
  by right; exists (a::l2); exists l3; exists b; rewrite H1 /= Ha1.
left; exists [::]; exists l2; exists l3; exists a; exists b.
have tmp: a <<! 0 by rewrite ltr_lerne Ha1 andbC /= lerNgtr cmp.
by rewrite H1; repeat split; done.
Qed.

(*
Lemma Qmult_le_0_compat :
 forall x y, 0 <= x -> 0 <= y -> 0 <= x * y.
intros x y Hx Hy; case (Qle_lt_or_eq _ _ Hx); clear Hx; intros Hx.
case (Qle_lt_or_eq _ _ Hy); clear Hy; intros Hy.
assert (H0 : 0 == 0 * y) by ring; rewrite H0.
apply Qlt_le_weak; apply Qmult_lt_compat_r; auto.
rewrite <- Hy; assert (H0 : x * 0 == 0) by ring; rewrite H0; apply Qle_refl.
rewrite <- Hx; assert (H0 : 0 * y == 0) by ring; rewrite H0; apply Qle_refl.
Qed.
*)

Lemma l1 : forall l, all_pos_or_zero l = true ->
  forall x, 0 <<= x -> 0 <<= eval_pol l x.
Proof.
move => l; elim: l; first by []. 
move => a l IHl /=; case Ha: (a <<! 0) => Hl x Hx; first discriminate.
apply: lerT0; first by rewrite ?lerNgtr Ha.
by apply: ler_0_lcompat; last apply: IHl.
Qed.

Lemma l2 : forall l, all_pos_or_zero l = true ->
  forall x y, 0 <<= x -> x <<= y -> eval_pol l x <<= eval_pol l y.
move => l; elim: l => [ | a l IHl] //=. 
case Ha : (ltb a 0) => Hl x y Hx Hy; first discriminate.
have y0 : 0 <<= y by apply: ler_trans Hy.
apply: lerTr; apply ler_2compat0l => //; first by apply: l1.
by apply: IHl.
Qed.

Definition inv (l:seq Qcb) : Prop :=
  forall epsilon, 0 <<! epsilon ->
    exists x,
      (forall y, 0 <<= y -> y <<= x -> eval_pol l y <<= eval_pol l x) /\
      (forall y z, x <<= y -> y <<= z ->  eval_pol l y <<= eval_pol l z) /\
      0 <<= x /\ x * eval_pol l x <<! epsilon.

Lemma l3 : forall l, all_pos_or_zero l = true -> inv l.
Proof.
move => l Hl eps Heps; move: (l1 l Hl) (l2 l Hl) => H1 H2.
have Hp1: 0 <<= eval_pol l 1 by  apply: H1.
rewrite ler_ltreq in Hp1; case/orP: Hp1 => Hp1.
  have pol1p: eval_pol l 1 != 0.
    by apply/negP => q; rewrite (eqP q) ltr_irrefl in Hp1.
  case H1p1: (1 <<! eps / eval_pol l 1).
    exists 1; split.
      move => y yp; rewrite ler_ltreq; move/orP => [y1 | y1].
        by apply: H2; last apply: ltrW.
      by rewrite (eqP y1) ler_refl.
    split.
      by move => y z y1 yz; apply: H2; first by apply: ler_trans y1.
    split; first by [].
    have hp2 := Hp1.
      rewrite -invr_ltr in hp2.
    by apply: (ltr_Ilcompat_l hp2); rewrite mulrK.
  exists (eps / (Qcb_make 2 * eval_pol l 1)).
  have epspl1 : 0 <<= eps / (Qcb_make 2 * eval_pol l 1).
    apply: ltrW; apply: ltr_0_lcompat; first done.
    rewrite invr_mul //; apply ltr_0_lcompat; last done.
    by rewrite invr_ltr.
  have half: eps/(Qcb_make 2 * eval_pol l 1) <<! eps/eval_pol l 1.
     by apply: half_lt.
  split.
    move => y y0; rewrite ler_ltreq; move/orP=> [y2 | y2].
      by apply: H2; last apply: ltrW.
    by rewrite (eqP y2) ler_refl.
  split.
    move => y z y' yz; apply: H2; last done.
    by apply: ler_trans y'.
  split; first done.
  case px0: (eval_pol l (eps / (Qcb_make 2 * eval_pol l 1)) == 0).
    by rewrite (eqP px0) mulr0.
  move: (negbT px0) => {px0} px0 .
  have tmp: eps /eval_pol l 1 * eval_pol l 1 <<= eps.
   by rewrite mulrVK // ler_refl.
  apply: ltr_ler_trans tmp.
  move: (negbT H1p1); rewrite -lerNgtr {H1p1} => H1p1.
  apply ltr_ler_2compat0l => //; apply: H2 => //; apply: ler_trans H1p1.
  by apply:ltrW.
exists 1; split.
  move => y y0 y1; case h: (y==1); first by rewrite (eqP h) ler_refl.
  by apply: H2 => //; rewrite ltr_lerne y1 h.
split; first by move => y z y1 yz; apply: H2 => //; apply: ler_trans y1.
split; first by [].
by rewrite -(eqP Hp1) mul1r.
Qed.


Definition inv2 (l:seq Qcb) : Prop :=
  forall epsilon, 0 <<! epsilon ->
    exists x, (forall y, 0 <<= y -> y <<= x -> eval_pol l y <<= eval_pol l x) /\
      (forall y z, x <<= y -> y <<= z ->  eval_pol l y <<= eval_pol l z) /\
      0 <<= x /\ 0 <<! eval_pol l x /\ x * eval_pol l x <<! epsilon.

Lemma l5 : forall a l, a <<! 0 -> inv2 l -> inv2 (a::l).
move => a l aneg il.
have aneg' := aneg.
rewrite -ltr_oppgtr oppr0 in aneg.
move: (il _ aneg) => [x [H1 [H2 [H3 [H4 H5]]]]].
have ix' : exists x', x <<! x' /\ 0 <<! eval_pol l x' /\
              x' * eval_pol l x' <<! (-a).
  have H4': 0 <<! -a -x*eval_pol l x.
    by rewrite -(addrN (x * eval_pol l x)) ltrTl.
(*
  rewrite ler_ltreq in H4; move/orP: H4 => [H4 | v0]; last first.
    move : (pol_cont (0::l) x _ H4') => [d2 [d2p pd2]].
    move: (cut_epsilon _ d2p) => [d [_ [dp [_ [_ [dd' _]]]]]].
    exists (x + d); split; first by rewrite -{1}[x]addr0 ltrTr.
    split.
      rewrite (eqP v0); apply: H2; first apply: ler_refl.
      by rewrite -{1}[x]addr0 lerTr ?ltrW.
    rewrite -(@ltrTlb _ (-(x * eval_pol l x))); apply: absr_lt.
    have t: absr (x + d -x) <<! d2.
      by rewrite [x+_]addrC addrK absr_nneg ?ltrW //; apply: ltr_ler_trans dd2.
    by move: (pd2 _ t); rewrite /= !add0r.
*)
  move : (pol_cont l x _ H4) => [d1 [d1p pd1]].
  move : (pol_cont (0::l) x _ H4') => [d2 [d2p pd2]].
  have: exists d, 0 <<! d /\ d <<= d1 /\ d <<= d2.
    case cmp: (d1 <<! d2).
      exists d1.
      by split; first done; split; first apply:ler_refl; apply: ltrW.
    move/negbT : cmp; rewrite -lerNgtr => cmp.
    by exists d2; split; first done; split; first done; apply:ler_refl.
  move => [d' [dp' [dd1 dd2]]]; move: (cut_epsilon _ dp') =>
    [d [_ [dp [_ [_ [dd' _]]]]]].
  exists (x + d).
  split; first by rewrite -{1}[x]addr0 ltrTr.
  split.
    rewrite -(@ltrTlb _ (eval_pol l x - eval_pol l (x + d))) add0r
        addrA [_ + eval_pol l x]addrC addrK; apply: absr_lt.
    rewrite -absr_oppr oppr_add opprK addrC; apply pd1.
    by rewrite [x+_]addrC addrK absr_nneg ?ltrW //; apply: ltr_ler_trans dd1.
  rewrite -(@ltrTlb _ (-(x * eval_pol l x))); apply: absr_lt.
  have t: absr (x + d -x) <<! d2.
    by rewrite [x+_]addrC addrK absr_nneg ?ltrW //; apply: ltr_ler_trans dd2.
  by move: (pd2 _ t); rewrite /= !add0r.
move: ix' => [x' [xx' [vx'pos smallvx']]].
have x'pos : 0 <<! x' by apply: ler_ltr_trans xx'.
have pxn : eval_pol (a::l) x <<! 0.
  by rewrite /= -(addrN a); apply: ltrTr.
have H1' : forall y, 0 <<= y -> y <<= x ->
   y * eval_pol l y <<= x * eval_pol l x.
  move => y y0 yx.
  (apply: ler_2compat0l => //; last by apply: H1); by apply: ltrW.
have H2' : forall y z, x <<= y -> y <<= z -> 
             y * eval_pol l y <<= z * eval_pol l z.
  move => y z xy yz; apply: ler_2compat0l => //.
      by apply: ler_trans xy.
    apply: ler_trans (ltrW H4) _; apply: H2.
      by apply: ler_refl.
    by apply: ler_trans yz.
  by apply: H2.
have negval : eval_pol (a::l) x' <<! 0.
  by rewrite -(addrN a) /= ltrTrb.
have max_x_val : exists b, (x' <<! b) && (-a/eval_pol l x' <<! b).
  have p1 : forall x, x <<! x + 1.
    move => A x0; rewrite -{1}(addr0 x0); apply: (ltrTr (ltr_0_1 _)).
  case cmp: (x' <<! (-a/eval_pol l x')).
    exists (-a/eval_pol l x' + 1); rewrite p1 andbC /=.
    by apply: ltr_trans cmp _; apply: p1.
  exists (x' + 1); rewrite p1 /=.
  move: (negbT cmp); rewrite -lerNgtr {cmp} => cmp.
    by apply: ler_ltr_trans cmp _; apply: p1.
move: max_x_val => [y]; move/andP => [yx val]; have yx':= ltrW yx.
have pyp: 0 <<! eval_pol l y.
  apply: ltr_ler_trans H4 _; apply: H2; first apply: ler_refl.
   by apply: ler_trans yx'; apply: ltrW.
have posval : 0 <<= eval_pol (a::l) y.
  rewrite -(addrN a) /=; apply: lerTr.
  apply: (@ler_Ilcompat_l _ (eval_pol l y)^-1); first by rewrite invr_ltr.
  have pyn0 : eval_pol l y != 0.
    by apply/negP; move/eqP => q; rewrite q ltr_irrefl in pyp.
  rewrite mulrK; last by [].
  apply: ltrW; apply: ler_ltr_trans val.
  apply: ler_lcompat; first by apply: ltrW.
  have pxp : eval_pol l x' != 0.
    by apply/negP; move/eqP => q; rewrite q ltr_irrefl in vx'pos.
  apply: (@ler_Ilcompat_l _ (eval_pol l x')); first by [].
  rewrite mulVr; last by [].
  apply: (@ler_Ilcompat_r _ (eval_pol l y)); first by [].
  rewrite mulVKr // mulr1; apply: H2 => //; first by apply:ltrW.
intros epsilon Hepsilon.
have posval' : 0 <<= eval_pol (0::a::l) y.
  by rewrite /= add0r; apply: ler_0_lcompat; first (apply: ler_trans yx'; apply: ltrW).
have ieps : exists eps', eps' <<! epsilon /\ 0 <<! eps'.
  by move: (cut_epsilon _ Hepsilon) => [e [_ [p [_ [_ [d _]]]]]]; exists e.
move: ieps => [eps' [eps2 Heps']].
have iv' : exists v', 0 <<= eval_pol (0::a::l) v' /\
                eval_pol (0::a::l) v' <<= eps' /\ v' <<= y /\ x' <<= v'.
  have negval' :  eval_pol (0::a::l) x' <<! 0.
    rewrite /= add0r -ltr_oppgtr oppr0 -mulrN; apply: ltr_0_lcompat => //. 
    by rewrite -oppr0 ltr_oppgtr.
  move: (constructive_mvt (0::a::l) x' y yx negval' posval' eps' Heps') =>
    [dummy [v' [_ [_ [posv' [smallv' [xd [dv' v'y]]]]]]]].
  exists v'; split; first done; split; first done; split; first done.
  by apply: ltrW; apply:ler_ltr_trans dv'.
move: iv' => [v' [posv' [smallv' [v'y xv']]]].
move: posv' smallv'; rewrite /= !add0r => posv' smallv'.
have pv' : 0 <<! v' by apply:ltr_ler_trans xv'.
have iv : exists v, x <<! v /\ v * eval_pol (a::l) v <<= eps' /\
          0 <<= eval_pol (a::l) v.
  rewrite ler_ltreq in posv'; move/orP: posv' => [posv' | nulv'].
    rewrite -(mulr0 v') in posv'.
    move: (ltr_Ilcompat_r pv' posv') => {posv'} posv'.
    have t: x <<! v' by apply: ltr_ler_trans xv'.
    have posv'2 := ltrW posv'.
    by exists v' => //.    
  move: (pol_cont (0::a::l) v' eps' Heps') => [delta1 [dp Hp]].
  move: (cut_epsilon _ dp) => [delta [_ [dp2 [_ [_ [dd _]]]]]].
  case vdy: (v' + delta <<= y).
    have vvd : v' <<! v' + delta by rewrite -{1}[v']addr0; apply: ltrTr.
    exists (v'+delta).
    split; first by apply: ltr_trans vvd; apply: ltr_ler_trans xx' _.
    split.
      rewrite -[_ * _]addr0 -oppr0 (eqP nulv') .
      have Hp': absr (eval_pol [:: 0, a & l] (v' + delta) - 
                       eval_pol [::0, a & l] v') <<! eps'.
        by apply Hp; rewrite [v' + _]addrC addrK absr_nneg // ltrW.
      by rewrite /= !add0r in Hp'; apply: absr_le; apply ltrW.
    have pv0 : 0 == a+v'*eval_pol l v'.
      have uv': v' != 0. 
        by apply/negP; move/eqP => q; rewrite q ltr_irrefl in pv'.
      by rewrite -(mulr0 v'^-1) (eqP nulv') mulKr // eq_refl.
    rewrite (eqP pv0) /= lerTr // -[v' * _]add0r mulr_addl [(v' * _) + _]addrC.
    apply: lerT. 
      apply: ler_0_lcompat; apply: ltrW; first by [].
      apply: ltr_ler_trans vx'pos _; apply: H2; first by apply: ltrW.
      by apply: ler_trans xv' _; rewrite -{1}[v']addr0 lerTr // ltrW.
    apply: ler_lcompat; first by apply: ltrW.
    apply: H2.
      by apply: ltrW; apply: ltr_ler_trans xv'. 
    by rewrite -{1}[v']addr0 lerTr // ltrW.
  exists y.
  split; first by apply: ltr_trans yx.
  split; last by [].
  have Hp' : 
    absr (eval_pol[:: 0, a & l] y - eval_pol [:: 0, a & l] v') <<! eps'.
    have vyd : y - v' <<! delta1.
      apply: ltr_trans dd; move: (negbT vdy).
      by rewrite -ltrNger -{1}[y]addr0 -(addNr v') addrA [_ + v']addrC ltrTrb.
    by apply: Hp; rewrite absr_nneg // -(addrN v') lerTl //.
  apply absr_le; move: Hp'; rewrite /= !add0r -(eqP nulv') oppr0 addr0.
  by apply: ltrW.
case: iv => v [xv [pvep]]; rewrite ler_ltreq orbC; move/orP => [pv0 | pvp].
  move: (pol_cont (0::a::l) v _ Heps') => [delta [pd dp]].
  move: (cut_epsilon _ pd) => [delta' [_ [pd' [_ [_ [dd' _]]]]]].
  have vvd : v <<! v + delta' by rewrite -{1}[v]addr0 ltrTr //.
  exists (v + delta'); split.
    move => y' y'0 y'vd; apply: lerTr.
    case y'x: (y' <<! x).
      apply: ler_trans (_ :  x*eval_pol l x <<= _).
        by apply: H1'; first done; rewrite ?ltrW.
      by apply: H2';first apply:ler_refl; apply: ltrW (ltr_trans xv _).
    move/negbT: y'x; rewrite -lerNgtr => xy'.
    by apply: H2'.
  split.
    move => y' z vdy' y'z; apply: lerTr; apply: H2'; last by [].
    by apply: ltrW; apply: ltr_ler_trans vdy'; apply: ltr_trans xv _.
  split; first by apply: ltrW (ltr_trans (ler_ltr_trans _ xv) _).
  split.
    rewrite mulr_addl addrA.
    apply: ler_ltr_trans (_ : a + v * eval_pol l (v + delta') <<! _).
      have v0 : 0 <<= v by apply: ler_trans (ltrW xv).
      by rewrite (eqP pv0) /= lerTr //; apply ler_lcompat => //; apply: H2;
        apply: ltrW.
    rewrite (_ : forall x y, (x <<! y) = ((x + 0) <<! y));
      last by move => *; rewrite addr0.
    apply: ltrTr; apply: ltr_0_lcompat; first done.
    apply: ltr_ler_trans H4 _; apply: H2; first apply: ler_refl; apply: ltrW.
    by apply: ltr_trans vvd.
  apply: ltr_trans eps2; apply: absr_lt; rewrite -[_ * _]add0r.
  rewrite -[0 + _]addr0 -{2}oppr0 -{2}(mulr0 v) -[v * 0]add0r {3}(eqP pv0).
  apply: dp; rewrite [v + _]addrC addrK.
  by rewrite absr_nneg // ltrW.
exists v.
have pv : 0 <<! v by apply:ler_ltr_trans xv.
have pvp': 0 <<! eval_pol l v.
  apply: ltr_Ilcompat_r pv _; rewrite mulr0; apply: ltr_ler_trans aneg _.
  by rewrite -(lerTrb a) addrN ltrW.
split.
  move => y' posy' y'v; case y'x : (y' <<= x).
    apply: ltrW (ler_ltr_trans _ pvp); apply: ler_trans (ltrW pxn) => /=.
    by apply: lerTr; apply: H1'.
  apply: lerTr; apply: ler_2compat0l => //.
    apply: (ler_Ilcompat_r pv); rewrite mulr0.
    apply: ltrW; apply: ltr_ler_trans aneg _.
    by have := ltrW pvp; rewrite -(addrN a) /= lerTrb => psv'.
  rewrite ler_ltreq in y'v; case/orP: y'v => y'v.
    move: (negbT y'x) => {y'x} y'x; rewrite -ltrNger in y'x.
    by apply: H2 => //; apply: ltrW.
  by rewrite (eqP y'v) ler_refl.
split.
  move => {v'y val posval posval' yx yx' y pyp} y z vy yz.
  apply: lerTr; apply: ler_2compat0l => //.
      by apply: ltrW; apply: ltr_ler_trans vy.
    apply: ler_trans (ltrW pvp') _.
    by apply: H2; [apply: ltrW | apply: ler_trans yz].
  by apply: H2; last done; apply: ltrW; apply: ltr_ler_trans vy.
split; first by apply: ltrW.
split; last by apply: ler_ltr_trans pvep _.
by [].
Qed.

Lemma l4 : forall l, alternate_1 l = true -> inv2 l.
Proof.
move => l; elim: l => /= [  | a l IHl]; first by move => *; discriminate.
case a0: (0 <<! a).
  move => alp; have alp':  all_pos_or_zero (a::l) by rewrite /= ltrNger ltrW.
  move => e ep; move: (l3 _ alp' _ ep) => [x [H1 [H2 [H3 H4]]]].
  exists x; split => //; split => //; split => //; split => //.
  by rewrite /= -[0]addr0 ltr_lerT ?ler_0_lcompat ?(ltrW H3) ?l1.
move/negbT: a0; rewrite -lerNgtr ler_ltreq; move /orP=> [a0| a0] alp.
  by apply: l5 a0 (IHl alp).
move => e ep; move: (cut_epsilon _ ep) => [e1 [e2 [e1p [e2p [s12 [d1 d2]]]]]].
move: (IHl alp _ (ltr_0_1 _)) => [x [H1 [H2 [H3 [H4 H5]]]]].
rewrite ler_ltreq in H3; move/orP: H3 => [H3 | x0]; last first.
  move: (pol_cont l x _ H4) => [delta1 [d1p pd1]].
  move: (pol_cont (0::a::l) x _ ep) => [delta2 [d2p pd2]].
  have : exists delta, 0 <<! delta /\ delta <<= delta1 /\ delta <<= delta2.
    case dd:(delta1 <<= delta2); last (move/negbT: dd; rewrite -ltrNger => dd).
      by exists delta1; split; first done; split; first apply: ler_refl.
    by exists delta2; split; first done; split; 
       last apply: ler_refl; apply: ltrW.
  move => [delta' [dp' [dd1' dd2']]].
  move: (cut_epsilon _ dp') => [delta [_ [dp [_ [_ [dd _]]]]]].
  have dd1 : delta <<= delta1 by apply: ler_trans dd1'; apply: ltrW.
  have dd2 : delta <<! delta2 by apply: ltr_ler_trans dd2'.
  exists delta.
  split.
    move => y y0 yd /=; apply: lerTr; apply: ler_2compat0l => //.
    apply: ltrW; apply: ltr_ler_trans H4 _; apply: H2; first apply: ler_refl.
      by rewrite -(eqP x0) ltrW.
    by apply: H2; first rewrite -(eqP x0).
  split.
    move => y z y0 yz /=; apply: lerTr; apply ler_2compat0l => //.
        have t: eval_pol l x <<= eval_pol l z.
          apply: H2; first apply:ler_refl; apply: ler_trans yz.
          by apply: ltrW(ltr_ler_trans _ y0); rewrite -(eqP x0).
        by apply: ltrW(ltr_ler_trans _ y0).
      apply: ler_trans (_ :  eval_pol l x <<= _); first by apply: ltrW.
      apply: H2; first by apply: ler_refl.
      by apply: ler_trans (ler_trans y0 yz); rewrite -(eqP x0) ltrW.
    by apply: H2 => //; rewrite -(eqP x0); apply: ltrW (ltr_ler_trans _ y0).
  split; first by apply: ltrW.
  split.
    rewrite /= (eqP a0) add0r; apply: ltr_0_lcompat; first by []. 
    apply: ltr_ler_trans H4 _; apply: H2; first by apply:ler_refl.
    by rewrite -(eqP x0) ltrW.
  apply absr_lt; rewrite -[_ * _]addr0 -oppr0 -(mul0r (eval_pol (a::l) x)).
  rewrite -[0 * _]add0r {2}(eqP x0) -[delta * _]add0r.
  by apply: pd2; rewrite -(eqP x0) oppr0 addr0 absr_nneg // ltrW.
have e1px : 0 <<! e1/x by apply: ltr_0_lcompat; first done; rewrite invr_ltr.
move: (IHl alp _ e1px) => [v [H6 [H7 [H8 [H9 H10]]]]].
have ux: GRing.unit x by apply/negP; move/eqP => q;rewrite q ltr_irrefl in H3.
without loss: v H6 H7 H8 H9 H10 / (v <<= x).
  move => gen; case xv : (x <<! v).
    have xlv : x <<= v by apply: ltrW.
    have H5': x * eval_pol l x <<! e1/x.
      apply: ler_ltr_trans H10; apply: ler_2compat0l => //.
          by apply: ltrW.
        by apply: ltrW.
      by apply: H2; first by apply: ler_refl.
    apply: (gen x H1 H2 (ltrW H3) H4 H5'); apply: ler_refl.
  move/negbT: xv; rewrite -lerNgtr.
  apply: (gen v H6 H7 H8 H9 H10).
move => xv.
rewrite ler_ltreq orbC eq_sym in H8; move/orP: H8 => [v0 | H8].
  move: (pol_cont l 0 _ H9) => [delta1 [d1p pd1]].
  move: (pol_cont (0::a::l) 0 _ ep) => [delta2 [d2p pd2]].
  have id: exists delta, 0 <<! delta /\ delta <<! delta1 /\ delta <<! delta2.
    move: (cut_epsilon _ d2p) => [d2' [_ [d2'p [_ [_ [dd2 _]]]]]].
    move: (cut_epsilon _ d1p) => [d1' [_ [d1'p [_ [_ [dd1 _]]]]]].
    case cmp: (d1' <<! d2').
      exists d1'; split; first done; split; first done.
      by apply: ltr_trans dd2.
    move/negbT: cmp; rewrite -lerNgtr => cmp.
    exists d2'; split; first done; split; first apply: ler_ltr_trans cmp dd1.
    by [].
  move: id => {dd2} [delta [dp [dd1 dd2]]].
  exists delta; split.
    move => y y0 yd /=; rewrite (eqP a0) !add0r; apply: ler_2compat0l => //.
      apply: ler_trans (ltrW H9) (_: eval_pol l v <<= _).
      apply: H7; first by apply: ler_refl.
      by rewrite (eqP v0); apply: ler_trans yd.
    by apply: H7; rewrite ?(eqP v0).
  split.
    move => y z dy yz; rewrite /= (eqP a0) !add0r; apply: ler_2compat0l => //.
        by apply: ltrW(ltr_ler_trans _ dy).
      apply: ltrW(ltr_ler_trans H9 _); apply: H7; first by apply: ler_refl.
      by rewrite (eqP v0); apply: ler_trans (ltrW (ltr_ler_trans dp dy)) yz.
    by apply: H7; first by rewrite (eqP v0); apply: ltrW(ltr_ler_trans _ dy).
  split; first by apply: ltrW.
  split.
    rewrite /= (eqP a0) add0r ltr_0_lcompat //.
    rewrite -(@ltrTlb _ (eval_pol l v - eval_pol l delta)) add0r.
    rewrite [_ _ delta + _]addrC addrNK absr_lt // -absr_oppr oppr_add opprK.
    rewrite addrC {1}(eqP v0); apply: pd1.
    by rewrite oppr0 addr0 absr_nneg // ltrW.
  rewrite (_:delta * _ = 0+delta*eval_pol (a::l) delta - eval_pol (0::a::l) 0).
  by apply: absr_lt; apply: pd2; rewrite oppr0 addr0 absr_nneg // ltrW.
  by rewrite /= !add0r mul0r oppr0 addr0.
exists v; split.
  move => y y0 yx /=; apply: lerTr.
  have : y * eval_pol l v <<= v * eval_pol l v.
    by apply: ler_rcompat => //; apply:ltrW.
  move => tmp; apply: ler_trans tmp; apply: ler_lcompat; first by [].
  by apply: H6.
split.
  move => y z vy yz /=; have y0: 0 <<= y by apply: ltrW(ltr_ler_trans H8 vy).
  apply: lerTr; apply: ler_2compat0l => //.
    apply: ltrW (ltr_ler_trans H9 _); apply: H7; first apply: ler_refl.
    by apply: ler_trans yz.
  by apply: H7.
split; first by apply: ltrW.
rewrite /= (eqP a0) add0r; split; first by rewrite ltr_0_lcompat.
apply: ltr_trans d1.
have u:  0 <<! v^-1 by rewrite invr_ltr.
have uv: GRing.unit v by apply/negP; move/eqP => q;rewrite q ltr_irrefl in H8.
apply: (ltr_Ilcompat_l u); rewrite [v * _]mulrC mulrK //.
apply: ltr_ler_trans H10 _; apply: ler_lcompat; first by apply:ltrW.
have xv0 : 0 <<! x * v by apply: ltr_0_lcompat.
apply: (ler_Ilcompat_r xv0); rewrite mulrK // [x * _]mulrC mulrK //.
Qed.

Lemma desc : forall l, alternate l = true ->
  exists x1, exists x2, exists k, 0 <<! x1 /\ x1 <<! x2 /\ 0 <<! k /\
   (forall x, 0 <<! x -> x <<= x1 -> eval_pol l x <<! 0) /\
   (forall x y, x1 <<= x -> x <<! y -> 
       k * (y - x) <<= eval_pol l y - eval_pol l x ) /\
   0 <<! eval_pol l x2.
move => l; elim: l => /= [ | a l IHl]; first by move => *; discriminate.
case aneg: (a <<! 0) => alt1;
   last (move/negbT: aneg; rewrite -lerNgtr => apos).
  have aneg': (0 <<! -a) by rewrite -oppr0 ltr_oppgtr.
  move: (l4 _ alt1 _ aneg') => [x1  [H1x1 [H2x1 [H3x1 [H4x1 H5x1]]]]].
  rewrite ler_ltreq orbC eq_sym in H3x1; move/orP: H3x1 => [x10 | H3x1].
    admit.
  exists x1.
  have Hex2: exists x2, x1 <<= x2 /\ -a/eval_pol l x1 + 1 <<= x2.
    case vx1: (-a/eval_pol l x1 + 1 <<! x1); 
      last (move/negbT: vx1; rewrite -lerNgtr => x1v).
      by exists x1; rewrite ler_refl ltrW.
    by exists (-a/eval_pol l x1 + 1); rewrite ler_refl.
  move: Hex2 => [x2 [x1x2 vx2]].
  have x1x2': x1 <<! x2.
    apply: ltr_ler_trans vx2; rewrite -{1}[x1]addr0.
    apply: ltrT; last by apply: ltr_0_1.
    have uv: GRing.unit (eval_pol l x1)
      by apply/negP; move/eqP=> q; rewrite q ltr_irrefl in H4x1.
    by apply: (ltr_Ilcompat_l H4x1); rewrite mulrVK.
  exists x2; exists (eval_pol l x1).
  split; first by [].
  split; first by [].
  split; first by [].
  split.
    move => x posx xx1; rewrite -(addrN a).
    apply: ltrTr; apply: ler_ltr_trans H5x1.
    have t: x*eval_pol l x1 <<= x1 * eval_pol l x1.
      by apply ler_rcompat => //; apply: ltrW.
    apply: ler_trans t; apply: ler_lcompat; first by apply: ltrW.
    by apply: H1x1; last done; apply: ltrW.
  split.
    move => x y x1x xy; rewrite [a + _]addrC oppr_add addrA addrK.
    have y0: 0 <<! y by apply: ltr_trans xy; apply: ltr_ler_trans x1x.
    have t:= ler_lcompat (ltrW y0) (H2x1 _ _ x1x (ltrW xy)).
    have t1 := lerTl t; have t2 := t1 (- (x *  eval_pol l x)) => {t1 t}.
    apply: ler_trans t2. rewrite -(mulNr x) -mulr_addl [(y - x) * _]mulrC.
    apply: ler_rcompat; first by rewrite -(addrN x) lerTl ?ltrW.
    rewrite ler_ltreq in x1x; move/orP: x1x => [x1x | x1x].
      by apply: H2x1 x1 x (ler_refl _) (ltrW x1x).
    by rewrite (eqP x1x) ler_refl.
  have vx2' : -a + eval_pol l x1 <<= x2 * eval_pol l x2.
    have vx2' : x2 * eval_pol l x1 <<= x2 * eval_pol l x2.
      apply: ler_lcompat; first by apply: ltrW; apply: ltr_trans x1x2'.
      by apply: H2x1; first apply: ler_refl.
    apply: ler_trans vx2'.
    have t: 0 <<! (eval_pol l x1)^-1 by rewrite invr_ltr.
    apply: (ler_Ilcompat_l t) => {t}.
    have upx1: GRing.unit (eval_pol l x1).
      by apply/negP;move/eqP=>q;rewrite q ltr_irrefl in H4x1.
    by rewrite mulrK // mulr_addl mulrV.
  rewrite -(addrN a) ltrTr //; apply: ltr_ler_trans vx2'.
  by rewrite -{1}[-a]addr0 ltrTr //.
rewrite ler_ltreq in apos; case a0 : (a == 0); last by rewrite a0 in alt1.
rewrite a0 in alt1 => {apos}.
move: (IHl alt1) => [v1 [v2 [k [v1pos [v1v2 [kpos [low [incr pos]]]]]]]] {IHl}.
have negval : (eval_pol l v1 <<! 0) by apply low; rewrite ?ler_refl.
have v2pos : (0 <<! v2) by apply: ltr_trans v1v2.
have epsv2 : (0 <<! k * v1 / Qcb_make 2). 
  apply: ltr_0_lcompat; first by apply: ltr_0_lcompat => //.
  by rewrite invr_ltr.
move: (constructive_mvt l v1 v2 v1v2 negval (ltrW pos) _ epsv2) =>
  [x1 [x2 [x1close [px1neg [px2pos [px2close [v1x1 [x1x2 x2v2]]]]]]]].
set k':=k * v1 / Qcb_make 2.
have x1pos : 0 <<! x1 by apply: ltr_ler_trans v1x1. 
exists x1; exists (v2); exists k'; split; first by [].
have Plow : forall x, 0 <<! x -> x <<= x1 -> a + x * eval_pol l x <<! 0.
  intros x xpos xx1; rewrite (eqP a0) add0r -(mulr0 x) (ltr_lcompat xpos) //.
  case xv1: (x <<! v1).
    by apply: low; last apply: ltrW.
  rewrite -/k' in x1close.
  apply: ler_ltr_trans px1neg.
  move/negbT: xv1; rewrite -lerNgtr => v1x.
  rewrite ler_ltreq in xx1; move/orP: xx1 => [xlx1 | xx1].
    have t:= incr _ _ v1x xlx1.
    rewrite -(@lerTlb _ (-eval_pol l x)) addrN; apply: ler_trans t.
    apply: ler_0_lcompat; first by apply: ltrW.
    by rewrite -(addrN x) lerTl // ltrW.
  by rewrite (eqP xx1) ler_refl.
split.
  case x1v2: (x1 <<! v2); first by [].
  have u: 0 <<! a + v2 * eval_pol l v2 by rewrite (eqP a0) add0r ltr_0_lcompat.
  have t : (0:Qcb) <<! 0.
    apply:ltr_trans u _; apply: Plow => //.
    by move/negbT: x1v2; rewrite lerNgtr.
  by rewrite ltr_irrefl in t.
split; first done.
split; first done.
split.
  move => x y x1x xy.
  rewrite [a + _]addrC oppr_add addrA addrK -mulrN -[-eval_pol l x]add0r
    -(addNr (eval_pol l y)) -addrA [x * _]mulr_addr mulrN -mulNr addrA 
    -mulr_addl (mulrC k').
  have Hk : ((y-x) * eval_pol l y + x * k * (y - x) <<=
        (y-x) * eval_pol l y + x * (eval_pol l y - eval_pol l x)).
    apply: lerTr; rewrite -mulrA; apply: ler_lcompat;
      first by apply: ler_trans x1x; apply: ltrW.
    by apply: incr; first apply: ler_trans x1x.
  apply: ler_trans Hk.
  have t: (y - x) * k' <<= eval_pol l x1 * (y - x) + x * k * (y - x).
    have t' : eval_pol l x1 * (y - x) + v1 * k * (y - x) <<=
              eval_pol l x1 * (y - x) + x * k * (y - x).
      apply: lerTr; rewrite -!mulrA; apply ler_rcompat.
        apply: ler_0_lcompat; first by apply: ltrW.
        by rewrite -(addrN x); apply: lerTl; apply: ltrW.
      by apply: ler_trans x1x.
    apply: ler_trans t'.
    rewrite /k' -mulr_addl [(y - x) * _]mulrC.
    apply: ler_rcompat; first by rewrite -(addrN x); apply:lerTl; apply:ltrW.
    have t: - (k * v1 / Qcb_make 2) + v1 * k <<= eval_pol l x1 + v1 * k.
      by apply: lerTl.
    apply: ler_trans t.
    have Hv1k2: v1*k == k*v1/Qcb_make 2 + k*v1/Qcb_make 2.
      have: Qcb_make 2 = 1 + 1 by apply/eqP.
      move=> ->; rewrite -mulr_addl [k * _]mulrC -{2 3}[v1 * _]mulr1 -mulr_addr.
      by rewrite mulrK //.
    by rewrite (eqP Hv1k2) addrA addNr add0r ler_refl.
  apply: ler_trans t _; apply: lerTl; rewrite [_ * (y - x)]mulrC.
  apply: ler_lcompat; first by rewrite -(addrN x); apply lerTl; apply: ltrW.
  rewrite -[eval_pol l x1]add0r -[eval_pol l y]addr0
     -{2}(addNr(eval_pol l x1)) addrA; apply: lerTl.
  have t: 0 <<= k *(y - x1).
    apply ler_0_lcompat; first by apply: ltrW.
    have t' : x1 <<= y by apply: ltrW; apply: ler_ltr_trans xy.
    by rewrite -(lerTlb x1) add0r addrNK.
  by apply: ler_trans t _; apply: (incr x1 y) => //; apply: ler_ltr_trans xy.
by rewrite (eqP a0) add0r; apply: ltr_0_lcompat.
Qed.

