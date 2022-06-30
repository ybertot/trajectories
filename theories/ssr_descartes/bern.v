(*Require Import QArith ZArith Zwf Omega.*)
From mathcomp Require Import ssreflect eqtype ssrbool ssrnat div fintype seq ssrfun order.
From mathcomp Require Import bigop fingroup choice binomial poly.
From mathcomp Require Export ssralg rat ssrnum.
Require Import infra pol civt desc.

Import GroupScope .
Import Order.Theory GRing.Theory Num.Theory.
Local Open Scope ring_scope .

(* Set Printing Width 50. *)

(******************************************************************************)
(* Two predicates to describe that a polynomial has only one root,
  one_root1 l a b ==
     there exists c, d, and k, so that a,c,d,b is ordered, k is positive,
     the polynomial value is positive between a and c, negative between d and b
     the slope is less than -k between c and d.
  This statement is specifically suited to speak about roots inside the
  interval a b.

  one_root2 l a ==
     there exists c, d, and k, so that a is smaller than c, k is positive,
     the polynomial value is negative between a and c, and the slope is
     larger than k above c.

  A consequence of one_root2 is that there can be only one root above c, hence
  only one root above a.*)
(******************************************************************************)

Local Open Scope order_scope .

Definition one_root1 {R : archiFieldType} (l : {poly R}) (a b : R) :=
  exists c, exists d, exists k : R,
     a < c /\ c < d /\ d < b /\ (0 < k)%R /\
     (forall x, a < x -> x <= c -> (0 < l.[x])%R) /\
     (forall x, d < x -> x < b -> (l.[x] < 0)%R) /\
     (forall x y, c < x -> x <= y -> y < d ->
        k * (y - x) <= l.[x] - l.[y]).

Definition one_root2 {R : archiFieldType} (l : {poly R}) (a : R) :=
   exists c, exists k : R,
     a < c /\ (0 < k)%R /\
     (forall x, a < x -> x <= c -> l.[x] < 0)%R /\
     (forall x y, c <= x -> x < y ->
         k * (y - x) <= l.[y] - l.[x]).

Lemma alt_one_root2 (R : archiFieldType) : forall l : {poly R}, alternate l ->
  one_root2 l 0.
Proof.
move => l a.
move: (desc a) => [[x1 k] /= [[/andP[x1p kp] neg] sl]].
exists x1, k; split; first done; split; first done; split.
  by move=> x xgt0 xlex1; apply: neg; rewrite xgt0 xlex1.
by move=> x y xlex1 xlty; apply: sl; rewrite xlex1 (ltW xlty).
Qed.

Definition translate_pol' {R : ringType} (l : {poly R})
  (a : R) : {poly R}:=
  l \Po ('X + a%:P).

Lemma size_translate_pol' {R : idomainType} : 
  forall (l : {poly R}) a, size (translate_pol' l a)  = size l.
Proof.
by move=> l a; rewrite size_comp_poly2 // size_XaddC.
Qed.

Lemma pascalQ {R : comRingType} : forall (a b : R) n,
  (a + b) ^+ n = \sum_(i < n.+1) ('C(n, i)%:R * (a ^+ (n - i) * b ^+ i)).
Proof.
move=> a b n.
rewrite exprDn_comm; last by exact: mulrC.
apply eq_bigr => i _.
by rewrite mulrCA mulr_natl mulrnAr.
Qed.

Lemma translate_pol'q {R : comRingType} :
  forall (l : {poly R}) a x, (translate_pol' l a).[x] = l.[x + a].
Proof.
move=> l a x; rewrite /translate_pol'.
by rewrite horner_comp !hornerE.
Qed.

Lemma one_root2_translate {R : archiFieldType} :
  forall (l : {poly R}) a b, one_root2 (translate_pol' l a) b -> one_root2 l (a + b).
Proof.
move=> l a b [x1 [k [x1a [kp [neg sl]]]]].
exists (a + x1); exists k.
split; first by rewrite ltr_add2l.
split; first by [].
split.
  move=> x abx xax1; rewrite (_ : x = x - a + a); last first.
    by rewrite addrNK.
  rewrite -translate_pol'q; apply: neg.
    by rewrite ltr_subr_addl.
  by rewrite ler_subl_addl.
move=> x y ax1x xy.
have t: forall z, z = (z - a) + a by move=> z; rewrite addrNK.
rewrite {2}(t y) {2}(t x) -!(translate_pol'q l) (_ : y - x = y - a - (x - a)).
  apply: sl.
    by rewrite ler_subr_addl.
  by rewrite ltr_le_sub//.
by rewrite [x + _]addrC opprD opprK addrA addrNK.
Qed.

Lemma one_root1_translate {R : archiFieldType} :
  forall (l : {poly R}) a b c, one_root1 (translate_pol' l c) a b ->
    one_root1 l (c + a) (c + b).
Proof.
move=> l a b c [x1 [x2 [k [ax1 [x1x2 [x2b [kp [pos [neg sl]]]]]]]]].
exists (c + x1); exists (c + x2); exists k.
split; first by rewrite ltr_add2l.
split; first by rewrite ltr_add2l.
split; first by rewrite ltr_add2l.
split; first by [].
split.
  move=> x cax xcx1; rewrite (_ : x = x - c + c); last by rewrite addrNK.
  rewrite -translate_pol'q; apply pos.
    by rewrite ltr_subr_addl.
  by rewrite ler_subl_addl.
split.
  move=> x cx2x xcb; rewrite (_ : x = x - c + c); last by rewrite addrNK.
  rewrite -translate_pol'q; apply: neg; rewrite -?ler_addlA //.
    by rewrite ltr_subr_addl.
  by rewrite ltr_subl_addl.
move=> x y cx1x xy ycx2.
have t: forall z, z = (z - c) + c by move=> z; rewrite addrNK.
rewrite {2}(t x) {2}(t y) (_ : y - x = y - c - (x - c)); last first.
  by rewrite [x + _]addrC opprD opprK addrA addrNK.
rewrite -!(translate_pol'q l); apply: sl; rewrite ?ler_add2l //.
by rewrite ltr_subr_addl.
by rewrite ler_sub.
by rewrite ltr_subl_addl.
Qed.

Lemma diff_xn_ub {R : archiFieldType} :
  forall (n : nat) (z : R), (0 < z)%R -> exists k : R, (0 <= k)%R /\
   forall x y : R, (0 < x)%R -> x <= y -> (y <= z) ->
      y ^+ n - x ^+ n <= k * (y - x).
Proof.
move => n; elim: n => [z z0| n IHn z z0].
  exists 0%R; split => // x y x0 xy yz.
  by rewrite !expr0 subrr mul0r.
case: (IHn z z0) => k [k0 kp].
exists (z*k + z ^+ n); split => [ | x y x0 xy yz].
  apply: addr_ge0 => //=.
    by rewrite mulr_ge0// ltW.
  by apply: exprn_ge0 => //; exact: ltW.
rewrite !exprS.
rewrite (_: _ * _ - _ =  y * (y ^+ n - x ^+ n) + (y - x) * x ^+ n); last first.
  by rewrite mulrDr mulrDl addrA mulrN mulNr addrNK.
rewrite [_ * (y-x)]mulrDl ler_add //=.
  rewrite -mulrA; apply: le_trans (_ : y * (k * (y - x)) <= _).
  rewrite ler_wpmul2l//.
    by rewrite (le_trans _ xy)// ltW.
    by apply: kp.
  rewrite !(mulrCA _ k) ler_wpmul2l//.
  by rewrite ler_wpmul2r// ?subr_ge0.
rewrite (mulrC (_ - _)).
rewrite ler_wpmul2r// ?subr_ge0//.
rewrite ler_expn2r//.
- by rewrite nnegrE ltW.
- by rewrite nnegrE ltW.
- by apply: le_trans yz.
Qed.

Definition reciprocate_pol (l: seq rat) := rev l.

Lemma reciprocate_size :  forall l, size (reciprocate_pol l) = size l.
by move => l; rewrite /reciprocate_pol size_rev.
Qed.

Lemma cut_epsilon {R : archiFieldType} (eps : R) : (0 < eps)%R ->
  exists eps1 : R, exists eps2, (0 < eps1 /\ 0 < eps2 /\ eps1 + eps2 <= eps)%R /\
    eps1 < eps /\ eps2 < eps.
Proof.
move=> p; exists (eps / 2%:R), (eps / 2%:R).
have p1 : (0 < eps / 2%:R)%R by rewrite divr_gt0// ltr0n.
split.
  split => //; split => //.
  by rewrite -mulrDr ger_pmulr// -mulr2n -mulr_natr mulVf// pnatr_eq0.
suff cmp : eps / 2%:R < eps by [].
by rewrite ltr_pdivr_mulr// ?ltr0n// ltr_pmulr// ltr1n.
Qed.

Lemma cm3 {R : archiFieldType} :
  forall b : R, (0 < b)%R -> forall l : {poly R},
   {c | forall x y : R, (0 <= x)%R -> (x <= y)%R -> (y <= b)%R ->
    `|(l.[y] - l.[x])| <= c * (y - x)}.
Proof.
(*move=> b pb; elim=> [|u l [c cp]] /=.
  by exists 0 => x y; rewrite subrr absr0 mul0r lerr.
exists ((eval_pol (abs_pol l) b) + c * b) => x y px hxy hyb.
rewrite addrAC oppr_add addrA subrr add0r addrC.
set el := eval_pol l in cp *.
rewrite (_ : y *_ - _ = y * el y - x * el y + x * el y - x * el x); last first.
  by rewrite -[_ - _ + _]addrA addNr addr0.
have py : 0 <= y by rewrite (ler_trans px).
have psyx : 0 <= y - x by rewrite lter_subrA /= add0r.
rewrite -addrA; apply: (ler_trans (absr_add_le _ _)).
rewrite -mulNr -mulr_addl -mulrN -mulr_addr !absf_mul (ger0_abs px).
rewrite (ger0_abs psyx) [_ * (y - x)]mulr_addl; apply: lter_add=> /=.
(*rewrite absr_nneg // [_ * (y - x)]mulr_addl; apply: lerT.*)
  rewrite mulrC lter_mulpr //=; apply: (ler_trans (ler_absr_eval_pol l y)).
  by rewrite eval_pol_abs_pol_increase // ?absrpos // ger0_abs.
rewrite (mulrC c); apply ler_trans with (x * c * (y - x)).
  by rewrite -mulrA lter_mulpl //= cp.
rewrite -!mulrA lter_mulpr //= ?(ler_trans hxy) //.
by apply: ler_trans (cp _ _ px hxy hyb); apply: absr_ge0.
Qed.*) Admitted.

Lemma one_root_reciprocate {R : archiFieldType} :
  forall (l : {poly R}), one_root2 (reciprocal_pol l) 1 -> one_root1 l 0 1.
Proof.
move=> l [x1 [k [x1gt1 [kp [neg sl]]]]].
have x10 : (0 < x1)%R by rewrite (lt_trans _ x1gt1)// ltr01.
(*have ux1 : GRing.unit x1 by apply/negP; move/eqP => q; rewrite q lterr in x10.*)
(*have uk: GRing.unit k by apply/negP; move/eqP => q; rewrite q lterr in kp.*)
set y' := x1 - (reciprocal_pol l).[x1] / k.
have y'1: x1 < y'.
  rewrite /y' -(ltr_add2l (-x1)) addNr addrA addNr add0r -mulNr.
  apply: divr_gt0 => //.
  rewrite oppr_gt0.
  by apply: neg => //.
have nx1 : (reciprocal_pol l).[x1] < 0%R by apply: neg; rewrite // lterr.
have y'pos : (0 <= (reciprocal_pol l).[y'])%R.
  rewrite -[_ _ y']addr0 -{2}(addNr (reciprocal_pol l).[x1]) addrA
   -{2}(opprK (_ _ x1)) subr_gte0 /=.
  apply: le_trans (_ : k * (y' - x1) <= _)=> /=.
    by rewrite /y' (addrC x1) addrK mulrN mulrC mulrVK // unitfE gt_eqF.
  by apply sl => //.
move: (diff_xn_ub (size l - 1) _ (@ltr01 R)) => [u [u0 up]].
have [u' [u1 u'u]] : exists u', (1 <= u' /\ u <= u')%R.
  case cmp: (1 <= u)%R; first by exists u; rewrite lexx cmp.
  by exists 1%R; rewrite lexx; split=> //; rewrite ltW // ltNge cmp.
have u'0 : (0 < u')%R by apply: lt_le_trans u1.
(*have u'unit : GRing.unit u' by apply/negP; move/eqP=> q; rewrite q lterr in u'0.*)
have divu_ltr : forall x : R, (0 <= x)%R -> (x / u' <= x)%R.
  move => x x0.
  rewrite ler_pdivr_mulr//.
  by rewrite ler_pemulr//.
(*   rewrite ler_eqVlt in x0; case/orP: x0 => [x0 | x0]. *)
(*      rewrite /=.  -lter_mulpl. *)

(* -(eqP x0) mulr0 lterr. *)
(*   rewrite -ltef_divpl // mulrV //. *)

(*   by apply/negP; move/eqP=> q; rewrite q lterr in x0. *)
have y'0 : (0 < y')%R by apply: lt_trans y'1.
pose y := y' + 1.
have y'y : y' < y by rewrite /y -{1}(addr0 y') ltr_add2l.
have y1 : x1 < y by apply: lt_trans y'1 _.
have ypos : (0 < (reciprocal_pol l).[y])%R.
  apply: le_lt_trans y'pos _=> /=.
  rewrite -subr_gte0 /=; apply: lt_le_trans (_ : k * (y - y') <= _)=> /=.
    by rewrite mulr_gt0// subr_gt0.
  by apply: sl=> //; apply: ltW.
have y0 : (0 < y)%R by apply: lt_trans y'y.
pose k' :=  ((k * x1 ^+ 2 * y ^- 1 ^+ (size l - 1))/(1+1)).
have k'p : (0 < k')%R.
  rewrite /k' !mulr_gt0//.
    rewrite exprn_gt0//.
    by rewrite invr_gt0//.
  by rewrite invr_gt0// addr_gt0// ltr01.
pose e : R := k' / u'.
have ep: (0 < e)%R by rewrite divr_gt0.
move: (cut_epsilon _ ep) => [e1 [e2 [[e1p [e2p e1e2e] [e1e e2e]]]]].
move: (@constructive_ivt _ (@reciprocal_pol _ l) _ _ _ y'1 nx1 y'pos e1p).
move=> [[a b']].
rewrite {1}/pair_in_interval.
move=> /and5P[/and3P[cla ? clb']].
rewrite /pair_in_interval.
move=> /and3P[x1a ab b'y' nega posb' ?].
(*  [a [b' [cla [nega [posb' [clb' [x1a [ab b'y']]]]]]]].*)
move: (cm3 y y0 (reciprocal_pol l)) => [c cp].
have a0 : (0 < a)%R by apply: lt_le_trans x1a.
have c0 : (0 < c)%R.
  rewrite -(@pmulr_lgt0 _ (b' - a)) ?subr_gt0//.
  apply: lt_le_trans
   (_ : `|(reciprocal_pol l).[b'] - (reciprocal_pol l).[a] |
          <= _); last first.
    apply: cp.
    - exact: ltW.
    - exact: ltW.
    - by rewrite (le_trans b'y')// ltW.
  by rewrite normr_gt0// gt_eqF// subr_gt0.
(*have uc: GRing.unit c by apply/negP; move/eqP => q; rewrite q lterr in c0.*)
have [b [b'b [clb blty]]] : exists b, b' < b /\ c * (b - b') < e2 /\ b <= y.
  move: (cut_epsilon _ e2p) => [e3 [e4 [[e3p [e4p e3e4e2] [e3e2 e4e2]]]]].
  case cmp: (b' + e2/c <= y).
    exists (b' + e3/c).
    split.
      by rewrite ltr_addl// divr_gt0.
    split.
      by rewrite (addrC b') addrK mulrA (mulrC c) mulfK // gt_eqF.
    apply: le_trans cmp; rewrite ler_add2l//.
    by rewrite ler_pmul// ltW// invr_gt0.
  exists y; split.
    by rewrite (le_lt_trans b'y').
  split => //.
  by rewrite mulrC -ltr_pdivl_mulr// ltr_subl_addl ltNge cmp.
pose n := ((size l))%:R - 1.
have b'0 : (0 < b')%R by apply: lt_trans ab.
have b0 : (0 < b)%R by apply: lt_trans b'b.
(*have ua: GRing.unit a by apply/negP; move/eqP=> q; rewrite q lterr in a0.
have ub': GRing.unit b' by apply/negP; move/eqP=> q; rewrite q lterr in b'0.*)
have b'v0: (0 < b'^-1)%R by rewrite invr_gte0.
have bv0 : (0 < b^-1)%R by rewrite invr_gte0.
have bb'v: b^-1 < b'^-1 by rewrite ltf_pinv.
exists b^-1; exists a^-1; exists k'.
split=> //.
split; first by rewrite (lt_le_trans bb'v)// lef_pinv// ltW.
split; first by rewrite invf_lt1// (lt_le_trans _ x1a).
split; first by [].
split.
  move => x x0 xb.
  have xv0 : (0 < x^-1)%R by rewrite invr_gt0.
  have xexp0 : (0 < x^-1 ^+ (size l - 1))%R by rewrite exprn_gt0.
  have b'x : b' < x^-1.
    by rewrite -(invrK b')// ltf_pinv// (le_lt_trans _ bb'v).
  rewrite -(pmulr_rgt0 _ xexp0) -{2}[x]invrK -horner_reciprocal; last first.
    by rewrite unitfE gt_eqF.
  apply: (le_lt_trans posb'); rewrite -subr_gte0 /=.
  apply: lt_le_trans (_ : k * (x^-1 - b') <= _)=> /=.
    by rewrite mulr_gt0// subr_gt0.
  by apply: sl => //; rewrite (le_trans x1a)// ltW.
split.
  move => x a1x xlt1.
  have x0 : (0 < x)%R by apply: lt_trans a1x; rewrite invr_gt0.
(*  have ux: GRing.unit x by apply/negP;move/eqP=>q; rewrite q lterr in x0.
  have uxv : GRing.unit x^-1 by rewrite unitr_inv.*)
  have xv0 : (0 < x^-1)%R by rewrite invr_gt0.
  have x1a0 : (x^-1 < a)%R by rewrite -[a]invrK ltf_pinv// posrE// invr_gt0.
  have xexp0 : (0 < x^-1 ^+ (size l - 1))%R by apply: exprn_gt0.
  rewrite -(pmulr_rlt0 _ xexp0) -{2}[x]invrK -horner_reciprocal//; last first.
    by rewrite unitfE gt_eqF.
  case cmp: (x^-1 <= x1); last (move/negbT:cmp => cmp).
    by apply: neg => //; rewrite -invr1 ltf_pinv// ?posrE ltr01//.
  apply: lt_trans nega; rewrite -subr_gte0.
  apply: lt_le_trans (_ : k * (a - x^-1) <= _).
    by rewrite mulr_gt0// subr_gt0.
  apply: sl => //.
  rewrite -ltNge in cmp.
  exact: ltW.
move => x z bvx xz zav ; rewrite le_eqVlt in xz; move/orP: xz => [xz | xz].
  by rewrite (eqP xz) !addrN mulr0 lexx.
have x0: (0 < x)%R by apply: lt_trans bvx.
have z0 : (0 < z)%R by apply: (lt_trans x0).
(*have ux: GRing.unit x by apply/negP;move/eqP=>q; rewrite q lterr in x0.
have uz: GRing.unit z by apply/negP;move/eqP=>q; rewrite q lterr in z0.*)
have invo_rec : forall l, reciprocal_pol (reciprocal_pol l) = l.
  (*by move => l'; rewrite /reciprocate_pol revK.*) admit.
rewrite -(invo_rec _ l).
rewrite (@horner_reciprocal _ _ x) //; last by rewrite unitfE gt_eqF.
rewrite (@horner_reciprocal _ _ z) //; last by rewrite unitfE gt_eqF.
rewrite reciprocal_size; last first.
  admit.
rewrite (_ : _ * _ - _ = (x ^+ (size l - 1) - z ^+ (size l - 1)) *
                     (reciprocal_pol l).[x ^-1] +
                     ((reciprocal_pol l).[x ^-1] -
                      (reciprocal_pol l).[z ^-1]) *
                      z ^+ (size l - 1)); last first.
  by rewrite !mulrDl !mulNr ![_.[_] * _]mulrC !addrA addrNK.
set t1 := _ * _.[_].
set t3 := (_.[_] - _).
set t2 := t3 * _.
pose k1 := -k'; pose k2 := k' + k'.
have times2 : forall a : rat, a + a = (1 + 1) * a.
  by move => a'; rewrite mulrDl !mul1r.
have k2p : k2 = (k * x1 ^+ 2 * y ^-1 ^+ (size l - 1)).
  rewrite /k2 /k' -mulr2n -mulr_natl.
  rewrite -(mulrC (1 + 1)^-1) mulrA mulfV; first  by rewrite mul1r.
  have twop : (0 < (1 + 1))%Q by [].
  by rewrite gt_eqF// ltr0n.
rewrite (_ : k' = k1 + k2); last by rewrite /k1 /k2 addrA addNr add0r.
rewrite mulrDl; apply: ler_add; last first.
  have maj' : t3 * y^-1 ^+ (size l - 1) <= t3 * z^+ (size l - 1).
    have maj : y^-1 ^+(size l - 1) <= z ^+ (size l - 1).
      case: (size l - 1)%N => [ | n']; first by rewrite !expr0 lexx.
      (*rewrite lef_expS2 /=.
          apply: ltrW(lter_trans _ xz); apply: ler_lte_trans bvx.
          by apply: ltef_invpp.
        by apply: ltrW; rewrite invf_gte0.
      by apply: ltrW.*) admit.
(*    rewrite lter_mulpl // /t3.
    apply: lter_le_trans (_ : k * (x^-1 - z^-1) <= _); last first.
      apply: sl.
        rewrite -[x1]invrK // ltef_invpp //. 
          by rewrite invf_gte0.
        apply: ltrW(lter_le_trans zav _).
        by apply: ltef_invpp => //.
      by apply: ltef_invpp.
    apply: mulr_gte0pp=> /=; first by rewrite ltrW.
    by rewrite subr_gte0; apply: ltef_invpp=> //=; apply: ltrW.*) admit.
  apply: le_trans maj'; rewrite /t3 k2p mulrAC.
(*  rewrite ltef_mulpr; last by apply expf_gt0; rewrite invf_gte0.
  apply: lter_trans (_ : k * (x^-1 - z^-1) <= _).
    rewrite ![k * _]mulrC mulrAC ltef_mulpr; last by [].
    rewrite -[x^-1](mulrK uz) -{2}[z^-1](mulrK ux) -(mulrC x) -(mulrC z).
    rewrite (mulrAC x) -!(mulrA _ (x^-1)) -mulr_subl (mulrC (z - x)).
    rewrite ltef_mulpr /=; last by rewrite subr_gte0.
    apply: lter_trans (_ : x1/z <= _).
      rewrite lter_mulpl //=; first by apply: ltrW.
      apply: lter_trans x1a _; rewrite -(invrK a); apply: ltef_invpp=> //=; last exact: ltrW.
      by rewrite invf_gte0.
    rewrite ltef_mulpr //. 
      rewrite -[x1]invrK //; apply: ltef_invpp => //.
        by rewrite invf_gte0.
      apply: ltrW(lter_trans xz _).
      by apply: lter_le_trans zav _; apply: ltef_invpp.
    by rewrite invf_gte0.
  apply: sl.
    apply: ltrW(ler_lte_trans x1a _).
    by rewrite -[a]invrK; apply: ltef_invpp => //; rewrite invf_gte0.
  by apply: ltef_invpp  => //.*) admit.
rewrite /t1/k1/k' {t2 t3}.
have xzexp : (x ^+ (size l - 1) <= z ^+ (size l - 1)).
  case sizep : (size l - 1)%N => [ | n'].
    by rewrite !expr0 ltexx.
(*  by rewrite lef_expS2 //= ltrW.*) admit.
case: (lerP 0 ((reciprocal_pol l).[x^-1])) => sign; last first.
  (*apply: le_trans (_ : 0 <= _).

    rewrite mulNr lter_oppl oppr0; apply: mulr_ge0pp; last first.
      by rewrite subr_gte0 /= ltrW.
    apply: ltrW; exact k'p.
  apply: mulr_gte0nn.
    by rewrite subr_lte0.
  by apply: ltrW.
*)
  admit.
rewrite mulNr lter_oppl -mulNr opprB.
have rpxe : (reciprocal_pol l).[x^-1] <= e.
  apply:le_trans (_ : (reciprocal_pol l).[b] <= _) => /=.
    rewrite -subr_gte0 /= ; apply: le_trans (_ : k * (b - x^-1) <= _).
      rewrite mulr_ge0//.
        exact: ltW.
      rewrite subr_ge0//.
      admit.
    apply: sl.
    rewrite -[x1]invrK //. (*; apply: ltef_invpp => //.
        by rewrite invf_gte0.
      by apply: ltrW(lter_le_trans (lter_trans xz zav) _); apply: ltef_invpp.
    by rewrite -[b]invrK //; apply: ltef_invpp.*) admit.
    admit.
  rewrite -[_ _ b]addr0 -(addrN ((reciprocal_pol l).[b'])) addrA.
  rewrite (addrC (_.[b])) -addrA; apply: le_trans e1e2e.
  apply: ler_add; first by [].
(*  apply: lter_abs; apply: lter_trans (ltrW clb).
  by apply: cp; last done; apply: ltrW.*) admit.
apply: le_trans (_ : (z^+ (size l - 1) - x ^+ (size l - 1)) * e <= _).
  move: xzexp; rewrite -subr_gte0 le_eqVlt; case/orP=> [xzexp | xzexp] /=.
    by rewrite /= -(eqP xzexp) !mul0r.
  (*rewrite -mulr_subr mulr_gte0pp //=; first by rewrite subr_gte0 /= ltrW.
  by rewrite subr_gte0.*) admit.
rewrite [_ * e]mulrC; apply: le_trans (_ : e * (u' * (z - x)) <= _)=> /=.
  rewrite ler_pmul2l//.
  apply: le_trans (_ : u * (z - x) <= _).
    apply: up => //.
      by apply: ltW.
    apply: ltW (lt_trans zav _).
    (*; rewrite -invr1; apply: ltef_invpp => //.
    by apply: lter_le_trans x1gt1 _.*) admit.
  by rewrite ler_pmul2r// subr_gt0.
rewrite mulrA.
rewrite ler_pmul2r// ?subr_gt0//.
rewrite /e divrK// ?unitfE.
by rewrite gt_eqF//.
Admitted.

(* TODO(rei)
Lemma Bernstein_isolate : forall a b l, a < b ->
   alternate (Mobius l a b) -> one_root1 l a b.
Proof.
rewrite /Mobius => a b l altb alt.
rewrite (_ : a = a + (a - a)); last by rewrite addrN addr0.
rewrite (_ : b = a + (b - a)); last by rewrite (addrC b) addrA addrN add0r.
apply one_root1_translate.
rewrite addrN (_ : (b-a) = (b-a) * 1); last by rewrite mulr1.
rewrite (_ : 0 =  (b-a) * 0); last by rewrite mulr0.
apply one_root1_expand; first by rewrite -(addrN a) lter_add2l.
apply one_root_reciprocate.
rewrite -[1]addr0; apply one_root2_translate.
by apply: alt_one_root2.
Qed.
*)

