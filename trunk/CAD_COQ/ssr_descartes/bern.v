Require Import QArith ZArith Zwf Omega.
Require Import ssreflect eqtype ssrbool ssrnat div fintype seq ssrfun.
Require Import bigops groups choice binomial.
Require Export ssralg infra_std pol cmvt desc.

Import GroupScope .
Import GRing.Theory .
Import OrderedRing.Theory.
Open Local Scope ring_scope .

Set Printing Width 50.

(* Two predicates to describe that a polynomial has only one root,
  one_root1 l a b :
     there exists c, d, and k, so that a,c,d,b is ordered, k is positive,
     the polynomial value is positive between a and c, negative between d and b
     the slope is less than -k between c and d.
  This statement is specifically suited to speak about roots inside the
  interval a b.

  one_root2 l a :
     there exists c, d, and k, so that a is smaller than c, k is positive,
     the polynomical value is negative between a and c, and the slope is
     larger than k above c.

  A consequence of one_root2 is that there can be only one root above c, hence
  only one root above a.
    
*)
Definition one_root1 (l : seq Qcb) (a b : Qcb) :=
  exists c, exists d, exists k, 
     a < c /\ c < d /\ d < b /\ 0 < k /\
     (forall x, a < x -> x <= c -> 0 < eval_pol l x) /\
     (forall x, d < x -> x < b -> eval_pol l x < 0) /\
     (forall x y, c < x -> x <= y -> y < d ->
        k * (y - x) <= eval_pol l x - eval_pol l y ).

Definition one_root2 (l : seq Qcb) (a : Qcb) :=
   exists c, exists k,
     a < c /\ 0 < k /\
     (forall x, a < x -> x <= c -> eval_pol l x < 0) /\
     (forall x y, c <= x -> x < y -> 
         k * (y - x) <= eval_pol l y - eval_pol l x).

Lemma alt_one_root2 : forall l, alternate l -> one_root2 l 0.
move => l a;
  move: (desc l a) => [x1 [x2 [k [x1p [x1x2 [kp [neg [sl pos]]]]]]]].
exists x1; exists k.
by split; first done; split; first done; split; done.
Qed.

Lemma one_root2_translate :
  forall l a b, one_root2 (translate_pol' l a) b -> one_root2 l (a + b).
Proof.
move=> l a b [x1 [k [x1a [kp [neg sl]]]]].
exists (a + x1); exists k.
split; first by rewrite  ler_add2r.
split; first by [].
split.
  move=> x abx xax1; rewrite (_ : x = x - a + a); last first.
    by rewrite addrNK.
  rewrite  -translate_pol'q; apply: neg.
    by rewrite -ler_addrA addrC.
  by rewrite -ler_addrA addrC.
move=> x y ax1x xy.
have t: forall z, z = (z - a) + a by move=> z; rewrite addrNK.
rewrite {2}(t y) {2}(t x) -!(translate_pol'q l) (_ : y - x = y - a - (x - a)).
  apply: sl; first by rewrite ler_sublA.
  by  rewrite ler_add2l.
by rewrite [x + _]addrC oppr_add opprK addrA addrNK.
Qed.

Lemma one_root1_translate :
  forall l a b c, one_root1 (translate_pol' l c) a b ->
    one_root1 l (c + a) (c + b).
Proof.
move=> l a b c [x1 [x2 [k [ax1 [x1x2 [x2b [kp [pos [neg sl]]]]]]]]].
exists (c + x1); exists (c + x2); exists k.
split; first by rewrite ler_add2r.
split; first by rewrite ler_add2r.
split; first by rewrite ler_add2r.
split; first by [].
split.
  move=> x cax xcx1; rewrite (_ : x = x - c + c); last by rewrite addrNK.
  by rewrite -translate_pol'q; apply pos; rewrite -ler_addlA.
split.
  move=> x cx2x xcb; rewrite (_ : x = x - c + c); last by rewrite addrNK.
  by rewrite -translate_pol'q; apply: neg; rewrite -?ler_addlA // ler_sublA.
move=> x y cx1x xy ycx2.
have t: forall z, z = (z - c) + c by move=> z; rewrite addrNK.
rewrite {2}(t x) {2}(t y) (_ : y - x = y - c - (x - c)); last first.
  by rewrite [x + _]addrC oppr_add opprK addrA addrNK.
rewrite -!(translate_pol'q l); apply: sl; rewrite ?ler_add2l -?ler_addlA //.
by rewrite ler_sublA.
Qed.

Lemma one_root1_expand :
  forall l a b c, 0 < c -> one_root1 (expand l c) a b ->
    one_root1 l (c * a) (c * b).
Proof.
move=> l a b c cp [x1 [x2 [k [ax1 [x1x2 [x2b [kp [pos [neg sl]]]]]]]]].
exists (c * x1); exists (c * x2); exists (k / c).
have tc : 0 < c^-1 by rewrite -invf_le0.
have uc: GRing.unit c by apply/negP; move/eqP => q; rewrite q lerr in cp.
split; first by rewrite ltf_mulpl.
split; first by rewrite ltf_mulpl.
split; first by rewrite ltf_mulpl.
split; first by rewrite mulf_cp0p.
split.
  move=> x acx xx1c; rewrite (_ : x = c * (x/c)); last by rewrite mulrC mulrVK.
  by rewrite -eval_expand; apply: pos; rewrite lef_divpl 1?mulrC.
split.
  move=> x cx2x xcb; rewrite (_ : x = c * (x/c)); last by rewrite mulrC mulrVK.
  rewrite -eval_expand; apply: neg; first by rewrite lef_divpl 1?mulrC.
  by rewrite lef_divpr 1?mulrC.
have t: forall z, z = c * (z/c) by move=> z; rewrite [c * _]mulrC mulrVK.
move=> x y cx1x xy ycx2; rewrite -mulrA mulr_addr mulrN ![c^-1 * _]mulrC
  {2}(t x) {2}(t y) -!(eval_expand l); apply: sl.
   by rewrite lef_divpl // mulrC.
 by rewrite ltf_mulpr.
by rewrite lef_divpr // mulrC.
Qed.

Lemma diff_xn_ub :
  forall n z, 0 < z -> exists k, 0 <= k /\
   forall x y:Qcb, 0 < x -> x <= y -> y <= z ->
      y ^+ n - x ^+ n <= k * (y - x).
Proof.
move => n; elim: n => {n} [z z0| n IHn z z0].
  by exists 0.
case: (IHn z z0) => k [k0 kp].
exists (z*k + z ^+ n); split => [ | x y x0 xy yz].
  apply: ler_addpl; first by apply: mulr_ge0pp => //; apply: ltrW.
  by apply: ltrW; apply: expf_gt0.
rewrite !exprS.
rewrite (_: _ * _ - _ =  y * (y ^+ n - x ^+ n) + (y - x) * x ^+ n); last first.
  by rewrite mulr_addl mulr_addr addrA mulrN mulNr addrNK.
rewrite [_ * (y-x)]mulr_addl; apply ler_add.
  rewrite -mulrA; apply: ler_trans (_ : y * (k * (y - x)) <= _).
    apply ler_mulpl; first by apply: ler_trans xy; apply: ltrW.
    by apply: kp.
  apply: ler_mulpr => //; by apply: mulr_ge0pp => //; rewrite subr_ge0.
rewrite (mulrC (_ - _)); apply: ler_mulpr; first by rewrite subr_ge0.
case: {IHn kp} n; first by rewrite !expr0 lerr.
move => n; rewrite -lef_expS2.
    by apply: ler_trans (_: y <= _).
  by apply: ltrW.
by apply: ler_trans (_: y <= _) => //; apply: ler_trans (_ : x <= _) => //;
  apply: ltrW.
Qed.

Lemma one_root_reciprocate :
  forall l, one_root2 (reciprocate_pol l) 1 -> one_root1 l 0 1.
Proof.
move=> l [x1 [k [x1gt1 [kp [neg sl]]]]].
have uk: GRing.unit k by apply/negP; move/eqP => q; rewrite q lerr in kp.
set y := x1 - eval_pol (reciprocate_pol l) x1 / k.
have y1: x1 < y.
  rewrite /y -(ler_add2r (-x1)) addNr addrA addNr add0r -mulNr.
  apply: mulf_gt0pp; last by rewrite -(ltf_mulpl _ _ kp) mulr0 mulrV.
  by rewrite ler_oppl oppr0; apply neg; rewrite // lerr.
have nx1 : eval_pol (reciprocate_pol l) x1 < 0 by apply: neg; rewrite // lerr.
have ypos : 0 <= eval_pol (reciprocate_pol l) y.
  rewrite -[_ _ y]addr0 -{2}(addNr (eval_pol (reciprocate_pol l) x1)) addrA
   -{2}(opprK (_ _ x1)) subr_ge0.
  apply: ler_trans (_ : k * (y - x1) <= _);
    first by rewrite /y (addrC x1) addrK mulrN mulrC mulrVK // lerr.
  apply sl => //; first by rewrite lerr.
have [e [ep pe]] : exists e, 0 < e /\ e < k / y ^+ (size l) by admit.
move: (cut_epsilon _ ep) => [e1 [e2 [e1p [e2p [e1e2 [e1e e2e]]]]]].
move: (constructive_mvt (reciprocate_pol l) _ _ y1 nx1 ypos _ e1p) =>
  [a [b' [cla [nega [posb' [clb' [x1a [ab b'y]]]]]]]].
have y0: 0 < y by apply: ltr_trans y1; apply: ltr_trans x1gt1.
move: (cm3 y y0 (reciprocate_pol l)) => [c cp].
have [b [b'b clb]] : exists b, b' < b /\ c * (b - b') < e2 by admit.
pose k' :=  ((k * y ^+ 2 * y ^- 1 ^+ (size l - 1))/(1+1)).
pose n := Qcb_make (Z_of_nat (size l)) - 1.
have k'p : 0 < k'.
  rewrite /k'; apply: mulf_gt0pp; last by[].
  apply: mulf_gt0pp; first by apply: mulf_gt0pp => //; apply expf_gt0.
  by apply: expf_gt0; rewrite -invf_le0; apply: expf_gt0.
have a0 : 0 < a by apply: ltr_le_trans x1a; apply: ltr_trans x1gt1.
have b'0 : 0 < b' by apply: ltr_trans ab.
have b0 : 0 < b by apply: ltr_trans b'b.
have ua: GRing.unit a by apply/negP; move/eqP=> q; rewrite q lerr in a0.
have ub': GRing.unit b' by apply/negP; move/eqP=> q; rewrite q lerr in b'0.
have b'v0: 0 < b'^-1 by rewrite -invf_le0.
have bv0 : 0 < b^-1 by rewrite -invf_le0.
have bb'v: b^-1 < b'^-1 by apply: ltf_invpp => //.
have ub: GRing.unit b by apply/negP; move/eqP=> q; rewrite q lerr in b0.
exists b^-1; exists a^-1; exists k'.
split; first by rewrite -invf_le0.
split; first by apply: ltf_invpp => //; apply: ltr_trans b'b.
split.
  by rewrite -invr1; apply: ltf_invpp => //; apply: ltr_le_trans x1a.
split; first by [].
split.
  move => x x0 xb.
  have ux: GRing.unit x by apply/negP; move/eqP=>q; rewrite q lerr in x0.
  have xv0: 0 < x^-1 by rewrite -invf_le0.
  have xexp0 : 0 < x^-1 ^+ (size l - 1) by apply: expf_gt0.
  have b'x: b' < x^-1.
    by rewrite -(invrK b') //; apply: ltf_invpp => //; apply: (ler_lt_trans xb).
  rewrite -(ltf_mulpl _ _ xexp0) mulr0 -{2}[x]invrK -reciprocateq;
   last by rewrite unitr_inv.
  apply: (ler_lt_trans posb'); rewrite -subr_le0.
  apply: ltr_le_trans (_ : k*(x^-1 - b') <= _).
    by rewrite -(mulr0 k) ltf_mulpl // subr_le0.
  by apply: sl; first apply:ltrW(ler_lt_trans x1a _).
split.
  move => x a1x xlt1.
  have x0 : 0 < x by apply: ltr_trans a1x; rewrite -invf_le0.
  have ux: GRing.unit x by apply/negP;move/eqP=>q; rewrite q lerr in x0.
  have uxv : GRing.unit x^-1 by rewrite unitr_inv.
  have xv0 : 0 < x^-1 by rewrite -invf_le0.
  have x1a0 : x^-1 < a.
    by rewrite -[a]invrK; apply: ltf_invpp => //; rewrite -invf_le0.
  have xexp0 : 0 < x^-1 ^+ (size l - 1) by apply: expf_gt0.
  rewrite -(ltf_mulpl _ _ xexp0) mulr0 -{2}[x]invrK -reciprocateq;
   last by rewrite unitr_inv.
  case cmp: (x^-1 <= x1); last (move/negbT:cmp => cmp).
    by apply: neg => //; rewrite -invr1; apply: ltf_invpp.
  apply: ltr_trans nega; rewrite -subr_le0.
  apply: ltr_le_trans (_ : k * (a - x^-1) <= _).
    by rewrite -(mulr0 k) ltf_mulpl // subr_le0.
  by apply: sl; first apply:ltrW.
(*
...
move=> x z b1z xz za1; rewrite ler_ltreq orbC in xz; move/orP: xz => [xz | xz].
  by rewrite (eqP xz) !addrN mulr0 ler_refl.
have x0: 0 < x by apply: ltr_trans b1z; rewrite invr_ltr.
have xm1 : 0 < x^-1 by rewrite invr_ltr.
have xe0: 0 < x^-1^+(size l - 1) by apply: expf_gt0.
apply (ler_Ilcompat_r xe0).
rewrite (mulr_addr _ (eval_pol _ _)) mulrN.
rewrite (_ : eval_pol l x = eval_pol l (x^-1)^-1); last by rewrite invrK.
have ux: GRing.unit x by apply/negP;move/eqP=>q; rewrite q lerr in x0.
have x10 : GRing.unit x^-1 by rewrite unitr_inv.
rewrite -reciprocateq; last by [].
have xz0 : 0 < x * z by rewrite mulf_cp0p => //; apply: (ltr_trans x0).
have z0 : 0 < z by apply (ltr_trans x0).
have uz: GRing.unit z by apply/negP;move/eqP=>q; rewrite q lerr in z0.
have invzltinvx: z^-1 < x^-1.
  by apply: (ltr_Ilcompat_r xz0); rewrite {2}[x*_]mulrC !mulrK //.
have ze0 : 0 < z^-1 ^+ (size l - 1) by apply: expf_gt0; rewrite invr_ltr.
case pzpos : (0 < eval_pol l z); move: pzpos; last first.
  rewrite ltrNger; move/negbFE => pzneg.


*)
Admitted.

Lemma Bernstein_isolate : forall a b l, a < b ->
   alternate (Bernstein_coeffs l a b) -> one_root1 l a b.
Proof.
rewrite /Bernstein_coeffs => a b l altb alt.
rewrite (_ : a = a + (a - a)); last by rewrite addrN addr0.
rewrite (_ : b = a + (b - a)); last by rewrite (addrC b) addrA addrN add0r.
apply one_root1_translate.
rewrite addrN (_ : (b-a) = (b-a) * 1); last by rewrite mulr1.
rewrite (_ : 0 =  (b-a) * 0); last by rewrite mulr0.
apply one_root1_expand; first by rewrite -(addrN a) ler_add2l.
apply one_root_reciprocate.
rewrite -[1]addr0; apply one_root2_translate.
by apply: alt_one_root2.
Qed.
