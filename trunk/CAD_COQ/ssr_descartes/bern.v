Require Import QArith ZArith Zwf Omega.
Require Import ssreflect eqtype ssrbool ssrnat div fintype seq ssrfun.
Require Import bigops groups choice binomial.
Require Export ssralg xssralg infra pol cmvt desc.

Import GroupScope .
Import GRing.Theory .
Import GOrdered.
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
     a <<! c /\ c <<! d /\ d <<! b /\ 0 <<! k /\
     (forall x, a <<! x -> x <<= c -> 0 <<! eval_pol l x) /\
     (forall x, d <<! x -> x <<! b -> eval_pol l x <<! 0) /\
     (forall x y, c <<! x -> x <<= y -> y <<! d ->
        k * (y - x) <<= eval_pol l x - eval_pol l y ).

Definition one_root2 (l : seq Qcb) (a : Qcb) :=
   exists c, exists k,
     a <<! c /\ 0 <<! k /\
     (forall x, a <<! x -> x <<= c -> eval_pol l x <<! 0) /\
     (forall x y, c <<= x -> x <<! y -> 
         k * (y - x) <<= eval_pol l y - eval_pol l x).

Lemma alt_one_root2 : forall l, alternate l -> one_root2 l 0.
Proof.
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
split; first by apply ltrTr.
split; first by [].
split.
  move=> x abx xax1; rewrite (_ : x = x - a + a); last first.
    by rewrite addrNK.
  rewrite  -translate_pol'q; apply: neg.
    by rewrite -(ltrTrb a) [a + (x - a)]addrC addrNK.
  by rewrite -(lerTrb a) [a + (x - a)]addrC addrNK.
move=> x y ax1x xy.
have t: forall z, z = (z - a) + a by move=> z; rewrite addrNK.
rewrite {2}(t y) {2}(t x) -!(translate_pol'q l) (_ : y - x = y - a - (x - a)).
  apply: sl.
    by rewrite -(lerTrb a) [a + (x - a)]addrC addrNK.
  by apply ltrTl.
by rewrite [x + _]addrC oppr_add opprK addrA addrNK.
Qed.

Lemma one_root1_translate :
  forall l a b c, one_root1 (translate_pol' l c) a b ->
    one_root1 l (c + a) (c + b).
Proof.
move=> l a b c [x1 [x2 [k [ax1 [x1x2 [x2b [kp [pos [neg sl]]]]]]]]].
exists (c + x1); exists (c + x2); exists k.
split; first by apply ltrTr.
split; first by apply ltrTr.
split; first by apply: ltrTr.
split; first by [].
split.
  move=> x cax xcx1; rewrite (_ : x = x - c + c); last by rewrite addrNK.
  rewrite -translate_pol'q; apply pos.
    by rewrite -(ltrTrb c) [c + (_ + _)]addrC addrNK.
  by rewrite -(lerTrb c) [c + (_ + _)]addrC addrNK.
split.
  move=> x cx2x xcb; rewrite (_ : x = x - c + c); last by rewrite addrNK.
  by rewrite -translate_pol'q; apply: neg; rewrite -(ltrTrb c)
    [c + (_ + _)]addrC addrNK.
move=> x y cx1x xy ycx2.
have t: forall z, z = (z - c) + c by move=> z; rewrite addrNK.
rewrite {2}(t x) {2}(t y) (_ : y - x = y - c - (x - c)); last first.
  by rewrite [x + _]addrC oppr_add opprK addrA addrNK.
rewrite -!(translate_pol'q l); apply: sl.
    by rewrite -(ltrTrb c) [c + (_ + _)]addrC addrNK.
  by apply: lerTl.
by rewrite -(ltrTrb c) [c + (_ + _)]addrC addrNK.
Qed.

Lemma one_root1_expand :
  forall l a b c, 0 <<! c -> one_root1 (expand l c) a b ->
    one_root1 l (c * a) (c * b).
Proof.
move=> l a b c cp [x1 [x2 [k [ax1 [x1x2 [x2b [kp [pos [neg sl]]]]]]]]].
exists (c * x1); exists (c * x2); exists (k / c).
have tc : 0 <<! c^-1 by rewrite invr_ltr.
have uc: GRing.unit c by apply/negP; move/eqP => q; rewrite q ltr_irrefl in cp.
split; first by apply: ltr_lcompat.
split; first by apply: ltr_lcompat.
split; first by apply: ltr_lcompat.
split; first by apply: ltr_0_lcompat.
split.
  move=> x acx xx1c; rewrite (_ : x = c * (x/c)); last by rewrite mulrC mulrVK.
  rewrite -eval_expand; apply: pos.
    by apply (ltr_Ilcompat_r cp); rewrite [c * (_ * _)]mulrC mulrVK.
  by apply (ler_Ilcompat_r cp); rewrite [c * (_ * _)]mulrC mulrVK.
split.
  move=> x cx2x xcb; rewrite (_ : x = c * (x/c)); last by rewrite mulrC mulrVK.
  by rewrite -eval_expand; apply: neg; apply (ltr_Ilcompat_r cp);
    rewrite [c * (_ * _)]mulrC mulrVK.
have t: forall z, z = c * (z/c) by move=> z; rewrite [c * _]mulrC mulrVK.
move=> x y cx1x xy ycx2; rewrite -mulrA mulr_addr mulrN ![c^-1 * _]mulrC
  {2}(t x) {2}(t y) -!(eval_expand l); apply: sl.
    by apply: (ltr_Ilcompat_r cp); rewrite [c * (_ * _)]mulrC mulrVK.
  by apply: (ler_Ilcompat_l cp); rewrite !mulrVK.
by apply: (ltr_Ilcompat_l cp); rewrite mulrVK // mulrC.
Qed.

(* This lemma is missing in xssralg. *)
Lemma ltr_exp : forall (x:Qcb) n, 0 <<! x -> 0 <<! x^+ n.
Proof.
move=> x n; elim: n => [ | p IHp] x0; first by [].
by rewrite exprS; apply: ltr_0_lcompat; last apply: IHp.
Qed.

Lemma ler_expr : forall n (x y:Qcb), 0 <<= x -> x <<= y -> x ^+ n <<= y ^+ n.
Proof.
move => n; elim: n => {n} [ x y x0 xy | n IHn x y x0 xy].
  by apply: ler_refl.
have: 0 <<= y by apply: ler_trans xy.
rewrite ler_ltreq; case/orP => [y0 | y0].
rewrite !exprS; apply: ler_trans (_ : x * y ^+ n <<= _).
  apply ler_2compat0l => //; first by apply ler_refl.
      by apply: ltrW; apply ltr_exp.
    by apply: IHn.
  apply ler_2compat0l => //; last by apply ler_refl.
  by apply: ltrW; apply ltr_exp.
rewrite -(eqP y0) in xy.
by rewrite (ler_antisym xy x0) -(eqP y0) !exprS !mul0r ler_refl.
Qed.
    
Lemma diff_xn_ub :
  forall n z, 0 <<! z -> exists k, 0 <<= k /\
   forall x y:Qcb, 0 <<! x -> x <<! y -> y <<! z ->
      y ^+ n - x ^+ n <<= k * (y - x).
Proof.
move => n; elim: n => {n} [z z0| n IHn z z0].
  by exists 0.
case: (IHn z z0) => k [k0 kp].
exists (z*k + z ^+ n); split => [ | x y x0 xy yz].
  apply: lerT0.
    apply: ler_0_lcompat; last by [].
    by apply: ltrW.
  by apply: ltrW; apply: ltr_exp.
rewrite !exprS.
rewrite (_: _ * _ - _ =  y * (y ^+ n - x ^+ n) + (y - x) * x ^+ n); last first.
  by rewrite mulr_addl mulr_addr addrA mulrN mulNr addrNK.
rewrite [_ * (y-x)]mulr_addl; apply lerT.
  apply: ler_trans (_ : y * k * (y-x) <<= _).
    rewrite -mulrA; apply: ler_2compat0l => //.
          by apply: ltrW; apply: ltr_trans xy.
        by apply: ler_refl.
      apply: ler_0_lcompat; first by []. 
      by rewrite -(addrN x) lerTl // ltrW.
    by apply: kp.
  apply:ler_2compat0l.
        apply ler_0_lcompat; last by [].
        by apply: ltrW; apply: ltr_trans xy.
      apply ler_2compat0l => //.
          by apply: ltrW; apply: ltr_trans xy.
        by apply: ltrW.
      by apply: ler_refl.
    by rewrite -(addrN x) lerTl // ltrW.
  by apply: ler_refl.
rewrite mulrC; apply: ler_2compat0l.
      by apply: ltrW; apply: ltr_exp.
    apply ler_expr; first by apply:ltrW.
    by apply: ltrW; apply: ltr_trans yz.
  by rewrite -(addrN x) lerTl // ltrW.
by apply: ler_refl.
Qed.

Lemma one_root2_size : forall a l, one_root2 l a -> 1 < size l.
Admitted.

Lemma reciprocate_size :  forall l, size (reciprocate_pol l) = size l.
Admitted.

Lemma ler_lcompat : forall x y z: Qcb_OComRingType,
   0 <<= x -> y <<= z -> x * y <<= x * z.
Proof.
move => x y z x0 yz.
Admitted.

Lemma ler_rcompat : forall x y z: Qcb_OComRingType,
   0 <<= y -> x <<= z -> x * y <<= z * y.
Proof.
by move => x y z x0 xz; rewrite ![_ * y]mulrC; apply: ler_lcompat.
Qed.

Lemma one_root_reciprocate :
  forall l, one_root2 (reciprocate_pol l) 1 -> one_root1 l 0 1.
Proof.
move=> l hor.
have: 1 < size (reciprocate_pol l) by apply: one_root2_size hor.
rewrite reciprocate_size => hs.
move: hor => [x1 [k [x1gt1 [kp [neg sl]]]]].
have x11 : x1 <<! x1 + 1 by rewrite -{1}[x1]addr0 ltrTrb.
have uk : GRing.unit k by apply/negP;move/eqP=>q; rewrite q ltr_irrefl in kp.
set y' := x1 - eval_pol (reciprocate_pol l) x1 / k.
(* Cette partie doit être simplifiée car on a pas besoin que
   eval_pol (reciprocate_pol l) y soit strictement positif, non neg suffit. *)
have [y [y1 y'y]] : exists y, x1 <<! y /\ y' <<! y.
  have y'1 : y' <<! y' + 1 by rewrite -{1}[y']addr0 ltrTrb.
  case h: (x1 <<! y'); last (move/negbT: h; rewrite -lerNgtr => h).
    by exists (y' + 1); split; first apply: ltr_trans y'1.
  by exists (x1 + 1); split; last apply: ler_ltr_trans x11.
have  {y' y'y} ypos : 0 <<! eval_pol (reciprocate_pol l) y.
  rewrite -[_ _ y]addr0 -(addrN (eval_pol (reciprocate_pol l) x1))
    addrA [_ _ y + _]addrC -addrA ltrTrb.
  apply: ltr_ler_trans (_ : k * (y - x1) <<= _).
    apply: ler_ltr_trans (_ : k * (y' - x1) <<! _).
      rewrite /y' [k * _]mulrC !mulr_addl mulNr mulrVK //.
      by rewrite [x1 * k + _]addrC mulNr addrK ler_refl.
    by apply: ltr_lcompat => //; apply ltrTl.
  by apply: sl; first apply ler_refl.
have x1neg := neg _ x1gt1 (ler_refl _).
pose n := Qcb_make (Z_of_nat (size l)) - 1.
have ltr1 : 0 <<! (1:Qcb) by [].
move: (diff_xn_ub (size l - 1) 1 ltr1) => [u [u0 up]].
have [u' [u1 u'u]] : exists u', 1<<= u' /\ u <<= u' by admit.
have u'0: 0 <<! u' by apply: ltr_ler_trans u1.
have u'unit : GRing.unit u'. 
  by apply/negP; move => q; rewrite (eqP q) ltr_irrefl in u'0.
have divu_ltr : forall x, 0 <<= x -> x / u' <<= x.
   move => x x0; rewrite -{2}(mulr1 x); apply ler_lcompat; first by [].
   by admit.
(* If we prove that the value is positive, we probably don't need to go
  through an existence proof. *)
have [e [ep pe]] : 
  exists e, 0 <<! e /\ e =
        ((k * y ^+ 2 * y ^- 1 ^+ (size l - 1) /(1 + 1)))/ u'.
  by admit.
(* The cut is probably useless, I guess everything can be done with only e. *)
move: (cut_epsilon _ ep) => [e1 [e2 [e1p [e2p [e1e2 [e1e e2e]]]]]].
have y0 : 0 <<! y by apply: ltr_trans y1; apply: ltr_trans x1gt1.
pose k' :=  ((k * y ^+ 2 * y ^- 1 ^+ (size l - 1))/(1+1)).
pose k2 := k' + k'.
have times2 : forall a:Qcb, a + a = (1 + 1) * a.
  by move => a; rewrite mulr_addl !mul1r.
have k2p : k2 = (k * y ^+ 2 * y ^-1 ^+ (size l - 1)).
  rewrite /k2 /k' times2 -(mulrC (1 + 1)^-1) mulrA mulrV; last first.
    have twop : 0 <<! ((1 + 1):Qcb) by apply: ltrT0.
    by apply/negP; move/eqP=>q; rewrite q ltr_irrefl in twop.
  by rewrite mul1r.
pose k1 := -k'.
have k'p : 0 <<! k'.
  rewrite /k'; apply: ltr_0_lcompat.
    apply: ltr_0_lcompat.
      apply: ltr_0_lcompat; first by [].
      by apply: ltr_exp.
    by apply: ltr_exp; rewrite invr_ltr.
  by apply: invr_ltr.
move: (constructive_mvt (reciprocate_pol l) _ _ y1 x1neg (ltrW ypos) _ ep) =>
  [a [b' [cla [nega [posb' [clb' [x1a [ab' b'y]]]]]]]].
(* A strange computation to find a b, where reciprocate_pol l has a
   positive value that is still smaller than e2. *)
move: (cm2 (reciprocate_pol l) y) => [c pc].
have [b [b'b clb]] : exists b, b' <<! b /\ c * (b - b') <<! e2 /\ b <<! y.
  by admit.
exists (b^-1); exists (a^-1); exists (k').
have a0 : 0 <<! a by apply:ltr_ler_trans x1a; first apply: ltr_trans x1gt1. 
have b'0 : 0 <<! b' by apply: ltr_trans ab'.
have b0 : 0 <<! b by apply:ltr_trans b'b.
have ua: GRing.unit a by apply/negP; move/eqP=> q; rewrite q ltr_irrefl in a0.
have ub' : GRing.unit b'
  by apply/negP; move/eqP=>q; rewrite q ltr_irrefl in b'0.
have ub: GRing.unit b by apply/negP; move/eqP=> q; rewrite q ltr_irrefl in b0.
split; first by rewrite invr_ltr.
split.
  apply: (ltr_Ilcompat_r a0); apply: (ltr_Ilcompat_l b0); rewrite mulrVK //.
  by rewrite mulrV // mul1r; apply: ltr_trans b'b.
split; first by rewrite -invr1_ltr0_1ltr; first apply: ltr_ler_trans x1a.
split; first by [].
split.
  move=> x x0 xb.
  have ux: GRing.unit x by apply/negP; move/eqP=>q; rewrite q ltr_irrefl in x0.
  have xV0: 0 <<! x^-1 by rewrite invr_ltr.
  have xb'0 : 0 <<! x*b'^-1 by apply: ltr_0_lcompat; rewrite ?invr_ltr.
  have bb'0 : 0 <<! b*b' by apply: ltr_0_lcompat.
  have b'x : b' <<! x^-1.
    apply: (ltr_Ilcompat_r xb'0); rewrite mulrVK // [x * _]mulrC mulrK //.
    apply: ler_ltr_trans xb _; apply: (ltr_Ilcompat_r bb'0).
    by rewrite mulrK // [b * _]mulrC mulrK //.
  have xexp0 : 0 <<! x^-1 ^+ (size l - 1) by apply: ltr_exp; rewrite invr_ltr.
  apply: (ltr_Ilcompat_r xexp0); rewrite mulr0.
  rewrite -{2}[x]invrK -reciprocateq; last by rewrite unitr_inv.
  apply: ler_ltr_trans posb' _.
  rewrite -(ltrTlb (-(eval_pol (reciprocate_pol l) b'))) addrN.
  apply: ltr_ler_trans (_ : k*(x^-1 - b') <<= _).
    by apply: ltr_0_lcompat; first done; rewrite -(ltrTlb b') add0r addrNK.
  by apply: sl; first apply: ltrW(ler_ltr_trans x1a _).
split.
  move=> x a1x xgt1.
  have x0 : 0 <<! x by apply: ltr_trans a1x; rewrite invr_ltr.
  have ux: GRing.unit x by apply/negP;move/eqP=>q; rewrite q ltr_irrefl in x0.
  have x10 : GRing.unit x^-1 by rewrite unitr_inv.
  have x1gt0 : 0 <<! x^-1 by rewrite invr_ltr.
  have x1a0 : 0 <<!a^-1*x by apply: ltr_0_lcompat; rewrite ?invr_ltr.
  have x1a' : x^-1 <<! a.
    by apply: (ltr_Ilcompat_r x1a0); rewrite mulrK // [_ * x]mulrC mulrVK.
  rewrite -[x]invrK //.
  have xexp0 : 0 <<! x^-1 ^+ (size l - 1) by apply: ltr_exp; rewrite invr_ltr.
  apply: (ltr_Ilcompat_r xexp0); rewrite mulr0 -reciprocateq //.
  case cmp: (x^-1 <<= x1); last (move/negbT:cmp; rewrite -ltrNger=> cmp).
    by apply: neg; first (apply: (ltr_Ilcompat_r x0); rewrite mulr1 mulrV).
  apply: ler_ltr_trans nega.
  rewrite -(lerTlb (-(eval_pol (reciprocate_pol l) x^-1))) addrN.
  apply: ler_trans (_ : k * (a - x^-1) <<= _).
    apply: ler_0_lcompat; first by apply: ltrW.
    by rewrite -(lerTlb x^-1) addrNK add0r ltrW.
  by apply: sl; first apply: ltrW.
move=> x z b1z xz za1; rewrite ler_ltreq orbC in xz; move/orP: xz => [xz | xz].
  by rewrite (eqP xz) !addrN mulr0 ler_refl.
have invo_rec :
  forall l, reciprocate_pol (reciprocate_pol l) = l.
  by admit.
have xmz0: 0 <<= z - x by rewrite -(addrN x); apply: lerTl; apply: ltrW.
have x0: 0 <<! x by apply: ltr_trans b1z; rewrite invr_ltr.
have ux: GRing.unit x by apply/negP;move/eqP=>q; rewrite q ltr_irrefl in x0.
have z0 : 0 <<! z by apply: (ltr_trans x0).
have uz: GRing.unit z by apply/negP;move/eqP=>q; rewrite q ltr_irrefl in z0.
rewrite -(invo_rec l) (reciprocateq _ x) // (reciprocateq _ z) //.
rewrite reciprocate_size.
rewrite (_ : _ * _ - _ = (x ^+ (size l - 1) - z ^+ (size l - 1)) *
                     eval_pol (reciprocate_pol l) x ^-1 +
                     (eval_pol (reciprocate_pol l) x ^-1 -
                      eval_pol (reciprocate_pol l) z ^-1) *
                      z ^+ (size l - 1)); last first.
  by rewrite !mulr_addl !mulNr ![eval_pol _ _ * _]mulrC !addrA addrNK.
set t1 := _ * eval_pol _ _.
set t3 := (eval_pol _ _ - _).
set t2 := t3 * _.
rewrite (_ : k' = k1 + k2); last by rewrite /k1 /k2 addrA addNr add0r.
rewrite mulr_addl.
apply: lerT; last first.
  have maj' : t3 * b^-1 ^+ (size l - 1) <<= t3 * z^+ (size l - 1).
    have maj : leb (b^-1 ^+(size l - 1)) (z ^+ (size l - 1)).
      by admit.
    by admit.
  apply: ler_trans maj'; rewrite /t3.
  rewrite k2p mulrAC.
  have cmpyb: k * y ^+ 2 * (z - x) * y^-1 ^+ (size l - 1) <<=
              k * b ^+ 2 * (z - x) * b^-1 ^+ (size l - 1).
    (* Not convinced here.  We need the assumption that size l > 2,
       but this is not granted.  So for polynomials of degree 1 (size l = 2)
       we may have to perform a different proof. *)
    by admit.
  apply: ler_trans cmpyb _.
  apply: ler_rcompat; first by admit.
  apply: ler_trans (_ : k * (x^-1 - z^-1) <<= _).
  rewrite ![k * _]mulrC mulrAC.
    apply: ler_rcompat; first by rewrite ltrW.
  by admit.
  apply: sl.
    by admit.
  by admit.
rewrite /t1 /k1 /k' {t2 t3}.
case: (lerP 0 (eval_pol (reciprocate_pol l) x^-1)) => sign; last by admit.
rewrite mulNr -ler_oppger opprK -mulNr oppr_sub.
(* because the polynomial is increasing in that part of its domain. *)
have rpxe : eval_pol (reciprocate_pol l) x^-1 <<= e by admit.
apply: ler_trans (_ : (z^+ (size l - 1) - x ^+ (size l - 1)) * e <<= _).
  apply: ler_2compat0l; last by [].
      by admit.
    by apply: ler_refl.
  by apply: ltrW.
rewrite [_ * e]mulrC.
apply: ler_trans (_ : e * (u' * (z - x)) <<= _).
  apply: ler_lcompat; first by apply: ltrW.
  apply: ler_trans (_ : u * (z - x) <<= _).
    apply: up => //.
    apply: ltr_trans za1 _; rewrite -invr1_ltr0_1ltr; last by [].
    by apply: ltr_ler_trans x1a.
  apply: ler_rcompat; first by [].
  exact u'u.
rewrite mulrA; apply: ler_rcompat; first by [].
(* divrK should be renamed mulVrK *)
by rewrite pe divrK // ler_refl.
Qed.

Lemma Bernstein_isolate : forall a b l, a <<! b ->
   alternate (Bernstein_coeffs l a b) -> one_root1 l a b.
Proof.
rewrite /Bernstein_coeffs => a b l altb alt.
rewrite (_ : a = a + (a - a)); last by rewrite addrN addr0.
rewrite (_ : b = a + (b - a)); last by rewrite (addrC b) addrA addrN add0r.
apply: one_root1_translate.
rewrite addrN (_ : (b-a) = (b-a) * 1); last by rewrite mulr1.
rewrite (_ : 0 =  (b-a) * 0); last by rewrite mulr0.
apply: one_root1_expand; first by rewrite -(addrN a) ltrTlb.
apply: one_root_reciprocate.
rewrite -[1]addr0; apply: one_root2_translate.
by apply: alt_one_root2.
Qed.
