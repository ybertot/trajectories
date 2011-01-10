Require Import ssreflect eqtype ssrbool ssrnat div fintype seq ssrfun.
Require Import bigop fingroup choice binomial.
Require Export ssralg  ssralg zint orderedalg pol cmvt desc.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


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

Section BernOnAbstractRationals.

Variable Q : oFieldType.

Hypothesis Q_arch : forall x:Q, 0 <= x -> {n : nat | x <= n%:R}.

Definition one_root1 (l : seq Q) (a b : Q) :=
  exists c, exists d, exists k, 
     a < c /\ c < d /\ d < b /\ 0 < k /\
     (forall x, a < x -> x <= c -> 0 < l.[x]) /\
     (forall x, d < x -> x < b ->  l.[x] < 0) /\
     (forall x y, c < x -> x <= y -> y < d ->
        k * (y - x) <=  l.[x] -  l.[y] ).

Definition one_root2 (l : seq Q) (a : Q) :=
   exists c, exists k,
     a < c /\ 0 < k /\
     (forall x, a < x -> x <= c ->  l.[x] < 0) /\
     (forall x y, c <= x -> x < y -> 
         k * (y - x) <=  l.[y] -  l.[x]).

Lemma alt_one_root2 : forall l : {poly Q},   alternate l -> one_root2 l 0.
move => l a.
move: (desc Q_arch a) => [x1 [k [x1p [kp [neg sl]]]]].
move: (above_slope 0 kp sl) => [x2 [pos x1x2]].
by exists x1; exists k; split; first done; split; first done; split; done.
Qed.

Lemma one_root2_translate :
  forall (l : {poly Q}) a b, 
    one_root2 (translate_pol l a) b -> one_root2 l (a + b).
Proof.
move=> l a b [x1 [k [x1a [kp [neg sl]]]]].
exists (a + x1); exists k.
split; first by rewrite  lter_add2r.
split; first by [].
split.
  move=> x abx xax1; rewrite (_ : x = x - a + a); last first.
    by rewrite addrNK.
  rewrite  -eval_translate_pol; apply: neg.
    by rewrite ltr_subr_addl addrC.
  by rewrite ler_subl_addl addrC.
move=> x y ax1x xy.
have t: forall z, z = (z - a) + a by move=> z; rewrite addrNK.
rewrite {2}(t y) {2}(t x) -!(eval_translate_pol _ a) (_ : y - x = y - a - (x - a)).
  by apply: sl; rewrite ?ltr_add2l // ler_subr_addl addrC.
by rewrite oppr_add addrAC -!addrA opprK addrN addr0.
Qed.

Lemma one_root1_translate :
  forall l a b c, one_root1 (translate_pol l c) a b ->
    one_root1 l (c + a) (c + b).
Proof.
move=> l a b c [x1 [x2 [k [ax1 [x1x2 [x2b [kp [pos [neg sl]]]]]]]]].
exists (c + x1); exists (c + x2); exists k.
split; first by rewrite lter_add2r.
split; first by rewrite lter_add2r.
split; first by rewrite lter_add2r.
split; first by [].
split.
  move=> x cax xcx1; rewrite (_ : x = x - c + c); last by rewrite addrNK.
   rewrite -eval_translate_pol; apply pos; first by rewrite ltr_subr_addr.
   by rewrite ler_subl_addr.
split.
  move=> x cx2x xcb; rewrite (_ : x = x - c + c); last by rewrite addrNK.
  rewrite -eval_translate_pol; apply: neg; first by rewrite ltr_subr_addr.
  by rewrite ltr_subl_addr.
move=> x y cx1x xy ycx2.
have t: forall z, z = (z - c) + c by move=> z; rewrite addrNK.
rewrite {2}(t x) {2}(t y) (_ : y - x = y - c - (x - c)); last first.
  by rewrite [x + _]addrC oppr_add opprK addrA addrNK.
rewrite -!(eval_translate_pol _ c); apply: sl; rewrite ?ler_add2l //.
  by rewrite ltr_subr_addr.
by rewrite ltr_subl_addr.
Qed.


Lemma one_root1_expand :
  forall l a b c, 0 < c -> one_root1 (expand l c) a b ->
    one_root1 l (c * a) (c * b).
Proof.
move=> l a b c cp [x1 [x2 [k [ax1 [x1x2 [x2b [kp [pos [neg sl]]]]]]]]].
exists (c * x1); exists (c * x2); exists (k / c).
have tc : 0 < c^-1 by rewrite invr_gt0.
(*have uc: GRing.unit c by apply/negP; move/eqP => q; rewrite q lterr in cp.*)
do 3 (split; first by rewrite ltr_pmul2rW).
split; first by rewrite mulr_gt0.
split.
  move=> x acx xx1c.
  rewrite (_ : x = c * (x/c)); last by rewrite mulrC mulfVK // eq_sym ltrWN.
  rewrite -eval_expand; apply: pos.
    by rewrite ltr_pdivl_mulr // mulrC.
  by rewrite ler_pdivr_mulr // mulrC.
split.
  move=> x cx2x xcb; rewrite (_ : x = c * (x/c)); last by rewrite mulrC mulfVK // eq_sym ltrWN.
  rewrite -eval_expand; apply: neg; first by rewrite ltr_pdivl_mulr // mulrC.
  by rewrite ltr_pdivr_mulr // mulrC.
have t: forall z, z = c * (z / c).
   by move=> z; rewrite [c * _]mulrC mulfVK // eq_sym ltrWN.
move=> x y cx1x xy ycx2; rewrite -mulrA mulr_addr mulrN ![c^-1 * _]mulrC
  {2}(t x) {2}(t y) -!(eval_expand l); apply: sl.
- by rewrite ltr_pdivl_mulr // mulrC.
- by rewrite ler_pmul2lW // ltrW.
- by rewrite ltr_pdivr_mulr // mulrC.
Qed.

Lemma diff_xn_ub :
  forall n z, 0 < z -> exists k, 0 <= k /\
   forall x y:Q, 0 < x -> x <= y -> y <= z ->
      y ^+ n - x ^+ n <= k * (y - x).
Proof.
move => n; elim: n => {n} [z z0| n IHn z z0].
  by exists 0; rewrite lerr; split=> // *; rewrite !expr0 mul0r subrr lerr.
case: (IHn z z0) => k [k0 kp].
exists (z * k + z ^+ n); split => [ | x y x0 xy yz].
  apply: addr_ge0; first by rewrite mulr_ge0 // ltrW.
  by rewrite exprn_ge0 // ltrW.
rewrite !exprS (_: _ * _ - _ =  y * (y ^+ n - x ^+ n) + (y - x) * x ^+ n); last first.
  by rewrite mulr_addl mulr_addr addrA mulrN mulNr addrNK.
rewrite [_ * (y-x)]mulr_addl ler_add //=.
  rewrite -mulrA; apply: ler_trans (_ : y * (k * (y - x)) <= _).
    rewrite ler_pmul2r; last by exact: ltr_le_trans xy.
    exact: kp.
  by apply: ler_pmul2lW => //; apply: mulr_ge0 => //; rewrite subr_ge0.
rewrite (mulrC (_ - _)) ler_pmul2lW //; first by rewrite subr_ge0.
rewrite ler_le_pexp2 //; first by exact: ltrW.
exact: ler_trans yz.
Qed.

(* This is false *)
(*
Lemma reciprocate_size :  forall l : {poly Q}, size (reciprocate_pol l) = size l.
*)

Lemma one_root_reciprocate :
  forall l, one_root2 (reciprocate_pol l) 1 -> one_root1 l 0 1.
Proof.
move=> l [x1 [k [x1gt1 [kp [neg sl]]]]].
have x10 : 0 < x1 by apply: ltr_trans x1gt1 => //; exact: ltr01.
(*
have ux1 : GRing.unit x1 by apply/negP; move/eqP => q; rewrite q lterr in x10.
have uk: GRing.unit k by apply/negP; move/eqP => q; rewrite q lterr in kp.
*)
set y' := x1 -  (reciprocate_pol l).[x1] / k.
have y'1: x1 < y'.
  rewrite /y' ltr_addr oppr_gt0 mulr_lt0_gt0 // ?invr_gt0 //.
  apply: neg => //; exact: lerr.
have nx1 :  (reciprocate_pol l).[x1] < 0 by apply: neg; rewrite // lterr.
have y'pos : 0 <=  (reciprocate_pol l).[y'].
  rewrite -[_ _ y']addr0 -{2}(addNr ( (reciprocate_pol l).[x1])) addrA
   -{2}(opprK (_ _ x1)) subr_gte0 /=.
  apply: ler_trans (_ : k * (y' - x1) <= _)=> /=.
    by rewrite /y' (addrC x1) addrK mulrN mulrC mulfVK ?lerr // ltrNW.
  by apply sl => //; rewrite lerr.
move: (diff_xn_ub (size l - 1) (ltr01 Q)) => [u [u0 up]].
have [u' [u1 u'u]] : exists u', 1 <= u' /\ u <= u'.
  case cmp: (1 <= u); first by exists u; rewrite lerr cmp.
  by exists 1; rewrite lerr; split=> //; rewrite ltrW // ltrNge cmp.
have u'0 : 0 < u' by apply: ltr_le_trans u1=> //; exact: ltr01.
(* have u'unit : GRing.unit u' by apply/negP; move/eqP=> q; rewrite q lterr in u'0. *)
have divu_ltr : forall x, 0 <= x -> x / u' <= x.
  by move => x x0; rewrite ler_pdivr_mulr //; apply: ler_epmulr.
have y'0: 0 < y' by apply: ltr_trans y'1.
pose y := y' + 1.
have y'y : y' < y by rewrite /y ltr_addr ltr01.
have y1 : x1 < y by apply: ltr_trans y'1 _.
have ypos : 0 <  (reciprocate_pol l).[y].
  apply: ler_lt_trans y'pos _=> /=.
  rewrite -subr_gte0 /=; apply: ltr_le_trans (_ : k * (y - y') <= _)=> /=.
    by rewrite mulr_gt0 // subr_gt0.
  by apply: sl=> //; apply: ltrW.
have y0: 0 < y by apply: ltr_trans y'y.
pose k' :=  ((k * x1 ^+ 2 * y ^- 1 ^+ (size l - 1))/(1+1)).
have k'p : 0 < k'.
  rewrite /k' mulr_gt0 //; last first.
    by rewrite invr_gt0 -[1]/(1%:R) -natr_add; have:= (ltr0Sn Q 1%N).
  by rewrite ?mulr_gt0 // exprn_gt0 // invr_gt0.
pose e := k' / u'.
have ep: 0 < e by rewrite /e; apply: mulr_gt0 => //; rewrite invr_gt0.
pose e1 := e / 2%:R.
pose e2 := e / 2%:R.
have e1p : e1 > 0.
  by rewrite /e1 ltr_pdivl_mulr ?mul0r //; have := (ltr0Sn Q 1%N).
have e2p : e2 > 0.
  by rewrite /e1 ltr_pdivl_mulr ?mul0r //; have := (ltr0Sn Q 1%N).
have e1e : e1 < e. admit (* 1 < 2 *).
have e2e : e2 < e. admit (* 1 < 2 *).
(*have e1e2 : e1 + e2 <= e.
  rewrite /e1 /e2 -mulr_addl.*)
move: (constructive_ivt Q_arch  y'1 nx1 y'pos e1p) =>
  [a [b' [cla [nega [posb' [clb' [x1a [ab b'y']]]]]]]].
move: (cm3 (reciprocate_pol l) y0) => [c cp].
have a0 : 0 < a by apply: ltr_le_trans x1a.
have c0 : 0 < c.
  move: (ab); rewrite -subr_gt0; move/ltr_pmul2l<-; rewrite mul0r.
  apply: ltr_le_trans
    (_ : `| (reciprocate_pol l).[b'] -  (reciprocate_pol l).[a] | 
          <= _)=> /=; last first.
  by apply: cp; last apply: ltrW (ler_lt_trans b'y' y'y); apply: ltrW.
  have d: 0 <  (reciprocate_pol l).[b'] -  (reciprocate_pol l).[a].
    by rewrite subr_gte0 /=; apply: ltr_le_trans posb'.
  by rewrite  absr_gt0 eq_sym ltrWN.
(*have uc: GRing.unit c by apply/negP; move/eqP => q; rewrite q lterr in c0.*)
have [b [b'b [clb blty]]] : exists b, b' < b /\ c * (b - b') < e2 /\ b <= y.
  pose e3 := e2 / 2%:R.
  pose e4 := e2 / 2%:R.
  have e3p : e3 > 0.
  by rewrite /e3 ltr_pdivl_mulr ?mul0r //; have := (ltr0Sn Q 1%N).
  have e4p : e4 > 0.
  by rewrite /e4 ltr_pdivl_mulr ?mul0r //; have := (ltr0Sn Q 1%N).
  have e3e2: e3 < e2. admit (* 1 < 2 *).
  case cmp: (b' + e2/c <= y).
    exists (b' + e3/c).
    split.
      by rewrite ltr_addr mulr_gt0 // invr_gt0.
    split.
       by rewrite (addrC b') addrK mulrA (mulrC c) mulfK // eq_sym ltrWN.
    apply: ltrW (ltr_le_trans _ cmp); rewrite lter_add2r /=. 
    by rewrite ltr_pmul2l // invr_gt0.
  exists y.
  split; first by apply: ler_lt_trans b'y' y'y.
  split; last by rewrite lerr.
  by rewrite mulrC -ltr_pdivl_mulr // ltr_subl_addr ltrNge cmp.
pose n := (size l).-1.
have b'0 : 0 < b' by apply: ltr_trans ab.
have b0 : 0 < b by apply: ltr_trans b'b.
(* have ua: GRing.unit a by apply/negP; move/eqP=> q; rewrite q lterr in a0. *)
(* have ub': GRing.unit b' by apply/negP; move/eqP=> q; rewrite q lterr in b'0. *)
(* have b'v0: 0 < b'^-1 by rewrite invf_gte0. *)
(* have bv0 : 0 < b^-1 by rewrite invf_gte0. *)
(* have bb'v: b^-1 < b'^-1. *)
(*  by apply: ltef_invpp => //. *)
(* have ub: GRing.unit b by apply/negP; move/eqP=> q; rewrite q lterr in b0. *)
exists b^-1; exists a^-1; exists k'.
split; first by rewrite invr_gt0.
split.
  (* inutilement complique de prouver la montonie de l'inverse *)
  admit.
split; first by rewrite invr_lt1; apply: ltr_le_trans x1a.
split=> //.
split.
  move => x x0 xb.
  (* have ux: GRing.unit x by apply/negP; move/eqP=>q; rewrite q lterr in x0. *)
  (* have xv0: 0 < x^-1 by rewrite invf_gte0. *)
  have xexp0 : 0 < x^-1 ^+ (size l -1).
    by apply: exprn_gt0 => //; rewrite invr_gt0.
  have b'x : b' < x^-1.
  (* inutilement complique de prouver la montonie de l'inverse *)
  admit.
  rewrite -(ltr_pmul2l _ _ xexp0) mul0r -{1}[x]invrK mulrC -reciprocateq; last first.
    by rewrite invr_eq0 ltrNW.
  apply: (ler_lt_trans posb'); rewrite -subr_gte0 /=.
  apply: ltr_le_trans (_ : k * (x^-1 - b') <= _)=> /=.
    by rewrite mulr_gt0 // subr_gt0.
  by apply: sl; first apply:ltrW (ler_lt_trans x1a _).
split.
  move => x a1x xlt1.
  have x0 : 0 < x by apply: ltr_trans a1x; rewrite invr_gt0.
  have xexp0 : 0 < x^-1 ^+ (size l -1).
     by apply: exprn_gt0 => //; rewrite invr_gt0.
(*  have ux: GRing.unit x by apply/negP;move/eqP=>q; rewrite q lterr in x0.
  have uxv : GRing.unit x^-1 by rewrite unitr_inv. *)
  have xv0 : 0 < x^-1 by rewrite invr_gt0.
  have x1a0 : x^-1 < a.
    rewrite -[a]invrK.
  (* inutilement complique de prouver la montonie de l'inverse *)
  admit.
  rewrite -(ltr_pmul2l _ _ xexp0) mul0r -{1}[x]invrK mulrC -reciprocateq; last first.
    by rewrite invr_eq0 ltrNW.
  case cmp: (x^-1 <= x1); last (move/negbT:cmp => cmp).
     apply: neg => //; rewrite -invr1.
     (* inutilement complique de prouver la montonie de l'inverse *)
     admit.
  apply: ltr_trans nega; rewrite -subr_gte0.
  apply: ltr_le_trans (_ : k * (a - x^-1) <= _).
    by rewrite mulr_gt0 // subr_gt0.
  apply: sl => //. 
  (* inutilement complique de prouver la montonie de l'inverse *)
  admit.
move => x z bvx xz zav; rewrite ler_eqVlt in xz; move/orP: xz => [xz | xz].
  by rewrite (eqP xz) !addrN mulr0 lterr.
have x0: 0 < x by apply: ltr_trans bvx; rewrite invr_gt0.
have z0 : 0 < z by apply: (ltr_trans x0).
have -> : l.[x] = x ^+ (size l - 1) * (reciprocate_pol l).[x^-1].
  rewrite reciprocateq ?invr_eq0 ?ltrNW // mulrA invrK -exprn_mull mulfV; last first.
    by rewrite eq_sym ltrWN.
  by rewrite exp1rn mul1r.
(* to be abstracted *)
have -> : l.[z] = z ^+ (size l - 1) * (reciprocate_pol l).[z^-1].
  rewrite reciprocateq ?invr_eq0 ?ltrNW // mulrA invrK -exprn_mull mulfV; last first.
    by rewrite eq_sym ltrWN.
  by rewrite exp1rn mul1r.
rewrite (_ : _ * _ - _ = (x ^+ (size l - 1) - z ^+ (size l - 1)) *
                      (reciprocate_pol l).[x ^-1] +
                     ( (reciprocate_pol l).[x ^-1] -
                       (reciprocate_pol l).[z ^-1]) *
                      z ^+ (size l - 1)); last first.
  by rewrite !mulr_addl !mulNr ![ _.[_] * _]mulrC !addrA addrNK.


(* (* *)
(* have ux: GRing.unit x by apply/negP;move/eqP=>q; rewrite q lterr in x0. *)
(* have uz: GRing.unit z by apply/negP;move/eqP=>q; rewrite q lterr in z0.*) *)


(* have invo_rec : forall l, reciprocate_pol (reciprocate_pol l) = l. *)
(*   by move => l'; rewrite /reciprocate_pol revK. *)
(* rewrite -(invo_rec l) (reciprocateq _ x) // (reciprocateq _ z) //. *)
(* rewrite reciprocate_size. *)
(* rewrite (_ : _ * _ - _ = (x ^+ (size l - 1) - z ^+ (size l - 1)) * *)
(*                       (reciprocate_pol l) x ^-1 + *)
(*                      ( (reciprocate_pol l) x ^-1 - *)
(*                        (reciprocate_pol l) z ^-1) * *)
(*                       z ^+ (size l - 1)); last first. *)
(*   by rewrite !mulr_addl !mulNr ![ _ _ * _]mulrC !addrA addrNK. *)
set t1 := _ *  _.[_].
set t3 := ( _.[_] - _).
set t2 := t3 * _.
pose k1 := -k'; pose k2 := k' + k'.
have times2 : forall a:Q, a + a = (1 + 1) * a.
  by move => a'; rewrite mulr_addl !mul1r.
have k2p : k2 = (k * x1 ^+ 2 * y ^-1 ^+ (size l - 1)).
  rewrite /k2 /k' times2 -(mulrC (1 + 1)^-1) mulrA mulfV; first  by rewrite mul1r.
    have twop : 0 < ((1 + 1):Q) by rewrite gtr0_ltr_add // ltr01.
    by rewrite eq_sym (ltrWN twop).
rewrite (_ : k' = k1 + k2); last by rewrite /k1 /k2 addrA addNr add0r.
rewrite mulr_addl; apply: ler_add; last first.
  have maj' : t3 * y^-1 ^+ (size l - 1) <= t3 * z^+ (size l - 1).
    have maj : y^-1 ^+(size l - 1) <= z ^+ (size l - 1).
      apply: ler_le_pexp2; first by apply: ltrW; rewrite invr_gt0.
      apply: ltrW; apply: ltr_trans xz; apply: ler_lt_trans bvx.
      (* compliqué monotonie inverse *)
      admit.
    rewrite  ler_pmul2r // /t3.
    apply: ltr_le_trans (_ : k * (x^-1 - z^-1) <= _); last first.
      apply: sl.
        rewrite -[x1]invrK //.
      (* compliqué monotonie inverse *)
       admit.
    (* compliqué monotonie inverse *)
     admit.
    apply: mulr_gt0 => //.
    rewrite subr_gt0.
    (* compliqué monotonie inverse *)
     admit.
  apply: ler_trans maj'; rewrite /t3 k2p mulrAC.
  rewrite ler_pmul2l; last by apply exprn_gt0; rewrite invr_gt0.
  apply: ler_trans (_ : k * (x^-1 - z^-1) <= _).
    rewrite ![k * _]mulrC mulrAC ler_pmul2l; last by [].
    have xVn0 : ~~ (x^-1 == 0) by rewrite invr_eq0 ltrNW.
    have xn0 : ~~ (x == 0) by rewrite ltrNW.
    have zn0 : ~~ (z == 0) by rewrite ltrNW.
    rewrite -[x^-1](mulfK zn0) -{2}[z^-1](mulfK xn0) -(mulrC x) -(mulrC z).
    rewrite (mulrAC x) -!(mulrA _ (x^-1)) -mulr_subl (mulrC (z - x)).
    rewrite ler_pmul2l /=; last by rewrite subr_gte0.
    apply: ler_trans (_ : x1 / z <= _).
      rewrite ler_pmul2r //=.
      apply: ler_trans x1a _; rewrite -(invrK a).
    (* compliqué monotonie inverse *)
     admit.
    rewrite ler_pmul2l ?invr_gt0 //. 
    (* compliqué monotonie inverse *)
    admit.
  apply: sl.
    apply: ltrW; apply: (ler_lt_trans x1a _).
    (* compliqué monotonie inverse *)
    admit.
  (* compliqué monotonie inverse *)
  admit.
rewrite /t1 /k1 /k' {t2 t3}.
have xzexp : (x ^+ (size l - 1) <= z ^+ (size l - 1)).
  apply: ler_le_pexp2 => //; exact: ltrW.
case: (lerP 0 ( (reciprocate_pol l).[x^-1])) => sign; last first.
  apply: ler_trans (_ : 0 <= _).
    rewrite mulNr lter_oppl oppr0; apply: mulr_ge0; last first.
      by rewrite subr_gte0 /= ltrW.
    apply: ltrW; exact: k'p.
  apply: mulr_le0.
    by rewrite subr_lte0.
  by apply: ltrW.
rewrite mulNr lter_oppl -mulNr oppr_sub.
have rpxe :  (reciprocate_pol l).[x^-1] <= e.
  apply:ler_trans (_ :  (reciprocate_pol l).[b] <= _) => /=.
    rewrite -subr_ge0 /= ; apply: ler_trans (_ : k * (b - x^-1) <= _).
      apply: mulr_ge0; first by apply: ltrW.
      rewrite subr_gte0 -[b]invrK //.
  (* compliqué monotonie inverse *)
      admit.
    apply: sl. 
      rewrite -[x1]invrK //.
    (*     by rewrite invr_gte0. *)
    (*   by apply: ltrW(ltr_le_trans (lter_trans xz zav) _); apply: ltef_invpp. *)
    (* by rewrite -[b]invrK //; apply: ltef_invpp. *)
  (* compliqué monotonie inverse *)
      admit.
  (* compliqué monotonie inverse *)
    admit.
  rewrite -[_ _ b]addr0 -(addrN ( (reciprocate_pol l).[b'])) addrA.
  rewrite (addrC ( _ b)) -addrA (_ : e = e1 + e2); last first.
    rewrite /e1 /e2 -mulr_addl -{2 3}[e] mul1r -mulr_addl mulrAC mulfV ?mul1r //.
    by rewrite ltrNW //; have:= (ltr0Sn Q 1).
  apply: ler_add; first by [].
  suff: `|(reciprocate_pol l).[b] - (reciprocate_pol l).[b']| <= e2 by case/absr_le.
  apply: ler_trans (ltrW clb).
  by apply: cp; last done; apply: ltrW.
apply: ler_trans (_ : (z^+ (size l - 1) - x ^+ (size l - 1)) * e <= _).
(* lter_trans does not work *)
  move: xzexp; rewrite -subr_gte0 ler_eqVlt; case/orP=> [xzexp | xzexp] /=.
     by rewrite /= -(eqP xzexp) !mul0r lterr.
  apply: ler_pmul2rW => //; exact: ltrW.
rewrite [_ * e]mulrC; apply: ler_trans (_ : e * (u' * (z - x)) <= _)=> /=.
  apply: ler_pmul2rW; first exact: ltrW.
  apply: ler_trans  (_ : u * (z - x) <= _).
    apply: up => //; first by apply: ltrW.
    apply: ltrW; apply: ltr_le_trans zav _; rewrite -invr1. 
  (* compliqué monotonie inverse *)
    admit.
    (* by apply: ltr_le_trans x1gt1 _. *)
  by rewrite ler_pmul2l // subr_gte0.
rewrite mulrA ler_pmul2l; last by rewrite subr_gte0.
by rewrite /= /e divfK  ?lterr // ltrNW.
Qed.


Lemma Bernstein_isolate : forall a b l, a < b ->
   alternate (Bernstein_coeffs l a b) -> one_root1 l a b.
Proof.
rewrite /Bernstein_coeffs => a b l altb alt.
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

End BernOnAbstractRationals.