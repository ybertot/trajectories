Require Import QArith ZArith Zwf Omega.
Require Import ssreflect eqtype ssrbool ssrnat div fintype seq ssrfun.
Require Import bigops groups choice binomial.
Require Export ssralg xssralg infra pol cmvt desc.

Import GroupScope .
Import GRing.Theory .
Import GOrdered.
Open Local Scope ring_scope .

Set Printing Width 50.

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

Lemma alt_one_root2 :
  forall l, alternate l = true -> one_root2 l 0.
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

Lemma one_root_reciprocate :
  forall l, one_root2 (reciprocate_pol l) 1 -> one_root1 l 0 1.
Proof.
move=> l [x1 [k [x1gt1 [kp [neg sl]]]]].
have x11 : x1 <<! x1 + 1 by rewrite -{1}[x1]addr0 ltrTrb.
have uk : GRing.unit k by apply/negP;move/eqP=>q; rewrite q ltr_irrefl in kp.
set y' := x1 - eval_pol (reciprocate_pol l) x1 / k.
have y'1 : y' <<! y' + 1 by rewrite -{1}[y']addr0 ltrTrb.
(* Cette partie doit être simplifiée car on a pas besoin que
   eval_pol (reciprocate_pol l) y soit strictement positif, non neg suffit. *)
have iy: exists y, x1 <<! y /\ y' <<! y.
  case h: (x1 <<! y'); last (move/negbT: h; rewrite -lerNgtr => h).
    by exists (y' + 1); split; first apply: ltr_trans y'1.
  by exists (x1 + 1); split; last apply: ler_ltr_trans x11.
move: iy => [y [y1 y'y]].
have ypos : 0 <<! eval_pol (reciprocate_pol l) y.
  rewrite -[_ _ y]addr0 -(addrN (eval_pol (reciprocate_pol l) x1))
    addrA [_ _ y + _]addrC -addrA ltrTrb.
  apply: ltr_ler_trans (_ : k * (y - x1) <<= _).
    apply: ler_ltr_trans (_ : k * (y' - x1) <<! _).
      rewrite /y' [k * _]mulrC !mulr_addl mulNr mulrVK //.
      by rewrite [x1 * k + _]addrC mulNr addrK ler_refl.
    by apply: ltr_lcompat => //; apply ltrTl.
  by apply: sl; first apply ler_refl.
have x1neg := neg _ x1gt1 (ler_refl _).
have ie : exists e, 0 <<! e /\ e <<! k/ y^+(size l).
  by admit.
move: ie => [e [ep pe]].
move: (cut_epsilon _ ep) => [e1 [e2 [e1p [e2p [e1e2 [e1e e2e]]]]]].
move: (constructive_mvt (reciprocate_pol l) _ _ y1 x1neg (ltrW ypos) _ e1p) =>
  [a [b' [cla [nega [posb' [clb' [x1a [ab b'y]]]]]]]].
move: (cm2 (reciprocate_pol l) y) => [c pc].
have ib : exists b, b' <<! b /\ c * (b - b') <<! e2.
  by admit.
move: ib => [b [b'b clb]].
(* The choice of k is not sure yet. *)
exists (b^-1); exists (a^-1); exists (k^-1).
have a0 : 0 <<! a by apply:ltr_ler_trans x1a; first apply: ltr_trans x1gt1. 
have b'0 : 0 <<! b' by apply: ltr_trans ab.
have b0 : 0 <<! b by apply:ltr_trans b'b.
have ua: GRing.unit a by apply/negP; move/eqP=> q; rewrite q ltr_irrefl in a0.
have ub' : GRing.unit b'
  by apply/negP; move/eqP=>q; rewrite q ltr_irrefl in b'0.
have ub: GRing.unit b by apply/negP; move/eqP=> q; rewrite q ltr_irrefl in b0.
split; first by rewrite invr_ltr.
split.
  apply (ltr_Ilcompat_r a0); apply (ltr_Ilcompat_l b0); rewrite mulrVK //.
  by rewrite mulrV // mul1r; apply: ltr_trans b'b.
split; first by rewrite -invr1_ltr0_1ltr; first apply: ltr_ler_trans x1a.
split; first by rewrite invr_ltr.
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
  apply (ltr_Ilcompat_r xexp0); rewrite mulr0.
  rewrite -{2}[x]invrK -reciprocateq; last by rewrite unitr_inv.
  apply: ler_ltr_trans posb' _.
  rewrite -(ltrTlb (-(eval_pol (reciprocate_pol l) b'))) addrN.
  apply: ltr_ler_trans (_ : k*(x^-1 - b') <<= _).
    by apply: ltr_0_lcompat; first done; rewrite -(ltrTlb b') add0r addrNK.
  by apply sl; first apply: ltrW(ler_ltr_trans x1a _).
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




