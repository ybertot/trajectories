Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype prime div.
Require Import ssralg poly polydiv polyorder ssrnum zmodp polyrcf.

Set Implicit Arguments.
Unset Strict Implicit.

Import GRing.Theory. (*Num.Theory Num.Def.*)
Import Pdiv.Idomain.

Section more_deriv.

Lemma derivXsubCexpSn : forall (R : idomainType) (c : R) (n : nat),
   (('X-c%:P) ^+(n.+1))^`() = (n.+1)%:R *: ('X-c%:P) ^+ n.
Proof.
move=> R c; elim=> [ | m Hm].
  by rewrite scaler_nat expr0 expr1 derivXsubC.
rewrite exprSr derivM derivXsubC Hm -scalerAl -exprSr mulr1 scaler_nat -mulrSr.
by rewrite -scaler_nat.
Qed.

Lemma derivXsubCexpn : forall (R : idomainType) (c : R) (n : nat),
   (0 < n)%N -> (('X-c%:P) ^+n)^`() = n%:R *: ('X-c%:P) ^+ (n.-1).
Proof.
move=> R c; elim=> [ | m Hm H] //=.
by rewrite derivXsubCexpSn.
Qed.

End more_deriv.


Section poly_simple_roots.

Variable (R : idomainType).
Hypothesis (HR : [char R] =i pred0).

Lemma mu_x_gcdp : forall (p : {poly R}) (x : R), (p != 0) -> 
   (root p x) ->
   \mu_x (gcdp p p^`()) == (\mu_x p) .-1.
Proof.
move=> p x Hp zero_x.
(*about p*)
have H_mult_p := (@mu_spec R p x Hp).
case: H_mult_p => q Hq Hpp.
(*mu x > 0*)
have Hmu : ((\mu_x p)%R > 0)%N.
  by rewrite mu_gt0.
(*about p'*)
have : (deriv p) =
   ('X - x%:P) ^+ ((\mu_x p).-1) *
   ((\mu_x p)%:R *: q + ('X-x%:P) * (deriv q)).
  by rewrite mulrDr mulrA -exprSr prednK // -scalerCA -derivXsubCexpn //
     -derivM mulrC {1}Hpp.
move=> Hpderiv.
(**********)
rewrite eq_sym -muP.
  apply/andP; split.
(*(X-x)^m-1 divides pgcd*)
    rewrite dvdp_gcd.
    apply/andP; split.
(*(X-x)^m-1 divides p*)
      rewrite {2}Hpp -(@prednK (\mu_x p)) // exprS mulrA.
      by apply dvdp_mulIr.
(*(X-x)^m-1 divides p'*)
    rewrite Hpderiv.
    by apply dvdp_mulIl.
(*(X-x)^m doesn't divide pgcd*)
  rewrite prednK // dvdp_gcd negb_and.
  apply/orP; right.
(*(X-x)^m doesn't divide p'*)
  rewrite Hpderiv -{1}(@prednK (\mu_x p)) // exprSr dvdp_mul2l.
(*(X-x) doesn't divide the remaining factor of p'*)
    rewrite dvdp_addl.
      rewrite (@eqp_dvdr _  q ((\mu_x p)%:R *: q) ('X -x%:P)).
        by rewrite dvdp_XsubCl.
      apply eqp_scale.
      have/charf0P ->:= HR.
      by rewrite -lt0n //.
    by apply dvdp_mulr.
  by rewrite -size_poly_gt0 size_exp_XsubC prednK //.
rewrite gcdp_eq0 negb_and.
by rewrite Hp.
Qed.

Lemma mu_gcdp_eq1 : forall (p : {poly R}) (x : R), (p != 0) ->
   root p x ->
   (\mu_x (divp p (gcdp p p^`())) == 1)%N.
Proof.
move=> p x Hp zero_x.
rewrite -(@eqn_add2r ((\mu_x)%R p)) (@addnC 1%N _) addn1 
  -{1}(@prednK ((\mu_x)%R p)).
  rewrite addnS -(eqP (mu_x_gcdp Hp zero_x)) -mu_mul.
    rewrite divpK.
      rewrite mu_mulC.
        by [].
      by apply lc_expn_scalp_neq0.
    by apply dvdp_gcdl.
  rewrite divpK.
    rewrite -size_poly_gt0 -mul_polyC size_Cmul.
      by rewrite size_poly_gt0.
    by apply lc_expn_scalp_neq0.
  by apply dvdp_gcdl.
by rewrite mu_gt0.
Qed.

Lemma same_roots_1 : forall (p : {poly R}) (x : R), root p x ->
   root (divp p (gcdp p p^`())) x.
Proof.
move=> p x zero_x.
case: (p==0)/eqP.
move => H; move : zero_x.
   by rewrite H deriv0 gcd0p div0p.
move/eqP => H.
rewrite -mu_gt0.
  move/eqP : (mu_gcdp_eq1 H zero_x) => H2.
  by rewrite H2.
rewrite divpN0.
  by apply leq_gcdpl.
move/negPf : H => H.
by rewrite gcdp_eq0 H.
Qed.

Lemma same_roots_2 : forall (p : {poly R}) (x : R),
   root (divp p (gcdp p p^`())) x -> root p x.
Proof.
move=> p x zero_x.
rewrite -(@rootZ R x (lead_coef (gcdp p p^`()) ^+ scalp (R:=R) p
   (gcdp p p^`())) p).
  rewrite -divpK.
    by rewrite rootM zero_x.
  by apply dvdp_gcdl.
by apply lc_expn_scalp_neq0.
Qed.

Lemma gcdp_simple_roots : forall (p : {poly R}) (x : R), (p != 0) ->
   root (divp p (gcdp p p^`())) x ->
   (\mu_x (divp p (gcdp p p^`())) == 1)%N.
Proof.
move=> p x Hp zero_x.
apply (mu_gcdp_eq1 Hp).
by apply same_roots_2.
Qed.
(*p!=0 beause of mu_polyC.*)

End poly_simple_roots.
