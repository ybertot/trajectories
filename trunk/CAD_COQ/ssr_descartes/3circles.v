Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype prime div.
Require Import ssralg poly polydiv polyorder ssrnum zmodp polyrcf qe_rcf_th complex poly_normal.

Set Implicit Arguments.
Unset Strict Implicit.

Import GRing.Theory Num.Theory Num.Def.
Import Pdiv.Idomain.

Section about_nonneg.

Variable R : rcfType.

Fixpoint nonneg (s : seq R) : bool :=
   if s is a ::tl then (0 <= a) && (nonneg tl) else true.

Lemma nonneg_poly_deg1 : forall (a : R),
   nonneg ('X - a%:P) = (a <= 0).
Proof.
move=> a.
apply/idP/idP.
  rewrite polyseqXsubC /=.
  move/andP => Ha.
  rewrite -oppr_ge0.
  exact: (proj1 Ha).
rewrite polyseqXsubC /= => Ha.
apply/andP; split.
  by rewrite oppr_ge0.
apply/andP; split => //.
by apply: ler01.
Qed.

Lemma nonneg_poly_deg2 : forall (z : complex R),
   nonneg ('X^2 + (1 *- 2 * Re z) *: 'X + (Re z ^+ 2 + Im z ^+ 2)%:P)
    = ((Re z) <= 0).
Proof.
move=> z.
apply/idP/idP.
  rewrite -(mul1r 'X^2) mul_polyC polyseq_deg2 /=.
  move/andP => H.
  have H2 := (proj2 H).
  move/andP : H2 => H2.
  rewrite -(@nmulr_rge0 _ (1 *- 2) (Re z)).
    exact: (proj1 H2).
  rewrite oppr_lt0.
  apply: addr_gt0; by apply: ltr01.
  by apply: oner_neq0.
move=> Hz.
rewrite -(mul1r 'X^2) mul_polyC polyseq_deg2 /=.
  apply/andP; split.
    apply: addr_ge0; by apply: sqr_ge0.
  apply/andP; split.
    rewrite nmulr_rge0 // oppr_lt0.
    apply: addr_gt0; by apply: ltr01.
  apply/andP; split => //.
  by apply: ler01.
by apply: oner_neq0.
Qed.

Lemma nonneg_mulr : forall (p q : {poly R}),
   (nonneg p) -> (nonneg q) -> (nonneg (p * q)).
Proof.
Admitted. (**********)

Lemma nonneg_root_nonpos : forall (p : {poly R}),
   (p \is monic) -> (forall z : (complex R),
      root (map_poly (real_complex R) p) z -> ((Re z) <= 0)) -> nonneg p.
Proof.
move=> p Hpmonic.
move: {2}(size p) (leqnn (size p))=> n.
elim: n p Hpmonic.
(* size p <= 0 *)
  move=> p Hpmonic Hpsize Hproot. 
  rewrite size_poly_leq0 in Hpsize.
  move/eqP : Hpsize => Hpnull.
  by rewrite Hpnull monicE lead_coef0 eq_sym  oner_eq0 in Hpmonic.
(* size p <= n.+1 *)
move=> n IH p Hpmonic Hpsize Hproots.
have HpCsize : size (map_poly (real_complex R) p) != 1%N.
  rewrite size_map_poly_id0.
    admit. (***********)
  rewrite monicE in Hpmonic.
  move/eqP : Hpmonic => Hpmonic. rewrite Hpmonic.
  by apply: oner_neq0.    
move/closed_rootP : HpCsize.
case=> x Hrootx.
case: (altP (Im x =P 0)) => Himx. 
(* real root *)
  have H := monicXsubC (Re x).
  have Hp := real_root_div_poly_deg1 Himx Hrootx.
  rewrite Pdiv.IdomainMonic.dvdp_eq // in Hp.
  move/eqP : Hp => Hp. rewrite Hp.
  apply: nonneg_mulr.
    apply: IH.
        rewrite monicE -(@lead_coef_Mmonic _ (p %/ ('X - (Re x)%:P)) ('X - (Re x)%:P)) //. 
        by rewrite -Hp -monicE.
      rewrite size_divp.
        rewrite size_XsubC.
        by rewrite leq_subLR addnC addn1.
      by apply: monic_neq0.
    move=> z Hz.
    apply: Hproots.
    rewrite Hp rmorphM rootM.
    apply/orP. by left.
  rewrite nonneg_poly_deg1.
  by apply: (Hproots x Hrootx).
(* pair of complex roots *)
have H : 'X^2 + (1 *- 2 * Re x) *: 'X + (Re x ^+ 2 + Im x ^+ 2)%:P \is monic.
  rewrite -addrA monicE lead_coefDl.
    by rewrite lead_coefXn.
  rewrite size_polyXn -mul_polyC size_MXaddC size_polyC /=.
  case H : (((1 *- 2 * Re x)%:P == 0) && ((Re x ^+ 2 + Im x ^+ 2)%R == 0)).
    by apply: ltn0Sn.
  case H' : ((1 *- 2 * Re x)%R != 0).  
    by apply: ltnSn.
  by rewrite !ltnS leqnSn.
have H2 : size ('X^2 + (1 *- 2 * Re x) *: 'X + (Re x ^+ 2 + Im x ^+ 2)%:P) = 3.
  rewrite -mul_polyC expr2 -mulrDl size_MXaddC.
  have Help : (('X + (1 *- 2 * Re x)%:P == 0) && (Re x ^+ 2 + Im x ^+ 2 == 0) = false).
    apply: Bool.andb_false_intro2. apply/eqP/eqP.
    apply: (@proj1 _ (0 <= Re x ^+ 2 + Im x ^+ 2)).
    apply/andP. rewrite -lt0r. apply: ltr_spaddr.
      rewrite lt0r. apply/andP. split.
        by rewrite sqrf_eq0.
      by apply: sqr_ge0.
    by apply: sqr_ge0.
  by rewrite Help {Help} size_XaddC.
have Hp := complex_root_div_poly_deg2 Himx Hrootx.
rewrite Pdiv.IdomainMonic.dvdp_eq // in Hp.
move/eqP : Hp => Hp. rewrite Hp.
apply: nonneg_mulr.  
  apply: IH.
       rewrite monicE -(@lead_coef_Mmonic _ (p %/ ('X^2 + (1 *- 2 * Re x) *: 'X + (Re x ^+ 2 + Im x ^+ 2)%:P)) ('X^2 + (1 *- 2 * Re x) *: 'X + (Re x ^+ 2 + Im x ^+ 2)%:P)) //. 
        by rewrite -Hp -monicE.
     rewrite size_divp.
       rewrite H2.
       rewrite leq_subLR addnC addn2. 
       apply: (@leq_trans n.+1).
         by done.
       by apply: leqnSn.
     by apply: monic_neq0.
    move=> z Hz.
    apply: Hproots.
    rewrite Hp rmorphM rootM.
    apply/orP. by left.
  rewrite nonneg_poly_deg2.
  by apply: (Hproots x Hrootx).
Qed. (**********)

Lemma nonneg_changes0 : forall (s : seq R),
   (nonneg s) -> (changes s = 0%N).
Proof.
elim=> [ |a ] //.
case=> [_ _ |b l IHbl Hablnonneg] //.
  by rewrite /= mulr0 addn0 ltrr.
apply/eqP.
rewrite addn_eq0.
apply/andP ; split.
  rewrite /= eqb0 -lerNgt.
  move/andP : Hablnonneg => Hablnonneg.
  apply: mulr_ge0.
    exact: (proj1 Hablnonneg).
  move/andP : (proj2 Hablnonneg) => Hblnonneg.
  exact: (proj1 Hblnonneg).
apply/eqP.
apply: IHbl.
move/andP : Hablnonneg => Hablnonneg.
exact: (proj2 Hablnonneg).
Qed.

End about_nonneg.


Section about_changes_0.

Variable R : rcfType.

(* Proposition 2.39 *)
Lemma monic_roots_changes_eq0 : forall (p : {poly R}),
   p \is monic -> (forall (z : complex R),
     (root (map_poly (real_complex R) p) z) -> (Re z <= 0)) ->
      changes p = 0%N.
Proof.
move=> p Hpmonic H.
apply: nonneg_changes0.
by apply: nonneg_root_nonpos.
Qed.

End about_changes_0.

Section le_thm_des_3_cercles.

Variable R : rcfType.

Definition inC (l r : R) (z : complex R) :=
   (Re z) ^+2 - (l + r) * (Re z) + (Im z) ^+2 + r * l == 0.

Lemma inCE : forall (l r : R) (z : complex R),
   inC l r z = ((Re z) ^+2 - (l + r) * (Re z) + (Im z) ^+2 + r * l == 0).
Proof. by []. Qed.

(* Theorem 10.47 i. *)
(* Theorem three_circles_1 : forall (p : {poly R}) (l r : R) (z : complex R),
   (root (map_poly (real_complex R) p) z -> (inC l r z) = false) ->
      .
*)

End le_thm_des_3_cercles.