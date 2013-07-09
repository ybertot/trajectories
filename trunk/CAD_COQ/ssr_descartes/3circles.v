(*
This file consists of several sections:
- nonnegative lists, polynomials with nonnegative coefs
- proof of Proposition 2.39 of [bpr], monic_roots_changes_eq0
- complements for scaleX_poly
- complements for transformations in R and roots
- complements for transformations and equality
- complements for transformations in C and roots
- proof of 3 circles i)
- proof of 3 circles ii)

Proofs need cleaning, which is work in progress.
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype prime div bigop.
Require Import ssralg poly polydiv polyorder ssrnum zmodp polyrcf qe_rcf_th complex.
Require Import poly_normal pol.

Set Implicit Arguments.
Unset Strict Implicit.

Import GRing.Theory Num.Theory Num.Def.
Import Pdiv.Idomain.

Section about_nonneg.

Variable R : rcfType.

Definition nonneg := fun (s : seq R) => all (fun x => 0 <= x) s.

Lemma nonneg_is_nonneg_1 : forall (s : seq R),
   (nonneg s) -> (forall k, (k < size s)%N -> 0 <= s`_k).
Proof. move=> s; by apply/all_nthP. Qed.

Lemma nonneg_is_nonneg_2 : forall (s : seq R),
  (forall k, (k < size s)%N -> 0 <= s`_k) ->  (nonneg s).
Proof. move=> s H; by apply/(all_nthP 0). Qed.

Lemma nonneg_poly_deg1 : forall (a : R),
   nonneg ('X - a%:P) = (a <= 0).
Proof.
move=> a.
apply/idP/idP.
  rewrite polyseqXsubC /= => /andP Ha; rewrite -oppr_ge0.
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
move=> p.
case Hpsize : (p == 0).
  move/eqP : Hpsize => H q.
  by rewrite H mul0r => Hp Hq.
move/eqP/eqP : Hpsize => Hpsize q.
case Hqsize : (q == 0).
  move/eqP : Hqsize => H Hp.
  by rewrite H mulr0.
move/eqP/eqP :Hqsize=> Hqsize Hp Hq.
apply: nonneg_is_nonneg_2 => k Hk.
rewrite coef_mul_poly /=.
apply: sumr_ge0.
case=> i Hi _ /=.
apply: mulr_ge0.
  case Hi2 : (i < size p)%N.
    by apply: nonneg_is_nonneg_1.
  by rewrite -(coefK p) coef_poly Hi2.
case Hi2 : (k - i < size q)%N.
   by apply: nonneg_is_nonneg_1.
by rewrite -(coefK q) coef_poly Hi2.
Qed.

Lemma nonneg_root_nonpos : forall (p : {poly R}),
   (p \is monic) -> (forall z : (complex R),
      root (map_poly (real_complex R) p) z -> ((Re z) <= 0)) -> nonneg p.
Proof.
move=> p Hpmonic.
move: {2}(size p) (leqnn (size p)) => n.
elim: n p Hpmonic.
(* size p <= 0 *)
  move=> p Hpmonic Hpsize Hproot. 
  rewrite size_poly_leq0 in Hpsize.
  move/eqP : Hpsize => Hpnull.
  by rewrite Hpnull monicE lead_coef0 eq_sym  oner_eq0 in Hpmonic.
(* size p <= n.+1 *)
move=> n IH p Hpmonic Hpsize Hproots.
case Hpsize2 : (size (map_poly (real_complex R) p) == 1%N).
  (* size p == 1 *)
  move/eqP : Hpsize2 => Hpsize2.
  rewrite size_map_poly_id0 in Hpsize2.  
  have Hpsize3 := (eq_leq Hpsize2).
    have Hp := (size1_polyC Hpsize3).
    rewrite Hp in Hpsize2.
    rewrite Hp monicE lead_coefE Hpsize2 -pred_Sn polyseqC in Hpmonic.
    rewrite size_polyC in Hpsize2.
    rewrite Hpsize2 /= in Hpmonic.
    move/eqP : Hpmonic => Hpmonic.
    rewrite Hp /= Hpmonic polyseqC oner_neq0 /= Bool.andb_true_r.
    by apply: ler01.
  rewrite eq_sym; apply: negbT; apply: ltr_eqF.
  rewrite monicE in Hpmonic.
  move/eqP : Hpmonic => Hpmonic.
  rewrite ltcR Hpmonic.
  by apply: ltr01.
(* size p != 1 *)
have HpCsize := (negbT Hpsize2).
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
        rewrite monicE -(@lead_coef_Mmonic _ (p %/ ('X - (Re x)%:P))
          ('X - (Re x)%:P)) //. 
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
  rewrite -(mul1r 'X^2) mul_polyC monicE lead_coefE polyseq_deg2 //=.
  by apply: oner_neq0.
have H2 : size ('X^2 + (1 *- 2 * Re x) *: 'X + (Re x ^+ 2 + Im x ^+ 2)%:P) = 3.
  rewrite -(mul1r 'X^2) mul_polyC polyseq_deg2 //=.
  by apply: oner_neq0.
have Hp := complex_root_div_poly_deg2 Himx Hrootx.
rewrite Pdiv.IdomainMonic.dvdp_eq // in Hp.
move/eqP : Hp => Hp. rewrite Hp.
apply: nonneg_mulr.  
  apply: IH.
       rewrite monicE -(@lead_coef_Mmonic _ (p %/ ('X^2 + (1 *- 2 * Re x) *: 'X +
         (Re x ^+ 2 + Im x ^+ 2)%:P)) ('X^2 + (1 *- 2 * Re x) *: 'X +
           (Re x ^+ 2 + Im x ^+ 2)%:P)) //. 
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
Qed.

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

(*Lemma Bernstein_coeffsE : forall (G : ringType) (p : {poly G}) (a b : G),
   Bernstein_coeffs p a b = reciprocal_pol ((p \shift a) \scale (b - a)) \shift 1.
Proof. by []. Qed.*)

Section about_scaleX_poly.

Variable (R : comRingType).

Lemma scaleX_poly_is_linear (c : R) : linear (scaleX_poly c).
Proof. by move=> a u v; rewrite /scaleX_poly comp_polyD comp_polyZ. Qed.

Lemma scaleX_poly_multiplicative (c : R) : multiplicative (scaleX_poly c).
Proof.   
split. move=> x y; exact: comp_polyM. by rewrite /scaleX_poly comp_polyC.
Qed.

Canonical scaleX_poly_additive (c : R) := Additive (scaleX_poly_is_linear c).
Canonical scaleX_poly_linear c := Linear (scaleX_poly_is_linear c).
Canonical scaleX_poly_rmorphism c := AddRMorphism (scaleX_poly_multiplicative c).

Lemma scaleX_polyC (c a : R) : a%:P \scale c = a%:P.
Proof. by rewrite /scaleX_poly comp_polyC. Qed.

End about_scaleX_poly.

Section about_transformations.

Variable (R : fieldType).

Lemma root_shift_1 : forall (p : {poly R}) (a x : R),
   (root p x) = root (p \shift a) (x-a).
Proof. move=> p a x. by rewrite !rootE -horner_shift_poly1. Qed.

Lemma root_shift_2 : forall (p : {poly R}) (a x : R),
   root p (x + a) = root (p \shift a) x.
Proof. move=> p a x.
by rewrite !rootE -{2}(@addrK _ a x) -horner_shift_poly1.
Qed.

Lemma root_scale_1 : forall (p : {poly R}) (a x : R), (a != 0) ->
   root p x = root (p \scale a) (x / a).
Proof.
move=> p a x Ha.
rewrite !rootE horner_scaleX_poly mulrC (@mulrVK _ a _ x) //. 
by rewrite unitfE.
Qed.

Lemma root_scale_2 : forall (p : {poly R}) (a x : R),
   root p (a * x) = root (p \scale a) x.
Proof.
move=> p a x.
by rewrite !rootE horner_scaleX_poly.
Qed.

Lemma root_reciprocal_1 : forall (p : {poly R}) (x : R), (x != 0) ->
   root p x = root (reciprocal_pol p) (x^-1).
Proof.
move=> p x Hx.
rewrite !rootE horner_reciprocal1.
  rewrite GRing.mulrI_eq0 //.
  apply: GRing.lregX; by apply/lregP.
by rewrite unitfE.
Qed.

Lemma root_reciprocal_2 : forall (p : {poly R}) (x : R), (x != 0) ->
   root p (x^-1) = root (reciprocal_pol p) x.
Proof.
move=> p x Hx.
rewrite !rootE horner_reciprocal.
  rewrite GRing.mulrI_eq0 //.
  apply: GRing.lregX; by apply/lregP.
by rewrite unitfE.
Qed.

Lemma root_Bernstein_coeffs_1 : forall (p : {poly R}) (x : R) (l r : R),
   (l != r) -> (x != l) -> (x != r) ->
   root p x = root (Bernstein_coeffs p l r) ((r - x) / (x - l)).
Proof.
move=> p x l r Hlr Hxl Hxr.
rewrite /Bernstein_coeffs.
rewrite -root_shift_2 -(@mulrK _ (x - l) _ 1). 
  rewrite mul1r -mulrDl addrA.
  rewrite -(@addrA _ _ (-x) x) (@addrC _ (-x) x) addrA addrK. 
  rewrite -root_reciprocal_2. 
    rewrite invrM.
        rewrite invrK.
        rewrite -root_scale_2 mulrC divrK.
          by rewrite -root_shift_2 -addrA (@addrC _ _ l) addrA addrK. 
        by rewrite unitfE subr_eq0 eq_sym.
      by rewrite unitfE subr_eq0 eq_sym.
    by rewrite unitfE invr_eq0 subr_eq0.
  apply: GRing.mulf_neq0.
    by rewrite subr_eq0 eq_sym.
  by rewrite invr_eq0 subr_eq0.
by rewrite unitfE subr_eq0.
Qed.

Lemma root_Bernstein_coeffs_2 : forall (p : {poly R}) (x : R) (l r : R),
   (x + 1 != 0) ->
   root p ((r + l * x) / (x + 1)) = root (Bernstein_coeffs p l r) x.
Proof.
move=> p x l r Hx.
rewrite /Bernstein_coeffs.
rewrite -root_shift_2 -root_reciprocal_2 //. 
rewrite -root_scale_2 -root_shift_2 -{3}(@mulrK _ (x + 1) _ l).
  by rewrite -mulrDl {2}(@addrC _ x 1) mulrDr mulr1 addrA
       -(addrA r (- l) l) (addrC (-l) l) addrA addrK.
by rewrite unitfE.
Qed.

Lemma Bernstein_coeffsM : forall (p q : {poly R}) (l r : R),
   Bernstein_coeffs (p * q) l r =
   (Bernstein_coeffs p l r) * (Bernstein_coeffs q l r).
Proof.
move=> p q l r.
by rewrite /Bernstein_coeffs !rmorphM /= reciprocalM rmorphM.
Qed.

Lemma Bernstein_coeffs_Xsubc : forall (c l r : R), (l != r) ->
   Bernstein_coeffs ('X - c%:P) l r = (l - c) *: 'X + (r - c)%:P.
Proof.
move=> c l r Hlr.
rewrite /Bernstein_coeffs rmorphB /= shift_polyC rmorphB /= scaleX_polyC.
rewrite /shift_poly comp_polyX rmorphD /= scaleX_polyC /scaleX_poly
   comp_polyX -addrA -(rmorphB _ l c) /=. 
rewrite reciprocal_monom.
rewrite rmorphD rmorphM /= comp_polyX !comp_polyC.
rewrite mulrDl polyC1 mul1r mulrC mul_polyC -addrA (addrC (l - c)%:P _)
    -rmorphD /= addrA addrNK //.
by rewrite subr_eq0 eq_sym.
Qed.

Lemma Bernstein_coeffs_Xsubc_monic : forall (c l r : R),
   (l != r) -> (l != c) ->
   (lead_coef (Bernstein_coeffs ('X - c%:P) l r))^-1 *:
      (Bernstein_coeffs ('X - c%:P) l r) 
         = 'X + ((r - c) / (l - c))%:P.
Proof.
move=> c l r Hlr Hlc.
rewrite Bernstein_coeffs_Xsubc //  lead_coefE.
have Hlc2 : ((l - c) != 0).
  by rewrite subr_eq0.
have HlcP : ((l - c)%:P == 0) = false.
  apply/eqP/eqP.
  by rewrite polyC_eq0 subr_eq0.
have Hsize : size ((l - c) *: 'X + (r - c)%:P) = 2.  
  rewrite -(mul_polyC (l - c) 'X).
  rewrite size_MXaddC HlcP /= size_polyC.
  by rewrite Hlc2.
have Hcoef1 : ((l - c) *: 'X + (r - c)%:P)`_1 = (l - c).
  by rewrite coefD coefC addr0 -mul_polyC coefMX coefC /=.
by rewrite Hsize -mul_polyC Hcoef1 mulrDr mul_polyC -rmorphM
   mulrC -!mul_polyC mulrA (mulrC _ 'X) -rmorphM (mulrC _ (l - c))
   mulfV //= polyC1 mulr1.
Qed.

End about_transformations.

Section about_transformations_and_equality.

Variable (R : idomainType).

Lemma shift_poly_eq : forall (p q : {poly R}) (a : R),
   (p == q) = (p \shift a == q \shift a).
Proof.
move=> p q a.
apply/idP/idP => Hpq.
  by move/eqP : Hpq => ->.
rewrite /shift_poly in Hpq.
rewrite -subr_eq0 -(@comp_poly2_eq0 _ (p-q) ('X + a%:P)) ?size_XaddC //.
by rewrite rmorphB subr_eq add0r.
Qed.

Lemma scale_poly_eq : forall (p q : {poly R}) (a : R), (a != 0) ->
   (p == q) = (p \scale a == q \scale a).
Proof.
move=> p q a Ha.
apply/idP/idP => Hpq.
  by move/eqP : Hpq => ->.
rewrite /scaleX_poly in Hpq.
rewrite -subr_eq0 -(@comp_poly2_eq0 _ (p-q) ('X * a%:P)) ?size_XmulC //.
by rewrite rmorphB subr_eq add0r.
Qed.

(*Lemma reciprocalD : forall (p q : {poly R}),
   reciprocal_pol (p + q) = (reciprocal_pol p) + (reciprocal_pol q).
Proof.
Admitted.

Lemma reciprocalB : forall (p q : {poly R}),
   reciprocal_pol (p - q) = (reciprocal_pol p) - (reciprocal_pol q).
Proof.
Admitted.*)


Lemma reciprocal_Xn : forall n,
   reciprocal_pol ('X^n) = (GRing.one R)%:P.
Proof.
move=> n.
rewrite /reciprocal_pol size_polyXn poly_def big_ord_recl.
rewrite subSS subn0 coefXn expr0 eqxx scale1r big1 ?addr0 // => i _.
rewrite lift0 subSS coefXn /=.
have H : (((n - i.+1)%N == n) = false).
  apply: negbTE.
  rewrite neq_ltn.
  apply/orP; left.
  rewrite -(ltn_add2r i.+1) subnK.
    rewrite -addSnnS. apply: ltn_addr. by apply: ltnSn.
  by case: i.
by rewrite H /= -mul_polyC mul0r.
Qed.

Lemma reciprocal_Xn_root0 : forall p : {poly R},
   reciprocal_pol p = reciprocal_pol (p %/ 'X^(\mu_0 p)).
Proof.
move=> p.
rewrite -(addr0 'X) -oppr0.
have Hmu0 := (root_mu p 0).
rewrite Pdiv.IdomainMonic.dvdp_eq in Hmu0.
  move/eqP : Hmu0 => Hmu0.
  by rewrite {1}Hmu0 reciprocalM {2}oppr0 addr0 reciprocal_Xn polyC1 mulr1 polyC0.
rewrite polyC0 oppr0 addr0. by apply: monicXn.
Qed.

Lemma pdivmu0_0th_neq0 : forall p : {poly R}, (p != 0) ->
   (p %/ 'X^(\mu_0 p))`_0 != 0.
Proof.
move=> p Hp.
have H0noroot : ~~(root (p %/ 'X^(\mu_0 p)) 0).
  rewrite -mu_gt0 //.  
    rewrite -eqn0Ngt -(addr0 'X) -(@oppr0 (poly_zmodType R)) -polyC0 mu_div.
      rewrite subn_eq0. by apply: leqnn.
    by apply: leqnn.
  rewrite Pdiv.CommonIdomain.divp_eq0.
  rewrite negb_or. apply/andP; split.
    by done.
  rewrite negb_or. apply/andP; split.
    rewrite -size_poly_gt0 size_polyXn. by apply: ltn0Sn.
  rewrite -leqNgt. apply: dvdp_leq =>//.
  rewrite -(addr0 'X) -oppr0 -polyC0.
  by apply: root_mu.
rewrite -horner_coef0. apply: negbT.
by move/rootPf : H0noroot.
Qed.

Lemma reciprocal_reciprocal : forall p : {poly R},
   reciprocal_pol (reciprocal_pol p) = p %/ ('X^(\mu_0 p)).
Proof.
move=> p.
case Hp0 : (p == 0).
  move/eqP : Hp0 => ->.
  by rewrite !reciprocalC div0p polyC0.
rewrite (@reciprocal_Xn_root0 p) reciprocal_idempotent //.
apply: pdivmu0_0th_neq0.
by apply: negbT.
Qed.

Lemma reciprocal0 : forall p : {poly R},
   (reciprocal_pol p == 0) = (p == 0).
Proof.
move=> p.
apply/idP/idP => Hp.
  have H : (p %/ ('X^(\mu_0 p)) == 0).
    rewrite -reciprocal_reciprocal.
    rewrite -polyC0 -reciprocalC.
    by move/eqP : Hp => ->.
  rewrite Pdiv.CommonIdomain.divp_eq0 in H.
  move/orP : H; case => [| H]//.
  move/orP : H; case => H.
    rewrite -size_poly_eq0 size_polyXn in H.
    by rewrite -(Bool.negb_involutive (_.+1 == 0%N)) -lt0n /= in H.
  have H2 := (root_mu p 0).
  case Hp0 : (p == 0) => //.
  rewrite gtNdvdp // in H2.  
    by apply: negbT.
  by rewrite oppr0 addr0.  
move/eqP : Hp => ->.
by rewrite -polyC0 reciprocalC.
Qed.

Lemma reciprocal_nth : forall (p : {poly R}) k, (k < size p)%N ->
   (reciprocal_pol p)`_k = p`_((size p) - k.+1).
Proof.
move=> p k Hk.
by rewrite /reciprocal_pol coef_poly Hk.
Qed.

Lemma reciprocal_nth_2 : forall (p : {poly R}) k, (k < size p)%N ->
   (reciprocal_pol p)`_(size p - k.+1) = p`_k.
Proof.
move=> p k Hk.
rewrite /reciprocal_pol coef_poly. 
have Hk2 : (size p - k.+1 < size p)%N.
  rewrite -(ltn_add2r k.+1) subnK // -addSnnS.
  apply: ltn_addr. by apply: ltnSn.
rewrite Hk2.
rewrite !subnS -!subn1 !subnBA.
    by rewrite addn1 -subnDA addn1 addnC addnK.
  by apply: ltnW.
by rewrite subn_gt0.
Qed. 

Lemma reciprocal_eq : forall (p q : {poly R}), (p`_0 != 0) -> (q`_0 != 0) ->
   (p == q) = (reciprocal_pol p == reciprocal_pol q).
Proof.
move=> p q Hp0 Hq0.
apply/idP/idP => Hpq.
  by move/eqP : Hpq => ->.
move/eqP : Hpq => Hpq.
apply/eqP.
apply: poly_inj.
have Hsize : (size p = size q).
  by rewrite -reciprocal_size // -(@reciprocal_size _ q) // Hpq.
apply: eq_from_nth => // i Hi.
rewrite -reciprocal_nth_2 // -(@reciprocal_nth_2 q) //. 
  by rewrite Hpq Hsize.
by rewrite -Hsize.
Grab Existential Variables.
exact: 0.
Qed.

End about_transformations_and_equality.

Section transformations_in_C.

Variable (R : rcfType).
Local Notation C:= (complex R).

Local Notation toC := (fun (p : {poly R}) =>
   @map_poly R _ (real_complex R) p).

Lemma shift_toC : forall (p : {poly R}) (a : R),
   toC (p \shift a) = (toC p) \shift a%:C.
Proof.
move=> p a.
by rewrite /shift_poly (map_comp_poly _ p ('X + a%:P)) rmorphD /=
   map_polyX map_polyC.
Qed.

Lemma scale_toC : forall (p : {poly R}) (a : R),
   toC (p \scale a) = (toC p) \scale a%:C.
Proof.
move=> p a.
by rewrite /scaleX_poly (map_comp_poly _ p ('X * a%:P)) rmorphM /=
   map_polyX map_polyC.
Qed.

Lemma reciprocal_toC : forall (p : {poly R}),
   toC (@reciprocal_pol _ p) = reciprocal_pol (toC p).
Proof.
move=> p.
rewrite /reciprocal_pol poly_def rmorph_sum /= poly_def size_map_inj_poly.
    apply: eq_bigr => i _.
    rewrite -mul_polyC.
    rewrite rmorphM /= map_polyXn /=.
    by rewrite !coef_map /= map_polyC /= mul_polyC.
  by apply: complexI.
by rewrite -complexr0.
Qed.

Lemma Bernstein_toC : forall (p : {poly R}) (l r : R),
   toC (Bernstein_coeffs p l r) = Bernstein_coeffs (toC p) l%:C r%:C.
Proof.
move=> p l r.
by rewrite {2}/Bernstein_coeffs -shift_toC /= -rmorphB -scale_toC
   -reciprocal_toC -shift_toC /Bernstein_coeffs.
Qed.

Lemma root_Bernstein_coeffs_C_1 :  forall (p : {poly R}) (z : C) (l r : R),
   (l != r) -> (z != l%:C) -> (z != r%:C) ->
      root (toC p) z =
      root (toC (Bernstein_coeffs p l r)) ((r%:C - z) / (z - l%:C)).
Proof.
move=> p z l r Hlr Hzl Hzr.
have HlrC : (l%:C != r%:C).
  rewrite -!complexr0 eq_complex /= negb_and.
  apply/orP.
  by left.
rewrite !rootE Bernstein_toC /Bernstein_coeffs -!rootE.
rewrite -@root_shift_2 -(@mulrK _ (z - l%:C) _ 1). 
  rewrite mul1r -mulrDl addrA.
  rewrite -(@addrA _ _ (-z) z) (@addrC _ (-z) z) addrA addrK. 
  rewrite -root_reciprocal_2. 
    rewrite invrM.
        rewrite invrK.
        rewrite -root_scale_2 mulrC divrK.
          by rewrite -root_shift_2 -addrA (@addrC _ _ l%:C) addrA addrK.
        by rewrite unitfE subr_eq0 eq_sym.
      by rewrite unitfE subr_eq0 eq_sym.
    by rewrite unitfE invr_eq0 subr_eq0.
  apply: GRing.mulf_neq0.
    by rewrite subr_eq0 eq_sym.
  by rewrite invr_eq0 subr_eq0.
by rewrite unitfE subr_eq0.
Qed.

Lemma root_Bernstein_coeffs_C_2 : forall (p : {poly R}) (z : C) (l r : R),
   (z + 1 != 0) ->
      root (toC p) ((r%:C + l%:C * z) / (z + 1)) = 
      root (toC (Bernstein_coeffs p l r)) z.
Proof.
move=> p z l r Hz.
rewrite !rootE Bernstein_toC /Bernstein_coeffs -!rootE.
rewrite -root_shift_2 -root_reciprocal_2 //. 
rewrite -root_scale_2 -root_shift_2 -{3}(@mulrK _ (z + 1) _ l%:C).
  by rewrite -mulrDl {2}(@addrC _ z 1) mulrDr mulr1 addrA -(addrA r%:C (- l%:C) l%:C)
       (addrC (-l%:C) l%:C) addrA addrK.
by rewrite unitfE.
Qed.

End transformations_in_C.

Lemma mul_polyC_seqmul : forall (R : rcfType) (p : {poly R}) (a : R),
   (a != 0) ->
   polyseq (a *: p) = seqmul (nseq (size p) a) p.
Proof.
move=> R p a Ha.
elim/poly_ind : p => [ | p c IHp].
  by rewrite size_poly0 /= seqmul0 -mul_polyC mulr0 -polyC0 polyseq0.
rewrite -{2}(cons_poly_def) -mul_polyC mulrDr mulrA mul_polyC -polyC_mul.
rewrite -!cons_poly_def !polyseq_cons.
case Hp : (~~ (nilp p)).
  have Hp2 : (~~ (nilp (a *: p))).
    rewrite nil_poly -mul_polyC.
    rewrite nil_poly in Hp.
    apply: mulf_neq0.
      by rewrite polyC_eq0.
    by rewrite Hp.
  rewrite Hp2.
  by rewrite seqmul_cons IHp.
have Hp2 : (nilp (a *: p)).
  rewrite nil_poly -mul_polyC mulf_eq0.
  rewrite nil_poly in Hp.
  apply/orP; right.
  by apply: negbFE.
rewrite Hp2 /= size_polyC.
case Hc : (c != 0).
  have Hac : (a * c != 0).
    by apply: mulf_neq0.
  by rewrite !polyseqC Hc /= Hac.
have Hac : ((a * c != 0) = false).
  apply: negbTE.
  rewrite mulf_eq0 negb_or negb_and.
  apply/orP; right.
  by rewrite Hc.
by rewrite !polyseqC Hc Hac /=.
Qed.

Lemma changes_mulC : forall (R : rcfType) (p : {poly R}) (a : R), (a != 0) ->
   changes p = changes (a *: p).
Proof.
move=> R p a Ha.
rewrite mul_polyC_seqmul //=.
move: p.
case => s Hs. 
elim: s Hs => [Hs |b l IHl Hs] //=.
case: l IHl Hs => [_ _ |c l IHcl Hs ] //=.
  by rewrite !addn0 !mulr0.
rewrite /= in IHcl.
rewrite IHcl //=.
rewrite /seqmul. apply/eqP. rewrite eqn_add2r.
rewrite !mulrA (mulrC a) -(mulrA b) -expr2 (mulrC _ (a^+2)) -mulrA eq_sym.
apply/eqP.
rewrite (@pmulr_rlt0 _ (a ^+2) (b * c)) //.
rewrite ltr_def; apply/andP; split.
  by rewrite sqrf_eq0.  
by apply: sqr_ge0.
Qed.

Lemma Bernstein_coeffs_0 : forall (R : idomainType) (p : {poly R}) (a b : R),
   (a != b) ->
   (p == 0) = ((Bernstein_coeffs p a b) == 0).
Proof.
move=> R p a b Hab.
apply/idP/idP => Hp; move/eqP : Hp => Hp.
  by rewrite /Bernstein_coeffs Hp /shift_poly /scaleX_poly !comp_polyC
     reciprocalC comp_polyC.
rewrite /Bernstein_coeffs in Hp.
rewrite (shift_poly_eq p 0 a) shift_polyC (@scale_poly_eq R _ _  (b - a)).
  rewrite /scaleX_poly comp_polyC -(@reciprocal0 R) (shift_poly_eq _ _ 1)
     shift_polyC.
  rewrite /Bernstein_coeffs in Hp.
  by rewrite Hp.
by rewrite subr_eq0 eq_sym.
Qed.
  
Section thm_3_cercles_partie1.

Variables (R : rcfType) (l r : R) (Hlr_le : l < r).

Local Notation C := (complex R).

Lemma Hlr : l != r.
Proof.
rewrite eq_sym.
apply: (@proj1 (r != l) (l <= r)).
apply/andP.
by rewrite -ltr_def.
Qed.

Lemma HlrC : (l%:C != r%:C).
Proof.
rewrite -!complexr0 eq_complex /= negb_and.
apply/orP; left.
exact: Hlr.
Qed.

Definition notinC (z : C) :=
   0 <= (Re z) ^+2 - (l + r) * (Re z) + (Im z) ^+2 + r * l.

Lemma notinCE : forall (z : C),
   notinC z = (0 <= (Re z) ^+2 - (l + r) * (Re z) + (Im z) ^+2 + r * l).
Proof. by []. Qed.

Lemma notinC_Re_lt0_1 : forall (z : C), (z != l%:C) ->
   (notinC z) = (Re ((r%:C - z) / (z - l%:C)) <= 0).
Proof.
case => a b Hab.
rewrite notinCE /=.
simpc.
rewrite !mulrA.
apply/idP/idP => H.
  rewrite -(mulNr (b * b) _) -mulrDl.
  apply: mulr_le0_ge0.
    rewrite -expr2 (mulrDl r (-a) _) (mulrC r (a - l)) (mulrC (-a) _) (mulrDl _ _ r)
       (mulrDl _ _ (-a)) mulrNN mulrN -expr2 !addrA (addrC (a * r) _)
       -(addrA _ (a * r) _ ) (addrC (a * r) _ ) (mulrC a r) addrA (addrC (- l * r) _ )
       -(addrA _ (r * a) (l * a)) -(mulrDl _ _ a) -(addrA (- a ^+2) _ _)
       (addrC (- l * r)) -!addrA (addrC _ (- b^+2)) !addrA mulNr (mulrC l r) (addrC r l).
    by rewrite -oppr_ge0 !opprD !opprK.
  rewrite invr_ge0.
  apply: addr_ge0; by apply: sqr_ge0.
rewrite -(mulNr (b * b) _) -mulrDl in H.
rewrite -expr2 (mulrDl r (-a) _) (mulrC r (a - l)) (mulrC (-a) _) (mulrDl _ _ r)
   (mulrDl _ _ (-a)) mulrNN mulrN -expr2 !addrA (addrC (a * r) _)
   -(addrA _ (a * r) _ ) (addrC (a * r) _ ) (mulrC a r) addrA (addrC (- l * r) _ )
   -(addrA _ (r * a) (l * a)) -(mulrDl _ _ a) -(addrA (- a ^+2) _ _)
   (addrC (- l * r)) -!addrA (addrC _ (- b^+2)) !addrA mulNr (mulrC l r) (addrC r l)
   in H.
rewrite -oppr_le0 !opprD !opprK.
rewrite -complexr0 eq_complex negb_and /= in Hab.
have H2 : (0 <= (a - l) ^+ 2 + b ^+ 2).
  apply: addr_ge0; by apply: sqr_ge0.
move/orP : Hab => Hab.
case: Hab => H3.
  rewrite -(@pmulr_lle0 _ ((a - l) ^+ 2 + b ^+ 2)^-1
     (- a ^+ 2 + (l + r) * a - b ^+ 2 - r * l)) //.
  rewrite ltr_def.
  apply/andP; split.
    apply: invr_neq0.
    rewrite paddr_eq0. 
        rewrite negb_and.
        apply/orP.
        left.
        by rewrite sqrf_eq0 subr_eq0.
      by apply: sqr_ge0.
    by apply: sqr_ge0.
  by rewrite invr_ge0.
rewrite -(@pmulr_lle0 _ ((a - l) ^+ 2 + b ^+ 2)^-1
     (- a ^+ 2 + (l + r) * a - b ^+ 2 - r * l)) //.
rewrite ltr_def.
apply/andP; split.
  apply: invr_neq0.
  rewrite paddr_eq0. 
      rewrite negb_and.
      apply/orP.
      right.
      by rewrite sqrf_eq0.
    by apply: sqr_ge0.
  by apply: sqr_ge0.
by rewrite invr_ge0.
Qed.

Lemma notinC_Re_lt0_2 : forall (z : C), (z + 1 != 0) ->
   (notinC ((r%:C + l%:C * z) / (z + 1))) = (Re z <= 0).
Proof.
move=> z Hz. 
rewrite (@notinC_Re_lt0_1 ((r%:C + l%:C * z) / (z + 1))) /=.
  rewrite -{1}(@mulrK _ (z+1) _ r%:C).
    rewrite -(mulNr (r%:C + l%:C * z) _ ) -(mulrDl _ _ (z+1)^-1) mulrDr mulr1 opprD
       !addrA addrK -{3}(@mulrK _ (z+1) _ l%:C).
      rewrite -(mulNr (l%:C * (z+1)) _ ) -(mulrDl _ _ (z+1)^-1) mulrDr mulr1
         opprD !addrA addrK invrM.
          rewrite invrK !mulrA -(mulrA _ _ (z+1)) (mulrC _ (z+1)) !mulrA mulrK.
            rewrite -mulNr -mulrDl (mulrC _ z) mulrK.
              by done.
            rewrite unitfE subr_eq0 eq_sym; by apply: HlrC.
          by rewrite unitfE.
        rewrite unitfE subr_eq0 eq_sym; by apply: HlrC.
      by rewrite -unitrV invrK unitfE.
    by rewrite unitfE.
  by rewrite unitfE.
rewrite -subr_eq0 -{2}(@mulrK _ (z + 1) _ l%:C).
  rewrite -mulNr -mulrDl mulrDr mulr1 opprD addrA addrK.
  apply: mulf_neq0.
    rewrite subr_eq add0r eq_sym; by apply: HlrC.
  by rewrite invr_eq0.
by rewrite unitfE.
Qed.

(* Theorem 10.47 i. *)
Theorem three_circles_1 : forall (p : {poly R}), (forall (z : C),
   root (map_poly (real_complex R) p) z -> (notinC z)) ->
      changes (Bernstein_coeffs p l r) = 0%N.
Proof.
move=> p H.
have Hlr := Hlr.
case Hp0 : (p == 0).
  rewrite (Bernstein_coeffs_0 p Hlr) in Hp0.
  move/eqP : Hp0 => ->.
  by rewrite polyseq0.
rewrite (@changes_mulC R (Bernstein_coeffs p l r)
   (lead_coef (Bernstein_coeffs p l r))^-1).
  apply: monic_roots_changes_eq0.
    rewrite monicE lead_coefZ mulrC -unitrE unitfE lead_coef_eq0
       -Bernstein_coeffs_0 //.
    apply/eqP.
    by move/eqP : Hp0.
  move=> z Hz.
  case Hz2 : (z + 1 == 0).
    rewrite addr_eq0 eq_complex in Hz2.
    move/andP : Hz2; case => Hrez _.
    move/eqP : Hrez => ->.
    rewrite raddfN.
    by apply: lerN10.
  rewrite map_polyZ rootZ /= in Hz.
    move/eqP/eqP : Hz2 => Hz2.
    rewrite -root_Bernstein_coeffs_C_2 // in Hz.
    rewrite -notinC_Re_lt0_2 //.
    apply: H => //.
  rewrite -complexr0 eq_complex /= negb_and.
  apply/orP; left.
  rewrite invr_eq0 lead_coef_eq0 -Bernstein_coeffs_0 //. 
  by apply: negbT. 
rewrite invr_eq0 lead_coef_eq0 -Bernstein_coeffs_0 //.  
by apply: negbT.
Qed.

End thm_3_cercles_partie1.

Section thm_3_cercles_partie2.

Variable (R : rcfType).

Local Notation C := (complex R).

Definition inC1 := fun (l r : R) (z : C) =>
   (Re z) ^+2 - (l + r) * (Re z) + (Im z) ^+2 - 
   (r - l) * (Im z) / (Num.sqrt 3%:R) + l * r < 0.

Definition inC2 := fun (l r : R) (z : C) =>
   (Re z) ^+2 - (l + r) * (Re z) + (Im z) ^+2 + 
   (r - l) * (Im z) / (Num.sqrt 3%:R) + l * r < 0.

Definition inC12 := fun (l r : R) (z : C) =>
   ((Re z) ^+2 - (l + r) * (Re z) + (Im z) ^+2 - 
   (r - l) * (Im z) / (Num.sqrt 3%:R) + l * r < 0) ||
   ((Re z) ^+2 - (l + r) * (Re z) + (Im z) ^+2 + 
   (r - l) * (Im z) / (Num.sqrt 3%:R) + l * r < 0).

Lemma inC12E : forall (l r : R) (z : C),
   inC12 l r z =  ((Re z) ^+2 - (l + r) * (Re z) + (Im z) ^+2 - 
   (r - l) * (Im z) / (Num.sqrt 3%:R) + l * r < 0) ||
   ((Re z) ^+2 - (l + r) * (Re z) + (Im z) ^+2 + 
   (r - l) * (Im z) / (Num.sqrt 3%:R) + l * r < 0).
Proof. by done. Qed.

Lemma inC1_or_inC2 : forall (l r : R) (z : C),
   (inC1 l r z) || (inC2 l r z) = (inC12 l r z).
Proof. by done. Qed.

Definition inB1 := fun (z : C) =>
   ((Re z) - 1 <= 0) && ((Im z)^+2 <= 3%:R * ((Re z) - 1) ^+2).

Lemma inB_inB1 : forall (z : C), (inB z) = (inB1 (z + 1)).
Proof.
case => a b.
by rewrite /inB1 /= addrK addr0 inBE.
Qed.

(*
Lemma inB1_help : forall (z : C), (inB1 z) = 
   (((Num.sqrt 3%:R) * ((Re z) - 1) - Im(z) <= 0) && 
     (0 <= - (Num.sqrt 3%:R * ((Re z) - 1)) - Im(z))).
Proof.
case=> a b.
rewrite /inB1 /=.
case Ha : (a - 1 == 0); move/eqP : Ha => Ha.
  rewrite Ha /= mulr0 oppr0 add0r lerr Bool.andb_true_l (expr2 0) !mulr0. 
  rewrite -eqr_le oppr_eq0 -sqrf_eq0.
  apply/idP/idP => H.
    rewrite eqr_le; apply/andP; split.
      by done.
    by apply: sqr_ge0.
  rewrite eqr_le in H; by case/andP : H => H1 H2.
*)

Lemma inB1_help : forall (z : C), (inB1 z) = 
   (((Num.sqrt 3%:R) * ((Re z) - 1) - Im(z) <= 0) && 
     (0 <= - (Num.sqrt 3%:R * ((Re z) - 1)) - Im(z))).
Proof.
case=> a b.
rewrite /inB1 /=.
apply/idP/idP; case/andP => H1 H2.
  case Ha : (a - 1 == 0); move/eqP : Ha => Ha.
    rewrite Ha mulr0 oppr0 add0r -eqr_le oppr_eq0 -sqrf_eq0 eqr_le.
    apply/andP; split.
      by rewrite Ha (expr2 0) !mulr0 in H2.
    by apply: sqr_ge0.
  have Ha2 : (0 < -(a - 1)).
    rewrite oppr_gt0 ltr_def; apply/andP; split => //.
    rewrite eq_sym; by apply/eqP.
  rewrite -(sqr_sqrtr (a:=3%:R)) in H2.
    rewrite -ComplexField.exprM in H2.
    rewrite -ler_sqrt in H2.
      rewrite !sqrtr_sqr normrM in H2.
      rewrite (ger0_norm (x := Num.sqrt 3%:R)) in H2.
        rewrite -(normrN (a-1)) (gtr0_norm (x:= - (a - 1))) // in H2.
        rewrite ler_norml in H2.
        case/andP : H2 => H2 H3.
        rewrite mulrN opprK in H2.
        apply/andP; split.
          by rewrite subr_le0.
        rewrite mulrN in H3.
        by rewrite subr_ge0.
      by apply: sqrtr_ge0.
    rewrite ComplexField.exprM.
    apply: mulr_gt0; rewrite ltr_def; apply/andP; split.
          by rewrite sqrf_eq0 sqrtr_eq0 -ltrNge ltr0n.
        by apply: sqr_ge0.
      rewrite sqrf_eq0; by apply/eqP.
    by apply: sqr_ge0.
  by apply: ler0n.
(* second direction *)
have Hb : `|b| <= Num.sqrt 3%:R * -(a - 1).
  rewrite ler_norml.
  apply/andP; split.
    by rewrite mulrN opprK -subr_le0.
  by rewrite -subr_ge0 mulrN.
have Ha2 : (0 <= - (a - 1)).
  rewrite -(pmulr_lge0 (x:=Num.sqrt 3%:R)).
    rewrite mulrC.
    by apply: (ler_trans (y:=`|b|)).  
  rewrite sqrtr_gt0; by apply: ltr0n.
apply/andP; split.
  by rewrite -oppr_ge0.
case Ha : (a - 1 == 0).
  move/eqP : Ha => Ha.
  rewrite Ha (expr2 0) !mulr0.
  rewrite Ha oppr0 mulr0 normr_le0 in Hb.
  move/eqP : Hb => ->.
  by rewrite expr2 mulr0.
rewrite -(sqr_sqrtr (a:=3%:R)) -ler_sqrt.
      rewrite -ComplexField.exprM !sqrtr_sqr normrM -(normrN (a-1))
        (ger0_norm (x:=Num.sqrt 3%:R)).
        by rewrite (ger0_norm (x:=- (a - 1))). 
      by apply: sqrtr_ge0.
    rewrite pmulr_lgt0; rewrite ltr_def; apply/andP; split.
          by rewrite sqrf_eq0 sqrtr_eq0 -ltrNge ltr0n.
        by apply: sqr_ge0.
      rewrite sqrf_eq0; by apply: negbT.
    by apply: sqr_ge0.
  rewrite ler_sqrt.
    by apply: ler0n.
  by rewrite ltr0n.
by rewrite ltr0n.
Qed.  

Lemma Re_invc : forall (z : C), Re z^-1 = Re z / ((Re z) ^+ 2 + (Im z) ^+2).
Proof. by case. Qed.

Lemma Im_invc : forall (z : C), Im z^-1 = (- Im z) / ((Re z) ^+ 2 + (Im z) ^+2).
Proof. case => a b. by rewrite mulNr. Qed.

Lemma inB1_notinC1201 : forall (z : C), (z != 0) ->
   (inB1 z) = ~~(inC12 0 1 (z ^-1)).
Proof.
case=> a b Hz.
rewrite -inC1_or_inC2 negb_or inB1_help /=.
have H : a ^+ 2 + b ^+ 2 \is a GRing.unit.
  rewrite eq_complex /= negb_and in Hz.
  move/orP:Hz; case=> H.
    rewrite unitfE paddr_eq0 ?sqr_ge0 // negb_and.
    apply/orP; left; by rewrite sqrf_eq0.
  rewrite unitfE paddr_eq0 ?sqr_ge0 // negb_and.
  apply/orP; right; by rewrite sqrf_eq0.
have H3 : (Num.ExtraDef.sqrtr (GRing.natmul (V:=R) (GRing.one R) (3))) \is a GRing.unit.
  by rewrite unitfE sqrtr_eq0 -ltrNge ltr0n.
rewrite /inC1 /= -lerNgt add0r oppr0 mul0r !addr0 !mul1r.
rewrite [x in (0 <= ((x + _) + _))]addrC -[x in (0 <= (x + _))]addrA
   ComplexField.exprM -(mulNr b) ComplexField.exprM sqrrN -mulrDl
   (expr2 ((a^+2 + b^+2)^-1)) -{2}(mulr1 (a^+2 + b^+2)) -invrM //
   -mulf_div [x in (0 <= _ + x + _)]mulrC !mulrA (mulrK (x:=(a^+2 + b^+2))) //
   -[in x in _ = x]mulNr -mulrDl -{5}(opprK 1) -(opprD a (- 1)) -mulrA -invrM //. 
rewrite -[in x in _ = x]mulNr -(mul1r ( - (a - 1) / (a ^+ 2 + b ^+ 2))) 
   -{5}(@mulrK _ (Num.sqrt 3%:R) _ 1) //.
rewrite mul1r mulf_div -mulrDl mulrN -[in x in (_ = x)]opprD.
rewrite /inC2 /= -lerNgt add0r oppr0 mul0r !addr0 !mul1r.
rewrite [x in (0 <= ((x + _) + _))]addrC -[x in (0 <= (x + _))]addrA
   ComplexField.exprM -(mulNr b) ComplexField.exprM sqrrN -mulrDl
   (expr2 ((a^+2 + b^+2)^-1)) -{3}(mulr1 (a^+2 + b^+2)) -invrM //
   -mulf_div [x in (0 <= _ + x + _)]mulrC !mulrA (mulrK (x:=(a^+2 + b^+2))) //
   -[in x in (_ = _ && x)]mulNr -mulrDl -{8}(opprK 1) -(opprD a (- 1)) -mulrA -invrM //. 
rewrite -(mul1r ( - (a - 1) / (a ^+ 2 + b ^+ 2))) 
    -{8}(@mulrK _ (Num.sqrt 3%:R) _ 1) //.
rewrite mul1r mulf_div -mulrDl.
rewrite mulNr oppr_ge0 pmulr_lge0.
  rewrite pmulr_lle0.
    by rewrite mulrN.  
  rewrite invr_gt0 ltr_def; apply/andP; split.
    rewrite -unitfE unitrM; apply/andP; by split.
  apply: mulr_ge0.
    by apply: sqrtr_ge0.
  apply: addr_ge0; by apply: sqr_ge0.
rewrite invr_gt0 ltr_def; apply/andP; split.
  rewrite -unitfE unitrM; apply/andP; by split.
apply: mulr_ge0.
  by apply: sqrtr_ge0.
apply: addr_ge0; by apply: sqr_ge0.
Qed.

Lemma notinC1201_lr_scale : forall (l r : R) (z : C), (l != r) ->
   ~~(inC12 0 1 z) = ~~(inC12 0 (r - l) ((r - l)%:C * z)).
Proof.
move=> l r. case=> a b Hlr.
rewrite !inC12E. simpc. rewrite /=.
rewrite !ComplexField.exprM !(mulrA (r - l) _ a) !(mulrA (r - l) _ b)
   -expr2 -(mulrN _ a) -mulrA -(mulrN _ (b / Num.sqrt 3%:R))
    -!(mulrDr ((r - l)^+2)).
apply/idP/idP => H; rewrite negb_or -!lerNgt in H; 
   move/andP : H => H; rewrite negb_or; apply/andP;
   rewrite -!lerNgt; split.
      apply: mulr_ge0.
        by apply: sqr_ge0.
      exact: (proj1 H).
    apply: mulr_ge0.
      by apply: sqr_ge0.
    exact: (proj2 H).
  rewrite -(pmulr_rge0 (x := ((r - l)^+2))).
    exact: (proj1 H).
  rewrite ltr_def; apply/andP; split.
    by rewrite sqrf_eq0 subr_eq0 eq_sym.  
  by apply: sqr_ge0.
rewrite -(pmulr_rge0 (x := ((r - l)^+2))).
  exact: (proj2 H).
rewrite ltr_def; apply/andP; split.
  by rewrite sqrf_eq0 subr_eq0 eq_sym.  
by apply: sqr_ge0.
Qed.

Lemma notinC12lr_shift : forall (l r : R) (z : C), (l != r) ->
   ~~(inC12 0 (r - l) z) = ~~(inC12 l r (z + l%:C)).
Proof.
move=> l r. case=> a b Hlr.
rewrite !inC12E. simpc. rewrite /=.
apply/idP/idP => H; rewrite negb_or; apply/andP; split;
   rewrite negb_or in H; move/andP : H => H.
      rewrite expr2 mulrDl !mulrDr mulrDl mulrDl -expr2 !opprD
        [l * a + _]addrC !addrA addrK -(addrA _ (- (r * a)) _)
        (addrC (- (r * a)) _) !addrA addrK -(addrA _ (a * l) _)
        (addrC (a * l)) (mulrC a l) -{1}(opprK l) mulNr -opprD
        -mulrDl addrC !addrA (addrC (l * r)) -(addrA _ (l * r) _)
        (addrC (l * r)) (mulrC l r) !addrA addrK.
      exact: (proj1 H).
    rewrite expr2 mulrDl !mulrDr mulrDl mulrDl -expr2 !opprD
      [l * a + _]addrC !addrA addrK -(addrA _ (- (r * a)) _)
      (addrC (- (r * a)) _) !addrA addrK -(addrA _ (a * l) _)
      (addrC (a * l)) (mulrC a l) -{1}(opprK l) mulNr -opprD
      -mulrDl addrC !addrA (addrC (l * r)) -(addrA _ (l * r) _)
      (addrC (l * r)) (mulrC l r) !addrA addrK.
    exact: (proj2 H).
  rewrite expr2 mulrDl !mulrDr mulrDl mulrDl -expr2 !opprD
    [l * a + _]addrC !addrA addrK -(addrA _ (- (r * a)) _)
    (addrC (- (r * a)) _) !addrA addrK -(addrA _ (a * l) _)
    (addrC (a * l)) (mulrC a l) -{1}(opprK l) mulNr -opprD
    -mulrDl addrC !addrA (addrC (l * r)) -(addrA _ (l * r) _)
    (addrC (l * r)) (mulrC l r) !addrA addrK in H.
  exact: (proj1 H).
case: H => H1 H2.
rewrite expr2 mulrDl !mulrDr mulrDl mulrDl -expr2 !opprD
  [l * a + _]addrC !addrA addrK -(addrA _ (- (r * a)) _)
  (addrC (- (r * a)) _) !addrA addrK -(addrA _ (a * l) _)
  (addrC (a * l)) (mulrC a l) -{1}(opprK l) mulNr -opprD
  -mulrDl addrC !addrA (addrC (l * r)) -(addrA _ (l * r) _)
  (addrC (l * r)) (mulrC l r) !addrA addrK in H2.
exact: H2.
Qed.

Lemma inB_notinC12 : forall (l r : R) (z : C), (l != r) -> (z + 1 != 0) ->
   (inB z) = ~~(inC12 l r ((r%:C + l%:C * z) / (z + 1))).
Proof.
move=> l r z Hlr Hz.
have H : ((r%:C + l%:C * z) / (z + 1) = ((r - l)%:C / (z + 1) + l%:C)).
  rewrite -{2}[l%:C](@mulrK _ (z + 1)). 
    by rewrite -mulrDl {2}[z+1]addrC mulrDr mulr1 rmorphB /= !addrA addrNK.
  by rewrite unitfE.
by rewrite H -notinC12lr_shift // -notinC1201_lr_scale //
   -inB1_notinC1201 // -inB_inB1.
Qed.

Local Notation toC := (fun (p : {poly R}) =>
   @map_poly R _ (real_complex R) p).

Lemma changes_nseq : forall (s : seq R) (a : R), (a != 0) ->
   changes (seqmul (nseq (size s) a) s) = changes s.
elim => [ | c l IHl a Ha] //.
case : l IHl => [IH |b l IHbl ] //.
  by rewrite /= !mulr0 addn0.
have Helpme : ((changes [::c, b & l]) = ((c * b < 0)%R + changes [:: b & l])%N).
  by done.
rewrite Helpme. rewrite -(IHbl a) //.
have Helpme2 : (((a * c) * (a * b) < 0) == (c * b < 0)).
  rewrite (mulrC a b) -mulrA (mulrC a) -!mulrA -expr2 mulrA.
  rewrite pmulr_llt0 // ltr_def. apply/andP; split.
    by rewrite sqrf_eq0.
  by apply: sqr_ge0.
by move/eqP : Helpme2 => <-.
Qed.

Lemma seqn0_nseq : forall (s : seq R) (a : R), (a != 0) ->
   seqmul (nseq (size (seqn0 s)) a) (seqn0 s) = seqn0 (seqmul (nseq (size s) a) s).
Proof.
elim => [ | c l IHl a Ha] //.
case Hc : (c != 0).
  have Hac : (a * c != 0).
    by apply: mulf_neq0.
  by rewrite seqmul_cons /= Hac /= Hc /= seqmul_cons /= -IHl.
have Hac : ((a * c != 0) = false).
  apply: negbF; rewrite mulf_eq0; apply/orP; right.
  by apply: negbFE.
by rewrite seqmul_cons /= Hc /= Hac /= IHl.
Qed. 

Lemma inBneg1 : (@inB R (-1)).
Proof.
rewrite inBE.
apply/andP; split.
  rewrite raddfN. by apply: lerN10.
rewrite !raddfN /= oppr0 sqrrN !expr2 mulr0 !mulr1.
by apply: ler0n.
Qed.

(* ~~ root p r *)
Theorem three_circles_2 : forall  (l r : R) (p : {poly R})
   (a : R), (~~ root p r) -> (l < a < r) -> (~~ root p a) ->
   (forall z : C, root (toC p) z -> ~~ (inC12 l r z) ) ->
   (changes (seqn0 (Bernstein_coeffs (p * ('X - a%:P)) l r)) = 1%N).
Proof.
move=> l r p a Hpnorootr Hlar Hpnoroota H.
have Hlr : l != r.
  apply: negbT.
  apply: ltr_eqF.
  move/andP : Hlar => Hlar.
  apply: (@ltr_trans _ a).
    exact: (proj1 Hlar).
  exact: (proj2 Hlar).
have Hal : l != a.
  move/andP : Hlar => Hlar.
  apply: negbT.
  apply: ltr_eqF.
  exact: (proj1 Hlar).  
case Hp : (p == 0).
  move/eqP : Hp => Hp.
  have : false.
    rewrite  -(andbN (root p a)).
    apply/andP. split => //.
    rewrite Hp; by apply: root0.
  by done.
move/eqP/eqP : Hp => Hp.
have Hlc1 : (lead_coef (Bernstein_coeffs (R:=R) (p * ('X - a%:P)) l r))^-1 != 0.
  apply: invr_neq0.
  rewrite Bernstein_coeffsM lead_coefM.
  apply: mulf_neq0; rewrite lead_coef_eq0.
    by rewrite -Bernstein_coeffs_0.
  rewrite -Bernstein_coeffs_0 //.
  apply: negbT.
  by apply: polyXsubC_eq0.
have Hlc2 : (lead_coef (Bernstein_coeffs p l r) != 0).
  by rewrite lead_coef_eq0 -Bernstein_coeffs_0.
rewrite -(@changes_nseq _
   (lead_coef (Bernstein_coeffs (p * ('X - a%:P)) l r)) ^-1) //
    seqn0_nseq // -mul_polyC_seqmul //.
rewrite Bernstein_coeffsM lead_coefM -mul_polyC invrM.
    rewrite rmorphM /= mulrA mulrC !mulrA
       (mulrC (Bernstein_coeffs ('X - a%:P) _ _) _)
       mul_polyC -mulrA mul_polyC mulrC.
    rewrite [in X in (changes (R:=R) (seqn0 (polyseq (_ * X))))]
      (@Bernstein_coeffs_Xsubc_monic R a l r Hlr Hal).
    rewrite -(opprK ((r - a) / (l - a))%:P) -polyC_opp.
    apply: normal_changes.
        move/andP : Hlar => Hlar.
        rewrite oppr_gt0 pmulr_rlt0.
          rewrite invr_lt0 subr_lt0; exact: (proj1 Hlar).
        rewrite subr_gt0; exact: (proj2 Hlar).
      apply: normal_root_inB.
        rewrite monicE lead_coef_lreg.
          by rewrite mulrC -unitrE unitfE.
        apply/lregP. by apply: invr_neq0.
      move=> z Hz.
      case Hz2 : (z + 1 != 0).
        rewrite (inB_notinC12 Hlr) //.
        rewrite -mul_polyC rmorphM /= map_polyC mul_polyC rootZ in Hz.
          apply: H.
          by rewrite root_Bernstein_coeffs_C_2.
        rewrite /= eq_complex negb_and.
        apply/orP; left. by apply: invr_neq0.
      rewrite addr_eq0 in Hz2.
      move/eqP : Hz2 => ->.
      exact: inBneg1.
    rewrite rootZ. 
      rewrite -root_Bernstein_coeffs_2.
        by rewrite mulr0 addr0 add0r invr1 mulr1.
      rewrite add0r. by apply: oner_neq0.
    by apply: invr_neq0.
  by rewrite unitfE.
rewrite unitfE lead_coef_eq0 -Bernstein_coeffs_0 //.
apply: negbT. by apply polyXsubC_eq0.
Qed.


End thm_3_cercles_partie2.