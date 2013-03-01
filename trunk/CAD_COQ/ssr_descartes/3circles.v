Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype prime div.
Require Import ssralg poly polydiv polyorder ssrnum zmodp polyrcf qe_rcf_th complex
   poly_normal pol.

Set Implicit Arguments.
Unset Strict Implicit.

Import GRing.Theory Num.Theory Num.Def.
Import Pdiv.Idomain.

Section about_nonneg.

Variable R : rcfType.

Fixpoint nonneg (s : seq R) : bool :=
   if s is a ::tl then (0 <= a) && (nonneg tl) else true.

Lemma nonneg_is_nonneg_1 : forall (s : seq R),
   (nonneg s) -> (forall k, (k < size s)%N -> 0 <= s`_k).
Proof.
elim => [ |a l IHl Halnonneg] //.
move/andP : Halnonneg => Halnonneg.
case=> [_ |k Hk ] //=.
  exact: (proj1 Halnonneg).
by apply: (IHl (proj2 Halnonneg) k).
Qed.

Lemma nonneg_is_nonneg_2 : forall (s : seq R),
  (forall k, (k < size s)%N -> 0 <= s`_k) ->  (nonneg s).
Proof.
elim=> [ |a l IHl H] //=.
apply/andP; split.
  by apply: (H 0%N).
apply: IHl=> k Hk.
by apply: (H k.+1).
Qed.

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
move: {2}(size p) (leqnn (size p))=> n.
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

Lemma Bernstein_coeffsE : forall (G : ringType) (p : {poly G}) (a b : G),
   Bernstein_coeffs p a b = reciprocal_pol ((p \shift a) \scale (b - a)) \shift 1.
Proof. by []. Qed.

Section about_roots_and_transformations.

Variable (R : fieldType).

Lemma root_shift_1 : forall (p : {poly R}) (a x : R), (root p x) = root (p \shift a) (x-a).
Proof.
move=> p a x.
by rewrite !rootE -horner_shift_poly1.
Qed.

Lemma root_shift_2 : forall (p : {poly R}) (a x : R), root p (x + a) = root (p \shift a) x.
Proof.
move=> p a x.
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

Lemma root_Bernstein_coeffs_1 : forall (p : {poly R}) (x : R) (l r : R), (l != r) ->
   (x != l) -> (x != r) ->
   root p x = root (Bernstein_coeffs p l r) ((r - x) / (x - l)).
Proof.
move=> p x l r Hlr Hxl Hxr.
rewrite Bernstein_coeffsE.
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

Lemma root_Bernstein_coeffs_2 : forall (p : {poly R}) (x : R) (l r : R), (x + 1 != 0) ->
   root p ((r + l * x) / (x + 1)) = root (Bernstein_coeffs p l r) x.
Proof.
move=> p x l r Hx.
rewrite Bernstein_coeffsE.
rewrite -root_shift_2 -root_reciprocal_2 //. 
rewrite -root_scale_2 -root_shift_2 -{3}(@mulrK _ (x + 1) _ l).
  by rewrite -mulrDl {2}(@addrC _ x 1) mulrDr mulr1 addrA -(addrA r (- l) l)
       (addrC (-l) l) addrA addrK.
by rewrite unitfE.
Qed.

End about_roots_and_transformations.

Section transformations_in_C.
Variable (R : rcfType).
Local Notation C:= (complex R).

Local Notation toC := (fun (p : {poly R}) => @map_poly R _ (real_complex R) p).

Lemma shift_toC : forall (p : {poly R}) (a : R),
   toC (p \shift a) = (toC p) \shift a%:C.
Proof.
move=> p a.
by rewrite /shift_poly (map_comp_poly _ p ('X + a%:P)) rmorphD /= map_polyX map_polyC.
Qed.

Lemma scale_toC : forall (p : {poly R}) (a : R),
   toC (p \scale a) = (toC p) \scale a%:C.
Proof.
Admitted.

Lemma reciprocal_toC : forall (p : {poly R}),
   toC (reciprocal_pol p) = reciprocal_pol (toC p).
Proof.
Admitted.

Lemma Bernstein_toC : forall (p : {poly R}) (l r : R),
   toC (Bernstein_coeffs p l r) = Bernstein_coeffs (toC p) l%:C r%:C.
Proof.
Admitted.

Lemma root_Bernstein_coeffs_C_1 :  forall (p : {poly R}) (z : C) (l r : R), (l != r) ->
   (z != l%:C) -> (z != r%:C) ->
      root (toC p) z =
      root (toC (Bernstein_coeffs p l r)) ((r%:C - z) / (z - l%:C)).
Proof.
move=> p z l r Hlr Hzl Hzr.
rewrite !rootE Bernstein_toC Bernstein_coeffsE -!rootE.
rewrite -@root_shift_2 -(@mulrK _ (z - l%:C) _ 1). 
  rewrite mul1r -mulrDl addrA.
  rewrite -(@addrA _ _ (-z) z) (@addrC _ (-z) z) addrA addrK. 
  rewrite -root_reciprocal_2. 
    rewrite invrM.
        rewrite invrK.
        rewrite -root_scale_2 mulrC divrK.
          by rewrite -root_shift_2 -addrA (@addrC _ _ l%:C) addrA addrK.
        rewrite unitfE (*-rmorphB*). rewrite subr_eq0 eq_sym. admit.
      rewrite unitfE subr_eq0 eq_sym. admit.
    by rewrite unitfE invr_eq0 subr_eq0.
  apply: GRing.mulf_neq0.
    rewrite subr_eq0 eq_sym. admit.
  by rewrite invr_eq0 subr_eq0.
by rewrite unitfE subr_eq0.
Qed. (**********)

Lemma root_Bernstein_coeffs_C_2 : forall (p : {poly R}) (z : C) (l r : R),
   (z + 1 != 0) ->
      root (toC p) ((r%:C + l%:C * z) / (z + 1)) = 
      root (toC (Bernstein_coeffs p l r)) z.
Proof.
move=> p z l r Hz.
rewrite !rootE Bernstein_toC Bernstein_coeffsE -!rootE.
rewrite -root_shift_2 -root_reciprocal_2 //. 
rewrite -root_scale_2 -root_shift_2 -{3}(@mulrK _ (z + 1) _ l%:C).
  by rewrite -mulrDl {2}(@addrC _ z 1) mulrDr mulr1 addrA -(addrA r%:C (- l%:C) l%:C)
       (addrC (-l%:C) l%:C) addrA addrK.
by rewrite unitfE.
Qed.

End transformations_in_C.

Section le_thm_des_3_cercles.

Variables (R : rcfType) (l r : R).

Local Notation C := (complex R).

Definition notinC (z : C) :=
   0 <= (Re z) ^+2 - (l + r) * (Re z) + (Im z) ^+2 + r * l.

Lemma notinCE : forall (z : C),
   notinC z = (0 <= (Re z) ^+2 - (l + r) * (Re z) + (Im z) ^+2 + r * l).
Proof. by []. Qed.

Lemma notinC_Re_lt0_1 : forall (z : C),
   (notinC z) = (Re ((r%:C - z) / (z - l%:C)) <= 0).
Proof.
case => a b.
rewrite notinCE /=.
simpc.
rewrite !mulrA.
(*Unset Printing Notations.*)
Search _ (- _ * _).
rewrite -(mulNr (b * b) _).
(*rewrite -(mulrDl ((r - a) * (a - l)) (- (b * b)) ((a - l) ^+2 + b ^+2)^-1).*)
(*rewrite -(mulrDl _ (- (b * b)) _).*)
rewrite -mulrDl.
rewrite -expr2.
rewrite (mulrDl r (-a) _).
rewrite (mulrC r (a - l)) (mulrC (-a) _).
rewrite (mulrDl _ _ r).
rewrite (mulrDl _ _ (-a)).
Search _ (- _ * - _).
rewrite mulrNN.
Admitted.
(**********)

Lemma norinC_Re_lt0_2 : forall (z : C),
   (notinC ((r%:C + l%:C * z) / (z + 1))) = (Re z <= 0).
Proof.
move=> z. 
rewrite (notinC_Re_lt0_1 ((r%:C + l%:C * z) / (z + 1))) /=.
rewrite -{1}(@mulrK _ (z+1) _ r%:C).
rewrite -(mulNr (r%:C + l%:C * z) _ ).
rewrite -(mulrDl _ _ (z+1)^-1).
rewrite mulrDr mulr1.
Search _ "oppr".
rewrite opprD.
rewrite !addrA.
rewrite addrK.
rewrite -{3}(@mulrK _ (z+1) _ l%:C).
rewrite -(mulNr (l%:C * (z+1)) _ ).
rewrite -(mulrDl _ _ (z+1)^-1).
rewrite mulrDr mulr1.
rewrite opprD.
rewrite !addrA.
rewrite addrK.

rewrite mulf_div.


case: z => a b.
simpc.

(* Theorem 10.47 i. *)
Theorem three_circles_1 : forall (p : {poly R}), (forall (z : C),
   (root (map_poly (real_complex R) p) z -> (notinC z))) ->
      changes (Bernstein_coeffs p l r) = 0%N.



End le_thm_des_3_cercles.