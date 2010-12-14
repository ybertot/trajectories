Require Import ssreflect eqtype ssrbool ssrnat div fintype seq ssrfun.
Require Import bigop fingroup choice.
Require Export ssralg orderedalg infraz poly pol.

Import GroupScope .
Import GRing.Theory.
Import OrderedRing.Theory.
Open Local Scope ring_scope .


Set Printing Width 30.

(* We want to prove a simple and contructive approximation of the
 middle value theorem: if a polynomial is negative in a and positive in b,
 and a < b, then for any positive epsilon, there exists c and d, so that 
 a <= c < d <= b, the polynomial is negative in c and positive and d,
 and the variation between c and d is less than epsilon.  To prove this,
 we use a second polynomial, obtained by taking the the absolute value
 of each coefficient.
*)

Section MoreOrderedAlg.

Variable R : oIdomainType.

Lemma Sn_eq0rN : forall n : nat, (n.+1)%:R != (0 : R).
Proof.
by move=> n; have:=  (@gtf0Sn R n); rewrite ltr_neqAle eq_sym; case/andP.
Qed.

Lemma ge0n : forall n : nat, (0 : R) <= n%:R.
Proof. by case=> [| n]; rewrite ?lerr // ltrW ?gtf0Sn. Qed.

End MoreOrderedAlg.

Section CmvtOnAbstractRationals.

Variable Q : oFieldType.

Hypothesis Q_arch : forall x:Q, 0 <= x -> {n : nat | x <= n%:R}.

Lemma constructive_ivt :
  forall (p : {poly Q})(x y : Q), x < y -> p.[x] < 0%R -> 0%R <= p.[y]  ->
       forall epsilon, 0 < epsilon ->
       exists x', exists y',  - epsilon <= p.[x'] /\
         p.[x'] < 0 /\ 0 <= p.[y'] /\
         p.[y'] <= epsilon /\ x <= x' /\ x' < y' /\ y' <= y.
Proof.
move=> p a b ab nla plb.
have ba' : 0 < b - a by rewrite -(addrN a) lter_add2l.
have evalba : 0 < p.[b] - p.[a]. 
  rewrite -(lter_add2l p.[a]) add0r -addrA addNr addr0. 
  exact: lter_le_trans plb.
case: (pol_ucont _ p _ _ ab) => c pc.
have cpos : 0 < c.
  rewrite -(ltef_mulp _ _ _ ba') /= mul0r.
  apply: lter_le_trans (pc a b _ _ _)=> /=; rewrite ?lerr // ?(ltrW ab) //=.
  by rewrite ger0_abs // ltrW.
move=> eps pe.
have pdiv : (0 < (b - a) * c / eps).
  by rewrite ltef_divp // mul0r mulf_gte0 /= ba' cpos.
move: (pdiv); move/ltrW; case/Q_arch => n qn.
have fact1 : (0 : Q) < n%:R by exact: lter_le_trans qn => /=.
case: n qn fact1 => [|n]; rewrite ?ltrr // => qn _.
pose sl := map (fun x => a + (b - a) * (x%:R / (n.+1%:R))) (iota 0 n.+2).
pose a'_index := find (fun x => p.[x] >= 0) sl.
have has_sl : has (fun x => p.[x] >= 0) sl.
  rewrite has_map; apply/hasP; exists n.+1; first by rewrite mem_iota add0n ltnSn ltnW.
  rewrite /= divff; last by exact: Sn_eq0rN.
  by rewrite mulr1 addrCA subrr addr0.
case: {2}a'_index (refl_equal a'_index) => [|ia'].
- rewrite /a'_index => ha'; have:= (nth_find 1 has_sl); rewrite ha' /=.
by rewrite mul0r mulr0 addr0 -ltrNge nla.
- move=> ha'; exists (nth 0 sl ia'); exists (nth 0 sl ia'.+1).
  have ia's : (ia' < size sl)%N by rewrite -ha' /a'_index find_size.
  have ia'iota : (ia' < size (iota 0 n.+2))%N by move: ia's; rewrite size_map.
  have:= (nth_find 0 has_sl); rewrite -/a'_index ha' => pb'p.
  have:= (ltnSn ia'); rewrite -{2}ha'.
  move/(@before_find _ 0 (fun x : Q => 0 <= p.[x]) sl); move/negbT.
  rewrite lerNgt => pa'n.
  have aa' : a <= sl`_ia'.
    rewrite /sl (nth_map 0%N) // lter_addrr /= mulr_ge0pp ?(ltrW ba') //.
    by rewrite mulr_ge0pp ?invf_gte0 ?ge0n //= ge0n.
  have ia'_sharp : (ia' < n.+1)%N.
    move: ia'iota; rewrite leq_eqVlt; rewrite size_iota; case/orP=> //.
    move/eqP; case=> abs.
    move: pa'n; rewrite abs (nth_map 0%N) ?size_iota // nth_iota //.
    rewrite add0n divff ?mulr1 ?Sn_eq0rN // addrCA subrr addr0 => {abs} abs.
    by move: plb; rewrite ler_nlt abs.
  have b'b : sl`_ia'.+1 <= b.
    rewrite /sl (nth_map 0%N) ?size_iota ?ltnS // nth_iota //.
    rewrite add0n.
    have e : b = a + (b - a) by rewrite addrCA subrr addr0.
    rewrite {2}e {e} lter_add2r //= -{2}(mulr1 (b -a)) lter_mulpl //= ?(ltrW ba') //.
    rewrite ltef_divpl ?gtef0Sn //= mul1r -subr_gte0 /=.
    have -> : (n.+1 = ia'.+1 + (n.+1 - ia'.+1))%N by rewrite subnKC.
    by rewrite mulrn_addr addrAC subrr add0r subSS ge0n.
  have b'a'_sub : sl`_ia'.+1 -  sl`_ia' = (b - a) / (n.+1)%:R.
    have side : (ia' < n.+2)%N by apply: ltn_trans (ltnSn _).
    rewrite /sl (nth_map 0%N) ?size_iota // nth_iota // add0n.
    rewrite (nth_map 0%N) ?size_iota // nth_iota // add0n.
    rewrite oppr_add addrAC addrA subrr add0r addrC -mulr_subr.
    by congr (_ * _); rewrite -mulr_subl mulrSr addrAC subrr add0r div1r.
  have a'b' :  sl`_ia' < sl`_ia'.+1.
    move/eqP: b'a'_sub; rewrite subr_eq; move/eqP->; rewrite lter_addrl /=.
    by rewrite mulr_gte0pp //= ?invf_gte0 /= gtef0Sn.
  have : `|p.[sl`_ia'.+1] - p.[sl`_ia']| <= eps.
    have := (pc sl`_ia' sl`_ia'.+1 aa' (ltrW a'b') b'b).
    rewrite b'a'_sub => hpc; apply: lter_trans hpc _ => /=.
    rewrite mulrA ltef_divpl /= ?gtef0Sn // mulrC [eps * _]mulrC.
    by rewrite -ltef_divpl.
  rewrite absr_lte ?(ltrW pe) // -/ia' -/sl;
  set b':=  sl`_ia'.+1; set a' :=  sl`_ia'.
  rewrite /=; case/andP =>  h1 h2; split.
  - rewrite lter_opp2 /= opprK -(lter_add2r p.[b']) /=; apply: lter_trans h2 _.
    by rewrite /= lter_addrl.
  split => //; split => //; split => //.
  rewrite -(lter_add2l (- p.[a'])) /=; apply: lter_trans h2 _.
  by rewrite lter_addrr /= oppr_gte0 /= ltrW.
Qed.

End CmvtOnAbstractRationals.