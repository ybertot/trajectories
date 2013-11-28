Require Import ssreflect ssrfun ssrbool eqtype ssrnat binomial seq choice.
Require Import fintype bigop ssralg poly ssrnum ssrint rat.
Require Import pol polyrcf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory Num.Def.
Local Open Scope ring_scope.


(* A technical binomial identity for the proof of de Casteljau *)
Lemma util_C : forall n i j : nat, (i <= j)%nat -> (j <= n)%nat -> 
    ('C(n, i) * 'C(n-i, j-i) = 'C(j, i) * 'C(n, j))%nat.
Proof.
move => n i j ij jn.
apply/eqP; rewrite -(@eqn_pmul2r ( i`! * (n - i) `!));
  last by rewrite muln_gt0; apply/andP; split; apply: fact_gt0.
rewrite -(@eqn_pmul2r ((j - i)`! * ((n - i)-(j - i))`!)); last first.
  by rewrite muln_gt0; apply/andP; split; apply: fact_gt0.
have ilen : (i <= n)%nat by apply: leq_trans jn.
rewrite (mulnAC 'C(n, i)) -mulnA !bin_fact //; last by apply: leq_sub2r.
rewrite !mulnA (mulnAC _ _ (i`!)) 2!(mulnAC _ _ ((j-i)`!)) -(mulnA 'C(j, i)).
rewrite bin_fact // -subnDA subnKC // mulnAC (mulnC j`!) -(mulnA _ j`!).
by rewrite bin_fact.
Qed.

Section ToBeAddedInOrderedAlg.

Variable F : numFieldType.

Lemma gt1expn : forall n (x : F), 1 <= x -> 1 <= x^+n.
Proof.
elim=> [| m ihm] x hx; first by rewrite expr0 lerr.
rewrite exprS; apply: ler_trans (hx) _; rewrite -{1}(mulr1 x).
rewrite ler_pmul2l; first by exact:ihm.
by apply: ltr_le_trans hx; rewrite /= ltr01.
Qed.

Lemma ge0_sum : forall m (G : nat -> F), 
  (forall i, ((i < m)%N ->  0 <= G i)) -> 0 <= \sum_(i < m) G i.
Proof.
elim=> [|m ihm] G hp; first by rewrite big_ord0 lerr.
rewrite big_ord_recr /=; apply: addr_ge0; last by apply: hp.
apply: ihm=> i ltim; apply: hp; apply: ltn_trans ltim _; exact: ltnSn.
Qed.

Lemma ge_sum :  forall m (G1 G2 : nat -> F), 
  (forall i, ((i < m)%N ->  G1 i <= G2 i)) -> \sum_(i < m) G1 i <= \sum_(i < m) G2 i.
Proof.
elim=> [|m ihm] G1 G2 hp; first by rewrite !big_ord0 lerr.
rewrite ! big_ord_recr /=; apply: ler_add=> /=; last by apply: hp. 
by apply: ihm=> i ltim; apply: hp; apply: ltn_trans ltim _. 
Qed.

Lemma normr_sum : forall m  (G : nat -> F),
  `|\sum_(i < m) G i| <= \sum_(i < m) `|G i|.
Proof.
elim=> [|m ihm] G; first by rewrite !big_ord0 normr0.
rewrite !big_ord_recr /=; apply: ler_trans (ler_norm_add _ _) _=> /=.
by rewrite ler_add2r; apply: ihm.
Qed.

Lemma absrge1 : forall x : F, 1 < x -> x^-1 < 1.
Proof.
move=> x lt1x; rewrite -(mul1r (x^-1)). 
rewrite lter_pdivr_mulr ?mul1r //.
apply: ltr_trans lt1x; exact: ltr01.
Qed.

Lemma absf_inv : forall x : F, `|x ^-1| = `|x|^-1.
Proof.
move=> x; case e: (x == 0); first by rewrite (eqP e) normr0 invr0 normr0.
have axn0 : ~~ (`|x| == 0) by rewrite normr_eq0 e.
by apply: (mulfI axn0); rewrite mulfV // -normrM mulfV ?e ?normr1.
Qed.

Lemma expf_gt1 : forall m (x : F), x > 1 -> x^+m.+1 > 1.
Proof.
elim => [|m ihm] x hx; first by rewrite expr1.
apply: ltr_trans (hx) _ => /=; rewrite exprS -{1}(mulr1 x).
rewrite ltr_pmul2l; first exact: ihm.
apply: ltr_trans hx; exact: ltr01.
Qed.

Lemma expf_ge1 : forall m (x : F), x >= 1 -> x^+m >= 1.
Proof.
elim => [|m ihm] x hx; first by rewrite expr0 lerr.
apply: ler_trans (hx) _ => /=; rewrite exprS. (* -{1}(mulr1 x). *)
rewrite ler_pmulr; first exact: ihm.
apply: ltr_le_trans hx; exact: ltr01.
Qed.

End ToBeAddedInOrderedAlg.

Section ToBeAddedInPoly.

Variable R : idomainType.

(* A remark, lemma size_Xma should be with addition *)
Lemma size_factor_expr : forall (t : R)(n : nat), 
  size (('X + t%:P)^+n) = n.+1.
Proof.
move=> t; elim=> [|n ihn]; first by rewrite expr0 size_polyC oner_eq0.
rewrite exprS size_monicM //; last first.
    by rewrite -size_poly_eq0 ihn; apply/negP; move/eqP.
  by rewrite  -(opprK t%:P) -polyC_opp monicXsubC.
by rewrite ihn -(opprK t%:P) -polyC_opp size_XsubC.
Qed.

Lemma size_amul_expr : forall (t c : R)(i : nat), 
  c != 0 -> size (('X * c%:P + t%:P) ^+ i) = i.+1.
Proof.
move=> t c; elim=> [| i ih] cn0; first by rewrite expr0 size_poly1.
have hn0 : size ('X * c%:P + t%:P) = 2.
  rewrite mulrC size_MXaddC polyC_eq0.
  move: cn0; rewrite -eqbF_neg=> /eqP => cn0.
  by rewrite size_polyC cn0 andFb.
by rewrite exprS size_mul // ?expf_eq0 -?size_poly_eq0 hn0 ?andbF // ih.
Qed.

Lemma size_factor : forall x : R, size ('X + x%:P) = 2.
Proof.
 by move=> x; rewrite size_addl ?size_polyX // size_polyC /=; case: (x == 0).
Qed.

Lemma size_polyX_mul : forall p : {poly R}, 
  size ('X * p) = if p == 0 then 0%nat else (size p).+1.
Proof.
move=> p; rewrite (_ : 'X * p = p * 'X + 0%:P); last by rewrite mulrC addr0.
  by rewrite size_MXaddC eqxx andbT.
Qed.

Lemma coef_poly0 : forall p q : {poly R}, (p * q)`_0 = p`_0 * q`_0.
Proof. 
by move=> p q; rewrite coef_mul_poly big_ord_recl big_ord0 sub0n addr0. Qed.

End ToBeAddedInPoly.
(* We prove the Chauchy bound in any ordered field *)

Section CauchyBound.

Variable F : realFieldType.

Variables (n : nat)(E : nat -> F).

Hypothesis pnz : E n != 0.

Lemma CauchyBound x: (\poly_(i < n.+1) E i).[x] = 0 -> 
  `| x | <= `|E n|^-1 * \sum_(i < n.+1) `|E i|.
Proof.
move=> px0; case: (lerP `|x| 1)=> cx1.
  set C := _ * _; suff leC1 : 1 <= C by apply: ler_trans leC1.
  have h1 : `|E n| > 0 by rewrite  normr_gt0.
  rewrite -(ler_pmul2l h1) /= mulr1 /C mulrA mulfV ?normr_eq0 // mul1r.
  rewrite big_ord_recr /= -{1}(add0r `|E n|) ler_add2r.
  (* here should be a lemme in orderedalg *)
  elim: n=> [|m ihm]; first by rewrite big_ord0 lerr.
  rewrite big_ord_recr /=; apply: addr_ge0=> //; exact: normr_ge0.
case e: n=> [| m].
  move: pnz; rewrite -px0 e horner_poly big_ord_recl big_ord0 /=.
  by rewrite addr0 expr0 mulr1 /= eqxx.
have h1 : E  m.+1 * x^+m.+1 = - \sum_(i < m.+1) E i * x^+ i.
  apply/eqP; rewrite -subr_eq0 opprK -{2}px0 horner_poly (big_ord_recr n).
  by rewrite e //= addrC.
case x0 : (x == 0).
  rewrite (eqP x0) normr0; apply:  mulr_ge0.
    by rewrite invr_gte0 /= normr_ge0.
  suff h2: forall i, (i < m.+2)%N -> 0 <= `|E i| by apply: (ge0_sum h2).
  move=> i _; exact: normr_ge0.
have {h1} h2 : E m.+1 * x =  - \sum_(i < m.+1) E i * x^-(m - i).
have xmn0 : ~~(x^+m == 0) by rewrite expf_eq0 x0 andbF.
  apply: (mulIf xmn0); rewrite mulNr big_distrl /= -mulrA -exprS h1.
  congr (- _); apply: congr_big; [by [] | by [] |] => [[i hi]] _ /=.
  have mi : m = (m - i + i)%N by rewrite subnK.
  rewrite {2}mi exprD -!mulrA; congr (_ * _); rewrite mulrA mulVf ?mul1r //.
  by rewrite expf_eq0 x0 andbF.
have h3 : `|\sum_(i < m.+1) E i / x ^+ (m - i) | <= \sum_(i < m.+2) `|E i|.
  apply: ler_trans (normr_sum m.+1 (fun i =>  E i / x ^+ (m - i))) _.
  apply: (@ler_trans _ (\sum_(i < m.+1) `|E i|)); last first.
    by rewrite (big_ord_recr m.+1) /= ler_addl /= normr_ge0.
  suff h: forall i, (i < m.+1)%N -> `|E i/x^+(m-i)| <= `|E i|.
    by apply: (ge_sum h).
  move=> i lti; rewrite normrM -{2}(mulr1 (`|E i|)) ler_wpmul2l ?normr_ge0 //.
  rewrite normfV normrX invf_le1; first by rewrite exprn_cp1 // ltrW.
  by rewrite exprn_gt0 // (ltr_trans ltr01).
rewrite lter_pdivl_mull; last by rewrite normr_gt0 -e.
by apply: ler_trans h3=> /=; rewrite -normrM h2 normrN lerr.
Qed.
 
End CauchyBound.
  
(*
Section TranslateProps.

(* First linearity lemma : translate complies with scalar product for *)
(* elements of the basis *)

(*
(* Second linearity lemma : translate complies with addition *)
Lemma translate_add : forall l1 l2 c,
  size l1 = size l2 -> 
  shift_poly (map (fun x : Qcb * Qcb => x.1 + x.2) (zip l1 l2)) c = 
    map (fun x => x.1 + x.2) (zip (shift_poly l1 c) (shift_poly l2 c)).
Proof.
move=> l1 l2 c e; apply: (@eq_from_nth _ 0); rewrite size_shift_poly !size_map.
  by rewrite !size1_zip ?size_shift_poly // e.
move=> i; rewrite size1_zip ?e // => his; rewrite translate_nth; last first.
  by rewrite size_map size2_zip // e.
rewrite size_map size1_zip ?e //= (nth_map (0, 0)); last first.
  by rewrite size2_zip ?size_shift_poly // e /=.
rewrite nth_zip ?size_shift_poly // !translate_nth // ?e //=.
rewrite -big_split /=; apply: congr_big=> // [[k hk]] _ /=.
rewrite (nth_map (0, 0)) ?size2_zip // ?e // nth_zip //= mulr_addl.
by rewrite mulrn_addl.
Qed.

Lemma translate_mulX : forall (q1 q2 : {poly Qcb}) c, 
  q2 != 0 -> q1 != 0 ->
  shift_poly q2 c = q1 -> shift_poly ('X * q2) c = ('X + c%:P) * q1.
Proof.
  move=> q1 q2 c q2n0 q1n0 e.
  have sp1 : size (shift_poly ('X * q2) c) = (size q2).+1.
    by rewrite size_shift_poly size_mul_id // -?size_poly_eq0 ?size_polyX.
  have sp2 : size ('X * q2) = (size q2).+1.
    by rewrite mulrC size_mul_monic ?monicX // size_polyX !addnS addn0.  
  apply: (@eq_from_nth _ 0).
    by rewrite sp1 size_mul_id // -?size_poly_eq0 ?size_factor // -e size_shift_poly.
  rewrite sp1 => [[_|j hj]].
    rewrite translate_nth ?size_polyX_mul ?(negPf q2n0) //.
    rewrite coef_poly0 coef_add coefC eqxx coefX add0r -e /shift_poly.    
    rewrite !nth_mkseq ?lt0n ?size_poly_eq0 // -?size_poly_eq0 ?sp2 //.
    rewrite big_distrr big_ord_recl coef_Xmul eqxx mul0r mul0rn add0r.
    apply: congr_big=> // [[k hk]] _.
    rewrite  !bin0 !subn0 !mulr1n -[('X * q2)`__]/(('X * q2)`_k.+1).
    rewrite [GRing.muloid _ _]/= [c * _]mulrC.
    rewrite -mulrA [_ * c]mulrC -exprS; congr (_ * _).
    (* we  should really put a nosimpl on `_ *)
    by rewrite coef_Xmul /=.
  rewrite /shift_poly nth_mkseq ?sp2 //.
  rewrite coef_mul; apply: sym_eq; rewrite 2!big_ord_recl big1; last first.
    case=> k hk _; rewrite -[('X + c%:P)`_ _]/(('X + c%:P)`_ k.+2).
    by rewrite coef_add coefC coefX /= addr0 mul0r.
  rewrite [nat_of_ord _]/= !subn0 addr0 -[nat_of_ord _]/1%N.
  rewrite !coef_add !coefX !coefC !eqxx -![_ == _]/false add0r addr0 mul1r.
  rewrite -e /shift_poly.
  rewrite big_ord_recl coef_Xmul eqxx mul0r mul0rn add0r subSS subn0.
  move: hj; rewrite ltnS leq_eqVlt; case/orP.
    move/eqP=> ej; rewrite ej nth_default ?size_mkseq ?leqnn // mulr0 add0r.
    rewrite nth_mkseq -?ej //; apply: congr_big => // [[k hk]] _.
    rewrite -[('X * q2)`_ _]/(('X * q2)`_k.+1) subSS coef_Xmul -[_ == 0%N]/false /=.
    move: hk; rewrite ltnS leq_eqVlt; case/orP; first by move/eqP->; rewrite !binn.
    move=> hkj; rewrite !bin_small //.
  move=> hjs. rewrite !nth_mkseq //; last by apply: ltn_trans hjs.
  rewrite big_distrr -big_split; apply: congr_big=> // [[k hk]] _.
  rewrite  -[('X * q2)`_ _]/(('X * q2)`_k.+1) coef_Xmul /= subSS.
  rewrite -mulrnAl mulrC -mulrA [_ * c]mulrC -exprS {hjs hk}.
  case: (ltngtP k j) => ekj.
  - by rewrite !bin_small //; apply: ltn_trans ekj _.
  - by rewrite -ltn_subS // mulrnAl -mulrn_addr -binS.
  - rewrite ekj !binn subnn bin_small // (_ : j - j.+1 = 0)%N; last first.
       by apply/eqP; rewrite subn_eq0.
    by rewrite !mulr0n mul0r add0r expr0.
Qed.

Lemma shift_polyXn : forall (c : Qcb) i, 
  (shift_poly 'X^i c) = ('X + c%:P)^+i.
Proof.
move=> c i; rewrite -(mulr1 'X^i); elim: i => [| i ihi].
  rewrite !expr0 mulr1 /shift_poly size_polyC oner_eq0 /=.
  rewrite /mkseq /= big_ord_recl big_ord0 subn0 bin0 addr0 expr0 mulr1 mulr1n.
  by rewrite -polyC1 coefC eqxx polyseqC oner_eq0.
rewrite exprS -mulrA.
rewrite (translate_mulX _ _ _ _ _ ihi) ?exprS // ?mulr1 -size_poly_eq0.
  by rewrite size_polyXn.
by rewrite size_factor_expr.
Qed.


Lemma translate_mulXn : forall n (q1 q2 : {poly Qcb}) c, q2 != 0 -> q1 != 0 ->
   q2 \shift c = q1 -> 
   ('X^n * q2) \shift c = ('X + c%:P)^+n * q1.
Proof.
elim=> [|n ihn] q1 q2 c nq20 nq10 e; first by rewrite expr0 !mul1r.
rewrite exprS -mulrA.
have h : shift_poly ('X^n * q2) c = ('X + c%:P) ^+ n * q1.
  by rewrite (ihn q1 q2).
rewrite (translate_mulX _ _ _ _ _ h); first by rewrite mulrA -exprS.
  rewrite -size_poly_eq0 mulrC size_mul_monic ?monicXn // size_polyXn !addnS /=.
  by rewrite addn_eq0 negb_and size_poly_eq0 nq20.
rewrite -size_poly_eq0 size_mul_id // -?size_poly_eq0 ?size_polyXn size_factor_expr //=.
by rewrite addn_eq0 negb_and size_poly_eq0 nq10 orbT.
Qed.

(* to be cleaned: a simple induction is probably enough *)
Lemma translate_padded_l : forall (i : nat) (q : seq Qcb)(c : Qcb) , 
  shift_poly (q ++ (nseq i 0)) c = (shift_poly q c) ++ (nseq i 0).
Proof.
move=> n; elim: n {-2}n (leqnn n) => [| i hi] n hn q c.
 by move: hn; rewrite leqn0; move/eqP->; rewrite !cats0.
move: hn; rewrite leq_eqVlt; case/orP; last by move=> hn; rewrite hi //.
move/eqP->; rewrite -[q ++ _]/(q ++ nseq 1 0 ++ nseq i 0) catA hi //.
rewrite /shift_poly size_cat size_nseq addnS addn0.
rewrite -[nseq i.+1 0]/([:: 0] ++ nseq i 0) catA; congr (_ ++ _).
apply: (@eq_from_nth _ 0).
  by rewrite size_cat /= !size_mkseq size_map size_iota addn1.
rewrite size_mkseq => j; rewrite ltnS leq_eqVlt; case/orP=> hj.
  rewrite (eqP hj) nth_mkseq // nth_cat size_mkseq ltnn subnn /= big1 //.
  case=> k /=; rewrite ltnS leq_eqVlt; case/orP=> hk _.
    rewrite (eqP hk) nth_cat ltnn subnn /= mul0r mul0rn //.
  by rewrite nth_cat hk bin_small // mulrn0.
rewrite nth_cat size_mkseq hj !nth_mkseq //; last by apply: ltn_trans hj _.
rewrite big_ord_recr /= nth_cat ltnn subnn mul0r mul0rn addr0.
by apply: congr_big; [by [] | by [] |] => [[k hk]] _ /=; rewrite nth_cat hk.
Qed.




Lemma translateXn_addr : forall c1 c2 n, 
  shift_poly (shift_poly 'X^n c1) c2 = shift_poly 'X^n (c1 + c2).
Proof.
move=> c1 c2 n.
apply:  (@eq_from_nth _ 0); rewrite ?size_shift_poly //.
rewrite size_polyXn => i hi. 
rewrite /shift_poly nth_mkseq ?size_mkseq ?size_polyXn // nth_mkseq //.
apply: trans_equal (_ : 
  \sum_(k < n.+1) (\sum_(k0 < n.+1)'X^n`_k0 * c1 ^+ (k0 - k) *+ 
    'C(k0, k) * c2 ^+ (k - i) *+ 'C(k, i)) = _).
  apply: congr_big => // [[k hk]] _ /=; rewrite nth_mkseq //.
  by rewrite big_distrl /= -sumr_muln.
rewrite exchange_big /=.
apply: trans_equal (_ : 
\sum_(j < n.+1) 
\sum_(i0 < n.+1) 'X^n`_j * (c1 ^+ (j - i0) *+ 'C(j, i0) * c2 ^+ (i0 - i) *+ 'C(i0, i)) = _).
  apply: congr_big=> // [[k hk]] _ /=; apply: congr_big=> // [[j hj]] _ /=.
  by rewrite !mulrnAr !mulrA mulrnAr.
apply: congr_big=> // [[k hk]] _ /=; rewrite -big_distrr /=.
rewrite -mulrnAr; congr (_ * _).
rewrite -(subnKC hk) big_split_ord /= addrC big1; last first.
  case=> j hj _ /=; rewrite bin_small; last by apply: ltn_addr.
  by rewrite mulr0n mul0r mul0rn.
rewrite add0r; case: (ltngtP k.+1 i) => hki.
  -rewrite bin_small //; last by apply: ltn_trans hki.
  rewrite mulr0n big1 // => [[j hj]] _ /=; rewrite (@bin_small j); last first.
    by apply: ltn_trans hj _.
  by rewrite mulr0n.
  - rewrite ltnS in hki. rewrite -{-  7 11 12}(subnKC hki) -addnS big_split_ord /= big1; last first.
      by case=> j hj _ /=; rewrite (@bin_small j).
    rewrite add0r exprn_addl -sumr_muln; apply: congr_big => // [[j hj]] _ /=.
  rewrite subnKC // -subnDA [(i + _)%N]addnC -addn_subA // subnn addn0.
  rewrite mulrnAl -!mulrnA;  congr (_ *+ _).
  rewrite [(_ * 'C(k, i))%N]mulnC {3}(_ : j = j + i - i)%N; last first.
    by rewrite -addn_subA // subnn addn0.
  by rewrite util_C 1?mulnC // ?leq_addl // -(subnK hki) leq_add2r.
  - rewrite -hki bin_small // mulr0n big1 // => [[j hj]] /= _.
    by rewrite (@bin_small j).
Qed.
*)
End TranslateProps.
*)

(*
Section ReciprocateProps.

Lemma reciprocate_padded :  forall (i : nat) (q : seq Qcb),
  reciprocate_pol (q ++ (nseq i 0)) = (nseq i 0) ++ (reciprocate_pol q).
Proof.
move=> i q; rewrite /reciprocate_pol rev_cat; congr (_ ++_).
apply: (@eq_from_nth _ 0); rewrite size_rev size_nseq // => j hij.
rewrite nth_rev ?size_nseq // !nth_ncons.
by case: i hij=> // i hij; rewrite ltnS subSS leq_subr hij.
Qed.

End ReciprocateProps.

*)

(*
Section ExpandProps.

Lemma expand_padded :  forall (i : nat) (q : seq Qcb)(c : Qcb) , 
  expand (q ++ (nseq i 0)) c = (expand q c) ++ (nseq i 0).
Proof.
elim=> [| i ih] q c; first  by rewrite !cats0.
rewrite -[q ++ _]/(q ++ [:: 0] ++ nseq i 0) catA ih.
suff {ih} -> :  expand (q ++ cons 0 [::]) c = expand q c ++ [:: 0] by rewrite -catA.
apply: (@eq_from_nth _ 0); first by rewrite size_cat /expand !size_mkseq  !size_cat.
rewrite /expand size_mkseq size_cat addnS addn0=> {i} i.
rewrite ltnS leq_eqVlt; case/orP.
  move/eqP->; rewrite nth_cat nth_mkseq // size_mkseq ltnn subnn nth_cat ltnn.
  by rewrite subnn /= mul0r.
move=> ltis; rewrite nth_mkseq; last by apply: ltn_trans ltis _.
by rewrite !nth_cat size_mkseq ltis nth_mkseq.
Qed.


End ExpandProps.

*)

(* b gives the coefficients of a polynomial on some bounded interval [a, b].
de_casteljau computest all the coefficients in the triangle for a, m, n, with
l := m - a and r := b - m.

invariant : l + r = b - a *)

Section DeCasteljauAlgo.

Variable R : archiFieldType.

Variables l r : R.

Fixpoint de_casteljau (b : nat -> R) (n : nat) :=
  match n with
    O => b
  | i.+1 => fun j => 
    (l * de_casteljau b i j + r * de_casteljau b i j.+1)%R
  end.

(* b gives the B. coefficients of a polynomial on some bounded interval [a, b].
computes the B. coefficients on [a, a + l] si b - a = l + r *)
Definition dicho' b i := de_casteljau b i 0.

(* b gives the B. coefficients of a polynomial P on some bounded interval [a, b].
computes the B. coefficients on [b-r, b] si b - a = l + r , as soon as p = deg P *)
Definition dicho p b i := de_casteljau b (p - i) i.


(* the computation of the value at index (k, n) only uses values (i, j) 
   for n <=  i <= n + k (a triangle, up and right *)



Lemma ext_dc :
  forall k b b' n, (forall i, (n <= i)%nat -> (i <= n + k)%nat -> b i = b' i) ->
  de_casteljau b k n = de_casteljau b' k n.
move => k b b'; elim: k => [ n q | k IHk n q] /=.
  by apply: q; rewrite ?addn0 leqnn.
rewrite !IHk //; move => i ni nik; apply: q => //; first exact: ltnW.
  by move: nik; rewrite addnS addSn.
by apply: leq_trans nik _; rewrite addnS leqnSn.
Qed.

(* de_casteljau is linear with respect to coefficients *)
Lemma lin_dc :
  forall k a a' b b' n,
    de_casteljau (fun j => (a * b j + a' * b' j)%R) k n =

    (a * de_casteljau b k n + a' * de_casteljau b' k n)%R.
move => k; elim: k => [ | k IHk] a a' b b' n /= ; first by [].
rewrite 2!IHk !mulrDr !mulrA !(mulrC r) !(mulrC l) !addrA.
by rewrite (addrAC _ _ (a' * l * _)%R).
Qed.

(* in particular it is additive *)
Lemma add_dc :
  forall k b b' n, de_casteljau (fun j => b j + b' j)%R k n =
     (de_casteljau b k n + de_casteljau b' k n)%R.
move => k b b' n; have := lin_dc k 1 1 b b' n.
rewrite (@ext_dc k (fun j => 1 * b j + 1 * b' j) (fun j => b j + b' j))%R.
  by rewrite !mul1r.
by move => x; rewrite /= !mul1r.
Qed.

(* in particular it is homothetic *)
Lemma scal_dc :
  forall k a b n, de_casteljau (fun j => a * b j)%R k n =
      (a * de_casteljau b k n)%R.
move => k a b n; have := lin_dc k a 0 b (fun i => 0)%R n.
rewrite (@ext_dc _ (fun j => a * b j + 0 * 0)%R (fun j => a * b j)%R).
by rewrite mul0r addr0.
by move => x; rewrite /= mul0r addr0.
Qed.


End DeCasteljauAlgo.

Section DeltaSeqs.

Variable R : archiFieldType.

Definition delta (i j : nat) : R := if (i == j) then 1 else 0.

Lemma dc_delta_head : forall j k l r, 
  (j < k)%nat -> dicho' l r (delta k) j = 0.
Proof.
rewrite /dicho' => j k l r hlt.
pose d0 := fun _ : nat => 0 : R.
rewrite (@ext_dc _ _ _ _ _ d0); last first.
  move=> i; rewrite add0n /delta => h1 h2.
  have : (i < k)%nat by apply: leq_ltn_trans hlt.
  by rewrite ltn_neqAle; case/andP; rewrite eq_sym; move/negPf->.
elim:  j {hlt} 0%nat=> [| j ihj n] /=; first by done.
by rewrite !ihj !mulr0 addr0.
Qed.

(*Lemma translation_delta:*)
Lemma dc_deltaS:
 forall k A B i j,
  de_casteljau A B (delta i.+1) k j.+1 = de_casteljau A B (delta i) k j.
elim=> [|k ihk] A B i j /=; last by rewrite !ihk.
case e : (i == j); first by rewrite /delta (eqP e) !eqxx.
by rewrite /delta eqSS e.
Qed.

(* algorithme applique a delta_i (colonne j > i)*)
 (*Lemma coef_algo_delta_col_supi:*)
Lemma dc_delta_lt : 
  forall k A B i j, (j > i)%nat ->  de_casteljau A B (delta i) k j = 0.
elim=> [|k ihk] A B i j hlt /=.
  by move: hlt; rewrite ltn_neqAle; case/andP; move/negPf; rewrite /delta; move->.
rewrite !ihk // ?mulr0 ?addr0 //; apply: ltn_trans hlt _; exact: ltnSn.
Qed.

(* algorithme applique a delta_i (ligne n ,colonne  i)*)
 
(*Lemma coef_algo_delta_col_i:*)
Lemma dcn_deltan : forall n i A B,  de_casteljau A B (delta i%nat)  n i = A ^+ n.
elim=> [|n ihn] i A B /=; first by rewrite /delta eqxx expr0.
by rewrite !ihn dc_delta_lt ?ltnSn // mulr0 exprS addr0.
Qed.

(* algorithme applique a delta_i (colonne k avec k < i - j, ligne j avec j < i)*)
(*Lemma coef_algo_delta_ligne_infi_k:*)
Lemma dc_delta_gt :
 forall j i A B,
 (j < i)%nat ->
 forall k, (k < i - j)%nat ->  de_casteljau A B (delta i) j k = 0.
elim=> [| j ihj] i A B hltji k hltkd /=.
  by move: hltkd; rewrite subn0 ltn_neqAle /delta eq_sym; case/andP; move/negPf->.
have ltij : (j < i)%nat by apply: ltn_trans hltji; rewrite ltnSn.
rewrite !ihj // ?mulr0 ?addr0 //; first by rewrite -subnSK.
by apply: ltn_trans hltkd _; rewrite -[(i - j)%nat]subnSK.
Qed.

(* pourquoi on a un add_rec qui nous saute à la figure??? *)


Lemma dc_delta_tail :
 forall i k A B,
  de_casteljau A B (delta i) (i + k)%nat 0 = A ^+ k * B ^+ i *+'C(k + i, i).
Proof.
elim=> [|i ihi] k A B /=; rewrite -?addnE.
  by rewrite add0n addn0 /= expr0 mulr1  bin0 dcn_deltan mulr1n.
rewrite dc_deltaS ihi.
elim: k => [|k ihk] /=.
  rewrite !add0n !expr0 !addn0 !mul1r dc_delta_gt ?mulr0 ?add0r 1?mulrC ?subSnn //.
  by rewrite !binn !mulr1n exprS mulrC.
rewrite !addnS /= dc_deltaS ihi ihk !addnS !addSn !mulrnAr mulrA -exprS.
rewrite [_ * B^+ i]mulrC mulrA -exprS [B^+_ * _]mulrC -mulrnDr.
by congr (_ *+ _).
Qed.
 
(* Lemma algo_reverse:*)
Lemma dc_reverse :
 forall b (A B : R) p i k,
 (i <= p)%N ->
 (k <= p - i)%N ->
  de_casteljau B A (fun t => b (p - t)%N) i k = de_casteljau A B b i (p - (i + k)).
Proof.
move=> b A B p; elim=> [| i ihi] k hip hk /=; first by rewrite add0n.
rewrite addrC; congr (_  + _).
  by rewrite ihi ?(ltnW hip) ?addnS ?addSn // -[(p - i)%N]subnSK.
rewrite ihi ?(leq_trans hk) // ?leq_sub2l // ?(ltnW hip) //=.
rewrite addSn -subnSK //. 
by move:hk; rewrite -ltn_subRL -ltnS subnSK.
Qed.

End DeltaSeqs.

Section BernsteinPols.

Variable R : archiFieldType.
Variables (a b : R).
Variable deg : nat.

Hypothesis neqab : a != b.

(* elements of the Bernstein basis of degree p *)
Definition bernp i : {poly R} := 
  ((b - a)^-deg)%:P * ('X - a%:P)^+i * (b%:P - 'X)^+(deg - i) *+ 'C(deg, i).

Definition relocate (q : {poly R}) : {poly R}:=
  let s := size q in
    (* 1st case : degree of q is too large for the current basis choice *)
  if (deg.+1 < s)%N then 0
    else
      (recip deg ((q \shift (- 1)) \scale (b - a))) \shift - a.

Lemma recipE (q : {poly R}) : (size q <= deg.+1)%N ->
  recip deg q = \poly_(i < deg.+1) q`_(deg - i).
move=> sq.
have t : forall n m (E : nat -> R), 'X ^+ n * \poly_(i < m) E i =
          \poly_(i < m + n) (E (i - n)%N *+ (n <= i)%N).
  elim=> [ | n IH] m E.
    rewrite expr0 mul1r addn0; rewrite !poly_def; apply: eq_bigr => i _.
    by rewrite subn0 leq0n mulr1n.
  rewrite exprS -mulrA IH !poly_def.
  rewrite addnS big_ord_recl.
  rewrite [X in _ *+ (n < X)]/nat_of_ord /= mulr0n scale0r add0r big_distrr.
  apply: eq_bigr; move=> [i ci] _ /=; rewrite /bump leq0n add1n ltnS subSS.
  by rewrite mulrC -scalerAl exprS mulrC.
rewrite /recip t subnKC // !poly_def; apply: eq_bigr.
move=> [i ci] _ /=; congr (_ *: _).
case h : (deg.+1 - size q <= i)%N.
  rewrite mulr1n; congr (q`_ _); apply/eqP.
  rewrite -(eqn_add2r (i - (deg.+1 - size q)).+1) subnK; last first.
    by rewrite -(ltn_add2r (deg.+1 - size q)) subnK // addnC subnK.
  rewrite -subSn // addnBA; last by apply/(leq_trans h)/leqnSn.
  by rewrite addnS subnK // subKn.
move/negP: h;move/negP; rewrite -ltnNge => h.
rewrite mulr0n nth_default //.
rewrite -(leq_add2r i.+1) -subSS subnK //. 
by rewrite addnC -(subnK sq) leq_add2r.
Qed.

Lemma size_recip (q : {poly R}):
   (size q <= deg.+1 -> size (recip deg q) <= deg.+1)%N.
Proof. by move=> s; rewrite recipE // size_poly. Qed.

(* TODO : to be added in poly.v *)
Lemma poly_ext (n : nat) (E1 E2 : nat -> R) :
  (forall i : nat, (i < n)%N -> E1 i = E2 i) ->
  \poly_(i < n) E1 i = \poly_(i < n) E2 i.
Proof.
by move=> e; rewrite !poly_def; apply: eq_bigr; move=> [] i c _ /=; rewrite e.
Qed.

Lemma poly_extend (m n : nat) (E : nat -> R) :
  (m <= n)%N -> (forall i : nat, (m <= i < n)%N -> E i = 0) ->
  \poly_(i < m) E i = \poly_(i < n) E i.
Proof.
move=> c e; rewrite !poly_def. 
rewrite (big_ord_widen n (fun i => E i *: 'X^i) c) big_mkcond /=.
apply: eq_bigr; move=> [i ci] _ /=; case h: (i < m)%N => //.
rewrite e; first by rewrite scale0r.
by rewrite ci andbT leqNgt h.
Qed.

Lemma recipK (q : {poly R}) : (size q <= deg.+1)%N ->
   recip deg (recip deg q) = q.
Proof.
move=> s; rewrite recipE; last by rewrite size_recip.
rewrite -{2}[q]coefK (poly_extend s).
  apply: poly_ext => i c; rewrite recipE // coef_poly.
  rewrite subKn; last by rewrite -ltnS.
  by rewrite (leq_ltn_trans _ (ltnSn deg)) // leq_subr.
by move=> i c; rewrite nth_default //; case/andP: c.
Qed.

Lemma recipD : forall q1 q2 : {poly R}, (size q1 <= deg.+1)%N ->
   (size q2 <= deg.+1)%N -> recip deg (q1 + q2) = recip deg q1 + recip deg q2.
Proof.
move=> q1 q2 s1 s2; rewrite !recipE // ?poly_def; last first.
  by rewrite (leq_trans (size_add _ _)) // geq_max s1 s2.
have t : forall i : 'I_deg.+1, true -> (q1 + q2)`_(deg.+1 - i.+1) *: 'X^i =
                 q1`_(deg.+1 - i.+1) *: 'X^i + q2`_(deg.+1 - i.+1) *: 'X^i.
  by move=> [i ci] _ /=; rewrite coef_add_poly scalerDl.
by rewrite (eq_bigr _ t) big_split.
Qed.

Lemma recipZ (q : {poly R}) c :
  (size q <= deg.+1)%N -> recip deg (c *: q) = c *: recip deg q.
Proof.
move=> s; rewrite !recipE // ?poly_def; last first.
  case h : (c == 0); first by rewrite (eqP h) scale0r size_poly0.
  by rewrite size_scale ?h.
rewrite -[_ *: (\sum_(_ < _) _)]mul_polyC big_distrr; apply:eq_bigr.
by move=> [i ci] _ /=; rewrite coefZ mul_polyC scalerA.
Qed.

Lemma recipP (q : {poly R}) : size q = deg.+1 ->
     recip deg q = reciprocal_pol q.
Proof. by move=> s; rewrite /recip s subnn expr0 mul1r. Qed.

Lemma recip_scale_swap (q : {poly R}) c : c != 0 -> (size q <= deg.+1)%N ->
    recip deg (q \scale c) = (c ^+ deg)%:P * recip deg q \scale c^-1.
Proof.
move=> c0 sz; rewrite !recipE //; last by rewrite size_scaleX.
rewrite !poly_def big_distrr /=.
rewrite [_ \scale c^-1]/scaleX_poly linear_sum; apply: eq_bigr.
move=> [i ci] _ /=; rewrite scaleX_polyE coef_poly.
case h: (deg - i < size q)%N; last first.
  rewrite scale0r nth_default; last by rewrite leqNgt h.
  by rewrite scale0r mulr0 comp_poly0.
rewrite comp_polyM comp_polyC comp_polyZ poly_comp_exp comp_polyX.
rewrite (mulrC 'X) exprMn scalerAl -!mul_polyC -!polyC_exp mulrA -!polyC_mul.
rewrite mulrA mulrAC [q`_ _ * _]mulrC; congr (_ %:P * _); congr (_ * _).
case h' : (i < deg)%N; first by rewrite exprVn expfB.
have -> : i = deg by apply/eqP; move: ci; rewrite ltnS leq_eqVlt h' orbF.
by rewrite subnn expr0 exprVn mulfV // expf_neq0.
Qed.

Lemma bern_coeffs_mon : forall i, (i <= deg)%N ->
    relocate 'X^i = ('X - a%:P )^+(deg - i) * (b%:P - 'X)^+i.
Proof.
have nsba0 : ~~ (b - a == 0) by rewrite subr_eq0 eq_sym.
move=> i leqip; rewrite /relocate /recip size_polyXn.
rewrite ltnNge ltnS leqip/=; rewrite shift_polyXn.
have -> // : forall c : R, c != 0 -> 
  (('X + (-1)%:P)^+ i) \scale c = ('X * c%:P + (-1)%:P)^+ i.
  move=> c hc; rewrite scaleX_polyE size_factor_expr.
  rewrite [(_ * _ + _) ^+ _]exprDn.
  rewrite (reindex_inj rev_ord_inj) /=.
  rewrite power_monom poly_def; apply: eq_bigr => j _.
  rewrite coef_poly subSS; have -> : (j < i.+1)%N by case j.
  rewrite subKn; last by case j.
  rewrite exprMn_comm; last by exact: mulrC.
  rewrite -mulrA (mulrCA 'X^j) (mulrC 'X^j) -!polyC_exp !mul_polyC.
  by rewrite scalerA !scalerMnl -(mulrC (c ^+ j)) mulrnAr bin_sub //; case j.
have -> // : forall c:R, c != 0 -> 
  reciprocal_pol (('X * c%:P + (-1)%:P) ^+ i) = (c%:P - 'X)^+i.
  move=> c hc; rewrite reciprocalX reciprocal_monom // addrC.
  by congr ((_ + _) ^+ _); rewrite mulrC mul_polyC scaleNr scale1r.
rewrite size_amul_expr // subSS /shift_poly comp_polyM !poly_comp_exp.
rewrite comp_polyD linearN /= !comp_polyX comp_polyC opprD -!polyC_opp opprK.
by rewrite polyC_sub addrAC !addrA addrK.
Qed.

(* TODO: change the condition on the size into a '<=', change the definition
  of Mobius for that. *)
Lemma relocateK (q : {poly R}) : (size q <= deg.+1)%N ->
  relocate (Mobius deg a b q) = (b-a) ^+deg *: q.
Proof.
move=> s; rewrite /relocate /Mobius.
rewrite size_comp_poly2; last by rewrite size_XaddC.
set sc := ((q \shift _) \scale _).
set sz := size _.
have dif : b - a != 0 by rewrite subr_eq0 eq_sym.
have t : (size sc <= deg.+1)%N.
  by rewrite size_scaleX // size_comp_poly2 //; apply: size_XaddC.
have t' : (sz <= deg.+1)%N by apply: size_recip.
rewrite ltnNge t' /= -shift_polyD addNr.
rewrite [_ \shift 0]/shift_poly addr0 comp_polyXr.
(* TODO: we miss a scaleX_poly_linear canonical structure.
  and lemma about composing scale operations. *)
rewrite recip_scale_swap // recipK // /sc mul_polyC /scaleX_poly linearZ /=.
rewrite -comp_polyA comp_polyM comp_polyX comp_polyC -mulrA -polyC_mul.
by rewrite mulVf // mulr1 comp_polyXr linearZ /= shift_polyDK.
Qed.

End BernsteinPols.

Section dicho_proofs.

Variable R : archiFieldType.

Lemma dicho'_delta_bern (a b m : R) k p (alpha := (b - m) * (b - a)^-1)
  (beta := ((m - a) * (b - a)^-1)) :
  a != b -> m != a -> (k <= p)%N -> 
  bernp a b p k = 
  \sum_(j < p.+1)((dicho' alpha beta  (delta R k) j)%:P * bernp a m p j).
Proof.
move=> dab dma hlt1.
rewrite -(big_mkord  
(fun _ => true)
(fun j => (dicho' alpha beta (delta R k) j)%:P * bernp a m p j)).
rewrite (big_cat_nat _ _ _ (leq0n k)) //=; last by apply: leq_trans hlt1 _; exact: leqnSn.
rewrite (_ : \sum_( _ <= i0 < _ ) _ = 0) /= ?add0r; last first.
  rewrite big1_seq //= => j; rewrite mem_iota add0n subn0; case/andP=> _ h.
  by rewrite dc_delta_head // polyC0 mul0r.
rewrite -{2}(add0n k) big_addn.
have h : forall i0, (0 <= i0 < p - k)%nat -> 
  (dicho' (m - a) (b - m) (delta R k) (i0 + k))%:P * bernp a m p (i0 + k) = 
   (( (m - a) ^+ i0) * (b - m) ^+ k)%:P * bernp a m p (i0 + k) *+ 'C(i0 + k, k).
  by move=> j h; rewrite /dicho' addnC dc_delta_tail polyC_muln -mulrnAl addnC.
have -> : bernp a b p k =  
          (('X - a%:P)^+k * ((b - a)^-k)%:P) * 
          ((b%:P  - 'X )^+(p - k) * ((b - a)^-(p - k))%:P) *+'C(p, k).
  rewrite /bernp -!mulrA. congr (_ *+ _).
  rewrite [_ * (_)%:P]mulrC [((b - a)^-k)%:P * _]mulrA -polyC_mul.
  by rewrite -invfM -exprD subnKC // !mulrA [_ %:P * _]mulrC.
have -> : (('X - a%:P) ^+ k * ((b - a) ^- k)%:P) =
           (beta^+k)%:P * (('X - a%:P) ^+ k * ((m - a) ^- k)%:P).
  rewrite /beta expr_div_n polyC_mul !mulrA -[_ * (_ ^+k)]mulrC !mulrA mulrAC.
  rewrite -!mulrA -polyC_mul mulfV ?polyC1 ?mulr1 ?expf_eq0 ?subr_eq0 //.
  by move/negPf: dma => ->; rewrite andbF.
rewrite -(exprVn (b - a)) [(_ ^-1 ^+ _)%:P]polyC_exp.
rewrite -exprMn_comm; last by exact: mulrC.
have -> : (b%:P - 'X) * ((b - a)^-1)%:P = 
   ((m%:P - 'X) * (m - a)^-1%:P) + (alpha%:P * ('X - a%:P) * (m - a)^-1%:P).
 (* a ring tactic would be nice here *)
  rewrite [(m%:P - _) * _]mulrDl mulrDr [(alpha%:P * _ + _) * _]mulrDl.
  rewrite (mulrC _ 'X) -(mulrA 'X) [_ + (- 'X * _)]addrC mulNr -mulrN.
  rewrite addrAC addrA -mulrDr -mulN1r -mulrDl.
  rewrite -(polyC_opp 1) -polyC_add /alpha.
  have -> : -1 = (a-b)/(b-a).
    by rewrite -opprB mulNr mulfV // subr_eq0 eq_sym.
  rewrite -mulrDl addrA addrNK -(opprB m a).
  rewrite -polyC_mul !mulNr mulrAC mulfV ?mul1r; last by rewrite subr_eq0.
  rewrite polyC_opp -addrA -mulrDl [_ * - a%:P]mulrC -[-a%:P]polyC_opp.
  rewrite -polyC_mul -polyC_add !mulrA.
  have {2}-> : m = m * (b - a) / (b - a) by rewrite mulfK // subr_eq0 eq_sym.
  rewrite -[_ + _ /(b-a)]mulrDl !mulrDr addrA addrAC [-a * -m]mulrN.
  rewrite [-a * m]mulrC addrNK [_ + m * b]addrC -mulrDl -polyC_mul.
  rewrite [_ * b]mulrC mulrAC mulfK; last by rewrite subr_eq0.
  by rewrite mulrN -mulNr polyC_mul -mulrDl addrC.
rewrite [_^+ (p - k)]exprDn /= subSn //.
rewrite -(big_mkord (fun _ => true) (fun i => ((m%:P - 'X) * ((m - a)^-1)%:P) ^+ (p - k - i) *
       (alpha%:P * ('X - a%:P) * ((m - a)^-1)%:P) ^+ i *+ 'C(
       p - k, i))).
rewrite  big_distrr /= (big_morph  _ (mulrnDl ('C(p, k))) (mul0rn _ _)).
apply: congr_big_nat=> // i /= hi.
rewrite /dicho' [(i + k)%nat]addnC dc_delta_tail /bernp.
rewrite !mulrnAr polyC_muln mulrnAl -!mulrnA; congr (_ *+ _); last first.
   rewrite addnC -util_C ?leq_addr //.
     by rewrite mulnC; congr (_ * _)%N;  rewrite addnC addnK.
   by move:hi; rewrite ltnS -(leq_add2l k) subnKC.
set Xa := ('X - a%:P); set Xb := (_ - 'X).
rewrite [alpha^+_ * _]mulrC [(beta^+_ * _)%:P]polyC_mul -!mulrA; congr (_ * _).
rewrite [(alpha%:P * _)]mulrC. 
rewrite [(_ * alpha%:P)^+i]exprMn_comm; last by exact: mulrC.
set lhs := (alpha ^+ i)%:P * _; rewrite !mulrA.
rewrite [_ * alpha%:P ^+ i]mulrC /lhs polyC_exp; congr (_ * _)=> {lhs alpha}.
set lhs := _ * (_ * Xb ^+ (p - _)).
rewrite !exprMn_comm; try exact: mulrC.
rewrite [Xa^+i * _]mulrC !mulrA [_ * Xa^+ _]mulrC !mulrA.
rewrite -exprD /lhs [_ * (Xa^+ _ * _)]mulrA [_ * Xa^+ _]mulrC -!mulrA.
rewrite addnC; congr (_ * _)=> {lhs}.
rewrite !mulrA [_ * Xb^+ (p - k - i)]mulrC -!mulrA [Xb^+ _ * _]mulrC.
rewrite subnDA; congr (_ * _); rewrite -!polyC_exp -!polyC_mul; congr (_ %:P).
rewrite -!exprVn -!exprD; congr ((m -a)^-1 ^+ _).
rewrite subnK; last by [].
by rewrite addnC subnK; last by [].
Qed.

Lemma dicho'_correct : forall (a b m : R)(alpha := (b - m) * (b - a)^-1)
  (beta := ((m - a) * (b - a)^-1))(p : nat)(q : {poly R})(c : nat -> R),
  a != b ->
  m != a ->
  q = \sum_(i < p.+1)(c i)%:P * bernp a b p i ->
  q = \sum_(j < p.+1)(dicho' alpha beta c j)%:P * bernp a m p j.
Proof.
move=> a b m alpha beta p q c neqab neqma qdef.
have {neqma qdef} -> : q = 
  \sum_(j < p.+1) \sum_(i < p.+1) 
  (c i)%:P * (dicho' alpha beta (delta R i) j)%:P * bernp a m p j.
  rewrite exchange_big /= qdef; apply: congr_big; [by [] | by [] |]. 
  case=> k hk _ /=.
  have hk': (k <= p)%N by exact: hk. 
  rewrite (dicho'_delta_bern neqab neqma hk').
  rewrite big_distrr /=;  apply: congr_big; [by [] | by [] |]. 
  by case=> i hi _; rewrite !mulrA.
apply: congr_big; [by [] | by [] |]. 
case=> i hi _ /=;  rewrite -big_distrl /=; congr (_ * _).
have -> : dicho' alpha beta c i = 
  dicho' alpha beta (fun k => \sum_(j < p.+1)(c j) * (delta R j k)) i.
  apply: ext_dc=> k _; rewrite add0n => h.
  have pk : (k < p.+1)%N by apply: leq_ltn_trans hi.
  rewrite (bigD1 (Ordinal pk)) //= /delta eqxx mulr1 big1 ?addr0 //.
  case=> j hj /=; move/negPf; case e : (j == k); last by rewrite mulr0.
  suff : Ordinal hj = Ordinal pk by move/eqP->.
  by apply: val_inj=> /=; apply/eqP.
elim: p i {hi} c alpha beta=> [| p ihp] i c alpha beta /=; set f := dicho' alpha beta.
  rewrite big_ord_recl /= big_ord0 /dicho' /= addr0.
  rewrite /f /dicho'.
  have : forall k, 
    (0 <= k)%N -> (k <= 0 + i)%N -> 
    \sum_(j < 1) c j * delta R j k = (c 0%N) * (delta R 0) k.
    by move=> k _ _; rewrite  big_ord_recl /= big_ord0 addr0.
  by move/ext_dc->; rewrite scal_dc polyC_mul.
  rewrite (_ : f _ _ = 
  f 
  (fun k : nat => 
    (\sum_(j < p.+1) c j * delta R j k) + (c p.+1 * delta R p.+1 k)) i);
  last first.
  by apply: ext_dc=> k _; rewrite add0n=> hki; rewrite big_ord_recr.
rewrite /f /dicho' add_dc polyC_add -ihp // big_ord_recr /=; congr (_ + _).
by rewrite scal_dc polyC_mul.
Qed.

Lemma bern_swap :
 forall p i (l r : R), (i <= p)%N -> bernp r l p i = bernp l r p (p - i).
Proof.
move=> p i l r lip; rewrite /bernp subKn // bin_sub //; congr (_ *+ _).
rewrite -[l - r]opprB -[l%:P - 'X]opprB -['X - r%:P]opprB.
rewrite -mulN1r -[-(r%:P - 'X)]mulN1r  -[- ('X - l%:P)]mulN1r.
rewrite !exprMn_comm; try exact: mulrC.
rewrite invfM polyC_mul [_ * ((r - l)^-p)%:P]mulrC.
rewrite -!mulrA; congr (_ * _).
rewrite  -exprVn polyC_exp [(- 1)^-1]invrN invr1 polyC_opp.
rewrite [(r%:P - 'X)^+i * _]mulrC !mulrA polyC1 -!exprD.
by rewrite -addnA subnKC // -signr_odd odd_add addbb /= expr0 mul1r.
Qed.

Lemma bern_rev_coef : forall (p : nat)(a b : R)(c : nat -> R),
  \sum_(i < p.+1)(c i)%:P * (bernp a b p i) = 
  \sum_(i < p.+1)(c (p - i)%N)%:P * (bernp b a p i).
Proof.
move=> p a b c.
pose t := \sum_(i < p.+1) (c (p - i)%N)%:P * bernp a b p (p - i)%N.
transitivity t.
  by rewrite (reindex_inj rev_ord_inj) /=; apply: eq_bigl.
apply:eq_bigr => [[i hi]] _ /=.
by rewrite bern_swap ?subKn // leq_subr.
Qed.

 
Lemma dicho_correct : forall (a b m : R)(alpha := (b - m) * (b - a)^-1)
  (beta := ((m - a) * (b - a)^-1))(p : nat)(q : {poly R})(c : nat -> R),
  a != b ->
  m != b ->
  q = \sum_(i < p.+1)(c i)%:P * bernp a b p i ->
  q = \sum_(j < p.+1)(dicho alpha beta p c j)%:P * bernp m b p j.
Proof.
move=> a b m alpha beta p q c neqab neqmb qdef.
rewrite bern_rev_coef in qdef.
have neqba : b != a by rewrite eq_sym.
rewrite (@dicho'_correct _ _ _ _ _ (fun i => c (p - i)%N) neqba neqmb qdef).
rewrite -(big_mkord  
(fun _ => true) (fun j => (dicho' ((a - m) / (a - b)) ((m - b) / (a - b))
         (fun i : nat => c (p - i)%N) j)%:P * bernp b m p j)).
rewrite big_nat_rev /= big_mkord; apply: congr_big; [by [] | by [] |].
move=> [i hi] _ {qdef}; rewrite add0n subSS.
rewrite -bern_swap //; congr (_%:P * _); rewrite /dicho' /dicho.
rewrite dc_reverse //= ?leq_subr // addn0 subKn //.
rewrite -opprB -[a - b]opprB -[a - m]opprB -mulN1r -[-(b - a)]mulN1r.
rewrite -[-(m - a)]mulN1r invfM [(- 1)^-1]invrN invr1 -mulrA.
rewrite [(b - m) * _]mulrC !mulrA mulNr mul1r opprK [-1 * _ ]mulrC 2!mulrN1.
by rewrite opprK -/beta mulrC mul1r.
Qed.

End dicho_proofs.
