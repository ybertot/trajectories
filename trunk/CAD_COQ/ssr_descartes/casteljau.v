Require Import ssreflect ssrfun ssrbool eqtype ssrnat binomial seq fintype bigops.
Require Import ssralg poly polydiv orderedalg.
Require Import  Qcanon.
Require Import infra pol.


Import GRing.Theory.
Import OrderedRing.Theory.
Open Scope ring_scope.

Lemma util_C : forall n i j : nat, (i <= j)%nat -> (j <= n)%nat -> 
    ('C(n, i) * 'C(n-i, j-i) = 'C(j, i) * 'C(n, j))%nat.
move => n i j ij jn.
apply/eqP; rewrite -(@eqn_pmul2r ( i`! * (n - i) `!));
  last by rewrite muln_gt0; apply/andP; split; apply: fact_gt0.
rewrite -(@eqn_pmul2r ((j - i)`! * ((n - i)-(j - i))`!)); last first.
  by rewrite muln_gt0; apply/andP; split; apply: fact_gt0.
have ilen : (i <= n)%nat by apply: leq_trans jn.
rewrite (mulnAC 'C(n, i)) -mulnA !bin_fact //; last by apply: leq_sub2r.
rewrite !mulnA (mulnAC _ _ (i`!)) 2!(mulnAC _ _ ((j-i)`!)) -(mulnA 'C(j, i)).
rewrite bin_fact // subn_sub subnKC // mulnAC (mulnC j`!) -(mulnA _ j`!).
rewrite bin_fact //.
Qed.

Section CauchyBound.

Variable F : oFieldType.

Variables (n : nat)(E : nat -> F).

Hypothesis pnz : E n != 0.

Lemma gt1expn : forall n (x : F), 1 <= x -> 1 <= x^+n.
Proof.
elim=> [| m ihm] x hx; first by rewrite expr0 lerr.
rewrite exprS; apply: ler_trans (hx) _; rewrite -{1}(mulr1 x).
rewrite ltef_mulpl //=; first by exact: ihm.
by apply: lter_le_trans hx; rewrite /= ltr01.
Qed.

Lemma ge0_sum : forall m (G : nat -> F), 
  (forall i, ((i < m)%N ->  0 <= G i)) -> 0 <= \sum_(i < m) G i.
Proof.
elim=> [|m ihm] G hp; first by rewrite big_ord0 lerr.
rewrite big_ord_recr /=; apply: lter_le_addpl=> //=; last by apply: hp; exact: ltnSn.
apply: ihm=> i ltim; apply: hp; apply: ltn_trans ltim _; exact: ltnSn.
Qed.

Lemma ge_sum :  forall m (G1 G2 : nat -> F), 
  (forall i, ((i < m)%N ->  G1 i <= G2 i)) -> \sum_(i < m) G1 i <= \sum_(i < m) G2 i.
Proof.
elim=> [|m ihm] G1 G2 hp; first by rewrite !big_ord0 lerr.
rewrite ! big_ord_recr /=; apply: lter_add=> /=; last by apply: hp; exact: ltnSn.
apply: ihm=> i ltim; apply: hp; apply: ltn_trans ltim _; exact: ltnSn.
Qed.

Lemma absr_sum : forall m  (G : nat -> F),
  `|\sum_(i < m) G i| <= \sum_(i < m) `|G i|.
Proof.
elim=> [|m ihm] G; first by rewrite !big_ord0 absr0 lerr.
rewrite !big_ord_recr /=; apply: lter_trans (absr_add_le _ _) _=> /=.
by rewrite ler_add2l; apply: ihm.
Qed.

Lemma absrge1 : forall x : F, 1 < x -> x^-1 < 1.
Proof.
move=> x lt1x; rewrite -(mul1r (x^-1)) ltef_divpl /= ?mul1r //. 
apply: lter_trans lt1x; exact: ltr01.
Qed.

Lemma absf_inv : forall x : F, `|x ^-1| = `|x|^-1.
Proof.
move=> x; case e: (x == 0); first by rewrite (eqP e) absr0 invr0 absr0.
have axn0 : ~~ (`|x| == 0) by rewrite absr_eq0 e.
by apply: (mulfI axn0); rewrite mulfV // -absf_mul mulfV ?e // absr1.
Qed.

Lemma expf_gt1 : forall m (x : F), x > 1 -> x^+m.+1 > 1.
Proof.
elim => [|m ihm] x hx; first by rewrite expr1.
apply: lter_trans (hx) _ => /=; rewrite exprS -{1}(mulr1 x).
apply: lter_mulpl=> /=; last exact: ihm.
apply: lter_trans hx; exact: ltr01.
Qed.

Lemma expf_ge1 : forall m (x : F), x >= 1 -> x^+m >= 1.
Proof.
elim => [|m ihm] x hx; first by rewrite expr0 lerr.
apply: lter_trans (hx) _ => /=; rewrite exprS -{1}(mulr1 x).
apply: lter_mulpl=> /=; last exact: ihm.
apply: lter_trans hx; apply: ltrW; exact: ltr01.
Qed.


Lemma CauchyBound : forall x, (\poly_(i < n.+1) E i).[x] = 0 -> 
  `| x | <= `|E n|^-1 * \sum_(i < n.+1) `|E i|.
Proof.
move=> x px0; case: (lerP `|x| 1)=> cx1.
  set C := _ * _; suff leC1 : 1 <= C by apply: ler_trans leC1.
  have h1 : `|E n| > 0 by rewrite  absr_gt0.
  rewrite -(ltef_mulpl _ _ _ h1) /= mulr1 /C mulrA mulfV ?absr_eq0 // mul1r.
  rewrite big_ord_recr /= -{1}(add0r `|E n|) ler_add2l.
  (* here should be a lemme in orderedalg *)
  elim: n=> [|m ihm]; first by rewrite big_ord0 lerr.
  rewrite big_ord_recr /=; apply: lter_le_addpl=> //; exact: absr_ge0.
case e: n=> [| m].
  move: px0 pnz; rewrite e /= horner_cons horner0 mul0r add0r; move->.
  by rewrite eqxx.
have h1 : E  m.+1 * x^+m.+1 = - \sum_(i < m.+1) E i * x^+ i.
  apply/eqP; rewrite -subr_eq0 opprK -{2}px0 horner_poly (big_ord_recr n).
  by rewrite e //= addrC.
case x0 : (x == 0).
  rewrite (eqP x0) absr0; apply:  mulr_ge0pp; first by rewrite invf_gte0 /= absr_ge0.
  suff h2: forall i, (i < m.+2)%N -> 0 <= `|E i| by apply: (ge0_sum _ _ h2).
  move=> i _; exact: absr_ge0.
have {h1} h2 : E m.+1 * x =  - \sum_(i < m.+1) E i * x^-(m - i).
have xmn0 : ~~(x^+m == 0) by rewrite expf_eq0 x0 andbF.
  apply: (mulIf xmn0); rewrite mulNr big_distrl /= -mulrA -exprS h1; congr (- _).
  apply: congr_big; [by [] | by [] |] => [[i hi]] _ /=.
  have mi : m = (m - i + i)%N by rewrite subnK.
  rewrite {2}mi exprn_addr -!mulrA; congr (_ * _); rewrite mulrA mulVf ?mul1r //.
  by rewrite expf_eq0 x0 andbF.
have h3 : `|\sum_(i < m.+1) E i / x ^+ (m - i) | <= \sum_(i < m.+2) `|E i|.
  apply: ler_trans (absr_sum m.+1 (fun i =>  E i / x ^+ (m - i))) _.
  apply: (@ler_trans _ (\sum_(i < m.+1) `|E i|)); last first.
    by rewrite (big_ord_recr m.+1) /= lter_addrr /= absr_ge0.
  apply: (ge_sum m.+1 (fun i => `|E i / x ^+ (m - i)|) (fun i => `|E i|))=> i lti.
  rewrite absf_mul -{2}(mulr1 (`|E i|)); apply: lter_mulpl; rewrite /= ?absr_ge0 //.
  rewrite absf_inv -invr1; apply: ltef_invpp=> /=; first exact: ltr01.
    by rewrite absr_gt0 expf_eq0 x0 andbF.
  by rewrite absf_exp; apply: expf_ge1; apply: ltrW.
rewrite mulrC ltef_divpr /=; last by rewrite absr_gt0 -e.
by apply: lter_trans h3=> /=; rewrite -absf_mul mulrC h2 absr_opp lerr.
Qed.
 
End CauchyBound.
  

(* b gives the coefficients of a polynomial on some bounded interval [a, b].
de_casteljau computest all the coefficients in the triangle for a, m, n, with
l := m - a and r := b - m.

invariant : l + r = b - a *)


Section DeCasteljauAlgo.

Variables l r : Qcb.


Fixpoint de_casteljau (b : nat -> Qcb) (n : nat) :=
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
move => k; elim: k => [ | k IHk] a a' b b' n /= ; first done.
rewrite 2!IHk !mulr_addr !mulrA !(mulrC r) !(mulrC l) !addrA.
by rewrite (addrAC _ _ (a' * l * _)%R).
Qed.

(* in particular it is additive *)
Lemma add_dc :
  forall k b b' n, de_casteljau (fun j => b j + b' j)%R k n =
     (de_casteljau b k n + de_casteljau b' k n)%R.
move => k b b' n; have := lin_dc k 1 1 b b' n.
rewrite (ext_dc k (fun j => 1 * b j + 1 * b' j) (fun j => b j + b' j))%R.
  by rewrite !mul1r.
by move => x; rewrite /= !mul1r.
Qed.

(* in particular it is homothetic *)
Lemma scal_dc :
  forall k a b n, de_casteljau (fun j => a * b j)%R k n =
      (a * de_casteljau b k n)%R.
move => k a b n; have := lin_dc k a 0 b (fun i => 0)%R n.

rewrite (ext_dc _ (fun j => a * b j + 0 * 0)%R (fun j => a * b j)%R).
by rewrite mul0r addr0.
by move => x; rewrite /= mul0r addr0.
Qed.


End DeCasteljauAlgo.

Section DeltaSeqs.

Definition delta (i j : nat) : Qcb := if (i == j) then 1 else 0.


Lemma dc_delta_head : forall j k l r, 
  (j < k)%nat -> dicho' l r (delta k) j = 0.
Proof.
rewrite /dicho' => j k l r hlt.
pose d0 := fun _ : nat => 0 : Qcb.
rewrite (ext_dc _ _ _ _ d0); last first.
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
rewrite !ihj // ?mulr0 ?addr0 //; first by rewrite ltn_subS.
by apply: ltn_trans hltkd _; rewrite [(i - j)%nat]ltn_subS.
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
rewrite [_ * B^+ i]mulrC mulrA -exprS [B^+_ * _]mulrC -mulrn_addr.
by congr (_ *+ _).
Qed.
 
(* Lemma algo_reverse:*)
Lemma dc_reverse :
 forall b A B p i k,
 (i <= p)%N ->
 (k <= p - i)%N ->
  de_casteljau B A (fun t => b (p - t)%N) i k = de_casteljau A B b i (p - (i + k)).
Proof.
move=> b A B p; elim=> [| i ihi] k hip hk /=; first by rewrite add0n.
rewrite addrC; congr (_  + _).
  by rewrite ihi ?(ltnW hip) ?addnS ?addSn // ltn_subS //; apply: leq_ltn_trans hk _.
rewrite ihi ?(leq_trans hk) // ?leq_sub2l // ?(ltnW hip) //=.
by rewrite addSn -ltn_subS // ltn_add_sub; move: hk; rewrite -ltnS -ltn_subS.
Qed.

End DeltaSeqs.

Section BernsteinPols.

Variables (a b : Qcb).
Variable p : nat.

Hypothesis neqab : a != b.

(* elements of the Bernstein basis of degree p *)
Definition bernp i : {poly Qcb} := 
  ((b - a)^-p)%:P * ('X - a%:P)^+i * (b%:P - 'X)^+(p - i) *+ 'C(p, i).

Definition relocate (q : {poly Qcb}) :=
  let s := size q in
    (* 1st case : degree of q is to large for the current basis choice *)
  if (p.+1 < s)%N then [::]
    (* 2nd case : we complete the list coefficients of q with tail zeroes *)
    else
      translate_pol' 
      (reciprocate_pol 
        (expand 
          (translate_pol' (q ++ (nseq (p.+1 - s) 0)) (- 1)) (b - a))) (- a).
Print Bernstein_coeffs.
(* should be abstracted and put  inpoly *)

(* size_Xma should be with addition *)
Lemma size_factor_expr : forall (t : Qcb)(n : nat), 
  size (('X + t%:P)^+n) = n.+1.
Proof.
move=> t; elim=> [|n ihn]; first by rewrite expr0 size_polyC oner_eq0.
rewrite exprS size_monic_mul; last first.
  - by rewrite -size_poly_eq0 ihn; apply/negP; move/eqP.
  - by rewrite  -(opprK t%:P) -polyC_opp monic_factor.
  - by rewrite ihn -(opprK t%:P) -polyC_opp size_XMa.
Qed.

Lemma size_amul_expr : forall (t c : Qcb)(i : nat), 
  c != 0 -> size (('X * c%:P + t%:P) ^+ i) = i.+1.
Proof.
move=> t c; elim=> [| i ih] cn0; first by rewrite expr0 size_poly1.
have hn0 : size ('X * c%:P + t%:P) = 2.
  by rewrite mulrC size_amulX size_polyC cn0.
by rewrite exprS size_mul_id // ?expf_eq0 -?size_poly_eq0 hn0 ?andbF // ih.
Qed.

Lemma translate_pol'P : forall (c : Qcb) i, (translate_pol' 'X^i c) = ('X + c%:P)^+i.
Proof.
move=> c i.
have lhs_size : size (translate_pol' 'X^i c) = i.+1.
   by rewrite size_translate_pol' size_polyXn.
apply: (@eq_from_nth _ 0); first by rewrite lhs_size  size_factor_expr.
move=> k; rewrite lhs_size => hki.
rewrite /translate_pol' nth_mkseq size_polyXn // addrC exprn_addl coef_sum.
rewrite (bigD1 (Ordinal (ltnSn _))) //= big1; last first.
  case=> j hj nhj /=; rewrite coef_Xn (_ : (j == i) = false) /= ?mul0r ?mul0rn //.
  case abs : (j == i) => //.
  suff h: Ordinal hj = Ordinal (ltnSn _) by rewrite h eqxx in nhj.
  by apply: val_inj; apply/eqP.
rewrite addr0 coef_Xn eqxx mul1r (bigD1 (Ordinal hki)) //=.
rewrite big1 => [| [j hj nhj]] /=; rewrite coef_natmul -polyC_exp mulrC coef_mulC.
  by rewrite coef_Xn eqxx mul1r addr0.
rewrite coef_Xn (_ : (k == j) = false) ?mul0r ?mul0rn //; case abs : (k == j) => //.
suff h: Ordinal hj = Ordinal hki by rewrite h eqxx in nhj.
by apply: val_inj; apply/eqP=> /=; rewrite eq_sym.
Qed.



(* to clean: a simple induction is probably enough *)
Lemma translate_padded_l : forall (i : nat) (q : seq Qcb)(c : Qcb) , 
  translate_pol' (q ++ (nseq i 0)) c = (translate_pol' q c) ++ (nseq i 0).
Proof.
move=> n; elim: n {-2}n (leqnn n) => [| i hi] n hn q c.
 by move: hn; rewrite leqn0; move/eqP->; rewrite !cats0.
move: hn; rewrite leq_eqVlt; case/orP; last by move=> hn; rewrite hi //.
move/eqP->; rewrite -[q ++ _]/(q ++ nseq 1 0 ++ nseq i 0) catA hi //.
rewrite /translate_pol' size_cat size_nseq addnS addn0.
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

Lemma reciprocate_pol_padded :  forall (i : nat) (q : seq Qcb),
  reciprocate_pol (q ++ (nseq i 0)) = (nseq i 0) ++ (reciprocate_pol q).
Proof.
move=> i q; rewrite /reciprocate_pol rev_cat; congr (_ ++_).
apply: (@eq_from_nth _ 0); rewrite size_rev size_nseq // => j hij.
rewrite nth_rev ?size_nseq // !nth_ncons.
by case: i hij=> // i hij; rewrite ltnS subSS leq_subr hij.
Qed.

Lemma size_factor : forall x : Qcb, size ('X + x%:P) = 2.
Proof.
by move=> x; rewrite size_addl ?size_polyX // size_polyC /=; case: (x == 0).
Qed.

Lemma coef_poly0 : forall p q : {poly Qcb}, (p * q)`_0 = p`_0 * q`_0.
Admitted.

Lemma translate_mulX : forall (q1 q2 : {poly Qcb}) c, q2 != 0 -> q1 != 0 ->
   translate_pol' q2 c = q1 -> translate_pol' ('X * q2) c = ('X + c%:P) * q1.
Proof.
  move=> q1 q2 c q2n0 q1n0 e.
  have sp1 : size (translate_pol' ('X * q2) c) = (size q2).+1.
    by rewrite size_translate_pol' size_mul_id // -?size_poly_eq0 ?size_polyX.
  have sp2 : size ('X * q2) = (size q2).+1.
    by rewrite mulrC size_mul_monic ?monicX // size_polyX !addnS addn0.  
  apply: (@eq_from_nth _ 0).
    by rewrite sp1 size_mul_id // -?size_poly_eq0 ?size_factor // -e size_translate_pol'.
  rewrite sp1 => [[|j]] hj. 
    rewrite coef_poly0 coef_add coefC eqxx coefX add0r -e /translate_pol'.    
    rewrite !nth_mkseq ?lt0n ?size_poly_eq0 // -?size_poly_eq0 ?sp2 //.
    rewrite big_distrr big_ord_recl coef_Xmul eqxx mul0r mul0rn add0r.
    apply: congr_big=> // [[k hk]] _.
    rewrite  !bin0 !subn0 !mulr1n -[('X * q2)`__]/(('X * q2)`_k.+1).
    rewrite [GRing.muloid _ _]/= [c * _]mulrC.
    rewrite -mulrA [_ * c]mulrC -exprS; congr (_ * _).
    (* we  should really put a nosimpl on `_ *)
    by rewrite coef_Xmul /=.
  rewrite /translate_pol' nth_mkseq ?sp2 //.
  rewrite coef_mul; apply: sym_eq; rewrite 2!big_ord_recl big1; last first.
    case=> k hk _; rewrite -[('X + c%:P)`_ _]/(('X + c%:P)`_ k.+2).
    by rewrite coef_add coefC coefX /= addr0 mul0r.
  rewrite [nat_of_ord _]/= !subn0 addr0 -[nat_of_ord _]/1%N.
  rewrite !coef_add !coefX !coefC !eqxx -![_ == _]/false add0r addr0 mul1r.
  rewrite -e /translate_pol'.
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

Lemma translate_mulXn : forall n (q1 q2 : {poly Qcb}) c, q2 != 0 -> q1 != 0 ->
   translate_pol' q2 c = q1 -> 
   translate_pol' ('X^n * q2) c = ('X + c%:P)^+n * q1.
Proof.
elim=> [|n ihn] q1 q2 c nq20 nq10 e; first by rewrite expr0 !mul1r.
rewrite exprS -mulrA.
have h : translate_pol' ('X^n * q2) c = ('X + c%:P) ^+ n * q1.
  by rewrite (ihn q1 q2).
rewrite (translate_mulX _ _ _ _ _ h); first by rewrite mulrA -exprS.
  rewrite -size_poly_eq0 mulrC size_mul_monic ?monicXn // size_polyXn !addnS /=.
  by rewrite addn_eq0 negb_and size_poly_eq0 nq20.
rewrite -size_poly_eq0 size_mul_id // -?size_poly_eq0 ?size_polyXn size_factor_expr //=.
by rewrite addn_eq0 negb_and size_poly_eq0 nq10 orbT.
Qed.

Lemma translateAlXn : forall c1 c2 n, 
  translate_pol' (translate_pol' 'X^n c1) c2 = translate_pol' 'X^n (c1 + c2).
Proof.
move=> c1 c2 n.
apply:  (@eq_from_nth _ 0); rewrite ?size_translate_pol' //.
rewrite size_polyXn => i hi. 
rewrite /translate_pol' nth_mkseq ?size_mkseq ?size_polyXn // nth_mkseq //.
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
  rewrite subnKC // -subn_sub [(i + _)%N]addnC -addn_subA // subnn addn0.
  rewrite mulrnAl -!mulrnA;  congr (_ *+ _).
  rewrite [(_ * 'C(k, i))%N]mulnC {3}(_ : j = j + i - i)%N; last first.
    by rewrite -addn_subA // subnn addn0.
  by rewrite util_C 1?mulnC // ?leq_addl // -(subnK hki) leq_add2r.
  - rewrite -hki bin_small // mulr0n big1 // => [[j hj]] /= _.
    by rewrite (@bin_small j).
Qed.


Lemma bern_coeffs_mon : forall i, 
  (i <= p)%N -> Poly (relocate 'X^i) =
  (- 1)^+p * ('X - b%:P)^+i * (a%:P - 'X)^+(p - i).
Proof.
have nsba0 : ~~ (b - a == 0) by rewrite subr_eq0 eq_sym.
move=> i leqip; rewrite /relocate size_polyXn.
rewrite ltnNge ltnS leqip /= subSS translate_padded_l expand_padded.
rewrite reciprocate_pol_padded  translate_pol'P.
have h : forall c, c != 0 -> 
  expand (('X + (-1)%:P)^+ i) c = ('X * c%:P + (-1)%:P)^+ i.

  move=> c hc; apply: (@eq_from_nth _ 0).
    by rewrite size_expand size_factor_expr size_amul_expr.
  rewrite size_expand size_factor_expr => j hj.
  rewrite /expand size_factor_expr nth_mkseq // !exprn_addl !coef_sum big_distrl /=; apply: congr_big=> // [k hk].
  rewrite !coef_natmul mulrnAl; congr (_ *+ _).
  rewrite -polyC_exp !coef_mulC -mulrA [_ * _^+j]mulrC mulrA; congr (_ * _).
  rewrite exprn_mull -polyC_exp coef_mulC coef_Xn. 
  by case ej : (j == i - k)%N;  rewrite -?(eqP ej) // !mul0r.
rewrite h // {h}.
have h : forall c, c != 0 -> 
  reciprocate_pol (('X * c%:P + (-1)%:P) ^+ i) = (c%:P - 'X)^+i.
  move=> c hc; apply: (@eq_from_nth _ 0).
    rewrite size_reciprocate size_amul_expr // addrC -mulN1r mulrC.
    by rewrite -polyC1 -polyC_opp size_amul_expr.
  rewrite size_reciprocate size_amul_expr // => j hj.
  rewrite nth_rev ?size_amul_expr // subSS !exprn_addl !coef_sum.
  apply: congr_big => // [[k hk]] _ /=; rewrite !coef_natmul; congr (_ *+ _).
  rewrite -polyC_exp coef_mulC -[- 'X]mulN1r !exprn_mull -polyC_exp.
  rewrite mulrA coef_mulC -polyC1 -polyC_opp -polyC_exp -polyC_mul.
  rewrite [_ * 'X^k]mulrC coef_mulC -mulrA; congr (_ * _).
  rewrite !coef_Xn /=; do 2 (apply: f_equal); apply/eqP/eqP; last by move->.
  have {hk} hk : (k <= i)%N by [].
  have {hj} hj : (j <= i)%N by [].
  by rewrite -{2}(subKn hk) -{2}(subKn hj); move->.
rewrite h // {h}.
(* use seq_mul_polyX ? *)
have h : forall k  c (p: {poly Qcb}), p != 0 ->
  translate_pol' (nseq k 0 ++ p) c = translate_pol' ('X^k * p) c.
  move=> k c q {leqip} nq0; case: k => [|k]; first by rewrite /= expr0 mul1r.
  have sp : size ('X^k.+1 * q) = (k.+1 + size q)%N.
    by rewrite size_mul_id // -?size_poly_eq0 ?size_polyXn.
  apply:  (@eq_from_nth _ 0).
    by rewrite !size_translate_pol' size_cat size_nseq sp.
  rewrite size_translate_pol' size_cat size_nseq => j hj.
  rewrite /translate_pol' !nth_mkseq ?size_cat ?size_nseq ?sp //.
  apply: congr_big => // [[m hm]] _ /=; congr (_ *+ _); congr (_ * _).
  rewrite mulrC coef_mulXn -cat_cons -[0:: nseq k 0]/(nseq k.+1 0) nth_cat.
  by rewrite size_nseq nth_nseq; case: (m < k.+1)%N.
rewrite h {h}; last first. 
  rewrite expf_eq0 -size_poly_eq0 addrC size_addl size_opp size_polyX ?andbF //.
  by rewrite size_polyC nsba0.
rewrite (_ : _ * _ =(-1) ^+i * 'X^(p - i) * ('X - (b - a)%:P)^+i); last first. 
  rewrite -mulrA [(-1)^+_ * _]mulrC -mulrA -exprn_mull [_ * - 1]mulrC.
  by rewrite mulN1r oppr_sub.
have trans_mulC : forall (p : {poly Qcb}) c d, c != 0 ->
  translate_pol' (c%:P * p) d = map (fun i => c * i) (translate_pol' p d).
  move=> q c d neq0; apply: (@eq_from_nth _ 0).
    rewrite size_translate_pol' size_map size_translate_pol'.
    by rewrite size_polyC_mul.
  rewrite size_translate_pol' size_polyC_mul // => j hj.
  rewrite /translate_pol' nth_mkseq ?size_polyC_mul //.
  rewrite (nth_map 0) ?size_mkseq // nth_mkseq //.
  rewrite big_distrr /=; apply: congr_big=> // [[k hk]] /= _.
  by rewrite coef_Cmul mulrnAr mulrA.
rewrite -{1}polyC1 -[-1%:P]polyC_opp -polyC_exp -mulrA.
rewrite trans_mulC ?expf_eq0 ?oppr_eq0 ?oner_eq0 ?andbF //.
have -> : forall (l : seq Qcb) c, Poly (map [eta *%R c] l) = c%:P * Poly l.
  move=> l c; apply/polyP=> k; rewrite coef_Cmul !coef_Poly.
  case: (ltnP k (size l))=> hkl; first by rewrite (nth_map 0) //.
  by rewrite !nth_default ?size_map // mulr0.
rewrite polyC_exp -{2}(subnKC leqip) exprn_addr -!mulrA; congr (_ * _).
suff -> : (translate_pol' ('X^(p - i) * ('X - (b - a)%:P) ^+ i) (- a))
  = (-1)%:P ^+ (p - i) * (('X - b%:P) ^+ i * (a%:P - 'X) ^+ (p - i)).
  by rewrite polyseqK.
suff h : translate_pol' (('X - (b - a)%:P) ^+ i) (- a) = ('X - b%:P)^+ i.
  rewrite (translate_mulXn _ _ _ _ _ _ h).
  - rewrite -[_%:P^+_  * _]mulrC -mulrA -exprn_mull [(- 1)%:P]polyC_opp.
    by rewrite mulrN1 oppr_sub polyC_opp mulrC.
  - by rewrite -size_poly_eq0 -polyC_opp size_factor_expr.
  - by rewrite -size_poly_eq0 -polyC_opp size_factor_expr.
rewrite -polyC_opp -translate_pol'P translateAlXn oppr_sub addrC addrA addNr.
by rewrite add0r translate_pol'P polyC_opp.
Qed.

Lemma dicho'_delta_bern : forall a b m k p (alpha := (b - m) * (b - a)^-1)(beta := ((m - a) * (b - a)^-1)),
  m != a ->
  (k <= p)%nat -> 
  bernp a b p k = 
  \sum_(j < p.+1)((dicho' alpha beta  (delta k) j)%:P * bernp a m p j).
Proof.
move=> a b m k p alpha beta  dma hlt1.
rewrite -(big_mkord  
(fun _ => true)
(fun j => (dicho' alpha beta (delta k) j)%:P * bernp a m p j)).
rewrite (big_cat_nat _ _ _ (leq0n k)) //=; last by apply: leq_trans hlt1 _; exact: leqnSn.
rewrite (_ : \sum_( _ <= i0 < _ ) _ = 0) /= ?add0r; last first.
  rewrite big1_seq //= => j; rewrite mem_iota add0n subn0; case/andP=> _ h.
  by rewrite dc_delta_head // polyC0 mul0r.
rewrite -{2}(add0n k) big_addn.
have h : forall i0, (0 <= i0 < p - k)%nat -> 
  (dicho' (m - a) (b - m) (delta k) (i0 + k))%:P * bernp a m p (i0 + k) = 
   (( (m - a) ^+ i0) * (b - m) ^+ k)%:P * bernp a m p (i0 + k) *+ 'C(i0 + k, k).
  by move=> j hj; rewrite /dicho' addnC dc_delta_tail polyC_natmul -mulrnAl addnC.
have -> : bernp a b p k =  
                        (('X - a%:P)^+k * ((b - a)^-k)%:P) * 
                        ((b%:P  - 'X )^+(p - k) * ((b - a)^-(p - k))%:P) *+'C(p, k).
  rewrite /bernp -!mulrA. congr (_ *+ _).
  rewrite [_ * (_)%:P]mulrC [((b - a)^-k)%:P * _]mulrA -polyC_mul -invf_mul -exprn_addr.
    by rewrite subnKC // ?(ltnW hlt1) // !mulrA; congr (_ * _); rewrite mulrC.
have -> : (('X - a%:P) ^+ k * ((b - a) ^- k)%:P) = (beta^+k)%:P * (('X - a%:P) ^+ k * ((m - a) ^- k)%:P).
  rewrite /beta exprn_mull polyC_mul expr_inv mulrA [_ * ((m - a)^-k)%:P]mulrC mulrA.
  rewrite -!polyC_mul !mulrA mulVf ?mul1r 1?mulrC // expf_eq0 subr_eq0.
  by move/negPf: dma => ->; rewrite andbF.
rewrite -(expr_inv (b - a)) [(((b - a)^-1)^+_)%:P]polyC_exp -[_^+(p - k) * _]exprn_mull.
have -> : (b%:P - 'X) * ((b - a)^-1)%:P = 
   ((m%:P - 'X) * (m - a)^-1%:P) + (alpha%:P * ('X - a%:P) * (m - a)^-1%:P).
 admit.
rewrite [_^+ (p - k)]exprn_addl /= leq_subS //.
rewrite -(big_mkord (fun _ => true) (fun i => ((m%:P - 'X) * ((m - a)^-1)%:P) ^+ (p - k - i) *
       (alpha%:P * ('X - a%:P) * ((m - a)^-1)%:P) ^+ i *+ 'C(
       p - k, i))).
rewrite  big_distrr /= -sumr_muln; apply: congr_big_nat=> // i; case/andP=> _ hi.
rewrite /dicho' [(i + k)%nat]addnC dc_delta_tail /bernp.
rewrite !mulrnAr polyC_natmul mulrnAl -!mulrnA; congr (_ *+ _); last first.
   rewrite addnC -util_C ?leq_addr //.
     by rewrite mulnC; congr (_ * _)%N;  rewrite addnC addnK.
   by case/andP: hi=> _ ; rewrite ltnS -(leq_add2l k) subnKC.
set Xa := ('X - a%:P); set Xb := (_ - 'X).
rewrite [alpha^+_ * _]mulrC [(beta^+_ * _)%:P]polyC_mul -!mulrA; congr (_ * _).
rewrite [(alpha%:P * _)]mulrC [(_ * alpha%:P)^+i]exprn_mull => {lhs}.
set lhs := (alpha ^+ i)%:P * _; rewrite !mulrA.
rewrite [_ * alpha%:P ^+ i]mulrC /lhs polyC_exp; congr (_ * _)=> {lhs alpha}.
set lhs := _ * (_ * Xb ^+ (p - _)).
rewrite !exprn_mull [Xa^+i * _]mulrC mulrA [_ * Xa^+ _]mulrC !mulrA.
rewrite -exprn_addr /lhs [_ * (Xa^+ _ * _)]mulrA [_ * Xa^+ _]mulrC -!mulrA.
rewrite addnC; congr (_ * _)=> {lhs}.
rewrite !mulrA [_ * Xb^+ (p - k - i)]mulrC -!mulrA [Xb^+ _ * _]mulrC.
rewrite subn_sub; congr (_ * _); rewrite -!polyC_exp -!polyC_mul; congr (_ %:P).
rewrite -!expr_inv -!exprn_addr; congr ((m -a)^-1 ^+ _).
rewrite [(_ + i)%N]addnC. 
rewrite addn_subA.
  by rewrite [(k + i)%N]addnC subn_add2l addnC subnK.
   by case/andP: hi=> _ ; rewrite ltnS -(leq_add2l k) subnKC.
Qed.

Lemma dicho'_correct : forall (a b m : Qcb)(alpha := (b - m) * (b - a)^-1)
  (beta := ((m - a) * (b - a)^-1))(p : nat)(q : {poly Qcb})(c : nat -> Qcb),
  m != a ->
  q = \sum_(i < p.+1)(c i)%:P * bernp a b p i ->
  q = \sum_(j < p.+1)(dicho' alpha beta c j)%:P * bernp a m p j.
Proof.
move=> a b m alpha beta p q c neqma qdef.
have {neqma qdef} -> : q = 
  \sum_(j < p.+1) \sum_(i < p.+1) 
  (c i)%:P * (dicho' alpha beta (delta i) j)%:P * bernp a m p j.
  rewrite exchange_big /= qdef; apply: congr_big; [by [] | by [] |]. 
  case=> k hk _ /=; rewrite (dicho'_delta_bern a b m k p neqma hk).
  rewrite big_distrr /=;  apply: congr_big; [by [] | by [] |]. 
  by case=> i hi _; rewrite !mulrA.
apply: congr_big; [by [] | by [] |]. 
case=> i hi _ /=;  rewrite -big_distrl /=; congr (_ * _).
have -> : dicho' alpha beta c i = 
  dicho' alpha beta (fun k => \sum_(j < p.+1)(c j) * (delta j k)) i.
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
    (0 <= k)%N -> (k <= 0 + i)%N ->  \sum_(j < 1) c j * delta j k = (c 0%N) * (delta 0) k.
    by move=> k _ _; rewrite  big_ord_recl /= big_ord0 addr0.
  by move/ext_dc->; rewrite scal_dc polyC_mul.
  rewrite (_ : f _ _ = 
  f 
  (fun k : nat => 
    (\sum_(j < p.+1) c j * delta j k) + (c p.+1 * delta p.+1 k)) i); last first.
    by apply: ext_dc=> k _; rewrite add0n=> hki; rewrite big_ord_recr.
rewrite /f /dicho' add_dc polyC_add -ihp // big_ord_recr /=; congr (_ + _).
by rewrite scal_dc polyC_mul.
Qed.

Lemma bern_swap :
 forall p i l r, (i <= p)%N -> bernp r l p i = bernp l r p (p - i).
Proof.
move=> p i l r lip; rewrite /bernp subKn // bin_sub //; congr (_ *+ _).
rewrite -[l - r]oppr_sub -[l%:P - 'X]oppr_sub -['X - r%:P]oppr_sub.
rewrite -mulN1r -[-(r%:P - 'X)]mulN1r  -[- ('X - l%:P)]mulN1r.
rewrite !exprn_mull invf_mul polyC_mul [_ * ((r - l)^-p)%:P]mulrC.
rewrite -!mulrA; congr (_ * _).
rewrite  -expr_inv polyC_exp [(- 1)^-1]invrN invr1 polyC_opp.
rewrite [(r%:P - 'X)^+i * _]mulrC !mulrA polyC1 -!exprn_addr.
by rewrite -addnA subnKC // -signr_odd odd_add addbb /= expr0 mul1r.
Qed.

(* This should come after bern_swap ! *)
Lemma bern_rev_coef : forall (p : nat)(a b : Qcb)(c : nat -> Qcb),
  \sum_(i < p.+1)(c i)%:P * (bernp a b p i) = 
  \sum_(i < p.+1)(c (p - i)%N)%:P * (bernp b a p i).
Proof.
move=> p a b c.
pose t := \sum_(i < p.+1) (c (p - i)%N)%:P * bernp a b p (p - i)%N.
transitivity t.
  rewrite (reindex_inj rev_ord_inj) /=; apply/eqP; rewrite -subr_eq0 -sumr_sub.
  by apply/eqP; apply: big1=> [[i hi]] _ /=; rewrite subSS subrr.
apply/eqP; rewrite -subr_eq0 -sumr_sub; apply/eqP; apply: big1=> [[i hi]] _ /=.
by rewrite bern_swap ?subKn ?subrr // leq_subr.
Qed.

 
Lemma dicho_correct : forall (a b m : Qcb)(alpha := (b - m) * (b - a)^-1)
  (beta := ((m - a) * (b - a)^-1))(p : nat)(q : {poly Qcb})(c : nat -> Qcb),
  m != b ->
  q = \sum_(i < p.+1)(c i)%:P * bernp a b p i ->
  q = \sum_(j < p.+1)(dicho alpha beta p c j)%:P * bernp m b p j.
Proof.
move=> a b m alpha beta p q c neqmb qdef.
rewrite bern_rev_coef in qdef.
rewrite (dicho'_correct b a m p q (fun i => c (p - i)%N) neqmb qdef).
rewrite -(big_mkord  
(fun _ => true) (fun j => (dicho' ((a - m) / (a - b)) ((m - b) / (a - b))
         (fun i : nat => c (p - i)%N) j)%:P * bernp b m p j)).
rewrite big_nat_rev /= big_mkord; apply: congr_big; [by [] | by [] |].
move=> [i hi] _ {qdef}; rewrite add0n subSS.
rewrite -bern_swap //; congr (_%:P * _); rewrite /dicho' /dicho.
rewrite dc_reverse //= ?leq_subr // addn0 subKn //.
rewrite -oppr_sub -[a - b]oppr_sub -[a - m]oppr_sub -mulN1r -[-(b - a)]mulN1r.
rewrite -[-(m - a)]mulN1r invf_mul [(- 1)^-1]invrN invr1 -mulrA.
rewrite [(b - m) * _]mulrC !mulrA mulNr mul1r opprK [-1 * _ ]mulrC 2!mulrN1.
by rewrite opprK -/beta mulrC mul1r.
Qed.
