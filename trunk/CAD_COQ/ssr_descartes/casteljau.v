Require Import ssreflect eqtype ssrbool ssrfun ssrnat binomial seq fintype bigops.
Require Import ssralg poly orderedalg.
Require Import  Qcanon.
Require Import infra pol.


Import GRing.

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

(* b gives the coefficients of a polynomial on some bounded interval [a, b].
de_casteljau computest all the coefficients in the triangle for a, m, n, with
l := m - a and r := b - m.

invariant : l + r = b - a *)

Section DeCasteljauAlgo.

Variables l r : Qcb.

Fixpoint de_casteljau (b : nat -> Qcb) (n : nat) :=
  match n with
    O => b
  | S i => fun j => 
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

(* these properties are transmitted to dicho and dicho', is it useful? *)
Lemma add_dicho' :
  forall k b c,
  dicho' (fun j => b j + c j)%R k = (dicho' b k + dicho' c k)%R.
move => k b c; apply: add_dc.
Qed.

Lemma scal_dicho' :
  forall k a b, dicho' (fun j => a * b j)%R k =
    (a * dicho' b k)%R.
move => k a b; apply: scal_dc.
Qed.

End DeCasteljauAlgo.
Open Scope ring_scope.

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

(* algorithme applique a delta_i (colonne 0, ligne j avec j < i)
 
Lemma coef_algo_delta_ligne_infi:
 forall j i A B, (j < i)%nat ->  coef_algo (delta i) A B j 0%nat = 0.
induction j; intros; simpl.
rewrite delta_ij; intuition.
rewrite IHj; intuition.
rewrite coef_algo_delta_ligne_infi_k; intuition.
ring.

Qed.
*)

(* algorithme applique a delta_i (colonne 0, ligne i + k )*) 
(*Lemma coef_algo_delta_ligne_sup_i:*)

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
 

Definition bernp (a b : Qcb) p i : {poly Qcb} := 
  ((b - a)^-p)%:P * ('X - a%:P)^+i * (b%:P - 'X)^+(p - i) *+ 'C(p, i).


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

Lemma bern_rev_coef : forall (p : nat)(a b : Qcb)(c : nat -> Qcb),
  \sum_(i < p.+1)(c i)%:P * (bernp a b p i) = 
  \sum_(i < p.+1)(c (p - i)%N)%:P * (bernp b a p i).
Proof.
move=> p a b c.
rewrite -(big_mkord  
(fun _ => true)
(fun i => (c i)%:P * (bernp a b p i))).
rewrite big_nat_rev /=.
rewrite -(big_mkord  
(fun _ => true)
(fun i => (c (p - i)%N)%:P * (bernp b a p i))).
apply: congr_big_nat; [by [] | by [] | by [] |].
move=> i; case=> ltip; rewrite add0n subSS; congr (_ * _).
rewrite /bernp subKn // bin_sub //; congr (_ *+ _).
rewrite -!mulrA -[b - a]oppr_sub -[a%:P - 'X]oppr_sub -['X - b%:P]oppr_sub.
rewrite -mulN1r -[-(b%:P - 'X)]mulN1r  -[- ('X - a%:P)]mulN1r.
rewrite !exprn_mull invf_mul polyC_mul [_ * ((a - b)^-p)%:P]mulrC.
rewrite -mulrA; congr (_ * _).
rewrite  -expr_inv polyC_exp [(- 1)^-1]invrN invr1 polyC_opp.
rewrite polyC1 -{1}(@subnK i p) // addnC exprn_addr -!mulrA.
congr (_ * _); rewrite !mulrA [(b%:P - _)^+_ * _]mulrC -!mulrA.
by congr (_ * _); rewrite mulrC.
Qed.



Lemma dicho_delta_bern : forall a b m k p (alpha := (b - m) * (b - a)^-1)(beta := ((m - a) * (b - a)^-1)),
  m != a ->
  (k <= p)%nat -> 
  bernp a b p k = 
  \sum_(j < p.+1)((dicho alpha beta p (delta k) j)%:P * bernp m b p j).
Proof.
move=> a b m k p alpha beta neqma leqkp.
rewrite bern_rev_coef /dicho.
rewrite (dicho'_delta_bern _ b _ _ _ neqma leqkp).
apply: congr_big; [by [] | by [] |].
case=> i ltiSp _ /=; rewrite /dicho' subKn; last by [].
rewrite /alpha.
Admitted.









Lemma reduced_de_casteljau_correct : forall n k (p : {poly Qcb})(a b m : Qcb), 
  (k < n)%nat ->
  p = \sum_(i < n) ((delta k) i)%:P * (bernp a b n i) ->
  p = 
  \sum_(i < n) 
  (dicho' (m - a) (b - m) (delta k) i)%:P * (bernp a b n i).
Proof.
Admitted.