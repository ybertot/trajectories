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
  de_casteljau A B (delta i) (i + k)%nat 0 = ((Qbin (k + i) i) * A ^+ k) * B ^+ i.
Proof.
elim=> [|i ihi] k A B /=; rewrite -?addnE.
  rewrite add0n addn0 /= expr0 mulr1 /Qbin bin0 dcn_deltan.
  rewrite (_ :  Qcb_make _ = 1) ?mul1r //.
  by apply: val_inj.
rewrite dc_deltaS ihi.
elim: k => [|k ihk] /=.
  rewrite !add0n !expr0 !mulr1 !addn0 dc_delta_gt ?mulr0 ?add0r 1?mulrC ?subSnn //.
  rewrite /Qbin !binn (_ :  Qcb_make _ = 1) ?mul1r //; last by apply: val_inj.
  by rewrite mulrC exprS.
rewrite !addnS /= dc_deltaS ihi ihk !addnS !addSn {3}/Qbin.
rewrite binS Znat.inj_plus  Qcb_makeadd -/(Qbin (k + i).+1 _) -/(Qbin _ i).
rewrite -[(_ + _) * _ * _]mulrA mulr_addl; congr (_ + _).
  by rewrite mulrC -2!mulrA; congr (_ * _); rewrite mulrC mulrA (exprS A _).
by rewrite mulrC (exprS B) [B * _]mulrC !mulrA.
Qed.
 

Definition bernp (a b : Qcb) p i : {poly Qcb} := 
  (Qbin p i)%:P * ((b - a)^-p)%:P * ('X - a%:P)^+i * (b%:P - 'X)^+(p - i).

Lemma dichobern : forall a b m k p,
  m != a ->
  (k <= p)%nat -> 
  bernp a b p k = 
  \sum_( 0 <= j < p.+1)((dicho' (m - a) (b - m) (delta k) j)%:P * bernp a m p j).
Proof.
move=> a b m k p  dma hlt1.
rewrite (big_cat_nat _ _ _ (leq0n k)) //=; last by apply: leq_trans hlt1 _; exact: leqnSn.
rewrite (_ : \sum_( _ <= i0 < _ ) _ = 0) /= ?add0r; last first.
  rewrite big1_seq //= => j; rewrite mem_iota add0n subn0; case/andP=> _ h.
  by rewrite dc_delta_head // polyC0 mul0r.
rewrite -{2}(add0n k) big_addn.
have h : forall i0, (0 <= i0 < p - k)%nat -> 
  (dicho' (m - a) (b - m) (delta k) (i0 + k))%:P * bernp a m p (i0 + k) = 
   (((Qbin (i0 + k) k) * (m - a) ^+ i0) * (b - m) ^+ k)%:P * bernp a m p (i0 + k).
  by move=> j hj; congr (_ * _); rewrite addnC /dicho' dc_delta_tail addnC.

pose alpha := (b - m) / (b - a).
pose beta := (m - a) / (b - a).
have -> : bernp a b p k = 
                        (Qbin p k)%:P * 
                        (('X - a%:P)^+k * ((b - a)^-k)%:P) * 
                        ((b%:P  - 'X )^+(p - k) * ((b - a)^-(p - k))%:P).
  rewrite /bernp -!mulrA; congr (_ * _).
  rewrite [_ * (_)%:P]mulrC [((b - a)^-k)%:P * _]mulrA -polyC_mul -invf_mul -exprn_addr.
    by rewrite subnKC // ?(ltnW hlt1) // !mulrA; congr (_ * _); rewrite mulrC.
have -> : (('X - a%:P) ^+ k * ((b - a) ^- k)%:P) = (beta^+k)%:P * (('X - a%:P) ^+ k * ((m - a) ^- k)%:P).
  rewrite /beta exprn_mull polyC_mul expr_inv mulrA [_ * ((m - a)^-k)%:P]mulrC mulrA.
  rewrite -!polyC_mul !mulrA mulVf ?mul1r 1?mulrC // expf_eq0 subr_eq0.
  by move/negPf: dma => ->; rewrite andbF.
rewrite -(expr_inv (b - a)) [(((b - a)^-1)^+_)%:P]polyC_exp -[_^+(p - k) * _]exprn_mull.
have -> : (b%:P - 'X) * ((b - a)^-1)%:P = 
   (m%:P - 'X) * (m - a)^-1%:P + alpha%:P * ('X - a%:P) * (m - a)^-1%:P.
 admit.
rewrite [_^+ (p - k)]exprn_addl /= leq_subS // big_distrr /=.
Admitted.














(*ouput de delta i*)
 
Theorem output_delta_infi:
 forall i j A B, (j < i)%nat ->  output (delta i) A B j = 0.
intros; unfold output.
rewrite coef_algo_delta_ligne_infi; auto.
Qed.
 
Theorem output_delta_supi:
 forall i j A B,
 (j >= i)%nat ->  output (delta i) A B j = (C j i * A ^ (j - i)) * B ^ i.
intros; unfold output.
pattern j at 1.
NReplace j (i + (j - i))%nat.
rewrite (coef_algo_delta_ligne_sup_i i (j - i)).
NReplace ((j - i) + i)%nat j; auto.
Qed.



















Lemma reduced_de_casteljau_correct : forall n k (p : {poly Qcb})(a b m : Qcb), 
  (k < n)%nat ->
  p = \sum_(i < n) ((delta k) i)%:P * (bernp a b n i) ->
  p = 
  \sum_(i < n) 
  (dicho' (m - a) (b - m) (delta k) i)%:P * (bernp a b n i).
Proof.
Admitted.