Require Import ssreflect eqtype ssrbool ssrfun ssrnat binomial seq fintype bigops.
Require Import ssralg poly orderedalg.
Require Import infra pol.

Import GRing.

Lemma util_C : forall n i j : nat, i <= j -> j <= n -> 
    'C(n, i) * 'C(n-i, j-i) = 'C(j, i) * 'C(n, j).
move => n i j ij jn.
apply/eqP; rewrite -(@eqn_pmul2r ( i`! * (n - i) `!));
  last by rewrite muln_gt0; apply/andP; split; apply: fact_gt0.
rewrite -(@eqn_pmul2r ((j - i)`! * ((n - i)-(j - i))`!)); last first.
  by rewrite muln_gt0; apply/andP; split; apply: fact_gt0.
have ilen : i <= n by apply: leq_trans jn.
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

Fixpoint de_casteljau (b : nat -> Qcb) n :=
  match n with
    0 => b
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
  forall k b b' n, (forall i, n <= i -> i <= n + k -> b i = b' i) ->
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

Definition bernp (a b : Qcb) p i : {poly Qcb} := 
  ((Qbin p i)* (b - a)^-1)%:P * ('X - a%:P)^+i * ('X - b%:P)^+(p - i).

Definition delta (i j : nat) : Qcb := if (i == j) then 1 else 0.

Lemma dc__delta_head : forall j k l r, 
  (j < k)%nat -> dicho' l r (delta k) j = 0.
Proof.
rewrite /dicho' => j k l r hlt.
pose d0 := fun _ : nat => 0 : Qcb.
rewrite (ext_dc _ _ _ _ d0); last first.
  move=> i; rewrite add0n => h1 h2; rewrite /delta.
  have : (i < k)%nat by apply: leq_ltn_trans hlt.
  by rewrite ltn_neqAle; case/andP; rewrite eq_sym; move/negPf->.
elim:  j {hlt} 0%nat=> [| j ihj n] /=; first by done.
by rewrite !ihj !mulr0 addr0.
Qed.


Lemma reduced_de_casteljau_correct : forall n k (p : {poly Qcb})(a b m : Qcb), 
  (k < n)%nat ->
  p = \sum_(i < n) ((delta k) i)%:P * (bernp a b n i) ->
  p = 
  \sum_(i < n) 
  (dicho' (m - a) (b - m) (delta k) i)%:P * (bernp a b n i).
Proof.
Admitted.