Require Import ssreflect eqtype ssrbool ssrfun ssrnat binomial.
Require Import ssralg orderedalg.
Require Import infra.
Import GRing.

Lemma util_C : forall n i j, i <= j -> j <= n -> 
    'C(n, i) * 'C(n-i, j-i) = 'C(j, i) * 'C(n, j).
move => n i j ij jn.
apply/eqP; rewrite -(@eqn_pmul2r ( i`! * (n - i) `!));
  last by rewrite muln_gt0; apply/andP; split; apply: fact_gt0.
rewrite -(@eqn_pmul2r ((j - i)`! * ((n - i)-(j - i))`!));
  last by rewrite muln_gt0; apply/andP; split; apply: fact_gt0.
have ilen : i <= n by apply: leq_trans jn.
rewrite (mulnAC 'C(n, i)) -mulnA !bin_fact //; last by apply: leq_sub2r.
rewrite !mulnA (mulnAC _ _ (i`!)) 2!(mulnAC _ _ ((j-i)`!)) -(mulnA 'C(j, i)).
rewrite bin_fact // subn_sub subnKC // mulnAC (mulnC j`!) -(mulnA _ j`!).
rewrite bin_fact //.
Qed.

Fixpoint de_casteljau (b : nat -> Q_oRingType) (l r : Q_oRingType) n :=
  match n with
    0 => b
  | S i => fun j => 
    (l * de_casteljau b l r i j + r * de_casteljau b l r i (j + 1)%nat)%R
  end.

Definition dicho' b l r i := de_casteljau b l r i 0.

Definition dicho p b l r i := de_casteljau b l r (p - i) i.

Lemma ext_dc :
  forall k b b' l r n, (forall i, n <= i -> i <= n + k -> b i = b' i) ->
  de_casteljau b l r k n = de_casteljau b' l r k n.
move => k b b' l r; elim: k => [ n q | k IHk n q] /=.
  by apply: q; rewrite ?addn0 leqnn.
rewrite !IHk; first done; move => i ni nik; apply: q.
Qed.

Lemma lin_dc :
  forall k a a' b b' l r n,
    de_casteljau (fun j => (a * b j + a' * b' j)%R) l r k n =
    (a * de_casteljau b l r k n + a' * de_casteljau b' l r k n)%R.
move => k; elim: k => [ | k IHk] a a' b b' l r n /= ; first done.
rewrite 2!IHk !mulr_addr !mulrA !(mulrC r) !(mulrC l) !addrA.
by rewrite (addrAC _ _ (a' * l * _)%R).
Qed.

Lemma add_dc :
  forall k b b' l r n, de_casteljau (fun j => b j + b' j)%R l r k n =
     (de_casteljau b l r k n + de_casteljau b' l r k n)%R.
move => k b b' l r n; have := lin_dc k 1 1 b b' l r n.
rewrite (ext_dc k (fun j => 1 * b j + 1 * b' j) (fun j => b j + b' j))%R.
  by rewrite !mul1r.
by move => x; rewrite /= !mul1r.
Qed.

Lemma scal_dc :
  forall k a b l r n, de_casteljau (fun j => a * b j)%R l r k n =
      (a * de_casteljau b l r k n)%R.
move => k a b l r n; have := lin_dc k a 0 b (fun i => 0)%R l r n.
rewrite (ext_dc _ (fun j => a * b j + 0 * 0)%R (fun j => a * b j)%R).
  by rewrite mul0r addr0.
by move => x; rewrite /= mul0r addr0.
Qed.

Lemma add_dicho' :
  forall k b c l r,
  dicho' (fun j => b j + c j)%R l r k = (dicho' b l r k + dicho' c l r k)%R.
move => k b c l r; apply: add_dc.
Qed.

Lemma scal_dicho' :
  forall k a b l r, dicho' (fun j => a * b j)%R l r k =
    (a * dicho' b l r k)%R.
move => k a b l r; apply: scal_dc.
Qed.


