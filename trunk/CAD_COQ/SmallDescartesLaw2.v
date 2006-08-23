Require SmallDescartesLaw.
Import Setoid.
Import ZArith.
Import Omega.
Import CAD_types.
Import Utils.
Import NArith.
Import Zwf.
Import QArith.
Import Qring.
Import Pol_ring2.
Import Qnorm.
Import SmallDescartesLaw.

Axiom copp_div_l :
  forall x y, copp x / y == copp (x / y).

Axiom clt_0_copp : forall x, x < c0 -> c0 < --x.

Axiom clt_0_plus_compat :
 forall x y, c0 < x -> c0 < y -> c0 < x ++ y.

Axiom clt_0_le_lt_plus_compat :
 forall x y, c0 <= x -> c0 < y -> c0 < x ++ y.


Axiom cplus_le_lt_compat :
  forall x y z t, x <= y -> z < t -> x++z < y++t.

Axiom cmul_lt_compat_r :
  forall x y z, c0 < z -> x < y -> x**z < y**z.

Axiom clt_le_trans : forall x y z, x < y -> y <= z -> x < z.

Axiom cle_lt_trans : forall x y z, x <= y -> y < z -> x < z.

Axiom clt_0 : forall x, c0 < copp x -> x < c0.

Axiom cplus_lt_compat_r :
  forall x y z, x < y -> x++z < y++z.

Theorem cplus_lt_r :
   forall x y, c0 < y -> x < x++y.
intros; apply clt_decompose.
intros Ha; elim (pos_non_c0 _ H).
setoid_replace c0 with ((x++y)--x).
setoid ring.
setoid_rewrite <- Ha; setoid ring.
setoid_rewrite cadd_sym.
apply cplus_pos_simplify.
apply clt_cle_weak; auto.
Qed.

Theorem Horner_step_positive_tech :
  forall r a Q, a < c0 -> 
  (forall x y, r < x -> x <= y -> 
           c0 < Pol_eval Q x /\ Pol_eval Q x <= Pol_eval Q y) ->
         r < r++c1 -- a/Pol_eval Q (r++c1).
intros r a Q Ha Hq.
setoid_replace (r ++ c1 -- a / Pol_eval Q (r ++ c1)) with
   (r++(c1 ++ (-- a / Pol_eval Q (r ++ c1)))).
apply cplus_lt_r.
apply clt_0_plus_compat.
apply c0_clt_c1.
apply cdiv_lt_0_compat_l.
assert (Hr1 : r < r++c1).
apply cplus_lt_r.
apply c0_clt_c1.
assert (Hq' := Hq (r++c1) (r++c1) Hr1 (cle_refl (r++c1))).
intuition;fail.
apply clt_0_copp; assumption.
setoid_rewrite copp_div_l.
setoid ring.
Qed.

Theorem Horner_step_positive :
forall a Q, a < c0 -> forall r, c0 <= r ->
  (forall x y, r < x -> x <= y -> 
           c0 < Pol_eval Q x /\ Pol_eval Q x <= Pol_eval Q y) ->
  c0 < Pol_eval (Pc a + X *Q)(r++c1--a/Pol_eval Q (r++c1)).
intros a Q Halt0 r Hrpos HQincr.
assert (Hb1: r < r++c1).
apply cplus_lt_r;apply c0_clt_c1.
assert (Hb2:= cle_refl (r++c1)).
assert (HQr1 := HQincr (r++c1) (r++c1) Hb1 Hb2).
assert (Hpos' : c0 < r++c1 -- a/Pol_eval Q (r++c1)).
apply cle_lt_trans with r.
assumption.
apply Horner_step_positive_tech; assumption.

apply clt_le_trans with (a++ (r ++ c1 -- a / Pol_eval Q (r ++ c1))**
                          (Pol_eval Q (r++c1))).
setoid_replace 
  (a ++ (r ++ c1 -- a / Pol_eval Q (r ++ c1)) ** Pol_eval Q (r ++ c1))
with
  ((r++c1)**Pol_eval Q (r++c1) ++ a --
        (Pol_eval Q (r++c1)** (a/Pol_eval Q (r++c1))));
  [idtac | setoid ring;fail].
setoid_rewrite cmul_div_r.
apply pos_non_c0;intuition.
match goal with |- _ < ?x => 
  setoid_replace x with ((r ++ c1) ** Pol_eval Q (r ++ c1));[idtac|setoid ring]
end.
apply cmul_lt_0.
apply cle_lt_trans with r; assumption.
intuition;fail.
setoid_rewrite Pol_eval_plus.
setoid_rewrite Pol_eval_c.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_X.
apply cplus_le_compat.
apply cle_refl.
repeat setoid_rewrite (cmul_sym (r ++ c1 -- a / Pol_eval Q (r ++ c1))).
apply cmul_le_compat_r.
assert (Hb3 : r++c1<=r++c1 --a/Pol_eval Q (r++c1)).
setoid_replace (r++c1 --a/Pol_eval Q (r++c1)) with
  (--(a/Pol_eval Q (r++c1))++(r++c1));[idtac |setoid ring].
apply cplus_pos_simplify; apply clt_cle_weak.
setoid_rewrite <- copp_div_l.
apply cdiv_lt_0_compat_l.
intuition;fail.
apply clt_0_copp; assumption.
assert (HQi' := HQincr (r++c1)(r++c1--a/Pol_eval Q (r++c1)) Hb1 Hb3).
intuition;fail.
apply clt_cle_weak; assumption.
Qed.

Theorem no_alternation_tech :
  forall Q a, a < c0 -> c0 < least_non_zero_coeff Q -> no_alternation Q ->
  c0 < c1 -- a / Pol_eval Q c1.
intros Q a Haneg Hqpos Hna.
assert (HQpos' : 0 < Pol_eval Q c1).
apply no_alternation_positive_strict.
assumption.
assumption.
apply c0_clt_c1.
apply clt_trans with (c1 ++ c0).
setoid_rewrite cadd_0_r.
apply c0_clt_c1.
setoid_replace (c1 -- a/Pol_eval Q c1) with (c1 ++ (-- (a/Pol_eval Q c1))).
apply cplus_le_lt_compat.
apply cle_refl.
setoid_rewrite <- copp_div_l.
apply cdiv_lt_0_compat_l.
assumption.
apply clt_0_copp.
assumption.
setoid ring.
Qed.

Theorem alternation_here_root :
  forall Q a, a < c0 -> c0 < least_non_zero_coeff Q ->
    no_alternation Q ->
    (exists r, c0 < r /\ Pol_eval (Pc a + X * Q) r < c0 /\
      exists r2, r < r2 /\ c0 < Pol_eval (Pc a + X * Q) r2 /\
      (forall x y, r < x -> x < y ->
               Pol_eval (Pc a + X * Q) x < Pol_eval (Pc a + X * Q) y)).
intros Q a Haneg HQpos Hna.
destruct (Pol_eval_continuous (Pc a + X*Q) c0 (-- a/(c1++c1))) as [r [Hrp Hr]].
apply cdiv_lt_0_compat_l;[apply c0_clt_2 | apply clt_0_copp; assumption].
exists r.
split.
assumption.
split.
apply cle_lt_trans with (a/(c1++c1)).
setoid_replace (a/(c1++c1)) with (a ++ -- a/(c1++c1)).
pose (u:= Pol_eval (Pc a + X * Q) c0).
setoid_replace (Pol_eval (Pc a + X * Q) r) with
   (Pol_eval (Pc a + X * Q) c0 ++
   (Pol_eval (Pc a + X * Q) r -- u)).
setoid_replace (Pol_eval (Pc a + X * Q) c0) with a.
apply cplus_le_compat.
apply cle_refl.
unfold u.
assert (Hrin: --r <= r--c0 <= r).
setoid_replace (r -- c0) with r.
split.
apply cle_trans with c0.
apply copp_le_0_compat.
apply clt_cle_weak; auto.
apply clt_cle_weak; auto.
apply cle_refl.
setoid ring.
assert (Hr' := Hr r Hrin).
intuition; fail.
setoid_rewrite Pol_eval_plus.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_c.
setoid_rewrite Pol_eval_X.
setoid ring.
unfold u; setoid ring.
setoid_replace (a++ --a/(c1++c1)) with (a -- a/(c1++c1)).
pose (u:= a/(c1++c1)); fold u.
setoid_rewrite (cut_half a).
unfold u; setoid ring.
setoid_rewrite copp_div_l.
setoid ring.
apply clt_0.
setoid_rewrite <- copp_div_l.
apply cdiv_lt_0_compat_l.
apply c0_clt_2.
apply clt_0_copp.
assumption.

exists (r++c1--a/Pol_eval Q (r++c1)).
assert(tech_hyp:   forall x y : Coef,
   r < x -> x <= y -> c0 < Pol_eval Q x /\ Pol_eval Q x <= Pol_eval Q y).
intros x y Hx Hy.
split.
apply no_alternation_positive_strict.
assumption.
assumption.
apply clt_trans with r; assumption.
assert (Hinc := no_alternation_increasing Q (clt_cle_weak _ _ HQpos) Hna x y).
assert (c0 <= x <= y).
split;[apply cle_trans with r;apply clt_cle_weak; assumption| assumption].
intuition; fail.

split.
apply Horner_step_positive_tech.
assumption.
assumption.
split.
setoid_rewrite Pol_eval_plus.
setoid_rewrite Pol_eval_c.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_X.
apply clt_le_trans with (a ++ (r ++ c1 -- a / Pol_eval Q (r ++ c1)) **
                        (Pol_eval Q (r++c1))).
setoid_replace (a ++ (r ++ c1 -- a / Pol_eval Q (r ++ c1)) ** Pol_eval Q (r ++ c1)) with
   (a ++ ((r++c1)**Pol_eval Q (r++c1))++(Pol_eval Q (r++c1)**(--a/Pol_eval Q (r++c1)))).
assert (Hr1: c0 < r++c1).
apply clt_0_plus_compat.
assumption.
apply c0_clt_c1.
assert (H := no_alternation_positive_strict Q Hna HQpos (r++c1) Hr1).
setoid_rewrite cmul_div_r.
apply pos_non_c0; intuition;fail.

match goal with |- _ < ?u => 
   setoid_replace u with ((r++c1)**Pol_eval Q (r++c1))
end.
apply cmul_lt_0; assumption.
setoid ring.
setoid_rewrite copp_div_l.
setoid ring.
apply cplus_le_compat.
apply cle_refl.
repeat setoid_rewrite (cmul_sym (r ++ c1 -- a / Pol_eval Q (r ++ c1))).
apply cmul_le_compat_r.
assert (r < r++c1) by (apply cplus_lt_r; apply c0_clt_c1).
assert (r++c1 < r++c1 -- a/Pol_eval Q (r++c1)).
setoid_replace (r ++ c1 -- a/Pol_eval Q (r++c1)) with
  ((r++c1) ++(-- a/Pol_eval Q (r++c1))).
apply cplus_lt_r.
apply cdiv_lt_0_compat_l.
apply no_alternation_positive_strict.
assumption.
assumption.
apply clt_trans with r; assumption.
apply clt_0_copp; assumption.
setoid_rewrite copp_div_l.
setoid ring.
assert (H' := tech_hyp _ _ H (clt_cle_weak _ _ H0)).
intuition;fail.
apply cle_trans with r.
apply clt_cle_weak; assumption.
apply clt_cle_weak; apply Horner_step_positive_tech.
assumption.
assumption.
intros x y Hx Hy.
repeat setoid_rewrite Pol_eval_plus.
repeat setoid_rewrite Pol_eval_c.
repeat setoid_rewrite Pol_eval_mult.
repeat setoid_rewrite Pol_eval_X.
apply cplus_le_lt_compat.
apply cle_refl.
apply cle_lt_trans with (x**Pol_eval Q y).
repeat setoid_rewrite (cmul_sym x); apply cmul_le_compat_r.
assert (H' := tech_hyp x y Hx (clt_cle_weak _ _ Hy)); intuition; fail.
apply cle_trans with r;apply clt_cle_weak; assumption.
apply cmul_lt_compat_r.
assert (H' := tech_hyp x y Hx (clt_cle_weak _ _ Hy)).
apply clt_le_trans with (Pol_eval Q x);intuition;fail.
assumption.
Qed.

(* This is the point where we have a departure from purely constructive
 mathematics.  The statement of this polynom can still be proved in
 constructive mathematics (I think so), but it is also easy to prove
 using classical mathematics, which should make it possible to go much
 faster. *)
Axiom intermediate_value_polynom :
   forall P a b, Pol_eval P a < c0 -> c0 < Pol_eval P b -> a < b ->
   forall eps, exists x, exists y,
        a <= x /\ x < y /\ y <= b /\ --eps < Pol_eval P x  /\
         Pol_eval P x <= c0 /\ c0 < Pol_eval P y /\ Pol_eval P y < eps /\
         y--x < eps.

Lemma neg_cmul_n0 :  forall a b, a ** b < c0 -> ~a==c0.
intros a b H Heq; elim (clt_neq _ _ H).
setoid_replace (a ** b) with c0.
apply ceq_refl.
setoid_rewrite Heq; setoid ring.
Qed.

Lemma cle_0 : forall a, c0 <= -- a -> a <= c0.
intros; setoid_replace c0 with (--a ++ a).
apply cplus_pos_simplify.
assumption.
setoid ring.
Qed.

Lemma neg_cmul_neg_l : forall a b, a**b < c0 -> c0 < b -> a < c0.
intros a b Hm Hb; apply clt_0.
apply clt_decompose.
intros Habs; apply (neg_cmul_n0 _ _ Hm).
setoid_replace c0 with (--a ++ a).
setoid_rewrite <- Habs;setoid ring.
setoid ring.
apply cmul_lt_0_le_reg_r with b.
assumption.
setoid_rewrite mul_copp.
setoid_replace (c0**b) with c0.
apply cle_0_copp; apply clt_cle_weak; assumption.
setoid ring.
Qed.

Lemma neg_cmul_pos_r : forall a b, a**b < c0 -> a < c0 -> c0 < b.
intros a b Hm Hb; apply clt_decompose.
assert (b**a < c0).
setoid_rewrite cmul_sym in Hm; assumption.
intros Habs; elim (neg_cmul_n0 _ _ H);setoid_rewrite Habs;auto.
apply cmul_lt_0_le_reg_r with (--a).
apply clt_0_copp; assumption.
setoid_rewrite cmul_0_l; setoid_rewrite cmul_sym; setoid_rewrite mul_copp.
apply clt_cle_weak; apply clt_0_copp; assumption.
Qed.

Lemma cmul_lt_0_lt_reg_r: 
   forall x y z : Coef, c0 < z -> x ** z < y ** z -> x < y.
intros; apply clt_decompose.
intros Habs; elim (clt_neq _ _ H0); setoid_rewrite Habs; auto.
apply cmul_lt_0_le_reg_r with z.
assumption.
apply clt_cle_weak; assumption.
Qed.

Theorem clt_0_inv_pow : forall x n, c0 < x -> c0 < c1/cpow x n.
intros.
apply cdiv_lt_0_compat_l.
apply cpow_lt_0_compat_l; assumption.
apply c0_clt_c1.
Qed.

Lemma inv_clt : forall x y, c0 < x -> x < y -> c1/y < c1/x .
intros x y Hx Hy.
apply cmul_lt_0_lt_reg_r with (x**y).
apply cmul_lt_0.
assumption.
apply clt_trans with x; assumption.
setoid_replace (c1/y**(x**y)) with (x ** (y**(c1/y))).
setoid_rewrite cmul_div_r.
apply pos_non_c0; apply clt_trans with x; assumption.
setoid_rewrite cmul_1_r.
setoid_replace (c1/x**(x**y)) with (y**(x**(c1/x))).
setoid_rewrite cmul_div_r.
apply pos_non_c0; assumption.
setoid_rewrite cmul_1_r.
assumption.
setoid ring.
setoid ring.
Qed.

Lemma inv_cle : forall x y, c0 < x -> x <= y -> c1/y <= c1/x.
intros x y Hx Hy; elim (ceq_dec x y).
intros Heq; apply cmul_lt_0_le_reg_r with (x**y).
apply cmul_lt_0.
assumption.
apply clt_le_trans with x; assumption.
setoid_replace (c1/y**(x**y)) with (x ** (y**(c1/y))).
setoid_rewrite cmul_div_r.
apply pos_non_c0; apply clt_le_trans with x; assumption.
setoid_rewrite cmul_1_r.
setoid_replace (c1/x**(x**y)) with (y**(x**(c1/x))).
setoid_rewrite cmul_div_r.
apply pos_non_c0; assumption.
setoid_rewrite cmul_1_r.
setoid_rewrite Heq; apply cle_refl.
setoid ring.
setoid ring.
intros Hn.
apply clt_cle_weak.
apply inv_clt.
assumption.
apply clt_decompose; assumption.
Qed.


Lemma cle_opp_div_r : forall a b c, c0 <= a -> c0 < b -> b <= c ->
  --(a/b) <= --(a/c).
intros a b c Ha Hb Hc; apply copp_le_compat.
repeat setoid_rewrite (cdiv_decompose a).
apply pos_non_c0; apply clt_le_trans with b; assumption.
apply pos_non_c0; assumption.
apply cmul_le_compat_r.
apply inv_cle; assumption.
assumption.
Qed.

Lemma cle_div_r : forall a b c, c0 <= a -> c0 < c -> c <= b ->
  a/b <= a/c.
intros a b c Ha Hb Hc.
repeat setoid_rewrite (cdiv_decompose a).
apply pos_non_c0; apply clt_le_trans with c; assumption.
apply pos_non_c0; assumption.
apply cmul_le_compat_r.
apply inv_cle; assumption.
assumption.
Qed.


Lemma cmul_neg_compat_l :
  forall a b, a <= c0 -> c0 <= b -> a**b <= c0.
intros a b Ha Hb; apply cle_0.
setoid_rewrite <- mul_copp.
apply cle_0_mult.
apply cle_0_copp; assumption.
assumption.
Qed.

Lemma cmul_neg_compat_r :  forall a b, c0 <= a -> b <= c0 -> a**b <= c0.
intros; setoid_rewrite cmul_sym; apply cmul_neg_compat_l; assumption.
Qed.

Theorem cmul_lt_compat : forall x y z t,
   c0 < x -> x < y -> c0 < z -> z < t ->  x ** z < y ** t.
intros x y z t Hx Hy Hz Ht.
apply clt_trans with (y**z).
apply cmul_lt_compat_r; assumption.
repeat setoid_rewrite (cmul_sym y).
apply cmul_lt_compat_r.
apply clt_trans with x; assumption.
assumption.
Qed.

Lemma cmul_lt_neg_r :
  forall x y, c0 < x -> y < c0 -> x**y < c0.
intros; setoid_rewrite (cmul_sym x).
setoid_replace c0 with (c0 ** x).
apply cmul_lt_compat_r;assumption.
setoid ring.
Qed.

Theorem cplus_lt_reg_r :
  forall x y z, x ++ z < y ++ z -> x < y.
intros.
setoid_replace x with ((x++z)++(--z));[idtac|setoid ring].
setoid_replace y with ((y++z)++(--z));[idtac|setoid ring].
apply cplus_lt_compat_r; assumption.
Qed.

Lemma csub_le_0 :
   forall a b, a <= b -> c0 <= b--a.
intros; setoid_replace (b--a) with (b++--a).
setoid_replace c0 with (a++--a).
apply cplus_le_compat.
assumption.
apply cle_refl.
setoid ring.
setoid ring.
Qed.

Lemma csub_lt_0 :
   forall a b, a < b -> c0 < b--a.
intros; setoid_replace (b--a) with (b++--a).
setoid_replace c0 with (a++--a).
apply cplus_lt_compat_r.
assumption.
setoid ring.
setoid ring.
Qed.

(*
Theorem increase_pol_close_0_X : 
   forall Q a r,
     c0 < r ->
     (forall x, r <= x -> c0 < Pol_eval Q x) ->
     (forall x y, r <= x -> x <= y -> Pol_eval Q x <= Pol_eval Q y) ->
     --(r**Pol_eval Q r) < Pol_eval (Pc a + X * Q) r ->
     forall x y, r <= x -> x < y -> 
        Pol_eval (X*(Pc a + X*Q)) x < Pol_eval (X*(Pc a +X*Q)) y.
intros Q a r Hr HQp HQi Hclose x y Hx Hy.
repeat (setoid_rewrite Pol_eval_mult || setoid_rewrite Pol_eval_plus ||
        setoid_rewrite Pol_eval_c || setoid_rewrite Pol_eval_X).

setoid_replace (y**(a++y**Pol_eval Q y)) with
  (x**(a++x**Pol_eval Q x) ++ 
   ((y--x)**((a++x**Pol_eval Q x)++(y**Pol_eval Q y))++
    y**x**(Pol_eval Q y --Pol_eval Q x)));[idtac |setoid ring;fail].
apply cplus_lt_r.
setoid_rewrite cadd_sym.
apply clt_0_le_lt_plus_compat.
apply cmul_le_0.
apply cmul_le_0.
apply clt_cle_weak; apply clt_trans with r.
assumption.
apply cle_lt_trans with x; assumption.
apply clt_cle_weak; apply clt_le_trans with r; assumption.
apply csub_le_0.
apply HQi.
assumption.
apply clt_cle_weak; assumption.
apply cmul_lt_0.
apply csub_lt_0; auto.
apply cle_lt_trans with (--(r**Pol_eval Q r)++r**Pol_eval Q r).
setoid_replace (-- (r ** Pol_eval Q r) ++ r ** Pol_eval Q r) with c0.
apply cle_refl.
setoid ring.
apply cplus_le_lt_compat.
apply cle_trans with (Pol_eval (Pc a + X*Q) r).
apply clt_cle_weak; assumption.
setoid_rewrite Pol_eval_plus; setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_c; setoid_rewrite Pol_eval_X.
apply cplus_le_compat.
apply cle_refl.
apply cle_trans with (r**Pol_eval Q x).
repeat setoid_rewrite (cmul_sym r).
apply cmul_le_compat_r.
apply HQi.
apply cle_refl.
assumption.
apply clt_cle_weak; assumption.
apply cmul_le_compat_r.
assumption.
apply clt_cle_weak.
apply HQp; assumption.
apply cle_lt_trans with (r**Pol_eval Q y).
repeat setoid_rewrite (cmul_sym r).
apply cmul_le_compat_r.
apply HQi.
apply cle_refl.
apply clt_cle_weak; apply cle_lt_trans with x; assumption.
apply clt_cle_weak; assumption.
apply cmul_lt_compat_r.
apply HQp.
apply clt_cle_weak; apply cle_lt_trans with x; assumption.
apply cle_lt_trans with x; assumption.
Qed.

Theorem increase_pol_close_0_Xn : 
   forall Q a r n,
     c0 < r ->
     (forall x, r <= x -> c0 < Pol_eval Q x) ->
     (forall x y, r <= x -> x <= y -> Pol_eval Q x <= Pol_eval Q y) ->
     --(r**Pol_eval Q r) < Pol_eval (Pc a + X * Q) r ->
     forall x y, r <= x -> x < y -> 
        Pol_eval (X^n*(Pc a + X*Q)) x < Pol_eval (X^n*(Pc a +X*Q)) y.
intros Q a r n Hr HQp HQi Hclose x y Hx Hy .
repeat setoid_rewrite Pol_eval_mult.
repeat setoid_rewrite Pol_eval_plus.
repeat setoid_rewrite Pol_eval_c.

setoid_replace
(Pol_eval (X ^ n) y ** Pol_eval (Pc a + X * Q) y) with
(Pol_eval (X ^ n) y - Pol_eval (X ^ n) x)**
(Pol_eval (Pc a + X *Q) x ++ y**Pol_eval Q y)

setoid_rewrite Pol_eval_mult;
setoid_rewrite Pol_eval_pow; setoid_rewrite Pol_eval_X.
assert (Hprod: x ** Pol_eval Q x < y ** Pol_eval Q y).
apply cle_lt_trans with (x**Pol_eval Q y).
repeat setoid_rewrite (cmul_sym x).
apply cmul_le_compat_r.
apply HQi.
assumption.
apply clt_cle_weak; assumption.
apply clt_cle_weak; apply clt_le_trans with r; assumption.
apply cmul_lt_compat_r.
apply HQp.
apply clt_cle_weak; apply cle_lt_trans with x; assumption.
assumption.
assert (Hpol: Pol_eval (Pc a +X*Q) x < Pol_eval (Pc a + X*Q) y).
setoid_rewrite Pol_eval_plus; setoid_rewrite Pol_eval_mult;
setoid_rewrite Pol_eval_c; setoid_rewrite Pol_eval_X.
setoid_rewrite Pol_eval_plus; setoid_rewrite Pol_eval_mult;
setoid_rewrite Pol_eval_c; setoid_rewrite Pol_eval_X.
apply cplus_le_lt_compat.
apply cle_refl.
assumption.
case n.
repeat setoid_rewrite cpow_0.
repeat setoid_rewrite cmul_1_l.
apply Hpol.
intros p; rewrite (Npred_correct p (Npos p)).
repeat setoid_rewrite cpow_plus; repeat setoid_rewrite cpow_1.
setoid_rewrite (cmul_sym x); setoid_rewrite (cmul_sym y).
repeat setoid_rewrite <- cmul_assoc.
apply clt_trans with 
  (cpow x (Npred (Npos p)) ** (y ** Pol_eval (Pc a + X * Q) y)).
repeat setoid_rewrite (cmul_sym (cpow x (Npred (Npos p)))).
apply cmul_lt_compat_r.
apply cpow_lt_0_compat_l.
apply clt_le_trans with r;assumption.
assert (Hbase := increase_pol_close_0_X Q a r Hr HQp HQi Hclose x y Hx Hy).
repeat setoid_rewrite Pol_eval_mult in Hbase.
repeat setoid_rewrite Pol_eval_X in Hbase.
exact Hbase.

*)


Theorem cmul_lt_le_compat :
  forall x y z t, c0 < x -> c0 < z -> x < y -> z <= t -> x ** z < y ** t.
intros; case (ceq_dec z t).
intros heq; setoid_rewrite <- heq; apply cmul_lt_compat_r; assumption.
intros; apply cmul_lt_compat; try assumption.
apply clt_decompose; assumption.
Qed.


Theorem one_alternation_root_main :
  forall P, one_alternation P -> least_non_zero_coeff P < c0 ->
  forall eps, c0 < eps -> exists a, exists b, c0 < a /\ a < b /\
      --eps < Pol_eval P a /\ Pol_eval P a <= c0 /\ c0 < Pol_eval P b /\
      Pol_eval P b < eps /\
      (forall x, 0 < x -> x < a -> Pol_eval P x < c0) /\
      (forall x, b < x -> c0 < Pol_eval P x) /\
      (forall x y, a < x -> x < y -> Pol_eval P x < Pol_eval P y).
intros P H; induction H.
intros HlnP eps Hp.
assert (Han:~a==0) by (apply (neg_cmul_n0 _ _ c)).
assert (Hal : least_non_zero_coeff P == a) by 
 exact (least_non_zero_P4 P a n P1 p Han).
assert (Haneg : a < c0) by (setoid_rewrite <- Hal; assumption).
assert (Hlqp : c0 < least_non_zero_coeff P1)
  by (apply neg_cmul_pos_r with a; assumption).
destruct (alternation_here_root P1 a Haneg Hlqp n0) as
  [r [Hrp [HPrn [r2 [Hrr2 [HPr2p HPincr]]]]]].
destruct (intermediate_value_polynom (Pc a +X*P1) r r2 HPrn HPr2p Hrr2 
            (eps/(cpow r2 n))) as 
            [v1 [v2 [Hv1 [Hv2 [Hv2r2 [HPv1l [HPv1u [HPv2l 
            [HPv2u Hdiff]]]]]]]]].
exists v1.
exists v2.
assert (Hv1p : c0 < v1) by (apply clt_le_trans with r; intuition; fail).
assert (Hv2p : c0 < v2) .
apply clt_le_trans with v1.
assumption.
apply clt_cle_weak; assumption.
split.
assumption.
split.
assumption.
split.
setoid_rewrite p; setoid_rewrite Pol_eval_mult;
setoid_rewrite Pol_eval_pow; setoid_rewrite Pol_eval_X.
apply cmul_lt_0_lt_reg_r with (c1/cpow v1 n).
apply clt_0_inv_pow; assumption.
setoid_rewrite (cmul_sym (--eps)).
setoid_rewrite <- cdiv_decompose.
apply pos_non_c0;apply cpow_lt_0_compat_l; assumption.
setoid_rewrite copp_div_l.
apply cle_lt_trans with (--(eps/cpow r2 n)).
apply cle_opp_div_r.
apply clt_cle_weak; assumption.
apply cpow_lt_0_compat_l; assumption.
apply cpow_le_compat_l.
apply clt_cle_weak; auto.
apply clt_cle_weak; apply clt_le_trans with v2; assumption.
setoid_rewrite (cmul_sym (cpow v1 n)); setoid_rewrite <- cmul_assoc.
setoid_rewrite cmul_div_r.
apply pos_non_c0; apply cpow_lt_0_compat_l; assumption.
setoid_rewrite cmul_1_r; assumption.
split.
setoid_rewrite p; setoid_rewrite Pol_eval_mult;
setoid_rewrite Pol_eval_pow; setoid_rewrite Pol_eval_X.
apply cmul_neg_compat_r.
apply clt_cle_weak; apply cpow_lt_0_compat_l; assumption.
assumption.
split.
setoid_rewrite p; setoid_rewrite Pol_eval_mult;
setoid_rewrite Pol_eval_pow; setoid_rewrite Pol_eval_X.
apply cmul_lt_0.
apply cpow_lt_0_compat_l;assumption.
assumption.
split.
setoid_rewrite p; setoid_rewrite Pol_eval_mult;
setoid_rewrite Pol_eval_pow; setoid_rewrite Pol_eval_X.
apply cmul_lt_0_lt_reg_r with (c1/cpow v2 n).
apply clt_0_inv_pow; assumption.
setoid_rewrite (cmul_sym eps).
setoid_rewrite <- cdiv_decompose.
apply pos_non_c0;apply cpow_lt_0_compat_l; assumption.
apply clt_le_trans with (eps/cpow r2 n).
setoid_rewrite (cmul_sym (cpow v2 n)); setoid_rewrite <- cmul_assoc.
setoid_rewrite cmul_div_r.
apply pos_non_c0; apply cpow_lt_0_compat_l; assumption.
setoid_rewrite cmul_1_r; assumption.
apply cle_div_r.
apply clt_cle_weak; assumption.
apply cpow_lt_0_compat_l; assumption.
apply cpow_le_compat_l.
apply clt_cle_weak; assumption.
assumption.
split.
intros x Hxp Hx.
setoid_rewrite p; setoid_rewrite Pol_eval_mult;
setoid_rewrite Pol_eval_pow; setoid_rewrite Pol_eval_X.
apply cmul_lt_neg_r.
apply cpow_lt_0_compat_l; assumption.
apply clt_le_trans with (2:= HPv1u).
repeat (setoid_rewrite Pol_eval_plus; setoid_rewrite Pol_eval_c).
repeat setoid_rewrite (cadd_sym a).
apply cplus_lt_compat_r.
repeat (setoid_rewrite Pol_eval_mult; setoid_rewrite Pol_eval_X).
apply cmul_lt_le_compat_r.
assumption.
assumption.
apply no_alternation_positive_strict; assumption.

apply HPincr.

BOUM.
intros x' y' Hx' Hy'; split; [idtac|clear x' y' Hx' Hy'].
setoid_rewrite p; setoid_rewrite Pol_eval_mult;
setoid_rewrite Pol_eval_pow; setoid_rewrite Pol_eval_X.
setoid_rewrite Pol_eval_mult;
setoid_rewrite Pol_eval_pow; setoid_rewrite Pol_eval_X.
case n.
repeat setoid_rewrite cpow_0.
repeat setoid_rewrite cmul_1_l.
apply HPincr.
apply cle_lt_trans with x; intuition;fail.
assumption.
fail.
intros p'; rewrite (Npred_correct p' (Npos p')).
repeat setoid_rewrite cpow_plus.
repeat setoid_rewrite cpow_1.
setoid_replace x' ** cpow x' (Npred (Npos p')) ** Pol_eval (Pc a + X * P1) x'

assert (dumm:= increase_pol_close_0_X).

apply cle_lt_trans with (cpow y' n**Pol_eval (Pc a + X * P1) x').
apply cmul_le_compat_r.
apply cpow_le_compat_l.
apply cle_trans with x;apply clt_cle_weak; assumption.
apply clt_cle_weak; assumption.

apply cmul_lt_compat.
apply cpow_lt_0_compat_l.
apply clt_trans with x; assumption.
apply cpow_lt_compat_l.
