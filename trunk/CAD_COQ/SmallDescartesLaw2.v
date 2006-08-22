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


Theorem Horner_step_positive :
forall a Q, a < c0 -> forall r, c0 <= r ->
  (forall x y, r < x -> x <= y -> 
           c0 < Pol_eval Q x /\ Pol_eval Q x <= Pol_eval Q y) ->
  c0 < Pol_eval (Pc a + X *Q)(r++c1--a/Pol_eval Q (r++c1)).
intros a Q Halt0 r Hrpos HQincr.
assert (Hb1: r < r++c1).
apply cplus_lt_r;apply c0_clt_c1.
assert (Hb2:= cle_refl (r++c1)).
assert (c0 < Pol_eval Q (r++1)).
generalize (HQincr _ _ Hb1 Hb2); intuition.
assert (Hpos: c0 < --(a/Pol_eval Q (r++1))).
setoid_rewrite <- copp_div_l.
apply cdiv_lt_0_compat_l.
assumption.
apply clt_0_copp; assumption.
assert (Hpos' : c0 < r++c1 -- a/Pol_eval Q (r++c1)).
match goal with |- c0 < ?a -- ?b => setoid_replace (a--b) with (a++(--b)) end.
apply clt_0_plus_compat.
apply clt_0_le_lt_plus_compat.
assumption.
apply c0_clt_c1.
assumption.
setoid ring.
setoid_rewrite Pol_eval_plus.
setoid_rewrite Pol_eval_c.
setoid_rewrite Pol_eval_mult.
setoid_rewrite Pol_eval_X.
apply clt_le_trans with (a++ (r ++ c1 -- a / Pol_eval Q (r ++ c1))**
                          (Pol_eval Q (r++c1))).
setoid_replace 
  (a ++ (r ++ c1 -- a / Pol_eval Q (r ++ c1)) ** Pol_eval Q (r ++ c1))
with
  ((r++c1)**Pol_eval Q (r++c1) ++ a --
        (Pol_eval Q (r++c1)** (a/Pol_eval Q (r++c1))));
  [idtac | setoid ring;fail].
setoid_rewrite cmul_div_r.
apply pos_non_c0;assumption.
match goal with |- _ < ?x => 
  setoid_replace x with ((r ++ c1) ** Pol_eval Q (r ++ c1));[idtac|setoid ring]
end.
apply cmul_lt_0.
apply clt_0_le_lt_plus_compat.
assumption.
apply c0_clt_c1.
assumption.
apply cplus_le_compat.
apply cle_refl.
repeat setoid_rewrite (cmul_sym (r ++ c1 -- a / Pol_eval Q (r ++ c1))).
apply cmul_le_compat_r.
assert (Hb3 : r++c1<=r++c1 --a/Pol_eval Q (r++c1)).
setoid_replace (r++c1 --a/Pol_eval Q (r++c1)) with
  (--(a/Pol_eval Q (r++c1))++(r++c1));[idtac |setoid ring].
apply cplus_pos_simplify; apply clt_cle_weak; assumption.
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



