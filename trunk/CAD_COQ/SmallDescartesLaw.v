Require Import Setoid.
Require Import ZArith.
Require Import CAD_types.
Require Import Utils.
Require Import NArith.

Require Import QArith.
Require Import Qring.
Require Import Qring.
Require Import Pol_ring2.
Import Qnorm.

Opaque Coef_record.Czero_test Coef_record.C0 Coef_record.Ceq Coef_record.C1
       Coef_record.Cadd Coef_record.Csub Coef_record.Cmul Coef_record.Cpow.

(* First prove that polynomials with no alternations and at least one
   positive coefficient are increasing and have a limit to infinity at
   infinity. *)

Fixpoint least_non_zero_coeff (p:Pol) : Coef :=
  match p with
    Pc c => c
  | PX P i c => if czero_test c then least_non_zero_coeff P else c
  end.

Inductive no_alternation : Pol -> Set :=
  no_alternation_c1 : forall c (q:Pol), q != Pc c -> no_alternation q
| no_alternation_c2 :
    forall n a P1 P2,
      no_alternation P2 -> a <> 0 ->
      0 <= a*(least_non_zero_coeff P2) ->
      P1 != (X^n *(Pc a+X*P2))%Pol -> no_alternation P1.


Inductive one_alternation : Pol -> Set :=
  one_alternation_here :
    forall P a (n:N) P1, (1 <= Z_of_N n)%Z ->
      P != (X^n *(Pc a + X * P1))%Pol ->
      a * least_non_zero_coeff P1 < 0 -> no_alternation P1 ->
      one_alternation P
| one_alternation_step :
    forall P a n P1,
      P != (X^n * (Pc a + X * P1))%Pol ->
      one_alternation P1 -> 0 < a * least_non_zero_coeff P1 ->
      one_alternation P.

Hint Resolve c0test_c PolEq_refl ceq_refl.
Hint Immediate ceq_sym PolEq_sym.

Theorem least_non_zero_coeff_0 :
   forall P, least_non_zero_coeff P == c0 -> P != P0.
induction P; simpl.
intros; constructor;auto.
caseEq (czero_test c).
intros Heqc Heq.
constructor.
auto.
auto.

intros Heq1 Heq2; elim (ceq_propF c 0); auto.
rewrite <- c0test_ceqb; trivial.
Qed.

Lemma least_non_zero_coeff_P0_aux :
  forall P P', P !=P' -> P0 = P' -> least_non_zero_coeff P == c0.
intros P P' H; induction H.
simpl; intros Heq; injection Heq.
intros Heq'; rewrite Heq'; auto.
intros Heq; discriminate.
intros Heq; injection Heq; intros Heq'.
simpl.
caseEq (czero_test p).
simpl in * ; auto.
intros Hcz; elim (ceq_propF p c0).
rewrite <- c0test_ceqb; auto.
rewrite Heq'; auto.
intros; discriminate.
intros; discriminate.
intros; discriminate.
Qed.

Lemma c0test_morph :
  forall p q, p == q -> czero_test p = czero_test q.
intros p q H; caseEq (czero_test p).
intros Hp0; assert (ceq p 0).
auto.
caseEq (czero_test q); auto.
intros Hqn0; elim (ceq_propF q 0).
rewrite <- c0test_ceqb; auto.
apply ceq_trans with p; auto.
intros Hpn0; caseEq (czero_test q); auto.
intros Hq0; elim (ceq_propF p 0).
rewrite <- c0test_ceqb; auto.
apply ceq_trans with q; auto.
Qed.

Theorem czero_test_0 : czero_test c0 = true.
rewrite c0test_ceqb.
caseEq (ceqb c0 c0); trivial.
intros habs; elim (ceq_propF c0 c0); auto.
Qed.

Add Morphism least_non_zero_coeff with signature Pol_Eq ==> ceq
   as lnz_morphism.
intros x1 x2 H; induction H; simpl;intros;auto.
caseEq (czero_test q);auto.
intros H';
apply ceq_trans with q; auto.
apply ceq_trans with 0; auto.
caseEq (czero_test p);auto.
intros H';apply ceq_trans with 0; auto.
apply ceq_trans with p; auto.
apply ceq_sym; auto.

rewrite (c0test_morph p q); auto.
case (czero_test q); auto.
simpl in IHPol_Eq.
rewrite (c0test_morph p q); auto.
case (czero_test q); auto.
apply ceq_sym; auto.
simpl in IHPol_Eq.
rewrite czero_test_0 in IHPol_Eq.
rewrite (c0test_morph p q); auto.
case (czero_test q); auto.
Qed.

Add Morphism Qle with signature Qeq ==> Qeq ==> iff as Qle_morphism.
Admitted.

Add Morphism Pol_eval with signature Pol_Eq ==> ceq ==> ceq as Pol_eval_morphism.
Admitted.

Lemma PX_interp :
   forall P n c, PX P n c != (X^(Npos n)*P+Pc c)%Pol.
intros P n c.
rewrite <- (mkPX_PX P n c c).
setoid ring.
simpl (X^(Npos n))%Pol.

rewrite Pmul_PpowXP.
unfold Pol_add, Pol_addC.
apply mkPX_PX.
setoid ring.
Qed.

Lemma Pol_mul_Rat_cst : forall a b, a !* Pc b != Pc (a**b).
intros a b; unfold Pol_mul_Rat.
caseEq (czero_test a).
intros Hatest; setoid_replace a with c0.
setoid_rewrite cmul_0_l; auto.
auto.
intros Hatest; caseEq (czero_test (a--c1)).
intros Hatest1; assert (a**b==b).
setoid_replace a with ((a --c1) ++ c1).
setoid_rewrite (c0test_c (a--c1)); auto.
setoid ring.
setoid ring.
setoid_rewrite H; auto.
simpl.
intros _; setoid_rewrite cmul_sym; auto.
Qed.

Lemma Pol_eval_mult_c :
  forall c P x, Pol_eval (Pc c * P) x == c ** Pol_eval P x.
intros c P x; induction P as [c' | P IHP i c'].
simpl; setoid_rewrite Pol_mul_Rat_cst; simpl; setoid ring.
simpl; setoid_rewrite mkPX_PX_c. 
setoid_rewrite Pol_mul_Rat_cst; simpl.
setoid_rewrite IHP; setoid ring.
Qed.

Lemma Pol_eval_plus :
  forall P P' x, Pol_eval (P + P')%Pol x == Pol_eval P x ++ Pol_eval P' x.
intros P; induction P; intros P' x; destruct P'.
simpl; auto.
simpl (Pc c + PX P' p c0).
simpl; setoid ring.
simpl; setoid ring.
generalize (ZPminus_spec p p0).
caseEq (ZPminus p p0).
intros Hm Hpp0.
simpl.
rewrite Hm.
rewrite Hpp0.
setoid_rewrite mkPX_PX_c.
simpl.
setoid_rewrite IHP.
setoid ring.
setoid_rewrite (PX_interp P); setoid_rewrite (PX_interp P').
simpl.
setoid_Rewrite 
Qed.

Lemma Pol_eval_mult :
  forall P P' x, Pol_eval (P * P')%Pol x == (Pol_eval P x ** Pol_eval P' x).
intros P; induction P as [c | P IHP i c]; intros P' x.
setoid_rewrite Pol_eval_mult_c; simpl; auto.
destruct P' as [c' | P' i' c'].
setoid_rewrite Pmul_sym.
setoid_rewrite Pol_eval_mult_c; simpl; setoid ring.
simpl.
setoid_rewrite mkPX_PX_c.
Qed.
simpl.


simpl; auto.
setoid_rewrite (Pol_mul_Rat_cst c' c).
simpl.
setoid ring.
simpl.
setoid_rewrite (Pol_mul_Rat_cst c' c).
setoid_rewrite mkPX_PX_c.
simpl.

simpl; auto.
Admitted.


Lemma Pol_eval_pow :
  forall P n x, Pol_eval (P^n)%Pol x == ((Pol_eval P x)^nat_of_N n)%Q.
Admitted.

Add Morphism Qmult with signature Qeq ==> Qeq ==> Qeq as Qmult_morphsim.
Admitted.

Add Morphism Qplus with signature Qeq ==> Qeq ==> Qeq as Qplus_morphism.
Admitted.

Add Morphism Qpower with signature Qeq ==> (@eq nat) ==> Qeq as Qpower_morphism.
Admitted.

Lemma Qle_0_mult :
   forall x y, 0<= x -> 0 <= y -> 0 <= x * y.
intros x y Hx Hy; assert (Qeq 0 (0*y)).
ring.
rewrite H.
apply Qmult_le_compat_r; auto.
Qed.

Lemma Qle_0_plus :
  forall x y, 0 <= x -> 0 <= y -> 0 <= x + y.
intros x y Hx Hy.
assert (Qeq 0 (0+0)).
ring.
rewrite H.
apply Qplus_le_compat; auto.
Qed.


Lemma Pol_eval_X : forall x, Qeq (Pol_eval X x) x.
intros; simpl.
Admitted.

Lemma Pol_eval_c : forall c x, Pol_eval (Pc c) x = c.
auto.
Qed.

Lemma least_non_zero_P1 :
  forall P, ~P != P0 -> ~Qeq (least_non_zero_coeff P) 0.
intros P Heq Hceq; elim Heq; apply least_non_zero_coeff_0; auto.
Qed.

Lemma Qplus_0_r : forall x:Q, (x+0 == x)%Q.
intros; ring.
Qed.

Lemma Qmult_1_r : forall x:Q, (x*1 == x)%Q.
intros; ring.
Qed.


Add Morphism (@Pc Coef) with signature Qeq ==> Pol_Eq as Pc_morphism.
Admitted.


Functional Scheme Npred_ind := Induction for Npred Sort Prop.

Lemma Npred_correct : forall p p', p' = Npos p -> p' = (1 + Npred p')%N.

intros p p'; functional induction (Npred p').
intros; discriminate.
intros; reflexivity.
unfold Nplus.
rewrite <- Pplus_one_succ_l.
elim (Psucc_pred (xO _x)).
intros; discriminate.
intros H; rewrite H; reflexivity.
reflexivity.
Qed.

Theorem X_mul_convert_pow : forall p, X * p != X^1*p.
intros; simpl;setoid ring.
Qed.

Lemma least_non_zero_P2 :
  forall P, exists n:N, exists P' : Pol,
   P != (X^n*(Pc(least_non_zero_coeff P)+X*P'))%Pol.
intros P; induction P.
exists 0%N; exists P0.

simpl.
unfold Pol_mul_Rat; rewrite czero_test_0.
setoid ring.

destruct IHP as [n [P' Heq]].
simpl least_non_zero_coeff.
caseEq (czero_test c).
intros Heqt; exists (n+Npos p)%N; exists P'.
rewrite (PX_interp P p c).
setoid_rewrite (c0test_c c); trivial.
match goal with |- _ != ?x => pose (u:= x); fold u end.
setoid_rewrite Heq; unfold u; rewrite Ppow_plus.
setoid ring.

intros _; exists 0%N; exists (X^(Npred (Npos p))*P)%Pol.
simpl (X^0)%Pol.
rewrite (PX_interp P p c).
rewrite X_mul_convert_pow.
setoid_replace (X^Npos p)%Pol with (X^1*X^Npred (Npos p))%Pol.
setoid ring.
rewrite <- Ppow_plus.
rewrite <- (Npred_correct p); auto.
Qed.

Theorem least_non_zero_P3 : least_non_zero_coeff P0 == c0.
apply ceq_refl.
Qed.

Theorem Pmul_0_l : forall x, P0 * x != P0.
intros; setoid ring.
Qed.

Theorem Pc_eq_X_pow_mul_decompose :
  forall Q a b n, Pc a != X^n*(Pc b + X*Q) -> a==b /\ (n = 0%N\/b==c0) /\ 
              Q != P0.
intros Q.
induction Q; intros a b n.
caseEq n.
intros Hn0.
subst n.
caseEq (czero_test c).
intros Hc0; setoid_rewrite (c0test_c c);auto.
match goal with |- Pc a != ?X -> _ =>
  setoid_replace X with (Pc b);[intros id; inversion id; auto | setoid ring]
end.
simpl (X^0); setoid ring.
intros Hcn0.
match goal with |- Pc a != ?X ->  _ =>
  setoid_replace X with (PX (Pc c) 1 b);[intros id; inversion id | setoid ring]
end.
assert (H':Pc c != P0);[auto|inversion H'].
rewrite c0test_ceqb in Hcn0.
elim (ceq_propF c c0); auto.
setoid_rewrite (PX_interp (Pc c)).
 simpl Pol_pow; setoid ring.
intros p Hn.

match goal with |- Pc a != ?v -> _ =>
    setoid_replace v with (PX (Pc b +X*Pc c) p c0)%Pol
end.
intros Heq; inversion Heq.
assert (H' : Pc b+ c!*X != P0) by auto.
unfold Pol_mul_Rat in H'.
caseEq (czero_test c); intros Hctest; rewrite Hctest in H'; simpl in H'.
inversion H'; assert (Hb: b++c0==c0) by assumption.
setoid_rewrite cadd_0_r in Hb.
setoid_rewrite Hb.
assert (Hc : c == c0) by auto.
setoid_rewrite Hc; auto.
caseEq (czero_test (c--c1)).
intros Hctest1; rewrite Hctest1 in H'.
setoid_replace (Pc b + X) with (PX P1 1 b) in H'.
inversion H'; elim P0_diff_P1;auto.
rewrite (PX_interp P1); simpl Pol_pow; setoid ring.
intros Hctest1; rewrite Hctest1 in H'.
assert (Hctest' : czero_test (c1**c)=false).
caseEq (czero_test (c1**c)); intros Hctest2; auto.
elim (ceq_propF c 0).
rewrite <- c0test_ceqb; auto.
setoid_rewrite <- (c0test_c (c1**c)); auto.
setoid ring.
rewrite Hctest' in H'.
simpl in H'.
inversion H'; assert (Habsc : Pc (c1**c) != Pol_ring2.P0) by assumption.
inversion Habsc.
elim (ceq_propF (c1**c) c0); auto; rewrite <- c0test_ceqb;auto.
setoid_rewrite (PX_interp (Pc b + X *Pc c)); setoid ring.
caseEq n.
intros Hn0; simpl (X^0);rewrite Pmul_1_l.
simpl.
rewrite Pscal_Pmul_l.
caseEq (czero_test c).
intros Hctest; setoid_rewrite (c0test_c _ Hctest); 
setoid_rewrite Pmul_0_l; setoid_rewrite Padd_0_r.
setoid_rewrite mkPX_PX_c; simpl.
intros Heq; inversion Heq.
assert (Hab : a==b).
apply ceq_trans with (b++c0);[assumption|setoid ring].
setoid_rewrite PX_interp.
rewrite (Npred_correct p (Npos p)); auto.
setoid_rewrite Ppow_plus.
simpl (X^1).
setoid_rewrite (Pmul_sym X).
setoid_rewrite <- Pmul_assoc.
setoid_replace (X*Q) with P0; [idtac | assumption].
repeat (auto;fail || setoid ring || split).
intros Hctest.
setoid_rewrite mkPX_PX_c; setoid_rewrite (PX_interp (X*Q)).
intros Heq.
assert (H':Pc a != PX (PX Q p c) 1 b).
setoid_rewrite (PX_interp (PX Q p c)).
setoid_rewrite (PX_interp Q).
simpl (X^1).
apply PolEq_trans with (1:= Heq).
setoid ring.
inversion H'.
assert (H'':PX Q p c != P0) by assumption.
inversion H''.
elim (ceq_propF c c0);auto.
rewrite <- c0test_ceqb; auto.

intros p' Hn; setoid_rewrite (PX_interp Q).
match goal with |- _ != ?x -> _ =>
   setoid_replace x with (PX (PX (PX Q p c) 1 b) p' c0)
end.
intros H'; inversion H'.
assert (Ha:a == c0) by assumption; 
assert (H'' : PX (PX Q p c) 1 b != P0) by assumption;
clear - IHQ Ha H''.
inversion H''.
assert (Hb: b==c0) by assumption;
assert (H'3: PX Q p c != P0) by assumption;
clear - IHQ Ha Hb H'3.
rewrite <- PX_interp.
assert (a==b) by (apply ceq_trans with c0; auto).
auto.
setoid_rewrite (PX_interp (PX (PX Q p c) 1 b)).
setoid_rewrite (PX_interp (PX Q p c)).
setoid_rewrite (PX_interp Q).
simpl (X^1); setoid ring.
Qed.

Theorem c0test_n : 
   forall x, ~ x==c0 -> czero_test x = false.
intros; caseEq (czero_test x); auto.
intros H0; elim H; apply ceq_prop; rewrite <- c0test_ceqb; rewrite H0.
exact I.
Qed.

Theorem least_non_zero_P4 :
  forall P b n Q, P != X^n * (Pc b + X * Q) -> ~b==c0 ->
            least_non_zero_coeff P == b.
intros P; induction P.
intros b n Q Heq Hbn0.
destruct (Pc_eq_X_pow_mul_decompose _ _ _ _ Heq) as [Hc [Hn HQ]].
exact Hc.

intros b n Q.
caseEq n.
intros Hn0; simpl (X^0);
match goal with |- _ != ?x -> _ => setoid_replace x with (PX Q 1 b) end.
intros Heq Hbn0; inversion Heq.
assert (Hcb : c==b) by assumption; clear - Hcb Hbn0.
setoid_rewrite Hcb; simpl; rewrite (c0test_n b); auto.
assert (Hcb : c==b) by auto; clear - Hcb Hbn0.
setoid_rewrite Hcb; simpl; rewrite (c0test_n b); auto.
assert (Hcb : c==b) by auto; clear - Hcb Hbn0.
setoid_rewrite Hcb; simpl; rewrite (c0test_n b); auto.
setoid_rewrite (PX_interp Q); simpl (X^1); setoid ring.

intros p' Hn.
match goal with |- _ != ?x -> _ => 
  setoid_replace x with (PX (PX Q 1 b) p' c0)
end.
intros Heq Hbn0; inversion Heq.
assert (Hc0 : c==c0) by assumption; assert (Hp :P !=PX Q 1 b) by assumption;
clear - Hc0 Hbn0 Hp.
assert (Hctest:czero_test c=true).
setoid_rewrite Hc0; rewrite czero_test_0; trivial.
simpl; rewrite Hctest.
setoid_rewrite Hp; simpl.
rewrite (c0test_n b); auto.
assert (Hc0: c==c0) by auto; 
 assert (Hp:P!=PX (PX Q 1 b) i c0) by assumption; clear - Hc0 Hbn0 IHP Hp.
assert (Hctest:czero_test c=true).
setoid_rewrite Hc0; rewrite czero_test_0; trivial.
simpl; rewrite Hctest.
setoid_rewrite Hp; simpl.
rewrite czero_test_0.
rewrite (c0test_n b); auto.
assert (HPQ: PX Q 1 b != PX P i c0) by assumption; clear - HPQ Hbn0.
inversion HPQ; elim Hbn0; auto.
setoid_rewrite (PX_interp (PX Q 1 b)); setoid_rewrite (PX_interp Q).
simpl (X^1); setoid ring.
Qed.

Theorem least_non_zero_P5 :
  forall P b, P != Pc b -> least_non_zero_coeff P == b.
intros P b Heq; setoid_rewrite Heq; auto.
Qed.

Theorem least_non_zero_P6 :
  forall P n Q a, P != X^n * (Pc a + X * Q) -> a == c0 ->
    least_non_zero_coeff P == least_non_zero_coeff Q.
intros P; induction P; intros n Q a.
intros Heq Ha.
destruct (Pc_eq_X_pow_mul_decompose _ _ _ _ Heq) as [Hc [Hn HQ]].
setoid_rewrite Hc; setoid_rewrite Ha; setoid_rewrite HQ; auto.
intros Heq Ha.
caseEq n.
intros Hn0; rewrite Hn0 in Heq; simpl (X^0) in Heq.
assert (H':PX P p c != PX Q 1 a).
setoid_rewrite (PX_interp Q).
simpl (X^1); setoid_rewrite Heq; setoid ring.
assert (Hatest: czero_test a = true).
setoid_rewrite Ha; apply czero_test_0.
setoid_rewrite H'; simpl; rewrite Hatest; auto.
intros p' Hn;
assert (H':PX P p c != PX (PX Q 1 a) p' c0).
rewrite Hn in Heq.
setoid_rewrite Heq; setoid_rewrite (PX_interp (PX Q 1 a));
setoid_rewrite (PX_interp Q).
simpl (X^1);setoid ring.
inversion H'.
assert (Hc0:c==c0) by assumption; assert (HPQ : P!=PX Q 1 a) by assumption;
clear - IHP Hc0 HPQ Ha.
assert (Hctest: czero_test c = true).
setoid_rewrite Hc0; apply czero_test_0.
simpl; rewrite Hctest; apply IHP with (n:=0%N)(Q:=Q)(a:=a); trivial.
apply PolEq_trans with (1:= HPQ); rewrite (PX_interp Q);
simpl Pol_pow;setoid ring.
assert (Hc0:c==c0) by auto; assert (HPQ: P!=PX(PX Q 1 a) i c0) by assumption;
clear - IHP Hc0 HPQ Ha.
simpl.
assert (Hctest : czero_test c = true).
setoid_rewrite Hc0; apply czero_test_0.
rewrite Hctest.

apply (IHP (Npos i) Q a); trivial.
rewrite HPQ; setoid_rewrite (PX_interp (PX Q 1 a));
setoid_rewrite (PX_interp Q); simpl (X^1);setoid ring.
assert (Hc0 : c==c0) by assumption; 
assert (HPQ : PX Q 1 a != PX P i c0) by assumption; 
clear - IHP Hc0 HPQ.
assert (Hctest : czero_test c = true).
setoid_rewrite Hc0; apply czero_test_0.
inversion HPQ.
assert (H' : Q != P) by assumption; clear - Hc0 Hctest H'.
setoid_rewrite H'; simpl.
setoid_rewrite Hctest; auto.
assert (H' : Q != PX P i0 c0) by assumption; clear - Hc0 Hctest H'.
setoid_rewrite H'.
simpl; rewrite Hctest;rewrite czero_test_0; auto.
assert (H':P!=PX Q i0 c0) by assumption; clear - Hctest H'.
setoid_rewrite H'; simpl; rewrite Hctest; rewrite czero_test_0; auto.
Qed.

Theorem least_non_zero_P7 :
  forall b, least_non_zero_coeff (Pc b) == b.
intros b; apply least_non_zero_P5; trivial.
Qed.

Theorem no_alternation_increasing :
  forall P, 0 <= least_non_zero_coeff P -> no_alternation P ->
  forall x y, 0 <= x <= y -> 0 <= Pol_eval P x <= Pol_eval P y.
intTheorem least_non_zero_P3 :
  forall P, Pnorm P = P0 -> least_non_zero_coeff P = 0.
ros P H H1;generalize H;clear H.
induction H1.
intros H x y Hint.
setoid_rewrite p.
simpl.
rewrite p in H.
simpl in H.
split; auto.
apply Qle_refl.
intros Hpos x y Hint ; rewrite p in Hpos; rewrite p.
do 2 rewrite Pol_eval_mult.
do 2 rewrite Pol_eval_pow.
do 2 rewrite Pol_eval_plus.
split.
apply Qle_0_mult.
rewrite Pol_eval_X.
apply Qpower_pos; intuition.
apply Qle_0_plus.
rewrite Pol_eval_c.
lazy beta iota zeta delta [least_non_zero_coeff] in Hpos;
fold least_non_zero_coeff in Hpos. 

