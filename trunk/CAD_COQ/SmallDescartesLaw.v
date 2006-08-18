Require Import Setoid.
Require Import ZArith.
Require Import CAD_types.
Require Import Utils.
Require Import QArith.
Require Import Qring.
Require Import NArith.

Require Import Qring.
Require Import Pol_ring2.
Import Qnorm.

Open Scope Q_scope.

(* First prove that polynomials with no alternations and at least one
   positive coefficient are increasing and have a limit to infinity at
   infinity. *)

Fixpoint least_non_zero_coeff (p:Pol) : Q :=
  match p with
    Pc c => c
  | PX P i c => if Qzero_test c then least_non_zero_coeff P else c
  end.

Inductive no_alternation : Pol1 Q -> Set :=
  no_alternation_c1 : forall (c:Q) (q:Pol1 Q), q != Pc c -> no_alternation q
| no_alternation_c2 :
    forall n (a:Q) P1 P2,
      no_alternation P2 -> a <> 0 ->
      0 <= a*(least_non_zero_coeff P2) ->
      P1 != (X^n *(Pc a+X*P2))%Pol -> no_alternation P1.


Inductive one_alternation : Pol1 Q -> Set :=
  one_alternation_here :
    forall P (a:Q) (n:N) P1, (1 <= Z_of_N n)%Z ->
      P != (X^n *(Pc a + X * P1))%Pol ->
      a * least_non_zero_coeff P1 < 0 -> no_alternation P1 ->
      one_alternation P
| one_alternation_step :
    forall P a n P1,
      P != (X^n * (Pc a + X * P1))%Pol ->
      one_alternation P1 -> 0 < a * least_non_zero_coeff P1 ->
      one_alternation P.

Ltac clean_coefficients :=
   unfold cops, Coef_record.Ceq, Coef_record.C1, 
     Coef_record.C0, ceq_compat, 
     Coef_record.Cadd, Coef_record.Cmul, Coef in *.

Theorem Q0test_c : forall x:Q, Qzero_test x = true -> Qeq x 0.
exact c0test_c.
Qed.

Theorem Qeq_propF : forall x y : Q, Qeq_bool x y = false -> ~x == y.
exact ceq_propF.
Qed.

Theorem Q0test_Qeqb : forall x : Q, Qzero_test x = Qeq_bool x 0.
exact c0test_ceqb.
Qed.

Hint Resolve Q0test_c.
Hint Resolve c0test_c.
Hint Unfold Coef_record.Ceq.
Hint Immediate Qeq_sym.

Theorem least_non_zero_coeff_0 :
   forall P, least_non_zero_coeff P == 0 -> P != P0.
induction P; simpl.
intros; constructor;auto.
caseEq (Qzero_test c).
intros Heqc Heq.
constructor.
auto.
auto.
intros Heq1 Heq2; elim (Qeq_propF c 0); auto.
rewrite <- Q0test_Qeqb; trivial.
Qed.

Lemma least_non_zero_coeff_P0_aux :
  forall P P', P !=P' -> P0 = P' -> least_non_zero_coeff P == 0.
intros P P' H; induction H.
simpl; intros Heq; injection Heq.
intros Heq'; rewrite Heq'; auto.
intros Heq; discriminate.
intros Heq; injection Heq; intros Heq'.
simpl.
caseEq (Qzero_test p).
simpl in * ; auto.
intros Hcz; elim (Qeq_propF p 0).
rewrite <- Q0test_Qeqb; auto.
rewrite Heq'; auto.
intros; discriminate.
intros; discriminate.
intros; discriminate.
Qed.

Lemma Q0test_morph :
  forall p q, p == q -> Qzero_test p = Qzero_test q.
intros p q H; caseEq (Qzero_test p).
intros Hp0; assert (ceq p 0).
auto.
caseEq (Qzero_test q); auto.
intros Hqn0; elim (Qeq_propF q 0).
rewrite <- Q0test_Qeqb; auto.
apply Qeq_trans with p; auto.
intros Hpn0; caseEq (Qzero_test q); auto.
intros Hq0; elim (Qeq_propF p 0).
rewrite <- Q0test_Qeqb; auto.
apply Qeq_trans with q; auto.
Qed.

Add Morphism (@Pc Q:Q->Pol) with signature Qeq ==> Pol_Eq as Pc_Morphism_Q.
exact Pc_Morphism.
Qed.

Add Morphism least_non_zero_coeff with signature Pol_Eq ==> Qeq
   as lnz_morphism.
intros x1 x2 H; induction H; simpl;intros;auto.
caseEq (Qzero_test q);auto.
intros H';
apply Qeq_trans with q; auto.
apply Qeq_trans with 0; auto.
caseEq (Qzero_test p);auto.
intros H';apply Qeq_trans with 0; auto.
apply Qeq_trans with p; auto.
apply Qeq_sym; auto.

  rewrite (Q0test_morph p q); auto.
simpl; case (Qzero_test q); auto.
simpl in IHPol_Eq.
  rewrite (Q0test_morph p q); auto.
simpl; case (Qzero_test q); auto.
apply ceq_sym; auto.
simpl in IHPol_Eq.
  rewrite (Q0test_morph p q); auto.
simpl; case (Qzero_test q); auto.
Qed.

Add Morphism Qle with signature Qeq ==> Qeq ==> iff as Qle_morphism.
Admitted.

Add Morphism Pol_eval with signature Pol_Eq ==> Qeq ==> Qeq as Pol_eval_morphism.
Admitted.

Lemma Pol_eval_plus :
  forall P P' x, (Pol_eval (P + P')%Pol x == Pol_eval P x + Pol_eval P' x)%Q.
Admitted.

Lemma Pol_eval_mult :
  forall P P' x, Pol_eval (P * P')%Pol x == (Pol_eval P x * Pol_eval P' x)%Q.
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

Lemma Pol_mul_Rat_cst : forall a b, a !* Pc b != Pc (a*b)%Q.
Admitted.

Add Morphism (@Pc Coef) with signature Qeq ==> Pol_Eq as Pc_morphism.
Admitted.

Lemma PX_interp :
   forall P n (c:Q), PX P n c != (X^(Npos n)*P+Pc c)%Pol.
intros P n c.
rewrite <- (mkPX_PX P n c c).
clean_coefficients; ring.
simpl (X^(Npos n))%Pol.
rewrite Pmul_PpowXP.
unfold Pol_add, Pol_addC.
apply mkPX_PX.
setoid ring.
Qed.


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

Lemma least_non_zero_P2 :
  forall P, exists n:N, exists P' : Pol,
   P != (X^n*(Pc(least_non_zero_coeff P)+X*P'))%Pol.
intros P; induction P.
exists 0%N; exists P0.
simpl.
rewrite Pol_mul_Rat_cst.
apply Pc_Morphism.
clean_coefficients.
clean_coefficients; ring.

destruct IHP as [n [P' Heq]].
simpl least_non_zero_coeff.
caseEq (Qzero_test c).
intros Heqt; exists (n+Npos p)%N; exists P'.
rewrite (PX_interp P p c).
assert (Pc_c_0 : Pc c != P0).
apply Pc_Morphism_Q; auto.
rewrite Pc_c_0.
rewrite Padd_0_r.

rewrite Ppow_plus.
rewrite (Pmul_sym(X^n)(X^Npos p)).
rewrite <- Pmul_assoc.
apply Pmul_Morphism.
setoid ring.
assumption.

intros _; exists 0%N; exists (X^(Npred (Npos p))*P)%Pol.
simpl (X^0)%Pol.
assert (Pc_1_P1 : Pc 1 != P1).
apply PolEq_refl.
rewrite (PX_interp P p c).
assert (Pol_Pow1 : (forall a, X * a != X^1 *a)%Pol).
simpl (X^1)%Pol.
intros a.
rewrite <- (PX_interp (Pc 1) 1 0).
apply PolEq_refl.
rewrite Pol_Pow1.
rewrite Pmul_assoc.
rewrite <- Ppow_plus.
replace (1+Npred(Npos p))%N with (Npos p).
rewrite Padd_sym.
rewrite Pmul_1_l.
apply PolEq_refl.
rewrite <- (Npred_correct p); trivial.
Qed.


Theorem no_alternation_increasing :
  forall P, 0 <= least_non_zero_coeff P -> no_alternation P ->
  forall x y, 0 <= x <= y -> 0 <= Pol_eval P x <= Pol_eval P y.
intros P H H1;generalize H;clear H.
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



*)
