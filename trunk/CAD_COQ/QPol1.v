Add LoadPath "/0/user/amahboub/QArith".

Require Import Pol1_is_ring.
Require Import ZArith.
Require Export ZArithRing.
Require Import QArith.
Require Import Bool_nat.

Open Scope Q_scope.

(*buliding  the set of rational coefficients*)

Definition Qcoef_set :=
  mk_cset Q (0#1) (1#1) Qeq Qplus Qmult Qminus Qopp.

Definition Qcoef_eq :=
  mk_ceq Q Qcoef_set Qeq_refl Qeq_sym Qeq_trans Qplus_simpl Qmult_simpl Qopp_simpl.

Lemma Qzero_left : forall x, (0#1) + x == x.
Proof.
  intro.
  unfold Qeq.
  unfold Qplus.
  simpl.
  ring.
Qed.

Lemma Qmult_plus_distr_l : forall x y z, (x + y) * z == (x * z) + (y * z).
Proof.
  intros (x1, x2) (y1, y2) (z1, z2).
  unfold Qeq;unfold Qplus;unfold Qmult.
  simpl.
  Kill_times.
  ring.
Qed.


Lemma Qminus_def : forall x y, x - y == x + (- y).
Proof.
  intros.
  unfold Qminus.
  exact (Qeq_refl (x + - y)).
Qed.

Lemma Qmult_1_n : forall n, (1#1)*n == n.
Proof.
  intro.
  unfold Qeq.
  unfold Qplus.
  unfold Qmult.
  simpl.
  destruct (Qnum n);auto.
Qed.
  

Definition Qcoef_th := 
  mk_ct Q Qcoef_set Qzero_left Qplus_sym Qplus_assoc Qmult_1_n
   Qmult_sym Qmult_assoc Qmult_plus_distr_l Qminus_def Qplus_inverse_r.

(*univariate polynomials over Q*)


Definition Poly := Pol1 Q.

Implicit Arguments PX [C].
Implicit Arguments Pc [C].

Implicit Arguments Pol1Eq.
Implicit Arguments Pol1_add.
Implicit Arguments Pol1_mul.
Implicit Arguments Pol1_sub.
Implicit Arguments Pol1_opp.

Delimit Scope P_scope with Pol1.
Bind Scope P_scope with Pol1.

Open Scope P_scope.



Notation "x != y" := (Pol1Eq Qcoef_set x y) : P_scope.
Notation "x ++ y" := (Pol1_add Qcoef_set x y) : P_scope.
Notation "x ** y" := (Pol1_mul Qcoef_set x y) : P_scope.
Notation "x -- y" := (Pol1_sub Qcoef_set x y) : P_scope.
Notation "-- x" := (Pol1_opp Qcoef_set x) : P_scope.





