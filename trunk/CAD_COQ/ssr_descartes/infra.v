Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import choice fintype finfun ssrfun bigops xssralg.

Require Import Zbool .
Require Import QArith.
Require Import Qcanon.

Close Scope Q_scope .

Set   Implicit Arguments.
Unset Strict Implicit.

Import Prenex Implicits.

Import GRing.Theory .

Open Local Scope ring_scope .

(* -------------------------------------------------------------------- *)
(* Various eqtype, subtype, choice, count canonical structures          *)
(*               from the standard library                              *)
(* -------------------------------------------------------------------- *)
Definition eqp (p q : positive) : bool :=
  match ((p ?= q) Eq)%positive with Eq => true | _ => false end.

Lemma eqpP : Equality.axiom eqp.
Proof.
  move=> p q; apply: (iffP  idP)=>[|<-]; last by rewrite /eqp Pcompare_refl.
  rewrite /eqp; case e: ((p ?= q) Eq)%positive=> // _; exact: Pcompare_Eq_eq.
Qed.

Canonical Structure eqp_Mixin := EqMixin eqpP.
Canonical Structure eqp_eqType := Eval hnf in EqType eqp_Mixin.

Definition p_unpickle n := Some (Ppred (P_of_succ_nat n)).

Lemma p_pick_cancel : pcancel nat_of_P p_unpickle.
Proof.
  move=> x; rewrite /p_unpickle; congr Some.
  by rewrite pred_o_P_of_succ_nat_o_nat_of_P_eq_id.
Qed.

Definition p_countMixin  := CountMixin p_pick_cancel .
Definition p_choiceMixin := CountChoiceMixin p_countMixin .

Canonical Structure p_choiceType :=
  Eval hnf in ChoiceType p_choiceMixin.
Canonical Structure p_countType :=
  Eval hnf in CountType  p_countMixin.

Lemma eqzP : Equality.axiom Zeq_bool.
Proof. by move=> z1 z2;  apply: (iffP idP); move/Zeq_is_eq_bool. Qed.

Canonical Structure Z_Mixin := EqMixin eqzP.
Canonical Structure Z_eqType := Eval hnf in EqType Z_Mixin.

Definition z_code (z : Z) :=
  match z with
    |0%Z => (0%nat, true)
    |Zpos p => (pickle p, true)
    |Zneg p => (pickle p, false)
  end.

Definition z_pickle z := pickle (z_code z).

Definition z_decode c :=
  match c with
    |(0%nat, true) => Some 0%Z
    |(0%nat, false) => None
    |(n, true) =>
      if (unpickle n) is Some p then Some (Zpos p) else None
    |(n, false) =>
      if (unpickle n) is Some p then Some (Zneg p) else None
  end.

Definition z_unpickle n :=
  match (unpickle n) with
    |None => None
    |Some u => z_decode u
  end.

Lemma z_codeK : pcancel z_code z_decode.
Proof.
  rewrite /z_code /z_decode.
  case=> // n; case e : (pickle n)=>[|m]; rewrite -?e ?pickleK //;
    by move/ltP: (lt_O_nat_of_P n); rewrite -e -[pickle]/nat_of_P ltnn.
Qed.

Lemma z_pick_cancel : pcancel z_pickle z_unpickle.
Proof.
  by move=> x; rewrite /z_pickle /z_unpickle pickleK z_codeK.
Qed.

Definition z_countMixin  := CountMixin z_pick_cancel .
Definition z_choiceMixin := CountChoiceMixin z_countMixin .

Canonical Structure z_choiceType :=
  Eval hnf in ChoiceType z_choiceMixin.
Canonical Structure z_countType :=
  Eval hnf in CountType  z_countMixin.

Definition eqq (x y : Q) : bool :=
  match x, y with
    | (xn # xd)%Q, (yn # yd)%Q => (xn == yn) && (xd == yd)
  end.

Lemma eqq_refl : forall q, eqq q q.
Proof. by move=> [d n]; rewrite /eqq; rewrite 2!eqxx. Qed.

Lemma eqqP : Equality.axiom eqq.
Proof.
  move=> q1 q2; apply: (iffP idP) => [|<-]; last exact: eqq_refl.
  by case: q1=> n1 d1; case: q2=> n2 d2; case/andP; move/eqP->; move/eqP->.
Qed.

Canonical Structure eqq_eqMixin := EqMixin eqqP.
Canonical Structure eqq_eqType := Eval hnf in EqType eqq_eqMixin.

Definition q_code (q : Q) :=
  match q with
    |(qnum # qden)%Q => (qnum, qden)
  end.

Definition q_pickle q := pickle (q_code q).

Definition q_decode c :=
  match c with
    |(q, d) => Some (q # d)%Q
  end.

Definition q_unpickle n :=
  match (unpickle n) with
    |None => None
    |Some u => q_decode u
  end.

Lemma q_codeK : pcancel q_code q_decode.
Proof. by move=> []. Qed.

Lemma q_pick_cancel : pcancel q_pickle q_unpickle.
Proof.
by move=> x; rewrite /q_pickle /q_unpickle pickleK q_codeK.
Qed.

Definition q_countMixin  := CountMixin q_pick_cancel .
Definition q_choiceMixin := CountChoiceMixin q_countMixin .

Canonical Structure q_choiceType :=
  Eval hnf in ChoiceType q_choiceMixin.
Canonical Structure q_countType :=
  Eval hnf in CountType q_countMixin.

Definition nnegqb (q : Q) :=
  match q with
    (qd # qn)%Q => match qd with Zneg _ => false | _ => true end
  end.

(* -------------------------------------------------------------------- *)
(* Q/== as a field and ordered ring                                     *)
(* -------------------------------------------------------------------- *)
Record Qcb : Type := QcbMake { qcb_val :> Q; _ : Qred qcb_val == qcb_val } .

Lemma qcb_val_E : forall x Hx, qcb_val (@QcbMake x Hx) = x .
Proof . by [] . Qed .

(* Q/== ==> eqTye/choiceType/countType *)
Canonical Structure qcb_subType :=
  Eval hnf in [subType for qcb_val by Qcb_rect] .

Definition qcb_eqMixin := Eval hnf in [eqMixin of qcb_subType by <:].
Canonical Structure qcb_eqType  := Eval hnf in EqType qcb_eqMixin .

Definition qcb_choiceMixin := [choiceMixin of Qcb by <:].
Canonical Structure qcb_choiceType :=
  Eval hnf in ChoiceType qcb_choiceMixin.

Definition qcb_countMixin := [countMixin of Qcb by <:].
Canonical Structure qcb_countType :=
  Eval hnf in CountType qcb_countMixin.

Canonical Structure qcb_subCountType :=
  Eval hnf in [subCountType of Qcb].

(* Properties about Qred, Q and Qcb and equalities over all these types *)
Lemma Qredb_involutive : forall q, Qred (Qred q) == (Qred q) .
Proof .
  move=> q; apply/eqP; apply Qred_involutive .
Qed .

Lemma Qredb_complete : forall q q', (q == q')%Q -> Qred q == Qred q' .
Proof .
  by move=> q q' H; apply/eqP; apply Qred_complete .
Qed .

Lemma Qcb_QeqP : forall (q q': Qcb), reflect (q == q')%Q (q == q') .
Proof .
  case=> q Hq; case=> q' Hq'; apply: (iffP idP); rewrite eqE /= .
  + by move/eqP => -> .
  + by move=> H; rewrite -(eqP Hq) -(eqP Hq'); apply Qredb_complete .
Qed .

Lemma Qcb_is_canon : forall (q q' : Qcb), (q == q')%Q -> q == q' .
Proof.
  case=> q Hq; case=> q' Hq'; rewrite eqE /= => H .
  by rewrite -(eqP Hq) -(eqP Hq'); apply Qredb_complete .
Qed .

(* Arithmetic over Qcb from the one over Q *)
Definition Q2Qcb (q:Q) : Qcb := QcbMake (Qredb_involutive q) .
Arguments Scope Q2Qc [Q_scope].

Definition Qcbplus  (x y : Qcb) := Q2Qcb (x + y).
Definition Qcbmult  (x y : Qcb) := Q2Qcb (x * y).
Definition Qcbopp   (x   : Qcb) := Q2Qcb (- x).
Definition Qcbminus (x y : Qcb) := Q2Qcb (x - y).
Definition Qcbinv   (x   : Qcb) := Q2Qcb (/x).
Definition Qcbdiv   (x y : Qcb) := Q2Qcb (x */ y).

Tactic Notation "qcb" tactic(T) :=
    repeat case=> ? ?;
      apply/eqP; apply Qcb_is_canon;
      rewrite !qcb_val_E; repeat setoid_rewrite Qred_correct;
      by T .

(* Q/== ==> Zmodule *)
Lemma QcbplusA : associative Qcbplus.
Proof. by qcb ring . Qed .

Lemma QcbplusC : commutative Qcbplus .
Proof . by qcb ring . Qed .

Lemma Qcbplus0q : left_id (Q2Qcb 0) Qcbplus .
Proof . by qcb ring . Qed .

Lemma QcbplusNq : left_inverse (Q2Qcb 0) Qcbopp Qcbplus .
Proof . by qcb ring . Qed .

Lemma QcbplusqN : right_inverse (Q2Qcb 0) Qcbopp Qcbplus .
Proof . by qcb ring . Qed .

Definition Qcb_zmodMixin :=
  ZmodMixin QcbplusA QcbplusC Qcbplus0q QcbplusNq .

Canonical Structure Qcb_zmodType :=
  Eval hnf in ZmodType Qcb_zmodMixin .

(* Q/== ==> Ring *)
Lemma QcbmultA : associative Qcbmult .
Proof . by qcb ring . Qed .

Lemma Qcbmult1q : left_id (Q2Qcb 1) Qcbmult .
Proof . by qcb ring . Qed .

Lemma Qcbmultq1 : right_id (Q2Qcb 1) Qcbmult .
Proof . by qcb ring . Qed .

Lemma Qcbmultq0 : forall (q : Qcb), Qcbmult q (Q2Qcb 0) = (Q2Qcb 0) .
Proof . by qcb ring . Qed .

Lemma Qcbmult_addl : left_distributive Qcbmult Qcbplus .
Proof . by qcb ring . Qed .

Lemma Qcbmult_addr : right_distributive Qcbmult Qcbplus .
Proof . by qcb ring . Qed .

Lemma nonzeroq1 : Q2Qcb 1 != Q2Qcb 0 .
Proof . by rewrite /Q2Qcb eqE /= . Qed .

Definition Qcb_ringMixin :=
  RingMixin QcbmultA Qcbmult1q Qcbmultq1 Qcbmult_addl Qcbmult_addr nonzeroq1 .
Canonical Structure Qcb_ringType :=
  Eval hnf in RingType Qcb_ringMixin .

(* Q/== ==> commutative ring *)
Lemma QcbmultC : commutative Qcbmult .
Proof . by qcb ring . Qed .

Canonical Structure Qcb_comRingType := ComRingType QcbmultC .

(* Q/== ==> unitary ring *)
Lemma Qcb_mulVx :
    forall x:Qcb, x != (Q2Qcb 0) -> Qcbmult (Qcbinv x) x = (Q2Qcb 1) .
Proof .
  case=> x Hx; move=> H; apply/eqP; apply Qcb_is_canon .
  rewrite QcbmultC !qcb_val_E; repeat setoid_rewrite Qred_correct .
  by apply Qmult_inv_r => Hx0; case/Qcb_QeqP: H .
Qed .

Lemma Qcb_mulxV :
    forall x:Qcb, x != (Q2Qcb 0) -> Qcbmult x (Qcbinv x) = (Q2Qcb 1) .
Proof .
  by move=> x Hx; rewrite QcbmultC; apply Qcb_mulVx .
Qed .

Definition Qcb_unit : pred Qcb := fun q:Qcb => q != (Q2Qcb 0) .

Lemma Qcb_intro_unit :
    forall (p q : Qcb), Qcbmult q p = (Q2Qcb 1) -> p != (Q2Qcb 0) .
Proof .
  move=> p q H; apply/negP; move/eqP => p0 .
  by rewrite p0 Qcbmultq0 in H .
Qed .

Lemma Qcb_intro_unit_nC :
    forall (p q : Qcb),
      Qcbmult q p = (Q2Qcb 1) /\ Qcbmult p q = (Q2Qcb 1)
      -> p != (Q2Qcb 0) .
Proof .
  by move=> p q *; apply (@Qcb_intro_unit p q); tauto .
Qed .

Lemma Qcb_inv_out : forall (p : Qcb), negb (p != (Q2Qcb 0)) -> Qcbinv p = p .
Proof .
  by move=> p H; rewrite negbK in H; rewrite (eqP H) /Qcbinv /= /Qinv .
Qed .

(* FIXME strub: cannot do 1/x when defining Qcb_unitRingType as:

   Canonical Structure Qcb_unitRingType :=
      Eval hnf in UnitRingType Qcb_comUitRingMixin . *)

Definition Qcb_unitRingMixin :=
  UnitRingMixin Qcb_mulVx Qcb_mulxV Qcb_intro_unit_nC Qcb_inv_out .

Definition Qcb_comUnitRingMixin :=
  ComUnitRingMixin Qcb_mulVx Qcb_intro_unit Qcb_inv_out .

Canonical Structure Qcb_unitRingType :=
   Eval hnf in UnitRingType Qcb_unitRingMixin .

Canonical Structure Qcb_comUnitRingType :=
   Eval hnf in ComUnitRingType Qcb_comUnitRingMixin.

(* Q/== ==> field *)
Definition Qcb_fieldMixin : GRing.Field.mixin_of Qcb_comUnitRingType .
Proof . by [] . Qed .

Definition Qcb_idomainMixin := FieldIdomainMixin Qcb_fieldMixin .

Canonical Structure Qcb_iddomainType :=
  Eval hnf in IdomainType Qcb_idomainMixin .

Canonical Structure Qcb_fieldType :=
  Eval hnf in @FieldType (IdomainType Qcb_idomainMixin) Qcb_fieldMixin .

(* Q/== ==> non-discrete ordered field *)
Definition Qcb_leb  (x y : Qcb) := (Zle_bool (Qnum x * QDen y) (Qnum y * QDen x))%Z .
Definition Qcb_ltb  (x y : Qcb) := (Zlt_bool (Qnum x * QDen y) (Qnum y * QDen x))%Z .

Local Notation "x <<= y" := (Qcb_leb x y) .
Local Notation "x <<! y" := (Qcb_ltb x y) .

Lemma Qcb_leb_iff : forall (x y : Qcb), (x <<= y) <-> (x <= y)%Q .
Proof . by move=> x y; apply: Qle_bool_iff . Qed .

Lemma qleb_orderb : orderb Qcb_leb .
Proof .
  split => [x|x y|x y z Hxy Hyz] .
  + apply/Qcb_leb_iff; apply Qle_refl .
  + case/andP => [Hxy Hyx]; apply/eqP; apply/Qcb_QeqP .
    by apply Qle_antisym; apply/Qcb_leb_iff .
  + by apply/Qcb_leb_iff; apply Qle_trans with x; apply/Qcb_leb_iff .
Qed .

Lemma qleb_Tr :
  forall (x y : Qcb), (x <<= y) ->
    forall z:Qcb, (Qcbplus x z) <<= (Qcbplus y z) .
Proof .
  move=> [x Hx] [y Hy] Hxy [z Hz] .
  move/Qcb_leb_iff: Hxy => Hxy; apply/Qcb_leb_iff .
  rewrite !qcb_val_E in Hxy |- *; repeat setoid_rewrite Qred_correct .
  by apply Qplus_le_compat; last apply Qle_refl .
Qed .

Lemma qleb_qltne :
  forall (x y : Qcb), (x <<! y) = (x <<= y) && (x != y) .
Proof .
  move=> x y; rewrite /Qcb_leb /Qcb_ltb .
  rewrite /Zlt_bool /Zle_bool .
  case D: (Qnum x * ' Qden y ?= Qnum y * ' Qden x)%Z => //= .
  + symmetry; apply negbTE; rewrite negbK; apply/Qcb_QeqP .
    by rewrite /Qeq; apply Zcompare_Eq_eq .
  + symmetry; apply/Qcb_QeqP; rewrite /Qeq .
    move/Zcompare_Eq_iff_eq=> Hdiscr; congruence .
Qed .

Lemma qleb_total : forall (x y : Qcb), (x <<= y) || (y <<= x) .
Proof .
  move=> x y; rewrite /Qcb_leb .
  generalize (Qnum x * ' Qden y)%Z => z1 .
  generalize (Qnum y * ' Qden x)%Z => z2 .
  by case (Zle_bool_total z1 z2) => ->; rewrite ?orbT .
Qed .

Lemma qleb_lcompatible : lcompatible Qcb_leb .
Proof .
  move=> [x Hx] [y Hy] [z Hz] .
  move/Qcb_leb_iff=> H0x; move/Qcb_leb_iff => Hyz .
  apply/Qcb_leb_iff; rewrite !qcb_val_E /= in H0x Hyz .
  rewrite ![QcbMake Hx * _]mulrC !qcb_val_E; setoid_rewrite Qred_correct .
  exact: Qmult_le_compat_r .
Qed .

Definition Qcb_orderedFieldMixin :=
  OfieldMixin
  qleb_orderb qleb_Tr qleb_qltne qleb_total qleb_lcompatible .

Canonical Structure Qcb_orderedFieldType :=
  Eval hnf in OfieldType Qcb_orderedFieldMixin .

(* -------------------------------------------------------------------- *)
Reserved Notation "'δ_ ( i , j )"
  (at level 8, format "''δ_' ( i ,  j )") .

Import Monoid.

Section Kronecker .

Variable T : eqType .
Variable R : Type .

Variables zero one : R .

Notation Local "0" := zero .
Notation Local "1" := one .

Variable times : mul_law 0 .
Variable plus  : add_law 0 times .

Notation Local "'*%M'" := (mul_operator times) (at level 0).
Notation Local "x * y" := ( *%M x y).

Definition kronecker (x y : T) : R := (if x == y then 1 else 0) .

Definition δfun := nosimpl kronecker .

Notation "'δ_ ( i , j )" := (δfun i j) .

Lemma δE : forall i j, 'δ_(i, j) = if (i == j) then 1 else 0.
Proof. by move=> i j; rewrite /δfun /kronecker. Qed.

Lemma δeq : forall x, 'δ_(x, x) = 1 .
Proof . by move=> x; rewrite δE eqxx . Qed .

Lemma δne : forall x y, x != y -> 'δ_(x, y) = 0 .
Proof . by move=> x y H; rewrite δE (negbTE H) . Qed .

Lemma δsym : forall x y, 'δ_(x, y) = 'δ_(y, x) .
Proof . by move=> x y; rewrite δE eq_sym . Qed .

Lemma δprod_ne :
    forall i j₁ j₂, j₁ != j₂ -> 'δ_(i, j₁) * 'δ_(i, j₂) = 0 .
Proof .
move=> i j₁ j₂ ne_j₁_j₂; rewrite !δE.
case H1 : (i == j₁); rewrite ?mul0m //; case H2 : (i == j₂); rewrite ?mulm0 //.
by move/eqP:ne_j₁_j₂; rewrite -(eqP H1) -(eqP H2).
Qed.

End Kronecker .

Notation "'δ'" := (@δfun _ )(at level 8, no associativity).

(* -------------------------------------------------------------------- *)
Section VSwap .
  Variable T : eqType .

  Definition vswap (i j n : T) :=
    if n == i then j else (if n == j then i else n) .

  Notation "i ← n → j" := (vswap i j n) (at level 5, no associativity) .

Lemma vswap_left : forall i j, i ← i → j = j .
Proof . by move=> *; rewrite /vswap eqxx . Qed .

Lemma vswap_right : forall i j, i ← j → j = i .
Proof .
    move=> i j; rewrite /vswap eqxx .
    by case D: (j == i); first rewrite (eqP D) .
  Qed .

Lemma vswap_neq : forall i j n, n != i -> n != j -> i ← n → j = n .
Proof .
    by move=> i j n Hi Hj; rewrite /vswap (negbTE Hi) (negbTE Hj) .
  Qed .

End VSwap .

Notation "i ← n → j" := (vswap i j n) (at level 5, no associativity) .


