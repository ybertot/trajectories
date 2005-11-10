   Require Import Qabs.
Require Import CAD_types.
Require Export Setoid_ring_theory.



Section Pol1.

(* Coef Ring *)
Parameter Coef:Set.

Parameter  cdeg : Coef -> N.
Parameter  c0 : Coef.
Parameter  c1 : Coef.
Parameter  cadd : Coef -> Coef -> Coef.

Parameter cmul : Coef -> Coef -> Coef.
Parameter copp : Coef -> Coef.
Parameter csub : Coef -> Coef -> Coef.
Parameter czero_test :Coef -> bool.
Parameter cpow : Coef -> N -> Coef.


(* Pour Pol_deriv *)
Parameter cof_pos:positive -> Coef .

Parameter ceq: Coef -> Coef -> Prop.
Parameter ceqb: Coef -> Coef -> bool.
Parameter  ceq_prop: forall x y : Coef, Bool.Is_true (ceqb x y) -> (ceq x y).

Parameter  c0test_c0 :czero_test c0 =true.
Parameter c0test_c: forall c , czero_test c = true-> (ceq c c0).
Parameter c0_diff_c1: ~(ceq c0 c1).

(*Parameter csub_def    : forall x y, (ceq (csub x  y )  (cadd x  (copp y))).*)
Parameter cpow_plus: forall x i j, (ceq (cpow x (i+j)) (cmul (cpow x i)(cpow x j))).



Notation "x ++ y" := (cadd x y) (at level 50, left associativity).
Notation "x ** y":= (cmul x y) (at level 40, left associativity).
Notation "-- x" := (copp x) (at level 35, right associativity).
Notation "x -- y" := (csub x y) (at level 50, left associativity).
Notation "x == y":=(ceq x y)(at level 70, no associativity).

Record coef_eq :Prop := mk_ceq{
   Ceq_refl : forall x, x==x;
   Ceq_sym : forall x y, x == y -> y == x;
   Ceq_trans : forall x y z, x == y -> y == z -> x == z;
   Cadd_ext : 
     forall x1 x2 y1 y2, x1 == x2 -> y1 == y2 -> x1 ++ y1 == x2 ++ y2;
   Cmul_ext :
     forall x1 x2 y1 y2, x1 == x2 -> y1 == y2 -> x1 ** y1 == x2 ** y2;
   Copp_ext :
     forall x1 x2, x1 == x2 -> -- x1 == -- x2
 }.
 
Parameter eq_th : coef_eq.
Definition ceq_refl:= Ceq_refl eq_th.
Definition ceq_sym := Ceq_sym  eq_th.
Definition ceq_trans := Ceq_trans  eq_th.
Definition cadd_ext := Cadd_ext  eq_th.
Definition cmul_ext := Cmul_ext  eq_th.
Definition copp_ext := Copp_ext  eq_th.


  Lemma Coef_setoid : Setoid_Theory Coef  ceq.
 Proof.   
  constructor.
  exact ceq_refl.
  exact ceq_sym .
  exact ceq_trans .
  Qed.

 Add Setoid Coef ceq Coef_setoid as Csetoid.

 Add Morphism cadd: cadd_ex.
 intros;apply cadd_ext ;auto.
 Qed.

 Add Morphism cmul: cmul_ex.
 intros;apply  cmul_ext  ;auto.
 Qed.

 Add Morphism copp: copp_ex.
 intros ; apply copp_ext;auto.
 Qed.

(* Ring structure over coefficients*)
 Record coef_theory : Prop := mk_ct {
   Cadd_0_l    : forall x, c0 ++ x == x;
   Cadd_sym    : forall x y, x ++ y == y ++ x;
   Cadd_assoc  : forall x y z, x ++ (y ++ z) == (x ++ y) ++ z;
   Cmul_1_l    : forall x, c1** x == x;
   Cmul_sym    : forall x y, x ** y == y ** x;
   Cmul_assoc  : forall x y z, x ** (y ** z) == (x ** y) ** z;
   Cdistr_l    : forall x y z, (x ++ y) ** z == (x ** z) ++ (y ** z);
   Csub_def    : forall x y, x -- y == x ++ --y;
   Copp_def    : forall x, x ++ (-- x) == c0
 }.

Parameter CT : coef_theory .

 Definition cadd_0_l :=  (Cadd_0_l CT). 
 Definition cadd_sym :=  (Cadd_sym CT).
 Definition cadd_assoc := (Cadd_assoc CT).
 Definition cmul_1_l := (Cmul_1_l CT).
 Definition cmul_sym  := (Cmul_sym CT).
 Definition cmul_assoc := (Cmul_assoc  CT).
 Definition cdistr_l := (Cdistr_l CT).
 Definition csub_def := (Csub_def  CT).
 Definition copp_def := (Copp_def  CT).


Lemma C_Ring : Setoid_Ring_Theory ceq cadd cmul c1 c0 copp ceqb.
split.
exact cadd_sym.
exact cadd_assoc.
exact cmul_sym.
exact cmul_assoc.
exact cadd_0_l.
exact cmul_1_l.
exact copp_def.
exact cdistr_l.
exact ceq_prop.
Defined.


Lemma copp_0 : -- c0==c0 .
Proof. 
rewrite <- (cadd_0_l  (--c0)).
apply copp_def.
Qed.

 Lemma cmul_0_l : forall x, c0 ** x == c0.
 Proof.
  intro x; setoid_replace (c0**x) with ((c0++c1)**x ++ --x).
  rewrite (cadd_0_l c1); rewrite (cmul_1_l x).
  rewrite (copp_def x);apply ceq_refl.
 rewrite (cdistr_l c0 c1 x);rewrite (cmul_1_l x).
  rewrite <- (cadd_assoc (c0**x) x (--x)).
  rewrite (copp_def x);rewrite (cadd_sym (c0**x) c0).
  rewrite (cadd_0_l (c0**x));apply ceq_refl.
 Qed.

 Lemma cmul_0_r : forall x, x**c0 == c0.
 Proof.
  intros;rewrite (cmul_sym x c0);apply cmul_0_l.
 Qed.

Lemma cmul_1_r:forall x, x**c1==x.
 Proof.
  intros;rewrite (cmul_sym x c1);apply cmul_1_l.
 Qed.


 Lemma copp_mul_l : forall x y, --(x ** y) == --x ** y.
 Proof.
  intros x y;rewrite <-(cadd_0_l (-- x ** y)).
  rewrite (cadd_sym c0 (--x**y)).
  rewrite <-(copp_def (x**y)).
  rewrite (cadd_assoc (-- x ** y) (x**y) (--(x**y))).
  rewrite <- (cdistr_l (--x) x y).
  rewrite (cadd_sym (--x) x);rewrite (copp_def  x).
  rewrite (cmul_0_l y);rewrite (cadd_0_l (--(x**y)));apply ceq_refl.
 Qed.
  
 Lemma copp_mul_r : forall x y, --(x**y) == x ** --y.
 Proof.
  intros.
  rewrite (cmul_sym x y);rewrite (cmul_sym x (-- y)).
  apply copp_mul_l.
 Qed.

 Lemma copp_add : forall x y, --(x ++ y) == --x ++ --y.
 Proof.
  intros x y;rewrite <- (cadd_0_l (--(x++y))).
  rewrite <- (copp_def x).
  rewrite <- (cadd_0_l (x ++ -- x ++ -- (x ++ y))).
  rewrite <- (copp_def y).
  rewrite (cadd_sym x (--x)).
  rewrite (cadd_sym y (--y)).
  rewrite <- (cadd_assoc (--y) y (-- x ++ x ++ -- (x ++ y))).
  rewrite <- (cadd_assoc (-- x)  x  (--(x ++ y))).
  rewrite (cadd_assoc  y (-- x)  (x ++ -- (x ++ y))).
  rewrite (cadd_sym y (--x)).
  rewrite <- (cadd_assoc  (-- x) y (x ++ -- (x ++ y))).
  rewrite (cadd_assoc y x (--(x++y))).
  rewrite (cadd_sym y x);rewrite (copp_def (x++y)).
  rewrite (cadd_sym (--x) c0);rewrite (cadd_0_l (--x)).
  apply cadd_sym.
 Qed.

 Lemma cdistr_r : forall x y z, x**(y ++ z) == x**y ++ x**z.
 Proof.
  intros.
  rewrite (cmul_sym x (y++z));rewrite (cmul_sym x y);rewrite (cmul_sym x z);
  apply cdistr_l.
 Qed.

 Lemma cadd_0_r : forall x, x ++ c0 == x.
 Proof.
  intro; rewrite (cadd_sym x c0);
  apply cadd_0_l.
 Qed.
 
 Lemma cadd_assoc1 : forall x y z, (x ++ y) ++ z == (y ++ z) ++ x.
 Proof.
  intros;rewrite <-(cadd_assoc x y z).
  rewrite (cadd_sym  x (y++z));apply ceq_refl.
 Qed.

 Lemma cadd_assoc2 : forall x y z, (y ++ x) ++ z == (y ++ z) ++ x.
 Proof.
  intros; rewrite <- (cadd_assoc y x z);
   rewrite (cadd_sym x z); apply cadd_assoc.
 Qed.

 Lemma cmul_assoc1 : forall x y z, (x ** y) ** z == (y ** z) ** x.
 Proof.
  intros;rewrite <-(cmul_assoc x y z).
  rewrite (cmul_sym x (y**z));apply ceq_refl.
 Qed.
 
 Lemma cmul_assoc2 : forall x y z, (y ** x) ** z == (y ** z) ** x.
 Proof.
  intros; rewrite <- (cmul_assoc y x z);
   rewrite (cmul_sym x z); apply cmul_assoc.
 Qed.

Lemma copp_opp : forall x, -- --x == x.
 Proof.
  intros x; rewrite <- (cadd_0_l  (-- --x)).
  rewrite <- (copp_def  x).
  rewrite <- (cadd_assoc x (--x) (-- --x)); rewrite (copp_def  (--x)).
  rewrite (cadd_sym  x c0);apply(cadd_0_l  x).
 Qed.

 Lemma cadd_reg_l : forall n m p, p ++ n == p ++ m -> n == m.
 intros;generalize (cadd_ext (--p) (--p) (p++n) (p++m)).
rewrite cadd_assoc;rewrite cadd_assoc.
assert (-- p ++ p == c0).
rewrite cadd_sym;rewrite copp_def; apply ceq_refl .
rewrite H0;rewrite cadd_0_l;rewrite cadd_0_l.
intro h;apply h;trivial.
apply copp_ext ;apply ceq_refl.
Qed.

Lemma cadd_reg_r: forall n m p, n ++ p==  m++p -> n == m.
intros; apply (cadd_reg_l n m p).
repeat rewrite (cadd_sym p);auto.
Qed.


Lemma copp_eq: forall c c', c -- c'==c0 -> c==c'.
intros c c' ; rewrite (csub_def c c') ;intro H.
generalize (cadd_ext (c++ --c') c0 c' c').
rewrite cadd_0_l.
intro h;rewrite <- h;trivial.
apply ceq_refl.
rewrite <- cadd_assoc.
rewrite (cadd_sym (--c')).
rewrite copp_def.
rewrite cadd_0_r;apply ceq_refl.
Qed.


(* End COEF_RING.*)

(* Section POL.*)
(* 

This defines operations on polynomials defined as Pol1 Coef given

Coef:Set
cdeg : Coef -> N
c0 : coef
c1 : Coef
cadd : Cooef -> Coef -> Coef
cmul : Cooef -> Coef -> Coef
copp : Coef -> Coef
csub : Coef -> Coef -> Coef
czero_test : Cof -> bool
cpow : Coef -> N -> Coef

+ cof_pos!!!!
*)

Load Pol_on_Coef.

 Fixpoint Peqb (P P' : Pol) {struct P'} : bool := 
  match P, P' with
  | Pc c, Pc c' => (ceqb c c') 
  | PX P i c, PX P' i' c' =>
    match Pcompare i i' Eq with
    | Eq => if Peqb P P' then (ceqb c c') else false
    | _ => false
    end
  | _, _ => false
  end.

 Notation " P ?== P' " := 
  (Peqb P P') (at level 70, no associativity) : pol_scope.

 Ltac caseEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.

Lemma Peq_ok : forall P P', 
    (Peqb P P') = true -> forall l, (ceq (Pol_eval P l) (Pol_eval P' l)).
induction P;destruct P';simpl;intros;try discriminate;trivial.
apply ceq_prop.
rewrite H;simpl.
auto.
generalize H;case (p ?= p0)%positive;intros;try discriminate.
generalize H0;caseEq (Peqb P P');intros;try discriminate.
apply cadd_ext.
apply cmul_ext.
auto.
 assert (h := Pcompare_Eq_eq p p0); destruct ((p ?= p0)%positive Eq);try discriminate.
rewrite h ; auto.
 apply ceq_refl.
apply ceq_prop;trivial.
rewrite H2;auto.
simpl;auto.
Qed.

 Lemma Pphi0 : forall l, (Pol_eval P0 l )== c0.
intros;simpl.
elim eq_th;auto.
Qed.
Lemma Pphi1 : forall l,  (Pol_eval P1 l) == c1.
intros;simpl.
elim eq_th;auto.
Qed.

(**Equality over polynomials,not in normal forms*)
 Inductive Pol_Eq:Pol -> Pol -> Prop :=
   |Eq_Pc_Pc : forall p q: Coef, (ceq p q)->(Pol_Eq (Pc p) (Pc q))
   |Eq_Pc_PX :
     forall p q: Coef, forall P:Pol,(ceq p q)->(Pol_Eq P P0)->forall i, (Pol_Eq (Pc p) (PX P i q))
   |Eq_PX_Pc :
     forall p q: Coef, forall P:Pol,(ceq p q)->(Pol_Eq P P0)->forall i, (Pol_Eq (PX P i  p) (Pc q))
   |Eq_PX_PX :
     forall p q:Coef, forall P Q :Pol, (ceq p q)->(Pol_Eq P Q)->forall i, (Pol_Eq (PX P i  p) (PX Q i q))
   |Eq_PXi_PXij:
     forall p q: Coef, forall P Q:Pol, forall i j, (ceq p q)-> (Pol_Eq Q (PX P i c0))->
      (Pol_Eq  (PX Q  j   q)(PX P (i+j)  p))
   |Eq_PXij_PXi:
     forall p q: Coef, forall P Q :Pol, forall i j,  (ceq p q)-> (Pol_Eq Q (PX P i c0)) ->
      (Pol_Eq (PX P (i+j)  p) (PX Q  j   q)).
 
(* Some notations *)
 (* Definition PolEq (P Q : Pol):= forall l ,(Pol_eval P l)==(Pol_eval Q l).*)

Notation "x != y" := (Pol_Eq x y)(at level 70, no associativity).
 Notation "x + y" := (Pol_add x y)(at level 50, left associativity).
 Notation "x * y" := (Pol_mul x y)(at level 40, left associativity).
 Notation "x - y" := (Pol_sub x y)(at level 50, left associativity).
 Notation "- x" := (Pol_opp x)(at level 35, right associativity).

Lemma absurdIplusJ : forall i j: positive , (i = j + i ) %positive -> False.
intros;assert ((Zpos i) = (Zpos j + Zpos i)%Z).
rewrite <- Zpos_plus_distr;rewrite <- H;auto.
assert (Zpos j > 0)%Z;[red;auto|omega].
Qed.

Lemma ZPminus_spec : forall x y,
  match ZPminus x y with
  | Z0 => x = y
  | Zpos k => x = (y + k)%positive
  | Zneg k => y = (x + k)%positive
  end.
 Proof.
  induction x;destruct y.
  replace (ZPminus (xI x) (xI y)) with (Zdouble (ZPminus x y));trivial.
  assert (H := IHx y);destruct (ZPminus x y);unfold Zdouble;rewrite 
H;trivial.
  replace (ZPminus (xI x) (xO y)) with (Zdouble_plus_one (ZPminus x 
y));trivial.
  assert (H := IHx y);destruct (ZPminus x y);unfold 
Zdouble_plus_one;rewrite H;trivial.
  apply Pplus_xI_double_minus_one.
  simpl;trivial.
  replace (ZPminus (xO x) (xI y)) with (Zdouble_minus_one (ZPminus x 
y));trivial.
  assert (H := IHx y);destruct (ZPminus x y);unfold 
Zdouble_minus_one;rewrite H;trivial.
  apply Pplus_xI_double_minus_one.
  replace (ZPminus (xO x) (xO y)) with (Zdouble (ZPminus x y));trivial.
  assert (H := IHx y);destruct (ZPminus x y);unfold Zdouble;rewrite 
H;trivial.
  replace (ZPminus (xO x) xH) with (Zpos (Pdouble_minus_one x));trivial.
  rewrite <- Pplus_one_succ_l.
  rewrite Psucc_o_double_minus_one_eq_xO;trivial.
  replace (ZPminus xH (xI y)) with (Zneg (xO y));trivial.
  replace (ZPminus xH (xO y)) with (Zneg (Pdouble_minus_one y));trivial.
  rewrite <- Pplus_one_succ_l.
  rewrite Psucc_o_double_minus_one_eq_xO;trivial.
  simpl;trivial.
 Qed.

 
(*PolEq is a setoid equality*)

 Lemma PolEq_refl :forall P, P != P.
 Proof.
induction P;constructor;trivial;apply ceq_refl.
Qed.

Lemma PolEq_sym: forall P Q, P != Q -> Q != P.
induction P; intros;destruct Q;inversion H;constructor;trivial;try apply ceq_sym;trivial.
apply IHP;trivial.
Qed.


Lemma PolEq_transO : forall P, P!=P0-> forall Q, P != Q-> Q != P0.
induction P.
inversion 1;subst.
intros;destruct Q.
inversion H0;unfold P0;constructor;apply ceq_sym;rewrite <- H2;trivial.
inversion H0;unfold P0;constructor;trivial;rewrite <- H2;apply ceq_sym;trivial.
intros H Q;generalize p c H;clear p c H; induction Q;intros.
inversion H;inversion H0;subst;unfold P0;constructor;rewrite <- H9;trivial.
inversion H0;subst;unfold P0;constructor;trivial.
inversion H;rewrite <- H3;trivial.
inversion H;apply IHP;trivial.
inversion H;rewrite H3;trivial.
inversion H;generalize (IHP  H7 ( PX Q i c0));intros.
generalize (H9 H8);intro.
inversion H10;trivial.
rewrite <-H3;inversion H;trivial.
apply (IHQ i c0).
unfold P0;constructor;inversion H;[apply ceq_refl|trivial].
apply PolEq_sym;trivial.
Qed.

Lemma PolEq_trans0: forall P Q, P!=P0-> Q != P0 -> P!=Q.
induction P;intros.
destruct Q;inversion H ;inversion H0.
constructor;rewrite H3;rewrite H6;apply ceq_refl.
constructor;trivial;rewrite H6;trivial.
generalize p c H ;clear p c H ;induction Q;intros;inversion H ;inversion H0.
constructor;[rewrite H3;rewrite H9;apply ceq_refl|trivial].
subst.
generalize (ZPminus_spec p p0);destruct (ZPminus p p0);intro h;rewrite h.
constructor;[rewrite H9;trivial|apply IHP;trivial].
rewrite Pplus_comm;constructor;[rewrite H3;trivial|apply IHP;trivial].
unfold P0;constructor;[apply ceq_refl|trivial].
rewrite Pplus_comm;constructor;[rewrite H9;trivial|idtac].
apply PolEq_sym;apply IHQ;trivial.
unfold P0;constructor;trivial;apply ceq_refl.
Qed.

Lemma PX_morph: forall P Q p q i, P!=Q -> p==q -> PX P i p != PX Q i q.
intros P Q p q i H;induction H;intros;constructor;trivial;constructor;trivial.
Qed.

Lemma PolEq_trans: forall P Q  , P!=Q -> forall R,  Q != R -> P !=R.
induction P.
intros;destruct Q.
destruct R;inversion H;inversion H0;subst;constructor;trivial;rewrite H3;trivial.
destruct R;inversion H0;inversion H;subst.
constructor;rewrite H10;trivial.
constructor;[rewrite H12;trivial|apply (PolEq_transO Q );trivial].
constructor;[rewrite H3;trivial|idtac].
generalize (PolEq_transO  Q H14 (PX R i c0) H8);intro H1;inversion H1;trivial.
constructor;[rewrite H12;trivial|idtac].
generalize  (PolEq_transO  (PX Q i c0) );intro H1;apply H1.
unfold P0;constructor;trivial;apply ceq_refl.
apply PolEq_sym;trivial.

(*cas de récursion*) 
intro Q; generalize p c; clear p c; induction Q;intros.
generalize c p c2 H H0 ; clear c p c2 H H0;induction R;intros.
inversion H;inversion H0;constructor;trivial;rewrite H3;trivial.
inversion H ; inversion H0;subst;
generalize (ZPminus_spec p p0);destruct (ZPminus p p0);intro h;rewrite h.
constructor;[rewrite H3;trivial|apply PolEq_trans0;trivial].
rewrite Pplus_comm;constructor;[rewrite H3;apply ceq_sym;trivial|apply PolEq_trans0;trivial].
unfold P0;constructor;trivial;apply ceq_refl.
rewrite Pplus_comm;constructor;[rewrite H3;trivial|apply PolEq_trans0;trivial].
unfold P0;constructor;trivial;apply ceq_refl.

generalize p0 c2 p c H H0;clear p0 c2 p c H H0 ;induction R;intros.
inversion H0;constructor;[inversion H;rewrite <- H3;trivial;apply ceq_sym;trivial|idtac].
inversion H.
apply (PolEq_transO Q);trivial;apply PolEq_sym;trivial.
apply (IHP (PX Q i0 c0));trivial;unfold P0;
constructor;trivial;apply ceq_refl.
assert (H16:PX P i0 c0 != P0). apply (PolEq_transO Q);trivial.
inversion H16;trivial.

inversion H;subst.
inversion H0;subst.
constructor;[rewrite H3;trivial|apply (IHP Q);assumption].
constructor;[rewrite H3;trivial|apply (IHP Q);trivial].
constructor; [rewrite H3;trivial| trivial].
assert (PX P i c0 != PX Q i c0). constructor;trivial;apply ceq_refl.
apply PolEq_sym;apply (IHR i c0 i c0);trivial;apply PolEq_sym;trivial.
subst;inversion H0;subst.
constructor;[rewrite <- H4;trivial|apply (IHP (PX Q i c0));trivial].
constructor;trivial;apply ceq_refl.
rewrite Pplus_assoc;constructor;[rewrite H4;trivial|apply (IHP (PX Q i c0));trivial].
constructor; trivial;apply ceq_refl.

generalize (ZPminus_spec p0 p);destruct (ZPminus p0 p);intro h;rewrite h.
assert (i0=i). rewrite h in H2;apply (Pplus_reg_r i0 i p);trivial.
constructor;[rewrite <- H3;trivial|apply (IHP (PX Q i c0));trivial].
apply PolEq_sym;rewrite <- H1;assumption.
rewrite Pplus_comm;constructor;try rewrite <- H3;trivial.
apply PolEq_sym;apply (IHR p1 c0 (i+p1)%positive c0).
constructor;trivial;apply ceq_refl.
assert ((i+p1)%positive = i0). 
apply (Pplus_reg_r (i+p1) i0 p);rewrite H2.
rewrite <- Pplus_assoc;rewrite h;rewrite (Pplus_comm p1);auto.
rewrite H1;apply PolEq_sym;trivial.
rewrite Pplus_comm;constructor;try (rewrite H3; apply ceq_sym);trivial.
rewrite <- H4;trivial.
apply (IHP (PX Q i c0));trivial;rewrite h in H2.
assert ((i0+p1)%positive = i). 
apply (Pplus_reg_r (i0+p1) i p0);
rewrite <- H2; rewrite (Pplus_comm p0);apply sym_equal;apply Pplus_assoc.
rewrite <- H1;constructor;trivial;apply ceq_refl.

inversion H0;subst.
constructor;[rewrite H3;trivial|apply PolEq_sym;apply IHQ;apply PolEq_sym;trivial].
apply PolEq_sym;trivial.

generalize (ZPminus_spec i i0);destruct (ZPminus i i0);intro h;rewrite h.
constructor.
rewrite H4;trivial.
subst.
assert (PX R i0 c0!= PX P i0 c0). apply PolEq_sym;apply IHQ.
apply PolEq_sym;trivial.
trivial.
inversion H1;trivial.
apply PolEq_sym;trivial.
generalize (absurdIplusJ i0 i);intro h;elim h;auto.
generalize (absurdIplusJ j i);intro h;elim h;auto.
subst.
rewrite <- Pplus_assoc;rewrite (Pplus_comm p);rewrite Pplus_assoc.
rewrite <- (Pplus_comm p);constructor.
rewrite H4;trivial.
assert (PX P (i0 + p) c0!= PX R i0 c0). apply IHQ.
apply PolEq_sym;trivial.
trivial.
inversion H1.
generalize (absurdIplusJ i0 p);intro h;elim h;auto.
rewrite  Pplus_comm;auto.
generalize (absurdIplusJ i0 (i+p));intro h;elim h;auto.
rewrite <- Pplus_assoc; rewrite <-(Pplus_comm i0);auto.
subst.
assert (i=p). apply Pplus_reg_r  with i0.
rewrite (Pplus_comm p);trivial.
subst;trivial.
rewrite <- Pplus_assoc;rewrite (Pplus_comm p);rewrite  Pplus_assoc.
rewrite <- (Pplus_comm p);constructor.
rewrite H3;trivial.
subst.
assert (PX P i c0!= PX R (i + p) c0).
 apply IHQ;trivial; apply PolEq_sym;trivial.
inversion H1.
generalize (absurdIplusJ i p);intro h;elim h;auto.
rewrite  Pplus_comm;auto.
assert (i0 = p);[idtac|subst;trivial].
rewrite Pplus_comm in H11; apply (Pplus_reg_l i);auto.
rewrite (Pplus_comm i0)  in H11. rewrite <- Pplus_assoc in H11.
generalize (absurdIplusJ j (i0 + p));intro h;elim h;auto.
rewrite Pplus_comm;auto.
rewrite Pplus_assoc;constructor;[rewrite H3;trivial|apply PolEq_sym; apply (IHR (i + i0)%positive  c0 i0 c0)].
constructor; trivial;try apply ceq_refl.
apply PolEq_sym;trivial.
Qed.


Definition Pol_Setoid : Setoid_Theory Pol Pol_Eq.
split.
apply PolEq_refl.
apply PolEq_sym.
intros;apply PolEq_trans with y;trivial.
Defined.
Add Setoid Pol Pol_Eq Pol_Setoid as PolEqSetoid.


(* Ring structure over coefficients
 Record Pol_theory : Prop := mk_pt {
   Padd_0_l    : forall x, P0 ++ x == x;
   Padd_sym    : forall x y, x ++ y == y ++ x;
   Padd_assoc  : forall x y z, x ++ (y ++ z) == (x ++ y) ++ z;
   Pmul_1_l    : forall x, c1** x == x;
   Pmul_sym    : forall x y, x ** y == y ** x;
   Pmul_assoc  : forall x y z, x ** (y ** z) == (x ** y) ** z;
   Pdistr_l    : forall x y z, (x ++ y) ** z == (x ** z) ++ (y ** z);
   Psub_def    : forall x y, x -- y == x ++ --y;
   Popp_def    : forall x, x ++ (-- x) == c0
 }.

*)
Lemma  Padd_0_l    : forall x, P0 + x != x.
unfold P0;intros x ;case x;simpl;intros.
constructor;apply cadd_0_l.
constructor;[apply cadd_0_l|apply PolEq_refl].
Qed.

Ltac case_c0_test c := caseEq(czero_test c);intro;[assert (c== c0);[apply c0test_c;trivial|idtac]|idtac].
(*
Lemma czero_test_ok: forall c c', c==c' -> czero_test c = czero_test c'.
intros;case_c0_test c.
assert (c' == c0).
rewrite<- H;trivial.
apply sym_equal;apply c0_zero;trivial.
case_c0_test c';auto.
assert (c==c0). rewrite H;trivial. 
assert (h:czero_test c = true);[apply c0_zero;trivial|rewrite h in H0;discriminate].
Qed.*)

Lemma mkPX_PX: forall P  i c c', c == c'  -> mkPX P i c != PX P i c'.
induction P;intros;simpl;case_c0_test c;constructor;trivial;try apply PolEq_refl.
unfold P0;constructor;trivial.
constructor;[trivial|apply PolEq_refl].
Qed.


Lemma mkPX_PX_c: forall P c p , mkPX P p c!= PX P p c.
intros;apply mkPX_PX; apply ceq_refl.
Qed.

Lemma mkPX_ok: forall P Q i c c', c == c' -> P!=Q -> mkPX P i c != mkPX Q i c'.
intros;apply PolEq_trans with (PX P i c).
apply mkPX_PX_c.
apply PolEq_trans with (PX Q i c').
constructor;trivial.
apply PolEq_sym;apply mkPX_PX_c.
Qed.

Lemma mkPXP_PXQ: forall P Q i c c', c == c'  -> P!= Q -> mkPX P i c != PX Q i c'.
intros;apply PolEq_trans with (mkPX Q i c).
apply mkPX_ok;trivial;apply ceq_refl.
apply mkPX_PX;trivial.
Qed.

Lemma ZPminus0: forall p, ZPminus p p = Z0.
induction p;simpl;auto;rewrite IHp;auto.
Qed.

Lemma ZPminusneg: forall p q , ZPminus p (p + q) = Zneg q.
intros;generalize (ZPminus_spec p (p+q));destruct (ZPminus p (p+q));intro.
generalize (absurdIplusJ p q);intro h;elim h;auto.
rewrite Pplus_comm;auto.
generalize (absurdIplusJ p ( q + p0));intro h;elim h ;auto.
rewrite <- (Pplus_comm p);rewrite Pplus_assoc;trivial.
assert (p0 = q);[apply (Pplus_reg_l p)|subst];auto.
Qed.

Lemma ZPminuspos: forall p q , ZPminus (p + q)  p= Zpos q.
intros;generalize (ZPminus_spec (p+q) p);destruct (ZPminus  (p+q) p);intro.
generalize (absurdIplusJ p  q);intro h;elim h ;auto.
apply sym_equal;rewrite Pplus_comm;assumption.
assert (p0 = q);[apply (Pplus_reg_l p)|subst];auto.
generalize (absurdIplusJ p ( q + p0));intro h;elim h ;auto.
rewrite <- (Pplus_comm p);rewrite Pplus_assoc;trivial.
Qed.

Hint Resolve ceq_sym ceq_trans ceq_refl
 cadd_ext cmul_ext copp_ext : c_spec.

Hint Resolve cadd_sym cmul_sym cadd_assoc cmul_assoc copp_def: c_spec.

(*Tactiques simplification des expressions dans C*)

 Ltac cgen :=
  repeat (progress (match goal with
  | |- context [-- c0] => rewrite copp_0
  | |- context [c0 ++ ?x] => rewrite (cadd_0_l x)
  | |- context [?x ++ c0] => rewrite (cadd_0_r x)
  | |- context [c1 ** ?x] => rewrite (cmul_1_l  x)
  | |- context [ c0 ** ?x] => rewrite (cmul_0_l x)
  | |- context [?x ** c0] => rewrite (cmul_0_r x)
  | |- context [(copp ?x) ** ?y] => rewrite <- (copp_mul_l x y)
  | |- context [?x ** (--?y)] => rewrite <- (copp_mul_r x y)
  | |- context [-- ( ?x ++ ?y)] => rewrite (copp_add x y)
  | |- context [ ?x -- ?y] => rewrite (csub_def x y)
  | |- context [ ( ?x ++ ?y) ** ?z] => rewrite (cdistr_l x y z)
  | |- context [?z ** (?x ++ ?y)] => rewrite (cdistr_r x y z)
  | |- context [ ?x ++ (?y ++ ?z)] => rewrite (cadd_assoc x y z)
  | |- context [?x ** (?y ** ?z)] => rewrite (cmul_assoc x y z)
  | |- context [-- (-- ?x)] => rewrite (copp_opp x)
  | |-  ?x == ?x => apply ceq_refl
  end)).

Ltac cadd_push x :=
  repeat (progress (match goal with
  | |- context [ (?y ++  x) ++ ?z] => 
     rewrite (cadd_assoc2 x y z)
  | |- context [(x ++ ?y) ++ ?z] => 
     rewrite (cadd_assoc1 x y z)
  end)).


Ltac cmul_push x :=
  repeat (progress (match goal with
  | |- context [(?y ** x) ** ?z] => 
     rewrite (cmul_assoc2  x y z)
  | |- context [(x ** ?y) ** ?z] => 
     rewrite (cmul_assoc1 x y z)
  end)).

 
Lemma  Padd_sym    : forall x y, x + y != y + x.
induction x.
simpl;destruct y;simpl.
constructor;apply cadd_sym.
constructor;[apply ceq_refl|apply PolEq_refl].
intro y; generalize p c;clear p c;induction y.
simpl;intros;constructor;[apply ceq_refl|apply PolEq_refl].
intros;generalize (ZPminus_spec p p0);destruct (ZPminus p p0);intro h;rewrite h.
simpl;rewrite (ZPminus0).
apply mkPX_ok;auto with c_spec;cgen.
simpl;rewrite (ZPminusneg);rewrite (ZPminuspos).
apply mkPX_ok;[apply cadd_sym|rewrite <- IHx].
case x.
simpl.
intro;constructor;[rewrite cadd_0_r;apply ceq_refl|apply PolEq_refl].
intros;simpl;caseEq (ZPminus p3 p1 );
intros;apply mkPX_ok;try (rewrite  cadd_0_r; apply ceq_refl);try apply PolEq_refl.
simpl;rewrite ZPminuspos;rewrite ZPminusneg.
apply mkPX_ok;[apply cadd_sym|rewrite IHy].
case y;simpl.
intros;constructor;[ apply cadd_0_r|apply PolEq_refl].
intros;caseEq (ZPminus p3 p1 );
intros;apply mkPX_ok;try apply cadd_0_r;try apply PolEq_refl.
Qed.

Lemma  Padd_0_r   : forall x, x+P0 != x.
intros;rewrite Padd_sym;apply Padd_0_l.
Qed.


Lemma PaddC_ok : forall P Q p q, P!=Q-> p==q->Pol_addC P p != Pol_addC Q q.
intros P Q p q H H0;inversion H;
simpl;
constructor;try rewrite H;try rewrite H0; try rewrite H1;try apply ceq_refl;try apply cadd_sym;try apply PolEq_refl;trivial.
Qed.

Lemma  Padd_P0_r    : forall  x P, P != P0 ->  x+P != x.
induction  x;intros.
simpl;destruct P;simpl;inversion H;constructor;trivial;rewrite H2;apply cadd_0_r.

generalize p c ;clear p c;induction P.
simpl;intros;inversion H;constructor;[ rewrite H2;apply cadd_0_l|apply PolEq_refl].
intros;generalize (ZPminus_spec p0 p);destruct (ZPminus p0 p);intro h;try rewrite h;
[simpl;rewrite ZPminus0|simpl;rewrite ZPminuspos|rewrite Padd_sym;simpl;rewrite ZPminuspos];
rewrite mkPX_PX_c;inversion H.
unfold P0;constructor;[rewrite H2;apply cadd_0_r|apply IHx;trivial].
rewrite Pplus_comm;constructor;[rewrite H2;rewrite cadd_0_r;apply ceq_refl|auto].
constructor;[rewrite H2;apply cadd_0_l|rewrite  Padd_sym;apply IHx;auto].
unfold P0;constructor;[apply ceq_refl|trivial].
Qed.

Lemma  Padd_P0_l   : forall  x P, P != P0 ->  P +x!= x.
intros;rewrite Padd_sym;apply Padd_P0_r;auto.
Qed.

Lemma Padd_ext_l : forall P Q R, P!=Q -> P+R != Q+R.
intros P Q R H;generalize R;clear R;induction H.
intros R; repeat rewrite <- (Padd_sym R);simpl.
apply PaddC_ok;trivial;apply PolEq_refl.
intros R;
generalize p q H i ;clear p q H i;induction R;intros;
[simpl;constructor;trivial;rewrite H;apply cadd_sym|idtac].
generalize (ZPminus_spec i p);destruct (ZPminus i p);intro h;try rewrite h;
[simpl;rewrite ZPminus0|simpl;rewrite ZPminuspos|
 repeat rewrite <- (Padd_sym ( PX R (i + p1) c));simpl;rewrite ZPminuspos];rewrite mkPX_PX_c.
constructor;[rewrite H;apply ceq_refl|rewrite IHPol_Eq;rewrite Padd_0_l;apply PolEq_refl].
constructor;[rewrite H;apply ceq_refl|rewrite <-  ( IHR c0 c0)].
apply ceq_refl.
simpl;rewrite Padd_0_l;apply PolEq_refl.
rewrite  Pplus_comm;constructor;[rewrite H;apply cadd_sym|idtac].
rewrite Padd_sym;rewrite IHPol_Eq;apply Padd_0_l.
intro R;generalize p q H i;clear p q H i;induction R;intros;
[simpl;constructor;trivial;rewrite H;apply cadd_sym|idtac].
generalize (ZPminus_spec i p);destruct (ZPminus i p);intro h;try rewrite h;
[simpl;rewrite ZPminus0|simpl; rewrite ZPminuspos|idtac];repeat rewrite mkPX_PX_c.
constructor;[rewrite H;apply ceq_refl|rewrite IHPol_Eq;apply Padd_0_l].
constructor;[rewrite H;apply ceq_refl|rewrite( IHR c0 c0)].
apply ceq_refl.
apply Padd_P0_l;unfold P0;constructor;apply ceq_refl.
rewrite Padd_sym;simpl;rewrite ZPminuspos.
rewrite mkPX_PX_c.
rewrite Pplus_comm;constructor.
rewrite H;apply cadd_sym.
apply Padd_P0_r;trivial.
intro R;generalize p q H i ;clear p q H i ;induction R;intros;
[simpl;constructor;trivial;rewrite H;apply ceq_refl|idtac].
generalize (ZPminus_spec i p);destruct (ZPminus i p);intro h;try rewrite h;
[simpl;rewrite ZPminus0|simpl; rewrite ZPminuspos|idtac];repeat rewrite mkPX_PX_c.
constructor;[rewrite H;apply ceq_refl|apply IHPol_Eq].
constructor;[rewrite H|apply IHR];apply ceq_refl.
repeat rewrite <- (Padd_sym (PX R (i + p1) c ));simpl;rewrite ZPminuspos;repeat rewrite mkPX_PX_c.
constructor;[rewrite H|repeat rewrite (Padd_sym (PX R p1 c0 ));apply IHPol_Eq];apply ceq_refl.
intro R; generalize p q j H;clear p q j H;induction R;intros;
[simpl;constructor;trivial;rewrite H;apply ceq_refl|idtac].
generalize (ZPminus_spec j p);destruct (ZPminus j p);intro h;try rewrite h.
simpl;rewrite ZPminus0;rewrite Pplus_comm;rewrite ZPminuspos.
repeat rewrite mkPX_PX_c.
constructor;[rewrite H;apply ceq_refl|apply IHPol_Eq].
simpl;rewrite ZPminuspos.
rewrite Pplus_assoc;rewrite (Pplus_comm i);simpl; rewrite <- Pplus_assoc; rewrite ZPminuspos.
repeat rewrite mkPX_PX_c.
constructor;[rewrite H;apply ceq_refl|apply IHR;apply ceq_refl].
rewrite Padd_sym;simpl Pol_add at 1;rewrite ZPminuspos.
generalize (ZPminus_spec i p1);destruct (ZPminus i p1);intro h1;try rewrite h1.
rewrite Pplus_comm;simpl;rewrite ZPminus0;repeat rewrite mkPX_PX_c.
rewrite Pplus_comm;constructor;[rewrite H;apply cadd_sym|rewrite Padd_sym;rewrite  IHPol_Eq].
rewrite h1;simpl;rewrite ZPminus0;rewrite mkPX_PX_c;
constructor;[apply cadd_0_l|apply PolEq_refl].
rewrite <- (Pplus_comm j); rewrite Pplus_assoc;simpl;rewrite ZPminuspos;repeat rewrite mkPX_PX_c.
rewrite Pplus_comm;constructor;[rewrite H;apply cadd_sym|idtac].
rewrite Padd_sym; rewrite IHPol_Eq .
rewrite h1;simpl;rewrite ZPminuspos;repeat rewrite mkPX_PX_c.
constructor;[apply cadd_0_l|apply PolEq_refl].
rewrite Pplus_assoc;rewrite (Pplus_comm i j).
rewrite (Padd_sym (PX P (j + i) p0));simpl;rewrite ZPminuspos;repeat rewrite mkPX_PX_c.
rewrite (Pplus_comm j i);constructor;[rewrite H;apply ceq_refl| idtac].
rewrite Padd_sym;rewrite IHPol_Eq;rewrite Padd_sym;simpl ;rewrite ZPminuspos.
rewrite mkPX_PX_c;constructor;[apply cadd_0_l|apply PolEq_refl].

intro R;generalize j p q H;clear j p q H;induction R;intros;
[simpl;constructor;trivial;rewrite H;apply ceq_refl|idtac].
generalize (ZPminus_spec j p);destruct (ZPminus j p);intro h;try rewrite h.
simpl Pol_add at 2;rewrite ZPminus0;simpl;rewrite Pplus_comm;rewrite ZPminuspos;
repeat rewrite mkPX_PX_c;constructor;[rewrite H;apply ceq_refl|apply PolEq_sym;apply IHPol_Eq].
rewrite Pplus_comm;rewrite <- Pplus_assoc;simpl;repeat rewrite ZPminuspos;
repeat rewrite mkPX_PX_c;constructor;[rewrite H;apply ceq_refl|rewrite Pplus_comm;apply IHR;apply ceq_refl].
rewrite (Padd_sym (PX Q j q ));simpl Pol_add at 2;rewrite ZPminuspos;rewrite Pplus_comm.
generalize (ZPminus_spec i p1);destruct (ZPminus i p1);intro h1;try rewrite h1.
simpl;rewrite ZPminus0;repeat rewrite mkPX_PX_c.
rewrite Pplus_comm;constructor;[rewrite H;apply cadd_sym|idtac].
rewrite Padd_sym;rewrite IHPol_Eq;rewrite h1;simpl;rewrite ZPminus0; 
rewrite mkPX_PX_c;constructor;[apply cadd_0_l|apply PolEq_refl].
rewrite Pplus_assoc;simpl;rewrite ZPminuspos;repeat rewrite mkPX_PX_c;
rewrite Pplus_comm;constructor;[rewrite H;apply cadd_sym|idtac].
rewrite Padd_sym;rewrite IHPol_Eq;rewrite h1;simpl;rewrite ZPminuspos;rewrite mkPX_PX_c.
constructor;[apply cadd_0_l| apply PolEq_refl].
rewrite Pplus_assoc;rewrite (Padd_sym( PX P (j + i) p0 ));simpl;rewrite ZPminuspos;
repeat rewrite mkPX_PX_c;rewrite Pplus_comm;constructor;[rewrite H;apply ceq_refl|idtac].
rewrite Padd_sym;rewrite IHPol_Eq;rewrite Padd_sym;simpl;rewrite ZPminuspos;
rewrite mkPX_PX_c;constructor;[apply cadd_0_l|apply PolEq_refl].
Qed.

Lemma Padd_ext_r : forall P Q R, P!=Q -> R+P != R+Q.
intros;repeat rewrite (Padd_sym R);apply Padd_ext_l;trivial.
Qed.

Lemma Padd_ext : forall P Q R S, P!=Q-> R!=S -> P+R!=Q+S.
intros;apply PolEq_trans with (Q+R).
apply Padd_ext_l;trivial.
apply Padd_ext_r;trivial.
Qed.


Add Morphism Pol_add: Padd_ex.
 intros;apply Padd_ext ;auto.
 Qed.

Lemma Pol_addC_mkPX: forall c c' P i, Pol_addC (mkPX P i c') c  != mkPX P i (c' ++ c).
intros;destruct P;simpl;
case (czero_test c2);simpl;
constructor;
try apply ceq_refl;try apply PolEq_refl;try apply cadd_sym.
Qed.

Lemma   Padd_assoc1 : forall z y x, x + (y + z) != (x + y) + z.
induction z. destruct y. destruct x. 
simpl;constructor;apply cadd_assoc.
simpl;constructor;[rewrite (cadd_sym c2 c); apply ceq_sym;apply cadd_assoc|apply PolEq_refl].
destruct x.
simpl;constructor;[repeat rewrite (cadd_sym c); apply cadd_assoc|apply PolEq_refl].
generalize (ZPminus_spec p0 p);destruct (ZPminus p0 p);intro h;rewrite h.
simpl;rewrite ZPminus0.
rewrite  Pol_addC_mkPX;repeat rewrite mkPX_PX_c;
constructor;[rewrite (cadd_sym c);apply cadd_assoc| apply PolEq_refl].
simpl; rewrite ZPminuspos;rewrite  Pol_addC_mkPX;repeat rewrite mkPX_PX_c;
constructor;[rewrite (cadd_sym c);apply cadd_assoc| apply PolEq_refl].
simpl Pol_add at 2;repeat rewrite (Padd_sym (PX x p0 c3));
simpl ;rewrite ZPminuspos;rewrite  Pol_addC_mkPX;repeat rewrite mkPX_PX_c;
constructor;[rewrite <- cadd_assoc;apply cadd_sym| apply PolEq_refl].

intro y; generalize p c;clear p c;induction y;intros.
destruct x.
simpl;constructor;[apply cadd_assoc|apply PolEq_refl].
generalize (ZPminus_spec p0 p);destruct (ZPminus p0 p);intro h;rewrite h.
simpl;rewrite ZPminus0;repeat rewrite mkPX_PX_c;constructor;
[rewrite cadd_assoc;rewrite (cadd_sym c3);apply ceq_refl|apply PolEq_refl].
simpl;rewrite ZPminuspos;repeat rewrite mkPX_PX_c;constructor;
[rewrite cadd_assoc;rewrite (cadd_sym c3);apply ceq_refl|apply PolEq_refl].
rewrite (Padd_sym (PX x p0 c3 )); rewrite (Padd_sym  (PX x p0 c3 + Pc c )(PX z (p0 + p1) c2));
simpl;rewrite ZPminuspos;repeat rewrite mkPX_PX_c;constructor;
[rewrite cadd_assoc;rewrite (cadd_sym c);apply ceq_refl|apply PolEq_refl].

generalize p c p0 c2; clear p c p0 c2;induction x;intros.
generalize (ZPminus_spec p p0);destruct (ZPminus p p0);intro h;rewrite h.
simpl;rewrite ZPminus0;rewrite Padd_sym;simpl;rewrite  Pol_addC_mkPX;
repeat rewrite mkPX_PX_c;constructor;[rewrite <- (cadd_sym c);apply cadd_assoc|apply PolEq_refl].
simpl;rewrite ZPminuspos;rewrite Padd_sym;simpl;rewrite  Pol_addC_mkPX;
repeat rewrite mkPX_PX_c;constructor;[rewrite <- (cadd_sym c);apply cadd_assoc|apply PolEq_refl].
simpl;rewrite ZPminusneg;rewrite Padd_sym;simpl;rewrite Pol_addC_mkPX;
repeat rewrite mkPX_PX_c;constructor;[rewrite <- (cadd_sym c);apply cadd_assoc|apply PolEq_refl].

generalize (ZPminus_spec p0 p1);destruct (ZPminus p0 p1);intro h;rewrite h.
simpl Pol_add at 2;rewrite ZPminus0;repeat rewrite mkPX_PX_c.
generalize (ZPminus_spec p p1);destruct (ZPminus p p1);intro h1;rewrite h1.
simpl Pol_add at 1;rewrite ZPminus0;simpl Pol_add at 4;rewrite ZPminus0;
repeat rewrite mkPX_PX_c.
simpl;rewrite ZPminus0; repeat rewrite mkPX_PX_c;constructor;[apply cadd_assoc|apply IHz].
simpl Pol_add at 1;rewrite ZPminuspos.
simpl Pol_add at 4;rewrite ZPminuspos;repeat rewrite mkPX_PX_c.
simpl;rewrite ZPminus0; rewrite mkPX_PX_c;constructor;[apply cadd_assoc|apply IHz].
rewrite Padd_sym.
simpl Pol_add at 1;rewrite ZPminuspos.
rewrite (Padd_sym(PX x p c )); simpl Pol_add at 4;
rewrite ZPminuspos;repeat rewrite mkPX_PX_c.
rewrite <- (Padd_sym (PX z (p + p2) c3));simpl; rewrite ZPminuspos;
repeat rewrite mkPX_PX_c;constructor;[
rewrite (cadd_sym c2 c3);rewrite cadd_assoc;apply ceq_refl|idtac].
rewrite (Padd_sym (PX z p2 c0 ));rewrite (Padd_sym (PX y p2 c0)).
rewrite <- IHx;rewrite Padd_sym;
apply Padd_ext_r.
simpl;rewrite ZPminus0;repeat rewrite mkPX_PX_c;constructor;
[rewrite  cadd_0_l;apply ceq_refl|apply PolEq_refl].
repeat rewrite (Padd_sym ( PX x p c)).
simpl Pol_add at 2;simpl Pol_add at 3;rewrite ZPminuspos;rewrite mkPX_PX_c.
generalize (ZPminus_spec p1 p);destruct (ZPminus p1 p);intro h1;rewrite h1.
simpl Pol_add at 1;rewrite ZPminus0.
simpl Pol_add at 4;rewrite ZPminuspos;repeat rewrite mkPX_PX_c.
simpl;rewrite ZPminus0;rewrite mkPX_PX_c;constructor.
rewrite <- (cadd_assoc c2 c). rewrite (cadd_sym c). rewrite cadd_assoc;apply ceq_refl.
rewrite <- (Padd_sym x). rewrite IHz . apply Padd_ext_l;apply Padd_sym.
rewrite <- Pplus_assoc.
simpl Pol_add at 1; repeat rewrite ZPminuspos.
simpl Pol_add at 4;rewrite ZPminuspos;repeat rewrite mkPX_PX_c.
rewrite <- (Padd_sym (PX z (p + p3) c3)) ;simpl;rewrite ZPminuspos;rewrite mkPX_PX_c.
constructor;[rewrite cadd_assoc;rewrite (cadd_sym c2);apply ceq_refl|auto].
rewrite (Padd_sym (PX z p3 c0 )).
rewrite (Padd_sym(PX y (p3 + p2) c0)).
rewrite <- IHx.
rewrite Padd_sym;apply Padd_ext_r.
simpl;rewrite ZPminuspos;rewrite mkPX_PX_c;constructor;[rewrite cadd_0_l;apply ceq_refl|apply PolEq_refl].
rewrite Padd_sym; simpl Pol_add at 1;rewrite ZPminuspos.
generalize (ZPminus_spec p2 p3);destruct (ZPminus p2 p3);intro h2;rewrite h2.
simpl Pol_add at 4;rewrite ZPminus0;repeat rewrite mkPX_PX_c.
simpl;rewrite ZPminuspos;repeat rewrite mkPX_PX_c.
constructor;[rewrite cadd_assoc;rewrite (cadd_sym c2);apply ceq_refl|auto].
rewrite IHz; apply Padd_ext_l.
simpl;rewrite ZPminus0;rewrite mkPX_PX_c;constructor;[apply cadd_0_l|apply Padd_sym].
rewrite Pplus_assoc;simpl Pol_add at 4;rewrite ZPminuspos.
simpl  Pol_add at 4;repeat rewrite mkPX_PX_c.
simpl;
rewrite ZPminuspos;rewrite mkPX_PX_c;constructor;[rewrite cadd_assoc;rewrite (cadd_sym c2);apply ceq_refl|auto].
rewrite IHz;apply Padd_ext_l.
rewrite Padd_sym;simpl;rewrite ZPminuspos;rewrite mkPX_PX_c.
constructor;[apply cadd_0_l|apply PolEq_refl].
rewrite Pplus_assoc.
rewrite (Padd_sym (PX y (p1 + p2) c2)); simpl Pol_add at 4;rewrite ZPminuspos.
repeat rewrite mkPX_PX_c.
simpl Pol_add at 3; rewrite ZPminuspos;rewrite mkPX_PX_c.
constructor;[apply cadd_assoc| auto].
rewrite  IHz; apply Padd_ext_l.
simpl;rewrite ZPminuspos;rewrite mkPX_PX_c.
constructor;[apply cadd_0_l|apply PolEq_refl].
rewrite (Padd_sym (PX y p0 c2)).
simpl Pol_add at 2;rewrite ZPminuspos;rewrite mkPX_PX_c.
generalize (ZPminus_spec p p0);destruct (ZPminus p p0);intro h1;rewrite h1.
simpl Pol_add at 1;rewrite ZPminus0;rewrite mkPX_PX_c.
simpl Pol_add at 4;rewrite ZPminus0.
rewrite mkPX_PX_c.
rewrite <- (Padd_sym (PX z (p0 + p2) c3));simpl;rewrite ZPminuspos.
rewrite mkPX_PX_c.
constructor;[rewrite cadd_assoc;rewrite (cadd_sym c);rewrite cadd_assoc;apply ceq_refl|auto].
rewrite <- (Padd_sym y); rewrite IHy.
rewrite <- (Padd_sym (x+y));apply PolEq_refl.
simpl Pol_add at 1;rewrite ZPminuspos;rewrite mkPX_PX_c.
simpl Pol_add at 4;rewrite ZPminuspos;rewrite mkPX_PX_c.
rewrite (Padd_sym  (PX (PX x p3 c0 + y) p0 (c ++ c2) ));simpl Pol_add at 3;rewrite ZPminuspos.
rewrite mkPX_PX_c.
constructor;[rewrite cadd_assoc;rewrite (cadd_sym c);rewrite cadd_assoc;apply ceq_refl|auto].
 rewrite <- ( Padd_sym y).
rewrite (Padd_sym (PX z p2 c0 ) (PX x p3 c0 + y)).
rewrite IHy;apply PolEq_refl.
rewrite Padd_sym;simpl Pol_add at 1; rewrite ZPminuspos;rewrite mkPX_PX_c.
rewrite (Padd_sym ( PX x p c ));simpl Pol_add at 4;rewrite ZPminuspos;rewrite mkPX_PX_c.
rewrite (Padd_sym (PX (PX y p3 c0 + x) p (c2 ++ c) )); simpl Pol_add at 3.
rewrite <- Pplus_assoc;rewrite ZPminuspos.
rewrite mkPX_PX_c;constructor;[rewrite cadd_assoc;apply ceq_refl|auto].
rewrite <- (Padd_sym( PX y p3 c0 + x));rewrite (Padd_sym (PX y p3 c0 ) x).
rewrite <- IHx; rewrite <- (Padd_sym x).
apply Padd_ext_r.
rewrite (Padd_sym (PX y p3 c0 )); simpl;rewrite ZPminuspos;rewrite mkPX_PX_c;constructor.
rewrite cadd_0_l;apply ceq_refl.
apply PolEq_refl.
Qed.

 Lemma   Padd_assoc: forall x y z, x + (y + z) != (x + y) + z.
intros;apply Padd_assoc1.
Qed.


 Lemma  Pmul_1_l    : forall x, P1* x != x.
unfold P1;induction x;simpl;unfold Pol_mul_Rat ;
case_c0_test c. unfold P0;constructor;apply ceq_sym;trivial.
case_c0_test  (c -- c1); [assert (c==c1);[ apply copp_eq;trivial|idtac]|idtac].
constructor;apply ceq_sym;trivial.
simpl;constructor;auto with c_spec;cgen.
rewrite mkPX_PX_c;rewrite Padd_0_r;constructor;[apply ceq_sym;trivial|auto].
rewrite mkPX_PX_c;case_c0_test (c -- c1). assert (c==c1). apply copp_eq;trivial.
simpl;constructor;[rewrite H2;apply cadd_0_r|auto].
simpl;constructor;auto.
rewrite cadd_0_r;apply cmul_1_l.
Qed.

Lemma Pmul_Rat_aux_c0 : forall P, Pol_mul_Rat_aux P c0 != P0.
induction P;simpl.
unfold P0;constructor;apply cmul_0_r.
rewrite mkPX_PX_c;unfold P0;constructor;[apply cmul_0_r| apply IHP].
Qed.

Lemma Pmul_Rat_aux_c1 : forall P, Pol_mul_Rat_aux P c1 != P.
induction P;simpl.
constructor;apply cmul_1_r.
rewrite mkPX_PX_c;constructor;[apply cmul_1_r| apply IHP].
Qed.

Lemma Pmul_Rat_aux_P0 : forall P c, P!=P0 -> Pol_mul_Rat_aux P c != P0.
induction P;intros;simpl.
inversion H;unfold P0;constructor;rewrite H2;apply cmul_0_l.
rewrite mkPX_PX_c;inversion H;unfold P0;constructor;[rewrite H2;apply cmul_0_l|auto].
Qed.

Lemma Pmul_Rat_aux_compc: forall P Q , P!=Q-> forall c, Pol_mul_Rat_aux P c != Pol_mul_Rat_aux Q c.
intros P Q H;induction H;intros;simpl.
constructor; rewrite H;apply ceq_refl.
rewrite mkPX_PX_c;constructor;[rewrite H;apply ceq_refl|auto].
apply Pmul_Rat_aux_P0; trivial.
rewrite mkPX_PX_c;constructor;[rewrite H;apply ceq_refl|apply Pmul_Rat_aux_P0; trivial].
repeat rewrite mkPX_PX_c;constructor;[rewrite H;apply ceq_refl|auto].
repeat rewrite mkPX_PX_c;constructor;[rewrite H;apply ceq_refl|auto].
rewrite IHPol_Eq;simpl.
rewrite mkPX_PX_c;constructor;[apply cmul_0_l|apply PolEq_refl].
repeat rewrite mkPX_PX_c;constructor;[rewrite H;apply ceq_refl|auto].
rewrite IHPol_Eq;simpl.
rewrite mkPX_PX_c;constructor;[apply cmul_0_l|apply PolEq_refl].
Qed.

Lemma Pmul_Rat_aux_compP : forall P  c c', c==c' ->Pol_mul_Rat_aux P c != Pol_mul_Rat_aux P c'.
induction P;intros;simpl.
constructor;rewrite H;apply ceq_refl.
repeat rewrite mkPX_PX_c;constructor;[rewrite H;apply ceq_refl|apply IHP;trivial].
Qed.

Lemma Pmul_Rat_aux_comp: forall P Q , P!=Q-> forall c c', c==c' ->Pol_mul_Rat_aux P c != Pol_mul_Rat_aux Q c'.
intros;apply PolEq_trans with (Pol_mul_Rat_aux P c').
apply Pmul_Rat_aux_compP;trivial.
apply Pmul_Rat_aux_compc;trivial.
Qed.

Lemma Pmul_Rat_aux_assoc : forall P c c' , Pol_mul_Rat_aux (Pol_mul_Rat_aux P c) c' != Pol_mul_Rat_aux P (c**c').
induction P;intros;simpl.
constructor;rewrite cmul_assoc;apply ceq_refl.
 rewrite (Pmul_Rat_aux_compc (mkPX (Pol_mul_Rat_aux P c2) p (c ** c2)) (PX(Pol_mul_Rat_aux P c2) p (c ** c2))).
apply  mkPX_PX_c.
simpl;repeat rewrite mkPX_PX_c.
constructor;[rewrite cmul_assoc;apply ceq_refl|auto].
Qed.

Lemma Pmul_Rat_aux_distr: forall P Q  c , Pol_mul_Rat_aux (P + Q) c != Pol_mul_Rat_aux P c + Pol_mul_Rat_aux Q c.
intros P Q; generalize P ;clear P;induction Q;intros.
simpl.
induction P;simpl.
constructor; apply cdistr_l.
rewrite Pol_addC_mkPX;repeat rewrite mkPX_PX_c;constructor;[rewrite cadd_sym;apply cdistr_l|apply PolEq_refl].
generalize c p ;clear c p ; induction P;intros.
simpl;repeat rewrite mkPX_PX_c;simpl;constructor;[apply cdistr_l|apply PolEq_refl].
generalize (ZPminus_spec p p0);destruct (ZPminus p p0);intros h;rewrite h.
simpl;rewrite ZPminus0;
rewrite (Pmul_Rat_aux_compc  (mkPX (P + Q) p0(c++ c3)) (PX (P + Q) p0 (c ++ c3)) ).
rewrite mkPX_PX_c;constructor;[apply ceq_refl|apply PolEq_refl].
repeat rewrite mkPX_PX_c.
simpl;rewrite ZPminus0;repeat rewrite mkPX_PX_c;constructor;cgen;auto with c_spec.
simpl;rewrite ZPminuspos;
rewrite (Pmul_Rat_aux_compc (mkPX (PX P p1 c0 + Q) p0 (c ++ c3)) (PX (PX P p1 c0 + Q) p0 (c ++ c3)) ).
rewrite mkPX_PX_c;constructor;[apply ceq_refl|apply PolEq_refl].
repeat rewrite mkPX_PX_c.
simpl;rewrite ZPminuspos;repeat rewrite mkPX_PX_c;constructor;cgen;auto with c_spec.
rewrite IHQ.
apply Padd_ext_l.
simpl;rewrite mkPX_PX_c;
constructor;[apply cmul_0_l|apply PolEq_refl].
rewrite (Pmul_Rat_aux_compc ((PX P p c + PX Q (p + p1) c3))(PX Q (p + p1) c3 + PX P p c )).
apply Padd_sym.
simpl;rewrite ZPminuspos.
rewrite (Pmul_Rat_aux_compc (mkPX (PX Q p1 c0 + P) p (c3 ++ c)) (PX (PX Q p1 c0 + P) p (c3++ c)) ).
rewrite mkPX_PX_c;constructor;[apply ceq_refl|apply PolEq_refl].
repeat rewrite mkPX_PX_c.
rewrite (Padd_sym (PX (Pol_mul_Rat_aux P c2) p (c ** c2) ));simpl;rewrite ZPminuspos.
repeat rewrite mkPX_PX_c.
constructor;[apply cdistr_l|auto].
rewrite (Pmul_Rat_aux_compc (PX Q p1 c0 + P) (P+PX Q p1 c0 ));try apply Padd_sym.
rewrite IHP;rewrite Padd_sym.
apply Padd_ext_l;simpl;rewrite mkPX_PX_c;constructor;[apply cmul_0_l|apply PolEq_refl].
Qed.


Lemma Pmul_Rat_distr: forall P Q  c , Pol_mul_Rat (P + Q) c != Pol_mul_Rat P c + Pol_mul_Rat Q c.
intros;unfold Pol_mul_Rat.
case_c0_test c.
rewrite Padd_0_l;apply PolEq_refl.
case_c0_test (c--c1). apply PolEq_refl.
apply Pmul_Rat_aux_distr.
Qed.

Lemma Pmul_Rat_compc: forall P Q , P!=Q-> forall c, Pol_mul_Rat P c != Pol_mul_Rat Q c.
intros P Q H;induction H;intros;unfold Pol_mul_Rat;case_c0_test c;try apply PolEq_refl;
case_c0_test (c--c1);(try constructor);trivial;
apply Pmul_Rat_aux_comp;try apply ceq_refl;try constructor;trivial.
Qed.

Lemma Pmul_Rat_compP: forall P c c', c==c'->Pol_mul_Rat P c != Pol_mul_Rat P c'.
induction P;intros.
 unfold Pol_mul_Rat;simpl;case_c0_test c2.
case_c0_test c'.
apply PolEq_refl.
case_c0_test (c'--c1). assert (c'==c1). apply copp_eq;trivial.
absurd (c0==c1);[apply c0_diff_c1|rewrite <- H1; rewrite <- H5;trivial].
simpl;unfold P0;constructor;
rewrite <- H;rewrite H1;rewrite cmul_0_r;apply ceq_refl.
case_c0_test (c2--c1).  assert (c2==c1). apply copp_eq;trivial.
case_c0_test c'.
absurd (c0==c1). apply c0_diff_c1. rewrite <- H5; rewrite <- H;trivial.
case_c0_test (c'--c1). assert (c'==c1). apply copp_eq;trivial.
constructor;apply ceq_refl.
simpl;constructor;apply ceq_sym;rewrite <- H;rewrite H3;apply cmul_1_r.
case_c0_test c'.
simpl;unfold P0;constructor;rewrite H;rewrite H3;apply cmul_0_r.
case_c0_test (c'--c1). assert (c'==c1). apply copp_eq;trivial.
simpl;constructor; rewrite H;rewrite H5;apply cmul_1_r.
simpl;constructor;rewrite H;apply ceq_refl.

unfold Pol_mul_Rat.
case_c0_test c2.
case_c0_test c'.
apply PolEq_refl.
case_c0_test (c'--c1). assert (c'==c1). apply copp_eq;trivial.
absurd (c0==c1);[apply c0_diff_c1|rewrite <- H1; rewrite <- H5;trivial].
simpl.
rewrite mkPX_PX_c;unfold P0;simpl;constructor.
rewrite <- H;rewrite H1;rewrite cmul_0_r;apply ceq_refl.
rewrite  (Pmul_Rat_aux_compP P c' c0).
rewrite <- H;trivial.
apply Pmul_Rat_aux_c0.
case_c0_test (c2--c1).  assert (c2==c1). apply copp_eq;trivial.
case_c0_test c'.
absurd (c0==c1). apply c0_diff_c1. rewrite <- H5; rewrite <- H;trivial.
case_c0_test (c'--c1). 
apply PolEq_refl.
simpl;rewrite mkPX_PX_c.
constructor.
rewrite <- H;rewrite H3;rewrite cmul_1_r;apply ceq_refl.
apply PolEq_sym;rewrite  (Pmul_Rat_aux_compP P c' c1).
rewrite <- H;trivial.
apply Pmul_Rat_aux_c1.
case_c0_test c'.
simpl;rewrite mkPX_PX_c.
unfold P0;constructor.
rewrite H;rewrite H3;apply cmul_0_r.
rewrite  (Pmul_Rat_aux_compP P c2 c0).
rewrite H;trivial.
apply Pmul_Rat_aux_c0.
case_c0_test (c'--c1). 
assert (c'==c1). apply copp_eq;trivial.
rewrite  (Pmul_Rat_aux_compP (PX P p c) c2 c1). rewrite H;trivial.
apply Pmul_Rat_aux_c1.
 apply Pmul_Rat_aux_compP;trivial;apply PolEq_refl.
Qed.

Lemma Pmul_Rat_comp: forall P Q , P!=Q-> forall c c', c==c'->Pol_mul_Rat P c != Pol_mul_Rat Q c'.
intros ;apply PolEq_trans with (Pol_mul_Rat P c').
apply  Pmul_Rat_compP;trivial.
apply  Pmul_Rat_compc;trivial.
Qed.

Lemma  Pmul_ext_l    : forall P Q x, P!=Q -> P* x != Q*x.
intros P Q x ; generalize P Q; clear P Q;induction x;intros;simpl.
unfold Pol_mul_Rat;case_c0_test c.
apply PolEq_refl.
case_c0_test (c -- c1). assert (c==c1);[apply copp_eq |idtac];auto.
apply Pmul_Rat_aux_comp;trivial;apply ceq_refl.
repeat rewrite mkPX_PX_c;simpl.
apply Padd_ext.
constructor;[apply ceq_refl|auto].
apply Pmul_Rat_comp;trivial;apply ceq_refl.
Qed.

Lemma  Pmul_0_r  : forall x, x * P0!= P0.
destruct x;simpl;unfold Pol_mul_Rat;
(assert (h: czero_test c0=true );[apply c0test_c0|rewrite h];apply PolEq_refl).
Qed.

Lemma  Pmul_P0_r  : forall x P , P!=P0 -> x * P!= P0.
intros x P;generalize x;clear x;induction P;intros;simpl;
unfold Pol_mul_Rat;inversion H.
case_c0_test c.
apply PolEq_refl.
case_c0_test (c -- c1). assert (c==c1);[apply copp_eq |idtac];auto.
absurd (c0==c1);[apply c0_diff_c1|rewrite <- H2;trivial].
rewrite (Pmul_Rat_aux_compP x c c0);try assumption;apply Pmul_Rat_aux_c0.
rewrite mkPX_PX_c;case_c0_test c.
rewrite Padd_0_r;unfold P0;constructor;[apply ceq_refl|auto].
case_c0_test (c -- c1). assert (c==c1);[apply copp_eq |idtac];auto.
rewrite Padd_P0_l.
unfold P0;constructor;try apply ceq_refl.
apply IHP;trivial.
absurd (c0==c1);[apply c0_diff_c1|rewrite <- H2;trivial].
rewrite Padd_P0_l.
unfold P0;constructor;[apply ceq_refl|apply IHP;trivial].
rewrite (Pmul_Rat_aux_compP x c c0);try assumption;apply Pmul_Rat_aux_c0.
Qed.

Lemma  Pmul_P0_l  : forall x P , P!=P0 -> P*x!= P0.
intros x P;generalize x;clear x;induction P;intros;simpl.
generalize c H;clear c H; induction x;intros.
simpl.
unfold Pol_mul_Rat;inversion H;subst;case_c0_test c.
apply PolEq_refl.
case_c0_test (c -- c1);auto.
simpl.
unfold P0;constructor;rewrite H2;apply cmul_0_l.
simpl.
unfold Pol_mul_Rat;rewrite mkPX_PX_c.
case_c0_test c.
rewrite Padd_0_r.
unfold P0;constructor;[apply ceq_refl|auto].
case_c0_test (c -- c1);trivial.
rewrite Padd_P0_r;trivial.
unfold P0;constructor;[apply ceq_refl|auto].
simpl.
unfold P0;constructor;[rewrite cadd_0_r;inversion H;rewrite H4;apply cmul_0_l|auto].
generalize p c H;clear p c H;induction x;intros;simpl;unfold Pol_mul_Rat;case_c0_test c.
apply PolEq_refl.
case_c0_test (c -- c1);trivial.
simpl.
inversion H;rewrite mkPX_PX_c;unfold P0;constructor;[rewrite H4;apply cmul_0_l|auto].
apply Pmul_Rat_aux_P0;trivial.
rewrite mkPX_PX_c;rewrite Padd_0_r;unfold P0;constructor;[apply ceq_refl|auto].
rewrite mkPX_PX_c;case_c0_test (c -- c1);trivial.
rewrite Padd_P0_r;trivial.
unfold P0;constructor;[apply ceq_refl|auto].
simpl.
rewrite Padd_P0_l.
unfold P0;constructor;[apply ceq_refl|auto].
rewrite mkPX_PX_c;unfold P0;constructor;[inversion H;subst|auto].
rewrite H4;apply cmul_0_l.
inversion H;apply Pmul_Rat_aux_P0;trivial.
Qed.

Lemma  Pmul_ext_r   : forall P Q x, P!=Q -> x*P != x*Q.
intros P Q x H;generalize x;clear x;induction H;intros;simpl.
apply Pmul_Rat_compP;trivial.
rewrite Padd_P0_l.
rewrite mkPX_PX_c;unfold P0;constructor;try apply ceq_refl.
apply Pmul_P0_r;trivial.
apply Pmul_Rat_compP;trivial.
rewrite Padd_P0_l.
rewrite mkPX_PX_c;unfold P0;constructor;try apply ceq_refl.
apply Pmul_P0_r;trivial.
apply Pmul_Rat_compP;trivial.
apply Padd_ext.
repeat rewrite mkPX_PX_c;constructor; [apply ceq_refl|apply IHPol_Eq].
apply Pmul_Rat_compP;trivial.
apply Padd_ext.
repeat rewrite mkPX_PX_c;constructor; [apply ceq_refl|rewrite  IHPol_Eq].
simpl;unfold Pol_mul_Rat.
assert (h: czero_test c0=true);[apply c0test_c0;apply ceq_refl|rewrite h].
rewrite Padd_0_r.
rewrite mkPX_PX_c;constructor;[apply ceq_refl|apply PolEq_refl].
apply Pmul_Rat_compP;apply ceq_sym;trivial.
apply Padd_ext.
repeat rewrite mkPX_PX_c;constructor;[apply ceq_refl|auto].
rewrite IHPol_Eq;simpl;rewrite Padd_P0_r.
unfold Pol_mul_Rat.
assert (h: czero_test c0=true);[apply c0test_c0;apply ceq_refl|rewrite h].
apply PolEq_refl.
rewrite mkPX_PX_c;constructor;[apply ceq_refl|apply PolEq_refl].
apply Pmul_Rat_compP;trivial.
Qed.

Lemma  Pmul_ext   : forall P Q  R S , P!=Q -> R!=S -> P* R!= Q*S.
intros;apply PolEq_trans with (P*S).
apply Pmul_ext_r;trivial.
apply Pmul_ext_l;trivial.
Qed.

Lemma Pmul_symPc : forall x c, x* (Pc c)!= (Pc c) *x.
induction x.
intros;simpl;unfold Pol_mul_Rat;case_c0_test c.
case_c0_test c2.
apply PolEq_refl.
case_c0_test(c2--c1).
unfold P0;constructor;trivial.
simpl;unfold P0;constructor;rewrite H0;apply cmul_0_l.
case_c0_test c2.
case_c0_test(c--c1).
unfold P0;constructor;apply ceq_sym;trivial.
simpl;unfold P0;constructor;apply ceq_sym;rewrite H1;apply cmul_0_l.
case_c0_test(c2--c1). assert (c2==c1). apply copp_eq;trivial.
case_c0_test(c--c1). assert (c==c1). apply copp_eq;trivial.
constructor;rewrite H3;trivial.
simpl;constructor;rewrite H3;rewrite cmul_1_l;apply ceq_refl.
case_c0_test(c--c1). assert (c==c1). apply copp_eq;trivial.
simpl;constructor;rewrite H4;apply cmul_1_l.
simpl;constructor;apply cmul_sym.
intros;simpl;unfold Pol_mul_Rat;case_c0_test c.
case_c0_test c2.
rewrite Padd_0_r;rewrite mkPX_PX_c;unfold P0;constructor;[apply ceq_refl|idtac].
rewrite <-  IHx;simpl.
unfold Pol_mul_Rat;rewrite H1;apply PolEq_refl.
case_c0_test(c2--c1).
rewrite Padd_0_r;rewrite mkPX_PX_c;constructor;trivial.
rewrite<- IHx;simpl;unfold Pol_mul_Rat;rewrite H1;rewrite H2;apply PolEq_refl.
rewrite Padd_0_r;simpl;repeat rewrite mkPX_PX_c;constructor;[rewrite H0;apply cmul_0_l| rewrite <- IHx;simpl].
unfold Pol_mul_Rat;rewrite H1;rewrite H2;apply PolEq_refl.
case_c0_test c2.
case_c0_test(c--c1). assert (c==c1). apply copp_eq;trivial.
rewrite Padd_P0_r. unfold P0;constructor;trivial.
rewrite mkPX_PX_c;unfold P0;constructor;[apply ceq_refl|auto].
rewrite <- IHx;simpl;unfold Pol_mul_Rat;rewrite H0;apply PolEq_refl.
rewrite Padd_P0_r.
simpl;unfold P0;constructor;rewrite H1;apply cmul_0_l.
rewrite mkPX_PX_c;unfold P0;constructor;[apply ceq_refl|rewrite <- IHx;simpl;unfold Pol_mul_Rat;rewrite H0;apply PolEq_refl].
case_c0_test(c2--c1).
assert (c2==c1). apply copp_eq;trivial.
case_c0_test(c--c1). assert (c==c1). apply copp_eq;trivial.
simpl;rewrite Pol_addC_mkPX .
rewrite mkPX_PX_c;constructor;[rewrite H3;rewrite cadd_0_l; trivial|rewrite <- IHx;simpl;unfold Pol_mul_Rat;rewrite H0;rewrite H1;apply PolEq_refl].
simpl;rewrite Pol_addC_mkPX;rewrite mkPX_PX_c;constructor.
rewrite cadd_0_l;rewrite H3;rewrite  cmul_1_l;apply ceq_refl.
rewrite <- IHx;simpl;unfold Pol_mul_Rat;rewrite H0;rewrite H1;apply PolEq_refl.
case_c0_test(c--c1). assert (c==c1). apply copp_eq;trivial.
simpl;rewrite Pol_addC_mkPX;repeat rewrite mkPX_PX_c.
constructor;[rewrite cadd_0_l;rewrite H4;apply cmul_1_l|auto].
rewrite <- IHx;simpl;unfold Pol_mul_Rat;rewrite H0;rewrite H1;apply PolEq_refl.
simpl;rewrite Pol_addC_mkPX;repeat rewrite mkPX_PX_c;constructor;
[rewrite cadd_0_l;apply cmul_sym|rewrite <- IHx;simpl;unfold Pol_mul_Rat;rewrite H0;rewrite H1;apply PolEq_refl].
Qed.

Lemma PX_pq_qp: forall P Q p q c c', c==c'->P != Q->PX (PX P p c0) q c != PX(PX Q q c0) p c'.
intros.
generalize (ZPminus_spec q p);destruct (ZPminus q p);intro h;rewrite h.
constructor;trivial.
constructor;trivial;apply ceq_refl.
rewrite Pplus_comm;constructor;trivial.
rewrite Pplus_comm;constructor;try apply ceq_refl.
constructor;trivial;apply ceq_refl.
rewrite Pplus_comm;constructor;trivial.
apply ceq_sym;trivial.
rewrite Pplus_comm;constructor;[apply ceq_refl|idtac].
constructor;[apply ceq_refl|apply PolEq_sym;trivial].
Qed.

Add Morphism Pol_mul: Pmul_ex.
intros ;apply Pmul_ext;trivial.
Qed.

Lemma Pmul_Xpc_Y: forall  x y :Pol, forall p c, (PX y p c) * x!= PX (y*x)p c0 + (Pol_mul_Rat x c).
induction x.
intros;simpl. unfold Pol_mul_Rat. case_c0_test c. case_c0_test c2.
rewrite Padd_0_r;unfold P0;constructor;try apply ceq_refl; unfold P0;constructor;apply ceq_refl.
case_c0_test (c2--c1). assert (c2==c1). apply copp_eq;trivial.
rewrite Padd_P0_r. unfold P0;constructor;trivial.
unfold P0;constructor;try apply ceq_refl; apply PolEq_refl.
simpl;unfold P0 at 1;constructor;try apply PolEq_refl;rewrite H0;rewrite cadd_0_r;rewrite cmul_0_l;apply ceq_refl.
case_c0_test (c--c1). assert (c==c1). apply copp_eq;trivial. case_c0_test c2.
rewrite Padd_0_r; constructor;trivial;apply PolEq_refl.
case_c0_test (c2--c1). assert (c2==c1). apply copp_eq;trivial. simpl.
constructor;[rewrite cadd_0_r;rewrite H2;trivial|apply PolEq_refl].
simpl;constructor;[rewrite H2;rewrite cadd_0_r;rewrite cmul_1_l;apply ceq_refl| apply PolEq_refl].
case_c0_test c2. rewrite Padd_0_r;simpl;apply mkPX_PX;rewrite H2;apply cmul_0_l.
case_c0_test (c2--c1). assert (c2==c1). apply copp_eq;trivial;simpl;
apply mkPX_PX;rewrite cadd_0_r;rewrite H4;apply cmul_1_l.
simpl;apply mkPX_PX;rewrite cadd_0_r;rewrite H4;apply cmul_1_l.
simpl;apply mkPX_PX;rewrite cadd_0_r;apply cmul_sym.

(*cas général*)
intros;unfold Pol_mul_Rat; case_c0_test c. case_c0_test c2. 
rewrite Padd_0_r;simpl;unfold Pol_mul_Rat;rewrite H;rewrite Padd_0_r.
repeat rewrite mkPX_PX_c.
apply PolEq_trans with (PX (PX (y * x) p0 c0 + Pol_mul_Rat x c2) p c0).
constructor;[apply ceq_refl|apply IHx].
unfold Pol_mul_Rat;rewrite H1.
apply PolEq_trans with (PX (PX (y * x) p c0 ) p0 c0 ).
apply PolEq_trans with (PX (PX (y * x) p0 c0 ) p c0).
constructor;[apply ceq_refl|apply Padd_0_r].
apply PX_pq_qp;[apply ceq_refl|apply PolEq_refl].
constructor;[apply ceq_refl|rewrite Padd_0_r].
apply PolEq_sym;apply mkPX_PX;apply ceq_refl.
case_c0_test (c2--c1). assert (c2==c1). apply copp_eq;trivial.
simpl Pol_mul;unfold Pol_mul_Rat; rewrite H;rewrite Padd_0_r.
rewrite (mkPX_PX (PX y p0 c2 * x) p c0 c0). apply ceq_refl.
apply PolEq_trans with (PX (   PX (y * x) p0 c0 + Pol_mul_Rat x c2 ) p c0 ). 
constructor;[apply ceq_refl|apply IHx].
apply PolEq_sym;apply PolEq_trans with ( ( PX (PX (y * x) p0 c0 ) p c0 ) + PX x p c). apply Padd_ext_l.
apply PolEq_sym.
rewrite (PX_pq_qp  (y * x) (y * x) p0 p c0 c0 ). apply ceq_refl. apply PolEq_refl.
constructor;[apply ceq_refl | rewrite Padd_0_r;apply PolEq_sym;apply mkPX_PX;apply ceq_refl].
simpl ;rewrite ZPminus0.
apply mkPXP_PXQ;[rewrite cadd_0_l;trivial|unfold Pol_mul_Rat;rewrite H1;rewrite H2;apply PolEq_refl].
simpl;unfold Pol_mul_Rat;rewrite H;rewrite Padd_0_r.
rewrite (Padd_ext_l  (PX (mkPX (y * x) p c0 + P0) p0 c0 ) (PX(PX (y * x) p0 c0)p c0)).
rewrite (PX_pq_qp (y * x) (y * x) p0 p c0 c0). apply ceq_refl. apply PolEq_refl.
constructor;[apply ceq_refl|rewrite Padd_0_r;apply mkPX_PX;apply ceq_refl].
rewrite (mkPX_PX (Pol_mul_Rat_aux x c2) p (c ** c2) c0).
rewrite H0;apply cmul_0_l.
simpl;rewrite ZPminus0.
apply mkPX_ok;[rewrite cadd_0_l;apply ceq_refl|idtac].
rewrite IHx.
unfold Pol_mul_Rat;rewrite H1;rewrite H2;apply PolEq_refl.

case_c0_test c2. 
rewrite Padd_0_r;simpl.
rewrite (mkPX_PX (PX y p0 c2 * x) p c0  c0). apply ceq_refl.
unfold Pol_mul_Rat;rewrite H.
case_c0_test (c --c1). assert (c==c1). apply copp_eq;trivial.
apply PolEq_trans with (PX ( PX (y * x) p0 c0 + Pol_mul_Rat x c2) p c0 + PX y p0 c2 ).
apply Padd_ext_l; constructor;[apply ceq_refl| apply IHx].
unfold Pol_mul_Rat;rewrite H0.
apply PolEq_trans with (PX (PX (y * x) p c0) p0 c0 + PX y p0 c2 ). apply Padd_ext_l.
rewrite (PX_pq_qp (y * x) (y * x) p p0 c0 c0). apply ceq_refl. apply PolEq_refl.
constructor;[apply ceq_refl|apply Padd_0_r].
simpl;rewrite ZPminus0.
apply mkPXP_PXQ;[rewrite H1;apply cadd_0_l|apply PolEq_sym;apply Padd_ext_l;apply mkPX_PX;apply ceq_refl].
simpl;rewrite (Padd_ext (PX (PX y p0 c2 * x) p c0 )(PX ( PX (y * x) p0 c0 + Pol_mul_Rat x c2) p c0 )
 (mkPX (Pol_mul_Rat_aux y c) p0 (c2 ** c)) (PX (Pol_mul_Rat_aux y c) p0 c0)).
constructor;[apply ceq_refl|apply IHx].
apply mkPX_PX;rewrite H1;apply cmul_0_l.
unfold Pol_mul_Rat; rewrite H0.
rewrite (Eq_PX_PX c0 c0  (PX (y * x) p0 c0 + P0) (PX (y * x) p0 c0 )). apply ceq_refl.
apply Padd_0_r.
rewrite (PX_pq_qp  (y * x)  (y * x) p0 p c0 c0). apply ceq_refl. apply PolEq_refl.
simpl;rewrite ZPminus0.
apply mkPXP_PXQ;[apply cadd_0_l|apply Padd_ext_l;apply PolEq_sym;apply mkPX_PX;apply ceq_refl].
case_c0_test (c2 --c1). assert (c2==c1). apply copp_eq;trivial.
simpl Pol_mul.
rewrite (mkPX_PX (PX y p0 c2 * x) p c0 c0 ). apply ceq_refl.
rewrite (Eq_PX_PX c0 c0 (PX y p0 c2 * x) (PX (y * x) p0 c0 + Pol_mul_Rat x c2)). apply ceq_refl.
apply IHx.
unfold Pol_mul_Rat;rewrite H0 ;rewrite H1;rewrite H.
case_c0_test (c --c1). assert (c==c1). apply copp_eq;trivial.
apply PolEq_trans with (PX (PX (y * x) p0 c0 ) p c0 + PX x p c0 + PX y p0 c2) .
apply Padd_ext_l;simpl;rewrite ZPminus0.
apply PolEq_sym;apply mkPX_PX;apply cadd_0_l.
rewrite (PX_pq_qp (y * x) (y * x) p0 p c0 c0). apply ceq_refl. apply PolEq_refl.
rewrite <- Padd_assoc.
apply PolEq_sym;apply PolEq_trans with (PX (PX (y * x) p c0) p0 c0  + PX y p0 c0 + PX x p c). apply Padd_ext_l. simpl;rewrite ZPminus0.
apply PolEq_sym;apply mkPXP_PXQ;
[apply cadd_0_l|apply Padd_ext_l;apply PolEq_sym ;apply mkPX_PX ;apply ceq_refl].
rewrite <- Padd_assoc;apply Padd_ext_r.
rewrite Padd_sym; generalize (ZPminus_spec p p0);destruct (ZPminus p p0);intro h;rewrite h;
simpl;[rewrite ZPminus0|rewrite ZPminuspos|rewrite ZPminusneg];
 (apply mkPX_ok;[rewrite H6;rewrite H3;apply cadd_sym|apply PolEq_refl]).
simpl Pol_mul_Rat_aux.
assert (PX (PX (y * x) p0 c0 + x) p c0 != PX (PX (y * x) p0 c0 ) p c0 + PX x p c0).
simpl;rewrite ZPminus0.
apply PolEq_sym;apply mkPX_PX;apply cadd_0_l.
rewrite H5.
rewrite <- Padd_assoc.
assert ( PX (mkPX (y * x) p c0 + Pol_mul_Rat_aux y c) p0 c0 != 
PX (PX (y * x) p c0) p0 c0 + PX (Pol_mul_Rat_aux y c)p0 c0).
simpl ;rewrite ZPminus0.
apply PolEq_sym;apply mkPXP_PXQ. apply cadd_0_l.
apply Padd_ext_l;apply PolEq_sym;apply mkPX_PX ; apply ceq_refl.
assert (PX (mkPX (y * x) p c0 + Pol_mul_Rat_aux y c) p0 c0 != PX (PX (y * x) p0 c0 )p c0 
+ PX ( Pol_mul_Rat_aux y c) p0 c0).
rewrite  (PX_pq_qp (y * x) (y * x)  p0 p c0 c0 ). apply ceq_refl. apply PolEq_refl.
simpl;rewrite ZPminus0.
apply PolEq_sym;apply mkPXP_PXQ. apply cadd_0_l.
rewrite (mkPX_PX (y * x) p c0 c0). apply ceq_refl.
apply PolEq_refl.
assert (PX (mkPX (y * x) p c0 + Pol_mul_Rat_aux y c) p0 c0 !=
PX (mkPX (y * x) p c0 ) p0 c0 + PX(Pol_mul_Rat_aux y c) p0 c0 ).
simpl;rewrite ZPminus0.
apply PolEq_sym;apply mkPX_PX ;apply cadd_0_l.
rewrite H8.
rewrite <- Padd_assoc.
apply Padd_ext.
rewrite (PX_pq_qp (y * x) (y * x) p0 p c0 c0). apply ceq_refl . apply PolEq_refl.
constructor;[apply ceq_refl| apply PolEq_sym;apply mkPX_PX;apply ceq_refl].
rewrite (mkPX_PX (Pol_mul_Rat_aux y c) p0 (c2 ** c) c).
rewrite H3;apply cmul_1_l.
rewrite Padd_sym; generalize (ZPminus_spec p0 p);destruct (ZPminus p0 p);intro h;rewrite h;
simpl;[rewrite ZPminus0|rewrite ZPminuspos|rewrite ZPminusneg];
(apply mkPX_ok;[apply cadd_sym|apply PolEq_refl]).
simpl.
unfold Pol_mul_Rat; rewrite H.
case_c0_test (c --c1). assert (c==c1). apply copp_eq;trivial.
rewrite (mkPX_PX  (PX y p0 c2 * x) p c0 c0). apply ceq_refl.
assert (PX (PX y p0 c2 * x) p c0 != PX(PX (y * x) p0 c0 + Pol_mul_Rat x c2)p c0).
constructor;[apply ceq_refl|apply IHx].
rewrite H5.
assert (PX (PX (y * x) p0 c0 + Pol_mul_Rat x c2) p c0 != PX (PX (y * x) p0 c0 )p c0 + PX(Pol_mul_Rat x c2) p c0).
simpl;rewrite ZPminus0.
apply PolEq_sym;apply mkPX_PX ;apply cadd_0_l.
rewrite H6.
rewrite (PX_pq_qp  (y * x)   (y * x)  p0 p c0 c0). apply ceq_refl. apply PolEq_refl.
rewrite <- Padd_assoc. rewrite <-(Padd_sym (PX y p0 c2)).
rewrite Padd_assoc. simpl Pol_add at 2;rewrite ZPminus0.
rewrite (mkPX_PX (PX (y * x) p c0 + y) p0 (c0 ++ c2) c2).
apply cadd_0_l.
unfold Pol_mul_Rat;rewrite H0;rewrite H1.

rewrite (Eq_PX_PX c0 c0 (mkPX (y * x) p c0 + y) (PX (y * x) p c0 + y)).
apply ceq_refl . apply Padd_ext_l;apply mkPX_PX;apply ceq_refl.
rewrite (mkPX_PX (Pol_mul_Rat_aux x c2) p (c ** c2) c2).
rewrite H4;apply cmul_1_l.
generalize (ZPminus_spec p0 p);destruct (ZPminus p0 p);intro h;rewrite h;
simpl;[rewrite ZPminus0|rewrite ZPminuspos|rewrite ZPminusneg];
(apply mkPX_ok;[apply cadd_sym|apply PolEq_refl]).

simpl.

rewrite (mkPX_PX (PX y p0 c2 * x) p c0  c0). apply ceq_refl.
rewrite (Eq_PX_PX c0 c0 (PX y p0 c2 * x)  (PX (y * x) p0 c0 + Pol_mul_Rat x c2)).
apply ceq_refl. apply IHx.
assert (PX (PX (y * x) p0 c0 + Pol_mul_Rat x c2) p c0 != PX (PX (y * x) p0 c0)p c0 + PX (Pol_mul_Rat x c2) p c0).
simpl;rewrite ZPminus0.
apply PolEq_sym;apply mkPX_PX ; apply cadd_0_l.
rewrite H3.
rewrite <- Padd_assoc.
assert (PX (mkPX (y * x) p c0 + Pol_mul_Rat_aux y c) p0 c0 != (PX (PX (y * x) p c0)p0 c0)+PX(Pol_mul_Rat_aux y c) p0 c0).
simpl;rewrite ZPminus0.
apply PolEq_sym;apply mkPXP_PXQ;[apply cadd_0_l|
apply Padd_ext_l;apply PolEq_sym;apply mkPX_PX;apply ceq_refl].
rewrite H4.
rewrite <-Padd_assoc;apply Padd_ext.
apply PX_pq_qp. apply ceq_refl. apply PolEq_refl.
rewrite Padd_sym; rewrite (mkPX_PX   (Pol_mul_Rat_aux y c) p0 (c2 ** c) (c2**c)). apply ceq_refl.
rewrite (mkPX_PX (Pol_mul_Rat_aux x c2) p (c ** c2)(c2**c)). apply cmul_sym.
unfold Pol_mul_Rat;rewrite H0;rewrite H1.
generalize (ZPminus_spec p0 p);destruct (ZPminus p0 p);intro h;rewrite h;
simpl;[rewrite ZPminus0|rewrite ZPminuspos|rewrite ZPminusneg];
(apply mkPX_ok;[apply cadd_sym|apply PolEq_refl]).
Qed.

Lemma    Pmul_sym    : forall x y, x * y != y * x.
intros x y; generalize x;clear x;induction y.
intros;apply Pmul_symPc.
simpl.
intros;rewrite (mkPX_PX (x * y) p c0 c0). apply ceq_refl.
apply PolEq_sym; rewrite (Eq_PX_PX c0 c0  (x*y)(y*x) ).
apply ceq_refl. apply IHy. 
apply Pmul_Xpc_Y.
Qed.

Lemma Pmul_Rat_aux_assocP: forall x y c , Pol_mul_Rat_aux (x * y) c != x * Pol_mul_Rat_aux y c.
induction y.
intros;simpl;induction x.
simpl;unfold Pol_mul_Rat; case_c0_test c. 
assert (c**c2==c0). rewrite H0;apply cmul_0_l.
case_c0_test (c**c2). 
simpl;unfold P0;constructor; apply cmul_0_l.
case_c0_test (c**c2 -- c1). assert (c**c2==c1). apply copp_eq;trivial.
absurd (c0==c1);[apply c0_diff_c1|rewrite <- H1;rewrite <- H5;apply ceq_refl].
simpl.
constructor;rewrite H1;rewrite cmul_0_r;apply cmul_0_l.
case_c0_test (c -- c1). assert (c==c1). apply copp_eq;trivial.
case_c0_test (c**c2). 
assert (c2 ==c0). 
generalize H4; rewrite H2;rewrite cmul_1_l;auto.
simpl;unfold P0;constructor;rewrite H5;apply cmul_0_r.
case_c0_test (c**c2--c1). assert (c**c2==c1). apply copp_eq;trivial.
simpl;constructor.
rewrite H2 in H6. generalize H6; rewrite cmul_1_l; intro H7;rewrite H7;apply cmul_1_r.
simpl;constructor.
rewrite H2;rewrite cmul_1_l;apply ceq_refl.
simpl.
case_c0_test( (c ** c2)). unfold P0;constructor; rewrite <- cmul_assoc;rewrite H2;apply cmul_0_r.
case_c0_test (c**c2 -- c1). assert (c**c2==c1). apply copp_eq;trivial.
constructor;rewrite <- cmul_assoc;rewrite H4;apply cmul_1_r.
constructor;rewrite <- cmul_assoc;apply ceq_refl.
unfold Pol_mul_Rat.
case_c0_test c.
case_c0_test (c**c2). 
unfold P0;simpl;constructor; apply cmul_0_l.
case_c0_test (c**c2 -- c1). assert (c**c2==c1). apply copp_eq;trivial.
absurd (c0==c1);[apply c0_diff_c1| generalize H4; rewrite H0;rewrite cmul_0_l;auto].
simpl;rewrite mkPX_PX_c.
constructor;[rewrite H0;rewrite cmul_0_l;rewrite cmul_0_r;apply ceq_refl |idtac].
rewrite (Pmul_Rat_aux_compP x (c**c2) c0);[rewrite H0;apply cmul_0_l|apply Pmul_Rat_aux_c0].
case_c0_test (c--c1). assert (c==c1). apply copp_eq;trivial.
case_c0_test (c ** c2).
simpl;rewrite mkPX_PX_c.  assert (c2==c0).
generalize H4;rewrite H2 ;rewrite cmul_1_l ;auto.
unfold P0;constructor;[rewrite H5;apply cmul_0_r|rewrite (Pmul_Rat_aux_compP x c2 c0);trivial; apply Pmul_Rat_aux_c0].
case_c0_test (c**c2 -- c1). assert (c**c2==c1). apply copp_eq;trivial.
simpl;rewrite mkPX_PX_c.
assert (c2==c1). generalize H6;rewrite H2;rewrite cmul_1_l;auto.
constructor;[repeat rewrite H7;rewrite cmul_1_r;apply ceq_refl| rewrite (Pmul_Rat_aux_compP x c2 c1);trivial; apply Pmul_Rat_aux_c1].
simpl;repeat rewrite mkPX_PX_c;constructor.
rewrite H2;rewrite cmul_1_l;apply ceq_refl.
apply Pmul_Rat_aux_compP;rewrite H2;rewrite cmul_1_l;apply ceq_refl.
case_c0_test (c**c2 ).
simpl.
rewrite (Pmul_Rat_aux_compc (mkPX (Pol_mul_Rat_aux x c) p (c3 ** c)) (PX (Pol_mul_Rat_aux x c) p (c3 ** c))).
apply mkPX_PX_c.
simpl;rewrite mkPX_PX_c.
unfold P0;constructor.
rewrite <- cmul_assoc;rewrite H2;apply cmul_0_r.
generalize IHx; unfold Pol_mul_Rat; rewrite H;rewrite H1; rewrite H0;trivial.
case_c0_test (c**c2 -- c1). assert (c**c2==c1). apply copp_eq;trivial. 
simpl.
rewrite (Pmul_Rat_aux_compc (mkPX (Pol_mul_Rat_aux x c) p (c3 ** c)) (PX (Pol_mul_Rat_aux x c) p (c3 ** c))).
apply mkPX_PX_c.
simpl;rewrite mkPX_PX_c.
constructor.
rewrite <- cmul_assoc;rewrite H4;apply cmul_1_r.
generalize IHx; unfold Pol_mul_Rat; rewrite H;rewrite H1; rewrite H0;rewrite H2;trivial.

simpl.
rewrite (Pmul_Rat_aux_compc (mkPX (Pol_mul_Rat_aux x c) p (c3 ** c)) (PX (Pol_mul_Rat_aux x c) p (c3 ** c))).
apply mkPX_PX_c.
simpl;repeat rewrite mkPX_PX_c.
constructor.
rewrite <- cmul_assoc;apply ceq_refl.
generalize IHx; unfold Pol_mul_Rat; rewrite H;rewrite H1; rewrite H0;rewrite H2;trivial.

(*icic
assert (h:czero_test (c ** c2)=false). rewrite <- H3; apply czero_test_ok;trivial.
rewrite h;simpl;case_c0_test (c**c2 -- c1). assert (c**c2==c1). apply copp_eq;trivial.
constructor.
assert (c2 == c1).  generalize H7;rewrite H2;rewrite cmul_1_l ;trivial.
rewrite H8;apply cmul_1_r.
constructor.
rewrite H4;apply ceq_refl.
case_c0_test (c ** c2). simpl.
unfold P0;constructor;rewrite <- cmul_assoc;rewrite H2; apply cmul_0_r.
case_c0_test (c**c2 -- c1). assert (c**c2==c1). apply copp_eq;trivial.
simpl;unfold P0;constructor; rewrite <- cmul_assoc;rewrite H4; apply cmul_1_r.
simpl;constructor;rewrite cmul_assoc;apply ceq_refl.
unfold Pol_mul_Rat; case_c0_test c. 
assert (c**c2==c0). rewrite H0;apply cmul_0_l.
assert (h:czero_test (c ** c2)=true);[apply c0test_c0;trivial|rewrite h].
simpl;unfold P0;constructor; apply cmul_0_l.
case_c0_test (c -- c1). assert (c==c1). apply copp_eq;trivial.
case_c0_test (c2). 
assert (c**c2 ==c0). rewrite H4;apply cmul_0_r.
assert (h:czero_test (c ** c2)=true);[apply c0test_c0;trivial|rewrite h].
simpl;rewrite (mkPX_PX  (Pol_mul_Rat_aux x c2) p (c3 ** c2)  c0).
rewrite H4; apply cmul_0_r.
unfold P0;constructor;try apply ceq_refl.
induction x ;simpl.
unfold P0; constructor;rewrite H4;apply cmul_0_r.
rewrite (mkPX_PX  (Pol_mul_Rat_aux x c2) p0 (c4 ** c2)  c0). 
rewrite H4; apply cmul_0_r.
unfold P0;constructor;try apply ceq_refl.
apply IHx0.
unfold Pol_mul_Rat;rewrite h;rewrite H;rewrite H0.
rewrite ( Pmul_Rat_aux_compP x c2 c0);trivial.
apply Pmul_Rat_aux_c0.
assert (c**c2 ==c2). rewrite H2; apply cmul_1_l.
assert (h:czero_test (c ** c2)=false). rewrite <- H3; apply czero_test_ok;trivial.
rewrite h.
simpl.
case_c0_test (c**c2 -- c1). assert (c**c2==c1). apply copp_eq;trivial.
rewrite (mkPX_PX  (Pol_mul_Rat_aux x c2) p (c3 ** c2) (c3 ** c2) );try apply ceq_refl.
assert (c2==c1). generalize H7; rewrite H2;rewrite cmul_1_l;auto.
constructor.
rewrite H8; apply cmul_1_r.
rewrite( Pmul_Rat_aux_compP x c2 c1);[trivial|apply Pmul_Rat_aux_c1].
apply mkPX_ok;[rewrite H4;apply ceq_refl|idtac].
apply Pmul_Rat_aux_compP;rewrite H4;apply ceq_refl.
case_c0_test (c ** c2). simpl.
generalize  ( Pmul_Rat_aux_compc  (mkPX (Pol_mul_Rat_aux x c) p (c3 ** c))
 (PX (Pol_mul_Rat_aux x c) p (c3 ** c))).
intros;rewrite H3.
apply mkPX_PX; apply ceq_refl.
simpl.
rewrite (mkPX_PX (Pol_mul_Rat_aux (Pol_mul_Rat_aux x c) c2) p (c3 ** c ** c2)  c0).
rewrite <- cmul_assoc;rewrite H2;apply cmul_0_r.
unfold P0;constructor; try apply ceq_refl.
simpl.
rewrite Pmul_Rat_aux_assoc.
rewrite (Pmul_Rat_aux_compP x (c**c2) c0);trivial.
apply Pmul_Rat_aux_c0.
case_c0_test (c**c2 -- c1). assert (c**c2==c1). apply copp_eq;trivial.
simpl.
rewrite (Pmul_Rat_aux_compc (mkPX (Pol_mul_Rat_aux x c) p (c3 ** c))(PX (Pol_mul_Rat_aux x c) p (c3 ** c))).
apply mkPX_PX ;apply ceq_refl.
simpl.
apply mkPXP_PXQ.
rewrite <- cmul_assoc;rewrite H4;apply cmul_1_r.
generalize IHx;unfold Pol_mul_Rat;rewrite H;rewrite H0;rewrite H1;rewrite H2;auto.
simpl.
rewrite (Pmul_Rat_aux_compc (mkPX (Pol_mul_Rat_aux x c) p (c3 ** c))(PX (Pol_mul_Rat_aux x c) p (c3 ** c))).
apply mkPX_PX ;apply ceq_refl.
simpl.
apply mkPX_ok.
rewrite cmul_assoc;apply ceq_refl.
generalize IHx;unfold Pol_mul_Rat;rewrite H;rewrite H0;rewrite H1;rewrite H2;auto.
*)
intros;simpl.
rewrite (mkPX_PX  (Pol_mul_Rat_aux y c2) p (c ** c2) (c**c2)).
apply ceq_refl.
rewrite Pmul_Rat_aux_distr.
simpl.
rewrite (Pmul_Rat_aux_compc (mkPX (x * y) p c0)  (PX (x * y) p c0) ).
apply mkPX_PX;apply ceq_refl.
rewrite (mkPX_PX (x * Pol_mul_Rat_aux y c2) p c0 c0); try apply ceq_refl.
simpl.
rewrite (mkPX_PX (Pol_mul_Rat_aux (x * y) c2) p (c0 ** c2) c0).
apply cmul_0_l.
apply Padd_ext.
constructor.
apply ceq_refl.
apply IHy.
unfold Pol_mul_Rat.
case_c0_test c.
case_c0_test (c**c2).
simpl.
unfold P0;constructor;apply cmul_0_l.
case_c0_test (c **c2-- c1). assert (c**c2==c1). apply copp_eq;trivial.
absurd (c0==c1);[apply c0_diff_c1|generalize H4;rewrite H0;rewrite cmul_0_l;trivial].
rewrite (Pmul_Rat_aux_compP x (c**c2) c0).
rewrite H0;apply cmul_0_l.
simpl;rewrite Pmul_Rat_aux_c0.
unfold P0;constructor;apply cmul_0_l.

case_c0_test (c -- c1). assert (c==c1). apply copp_eq;trivial.
case_c0_test (c**c2). 
rewrite (Pmul_Rat_aux_compP x (c2) c0).
generalize H4;rewrite H2;rewrite cmul_1_l;auto.
apply Pmul_Rat_aux_c0.
case_c0_test (c**c2 -- c1). assert (c**c2==c1). apply copp_eq;trivial.
rewrite (Pmul_Rat_aux_compP x (c2) c1).
generalize H6;rewrite H2;rewrite cmul_1_l;auto.
apply Pmul_Rat_aux_c1.
apply Pmul_Rat_aux_compP .
rewrite H2;rewrite cmul_1_l;apply ceq_refl.
case_c0_test (c**c2).
simpl.
rewrite Pmul_Rat_aux_assoc.
rewrite (Pmul_Rat_aux_compP x (c**c2) c0);trivial.
apply Pmul_Rat_aux_c0.
case_c0_test (c**c2 -- c1). assert (c**c2==c1). apply copp_eq;trivial.
rewrite Pmul_Rat_aux_assoc.
rewrite (Pmul_Rat_aux_compP x (c**c2) c1);trivial.
apply Pmul_Rat_aux_c1.
apply Pmul_Rat_aux_assoc.
Qed.


Lemma Pmul_Rat_Pmul : forall x y c, Pol_mul_Rat (x*y) c != x * Pol_mul_Rat y c.
intros;simpl.
unfold Pol_mul_Rat. case_c0_test c. rewrite Pmul_0_r;apply PolEq_refl.
case_c0_test (c -- c1). assert (c==c1). apply copp_eq;trivial.
apply PolEq_refl.
apply Pmul_Rat_aux_assocP.
Qed.

Lemma Pmul_assoc_Pc : forall x y c, x * (y * Pc c)!= (x *y) * Pc c.
intros.
simpl.
unfold Pol_mul_Rat. case_c0_test c. apply Pmul_0_r.
case_c0_test ( c--c1). assert (c==c1). apply copp_eq;trivial.
apply PolEq_refl.
apply PolEq_sym;apply Pmul_Rat_aux_assocP.
Qed.

 Lemma   Pdistr_l    : forall x y z, (x + y) * z != (x * z) + (y * z).
intros x y z;generalize x y;clear x y ;induction z;intros.
simpl;apply Pmul_Rat_distr;simpl.
simpl.
rewrite (mkPXP_PXQ ((x + y) * z)  (x * z + y * z) p c0 c0); try apply ceq_refl.
apply IHz.
apply PolEq_trans with (PX (x * z ) p c0 + PX(y*z) p c0 + Pol_mul_Rat (x + y) c).
apply Padd_ext_l.
simpl;rewrite ZPminus0.
apply PolEq_sym;apply mkPX_PX;apply cadd_0_l.
rewrite (mkPX_PX (x * z) p c0 c0);try apply ceq_refl.
rewrite (mkPX_PX (y * z) p c0 c0);try apply ceq_refl.
rewrite <-( Padd_assoc (PX (x * z) p c0 ) (Pol_mul_Rat x c )).
rewrite(Padd_sym (Pol_mul_Rat x c )).
rewrite <- Padd_assoc.
rewrite  <-Padd_assoc.
apply Padd_ext_r.
apply Padd_ext_r.
rewrite Pmul_Rat_distr.
apply Padd_sym.
Qed.

 Lemma   Pmul_assoc  : forall x y z, x * (y * z) != (x * y) * z.
intros; generalize x y;clear x y ;induction z;intros;simpl.
rewrite Pmul_Rat_Pmul; apply PolEq_refl.
rewrite (mkPX_PX (y * z) p c0 c0);try apply ceq_refl.
rewrite (mkPX_PX  (x * y * z) p c0 c0);try apply ceq_refl.
rewrite Pmul_Rat_Pmul.
rewrite(Eq_PX_PX c0 c0  (x * y * z)   (x * (y * z) ));try apply ceq_refl.
rewrite IHz;apply PolEq_refl.
rewrite Pmul_sym;rewrite Pdistr_l.
apply Padd_ext.
rewrite Pmul_sym.
simpl.
rewrite (mkPX_PX (x * (y * z)) p c0 c0);try apply ceq_refl.
unfold Pol_mul_Rat.
assert (czero_test c0 = true). apply c0test_c0 ;apply ceq_refl.
rewrite H.
apply Padd_0_r.
apply Pmul_sym.
Qed.


Lemma PsubX_PaddX : forall x y fsub fadd p, (forall P, fadd P != fsub P) -> Pol_subX fsub y p x!= Pol_addX fadd (-y) p x.
induction x;intros.
simpl;apply PolEq_refl.
generalize (ZPminus_spec p0 p);destruct (ZPminus p0 p);intro h;rewrite h.
simpl;rewrite ZPminus0.
apply mkPX_ok;[apply ceq_refl|apply PolEq_sym;apply H].
simpl.
rewrite ZPminusneg.
apply mkPX_ok;try apply ceq_refl.
apply IHx.
apply  H.
simpl.
rewrite ZPminuspos.
apply mkPX_ok.
apply ceq_refl.
apply PolEq_sym;apply H.
Qed.

 Lemma   Psub_def    : forall x y, x - y != x + -y.
intros; generalize x;clear x;induction y.
intros;simpl.
generalize c;clear c;induction x;intros.
simpl.
constructor;apply csub_def.
simpl.
constructor;[ rewrite cadd_sym;apply csub_def|apply PolEq_refl].
generalize p c;clear p c;induction x;intros.
simpl.
rewrite (mkPX_PX (- y) p (-- c) (-- c)); try apply ceq_refl.
simpl;constructor;[apply csub_def|apply PolEq_refl].
generalize (ZPminus_spec p0 p);destruct (ZPminus p0 p);intros h;rewrite h;
[simpl;rewrite ZPminus0|simpl;rewrite ZPminuspos|idtac].
repeat rewrite mkPX_PX_c.
simpl;rewrite ZPminus0.
rewrite mkPX_PX_c.
constructor;[apply csub_def|apply IHy].
repeat rewrite mkPX_PX_c.
simpl;rewrite ZPminuspos;rewrite mkPX_PX_c;constructor;[apply csub_def|apply IHy].
simpl.
rewrite (mkPX_PX (-y) (p0+p1)(--c)(--c)).
apply ceq_refl.
simpl;rewrite ZPminusneg.
repeat rewrite mkPX_PX_c.
constructor;[apply csub_def|apply PsubX_PaddX].
intros;apply PolEq_sym;apply IHy.
Qed.

  Lemma   Popp_def    : forall x, x + (- x) != P0.
induction x;simpl.
unfold P0;constructor;cgen;auto with c_spec.
rewrite mkPX_PX_c;simpl;rewrite ZPminus0;rewrite mkPX_PX_c.
unfold P0;constructor;auto with c_spec.
Qed.

Definition Pol_theory :  Setoid_Ring_Theory Pol_Eq Pol_add Pol_mul P1 P0 Pol_opp Peqb.
constructor.
exact Padd_sym.
exact Padd_assoc.
exact Pmul_sym.
exact Pmul_assoc.
exact Padd_0_l.
exact Pmul_1_l.
exact Popp_def.
exact Pdistr_l.
induction x;destruct y;simpl.
intro ;apply Eq_Pc_Pc.
apply ceq_prop ;trivial.
intro h;contradiction.
intro;contradiction.
assert (h := Pcompare_Eq_eq p p0); destruct ((p ?= p0)%positive Eq);try discriminate; try (simpl;intros;contradiction).
rewrite h ; auto.
caseEq  (Peqb x y);try (simpl;intros;contradiction).
caseEq (ceqb c c2);simpl;intros;try (simpl;intros;contradiction).
constructor;[apply ceq_prop;rewrite H;unfold Is_true;auto|apply IHx;auto].
rewrite H0;auto.
Defined.

Lemma Padd_comp : forall P Q  R S, P !=Q -> R!=S -> P+R != Q+S.
exact Padd_ext.
Qed.

Lemma Pmul_comp: forall P Q  R S, P !=Q -> R!=S -> P*R != Q*S.
exact Pmul_ext. 
Qed.


Lemma Popp_0: forall P, P!=P0 -> -P!= P0.
induction P.
intro;simpl.
inversion H. unfold P0;constructor; rewrite H2;apply copp_0.
intro H;inversion H;simpl.
rewrite mkPX_PX_c;unfold P0.
constructor.
rewrite H2;apply copp_0.
apply IHP;trivial.
Qed.

Lemma Popp_comp: forall P Q, P!=Q -> -P != -Q.
intros P Q H;induction H;simpl; repeat rewrite mkPX_PX_c;constructor;try rewrite H0;try rewrite H; try apply ceq_refl.
 apply Popp_0;trivial.
 apply Popp_0;trivial.
apply IHPol_Eq.
rewrite IHPol_Eq.
simpl; rewrite mkPX_PX_c.
constructor;[apply copp_0|apply PolEq_refl].
rewrite IHPol_Eq;simpl; rewrite mkPX_PX_c;
constructor;[apply copp_0|apply PolEq_refl].
Qed.

Add Morphism Pol_opp:Popp_ex.
exact Popp_comp.
Qed.


Add Setoid Ring Pol Pol_Eq Pol_Setoid Pol_add Pol_mul P1 P0 Pol_opp Peqb Padd_ex  Pmul_ex
 Popp_ex  Pol_theory [Pc PX].

End Pol1.
