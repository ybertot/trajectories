Require Import Setoid.

Definition Is_true (b:bool) : Prop:=
match b with
|true => True
|false => False
end.

Reserved Notation "x ++ y" (at level 50, left associativity).
Reserved Notation "x -- y" (at level 50, left associativity).
Reserved Notation "x ** y" (at level 40, left associativity).
Reserved Notation "-- x" (at level 35, right associativity).
Reserved Notation "x == y" (at level 70, no associativity).
Reserved Notation "x ?== y" (at level 70, no associativity).


Reserved Notation "x + y" (at level 50, left associativity).
Reserved Notation "x -y" (at level 50, left associativity).
Reserved Notation "x * y" (at level 40, left associativity).
Reserved Notation "- x" (at level 35, right associativity).
Reserved Notation " x != y "(at level 70, no associativity).


Reserved Notation "x '+ y" (at level 50, left associativity).
Reserved Notation "x '- y" (at level 50, left associativity).
Reserved Notation "x '* y" (at level 40, left associativity).
Reserved Notation "'- x" (at level 35, right associativity).
Reserved Notation " x '= y "(at level 70, no associativity).



Section COEF_RING.


 Variable C : Set.

 Record coef_set : Type := mk_cset{
   CO : C;
   CI : C;
   Ceq : C -> C -> Prop;
   Cadd : C -> C -> C;
   Cmul : C -> C -> C;
   Csub : C -> C -> C;
   Copp : C -> C;
   Czero_test : C -> bool
 }.

 Variable coef : coef_set.
 
 Notation "x ++ y" := (Cadd coef x y).
 Notation "x ** y":= (Cmul coef x y).
 Notation "-- x" := (Copp coef x).
 Notation "x -- y" := (Csub coef x y).
 Notation "x == y" := (Ceq coef x y).

 Record coef_eq :Prop := mk_ceq{
   Ceq_refl : forall x, x == x;
   Ceq_sym : forall x y, x == y -> y == x;
   Ceq_trans : forall x y z, x == y -> y == z -> x == z;
   Cadd_ext : 
     forall x1 x2 y1 y2, x1 == x2 -> y1 == y2 -> x1 ++ y1 == x2 ++ y2;
   Cmul_ext :
     forall x1 x2 y1 y2, x1 == x2 -> y1 == y2 -> x1 ** y1 == x2 ** y2;
   Copp_ext :
     forall x1 x2, x1 == x2 -> -- x1 == -- x2
 }.

 Variable eq_th : coef_eq.

(* Ring structure over coefficients*)
 Record coef_theory : Prop := mk_ct {
   Cadd_0_l    : forall x, (CO coef) ++ x == x;
   Cadd_sym    : forall x y, x ++ y == y ++ x;
   Cadd_assoc  : forall x y z, x ++ (y ++ z) == (x ++ y) ++ z;
   Cmul_1_l    : forall x, (CI coef)** x == x;
   Cmul_sym    : forall x y, x ** y == y ** x;
   Cmul_assoc  : forall x y z, x ** (y ** z) == (x ** y) ** z;
   Cdistr_l    : forall x y z, (x ++ y) ** z == (x ** z) ++ (y ** z);
   Csub_def    : forall x y, x -- y == x ++ --y;
   Copp_def    : forall x, x ++ (-- x) == (CO coef)
 }.

End COEF_RING.



Section POL1 .


 Variable C:Set.
 Variable coef : (coef_set C).
 Variable eq_th : (coef_eq C coef).

 Definition ceq:=(Ceq C coef).

 Definition cadd:=(Cadd C coef).
 Definition cmul:=(Cmul C coef).
 Definition copp:= (Copp C coef).
 Definition csub:=(Csub C coef).
 Definition c0:=(CO C coef).
 Definition c1:=(CI C coef).

 Notation "x ++ y" := (cadd x y).
 Notation "x ** y" := (cmul x y).
 Notation "x -- y" := (csub x y).
 Notation " -- x" := (copp x).
 Notation "x == y":=(ceq x y).

 Lemma ceq_refl : forall x, x==x.
 Proof.
   exact(Ceq_refl C coef eq_th).
 Qed.

 Lemma ceq_sym : forall x y, x==y -> y==x.
 Proof.
   exact (Ceq_sym C coef eq_th).
 Qed.

 Lemma ceq_trans : forall x y z, x == y -> y == z -> x == z.
 Proof.
   exact(Ceq_trans C coef eq_th).
 Qed.

 Lemma cadd_ext : forall x1 x2 y1 y2, x1 == x2 -> y1 == y2 -> x1 ++ y1 == x2 ++ y2.
 Proof.
   exact (Cadd_ext C coef eq_th).
 Qed.

 Lemma cmul_ext :forall x1 x2 y1 y2, x1 == x2 -> y1 == y2 -> x1 ** y1 == x2 ** y2.
 Proof.
   exact (Cmul_ext C coef eq_th).
 Qed.

 Lemma copp_ext :  forall x1 x2, x1 == x2 -> -- x1 == -- x2.
 Proof.
   exact(Copp_ext C coef eq_th).
 Qed.

 

 Variable CT : (coef_theory C coef).


 Lemma cadd_0_l : forall x, c0 ++ x == x.
 Proof.
   exact (Cadd_0_l C coef CT). 
 Qed.

 Lemma cadd_sym : forall x y, x ++ y == y ++ x.
 Proof.
   exact (Cadd_sym C coef CT).
 Qed.

 Lemma cadd_assoc : forall x y z, x ++ (y ++ z) == (x ++ y) ++ z.
 Proof.
   exact (Cadd_assoc C coef CT).
 Qed.

 Lemma cmul_1_l : forall x, c1** x == x.
 Proof.
   exact (Cmul_1_l C coef CT).
 Qed.

 Lemma cmul_sym  :forall x y, x ** y == y ** x.
 Proof.
   exact (Cmul_sym C coef CT).
 Qed.

 Lemma cmul_assoc : forall x y z, x ** (y ** z) == (x ** y) ** z.
 Proof.
   exact (Cmul_assoc  C coef CT).
 Qed.

 Lemma cdistr_l : forall x y z, (x ++ y) ** z == (x ** z) ++ (y ** z).
   Proof.
   exact(Cdistr_l C coef CT).
   Qed.

 Lemma csub_def : forall x y, x -- y == x ++ --y.
 Proof.
   exact (Csub_def  C coef CT).
 Qed.

 Lemma copp_def : forall x, x ++ (-- x) == c0.
 Proof.
   exact (Copp_def  C coef CT).
 Qed.



 Lemma Coef_setoid : Setoid_Theory C ceq.
 Proof.   
   constructor.
   exact ceq_refl.
   exact ceq_sym.
   exact ceq_trans.
 Qed.

 Add Setoid C ceq Coef_setoid.

 Add Morphism cadd: Cadd_ex.
 Proof.
   exact cadd_ext. 
 Qed.
 
 Add Morphism cmul: Cmul_ex.
 Proof.
   exact cmul_ext.
 Qed.

 Add Morphism copp: Copp_ex.
 Proof. 
   exact copp_ext.
 Qed.

 Hint Resolve ceq_sym ceq_trans ceq_refl
   cadd_ext cmul_ext copp_ext : ceq_spec.



  (*pour jouer : reecriture setoid a une occurence apres l'abstraction
   par pattern*)
 Ltac rewrite_pattern t :=
   match goal with
     |- ?a ?b => let H := fresh "H" in
       (assert (H : forall c1 c2, c1==c2 -> (a c1)->(a c2));
	 intros;simpl in *; eauto with ceq_spec;
	   apply (H _ _ t))
     |_ => idtac "not an application"
   end.
 
  (*some lemmas about the ring structure of coefficients C*)



 Lemma copp_0 : -- c0==c0 .
 Proof. 
   rewrite <- (cadd_0_l  (--c0)).
   unfold ceq.
   unfold copp;unfold c0.
   apply copp_def.
 Qed.
 
 Lemma cmul_0_l : forall x, c0 ** x == c0.
 Proof.
   intro x; setoid_replace (c0**x) with ((c0++c1)**x ++ --x).
   rewrite (cdistr_l c0 c1 x);rewrite (cmul_1_l x).
   rewrite <- (cadd_assoc (c0**x) x (--x)).
   rewrite (copp_def x);rewrite (cadd_sym (c0**x) c0).
   rewrite (cadd_0_l (c0**x));unfold ceq;apply ceq_refl.
   rewrite (cadd_0_l c1); rewrite (cmul_1_l x).
   rewrite (copp_def x);unfold ceq;apply ceq_refl.
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
   rewrite (cmul_0_l y);rewrite (cadd_0_l (--(x**y)));unfold ceq;apply ceq_refl.
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
   rewrite (cadd_sym  x (y++z));unfold ceq;apply ceq_refl.
 Qed.

 Lemma cadd_assoc2 : forall x y z, (y ++ x) ++ z == (y ++ z) ++ x.
 Proof.
   intros; rewrite <- (cadd_assoc y x z);
     rewrite (cadd_sym x z); apply cadd_assoc.
 Qed.

 Lemma cmul_assoc1 : forall x y z, (x ** y) ** z == (y ** z) ** x.
 Proof.
   intros;rewrite <-(cmul_assoc x y z).
   rewrite (cmul_sym x (y**z));unfold ceq;apply ceq_refl.
 Qed.
 
 Lemma cmul_assoc2 : forall x y z, (y ** x) ** z == (y ** z) ** x.
 Proof.
   intros; rewrite <- (cmul_assoc y x z);
     rewrite (cmul_sym x z); apply cmul_assoc.
 Qed.

 Lemma copp_opp : forall x, -- --x == x.
 Proof.
   intros x; rewrite <- (cadd_0_l (-- --x)).
   rewrite <- (copp_def x).
   rewrite <- (cadd_assoc x (--x) (-- --x)); rewrite (copp_def  (--x)).
   rewrite (cadd_sym x c0);apply(cadd_0_l x).
 Qed.




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

 
 
(* one variable polynomials over C*)
 Inductive Pol1:Set:=
 |Pc : C-> Pol1
 |PX : Pol1 -> C -> Pol1.

 Definition PO:= (Pc c0).
 Definition PI:=(Pc c1).


(*Equality over polynomials,not in normal forms*)
 Inductive Pol1Eq:Pol1 -> Pol1 -> Prop :=
   |Eq1_Pc_Pc : forall p q: C, (ceq p q)->(Pol1Eq (Pc p) (Pc q))
   |Eq1_Pc_PX :
     forall p q: C, forall Q1:Pol1, (ceq p q)->(Pol1Eq Q1 PO)->(Pol1Eq (Pc p) (PX Q1 q))
   |Eq1_PX_Pc :
     forall p q: C, forall P1:Pol1, (ceq p q)->(Pol1Eq P1 PO)->(Pol1Eq (PX P1 p) (Pc q))
   |Eq1_PX_PX :
     forall p q:C, forall P1 Q1 :Pol1, (ceq p q)->(Pol1Eq P1 Q1)->(Pol1Eq (PX P1 p) (PX Q1 q)).

(*Addition over polynomials*)
 Fixpoint Pol1_add(P Q:Pol1){struct P}:Pol1 :=
   match P, Q with
     |Pc p, Pc q => Pc (p ++ q)
     |Pc p, PX Q1 q => PX Q1 (p ++ q)
     |PX P1 p, Pc q => PX P1 (p ++ q)
     |PX P1 p, PX Q1 q  => PX (Pol1_add P1 Q1) (p ++ q)
   end.

(*Product poly * cst*)
 Fixpoint Pol1_cmul(P:Pol1)(q:C){struct P}:Pol1:=
   match P with
     |Pc p => Pc (q** p)
     |PX P1 p => PX (Pol1_cmul P1 q) (p ** q)
   end.

(*Product over polynomial*)
 Fixpoint Pol1_mul(P Q:Pol1){struct P}:Pol1 :=
   match P with
     |Pc p  => Pol1_cmul Q p
     |PX P1 p=> (Pol1_add (PX (Pol1_mul P1 Q)  c0) (Pol1_cmul Q p))
   end.

(*Opposite *)
 Fixpoint Pol1_opp(P:Pol1):Pol1 :=
   match P with
     |Pc p => Pc (-- p)
     |PX P1 p => PX (Pol1_opp P1) (-- p)
   end.

(*Subtraction*)
 Definition Pol1_sub(P Q:Pol1):=(Pol1_add P (Pol1_opp Q)).


(* Some notations *)
 Notation "x != y" := (Pol1Eq x y).
 Notation "x + y" := (Pol1_add x y).
 Notation "x * y" := (Pol1_mul x y).
 Notation "x - y" := (Pol1_sub x y).
 Notation "- x" := (Pol1_opp x).
 



(*Pol1Eq is a setoid equality*)

 Lemma Pol1Eq_refl :forall P, P != P.
 Proof.
   induction P;constructor; unfold ceq;try apply ceq_refl;trivial.
 Qed.

 Lemma Pol1Eq_sym : forall P Q, P != Q -> Q != P.
 Proof.
   intros P Q; induction 1; constructor; unfold ceq;try apply ceq_sym;trivial.
 Qed.

 Lemma Pol1Eq_transO : forall P, P!=PO -> forall Q, P != Q-> Q != PO.
 Proof.
induction P; inversion 1;subst; try constructor;try apply (ceq_trans c c0 q);trivial;
 intros;inversion H0;subst;unfold PO; constructor.
unfold ceq;apply (ceq_trans q c c0); auto;
apply ceq_sym;auto.
unfold ceq;apply (ceq_trans q c c0); auto;
apply ceq_sym;auto.
auto.
unfold ceq;apply (ceq_trans q c c0); auto;
apply ceq_sym;auto.
unfold ceq;apply (ceq_trans q c c0); auto;
apply ceq_sym;auto.
apply IHP; trivial;apply Pol1Eq_sym;trivial.
 Qed.


 Lemma Pol1Eq_trans : forall P Q, P != Q -> forall R, Q != R -> P != R.
 Proof.
intros P Q;induction 1;intros; inversion H0;subst; try constructor;
   try apply (ceq_trans p q q0);trivial;inversion H1; subst; constructor;
   try apply (ceq_trans p q); trivial; try apply IHPol1Eq; trivial.
   apply (Pol1Eq_transO (Pc p0)); trivial.
   apply (Pol1Eq_transO (PX P1 p0));trivial.
   apply Pol1Eq_sym;trivial.
   apply Pol1Eq_sym;trivial.
Qed.

(*equality over polynomials is a morphism*)
Lemma Pol1_setoid : Setoid_Theory Pol1 Pol1Eq.
 Proof.
 constructor.
 exact Pol1Eq_refl.
 exact Pol1Eq_sym.
 intros; apply Pol1Eq_trans with y;trivial.
 Qed.

Add Setoid Pol1 Pol1Eq Pol1_setoid.



(*Pol1 constructors are morphisms *)

Add Morphism PX : PX_ext.
 Proof.
  intros;constructor;trivial.
  Qed.

Add Morphism Pc : Pc_ext.
 Proof.
  intros;constructor;trivial.
 Qed.


 Lemma Pol1add_sym : forall P Q, P+Q != Q+P.
  Proof.
    induction P;destruct Q;simpl;constructor;auto;
    try  apply cadd_sym; apply Pol1Eq_refl.
  Qed. 

 Lemma Pol1add_extO :
 forall P, P != PO -> forall Q R, Q != R -> Q != P + R.
 Proof.
  induction P; intros H Q R; inversion 1;inversion H;subst;
  unfold PO; simpl;constructor;
  try (assert (A : c == c0); trivial; rewrite A; clear A; cgen);trivial.
  apply Pol1Eq_sym ; apply IHP;trivial;apply Pol1Eq_sym;trivial.
  apply (Pol1Eq_trans P1 PO);trivial; apply Pol1Eq_sym;trivial.
  auto.
 Qed.

 Lemma Pol1add_extO':
 forall P, P != PO -> forall Q R, Q != R -> Q != R + P.
 Proof.
   intros.
   apply (Pol1Eq_trans Q (P+R));
   [apply Pol1add_extO;trivial| apply Pol1add_sym].
 Qed.

 Lemma Pol1add_0_l : forall P, PO+P != P.
 Proof.
  induction P;unfold PO;simpl;constructor;try apply cadd_0_l.
  apply Pol1Eq_refl.
  Qed.


 Lemma Pol1add_0_l' : forall P, P+PO!=P.
 Proof.
   intros.
   apply (Pol1Eq_trans (P +PO) (PO+P));
   [apply Pol1add_sym|apply Pol1add_0_l].
  Qed.

 
 Lemma Pol1add_ext:
 forall P1 P2, P1 != P2 -> forall Q1 Q2, Q1 != Q2 -> P1 + Q1 != P2 + Q2.
 Proof. 
induction 1; intros A1 A2;induction 1; subst;simpl;
 try constructor; unfold ceq;unfold cadd;try apply cadd_ext;auto.
apply (Pol1Eq_trans (Q1 + Q0) (PO + PO));
  [auto | apply Pol1add_0_l].
  apply (Pol1Eq_trans P1 PO);trivial;apply Pol1Eq_sym;trivial.
  apply (Pol1add_extO Q1);trivial.
  apply (Pol1Eq_trans P1 PO);trivial;apply Pol1Eq_sym;trivial.
  apply Pol1Eq_sym; apply Pol1add_extO;trivial;apply Pol1Eq_sym;trivial.
  apply Pol1Eq_sym; apply Pol1add_extO;trivial.
  apply Pol1Eq_sym; trivial.
  apply Pol1add_extO';trivial.
  apply Pol1Eq_sym; apply Pol1add_extO';
  [trivial |apply Pol1Eq_sym;trivial].
 Qed.

(*Pol addition is a morphism*)
 Add Morphism Pol1_add : Pol1_add_ext.
 Proof.
 intros; apply Pol1add_ext;trivial.
 Qed.


 Lemma Pol1_cmul_spec : forall P c, Pol1_cmul P c != P * (Pc c).
 Proof.
  induction P;intros;simpl;constructor.
  apply cmul_sym.
rewrite (cadd_0_l (c**c2)); unfold ceq;apply ceq_refl.
  auto.
 Qed.

 Lemma Pol1_add_spec : forall P Q p q,
 (PX P p) + (PX Q q) != PX (P+Q) (p ++ q).
  Proof.
   induction P;destruct Q; simpl;constructor; try constructor;unfold ceq;
   try apply ceq_refl ; apply Pol1Eq_refl.
  Qed.

 Lemma Pol1add_assoc : forall P Q R, P + (Q + R) != (P+Q)+R.
  Proof.
  induction P;induction Q; destruct R; intros;simpl;constructor;
  try rewrite (cadd_assoc c c2 c3);unfold ceq; try apply ceq_refl;try apply Pol1Eq_refl.
  apply IHP.
  Qed.

 Lemma Pol1_distr_PX : 
 forall P Q q, P*(PX Q q) != (PX (P*Q) c0) + (Pol1_cmul P q).
  Proof.
   induction P;destruct Q; intros;
   try  (simpl;constructor; rewrite (cadd_0_l (q**c)); apply ceq_refl).
   simpl;constructor;
   [rewrite (cadd_0_l (q ** c)) | constructor]; unfold ceq;apply ceq_refl.
   simpl;constructor.
   rewrite (cadd_0_l (q ** c)); unfold ceq;apply ceq_refl.
   constructor.
   unfold ceq;apply ceq_refl.
   apply Pol1Eq_refl.
   Opaque Pol1_add.
   simpl.
   rewrite (IHP (Pc c2) q).
   rewrite (Pol1_cmul_spec P q).
   rewrite (Pol1_add_spec (PX (P * Pc c2) c0 + P * Pc q) (Pc (c ** c2)) c0 (q ** c)).
   rewrite (Pol1_add_spec (PX (P * Pc c2) c0 + Pc (c ** c2)) (P * Pc q)  c0 (c**q)).
   constructor.
   rewrite (cmul_sym q c); unfold ceq;apply ceq_refl.
   rewrite <- (Pol1add_assoc (PX (P * Pc c2) c0) (P * Pc q ) (Pc (c ** c2))).
   rewrite (Pol1add_sym (P*(Pc q)) (Pc (c ** c2))).
   rewrite (Pol1add_assoc (PX (P * Pc c2) c0) (Pc (c ** c2)) (P*(Pc q))).
   apply Pol1Eq_refl.
   Opaque Pol1_add.
   simpl.
   rewrite (IHP (PX Q c2) q).
   rewrite (Pol1_cmul_spec P q).
   rewrite (Pol1_cmul_spec Q c).
   rewrite (Pol1_add_spec (PX (P * PX Q c2) c0 + P * Pc q) (PX (Q *Pc c) (c2 ** c)) c0 (q**c)).
   rewrite (Pol1_add_spec (PX (P * PX Q c2) c0 + PX (Q * Pc c) (c2 ** c)) (P * Pc q) c0 (c**q)).
   constructor.
   rewrite (cmul_sym q c); unfold ceq;apply ceq_refl.
   rewrite <- (Pol1add_assoc (PX (P * PX Q c2) c0 ) (P * Pc q) (PX (Q * Pc c) (c2 ** c))).
   rewrite (Pol1add_sym (P * Pc q) (PX (Q * Pc c) (c2 ** c))).
   rewrite (Pol1add_assoc (PX (P * PX Q c2) c0 ) (PX (Q * Pc c) (c2** c)) (P*Pc q)).
   apply Pol1Eq_refl.
   Transparent Pol1_add.
  Qed.

 Lemma Pol1mul_sym : forall P Q, P*Q != Q*P.
 Proof.
  induction P;intros; destruct Q;simpl;constructor; 
  try cgen; try apply cmul_sym;unfold ceq; try apply ceq_refl.
  apply Pol1_cmul_spec.
  apply Pol1Eq_sym;apply Pol1_cmul_spec.
  rewrite (Pol1_distr_PX P Q c2).
  rewrite (Pol1_distr_PX Q P c).
  rewrite (IHP Q).
  rewrite <- (Pol1add_assoc (PX (Q * P) c0) (Pol1_cmul Q c) (Pol1_cmul P c2)).
  rewrite (Pol1add_sym (Pol1_cmul Q c) (Pol1_cmul P c2)).
  rewrite  (Pol1add_assoc (PX (Q * P) c0) (Pol1_cmul P c2) (Pol1_cmul Q c) ).
  apply Pol1Eq_refl.
 Qed.

 Lemma Pol1_distr_PX_r : forall Q q P,
  (PX Q q)*P != (PX (Q*P) c0) +(Pol1_cmul P q).
 Proof.
 intros.
 rewrite (Pol1mul_sym (PX Q q) P);
 rewrite (Pol1mul_sym Q P);
 apply Pol1_distr_PX.
 Qed.



 Add Morphism Pol1_cmul : Pol1_cmul_ext.
 induction 1;intros;simpl;constructor;unfold PO in *;
 try rewrite (cmul_sym p c);try rewrite (cmul_sym q c2);
unfold ceq;unfold cmul; try apply cmul_ext;trivial.
 induction Q1;simpl;constructor;
 inversion_clear H0; subst;
 try rewrite H2;try  apply cmul_0_l; try apply cmul_0_r.
 apply IHQ1;trivial;intros;simpl in *.
 assert (PX (Pol1_cmul Q1 c) (c3 ** c) != Pc (c2 ** c0));try exact (IHPol1Eq H1).
 inversion_clear H4.
 rewrite (cmul_0_r c2);auto.
 simpl in *.
 rewrite <- (cmul_0_r c2);auto.
 auto. 
 Qed.


 Lemma Pol1mul_0_l : forall Q, (Pc c0) * Q != (Pc c0).
 Proof.
  induction Q; intros; simpl;constructor.
  apply cmul_0_l.
  apply cmul_0_r.
  rewrite (Pol1_cmul_spec Q c0).
  rewrite (Pol1mul_sym Q (Pc c0)).
  auto.
 Qed.

 Lemma Pol1mul_0_r : forall Q, Q*(Pc c0)!= Pc c0.
 Proof.
  intros; rewrite (Pol1mul_sym Q (Pc c0)); apply Pol1mul_0_l.
 Qed.

 Lemma Pol1mul_ext_0_l : forall P Q, P != (Pc c0) -> P *Q !=(Pc c0).
 Proof.
  induction P;destruct Q;intros;inversion H;subst; simpl;constructor;
  try  rewrite H2; try apply cmul_0_l;try apply cmul_0_r.
  rewrite (Pol1_cmul_spec Q c0);apply Pol1mul_0_r.
  rewrite H3; rewrite (cmul_0_l c2); apply cadd_0_l.
  auto.
  rewrite (cadd_0_l (c2**c));rewrite H3; apply cmul_0_r.
  rewrite H3.
  rewrite (Pol1_cmul_spec Q c0).
  rewrite (Pol1mul_0_r Q).
  assert (P*PX Q c2 != Pc c0).
  auto.
  rewrite H0;simpl;rewrite (cadd_0_l c0); apply Pol1Eq_refl.
 Qed. 

 Lemma Pol1mul_ext_0_r : forall P Q, P != (Pc c0) -> Q*P !=(Pc c0).
 Proof.
  intros. 
  rewrite (Pol1mul_sym Q P).
  apply Pol1mul_ext_0_l;trivial.
 Qed.

 Lemma Pol1mul_ext : forall P1 P2,
  P1 != P2 -> forall Q1 Q2, Q1 != Q2 -> P1*Q1 != P2*Q2.
  Proof.
   induction 1; intros;unfold PO in *.
   rewrite (Pol1mul_sym (Pc p) Q1); rewrite (Pol1mul_sym (Pc q) Q2).
   rewrite <- (Pol1_cmul_spec Q1 p); rewrite <- (Pol1_cmul_spec Q2 q).
   rewrite H0;rewrite H; apply Pol1Eq_refl.
   rewrite (Pol1mul_sym (PX Q1 q ) Q2).
   rewrite (Pol1_distr_PX Q2 Q1 q).
   assert (PX (Q2 * Q1) c0 != Pc c0).
   constructor;unfold ceq;try apply ceq_refl.
   rewrite (Pol1mul_sym Q2 Q1).
   unfold PO in *;rewrite <- (Pol1mul_0_l Q2).
   apply (IHPol1Eq Q2 Q2 (Pol1Eq_refl Q2)).
   rewrite H2.
   rewrite (Pol1mul_sym (Pc p) Q0).
   rewrite <- (Pol1_cmul_spec Q0 p).
   rewrite H1;rewrite H;fold PO; apply Pol1Eq_sym;apply Pol1add_0_l.
   rewrite (Pol1mul_sym (PX P1 p) Q1).
   rewrite (Pol1_distr_PX Q1 P1 p).
   assert (PX (Q1*P1) c0!=Pc c0).
   constructor;unfold ceq;try apply ceq_refl.
   rewrite (Pol1mul_sym Q1 P1).
   unfold PO;rewrite <- (Pol1mul_0_l Q1).
   apply (IHPol1Eq Q1 Q1 (Pol1Eq_refl Q1)).
   rewrite (Pol1mul_sym (Pc q) Q2);rewrite <- (Pol1_cmul_spec Q2 q).
   rewrite H2;rewrite H1;rewrite H.
   apply Pol1add_0_l.
   rewrite (Pol1mul_sym (PX P1 p) Q0);
   rewrite (Pol1mul_sym (PX Q1 q) Q2).
   rewrite (Pol1_distr_PX Q0 P1 p);
   rewrite (Pol1_distr_PX Q2 Q1 q).
   apply Pol1_add_ext.
   constructor;unfold ceq;try apply ceq_refl.
   rewrite (Pol1mul_sym Q0 P1);rewrite (Pol1mul_sym Q2 Q1);
   apply (IHPol1Eq Q0 Q2);trivial.
   rewrite H1; rewrite H;apply Pol1Eq_refl.
  Qed.


Add Morphism Pol1_mul : Pol1mul_ext_morph.
intros; apply Pol1mul_ext; trivial.
Qed.


 Lemma Pol1opp_def : forall P, P + -P != Pc c0.
 Proof.
  induction P;simpl;constructor;try apply copp_def.
  auto.
 Qed.

 Lemma Pol1opp_ext : forall P Q, P != Q -> -P != -Q. 
 Proof.
  induction P;destruct Q;subst;simpl;constructor;try inversion H;subst;unfold ceq;unfold copp;
  try apply copp_ext;trivial.
  inversion_clear H4;simpl;unfold PO in *; constructor;try rewrite H0;
  try apply copp_0;unfold PO in *.
  rewrite <- (Pol1add_0_l (-P1));
  fold PO in H1; rewrite <- H1;
  apply Pol1opp_def.
  rewrite <- (Pol1add_0_l (-P)).
  rewrite <- H4.
  rewrite (Pol1opp_def P);apply Pol1Eq_sym;auto.
  auto.
 Qed.

Add Morphism Pol1_opp : Pol1opp_ext_morph.
intros;apply Pol1opp_ext;trivial.
Qed.


 
 
 Lemma Pol1_cmul_add : forall P Q c,
 Pol1_cmul(P + Q) c !=(Pol1_cmul P c) + (Pol1_cmul Q c).
 Proof.
  induction P;destruct Q;intros;simpl;constructor;try apply Pol1Eq_refl;
  try apply cdistr_l;try apply cdistr_r.
  rewrite (cmul_sym c3 c);apply cdistr_l.
  rewrite (cmul_sym c3 c2);apply cdistr_l.
  auto.
 Qed.

 Lemma Pol1_assoc_sym : forall a b c d,
 a + b + (c +d) != (a+c) +(b+d).
 Proof. 
  intros.
  rewrite <- (Pol1add_assoc a b (c+d)).
  rewrite (Pol1add_assoc b c d).
  rewrite (Pol1add_sym b c).
  rewrite <- (Pol1add_assoc c b d).
  rewrite  (Pol1add_assoc a c (b+d)).
  apply Pol1Eq_refl.
 Qed. 

 Lemma Pol1distr_l : forall R P Q, (P+Q)*R != P*R + Q*R.
 Proof.
  induction R.
 induction P;destruct Q;intros; simpl;constructor;
cgen;unfold ceq;try apply ceq_refl;
try apply Pol1Eq_refl.
  auto.
  intros.
  rewrite (Pol1_distr_PX (P + Q) R c).
  rewrite (IHR P Q).
  assert (PX (P*R + Q*R) (c0++c0) != (PX (P*R) c0)+(PX (Q*R) c0)).
  apply Pol1Eq_sym.
  apply (Pol1_add_spec (P*R) (Q*R) c0 c0).
  generalize H;rewrite (cadd_0_l c0).
  intro.
  clear H.
  rewrite H0;rewrite (Pol1_cmul_add P Q c).
  rewrite (Pol1_assoc_sym (PX (P * R) c0) (PX (Q * R) c0) (Pol1_cmul P c) (Pol1_cmul Q c)).
  rewrite <- (Pol1_distr_PX P R c).
  rewrite <- (Pol1_distr_PX Q R c).
  apply Pol1Eq_refl.
 Qed.

 Lemma Pol1distr_r : forall P Q R,
   P*(Q + R) != P*Q + P*R.
 Proof. 
  intros.
  rewrite (Pol1mul_sym P Q);
  rewrite (Pol1mul_sym P R);
  rewrite (Pol1mul_sym P (Q+R));
  apply Pol1distr_l.
 Qed.

Lemma Pol1mul_1_l : forall P, PI * P != P.
 Proof.
  induction P;intros;unfold PI in *;simpl;constructor;
  try rewrite (cmul_sym c c1); try apply cmul_1_l.
  rewrite (Pol1_cmul_spec P c1).
  rewrite (Pol1mul_sym P (Pc c1));trivial.
 Qed.

Lemma Pol1mul_1_r : forall P, P *PI!= P.
 Proof.
  induction P;intros;unfold PI in *;simpl;constructor;
  try rewrite (cmul_sym c c1); try apply cmul_1_l.
cgen;apply (ceq_refl C c).
auto.
 Qed.


 Lemma Pol1cmul_comp : forall P c1 c2,
(Pol1_cmul (Pol1_cmul P c1) c2) !=(Pol1_cmul P (c2**c1)).
 Proof.
  induction P;intros;simpl;constructor.
  apply cmul_assoc.
  rewrite (cmul_sym c3 c2);unfold ceq;apply ceq_sym; apply cmul_assoc.
  trivial.
  Qed.

 Lemma Pol1mul_Pc_PX : forall c P p,
 (Pc c)*(PX P p) != PX (Pol1_cmul P c) (c**p).
 Proof.
  destruct P;intros;simpl;rewrite (cmul_sym c p);
  apply Pol1Eq_refl.
 Qed.

 Lemma Pol1mul_PX_Pc : forall P p c,
 (PX P p)*(Pc c) != PX (Pol1_cmul P c) (p**c).
 Proof.
  intros;
  rewrite (Pol1mul_sym (PX P p) (Pc c));
  rewrite (cmul_sym p c);
  apply Pol1mul_Pc_PX.
 Qed.
 
 Lemma Pol1cmul_assoc : forall P Q c,
 (Pol1_cmul (P*Q) c) != (Pol1_cmul P c)*Q.
 Proof.
 induction P;destruct Q;intros;simpl;constructor;cgen;
  try (cmul_push c1;unfold ceq;apply ceq_refl).
rewrite (cmul_assoc2 c c2 c3);unfold ceq;apply ceq_refl.
 apply (Pol1cmul_comp Q c c3).
rewrite (cmul_assoc2 c2 c c3);unfold ceq;apply ceq_refl.
 rewrite (Pol1mul_sym P (Pc c2)).
 unfold Pol1_mul at 1.
 rewrite (Pol1cmul_comp P c2 c3).
 rewrite (Pol1mul_sym (Pol1_cmul P c3) (Pc c2));simpl.
 rewrite (Pol1cmul_comp P c3 c2).
 rewrite (cmul_sym c2 c3);apply Pol1Eq_refl.
 assert  (Pol1_cmul (P * PX Q c2 + Pol1_cmul Q c) c3 != (Pol1_cmul (P * PX Q c2) c3)  + (Pol1_cmul (Pol1_cmul Q c) c3)).
 fold (Pc c3 * (P * PX Q c2 + Pol1_cmul Q c)).
 rewrite (Pol1distr_r (Pc c3) (P * PX Q c2) ( Pol1_cmul Q c)).
 unfold Pol1_mul at 1 3; apply Pol1Eq_refl.
 rewrite H.
 rewrite (IHP (PX Q c2) c3).
 rewrite (Pol1cmul_comp Q c c3).
 rewrite (cmul_sym c c3); apply (Pol1Eq_refl).
 Qed.

 Lemma Pol1mul_assoc : forall P Q R, P *(Q*R) != (P*Q)*R.
 Proof.
  induction P; destruct Q;intros.
  simpl; apply Pol1cmul_comp.
  assert (Pc c * (PX Q c2 * R) != Pol1_cmul (PX Q c2 * R) c).
  simpl;apply Pol1Eq_refl.
  rewrite H.
  rewrite (Pol1cmul_assoc (PX Q c2 ) R c).
  simpl;apply Pol1Eq_refl.
  rewrite (Pol1_distr_PX_r P c (Pc c2* R)).
  rewrite  (IHP (Pc c2) R).
  destruct R;simpl;constructor;cgen;cmul_push c;unfold ceq;try apply ceq_refl.
  apply Pol1Eq_refl.
  rewrite (Pol1cmul_comp R c2 c);apply Pol1Eq_refl.
  rewrite (Pol1_distr_PX_r P c (PX Q c2 * R) ).
  rewrite (IHP (PX Q c2) R).
  rewrite (Pol1cmul_assoc (PX Q c2) R c).
  assert (PX (P * PX Q c2 * R) c0 != PX (P*PX Q c2) c0 * R).
  rewrite (Pol1_distr_PX_r (P * (PX Q c2)) c0 R).
  fold ((Pc c0)*R).
  rewrite (Pol1mul_0_l R).
  fold PO;rewrite (Pol1add_0_l' (PX (P * PX Q c2 * R) c0)).
  apply Pol1Eq_refl.
  rewrite H.
  rewrite <- (Pol1distr_l R (PX (P * PX Q c2) c0) (Pol1_cmul (PX Q c2) c)).
  simpl;apply Pol1Eq_refl.
  Qed.


(*plus rien a voir avec la structure d'anneaux,
pour abstraire par rapport aux coeficients*)

(*normalisation des polynomes, necessite un test a zero sur les coefficents*) 



  
 Fixpoint derivative(A:Pol1) : Pol1 :=
   match A with
     |Pc c => Pc c0
     |PX B b => (PX (derivative B) c0) + B
   end.

(*evaluation d'un polynome en un point de C*)

Fixpoint eval_pol(P:Pol1)(c:C){struct P}:C:=
  match P with
    |Pc a => a
    |PX A a => (eval_pol A c) ++ a
  end.

Reserved Notation "P @ l " (at level 10, no associativity).
Notation "P @ c " := (eval_pol P c).

(*lemmes de compatibilite de l'evaluation avec les operations sur les polynomes?*)





End POL1.

