Require Import Setoid.
Require Import ZArith.

Definition Is_true (b:bool) : Prop:=
match b with
|true => True
|false => False
end.


Reserved Notation "x // y" (at level 50, left associativity).
Reserved Notation "x ++ y" (at level 50, left associativity).
Reserved Notation "x -- y" (at level 50, left associativity).
Reserved Notation "x ** y" (at level 40, left associativity).
Reserved Notation "-- x" (at level 35, right associativity).
Reserved Notation "x == y" (at level 70, no associativity).
Reserved Notation "x ?== y" (at level 70, no associativity).




Reserved Notation "x / y" (at level 40, left associativity).
Reserved Notation "x -y" (at level 50, left associativity).
Reserved Notation "x * y" (at level 40, left associativity).
Reserved Notation "- x" (at level 35, right associativity).
Reserved Notation " x != y "(at level 70, no associativity).
Reserved Notation " x !=? y "(at level 70, no associativity).


Reserved Notation "x '+ y" (at level 50, left associativity).
Reserved Notation "x '- y" (at level 50, left associativity).
Reserved Notation "x '* y" (at level 40, left associativity).
Reserved Notation "'- x" (at level 35, right associativity).
Reserved Notation " x '= y "(at level 70, no associativity).

	 (*********************************************************)
         (*********** Coefficients form and inegral domains********)
	 (*********************************************************)


Section COEF_RING.

 
 Variable C : Set.
 Implicit Arguments C.

 Record coef_set : Type := mk_cset{
   CO : C;
   CI : C;
   Ceq : C -> C -> Prop;
   Cadd : C -> C -> C;
   Cmul : C -> C -> C;
   Csub : C -> C -> C;
   Copp : C -> C;
   Czero_test : C -> bool;
   C_of_pos : positive -> C;
   Cpow : C -> N -> C;
   Cdiv : C -> C -> option C
 }.

 Variable coef : coef_set.
 
 Notation "x ++ y" := (Cadd coef x y).
 Notation "x ** y":= (Cmul coef x y).
 Notation "-- x" := (Copp coef x).
 Notation "x -- y" := (Csub coef x y).
 Notation "x == y" := (Ceq coef x y).
 Notation "x // y" := (Cdiv coef x y). 
 
 
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


(*TODO:+intergral dom requirements*)


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

	 (*****************************************************)
	 (******Properties of an integral domain***************)
	 (*****************************************************)

Section COEF_PROP.

 
 Variable C : Set.

 Implicit Arguments C.

 Variable coef : (coef_set C).
 Variable eq_th : (coef_eq C coef).

 Implicit Arguments coef.
 Implicit Arguments eq_th.

 Let ceq:=(Ceq C coef).
 Let cadd := (Cadd C coef).
 Let cmul := (Cmul C coef).
 Let copp := (Copp C coef).
 Let csub := (Csub C coef).
 Let czero_test:=(Czero_test C coef).
 
 Notation c0 := (CO C coef).
 Notation c1 := (CI C coef).
 
 Notation "x ++ y" := (cadd x y).
 Notation "x ** y" := (cmul x y).
 Notation "x -- y" := (csub x y).
 Notation " -- x" := (copp x).
 Notation "x == y" :=(ceq x y).

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
   unfold copp. 
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


End COEF_PROP.


	 (**************************************************)
	 (******Definition of univariate polynomials********)
	 (******************and operations******************)
	 (**************************************************)


Section POL1 .


 Variable C:Set.
 Variable coef : coef_set C.
 Variable eq_th : coef_eq C coef.



 Let ceq:= Ceq C coef.
 Let cadd := Cadd C coef.
 Let cmul := Cmul C coef.
 Let copp := Copp C coef.
 Let csub := Csub C coef.
 Let czero_test := Czero_test C coef.

 Notation "x // y" := (Cdiv C coef x y).
 Notation "x ++ y" := (Cadd C coef x y).
 Notation "x ** y" := (Cmul C coef x y).
 Notation "x -- y" := (Csub C coef x y).
 Notation " -- x" := (Copp  C coef x).
 Notation "x == y" := (Ceq C coef x y).
 Notation c0 := (CO C coef).
 Notation c1 := (CI C coef).
 
(* one variable sparse polynomials over C, either constant or P*X^i+c*)
 Inductive Pol1:Set:=
 |Pc : C-> Pol1
 |PX : Pol1 -> positive -> C -> Pol1.

 Definition P0:= (Pc c0).
 Definition PI:=(Pc c1).

 (* bulids PX P i c, in normal form, provided that P is in normal form*)
 Definition mkPX P i c := 
  match P with
  | Pc p => if (czero_test p) then Pc c else PX P i c
  | PX P' i' c' => if (czero_test c') then PX P' (i' + i) c else PX P i c
  end.
 
(*Equality over polynomials, is Leibniz equality over normal forms. Normal fors are factorized as much as possible and have no head zero*)
 

(*What is a polynomial in normal form, function or predicate?let's try with a predicate*)


 (*First a predicate telling if a polynomial, supposed to be in normal
  form, can be used as P in PX P c to build a pol in normal form, ie
  X does not divide P*)

 Inductive not_Xmult:Pol1->Prop :=
   |not_Xmult_Pc : forall c, 
     (Is_true (negb(czero_test c)))->(not_Xmult (Pc c))
   |not_Xmult_PX : forall P, forall i, forall c,
     (Is_true (negb(czero_test c)))->(not_Xmult (PX P i c)).

 Inductive Pol1_is_norm:Pol1->Prop:=
   |norm_Pc : forall c, (Pol1_is_norm (Pc c))
   |norm_PX : forall P, forall i, forall c, 
     (Pol1_is_norm P)->(not_Xmult P)->(Pol1_is_norm (PX P i c)).
 
 (* just in case, the normalization function, and its corection*)
 Fixpoint normalize(P:Pol1):Pol1 :=
   match P with
     |Pc c' => P
     |PX P' i p => (mkPX (normalize P') i p)
   end.


 Lemma normalize_cor : forall P, (Pol1_is_norm P) -> (P = (normalize
   P)).
 Proof.
   intros.
   induction H;simpl.
   trivial.
   induction H0;simpl.
   induction (czero_test c0);try elim H0;trivial.
   simpl in IHPol1_is_norm.
   rewrite <- IHPol1_is_norm.
   simpl.
   assert (czero_test c0 = false).
   induction (czero_test c0);simpl in H0.
   elim H0.
   trivial.
   rewrite H1;simpl.
   trivial.
 Qed.
   
(*syntactic equality modulo equality over C*)

 Inductive Pol1_CEq :Pol1->Pol1->Prop :=
   |CeqPc : forall c c', (c == c')->(Pol1_CEq (Pc c) (Pc c'))
   |CeqPX : forall P P', forall i i', forall c c', 
     (Pol1_CEq P P')->(i = i')->(c == c')->
     (Pol1_CEq (PX P i c) (PX P' i' c')).


 Definition Pol1Eq(P Q:Pol1):Prop := (Pol1_CEq (normalize P)  (normalize Q)).
 
 Notation "P !=? Q" := (Pol1_CEq P Q).
 Notation "P != Q" := (Pol1Eq P Q).

(* all the following defined operations preserve normalization *)

 (*Opposite*)
 Fixpoint Pop(P:Pol1):Pol1 :=
   match P with
     |Pc p => Pc (-- p)
     |PX P i p => mkPX (Pop P) i (-- p)
   end.

Notation "- P" := (Pop P).

(** Addition and subtraction **)
 
(*P+Pc c*)
 Definition PaddC (P:Pol1)(c:C):Pol1 :=
  match P with
  | Pc c1 => Pc (c1 ++ c)
  | PX P i c1 => PX P i (c++c1)
  end.

(*P - Pc c*)
 Definition PsubC (P:Pol1) (c:C) : Pol1 :=
  match P with
  | Pc c1 => Pc (c1 -- c)
  | PX P i c1 => PX P i (c1 -- c)
  end.

 Section Pop_aux.

   Variable Pop : Pol1 -> Pol1 -> Pol1.
   Variable P' : Pol1.
   (* Inv : is_PX P', is_norm P', is_norm P *)
    (*P+P'*X^i*)
   Fixpoint PaddX (i':positive) (P:Pol1) {struct P} : Pol1 :=
     match P with
       | Pc c => PX P' i' c
       | PX P i c =>
	 match ZPminus i i' with
	   | Zpos k => mkPX (Pop (PX P k c0) P') i' c
	   | Z0 => mkPX (Pop P P') i c
	  | Zneg k => mkPX (PaddX k P) i c
	 end
     end.
   
    (*P-P'*X^i'*)
   Fixpoint PsubX (i':positive) (P:Pol1) {struct P} : Pol1 :=
     match P with
       | Pc c => PX (- P') i' c
       | PX P i c =>
	 match ZPminus i i' with
	   | Zpos k => mkPX (Pop (PX P k c0) P') i' c
	   | Z0 => mkPX (Pop P P') i c
	   | Zneg k => mkPX (PsubX k P) i c
	 end
     end.
 
 
 End Pop_aux.

 (* Inv : is_norm P, is_norm P' *)
 Fixpoint Padd (P P': Pol1) {struct P'} : Pol1 :=
   match P' with
     | Pc c' => PaddC P c'
     | PX P' i' c' =>
       match P with
	 | Pc c => PX P' i' (c ++ c')
	 | PX P i c =>
	   match ZPminus i i' with
	     | Zpos k => mkPX (Padd (PX P k c0) P') i' (c ++ c')
	     | Z0 => mkPX (Padd P P') i (c ++ c')
	     | Zneg k => mkPX (PaddX Padd P' k P) i (c ++ c')
	   end
       end
   end.
 Notation "P + P'" := (Padd P P').

 Fixpoint Psub (P P': Pol1) {struct P'} : Pol1 :=
   match P' with
     | Pc c' => PsubC P c'
     | PX P' i' c' =>
       match P with
	 | Pc c => PX (- P') i' (c -- c')
	 | PX P i c =>
	   match ZPminus i i' with
	     | Zpos k => mkPX (Psub (PX P k c0) P') i' (c -- c')
	     | Z0 => mkPX (Psub P P') i (c -- c')
	     | Zneg k => mkPX (PsubX Psub P' k P) i (c -- c')
	   end
       end
   end.
 Notation "P - P'" := (Psub P P').
 
 (** Multiplication *) 


(*P*(Pc c) *)
 Fixpoint PmulC_aux (P:Pol1) (c:C) {struct P} : Pol1 :=
  match P with
  | Pc c' => Pc (c' ** c)
  | PX P i c' => mkPX (PmulC_aux P c) i (c'** c)
  end.

(*hack to speed up*)
 Definition PmulC P c :=
  if (czero_test c) then P0 else
  if (czero_test (c -- c1)) then P else PmulC_aux P c.
 
 Fixpoint Pmul (P P' : Pol1) {struct P'} : Pol1 :=
  match P' with
  | Pc c' => PmulC P c'
  | PX P' i' c' => 
     (mkPX (Pmul P P') i' c0) + (PmulC P c')
  end.

 Notation "P * P'" := (Pmul P P').

 Definition Pol1_zero_test(P:Pol1):bool:=
   match P with
     |Pc c => (czero_test c)
     |PX _ _ _=> false
   end.

 Definition Pol1_of_pos(p:positive):Pol1:= Pc (C_of_pos C coef p).


 (*P^n*)
 Fixpoint Ppow'(P:Pol1)(p:positive){struct p}:Pol1:=
   match p with
     |xH => P
     |xO p' => let Q:=(Ppow' P p') in (Pmul Q Q)
     |xI p' => let Q:=(Ppow' P p') in (Pmul (Pmul Q Q) P)
   end.

 Definition Ppow(P:Pol1)(n:N):Pol1 :=
   match n with
     |N0 => PI
     |Npos p => Ppow' P p
   end.


   
  (*couple degree * coefdom for a polynomial in normal form *)
 Fixpoint deg_coefdom(A:Pol1) : N*C :=
   match A with
     |Pc a => (N0,a)
     |PX P i p => let (d,c) := (deg_coefdom P) in (Nplus (Npos i) d, c)
   end.

   
   
(*division:like an euclidian division, but if the division over coef
fails, returns None*)

(* division by a constante  *)
   Fixpoint div_cst(A:Pol1)(q:C){struct A}:option Pol1:=
     match A with
       |Pc a =>
               match (a // q) with
	       |Some c => Some (Pc c)
	       |None => None
	       end
       |PX P i p => 
       		    match (div_cst P q), (p // q) with
		    |Some P, Some c => Some (PX P i c)
		    |_, _ => None
		    end
     end.

   Section euclide_aux.

     Variable D : Pol1.
     
     (*degee and leading coef of D*)
     Definition dd_cd := deg_coefdom D.
     Definition dd := fst dd_cd.
     Definition cd := snd dd_cd.
     
  (*auxiliary division of RX^i by D.invariant : 
  -- deg R < deg D
  -- R <> 0
  -- D is not constant *)		
   Fixpoint div_aux(R : Pol1)(i:positive){struct i}:option (Pol1*Pol1) :=
     let (dr,cr) := (deg_coefdom R) in
       match (Ncompare (dr + (Npos i)) dd) with
	 |Lt => Some (Pc c0, PX R i c0)
	 | _  => 
	   match i with
	   | xH => 
		   let cdiv := (cr // cd ) in
		   match cdiv with
		   |None => None
		   |Some  c => Some ((Pc c), (mkPX R xH c0) - (PmulC D c))
		   end
	   | xO p =>	
	       	    match (div_aux R p) with
		    |None => None
		    |Some res => 
		    	let (Q1, c1) := res in
		       	let (dc1, cc1):=(deg_coefdom c1) in
		       	if (czero_test cc1) then 
		       	Some (mkPX Q1 p c0, Pc c0)
	       	       	else
		       		match (div_aux c1 p) with
				|None => None
				|Some res1 => 	
		 			let (Q2, R2):=res1 in 
		 			Some ((mkPX Q1 p c0) + Q2, R2)
				end
		     end
	  | xI p =>
	  	    match (div_aux R p) with
		    |None => None
		    |Some res =>
		    	let (Q1, c1) := res in
	       		let (dc1, cc1):=deg_coefdom c1 in
	       		if (czero_test cc1) then 
		 	Some ((mkPX Q1 (Psucc p) c0), Pc c0)
	       		else
		 	match (div_aux c1 p) with
			|None => None
			|Some res1 =>
				let (Q2, R2) := res1 in
		 		let (dr2, cr2) := (deg_coefdom R2) in	
		 		if (czero_test cr2) then
		   		Some ((mkPX Q1 (Psucc p) c0)+(mkPX Q2 xH c0), Pc c0)
		 		else
		   		match (Ncompare (Nsucc dr2) dd) with
		   		| Lt => 
		     		Some ((mkPX Q1 (Psucc p) c0)+(mkPX Q2 xH c0), mkPX R2 xH c0)
		   		| _ =>
					match (cr2 // cd) with
					|None => None
					|Some c => 
		     			let quo := (mkPX Q1 (Psucc p) c0) + (mkPX Q2 xH c0)+(Pc c) in
                     			let rem := (mkPX R2 xH c0) - (PmulC D c) in
		     			Some (quo,rem)	
		   			end
	   			end
       			end
	   	    end
	   end
	end.		
 
 End euclide_aux.

(*straightforward division of polynomials with coef in Rat:
  - as usual arguments are supposed to be normalized
  - div_euclide A B = (Q,R) with  A = BQ +R and 
	--either deg(R)< deg(B)
	-- or deg(R)=deg(B)=0 and R != P R0
	-- Q and R are normalized
  ** non trivial case :
  if AX^i +a is to be divided by B, with  A = PQ1 + c1 and deg(c1)<deg(B)
  then AX+a=(BQ1)X^i + c1X^i +a and :
    - either deg (c1X^i +a) < deg (B),it ok : Q = X^i*Q1 and R = c1X^i + a
    - or deg (c1X^i +a) >= deg (B) and  Q = (X^i*Q1+Q2) et R = R2 + a
  where (Q2, R2) = div_aux B db cb c1 i i.e. c1X^i = Q2B +R2
  ** poly returned are normalized as soon as args are normalized
  *)
 
 (*first division by a non constant polynomial*)
 Section euclide_PX.
   Variable B : Pol1.
   Definition dcb := deg_coefdom B.
   Definition db := fst dcb.
   Definition cb := snd dcb.

   (*division of A by the non constant polynomial B*)
   Fixpoint euclide_div_PX (A :Pol1):option (Pol1*Pol1) :=
   match A with
     |Pc a => Some (Pc c0, Pc a)
     |PX P i p =>
     	match (euclide_div_PX P) with
	|None => None
	|Some res =>
       		let (Q1, c1):= res in
	 	let (dr, r) := deg_coefdom c1 in
	   	match (Pol1_zero_test c1),(Ncompare (Nplus (Npos i) dr) db) with
	     	|true, _ => Some (mkPX Q1 i c0, Pc p)
	     	| _ , Lt => Some (mkPX Q1 i c0, mkPX c1 i p)
	     	| _ , _ => 
			match (div_aux B c1 i) with
			|None => None
			|Some res1 =>
			let (Q2, R2) := res1 in
	       		Some ((mkPX Q1 i c0) + Q2, R2 + Pc p)
			end
	   	end
	end
   end.

 End euclide_PX.

 (*general division function *)
 Definition euclide_div(A B:Pol1):option (Pol1*Pol1) :=
   match B with
     |Pc q => 
     	match (div_cst A q) with
	|None => None
	|Some res => Some (res, Pc c0)
     	end
     |_ => (euclide_div_PX B A)
   end.


 Definition Pol1div(A B:Pol1):option Pol1:=
 match (euclide_div A B) with
 |None => None
 |Some res => Some (fst res)
 end.


(*Pol1 is a coef_set*)

 Definition Pol1_is_coef_set :=
   mk_cset Pol1 (Pc c0) (Pc c1) Pol1Eq Padd Pmul Psub Pop
   Pol1_zero_test Pol1_of_pos Ppow Pol1div.


  (*Derivative*)
 Fixpoint Pderiv(P:Pol1):Pol1 :=
   match P with
     |Pc c => Pc c0
     |PX A i a => match i with
		    |xH => A +(mkPX (Pderiv A) xH c0)
		    |_ => (PmulC (PX A (Ppred i) c0) (C_of_pos C coef i)) +
		      (mkPX (Pderiv A) i c0)
		  end
   end.
   
  (* evaluation of a Poly at an element of C *)
 Fixpoint Peval(P:Pol1)(x:C){struct P} : C :=
   match P with
     |Pc c =>  c
     |PX A i a => ((Peval A x)**(Cpow C coef x (Npos i))) ++ a
   end.
   



               (****************************************************)
               (**********Proofs for univariate polynomials******)
               (****************************************************)


  (*Pol1_CEq is a setoid equality*)

 Lemma Pol1_CEq_refl :forall P, P !=? P.
 Proof.
   intros.
   induction P;constructor;trivial;apply (Ceq_refl C coef eq_th).
 Qed.

 
 Lemma Pol1_CEq_sym : forall P Q, P !=? Q -> Q !=? P.
 Proof.
   intros.
   induction H;constructor;trivial;try apply ceq_sym;try apply sym_equal;trivial.
 Qed.

 Lemma Pol1_CEq_trans0 : forall P Q, P !=? Q -> forall R, (Q !=? R -> P !=? R).
 Proof.
   intros P Q H.
   induction H;intros.
   inversion H0.
   constructor;apply ceq_trans with c';trivial.
   inversion H2.
   constructor.
   apply IHPol1_CEq;trivial.
   apply trans_eq with i';trivial.
   apply ceq_trans with c';trivial.
 Qed.


(*Pol1Eq is a setoid equality*)

 Lemma Pol1Eq_refl :forall P, P != P.
 Proof.
   intros.
   unfold Pol1Eq.
   apply Pol1_CEq_refl.
 Qed.

 Lemma Pol1Eq_sym : forall P Q, P != Q -> Q != P.
 Proof.
   unfold Pol1Eq.
   intros.
   apply Pol1_CEq_sym;trivial.
 Qed.


 Lemma Pol1Eq_trans : forall P Q R, P!= Q -> Q != R -> P != R.
 Proof.
   unfold Pol1Eq.
   intros.
   apply Pol1_CEq_trans0 with (normalize Q);trivial.
 Qed.


  (*setoid strcture for Pol1*)
 Lemma Pol1_setoid : Setoid_Theory Pol1 Pol1Eq.
 Proof.
   constructor.
   exact Pol1Eq_refl.
   exact Pol1Eq_sym.
   intros; apply Pol1Eq_trans with y;trivial.
 Qed.

 Add Setoid Pol1 Pol1Eq Pol1_setoid.

(* pour le reste des preuves on verra plus tard*)

End POL1.

	    (*******************************************************)
            (***************Definition of generic*******************)
	    (**************multivariate polynomials*****************)
	    (*******************************************************)


Section POL_DEF.

 Variable C_base : Set.
 Variable coef : coef_set C_base.
 Variable eq_th : coef_eq C_base coef.

 Let ceq:= Ceq C_base coef.
 Let cadd := Cadd C_base coef.
 Let cmul := Cmul C_base coef.
 Let copp := Copp C_base coef.
 Let csub := Csub C_base coef.
 Let czero_test := Czero_test C_base coef.

 Notation "x ++ y" := (Cadd C_base coef x y).
 Notation "x ** y" := (Cmul C_base coef x y).
 Notation "x -- y" := (Csub C_base coef x y).
 Notation " -- x" := (Copp  C_base coef x).
 Notation "x == y" := (Ceq C_base coef x y).
 Notation c0 := (CO C_base coef).
 Notation c1 := (CI C_base coef).
 
(*multivariate polynomials built recursively from univariate ones*)

 Fixpoint Poln(n:nat):Set :=
   match n with
     |O => C_base
     |S n => Pol1 (Poln n)
   end.

  (* forall n, Poln n is equipped with a coef structure*)
 Definition Poln_is_coef_set : forall n, coef_set (Poln n).
   intros;induction n;simpl.
   assumption.
   apply (Pol1_is_coef_set (Poln n) (IHn)).
 Defined.

End POL_DEF.
