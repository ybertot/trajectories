Require Import Setoid.
Require Import ZArith.

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
Reserved Notation " x !=? y "(at level 70, no associativity).


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

 Definition cadd := (Cadd C coef).
 Definition cmul := (Cmul C coef).
 Definition copp := (Copp C coef).
 Definition csub := (Csub C coef).
 Definition c0 := (CO C coef).
 Definition c1 := (CI C coef).
 Definition czero_test:=(Czero_test C coef).
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

 
 
(* one variable sparce polynomials over C, either constant or P*X^i+c*)
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
  X do not divide P*)

 Inductive not_Xmult:Pol1->Prop :=
   |not_Xmult_Pc : forall c, 
     (Is_true (negb(czero_test c)))->(not_Xmult (Pc c))
   |not_Xmult_PX : forall P, forall i, forall c,
     (Is_true (negb(czero_test c)))->(not_Xmult (PX P i c)).

 Inductive Pol1_is_norm:Pol1->Prop:=
   |norm_Pc : forall c, (Pol1_is_norm (Pc c))
   |norm_PX : forall P, forall i, forall c, 
     (Pol1_is_norm P)->(not_Xmult P)->(Pol1_is_norm (PX P i c)).
 
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
   induction (czero_test c2);try elim H0;trivial.
   simpl in IHPol1_is_norm.
   rewrite <- IHPol1_is_norm.
   simpl.
   assert (czero_test c2 = false).
   induction (czero_test c2);simpl in H0.
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

(* the following defined operations preserve normalization *)

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
 Notation "P ++ P'" := (Padd P P').

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
     (mkPX (Pmul P P') i' c0) ++ (PmulC P c')
  end.

 Notation "P * P'" := (Pmul P P').

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

  (*Pol1_CEq is a setoid equality*)

 Lemma Pol1_CEq_refl :forall P, P !=? P.
 Proof.
   intros.
   induction P;constructor;trivial;apply ceq_refl.
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

(*decidable test to zero for a normalized polynomial*)
 Definition Pol1_zero_test(P:Pol1):bool:=
   match P with
     |Pc c => (czero_test c)
     |PX _ _ _=> false
       end.







(* pour le reste des preuves on verra plus tard*)

  



End POL1.

