Reserved Notation "x ++ y" (at level 50, left associativity).
Reserved Notation "x -- y" (at level 50, left associativity).
Reserved Notation "x ** y" (at level 40, left associativity).
Reserved Notation "-- x" (at level 35, right associativity).
Reserved Notation " x != y "(at level 70, no associativity).

Reserved Notation "x + y" (at level 50, left associativity).
Reserved Notation "x - y" (at level 50, left associativity).
Reserved Notation "x * y" (at level 40, left associativity).
Reserved Notation "- x" (at level 35, right associativity).
Reserved Notation "x == y" (at level 70, no associativity).
Reserved Notation "x # y" (at level 20, no associativity).



Require Export ZArith.
Require Export Mylist.
Require Import Setoid.
Require Import Utils.

Definition Is_true (b:bool) : Prop:=
match b with
|true => True
|false => False
end.



(*pourquoi un module et pas un parametre record par exemple*)

(*in order to test the efficency, depending to when the reduction of
  rationnals is performed*)

 Module Type RAT_OPS.
   
   Parameter Rat : Set.

   Bind Scope Rat_scope with Rat.   
   Open Scope Rat_scope.

 

(*constants, operations over rationnals,
-MkRat builds a rationnal number from an integer and a positive
-RatEq is an eq relation over rationnals
-Rat_zero_test is a decidable test to the zero constant
-Rat_sign gives the sign of a rationnal : Z0 means it is zero, Zpos _, it is pos, ...
-Rat_pow builds a power of a rationnal, if the rat argument is
  normalized then the power is normalized
*)
   
   Parameter  R0 : Rat.
   Parameter  R1 : Rat.
   Parameter  MkRat : Z -> positive -> Rat.
   Parameter  Norm : Rat -> Rat.
   Parameter  Rat_add : Rat -> Rat -> Rat.
   Parameter  Rat_opp : Rat -> Rat.
   Parameter  Rat_prod : Rat -> Rat -> Rat.
   Parameter  Rat_sub : Rat -> Rat -> Rat.
   Parameter  Rat_inv : Rat -> Rat.
   Parameter  Rat_div : Rat -> Rat -> Rat.
   Parameter  RatEq : Rat -> Rat -> Prop.
   Parameter  Rat_zero_test : Rat -> bool.
   Parameter  Rat_lt : Rat -> Rat -> bool.
   Parameter  Rat_sign : Rat -> Z.
   Parameter  Rat_pow : Rat -> N -> Rat.
   Parameter  Rat_abs_val : Rat -> Rat.


   Notation "a # b" := (MkRat a b) : Rat_scope.

   Infix "+" := Rat_add :Rat_scope.
   Notation "- x" := (Rat_opp x) : Rat_scope.
   Infix  "*" := Rat_prod : Rat_scope.
   Infix "-" := Rat_sub : Rat_scope.
   Notation "/ x" := (Rat_inv x): Rat_scope.
   Infix "/":= Rat_div : Rat_scope.

   Notation "x == y" := (RatEq x y) : Rat_scope.

(* plus tard 
   Parameter  RatEq_refl : forall x, x ==x.
   Parameter  RatEq_sym : forall x y, x == y -> y ==x.
   Parameter  RatEq_trans : forall x y z, x == y -> y == z -> x == z.
     
      
  needed exensionality of operations, and their properties 

   Parameter  Rat_add_ext : 
     forall x1 x2 y1 y2, x1 == x2 -> y1 == y2 -> x1 + y1 == x2 + y2.
   Parameter  Rat_opp_ext : forall x1 x2, x1 == x2 -> - x1 == - x2.
   Parameter  Rat_prod_ext :
     forall x1 x2 y1 y2, x1 == x2 -> y1 == y2 -> x1 * y1 == x2 * y2.
   Parameter Rat_inv_ext : forall x1 x2, x1 == x2 -> / x1 == / x2.

  

   Parameter  Rat_opp_spec : forall x, x + (- x) == R0.
   Parameter  Rat_sub_spec : forall x y, x - y == x + (- y).
   Parameter  Rat_div_spec : forall x y, x / y == x * (/ y).
   Parameter  Rat_zero_test_spec : forall x, (Is_true (Rat_zero_test x))-> x == R0.
  
   
 
   Parameter  Rat_0_l    : forall x, R0 + x== x.
   Parameter  Rat_add_sym    : forall x y, x + y == y + x.
   Parameter  Rat_add_assoc  : forall x y z, x + (y + z) == (x + y) + z.
   Parameter  Rat_prod_1_l    : forall x,  R1 * x== x.
   Parameter  Rat_prod_sym    : forall x y, x * y == y * x.
   Parameter  Rat_prod_assoc  : forall x y z, x * (y * z) == (x * y) * z.
   Parameter  Rat_distr_l  : forall x y z, (x + y) * z == (x * z) + (y * z).

*)

(*   Definition Rat_of_Z(x : Z) := (MkRat x 1).
   Definition Rat_of_pos(i:positive) := (Rat_of_Z (Zpos i)).
  *)
 
 Open Scope Rat_scope.

 End RAT_OPS.


 Module RAT_PROP(Q:RAT_OPS).

   Import Q.
   Definition Rat_of_Z(x : Z) := (MkRat x 1).
   Definition Rat_of_pos(i:positive) := (Rat_of_Z (Zpos i)).
   Definition Rat_of_N(n:N):=
     match n with
       |N0 => R0
       |Npos p => (Rat_of_pos p)
     end.
   
   
 Definition fact'(n m:positive):positive:=  ((Psucc n)*m)%positive.

 Definition fact(n:N):=
   match n with
     |N0 => R1
     |Npos p => Rat_of_pos (Prec positive xH fact' p)
   end.

   (*binomial coefficient C(n,p)*)(*pareil,c'est surement ameliorable*)
 Definition binomial(n p:N):Rat:=
   match Ncompare n p with
     |Eq => R1
     |Lt => R1 (*should nt happen!*)
     |Gt => (fact n)/((fact p)*(fact (Nminus n  p)))
   end.


 Fixpoint max_list(l:list Rat):Rat:=
   match l with
     |nil => R0
     |r::l' =>
       match l' with
	 |nil => r
	 |_ =>
	   let m:= max_list l' in
	     if Rat_lt r m 
	       then m
	       else r
       end
   end.

 Definition Rat_le(q q':Rat) := orb (Rat_lt q q') (Rat_zero_test (q -q')).






   (*such a rational structure is a setoid, vivement le nouveau setoid 
  ....et la preuve de correction pour Qnorm!
   Definition Rat_Setoid : Setoid_Theory Rat RatEq.
   Proof.
     split.
   exact RatEq_refl.
   exact RatEq_sym.
   exact RatEq_trans.
   Qed.

   Add Setoid Rat RatEq Rat_Setoid.
   
   
   Add Morphism Rat_add : Rat_add_comp.
     exact Rat_add_ext.
   Qed.

   Add Morphism Rat_opp : Rat_opp_comp.
     exact Rat_opp_ext.
   Qed.

   Add Morphism Rat_prod : Rat_prod_comp.
     exact Rat_prod_ext.
   Qed.

   Add Morphism Rat_inv : Rat_inv_comp.
     exact Rat_inv_ext.
   Qed.

   Add Morphism Rat_sub : Rat_sub_comp.
     intros.
     rewrite (Rat_sub_spec r r1).
     rewrite (Rat_sub_spec r0 r2).
     rewrite H;rewrite H0.
     apply RatEq_refl.
   Qed.

   Add Morphism Rat_div : Rat_div_comp.
     intros.
     rewrite (Rat_div_spec r r1).
     rewrite (Rat_div_spec r0 r2).
     rewrite H;rewrite H0.
     apply RatEq_refl.
   Qed.*)

   End RAT_PROP.