Require Export ZArith.
Require Export Mylist.
Require Import Utils.



Record Rat_ops : Type := mk_rat{
     Rat : Set;
     R0 : Rat;
     R1 : Rat;
     MkRat : Z -> positive -> Rat;
     Norm : Rat -> Rat;
     Rat_add : Rat -> Rat -> Rat;
     Rat_opp : Rat -> Rat;
     Rat_prod : Rat -> Rat -> Rat;
     Rat_sub : Rat -> Rat -> Rat;
     Rat_inv : Rat -> Rat;
     Rat_div : Rat -> Rat -> Rat;
     RatEq : Rat -> Rat -> Prop;
     Rat_zero_test : Rat -> bool;
     Rat_lt : Rat -> Rat -> bool;
     Rat_sign : Rat -> comparison;
     Rat_pow : Rat -> N -> Rat;
     Rat_abs_val : Rat -> Rat
}.


 Section RAT_PROP.
  Variable Q_ops : Rat_ops.
  
  Let MkRat := MkRat Q_ops.
  Let Rat_lt := Rat_lt Q_ops.
  Let R0 := R0 Q_ops.
  Let R1 := R1 Q_ops.
  Let Rat_zero_test := Rat_zero_test Q_ops.
  Let Rat_div := Rat_div Q_ops.
  Let Rat_prod := Rat_prod Q_ops.
  Let Rat_sub := Rat_sub Q_ops.
  Let Rat := Rat Q_ops.
   Infix "/" := Rat_div.
   Infix "*" := Rat_prod.
   Infix "-" := Rat_sub.

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

 Definition Rat_min(q q':Rat):=if  (Rat_lt  q q') then q else q'.
 Definition Rat_max(q q':Rat):= if (Rat_lt q q') then q' else q.

  Definition Rat_min4(a b c d:Rat):=
  (Rat_min a (Rat_min b (Rat_min c d))).

  Definition Rat_max4(a b c d:Rat):=
  (Rat_max a (Rat_min b (Rat_min c d))).

End RAT_PROP.


