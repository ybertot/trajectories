
Unset Boxed Definitions.
Unset Boxed Values.


 Require Import Qabs.
Require Import CAD.
Require Import One_dim.
Require Import Up_dim.

Set Implicit Arguments.

  
Module CAD_gen(Q:RAT_STRUCT).

Module ONE_DIM := MK_ONE_DIM Q.
Module UP_DIM := MK_UP_DIM Q.

Import Q.
Import ONE_DIM.
Import UP_DIM.


Fixpoint Poln(n:nat):Set:=
match n with
|O => Rat
|S n => Pol1 (Poln n)
end.

Section CAD_no_unfold.

Variable f: forall C : Set, Cad Rat C -> Cad Rat (Pol1 C).

Fixpoint CAD_build_comp(n:nat):Cad Rat (Poln n) :=
match n return Cad Rat (Poln n) with
|O => One_dim_cad
|S n =>
  f (CAD_build_comp n)
end.

End CAD_no_unfold.

Definition CAD_build := CAD_build_comp CAD_make.
   

End CAD_gen.


(********************************************************************************)


(*mais ca ca marche plus. voir bug de roland? coqcvs? 
Fixpoint CAD_build(n:nat):Cad Rat (Poln n) :=
match n return (Cad Rat) (Poln n) with
|O => One_dim_cad
|S n =>
  @CAD_make (Poln n) (CAD_build n)
end.




Fixpoint CAD_build(n:nat):Cad Rat (Poln n) :=
match n return (Cad Rat) (Poln n) with
|O => One_dim_cad
|S n =>
 (* let CAD_n := CAD_build n in*)
  CAD_make (CAD_build n)
end.

End CAD.
*)
