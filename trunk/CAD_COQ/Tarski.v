Unset Boxed Definitions.
Unset Boxed Values.


Require Import Qabs.
Require Import Utils.

Require Import CAD_types.v
Require Import One_dim.
Require Import Up_dim.

Set Implicit Arguments.


Module CAD_gen(Q:RAT_STRUCT).

Import Q.
(*
Module QCAD := CAD_DATAS Q.
Import QCAD.
*)

Module ONE_DIM := MK_ONE_DIM Q.
Import ONE_DIM.

Module UP_DIM := MK_UP_DIM Q.
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

Definition CAD_build := CAD_build_comp UP_DIM.CAD_make.
   

End CAD_gen.

