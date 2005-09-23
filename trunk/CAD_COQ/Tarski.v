Unset Boxed Definitions.
Unset Boxed Values.


Require Import Qabs.
Require Import Utils.

Require Import CAD_types.

Require Import One_dim.
Require Import Up_dim.

Set Implicit Arguments.


Module CAD_gen(Q:RAT_STRUCT).

Import Q.

Module ONE_DIM := MK_ONE_DIM Q.
Import ONE_DIM.

Module UP_DIM := MK_UP_DIM Q.
Import UP_DIM.

Fixpoint Poln(n:nat):Set:=
  match n with
    |O => Rat
    |S n => Pol1 (Poln n)
  end.

Definition Infon(n:nat):=
  match n with
    |O => Rat
    |S n => build_Info (Poln n)
end.

Fixpoint cell_pointn(n:nat):Set:=
  match n with
    |O=>unit
    |S n => @cell_point (Poln n) (Infon n) (cell_pointn n)
  end.

Fixpoint mkCadn(n:nat):Set -> Set:=
  match n with
    |O => fun A :Set => A
    |S n => (*fun A :Set => (mkCadn n (list A))*)mkCad (mkCadn n)
  end.

Fixpoint mkCad_mapn(n:nat)(C D:Set)(f:C -> D){struct n}:
  mkCadn n C -> mkCadn n D:=
     match n return mkCadn n C -> mkCadn n D with
       |O =>  f
       |S n => @mkCad_mapn n (list C) (list D) (@map C D f)
    end.


Fixpoint CAD_build(n:nat):
  Cad Rat (Poln n) (Infon n) (cell_pointn n) (mkCadn n):=
  match n return 
    Cad Rat (Poln n) (Infon n) (cell_pointn n) (mkCadn n) with
    |O => One_dim_cad
    |S n => @CAD_make (Poln n) (Infon n) (cell_pointn n) (mkCadn n) (mkCad_mapn n)  (CAD_build n)
  end.




End CAD_gen.
