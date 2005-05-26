Require Import ZArith.
Require Import Mylist.
Require Import Qabs_rec.
Section CAD_def.

Set  Implicit Arguments.

Variable Rat_struct : Rat_ops.
Let C_base:= Rat Rat_struct.

Record Cad :Type := mk_cad{
  C:Set;
  CO : C;
  CI : C;
  Cadd : C -> C -> C;
  Cmul : C -> C -> C;
  Csub : C -> C -> C;
  Copp : C -> C;
  Czero_test : C -> bool;
  C_of_pos : positive -> C;
  Cpow : C -> N -> C;
  Cdiv : C -> C -> C;
  Pol : Set;
  Pol_0: Pol;
  Pol_1:Pol;
  Pol_add : Pol -> Pol -> Pol;
  Pol_mul : Pol -> Pol -> Pol ;
  Pol_sub : Pol -> Pol -> Pol;
  Pol_opp : Pol -> Pol;
  Pol_deg : Pol ->N;
  Pol_mk_PX : Pol -> positive -> C -> Pol;
  Pol_zero_test : Pol -> bool;
  Pol_of_pos : positive -> Pol;
  Pol_pow : Pol -> N -> Pol;
  Pol_div : Pol -> Pol-> Pol;
  Pol_subres_list : Pol -> Pol -> list (Pol);
  Pol_subres_coef_list : Pol -> Pol -> list C;
  Pol_gcd : Pol -> Pol -> Pol;
  Pol_square_free : Pol -> Pol;
  Pol_deriv : Pol -> Pol;
  Pol_eval : Pol -> C -> C;
  Pol_is_base_cst : Pol -> bool;
  Pol_mk_Pc : C_base -> (Pol);
  Pol_mk_coef : C_base -> C;
  Pol_mult_base_cst : Pol -> C_base -> Pol;
  Pol_div_base_cst : Pol -> C_base -> Pol;
  Pol_partial_eval : Pol -> C_base -> C;
  cell_point:Set; 
  cell_point_up:Set;
  cell_point_proj : cell_point_up -> cell_point;
  cell_point_up_refine : cell_point_up -> nat -> option cell_point_up;
  Pol_low_bound : Pol -> cell_point -> C_base;
  Pol_up_bound : Pol -> cell_point -> C_base;
  Pol_low_sign :Pol -> cell_point -> option comparison;
  Pol_value_bound : cell_point_up -> Pol->  (C_base*C_base);
  Cert:Set;
  mk_Cert : Pol -> Pol -> N -> option comparison -> Cert;
  build_Cert:Pol->(option comparison)->Cert;
  Cert_fst : Cert -> Pol;
  Pol_sign_at :
 	Cert -> cell_point_up -> nat -> 
		cell_point_up*(option comparison);
    Pol_cad : list Pol -> nat -> list (cell_point_up * (list (option comparison)))
 }.
 
End CAD_def.
