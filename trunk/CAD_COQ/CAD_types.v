Unset Boxed Definitions.
Unset Boxed Values.



Require Export NArith.
Require Export Mylist.

Set Implicit Arguments.



  (************************************************************)
  (*****         Type definitions for the CAD              ****)
  (************************************************************)



(** Type of result of sign computations *)
Definition Sign := option comparison.


(** Polynomials in Horner form, one var with coefs in C *)
Inductive Pol1(C:Set):Set:=
  |Pc : C-> Pol1 C
  |PX : Pol1 C -> positive -> C -> Pol1 C.


(** Elements of R :
either -infty : a least bound for the roots considered,
or a rational point between two consecutive roots
or a rational root
or an algebraic root: Alg is the type of the encoding, to be defined
in Gen_functor.v at each level *)

Inductive mk_Rpoint(Rat:Set)(Alg:Set):Set:=
  |Minf : Rat -> mk_Rpoint Rat Alg
  |Between : Rat -> mk_Rpoint Rat Alg
  |Root : Rat -> mk_Rpoint Rat Alg
  |Alg_root : Alg -> mk_Rpoint Rat Alg.




(** Cad gathers what is needed to go from dimension n to dim n+1 *)
Record Cad(Rat:Set)(C:Set) :Type := mk_cad{
  Pol_0: Pol1 C;
  Pol_1:Pol1 C;
  Pol_add : Pol1 C -> Pol1 C -> Pol1 C;
  Pol_mul : Pol1 C -> Pol1 C -> Pol1 C ;
  Pol_sub : Pol1 C -> Pol1 C -> Pol1 C;
  Pol_opp : Pol1 C -> Pol1 C;
  Pol_deg : Pol1 C ->N;
  Pol_mk_PX : Pol1 C -> positive -> C -> Pol1 C;
  Pol_zero_test : Pol1 C -> bool;
  Pol_of_pos : positive -> Pol1 C;
  Pol_base_cst_sign:Pol1 C ->option comparison;
  Pol_pow : Pol1 C -> N -> Pol1 C;
  Pol_div : Pol1 C -> Pol1 C -> Pol1 C;
  Pol_gcd_gcd_free: Pol1 C -> Pol1 C -> (Pol1 C)*(Pol1 C)*(Pol1 C);
  Pol_square_free : Pol1 C -> Pol1 C;
  Pol_deriv : Pol1 C -> Pol1 C;
  Pol_eval : Pol1 C -> C -> C;
  Pol_is_base_cst : Pol1 C -> bool;
  Pol_mk_Pc : Rat -> Pol1 C;
  Pol_mk_coef : Rat -> C;
  Pol_mult_base_cst : Pol1 C -> Rat -> Pol1 C;
  Pol_div_base_cst : Pol1 C -> Rat -> Pol1 C;
  Pol_partial_eval : Pol1 C -> Rat -> C;
  Rpoint : Set;
  cell_point:Set; 
  cell_point_up:Set;
  cell_point_proj : cell_point_up -> cell_point;
  rpoint_of_cell : cell_point_up -> Rpoint;
  mk_cell_point_up : cell_point -> Rpoint -> cell_point_up;
  cell_point_up_refine : cell_point_up -> nat -> option cell_point_up;
  Pol_low_bound : Pol1 C -> cell_point -> Rat;
  Pol_up_bound : Pol1 C -> cell_point -> Rat;
  Pol_value_bound : cell_point_up -> Pol1 C ->  (Rat*Rat);
  Info:Set;
  mk_Info :
    Pol1 C -> Pol1 C -> N -> option comparison -> option comparison -> Info;
  Info_of_Pol: (option comparison)->Pol1 C ->Info;
  Pol_of_Info : Info -> Pol1 C;
  Pol_low_sign :
    cell_point -> Pol1 C -> Pol1 C -> nat -> (cell_point * option comparison);
  Pol_sign_at :
 	Info -> cell_point_up -> nat -> 
		cell_point_up*((Pol1 C)*(option comparison));
  Cad_col:Set;
  cell_point_of_Cad_col : Cad_col -> cell_point_up;
  sign_col_of_Cad_col : Cad_col -> list ((Pol1 C)  * Sign);
  mk_Cad_type:Set -> Set;
  Cad_map : forall A B:Set, mk_Cad_type A -> (A -> B) -> mk_Cad_type B;
  Pol_cad : list (Pol1 C) -> nat -> mk_Cad_type Cad_col
 }.
