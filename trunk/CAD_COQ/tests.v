
(* Tests en deux variables *)

Definition X:=PX (Pc c1) 1 c0.




(********************************************************************************)
(********************************************************************************)
(********************************************************************************)



Require Import Qabs.
Require Import Qnorm.
Require Import One_dim.
Require Import CAD.


Module Q:=Q_NORM_SYST.
Module QFUNS:= RAT_FUNS Q.
Module QINT := RAT_INT_OPS Q.
Module ONE := MK_ONE_DIM Q.

Import Q.
Import QFUNS.
Import QINT.
Import ONE.



Load One_dim_test.

Inductive print_index:Set:=
|Pt : Q -> print_index
|Int : Q -> Q -> print_index
|B : Q -> print_index
|M : Q -> print_index.

Definition print_isol_box(i:ONE_DIM.isol_box):=
match i with
|ONE_DIM.Singl _ r => Pt r
|ONE_DIM.Pair _ p _ _ _ => let (a,b) := p in Int a b
|ONE_DIM.Minf _ r => M r
end.

Definition print_cell(z:ONE_DIM.cell_point_up):=
match z with
|ONE_DIM.Between _ r => B r
|ONE_DIM.Root i => print_isol_box i
end.

Definition print_table_cell(z:ONE_DIM.cell_point_up * list (Pol * Sign)):=
(print_cell (fst z), map (fun x => snd x) (snd z)).

Definition print_table(l:list (ONE_DIM.cell_point_up * list (Pol * Sign))):=
map print_table_cell l.







Fixpoint Q_of_nat(n:nat):Q:=
  match n with
    |O => r0
    |S n => r1 +r (Q_of_nat n)
  end.

(**************************************************************************)
(************** Builds P1(n) :=(X - n)(X - (n+1))....(X - 3n) **************)
(**************************************************************************)

Definition root_prod_n_3n(n:nat):=
  let aux := fix aux(m:nat):Pol :=
    match m with
      |O => (Pc r0)
      |S O => (PX (Pc r1) xH (-r (Q_of_nat (S n))))*
	(PX (Pc r1) xH (-r (Q_of_nat (2*n +1))))
      |S m' => (PX (Pc r1) xH (-r (Q_of_nat (n+m))))*
	(PX (Pc r1) xH (-r (Q_of_nat ((2*n)+m))))*(aux m')
    end in
    aux n.

(**************************************************************************)
(*****************  Builds P2(n) :=(X -1)(X -2)...(X -2n)  *****************)
(**************************************************************************)

Definition root_prod_1_2n(n:nat):=
 let aux := fix aux(m:nat):Pol :=
    match m with
      |O => (Pc r0)
      |S O => (PX (Pc r1) xH (-r (Q_of_nat (S n))))*
	(PX (Pc r1) xH (-r (Q_of_nat n)))
      |S m'=> (PX (Pc r1) xH (-r (Q_of_nat m)))*
	(PX (Pc r1) xH (-r (Q_of_nat (n+m))))*(aux m')
    end in
    aux n.
 
(**************************************************************************)
(************  Builds the list [X, (X-1),(X-2),...,(X-(n-1))] *************)
(**************************************************************************)

Fixpoint mono_list(n:nat):list (Pol1 Q):=
  match n with
    |O => (PX (Pc r1) xH (-r r0))::nil
    |S m => (PX (Pc r1) xH (-r (Q_of_nat m)))::(mono_list m)
  end.

(**************************************************************************)
(**********************  Computing  sign tables  **************************)
(**************************************************************************)

Definition test(n:nat):= 
print_table (sign_table ((root_prod_1_2n n)::(root_prod_n_3n n)::nil) 90).


Eval compute in (print_table (sign_table ((root_prod_1_2n 2)::nil) 90)).
Eval compute in (family_root ((root_prod_1_2n 2)::nil) 90).



(********************************************************************************)
(* Tests en deux variables *)

Require Import Qabs.
Require Import Qnorm.
Require Import One_dim.
Require Import CAD.
Require Import Up_dim.



Module Q:=Q_NORM_SYST.
Module QFUNS:= RAT_FUNS Q.
Module QINT := RAT_INT_OPS Q.
Module ONE := MK_ONE_DIM Q.
Module UP := MK_UP_DIM Q.


Import Q.
Import QFUNS.
Import QINT.
Import ONE.
Import UP.





Definition Dim_two_cad := CAD_make One_dim_cad.


(*
Definition P0:=  Pol_0 One_dim_cad.
Definition P1:= Pol_1 One_dim_cad.
Definition Padd := Pol_add One_dim_cad.
Definition Pmul := Pol_mul One_dim_cad.
Definition Psub := Pol_subOne_dim_cad.
Definition Popp :=  Pol_opp One_dim_cad.
Definition Pdeg :=  Pol_deg One_dim_cad.
Definition mkPX := Pol_mk_PX One_dim_cad.
Definition Pzero_test := Pol_zero_test One_dim_cad.
Definition P_of_pos := Pol_of_pos One_dim_cad.
Definition Pbase_cst_sign := Pol_base_cst_sign One_dim_cad.
Definition Ppow := Pol_pow One_dim_cad.
Definition Pdiv := Pol_div One_dim_cad.
Definition Psubres_list := Pol_subres_list One_dim_cad.
Definition Psubres_ceof_list One_dim_cad.
Definition P_gcd := Pol_gcd One_dim_cad.
Definition Psquae_free := Pol_square_free One_dim_cad.
Definition Pderiv := Pol_deriv One_dim_cad.
Definition Peval := Pol_eval One_dim_cad.
Definition Pis_base_cst := Pol_is_base_cst One_dim_cad.
Definition mk_Pc := Pol_mk_Pc One_dim_cad.
Definition mk_coef := Pol_mk_coef One_dim_cad.
Definition Pmult_base_cst := Pol_mult_base_cst One_dim_cad.
Definition Pdiv_base_cst := Pol_div_base_cst One_dim_cad.
Definition P_partial_eval := Pol_partial_eval One_dim_cad.
Definition Pcell_point_up := cell_point_upOne_dim_cad.Set;
Definition Pcell_point_up_refine := cell_point_up_refine One_dim_cad.
Definition low_bound := Pol_low_bound One_dim_cad.
Definition up_bound := Pol_up_bound One_dim_cad.
Definition value_bound := Pol_value_bound One_dim_cad.
Definition PCert := Cert One_dim_cad.
Definition Pmk_Cert := mk_Cert One_dim_cad.
Definition Pbuild_Cert := build_Cert One_dim_cad.
Definition PCert_fst := Cert_fst One_dim_cad.
Definition low_sign := Pol_low_sign One_dim_cad.
Definition sign_at := Pol_sign_at One_dim_cad.
Definition cad := Pol_cad One_dim_cad.
*)

