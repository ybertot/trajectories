(* pour commencer*)
 Require Import Tarski.
 Require Import Qnorm.
 Require Import One_dim.
 Require Import Qnorm.
 Require Import Utils.

 Require Import QNORM_SYST.
 Require Import Qnorm.
 Module Q:= Q_NORM_SYST.
 Import Q.

 Module myCAD := CAD_gen Q.
 Import myCAD.

(*
 Module ONE := MK_ONE_DIM Q.
 Import ONE.
*)



(* Tests en deux variables *)


Definition twovar := CAD_build 1.

(* affichage*)

(* que les pols et les signes *)



Definition cell_type :=
(unit * mk_Rpoint Q (uple5 Q Q (Pol1 Q) (Pol1 Q) (list Q)) *
  mk_Rpoint Q
  (uple5 Q Q (Pol1 (Pol1 Q)) (Pol1 (Pol1 Q))
    (list
      (uple5 (Pol1 Q) (Pol1 Q) N (option comparison)
        (option comparison)))) *
  list (Pol1 (Pol1 Q) * option comparison))%type.

Definition polsign_of_cell(x:cell_type):=
let (_,l1):=x in
l1.


Definition sign_of_cell(x:cell_type):=
let (_,l1):=x in
map (fun x => snd x) l1.


Definition print_sign_res(l:list (list cell_type)):=
  map (fun x => map sign_of_cell x) l.

Definition print_polsign_res(l:list (list cell_type)):=
  map (fun x => map polsign_of_cell x) l.


Definition test_sign(l:list (Pol1 (Poln 1)))(n:nat):=
  print_sign_res (Pol_cad twovar l n).

Definition test_polsign(l:list (Pol1 (Poln 1)))(n:nat):=
  print_polsign_res (Pol_cad twovar l n).



Fixpoint Q_of_nat(n:nat):Q:=
  match n with
    |O => r0
    |S n => r1 +r (Q_of_nat n)
  end.



Definition X := PX (Pc (Pc r1)) 1 (Pc r0).

Definition Y := Pc (PX (Pc r1) 1  r0).

Definition Pol := (Pol1 (Poln 1)).

Bind Scope P_scope with Pol.
Open Scope P_scope.

Definition plus := Pol_add twovar.
Definition minus := Pol_sub twovar.
Definition prod := Pol_mul twovar.



Infix "+":=plus:P_scope.
Infix "-":=minus:P_scope.
Infix "*":=prod:P_scope.


Definition circle := (X * X) + (Y * Y) - (Pc (Pc r1)).

Definition XY:= X * Y.

(* passe pas 
Eval vm_compute in (length (test_sign (X::circle::nil) 90)).
*)

Eval vm_compute in (test_sign (Y::circle::nil) 90).























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

