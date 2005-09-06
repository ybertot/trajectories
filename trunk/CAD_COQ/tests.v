(* pour commencer*)

 Require Import Utils.
 Require Import CAD_types.
 Require Import One_dim.
 Require Import Tarski.

 
 Require Import Qnorm.
 Module Q:= Q_NORM_SYST.
 Import Q.

 Module myCAD := CAD_gen Q.
 Import myCAD.

 Module ONE := MK_ONE_DIM Q.
 Import ONE.

 

(* Notations for polynomials *)
Infix "*":= Pol_mul.
Infix "+":= Pol_add.
Infix "-":= Pol_sub.
Notation "- x" := (Pol_opp x).


Fixpoint Q_of_nat(n:nat):Q:=
  match n with
    |O => r0
    |S n => r1 +r (Q_of_nat n)
  end.

(* Printers for sign_tables *)

(* Printing real numbers : erasure of the coding of alg.numbers, keeping
  only the interval *)
Inductive short_rpoint:Set:=
|Minfty : short_rpoint   (* -infty, useless *)
|B : Rat -> short_rpoint  (* a rational point between 2 roots*)
|R : Rat -> short_rpoint (* a rational root *)
|AR : Rat -> Rat -> short_rpoint. (* an algebraic root in th interval*)


Definition print_rpoint(z:Rpoint):=
match z with
|Minf _ => Minfty
|Between b => B b
|Root r => R r
|Alg_root z =>
  let (a, b, _, _, _):= z in AR a b
end.

Definition print_col(c:Rpoint * (list (Pol*Sign))):=
  let (r, csign):= c in
    (print_rpoint r, map (fun x => snd x) csign).


(* a printed sign table is a list of columns, a column :(Rpoint, list
  short_rpoint) is indexed by the short representation of a real
  number and is a list of signs for the polynomials of the family
  considered *)
Definition print_table(t : list (Rpoint * (list (Pol * Sign)))):=
  map print_col t.


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
(*****************  Computing  sign tables, examples  *********************)
(**************************************************************************)

Definition test(n:nat):= 
print_table (sign_table ((root_prod_1_2n n)::(root_prod_n_3n n)::nil) 90).


(* Temps sur valpareso *)
Time Eval compute in (test 2).
(*Finished transaction in 24. secs (23.6u,0.02s)*)


Time Eval vm_compute in (test 2).
(*Finished transaction in 2. secs (2.41u,0.s)*)

Time Eval vm_compute in (test 3).
(*Finished transaction in 98. secs (95.85u,0.s)*)
(* sans la vm ca passe pas...curieux...*)


(********************************************************************)
(*******          Des testes en plus de variable                *****)
(********************************************************************)





 Require Import Utils.
 Require Import CAD_types.
 Require Import One_dim.
 Require Import Up_dim.
 Require Import Tarski.

 
 Require Import Qnorm.
 Module Q:= Q_NORM_SYST.
 Import Q.

 Module myCAD := CAD_gen Q.
 Import myCAD.

(* Module ONE := MK_ONE_DIM Q.

 Module UP := MK_UP_DIM Q.
*)

 Definition onevar := CAD_build O.
 Definition twovar := CAD_build 1.

Set Implicit Arguments.

(* Pour l'affichage *)

Definition cell_type(Coef berncoef cell_point:Set) :=
(mkcell_point_up Rat Coef berncoef cell_point *
          list (Pol1 Coef * Sign))%type.


Definition polsign_of_cell(Coef berncoef cell_point:Set)
  (x:cell_type Coef berncoef cell_point):=
let (_,l1):=x in
l1.

Definition sign_of_cell(Coef berncoef cell_point:Set)
  (x:cell_type Coef berncoef cell_point):=
let (_,l1):=x in
map (fun x => snd x) l1.


Definition print_sign_res(Coef berncoef cell_point:Set)
  (l:list (list (cell_type Coef berncoef cell_point))):=
  map (fun x => map (@sign_of_cell Coef berncoef cell_point) x) l.

Definition print_polsign_res(Coef berncoef cell_point:Set)
  (l:list (list (cell_type Coef berncoef cell_point))):=
  map (fun x => map (@polsign_of_cell Coef berncoef cell_point) x) l.



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


Definition circle := ((X * X) + (Y * Y) - (Pc (Pc r1))).

Definition XY:= X * Y.


Eval vm_compute in (test_sign (Y::circle::nil) 90).

Eval vm_compute in (test_sign (X::circle::nil) 90).
