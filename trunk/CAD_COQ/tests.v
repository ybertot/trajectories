Add LoadPath "/0/user/amahboub/QArith".
Add LoadPath "/0/user/amahboub/CAD_COQ".

Require Import QArith.
Require Import Qabs.
Require Import Qnorm.
Require Import Bernstein.
Import Q_NORM_SYST.

Module Q_NORM_POLY := POLY Q_NORM_SYST.
Import Q_NORM_POLY.
Module Q_NORM_POLY_PROP:= RAT_PROP Q_NORM_SYST.
Import Q_NORM_POLY_PROP.



(********************polynomes de bernstein*********************************)

(****c=0, d=1****)
(*p=1*)

Definition B_1_0 := (PX (Pc (- R1)) xH R1).
Definition B_1_1 := PX (Pc R1) xH R0.

(*p=2*)
Definition B_2_0 := (PX (Pc (- R1)) xH R1) ^ 2.
Definition B_2_1 := PX (PX (Pc (- (2#1)))  xH (2#1)) xH R0.
Definition B_2_2 := PX (Pc R1) 2 R1.

(*p=3*)

Definition B_3_0:= (PX (Pc (- R1)) xH R1) ^ 3.
Definition B_3_1 := (PX (Pc (3#1)) xH R0)**((PX (Pc (- R1)) xH R1) ^ 2).
Definition B_3_2 := (PX (Pc (3#1)) 2 R0)**(PX (Pc (- R1)) xH R1).
Definition B_3_3 := PX (Pc R1) 3 R0.


Definition Q := (mult_cst B_3_0 (4#1))++(mult_cst B_3_1 (- 6#1))++(mult_cst B_3_2 (7#1))++(mult_cst B_3_3 (10#1)).

Definition Q' := (mult_cst B_3_0 (15#1))++(mult_cst B_3_1 (3#1))++(mult_cst B_3_2 (- 9#2))++(mult_cst B_3_3 (11#1)).

(****** sur [0, 1/2]******)
(*p=1*)
Definition B'_1_0:= PX (Pc (- (2#1))) xH R1.
Definition B'_1_1 := PX (Pc R1) xH R1.

(*p=2*)
Definition B'_2_0 := (PX (Pc (- (2#1))) xH R1) ^ 2.
Definition B'_2_1 := PX (PX (Pc (- (8#1)))  xH (4#1)) xH R0.
Definition B'_2_2 := PX (Pc (4#1)) 2 R1.

(*p=3*)
Definition B'_3_0:= (PX (Pc (- (2#1))) xH R1) ^ 3.
Definition B'_3_1 := (PX (Pc (6#1)) xH R0)**((PX (Pc (- (2#1))) xH R1) ^ 2).
Definition B'_3_2 := (PX (Pc (12#1)) 2 R0)**(PX (Pc (- (2#1))) xH R1).
Definition B'_3_3 := PX (Pc (8#1)) 3 R0.


Definition P:=(PX (Pc R1) xH (- (2#1)))**(PX (Pc R1) xH (- (3#1)))**(PX (Pc R1) xH  (8#1))**(PX (Pc R1) xH (- (6#1))).



(*********sous resultants******************************)

(*definir des variables a,b,c,d*)
Definition P:=PX (PX (PX (Pc R1) 2 a) 1 b) 1 c.
Definition P':= deriv P.







(* le polynome X *)
Definition P1 := (PX (Pc R1) xH R0).

(*  polynomes nul et 1 *)

Definition Pol0 := Pc R0.

Definition Pol1 := Pc R1.

(*5X + 3*)
Definition P2 := PX (Pc (5#1)) xH (3#1).

(*5X^3 +3*)
Definition P3 := PX (Pc (5#1)) (xI xH) (3#1).

(*X^2+1*)
Definition P4 := PX (Pc R1) (xO xH) R1.

(*X+1*)
Definition P5 := PX (Pc R1) xH R1.

(*X-1*)
Definition P6 := PX (Pc R1) xH (- R1).

(*X^2-1*)
Definition P7 := PX (Pc R1) (xO xH) (- R1).

(*X^9 + X^7 - 3*)
Definition P8 := PX P4 7 ((-3)#1).

Eval compute in bernstein 3 3 R0 R1.   

(**********************)
Add LoadPath "/0/user/amahboub/QArith".
Add LoadPath "/0/user/amahboub/cad_coq".



Require Import QArith.
Require Import Qnorm.
Require Import Sturm.
Require Import Qnotn.
Import Q_NOT_NORM.

Module Q_NOT_NORM_POLY := POLY Q_NOT_NORM.
Import Q_NOT_NORM_POLY.
