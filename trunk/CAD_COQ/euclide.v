Add LoadPath "/0/user/amahboub/RING".
Add LoadPath "/0/user/amahboub/QArith".

Load "QPol1.v".

Require Import Pol1_is_ring.
Require Import ZArith.
Require Import QArith.
Require Import Bool_nat.

Open Scope Q_scope.
Open Scope P_scope.


(*normalisation des polynomes : vire les coefs nuls en tete, le mettre
  dans Pol_is_ring? il faut un test a zero sur les coefficients
 Fixpoint norm_poly(A:Poly):Poly:=
   match A with
     |Pc _ => A
     |PX B b => let C := (norm_poly B) in
       match C with
	 |Pc (c#d)=> match c with
		      |Z0 => Pc b
		       |_ => PX C b
		     end
	|PX _ _ => PX C b
       end
   end.
 *)

(* division d'un polynome par une constante  *)
 Fixpoint div_cst(A:Poly)(q:Q){struct A}:Poly:=
   match A with
     |Pc a => Pc (a/q)
     |PX P p => PX (div_cst P q) (p/q)
   end.
 
  (* produit d'un polynome par ue consante *)
 Fixpoint mult_cst(A:Poly)(q:Q){struct A}:Poly:=
  match A with
    |Pc a => Pc (a*q)
    |PX P p => PX (mult_cst P q) (p*q)
  end.



(*couple degre * coef dominant pour un polynome non necessairement
    normalise, le degre est celui du normalise*)
 Fixpoint deg_coefdom(A:Poly):nat*Q :=
   match A with
     |Pc a => (O,a)
    |PX P p => let (d,c):= (deg_coefdom P) in
      let c1 := Qnum c in
	match d with
	  |O => match c1 with
		  |Z0 => (O, p)
		  |_ => (1, c)
		end
	  |S n => ((S (S n)), c)
	end
   end.


 
 
(*division euclidienne bebete des polynomes a coef dans Q:
  - C dit etre en forme normale, on  commence donc par le normaliser
  - div_euclide A C = (Q,R) avec A = BQ +R et 
  - B est le normalse de C
	- deg (R)< deg(C)

  le cas non trivial :
  si on veut diviser Ax +a par B, avec A = BQ1 + R1 et deg(R1)<deg(B)
  alors AX+a=(BQ1)X + R1X +a
  deux possibilites :
    - ou bien deg (R1X +a) < deg (B) on a gagne, Q = X*Q1 et R = R1X + a
    - ou bien deg (R1X +a) = deg (B) et  Q = (X*Q1+r/b) et R = R1X - r/b B + a
  ou r = coefdom(R) et b = coefdom(B)
  
  *)
 

 Fixpoint div_euclide(A C:Poly){struct A}:Poly*Poly :=
  let B := (norm_poly C) in 
     match A, B with
       |Pc a, Pc b => (Pc (a/b), Pc (0#1))
       |Pc a, PX _ _ => (Pc (0#1), Pc a)
       |PX P p, Pc b => (div_cst A b, Pc (0#1)) 
       |PX P p, PX _ _ =>
	 let (Q1, R):=div_euclide P B in
	 let R1 := (norm_poly R) in
	   let (dr, r) := deg_coefdom R1 in
	     let (db,b) := deg_coefdom B in
	       match (Qnum r),(lt_ge_dec dr (db-1)) with
		 |  Z0, _ => (PX Q1 (0#1), Pc p)
		 |  _, left _ => (PX Q1 (0#1), PX R1 p)
		 |  _, right _ => let quo := (PX Q1 (r/b)) in
		   let rem := (PX R1 (0#1)) -- (mult_cst B (r/b)) ++ (Pc p) in
		     ((norm_poly quo),(norm_poly rem))
	       end
     end.

Definition P1 := (PX (Pc (9#1)) (3#1)).
Definition P2 := (PX (Pc (3#1)) (0#1)).


