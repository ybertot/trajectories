Require Import Utils.
Set Implicit Arguments.



 Notation  "x # y" := (MkRat x y)(at level 20, no associativity).

 Notation "x ++ y" := (cadd x y) (at level 50, left associativity).
 Notation "x ** y":= (cmul x y) (at level 40, left associativity).
 Notation "-- x" := (copp x) (at level 35, right associativity).
 Notation "x -- y" := (csub x y) (at level 50, left associativity).
 Notation "x // y" := (cdiv x y) (at level 40, left associativity).




(*
Inductive Pol1(C:Set):Set:=
 |Pc : C-> Pol1 C
 |PX : Pol1 C -> positive -> C -> Pol1 C.
*)
Definition Pol := Pol1 Coef.

Definition P0 := Pc  c0.
Definition P1 := Pc c1.

 
Definition mkPX P i c := 
  match P with
  | Pc p => if (czero_test p) then Pc c else PX P i c
  | PX P' i' c' => if (czero_test c') then PX P' (i' + i) c else PX P i c
  end.

(* all the following defined operations preserve normalisation *)

 Definition Pol_opp:=fix Pol_opp (P:Pol):Pol :=
   match P with
     |Pc p => Pc (-- p)
     |PX P i p => mkPX (Pol_opp P) i (-- p)
   end.
Notation "- P" := (Pol_opp P).

(** Addition and subtraction **)
 
(*P+Pc c*)
 Definition Pol_addC (P:Pol)(c:Coef):Pol :=
  match P with
  | Pc c1 => Pc (c1 ++ c)
  | PX P i c1 => PX P i (c++c1)
  end.

(*P - Pc c*)
 Definition Pol_subC (P:Pol) (c:Coef) : Pol :=
  match P with
  | Pc c1 => Pc (c1 -- c)
  | PX P i c1 => PX P i (c1 -- c)
  end.

 
(*Pop is Padd _ P' where P' is a fixed poynomial*)
Definition Pol_addX(Pol_op:Pol->Pol)(P':Pol):=
      fix Pol_addX(i':positive)(P:Pol) {struct P} : Pol :=
     match P with
       | Pc c => PX P' i' c
       | PX P i c =>
	 match ZPminus i i' with
	   | Zpos k => mkPX (Pol_op (PX P k c0)) i' c
	   | Z0 => mkPX (Pol_op P) i c
	  | Zneg k => mkPX (Pol_addX k P) i c
	 end
     end.
   

    (*P-P'*X^i'*)
(*Pop is Padd _ P' *)
Definition Pol_subX(Pol_op:Pol->Pol)(P':Pol):=
   fix Pol_subX(i':positive)(P:Pol){struct P} : Pol :=
     match P with
       | Pc c => PX (- P') i' c
       | PX P i c =>
	 match ZPminus i i' with
	   | Zpos k => mkPX (Pol_op (PX P k c0)) i' c
	   | Z0 => mkPX (Pol_op P) i c
	   | Zneg k => mkPX (Pol_subX k P) i c
	 end
     end.
 
 
 (* Inv : is_norm P, is_norm P' *)
 Definition Pol_add := fix Pol_add (P P': Pol) {struct P'} : Pol :=
   match P' with
     | Pc c' => Pol_addC P c'
     | PX P' i' c' =>
       match P with
	 | Pc c => PX P' i' (c ++ c')
	 | PX P i c =>
	   match ZPminus i i' with
	     | Zpos k => mkPX (Pol_add (PX P k c0) P') i' (c ++ c')
	     | Z0 => mkPX (Pol_add P P') i (c ++ c')
	     | Zneg k => mkPX (Pol_addX (fun x => Pol_add x P') P' k P) i (c ++ c')
	   end
       end
   end.
 Notation "P + P'" := (Pol_add P P').

 Definition Pol_sub :=
   fix Pol_sub (P P': Pol) {struct P'} : Pol :=
   match P' with
     | Pc c' => Pol_subC P c'
     | PX P' i' c' =>
       match P with
	 | Pc c => PX (- P') i' (c -- c')
	 | PX P i c =>
	   match ZPminus i i' with
	     | Zpos k => mkPX (Pol_sub (PX P k c0) P') i' (c -- c')
	     | Z0 => mkPX (Pol_sub P P') i (c -- c')
	     | Zneg k => mkPX (Pol_subX (fun x => Pol_sub x P') P' k P) i (c -- c')
	   end
       end
   end.
 Notation "P - P'" := (Pol_sub P P').
 
 (** Multiplication *) 


(*P*(Pc c) *)
Definition Pol_mult_cst_aux :=
 fix Pol_mult_cst_aux (P:Pol) (c:Coef) {struct P} : Pol :=
  match P with
  | Pc c' => Pc (c' ** c)
  | PX P i c' => mkPX (Pol_mult_cst_aux P c) i (c'** c)
  end.

(*hack to speed up*)
 Definition Pol_mult_cst P c :=
  if (czero_test c) then P0 else
  if (czero_test (c -- c1)) then P else Pol_mult_cst_aux P c.
 
 Definition Pol_mul := fix Pol_mul(P P':Pol) {struct P'} : Pol :=
  match P' with
  | Pc c' => Pol_mult_cst P c'
  | PX P' i' c' => 
     (mkPX (Pol_mul P P') i' c0) + (Pol_mult_cst P c')
  end.

 Notation "P * P'" := (Pol_mul P P').

 Definition Pol_zero_test(P:Pol):bool:=
   match P with
     |Pc c => (czero_test c)
     |PX _ _ _=> false
   end.

 Definition Pol_of_pos(p:positive):Pol:= Pc (cof_pos p).

 (*P^n*)
Definition Pol_pow':=
 fix Pol_pow'(P:Pol)(p:positive){struct p}:Pol:=
   match p with
     |xH => P
     |xO p' => let Q:=(Pol_pow' P p') in (Pol_mul Q Q)
     |xI p' => let Q:=(Pol_pow' P p') in (Pol_mul (Pol_mul Q Q) P)
   end.

 Definition Pol_pow(P:Pol)(n:N):Pol :=
   match n with
     |N0 => P1
     |Npos p => Pol_pow' P p
   end.


   
  (*couple degree * coefdom for a polynomial in normal form *)
Definition Pol_deg_coefdom:= 
fix Pol_deg_coefdom(A:Pol) : N*Coef :=
   match A with
     |Pc a => (N0,a)
     |PX P i p => let (d,c) := (Pol_deg_coefdom P) in (Nplus (Npos i) d, c)
   end.

Definition Pol_deg :=
 fix Pol_deg(P:Pol):N:=
   match P with 
   |Pc _ => N0
   |PX P i _ => let d := Pol_deg P in (Nplus (Npos i) d)
 end.

Definition Pol_dom :=
  fix Pol_dom(P:Pol):Coef:=
  match P with
   |Pc p => p
   |PX P _ _ => Pol_dom P
  end.
   
(*division:like an euclidian division, but if the division over coef
fails, returns None*)

Definition Pol_div_cst :=
fix Pol1_div_cst(A:Pol)(q:Coef){struct A}: Pol:=
     match A with
       |Pc a => Pc (a // q)
       |PX P i p => PX (Pol1_div_cst P q) i (p // q)
     end.


 (*auxiliary division of RX^i by D.invariant : 
  -- deg R < deg D
  -- R <> 0
  -- D is not constant *)
Definition Pol_div_aux(D:Pol):=
	let (dd, cd) := Pol_deg_coefdom D in
fix Pol_div_aux(R:Pol)(i:positive){struct i}:Pol*Pol:=
     	let (dr,cr) := (Pol_deg_coefdom R) in
       	match (Ncompare (dr + (Npos i)) dd) with
		 |Lt => (Pc c0, PX R i c0)
		 | _  => 
		   match i with
		   | xH => (Pc (cr // cd), (mkPX R xH c0) - (Pol_mult_cst D (cr//cd)))
		   | xO p =>
		       let (Q1, R1) := (Pol_div_aux R p) in
		       let (dR1, cR1):=(Pol_deg_coefdom R1) in
		       if (czero_test cR1) then (mkPX Q1 p c0, Pc c0)
		       else
			 let (Q2, R2):=(Pol_div_aux R1 p) in 
			 ((mkPX Q1 p c0) + Q2, R2)
		  | xI p =>
		       let (Q1, R1):=(Pol_div_aux R p) in
		       let (dR1, cR1):=Pol_deg_coefdom R1 in
		       if (czero_test cR1) then 
			 ((mkPX Q1 (Psucc p) c0), Pc c0)
		       else
			 let (Q2, R2) := (Pol_div_aux R1 p) in
			 let (dr2, cr2) := (Pol_deg_coefdom R2) in
				 if (czero_test cr2) then
			   ((mkPX Q1 (Psucc p) c0)+(mkPX Q2 xH c0), Pc c0)
			 else
			   match (Ncompare (Nsucc dr2) dd) with
				   | Lt => 
				     ((mkPX Q1 (Psucc p) c0)+(mkPX Q2 xH c0), mkPX R2 xH c0)
				   | _ =>
				     let quo := (mkPX Q1 (Psucc p) c0)+ (mkPX Q2 xH c0)+(Pc (cr2//cd)) in
        		             let rem := (mkPX R2 xH c0) - (Pol_mult_cst D (cr2//cd)) in
				     (quo,rem)
				   end
			   end
       	end.
 		


(*straightforward division of polynomials with coef in Rat:
  - as usual arguments are supposed to be normalized
  - div_euclide A B = (Q,R) with  A = BQ ++ and 
	--either deg(R)< deg(B)
	-- or deg(R)=deg(B)=0 and R != P R0
	-- Q and R are normalized
  ** non trivial case :
  if AX^i +a is to be divided by B, with  A = PQ1 + c1 and deg(c1)<deg(B)
  then AX+a=(BQ1)X^i + c1X^i +a and :
    - either deg (c1X^i +a) < deg (B),it ok : Q = X^i*Q1 and R = c1X^i + a
    - or deg (c1X^i +a) >= deg (B) and  Q = (X^i*Q1+Q2) et R = R2 + a
  where (Q2, R2) = div_aux B db cb c1 i i.e. c1X^i = Q2B ++2
  ** poly returned are normalized as soon as args are normalized
  *)
 
 (*first division by a non constant polynomial*)

Definition Pol_euclide_div_PX(B:Pol):=
	let (db,cb) := Pol_deg_coefdom B in
		 	fix Pol_euclide_div_PX (A :Pol):Pol*Pol :=
  	 match A with
     	|Pc a => (Pc c0, Pc a)
     	|PX P i p =>
       	let (Q1, R1):=Pol_euclide_div_PX P in
		 let (dr, r) := Pol_deg_coefdom R1 in
		   match (Pol_zero_test R1),(Ncompare (Nplus (Npos i) dr) db) with
		     |true, _ => (mkPX Q1 i c0, Pc p)
		     | _ , Lt => (mkPX Q1 i c0, mkPX R1 i p)
		     | _ , _ => let (Q2, R2) := (Pol_div_aux B R1 i) in
		       ((mkPX Q1 i c0)+Q2, R2 + Pc p)
		   end
   	end.




 (*general division function *)
 Definition Pol_euclide_div(A B:Pol):Pol*Pol :=
   match B with
     |Pc q => (Pol_div_cst A q, Pc c0) 
     |_ => (Pol_euclide_div_PX B A)
   end.


 Definition Pol_div(A B:Pol):Pol:= fst (Pol_euclide_div A B).


(*Pol1 is a coef_set


 Definition Pol1_is_coef_set :=
   mk_iring Pol P0 P1 Pol_add Pol_mul Pol_sub Pol_opp
   Pol_zero_test Pol_of_pos Pol_pow Pol_div.

*)

  (*Derivative*)
Definition Pol_deriv := 
 fix Pol1_deriv(P:Pol):Pol :=
   match P with
     |Pc c => Pc c0
     |PX A i a => match i with
		    |xH => A +(mkPX (Pol1_deriv A) xH c0)
		    |_ => (Pol_mult_cst (PX A (Ppred i) c0) (cof_pos i)) +
		      (mkPX (Pol1_deriv A) i c0)
		  end
   end.
   



  (*q to the n*(n+1)/2 *)
 Definition sum_pow(q:Coef)(n:N):Coef :=
   match n with
     |N0 => c1
     |Npos p => 
       match p with
	 |xH => q
	 |xO p' => cpow q (Npos (Pmult p' (Psucc p)))
	 |xI p' => cpow q (Npos (Pmult (Psucc p') p))
       end
   end.


(*computation of the kth Pol1_subresultant coefficient*)
 Definition Pol_subres_aux (j k:N)(q q':Coef): Coef:=
   let t := (Npred (Nminus j k)) in
    (sum_pow (-- c1) t)**(cpow (q // q') t)** q.
  

  (*next polynomial in the sequence,after ASRi_1 and SRj_1 and arguments
    for the possible next step of computations. if is nul, then B was
    the last poly of the sequence. SRj_1 is no nul*)
 


 Definition Pol_next_subres(SRi_1 SRj_1:Pol)(srj:Coef)(i j:N):
   Pol * Coef * N * N :=
   let (k, dom_srj_1) := (Pol_deg_coefdom SRj_1) in
   let (d, dom_sri_1) := (Pol_deg_coefdom SRi_1) in
   let next_SR := fun x:Coef =>
     -(Pol_div_cst 
       (snd (Pol_euclide_div (Pol_mult_cst SRi_1 x) SRj_1))
       (srj **  dom_sri_1)) in
     match (Ncompare k  (Npred j)) with
       |Eq => 
	 let srj_1 := dom_srj_1 in
	   (next_SR (cpow dom_srj_1 2), dom_srj_1, j, k)
       |_ => 
	 let srk := (Pol_subres_aux j k dom_srj_1 srj) in
	   (next_SR (dom_srj_1 **  srk), srk, j, k)
     end.



 Definition Pol_next_subres_triple(Ti_1 Tj_1:Pol*(Pol*Pol))(srj:Coef)(i j:N):
   (Pol*(Pol*Pol))* Coef * N * N :=
   let (SRi_1,Di_1) := Ti_1 in
   let (SRj_1,Dj_1) := Tj_1 in
   let (Ui_1,Vi_1) := Di_1 in
   let (Uj_1,Vj_1) := Dj_1 in
   let (k, dom_srj_1) := (Pol_deg_coefdom SRj_1) in
   let (d, dom_sri_1) := (Pol_deg_coefdom SRi_1) in
   let next :=
     (fun x => 
       let (C,R) := (Pol_euclide_div (Pol_mult_cst SRi_1 x) SRj_1) in
       (C, Pol_div_cst R ((-- srj)** dom_sri_1)) ) in
   let next_UV :=
     (fun (x:Coef)(Pi_1 Pj_1 C:Pol) =>
       (Pol_div_cst
	 ((C * Pj_1) - (Pol_mult_cst Pi_1 x)) (srj** dom_sri_1))) in
     match (Ncompare k  (Npred j)) with
       |Eq => 
	 let y:= (cpow dom_srj_1 2) in
	 let (C,SR) := next y in
	   (SR, (next_UV y Ui_1 Uj_1 C, next_UV y Vi_1 Vj_1 C), dom_srj_1, j, k)
       |_ => 
	 let srk := (Pol_subres_aux j k dom_srj_1 srj) in
	 let y:= (dom_srj_1 **  srk) in
	 let (C,SR) := next y in
	   (SR, (next_UV y Ui_1 Uj_1 C, next_UV y Vi_1 Vj_1 C), srk, j, k)
     end.


   (*builds the list, from A B n ensures termination and will be deg P + 1*)

Definition Pol_subres_list1:=
 fix Pol1_subres_list1(A B:Pol)(q:Coef)(i j:N)(m:nat){struct m}:list Pol :=
   match m with
     |O => nil
     |S n => 
       let (next,l) := (Pol_next_subres A B q i j) in
       let (next',k) := next in
       let (SR, sr) := next' in
	 if (Pol_zero_test SR) then nil
	   else   SR :: (Pol1_subres_list1 B SR sr k l n)
   end.

 Definition Pol_subres_list(A B:Pol) := 
   let p := Pol_deg A in
   let q := Pol_deg B in
   A :: B :: (Pol_subres_list1 A B c1 (p+1) p  (S (nat_of_N p))). 


Definition Pol_subres_coef_list(A B:Pol):=
   let dom := (fun x => Pol_dom x) in
   let res := Pol_subres_list A B in
     map dom res.


Definition Pol_ext_signed_subres_list :=
 fix Pol1_ext_signed_subres_list(T T':Pol*(Pol*Pol))(q:Coef)(i j:N)(m:nat)
   {struct m}:list (Pol*(Pol*Pol)) :=
   let (B,D):= T' in
     if (Pol_zero_test B) then nil
       else
	 match m with
	   |O => nil
	   |S n => 
	     let (next,l) := (Pol_next_subres_triple T T' q i j) in
             let (next',k) := next in
	     let (next_T, sr) := next' in
	     let (next_SR,_) := next_T in
     	       next_T :: (Pol1_ext_signed_subres_list T' next_T sr k l n)
	 end.



  (*first polynomials in the subresultant chain
   
   Definition Pol1_subres_chain_init :=
     match (Rat_sign dom_p) with
       |Eq => (Pc R0, R0, Pc R0) must never happen!
       |Gt => (P, R1, Q)
       |Lt => match (Npred (Nminus deg_p deg_q)) with
		    |N0 => (P, - R1, Q) 
		    |Npos p => match p with
				 |xO _ => (P, (- R1), Q) 
				 |_ => (-- P, R1, (-- Q))
			       end
		  end
     end.
   

   Definition SRq := snd subres_chain_init.
   Definition SRp := fst (fst subres_chain_init).
   Definition srp := snd (fst subres_chain_init).
   *)

 
   (* extended signed subres chain *)
   Definition Pol_ext_signed_subres_chain(P Q:Pol) : list (Pol*(Pol*Pol)) :=
	let ddp := Pol_deg_coefdom P in
   	let ddq := Pol_deg_coefdom Q in
   	let deg_p := fst ddp in
   	let deg_q := fst ddq in
   	let dom_p := snd ddp in
   	let dom_q := snd ddq in
	let Tp := (P, (P1,P0)) in
	let Tq := (Q, (P0,P1)) in
     	Tp :: (Tq :: 	
    	(Pol_ext_signed_subres_list
      	Tp Tq  c1 deg_p (Npred deg_p) (S (nat_of_N deg_p)))).
     
       



   (*gcd of P and Q : last subresultant dP>dQ*)
 Definition Pol_gcd_strict (P Q:Pol) :=
   let l := (Pol_subres_list P Q) in 
   let SRj := (last_elem l Q) in
   let srj := Pol_dom SRj in
   let cP := Pol_dom P in
     Pol_div_cst (Pol_mult_cst SRj cP) srj.
    

 Definition Pol_gcd(P Q:Pol) :=
   let (dP, cP):= Pol_deg_coefdom P in
   let (dQ,cQ) := Pol_deg_coefdom Q in
     match Ncompare dP dQ with
       |Lt  => Pol_gcd_strict Q P
       |Gt  => Pol_gcd_strict P Q
       |Eq => Pol_gcd_strict P ((Pol_mult_cst Q cP) - (Pol_mult_cst P cQ))
     end.

  (*gcd of P and Q, and gcd free part of P with respect to Q, pourZ,
ca rajoute des contenus dans les DEUX
Definition gcd_gcd_free (P Q:Pol) :=
   let cP := Pol_dom P in
   let (Tj, Tj_1):= two_last_elems (Pol_ext_signed_subres_chain P Q) 
     ((Pc R0, (Pc R0,Pc R0)),(Pc R0, (Pc R0,Pc R0))) in
   let (SRj,Dj) := Tj in
   let srj := Pol_dom SRj in
   let (_,Dj_1) := Tj_1 in
   let (_, Vj_1) := Dj_1 in
   let cVj_1 := Pol_dom Vj_1 in 
     (Pol_div_cst (Pol_mult_cst SRj cP) srj, (Pol_div_cst (Pol_mult_cst Vj_1 cP) cVj_1)).
*)    

(*WARNING we have NOT gcd*(gcd_free)=P but up to a constant
returns, gcd, gcd_free of P, gcd_free of Q*)
 Definition Pol_gcd_gcd_free_strict (P Q:Pol) :=
   let cP := Pol_dom P in
   let (Tj, Tj_1):= two_last_elems (Pol_ext_signed_subres_chain P Q) 
     ((Pc c0, (Pc c0,Pc c0)),(Pc c0, (Pc c0,Pc c0))) in
   let (SRj,Dj) := Tj in
   let srj := Pol_dom SRj in
   let (_,Dj_1) := Tj_1 in
   let (Uj_1, Vj_1) := Dj_1 in
   let cVj_1 := Pol_dom Vj_1 in
   let cUj_1 := Pol_dom Uj_1 in
     (Pol_div_cst (Pol_mult_cst SRj cP) srj,
       Pol_div_cst (Pol_mult_cst Vj_1 cP) cVj_1,
       Pol_div_cst (Pol_mult_cst Uj_1 cP) cUj_1).


(*TODO virer les contenus constants?*)


  (*gcd of P and Q : last subresultant, one preliminary step for
 polys of same deg*)
 Definition Pol_gcd_gcd_free (P Q:Pol) :=
   match P, Q with
   |Pc p, Pc q => 
	let (a,b) := cgcd_gcd_free p q in (Pc (snd a), Pc (snd a), Pc b)
   |_,_ => 
   let (dQ,cQ):= Pol_deg_coefdom Q in
   let (dP,cP):= Pol_deg_coefdom P in
     match (Ncompare dP dQ) with
       |Eq => 
	 let Next := (Pol_mult_cst Q cP) - (Pol_mult_cst P cQ) in
	 let (GCD_Q',Next'):= Pol_gcd_gcd_free_strict Q Next in
	 let (GCD,Q'):= GCD_Q' in
	 let cGCD := Pol_dom GCD in
	 let cQ' := Pol_dom Q' in
	 let cNext' := Pol_dom Next' in
	 let cNext := Pol_dom Next in
	   (GCD,
	     (Pol_mult_cst Q' ((cGCD** cNext'** cP)// cNext)) -
	     (Pol_mult_cst Next' ((cGCD** cQ')// cQ)),
	     Q')
       |Gt  => Pol_gcd_gcd_free_strict P Q
       |Lt  => Pol_gcd_gcd_free_strict Q P
      end
     end.
    

 Definition Pol_square_free(P:Pol) := snd (fst (Pol_gcd_gcd_free P (Pol_deriv P))).




  (* evaluation of a Pol1 at an element of C *)
Definition Pol_eval :=
 fix Pol1_eval(P:Pol)(x:Coef){struct P} : Coef :=
   match P with
     |Pc c =>  c
     |PX A i a => ((Pol1_eval A x)** (cpow x (Npos i))) ++ a
   end.





(*operators for polys with more than 2 variables *)
 (* cis_base_cst the operator at the coef level  *)

(* is base cst at level n+1 *)
 Definition  Pol_is_base_cst(P:Pol):=
 match P with
 |Pc c => cis_base_cst c
 |PX Q i c => false
 end.



Definition Pol_trunc(P:Pol) :=
let f:=
  fix Poln_trunc(P:Pol)(tlist:list Pol)(clist:list Coef){struct P}:(list Pol)*(list Coef) :=
    match P with
    |Pc c =>
    if (cis_base_cst c) then ((P :: tlist), clist) else ((P :: (Pc c0) :: tlist), c::clist)
    |PX Q i c => let (tres,cres):= Poln_trunc Q tlist clist in
	(map (fun x => (mkPX  x i c)) tres, cres)
    end in
f P nil nil.


 Definition  Pol_mkPc(c:Rat):= Pc (cmkPc c).



Definition Poln_op_base_cst (Op:Coef->Rat->Coef):=
  fix Poln_op_base_cst(P:Pol)(c:Rat){struct P}:Pol:=
    match P with
    |Pc p => Pc (Op p c)
    |PX Q i q => mkPX (Poln_op_base_cst Q c) i (Op q c)
    end.

Definition Pol_mult_base_cst := Poln_op_base_cst cmult_base_cst.
Definition Pol_div_base_cst :=Poln_op_base_cst cdiv_base_cst.

Definition Pol_partial_eval :=
    fix partial_eval(P:Pol)(c:Rat){struct P}:Coef:=
    match P with
    |Pc p => p
    |PX Q i q =>
    (cmult_base_cst (partial_eval Q c) (rpow c (Npos i)))++q
    end.


(* Operations over Bernstein Coefficients *)


    Definition X := PX (Pc c1) xH c0.
      
     
      (*first some transformations over polynomials*)
     
    (*P(X+c), on pourrait s'embeter plus quand meme*)
  (*bug   Definition Ptranslate:=fix Ptranslate(P:Pol)(c: Rat){struct P}:Pol:=
       match P with
	 |Pc p => P
	 |PX P' i p' => 
	   let Q := Ptranslate P' c in 
	     (Pol_pow (Q*((X + (Pol_mkPc c))))  (Npos i)) + (Pc p')
       end.*)
     
  Definition Ptranslate:=fix Ptranslate(P:Pol)(c: Rat){struct P}:Pol:=
       match P with
	 |Pc p => P
	 |PX P' i p' => 
	   let Q := Ptranslate P' c in 
	     (Q * (Pol_pow (X + (Pol_mkPc c))  (Npos i))) + (Pc p')
       end.
     
      (*P(cX)*)
     Definition dilat := 
	fix dilat(P:Pol)(c:Rat){struct P}:Pol:=
       match P with
	 |Pc _ => P
	 |PX P' i p => PX (Pol_mult_base_cst  (dilat P' c) (rpow c (Npos i))) i p
       end.
     
       (* X^d * P(1/X) where deg(P)=d, ie "reverse" of the polynomial *) 
     Definition Rev1:= fix Rev1 (Q P:Pol)(i:positive){struct P}:Pol:=
       match P with
	 |Pc c => mkPX Q i c
	 |PX P' j p => Rev1 (mkPX Q i p) P' j
       end.
     
     Definition Rev(P:Pol):=
       match P with
	 |Pc c => Pc c
	 |PX P' i p' => Rev1 (Pc p') P' i 
       end.
     
     
     
       (*adds i times the rational r in head of the Rat list l*)
     Definition repeat_add:= fix repeat_add(r:Coef)(i:positive)(l:list Coef){struct i}:
       list Coef :=
       match i with
	 |xH => r::l
	 |xO p => repeat_add r p (repeat_add r p l)
	 |xI p => r::(repeat_add r p (repeat_add r p l))
       end.
     

     (*list of coef of a Poly of degree <= p, over 1, X,..., X^p, with
    all zeros, constant in head, *)

     Definition Pol_to_list_dense:= fix Pol_to_list_dense(P:Pol)(p:N){struct P}:list Coef:=
       match P with
	 |Pc c =>
	   match p with
	     |N0 => c::nil
	     |Npos p' => c::(repeat_add c0 p' nil)
	   end
	 |PX Q i q =>
	   match i with
	     |xH => q::(Pol_to_list_dense Q (Npred p))
	     |_ => q :: (repeat_add c0 (Ppred i) (Pol_to_list_dense Q
	       (Nminus p (Npos i))))
	   end
       end.
     

    (*divides by the proper binomial coefs to get the bern coefs*)
     Definition binomial_div:=
	 fix binomial_div (l:list Coef)(p:N)(i:N){struct l}:
       list Coef:=
       match l with
	 |nil => nil
	 |h::t => 
	   (cdiv_base_cst h (rbinomial p i))::
	   (binomial_div t p (Npred i))
       end.
     

(*  coefs of P in the Bernstein basis over c,d,p form b_p to b_0 if 
    p is the degree of P *)
     Definition Pol_bern_coefs(P:Pol)(c d:Rat)(p:N):list Coef :=
  	 let Q := (Ptranslate (Rev (dilat (Ptranslate P c) (rsub d  c)))  r1) in
	   let list_coef := Pol_to_list_dense Q p in
	     binomial_div list_coef p p.
    


     
    (*input : list of bernstein coefs for P of deg <= p in the bern basis
      p over c,d. and a rational e
    
    output : list of bernstein coefs for P of deg <= p in the bern basis
    p over c,e 
    and
    list of bernstein coefs for P of deg <= p in the bern basis
    p over e,d
    *)

      (* computation of the next diag in the "Pascal triangle" of the
	Bernstein relation *)
       	Definition next_diag_bern(c d e:Rat):=
     	let alpha := rdiv (rsub d e) (rsub d c) in
        let beta := rdiv (rsub e c) (rsub d c) in
       fix next_diag_bern(diag:list Coef)(b:Coef){struct diag}:
	 list Coef:=
	 match diag with
	   |nil => b::nil
	   |hd :: tl => 
	     let l:=next_diag_bern tl b in
	       match l with
		 |nil => nil (*should never happen*)
		 |rhd::rtl =>
		   ((hd **  (cmkPc alpha))
		     ++ (rhd ** (cmkPc beta)))
		   ::l
	       end
	 end.

      (* computation of the new coef, given the previous from b0 to bp
      WARNING, b'' is in reverse order*)
  Definition bern_split1(c d e:Rat):=
       fix bern_split1(bern_coef b' b'':list Coef){struct bern_coef}
	 :(list Coef)*(list Coef):=
	 match bern_coef with
	   |nil  => (b',b'')
	   |hd::tl => 
	     let next_b'':= next_diag_bern c d e b'' hd in
	       match next_b'' with
		 |nil => (nil,nil) (*should never happen*)
		 |hd''::tl'' => bern_split1 tl (hd''::b') next_b''
	       end
	 end.


     Definition Pol_bern_split(bern_coef:list Coef)(c d e:Rat):=
       let (b',b''):= bern_split1 c d e (rev bern_coef) nil nil in 
	 (b', rev b'').



(*   Inductive isol_box:Set:=
     	|Singl : cell_point -> Rat -> isol_box
     	|Pair : cell_point -> (Rat*Rat)->Pol -> Pol -> 
	list (four_uple Coef Coef N Sign)-> isol_box
        |Minf : cell_point -> isol_box. *)

(*Cert contains all the information to keep for further computations *)
Inductive isol_box:Set:=
     	|Singl : cell_point -> Rat -> isol_box
     	|Pair : cell_point -> (Rat*Rat)->Pol->Pol->list cCert-> isol_box
        |Minf : cell_point -> Rat -> isol_box. 


(*
Definition isol_box := mk_isol_box Rat cCert Pol cell_point.
Definition cell_point_up := mk_cell_point_up Rat cell_point isol_box.
*)


Definition print_isol(i:isol_box):list display_cell:=
  match i with
  |Singl z _ => Rt :: cprint_cell z
  |Pair z _ _ _ _ => Rt :: cprint_cell z
  |Minf z _ => Be :: cprint_cell z
end.


  Inductive cell_point_up:Set:=
       |Between : cell_point -> Rat -> cell_point_up
       |Root : isol_box -> cell_point_up.



Definition print_cell(z:cell_point_up):list display_cell:=
  match z with
  |Between z _ => Be :: (cprint_cell z)
  |Root i => (print_isol i)
 end.




Definition cell_point_up_proj (c:cell_point_up):=
match  c with
|Between z _ => z
|Root r =>
	match r with
	|Singl z _ => z
	|Pair z _  _ _ _ => z
	|Minf z _ => z
	end
end.

  Definition Cert := four_uple Pol Pol N Sign.
  Definition mk_Cert(P Q:Pol)(n:N)(s:Sign):= Four  P Q n s. 
(* we keep the degree of Pbar because the possible computations of bern coefs will work with Pbar*)
 Definition build_Cert(P:Pol)(s:Sign):Cert :=
  let Pbar := Pol_square_free P in
  Four P Pbar (Pol_deg Pbar) s.


Definition Cert_fst(c:Cert):= four_fst c.





(* Very naive interval arithmetic for bound computations *)

(* [a,b]+[c,d], a<=b and c<=d *)
Definition radd_int(a b c d:Rat):=((radd a c), (radd b d)).

(* [a,b]*[c,d], a<=b and c<=d *)
Definition rprod_int(a b c d:Rat):= 
((rmin4 (rprod a c) (rprod a d) (rprod b c) (rprod b d)),
(rmax4 (rprod a c) (rprod a d) (rprod b c) (rprod b d))).

(*[a,b]^i, a<=b*)
Definition rpow_int_pos:=
fix ipow(a b:Rat)(i:positive){struct i}:Rat*Rat:=
          match i with
	|xH => (a,b)
	|xO p => let (c,d) := ipow a b p in rprod_int c d c d
	|xI p =>
	let (c,d) := ipow a b p in
	let (c',d') := (rprod_int c d c d) in
	rprod_int c' d' a b
	end.

Definition rpow_int(a b:Rat)(n:N):=
 match n with
  |N0 => (r1,r1)
  |Npos p =>rpow_int_pos a b p
end.


Definition rdiv_int(a b c d:Rat):=
(rmin4 (rdiv a c) (rdiv a b) (rdiv b c)  (rdiv b d),
rmax4 (rdiv a c) (rdiv a b) (rdiv b c)  (rdiv b d)).


Definition Pol_value_bound (z:cell_point_up)(P:Pol):=
match z with
|Between z' b =>cvalue_bound z' (Pol_partial_eval P b)
|Root u =>
    match u with
    |Singl z' r => cvalue_bound z' (Pol_partial_eval P r) 
    |Minf z' m => cvalue_bound z' (Pol_partial_eval P m)
    |Pair z' (a,b) _ _ _ =>
let g:= fix Pol_eval_int(P:Pol):(Rat*Rat):=
match P with
    |Pc c => (*let x:= cvalue_bound z' c in x*) cvalue_bound z' c
    |PX P i p =>    
    let (c,d):= Pol_eval_int P in
    let (e,f):= rpow_int a b (Npos i) in
    let (g,h):= rprod_int c d e f in
    let (k,l):= cvalue_bound z' p in
   radd_int g h k l 
   end in
g P
end
end.



(* to add the sign of a pol to a list of signs at a tagged root*) 
 Definition add_cst_sign(l:list (isol_box*(list (Pol*Sign))))(P:Pol)(sign:Sign):=
   let add_sign := fun w => (fst w, (P,sign)::(snd w)) in
     map add_sign l.

(* to add the sign of a pol at the end of a list of signs *)
 Definition add_to_cst_list(l:list (isol_box*(list (Pol*Sign))))(sign :list (Pol*Sign)):=
   let add_list := fun w => (fst w,  (snd w) @ sign) in
     map add_list l.







Inductive Pol_info : Set :=
|Cst_sign : Pol -> Sign -> Pol_info
|Non_cst_sign : four_uple Pol Pol N Sign -> Pol_info.

Definition Pol_of_info_Pol(u:Pol_info):=
match u with
|Cst_sign P _ => P
|Non_cst_sign  f => four_fst f
end.

Definition Pol_base_cst_sign(P:Pol):=
match P with
|Pc c => cbase_cst_sign c
|PX _ _ _ =>None
end.






(*
  Definition cert_refine(z:cell_point)(P Pbar:Pol)(a b:Coef)(c:Cert)(n:nat):=
     let mid := rdiv (radd a b) (2#1) in
     let Pmid := Pol_partial_eval P mid in
     let Pbarmid := Pol_partial_eval Pbar mid in
	match csign_at Pmid Pbarmid (cdeg Pbarmid) (Some Eq) z  n with (*Some Eq is dummy*)
	|None => None 
	|Some Eq => Singl z mid
	|Some _ =>
           let (b',b''):=Pol_bern_split_tag a b mid c z in
	   let Vb' := op_sign_changes (map (fun x => (csign_at x z))) b' in
	   match Vb' with
	|None => None
	|Some 1 => Pair z (a,mid) P Pbar b'
	|_ => Pair z (mid b) P Pbar b''
	end
	end.

Definition cell_point_up_refine(z:cell_point_up) :=
   match z with
   |Root ibox =>
	match ibox with
	 |Singl z' r => Singl (ccell_point_up_refine z') r
	 |Pair z' (a,b) P Pbar c => let z'':= ccell_point_up_refine z') in cert_refine z'' a b P Pbar c
	 |Minf z' m => Minf (ccell_refine z' m)
   |Between z' b => z
  end.


*)

	
