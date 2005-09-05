(*Require Import Utils.
Set Implicit Arguments.*)



 Notation  "x # y" := (MkRat x y)(at level 20, no associativity).

 Notation "x ++ y" := (cadd x y) (at level 50, left associativity).
 Notation "x ** y":= (cmul x y) (at level 40, left associativity).
 Notation "-- x" := (copp x) (at level 35, right associativity).
 Notation "x -- y" := (csub x y) (at level 50, left associativity).
 Notation "x // y" := (cdiv x y) (at level 40, left associativity).




  (************************************************************)
  (****             Type definitions                       ****)
  (************************************************************)



 Definition Alg := mkAlg Rat Coef cInfo.
 Definition Rpoint := mkRpoint Rat Coef cInfo.
 Definition cell_point_up := mkcell_point_up Rat Coef cInfo cell_point.


 (************************************************************)
 (**              Polynomials with one  variable            **)
 (************************************************************)


Definition Pol := Pol1 Coef.

Definition P0 := Pc  c0.
Definition P1 := Pc c1.
Definition X := PX (Pc c1) xH c0.
 
Definition mkPX P i c := 
  match P with
  | Pc p => if (czero_test p) then Pc c else PX P i c
  | PX P' i' c' => if (czero_test c') then PX P' (i' + i) c else PX P i c
  end.


 (*************************************************************)
 (**       Integral domain operations  over polynomials      **)  
 (*All the following defined operations preserve normalisation*)
 (*************************************************************)



(** Opposite **)
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
 Definition Pol_mul_Rat_aux :=
   fix Pol_mul_Rat_aux (P:Pol) (c:Coef) {struct P} : Pol :=
     match P with
       | Pc c' => Pc (c' ** c)
       | PX P i c' => mkPX (Pol_mul_Rat_aux P c) i (c'** c)
     end.

(*hack to speed up*)
 Definition Pol_mul_Rat P c :=
  if (czero_test c) then P0 else
  if (czero_test (c -- c1)) then P else Pol_mul_Rat_aux P c.

 
 Definition Pol_mul := fix Pol_mul(P P':Pol) {struct P'} : Pol :=
  match P' with
  | Pc c' => Pol_mul_Rat P c'
  | PX P' i' c' => 
     (mkPX (Pol_mul P P') i' c0) + (Pol_mul_Rat P c')
  end.

 Notation "P * P'" := (Pol_mul P P').


 (** Zero test for pols in normal form **)
 Definition Pol_zero_test(P:Pol):bool:=
   match P with
     |Pc c => (czero_test c)
     |PX _ _ _=> false
   end.

 (** Builds a Pol from a Rat *)
 Definition Pol_of_Rat(r:Rat) := Pc (cof_Rat r). 

 (** Builds a constant pol from a positive **)
 Definition Pol_of_pos(p:positive):Pol:= Pc (cof_Rat (rof_pos p)).


 (** Cst pol from a rational **)
 Definition  Pol_mkPc(c:Rat):= Pc (cof_Rat c).

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


(*   
  (*couple degree * coefdom for a polynomial in normal form *)
 Definition Pol_deg_coefdom:= 
   fix Pol_deg_coefdom(A:Pol) : N*Coef :=
     match A with
       |Pc a => (N0,a)
       |PX P i p => let (d,c) := (Pol_deg_coefdom P) in (Nplus (Npos i) d, c)
     end.

 (** degree only **)
 Definition Pol_deg :=
   fix Pol_deg(P:Pol):N:=
     match P with 
       |Pc _ => N0
       |PX P i _ => let d := Pol_deg P in (Nplus (Npos i) d)
     end.

 (** leading coef only **)
 Definition Pol_dom :=
   fix Pol_dom(P:Pol):Coef:=
     match P with
       |Pc p => p
       |PX P _ _ => Pol_dom P
     end.
*)



 (** Derivative **)
 Definition Pol_deriv := 
   fix Pol1_deriv(P:Pol):Pol :=
     match P with
       |Pc c => Pc c0
       |PX A i a => 
	 match i with
	   |xH => A +(mkPX (Pol1_deriv A) xH c0)
	   |_ => (Pol_mul_Rat (PX A (Ppred i) c0) (cof_pos i)) +
	     (mkPX (Pol1_deriv A) i c0)
	 end
     end.
   


  (** division:like an euclidian division, but if the division over coef
  fails, returns 0*)
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
	       | xH => (Pc (cr // cd), (mkPX R xH c0) - (Pol_mul_Rat D (cr//cd)))
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
        		         let rem := (mkPX R2 xH c0) - (Pol_mul_Rat D (cr2//cd)) in
				   (quo,rem)
			     end
	     end
       	 end.
 		


  (** division of polynomials with coef in Coef:
  - as usual arguments are supposed to be normalized
  - div_euclide A B = (Q,R) with  A = BQ ++ and 
	--either deg(R)< deg(B)
	-- or deg(R)=deg(B)=0 and R != P R0
	-- Q and R are normalized
  ## non trivial case :
  if AX^i +a is to be divided by B, with  A = PQ1 + c1 and deg(c1)<deg(B)
  then AX+a=(BQ1)X^i + c1X^i +a and :
    - either deg (c1X^i +a) < deg (B),it ok : Q = X^i*Q1 and R = c1X^i + a
    - or deg (c1X^i +a) >= deg (B) and  Q = (X^i*Q1+Q2) et R = R2 + a
  where (Q2, R2) = div_aux B db cb c1 i i.e. c1X^i = Q2B ++2
  ## poly returned are normalized as soon as args are normalized
  **)
 
 (** First division by a non constant polynomial **)

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




 (** General division function **)
 Definition Pol_euclide_div(A B:Pol):Pol*Pol :=
   match B with
     |Pc q => (Pol_div_cst A q, Pc c0) 
     |_ => (Pol_euclide_div_PX B A)
   end.

 (** Only the quotient **)
 Definition Pol_div(A B:Pol):Pol:= fst (Pol_euclide_div A B).


  (************************************************************)
  (***          Subresultant polynomials                     **)
  (************************************************************)

  (** Notations are the ones of BPR **)

  (** q to the n*(n+1)/2 **)
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


  (** kth subresultant coefficient **)
 Definition Pol_subres_aux (j k:N)(q q':Coef): Coef:=
   let t := (Npred (Nminus j k)) in
     (sum_pow (-- c1) t)**(cpow (q // q') t)** q.
 
 
  (*next polynomial in the sequence,after ASRi_1 and SRj_1 and arguments
      for the possible next step of computations. if is nul, then B was
      the last poly of the sequence. SRj_1 is not zero*)
 
 Definition Pol_next_subres(SRi_1 SRj_1:Pol)(srj:Coef)(i j:N):
   (uple4 Pol Coef N N) :=
   let (k, dom_srj_1) := (Pol_deg_coefdom SRj_1) in
   let (d, dom_sri_1) := (Pol_deg_coefdom SRi_1) in
   let next_SR := fun x:Coef =>
     -(Pol_div_cst 
       (snd (Pol_euclide_div (Pol_mul_Rat SRi_1 x) SRj_1))
       (srj **  dom_sri_1)) in
     match (Ncompare k  (Npred j)) with
       |Eq => 
	 let srj_1 := dom_srj_1 in
	   (Four (next_SR (cpow dom_srj_1 2)) dom_srj_1 j k)
       |_ => 
	 let srk := (Pol_subres_aux j k dom_srj_1 srj) in
	   (Four (next_SR (dom_srj_1 **  srk)) srk j k)
     end.

  (** next triple (S, U, V) in the rec relation for subresultants **)
 Definition Pol_next_subres_triple(Ti_1 Tj_1:(triple Pol Pol Pol))(srj:Coef)(i j:N):
   uple6 Pol Pol Pol Coef N N :=
   let (SRi_1,Ui_1,Vi_1) := Ti_1 in
   let (SRj_1,Uj_1, Vj_1) := Tj_1 in
   let (k, dom_srj_1) := (Pol_deg_coefdom SRj_1) in
   let (d, dom_sri_1) := (Pol_deg_coefdom SRi_1) in
   let next :=
     (fun x => 
       let (C,R) := (Pol_euclide_div (Pol_mul_Rat SRi_1 x) SRj_1) in
       (C, Pol_div_cst R ((-- srj)** dom_sri_1)) ) in
   let next_UV :=
     (fun (x:Coef)(Pi_1 Pj_1 C:Pol) =>
       (Pol_div_cst
	 ((C * Pj_1) - (Pol_mul_Rat Pi_1 x)) (srj** dom_sri_1))) in
     match (Ncompare k  (Npred j)) with
       |Eq => 
	 let y:= (cpow dom_srj_1 2) in
	 let (C,SR) := next y in
	   (Six
	     SR (next_UV y Ui_1 Uj_1 C) (next_UV y Vi_1 Vj_1 C) dom_srj_1 j k)
       |_ => 
	 let srk := (Pol_subres_aux j k dom_srj_1 srj) in
	 let y:= (dom_srj_1 **  srk) in
	 let (C,SR) := next y in
	   (Six
	     SR (next_UV y Ui_1 Uj_1 C) (next_UV y Vi_1 Vj_1 C) srk j k)
     end.


   (**Subres pol list, from A B, n ensures termination and will be deg P + 1**)

 Definition Pol_subres_list1:=
   fix Pol1_subres_list1(A B:Pol)(q:Coef)(i j:N)(m:nat){struct m}:list Pol :=
     match m with
       |O => nil
       |S n => 
	 let (SR,sr,k,l) := (Pol_next_subres A B q i j) in
	   if (Pol_zero_test SR) then nil
	     else   SR :: (Pol1_subres_list1 B SR sr k l n)
     end.

 Definition Pol_subres_list(A B:Pol) := 
   let p := Pol_deg A in
   let q := Pol_deg B in
   A :: B :: (Pol_subres_list1 A B c1 (p+1) p  (S (nat_of_N p))). 


 Definition Pol_subres_coef_list(A B:Pol):=
   let dom := (fun x => Pol_dom x) in (* for impl args*)
   let res := Pol_subres_list A B in
     map dom res.

  (** Extented subresultants **)
 Definition Pol_ext_signed_subres_list :=
  fix Pol1_ext_signed_subres_list(T T':(triple Pol Pol Pol))(q:Coef)(i j:N)(m:nat)
    {struct m}:list (triple Pol Pol Pol) :=
    let (B,_,_):= T' in
      if (Pol_zero_test B) then nil
	else
	 match m with
	   |O => nil
	   |S n => 
	     let (next_SR,next_U,next_V,sr,k,l) := (Pol_next_subres_triple T T' q i j) in
	     let next_T := Tr next_SR next_U next_V in
     	       next_T :: (Pol1_ext_signed_subres_list T' next_T sr k l n)
	 end.

 
  (** extended signed subres chain *)
   Definition Pol_ext_signed_subres_chain(P Q:Pol) :=
	let (deg_p, dom_p) := Pol_deg_coefdom P in
   	let (deg_q, dom_q) := Pol_deg_coefdom Q in
	let Tp := Tr P P1 P0 in
	let Tq := Tr Q P0 P1 in
     	  Tp :: (Tq :: 	
    	    (Pol_ext_signed_subres_list
      	      Tp Tq  c1 deg_p (Npred deg_p) (S (nat_of_N deg_p)))).
     
       



   (** Gcd of P and Q : last subresultant dP>dQ **)

   (** For polys with different degrees **)
   Definition Pol_gcd_strict (P Q:Pol) :=
     let l := (Pol_subres_list P Q) in 
     let SRj := (last_elem l Q) in
     let srj := Pol_dom SRj in
     let cP := Pol_dom P in
       Pol_div_cst (Pol_mul_Rat SRj cP) srj.
    

   Definition Pol_gcd(P Q:Pol) :=
     let (dP, cP):= Pol_deg_coefdom P in
     let (dQ,cQ) := Pol_deg_coefdom Q in
       match Ncompare dP dQ with
	 |Lt  => Pol_gcd_strict Q P
	 |Gt  => Pol_gcd_strict P Q
	 |Eq => Pol_gcd_strict P ((Pol_mul_Rat Q cP) - (Pol_mul_Rat P cQ))
       end.

   (** Triple gcd of P and Q, P/gcd, Q/gcd **) 

   (** For polys with different degrees **)
   Definition Pol_gcd_gcd_free_strict (P Q:Pol) :=
     let cP := Pol_dom P in
     let (Tj, Tj_1):= two_last_elems (Pol_ext_signed_subres_chain P Q) 
       ((Tr (Pc c0) (Pc c0) (Pc c0)),(Tr (Pc c0) (Pc c0) (Pc c0))) in
     let (SRj,_,_) := Tj in
     let srj := Pol_dom SRj in
     let (_,Uj_1,Vj_1) := Tj_1 in
     let cVj_1 := Pol_dom Vj_1 in
     let cUj_1 := Pol_dom Uj_1 in
       (Pol_div_cst (Pol_mul_Rat SRj cP) srj,
         Pol_div_cst (Pol_mul_Rat Vj_1 cP) cVj_1,
	 Pol_div_cst (Pol_mul_Rat Uj_1 cP) cUj_1).


  (*TODO virer les contenus constants?*)


   Definition Pol_gcd_gcd_free (P Q:Pol) :=
     match P, Q with
       |Pc p, Pc q => 
	 let (a,b) := cgcd_gcd_free p q in (Pc (snd a), Pc (snd a), Pc b)
       |_,_ => 
	 let (dQ,cQ):= Pol_deg_coefdom Q in
	 let (dP,cP):= Pol_deg_coefdom P in
	   match (Ncompare dP dQ) with
	     |Eq => 
	       let Next := (Pol_mul_Rat Q cP) - (Pol_mul_Rat P cQ) in
	       let (GCD_Q',Next'):= Pol_gcd_gcd_free_strict Q Next in
	       let (GCD,Q'):= GCD_Q' in
	       let cGCD := Pol_dom GCD in
	       let cQ' := Pol_dom Q' in
	       let cNext' := Pol_dom Next' in
	       let cNext := Pol_dom Next in
		 (GCD,
		   (Pol_mul_Rat Q' ((cGCD** cNext'** cP)// cNext)) -
		   (Pol_mul_Rat Next' ((cGCD** cQ')// cQ)),
		   Q')
	     |Gt  => Pol_gcd_gcd_free_strict P Q
	     |Lt  => Pol_gcd_gcd_free_strict Q P
	   end
     end.
    

   (** Square free part of a poly **)
 Definition Pol_square_free(P:Pol) := snd (fst (Pol_gcd_gcd_free P (Pol_deriv P))).


  (************************************************************)
  (***      Misc.                                            **)
  (************************************************************)


 (** Truncations of P:truncates if the leading coef is not a base cst **)
 Definition Pol_trunc(P:Pol) :=
   let f:=
     fix Poln_trunc(P:Pol)(tlist:list Pol)(clist:list Coef){struct P}:(list Pol)*(list Coef) :=
       match P with
	 |Pc c =>
	   if (cis_Rat c) then ((P :: tlist), clist) else ((P :: (Pc c0) :: tlist), c::clist)
	 |PX Q i c => let (tres,cres):= Poln_trunc Q tlist clist in
	   (map (fun x => (mkPX  x i c)) tres, cres)
       end in
       f P nil nil.


  (** evaluation of a Pol1 at an element of the Coef set *)
 Definition Pol_eval :=
   fix Pol1_eval(P:Pol)(x:Coef){struct P} : Coef :=
     match P with
       |Pc c =>  c
       |PX A i a => ((Pol1_eval A x)** (cpow x (Npos i))) ++ a
     end.




  (** Tests if P is a base cst **)
 Definition  Pol_is_base_cst(P:Pol):=
   match P with
     |Pc c => cis_Rat c
     |PX Q i c => false
   end.


  (** Prod and div by a rational, maps the rat operation over base coefs *)
 Definition Poln_op_base_cst (Op:Coef->Rat->Coef):=
   fix Poln_op_base_cst(P:Pol)(c:Rat){struct P}:Pol:=
     match P with
       |Pc p => Pc (Op p c)
       |PX Q i q => mkPX (Poln_op_base_cst Q c) i (Op q c)
     end.




 Definition Pol_mult_base_cst := Poln_op_base_cst cmult_base_cst.
 Definition Pol_div_base_cst :=Poln_op_base_cst cdiv_base_cst.


  (** Eval of a pol at a rational, returns a coef *)
 Definition Pol_partial_eval :=
   fix partial_eval(P:Pol)(c:Rat){struct P}:Coef:=
     match P with
       |Pc p => p
       |PX Q i q =>
	 (cmult_base_cst (partial_eval Q c) (rpow c (Npos i)))++q
     end.






 (************************************************************)
 (* Informations about a Pol to be computed once and for all *)
 (************************************************************)


 (* Info is P Pbar dPbarlowsign signinfo
  where Pbar is the square free part of P,
  dPbar is the degree of Pbar (for later bern computations)
  lowsign the sign of P in -inf
  signinfo is the sign of P if it is known to be constant,
  and None else *)

 (* Definition Info := uple5 Pol Pol N Sign Sign.*)
 Definition Info := build_Info Coef.

  Definition mk_Info(P Q:Pol)(n:N)(low sign_info:Sign):= 
    Five  P Q n low sign_info. 

  Definition Pol_of_Info(c:Info):= fst5 c.


 (************************************************************)
 (***            Bernstein toolkit for root isolation       **)
 (************************************************************)




 (** Auxiliary  functions **)    
     
 Definition Ptranslate:=
   fix Ptranslate(P:Pol)(c: Rat){struct P}:Pol:=
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
     

 (**divides list of coefs by the relevant binomial coefs to get the bern list*)
 Definition binomial_div:=
   fix binomial_div (l:list Coef)(p:N)(i:N){struct l}:
     list Coef:=
     match l with
       |nil => nil
       |h::t => 
	 (cdiv_base_cst h (rbinomial p i))::
	 (binomial_div t p (Npred i))
     end.
     

  (*  coefs of P in the Bernstein basis over c,d,p from b_p to b_0 if 
	p is the degree of P 
  builds the list of info pol, no infomation about constant sign is assumed *)
 Definition Pol_bern_coefs(P:Pol)(c d:Rat)(p:N):=
   let Q := (Ptranslate (Rev (dilat (Ptranslate P c) (rsub d  c)))  r1) in
     let list_coef := Pol_to_list_dense Q p in
       map (cInfo_of_Pol None) (binomial_div list_coef p p).
    


 (* bern coefs after split of the interval    
   input : list of bernstein coefs for P of deg <= p in the bern basis
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
		 ((hd **  (cof_Rat alpha))
		   ++ (rhd ** (cof_Rat beta)))
		 ::l
	     end
       end.


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

 (** computes the list of cPol_info for the bern coefs **)
 Definition Pol_bern_split(bern_coef_info:list cInfo)(c d e:Rat):=
   let bern_coef := map cPol_of_Info bern_coef_info in
   let (b',b''):= bern_split1 c d e (rev bern_coef) nil nil in 
     (map (cInfo_of_Pol None) b', map (cInfo_of_Pol None) (rev b'')).



 (************************************************************)
 (*** Representation of algebraic points in n dimensions    **)
 (************************************************************)

(*
 (** encoding of algebraic numbers at this level, 
  a b P Pbar (list bernstein coefs of P over [a b]).
  Pbar is the square free part of P.
  for each bern coef, we keep the polinfo because we will later
  have to compute signs of these coefs *)
 Definition Alg := uple5 Rat Rat Pol Pol (list cInfo).


 (** element of R at this level **)
 Definition Rpoint := mk_Rpoint Rat Alg.


 (** cell of the cad built at this level **)
 Definition cell_point_up := (cell_point * Rpoint)%type.

 Definition cell_point_up_proj (c:cell_point_up):= fst c.
 


 Definition Cad_col:=(cell_point_up*(list (Pol*Sign)))%type.

 Definition cell_point_of_Cad_col(c:Cad_col):= fst c.
 Definition sign_col_of_Cad_col(c:Cad_col):= snd c.
*)

 (************************************************************)
 (******         Misc. for sign_tables handling        *******)
 (************************************************************)

(* to add the sign of a pol to a list of signs at a tagged root*)
 Definition add_cst_sign
   (l:list (Rpoint*(list (Pol*Sign))))(P:Pol)(sign:Sign):=
   let add_sign := fun w => (fst w, (P,sign)::(snd w)) in
     map add_sign l.

(* to add the sign of a pol at the end of a list of signs *)
 Definition add_to_cst_list
   (l:list (Rpoint*(list (Pol*Sign))))(sign :list (Pol*Sign)):=
   let add_list := fun w => (fst w,  (snd w) @ sign) in
     map add_list l.




  (************************************************************)
  (***      Bounds on the value of P at a cell_point_up      **)
  (**************************g**********************************)

  Definition Pol_value_bound (z:cell_point_up)(P:Pol):=
    let (z',r):=z in
      match r with
	|Minf m => cvalue_bound z' (Pol_partial_eval P m)
	|Between b => cvalue_bound z' (Pol_partial_eval P b)
	|Root r => cvalue_bound z' (Pol_partial_eval P r)
	|Alg_root alg =>
	  let (a,b,_,_,_):= alg in
	  let g:= fix Pol_eval_int(P:Pol):(Rat*Rat):=
	    match P with
	      |Pc c => cvalue_bound z' c
	      |PX P i p =>
		let (c,d):= Pol_eval_int P in
		let (e,f):= rpow_int a b (Npos i) in
	        let (g,h):= rprod_int c d e f in
		let (k,l):= cvalue_bound z' p in
		  radd_int g h k l 
	    end in
	    g P
      end.



  (************************************************************)
  (***        Refinement of algebraic numbers encodings     ***)
  (************************************************************)


 Definition alg_refine(z:cell_point)(alg:Alg)(n:nat):=
   let (a, b, P, Pbar, blist):= alg in
   let mid := rdiv (radd a b) (2#1) in
   let Pmid := Pol_partial_eval P mid in
   let Pbarmid := Pol_partial_eval Pbar mid in  
     match 
       (snd (snd 
	 (csign_at (cmk_Info Pmid Pbarmid (cdeg Pbarmid) None None) z n)))
       with
       |None => None
       |Some Eq => Some (z,(Root Coef cInfo mid))
       |Some _ =>
	 let (b',b''):= Pol_bern_split blist a b mid in
	 let Vb' := 
	   op_sign_changes 
	   (map (fun x => snd (snd (csign_at x z n))) b') in
	   match Vb' with
	     |None => None
	     |Some 1 => Some (z, (Alg_root (Five a mid P Pbar b')))
	     |Some _ => Some (z, (Alg_root (Five a mid P Pbar b'')))
	   end
     end.


 (** keeps only the relevant half of each int in every algebraic coordinate **)
 Definition cell_refine(z:cell_point_up)(n:nat) :=
   let (z',r):= z in
     let z':= ccell_refine z' n in
       match z' with
	 |None => None
	 |Some z' =>
	   match r with
	     |Minf m => Some (z', Minf Coef cInfo m)
	     |Between b => Some (z', Between Coef cInfo b)
	     |Root r => Some (z', Root Coef cInfo r)
	     |Alg_root alg => alg_refine z' alg n
	   end
   end.


	
