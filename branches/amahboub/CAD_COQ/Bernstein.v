Require Import Qabs.
Require Export ZArith.
Require Export Mylist.
Require Export Pol1sparse_is_ring.
Require Export Utils.

 Definition Npred(n :N):N :=
   match n with
     |N0 => N0
     |Npos p => match p with
		  |xH => N0
		  |_ => Npos (Ppred p)
		end
   end.


 Definition Nminus(n m:N):N :=
   match n, m with
     |N0, _ => N0
     |_, N0 => n
     |Npos p, Npos q =>  match Pminus_mask p q with
			   |IsNeg => N0
			   |IsNul => N0
			   |IsPos p => Npos p
			 end
     end.

 Definition nat_of_N(n:N):nat:=
   match n with
     N0 => O
     |Npos p => nat_of_P p
   end.


 Module POLY(QOPS:RAT_OPS).
   Import QOPS.
   Module QPROP := RAT_PROP QOPS.
   Import QPROP.
(*coefficient structure for the previous parametric set of rationnal numbers *)
   
   Definition Rat_coef_set :=
     mk_cset Rat R0 R1 RatEq Rat_add Rat_prod Rat_sub Rat_opp Rat_zero_test.


  (* une fois qu'on aura les preuves 

   Definition Rat_coef_eq :=
     mk_ceq Rat Rat_coef_set RatEq_refl RatEq_sym RatEq_trans
     Rat_add_ext Rat_prod_ext Rat_opp_ext.
     

   Definition Rat_coef_th :=
     mk_ct Rat Rat_coef_set Rat_0_l Rat_add_sym Rat_add_assoc Rat_prod_1_l
     Rat_prod_sym Rat_prod_assoc Rat_distr_l Rat_sub_spec Rat_opp_spec.
 *)

  (*univariate polynomials over Q*)
   

   Definition Poly := Pol1 Rat.
   
   Implicit Arguments PX [C].
   Implicit Arguments Pc [C].
   
   Implicit Arguments Pol1Eq.
   Implicit Arguments Padd.
   Implicit Arguments Pmul.
   Implicit Arguments Psub.
   Implicit Arguments Pop.
   Implicit Arguments Ppow.

   Delimit Scope P_scope with Pol1.
   Bind Scope P_scope with Pol1.

   Open Scope P_scope.

   Notation "x != y" := (Pol1Eq Rat_coef_set x y) : P_scope.
   Notation "x ++ y" := (Padd Rat_coef_set x y) : P_scope.
   Notation "x ** y" := (Pmul Rat_coef_set x y) : P_scope.
   Notation "x -- y" := (Psub Rat_coef_set x y) : P_scope.
   Notation "-- x" := (Pop Rat_coef_set x) : P_scope.
   Notation "x ^ y" :=(Ppow Rat_coef_set x y) :P_scope.

   Definition poly_zero_test := (Pol1_zero_test Rat Rat_coef_set).
   Definition  Rat_mkPX := (mkPX Rat Rat_coef_set).
   
  (* division by a (Rational) constante  *)
   Fixpoint div_cst(A:Poly)(q:Rat){struct A}:Poly:=
     match A with
       |Pc a => Pc (a/q)
       |PX P i p => PX (div_cst P q) i (p/q)
     end.
   
    (* product of a polynomial by a constant *)
   Fixpoint mult_cst(A:Poly)(q:Rat){struct A}:Poly:=
     match A with
       |Pc a => Pc (a*q)
       |PX P i p => Rat_mkPX (mult_cst P q) i (p*q)
     end.



  (*derivative*)
   Fixpoint deriv(P:Poly):Poly :=
     match P with
       |Pc c => Pc R0
       |PX A i a => match i with
		      |xH => A ++ (Rat_mkPX (deriv A) xH R0)
		      |_ => (mult_cst (PX A (Ppred i) R0) (Rat_of_pos i)) ++ 
			(Rat_mkPX (deriv A) i R0)
		    end
     end.

   

  (* evaluation of a Poly at a Rat *)
   Fixpoint eval(P:Poly)(x:Rat){struct P} : Rat :=
     match P with
       |Pc c =>  c
       |PX A i a => ((eval A x)*(Rat_pow x (Npos i)) )+a
     end.
   

  (*couple degree * coefdom for a polynomial in normal form *)
   Fixpoint deg_coefdom(A:Poly) : N*Rat :=
     match A with
       |Pc a => (N0,a)
       |PX P i p => let (d,c) := (deg_coefdom P) in (Nplus (Npos i) d, c)
     end.

   Section euclide_aux.

     Variable D : Poly.
     
     (*degee and leading coef of D*)
     Let dd_cd := deg_coefdom D.
     Let dd := fst dd_cd.
     Let cd := snd dd_cd.
     
  (*auxiliary division of RX^i by D.invariant : 
  -- deg R < deg D
  -- R <> 0
  -- D is not constant *)		
   Fixpoint div_aux(R : Poly)(i:positive){struct i}:Poly*Poly :=
     let (dr,cr) := (deg_coefdom R) in
       match (Ncompare (dr + (Npos i)) dd) with
	 |Lt => (Pc R0, PX R i R0)
	 | _  => 
	   match i with
	   | xH => (Pc (cr/cd), (Rat_mkPX R xH R0) -- (mult_cst D (cr/cd)))
	   | xO p =>
	       let (Q1, R1) := (div_aux R p) in
	       let (dR1, cR1):=(deg_coefdom R1) in
	       if (Rat_zero_test cR1) then (Rat_mkPX Q1 p R0, Pc R0)
	       else
		 let (Q2, R2):=(div_aux R1 p) in 
		 ((Rat_mkPX Q1 p R0) ++ Q2, R2)
	  | xI p =>
	       let (Q1, R1):=(div_aux R p) in
	       let (dR1, cR1):=deg_coefdom R1 in
	       if (Rat_zero_test cR1) then 
		 ((Rat_mkPX Q1 (Psucc p) R0), Pc R0)
	       else
		 let (Q2, R2) := (div_aux R1 p) in
		 let (dr2, cr2) := (deg_coefdom R2) in
		 if (Rat_zero_test cr2) then
		   ((Rat_mkPX Q1 (Psucc p) R0)++(Rat_mkPX Q2 xH R0), Pc R0)
		 else
		   match (Ncompare (Nsucc dr2) dd) with
		   | Lt => 
		     ((Rat_mkPX Q1 (Psucc p) R0)++(Rat_mkPX Q2 xH R0), Rat_mkPX R2 xH R0)
		   | _ =>
		     let quo := (Rat_mkPX Q1 (Psucc p) R0)++ (Rat_mkPX Q2 xH R0)++(Pc (cr2/cd)) in
                     let rem := (Rat_mkPX R2 xH R0) -- (mult_cst D (cr2/cd)) in
		     (quo,rem)
		   end
	   end
       end.
 
 End euclide_aux.

(*straightforward division of polynomials with coef in Rat:
  - as usual arguments are supposed to be normalized
  - div_euclide A B = (Q,R) with  A = BQ +R and 
	--either deg(R)< deg(B)
	-- or deg(R)=deg(B)=0 and R != P R0
	-- Q and R are normalized
  ** non trivial case :
  if AX^i +a is to be divided by B, with  A = PQ1 + R1 and deg(R1)<deg(B)
  then AX+a=(BQ1)X^i + R1X^i +a and :
    - either deg (R1X^i +a) < deg (B),it ok : Q = X^i*Q1 and R = R1X^i + a
    - or deg (R1X^i +a) >= deg (B) and  Q = (X^i*Q1+Q2) et R = R2 + a
  where (Q2, R2) = div_aux B db cb R1 i i.e. R1X^i = Q2B +R2
  ** poly returned are normalized as soon as args are normalized
  *)
 
 (*first division by a non constant polynomial*)
 Section euclide_PX.
   Variable B : Poly.
   Let dcb := deg_coefdom B.
   Let db := fst dcb.
   Let cb := snd dcb.

   (*division of A by the non constant polynomial B*)
   Fixpoint div_euclide_PX (A :Poly):Poly*Poly :=
   match A with
     |Pc a => (Pc R0, Pc a)
     |PX P i p =>
       let (Q1, R1):=div_euclide_PX P in
	 let (dr, r) := deg_coefdom R1 in
	   match (poly_zero_test R1),(Ncompare (Nplus (Npos i) dr) db) with
	     |true, _ => (Rat_mkPX Q1 i R0, Pc p)
	     | _ , Lt => (Rat_mkPX Q1 i R0, Rat_mkPX R1 i p)
	     | _ , _ => let (Q2, R2) := (div_aux B R1 i) in
	       ((Rat_mkPX Q1 i R0)++Q2, R2 ++ Pc p)
	   end
   end.

 End euclide_PX.

 (*general division function *)
 Definition euclide_div(A B:Poly):Poly*Poly :=
   match B with
     |Pc q => (div_cst A q, Pc R0)
     |PX _ _ _ => (div_euclide_PX B A)
   end.

(* principal signed subresulants sequence for P and Q*)
(*ie without zeros and repetitions modulo a constant*)
(* P = a_p X^p + ... + a_0 *)
(* Q = b_q X^q + ... + b_0 with q < p *)
(* cf agorithm 8.73 in MFR *)




  (*q to the n*(n+1)/2 *)
 Definition sum_pow(q:Rat)(n:N):Rat :=
   match n with
     |N0 => R1
     |Npos p => match p with
		  |xH => q
		  |xO p' => Rat_pow q (Npos (Pmult p' (Psucc p)))
		  |xI p' => Rat_pow q (Npos (Pmult (Psucc p') p))
		end
   end.

(*computation of the kth subresultant coefficient*)
 Definition subres_aux (j k:N)(q q':Rat):Rat:=
   let t := (Npred (Nminus j k)) in
     (sum_pow (- R1) t)*(Rat_pow (q/q') t)*q.


  (*next polynomial in the sequence,after ASRi_1 and SRj_1 and arguments
    for the possible next step of computations. if is nul, then B was
    the last poly of the sequence. SRj_1 is no nul*)
 

 Definition next_subres(SRi_1 SRj_1:Poly)(srj:Rat)(i j:N):
   Poly * Rat * N * N :=
   let (k, dom_srj_1) := (deg_coefdom SRj_1) in
   let (d, dom_sri_1) := (deg_coefdom SRi_1) in
     match (Ncompare k  (Npred j)) with
       |Eq => let srj_1 := dom_srj_1 in
	 let rem :=
	   (snd (euclide_div (mult_cst SRi_1 (Rat_pow srj_1 2)) SRj_1)) in
	   (--(div_cst rem (srj * dom_sri_1)) , srj_1, j, k)
       |_ => let srk := (subres_aux j k dom_srj_1 srj) in
	 let rem := 
	   (snd (euclide_div (mult_cst SRi_1 (dom_srj_1 * srk))
	     SRj_1)) in
	   (-- (div_cst rem (srj * dom_sri_1)), srk, j, k)
     end.



    (*builds the list, n ensures termination and will be deg P + 1*)
 Fixpoint signed_subres_list(A B:Poly)(q:Rat)(i j:N)(m:nat){struct m}:list Poly :=
   match m with
     |O => nil
     |S n => if (poly_zero_test B) then nil
       else
	 let (next,l) := (next_subres A B q i j) in
	   let (next',k) := next in
	     let (SR, sr) := next' in
	       SR :: (signed_subres_list B SR sr k l n)
   end.



	 
 Section SUBRES_CHAIN.
   Variable P Q :Poly.
   Let ddp := deg_coefdom P.
   Let ddq := deg_coefdom Q.
   Let deg_p := fst ddp.
   Let deg_q := fst ddq.
   Let dom_p := snd ddp.
   Let dom_q := snd ddq.

  (*first polynomials in the subresultant chain*)
   
   Definition subres_chain_init :=
     match (Rat_sign dom_p) with
       |Z0 => (Pc R0, R0, Pc R0) (*must never occur!*)
       |Zpos _ => (P, R1, Q)
       |Zneg _ => match (Npred (Nminus deg_p deg_q)) with
		    |N0 => (P, R1, Q)
		    |Npos p => match p with
				 |xO _ => (P, (- R1), Q) 
				 |_ => (-- P, R1, (-- Q))
			       end
		  end
     end.
   

   Let SRq := snd subres_chain_init.
   Let SRp := fst (fst subres_chain_init).
   Let srp := snd (fst subres_chain_init).
   
   Definition signed_subres_chain : list Poly :=
     SRp :: (SRq :: 
       (signed_subres_list SRp SRq srp (Nsucc deg_p) deg_p (S (nat_of_N deg_p)))).

 End SUBRES_CHAIN.
 
    (*evaluation of the sign of a list of Poly at a rational point x*)
 Fixpoint sign_eval_map(l:list Poly)(x:Rat){struct l} : list Z := 
  match l with
    |nil => nil
    |P :: l' => (Rat_sign (eval P x)) :: (sign_eval_map l' x)
  end.


  (*number of sign changes in a list of binary integers*)
  (*recursion on list lenght*)
  (*mieux?*)

 Fixpoint sign_changes_rec(l: list Z)(n : nat){struct n} : nat :=
   match n with
     |O => O
     |S n => match l with
	      |nil => O
	      |a :: l' => match a with
			   |Z0 => sign_changes_rec l' n
			   |_ => match l' with
				  |nil => O
				  |b :: l'' => match (a*b)%Z with
						|Z0 => sign_changes_rec (a :: l'') n
						|Zpos _ => sign_changes_rec l' n
						|Zneg _ => S (sign_changes_rec l' n)
					       end
				 end
			  end
	     end
   end.

 Definition sign_changes(l : list Z) : nat := sign_changes_rec l (length l).

  (*sturm theorem : computes
  #{x \in ]a,b[| P(x)=0 & Q(x) > 0} - # {x\in ]a,b[ | P(x)=0 & Q(x)<0}
  using the modified sturm sequence ie the subresultant chain
  of P and P'Q *)
(*precondition : a et b are not roots of P*)
 Definition sturm_query(P Q:Poly)(a b:Rat):nat :=
   let sturm_seq := signed_subres_chain P ((deriv P)**Q) in
   let va := sign_eval_map sturm_seq a in
   let vb := sign_eval_map sturm_seq b in
     ((sign_changes va) - (sign_changes vb))%nat.

 (*gcd of P and Q : last subresultant*)
 Definition gcd(P Q:Poly) :Poly :=
   let l := (signed_subres_chain P Q) in (last_elem l Q).


  (*some transformations over polynomials, useful later fo Bernstein*)


 (* coefficient of X^(i-k) in the expansion of (X+c)^i ie C(i,k) * c^k*)
 Definition monom_trans_coef(k:N)(c:Rat)(i:N):=
     match (Ncompare k i) with
       |Gt => R0
       |_  => (binomial i k)*(Rat_pow c k)
     end.


 Definition trans_X_i_rec(i k:positive)(c:Rat):Poly:=
   Prec Poly (PX (Pc R1) xH (monom_trans_coef 1 c (Npos i)))
   (fun k P => PX P xH (monom_trans_coef (Npos k) c (Npos i))) k.

 (*(X+c)^i*)
 Definition trans_X_i(i:positive)(c:Rat):Poly:=
   trans_X_i_rec i i c.
   


(*P(X+c)*)
 Fixpoint Ptranslate(P:Poly)(c:Rat){struct P}:Poly:=
   match P with
     |Pc p => P
     |PX P' i p' => 
       let Q := Ptranslate P' c in 
	 Q**(trans_X_i i c) ++ (Pc p')
   end.


(*P(cX)*)
 Fixpoint dilat(P:Poly)(c:Rat){struct P}:Poly:=
   match P with
     |Pc _ => P
     |PX P' i p => PX (mult_cst  (dilat P' c) (Rat_pow c (Npos i))) i p
   end.

(*transfoms a pol in Horner form into a list of coef*power, and reverses *)
 Fixpoint Pol_to_list'(l:list (Rat*N))(P:Poly){struct P}:list (Rat*N) :=
   match P with
     |Pc p => (p,N0)::l
     |PX Q i q => Pol_to_list' ((q, Npos i)::l) Q
   end.

 Definition Pol_to_list := Pol_to_list' nil.

  (*builds a pol in Honer form from a list of coef*power*)
 Fixpoint list_to_Pol(l:list (Rat*N)):Poly :=
   match l with
     |nil => Pc R0 (*should never happen!*)
     |h::t => 
       let (coef,deg):= h in
	 match t with
	   |nil => Pc coef
	   |h'::t'=>
	     let (coef',deg'):=h' in
	       match deg' with
		 |N0 => Pc coef (*should never happen*)
		 |Npos d' =>
		   let Q := list_to_Pol t in
		     Rat_mkPX Q d' coef
	       end
	 end
   end.


  (* X^d * P(1/X) where deg(P)=d, ie "reverse" of the polynomial *)
 Definition Rec(P:Poly):Poly := list_to_Pol (Pol_to_list P).

 Fixpoint Rev1(Q P:Poly)(i:positive){struct P}:Poly:=
   match P with
     |Pc c => Rat_mkPX Q i c
     |PX P' j p => Rev1 (Rat_mkPX Q i p) P' j
   end.

 Definition Rev(P:Poly):=
   match P with
     |Pc c => Pc c
     |PX P' i p' => Rev1 (Pc p') P' i 
   end.

   (*adds (i-1) times the rationnal r in head of the Rat list l*)
 Fixpoint repeat_add(r:Rat)(i:positive)(l:list Rat){struct i}:list Rat :=
   match i with
     |xH => l
     |xO p => r::(repeat_add r p (repeat_add r p l))
     |xI p => repeat_add r p (repeat_add r p l)
   end.

   (*list of coef of a Poly, with all zeros, from constant coef to leading*)
 Fixpoint Pol_to_list_dense(P:Poly):list Rat:=
   match P with
     |Pc p => p::nil
     |PX Q i q => q :: (repeat_add R0 i (Pol_to_list_dense Q))
   end.


(*divides by the proper binomial coefs to get the bern coefs*)
 Fixpoint binomial_div (l:list Rat)(p:N)(i:N){struct l}:list Rat:=
   match l with
     |nil => nil
     |h::t => (h/(binomial p i))::(binomial_div t p (Npred i))
   end.


(*coefs of P in the Bernstein basis over c,d, form b_p to b_0 if
  p is the degree of P*)
 Definition bernstein_coefs(P:Poly)(c d:Rat):list Rat :=
   let Q := (Ptranslate (Rec (dilat (Ptranslate P c) (d -c))) ( R1)) in
   let (deg, coef) := deg_coefdom Q in
   let list_coef := Pol_to_list_dense Q in
     binomial_div list_coef deg deg.

 
  (*input : list of bernstein coefs for P of deg <= p in the bern basis
    p over c,d. and a rational e
  
  output : list of bernstein coefs for P of deg <= p in the bern basis
  p over c,e 
  and
  list of bernstein coefs for P of deg <= p in the bern basis
  p over e,d
  *)



 Fixpoint next_bern_list_i(bern_i_1:list Rat)(a b:Rat)
   {struct bern_i_1}: list Rat :=
   match bern_i_1 with
     |nil => nil
     |b'::l' => match l' with
		  |nil => nil
		  |b''::l'' => (b*b' + a*b'')::(next_bern_list_i l' a b)
		end
   end.

(* Section BERN_SPLIT.
   Variables c d e:Rat.
   Definition  a := (d-e)/(c-c).
   Definition b := (e-c)/(d-c).
 
  Fixpoint bernstein_split(bern_coef:list Rat)(p:N)(l' l'':list Rat):=
    let (b',b'') := first_last bern_coef R0 in
      match p with
	|N0 =>	(b'::l', b''::l'')
	|Npos p =>
	  let (l',l''):= bernstein_split (next_bern_list bern_coef) p-1 in
	    (b'::l', b''::l'')
*)

End POLY.
