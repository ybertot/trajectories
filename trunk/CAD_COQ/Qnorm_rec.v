
(*rationnal numbers are the ones in QArith, and operations are systematically
  normalizing*)

Require Export QArith.
Require Import Qabs.

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


 Definition is_gt(p q:positive):bool :=
   match Pcompare p q Eq with
     |Gt => true
     |_ => false
   end.



(* euclidian division, for positives *)

 Fixpoint quo_rem(a b :positive){struct a} : N*N :=
  match a with 
    |xH => if (is_gt b xH) then (N0, Npos xH) else (Npos xH, N0)
    |xO a' => let (q', r') := quo_rem a' b in
      match r' with
	|N0 => (Ndouble q', N0)
	|Npos p' => if (is_gt b (xO p'))
	  then  (Ndouble q', Npos (xO p'))
	  else (Nsucc (Ndouble q'), Nminus (Npos (xO p')) (Npos b))
      end
    |xI a' => let (q',r') := quo_rem a' b in
      match r' with
	|N0 => if (is_gt b xH) then (Ndouble q', Npos xH) else (Npos a, N0)
	|Npos p' => if (is_gt b (xI p'))
	  then (Ndouble q', Npos (xI p'))
	  else (Nsucc (Ndouble q'), Nminus (Npos (xI p')) (Npos b))
      end
  end.


(*if a >b > 0 computes the simplification of (a,b) ie gcd free parts (a', b')*)
(*n for the termination, will be a*)
 Fixpoint remove_gcd_term(a b n: positive){struct n}: positive*positive :=
   let (q,r) := quo_rem a b in
     match r, q, n with
       |N0, N0, _ =>  (a,b) (* n'arrive jamais *)
       |N0, Npos q', _ => (q', xH)
       |_, _, xH => (a,b) (* n'arrive jamais *)
       |Npos r', N0, xO n'  => let (l,m) := (remove_gcd_term b r' n') in (m, l)
       |Npos r', N0, xI n' => let (l,m) := (remove_gcd_term b r' n') in (m, l)
       |Npos r', Npos q', xO n' =>
	 let (l,m) := (remove_gcd_term b r' n') in
	   (Pplus (Pmult l q') m, l)
       |Npos r', Npos q', xI n' =>
	 let (l,m) := (remove_gcd_term b r' n') in
	   (Pplus (Pmult l q') m, l)
     end.

 Definition remove_gcd(a b:positive):=remove_gcd_term a b a.
 
 (* normalization of fractions*)

 Definition Qsimpl(q:Q):Q :=
   match Qnum q with
     |Z0 => 0#1
     |Zpos a => let b := Qden q in
       match Pcompare a b Eq with
	 |Eq => 1#1
	 |Lt => let (b', a'):= (remove_gcd b a) in (Zpos a')#b' 
	 |Gt => let (a', b'):= (remove_gcd a b) in (Zpos a')#b'
       end
     |Zneg a => let b := Qden q in
       match Pcompare a b Eq with
	 |Eq => (Zneg xH)#1
	 |Lt => let (b', a'):= (remove_gcd b a) in (Zneg a')#b' 
	 |Gt => let (a', b'):= (remove_gcd a b) in (Zneg a')#b'
       end
   end.


(*first normalizing operations over rationnals *)
 Definition Qplus_r(x y : Q) := Qsimpl (Qplus x y).
 Definition Qmult_r(x y : Q) := Qsimpl (Qmult x y).
 Definition Qsub_r(x y : Q) := (Qplus_r x (Qopp y)).
 Definition Qdiv_r(x y : Q) := (Qmult_r  x (Qinv y)).
 Definition Qmake_r(n :Z)(d  : positive) := (Qsimpl (Qmake n d)).
 
 (*zero test for a normalized rationnal*)
 Definition Qzero_test(q:Q):=
   let (d,n) := q in
     match d with
       |Z0 => true
       |_ => false
     end.

(*the sig of a rationnal number is th one of its denom*)
 Definition Qsign := Qnum.
 
(*no need to use normalized mult to compute a power of a norm rational*) 
 Fixpoint Qpow_pos(q:Q)(i:positive){struct i}:Q:=
   match i with
     |xH => q
     |xO p => let q' := (Qpow_pos q p) in q'*q'
     |xI p => let q' := (Qpow_pos q p) in q * q' * q'
   end.

 Definition Qpow(q:Q)(i:N) : Q :=
   match i with
     |N0 => 1#1
     |Npos p => Qpow_pos q p
   end.

 Definition Q_abs_val(q:Q):=
   match Qnum q with
     |Zneg _ => - q
     |_ => q
   end.


 Definition Qlt_dec(q q':Q):=
   match Zcompare ((Zpos (Qden q'))*(Qnum q)) ((Zpos (Qden q))*(Qnum q')) with
     |Lt => true
     |_ => false
   end.

Definition Q_norm := mk_rat Q (0#1) (1 # 1) Qmake_r (fun x => x) Qplus_r 
	Qopp Qmult_r Qsub_r Qinv Qdiv_r Qeq Qlt_dec Qzero_test 
	(fun x => match (Qnum x) with |Z0 => Eq | Zpos => Gt | Zneg => Lt end) Qpow.




