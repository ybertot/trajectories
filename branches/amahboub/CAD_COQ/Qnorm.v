
(*rationnal numbers are the ones in QArith, and operations are systematically
  normalizing*)

Add LoadPath "/0/user/amahboub/QArith".
Add LoadPath "/0/user/amahboub/cad_coq".

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


(*Commencer par faire la preuve de correction/completude de Qsimpl...

 Lemma Qplus_r_ext : forall x1 x2 y1 y2, 
   x1 == x2 -> y1 == y2 -> (Qplus_r x1  y1) == (Qplus_r x2  y2).
 Proof.
   intros.
   unfold Qplus_r.
   setoid_rewrite H.
   setoid_rewrite H0.
   apply Qeq_refl.
 Qed.

 Lemma Qmult_r_ext : forall x1 x2 y1 y2, 
   x1 == x2 -> y1 == y2 -> (Qmult_r x1  y1) == (Qmult_r x2  y2).
 Proof.
   intros;unfold Qmult_r.
   setoid_rewrite H.
   setoid_rewrite H0.
   apply Qeq_refl.
 Qed.

 

 Lemma Qopp_spec : forall x, (Qplus_r x  (- x)) == (0#1).
 Proof.
   intros.
   unfold Qplus_r.
   setoid_rewrite (Qplus_inverse_r x).
   setoid_rewrite (Qred_correct (0#1)).
   apply Qeq_refl.
 Qed.

 Lemma Qsub_r_spec : forall x y, (Qsub_r x y) == (Qplus_r x (Qopp y)).
 Proof.
   intros.
   unfold Qsub_r.
   apply Qeq_refl.
 Qed.

 Lemma Qdiv_r_spec : forall x y,  (Qdiv_r x y) == (Qmult_r x (Qinv y)).
 Proof.
   intros.
   unfold Qdiv_r.
   apply Qeq_refl.
 Qed.

 Ltac caseEq t := generalize (refl_equal t);pattern t at -1;case t.

 Lemma Qzero_test_def : forall x, 
   (Qzero_test x) = true  -> (Qnum x) = Z0.
 Proof.
   intros.
   destruct x; inversion H.
   simpl.
   induction Qnum;simpl;trivial;try (absurd (false=true);discriminate).
 Qed.
 
 Lemma Qzero_test_spec : forall x, (Is_true (Qzero_test x))-> x == (0 #1).
 Proof.
   intros.
   unfold Qeq;simpl.
   caseEq (Qzero_test x);intro.
   rewrite (Qzero_test_def x H0);simpl;trivial.
   rewrite H0 in H;simpl in H.
   elim H.
 Qed.
 

 Lemma Q0_l : forall x, (Qplus_r (0#1) x) == x.
 Proof.
   intros.
   unfold Qplus_r.
   setoid_rewrite (Qplus_sym (0#1) x).
   setoid_rewrite (Qzero_right x).
   setoid_rewrite (Qred_correct x).
   apply Qeq_refl.
 Qed.

 Lemma Qplus_r_sym : forall x y, (Qplus_r x y) == (Qplus_r y x).
 Proof.
   intros.
   unfold Qplus_r.
   setoid_rewrite (Qplus_sym x y).
   apply Qeq_refl.
 Qed.

 Lemma Qplus_r_assoc : forall x y z,
   (Qplus_r x (Qplus_r y z)) == (Qplus_r (Qplus_r x y ) z).
 Proof.
   intros.
   unfold Qplus_r.
   setoid_rewrite (Qred_correct (Qplus x y)).
   setoid_rewrite (Qred_correct (Qplus y z)).
   setoid_rewrite (Qplus_assoc x y z).
   apply Qeq_refl.
 Qed.
	

 Lemma Qmult_r_1_l : forall x, (Qmult_r (1#1) x) == x.
 Proof.
   intros.
   unfold Qmult_r.
   setoid_rewrite (Qmult_sym (1#1) x).
   setoid_rewrite (Qred_correct (x * (1#1))).
   apply (Qmult_n_1 x).
 Qed.

 Lemma Qmult_r_sym : forall x y, (Qmult_r x y) == (Qmult_r y x).
 Proof.
   intros.
   setoid_rewrite (Qmult_r_correct x y). 
   setoid_rewrite (Qmult_r_correct y x).
   setoid_rewrite (Qmult_sym x y).
   apply Qeq_refl.
 Qed.
 
 Lemma Qmult_r_assoc : forall x y z, 
   (Qmult_r x  (Qmult_r y z)) == (Qmult_r(Qmult_r x  y) z). 
 Proof.
   intros.
   setoid_rewrite (Qmult_r_correct x y).
   setoid_rewrite (Qmult_r_correct y z).
   setoid_rewrite (Qmult_r_correct x (y*z)).
   setoid_rewrite (Qmult_r_correct (x*y) z).
   apply Qmult_assoc.
 Qed.

 Lemma Qdistr'_l : forall x y z,
   (Qmult_r (Qplus_r x y) z) == (Qplus_r (Qmult_r x z) (Qmult_r y z)).
 Proof.
   intros.
   setoid_rewrite (Qplus_r_correct  x y).
   setoid_rewrite (Qmult_r_correct  x z).
   setoid_rewrite (Qmult_r_correct y z).
   setoid_rewrite (Qplus_r_correct  (x*z) ( y * z)).
   setoid_rewrite (Qmult_r_correct (x+y) z).
   setoid_rewrite (Qmult_sym x z).
   setoid_rewrite (Qmult_sym y z).   
   setoid_rewrite (Qmult_sym (x + y) z).
   apply Qmult_plus_distr_r.
 Qed.

 
*)




 Module Q_NORM_SYST <: RAT_OPS.

  Definition Rat := Q.

(*constants, operations over rationnals,
-MkRat builds a rationnal number from an integer and a positive
-RatEq is an eq relation over rationnals
-Rat_zero_test is a decidable test to the zero constant
-Rat_sign gives the sign of a rationnal : Z0 means it is zero, Zpos _, it is pos, ...
-Rat_pow builds a power of a rationnal, if the rat argument is
  normalized then the power is normalized
*)
   
   Definition  R0 := 0#1.
   Definition  R1 := 1#1.
   Definition  MkRat := Qmake_r.
   Definition  Norm(x:Rat) := x.
   Definition  Rat_add := Qplus_r.
   Definition  Rat_opp := Qopp.
   Definition  Rat_prod := Qmult_r.
   Definition  Rat_sub := Qsub_r.
   Definition  Rat_inv := Qinv.
   Definition  Rat_div := Qdiv_r.
   Definition  RatEq := Qeq.
   Definition  Rat_zero_test := Qzero_test.
   Definition  Rat_sign := Qnum.
   Definition  Rat_pow := Qpow.



   Notation "a # b" := (MkRat a b) : Rat_scope.

   Infix "+" := Rat_add :Rat_scope.
   Notation "- x" := (Rat_opp x) : Rat_scope.
   Infix  "*" := Rat_prod : Rat_scope.
   Infix "-" := Rat_sub : Rat_scope.
   Notation "/ x" := (Rat_inv x): Rat_scope.
   Infix "/":= Rat_div : Rat_scope.

   Notation "x == y" := (RatEq x y) : Rat_scope.

   Definition  RatEq_refl := Qeq_refl.
   Definition  RatEq_sym := Qeq_sym.
   Definition  RatEq_trans := Qeq_trans.
     
  (* plus tard on a dit ...    
 
   Definition  Rat_add_ext := Qplus_r_ext.
   Definition  Rat_opp_ext := Qopp_comp.
   Definition  Rat_prod_ext := Qmult_r_ext.
   Definition  Rat_inv_ext := Qinv_comp.

  

   Definition  Rat_opp_spec := Qopp_spec.
   Definition  Rat_sub_spec := Qsub_r_spec.
   Definition  Rat_div_spec := Qdiv_r_spec.
   Definition  Rat_zero_test_spec := Qzero_test_spec.
  
   

   Definition  Rat_0_l    := Q0_l.
   Definition  Rat_add_sym    := Qplus_r_sym.
   Definition  Rat_add_assoc  := Qplus_r_assoc.
   Definition  Rat_prod_1_l    := Qmult_r_1_l.
   Definition  Rat_prod_sym    := Qmult_r_sym.
   Definition  Rat_prod_assoc  := Qmult_r_assoc.
   Definition  Rat_distr_l  := Qdistr'_l.
*)
(*   Definition Rat_of_Z(x : Z) := (MkRat x 1).
   Definition Rat_of_pos(i:positive) := (Rat_of_Z (Zpos i)).
*)

 Open Scope Rat_scope.
 End Q_NORM_SYST.






















(*tester la division*)


(* sturm a une variable

-- borner les racines d'un polynomes

-- creer une liste d'intervalles a bornes rationnelles pour chacune de ces racines

-- calculer la suite de restes pour un poly P

-- calculer la suite des sous resultants pour P?

-- calculer la sturm query pour un couple de polynomes

-- generalisation a n polynomes
*)


(* rem de benjamin attention ca ne marche que si b est different de 1
Fixpoint rem(a b :positive){struct a} : N :=
  match a with
     |xH => if (is_gt b xH) then Npos xH else N0
     |xO a' => let r' := rem a' b in
       match r' with
         |N0 => N0
         |Npos p' => if (is_gt b (xO p'))
           then (Npos (xO p')) else (Nminus (Npos (xO p')) (Npos b))
       end
     |xI a' => let r' := rem a' b in
       match r' with
         |N0 => Npos xH
         |Npos p' => if (is_gt b (xI p'))
           then (Npos (xI p')) else (Nminus (Npos (xI p')) (Npos b))
       end
   end.
*)