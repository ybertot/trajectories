Require Export NArith.
Require Export Mylist.


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


  (*last element of a list *)
 Fixpoint last_elem(A:Set)(l:list A)(bottom:A){struct l}:A:=
   match l with
     |nil => bottom
     |a::q =>
       match q with
	 |nil => a
	 |_ => last_elem A q bottom
       end
   end.

 Implicit Arguments last_elem [A].

 Fixpoint two_last_elems(A:Set)(l:list A)(bottom:A*A){struct l}:A*A :=
   match l with
     |nil => bottom
     |a::q => 
       match q with
		|nil => bottom
		|b::q' =>
		  match q' with
		    |nil => (a,b)
		    |_ => two_last_elems A q bottom
		  end
       end
   end.

 Implicit Arguments two_last_elems [A].

