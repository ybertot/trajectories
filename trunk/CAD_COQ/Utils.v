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
     |a::q => last_elem A q bottom
   end.

 Implicit Arguments last_elem [A].

  (*first and last elemts of a list in a sngle op*)
 Fixpoint first_last(A:Set)(l:list A)(bottom:A){struct l}:A*A:=
   match l with
     |nil => (bottom,bottom)
     |a::q => match q with
		|nil => (a,a)
		|b::q' => let (c,d):= first_last A q bottom in (a,d)
	      end
   end.

 Implicit Arguments first_last [A].