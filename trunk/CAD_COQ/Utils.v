Require Export NArith.
Require Export Mylist.

Set Implicit Arguments.

Definition Sign := option comparison.

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
	 |_ => last_elem q bottom
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
		    |_ => two_last_elems q bottom
		  end
       end
   end.

 Implicit Arguments two_last_elems [A].


 Fixpoint flat_map_ac(A B:Set)(f:A -> (list B))(l:list A)(res:list B){struct l}:list B:=
   match l with
     |nil => res
     |a::l' => flat_map_ac f l' ((f a)@res)
   end.

 Definition flat_map(A B:Set)(f:A -> (list B))(l:list A):= flat_map_ac f l nil.



Fixpoint sign_changes_rec(sign:comparison)(l:list comparison)
  {struct l}:nat:=
  match l with
    |nil => 0
    |a :: l' =>
      match sign, a with
	|Eq, _ => sign_changes_rec a l'
	|_, Eq => sign_changes_rec sign l'
	|Lt, Gt => S (sign_changes_rec Gt l')
	|Gt, Lt => S (sign_changes_rec Lt l')
	|_,_ => sign_changes_rec a l'
      end
  end.

Definition sign_changes(l : list comparison) : nat := 
  match l with
    |nil => O
    |a ::l' => sign_changes_rec a l'
  end.



Fixpoint op_sign_changes_rec(sign:(option comparison))(l:list (option comparison))
  {struct l}:option nat:=
  match l with
    |nil => Some 0
    |a :: l' =>
      match sign, a with
	|_, None => None
	|None, _ => None
	|Some Eq, _ => op_sign_changes_rec a l'
	|_, Some Eq => op_sign_changes_rec sign l'
	|Some Lt, Some Gt =>
	  let res := op_sign_changes_rec (Some Gt) l' in
	    match res with
	      |None => None
	      |Some r => Some (S r)
	    end
	|Some Gt, Some Lt =>
	  let res := op_sign_changes_rec (Some Lt) l' in
	    match res with
	      |None => None
	      |Some r => Some (S r)
	    end
	|_,_ => op_sign_changes_rec a l'
      end
  end.




Definition op_sign_changes(l:list (option comparison)) : (option nat) :=
  match l with
    |nil => Some O
    |a :: l'=> op_sign_changes_rec a l'
  end.
     
Definition sign_mult( u v:(option comparison)):=
   match u, v with
    |None,_ => None
    | _, None => None
    |Some u, Some v =>
	match u, v with
	 |Eq, _ =>Some Eq
    	|_, Eq => Some Eq
    	|Lt, Lt => Some Gt
    	|Lt, Gt => Some Lt
    	|Gt, Lt => Some Lt
    	|Gt, Gt => Some Gt
	end
end.

(* convenient uples in Set*)

Inductive triple(A B C :Set):Set:=
|Tr:forall a:A,forall b:B, forall c:C, triple A B C.

Definition triple_fst(A B C:Set)(u:triple A B C):=
  match  u with
  |Tr a _ _ => a
end.


Inductive four_uple(A B C D:Set):Set:=
|Four:forall a:A, forall b:B, forall c:C, forall d:D, four_uple A B C D.

Definition four_fst(A B C D:Set)(u:four_uple A B C D):=
  match  u with
  |Four a _ _ _ => a
end.


Fixpoint clean_head(A:Set)
(Aeq:A -> A -> bool)(a:A)(l:list A){struct l}:list A:=
match l return list A with
|nil => (a::nil)
|hd::tl =>
  if (Aeq a hd)
    then clean_head Aeq a tl
    else hd :: (clean_head Aeq a tl)
end.



Fixpoint clean_list(A:Set)(Aeq:A->A->bool)(l:list A){struct l}:list A:=
match l return (list A) with
|nil => nil
|a :: tl =>clean_head Aeq a (@clean_list A Aeq tl)
end.

Fixpoint eqn(n m:nat){struct n}:bool:=
match n,m with
|O, O => true
|S n, S m => eqn n m
|_, _ => false
end.

