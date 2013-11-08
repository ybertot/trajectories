Require Import BigQ.
Import BigQ.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
Require Import mxalgebra perm zmodp matrix ssrint refinements funperm.
Require Import seq seqpoly square_free casteljau desc.





(* Viewing p1 and p2 (list of rationals as representing polynomials,
  with coefficients of lower degree appearing first. *)
Fixpoint addp (p1 p2 : seq bigQ) :=
  match p1, p2 with
  | (a :: p1'), (b :: p2') => (a + b)%bigQ::addp p1' p2'
  | [::], _ => p2
  | _, [::] => p1
  end.

Section addp_correct.

End addp_correct.

(* Multiplication by a scalar. *)
Fixpoint scal a p :=
  match p with
  | b::p' => (a * b)%bigQ::scal a p'
  | [::] => [::]
  end.

(* Multiplication between two polynomials, naive algorithm. *)
Fixpoint mulp p1 p2 :=
  match p1 with
  | a::p1' => addp (scal a p2)  (0%bigQ::mulp p1' p2)
  | [::] => [::]
  end.

(* Composition of two polynomials, Horner style *)
Fixpoint compp p1 p2 :=
  match p1 with
  | [::] => [::]
  | [:: a] => p1
  | a :: p1' => addp (a::nil) (mulp p2 (compp p1' p2))
  end.

(* Translation by a is composition with (X + a) *)
Definition theta a p := compp p (a::1::nil)%bigQ.

(* Expansion by factor k is composition with (k X) *)
Definition chi k (p : seq bigQ) := compp p (0::k::nil)%bigQ.

(* Inversion *)

Definition rho := @rev bigQ.

Definition tau l r p := map red (theta 1 (rho (chi (r - l) (theta l p)))).

(* Computing binomial coefficients in the filed bigQ *)
Fixpoint fact_aux (count : nat) (n : bigQ) :=
  match count with
  | 0%nat => n
  | 1%nat => n
  | S p => (n * fact_aux p (n + 1))%bigQ
  end. 

Definition fact (n : nat) : bigQ := fact_aux n 1.

Definition binomial n i := red ((fact n) / (fact i * fact (n - i)))%bigQ.

(* The scalar product between sequences of numbers, the size of
  the result is the minimum of the input sizes. *)
Definition product l1 l2 := map (fun c => (c.1 * c.2)%bigQ) (zip l1 l2).

(* Defining a function that returns the list of natural numbers, in
 increasing order. *)

Definition binvs n := map (fun i => (1/binomial n i)%bigQ) (iota 0 (S n)).

(* Computing the initial list of Bernstein coefficients for a polynomial
  and an interval.  The first argument is degree of the polynomial. *)
Definition b_coefs n l r p := rev (product (binvs n) (tau l r p)).

(* Bernstein coefficients for half intervals can be computed using the
 algorithm by de Casteljau. *)
Fixpoint casteljau l (n : nat) :=
  match n with
    O => fun j => nth 0%bigQ l j
  | S p => fun j => ((casteljau l p j + casteljau l p j.+1)/2)%bigQ
  end.

(* This computes the Bernstein coefficients for the left hand side
  half. *)
Definition dicho_l n l :=
  map (fun i => red (casteljau l i 0)) (iota 0 (S n)).

Definition dicho_r n l :=
  map (fun i => red (casteljau l (n - i) i)) (iota 0 (S n)).

Fixpoint seqn0 l :=
  match l with
  | [::] => [::]
  | a::l' => if (eq_bool a 0) then seqn0 l' else a::seqn0 l'
  end.

Definition ch_at a b :=
  match (a ?= 0)%bigQ with
  | Eq => 0%nat
  | Gt => match (b ?= 0)%bigQ with Lt => 1%nat | _ => 0%nat end
  | Lt => match (b ?= 0)%bigQ with Gt => 1%nat | _ => 0%nat end
  end.

Fixpoint ch_r a l : nat :=
  match l with | nil => 0%nat | b::l' => (ch_at a b + ch_r b l')%nat end.

Definition changes l :=
  match l with | [::] => 0%nat | a::l' => ch_r a l' end.

Inductive root_info := 
  | Exact (x : bigQ)
  | One_in (x y : bigQ)
  | Zero_in (x y : bigQ)
  | Unknown (x y : bigQ).

Fixpoint isol_rec n d a b l acc : seq root_info :=
  match n with
    O => Unknown a b::nil
  | S p =>
    match changes l with
    | 0%nat => Zero_in a b::acc
    | 1%nat => One_in a b::acc
    | _ =>
    let c := red ((a + b)/2) in
    let l2 := dicho_r d l in
    isol_rec p d a c (dicho_l d l)
        if eq_bool (head 0%bigQ l2) 0 then Exact c::isol_rec p d c b l2
        else isol_rec p d c b l2
    end
  end.
    
Definition big_num := 500%nat.

(* this polynomial has only one root, but the curve comes close to
  the x axis around 2.5: this forces the dichotomy process a few times. *)
Definition mypol : list bigQ := ((-28/5)::11::(-6)::1::nil)%bigQ.

(* The following isolates the single root of mypol in (0,4) *)
Compute b_coefs 3 0 4 mypol.
Compute b_coefs 3 2 4 mypol.
Compute map (fun p => p.1 ?= p.2)%bigQ 
    (zip (dicho_r 3 (b_coefs 3 2 4 mypol)) (b_coefs 3 3 4 mypol)).
Compute changes (b_coefs 3 3 4 mypol).
Compute isol_rec big_num 3 2 3 (b_coefs 3 2 3 mypol) [::].
Compute isol_rec big_num 3 0 4 (b_coefs 3 0 4 mypol) [::].

Fixpoint lead_coef_r c p :=
  match p with
    [::] => c
  | x::p' => 
    lead_coef_r  match (x ?= 0)%bigQ with Eq => c | _ => x end p'
  end.

Definition lead_coef p := lead_coef_r 0%bigQ p.

Fixpoint is_zero_pol (p : seq bigQ) :=
  match p with
    [::] => true
  | x::p' => match (x ?= 0)%bigQ with Eq => is_zero_pol p' | _ => false end
  end.

Fixpoint normalize p :=
  match p with
    [::] => [::]
  | x::p' => 
    if is_zero_pol p then nil else x::normalize p'
  end.

Fixpoint chomp {A : Type} (p : list A) :=
  match p with
    [::] => [::]
  | x::nil => nil
  | x::p' => x::chomp p'
  end.

(* To be used with a monic divisor d. *)

Fixpoint divp_r (p d : seq bigQ) : seq bigQ * seq bigQ :=
  match p with
    a::p' =>
    let (q, r) := divp_r p' d in
      let y := nth 0%bigQ r (size d).-2 in
      (y::q, addp (a::r) (scal ((-1) * y) d))
  | nil => (nil, nil)
  end.        

Definition divp p d :=
  let d' := normalize d in
  let lc := lead_coef d' in
  match d' with
    nil => (nil, p)
  | _::_ => let (q, r) := divp_r p (map (fun x => x/lc)%bigQ d') in
    (map (fun x => x/lc)%bigQ q, r)
  end.

Definition clean_divp p d :=
  let (a, b) := divp p d in (map red (normalize a), map red (normalize b)).

Fixpoint bigQ_of_nat (n : nat) :=
  match n with 0%nat => 0%bigQ | S p => (1 + bigQ_of_nat p)%bigQ end.

Definition derive p := 
  match product (map bigQ_of_nat (iota 0 (size p))) p with
    _::p' => p' | _ => nil
  end.

Fixpoint gcd_r n (p q : seq bigQ) : seq bigQ :=
  match n with
    0 => p
  | S n' =>
    let (_, r) := clean_divp p q in
      match r with nil => q | _ => gcd_r n' q r end
  end.

Definition gcd (p q : seq bigQ) :=
  let r := gcd_r (maxn (size p) (size q)).+1 p q in
  let lc := lead_coef r in
  map (fun x => red (x/lc)) r.

Definition no_square p :=
  fst (clean_divp p (gcd p (derive p))).

Definition isolate a b l : seq root_info :=
  let l := no_square l in
  let deg := (size l).-1 in
  let coefs := b_coefs deg a b l in
  let b_is_root :=
    if eq_bool (last 0%bigQ coefs) 0 then [:: Exact b] else [::] in
  let result := isol_rec big_num deg a b coefs b_is_root in
  if eq_bool (head 0%bigQ l) 0 then Exact a::result else result.

Fixpoint horner x p :=
  match p with
    nil => 0%bigQ
  | a::p' => (a + x * horner x p')%bigQ
  end.

Fixpoint ref_rec n a b pol :=
  match n with
    O => One_in (red a) (red b)
  | S p =>
    let c := ((a + b)/2)%bigQ in
    let v := horner c pol in
    match (v ?= 0)%bigQ with
      Lt =>  ref_rec p c b pol
    | Gt =>  ref_rec p a c pol
    | Eq => Exact (red c)
    end
  end.

Fixpoint first_sign l :=
  match l with
    nil => 1%bigQ
  | a::tl =>
   match (a ?= 0) with Eq => first_sign tl | Lt => -1 | Gt => 1 end%bigQ
  end.

Definition refine n a b p :=
  let deg := (List.length p).-1 in
  let coefs := b_coefs deg a b p in
  ref_rec n a b (scal (-1 * first_sign coefs) p).

(* This polynomial has 1,2, and 3 as roots. *)
Definition pol2 : list bigQ := ((-6)::11::(-6)::1::nil)%bigQ.

(* This polynomial as 1 and 2 as roots, with respective multiplicities
  1 and 2. *)

Fixpoint no_root (l : list root_info) : bool :=
  match l with
    nil => true
  | Zero_in a b::l' => no_root l'
  | _ => false
  end.


Definition pol3 : list bigQ := ((-4)::8::(-5)::1::nil)%bigQ.

(* The following computation proves that mypol has no roots in (2,4) *)
Compute mypol.
Compute no_square mypol.

Compute isolate 2 4 mypol.


Time Compute refine 20 0 2 mypol.

Compute (horner (110139 # 131072) mypol).
Compute (horner (440557 # 524288) mypol).

(* Polynomial pol2 actually has roots in 1, 2, and 3 *)
Compute isolate 0 4 pol2.

Compute isolate 0 4 pol3.

(* When the path of computation touches the roots, they are recognized
 as such. *)
Compute isolate 1 3 pol2.

Compute refine 10 (11#10) 3 pol2.

Compute ((10000 * 20479 / 10240)%bigZ, (10000 * 10249 / 5120)%bigZ).

(* Without type information, this gives an error message that looks like a
  bug. *)

Compute clean_divp ((-2)::1::1::nil)%bigQ (4::2::nil)%bigQ.

Compute let p := ((-2)::1::1::nil)%bigQ in
        let d := (2::1::nil)%bigQ in
        let (q, r) := divp p d in
        (q, r, normalize (addp p (scal (-1) (addp (mulp q d) r)))).

Compute let p := ((-2)::1::1::nil)%bigQ in
        let q := ((-1)::3::(-3)::1::nil)%bigQ in
        gcd p q.

Compute derive ((-1)::3::(-3)::1::nil)%bigQ.

Compute gcd ((-1)::3::(-3)::1::nil)%bigQ (derive ((-1)::3::(-3)::1::nil)%bigQ).

Compute clean_divp ((-1)::3::(-3)::1::nil)%bigQ
             (1::(-2)::1::nil)%bigQ.

Time Compute no_square ((-1)::3::(-3)::1::nil)%bigQ.

(* This is a poor man's correctness proof for the decision procedure,
  but it should actually be extended to be used in any real-closed field. *)
