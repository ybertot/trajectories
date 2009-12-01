open Num;;
open Format;;

include Format;;                                       
include Num;;
    	 	
(* the ring structure *) 
module type RING = 
sig 
type t 
(* type of elements o the ring *) 
val zero : t 
val unit : t 
val plus : t -> t -> t 
val mult : t -> t -> t 
val equal : t -> t -> bool 
val print : t -> unit 
end ;; 

(* la structure d'anneau sur des valeurs de type t *) 

module type POLYNOMIAL = 
sig 
type c 
(* type of coefficients *) 
type t 
(* type of polynoms *) 
val zero : t 
val unit : t 
(* unit for the polynomial product. It is superfluous, since it is a
   special case of monomial; however this makes polynomials match the
   interface of rings *)
val monomial : c -> int -> t 
(* monomial a k retruns the monomial X^k *) 
val plus : t -> t -> t 
val mult : t -> t -> t 
val equal : t -> t -> bool 
val print : t -> unit 
val eval : t -> c -> c 
end ;; 
(* The functor that given a ring structure returns a polynomial
   structure. One must be careful to make the type of coefficients
   consistent with the type of the elements of the ring structure
   received as parameter *)
 
module Make (A : RING) : (POLYNOMIAL with type c = A.t);;
    	 	
(* the ring structure *) 
module type RING = 
sig 
type t 
val zero : t 
val unit : t 
val plus : t -> t -> t 
val mult : t -> t -> t 
val equal : t -> t -> bool 
val print : t -> unit 
end ;;
 
(* the polynom structure *) 
module type POLYNOMIAL =
 sig 
type c 
type t 
val zero : t 
val unit : t 
val monomial : c -> int -> t 
val plus : t -> t -> t 
val mult : t -> t -> t 
val equal : t -> t -> bool 
val print : t -> unit 
val eval : t -> c -> c 
end ;; 

module Make (A : RING) = 
struct 

type c = A.t 
(* a monomial is both a coeficient and an power *) 
type monomial = (c * int) 
(* a polynom is a list of monomials sorted by their power this
   invariant should be carefully preserved *) 
type t = monomial list
 (* null coeficients are eliminated, so as to get a canonical
    representation. In particular the null monomial is the empty
    list *)
let zero = [] 
(* thanks to the invariant, two equal polynomials should have the same
   decomposition up to equality of the monomials *) 
let rec equal p1 p2 = 
  match p1, p2 with 
    | [],[] -> true 
    | (a1, k1)::q1, (a2, k2)::q2 -> 
        k1 = k2 && A.equal a1 a2 && equal q1 q2 
    | _ -> false (* monomial creation *) 

let monomial a k = 
  if k < 0 then failwith "monomial: the power cannot be negative" 
  else if A.equal a A.zero then [] else [a, k] 

(* a pacticular case *) 
let unit = [A.unit, 0] 
(* one must be careful to preserve the invariant and sort the
   monomials *) 
let rec plus u v = 
  match u, v with 
      (x1, k1)::r1 as p1, ((x2, k2)::r2 as p2) -> 
        if k1 < k2 then (x1, k1):: (plus r1 p2) 
        else if k1 = k2 then 
          let x = A.plus x1 x2 in 
            if A.equal x A.zero then plus r1 r2 
            else (A.plus x1 x2, k1):: (plus r1 r2) 
        else (x2, k2):: (plus p1 r2) 
    | [], _ -> v 
    | _ , [] -> u 

(* could be improved to avoid recomputing powers of k *) 
let rec fois (a, k) = (* we assume a <> zero *) 
function 
  | [] -> [] 
  | (a1, k1)::q -> 
      let a2 = A.mult a a1 in 
        if A.equal a2 A.zero then fois (a,k) q 
        else (a2, k + k1) :: fois (a,k) q 

let mult p = List.fold_left (fun r m -> plus r (fois m p)) zero 

(* low quality printing *) 
let print p = 
  List.iter 
    (fun (a,k) -> 
       Printf.printf "+ ("; A.print a; Printf.printf ") X^%d " k) p 

(* Power c^k by dichotomy: c is a coeficient, k an interger >= 0. *) 
let rec puis c = 
  function 
    | 0 -> A.unit 
    | 1 -> c 
    | k -> 
        let l = puis c (k lsr 1) in 
        let l2 = A.mult l l in 
          if k land 1 = 0 then l2 else A.mult c l2 

let eval p c = 
  match List.rev p with
    | [] -> A.zero 
    | (h::t) -> 
        let (* reduce two monomials into a single one. NB: on a k >=
  l. *) 
            twoinone (a, k) (b, l) = 
          A.plus (A.mult (puis c (k-l)) a) b, l in 
        let a, k = List.fold_left twoinone h t in 
          A.mult (puis c k) a 
end ;; 

