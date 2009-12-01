exception Abort

exception NotFound


(* -------------------------------------------------------------------- *)
(* More on nums *)
module Num =
struct
  include Num

  let num_zero    = (num_of_int   0)
  let num_one     = (num_of_int   1)
  let num_neg_one = (num_of_int (-1))

  let bigint_num = function
  | Int     n -> Big_int.big_int_of_int n
  | Big_int n -> n
  | Ratio   n -> Ratio.big_int_of_ratio n

  let kck = fun x y ->
    if x = y then num_neg_one else num_zero
end

open Num

(* Very naive interval arithmetic for bound computations *)

let i0 = (num_zero, num_zero)
let i1 = (num_one, num_one)

(* [a,b]+[c,d], a<=b and c<=d *)
let add_int i1 i2 =
  let (i1', i1'') = i1 in
  let (i2', i2'') = i2 in
    (add_num i1' i2', add_num i1'' i2'')

(* [a,b]+ c, a<=b *)
let add_int_num i1 c =
  let (i1', i1'') = i1 in
    (add_num i1' c, add_num i1'' c)

(* [a,b]*[c,d], a<=b and c<=d *)
let mult_int i1 i2 = 
  let (a, b) = i1 in
  let (c, d) = i2 in
  let ac = mult_num a c in
  let ad = mult_num a d in
  let bc = mult_num b c in
  let bd = mult_num b d in
    (min_num (min_num (min_num ac ad) bc) bd,
              max_num (max_num (max_num ac ad) bc) bd)
(* [i1, i2] * c i1 <= i2 *)
let mult_int_num i c =
  let (i1, i2) = i in
    match sign_num c with
      | - 1 -> (mult_num i2 c, mult_num i1 c)
      | 0 -> i0
      | 1 ->  (mult_num i1 c, mult_num i2 c)

(*[a,b]^i, a<=b*)
let pow_int iab i =
  let rec pow_aux one iab i =
    match i with
      | i when i < 0 -> invalid_arg "fast_power requires non-negative n"
      | 0 -> one (* "one" is used as product accumulator *)
      | i -> 
          let sq = mult_int iab iab in (* x contains the last square *)
            if (i mod 2) = 1 then pow_aux (mult_int one iab) sq (i / 2)
            else pow_aux one sq (i / 2)
    in
      pow_aux i1 iab i

(* [a,b]/[c,d], a<=b and c<=d *)
let div_int i1 i2 = 
  let (a, b) = i1 in
  let (c, d) = i2 in
  let ac = div_num a c in
  let ad = div_num a d in
  let bc = div_num b c in
  let bd = div_num b d in
    (min_num (min_num (min_num ac ad) bc) bd,
              max_num (max_num (max_num ac ad) bc) bd)

(* [i1, i2] / c i1 <= i2 *)
let div_int_num i c =
  let (i1, i2) = i in
    match sign_num c with
      | - 1 -> (div_num i2 c, div_num i1 c)
      | 0 -> i0
      | 1 ->  (div_num i1 c, div_num i2 c)
    

(* -------------------------------------------------------------------- *)
(* naive binomial coeficient (n p) = n!/p!(n - p)! using the
   Pascal triangle ie (n + 1, p + 1) = (n, p) + (n, p + 1) *) 
let rec binomial n p =
  match (n, p) with
    |(0, _) -> 0
    |(_, 0) -> 1
    |(m, q) -> binomial (m - 1) (q - 1) + binomial (m - 1) q

(* mean of n1 and n2 *)
let middle n1 n2 =
  div_num (add_num n1 n2) (num_of_int 2)


(* q to the n*(n+1)/2 *)
let sum_pow q n = 
  let qton = power_num q (num_of_int n) in
    div_num (mult_num q qton) (num_of_int 2)

(* -------------------------------------------------------------------- *)
(* signs *)

type sign = Zero | Neg | Pos | Unknown


(* -------------------------------------------------------------------- *)
(* More on lists *)

let find_at l x =
  let rec aux l n =
    match l with
      |[] -> raise NotFound
      | h :: tl -> 
          if h = x then n
          else aux tl (n + 1)
  in
    aux l 0

(* sorts and remove duplicates, with std equality *)
let merge_clean l=
   let rec f l = match l with
       []->[]
      |[a]->[a]
      |a::b::q->if a=b then f (a::q) else a::(f (b::q))
   in f (Sort.list (>=) (List.flatten l))

(* removes duplicates with a given comparison function *)
let rec clean_list compare l = 
  match l with
      []->[]
    |[a]->[a]
    |a :: b :: q -> 
       if compare a b then clean_list compare (a :: q)
       else a :: (clean_list compare (b::q))

  
let flat_map f l = 
  let rec aux_rec l' res = 
    match l' with
      |[] -> res
      |a :: l'' -> aux_rec l'' ((f a) @ res)

  in
    aux_rec l []


(* -------------------------------------------------------------------- *)
(* Printing and debug stuff *)
let debug=ref false;;

let pr x = if !debug then (Format.printf "@[%s@]" x; flush(stdout);)else ()

let prn x = if !debug then (Format.printf "@[%s\n@]" x; flush(stdout);) else ()

let prt0 s = () (* print_string s;flush(stdout)*)

let prt s = if !debug then (print_string (s^"\n");flush(stdout)) else ()

module StringComparable =
struct
  type t       = string
  let  compare = (Pervasives.compare : t -> t -> int)
end

module StringSet = Set.Make(StringComparable)

module ExtMapMake(X : Map.OrderedType) =
struct
  include Map.Make(X)

  module Set = Set.Make(X)

  let items = fun t ->
    List.rev (fold (fun k v items -> (k, v) :: items) t [])

  let keys = fun t ->
    fold (fun k v keys -> Set.add k keys) t Set.empty
end

module StringMap = ExtMapMake(StringComparable)

module IntListComparable =
struct
  type t       = int list
  let  compare = (Pervasives.compare : t -> t -> int)
end

module IntListSet = Set.Make(IntListComparable)

module IntListMap = ExtMapMake(IntListComparable)

