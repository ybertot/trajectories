open Core
open List


type coef = Num.num
type variable = int

let add_coef = Num.add_num
let eq_coef = Num.eq_num
let minus_coef = Num.minus_num
let mult_coef = Num.mult_num
let sub_coef = (fun x y -> add_coef x (minus_coef y))
let div_coef = Num.div_num
let pow_coef x y = Num.power_num x (Num.num_of_int y)
let le_coef = Num.le_num
let lt_coef = Num.lt_num
let coef_of_int = Num.num_of_int
let string_of_coef = Num.string_of_num
let coef0 = Num.num_zero
let coef1 = Num.num_one
let coef_sign = Num.sign_num

(* type of polynomials *)

type poly = 
    Pint of coef                       (* constant poly *)
  | Prec of variable * (poly array)    (* coefficients increasing deg *)


(* Unless explicitely mentionned, operations expect their args to be in normal
 form, ie : 

- variables are postive integers
- coefficients of a pol in x only feature polynomials with variables < x
- no head  zeros in the coefficients
- no Prec (x, a) where a would have a single element (meaning the pol is cst in x

*)


(*----------------------------------------------------------------------------*)
(***  Printing ***)
(*----------------------------------------------------------------------------*)

(* if univ=false, we use x,y,z,a,b,c,d... for var names
   else, x1,x2,...
 *)
let univ=ref false

(* cant afford more than 26 variables ... *)
let string_of_var x =
  if !univ then
    "x"^(string_of_int x)
  else 
    if x<=3 then String.make 1 (Char.chr(x+(Char.code 'a')))
    else String.make 1 (Char.chr(x-4+(Char.code 'a')))


(* poly printer *)
let rec string_of_P p =
  match p with
    |Pint a -> 
       if le_coef coef0 a
       then string_of_coef a
       else "("^(string_of_coef a)^")" (* paren for neg coefs *)
    |Prec (x, t) -> 
       if Array.length t = 1 then failwith "not normal form"
       else 
         let res = 
           Array.mapi
             (fun i ti ->
                let s_of_ti = string_of_P ti in 
                  if s_of_ti = "0" then ""
                  else 
                    if i = 0 then s_of_ti^" + "
                    else 
                      let sti = 
                        if s_of_ti = "" then ""
                        else if s_of_ti = "1" then "" 
                        else if (String.contains s_of_ti '+') then "("^s_of_ti^")"
                        else s_of_ti in
                      let deg = Array.length t - 1 in 
                      let expi = 
                        if i = 1 then "" else "^"^(string_of_int i)
                      in
                        if i = deg then
                          sti^(string_of_var x)^expi
                        else 
                          sti^(string_of_var x)^expi^" + ")
             t
         in
           Array.fold_left (fun s1 s2 -> s1 ^ s2) "" res

(* printer for debug *)
let printP p = Format.printf "@[%s@]" (string_of_P p)

(* printer of an array of polys *)
let print_tpoly lp =
  let s = ref "\n{ " in
    Array.iter (fun p -> s:=(!s)^(string_of_P p)^"\n") lp;
    prt0 ((!s)^"}")

(* printer for a list of polys *)
let print_lpoly lp = print_tpoly (Array.of_list lp)

(* #install_printer printP *)

(*----------------------------------------------------------------------------*)
(*** Utilities ***)
(*----------------------------------------------------------------------------*)


(* cst pol *)
let cf x = Pint x

let p1 = cf coef1

let p0 = cf coef0
(* cst pol to cste *)
let int_of_Pint = 
  function 
    |Pint x ->x
    |_ -> failwith "not constant"

(* tests if a (normal) poly is cst *)
let is_constantP p = 
  match p with
    |Pint _ -> true
    |Prec (_, _) -> false


(* tests if a (normal) poly is zero *)
let is_zero p =
  match p with Pint n -> if eq_coef n coef0 then true else false |_-> false

(* tests is a pol has only one variable, rejects cst pols *)
let single_var_test p =
  match p with
    |Pint _ -> false
    |Prec (_, t) -> Array.fold_right (&&) (Array.map is_constantP t) true

(* constant coef of a normal poly *)
let rec coef_constant p =
  match p with
      Pint a -> a
    |Prec(_, q) -> coef_constant q.(0)


(* nth variable *)
let x n = Prec (n,[|cf coef0; cf coef1|])

(* the monomial v^n *)
let mon v n = 
  match n with
    | 0 -> Pint coef1;
    |_ ->
       let tmp = Array.make (n + 1) (Pint coef0) in
         tmp.(n) <- Pint coef1;
         Prec (v, tmp)

(* coefficient of deg i in var v, v <= max var of p *)
let coef v i p =
  match p with 
    | Prec (x, p1) when x = v  -> 
        if i < (Array.length p1) then p1.(i) 
        else Pint coef0
    |_ -> if i = 0 then p else Pint coef0

(* deg in var v of pol p, v <= max var of p *)
let rec deg v p =
  match p with 
      Prec(x, p1) when x = v -> Array.length p1 -1
    |_ -> 0
(* degree of p in its current variable *)
let rec current_deg p =
  match p with
    |Prec (_, t) -> Array.length t - 1
    |_ -> 0

(* leading coef in v *)
let lcoef v p = coef v (deg v p) p

(* leading coef in current variable *)
let current_lcoef p =
  match p with
    |Pint c -> Pint c
    |Prec (_, t) -> 
       let n = Array.length t in t.(n - 1)
         

(* max variable *)
let max_var_pol p = 
  match p with 
      Pint _ -> 0
    |Prec(x,_) -> x


(* same but the argument need not be normalized *)
let rec max_var_pol2 p =
  match p with 
      Pint _ -> 0
    |Prec(v,c)-> Array.fold_right (fun q m -> max (max_var_pol2 q) m) c v


(* max var of an array of poly *)
let rec max_var l = Array.fold_right (fun p m -> max (max_var_pol2 p) m) l 0

(* premier coef entier de p *)
let rec head_int_coef p =
  let v = max_var_pol p in
    if v>0
    then head_int_coef (lcoef v p)
    else (match p with | Pint a -> a |_ -> assert false)



(* sorted list of the variables of a pol *)
let rec vars = function
    Pint _->[]
  |Prec (x, l) -> merge_clean ([x]::(Array.to_list (Array.map vars l)))


(* total degree *)
let rec deg_total p =
  match p with 
      Prec (x,p1) -> let d = ref 0 in
        Array.iteri (fun i q -> d:= (max !d (i+(deg_total q)))) p1;
        !d
    |_ -> 0


(* copy of a pol *)
let rec copyP p =
  match p with
      Pint i -> Pint i
    |Prec(x, q) -> Prec(x, Array.map copyP q)
       

(* Equality btw two pols
   One should not use = since it does not work on Big_int ... *)
let rec eqP p q =
  match (p, q) with 
      (Pint a, Pint b) -> eq_coef a b
    |(Prec (x, p1), Prec (y, q1)) ->
       if x <> y then false
       else if (Array.length p1) <> (Array.length q1) then false
       else (try (Array.iteri (fun i a -> if not (eqP a q1.(i))
			       then failwith "raté")
		    p1;
		  true)
	     with _ -> false)
    | (_,_) -> false


(* nomalization of a pol whose coefs are in normal form :
cleans head zeros and if it becomes cst, computes the cst *)
let rec norm p = 
  match p with
    Pint _ -> p
  |Prec (x,a)->
     let d = (Array.length a -1) in
     let n = ref d in 
       while !n > 0 && (eqP a.(!n) (Pint coef0)) do
	 n:=!n - 1;
       done;
       if !n < 0 then Pint coef0
       else if !n = 0 then a.(0) 
       else if !n = d then p
       else (let b=Array.make (!n+1) (Pint coef0) in
               for i=0 to !n do b.(i)<-a.(i);done;
               Prec(x,b))

(*----------------------------------------------------------------------------*)
(*** Ring aritmetic ***)
(*----------------------------------------------------------------------------*)

(* opposite *)
let rec oppP p =
  match p with 
      Pint a -> Pint (minus_coef a)
    |Prec(x,p1) -> Prec(x,Array.map oppP p1)


(* addition *)
let rec addP p q =
  let res =
    (match (p,q) with
	 (Pint a,Pint b) -> Pint (add_coef a b)
       |(Pint a, Prec (y,q1)) -> let q2=Array.map copyP q1 in
           q2.(0)<- addP p q1.(0);
           Prec (y,q2)
       |(Prec (x,p1),Pint b) -> let p2=Array.map copyP p1 in
           p2.(0)<- addP p1.(0) q;
           Prec (x,p2)
       |(Prec (x,p1),Prec (y,q1)) -> 
          if x<y then (let q2=Array.map copyP q1 in
                         q2.(0)<- addP p q1.(0);
                         Prec (y,q2))
          else if x>y then (let p2=Array.map copyP p1 in
                              p2.(0)<- addP p1.(0) q;
                              Prec (x,p2))
          else 
            (let n=max (deg x p) (deg x q) in 
             let r=Array.make (n+1) (Pint coef0) in
               for i=0 to n do
                 r.(i)<- addP (coef x i p) (coef x i q);
               done;
               Prec(x,r))) 
  in norm res


(* subtraction *)
let subP p q=addP p (oppP q)


let rec mult_cst a p =
  match p with
    |Pint c -> Pint (mult_coef a c)
    |Prec (x, t) -> Prec (x, Array.map (mult_cst a) t)

(* product of p by v^n, v <= max_var p *)
let rec multx n v p =
  match p with
      Prec (x,p1) when x=v -> let p2= Array.make ((Array.length p1)+n) (Pint coef0) in
        for i=0 to (Array.length p1)-1 do
          p2.(i+n)<-p1.(i);
        done;
        Prec (x,p2)
    |_ -> if p = (Pint coef0) then (Pint coef0) 
       else (let p2=Array.make (n+1) (Pint coef0) in 
               p2.(n)<-p;
               Prec (v,p2))


(* product *)
let rec multP p q =
  match (p,q) with
      (Pint a,Pint b) -> Pint (mult_coef a b)
    |(Pint a, Prec (y,q1)) ->
       if eq_coef a coef0 then Pint coef0
       else let q2 = Array.map (fun z-> multP p z) q1 in
         Prec (y,q2)
           
    |(Prec (x,p1), Pint b) ->
       if eq_coef b coef0 then Pint coef0
       else let p2 = Array.map (fun z-> multP z q) p1 in
         Prec (x,p2)
    |(Prec (x,p1), Prec(y,q1)) ->
       if x<y 
       then (let q2 = Array.map (fun z-> multP p z) q1 in
               Prec (y,q2))
       else if x>y
       then (let p2 = Array.map (fun z-> multP z q) p1 in
               Prec (x,p2))
       else Array.fold_left addP (Pint coef0)
         (Array.mapi (fun i z-> (multx i x (multP z q))) p1)


(* power *)
  let powP p i = 
    let rec pow_aux one p i =
    match i with
      | i when i < 0 -> invalid_arg "fast_power requires non-negative n"
      | 0 -> one (* "one" is used as product accumulator *)
      | i -> 
          let sq = multP p p in (* x contains the last square *)
            if (i mod 2) = 1 then pow_aux (multP one p) sq (i / 2)
            else pow_aux one sq (i / 2)
    in
      pow_aux p1 p i


let (@@) a b = multP a b

let (--) a b = subP a b

let (++) a b = addP a b

let (^^) a b = powP a b

(* Sum of the squares of the coefficents in the current variable *)
let sum_square_coefs p =
  match p with
    |Pint c -> Pint (mult_coef c c)
    |Prec (_, t) -> Array.fold_left (fun x y -> x ++ (y @@ y)) p0 t
(*----------------------------------------------------------------------------*)
(*** Evaluation ***)
(*----------------------------------------------------------------------------*)

(* (possibly partial) evaluation of p at a constant point a *)
let rec evalP p a =
  match p with
    |Pint c -> p
    |Prec (_, t) -> 
       let tmp = Array.mapi (fun i ti -> mult_cst (pow_coef a i) ti) t
       in Array.fold_left addP p0 tmp



(*----------------------------------------------------------------------------*)
(*** Truncations ***)
(*----------------------------------------------------------------------------*)

(* tail of a polynomial : removing the monomial in which the given
   var is of highest degree*)
let tailP v p =
  subP p (multP (lcoef v p) (powP (x v) (deg v p)))


(* list of truncations for subresultant elimination : 
   - if p = pnX^n + p' with p' = pn-1X^(n - 1) + .. + p0
   - trunc_list p = (l1, l2) where
   - if pn in a real constant then l1 = [p], l2 = []
   - else l1 = p' :: (trunc_list p').1 
   and l2 = pn :: (trunc_list p').2

   In other words, (trunc_list p').2 contains the first consecutif non
   constant coefficients in the current variable, an (trunc_list p').1
   the corresponding truncations of p, ie the actual forms p takes if
   these successive leading coefficients vanish.
*)
let trunc_list p =
  let rec aux_rec p resp resc = 
    match p with
      |Pint c -> 
         (* shall we do something special when c = 0 ? *)
         (p :: resp, resc)
      |Prec (x, t) -> 
         let n = Array.length t in
         let lcoef = t.(n - 1) in
           match lcoef with
             |Pint c ->
                if eq_coef c coef0 then failwith "Not In Normal Form"
                else (p :: resp, resc)
             |Prec (x1, t1) ->
                let ptail = Prec (x,  Array.sub t 0 (n - 1)) in
                  aux_rec ptail resp resc
  in
    
    aux_rec p [] []


(*----------------------------------------------------------------------------*)
(*** Translation : p (x + t), t is a coefficient ***)
(*----------------------------------------------------------------------------*)

let translateP p t =
  match p with
    |Pint c -> p
    |Prec (v, q) ->
       let tmp = Array.mapi (fun i ti -> (ti @@ (x v ++ (cf t))^^i)) q in
         Array.fold_left addP p0 tmp

(*----------------------------------------------------------------------------*)
(*** Dilatation : p (x + t), t is a coefficient ***)
(*----------------------------------------------------------------------------*)
let dilateP p t = 
  match p with 
    |Pint c -> p
    |Prec (v, q) ->
       let tmp = Array.mapi (fun i ti -> (ti @@ ((x v) @@ (cf t))^^i)) q in
         Array.fold_left addP p0 tmp

  (* X^d * P(1/X) where deg(P)=d, ie "reverse" of the polynomial *) 

(*----------------------------------------------------------------------------*)
(*** Reverse of a polynomial, is X^dP( 1 / X) ***)
(*----------------------------------------------------------------------------*)
let revP p =
  match p with
    |Pint c -> p
    |Prec (v, q) -> Prec (v, Array.of_list (List.rev (Array.to_list q)))
       
(*----------------------------------------------------------------------------*)
(*** Formal derivation ***)
(*----------------------------------------------------------------------------*)

(* v smaller than max_var p*)
let rec deriv v p =
  match p with 
      Pint a -> Pint coef0
    |Prec(x,p1) when x=v ->
       let d = Array.length p1 -1 in
         if d=1 then p1.(1)
         else
           (let p2 = Array.make d (Pint coef0) in
              for i=0 to d-1 do
		p2.(i)<- multP (Pint (coef_of_int (i+1))) p1.(i+1);
              done;
              Prec (x,p2))
    |Prec(x,p1)-> Pint coef0

(*----------------------------------------------------------------------------*)
(*** Divisibility ***)
(*----------------------------------------------------------------------------*)


(* computes (s,r) st p = s*q+r *)
let rec quo_rem_pol p q x =
  if x = 0
  then (match (p,q) with 
          |(Pint a, Pint b) -> (Pint (div_coef a b), cf (coef0))
	     (*if eq_coef (mod_coef a b) coef0
             then (Pint (div_coef a b), cf 0)
             else failwith "div_pol1"*)
	  |_ -> assert false)
  else 
    let m = deg x q in
    let b = lcoef x q in
    let q1 = tailP x q in (* q = b*x^m+q1 *)
    let r = ref p in
    let s = ref (cf coef0) in
    let continue = ref true in
      while (!continue) && (not (eqP !r (cf coef0))) do
	let n = deg x !r in
	  if n < m
	  then continue:=false
	  else (
            let a = lcoef x !r in
            let p1 = tailP x !r in  (* r = a*x^n+p1 *)
            let c = div_pol a b (x-1) in  (* a = c*b *)
	    let s1 = c @@ ((mon x (n-m))) in
              s:= addP (!s) s1;
              r:= p1 -- (s1 @@ q1);
          )
      done;
      (!s,!r)

(* fails if a does not divide p, alse returns the quotient *)
and div_pol p q x =
  let (s , r) = quo_rem_pol p q x in
    if eqP r (cf coef0) then s else failwith "div_pol2"

(* divides every coef of p by the cst a *)
let rec div_pol_int p a=
  match p with
      Pint b -> Pint (div_coef b a)
    |Prec(x,p1) -> Prec(x,Array.map (fun x -> div_pol_int x a) p1)


(* polynomial gcd, using subresultants *)

let rec gcdP p q =
  let x = max (max_var_pol p) (max_var_pol q) in
    gcd_pol p q x

and gcd_pol p q x =
  gcd_pol_rec p q x


and content_pol p x = 
  match p with
      Prec(v, p1) when v=x ->
        Array.fold_left (fun a b -> gcd_pol_rec a b (x-1)) (cf coef0) p1
    | _ -> p

and gcd_coef_pol c p x =
  match p with
      Prec(v,p1) when x=v ->
        Array.fold_left (fun a b -> gcd_pol_rec a b (x-1)) c  p1
    |_ -> gcd_pol_rec c p (x-1)
       
and gcd_pol_rec p q x =
  match (p,q) with
      (Pint a,Pint b) -> (*Pint (gcd (abs_coef a) (abs_coef b))*)
        Pint (div_coef a b)
    |_ -> if eqP p (cf coef0)
       then q
       else if eqP q (cf coef0)
       then p
       else if (deg x q) = 0
       then gcd_coef_pol q p x
       else if (deg x p) = 0
       then gcd_coef_pol p q x
       else (
	 let a = content_pol p x in
	 let b = content_pol q x in
	 let c = gcd_pol_rec a b (x-1) in
	   pr (string_of_int x);
	   let p1 = div_pol p c x in
	   let q1 = div_pol q c x in
	   let r = gcd_sub_res p1 q1 x in
	   let cr = content_pol r x in
	   let res = c @@ (div_pol r cr x) in
	     res
       )

(* Sub-résultants:

   ai*Ai = Qi*Ai+1 + bi*Ai+2

   deg Ai+2 < deg Ai+1

   Ai = ci*X^ni + ...
   di = ni - ni+1

   ai = (- ci+1)^(di + 1)
   b1 = 1
   bi = ci*si^di  si i>1
   
   s1 = 1
   si+1 = ((ci+1)^di*si)/si^di

*)
and gcd_sub_res p q x =
  if eqP q (cf coef0)
  then p
  else 
    let d = deg x p in
    let d' = deg x q in
      if d<d'
      then gcd_sub_res q p x
      else
	let delta = d-d' in
	let c' = lcoef x q in
	let r = snd (quo_rem_pol (((oppP c')^^(delta+1))@@p) (oppP q) x) in
	  gcd_sub_res_rec q r (c'^^delta) c' d' x
	    
and gcd_sub_res_rec p q s c d x =
  if eqP q (cf coef0) 
  then p
  else (
    let d' = deg x q in
    let c' = lcoef x q in
    let delta = d-d' in
    let r = snd (quo_rem_pol (((oppP c')^^(delta+1))@@p) (oppP q) x) in
    let s'= lazard_power c' s delta x in
      gcd_sub_res_rec q (div_pol r (c @@ (s^^delta)) x) s' c' d' x
  )

and lazard_power c s d x =
  let res = ref c in
    for i=1 to d-1 do
      res := div_pol ((!res)@@c) s x;
    done;
    !res


let square_free p x =
  if (deg x p) <= 1 then p
  else
    let p' = deriv x p in
      div_pol p (gcd_pol p p' x) x

(* For sake of compatibility, we reproduce here the code coming from
   the Coq implementation for subresultant coefficients and
   polynomial.
   The above implem of gcd shold be tested against an ocaml version
   of the extended subresultant pols based implem of the Coq, since
   the def or  subresultants slightlty changes *)

(* We follow BPR notations : 

   - srk (resp srk_1) is the kth (resp (k - 1)th) subres coef
   - psrk (resp psrk_1) is the kth (resp (k - 1)th) subres poly
   - dom_srk (resp srk_1) is the leading coef of the kth (resp (k -
   1)th subres poly
   
*)


let next_subres_coef j deg_psrj_1 dom_srj_1 srj var = 
  let t = j - deg_psrj_1 - 1 in
  let eps = 
    if ((t * (t + 1) / 2) mod 2 = 0) then p1
    else (oppP p1) in
    eps @@
      (powP (div_pol dom_srj_1 srj var) t) @@ dom_srj_1.
      
      
(* next subresultant polynomial in the chain. psrj_1 should not be zero*)
(* computes:
   - next subres pol
   - next subres coef
   - next pair of relevant index for further computation
*)      
let next_subres_pol psri_1 psrj_1 srj i j var = 
  let k = current_deg psrj_1 in
  let dom_srj_1 = current_lcoef psrj_1 in
  let dom_sri_1 = current_lcoef psri_1 in
  let next_psr_aux = fun x ->  
    oppP (div_pol
            (snd (quo_rem_pol (x @@ psri_1) psrj_1 var))
            (dom_sri_1 @@ srj) var)
  in
    if k = j - 1 then 
	(next_psr_aux (dom_srj_1 ^^ 2), dom_srj_1, j, k)
    else
      let srk = next_subres_coef j k dom_srj_1 srj var in
	(next_psr_aux (dom_srj_1 @@ srk), srk, j, k)
          
(* list of polynomial subresultants in the chain issued form a and b.*)
(* var should be the current variable, for instance the one to be
   eliminated *)

let pol_subres_list a b var =
  let dega = current_deg a in
  let rec aux_rec x y c i j = 
    let (psr,sr,k,l) = (next_subres_pol x y c i j var) in
      if (is_zero psr) then []
      else psr :: (aux_rec y psr sr k l)
      in
        a :: b :: aux_rec a b p1 (dega + 1) dega
 
(* list of subresultant coefficients  in the chain issued form a and
   b.
   var should be the current variable, for instance the one to be
   eliminated
   there is may be a more clever way of computing these from a
   recurrence formula *)


let subres_coef_list a b var = 
  map current_lcoef (pol_subres_list a b var)

