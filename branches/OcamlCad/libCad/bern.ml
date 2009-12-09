open Core
open List
open Poly

exception IllFormedPoly
exception MoreThanOneVar
(*----------------------------------------------------------------------------*)
(***  Bernstein coefficients ***)
(*----------------------------------------------------------------------------*)

(* Initialisation of the computation of bernstein coefficients:
   computes the coefficients of p in the bern basis of degree n with
   parameters a and b, ie over inteval ]a,b[.
   Result is an array, with should be of length n + 1 *)
let bern_init p n a b =
  let q = translateP (revP (dilateP (translateP p a) (sub_coef b a))) coef1 in
  let ares =
    match q with
      |Pc c -> let t = Array.make (n + 1) p0 in t.(0) <- (cf c); t
      |Prec (_, t) -> 
         Array.mapi (fun i ti -> div_pol_int ti (coef_of_int (binomial n i))) t
  in
    Array.to_list ares

(* de Casteljau algorithm: we first compute the next diagonal in the
   Pascal triangle:
   - intuition is that e \in ]c, d[ but corectness does not require
   c < e < d, only e distinct from c and d 
   - b :: diag is a diagonal already computed in the triangle *)
let  next_diag_bern c d e diag b =
  (* alpha = (d - e) / (d - c) *)
   let alpha = div_coef (sub_coef d e) (sub_coef d c) in
     (* beta = (e - c) / (d - c) *)
   let beta = div_coef (sub_coef e c) (sub_coef d c) in
   let rec next_diag_bern_aux diag b = 
     match diag with
       |[] -> [b]
       |hd :: tl -> 
          let l = next_diag_bern_aux tl b in
            match l with
	      |[] -> [] (*should never happen*)
	      |rhd :: rtl ->
	         ((mult_cst alpha hd) ++ (mult_cst beta rhd)) :: l
   in next_diag_bern_aux diag b

(* Main function : from blist a list of bern coefs in the basis
   (lenght blist) with parameters c d, and e a rational distinct from
   c and d, computes (a pair of) two lists of bern coefs, in basis
   (length blist)
   respectively with parameters c, e and e, d. *)
let bern_split blist c d e = 
  let rec bern_split_aux blist b' b'' =
    match blist with
      |[] -> (b', b'')
      |hd :: tl -> 
         let next_b'' = next_diag_bern c d e b'' hd in
           match next_b'' with
             |[] -> ([], []) (* should never happen *)
             |hd'' :: tl'' -> bern_split_aux tl (hd'' :: b') next_b'' in    
  let (b', b'') = bern_split_aux (List.rev blist) [] [] in
    (b', List.rev b'')


(*----------------------------------------------------------------------------*)
(***  Sample points, algebraic numbers encoding ***)
(*----------------------------------------------------------------------------*)


(* We encode a real algebraic number z by:
   - a pair of rational a, b
   - a polynomial p
   - the list of bernstein coefficients of p in basis (deg p) with
   parameters a and b *)
type alg = {
   lbound : coef;
   rbound : coef;
   pannul : poly
}

(* A sample point in the _one dimensional_ cad output is either:
   - a rational point, witness for the mandatory minus infty component
   - or a rational point, discovered as root of a polynomial
   - or an algebraic point
   - or a rational point, witness for an intervall cell
   We do not need a flag for plus infty, treated as the last category.
*)

type sample_point1 =
  |Minf of coef
  |Rroot of coef
  |Aroot of alg
  |Between of coef

(* A sample point in the _upper dimensional_ cad output, ie witnessing
   a partition of |R^n is an array of
   size n filled with sample_point1. Several invariants for
   coordinates of such an array t being in the category Aroot : 
   if t.i = Alg (ai, bi, pi, bli) is the (i + 1)th coordinate of z, then:
   - ai < zi+1 < bi
   - pi has (i + 1) variables
   - z1 is the unique root of p0 in ]a0, b0[
   - zi+1 is the unique root if pi(z1,...zi) in ]ai, bi[
*)

type sample_point = sample_point1 list


(*----------------------------------------------------------------------------*)
(***  bounds on polynomial values ***)
(*----------------------------------------------------------------------------*)

(* a real point is either known by its exact value or bounded *)
type approx = Exact of coef | Int of coef * coef

(* approx from a sample_point1 *)
let approx_of_sample_point1 z = 
  match z with
    |Minf m -> Exact m
    |Rroot r -> Exact r
    |Between b -> Exact b
    |Aroot a -> Int (a.lbound, a.rbound)

let add_approx a1 a2 =
  match a1, a2 with
    |Exact e1, Exact e2 -> Exact (add_coef e1 e2)
    |Exact e1, Int (a2, b2) -> 
       let (a, b) = (add_int_num (a2, b2) e1) in Int (a, b)
    |Int (a1, b1), Exact e2  -> 
       let (a, b) = (add_int_num (a1, b1) e2) in Int (a, b)
    |Int (a1, b1), Int (a2, b2) -> 
       let (a, b) = (add_int (a1, b1) (a2, b2)) in Int (a, b)

let mult_approx a1 a2 =
  match a1, a2 with
    |Exact e1, Exact e2 -> Exact (mult_coef e1 e2)
    |Exact e1, Int (a2, b2) -> 
       let (a, b) = (mult_int_num (a2, b2) e1) in Int (a, b)
    |Int (a1, b1), Exact e2  -> 
       let (a, b) = (mult_int_num (a1, b1) e2) in Int (a, b)
    |Int (a1, b1), Int (a2, b2) -> 
       let (a, b) = (mult_int (a1, b1) (a2, b2)) in Int (a, b)

let mult_approx_num a x =
  match a with
    |Exact e -> Exact (mult_coef e x)
    |Int (a, b) -> 
       let (ra, rb) = (mult_int_num (a, b) x) in Int (ra, rb)

let pow_approx a i = 
  match a with
    |Exact e -> Exact (pow_coef e i)
    |Int (a, b) -> 
       let (a', b') = pow_int (a, b) i in
         Int (a',b')

let div_approx a1 a2 =
  match a1, a2 with
    |Exact e1, Exact e2 -> Exact (div_coef e1 e2)
    |Exact e1, Int (a2, b2) -> 
       let (a, b) = (div_int_num (a2, b2) e1) in Int (a, b)
    |Int (a1, b1), Exact e2  -> 
       let (a, b) = (div_int_num (a1, b1) e2) in Int (a, b)
    |Int (a1, b1), Int (a2, b2) -> 
       let (a, b) = (div_int (a1, b1) (a2, b2)) in Int (a, b)
      
(* A sample point defines a box (which might be flat in certain
   dimension, where the exact, rational, value of the coordinate is
   known). Hence we can approx the values of a polynomial evaluated at a
   sample point by naive interval arithmetic. *)


(* Extracts the array of constant coefs from a pol with one variable
   exactly, fails otherwise *)
let coefs_of_svarpol p =
  let extract pi =
    match pi with
      |Pc c -> c
      |_ -> raise MoreThanOneVar
  in
    Array.map extract p

(* - t should be an array of Pc _, coding a pol in one var,
   otherwise, an excpt is raised
   - x is this variable
   - z is a sample point
   - computes bounds for the pol t.(i) x^i at zi
*)
let approx_of_svarpol_at_spoint1 a1 pt =
  let t = coefs_of_svarpol pt in
  let eval_mon_at_a1 = 
    match a1 with
      |Exact a ->  fun i ti ->  Exact (mult_coef ti (pow_coef a i))
        |Int (a, b) -> 
           fun i ti -> 
             let (a', b') = mult_int_num (pow_int (a, b) i) ti in 
               Int (a', b')
  in
  let tmp = Array.mapi eval_mon_at_a1 t in
    Array.fold_right add_approx tmp (Exact coef0)
      
(* - t is an array of recursively computed approx, coding a poly with
   approx coefficients
   - a1 is an approx
   - computes the resulting approx of p = t.(i)x^i at a1
*)
let approx_of_approx_pol_at_approx t a1 = 
  let eval_mon_at_a1 i ti = mult_approx (pow_approx a1 i) ti in
  let tmp = Array.mapi eval_mon_at_a1 t in
    Array.fold_right add_approx tmp (Exact coef0)

(* Computation of the approx value of p at z a sample point *)
let rec approx_of_pol_at_spoint z p = 
  match p with
    |Pc c -> Exact c
    |Prec (x, t) ->
       match z with
         |[] -> failwith "ill formed (empty?) sample point"
         | _ -> 
             let z1 = nth z x in
             let a1 = approx_of_sample_point1 z1 in
             let res = 
               (* p has a single variable *)
               try  (approx_of_svarpol_at_spoint1 a1 t)
               with MoreThanOneVar ->
                 (* p has more variables *)
                 let trec = Array.map (approx_of_pol_at_spoint z) t in
               approx_of_approx_pol_at_approx trec a1
             in res


(*----------------------------------------------------------------------------*)
(***  caching hash tables ***)
(*----------------------------------------------------------------------------*)

(*!!!! In case of big ints we should explicitely build the interfaces
  for these poly and coef based keys, since syntactic equality is not
  what we want *)

(* Cache for approx computed values of a polynomial at a sample point
let hvalP = (Hashtbl.create 12345 : (poly * sample_point, approx) Hashtbl.t)
*)

(* Cache for the bernstein coefficients of a polynomial *)
let bern_htbl = (Hashtbl.create 12345 : (poly, coef * coef * poly list) Hashtbl.t)

(* Cache for square free parts of polys *)
let square_free_htbl = (Hashtbl.create 12345 : (poly, poly) Hashtbl.t)

(* Cache for gcds of polys *)
let gcd_htbl = (Hashtbl.create 12345 : (poly * poly, poly) Hashtbl.t)
(*----------------------------------------------------------------------------*)
(***  caching functions ***)
(*----------------------------------------------------------------------------*)


(* Gets the square free part of poly p
   - first asking the hash table
   - if not already stored in the hastable, then computes, stores and return
   the value. Note that if the computation is not trival (deg <= 1),
   the result is also stored in the gcd table *)

let hsqfreeP p =
  let res = try Hashtbl.find square_free_htbl p with
      NotFound ->
        match p with
          |Pc _ -> p
          |Prec(x, _) ->
             if (deg x p) <= 1 then p 
             else
               let p' = deriv x p in
                 div_pol p (gcd_pol p p' x) x 
  in
    Hashtbl.add gcd_htbl ((p, p'), res);
    Hashtbl.add square_free_htbl p res; 
    res

(* alg constructor. we ensure the polynomial is always square free *)
let mk_alg a b p = {lbound = a; rbound = b; pannul = hsqfreeP p}


(* Gets the gcd of two polynomials
   - first asking the hashtable
   - if not already stored in the hastable, then computes, stores and return
   the value. *)
let gcd_htbl p q =
  let res = try Hashtbl.find gcd_htbl (p, q) with
      NotFound ->
        let g = gcdP p q in
          Hashtbl.add gcd_htbl (p, q) g; 
          g


(* Gets the value of poly p at sample_point z :
   - first asking the hash table
   - if not already stored in the hastable, then computes, stores and return
   the value *)
(*
let happroxP p z =
  let res = try Hashtbl.find hvalP (p, z) with
      NotFound -> let a = approx_of_pol_at_spoint z p in
        Hashtbl.add hvalP (p, z) a; a
  in res
*)
(* Gets the coef of poly p in the bernstein basis of degree the
   current degree of p and parameter a b, by
   - first asking the hash table
   - if not found, then
   1) Looks in the table for the first list of coefs with parameter
   (a, _). If there is one, use these coefs to split them and take the
   first resuling list; else:
   2) Looks in the table for the first list of coefs with parameter
   (_, b). If there is one, use these coefs to split them and take the
   second resuling list
   3) else initializes a bernstein computation

*)

let hbern_coefsP p a b =
  if Hashtbl.mem bern_htbl p then 
    let llb = Hashtbl.find_all bern_htbl p in
    let lints = List.map (fun (x, y, _) -> (x, y)) llb in
      (* warning lint is listed twice, which is too much *)
      if List.mem (a, b) lints  then
        let n = find_at lints (a, b) in
        let (_,_, res) = (List.nth llb n) in 
          res
      else 
        let llbounds = List.map fst lints in
          if List.mem a llbounds then 
            let n = find_at llbounds a in
            let (_, c) = List.nth lints n in
            let (_, _, bl) = List.nth llb n in
            let (bll, blr) = bern_split bl a c b in
              Hashtbl.add bern_htbl p (a, c, bll); 
              Hashtbl.add bern_htbl p (c, b, blr); 
              bll
          else
        let lrbounds = List.map snd lints in
          if List.mem b lrbounds then 
            let n = find_at lrbounds b in
            let (c, _) = List.nth lints n in
            let (_, _, bl) = List.nth llb n in
            let (bll, blr) = bern_split bl a c b in
              Hashtbl.add bern_htbl p (a, b, bll); 
              Hashtbl.add bern_htbl p (c, b, blr); 
              blr
          else
            let lb = bern_init p (current_deg p) a b 
            in Hashtbl.add bern_htbl p (a, b, lb); lb
  else 
    let lb = bern_init p (current_deg p) a b
    in Hashtbl.add bern_htbl p (a, b, lb); lb
        
(* bl is the bernstein coefficients of p with parameter a, b.
   returns the pair of new bernstein coefficients of p with parameters
   a and c, and c and b, and stores the results in the table *) 
let hbern_splitsP p a b c bl = 
  let llb = Hashtbl.find_all bern_htbl p in
  let lints = List.map (fun (x, y, _) -> (x, y)) llb in
    (* warning lint is listed twice, which is too much *)
    (* first case: both coef lists are already in the table *)
    if (List.mem (a, c) lints) && (List.mem (c, b) lints)  then
      let n = find_at lints (a, c) in
      let m = find_at lints (c, b) in
      let (_, _, b') = List.nth llb n in
      let (_, _, b'') = List.nth llb m in
            (b', b'')
    (* else we need a bern_split *)
    else
      let (bll, blr) = bern_split bl a b c in
        Hashtbl.add bern_htbl p (a, c, bll); 
        Hashtbl.add bern_htbl p (c, b, blr); 
        (bll, blr)
          

(* we recursively define:
   - the refinement of a sample poin. Refinement recursively affects all the
   algebraic coordinates of sp by halving them
   - with the determination of the sign of poly p at a sample point sp

   Warning, not tail rec, but the number of variables, hence the
   length of the list sp should unfortunately never exceed 10...
*)

(*
let rec sample_point_refine sp =
  match sp with
      [] -> []
    |z :: sp_tl ->
       (* recursively refined tail *)
       let ref_sp_tl = sample_point_refine sp in
       match zp with
         |Minf c -> z :: sample_point_refine sp_tl
         |Rroot r -> z :: sample_point_refine sp_tl
         |Between b -> z :: sample_point_refine sp_tl
         |Aroot alg ->
            let a = alg.lbound in
            let b = alg.rbound in
            let p = alg.pannul in
            let mid = middle a b in
            let smid = pol_sign_at (Root smid)::[] p in
              (* first case: the mid is the exact value of the root *)
              if smid = 0 then (Root smid) :: ref_sp_tl
              (* second case: we have to halve ]a b[*)
              else
                let lb = hbern_coefsP p a b in
                let (b', b'') =  hbern_splitsP p a b mid in
                  (* recursive call to pol_sign_at to compute
                     the sign of the coefficients we pass along
                     ref_sp_tl so that it gets more and more refined *)
                let (ref_sp_tl', nsc') = sign_changes ref_sp_tl b' in
                  (* we know that either nsc' or nsc'' is 1 *)
                  if nsc' = 1 then (mk_alg a mid p) :: ref_sp_tl'
                  else (mk_alg mid b p) :: ref_sp_tl'

(* sign changes in a list obtained by mapping evaluation at sample
   point sp over the list of polynomials lp.
   returns a pair (sp', n), n is the number of sign changes in the list
   of poly l evaluated at sp, and sp' is a refinement of sp.
   That one could be defined outside, not in a mutually recursive way but we
   put it her for sake of readability *)
and sign_changes sp lp =
    match sp with
      |[] -> 
         (* base case, polynomials in lp should all be constants, no
   refinement here *)
         (* sign of a constant pol *)
         (let sign_of_cst_poly p =
            match p with
              |Prec c -> coef_sign c 
              | _ -> raise IllFormedPoly
          in
           (* recursive count of sign changes, without refinement.
              returns res + number of sign changes in x :: l, for an
              x with sign sx *)
          let rec sign_count_rec ll sx res =
            match ll with
              |[] -> res 
              |y :: tl -> 
                 let sy = sign_of_cst_poly y in
                   if sy = 0 then
                     sign_count_rec tl sx res
                   else if sx = sy then sign_count_rec tl sy res
                   else sign_count_rec tl sy (1 + res)
          in
            match lp with
              |[] -> ([], 0)
              | x :: tl -> 
                  let sx = sign_of_cst_poly x in 
                    ([], sign_count_rec tl sx 0))
      |_ ->
         (* recursively computes (sp', n), where n is res.1 + the
            sumber of sign changes in the values of polys in ll
            evaluated at res.2 and sp' is a refinement of sp.2 *)
         (let rec sign_count_rec ll sx res =
            match ll with
              |[] -> res
              | y :: tl ->
                  let (sp_res, n_res) = res in
                  let (sp_res', sy) = pol_sign_at sp_res y in
                    if sy  = 0 then sign_count_rec tl sx (sp_res', n_res)
                    else if sx = sy then sign_count_res tl sy (sp_res', n_res)
                    else sign_count_rec tl sy (sp_res', n_res + 1)
          in
            match lp with
              |[] -> ([], 0)
              | x :: tl -> 
                  let sx = pol_sign_at sp x in 
                    ([], sign_count_rec tl x (sp, 0)))
         )
(* determination of the sign of p(sp). possibly refines sp
   hence computes a (sp' ,  s) where sp' resfines sp and s is
   -1, 0, or 1, the sign of p at sp.
   First case: sp is in fact a root of p. Second case: it is not.
   To discriminate the two cases, we need to compute bernstein coefs
   for some gcds.
   In the second case, the approx p(sp) is refined, untill its
   rational bounds have the same sign, which is the sign of p(sp).
 *)
and pol_sign_at sp p = 
    match p with
        (* trivial case of a constant pol *)
      |Pc c -> coef_sign c
      | _ -> 
          (* non trivial polynomial *)
          match sp with
            |[] -> failwith "empty sample point ?"
            |sp1 :: sptl ->
               (* recursive case : a non triv pol and a non triv
                  sample point:
                  - in the three first cases, sp1 is a rational
                  constant. the partial eval of p with xn+1 = sp1
                  leads to a simple recursive call *)
               match sp1 with
                 |Minf c ->
                    let pc = evalP p c in pol_sign_at sptl pc
                 |Rroot r ->
                    let pr = evalP p r in pol_sign_at sptl pr
                 |Between b ->
                    let pb = evalP p b in pol_sign_at sptl pb
                 |Aroot alg ->
                    (* recursive case : a non triv pol and a non triv
                       sample point:
                       - in the last case, sp1 is an algebraic
                       point. *)
                    let lb = alg.lbound in
                    let rb = alg.rbound in
                    let palg = alg.pannul in
                      (* we need to decide whether p (sp) = 0 or
                         not. p(sp) = 0 iff sp1 is a common root to
                         p(sptl) and palg(sptl), ie if g(sp) has a
                         root in ]lb, rb[, where g = gcd (p,
                         palg). Since multiplicity does not affect the
                         result of root counting, we use the square free parts
                         of the polys involved in bern computations *)
                    let palg_bar = hsqfreeP palg in
                    let p_bar = hsqfreeP p in
                    let g = gcd_htbl palg_bar p_bar in
                    let dg = current_deg  g in
                    let gbl = hbern_coefsP g lb rb in
                    let (sptl', nsc_gbl) = sign_changes sptl gbl in
                      (* first case : g has no root in ]lr, br[ : 
                         we refine the approx of p (sp) until the
                         bounds have the same sign, which is the sign
                         of p (sp)*)
                      if nsc_gbl = 0 then 
                        let psp = approx_of_pol_at_spoint sp p in
                          match psp with
                            |Exact x -> coef_sign x
                            |Approx (xa, xb) ->
                               if xa = 0 then (sptl',1)
                               else if xb = 0 then (sptl', -1)
                               else if coef_sign (coef_mlut xa xb) = 1
                               then (sptl', coef_sign xa)
                               else 
                        (* second case : g has 1! root in ]lr, br[ :
                           p(sp) is zero *)
                      else if nsc_gbl = 1 then 
                        (* third case : we don't know yet how many
                           roots g has in ]lr, br[, we refine sp and
                           repeat the sign determination process *)
                      else 
*)
