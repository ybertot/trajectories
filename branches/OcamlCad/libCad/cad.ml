open Core
open Poly
open Bern


(* Subresultant elimination of the current leading variable, following BPR *)

(* - Each element of llP is the list of truncations of a poly in the
   initial list lP, candidate for elimination of the current variable X.
   In other words, flattening llP gives trunc (lP).
   - computes a the list of sr_j(R, dR / dX) for all R in trun(lP)
*)


let rec subres_coef_der_list llP res var = 
  match llP with
    |[] -> []
    |lP :: llP' ->
       let rec aux_rec (l : poly list)(res : poly list) =   
	 match l with
	   | [] -> res
	   | p :: l' ->
	       aux_rec l' (subres_coef_list p (deriv var p) var) @ res
       in
         aux_rec lP (subres_coef_der_list llP' res var)


(* - Each element of llP is the list of truncations of a poly in the
   initial list lP, candidate for elimination of the current variable X.
   In other words, flattening llP gives trunc (lP).
   - computes a the list of sr_j(R, S) for all R S distincts in trun(lP)
*)

let rec subres_coef_al_list llP res var =
  match llP with
    |[] -> res
    |lP :: llP' ->
       match llP' with
         |[] -> res
	 |lQ :: _ ->
  let rec subres_peer peer_res u v  = 
    match u with
      |[] -> peer_res
      |r :: u' ->
    let dr = deg var r in
    let subres  = fun x ->
      let dx = deg var x in
        if dr < dx then subres_coef_list x r var
        else subres_coef_list r x var
    in
      subres_peer ((flat_map subres v) @ res) u' v 
  in
    subres_coef_al_list llP' 
      ((flat_map (subres_peer [] lP) llP') @ res)
      var

(* Projection of the family l of polys by subresultant elimination.
  Multiple occurences are cleaned *)

let elim l var = 
  let pol_trunc_lead_coef_lists = List.map trunc_list l in
(* list of lists of successive trunctions for each poly in l *)
  let pol_trunc_list = List.map fst pol_trunc_lead_coef_lists in
(* list of lists of successive possibly vanishing lead coefs for each
  poly in l 
*)
  let lead_coef_list = flat_map snd pol_trunc_lead_coef_lists in
(* list of subres coefficients with derivatives, accumulating the
       leading coefs in the result *)
  let subres_coef_der_list_l = 
    subres_coef_der_list pol_trunc_list lead_coef_list var in
(* complete elimination family, removing possible dupilcates *)
    clean_list eqP 
      (subres_coef_al_list pol_trunc_list subres_coef_der_list_l var)


(* Cauchy bounds for the roots of a univariate polynomial: *)
(* if p(X) = p0 + ... + pnX^n, c(P) = (n + 1) * \sum_i p_i^2 / pn^2 *)
(* majorizes the absolute value of the roots of p *)

(* Cauchy bound for the univariate pol p(z)(x) where z \in R^n is an
   algebraic point.

   We compute an approximation for c(p(z)) and keep the lower bound
   if it is an interval, hoping that it is positive*)


let cauchy_bound z p = 
  let s = sum_square_coefs p in 
  let dp = current_deg p in
  let lc = current_lcoef p in
  let satz = approx_of_pol_at_spoint z s in
  let lcatz = approx_of_pol_at_spoint z lc in
  let res = mult_approx_num 
    (div_approx satz lcatz) (coef_of_int (dp + 1)) in
    match res with
      |Exact e -> 
         if coef_sign e <> 1 then failwith "Bug, from cauchybound"
         else e 
      |Int (a, _) ->
         if coef_sign a = -1 then failwith "Root bound non positive"
         else a
 
(* Each sample point in R^n comes with a list of pairs (p, s), where
   p \in R[x1, ..., xn] and sign (p(z)) = s *)
type sign_col = (poly * sign) list

let rec sign_find p col = 
  match col with
    |[] -> raise NotFound
    |ps :: l -> 
       let (p1, s1) = ps in 
         if eqP p1 p then s1 
         else sign_find p l

(* p(z)(x) can have a smaller degree than the one of p in x, if some
   consecutive leading coefficients of x vanish at z. Fortunately, all
   these coefficients are in the eliminating familly, above a given
   sample point, their sign is known *)

(* Non degenerated form of p(z)(x) above sample point z. s is the
   sign col for the elim family at sample point z  *)
let non_deg_pol z sz p = 
  match p with
    |Pc _ -> p
    |Prec (x, t) -> 
       (* list of coefs of p, leading first *)
       let lt = List.rev (Array.to_list t) in
       let rec skip_vanishing l =
         match l with 
           |[] -> []
           |lc :: tl -> 
              match lc with
                |Pc c -> if eq_coef c coef0 then skip_vanishing tl
                  else l
                |Prec (_, _) ->
                   let s = sign_find lc sz in
                     if s = Zero then skip_vanishing tl
                     else if s = Unknown then 
                       failwith "Unknown sign in output cad!"
                     else l
       in
       let lres = skip_vanishing lt in
         match lt with
           |[] -> p0
           |_ -> Prec (x, Array.of_list (List.rev lres))



(* Sign of NON DEGENERATED polynomial p(z)(x) at -infty, simply obtained
   from the parity of the degree, and the sign of the leading coefficient
let sign_at_minfty z p =
  let n = current_deg p in
    if n mod 2 = 0 then Pos else Neg
 *)
type cad_output = 
    Leaf of sample_point * sign_col | Node of cad_output array
