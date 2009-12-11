open Core
open Poly
open Bern

(***************************************************************************)
(* Subresultant elimination of the current leading variable, following BPR *)
(***************************************************************************)


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

(***************************************************************************)
(*                        Root isolation                                   *)
(***************************************************************************)

(** datatype for cad output **)
 
(* Each sample point sp in R^n comes with a list of pairs (p, s), where
   p \in R[x1, ..., xn] and sign (p(sp)) = s *)

type sign_col = (poly * sign) list

let rec sign_find p col = 
  match col with
    |[] -> raise NotFound
    |ps :: l -> 
       let (p1, s1) = ps in 
         if eqP p1 p then s1 
         else sign_find p l

type cad_output = 
    Leaf of sample_point * sign_col | Node of cad_output list

(** First step : find an interval of finite length containing all the
   roots of a polynomial **)

(* Cauchy bounds for the roots of a univariate polynomial: *)
(* if p(X) = p0 + ... + pnX^n, c(P) = (n + 1) * \sum_i p_i^2 / pn^2 *)
(* majorizes the absolute value of the roots of p *)

(* Cauchy bound for the univariate pol p(z)(x) where z \in R^n is an
   algebraic point.

   We compute an approximation for c(p(z)) and keep the lower bound
   if it is an interval, hoping that it is positive. 

   If m = cauchy_bound sp p, then the roots of p(sp, x) ar in ]-m, m[ *)
let cauchy_bound sp p = 
  let s = sum_square_coefs p in 
  let dp = current_deg p in
  let lc = current_lcoef p in
  let satz = approx_of_pol_at_spoint sp s in
  let lcatz = approx_of_pol_at_spoint sp lc in
  let cauchy = mult_approx_num 
    (div_approx satz lcatz) (coef_of_int (dp + 1)) in
  let res = add_approx_num cauchy coef1 in
    match res with
      |Exact e -> 
         if sign_coef e <> 1 then failwith "Bug, from cauchybound"
         else e 
      |Int (a, _) ->
         if sign_coef a = -1 then failwith "Root bound non positive"
         else a

(** Second step, find the normal form of a polynomial with algebraic
    coefficients, obtained as a partial evaluation p(sp, x), where sp
    is a sample point.
    Indeed p(st)(x) can have a smaller degree than the formal 
    one of p in x, if some
    consecutive leading coefficients of x vanish at z. Fortunately, all
    these coefficients are in the eliminating family, and above a given
    sample point sp, their sign is recursively known **)

(* Non degenerated form of p(z)(x) above sample point z. s is the
   sign col for the elim family at sample point sp  *)
let non_deg_pol sp sign p = 
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
                   let s = sign_find lc sign in
                     if s = Zero then skip_vanishing tl
                     else if s = Unknown then 
                       failwith "Unknown sign in output cad!"
                     else l
       in
       let lres = skip_vanishing lt in
         match lt with
           |[] -> p0
           |_ -> Prec (x, Array.of_list (List.rev lres))


(** Third step: real root isolation process **)

(* Sign at -infinity of the univariate pol p(sp, x). There are at
   least two ways of computing this sign:
   - normalize p above sp, then compute the sign of its leading coef
   and deduce the sign at -infty from this sign and the parity of the
   degree of p above sp 
   - evaluate p at a point p(sp, m), when m is smaller than
   -cauchybound (p(sp, x)).
   Here we use the second method. *)

(* This is probably not the form we will use *)
let sign_at_minfty sp p =
  let m = minus_coef (cauchy_bound sp p) in
    pol_sign_at (Minf m :: sp) p

(* Initialization : computes from scratch a list of 1dim sample points
   describing the roots of p(sp, x) in the interval ]c, d[, given the
   sign column corresponding to the sample sp in the recursivelly
   computed cad and bl the list of bernstein coefs of p with  param c
   and d.
   Result is a pair (sp', l) where sp' refines sp and l is a list of
   pairs of the form (sp1, (p, s)), where sp1 is a sample_point1, p
   is the argument and s = sign (p (sp, s)) *)

(* This is a VERY BAD code, since during this process we compute most of the signs of P
   between its roots but forget about them and later recompute them
   by evaluation... Yet the semantic is somehow simpler*)
let root_isol_int sp p c d bl =
  let rec root_isol1_rec p c d bl res = 
      (* refinement of the input sample point and 1dim sample points
         accumulated so far *)
    let (sp_res, l_res) = res in
      if lt_coef c d then (sp_res, [])
      else
        (* number of sign changes in the list of bern coefs at sp *)
        let (sp', test) = sign_changes sp_res bl in
          (* further split result *)
        let split_case = 
          let mid = middle c d in
          let (bl', bl'') = hbern_splitsP p c d mid bl in
          let (midsp', sP_mid) = pol_sign_at (Between mid :: sp_res) p in
          let sp' = List.tl midsp' in
          let (sp'', l_res') = root_isol1_rec p c mid bl' (sp', l_res) in
          let l_res'' = 
            (* if we've found a root at mid, we push it in l_res' *)
            if sP_mid = 0 then (sp'', (Rroot mid, (p,0)) :: l_res') else (sp'', l_res') in
              root_isol1_rec p mid d bl'' l_res'' in            
            (* 1st case: 0 sign change, ie no root for p(sp, x) in ]c,d[ *)
            if test = 0 then (sp',  l_res)
              (* 2nd case: 1 sign change *)
            else if test = 1 
            then
              let (csp', sP_c) = pol_sign_at (Between c :: sp_res) p in
              let sp' = List.tl csp' in
              let (dsp'', sP_d) = pol_sign_at (Between d :: sp') p in
              let sp'' = List.tl dsp'' in
              let sP_cP_d = sP_c * sP_d in
                (* case 2a) : 1! sign change + p(sp,c)p(sp,d) < 0:
                   1! root of p in ]c,d[*)
                if sP_cP_d = -1 then 
                  let aroot = mk_alg c d p in
                    (sp'', (Aroot aroot, (p, 0))::l_res)
                      (* case 2b) : 1! sign change + p(sp,c)p(sp,d) >= 0; split again *)
                else split_case
                  (* 3rd case: more sign changes: we need to split further (same as case 2b) *)
            else split_case in
    root_isol1_rec p c d bl (sp, [])
      
      
(* sc is the sign col already computed at the sample point sp. returns
   (sp', sc'), where sp' refines sp and sc' = sign ( q(sp)) :: sc *)
let sign_col_cons sp q sc = 
  let (sp', sq) = pol_sign_at sp q in
   (sp', (q, sq) :: sc)
     
(* - b is a rational constant between two consecutive roots r1 and
        r2 : r1 < b < r2.
   - sp is a sample point
   - sc is the sign column computed at r1 :: sp
   - computes (sp', sc') where sp' refines sp and sc' is the
        sign_column at b :: sp (r2 is not needed)
   This is ugly: ultimately this function should disappear since the
        information it
   returns has already been computed at isolation time. cf previous
   comment *)
let between_sign_col sp b sc =
  let rec aux_rec sp sc res =
    match sc with
      |[] -> (sp, res)
      |shd :: stl -> 
         let (p, psign) = shd in
           if psign = 0 then 
             let (sp', psignb) = pol_sign_at ((Between b) :: sp) p in
               aux_rec sp' stl ((p, psignb) :: res)
           else
             aux_rec sp stl (shd :: res)
  in aux_rec sp sc []

(** A sign table above a sample point sp is a list of pairs (sp1, l) where sp1 is a
    samplepoint1, and l a list of pairs (p, s) where s is sign (p (sp,
    sp1)) **)

(*
  Sign table for the family p :: lp over interval ]low, up[, above
  sample point sp.
  p(low) has sign lowsign, p(up) has sign upsign, low and up are not
  roots  of p, and lp_stbl is the already
  computed sign table of family lp over ]low, up[ and above sp.
  bl are the bern coefs of p with param low and up.
  This function inserts the roots of p in the sign table l, and
  updates the sample points(1) in between.
  Result is a pair (sp', t) where sp' refines sp and t is the sign
  table.
  In t, samplepoint1 come in decreasing order.
*)

(*
let add_root p lp sp lp_stbl low up lowsign upsign bl = 
  let rec add_root_rec sp lp_stbl low up lowsign upsign bl =
    match lp_stbl with
      |[] -> (sp, [])
      |sp1_sc :: stbl_tl ->
         (* sc is a pair: a samplepoint1 and a sign_col *)
         let (sp1, sc) = sp1_sc in
           match sp1 with               
               (* Minf x and Between x cases : the polys in lp have a
                  constant sign over ]low, up[ *)
             |Minf _ ->
                let (sp', p_list) = root_isol_int sp p low up bl in
                  (sp', 
                   (add_to_cst_list p_list sc)++
                     [(Minf low, (p, low) ):: sc])
             |Between _ ->
                let (sp', p_list) = root_isol_int sp p low up bl in
                  (sp', 
                   (add_to_cst_list p_list sc)++
                     [(Between low, (p, low) ):: sc])
                (* Now the root cases *)
             |Rroot r ->
                let (lb', lb'') = hbern_splitsP p low up r bl in
                  (* low < up <= r : up is not relevant, we extend
                     the domain to ]low, r[*)
                if (le_coef up r) then 
                  let (sp', low_r_sc) = 
                    add_roots_rec sp stbl_tl low r lowsign upsign bl' in
                    (sp', (sp1, (p, upsign)) :: low_r_sc)
                   (* low < r < up *)
                else
                  let (sp', sp_r) = pol_sign_at (Root r :: sp) p in
                  let (sp'', p_list_r_up) = 
                    root_isol_int sp' p r up lb'' in
                  let update_sc = 
                    fill_sign_between sp (middle r up) sc in
                  let sc_r_up = 
                    add_to_cst_list p_list_r_up update_sc in
                  let (sp''', sc_low_r) = 
                    add_roots_rec sp'' stbl_tl low r lowsign sp_r in
                    (sp''', sc_r_up ++ ((Rroot r, (p, sp_r) :: sc) :: sc_low_r))
             |Aroot of alg
*)
