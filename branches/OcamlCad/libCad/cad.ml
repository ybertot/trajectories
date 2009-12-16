open Core
open List
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


(* (sp, (Between (c + d)/2, (p, sign (p(sp, (c + d)/2))))), by evaluation *)
let scol_at_mid1 sp c d p =
  let m = middle c d in
  let (msp', smp ) = pol_sign_at (Between m :: sp) p in
    (List.tl msp', (Between m, (p, smp)))


(* We construct sample point lists by isolating the roots and
   inserting Between sample points between consecutive roots. To
   avoid multiple redundant evaluations, we use boolean flags, and
   define int(c, d, c_is_r, d_is_r) by:
   - c and d are nums
   - c_is_r and d_is_r are boolean flags, true if respectively c and d
   have been
   diagnosed as roots of p. 
   Namely if c_is_r (resp. d_is_r) is true, the wanted sample point
   list should start (resp. end) with a Beetwen sample point1.
 
   c_is_r | d_is_r | interval
   --------------------------
   1      | 1      | ]c, d[
   1      | 0      | ]c, <-d]
   0      | 1      | [c->, d[
   0      | 0      | [c->, <-d]
   where c-> (resp <-d) is the smallest (resp greatest) root of p
   greater (resp smaller) than c (resp d). If the interval has an open
   endpoint, it means the corresponding end of the list is a Between
   or a Minf. 
*)

(* root is the only root in ]c, d[. 
   - computes a correct sample point list for int(c, d, c_is_r,
   d_is_r)
   - long but rather elementary function *)
let rec insert_root1 sp p c c_is_r d d_is_r root =
  match root with
    |Minf _ -> failwith "not a root"
    |Between _ -> failwith "not a root"
    |Rroot r ->
       (match (c_is_r, d_is_r) with
           (* endpoints are not roots, we do not insert Between
              witnesses *)
         |false, false -> (sp, [(root, (p, 0))])
         |false, true ->
            (* we need a Between witness on the right, sanity check first *)
            if le_coef d r then failwith "alg refine needed?"
            else
              let (sp', scbr) = scol_at_mid1 sp r d p in
                (sp', [(root, (p, 0)); scbr])
         |true, false ->
            (* we need a Between witness on the left, sanity check first *)
            if le_coef r c then failwith "alg refine needed?"
            else
              let (sp', scbl) = scol_at_mid1 sp c r p in
                (sp', [scbl; (root, (p, 0))])
         |true, true ->
            (* we need a Between witness on the left and on the right,
               sanity check first *)            
            if (le_coef r c) || (le_coef d r) then failwith "alg refine needed?"
            else
              (* else we insert the witnesses *)
              let (sp', scbr) = scol_at_mid1 sp r d p in
              let (sp'', scbl) = scol_at_mid1 sp' c r p in
                (sp'', [scbl; (root, (p, 0)); scbr]))
    |Aroot ralg ->
       let a = ralg.lbound in
       let b = ralg.rbound in
       let rec_refine = 
         let new_root_sp' = sample_point_refine (root :: sp) in
         let new_root :: sp' = new_root_sp' in 
           insert_root1 sp' p c c_is_r d d_is_r new_root in
       match (c_is_r, d_is_r) with
           (* endpoints are not roots, we do not insert Between
              witnesses *)
         |false, false -> (sp, [(root, (p, 0))])
         |false, true ->
            (* we need a Between witness on the right, sanity check first *)
            if lt_coef d b then failwith "alg refine needed?"
              (* we need to refine the alg *)
            else if eq_coef d b then rec_refine
            else  
              (* else we insert the witnesses *)
              let (sp', scbr) = scol_at_mid1 sp b d p in
                (sp', [(root, (p, 0)); scbr])
         |true, false ->
            (* we need a Between witness on the left, sanity check first *)
            if lt_coef a c then failwith "alg refine needed?"
              (* we need to refine the alg *)
            else if eq_coef c a then rec_refine
            else
              let (sp', scbl) = scol_at_mid1 sp c a p in
                (sp', [scbl; (root, (p, 0))])
         |true, true ->
            (* we need a Between witness on the left and on the right,
               sanity check first *)            
            if (lt_coef  a c) || (lt_coef d b) then failwith "alg refine needed?"
              (* if one bound is not sharp enough we need to refine *)
            else if (eq_coef d b) || (eq_coef c a) then rec_refine
              (* else we insert the witnesses *)
            else
              let (sp', scbr) = scol_at_mid1 sp b d p in
              let (sp'', scbl) = scol_at_mid1 sp' c a p in
                (sp'', [scbl; (root, (p, 0)); scbr])



(* Initialization : computes from scratch a l list of 1dim sample
   points describing the roots of p(sp, x) in the interval 
   int(c, d, c_is_r, d_is_r), given the
   sign column corresponding to the sample sp in the recursively
   computed cad and bl the list of bernstein coefs of p with  param c
   and d.
   scp (resp sdp) is the sign of p at c (resp at d).
   Result is a pair (sp', l) where sp' refines sp and l is a list of
   pairs of the form (sp1, (p, s)), where sp1 is a sample_point1, p
   is the argument and s = sign (p (sp, s)).
   sample points in l come in increasing order.

*)

let rec sample_list_int1 sp p c c_is_r scp d d_is_r sdp bl = 
  (* 0th case: ]c,d[ is empty*)
  if lt_coef d c then (sp, []) 
  else
    let split_case =
      let m = middle c d in
      let (bl', bl'') = hbern_splitsP p c d m bl in
      let (m_sp', smp) = pol_sign_at ((Between m) :: sp) p in
      let sp' = List.tl m_sp' in
      let (sp'', res_l) = 
        sample_list_int1 sp' p c c_is_r scp m true 0 bl' in
      let (sp''', res_r) =
        sample_list_int1 sp'' p  m true 0 d d_is_r sdp bl'' in
        (* 1st case : an exact root is found at m *)
        if smp = 0 then
          (sp''', res_l @ [(Rroot m, (p, 0))] @ res_r)
            (* 2nd case : no root, m is a between witness *)
        else
          (sp''', res_l @ [(Between m, (p, smp))] @ res_r) in
            (* number of sign changes in the list of bern coefs at sp *)
    let (sp', test) = sign_changes sp bl in
      (* 1st case: 0 sign change, ie no root for p(sp, x) in ]c,d[ *)
      if test = 0 then
        (* 1st case a) c is a between or a minf, hence c is already
           a witness of this cell *)
        if not c_is_r then (sp', [])
        else
          (* 1st case b) : c is a root, hence we should add a witness
             for this cell *)
            (* 1st case b)' : d is not a root, it's a good sample point *)
          if not d_is_r then (sp', [Between d, (p, sdp)])
            (* 1st case b)'' : d is a root, we need the middle as a
               sample point, and some evaluation *)
          else
            let (sp'', sc) = scol_at_mid1 sp' c d p in
              (sp'', [sc])
      (* 2nd case: 1 sign change, ie 1! root for p(sp, x) in ]c, d[*)
      else if test = 1 then
        let spcpd = scp * sdp in
          (* case 2a) : 
             1! sign change + p(sp,c)p(sp,d) < 0 => 1! root of p in ]c,d[*)
          if spcpd = -1 then 
            let new_aroot = Aroot (mk_alg c d p) in
              insert_root1 sp' p c c_is_r d d_is_r new_aroot
          (* case 2b) : 
             1! sign change + p(sp,c)p(sp,d) >= 0 => split again *)
          else split_case
            (* 3rd case: more sign changes => split again *)
      else split_case

let rec map_sign_col sc l =
  match l with
    |[] -> []
    | hd :: tl ->
        let (hd1, hd2) = hd in
          (hd1, hd2 :: sc) :: map_sign_col sc tl

(*
  - sp is a sample point
  - c and d are reals (like coefs)
  - p is a poly
  - lp is a list of poly
  - lpsl is a signed sample list for lp on ]c,d[
  - slpc (resp. slpd) is the sign col of lp at c (resp. d)
  - c_is_r (resp d_is_r) is boolean flag set in c (resp. d) is a root
  for p(sp, x)
  - spc (resp. spd) is the sign of p at c (resp. d)
  - bl is the list of bern coefs for p on ]c, d[

  computes a signed sample list of p :: lp on ]c, d[
  
  TO DO:
  - three last cases SHOULD be factorized using an aux function...
  - ugly numerous appends could be avoided by a more CPS version
*)
let rec sample_list_int sp p lp lpsl slpc slpd c c_is_r spc d d_is_r spd bl =
  match lpsl with
    |[] ->
       (match lp with
           (* one pol case *)
         |[] -> 
            let (sp', resp) = 
              sample_list_int1 sp p c c_is_r spc d d_is_r spd bl in
              (sp', map_sign_col [] resp)
         |_ -> failwith "Empty sample list")
    |sp1_sc1 :: lpsl_tl ->
       let (sp1, sc1) = sp1_sc1 in
         match sp1 with
             (* 1st case: 
                - sp1_sc1 sould be the last element of lpsl.
                - polys in lp have a cst sign over ]c, d[
                - d should be minf witness for p :: lp *)
           |Minf m ->
              let (sp', psl) = 
                sample_list_int1 sp p c c_is_r spc d d_is_r spd bl in
              let plpsl = 
                map_sign_col sc1 psl in
                (sp', plpsl @ [(Minf d, (p, spd) :: sc1)])
              (* 2nd case:
                 - low >= b should not happen 
                 - if p(sp, b) = 0 we transform Between b into Rroot r.
                 on ]low, b{ pols in lp have a cst sign, we compute
                 the sample list for p and map the signs of sc1. On
                 ]b, up[, recursive call to sample_list.
              *)
           |Between b ->
              if lt_coef b c then failwith "non overlapping ints"
              else 
                let (bsp', spb) = pol_sign_at (sp1 :: sp) p in
                let sp' = List.tl bsp' in
                let (bl', bl'') = hbern_splitsP p c d b bl in
                  (* 1st case: p(sp,b) = 0 *)
                  if spb = 0 then 
                    let (sp'', psl) = 
                      sample_list_int1 sp p c c_is_r spc b true 0 bl
                    in
                    let resl = map_sign_col sc1 psl in
                    let (sp''', resr) = 
                      sample_list_int 
                        sp'' p lp lpsl_tl sc1 slpd b true 0 d d_is_r spd bl' in
                      (sp''', resl @ [(Rroot b, (p, 0) :: sc1)] @ resr)
                  else
                    (* 2nd case: p(sp,b) <> 0 *)
                    let (sp'', psl) = 
                      sample_list_int1 sp p c c_is_r spc b false spb bl
                    in
                    let resl = map_sign_col sc1 psl in
                    let (sp''', resr) = 
                      sample_list_int 
                        sp'' p lp lpsl_tl sc1 slpd b false spb d d_is_r spd bl' in
                      (sp''', resl @ [(Between b, (p, spb) :: sc1)] @ resr)
           |Rroot r ->
              if lt_coef r c then failwith "non overlapping ints"
              else 
                 (* else we return ll @ (rroot r, _) @ lr 
                  where ll is the signed sample list for p, signs for
                     lp being unifomly slpc, and lr is a recursive
                     call on ]b,d[ *)
                let (rsp', spr) = pol_sign_at (sp1 :: sp) p in
                let sp' = List.tl rsp' in
                let (bl', bl'') = hbern_splitsP p c d r bl in
                  (* 1st case p(sp, r) = 0 *)
                  if spr = 0 then
                    let (sp'', psl) = 
                      sample_list_int1 sp p c c_is_r spc r true 0 bl
                    in
                    let resl = map_sign_col slpc psl in
                    let (sp''', resr) = 
                      sample_list_int 
                        sp'' p lp lpsl_tl sc1 slpd r true 0 d d_is_r spd bl' in
                      (sp''', resl @ [(Rroot r, (p, 0) :: sc1)] @ resr)
                  else
                    (* 2nd case: p(sp,b) <> 0 *)
                    let (sp'', psl) = 
                      sample_list_int1 sp p c c_is_r spc r false spr bl
                    in
                    let resl = map_sign_col slpc psl in
                    let (sp''', resr) = 
                      sample_list_int 
                        sp'' p lp lpsl_tl sc1 slpd r false spr d d_is_r spd bl' in
                      (sp''', resl @ [(Rroot r, (p, spr) :: sc1)] @ resr)
           |Aroot ralg ->
              let a = ralg.lbound in
              let b = ralg.lbound in
                (* if a <= c (which should be an =) then we refine the alg *)
                if le_coef a c then 
                  let ralg :: sp' = sample_point_refine (sp1 :: sp) in
                    sample_list_int 
                      sp p lp lpsl slpc slpd c c_is_r spc d d_is_r spd bl
                else
                  (* else we return ll @ (Aroot ralg, _) @ lr 
                  where ll is the signed sample list for p, signs for
                     lp being unifomly slpc, and lr is a recursive
                     call on ]b,d[ *)
                  let (ralgsp', spralg) = pol_sign_at (sp1 :: sp) p in
                  let sp' = List.tl ralgsp' in
                  let (bl', bl_aux) = hbern_splitsP p c d a bl in
                  let (_, bl'') = hbern_splitsP p a d b bl_aux in
                  (* 1st case p(sp, r) = 0 *)
                  if spralg = 0 then
                    let (sp'', psl) = 
                      sample_list_int1 sp p c c_is_r spc a true 0 bl
                    in
                    let resl = map_sign_col sc1 psl in
                    let (sp''', resr) = 
                      sample_list_int 
                        sp'' p lp lpsl_tl sc1 slpd b true 0 d d_is_r spd bl' in
                      (sp''', resl @ [(Aroot ralg, (p, 0) :: sc1)] @ resr)
                  else
                    (* 2nd case: p(sp,b) <> 0 *)
                    let (sp'', psl) = 
                      sample_list_int1 sp p c c_is_r spc a false spralg bl
                    in
                    let resl = map_sign_col sc1 psl in
                    let (sp''', resr) = 
                      sample_list_int 
                        sp'' p lp lpsl_tl sc1 slpd b false spralg d d_is_r spd bl' in
                      (sp''', resl @ [(Aroot ralg, (p, spralg) :: sc1)] @ resr)





let sign_at_minfty sp p =
  let m = minus_coef (cauchy_bound sp p) in
  let (msp, s) = pol_sign_at (Minf m :: sp) p in
    (List.tl msp, s)

let sign_at_pinfty sp p =
  let m = cauchy_bound sp p in
  let (msp, s) = pol_sign_at (Between m :: sp) p in
    (List.tl msp, s)


(* complete signed sample point list for p(sp, x) *)

(* Sign at -infinity/infinity of the univariate pol p(sp, x): There
   are at least two ways of computing this sign:
   - normalize p above sp, then compute the sign of its leading coef
   and deduce the sign at -infty from this sign and the parity of the
   degree of p above sp 
   - evaluate p at a point p(sp, m), when m is smaller than
   -cauchybound (p(sp, x)).
   Here we use the second method. *)

let sample_list1 sp p = 
  (* the cauchy bound gives the point at +infty. *)
  let (sp1, pinf) = cauchy_bound sp p in
  let (pinf_sp2, spinf) = pol_sign_at (Between pinf :: sp1) p in
  let sp2 = List.tl pinf_sp2 in
    (* the cauchy bound opposite gives the point at -infty. *)
  let minf = minus_coef pinf in
  let (minf_sp3, spinf) = pol_sign_at (Between pinf :: sp2) p in
  let sp3 = List.tl pinf_s3 in



  let bl = hbern_coefsP p minf pinf in
  let (sp4, list_on_open) = 
    sample_list_int1 sp3 p  c_is_r scp d d_is_r sdp bl
