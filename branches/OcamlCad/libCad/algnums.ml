open Core
open Num
open List
open Poly

(** encoding of algebraic numbers at this level, 
      x := (a, b, P, Pbar, lb) : mkAlg 
    - a < x < b  
    - P is a polynomial such [P x = 0]
    - Pbar is the square free part of P.
    - lb is the list bernstein coefs of P over ]a b[.
    For each bern coef, we keep the polinfo because we will later
    have to compute signs of these coefs, so berncoef will be recursively
    instanciate with build_Info. *)

type mkAlg = {
  mutable lb : num;          (* left bound  *)
  mutable rb : num;          (* right bound *)
  mutable pol : poly;     (* pol P st P(x) = 0 *)
  mutable polbar : poly;  (* square free part of *)
  mutable pbern : poly list   (* list of pinfo for each bernstein coef
                                of pol over ]rb, lb[ *)
}
