Unset Boxed Definitions.
Unset Boxed Values.



Require Export NArith.
Require Export Mylist.
Require Import Utils.

Set Implicit Arguments.



  (************************************************************)
  (*****         Type definitions for the CAD              ****)
  (************************************************************)


Section TYPES.


  (** Type of result of sign computations *)
  Definition Sign := option comparison.
  


  (**** Polynomials in Horner form, one var with coefs in C ****)

  
  (*The set of base coefficients *)
  Variable Rat :Set.
  Variable rmin : Rat -> Rat -> Rat.
  Variable req : Rat -> Rat -> bool.


  (*The set of coefficients*)
  Variable Coef:Set.


  (* Polys in one var over C*)
  Inductive Pol1(C:Set):Set:=
    |Pc : C -> Pol1 C
    |PX : Pol1 C -> positive -> C -> Pol1 C.


  Let Pol := Pol1 Coef.

  (* Here we can also define all the operators on Pols wich are not recursive
    in the number of variables *)

  (* Couple (degree * coefdom) for a polynomial *)
  Definition Pol_deg_coefdom := 
    let aux := 
      fix aux (deg:N) (P:Pol){struct P} : N * Coef :=
	match P with
	  | Pc a => (deg,a)
	  | PX P i p => aux (deg + Npos i)%N P
	end 
	in aux N0.

(* Degree only *)
  Definition Pol_deg P := fst (Pol_deg_coefdom P).

(* Leading coef only *)
  Fixpoint Pol_dom(P:Pol) : Coef :=
   match P with
   | Pc p => p
   | PX P _ _ => Pol_dom P
   end.

(* Hack for division *)
  Definition Pol_coefdom_if_PC (c:Coef) (P:Pol) : Coef :=
   match P with
   | Pc p => p
   | PX P _ _ => c
   end.



  (************************************************************)
  (* Informations about a Pol to be computed once and for all *)
  (************************************************************)

  (* Info is (P, Pbar, dPbar, lowsign, signinfo) where :
     - P is a polynomial
     - Pbar is the square free part of P,
     - dPbar is the degree of Pbar (for later bern computations)
     - lowsign the sign of P in -inf
     - signinfo is the sign of P if it is known to be constant,
       and None else *)

  Definition Info := uple5 Pol Pol N Sign Sign.

  Definition mk_Info P Q n low sign_info : Info := 
    Five P Q n low sign_info. 

  Definition Pol_of_Info (c:Info) := fst5 c.



  (************************************************************)
  (* ** Representation of algebraic points in n dimensions ** *)
  (************************************************************)


 (* This will be the information encoding bernstein coefs which are
  retained, in fact Info at the level below *)
  Variable berncoef : Set.


  (** encoding of algebraic numbers at this level, 
      x := (a, b, P, Pbar, lb) : mkAlg 
    - a < x < b  
    - P is a polynomial such [P x = 0]
    - Pbar is the square free part of P.
    - lb is the list bernstein coefs of P over ]a b[.
    For each bern coef, we keep the polinfo because we will later
    have to compute signs of these coefs, so berncoef will be recursively
    instanciate with Info. *)

  Definition mkAlg := uple5 Rat Rat Pol Pol (list berncoef).



  (** Elements of R :
  either -infty : a least bound for the roots considered,
  or a rational point between two consecutive roots
  or a rational root
  or an algebraic root: mkAlg is the type of the encoding, to be defined
  in Gen_functor.v at each level *)


  Inductive mkRpoint :Set:=
   | Minf     : Rat -> mkRpoint
   | Between  : Rat -> mkRpoint
   | Root     : Rat -> mkRpoint 
   | Alg_root : mkAlg -> mkRpoint.



  (* mkAlgebraic number (point in a cell) at the coef level *)
  Variable cell_point : Set. 

  (** mkAlgebraic number (point in a cell) at this level **) 
  Definition mkcell_point_up := (cell_point * mkRpoint)%type.

(*  Definition cell_point_proj (cpu:mkcell_point_up) := fst cpu.
  Definition rpoint_of_cell(c:mkcell_point_up):= snd c.*)

  Definition build_cell_point_up(c:cell_point)(r:mkRpoint):=(c,r).

  (************************************************************)
  (*****               Record Cad                        ******)
  (************************************************************)


  (* This is a highly unsatisfactory version, with a lot of redundancy
  and no propagation of refinements : path (= coordinates of the real
  point) is put as a label of the leave *)

  (* builds the type of the tree result for n variable, ie complete
  trees of depth n, with leaves of type C *)
  Variable mkCad:Set -> Set.

  (* from f:C ->D, and a complete tree with leaves in C, maps f on the
  leaves of the tree, building  a complete tree with leaves in D *)
  Variable mkCad_map : forall C D:Set, (C -> D) -> mkCad C -> mkCad D.


  (* builds the type of the tree result for n+1 variable, ie complete
    trees of depth n+1, with leaves of type C *)  
  Definition mkCad_up(C:Set):=mkCad (list C).

  Definition mkCad_map_up(C D:Set)(f:C -> D)(cad :mkCad (list C)):
    mkCad (list D):=
     let aux := fun clist:list C => map f clist in
       @mkCad_map (list C) (list D)  aux cad.


  (* Cad gathers what is needed from level n to build the cad at level n+1 *)
  
  Record Cad : Set := mk_cad {
    Pol_0                : Pol;
    Pol_1                : Pol;
    Pol_add              : Pol -> Pol -> Pol;
    Pol_mul_Rat          : Pol -> Rat -> Pol;
    Pol_mul              : Pol -> Pol -> Pol;
    Pol_sub              : Pol -> Pol -> Pol;
    Pol_opp              : Pol -> Pol;
    Pol_of_Rat           : Rat -> Pol;
    Pol_is_Rat           : Pol -> bool;
    Pol_zero_test        : Pol -> bool;
    Pol_base_cst_sign    : Pol -> option comparison;
    Pol_pow              : Pol -> N -> Pol;
    Pol_div_Rat          : Pol -> Rat -> Pol;
    Pol_div              : Pol -> Pol -> Pol;
    Pol_gcd_gcd_free     : Pol -> Pol -> Pol * Pol * Pol;
    Pol_square_free      : Pol -> Pol;
    cell_point_up_refine : mkcell_point_up -> nat -> option mkcell_point_up;
    Pol_low_bound        : Pol -> cell_point -> Rat;
    Pol_value_bound      : mkcell_point_up -> Pol -> Rat * Rat;
    Info_of_Pol          : option comparison -> Pol -> Info;
    Pol_low_sign         : 
      cell_point -> Pol -> Pol -> nat -> (cell_point * (option comparison));
    Pol_sign_at          :
      Info -> mkcell_point_up -> nat -> 
      mkcell_point_up * (Pol * option comparison);
    Pol_cad : list Pol -> nat -> mkCad_up (mkcell_point_up * (list (Pol * Sign)))
  }.


End TYPES.

(*
  Variable mkCad : Set->Set.

  Variable min_cell_point_list : 
    list cell_point -> cell_point.


  Variable map_Cad : forall C D ARGS:Set,
    mkCad C -> (ARGS -> C -> cell_point*D) -> mkCad D.


  Variable Rpoint_bot : mkRpoint.

  Definition min_mkRpoint(a b:mkRpoint):=
    match a, b with
      |Alg_root tag_a, Alg_root tag_b =>
	let (xa, ya, Pa, Pbara,la) := tag_a in
	let (xb,yb,Pb, Pbarb,lb) := tag_b in
	let x := rmin xa xb in
	let y := rmin ya yb in
	  if req x y then Root x
	    else Alg_root (Five x y Pa Pbara la)
      |_,_ => a
    end.


  Fixpoint min_mkRpoint_list1(r:mkRpoint)(l:list mkRpoint)
    {struct l} : mkRpoint:=
    match l with
      |nil => r
      |r'::tl =>
	min_mkRpoint_list1 (min_mkRpoint r r') tl
    end.

  Definition min_mkRpoint_list := min_mkRpoint_list1 Rpoint_bot.

  Definition mkCad_up(C:Set) := mkCad (list (cell_point * C)).

(*  Definition min_cell_point_up_list1
    (z:mkcell_point_up)(l:list mkcell_point_up):=
    let (c,r):=z in
    let minc := min_cell_point_list c (map (fun x => fst x) l) in
    let minr := min_mkRpoint_list r (map (fun x => snd x) l) in
      (minc, minr).*)

  Definition min_cell_point_up_list(l:list mkcell_point_up):=
    let minc := min_cell_point_list (map (fun x => fst x) l) in
    let minr := min_mkRpoint_list (map (fun x => snd x) l) in
      (minc, minr).

(*

  Definition min_cell_point_up_list:=
    min_cell_point_up_list1 cell_up_bot.
*)

(* moralement C est une col , a changer on avait pas d'arbre...*)
  Definition map_Cad_up(C D ARGS:Set)(cad:mkCad_up C)
    (f:ARGS -> C -> mkcell_point_up*D):=
    let aux := 
      fun a:ARGS => fun rclist : list (mkRpoint *C) =>
	let clist := map (fun x => snd x)  rclist (*:list C*) in
	let celldlist := map (f a) clist (*:list mkcell_point_up*D*) in
	let rdlist := map (fun x => (snd (fst x),snd x)) celldlist in
	let celllist := map (fun x => fst (fst x)) celldlist in
	(min_cell_point_list celllist,rdlist) in
	@map_Cad (list (mkRpoint * C)) (list (mkRpoint * D)) ARGS
	  cad aux.
*)
