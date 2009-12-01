open Core
open EqAst
open Poly
open Cad

exception InvalidInput of exn
exception InvalidPol

let rec pol_of_pol_expr ids pe =
  match pe with
    |PVar (i, id) -> 
       let n = find_at ids id in
         mon n i
    |PCst c -> cf c
    |PAdd (pe1, pe2) ->
       let p1 = pol_of_pol_expr ids pe1 in
       let p2 = pol_of_pol_expr ids pe2 in
         addP p1 p2
    |PSub (pe1, pe2) ->
       let p1 = pol_of_pol_expr ids pe1 in
       let p2 = pol_of_pol_expr ids pe2 in
         subP p1 p2
    |PMul (pe1, pe2) ->
       let p1 = pol_of_pol_expr ids pe1 in
       let p2 = pol_of_pol_expr ids pe2 in
         multP p1 p2




(*type num = Num.num*)


(* let pol_expr_var_list pe = *)
(*   let rec aux pe vm = *)
(*     match pe with *)
(*       |PVar (i, id) -> *)
(*          if List.mem i vm then vm else i :: vm *)
(*       |PCst _ -> vm *)
(*       |PAdd (pe1, pe2) ->  *)
(*          let vm1 = aux pe1 vm in *)
(*            aux pe2 vm1 *)
(*       |PSub (pe1, pe2) ->  *)
(*          let vm1 = aux pe1 vm in *)
(*            aux pe2 vm1 *)
(*       |PMul (pe1, pe2) ->  *)
(*          let vm1 = aux pe1 vm in *)
(*            aux pe2 vm1 *)
(*   in aux pe [] *)


(* type poly = num IntListMap.t *)

(* let rec poly_add p1 p2 = *)
(*   IntListMap.mapi *)
(*     (fun i c -> Num.add_num c (IntListMap.find i p2)) p1  *)

(* let rec poly_sub p1 p2 = *)
(*   IntListMap.mapi *)
(*     (fun i c -> Num.sub_num c (IntListMap.find i p2)) p1  *)





(* (\* lifts if monomial (ie. an int list) living in num[X0,...Xj] to *)
(*    num[X0,...X(j+k)] *\) *)












(* let rec lift_mon m k = *)
(*   if k = 0 then m *)
(*   else 0 :: (lift_mon m (k - 1)) *)

(* (\* X_k^j in num[X0, Xn-1]*\) *)

(* let head_mon_exp n j =  *)
(*   let rec mon_tl n = *)
(*     if n = 0 then [] *)
(*     else 0 :: mon_tl (n - 1) *)
(*   in j :: mon_tl n *)

(* let mon n k j = *)
(*   if k = 0 then head_mon_exp n j *)
(*   else lift_mon (head_mon_exp k j) (n - k) *)


(* (\* *)
(* let rec poly_of_pol_expr pe l n =  *)
(*   match pe with *)
(*   | PVar (i, id) -> nkmon n (find_at l id) *)
(*   | PCst c -> ncst n c *)
(*   | PAdd (pe1, pe2) -> *)
(*       let p1 = poly_of_pol_expr pe1 in *)
(*       let p2 = poly_of_pol_expr pe2 in *)
(*         padd p1 p2 *)
(*   | PSub (pe1, pe2) ->  *)
(*       let p1 = poly_of_pol_expr pe1 in *)
(*       let p2 = poly_of_pol_expr pe2 in *)
(*         psub p1 p2 *)
(*   | PMul (pe1, pe2) ->  *)
(*       let p1 = poly_of_pol_expr pe1 in *)
(*       let p2 = poly_of_pol_expr pe2 in *)
(*         pmul p1 p2 *)

(* *\) *)





let parse_equation = fun input ->
  let lexbuf = Lexing.from_string input in
    EqParser.equation EqLexer.lexer lexbuf


let read_and_solve_problem = fun ?(stream = stdin) () ->
  let respace = Str.regexp "^[ \t]*$" in
  let rec input = fun data ->
    let line =
      try  Some (input_line stream)
      with End_of_file -> None
    in
      match line with
      | Some line ->
          if   Str.string_match respace line 0
          then input data
          else input (line :: data)
      | None      -> data
  in
    match List.rev (input []) with
    | ((_ :: _) as eqs) ->
(*        raise (InvalidInput (Failure "not yet implemented"))*)
     begin 
        let eqs =
          try  List.map parse_equation eqs
          with
          | EqLexer.LexError _ as e -> raise (InvalidInput e)
          | Parsing.Parse_error as e -> raise (InvalidInput e)
        in
        let pol_exprs = pol_expr_of_equations eqs in
        let ids = ids_of_exprs pol_exprs in
        let vars_number = List.length ids in
        let pols = List.map (pol_of_pol_expr ids) pol_exprs in
          match eqs with
            | []       -> Printf.fprintf stderr "liste vide\n%!"
            | _ -> Printf.fprintf stderr "ok : %s\n%!"
                (String.concat ", " (List.map string_of_P pols))
(*             | _ ->        Printf.fprintf stderr "ok : %s\n%!" *)
(*                     (String.concat ", " (List.map string_of_equation eqs)) *)
     end
    | _ ->
        raise (InvalidInput (Failure "input is too short"))

