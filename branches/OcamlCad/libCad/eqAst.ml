(* -------------------------------------------------------------------- *)
type pol_expr =
  | PVar of int * string
  | PCst of Num.num
  | PAdd of pol_expr * pol_expr
  | PSub of pol_expr * pol_expr
  | PMul of pol_expr * pol_expr


type equation = {
  eq_pol_expr   : pol_expr;
  eq_sign   : [ `Eq | `Le | `Ge | `Lt | `Gt ];
  eq_bound  : Num.num;
}

let rec string_of_pol_expr p = 
  match p with
    |PVar (i,s) -> 
       if i = 1 then s 
       else s^"^"^(string_of_int i)
    |PCst n -> Num.string_of_num n
    |PAdd (p1, p2) -> (string_of_pol_expr p1)^" + "^(string_of_pol_expr p2)
    |PMul (p1, p2) -> (string_of_pol_expr p1)^" * "^(string_of_pol_expr p2)
    |PSub (p1, p2) -> (string_of_pol_expr p1)^" - "^(string_of_pol_expr p2)

let rec string_of_equation e = 
  let sp = string_of_pol_expr e.eq_pol_expr in
  let sb = Num.string_of_num e.eq_bound in
  match e.eq_sign with
    |`Eq -> sp^" = "^sb
    |`Le -> sp^" <= "^sb
    |`Ge -> sp^" >= "^sb
    |`Lt -> sp^" < "^sb
    |`Gt -> sp^" > "^sb


let pol_expr_of_equations = List.map (fun x -> x.eq_pol_expr)

(* naive construction of the list of ids in a pol_expr.
   we perhaps should use maps or even hashtables here but the number
   of vars should really be very small usually... *)
       
let rec ids_of_expr l pe =
  match pe with
    |PVar (_, id) -> 
       if (List.mem id l) then l
       else id :: l
    |PCst _ -> l
    |PAdd (pe1, pe2) -> 
       let l1 = ids_of_expr l pe1  in
         ids_of_expr l1 pe2
    |PSub (pe1, pe2) -> 
       let l1 = ids_of_expr l pe1 in
         ids_of_expr l1 pe2
    |PMul (pe1, pe2) -> 
       let l1 = ids_of_expr l pe1 in
         ids_of_expr l1 pe2

           

let ids_of_exprs lpe =
  match lpe with
    |[] -> []
    |pe :: spe ->
       let ids = ids_of_expr [] pe in
         List.fold_left ids_of_expr ids spe
    

(* -------------------------------------------------------------------- *)
