%{
  open EqAst
  open Core.Num
  open Core

  let _coeffs_map = fun coeffs ->
    List.fold_left
      (fun map ((c, p), id) ->
         try
           let (c',p') = Core.StringMap.find id map in
             if p = p'  then Core.StringMap.add id (c +/ c', p) map
             else Core.StringMap.add id (c, p) map
         with
           | Not_found ->
               Core.StringMap.add id (c, p) map)
      Core.StringMap.empty
      coeffs

  let _equation = fun coeffs sign bound ->
    { eq_coeffs = _coeffs_map coeffs ;
      eq_sign   = sign               ;
      eq_bound  = bound              }
%}

%token <Big_int.big_int> INTEGER
%token <string> ID
%token PLUS MINUS DIV POWER EOL
%token LE GE LT GT EQ
%token <int> INT

%nonassoc LE GE EQ
%left     PLUS MINUS
%nonassoc UMINUS
%start    equation

%type <EqAst.equation> equation

%%
equation:
| equation_ EOL { $1 }
;

equation_:
| coeffs eqsign num { _equation $1 $2 $3 }
;

coeffs:
| coeffs PLUS  coeff { $3 :: $1 }
| coeffs MINUS coeff { ((minus_num (fst (fst $3)), snd (fst $3)), snd $3) :: $1 }
| coeff              { [$1] }
;

coeff:
| ID               { ((Num.num_one, 1), $1) }
| num ID           { (($1, 1), $2) }
| num ID POWER pow { (($1, $4), $2) }
| MINUS ID         { ((Num.num_neg_one, 1), $2) }
;

eqsign:
| LT { `Lt }
| GT { `Gt }
| LE { `Le }
| GE { `Ge }
| EQ { `Eq }
;

num:
| INTEGER             { num_of_big_int $1 }
| INTEGER DIV INTEGER { num_of_ratio (Ratio.create_ratio $1 $3) }
| MINUS num           { minus_num $2 }
;

pow:
|INT { $1 }
;
