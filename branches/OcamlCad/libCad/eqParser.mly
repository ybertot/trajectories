%{
  open EqAst
  open Core.Num
  open Core

  let _equation = fun polys sign bound ->
    { eq_pol_expr   = polys              ;
      eq_sign   = sign               ;
      eq_bound  = bound              }

  let _add = fun x y -> EqAst.PAdd (x, y)
  let _sub = fun x y -> EqAst.PSub (x, y)
  let _mul = fun x y -> EqAst.PMul (x, y)
  let _var = fun x y -> EqAst.PVar (x, y)
  let _cst = fun x -> EqAst.PCst x
%}

%token <Big_int.big_int> INTEGER
%token <int> INT
%token <string> ID
%token PLUS MINUS MUL DIV POWER EOL
%token LE GE LT GT EQ
%token <int> POWER
%nonassoc LE GE LT GT EQ
%left     PLUS MINUS 
%left MUL
%start    equation

%type <EqAst.equation> equation

%%
equation:
| equation_ EOL { $1 }
;

equation_:
| poly eqsign num { _equation $1 $2 $3 }
;

poly:
| poly  PLUS  poly  { _add $1 $3 }
| poly  MINUS poly { _sub $1 $3 }
| poly  MUL  poly { _mul $1 $3 }
| mon              { $1 }
;

mon:
| ID                 { _var 1 $1                              }
| num ID             { _mul (_cst $1) (_var 1 $2)                }
| num ID POWER   { _mul (_cst $1) (_var $3 $2)               }
| ID POWER       { _var $2 $1 }               
| MINUS ID           { _mul (_cst (Num.num_neg_one)) (_var 1 $2)  }
| MINUS ID POWER { _mul (_cst (Num.num_neg_one)) (_var $3 $2) }
| num                { _cst $1 }
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
| INT { $1 }
;
