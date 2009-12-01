type num = Core.Num.num
 
type sign  = [ `Eq | `Le | `Ge | `Lt | `Gt ]

type 'a poly = Pc of 'a | Px of ('a poly * int * 'a )

val test : Core.Num.num poly

exception InvalidProblem of string

