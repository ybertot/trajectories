Require Import QArith List Omega ZArith seq xssralg infra.

Import GRing.Theory .
Import GOrderedField.
Open Local Scope ring_scope .

Fixpoint eval_pol (l : seq Qcb)(x : Qcb) {struct l} : Qcb :=
  match l with 
    nil => 0
  | a::tl => a + x * (eval_pol tl x)
  end.

