Require Import QArith ZArith Zwf Omega.
Require Import ssreflect eqtype ssrbool ssrnat div fintype seq ssrfun.
Require Import bigops groups choice binomial.
Require Export ssralg xssralg infra .

Import GroupScope .
Import GRing.Theory .
Import GOrdered.
Open Local Scope ring_scope .

Set Printing Width 50.

Fixpoint eval_pol (l : seq Qcb)(x : Qcb) {struct l} : Qcb :=
  match l with 
    nil => 0
  | a::tl => a + x * (eval_pol tl x)
  end.

(* Polynomial are only represented by the list of their coefficients.
  To any polynomial, we associate the absolute polynomial, whose
  coefficients are the absolute values of the initial coefficients. *)

Fixpoint abs_pol (l : seq Qcb) : seq Qcb :=
 match l with nil => nil | a :: tl => (absr a) :: (abs_pol tl) end.

(* The value of the absolute polynomial is always larger than the value
 of the initial polynomial. *)

Lemma ler_absr_eval_pol :
  forall l x, absr (eval_pol l x) <<= eval_pol (abs_pol l) (absr x).
Proof.
elim => [|y s IHs] x /=; first by rewrite absr0.
by apply: (ler_trans (absr_addr _ _)); rewrite lerTrb absr_mulr ler_lcompat ?absrpos.
Qed.

Lemma ler0_eval_pol_abs_pol :
  forall l x, 0 <<= x -> 0 <<= eval_pol (abs_pol l) x.
Proof.
elim => [| y s Ihs] x hx /=; first by rewrite ler_refl.
by apply: lerT0; rewrite ?absrpos // ler_0_lcompat // Ihs.
Qed.

Lemma eval_pol_abs_pol_increase : 
  forall l x y, 0 <<= x -> x <<= y ->
    eval_pol (abs_pol l) x <<= eval_pol (abs_pol l) y.
elim=> [|u s Ihs] x y hx hy /=; first by rewrite ler_refl.
rewrite lerTrb; apply ler_trans with (y * eval_pol (abs_pol s) x).
  by rewrite ler_rcompat // ler0_eval_pol_abs_pol.
by rewrite ler_lcompat // ?Ihs // (ler_trans hx).
Qed.

(* To describe polynomial addition, multiplication by a scalar, and
  multiplication, we simply specify these operations so that their
  interpretation through polynomial evaluation returns the corresponding
  scalar operation. *)

Definition add_pol :
  forall l1 l2, {l' | forall x, eval_pol l1 x + eval_pol l2 x =
  eval_pol l' x}.
elim=> [|a l1 Ihl1] [|b l2].
- by exists [::]; rewrite /= addr0.
- by exists (b :: l2); move=> /= x; rewrite add0r.
- by exists (a :: l1); move=> /= x; rewrite addr0.
- (* ring needed!*)
  case: (Ihl1 l2)=> [l' hl']; exists ((a + b) :: l'); move=> /= x.
  rewrite [b + _]addrC addrA -[a + _ + _]addrA -mulr_addr hl'.
  by rewrite -addrA [_ + b]addrC addrA.
Defined.


Definition s_mult_pol :
  forall a l, {l' | forall x, a * eval_pol l x = eval_pol l' x}.
move=> a; elim=> [| b l Ihl] /=.
- by exists [::]; rewrite /= mulr0.
- case: Ihl => l' hl'; exists ((a * b) :: l'); move=> /= x.
  by rewrite -hl' mulr_addr 2!mulrA [x * _]mulrC.
Defined.

Definition mult_pol :
  forall l1 l2, {l' | forall x, eval_pol l1 x * eval_pol l2 x =
   eval_pol l' x}.
elim=> [|a l1 Ihl1] /=.
- by exists [::]; move=> /= x; rewrite mul0r.
- move=> l2; case (s_mult_pol a l2) => l2a h.
  case (Ihl1 (0 :: l2)) => l1l2x h1; case (add_pol l1l2x l2a)=> l' h2.
  exists l'; move=> /= x; rewrite -h2 -h1 -h /= add0r mulr_addl.
  by rewrite mulrA [_ * x]mulrC [a*_ + _]addrC.
Defined.

Definition mirror_pol :
  forall l, {l' | forall x, eval_pol l (-x) = eval_pol l' x}.
elim=> [|a l1 IHl1] /=.
- by exists [::].
case IHl1 => l' pl'.
case (s_mult_pol (-1) l') => l'' pl''.
by exists [:: a & l''] => x /=; rewrite -pl'' -pl' !mulNr mulrN mul1r.
Defined.
  
Lemma translate_pol :
  forall l a, {l' | forall x, eval_pol l x = eval_pol l' (x - a)}.
elim=> [| b l Ihl]; move=> a /=.
- by exists [::].
- case (Ihl a) => l' h; case (mult_pol [:: a ; 1] l') => l2 h2.
  case (add_pol [:: b] l2) => l3 h3.
  exists l3; move=> x; rewrite -h3 -h2 h /= mulr0 !addr0 mulr1.
  by rewrite (_ : a + (x - a) = x) // -oppr_sub oppr_add addrA
       addrN add0r opprK.
Qed.

Lemma Qcb_Z : forall n : Z, Qred (Qmake n 1) == Qmake n 1.
Proof.
move=> n; apply/eqP; apply: Qcanon.Qred_identity => /=.
rewrite Znumtheory.Zgcd_1_rel_prime.
apply Znumtheory.rel_prime_sym.
apply Znumtheory.rel_prime_1.
Qed.

Canonical Structure Qcb_make (n : Z) := QcbMake (Qcb_Z n).

Lemma Qcb_make0 : Qcb_make 0 = 0.
Proof. exact: val_inj. Qed.

Lemma Qcb_make1 : Qcb_make 1 = 1.
Proof. exact: val_inj. Qed.

Definition Qbin m n := Qcb_make (Z_of_nat (bin m n)).

Axiom QbinS : forall m n, Qbin m.+1 n.+1 = Qbin m n.+1 + Qbin m n.
Axiom Qbin0 : forall m, Qbin m 0 = 1.

Fixpoint qpower_rec (x :Qcb) (n:nat) :=
   match n with 0%nat => 1 | S p => x * qpower_rec x p end.

Definition qpower := nosimpl qpower_rec.

Notation "x ^ y" := (qpower x y).

Definition translate_pol' (l :seq Qcb) (a:Qcb) :=
  mkseq (fun i:nat =>
     \sum_(k < (size l).+1) Qbin k i * nth 0 l k * a ^ (k - i)) (size l).

Lemma mkseq_shift :
  forall T (f : nat ->T) n, mkseq f n.+1 = f 0%nat::mkseq (fun x => f x.+1) n.
move => T f n; rewrite /mkseq -[n.+1]/(1+n)%nat iota_add addnC iota_addl /=.
by congr (cons (f 0%nat)); rewrite -map_comp; apply: eq_in_map; move => x _ /=.
Qed.

Require Import String.
Open Scope string_scope.
Definition case_name (x:string) := True.

Ltac Name_case s :=
  match goal with
     _ : case_name ?s' |- _ =>
     let u:= eval compute in (s' ++ " not finished") in fail 1 u
 | |- _ => assert (case_name s); [solve[exact I] | ]
 end.

Lemma eval_pol_big :
  forall l x, eval_pol l x = \sum_(i < size l) nth 0 l i * x ^ i.
move => l x; elim: l=> [ | a l IHl].
Admitted.

Lemma translate_pol'q :
  forall l a x, eval_pol (translate_pol' l a) x = eval_pol l (x + a).
move => l a; elim: l => [ | b l' IHl' x]; first by [].
  have -> : eval_pol (b::l') (x+a) = b + (x + a) * eval_pol l' (x + a) by [].
  rewrite /translate_pol'.
  have -> : size (b::l') = (1+(size l'))%N by [].
rewrite mkseq_shift.
Admitted.

