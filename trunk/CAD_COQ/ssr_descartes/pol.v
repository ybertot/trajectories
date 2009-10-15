Require Import QArith ZArith Zwf Omega.
Require Import ssreflect eqtype ssrbool ssrnat div fintype seq ssrfun.
Require Import bigops groups choice binomial.
Require Export ssralg xssralg infra.

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
by apply: (ler_trans (absr_addr _ _));
   rewrite lerTrb absr_mulr ler_lcompat ?absrpos.
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

Lemma Qcb_makeadd: forall n m:Z, Qcb_make (n + m) = Qcb_make n +  
Qcb_make m.
Proof.
move=> n m; apply : val_inj.
by rewrite /=  -(eqP (Qcb_Z _)) /= !Zmult_1_r.
Qed.

Lemma QbinS : forall m n, Qbin m.+1 n.+1 = Qbin m n.+1 + Qbin m n.
Proof. move=> m n; by rewrite  /Qbin binS inj_plus Qcb_makeadd. Qed.

Lemma  Qbin0 : forall m, Qbin m 0 = 1.
Proof. by move=> m;rewrite /Qbin bin0 Qcb_make1. Qed.

Lemma Qbinn : forall n, Qbin n n = 1.
Proof. move=> n; by rewrite /Qbin binn Qcb_make1. Qed.

Lemma Qbin_sub : forall n m, m <= n -> Qbin n m = Qbin n (n - m).
Proof. by move=> n m nlm; rewrite /Qbin bin_sub. Qed.
   
Lemma Qbin_small : forall m n, m < n -> Qbin m n = 0.
Proof. by move=> m n mln; rewrite /Qbin bin_small // Qcb_make0. Qed.

Definition translate_pol' (l :seq Qcb) (a:Qcb) :=
  mkseq (fun i:nat =>
     \sum_(k < (size l).+1) Qbin k i * nth 0 l k * a ^+ (k - i)) (size l).

Lemma size_translate_pol' : forall l a, size (translate_pol' l a)  = size l.
by move => l a; rewrite /translate_pol' size_mkseq.
Qed.

Lemma mkseq_shift :
  forall T (f : nat ->T) n, mkseq f n.+1 = f 0%nat::mkseq (fun x => f x.+1) n.
move => T f n; rewrite /mkseq -[n.+1]/(1+n)%nat iota_add addnC iota_addl /=.
by congr (cons (f 0%nat)); rewrite -map_comp; apply: eq_in_map; move => x _ /=.
Qed.

Lemma eval_pol_big :
  forall l x, eval_pol l x = \sum_(i < size l) nth 0 l i * x ^+ i.
Proof.
move => l x; elim: l=> [ | a l IHl]; first by rewrite big_ord0.
rewrite /= big_ord_recl /= mulr1 IHl; congr (fun v => a + v).
rewrite big_distrr; apply:eq_bigr => i _.
by rewrite /= [x * _]mulrC -mulrA [_ * x]mulrC exprS.
Qed.

Theorem pascal : forall a b n,
  (a + b) ^+ n = \sum_(i < n.+1) (Qbin n i * (a ^+ (n - i) * b ^+ i)).
Proof.
move=> a b; elim=> [|n IHn]; first by rewrite big_ord_recl big_ord0.
rewrite big_ord_recr big_ord_recl /= exprS {}IHn mulr_addl !big_distrr.
rewrite big_ord_recl big_ord_recr /= !Qbin0 !Qbinn !subn0 !subnn !mul1r !mulr1.
rewrite -!exprS addrA; congr (_ + _); rewrite -addrA -big_split; congr (_ + _).
apply: eq_bigr => i _ /=; rewrite 2!(mulrCA b) (mulrCA a) (mulrA a) -!exprS.
by rewrite -leq_subS ?ltn_ord // -mulr_addl -QbinS.
Qed.

Lemma translate_pol'q :
  forall l a x, eval_pol (translate_pol' l a) x = eval_pol l (x + a).
move => l a x; rewrite !eval_pol_big size_translate_pol' /translate_pol'.
apply: trans_equal (_ : \sum_(k < (size l).+1)
                      (\sum_(i < size l) Qbin k i* l`_k * a^+ (k - i) * x^+ i)
                       = _).
  rewrite exchange_big /=.
  by apply: eq_bigr => i _; rewrite nth_mkseq //= big_distrl.
apply sym_equal.
apply: trans_equal (_ : \sum_(i < size l)
                \sum_(0 <= j < i.+1) l`_i * Qbin i j * (x^+(i-j) * a ^+j) = _).
  apply: eq_bigr => i _; rewrite big_mkord pascal big_distrr /=.
  by apply: eq_bigr => j _; rewrite /= !mulrA.
have jgti : forall i : 'I_(size l),
      \sum_(i.+1 <= j < size l) l`_i * Qbin i j * (x ^+ (i - j) * a ^+ j) = 0.
  move => i; apply: big1_seq => j /=; rewrite mem_index_iota.
  by move/andP => [ilj _]; rewrite Qbin_small // mulr0 mul0r.
apply: trans_equal (_ : \sum_(i < size l)
        \sum_(j < size l) l`_i * Qbin i j * (x ^+ (i - j) * a ^+ j) = _).
  apply: eq_bigr => i _.
  rewrite -(@big_mkord Qcb 0 +%R (size l) (fun i => true)
   (fun j => l`_i * Qbin i j *(x ^+ (i - j) * a ^+ j))).
  by rewrite  (@big_cat_nat _ _ _ i.+1 0 (size l)) //= jgti addr0.
rewrite big_ord_recr /=.
have -> : \sum_(i < size l) Qbin (size l) i * l`_(size l) *
             a ^+ (size l - i) * x ^+i = 0.
  by apply: big1 => i _; rewrite nth_default // mulr0 !mul0r.
rewrite addr0; apply eq_bigr => i _.
rewrite -(@big_mkord Qcb 0 +%R (size l) (fun i => true)
   (fun j => l`_i * Qbin i j *(x ^+ (i - j) * a ^+ j))).
rewrite !(@big_cat_nat _ _ _ i.+1 0 (size l)) //= jgti addr0 big_mkord.
rewrite -(@big_mkord Qcb 0 +%R (size l) (fun i => true)
   (fun j => Qbin i j * l`_i * a ^+ (i - j) * x ^+ j)).
have jgti' :
   \sum_(i.+1 <= j < size l) Qbin i j * l`_i * a ^+ (i - j) * x ^+ j = 0.
  apply: big1_seq => j /=; rewrite mem_index_iota.
  by move/andP => [ilj _]; rewrite Qbin_small // !mul0r.
rewrite !(@big_cat_nat _ _ _ i.+1 0 (size l)) //= jgti' addr0 big_mkord.
set f := fun j:'I_i.+1 => (Ordinal ((leq_subr j i): (i - j) < i.+1)).
have finv: forall j:'I_i.+1, xpredT j -> f (f j) = j.
  by move => j _; apply: val_inj => /=; rewrite subKn //; have : j < i.+1.
rewrite (reindex_onto f f finv) /=.
have tmp :(fun j => f (f j) == j) =1 xpredT.
  by move=> j /=; apply/eqP; apply finv.
rewrite (eq_bigl _ _ tmp); apply: eq_bigr => j _.
have jli : j <= i by have : j < i.+1. 
by rewrite subKn // [x ^+ _ * _]mulrC [Qbin i j * _]mulrC !mulrA -Qbin_sub.
Qed.

Definition reciprocate_pol (l: seq Qcb) := rev l.

Lemma size_reciprocate : forall l, size (reciprocate_pol l) = size l.
Proof. by move=> l; rewrite /reciprocate_pol size_rev. Qed.

Lemma reciprocateq :
  forall l x, 0 <<! x -> 
     eval_pol (reciprocate_pol l) x = x ^+ (size l) * eval_pol l (x^-1).
move=> [ | a l] x xp; rewrite !eval_pol_big size_reciprocate.
  by rewrite !big_ord0 mulr0.
rewrite big_distrr /=.
set f := fun j:'I_(size l).+1 =>
          Ordinal (leq_subr j (size l):size l - j <(size l).+1).
have finv: forall j:'I_(size l).+1, xpredT j -> f (f j) = j.
  by move => j _; apply: val_inj => /=; rewrite subKn //;
      have : j < (size l).+1.
rewrite (reindex_onto f f finv) /=.
have tmp :(fun j => f (f j) == j) =1 xpredT.
  by move=> j /=; apply/eqP; apply finv.
rewrite (eq_bigl _ _ tmp); apply: eq_bigr => j _.
rewrite /reciprocate_pol nth_rev.

