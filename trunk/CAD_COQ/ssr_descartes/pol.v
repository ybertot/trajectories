Require Import QArith ZArith Zwf Omega.
Require Import ssreflect ssrbool eqtype  ssrfun ssrnat binomial div seq choice.
Require Import fintype bigops groups ssralg orderedalg.
Require Export infra.

Import GroupScope .
Import GRing.Theory.
Import OrderedRing.Theory.
Open Local Scope ring_scope .

Set Printing Width 50.


Fixpoint eval_pol l (x : Qcb) :=
  if l is a :: tl then a + x * eval_pol tl x else 0.


(* Polynomial are only represented by the list of their coefficients.
  To any polynomial, we associate the absolute polynomial, whose
  coefficients are the absolute values of the initial coefficients. *)

Fixpoint abs_pol (l : seq Qcb) : seq Qcb :=
 if l is a::tl then absr a :: abs_pol tl else nil.

(* The value of the absolute polynomial is always larger than the value
 of the initial polynomial. *)

(* The absolute value notation does not work well. Notation should change. *)
Lemma ler_absr_eval_pol :
  forall (l : seq Qcb)(x : Qcb), 
  |eval_pol l x| <= eval_pol (abs_pol l) (|x|).
Proof.
elim => [|y s IHs] x /=; first by rewrite absr0.
apply: (ler_trans (absr_add_le _ _)); rewrite ler_add2r.
rewrite absf_mul; move: (absr_ge0 x); rewrite ler_eqVlt.
by case/orP; [move/eqP<-; rewrite !mul0r lerr | move/ltf_mulpl->].
Qed.

Lemma ler0_eval_pol_abs_pol :
  forall l x, 0 <= x -> 0 <= eval_pol (abs_pol l) x.
Proof.
elim => [| y s Ihs] x hx /=; rewrite ?lerr ?ler_addpl ?absr_ge0 // mulr_cp0p //.
exact: Ihs.
Qed.


Lemma eval_pol_abs_pol_increase : 
  forall l x y, 0 <= x -> x <= y ->
    eval_pol (abs_pol l) x <= eval_pol (abs_pol l) y.
elim=> [|u s Ihs] x y hx hy /=; first by rewrite lerr.
rewrite ler_add2r; apply: (@ler_trans _ (y * eval_pol (abs_pol s) x)).
  by rewrite ler_mulpr ?ler0_eval_pol_abs_pol.
by rewrite ler_mulpl ?Ihs // (ler_trans hx).
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
Proof.
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


(* Canonical Structure Qcb_make (n : Z) := QcbMake (Qcb_Z n).*)
Definition Qcb_make (n : Z) := QcbMake (Qcb_Z n).

Lemma cm3 :
  forall b, 0 < b -> forall l, 
   {c | forall x y, 0 <= x -> x <= y -> y <= b -> 
    |(eval_pol l y - eval_pol l x)| <= c * (y - x)}.
move=> b pb; elim=> [|u l [c cp]] /=.
  by exists 0 => x y; rewrite subrr absr0 mul0r lerr.
exists ((eval_pol (abs_pol l) b) + c * b) => x y px hxy hyb. 
rewrite addrAC oppr_add addrA subrr add0r addrC.
set el := eval_pol l in cp *.
rewrite (_ : y *_ - _ = y * el y - x * el y + x * el y - x * el x); last first.
  by rewrite -[_ - _ + _]addrA addNr addr0.
have py : 0 <= y by rewrite (ler_trans px).
have psyx : 0 <= y - x by rewrite ler_subrA add0r.
rewrite -addrA; apply: (ler_trans (absr_add_le _ _)).
rewrite -mulNr -mulr_addl -mulrN -mulr_addr !absf_mul (ger0_abs px).
rewrite (ger0_abs psyx) [_ * (y - x)]mulr_addl; apply: ler_add.
(*rewrite absr_nneg // [_ * (y - x)]mulr_addl; apply: lerT.*)
  rewrite mulrC ler_mulpr //; apply: (ler_trans (ler_absr_eval_pol l y)).
  by rewrite eval_pol_abs_pol_increase // ?absrpos // ger0_abs.
rewrite (mulrC c); apply ler_trans with (x * c * (y - x)).
  by rewrite -mulrA ler_mulpl // cp.
rewrite -!mulrA ler_mulpr // ?(ler_trans hxy) //.
by apply: ler_trans (cp _ _ px hxy hyb); apply: absr_ge0.
Qed.

Lemma pol_cont : forall l (x:Qcb) eps, 0 < eps ->
  exists delta, 0 < delta /\ forall y,  |(y - x)| < delta ->
    |(eval_pol l y - eval_pol l x)| < eps.
have side :  forall l (x:Qcb) eps, 0 < eps ->
  exists delta, 0 < delta /\ forall y, x <= y -> |(y - x)| < delta ->
    |(eval_pol l y - eval_pol l x)| < eps.
  move => l x e ep; move: (translate_pol l (x-1)) => [l' pl'].
  have zlt2 : (0:Qcb) < 1 + 1 by [].
  move: (cm3 _ zlt2  l') => [c pc].
  have yxx1 : forall y, y - x = y - (x - 1) - (x - (x - 1)).
    by move => y; rewrite !oppr_add !opprK !addrA addrNK addrK.
  have leb0 : 0 <= x - (x - 1).
    by rewrite oppr_add opprK addrA addrN add0r ltrW // ltr_0_1.
  case c0 : (c == 0).
    exists 1; split=> //.
    move => y xy1 ycx.
    have cxy : (c * (y - x) < e) by rewrite (eqP c0) mul0r. 
    rewrite !pl'; apply: ler_lt_trans cxy. 
    rewrite yxx1; apply: pc=> //; first by rewrite ler_add //= lerr.
    rewrite oppr_add addrA ler_add // ltrW //; move: ycx; rewrite absr_lt //.
    by case/andP.
  have cp : (0 < c). 
    move: (negbT c0) =>{c0} c0.
    rewrite ltr_neqAle eq_sym c0 /=.
    have tmp : (1:Qcb) <= 1 + 1 by [].
    have := pc 0 1 (lerr _) (ltrW (ltr01 _)) tmp; move {tmp}.
    rewrite oppr0 addr0 mulr1=>tmp; apply: ler_trans tmp; exact: absr_ge0.
  have ecp: (0 < e / c) by rewrite mulf_gt0 ep -invf_le0 cp.
  have ie1: exists e1, 0 < e1 /\ e1 <= 1 /\ e1 <= e/c.
    case cmp : (e/c < 1).
      exists (e/c).
      by split; first done; split; last apply:lerr; apply ltrW.
    exists 1; split; first done; split; first apply:lerr.
    by move/negbFE: cmp.
  move: ie1 => [e1 [e1p [e11 e1ec]]].
  exists e1; split; first by [].
  move => y xy xcy.
(*  rewrite absr_ge0 in xcy; last by rewrite -(lerTlb x) addrNK add0r.*)
  have cp' : 0 < c^-1 by rewrite -invf_le0.  
  have xcy' : (c * (y - x)) < e.
    rewrite mulrC -lef_divpl //; apply: ltr_le_trans e1ec; move: xcy.
    by rewrite absr_lt ?(ltrW e1p) //; case/andP.
  apply: ler_lt_trans xcy'; rewrite (yxx1 y) !pl'.
  apply: pc => //; first by rewrite ler_add //= lerr.
    rewrite oppr_add addrA ler_add // ltrW //; apply: ltr_le_trans e11.
  by move: xcy; rewrite absr_lt // ?(ltrW e1p) //; case/andP=> _.
move => l x e ep.
move: (side l x e ep) => [delta1 [dp1 de1]].
move: (mirror_pol l) => [l' pl'].
move: (side l' (-x) e ep) => [delta2 [dp2 de2]].
have : exists delta, 0 < delta /\ delta <= delta1 /\ delta <= delta2.
  case cmp: (delta1 < delta2).
    by exists delta1; split; last (split; first apply:lerr; apply: ltrW).
  exists delta2; split; first done; last (split; last apply:lerr).
  by move/negbFE: cmp.
move => [delta [dp [dd1 dd2]]].
  exists delta; split; first by [].
move => y ycx; case cmp: (y < x).
  rewrite -(opprK x) -(opprK y) !pl'.
  apply: de2; first by rewrite -ler_opp2 ltrW.
  by rewrite -oppr_add absr_opp; apply: ltr_le_trans dd2.
apply: de1; first by move/negbFE: cmp.
by apply: ltr_le_trans dd1.
Qed.

Lemma Qcb_make0 : Qcb_make 0 = 0.
Proof. exact: val_inj. Qed.

Lemma Qcb_make1 : Qcb_make 1 = 1.
Proof. exact: val_inj. Qed.

Definition Qbin m n := Qcb_make (Z_of_nat (binomial m n)).

Lemma Qcb_makeadd: forall n m:Z, Qcb_make (n + m) = Qcb_make n + Qcb_make m.
Proof. 
by move=> n m; apply : val_inj; rewrite /=  -(eqP (Qcb_Z _)) /= !Zmult_1_r.
Qed.

Lemma QbinS : forall m n, Qbin m.+1 n.+1 = Qbin m n.+1 + Qbin m n.
Proof. move=> m n; by rewrite  /Qbin binS inj_plus Qcb_makeadd. Qed.

Lemma  Qbin0 : forall m, Qbin m 0 = 1.
Proof. by move=> m;rewrite /Qbin bin0 Qcb_make1. Qed.

Lemma Qbinn : forall n, Qbin n n = 1.
Proof. move=> n; by rewrite /Qbin binn Qcb_make1. Qed.

Lemma Qbin_sub : forall n m : nat, (m <= n)%N -> Qbin n m = Qbin n (n - m).
Proof. by move=> n m nlm; rewrite /Qbin bin_sub. Qed.
   
Lemma Qbin_small : forall m n, (m < n)%N -> Qbin m n = 0.
Proof. by move=> m n mln; rewrite /Qbin bin_small // Qcb_make0. Qed.

Definition translate_pol' (l :seq Qcb) (a:Qcb) :=
  mkseq (fun i:nat =>
     \sum_(k < (size l).+1) Qbin k i * nth 0 l k * a ^+ (k - i)) (size l).

Lemma size_translate_pol' : forall l a, size (translate_pol' l a)  = size l.
Proof. by move => l a; rewrite /translate_pol' size_mkseq. Qed.

Lemma mkseq_shift :
  forall T (f : nat ->T) n, mkseq f n.+1 = f 0%nat::mkseq (fun x => f x.+1) n.
Proof.
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

Lemma pascal : forall a b n,
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
Proof.
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
set f := fun j:'I_i.+1 => (Ordinal ((leq_subr j i): ((i - j) < i.+1))%N).
have finv: forall j:'I_i.+1, xpredT j -> f (f j) = j.
  by move => j _; apply: val_inj => /=; rewrite subKn //; have : (j < i.+1)%N.
rewrite (reindex_onto f f finv) /=.
have tmp :(fun j => f (f j) == j) =1 xpredT.
  by move=> j /=; apply/eqP; apply finv.
rewrite (eq_bigl _ _ tmp); apply: eq_bigr => j _.
have jli : (j <= i)%N by have : (j < i.+1)%N. 
by rewrite subKn // [x ^+ _ * _]mulrC [Qbin i j * _]mulrC !mulrA -Qbin_sub.
Qed.

Definition reciprocate_pol (l: seq Qcb) := rev l.

Lemma size_reciprocate : forall l, size (reciprocate_pol l) = size l.
Proof. by move=> l; rewrite /reciprocate_pol size_rev. Qed.

Lemma reciprocateq :
  forall l x, GRing.unit x -> 
     eval_pol (reciprocate_pol l) x = x ^+ (size l - 1) * eval_pol l (x^-1).
Proof.
move=> [ | a l] x xp; rewrite !eval_pol_big size_reciprocate.
  by rewrite !big_ord0 mulr0.
rewrite big_distrr /=.
set f := fun j:'I_(size l).+1 =>
          Ordinal (leq_subr j (size l):size l - j <(size l).+1)%N.
have finv: forall j:'I_(size l).+1, xpredT j -> f (f j) = j.
  by move => j _; apply: val_inj => /=; rewrite subKn //;
      have : (j < (size l).+1)%N.
rewrite (reindex_onto f f finv) /=.
have tmp :(fun j => f (f j) == j) =1 xpredT.
  by move=> j /=; apply/eqP; apply finv.
rewrite (eq_bigl _ _ tmp) {tmp}; apply: eq_bigr => j _.
have jls : (j < (size l).+1)%N by [].
rewrite /reciprocate_pol nth_rev; last by apply: leq_subr.
rewrite /= !subSS subKn // subn0 mulrA [(x ^+ (size l)) * _]mulrC -mulrA.
congr ((a :: l)`_j * _).
have tmp : size l = ((size l - j) + j)%N by rewrite subnK //.
by rewrite {3}tmp {tmp} expr_inv exprn_addr mulrK //; apply: unitr_exp.
Qed.

Definition expand (l : seq Qcb) (r : Qcb) :=
  mkseq (fun i => l`_i * r ^+i) (size l).

(* This lemma is important for the view of polynomial evaluation as an instance
 of a big operation. *)
Lemma size_expand : forall l r, size (expand l r) = size l.
Proof. by move=> l r; rewrite /expand size_mkseq. Qed.

(* The correction lemma for expand. *)
Lemma eval_expand : forall l r x, eval_pol (expand l r) x = eval_pol l (r * x).
Proof.
move => l r x; rewrite !eval_pol_big size_expand; apply: eq_bigr => i _.
by rewrite /expand nth_mkseq /= // exprn_mull mulrA. 
Qed.

(* The Berstein coefficients of polyniomal l for the interval (a, b) *)

Definition Bernstein_coeffs (l: seq Qcb)(a b : Qcb) : seq Qcb :=
  translate_pol' (reciprocate_pol (expand (translate_pol' l a) (b-a))) 1.


