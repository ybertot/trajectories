Require Import QArith ZArith Zwf Omega.
Require Import ssreflect ssrbool eqtype  ssrfun ssrnat binomial div seq choice.
Require Import fintype bigop fingroup ssralg poly orderedalg.
Require Export infra.

Import GroupScope .
Import GRing.Theory.
Import OrderedRing.Theory.
Open Local Scope ring_scope .

Set Printing Width 50.

Section ToBeAddedInOrderedAlg.

Section Idomain.

Variable (R : oIdomainType).
Lemma absr_sum : forall m  (G : nat -> R),
  `|\sum_(i < m) G i| <= \sum_(i < m) `|G i|.
Proof.
elim=> [|m ihm] G; first by rewrite !big_ord0 absr0 lerr.
rewrite !big_ord_recr /=; apply: lter_trans (absr_add_le _ _) _=> /=.
by rewrite ler_add2l; apply: ihm.
Qed.

Lemma ge0_sum : forall m (G : nat -> R), 
  (forall i, ((i < m)%N ->  0 <= G i)) -> 0 <= \sum_(i < m) G i.
Proof.
elim=> [|m ihm] G hp; first by rewrite big_ord0 lerr.
rewrite big_ord_recr /=; apply: lter_le_addpl=> //=; last by apply: hp; exact: ltnSn.
apply: ihm=> i ltim; apply: hp; apply: ltn_trans ltim _; exact: ltnSn.
Qed.

Lemma ge_sum :  forall m (G1 G2 : nat -> R), 
  (forall i, ((i < m)%N ->  G1 i <= G2 i)) -> \sum_(i < m) G1 i <= \sum_(i < m) G2 i.
Proof.
elim=> [|m ihm] G1 G2 hp; first by rewrite !big_ord0 lerr.
rewrite ! big_ord_recr /=; apply: lter_add=> /=; last by apply: hp; exact: ltnSn.
apply: ihm=> i ltim; apply: hp; apply: ltn_trans ltim _; exact: ltnSn.
Qed.

End Idomain.


Variable F : oFieldType.

Lemma gt1expn : forall n (x : F), 1 <= x -> 1 <= x^+n.
Proof.
elim=> [| m ihm] x hx; first by rewrite expr0 lerr.
rewrite exprS; apply: ler_trans (hx) _; rewrite -{1}(mulr1 x).
rewrite ltef_mulpl //=; first by exact: ihm.
by apply: lter_le_trans hx; rewrite /= ltr01.
Qed.


Lemma absrge1 : forall x : F, 1 < x -> x^-1 < 1.
Proof.
move=> x lt1x; rewrite -(mul1r (x^-1)) ltef_divpl /= ?mul1r //. 
apply: lter_trans lt1x; exact: ltr01.
Qed.

Lemma absf_inv : forall x : F, `|x ^-1| = `|x|^-1.
Proof.
move=> x; case e: (x == 0); first by rewrite (eqP e) absr0 invr0 absr0.
have axn0 : ~~ (`|x| == 0) by rewrite absr_eq0 e.
by apply: (mulfI axn0); rewrite mulfV // -absf_mul mulfV ?e // absr1.
Qed.

Lemma expf_gt1 : forall m (x : F), x > 1 -> x^+m.+1 > 1.
Proof.
elim => [|m ihm] x hx; first by rewrite expr1.
apply: lter_trans (hx) _ => /=; rewrite exprS -{1}(mulr1 x).
apply: lter_mulpl=> /=; last exact: ihm.
apply: lter_trans hx; exact: ltr01.
Qed.

Lemma expf_ge1 : forall m (x : F), x >= 1 -> x^+m >= 1.
Proof.
elim => [|m ihm] x hx; first by rewrite expr0 lerr.
apply: lter_trans (hx) _ => /=; rewrite exprS -{1}(mulr1 x).
apply: lter_mulpl=> /=; last exact: ihm.
apply: lter_trans hx; apply: ltrW; exact: ltr01.
Qed.

End ToBeAddedInOrderedAlg.

Section MoreMapPoly.

Variables (aR rR : ringType).

Variable f : aR -> rR.

Lemma map_polyC : forall c,
  map_poly f c%:P = if c == 0 then 0 else (f c)%:P.
Proof.
move=> a; rewrite /map_poly /= size_polyC.
case a0 : (a == 0); apply/polyP=> i; rewrite coef_poly //=.
by rewrite ltnNge lt0n !coefC; case: (i == 0)%N.
Qed.

End MoreMapPoly.

(*Polynomial obtained from p by taking the absolute values of the coefficients*)
Definition abs_pol (p : {poly Qcb}) := map_poly (@OrderedRing.absr _) p.

Lemma size_abs_pol p : size (abs_pol p) = size p.
Proof.
move=> p; case p0 : (p == 0).
  by rewrite  (eqP p0) /abs_pol /= map_polyC eqxx.
by rewrite /abs_pol /map_poly size_poly_eq // absr_eq0 lead_coef_eq0 p0.
Qed.

Lemma ler_absr_eval_pol : forall (p : {poly Qcb})(x : Qcb), 
  `|p.[x]| <= (abs_pol p).[`|x|].
Proof.
move=> p x; rewrite !horner_coef size_abs_pol.
rewrite (_ : \sum_(i < size p) _ * _ = \sum_(i < size p) `|p`_i * x ^+ i|).
  by apply: (@absr_sum _ (size p) (fun i =>  p`_i * x ^+ i)).
apply: congr_big => // [] [i hi] _.
by rewrite coef_poly /= hi absf_mul absf_exp.
Qed.

Lemma ler0_eval_pol_abs_pol :
  forall l x, 0 <= x -> 0 <= (abs_pol l).[x].
Proof.
move=> p x hx; rewrite /abs_pol /map_poly horner_poly. 
apply: (@ge0_sum _ _(fun i =>  `|p`_i| * x ^+ i)) => i hi.
by apply: mulr_ge0pp; rewrite ?absr_ge0 // expf_ge0.
Qed.


Lemma eval_pol_abs_pol_increase : 
  forall l x y, 0 <= x -> x <= y ->
    (abs_pol l).[x] <= (abs_pol l).[y].
move=> p x y hx hxy; rewrite /abs_pol /map_poly !horner_poly.
apply: (@ge_sum _ _ (fun i => `|p`_i| * x ^+ i) (fun i => `|p`_i| * y ^+ i)) => i leisp.
apply: lter_mulpl => /=; rewrite ?absr_ge0 //.
(* here a strangeness in orderedalg *)
case: i {leisp}; first by rewrite expr0 lerr.
by move=> n; rewrite lef_expS2 //; apply: ler_trans hxy.
Qed.

(* To describe polynomial addition, multiplication by a scalar, and
  multiplication, we simply specify these operations so that their
  interpretation through polynomial evaluation returns the corresponding
  scalar operation.

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
*)
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
  forall (p : {poly Qcb}) b, 0 < b ->
   {c | forall x y, 0 <= x -> x <= y -> y <= b -> 
    `|(p.[y] - p.[x])| <= c * (y - x)}.
Proof.
move=> p b bp; elim/poly_ind: p => [| p u [c cp]].
  by exists 0 => x y xp xy xc; rewrite mul0r !hornerC subrr absr0 lerr.
exists ((abs_pol p).[b] + c * b) => x y px hxy hyb. 
rewrite !horner_lin addrAC oppr_add addrA addrNK.
have py : 0 <= y by rewrite (ler_trans px).
have psyx : 0 <= y - x by rewrite lter_subrA /= add0r.
rewrite (_ : _ * y - _ = y * p.[y] - x * p.[y] + x * p.[y] - x * p.[x]); last first.
  by rewrite -[_ - _ + _]addrA addNr addr0 mulrC [_ * y]mulrC.
rewrite -addrA; apply: (ler_trans (absr_add_le _ _)).
rewrite -mulNr -mulr_addl -mulrN -mulr_addr !absf_mul (ger0_abs px).
rewrite (ger0_abs psyx) [_ * (y - x)]mulr_addl; apply: lter_add=> /=.
(*rewrite absr_nneg // [_ * (y - x)]mulr_addl; apply: lerT.*)
  rewrite mulrC lter_mulpr //=.   
  apply: (ler_trans (ler_absr_eval_pol p y)).
  by rewrite eval_pol_abs_pol_increase // ?absrpos // ger0_abs.
rewrite (mulrC c); apply ler_trans with (x * c * (y - x)).
  by rewrite -mulrA lter_mulpl //= cp.
rewrite -!mulrA lter_mulpr //= ?(ler_trans hxy) //.
by apply: ler_trans (cp _ _ px hxy hyb); apply: absr_ge0.
Qed.


Definition translate_pol (l : {poly Qcb}) (a:Qcb) :=
  \poly_(i < size l)
     \sum_(k < size l) nth 0 l k * a ^+ (k - i) *+ 'C(k, i).

(*
Definition translate_pol (l :seq Qcb) (a:Qcb) :=
  mkseq (fun i:nat =>
     \sum_(k < size l) nth 0 l k * a ^+ (k - i) *+ 'C(k, i)) (size l).
*)

(* Lemma size_translate_pol : forall l a,  *)
(*   size (translate_pol l a)  = size l. *)
(* Proof. by move => l a; rewrite /translate_pol size_mkseq. Qed. *)

Lemma size_translate_pol : forall l a,
  size (translate_pol l a)  = size l.
Proof.
  move => l a; rewrite /translate_pol.
case sl: (size l) => [| s]; last first.
  rewrite size_poly_eq //= big_ord_recr big1 /=.
  - rewrite add0r binn subnn mulr1 mulr1n -[s]/(s.+1.-1) -sl.
    by rewrite -/(lead_coef l) lead_coef_eq0 -size_poly_eq0 sl.
  by move=> [i hi] /= _; rewrite bin_small.
apply/eqP; rewrite size_poly_eq0; apply/eqP; apply/polyP=> i.
by rewrite coef_poly.
Qed.

Lemma eval_translate_pol : forall (p : {poly Qcb}) (a x : Qcb),
  (translate_pol p a).[x] = p.[x + a].
Proof.
move=> p a x; rewrite /translate_pol /= horner_poly.
rewrite horner_coef.
transitivity (\sum_(i < size p)
      \sum_(k < size p)
          p`_k * a ^+ (k - i) *+ 'C(k, i) * x ^+ i).
- by apply: congr_big => // i _; rewrite big_distrl.
rewrite exchange_big /=; apply: congr_big => // [[i hi]]  _ /=.
transitivity 
  (p`_i * \sum_(i0 < size p) a ^+ (i - i0) *+ 'C(i, i0) * x ^+ i0).
- rewrite big_distrr /=; apply: congr_big => // j _; rewrite mulrA.
  by congr (_ * _); rewrite mulrnAr.
congr (_ * _); rewrite addrC exprn_addl.
transitivity
  (\sum_(0 <= i0 < (size p)) a ^+ (i - i0) *+ 'C(i, i0) * x ^+ i0).
- symmetry; exact: big_mkord.
rewrite (big_cat_nat _ _ _ _ hi) ?leq0n //=. 
rewrite (_ : \sum_(i.+1 <= i0 < size p) _ = 0); last first.
- apply: big1_seq => /= [] k; rewrite mem_index_iota; case/andP=> hik hksp.
  by rewrite bin_small // mulr0n mul0r.
by rewrite big_mkord addr0; apply: congr_big=> // k _; rewrite mulrnAl.
Qed.

Lemma pol_eval_translate_pol : forall (p : {poly Qcb}) (a x : Qcb),
  p.[x] = (translate_pol p a).[x - a].
Proof. by move=> p a xl; rewrite eval_translate_pol addrNK. Qed.


(* Lemma eval_translate_pol : forall (p : {poly Qcb}) (a x : Qcb), *)
(*   (translate_pol p a).[x] = p.[x + a]. *)
(* Proof. *)
(* move=> p a x; rewrite horner_coef /translate_pol /= -horner_Poly. *)
(* rewrite horner_poly. *)
(* transitivity (\sum_(i < size p) *)
(*       \sum_(k < size p) *)
(*           p`_k * a ^+ (k - i) *+ 'C(k, i) * x ^+ i). *)
(* - by apply: congr_big => // i _; rewrite big_distrl. *)
(* rewrite exchange_big /=; apply: congr_big => // [[i hi]]  _ /=. *)
(* transitivity  *)
(*   (p`_i * \sum_(i0 < size p) a ^+ (i - i0) *+ 'C(i, i0) * x ^+ i0). *)
(* - rewrite big_distrr /=; apply: congr_big => // j _; rewrite mulrA. *)
(*   by congr (_ * _); rewrite mulrnAr. *)
(* congr (_ * _); rewrite addrC exprn_addl. *)
(* transitivity *)
(*   (\sum_(0 <= i0 < (size p)) a ^+ (i - i0) *+ 'C(i, i0) * x ^+ i0). *)
(* - symmetry; exact: big_mkord. *)
(* rewrite (big_cat_nat _ _ _ _ hi) ?leq0n //=.  *)
(* rewrite (_ : \sum_(i.+1 <= i0 < size p) _ = 0); last first. *)
(* - apply: big1_seq => /= [] k; rewrite mem_index_iota; case/andP=> hik hksp. *)
(*   by rewrite bin_small // mulr0n mul0r. *)
(* by rewrite big_mkord addr0; apply: congr_big=> // k _; rewrite mulrnAl. *)
(* Qed. *)


Lemma pol_cont : forall (l : {poly Qcb}) (x eps :Qcb), 0 < eps ->
  exists delta, 0 < delta /\ forall y,  `|(y - x)| < delta ->
    `|l.[y] - l.[x]| < eps.
Proof.
have side :  forall (l : {poly Qcb}) (x:Qcb) eps, 0 < eps ->
  exists delta, 0 < delta /\ forall y, x <= y -> `|(y - x)| < delta ->
    `|(l.[y] - l.[x])| < eps.
  move => l x e ep. (* move: (translate_pol l (x-1)) => [l' pl']*)
  have zlt2 : (0:Qcb) < 1 + 1 by [].
  case: (cm3 (translate_pol l (x -1)) _ zlt2) => c pc.
  have yxx1 : forall y, y - x = y - (x - 1) - (x - (x - 1)).
    by move => y; rewrite !oppr_add !opprK !addrA addrNK addrK.
  have leb0 : 0 <= x - (x - 1).
    by rewrite oppr_add opprK addrA addrN add0r ltrW // ltr_0_1.
  case c0 : (c == 0).
    exists 1; split=> //.
    move => y xy1 ycx.
    have cxy : (c * (y - x) < e) by rewrite (eqP c0) mul0r.
    rewrite 2!(pol_eval_translate_pol l (x - 1)).
    apply: ler_lte_trans cxy => /=.
    rewrite yxx1; apply: pc=> //; first by rewrite lter_add //= lerr.
    rewrite oppr_add addrA lter_add //= ltrW //; move: ycx; exact: lter_abs.
  have cp : (0 < c). 
    move: (negbT c0) =>{c0} c0.
    rewrite ltr_neqAle eq_sym c0 /=.
    have tmp : (1:Qcb) <= 1 + 1 by [].
    have := pc 0 1 (lerr _) (ltrW (ltr01 _)) tmp; move {tmp}.
    rewrite oppr0 addr0 mulr1=>tmp; apply: ler_trans tmp; exact: absr_ge0.
  have ecp: (0 < e / c) by rewrite mulr_gte0pp //= invf_gte0.
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
  have cp' : 0 < c^-1 by rewrite invf_gte0.  
  have xcy' : (c * (y - x)) < e.
    rewrite mulrC -ltef_divpr //=; apply: lter_le_trans e1ec=> /=; move: xcy.
    exact: lter_abs.
  apply: ler_lte_trans xcy'; rewrite (yxx1 y) 2!(pol_eval_translate_pol l (x - 1)).
  apply: pc => //; first by rewrite lter_add //= lerr.
    rewrite oppr_add addrA lter_add //= ltrW //; apply: lter_le_trans e11=> /=.
  by move: xcy; exact: lter_abs.
move => l x e ep.
move: (side l x e ep) => [delta1 [dp1 de1]].
pose l' := \poly_(i < size l) (l`_i * (- 1)^+i).
(*move: (mirror_pol l) => [l' pl'].*)
move: (side l' (-x) e ep) => [delta2 [dp2 de2]].
have : exists delta, 0 < delta /\ delta <= delta1 /\ delta <= delta2.
  case cmp: (delta1 < delta2).
    by exists delta1; split; last (split; first apply:lerr; apply: ltrW).
  exists delta2; split; first done; last (split; last apply:lerr).
  by move/negbFE: cmp.
move => [delta [dp [dd1 dd2]]].
  exists delta; split; first by [].
move => y ycx; case cmp: (y < x).
  have mirror : forall u, l.[u] = l'.[- u].
  - move=> u; rewrite /l' horner_coef horner_poly; apply: congr_big=> // i _.
  by rewrite -mulrA; congr (_ * _); rewrite -exprn_mull mulrN mulNr opprK mul1r.
  rewrite 2!mirror; apply: de2; first by rewrite -lter_opp2 /= ltrW.
  by rewrite -oppr_add absr_opp; apply: lter_le_trans dd2.
apply: de1; first by move/negbFE: cmp.
by apply: lter_le_trans dd1.
Qed.

Lemma Qcb_make0 : Qcb_make 0 = 0.
Proof. exact: val_inj. Qed.


Lemma Qcb_make1 : Qcb_make 1 = 1.
Proof. exact: val_inj. Qed.

(*
Definition Qbin m n := Qcb_make (Z_of_nat (binomial m n)).
*)

Lemma Qcb_makeadd: forall n m:Z, Qcb_make (n + m) = Qcb_make n + Qcb_make m.
Proof. 
by move=> n m; apply : val_inj; rewrite /=  -(eqP (Qcb_Z _)) /= !Zmult_1_r.
Qed.

(*
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
*)


Lemma mkseq_shift :
  forall T (f : nat ->T) n, mkseq f n.+1 = f 0%nat::mkseq (fun x => f x.+1) n.
Proof.
move => T f n; rewrite /mkseq -[n.+1]/(1+n)%nat iota_add addnC iota_addl /=.
by congr (cons (f 0%nat)); rewrite -map_comp; apply: eq_in_map; move => x _ /=.
Qed.

(*
Lemma eval_pol_big :
  forall l x, eval_pol l x = \sum_(i < size l) nth 0 l i * x ^+ i.
Proof.
move => l x; elim: l=> [ | a l IHl]; first by rewrite big_ord0.
rewrite /= big_ord_recl /= mulr1 IHl; congr (fun v => a + v).
rewrite big_distrr; apply:eq_bigr => i _.
by rewrite /= [x * _]mulrC -mulrA [_ * x]mulrC exprS.
Qed.
*)
Lemma pascalQ : forall (a b : Qcb) n,
  (a + b) ^+ n = \sum_(i < n.+1) ((a ^+ (n - i) * b ^+ i) *+ 'C(n, i)).
Proof.
move=> a b; elim=> [|n IHn]; first by rewrite big_ord_recl big_ord0.
rewrite big_ord_recr big_ord_recl /= exprS {}IHn mulr_addl !big_distrr.
rewrite big_ord_recl big_ord_recr /= !bin0 !binn !subn0 !subnn !mul1r !mulr1.
rewrite !mulr1n -!exprS addrA; congr (_ + _); rewrite -addrA -big_split. 
congr (_ + _); apply: eq_bigr => i _ /=; rewrite /bump leq0n /=.
rewrite  ![(1 + _)%N]addnC /= addn1 subSS !mulrnAr !mulrA -exprS -ltn_subS; last by case: i.
by rewrite [b * _]mulrC -mulrA -exprS -mulrn_addr -binS.
Qed.

(*
Lemma translate_pol'q :
  forall l a x, eval_pol (translate_pol' l a) x = eval_pol l (x + a).
Proof.
move => l a x; rewrite !eval_pol_big size_translate_pol' /translate_pol'.
apply: trans_equal (_ : \sum_(k < size l)
                      (\sum_(i < size l) l`_k * a^+ (k - i) * x^+ i *+ 'C(k, i))
                       = _).
  rewrite exchange_big /=.
   apply: eq_bigr => i _; rewrite nth_mkseq //= big_distrl /=.
   by apply: congr_big; [by [] | by []|] => j _; rewrite mulrnAl.
apply sym_equal.
apply: trans_equal (_ : \sum_(i < size l)
                \sum_(0 <= j < i.+1) l`_i * (x^+(i-j) * a ^+j *+ 'C(i, j)) = _).
  apply: eq_bigr => i _; rewrite big_mkord pascalQ big_distrr //=.
have jgti : forall i : 'I_(size l),
      \sum_(i.+1 <= j < size l) l`_i *+ 'C(i, j) * (x ^+ (i - j) * a ^+ j) = 0.
  move => i; apply: big1_seq => j /=; rewrite mem_index_iota.
  by move/andP => [ilj _]; rewrite bin_small // mulr0n mul0r.
apply: trans_equal (_ : \sum_(i < size l)
        \sum_(j < size l) l`_i *+ 'C(i, j) * (x ^+ (i - j) * a ^+ j) = _).
  apply: eq_bigr => i _.
  rewrite -(@big_mkord Qcb 0 +%R (size l) (fun i => true)
   (fun j => l`_i *+ 'C(i,  j) *(x ^+ (i - j) * a ^+ j))).
  rewrite  (@big_cat_nat _ _ _ i.+1 0 (size l)) //= jgti addr0.
  by apply: congr_big; [by [] | by []|] => j _;rewrite mulrnAl -!mulrnAr.
apply: eq_bigr => i _.
rewrite -(@big_mkord Qcb 0 +%R (size l) (fun i => true)
   (fun j => l`_i *+ 'C(i, j) *(x ^+ (i - j) * a ^+ j))).
rewrite !(@big_cat_nat _ _ _ i.+1 0 (size l)) //= jgti addr0 big_mkord.
rewrite -(@big_mkord Qcb 0 +%R (size l) (fun i => true)
   (fun j => l`_i * a ^+ (i - j) * x ^+ j *+ 'C(i,  j))).
have jgti' :
   \sum_(i.+1 <= j < size l)  l`_i * a ^+ (i - j) * x ^+ j *+ 'C(i, j) = 0.
  apply: big1_seq => j /=; rewrite mem_index_iota.
  by move/andP => [ilj _]; rewrite bin_small // !mul0r.
rewrite !(@big_cat_nat _ _ _ i.+1 0 (size l)) //= jgti' addr0 big_mkord.
set f := fun j:'I_i.+1 => (Ordinal ((leq_subr j i): ((i - j) < i.+1))%N).
have finv: forall j:'I_i.+1, xpredT j -> f (f j) = j.
  by move => j _; apply: val_inj => /=; rewrite subKn //; have : (j < i.+1)%N.
rewrite (reindex_onto f f finv) /=.
have tmp :(fun j => f (f j) == j) =1 xpredT.
  by move=> j /=; apply/eqP; apply finv.
rewrite (eq_bigl _ _ tmp); apply: eq_bigr => j _.
have jli : (j <= i)%N by have : (j < i.+1)%N. 
by rewrite subKn // mulrnAl [x ^+ _ * _]mulrC mulrA bin_sub.
Qed.
*)

Definition reciprocate_pol (l: {poly Qcb}) := \poly_(i < size l)l`_(size l - i.+1).


Lemma reciprocateq :
  forall (l : {poly Qcb}) x, x != 0 ->
     (reciprocate_pol l).[x] = x ^+ (size l - 1) * l.[x^-1].
Proof.
move=> l x xn0 ; rewrite /reciprocate_pol horner_poly.
case sl : (size l) => [| n].
  rewrite sub0n expr0 mul1r big_ord0; move/eqP: sl; rewrite size_poly_eq0.
  by move/eqP->; rewrite horner0.
rewrite horner_coef subn1 /=  big_distrr /=.
set f := fun j:'I_(n).+1 =>
          Ordinal (leq_subr j (n):n - j <(n).+1)%N.
have finv: forall j:'I_(n).+1, xpredT j -> f (f j) = j.
  by move => j _; apply: val_inj => /=; rewrite subKn //;
      have : (j < (n).+1)%N.
rewrite (reindex_onto f f finv) /=.
have tmp :(fun j => f (f j) == j) =1 xpredT.
  by move=> j /=; apply/eqP; apply finv.
rewrite (eq_bigl _ _ tmp) {tmp} sl; apply: eq_bigr => [[j hj]] _ /=.
rewrite subSS subKn // -mulrCA; congr (_ * _).
have xej : x^+j != 0 by exact: expf_neq0.
apply: (mulIf xej); rewrite {xej} -mulrA -exprn_mull mulVf // exp1rn mulr1.
by rewrite -exprn_addr subnK.
Qed.

Definition expand (l : {poly Qcb})(r : Qcb) :=
  \poly_(i < size l)(l`_i * r ^+i).

(* Lemma size_expand : forall l r, size (expand l r) = size l. *)
(* Proof. by move=> l r; rewrite /expand size_mkseq. Qed. *)

(* The correction lemma for expand. *)
Lemma eval_expand : forall l r x, 
  (expand l r).[x] = l.[r * x].
Proof.
move => l r x.
rewrite /expand horner_poly horner_coef; apply: congr_big=> // [[i hi]] _ /=.
by rewrite exprn_mull mulrA.
Qed.

(* The Berstein coefficients of polyniomal l for the interval (a, b) *)

Definition Bernstein_coeffs (l: {poly Qcb})(a b : Qcb) : {poly Qcb} :=
  translate_pol (reciprocate_pol (expand (translate_pol l a) (b - a))) 1.


