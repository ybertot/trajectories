Require Import QArith ZArith Zwf Recdef Omega.
Require Import ssreflect eqtype ssrbool ssrnat div fintype seq ssrfun pol.
Require Import bigops groups choice .
Require Export ssralg xssralg infra .

Import GroupScope .
Import GRing.Theory .
Import GOrdered.
Open Local Scope ring_scope .

Set Printing Width 50.
(* After a use of simpl, products of positive integers are replaced by
 products of positive numbers encapsulated in a Zpos constructor.  This
 precludes uses of some theorems.  We can undo this using the following
 tactic. *)

Ltac expand_Zpos_mult := 
  repeat match goal with |- context [Zpos(?a * ?b)] => 
     change (Zpos(a*b)) with ((Zpos a)*(Zpos b))%Z
  end.

(* We want to prove a simple and contructive approximation of the
 middle value theorem: if a polynomial is negative in a and positive in b,
 and a < b, then for any positive epsilon, there exists c and d, so that 
 a <= c < d <= b, the polynomial is negative in c and positive and d,
 and the variation between c and d is less than epsilon.  To prove this,
 we use a second polynomial, obtained by taking the the absolute value
 of each coefficient.
*)

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

(* A polynomial that has distinct values cannot be the null
 polynomial. *)

Lemma cm1 :
  forall l x y, eval_pol l x <<! eval_pol l y  -> exists a, l = a :: (behead l).
by move=> [| u l] x y /=; rewrite ?ltr_irrefl //; move=> h; exists u.
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


Lemma translate_pol :
  forall l a, exists l', forall x, eval_pol l x = eval_pol l' (x - a).
elim=> [| b l Ihl]; move=> a /=.
- by exists [::].
- case (Ihl a) => l' h; case (mult_pol [:: a ; 1] l') => l2 h2.
  case (add_pol [:: b] l2) => l3 h3.
  exists l3; move=> x; rewrite -h3 -h2 h /= mulr0 !addr0 mulr1.
  by rewrite (_ : a + (x - a) = x) // -oppr_sub oppr_add addrA addrN add0r opprK.
Qed.


Lemma cm2 :
  forall l b, { c |
  forall x, 0 <<= x -> x <<= b -> absr (eval_pol l x - eval_pol l 0) <<= c * x}.
Proof.
move=> l b; case: l =>[| a l].
- by exists 0; move=> /= x; rewrite mul0r oppr0 addr0 absr0 ler_refl.
- exists (eval_pol (abs_pol l) b) => x px xb /=; rewrite mul0r addr0.
  rewrite addrC addKr absr_mulr absr_nneg // mulrC ler_rcompat //.
  rewrite (ler_trans (ler_absr_eval_pol _ _)) //.
  by rewrite eval_pol_abs_pol_increase // ?absrpos // absr_nneg.
Qed.

(* Cannot be abstracted since not every ordered ring has a floor ring *)
Lemma QZ_bound : forall x:Q, (0 <= x)%Q -> {n : Z | x <= n#1}%Q.
intros [n d]; exists(Zdiv n (Zpos d)+1)%Z.
assert (dpos : (('d) > 0)%Z) by apply (refl_equal Gt).
unfold Qle; simpl; rewrite Zmult_1_r; rewrite Zmult_plus_distr_l.
rewrite Zmult_1_l {1}(Z_div_mod_eq n ('d)) //.
rewrite (Zmult_comm ('d)); apply Zplus_le_compat; auto with zarith.
destruct (Z_mod_lt n ('d)) as [_ H2]; auto.
by apply Zlt_le_weak.
Defined.

(* Not used but should also be treated in xssralg
Lemma Qdiv_lt_0_compat : forall x y, 0 < x -> 0 < y -> 0 < x / y.
intros x [[ | p | p] d] Hx Hy; unfold Qdiv, Qinv; simpl.
unfold Qlt in Hy; simpl in Hy; elimtype False; omega.
rewrite Qmult_comm;
assert (H0 : 0 == 0 * x) by ring; rewrite H0.
apply Qmult_lt_compat_r; auto.
unfold Qlt in Hy; simpl in Hy; discriminate Hy.
Qed.
*)

Lemma cm3 :
  forall b, 0 <<! b -> forall l, 
   {c | forall x y, 0 <<= x -> x <<= y -> y <<= b -> 
    absr (eval_pol l y - eval_pol l x) <<= c * (y - x)}.
move=>b pb; elim=> [|u l [c cp]] /=.
  by exists 0 => x y; rewrite subrr absr0 mul0r ler_refl.
exists ((eval_pol (abs_pol l) b) + c * b) => x y px hxy hyb. 
rewrite addrAC oppr_add addrA subrr add0r addrC.
set el := eval_pol l in cp *.
rewrite (_ : y *_ - _ = y * el y - x * el y + x * el y - x * el x); last first.
  by rewrite -[_ - _ + _]addrA addNr addr0.
have py : 0 <<= y by rewrite (ler_trans px).
have psyx : 0 <<= y - x by rewrite -(subrr x) lerTl.
rewrite -addrA; apply: (ler_trans (absr_addr _ _)).
rewrite -mulNr -mulr_addl -mulrN -mulr_addr !absr_mulr (absr_nneg px).
rewrite absr_nneg // [_ * (y - x)]mulr_addl; apply: lerT.
  rewrite mulrC ler_rcompat //; apply: (ler_trans (ler_absr_eval_pol l y)).
  by rewrite eval_pol_abs_pol_increase // ?absrpos // absr_nneg.
rewrite (mulrC c); apply ler_trans with (x * c * (y - x)).
  by rewrite -mulrA ler_lcompat ?cp.
rewrite -!mulrA ler_rcompat // ?(ler_trans hxy) //.
by rewrite  (ler_trans (absrpos (el y - el x))) // cp.
Qed.


Definition find_pair : forall A:eqType, forall P:A->bool, forall Q:A->A->Prop,
    forall l:seq A, forall a b:A, P a -> ~P b ->
    (forall l1 l2 x y, a::l ++ b::nil= l1 ++ x :: y :: l2 -> Q x y) ->
    {c :A & { d | Q c d /\ P c /\ ~P d}}.
move => A P Q l; elim: l => [ | a l IHl] a' b' Pa Pb connect. 
  by exists a'; exists b'; split => //; apply: (connect [::] [::]).
case Pa1: (P a).
  have tmp :
     forall l1 l2 x y,  a :: l ++ [:: b' ]= l1 ++ [::x, y & l2] -> Q x y.
    by move => l1 l2 x y q; apply: (connect (a'::l1) l2); rewrite /= q.
  move: (IHl a b' Pa1 Pb tmp) => [c [d [cd Pc]]].
  by exists c; exists d.
exists a'; exists a; split.
  by apply (connect nil (l++b'::nil)).
by split; first done; rewrite Pa1.
Qed.

Fixpoint nat_ns (p : Z)(n : nat) :=
  match n with
    |0 => [:: p]
    |m.+1 => (p - (Z_of_nat m.+1)) :: nat_ns p m
  end.

Definition ns p n :=
  match n with
    |Zpos q => nat_ns p (nat_of_P q)
    |_ => [:: p]
  end.

Lemma ltb_Zneg0 : forall x, (Zneg x) <<! 0.
Proof. move=> x; apply/ Zlt_is_lt_bool; exact: Zlt_neg_0. Qed.

Lemma leb_Zneg0N : forall x, 0 <<= (Zneg x) = false.
Proof. by move=> x; rewrite lerNgtr ltb_Zneg0. Qed.

Lemma nat_ns_head : forall (p : Z) n, 
  exists l, nat_ns p n = (p - (Z_of_nat n)) :: l.
Proof.
move=> p; elim=>[|n [l Ih]] /=.
  by rewrite oppr0 addr0; exists [::].
by rewrite Ih; exists [:: p - Z_of_nat n & l].
Qed.

Lemma ns_head :  forall p n :Z, (0 <<= n) -> exists l, ns p n = (p - n) :: l.
Proof.
move=> p [|n|n] /=; last 1 first.
- by rewrite leb_Zneg0N.
- by exists [::]; rewrite oppr0 addr0.
- move=> _; set m := nat_of_P n; case: (nat_ns_head p m)=> l' ->; exists l'.
  by rewrite /m Zpos_eq_Z_of_nat_o_nat_of_P.
Qed.

Lemma nat_ns_step : forall p n, forall l1 l2 x y,
  nat_ns p n = l1 ++ [:: x, y & l2] -> y = x + 1.
Proof.
move=> p; elim=> [|n Ihn] l1 l2 x y /=.
  by move/(congr1 size)=> /=; rewrite size_cat /= !addnS; move/eqP; rewrite eqSS.
case: l1 => [|u l3] /=; last by case=> _; move/Ihn.
case=> <-; case: (nat_ns_head p n)=> [l' ->]; case=> <- _.
rewrite Zpos_P_of_succ_nat /Zsucc /= -[(_ + 1)%Z]/((Z_of_nat n) + 1) oppr_add addrA.
by rewrite addrK.
Qed.


Lemma ns_step : forall p n, forall l1 l2 x y, 0 <<= n ->
  ns p n = l1 ++ [:: x, y & l2] -> y = x + 1.
Proof.
move=> p [|n|n] /=; last 1 first.
- by rewrite leb_Zneg0N.
- move=> ? ? ? ? ?.
  by move/(congr1 size)=> /=; rewrite size_cat /= !addnS; move/eqP; rewrite eqSS.
- move=> l1 l2 x y _; exact: nat_ns_step.
Qed.

Lemma nat_ns_tail : forall p n, exists l, nat_ns p n = l ++ [:: p].
Proof.
move=> p; elim=> [|n [l' Ihn]] /=.
- by exists [::]; rewrite cat0s.
- by rewrite Ihn; exists [:: (p - (' P_of_succ_nat n)%Z) & l']; rewrite cat_cons.
Qed.
  
Lemma ns_tail : forall p n, exists l, ns p n = l ++ p ::nil.
Proof.
move=> p [|n|n] /=. 
- by exists [::]; rewrite cat0s.
- by case: (nat_ns_tail p (nat_of_P n))=> l' ->; exists l'.
- by exists [::]; rewrite cat0s.
Qed.

(* Lemmas about minus are missing in xssralg .. .*)
Lemma nat_ns_bounds : forall p n x l1 l2, nat_ns p n = l1 ++ [:: x & l2] -> 
        (p - Z_of_nat n <<= x) && (x <<= p).
Proof.
move=> p; elim=> [|n Ihn] x l1 l2 /= h.
- rewrite oppr0 addr0. 
  suff exp : p = x by rewrite exp ler_refl.
  case: l1 h => /=; first by case.
  move=> z s.
  by move/(congr1 size)=> /=; rewrite size_cat /= !addnS; move/eqP; rewrite eqSS.
- case: l1 h => [| u l1] /=.
  + set sn := (' _)%Z; case=> h _; rewrite -h ler_refl /= -(lerTlb (- p)) addrN.
    by rewrite addrC addKr ltrW // ltb_Zneg0.
  + case=> _; move/Ihn; case/andP=> h1 h2; rewrite h2 andbT; apply: ler_trans h1.
    rewrite -(lerTrb (- p)) !addrA addNr !add0r ler_oppger Zpos_P_of_succ_nat /Zsucc.
    rewrite -(lerTlb (- (Z_of_nat n))) addrN -[Zplus _ _]/(Z_of_nat n + 1).
    by rewrite -addrAC addrN add0r ltrW // ltr_0_1.
Qed.

Lemma ns_bounds : forall p n x l1 l2, 0 <<= n -> ns p n = l1 ++ x::l2 -> 
        (p - n <<= x) && ( x <<= p).
Proof.
move=> p [| n | n] x l1 l2 /=.
- move=> _ h; rewrite oppr0 addr0.
  suff exp : p = x by rewrite exp ler_refl.
  case: l1 h => /=; first by case.
  move=> z s.
  by move/(congr1 size)=> /=; rewrite size_cat /= !addnS; move/eqP; rewrite eqSS.
- by move=> _; move/nat_ns_bounds; rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
- by rewrite leb_Zneg0N.
Qed. 

Lemma map_contiguous :
forall (A B : Type)(f : A -> B) l l1 l2 a b,
  map f l = l1 ++ [:: a, b & l2] ->
  {l'1 : seq A & 
    {l'2 : seq A & 
      {x : A & 
        {y : A | [/\ l1 = map f l'1, l2= map f l'2, a = f x,
          b = f y & l = l'1 ++ [:: x, y & l'2]]}}}}.
Proof.
intros A B f; elim=> [|x l Ihl] /= l1 l2 a b h; first by case: l1 h.
case: l Ihl h => [|a' l'] /= h.
- by move/(congr1 size)=> /=; rewrite size_cat /= !addnS; move/eqP; rewrite eqSS.
- case: l1 h => [|a1 l1] /= h.
    by case=> <- <- <-; exists [::]; exists l'; exists x; exists a' => /=.
  case=> e1; move/h => [l1' [l2' [x' [y' [h1 h2 h3 h4 h5]]]]].
  exists [:: x & l1']; rewrite /= -h1 h2 e1; exists l2'; exists x'; exists y'.
  by split=> //; rewrite h5.
Qed.

(*This is map_cat.
Lemma map_app :
  forall A B:Type, forall f : A -> B, forall l1 l2, map f (l1++l2) = map f l1 ++ map f l2.
intros A B f l1; induction l1; simpl; auto.
intros l2; rewrite IHl1; auto.
Qed.
*)


Lemma non_empty_tail : 
  forall (A : Type) (a : A) l, exists l', exists b, [:: a & l] = l' ++ [::b].
Proof.
move=> A a l; elim: l a => [| x l  Ihl] a.
- by exists [::]; exists a.
- case: (Ihl x)=> s [b Ihb]; rewrite Ihb; exists [:: a & s]; exists b.
  by rewrite cat_cons.
Qed.

(* wait and see ...
Lemma Qfrac_add_Z_l : forall a b c,
  (a # 1) + (b # c)%Q = ( a * ' c + b # c)%Q :> Qcb.
intros;unfold Qeq; simpl; ring.
Qed.
*)


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


Lemma constructive_mvt :
  forall l x y, x <<! y -> eval_pol l x <<! 0%R -> 0%R <<= eval_pol l y  ->
       forall epsilon, 0 <<! epsilon ->
       exists x', exists y',  - epsilon <<= eval_pol l x' /\
         eval_pol l x' <<! 0 /\ 0 <<= eval_pol l y' /\
         eval_pol l y' <<= epsilon /\ x <<= x' /\ x' <<! y' /\ y' <<= y.
Proof.
move=> l a b ab nla plb.
have ba' : 0 <<! b - a by rewrite -(addrN a) ltrTlb.
(*have mpolapos : 0 <<! - eval_pol l a by rewrite gtr0_ltNr0 opprK.*)
have evalba : 0 <<! eval_pol l b - eval_pol l a. 
  rewrite  -(ltrTlb (eval_pol l a)) add0r -addrA addNr addr0.
  exact: ltr_ler_trans plb.
case: (translate_pol l a) => l' q.
case: (@cm3 (b - a) ba' l') => /= c pc.
have cpos : 0 <<! c.
  apply: (ltr_Ilcompat_l ba'); rewrite mul0r -[b -a]addr0 -{2}oppr0.
  apply: ltr_ler_trans (pc 0 (b - a) _ _ _); rewrite ?ler_refl ?ltrW //.
  by rewrite -{2}(addrN a) -!q absr_nneg ?ltrW.
move=> eps pe.
have pdiv : (0 <<! (b - a) * c / eps).
  by apply: ltr_0_lcompat; rewrite ?invr_ltr // ltr_0_lcompat.
move: (pdiv); move/ltrW; move/Qcb_lebP; case/QZ_bound => n qn.
(* assia : canonical structures are missing here for Z -> Qcb *)
have admit1 : 0 <<! n by admit.
have mkl: 
  exists l, forall l1 l2 x y, 
    [:: a & l] ++ [:: b] = l1 ++ [:: x, y & l2] ->
    y - x = (b - a) / (Qcb_make n) /\ 
    exists k : Z, 
      x = a + (b - a)* (Qcb_make k)/ (Qcb_make n) /\ 
      (0<<= k) /\ (k <<= n - 1).
  case en : (n == 1).
  - rewrite (eqP en); exists [::] => l1 l2 x y /=; case: l1 => [| t1 ql1] /=.
      case=> e1 e2 e3; rewrite e1 e2 Qcb_make1 invr1 mulr1; split=> //.
      by exists 0; rewrite addrN ler_refl Qcb_make0 mulr0 mul0r addr0; split.
    by move/(congr1 size)=> /=; rewrite size_cat /= !addnS; move/eqP; rewrite eqSS.
  - exists (map  (fun x => a + (b-a)*((Qcb_make x)/(Qcb_make n))) (ns (n-1) (n-2))).
    move=> l1 l2 x y; case: l1 => [|t1 ql1] /=.
      have h1 : 0 <<= n - 2%Z by admit.
      case: (ns_head (n - 1) (n - 2) h1) => a1 qa1.
      rewrite qa1 /= (_ : (n - 1) - (n - 2)%Z = 1) ?Qcb_make1; last first.
      by rewrite addrAC [-(n - 2%Z)]oppr_add addrA opprK addrN add0r. 
      case => -> <- /=; split.
        by rewrite addrAC addrN add0r mulrA mulr1.
      have admit2 : leb 0 (n - 1) by admit.
      exists 0; rewrite Qcb_make0 mulr0 mul0r addr0 ler_refl; split=> //; split=> //.
      case=> ->; case: l2 => [|d l2] /=.
      rewrite -[[:: x, y & [::]]]/([::x]++[:: y]) catA.
      rewrite !cats1 -!rot1_cons; move/rot_inj; case=> <-.
      case: (ns_tail (n - 1) (n - 2))=> l3 ->; rewrite map_cat /=.
      rewrite cats1 -rot1_cons; move/rot_inj; case=> <- h2.
      have admit3 : (Qcb_make (n - 1) / Qcb_make n) = 1 - (Qcb_make n)^-1.
         admit.
      rewrite admit3 mulr_addr mulr1 oppr_add !addrA oppr_add addrA addrN add0r.
      rewrite -mulrN opprK; split=> //.
      exists (n - 1); split.
        by rewrite  -mulrA admit3 mulr_addr mulr1 !addrA.
      rewrite ler_refl.
      have admit4 : leb 0 (n - 1) by admit.
      done.
    case: (non_empty_tail  _ d l2) => l3 [e qe]; rewrite qe.
    rewrite -[ql1 ++ [:: x, y & l3 ++ [:: e]]]/(ql1 ++ [:: x, y & l3] ++ [:: e]).
    rewrite [_ ++ _ ++ [:: e]]catA !cats1 -!rot1_cons; move/rot_inj; case=> -> q''.
    case: (map_contiguous _ _ (fun x => t1+(e-t1)*((Qcb_make x)/(Qcb_make n)))
             _ _ _ _ _ q'') =>  [l'1 [l'2 [n1 [n2 [_ [_ [qx [qy st]]]]]]]].
    rewrite qx qy.
    have admit5 : leb 0 (n - 2%Z) by admit.
    have n21 : n2 = n1 + 1 by apply: ns_step st.
    split.
      rewrite n21 [t1 + _]addrC -addrA oppr_add [t1 + _]addrA addrN add0r
       -mulrN -mulr_addr -mulNr -[_ * _^-1 + _]mulr_addl.
      have tmp: Qcb_make (n1 + 1) - Qcb_make n1 = 1.
        by rewrite -[_ - _]/(Q2Qcb(Qcb_make _ + Qcbopp(Qcb_make _)))
          /Qcbopp /Qcb_make 4!qcb_val_E /Qopp /Qden /Qnum {2}/Q2Qcb qcb_val_E
          (eqP (Qcb_Z _)) /Qplus /Qden /Qnum /Pmult 2!Zmult_1_r -Zplus_assoc
          [Zplus _ (Zopp _)]Zplus_comm Zplus_assoc Zplus_opp_r Zplus_0_l.
      by rewrite tmp mul1r.
    exists n1; split; first by rewrite mulrA.
    have bds : leb 1 n1 && leb n1 (n-1).
      have tmp : (n - 1) - (n - 2%Z) = 1
        by rewrite oppr_add opprK addrA [ _ - n]addrC addKr.
      by rewrite -{1}tmp; apply: ns_bounds _ _ _ _ _ admit5 st.
    move/andP: bds => [bds1 bds2];split; last done.
    have admit6: leb 0 n1 by admit.
    by [].
  case: mkl => [sl qsl].
  have admit7 : ~ ltb (eval_pol l b) 0 by admit.
  case: (find_pair _ (fun x => ltb (eval_pol l x) 0)
             (fun x y => y - x = (b-a)/Qcb_make n /\
                (exists k, x = a + (b-a)*Qcb_make k / Qcb_make n /\
                        leb 0 k /\ leb k (n-1))) sl a b nla admit7 qsl) =>
             [a' [b' [[A1 [k [A4 A5]]] [A2 A3]]]] {qsl sl}.
exists a'; exists b'.
have aa' : leb a a'.
Admitted.
(*
exists a'; exists b'.
assert (aa':a <= a').
(setoid_replace a with (a+0) by ring); rewrite A4.
apply Qplus_le_compat; try apply Qle_refl.
repeat apply Qmult_le_0_compat; auto.
unfold Qle; simpl; omega.
apply Qlt_le_weak; apply Qinv_lt_0_compat; unfold Qlt; simpl; omega.
assert (bb': b' <= b).
setoid_replace b with (a + (b-a) * (n#1) * /(n#1)) by
 field; unfold Qeq; simpl; try omega.
(setoid_replace b' with (a' + (b' - a')) by ring); rewrite A1, A4.
rewrite <- Qplus_assoc; apply Qplus_le_compat; try apply Qle_refl.
unfold Qdiv;
 match goal with |- ?f <= _ => setoid_replace f with ((b-a)* ((k#1)+1) * /(n#1))
 end.
apply Qmult_le_compat_r.
repeat rewrite (Qmult_comm (b-a)); apply Qmult_le_compat_r.
rewrite Qfrac_add_Z_l; unfold Qle; simpl; omega.
auto.
apply Qlt_le_weak; apply Qinv_lt_0_compat; unfold Qlt; simpl; omega.
field; unfold Qeq; simpl; omega.
assert (ab': a' < b').
setoid_replace a' with (a' + 0) by ring.
(setoid_replace b' with (a' + (b' - a')) by ring); rewrite A1.
apply Qplus_le_lt_compat; try apply Qle_refl; apply Qmult_lt_0_compat; auto.
apply Qinv_lt_0_compat; unfold Qlt; simpl; omega.
assert (epsban: (b-a)*c / (n#1) <= epsilon).
apply Qmult_lt_0_le_reg_r with ((n#1) / epsilon).
apply Qmult_lt_0_compat; auto.
unfold Qlt; simpl; omega.
match goal with |- ?f1 <= ?f2 =>
  (setoid_replace f2 with (n#1) by field; auto);
  (setoid_replace f1 with ((b-a)*c /epsilon) by
   (field; split; auto; unfold Qeq; simpl; omega)); auto
end.
split;[idtac | split; auto].
(* start with epsilon and a'. *)
apply Qopp_le_rl.
apply Qle_trans with (eval_pol l b' - eval_pol l a').
setoid_replace (-eval_pol l a') with (0 - eval_pol l a') by ring.
apply Qplus_le_compat; auto; apply Qnot_lt_le; auto.
repeat rewrite q.
rewrite <- (pos_Qabs (eval_pol l' (b'-a) - eval_pol l' (a'-a))).
apply Qle_trans with (c*((b'-a)-(a'-a))).
apply pc; auto.
(setoid_replace 0 with (a - a) by ring); apply Qplus_le_compat; auto; apply Qle_refl.
apply Qplus_le_compat; auto.
apply Qplus_le_compat; auto.
setoid_replace (b' -a -(a'-a)) with (b' -a') by ring.
rewrite A1.
unfold Qdiv; rewrite Qmult_assoc; rewrite (Qmult_comm c); exact epsban.
repeat rewrite <- q.
(setoid_replace 0 with (0+0) by ring);apply Qplus_le_compat.
apply Qnot_lt_le; auto.
apply Qopp_le_lr.
(setoid_replace 0 with (-0) by ring);apply Qlt_le_weak; assumption.
split.
apply Qnot_lt_le; auto.
split; auto.
apply Qle_trans with (eval_pol l' (b' -a) -eval_pol l' (a' -a)).
setoid_replace (eval_pol l b') with (eval_pol l b' + 0) by ring.
apply Qplus_le_compat.
rewrite q; apply Qle_refl.
rewrite <- q; apply Qopp_le_lr; auto.
rewrite <- (pos_Qabs (eval_pol l' (b'-a) - eval_pol l' (a'-a))).
apply Qle_trans with (c*((b'-a)-(a'-a))).
apply pc; auto.
(setoid_replace 0 with (a - a) by ring); apply Qplus_le_compat; auto; apply Qle_refl.
apply Qplus_le_compat; auto.
apply Qplus_le_compat; auto.
setoid_replace (b' -a -(a'-a)) with (b' -a') by ring.
rewrite A1.
unfold Qdiv; rewrite Qmult_assoc; rewrite (Qmult_comm c); exact epsban.
repeat rewrite <- q.
(setoid_replace 0 with (0+0) by ring);apply Qplus_le_compat.
apply Qnot_lt_le; auto.
apply Qopp_le_lr.
apply Qlt_le_weak; assumption.
Qed.

Lemma constructive_mvt :
  forall l x y, x < y -> eval_pol l x < 0 -> 0 <= eval_pol l y  ->
       forall epsilon, 0 < epsilon ->
       exists x', exists y',  -epsilon <= eval_pol l x' /\
         eval_pol l x' < 0 /\ 0 <= eval_pol l y' /\
         eval_pol l y' <= epsilon /\ x <= x' /\ x' < y' /\ y' <= y.
intros l a b ab nla plb.
destruct (translate_pol l a) as [l' q].
assert (ba':0 < b-a).
setoid_replace 0 with (a-a) by ring.
unfold Qminus; repeat rewrite <- (Qplus_comm (-a));
apply Qplus_le_lt_compat; auto.
assert (ba:~ b-a == 0).
intros abs; case (Qlt_not_eq 0 (b-a) ba'); rewrite abs; apply Qeq_refl.
destruct (cm3 (b-a) ba' l') as [c pc].
assert (mpolapos : 0 < -eval_pol l a) by (apply Qopp_lt_lr; assumption).
assert (t1 : a-a == 0) by ring.
assert (cpos: 0 < c).
setoid_replace 0 with (0 */(b-a)) by ring.
setoid_replace c with ((c*(b-a-(a-a)))/(b-a)) by (field;auto).
apply Qmult_lt_compat_r; auto.
apply Qlt_le_trans with (Qabs (eval_pol l' (b-a) - eval_pol l' (a-a))).
match goal with |- 0 < Qabs(?a) => assert (ineq: 0 < a) end.
repeat rewrite <- q; setoid_replace 0 with (0+0) by ring.
apply Qplus_le_lt_compat; auto.
rewrite pos_Qabs; auto.
apply pc; try solve[rewrite t1; auto | auto].
assert (cn0 : ~c==0) by (apply Qnot_eq_sym; apply Qlt_not_eq ; auto).
intros epsilon pe.
assert (en0 : ~ epsilon == 0) by (apply Qnot_eq_sym; apply Qlt_not_eq; auto).
assert (pdiv: 0 < (b-a)*c/epsilon) by (repeat apply Qmult_lt_0_compat; auto).
destruct (QZ_bound ((b-a)*c/(epsilon))) as [n qn]; auto.
assert (pn : (0 < n)%Z).
destruct ((b-a)*c/epsilon) as [nu de]; unfold Qle in qn, pdiv;
simpl in qn, pdiv.  unfold Qlt in pdiv; simpl in pdiv; rewrite Zmult_1_r in pdiv, qn.
assert (pdiv' := Zlt_le_trans _ _ _ pdiv qn).
apply Zmult_lt_0_reg_r with ('de)%Z; try solve [compute; auto with zarith].
assert (mkl: 
  exists l, forall l1 l2 x y, a::l++b::nil = l1++x::y::l2 ->
      y-x == (b-a)/(n#1) /\ exists k, x == a + (b-a)*(k#1)/(n#1) /\ (0<= k <= n-1)%Z).
case (Z_eq_dec n 1).
intros n1; exists nil; intros l1 l2 x y; destruct l1; simpl;
  intros ql.
injection ql; intros; subst x y n; split;
 [field | exists 0%Z; split; [field | omega]].
repeat (destruct l1; try discriminate).
intros nn1; exists (map  (fun x => a + (b-a)*((x#1)/(n#1))) (ns (n-1) (n-2))).
intros l1 l2  x y; destruct l1.
assert (0 <= n-2)%Z by omega.
destruct (ns_head (n-1) (n-2)) as [a1 qa1];auto; rewrite qa1; simpl.
replace ((n-1)-(n-2))%Z with 1%Z by ring.
intros ql; injection ql; intros; subst x y; split.
field; unfold Qeq; simpl; omega.
exists 0%Z; split;[field; unfold Qeq; simpl; omega | omega].
simpl; intros q'; injection q'; clear q'.
destruct l2 as [| d l2].
replace (x::y::nil) with ((x::nil)++(y::nil)). rewrite  <- app_ass.
intros q' _; elim (app_inj_tail  _ _ _ _ q'); clear q'; intros q' q''.
destruct (ns_tail (n-1)(n-2)) as [l3 ql3].
rewrite ql3 in q'.
rewrite map_app in q'; simpl in q'.
elim (app_inj_tail _ _ _ _ q'); clear q'; intros q' q3'.
subst x y.
assert (t0:(n-1#1)/(n#1) == 1 - /(n#1)).
setoid_replace 1 with ((n#1)/(n#1)).
setoid_replace (/(n#1)) with (1/(n#1)).
unfold Qdiv.
match goal with |- _ == ?a =>
    setoid_replace a with (((n#1) - 1) * /(n#1)) by ring end.
apply Qmult_comp.
unfold Qeq; simpl; ring.
apply Qeq_refl.
field; unfold Qeq; simpl; omega.
field; unfold Qeq; simpl; omega.
rewrite t0.
split.
field; unfold Qeq; simpl; omega.
exists (n-1)%Z; split.
unfold Qdiv; rewrite Qmult_assoc; apply Qeq_refl.
omega.
simpl; auto.
unfold Qdiv.
destruct (non_empty_tail  _ d l2) as [l3 [e qe]].
rewrite qe.
replace (l1++x::y::l3++e::nil) with ((l1++x::y::l3)++(e::nil)).
intros q' _.
destruct (app_inj_tail _ _ _ _ q') as [q'' _].
destruct (map_contiguous _ _ (fun x => a+(b-a)*((x#1)*/(n#1)))
             _ _ _ _ _ q'') as [l'1 [l'2 [n1 [n2 [_ [_ [qx [qy st]]]]]]]].
subst x y; setoid_replace (n2#1) with ((n1#1)+1).
split.
ring.
exists n1; split. 
rewrite Qmult_assoc; apply Qeq_refl.
apply ns_bounds in st; omega.
rewrite Qfrac_add_Z_l; rewrite Zmult_1_r.
apply ns_step in st; try omega; rewrite st; apply Qeq_refl.
rewrite app_ass; auto.
destruct mkl as [sl qsl].
destruct (find_pair Q (fun x => eval_pol l x < 0) 
                  (fun x y => y - x == (b-a)/(n#1) /\
                     exists k, x == a + (b-a)*(k#1) /(n#1) /\
                     (0 <= k <= n-1)%Z)
                 sl a b) 
  as [a' [b' [[A1 [k [A4 A5]]][A2 A3]]]]; auto.
apply Qle_not_lt; auto.
intros x _; case (Qlt_le_dec (eval_pol l x) 0); auto.
intros H; right; apply Qle_not_lt; auto.
clear qsl sl.
exists a'; exists b'.
assert (aa':a <= a').
(setoid_replace a with (a+0) by ring); rewrite A4.
apply Qplus_le_compat; try apply Qle_refl.
repeat apply Qmult_le_0_compat; auto.
unfold Qle; simpl; omega.
apply Qlt_le_weak; apply Qinv_lt_0_compat; unfold Qlt; simpl; omega.
assert (bb': b' <= b).
setoid_replace b with (a + (b-a) * (n#1) * /(n#1)) by
 field; unfold Qeq; simpl; try omega.
(setoid_replace b' with (a' + (b' - a')) by ring); rewrite A1, A4.
rewrite <- Qplus_assoc; apply Qplus_le_compat; try apply Qle_refl.
unfold Qdiv;
 match goal with |- ?f <= _ => setoid_replace f with ((b-a)* ((k#1)+1) * /(n#1))
 end.
apply Qmult_le_compat_r.
repeat rewrite (Qmult_comm (b-a)); apply Qmult_le_compat_r.
rewrite Qfrac_add_Z_l; unfold Qle; simpl; omega.
auto.
apply Qlt_le_weak; apply Qinv_lt_0_compat; unfold Qlt; simpl; omega.
field; unfold Qeq; simpl; omega.
assert (ab': a' < b').
setoid_replace a' with (a' + 0) by ring.
(setoid_replace b' with (a' + (b' - a')) by ring); rewrite A1.
apply Qplus_le_lt_compat; try apply Qle_refl; apply Qmult_lt_0_compat; auto.
apply Qinv_lt_0_compat; unfold Qlt; simpl; omega.
assert (epsban: (b-a)*c / (n#1) <= epsilon).
apply Qmult_lt_0_le_reg_r with ((n#1) / epsilon).
apply Qmult_lt_0_compat; auto.
unfold Qlt; simpl; omega.
match goal with |- ?f1 <= ?f2 =>
  (setoid_replace f2 with (n#1) by field; auto);
  (setoid_replace f1 with ((b-a)*c /epsilon) by
   (field; split; auto; unfold Qeq; simpl; omega)); auto
end.
split;[idtac | split; auto].
(* start with epsilon and a'. *)
apply Qopp_le_rl.
apply Qle_trans with (eval_pol l b' - eval_pol l a').
setoid_replace (-eval_pol l a') with (0 - eval_pol l a') by ring.
apply Qplus_le_compat; auto; apply Qnot_lt_le; auto.
repeat rewrite q.
rewrite <- (pos_Qabs (eval_pol l' (b'-a) - eval_pol l' (a'-a))).
apply Qle_trans with (c*((b'-a)-(a'-a))).
apply pc; auto.
(setoid_replace 0 with (a - a) by ring); apply Qplus_le_compat; auto; apply Qle_refl.
apply Qplus_le_compat; auto.
apply Qplus_le_compat; auto.
setoid_replace (b' -a -(a'-a)) with (b' -a') by ring.
rewrite A1.
unfold Qdiv; rewrite Qmult_assoc; rewrite (Qmult_comm c); exact epsban.
repeat rewrite <- q.
(setoid_replace 0 with (0+0) by ring);apply Qplus_le_compat.
apply Qnot_lt_le; auto.
apply Qopp_le_lr.
(setoid_replace 0 with (-0) by ring);apply Qlt_le_weak; assumption.
split.
apply Qnot_lt_le; auto.
split; auto.
apply Qle_trans with (eval_pol l' (b' -a) -eval_pol l' (a' -a)).
setoid_replace (eval_pol l b') with (eval_pol l b' + 0) by ring.
apply Qplus_le_compat.
rewrite q; apply Qle_refl.
rewrite <- q; apply Qopp_le_lr; auto.
rewrite <- (pos_Qabs (eval_pol l' (b'-a) - eval_pol l' (a'-a))).
apply Qle_trans with (c*((b'-a)-(a'-a))).
apply pc; auto.
(setoid_replace 0 with (a - a) by ring); apply Qplus_le_compat; auto; apply Qle_refl.
apply Qplus_le_compat; auto.
apply Qplus_le_compat; auto.
setoid_replace (b' -a -(a'-a)) with (b' -a') by ring.
rewrite A1.
unfold Qdiv; rewrite Qmult_assoc; rewrite (Qmult_comm c); exact epsban.
repeat rewrite <- q.
(setoid_replace 0 with (0+0) by ring);apply Qplus_le_compat.
apply Qnot_lt_le; auto.
apply Qopp_le_lr.
apply Qlt_le_weak; assumption.
Qed.
*)