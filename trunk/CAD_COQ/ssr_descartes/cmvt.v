Require Import QArith ZArith Zwf Omega.
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

(* Theorem binding the slope between two points inside an interval. *)
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

(* We will look at n points regularly placed between a and b,  a satisfies
  a property P and b does not, we want to find the first point among the
  n points that satisfies P and has a neighbour that does not. *)
Definition find_pair : forall A:eqType, forall P:A->bool, forall Q:A->A->Prop,
    forall l:seq A, forall a b:A, P a -> ~P b ->
    (forall l1 l2 x y, a::l ++ b::nil= l1 ++ x :: y :: l2 -> Q x y) ->
    {c :A & { d | Q c d /\ P c /\ ~P d}}.
Proof.
move => A P Q l; elim: l => [ | a l IHl] a' b' Pa Pb connect. 
  by exists a'; exists b'; split => //; apply: (connect [::] [::]).
case Pa1: (P a).
  have tmp :
     forall l1 l2 x y,  a :: l ++ [:: b' ]= l1 ++ [::x, y & l2] -> Q x y.
    by move => l1 l2 x y q; apply: (connect (a'::l1) l2); rewrite /= q.
  by move: (IHl a b' Pa1 Pb tmp) => [c [d [cd Pc]]]; exists c; exists d.
exists a'; exists a; split; first by apply (connect nil (l++b'::nil)).
by rewrite Pa1. 
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

Lemma leb_Z : forall x y:Z, x <<= y -> Qcb_make x <<= Qcb_make y.
Proof. 
move => x y xy.
rewrite Qcb_leb_iff /qcb_val /Qcb_make /Qle /Qnum /Qden 2!Zmult_1_r.
by rewrite -[leb _ _]/(Zle_bool _ _) in xy; move: (Zle_cases x y); rewrite xy.
Qed.

Lemma leb_0_Z : forall y, 0%Z <<= y -> 0 <<= Qcb_make y.
Proof. by move => y yp; apply: leb_Z. Qed.

Lemma ltb_Z : forall x y:Z, x <<! y -> Qcb_make x <<! Qcb_make y.
Proof. 
  move => x y xy; apply/Qcb_ltbP. rewrite 
       /qcb_val /Qcb_make /Qlt /Qnum /Qden 2!Zmult_1_r.
  rewrite -[ltb _ _]/(Zlt_bool _ _) in xy.
  by move: (Zlt_cases x y); rewrite xy.
Qed.

Lemma ltb_0_Z : forall y, 0%Z <<! y -> 0 <<! Qcb_make y.
Proof. by move => y yp; apply: ltb_Z. Qed.

Lemma Qcb_make_add :
  forall x y, Qcb_make (x + y) == Qcb_make x + Qcb_make y.
move => x y; apply/Qcb_QeqP.
by rewrite-[(Qcb_make _ + _)%R]/(Q2Qcb(Qplus (qcb_val (Qcb_make x))
                                  (qcb_val (Qcb_make y)))) /Qcb_make
   !qcb_val_E /Qplus /Qnum /Qden !Zmult_1_r Pmult_1_r /Q2Qcb qcb_val_E
   (eqP (Qcb_Z _)).
Qed.

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
have admit1 : 0 <<! n.
  have qn' : (((b - a) * c / eps) <<= (Qcb_make n)).
    by rewrite Qcb_leb_iff /Qcb_make qcb_val_E. 
  have tmp : 0 <<! Qcb_make n.
    by apply: ltr_ler_trans pdiv qn'.
  by move/Qcb_ltbP: tmp; rewrite /Qlt /= Zmult_1_r Zlt_is_lt_bool => tmp.
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
  have admit8 : 0 <<= n - 2%Z.
    move/eqP: en; move: admit1; rewrite -[1]/1%Z -[0]/0%Z /is_true -Zle_is_le_bool
     -Zlt_is_lt_bool -[(n-2%Z)%R]/(n - 2)%Z; clear; intros; omega.
  have admit2 : 0 <<= n - 1.
    rewrite -[leb _ _]/(Zle_bool 0 _) /is_true -(Zle_is_le_bool 0 (n - 1)).
    move: admit8.
    rewrite -[leb _ _]/(Zle_bool _ _) /is_true -(Zle_is_le_bool 0 (n - 2)) => h1;
    apply: Zle_trans h1 _.
    by clear; omega.
  move=> l1 l2 x y; case: l1 => [|t1 ql1] /=.
    case: (ns_head (n - 1) (n - 2) admit8) => a1 qa1.
    rewrite qa1 /= (_ : (n - 1) - (n - 2)%Z = 1) ?Qcb_make1; last first.
      by rewrite addrAC [-(n - 2%Z)]oppr_add addrA opprK addrN add0r. 
    case => -> <- /=; split.
      by rewrite addrAC addrN add0r mulrA mulr1.
    exists 0; rewrite Qcb_make0 mulr0 mul0r addr0 ler_refl; split=> //; split=> //.
  case=> ->; case: l2 => [|d l2] /=.
    rewrite -[[:: x, y & [::]]]/([::x]++[:: y]) catA.
    rewrite !cats1 -!rot1_cons; move/rot_inj; case=> <-.
    case: (ns_tail (n - 1) (n - 2))=> l3 ->; rewrite map_cat /=.
    rewrite cats1 -rot1_cons; move/rot_inj; case=> <- h2.
    have admit3 : (Qcb_make (n - 1) / Qcb_make n) = 1 - (Qcb_make n)^-1.
      have nn0 : ~~ (Qcb_make n == 0).
        by apply/negP => nis0; move/Qcb_QeqP: nis0; 
         rewrite /Qeq /= Zmult_1_r => nis0; move: admit1;
         rewrite nis0 ltr_irrefl.
      by apply/eqP; rewrite /= (eqP (Qcb_make_add _ _)) mulr_addl mulrV /= //.
    rewrite admit3 mulr_addr mulr1 oppr_add !addrA oppr_add addrA addrN add0r.
    rewrite -mulrN opprK; split=> //.
    exists (n - 1); split; last by rewrite ler_refl.
    by rewrite  -mulrA admit3 mulr_addr mulr1 !addrA.
  case: (non_empty_tail  _ d l2) => l3 [e qe]; rewrite qe.
  rewrite -[ql1 ++ [:: x, y & l3 ++ [:: e]]]/(ql1 ++ [:: x, y & l3] ++ [:: e]).
  rewrite [_ ++ _ ++ [:: e]]catA !cats1 -!rot1_cons; move/rot_inj; case=> -> q''.
  case: (map_contiguous _ _ (fun x => t1+(e-t1)*((Qcb_make x)/(Qcb_make n)))
             _ _ _ _ _ q'') =>  [l'1 [l'2 [n1 [n2 [_ [_ [qx [qy st]]]]]]]].
  rewrite qx qy.
  have n21 : n2 = n1 + 1 by apply: ns_step st.
  split.
    rewrite n21 [t1 + _]addrC -addrA oppr_add [t1 + _]addrA addrN add0r -mulrN
       -mulr_addr -mulNr -[_ * _^-1 + _]mulr_addl.
    have admit5: Qcb_make (n1 + 1) - Qcb_make n1 = 1.
      by rewrite -[_ - _]/(Q2Qcb (Qcb_make _ + Qcbopp(Qcb_make _)))
          /Qcbopp /Qcb_make 4!qcb_val_E /Qopp /Qden /Qnum {2}/Q2Qcb qcb_val_E
          (eqP (Qcb_Z _)) /Qplus /Qden /Qnum /Pmult 2!Zmult_1_r -Zplus_assoc
          [Zplus _ (Zopp _)]Zplus_comm Zplus_assoc Zplus_opp_r Zplus_0_l.
    by rewrite admit5 mul1r.
  exists n1; split; first by rewrite mulrA.
  have bds : (1 <<= n1) && (n1 <<= (n-1)).
    have admit9 : (n - 1) - (n - 2%Z) = 1
        by rewrite oppr_add opprK addrA [ _ - n]addrC addKr.
    by rewrite -{1}admit9; apply: ns_bounds _ _ _ _ _ admit8 st.
  move/andP: bds => [bds1 bds2];split; last by [].
  have admit6: 0 <<= n1 by apply: ler_trans bds1; apply: ltrW; apply ltr_0_1.
  by [].
case: mkl => [sl qsl].
have admit7 : ~ eval_pol l b <<! 0.
  by apply/negP; rewrite -lerNgtr.
case: (find_pair _ (fun x => ltb (eval_pol l x) 0)
             (fun x y => y - x = (b-a)/Qcb_make n /\
                (exists k, x = a + (b-a)*Qcb_make k / Qcb_make n /\
                        leb 0 k /\ leb k (n-1))) sl a b nla admit7 qsl) =>
             [a' [b' [[A1 [k [A4 A5]]] [A2 A3]]]] {qsl sl}.
exists a'; exists b'.
have aa' : a <<= a'.
  rewrite -(addr0 a) A4; apply: lerT; first by apply ler_refl.
  apply: ler_0_lcompat; first apply:ler_0_lcompat.
      by rewrite ler_ltreq; apply/orP; left.
    by apply: leb_0_Z; move: A5 => [A5 _].
  by rewrite ler_ltreq; apply/orP; left; rewrite invr_ltr; apply: ltb_Z.
have bb' :  b' <<= b.
  have bdec : b = a + (b - a) * (Qcb_make n) / (Qcb_make n).
    have nn0 : Qcb_unit (Qcb_make n).
      apply/negP => nq0; move/Qcb_QeqP: nq0.
      rewrite /Qeq Zmult_1_r /Qcb_make qcb_val_E /Qnum Zmult_0_l => nq0.
      by move: admit1; rewrite nq0 ltr_irrefl.
    by rewrite mulrK // addrA [a + _]addrC addrK.
  have b'a: b' = a' + (b' - a') by rewrite addrA [ a' + _]addrC addrK.
  rewrite b'a A1 A4 -addrA {3}bdec -mulr_addl;
      apply: lerTr; apply ler_rcompat.
    by rewrite ler_ltreq invr_ltr ltb_0_Z //.
  rewrite -{2}[ b - a ]mulr1 -mulr_addr; apply: ler_lcompat.
    by rewrite ler_ltreq ba'.
  rewrite -Qcb_make1 -(eqP (Qcb_make_add _ _)); apply: leb_Z.
  have admit6:  k+1 <<= n.
    move:A5 => [_ A5].
    by rewrite -(lerTlb (-1)) -[(k + 1)%Z]/(k + 1) -addrA addrN addr0.
  by [].
have ab' :  a' <<! b'.
  rewrite -[a']addr0 -[b']addr0 -{2}[0](addrN a') addrA [b' + _]addrC -addrA.
  apply: ltrTr; rewrite A1; apply: ltr_0_lcompat; first by []. 
  by rewrite invr_ltr ltb_0_Z.
have epsban: (b-a)*c/Qcb_make n <<= eps.
  have tmp : 0 <<! Qcb_make n / eps.
    apply: ltr_0_lcompat; first by apply: ltb_Z.
    by rewrite invr_ltr.
  apply: (ler_Ilcompat_r tmp).
  have admit10 : GRing.unit eps.
    by apply/negP => e0; rewrite (eqP e0) ltr_irrefl in pe.
  rewrite mulrVK // (mulrC (Qcb_make n)) (mulrC ((b - a) * c)) !mulrA mulrK.
    by rewrite -mulrA mulrC; apply/Qcb_lebP.
  apply/negP => abs; move/Qcb_QeqP: abs; rewrite /Qeq !qcb_val_E.
  by rewrite -[Qden(Q2Qcb 0)]/(xH) -[Qnum(Q2Qcb 0)]/0%Z /Qnum /Qden Zmult_0_l
      Zmult_1_r => abs; rewrite abs in admit1; move: admit1; rewrite ltr_irrefl.
have main: eval_pol l b' - eval_pol l a' <<= eps.
  rewrite !q -(@absr_nneg _ (_ - _)).
    have b'a': c * (b' - a') <<= eps by rewrite A1 mulrA (mulrC c).
    apply: ler_trans b'a'; rewrite -{2}(addr0 b') -(addNr a) addrA
        -(addrA (b' - a)) -(opprK (a - a')) oppr_add opprK (addrC (-a)).
    apply: pc.
        by rewrite -(addrN a); apply: lerTl.
      by rewrite lerTlb ler_ltreq ab'.
    by rewrite lerTlb. 
  rewrite -!q; apply: lerT0; first by rewrite lerNgtr; move/negP: A3.
  by rewrite -ler_oppger oppr0 opprK ler_ltreq A2.
split; last (split; first exact A2).
  rewrite -ler_oppger opprK.
    have tmp: 0 - eval_pol l a' <<= eval_pol l b' - eval_pol l a'.
    by apply: lerTl; move/negP: A3; rewrite ltrNger negb_involutive.
  by rewrite add0r in tmp; apply: ler_trans tmp _.
split; first by rewrite lerNgtr; move/negP: A3.
split; last by auto.
 apply: ler_trans main; rewrite -{1}(addr0 (eval_pol l b')); apply: lerTr.
by rewrite -ler_oppger opprK oppr0 ler_ltreq A2.
Qed.
