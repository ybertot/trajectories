Require Import CAD_types.
Require Import Mylist.
Require Import Tactic.
Require Import PDet.
Require Import Utils.
Require Import Bool.
Import phi.
Require Import PolMonOSum.
Require Import ZArith.
Set Implicit Arguments.
Hypothesis cpow_1 : forall c, cpow c 1%N ==c.
Hypothesis cintegral : forall a b, czero_test (a **b) = orb (czero_test a) (czero_test b).


Notation "x ^ i ":= (Pol_pow x i).
Notation "x ^^ i ":=(cpow x i) (at level 30, no associativity).


(* ca sert ca?*)
Add Morphism (@cons Pol)
 with signature Pol_Eq ==> Pol_list_equiv ==>Pol_list_equiv as cons_comp.
intros.
constructor;trivial.
Qed.

(* version setoid de In *)
(* on generalise lus que ca dans Myllist?*)
Fixpoint PIn(P:Pol)(l:list Pol){struct l}:Prop:=
  match l with
   |nil => False
   |b :: m => b != P \/ PIn P m
  end.




(* trivial lemma specifying the In predicate of st lib List*)
Lemma PIn_app :forall a l, PIn a l -> exists l1, exists l2, l *= app l1 (a::l2).
Proof with (trivial;reflexivity).
intros  a l H_In.
induction l.
elim H_In.
elim H_In;intro G.
exists (@nil Pol);exists l.
simpl;rewrite G...
elim (IHl G);intros l3 Hex.
elim Hex.
intros l4 Heq.
exists (a0:: l3).
exists l4.
simpl.
rewrite Heq...
Qed.

Lemma PIn_PIn_app_r : forall P l1, PIn P l1 -> forall l2, PIn P (app l1 l2).
Proof.
intros P;induction l1;intros H l2;elim  H;rewrite <- app_comm_cons;intro G.
left;trivial.
right.
apply (IHl1 G).
Qed.

Lemma PIn_PIn_app_l : forall P l2 l1, PIn P l1 -> PIn P (app l2 l1).
Proof.
intros P;induction l2;intros l1 H.
auto.
rewrite <- app_comm_cons.
right.
apply (IHl2 l1 H).
Qed.



Add Morphism PIn with signature Pol_Eq ==> Pol_list_equiv ==> iff as PIn_comp.
intros P Q Heq  l1 l2 Hequiv.
induction Hequiv;simpl.
reflexivity.
split;intro G;inversion G.
left.
rewrite <- H.
rewrite <- Heq;auto.
right.
rewrite <- IHHequiv;auto.
left.
rewrite  H.
rewrite  Heq;auto.
right.
rewrite  IHHequiv;auto.
Qed.



(* comment on reconnait un sous-terme?*)
Ltac myreplace_aux t1 t2 :=
match goal with
| |- context ctx[t1] => let t3:=(context ctx[ t2]) in transitivity t3
|  |- _ => idtac "rate"
end.

Ltac myreplace :=
 repeat progress
  (match goal with
   | |- - _ != - _ => apply Popp_comp
   | |- det _ _ != det _ _ => apply det_morph;try reflexivity
   | |- app _ _ *= app _ _=> apply app_morph;try reflexivity
   | |- _ :: _ *= _ :: _ => constructor;[try setoid ring|try reflexivity]
   | |-_ =>  try reflexivity;try Pcsimpl
  end).



(*an other version of det_sum_simpl, using In, lefet then right*)
Lemma det_PIn_l : forall l1 l2 P Q d c, PIn Q l1 ->
det d (app l1 ((P+(scal c Q))::l2)) != det d (app l1 (P::l2)). 
Proof with (try reflexivity;auto).
induction l1;intros l2 P Q d c H_In;simpl in H_In;elim H_In;intro G.
transitivity (det d (app nil ((app (Q :: l1) (P + (scal c Q) :: l2))))).
simpl;myreplace.
rewrite det_t.
rewrite det_sum_simpl.
rewrite det_t.
setoid ring;simpl.
myreplace.
symmetry...
elim (@PIn_app Q l1 G).
intros l3 Hex.
elim Hex;intros l4 Heq.
transitivity (det d (app (a::l3) (app (Q::l4) (P+(scal c Q)::l2)))).
repeat rewrite ass_app.
myreplace.
rewrite <- app_comm_cons.
constructor...
transitivity (- det d (app (a :: l3) (app (P +(scal c Q):: l4) (Q :: l2)))).
rewrite det_t.
myreplace.
rewrite det_sum_simpl.
rewrite det_t.
simpl.
pattern cons at 1.
rewrite  app_comm_cons.
rewrite ass_app.
setoid ring.
myreplace.
symmetry...
Qed.

Lemma det_PIn_r : forall l1 l2 P Q d c, PIn Q l2 ->
det d (app l1 ((P+(scal c Q))::l2)) != det d (app l1 (P::l2)). 
Proof with (try reflexivity;trivial).
intros l1 l2 P Q d c H_In.
elim (PIn_app Q l2 H_In).
intros l3 Hex.
elim Hex.
intros l4 Heq.
transitivity (det d (app l1 (P+scal c Q::app l3 (Q :: l4)))).
myreplace...
repeat rewrite app_comm_cons.
rewrite det_sum_simpl.
rewrite <- app_comm_cons.
myreplace.
symmetry...
Qed.

(* generalisation of det_sum_simpl to a finite linear combination  of redundant  polynomials*)



Lemma det_Psum : forall m f l1 l2 P d g,
(forall n, n <= m -> (f n) = P0 \/ PIn (f n) l1 \/ PIn (f n) l2) ->
det d (app l1 ((P + Psum (fun i =>scal  (g i)  (f i))  m)::l2))
 != det d (app l1 (P::l2)).
Proof with (auto;try reflexivity).
induction m;intros f l1 l2 P d g H_neutral;simpl.
elim (H_neutral O);[intro H_f0|intro Hf0|auto with arith].
rewrite H_f0.
apply det_morph.
apply app_morph;[reflexivity|constructor;[unfold scal;Pcsimpl;setoid ring|reflexivity]].
elim Hf0;intro H_In.
induction l1.
elim H_In.
rewrite det_PIn_l...
rewrite det_PIn_r...
elim (H_neutral (S m));[intro H_fsm|intro Hfsm|auto with arith].
rewrite H_fsm.
transitivity (det d (app l1 (P + (Psum   (fun i : nat => scal (g i) (f i)) m)  :: l2)));
[unfold scal;myreplace;setoid ring|apply IHm]...
transitivity (det d (app l1 ((P + Psum  (fun i : nat => scal (g i) (f i)) m) + (scal (g (S m)) (f (S m))) :: l2))).
myreplace.
elim Hfsm;intro H_In.
rewrite det_PIn_l...
rewrite det_PIn_r...
Qed.

(* A*X^n *)
Fixpoint times_X_n(A:Pol)(n:nat){struct n}:Pol:=
match n with
|O => A
|S n => X *(times_X_n A n)
end.

Add Morphism times_X_n with signature Pol_Eq ==> (@eq nat) ==> Pol_Eq as times_X_n_comp.
intros x1 x2 Heq.
induction x;simpl.
trivial.
rewrite IHx.
reflexivity.
Qed.

(* linearity for times_X_n*)
Lemma times_X_n_scal : forall n A a, times_X_n (a!*A) n != a !* (times_X_n A n).
Proof.
induction n;intros A a;simpl.
reflexivity.
rewrite IHn.
repeat rewrite  Pscal_Pmul_l.
setoid ring.
Qed.


(* builds the list A*X^n ::...::A*X :: A ::nil*)
Fixpoint times_X_n_family(A:Pol)(n:nat){struct n}:list Pol:=
match n with
|O => A::nil
|S n => (times_X_n A (S n))::(times_X_n_family A n)
end.

Add Morphism times_X_n_family with signature Pol_Eq ==> (@eq nat) ==> Pol_list_equiv as X_n_fam_comp.
intros x1 x2 Heq.
induction x;simpl.
constructor;trivial;reflexivity.
constructor;[rewrite Heq|rewrite IHx];reflexivity.
Qed.

(* devrait etre dans Pring, oups cést  Pmul_Rat_aux_assoc*)
Lemma scal_assoc : forall a b C, a !* (b!* C) != (a ** b) !* C.
Proof.
intros a b C.
repeat rewrite  Pscal_Pmul_l.
rewrite Pmul_assoc.
apply Pmul_comp;[idtac|reflexivity].
simpl.
unfold Pol_mul_Rat.
case_c0_test b.
rewrite H0.
constructor.
setoid ring.
case_c0_test (b -- c1).
assert (H1': b == c1).
transitivity (c1 ++ c0);[rewrite <- H1|idtac];setoid ring.
rewrite H1'.
constructor;setoid ring.
reflexivity.
Qed.

Lemma scal_Passoc : forall c P Q, (scal c P)*Q != scal c (P*Q).
Admitted.

(* multinilearity of det when its arg contains a times_X_n_family **)
Lemma det_times_Xn_multilin : forall d a A n l1 l2 ,
 det d (app l1 (app (times_X_n_family (a !* A) n) l2))
!=  (cpow  a (N_of_nat (n+1))) !*
 det d (app l1 (app (times_X_n_family A n) l2)).
Proof.
intros d a;induction n;simpl;intros l1 l2.
rewrite cpow_1.
apply (det_scal d l1 l2 A a).
transitivity (det d
  (app (app l1 ((X * times_X_n (a !* A) n) ::nil))  (app (times_X_n_family (a !* A) n) l2))).
apply det_morph.
rewrite app_ass.
simpl;reflexivity.
rewrite IHn.
transitivity (cpow a (N_of_nat (n + 1))
!* (det d
     (app (app l1 (a!* (X *( times_X_n A n)) :: nil))
        (app (times_X_n_family A n) l2)))).
apply Pmul_Rat_compc.
apply det_morph.
apply app_morph;[idtac|reflexivity].
apply app_morph;[reflexivity|constructor;[idtac|reflexivity]].
rewrite times_X_n_scal.
repeat rewrite  Pscal_Pmul_l;setoid ring.
transitivity (cpow a (N_of_nat (n + 1))
!* det d (app l1 ((a!* (X * times_X_n A n)) :: app (times_X_n_family A n) l2))).
rewrite app_ass.
simpl;reflexivity.
rewrite (det_scal d l1 (app (times_X_n_family A n) l2) (X * times_X_n A n) a).
unfold scal.
rewrite scal_assoc.
assert  (Npos (P_of_succ_nat (n + 1)) = (N_of_nat (n+1) + 1)%N).
unfold N_of_nat.
case (n+1)%nat.
reflexivity.
intro.
simpl.
rewrite Pplus_one_succ_r;reflexivity.
rewrite H.
rewrite (cpow_plus a (N_of_nat (n + 1)%nat) (Npos xH)).
rewrite cpow_1.
reflexivity.
Qed.

(* devrait etre ailleurs *)
Lemma P0test_F : forall P, P0test P =false -> ~P!=P0.
intros P H.
induction P;
intro G;
inversion G.
absurd (c == c0);[idtac|assumption].
apply ceq_propF.
rewrite <- c0test_ceqb;assumption.
caseEq (P0test P);intro Test.
simpl in H.
rewrite Test in H.
absurd (c == c0);[idtac|assumption].
apply ceq_propF.
rewrite <- c0test_ceqb;assumption.
apply IHP;assumption.
Qed.

(* P0test is a morphism, devrait etre ailleurs...*)
Add Morphism P0test with signature Pol_Eq ==> (@eq bool) as P0test_comp.
intros x1 x2 Heq.
induction Heq;simpl;try simpl in IHHeq;try rewrite IHHeq;try rewrite c0test_c0;try rewrite H;trivial.
caseEq (P0test Q);intro G;trivial.
rewrite H;reflexivity.
caseEq (P0test P);intro G;trivial.
rewrite H;trivial.
caseEq (P0test P);intro G;trivial.
rewrite H;trivial.
Qed.

Ltac toto Heq G := 
match goal with
| |-  context [if ?cond then _ else _] =>  rewrite Heq in G;rewrite G
| |- context [nat_deg ?P] => absurd (P!=P0);[apply P0test_F|idtac];assumption
end.

(* nat_deg is a morphism idem...*)
Add Morphism nat_deg with signature Pol_Eq ==> (@eq nat)  as nat_deg_comp.
intros x1 x2 Heq.

induction Heq;simpl;try reflexivity;
caseEq (P0test P);intro G;trivial; try (toto Heq G);trivial.
rewrite IHHeq;trivial.
assert (Qis0:P0test Q =true).
rewrite Heq.
simpl.
rewrite G.
apply c0test_c0.
rewrite Qis0;trivial.
caseEq (P0test Q);intro Qtest.
absurd (Q != P0).
intro Abs.
rewrite Abs in Heq. 
inversion Heq.
rewrite H5 in G.
simpl in G.
rewrite c0test_c0 in G.
discriminate.
apply P0test_is_P0;assumption.

rewrite IHHeq.
simpl.
rewrite G.
rewrite nat_of_P_plus_morphism.
auto with zarith.
caseEq (P0test Q);intro Qtest.
trivial.
absurd (Q != P0).
intro Abs.
rewrite Abs in Qtest;simpl in Qtest.
rewrite c0test_c0 in Qtest.
discriminate.
assert (Pis_zero := P0test_is_P0 P G).
rewrite Pis_zero in Heq.
transitivity (PX P0 i c0);[assumption|constructor;reflexivity].
caseEq (P0test Q);intro Qtest.
assert (Qis_zero := P0test_is_P0 Q Qtest).
rewrite Qis_zero in Heq.
inversion Heq.
rewrite H5 in G.
simpl in G.
rewrite c0test_c0 in G.
discriminate.
rewrite nat_of_P_plus_morphism.
rewrite IHHeq.
simpl.
rewrite G.
auto with zarith.
Qed.

(* useful tactic for desctruction of case(x -- c1) *)
Ltac is_one x :=
 match goal with
[ H : x -- c1 == c0 |- _  ] =>
let G := fresh in
 assert ( G : x == c1) ; [transitivity (c1++c0) ;[ rewrite <- H | idtac] ; setoid ring|idtac]
| |- _ => idtac "rate"
end.

(* devrait etre dans Pring *)
Lemma Pscal_PX : forall P a i b, a !* PX P i b != PX (a !* P) i (a ** b).
Proof.
induction P;intros a i b;unfold Pol_mul_Rat;simpl;
case_c0_test a.
rewrite H0.
constructor;setoid ring.
case_c0_test (a--c1).
is_one a.
constructor;[rewrite H2|idtac];setoid ring.
rewrite cintegral.
rewrite H.
rewrite orb_b_false.
case_c0_test c;try rewrite H2;
(constructor;[idtac|constructor];setoid ring).
constructor;[rewrite H0|reflexivity].
setoid ring.
case_c0_test (a--c1).
is_one a.
constructor;[rewrite H2|idtac];setoid ring.
apply mkPX_PX.
setoid ring.
Qed.

(* a <>0 -> aP = 0 iff P=0 *)
Lemma P0test_scal : forall P a, czero_test a = false -> P0test (a!*P) = P0test P.
Proof.
induction P;intros a Ha;simpl.
unfold Pol_mul_Rat.
rewrite Ha.
simpl.
caseEq (czero_test (a -- c1));intro G;simpl.
trivial.
rewrite cintegral.
rewrite Ha.
auto with bool.
transitivity (P0test (PX (a!*P) p (a**c))).
apply P0test_comp.
apply Pscal_PX.
caseEq (P0test P);intro Ptest.
assert (Pis_0 := P0test_is_P0 P Ptest).
rewrite Pis_0.
simpl.
assert (P0test (a !* P0)=true).
rewrite Pmul_P0_c.
simpl.
apply c0test_c0.
rewrite H.
rewrite cintegral.
rewrite Ha.
auto with bool.
simpl.
assert (P0test (a !* P) =false).
rewrite (IHP a Ha).
assumption.
rewrite H.
trivial.
Qed.

Lemma nat_deg_scal : forall a P, czero_test a = false -> nat_deg (a!* P) = nat_deg P.
Proof.
intro a.
induction P;intro H;
unfold Pol_mul_Rat;
rewrite H.
case_c0_test (a -- c1).
reflexivity.
unfold Pol_mul_Rat_aux.
reflexivity.
case_c0_test (a -- c1).
reflexivity.


simpl.
caseEq (P0test P);intro P0test.
assert (Pis0 := P0test_is_P0 P P0test).
rewrite Pis0.
simpl.
assert (test : czero_test (c0**a) =true).
rewrite  (c0_test_ext (c0**a) c0).
apply c0test_c0.
setoid ring.
rewrite test.
simpl;trivial.
transitivity (nat_deg (PX (a!*P) p (c**a))).
apply nat_deg_comp.
transitivity (PX  (Pol_mul_Rat_aux P a) p (c**a)).
apply mkPX_PX;reflexivity.
constructor;[reflexivity|idtac].
unfold Pol_mul_Rat.
rewrite H.
rewrite H0.
reflexivity.
simpl.
assert (PolMonOSum.P0test  (a !* P) = false).
rewrite P0test_scal;assumption.
rewrite H1.
rewrite (IHP H).
trivial.
Qed.


Lemma mon_spec : forall n, mon (N_of_nat (S n))  != X*mon (N_of_nat n).
Admitted.

Lemma mon_X_spec : forall n, mon (N_of_nat n) != X ^ (N_of_nat n).
Admitted.

 Lemma mon_add : forall n m, (mon n)*(mon m) != mon (n + m). 
Admitted.

(* relation btw times_X_n and mon *)
Lemma times_X_n_to_mon : forall n P, times_X_n P n != P*(mon (N_of_nat n)).
Proof.
induction n;intro P.
simpl;Pcsimpl.
Admitted.

(*times_X_n_family contains the first P*mon n*)
Lemma PIn_times_X_n_family : forall P, forall m n, n <= m -> PIn (P*(mon (N_of_nat n))) (times_X_n_family P m).
Proof.
induction m;intros n Hle;simpl.
inversion Hle;simpl.
left.
Pcsimpl.
inversion Hle.
left.
rewrite times_X_n_to_mon.
rewrite mon_spec.
setoid ring.
right.
exact (IHm n H0).
Qed.


Lemma N_of_nat_add: forall n m, N_of_nat (n + m)  = (N_of_nat n +  N_of_nat m)%N.
Admitted.


(* forall P, P\in family (A + sum g(i)BX^i i=0...k) -> 
P = A + sum g(i)BX^(i+j) i=0...k), for some j<= n*)
Lemma PIn_family_of_sum : forall n A B P k g,
 PIn P (times_X_n_family (A + (Psum (fun i => scal (g i) (B*(mon (N_of_nat i)))) k)) n) ->
exists j, (j<= n)/\(P!=A*(mon (N_of_nat j)) + (Psum (fun i => scal (g i) (B*(mon (N_of_nat (i+j))))) k)).
Proof.
induction n;simpl;intros A B P k g HIn;elim HIn;intro Heq.
exists 0;split.
auto with arith.
rewrite <- Heq.
simpl;Pcsimpl.
apply Padd_comp;[reflexivity|apply Psum_ext].
intro n.
replace (n+0)%nat with n;[reflexivity|auto with arith].
elim Heq.
rewrite 
(times_X_n_to_mon n (A + Psum (fun i : nat => scal (g i) (B * mon (N_of_nat i))) k))
in Heq.
exists (S n);split.
auto with arith.
rewrite <- Heq.
rewrite mon_spec.
setoid ring.
apply Padd_comp;[reflexivity|idtac].
transitivity (Psum (fun i : nat => scal (g i) (B * mon (N_of_nat i))) k *
mon (N_of_nat (S n))).
rewrite mon_spec;setoid ring.
rewrite Psum_mul_r.
apply Psum_ext;intro m.
rewrite <- scal_Passoc.
rewrite  <-  Pmul_assoc.
rewrite mon_add.
replace (N_of_nat m + N_of_nat (S n))%N with (N_of_nat (m + S n)).
apply scal_Passoc.
apply N_of_nat_add.
elim (IHn A B P k g Heq);intros j0 Sol.
elim Sol;intros Lt_j0 EqP.
exists j0;split.
auto with arith.
assumption.
Show Proof.
Qed.



Lemma det_family_sum_aux : forall n l m  k d A B g,
k+n<=m ->
det d (app 
l (app (times_X_n_family (A + (Psum (fun i => scal (g i)  (B*(mon (N_of_nat i)))) k)) n)
(times_X_n_family B m)))
!=
det d (app l (app
(times_X_n_family A n)
(times_X_n_family B m))).
Proof.
induction n;intros l m k d A B g Hle.
simpl.
apply (@det_Psum k (fun i : nat => (B * mon (N_of_nat i)))).
right;right.
apply PIn_times_X_n_family.
omega.
unfold times_X_n_family;fold times_X_n_family.
transitivity (det d 
(app
 (app l ((times_X_n
                    (A + Psum (fun i : nat => scal (g i) (B * mon (N_of_nat i))) k)
                    (S n))::nil))  
(app (times_X_n_family
              (A + Psum (fun i : nat => scal (g i) (B * mon (N_of_nat i))) k)
              n) (times_X_n_family B m)))).
rewrite app_ass; reflexivity.                   
transitivity (det d
       (app 
       (app l
          (times_X_n A (S n) ::nil))
          (app (times_X_n_family A n)
             (times_X_n_family B m)))).

rewrite (IHn (app l
        (times_X_n
           (A + Psum (fun i : nat => scal (g i) (B * mon (N_of_nat i))) k)
           (S n) :: nil)) m k d A B g).
omega.
rewrite app_ass.
replace (app
        (times_X_n
           (A + Psum (fun i : nat => scal (g i) (B * mon (N_of_nat i))) k)
           (S n) :: nil) (app (times_X_n_family A n) (times_X_n_family B m)))
with
        ((times_X_n
           (A + Psum (fun i : nat => scal (g i) (B * mon (N_of_nat i))) k)
           (S n)) ::(app (times_X_n_family A n) (times_X_n_family B m)));[idtac|
reflexivity].
transitivity 
(det d
(app l
((A*(mon (N_of_nat (S n))) 
  + (Psum (fun i : nat => scal (g i) (B * mon (N_of_nat i))) k)*mon(N_of_nat (S n)))::
app (times_X_n_family A n) (times_X_n_family B m)))).
myreplace.
rewrite times_X_n_to_mon.
setoid ring.
transitivity
(det d
  (app l
     (A * mon (N_of_nat (S n)) +
      Psum (fun i : nat => scal (g i) (B * mon (N_of_nat i))*
      mon (N_of_nat (S n))) k
      :: app (times_X_n_family A n) (times_X_n_family B m)))).
myreplace.
rewrite <- (Psum_mul_r k (fun i :nat => scal (g i)(B*(mon (N_of_nat i))))).
setoid ring.
transitivity (det d
     (app l ((times_X_n A (S n)) ::
        (app (times_X_n_family A n) (times_X_n_family B m))))).
transitivity (det d
  (app l
     (A * mon (N_of_nat (S n)) +
      Psum
        (fun i : nat =>
         scal (g i) (B * mon (N_of_nat i) * mon (N_of_nat (S n)))) k
      :: app (times_X_n_family A n) (times_X_n_family B m)))).
myreplace.
apply Padd_comp;[reflexivity|apply Psum_ext].
intro n0;apply scal_Passoc.
rewrite (@det_Psum k (fun i=> (B * mon (N_of_nat i)) * mon (N_of_nat (S n)))).
intros j Hlejk.
right;right.
apply PIn_PIn_app_l.
rewrite <- Pmul_assoc.
rewrite mon_add.
rewrite <- N_of_nat_add.
apply PIn_times_X_n_family.
omega.
myreplace.
symmetry;apply times_X_n_to_mon.
repeat rewrite app_ass;reflexivity.
repeat rewrite app_ass;reflexivity.
Qed.

Lemma det_family_sum : forall n m  k d A B g,
k+n<=m ->
det d 
 (app (times_X_n_family (A + (Psum (fun i => scal (g i)  (B*(mon (N_of_nat i)))) k)) n)
(times_X_n_family B m))
!=
det d (app
(times_X_n_family A n)
(times_X_n_family B m)).
Proof.
intros.
apply (@det_family_sum_aux n (@nil Pol) m k d A B g H) .
Qed.


Definition eps(n:nat) := cpow (-- c1) (N_of_nat n). 
Hypothesis cpow_0 : forall c, cpow c N0 == c1.


Lemma Popp_Pscal : forall P, - P != -- c1 !*P.
Proof.
induction P.
simpl.
Pcsimpl.
rewrite Pscal_Pmul_l.
simpl.
unfold Pol_mul_Rat.
case_c0_test c.
rewrite H0.
Pcsimpl.
setoid ring.
case_c0_test (c -- c1).
is_one c.
rewrite H2;reflexivity.
simpl.
setoid_replace (-- c) with (-- c1** c);[reflexivity|setoid ring].
rewrite Pscal_PX.
simpl.
rewrite IHP.
apply mkPX_PX.
setoid ring.
Qed.


Lemma det_app_rev : forall d l2 l4 l1 l3 l5 a b, 
det d  (app l1 (app (a::l2) (app l3 (app (b::l4) l5)))) !=
scal (eps ((length l2 + 1)%nat*(length l4 + 1)%nat))
(det d  (app l1 (app (b::l4) (app l3 (app (a::l2) l5))))).
Proof.
intros d;induction l2.
intros l4 l1 l3 l5 u v;simpl.
(* beurk*)
unfold scal;setoid_replace (eps 1) with (-- c1).
transitivity (det d (app l1 (app (u::l3) (v::l5)))).
repeat rewrite app_comm_cons;reflexivity.
transitivity (-det d (app l1 (app (v :: l3) (u :: l5))));[apply det_t|repeat rewrite <- app_ass].
repeat rewrite app_comm_cons.
repeat rewrite <- app_ass.
apply Popp_Pscal.
unfold eps.
rewrite cpow_1;reflexivity.
simpl.
transitivity (det d (app l1 (app (u::l3) (v::(a::app l4 l5)))));[reflexivity|rewrite det_t].
transitivity (det d (app (app l1 (u::nil)) (a::nil) (app (
simpl.










intros d;induction l2.
destruct l4;intros l1 l3 l5 u v;simpl.
unfold scal;setoid_replace (eps 1) with (-- c1).
transitivity (det d (app l1 (app (u::l3) (v::l5)))).
repeat rewrite app_comm_cons;reflexivity.
transitivity (-det d (app l1 (app (v :: l3) (u :: l5))));[apply det_t|repeat rewrite <- app_ass].
repeat rewrite app_comm_cons.
repeat rewrite <- app_ass.
apply Popp_Pscal.
unfold eps.
rewrite cpow_1;reflexivity.
simpl.
transitivity (det d (app l1 (app (u::l3) (v::(a::app l4 l5)))));[reflexivity|rewrite det_t].
transitivity (det d (app (app l1 (u::nil)) (a::nil) (app (
simpl.

simpl in IHl4.
rewrite (IHl4 l1 .



rewrite scal_spec.
Pcsimpl.

;simpl in Hl2, Hl4;
try (absurd (0>0);[apply gt_asym|idtac];assumption).
transitivity (det d (app l1 (app (a::(app l2 l3)) (a0::(app l4 l5))))).
myreplace.
repeat rewrite <- app_ass.
rewrite app_comm_cons;reflexivity.
rewrite det_t.
transitivity - det d (app (app l1 (a0::nil))

(replace (length l1 * 0)%nat with 0;[idtac|auto with arith];
unfold scal;setoid_replace (eps 0) with c1;[Pcsimpl|unfold eps;simpl;rewrite cpow_0;reflexivity]).

simpl in IHl4.
transitivity (det d (app l1 (app l3 (app (a :: l4) l5)))).
Focus 2.
rewrite (IHl4 l1 l3 l5).


unfold scal;rewrite cpow_0.
rewrite app_ass;Pcsimpl.



Section SubresPolDef.


Variables P Q : Pol.

Let p:= nat_deg P.
Let q := nat_deg Q.

Definition subres_family(j:nat) := 
app (times_X_n_family P (q-j-1))  (times_X_n_family Q (p-j-1)).

Definition j_subres(j:nat):=det (p+q-j-1) (subres_family j).

End SubresPolDef.

Section SubResProps.


Variables P Q:Pol.
Definition p:= nat_deg P.
Definition q := nat_deg Q.
Hypothesis q_le_p : q<=p.



(* subres j aP bQ = a^(p-j) b^(q-j) *subres j P Q *)
Lemma j_subres_scal: forall a b j, j<q ->czero_test a = false -> czero_test b =false ->
j_subres (a !* P) (b !* Q)  j != (cpow  a (N_of_nat (q-j)%nat)) ** (cpow b (N_of_nat (p-j)%nat)) !* (j_subres P Q j).
Proof.
unfold j_subres.
unfold subres_family.
intros a b j j_lt_q a_not_0 b_not_0.
repeat rewrite (nat_deg_scal);trivial.
fold p;fold q.
transitivity (det (p + q - j - 1) (app nil
  (app (times_X_n_family (a !* P) (q - j - 1))
     (times_X_n_family (b !* Q) (p - j - 1))))).
simpl;reflexivity.
rewrite det_times_Xn_multilin;simpl.
transitivity (cpow a (N_of_nat (q - j - 1 + 1))
!* det (p + q - j - 1)
     (app (times_X_n_family P (q - j - 1))
        (app (times_X_n_family (b !* Q) (p - j - 1)) nil))).
rewrite <- app_nil_end;reflexivity.
rewrite det_times_Xn_multilin.
rewrite scal_assoc.
apply Pmul_Rat_comp.
rewrite <- app_nil_end;reflexivity.
apply cmul_ext.
assert (G:(q - j - 1 + 1)%nat=(q - j)%nat).
omega.
rewrite G;reflexivity.
assert (G:(p - j - 1 + 1)%nat=(p - j)%nat).
omega.
rewrite G;reflexivity.
Qed.


Variables B H:Pol.
Definition b:= nat_deg B.
Definition h:= nat_deg H.

Hypothesis lt_h_q : h <q.
Hypothesis b_is_p_minus_q :  b= (p - q)%nat.

Hypothesis euclid_relation : P !=H+ B*Q.





Definition lcoef(P:Pol):= get_coef (nat_deg P) P.


Ltac myreplace2 :=
  repeat progress
    (match goal with
    | |- times_X_n_family _ _ *= times_X_n_family _ _=> apply X_n_fam_comp;try reflexivity;auto
    | |- context [subres_family _ _ _] => unfold subres_family
    | |- _ =>  myreplace
end).

(* pour la suite, cf bugreport hugo*) 
Ltac cool :=match goal with
| |- context ctx [Pol_mul  (sum_of_Pol ?P)  ?Q ] => let t:= 
(context ctx[ (Psum  (fun i => scal (get_coef i P) ((mon (N_of_nat i)))*Q) (nat_deg P)) ] ) in
transitivity t
end.
Delimit Scope P_scope with Pol.
Bind Scope P_scope with Pol.

Lemma subres_PQ_GH : forall j, j < h ->
j_subres P Q j != ((eps ((p-q)*(q-j))%nat) ** ((lcoef Q) ^^ N_of_nat (p -h)%nat)) !* j_subres Q H j.
Proof with (try reflexivity;auto).
(*we first prove : jsubres P Q j != det (family H (q-j)) (family Q (p-j))*)
intros j Hj.
transitivity (j_subres (H+B*Q) Q j);unfold j_subres.
myreplace2.
rewrite (nat_deg_comp euclid_relation).
myreplace2...
transitivity (det (nat_deg (H + B * Q) + nat_deg Q - j - 1) (subres_family (H + ((sum_of_Pol B)* Q)) Q j)).
myreplace2;rewrite <- (P_mon_sum B)...
unfold subres_family.
rewrite <- (nat_deg_comp euclid_relation).
rewrite  (@nat_deg_comp (H + (sum_of_Pol B)*Q) (H+B*Q)).
(*pourquoi ici replace marche pas???*)
transitivity (
det (nat_deg P + nat_deg Q - j - 1)
  (app (times_X_n_family (H +  (Psum  (fun i => scal (get_coef i B) (mon (N_of_nat i))*Q) (nat_deg B))) (nat_deg Q - j - 1))
     (times_X_n_family Q (nat_deg (H + B * Q) - j - 1)))
).
myreplace2.
apply Padd_comp...
transitivity (
Psum (fun i : nat => (scal (get_coef i B) (mon (N_of_nat i))) * Q)
     (nat_deg B)).
rewrite <- (Psum_mul_r (nat_deg B) (fun i =>  scal (get_coef i B) (mon (N_of_nat i)))).
unfold sum_of_Pol...
apply Psum_ext ;intro n...
transitivity (
det (nat_deg P + nat_deg Q - j - 1)
  (app
     (times_X_n_family
        (H +
         Psum (fun i : nat => scal (get_coef i B) (Q*(mon (N_of_nat i))))
           (nat_deg B)) (nat_deg Q - j - 1))
     (times_X_n_family Q (nat_deg (H + B * Q) - j - 1)))).
myreplace2.
apply Padd_comp;[reflexivity|apply Psum_ext].
intro n.
rewrite scal_Passoc.
unfold scal.
setoid_replace (mon (N_of_nat n) * Q) with (Q*mon (N_of_nat n));setoid ring.
transitivity (
det (nat_deg P + nat_deg Q - j - 1) (app
(times_X_n_family H (nat_deg Q - j - 1))
(times_X_n_family Q (nat_deg (H + B*Q) - j - 1)))).
apply (@det_family_sum
(nat_deg Q - j - 1) ((nat_deg (Pol_add H  (Pol_mul B Q))) - j - 1)%nat (nat_deg B) (nat_deg P + nat_deg Q - j - 1)%nat
H Q (fun i => get_coef i B)).
rewrite <- euclid_relation.
fold p q b h;omega.
(* ok, now we develop the determinant *)






transitivity 
rewrite b_is_p_minus_q.


apply (det_family_sum_aux 
(nat_deg Q - j - 1) ((nat_deg (Pol_add H  (Pol_mul B Q))) - j - 1)%nat (nat_deg Q - j - 1)%nat (nat_deg P + nat_deg Q - j - 1)%nat
H Q (fun i => get_coef i B)).



rewrite (det_family_sum (nat_deg H - j - 1)




transitivity (det (nat_deg P + nat_deg Q - j - 1)
(app
     (times_X_n_family H (nat_deg Q - j - 1))
    (times_X_n_family Q (nat_deg (H + B * Q) - j - 1)))).
apply det_family_sum_aux.


Lemma det_Psum : forall m f l1 l2 P d g,
(forall n, n <= m -> (f n) = P0 \/ PIn (f n) l1 \/ PIn (f n) l2) ->
det d (app l1 ((P + Psum (fun i =>scal  (g i)  (f i))  m)::l2))
 != det d (app l1 (P::l2)).


Check X_n_fam_comp.
Check app_morph.



setoid_replace (times_X_n_family (H + sum_of_Pol B * Q) (nat_deg Q - j - 1)) with (@nil Pol).

(* deletion of the monomial sum of B*)
 match goal with
| |- context ctx [Pol_mul (sum_of_Pol ?P) ?Q ] =>
let t := 
(context ctx[ (Psum  (fun i => scal (get_coef i P) ((mon (N_of_nat i)))*Q) (nat_deg P)) ] ) in
apply Pol_eq_trans with  t
end.
cool.


Let lc_q := snd (Pol_deg_coefdom Q).
Let lc_h := snd (Pol_deg_coefdom H).
Hypothesis div_rel : P + (B*Q)  != H.

(* somme des entiers de 1 a n*)
Fixpoint sum_up_to(n:nat):nat:=
match n with
|O => O
|S n => ((S n) + (sum_up_to n))%nat
end.

(* (-1)^(n*(n-1))/2 *)
Definition eps(n:nat) := cpow (--c1) (N_of_nat (sum_up_to (pred n))).

(* 
Lemma subres_shift : forall j, j < h ->
j_subres P Q j != (eps (p -q)%nat) !*((cpow lc_q (N_of_nat (p - q)%nat)) !*(j_subres Q H j)).
Admitted.

Lemma subres_h :
j_subres P Q h !=(eps (p -q)%nat) !*((cpow lc_q (N_of_nat (p - q)%nat)) !*((cpow lc_h (N_of_nat (q - h -1)%nat))!*H)).
Admitted. 


Lemma first_nul_subres : forall j, h<j<q-1 ->
j_subres P Q j != P0.
Admitted.

Lemma subres_q_1 :
j_subres P Q (pred q) != (eps (p-q)%nat )!*((cpow lc_q (N_of_nat (p - q+1))) !* H).
Admitted.

Lemma Pol_deg_add : forall A B a b c,
nat_deg A  =a -> nat_deg B = b -> le a b -> nat_deg (A+B)  = c -> le c b. 
Proof.
induction A;destruct B;simpl;intros;try omega.
caseEq (BinInt.ZPminus p0 p1);intros;rewrite H3 in H2.
Admitted.

