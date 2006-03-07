Load Pol_ring.


Require Import Mylist.

Require Import Arith.
Require Import Even.


Fixpoint get_coef (k:nat) (P:Pol) {struct k}: Coef:=
           match k with
                        O => match P with 
                                 Pc c => c
                                | PX _ _ c => c
                               end
                        |S k' => match P with
                                Pc _ => c0
                               | PX Q xH _ => get_coef k' Q
                               | PX Q i _ => get_coef k' (PX Q (i-1) c0) 
                         end
                end.

Lemma gcoef_P0 : forall k , get_coef k P0 == c0.
intro k; case k;simpl; intros;setoid ring.
Qed.

(*Axiom Cheat: forall A:Prop,A.*)

Lemma Pplus_xIPminus1_assoc: forall p q , (p + (xI q - 1) = p + xI q - 1)%positive.
intros.
 rewrite (Pplus_reg_l 1(p + (xI q - 1))(p + xI q - 1 )).
auto.
 rewrite Pplus_assoc.
rewrite (Pplus_comm 1).
rewrite <- Pplus_assoc.
rewrite Pplus_minus;auto.
rewrite Pplus_minus; trivial.
destruct p;simpl;auto with arith.
Qed.


Lemma Pplus_Pminus1_assoc: forall p q , (p + (xO q - 1) = p + xO q - 1)%positive.
intros.
 rewrite (Pplus_reg_l 1(p + (xO q - 1))(p + xO q - 1 )).
auto.
 rewrite Pplus_assoc.
rewrite (Pplus_comm 1).
rewrite <- Pplus_assoc.
rewrite Pplus_minus;auto.
rewrite Pplus_minus; trivial.
destruct p;simpl;auto with arith.
Qed.


Add Morphism get_coef  with signature (@eq nat) ==> Pol_Eq ==> ceq as gcoef_Morphism.
induction x.
intros P Q  Heq; inversion Heq; simpl;trivial.
rename P0 into P2;subst.
apply ceq_sym;trivial.
intros P Q  Heq; inversion Heq;try (rename P0 into P2;subst).
simpl; setoid ring.
simpl.
generalize (gcoef_P0 x);intro.
destruct i.
rewrite (IHx (PX P2 (xI i - 1) c0) (P0)).
constructor; [setoid ring|trivial].
apply ceq_sym;trivial.
rewrite (IHx (PX P2 (xO i - 1) c0) P0).
constructor; [setoid ring|trivial].
apply ceq_sym;trivial.
rewrite <-H1; apply IHx; apply PolEq_sym;trivial.
simpl.
generalize (gcoef_P0 x);intro.
destruct i.
rewrite (IHx (PX P2 (xI i - 1) c0) P0); trivial.
constructor; [setoid ring|trivial].
rewrite (IHx (PX P2 (xO i - 1) c0) P0); trivial.
constructor; [setoid ring|trivial].
rewrite <-H1; apply IHx; trivial.
simpl.
destruct i; apply IHx; rewrite H0;setoid ring.
simpl.
destruct j.
destruct i.
simpl Pplus at 1.
simpl.
apply IHx;rewrite H0.
rewrite PX_pq_pq;simpl.
rewrite Pplus_carry_spec.
rewrite xO_succ_permute.
rewrite xI_succ_xO.
generalize (Psucc (xO (i + j))); intro.
generalize (Ppred_succ p0); intro.
assert (Psucc p0 -1 = Ppred (Psucc p0))%positive.
destruct p0;simpl;auto with arith.
rewrite  H2;rewrite H1;setoid ring.
simpl.
apply IHx;rewrite H0.
rewrite PX_pq_pq;simpl.
generalize (i+j)%positive;intro.
assert (xO p0= xI p0 -1)%positive.
destruct p0;simpl;auto with arith.
rewrite H1;setoid ring.
simpl;apply IHx;rewrite H0.
rewrite PX_pq_pq;simpl.
generalize j;intro.
assert (xO(Psucc j0) =xI j0 + 1)%positive.
destruct j;simpl; auto with arith.
rewrite H1;auto  with arith.
assert (xI j0 = xI j0 +1 -1)%positive.
rewrite Pplus_comm; rewrite <-  Pplus_xIPminus1_assoc.
rewrite Pplus_minus;auto.
rewrite <- H2; setoid ring.
destruct i;simpl;apply IHx;rewrite H0.
rewrite PX_pq_pq.
cut ((xI i + (xO j - 1)= xI (i + j) - 1)%positive).
intro h;rewrite h;setoid ring.
rewrite  Pplus_Pminus1_assoc.
simpl;auto.
rewrite PX_pq_pq.
rewrite  Pplus_Pminus1_assoc;simpl;setoid ring.
rewrite PX_pq_pq.
rewrite Pplus_minus; auto;unfold Pminus;simpl; setoid ring.
destruct i;simpl;apply IHx;rewrite H0.
unfold Pminus;simpl.
rewrite Pdouble_minus_one_o_succ_eq_xI;setoid ring.
unfold Pminus;simpl;setoid ring.
unfold Pminus;simpl;setoid ring.
simpl.
destruct i;destruct j; simpl; apply IHx; rewrite H0; try rewrite PX_pq_pq.
unfold Pminus;simpl.
rewrite Pplus_carry_spec.
rewrite Pdouble_minus_one_o_succ_eq_xI;setoid ring.
rewrite  Pplus_Pminus1_assoc;simpl;setoid ring.
unfold Pminus;simpl.
rewrite Pdouble_minus_one_o_succ_eq_xI;setoid ring.
rewrite  Pplus_xIPminus1_assoc;simpl;setoid ring.
rewrite  Pplus_Pminus1_assoc;simpl;setoid ring.
unfold Pminus;simpl;setoid ring.
simpl.
unfold Pmin