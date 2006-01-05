(* Construit une structure de relation et declare de morphismes si on a
  dans l'environnement la signature suivante :

    c0 : Coef;
    c1 : Coef;
    cadd : Coef -> Coef -> Coef;
    cmul : Coef -> Coef -> Coef;
    copp : Coef -> Coef;
    csub : Coef -> Coef -> Coef;
    ceq: Coef -> Coef -> Prop; qu'on note == pour le commentaire 

    ceq_refl : forall x, x==x;
    ceq_sym : forall x y, x == y -> y == x;
    ceq_trans : forall x y z, x == y -> y == z -> x == z
  
    cadd_ext : forall x1 x2 y1 y2,
      x1 == x2 -> y1 == y2 -> x1 ++ y1 == x2 ++ y2;
    cmul_ext : forall x1 x2 y1 y2,
      x1 == x2 -> y1 == y2 -> x1 ** y1 == x2 ** y2;
    copp_ext : forall x1 x2, x1 == x2 -> -- x1 == -- x2

il faut aussi:
Require Import Setoid *)


Definition ceq_Eq_Relation_Class : Relation_Class.
 eapply (@SymmetricReflexive unit _ ceq).
 exact ceq_sym.
 exact ceq_refl.
Defined.


Add Relation Coef ceq
 reflexivity proved by ceq_refl
 symmetry proved by ceq_sym
 transitivity proved by ceq_trans
 as ceq_relation.


  (* Morphism declarations *)

Add Morphism cadd with signature ceq ==> ceq ==> ceq as cadd_Morphism.
  intros;apply cadd_ext;assumption.
Qed.

Add Morphism cmul with signature ceq ==> ceq ==> ceq as cmul_Morphism.
  intros;apply cmul_ext;assumption.
Qed.

Add Morphism copp with signature ceq ==> ceq as copp_Morphism.
  intros;apply copp_ext;assumption.
Qed.

