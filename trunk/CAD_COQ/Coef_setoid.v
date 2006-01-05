(* Construit une structure de setoid et declare de morphismes si on a
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

  (* Setoid structure on Coef *)
  Lemma csetoid : Setoid_Theory Coef  ceq.
  Proof.   
    constructor.
    exact ceq_refl.
    exact ceq_sym .
    exact ceq_trans .
  Qed.
  
  Add Setoid Coef ceq csetoid  as Csetoid.

  (* Morphism declarations *)
  Add Morphism cadd: cadd_compat.
    intros;apply cadd_ext ;auto.
  Qed.
  
  Add Morphism cmul: cmul_compat.
    intros;apply  cmul_ext  ;auto.
  Qed.

  Add Morphism copp: copp_compat.
    intros ; apply copp_ext;auto.
  Qed.

