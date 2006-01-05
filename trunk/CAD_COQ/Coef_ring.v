
(* a chrager apres Coef_lod.v et Coef_setoid.v, ou bien fournire la
  signature suivante :


  c0 : Coef;
    c1 : Coef;
    cadd : Coef -> Coef -> Coef; qu'on note ++ pour le commentaire 
    cmul : Coef -> Coef -> Coef; deux etoiles
    copp : Coef -> Coef; (--)
    csub : Coef -> Coef -> Coef;(--)
    ceq: Coef -> Coef -> Prop; qu'on note == pour le commentaire 

    ceq_refl : forall x, x==x;
    ceq_sym : forall x y, x == y -> y == x;
    ceq_trans : forall x y z, x == y -> y == z -> x == z
  
    cadd_ext : forall x1 x2 y1 y2,
      x1 == x2 -> y1 == y2 -> x1 ++ y1 == x2 ++ y2;
    cmul_ext : forall x1 x2 y1 y2,
      x1 == x2 -> y1 == y2 -> x1 ** y1 == x2 ** y2;
    copp_ext : forall x1 x2, x1 == x2 -> -- x1 == -- x2


   cadd_0_l    : forall x, c0 ++ x == x;
   cadd_sym    : forall x y, x ++ y == y ++ x;
   cadd_assoc  : forall x y z, x ++ (y ++ z) == (x ++ y) ++ z;
   cmul_1_l    : forall x, c1** x == x;
   cmul_sym    : forall x y, x ** y == y ** x;
   cmul_assoc  : forall x y z, x ** (y ** z) == (x ** y) ** z;
   cdistr_l    : forall x y z, (x ++ y) ** z == (x ** z) ++ (y ** z);
   csub_def    : forall x y, x -- y == x ++ --y;
   copp_def    : forall x, x ++ (-- x) == c0

il faut aussi:
Require Import Ring_tac.
Require Import Pol.
Require Import Ring_theory.

*)

  (* builds the ring structure for newring, creates a cring tactic *)
  
  (* ring theory and extensionality*)
  Definition cRth := mk_rt c0 c1 cadd cmul csub copp ceq
    cadd_0_l cadd_sym cadd_assoc cmul_1_l
    cmul_sym cmul_assoc cdistr_l csub_def copp_def.

  Definition ceqe := mk_reqe cadd cmul copp ceq
    cadd_ext cmul_ext copp_ext.
  
  (* instanciation *)
  Module CoefAE.
    Definition R := Coef.
    Definition req := ceq.
    Definition Rsth := csetoid.
    Definition rO := c0.
    Definition rI := c1.
    Definition radd := cadd.
    Definition rmul := cmul.
    Definition rsub := csub.
    Definition ropp := copp.
    Definition Reqe := ceqe.
    Definition Rth := cRth.  
  End CoefAE.


(*


Module SAE_Entries(SAE:SetoidAbstractEntries).
 Import SAE.
 Definition R := R.
 Definition rO := rO.
 Definition rI := rI.
 Definition radd := radd.
 Definition rmul := rmul.
 Definition rsub := rsub.
 Definition ropp := ropp.
 Definition req := req. 
 Definition Rsth := Rsth.
 Definition Reqe := Reqe.
 Lemma ARth : almost_ring_theory rO rI radd rmul rsub ropp req.
 Proof (@Rth_ARth R rO rI radd rmul rsub ropp req Rsth Reqe Rth).

  (* Coefficients *) 
 Definition C := Z.
 Definition cO := 0%Z.
 Definition cI := 1%Z.
 Definition cadd := Zplus.
 Definition cmul := Zmult.
 Definition csub := Zminus.
 Definition copp := Zopp.
 Definition ceqb := Zeq_bool.
 Definition phi := @gen_phiZ R rO rI radd rmul ropp.
 Lemma CRmorph : ring_morph rO rI radd rmul rsub ropp req
                            cO cI cadd cmul csub copp ceqb phi.
 Proof (@gen_phiZ_morph R rO rI radd rmul rsub ropp req Rsth Reqe Rth).
End SAE_Entries. 

*)


  Module CoefEntries := SAE_Entries CoefAE.

  Module Coefring := MakeRingPol CoefEntries.

(* il ne veut pas c0 et c1 : User error: c0 is bound to a notation that does not denote a reference*)
  Ltac CoefCst := genCstZ (C0 cops) (C1 cops).
		       
  Ltac cring :=
    let T := Coefring.Make_ring_tac in
      T (Cadd cops) (Cmul cops) (Csub cops) (Copp cops) (Ceq ceq_compat) CoefCst.

  (* j'arive pas encore a faire passer ca en cvs, ..
  Ltac crewrite :=
    let T := Coefring.Make_ring_rewrite in
      T cadd cmul csub copp ceq CoefCst.*)
