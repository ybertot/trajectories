(* Pour charger  une structure de coefs, avec des noms courts pour les champs*)
(*Attention il n'y a pas de sections...*)

  Variable Coef :Set.

  (* operations sur les coefs*)
  Variable cops : Coef_ops Coef.


  Notation cdeg := (Cdeg cops).
  Notation c0 := (C0 cops).
  Notation c1 := (C1 cops).
  Notation cadd := (Cadd cops).
  Notation cmul := (Cmul cops).
  Notation copp := (Copp cops).
  Notation csub := (Csub cops).
  Notation czero_test := (Czero_test cops).
  Notation cpow := (Cpow cops).
  Notation cof_pos := (Cof_pos cops).
  Notation ceqb := (Ceqb cops).



  (* Notations for coefs *)
  Notation "x ++ y" := (cadd x y) (at level 50, left associativity).
  Notation "x ** y":= (cmul x y) (at level 40, left associativity).
  Notation "-- x" := (copp x) (at level 35, right associativity).
  Notation "x -- y" := (csub x y) (at level 50, left associativity).



  (* Compatibility between equalities, zerotest *)
  Variable ceq_compat : Coef_eq_compat cops.
  Notation ceq := (Ceq ceq_compat).
  Notation ceq_prop := (Ceq_prop ceq_compat).
  Notation c0test_c0 := (C0test_c0 ceq_compat).
  Notation  c0test_c := (C0test_c ceq_compat).
  Notation  c0_diff_c1 := (C0_diff_c1 ceq_compat).
  Notation  cpow_plus := (Cpow_plus ceq_compat).

  Notation "x == y":=(ceq x y)(at level 70, no associativity).
  (* eq is a setoid eq and ext for ring operations*)
  Variable cset : Coef_setoid ceq_compat.

  Notation ceq_refl := (Ceq_refl cset).
  Notation ceq_sym := (Ceq_sym cset).
  Notation ceq_trans := (Ceq_trans cset).

  (* ops morphisms *)
  Variable cmorph : Coef_morph ceq_compat.

  Notation cadd_ext := (Cadd_ext cmorph).
  Notation cmul_ext := (Cmul_ext cmorph).
  Notation copp_ext := (Copp_ext cmorph).

  (* ring ops on coefs satisty ring axioms *)

  Variable cring_struct : Coef_ring ceq_compat.
  Notation cadd_0_l    := (Cadd_0_l cring_struct).
  Notation cadd_sym    := ( Cadd_sym cring_struct).
  Notation cadd_assoc  := ( Cadd_assoc cring_struct).
  Notation cmul_1_l    := (Cmul_1_l cring_struct).
  Notation cmul_sym    := (Cmul_sym cring_struct).
  Notation cmul_assoc  := (Cmul_assoc cring_struct).
  Notation cdistr_l    := (Cdistr_l cring_struct).
  Notation csub_def    := (Csub_def cring_struct).
  Notation copp_def    := (Copp_def cring_struct).
