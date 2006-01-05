
  (* builds the ring structure for newring, creates a Polring tactic *)
  
  (* ring theory and extensionality*)
  Definition PRth := mk_rt P0 P1 Pol_add Pol_mul Pol_sub Pol_opp Pol_Eq
    Padd_0_l Padd_sym Padd_assoc Pmul_1_l
    Pmul_sym Pmul_assoc Pdistr_l Psub_def Popp_def.

  Definition Peqe := mk_reqe Pol_add Pol_mul Pol_opp Pol_Eq
    Padd_ext Pmul_ext Popp_comp.
  
  (* instanciation *)
  Module PolAE.
    Definition R := Pol.
    Definition req := Pol_Eq.
    Definition Rsth := Pol_Setoid.
    Definition rO := P0.
    Definition rI := P1.
    Definition radd := Pol_add.
    Definition rmul := Pol_mul.
    Definition rsub := Pol_sub.
    Definition ropp := Pol_opp.
    Definition Reqe := Peqe.
    Definition Rth := PRth.  
  End PolAE.

  Module PolEntries := SAE_Entries PolAE.

  Module Polring := MakeRingPol PolEntries.

(* il ne veut pas c0 et c1 : User error: c0 is bound to a notation that does not denote a reference*)
  Ltac PolCst := genCstZ P0 P1.
		       
  Ltac Pring :=
    let T := Polring.Make_ring_tac in
      T Pol_add Pol_mul Pol_sub Pol_opp Pol_Eq PolCst.


  (* j'arive pas encore a faire passer ca en cvs, ..
  Ltac crewrite :=
    let T := Coefring.Make_ring_rewrite in
      T cadd cmul csub copp ceq CoefCst.*)
