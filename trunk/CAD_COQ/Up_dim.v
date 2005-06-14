
Unset Boxed Definitions.
Unset Boxed Values.



 (*Require Import Qabs_rec.
  Require Import CAD_rec.*)
Require Import CAD.
Require Import Qabs.
Require Import Utils.

Set  Implicit Arguments.

Module MK_UP_DIM(Q:RAT_STRUCT).


  
  Module QFUNS:= RAT_FUNS Q.
  Module QINT := RAT_INT_OPS Q.
  Import Q.
  Import QFUNS.
  Import QINT.


  (*Variable Rat_struct : Rat_ops.
  Definition C_base := Rat Rat_struct.*)

  Section UP_DIM.
  (*Variable CAD_n : Cad Rat Rat_struct.*)
  
  Variable C:Set.
  Variable CAD_n : Cad Rat C.

  Definition Coef := Pol1 C.
(*  Definition Coef := Pol CAD_n.*)
  Definition c0 := Pol_0 CAD_n.
  Definition c1 := Pol_1 CAD_n.
  Definition cadd := Pol_add CAD_n.
  Definition cmul := Pol_mul CAD_n.
  Definition csub := Pol_sub CAD_n.
  Definition copp := Pol_opp CAD_n. 
  Definition cdeg := Pol_deg CAD_n.
  Definition czero_test := Pol_zero_test CAD_n.
  Definition cof_pos := Pol_of_pos CAD_n.
  Definition cpow := Pol_pow CAD_n.
  Definition cdiv := Pol_div CAD_n.
  Definition csubres_list := Pol_subres_list CAD_n.
  Definition subres_coef_list := Pol_subres_coef_list CAD_n.
  Definition cis_base_cst := Pol_is_base_cst CAD_n.
  Definition cmkPc := Pol_mk_Pc CAD_n.
  Definition cmk_coef := Pol_mk_coef CAD_n.
  Definition  cmult_base_cst := Pol_mult_base_cst CAD_n.
  Definition cdiv_base_cst :=  Pol_div_base_cst CAD_n.
  Definition csquare_free := Pol_square_free CAD_n.
  Definition cgcd_gcd_free := Pol_gcd_gcd_free CAD_n.
  Definition csign_at := Pol_sign_at CAD_n. 
  Definition clow_bound := Pol_low_bound CAD_n.
  Definition clow_sign := Pol_low_sign CAD_n.
  Definition ccell_point_proj := cell_point_proj CAD_n.
  Definition low_cell_point := cell_point CAD_n.
  Definition cell_point := cell_point_up CAD_n.
  Definition cvalue_bound := Pol_value_bound CAD_n.
  Definition cCert:=Cert CAD_n.
  Definition cmk_Cert := mk_Cert CAD_n.
  Definition cCert_fst := Cert_fst CAD_n.
  Definition cbuild_Cert := build_Cert CAD_n.
  Definition ccell_point_up_refine := cell_point_up_refine CAD_n.
  Definition cbase_cst_sign := Pol_base_cst_sign CAD_n.
  Definition ccad := Pol_cad CAD_n.
  Definition cprint_cell := print_cell CAD_n.
  (* for intervals, we keep a polynomial, its ben coefs over the int,
   and for each bern coef, its degree and square free part *)




  Load Gen_functor.
  (*Are now available:
     Pol_add :Pol -> Pol->Pol
     Pol_mul :Pol->Pol->Pol
     Pol_sub :Pol->Pol->Pol
     Pol_opp :Pol->Pol
     Pol_div:Pol->Pol->Pol
     Pol_zero_test : Pol->bool
     mk_PX := Pol ->positive -> Coef -> Pol
     Pol_of_pos := positive -> Pol
     Pol_pow := Pol -> N -> Pol
     Pol_subres_list := Pol -> Pol-> list Pol
     Pol_subres_coef_list := Pol -> Pol -> list Coef
     Pol_gcd := Pol -> Pol -> Pol
     Pol_square_free := Pol -> Pol
     Pol_deriv := Pol -> Pol
     Pol_eval := Pol -> Coef -> Coef.
     Pol_trunc : Pol  -> list Pol 
     Pol_mk_coef : 
     Pol_mkPc := 
     Pol_is_base_cst 
     Pol_mult_base_cst
     Pol_div_base_cst 
     Pol_partial_eval 
     Pol_trunc
     Pol_bern_coefs
     Pol_bern_split+....*)

  (*

  Definition triple_csign_at(u:four_uple Coef Coef N Sign)(z:cell_point):=
  let (P, Pbar, dPbar, low) := u in 
  csign_at P Pbar dPbar low .

  Definition Pol_bern_coefs_tag(P:Pol)(a b:C_base)(dP:N)(z:cell_point):=
  let blist := Pol_bern_coefs P a b dP in
  let g:= fun u =>
    let ubar := csquare_free u in
    (Four u ubar  (cdeg ubar) (clow_sign u (ccell_point_proj z))) in
  map g blist.

  Definition Pol_bern_split_tag(c d e:C_base)(b:list (four_uple Coef Coef N Sign))(z:cell_point):=
  let bcoefs := map (fun x => four_fst x) b in
  let g:= fun u =>
    let ubar := csquare_free u in
    (Four u ubar (cdeg ubar) (clow_sign u (ccell_point_proj z))) in
  let split := Pol_bern_split bcoefs c d e in
  let (b',b'') := split in
  (map g b', map g b'').*)

  Definition cmk_Cert_above(z:cell_point)(n:nat)(P:Coef):=
  let Pbar :=csquare_free P in
    let dPbar := cdeg Pbar in
      cmk_Cert P Pbar dPbar (clow_sign (ccell_point_proj z) P Pbar dPbar n).

  Definition Pol_bern_split_tag(z:cell_point)(blist:list cCert)(c d e:Rat)(n:nat):=
  let bern_coef := map cCert_fst blist in
    let (b',b''):= Pol_bern_split bern_coef c d e in
      (map (cmk_Cert_above z n) b', map (cmk_Cert_above z n) b'').
  (*rajouter z *)

  Definition Pol_eval_sign_at_isol(P Pbar:Pol)(z:cell_point)(c:Rat)(n:nat):=
  let Pbar_at_c := Pol_partial_eval Pbar c in
    let P_at_c := Pol_partial_eval P c in
      let dPbar_at_c := cdeg Pbar_at_c in
	csign_at (cmk_Cert P_at_c Pbar_at_c dPbar_at_c   
	  (clow_sign (ccell_point_proj z) P_at_c Pbar_at_c dPbar_at_c n)) z n.



  (*** Bounds for the roots of a polynomial above an isolated root *)

  Definition  sum_square_coef:=
  fix sum_square_val_coef (P:Pol):Coef:=
    match P with
      |Pc p => p **  p
      |PX P' i p => (p ** p) ++ sum_square_val_coef P' 
    end.
  
  Definition Pol_num_bound(P:Pol)(z:cell_point):=
  let n:= sum_square_coef P in
    cvalue_bound z n.


  Definition Pol_bound(P:Pol)(z:cell_point):=
  let (dP, den) := Pol_deg_coefdom P in
    let (a,b):= (Pol_num_bound P z)  in
      let (c,d) := (cvalue_bound z (den ** den)) in
	let (res,_) :=  rdiv_int a b c d in
	  rprod (radd (rof_N dP)  r1) res.

  Definition  Pol_up_bound(P:Pol)(z:cell_point):= radd (Pol_bound P z) r1.

  Definition  Pol_low_bound(P:Pol)(z:cell_point):= ropp (radd (Pol_bound P z) r1).

  Definition Pol_low_sign(z:cell_point)(P Pbar:Pol)(dPbar:N)(n:nat):=
  let m:= Pol_low_bound P z in
  let P_atm := (Pol_partial_eval P m) in
  let Pbar_atm := Pol_partial_eval Pbar m in
  let dPbar_atm := cdeg Pbar_atm in
  let s := clow_sign (ccell_point_proj z) P_atm Pbar_atm (cdeg Pbar_atm) n in 
	  csign_at (cmk_Cert P_atm Pbar_atm dPbar_atm s) z n.

  Definition Pol_low_sign_for_upper(z:cell_point)(P Pbar:Pol)(dPbar:N)(n:nat):=
  snd (snd (Pol_low_sign z P Pbar dPbar n)).
  (*propager,les args de low_sign sont pas bons *)

  (* while mapping sign determination over a list of coef, also refines the cell_point,
  by remembering the refinments made by the sign computations *)

  Definition csign_at_refine(z:cell_point)(l:list cCert)(n:nat):cell_point*list (Coef*Sign):= 
  let sign_refine := fix sign_refine(l:list cCert)(res:cell_point*list (Coef *Sign)){struct l}:
    cell_point*list (Coef*Sign):=
    match l with
      |nil => res
      |hd :: tl =>
	let (z', s):= csign_at hd z n in
	  sign_refine tl (z', (s::(snd res)))
    end in
    sign_refine l (z,nil).

  (***root isolation above an int cell point *)

  (*isolates roots of P over ]c d[ above z*)
  Definition root_isol1(P:Pol)(z:cell_point)(Pbar:Pol):=
  fix root_isol1(res:list (isol_box*(list (Pol*Sign))))
    (c d:Rat)(blist: list cCert)(n:nat){struct n}:
    list (isol_box*(list (Pol*Sign))):=
    if rlt d c 
      then nil
      else
	let (z,Vb) := csign_at_refine z blist n in
          let test := op_sign_changes (map (fun x => snd x) Vb) in
	    match test  with
              |None => (Pair z (c, d) P Pbar blist, (P,None)::nil)::res
	      |Some O => res
	      |Some 1 =>
		match  (sign_mult 
                  (snd (snd (Pol_eval_sign_at_isol P Pbar z c n)))
                  (snd (snd (Pol_eval_sign_at_isol P Pbar z d n)))) with
                  |None => (Pair z (c,d) P Pbar  blist, (P,None)::nil)::res
                  |Some Eq =>
                    match n with
                      |O=> (Pair z (c, d) P Pbar blist, (P,None)::nil)::res
                      |S n' => 
                        let mid := rdiv (radd d c)  (2 # 1) in
                          let (b', b''):= Pol_bern_split_tag z blist c d mid n in
                            let res':= root_isol1 res c  mid  b' n' in
                              let Pmid := snd (snd (Pol_eval_sign_at_isol Pbar Pbar z mid n)) in
                                match  Pmid  with
                                  |None =>  (Pair z (c,d) P Pbar blist, (P,Pmid)::nil):: res
                                  |Some Eq => root_isol1 ((Singl z mid, (P,Pmid)::nil)::res')
                                    mid d b'' n'
                                  |_ => root_isol1 res'  mid d b'' n'
                                end
                    end
                  |_ =>((Pair z (c, d) P Pbar blist), (P,(Some Eq))::nil)::res
                end
	      |_ =>
		match n with
		  |O => (Pair z (c, d) P Pbar blist, (P,None)::nil)::res
		  |S n' => 
		    let mid := rdiv (radd d c)  (2 # 1) in
		      let (b', b''):= Pol_bern_split_tag  z blist c d mid n in
			let res':= root_isol1 res c  mid  b' n' in
			  let Pmid := snd (snd (Pol_eval_sign_at_isol Pbar Pbar z mid n)) in
			    match  Pmid with
                              |None => (Pair z (c, d) P Pbar blist,(P, Pmid)::nil)::res
			      |Some Eq =>
				root_isol1 ((Singl z mid, (P,Pmid)::nil)::res') mid d b'' n'
			      |_ =>
				root_isol1 res'  mid d b'' n'
                            end
		end
	    end.

  Definition Pol_bern_coefs_tag(z:cell_point)(P:Pol)(a b:Rat)(degPbar:N)(n:nat):=
  let b_init := Pol_bern_coefs P a b degPbar in
    map (cmk_Cert_above z n) b_init.

  Definition root_isol(P:Pol)(z:cell_point)(Pbar:Pol)(degPbar:N)(lbound ubound:Rat)(n:nat):= 
  let (z', sign):=(Pol_low_sign z P Pbar degPbar n) in
    root_isol1 P z Pbar
    ((Minf z' lbound, (P,snd sign)::nil)::nil)
    lbound ubound (Pol_bern_coefs_tag z P lbound ubound degPbar n) n.



  Definition root_isol_int(P:Pol)(z:cell_point)(Pbar:Pol)(degPbar:N)
  (c d:Rat)(n:nat) := 
  root_isol1  P z Pbar
  nil c d (Pol_bern_coefs_tag z P c d degPbar n) n.


  (* Sign of Q at a root of P : *)

   (** which is not a root of Q*)
   (*   None means n was not large enough *)

  Definition sign_at_non_com(z:cell_point)(Q Qbar:Pol)(dQbar:N):=
  fix sign_at_non_com(a b:Rat)(P Pbar:Pol)
    (bern bernQ:list cCert) (n:nat){struct n}: (isol_box*(Pol* Sign)):=
    let (z,Vb) := csign_at_refine z bernQ n in
      let test := op_sign_changes (map (fun x => snd x) Vb) in
	match test with
	  |None => (Pair z (a,b) P Pbar bern, (Q, None))
       	  |Some O => (Pair z (a,b) P Pbar bern, (Q, snd (snd (Pol_eval_sign_at_isol Q Qbar z a n))))
	  | _ => 
	    let mid := rdiv (radd a b)  (2 # 1) in
	      let Pbar_mid := snd (snd (Pol_eval_sign_at_isol Pbar Pbar z mid n)) in
		match Pbar_mid with
		  |None =>(Pair z (a,b) P Pbar bern, (Q, None))
                  |Some Eq => (Singl z mid , (Q,snd ( snd (Pol_eval_sign_at_isol Q Qbar z mid n))))
		  |_ =>
		    match n with
		      |O => (Pair z (a,b) P Pbar bern, (Q, None))
		      |S m =>
			match (sign_mult 
                          (snd (snd (Pol_eval_sign_at_isol P Pbar z mid n)))
                          (snd (snd (Pol_eval_sign_at_isol P Pbar z a n)))) with
                          |None => (Pair z (a,b) P Pbar bern, (Q, None))
                          | Some Lt  =>
			    let (bern',_) := Pol_bern_split_tag z bern a b mid n in
			      let (bernQ',_) := Pol_bern_split_tag z bernQ a b mid n in
				sign_at_non_com a mid P Pbar bern' bernQ' m
			  |_ =>
			    let (_,bern'') := Pol_bern_split_tag  z bern a b mid n in
			      let (_,bernQ'') := Pol_bern_split_tag  z bernQ a b mid n in
				sign_at_non_com mid b P Pbar bern'' bernQ'' m
			end
		    end
		end
	end. 

  Definition sign_at_com:= 
  fix sign_at_com (z:cell_point)(a b:Rat)(P Pbar G Gbar:Pol)
    (bernG bernQ:list cCert)(n:nat){struct n}:
    isol_box*Sign:=
    let (z,Vb) := csign_at_refine z bernQ n in
      let test := op_sign_changes  (map (fun x => snd x) Vb) in
	match test with
	  |None => (Pair z (a,b) G Gbar bernG, None)
	  |Some O => (Pair z (a,b) G Gbar bernG, None) (*never!*)
	  |Some 1 => (Pair z (a,b) G Gbar bernG, (Some Eq))
	  | _ =>
	    let mid := rdiv (radd a b)  (2 # 1) in
	      let Pbar_mid := snd (snd (Pol_eval_sign_at_isol Pbar Pbar z mid n)) in
		match Pbar_mid with
                  |None => (Pair z (a,b) G Gbar bernG, None)
		  |Some Eq => (Singl z mid, (Some Eq))
		  | _ => 
		    match n with
		      |O => (Pair z (a,b) G Gbar bernG, None)
		      |S n' =>
			match (sign_mult 
                          (snd (snd (Pol_eval_sign_at_isol Pbar Pbar z a n)))
                          Pbar_mid) with
                          |None =>  (Pair z (a,b) G Gbar bernG, None)
			  |Some Lt =>
			    let (bernG',_):=Pol_bern_split_tag z bernG a b mid  n in
			      let (bernQ',_):= Pol_bern_split_tag z bernQ a b mid n in
			        sign_at_com z a mid P Pbar G Gbar bernG' bernQ' n'
			  |_ =>
			    let (_,bernG''):=Pol_bern_split_tag z bernG a b mid n in
			      let (_,bernQ''):=Pol_bern_split_tag z bernQ a b mid  n in
			        sign_at_com z mid b P Pbar G Gbar bernG'' bernQ'' n'
			end
		    end
		end
	end.


    (*refines a Pair to determine the sign of Q at that root of P
      G = gcd P Q, ie up to the point where G has either a unique root or no root*)

  Definition Pair_refine (z:cell_point)(Q Qbar:Pol)(dQbar:N):=
  fix Pair_refine(a b:Rat)(P Pbar G:Pol)
    (bern bernG:list cCert)(n:nat){struct n}:
    isol_box*(Pol*Sign):=
    let (z,Vb) := csign_at_refine z bernG n in
      let test := op_sign_changes (map (fun x => snd x) Vb) in
	match test with
          |None => (Pair z (a,b) P Pbar bern,(Q, None))
	  |Some O => 
	    let bernQ := (Pol_bern_coefs_tag z Qbar a b dQbar n) in
	      sign_at_non_com z Q Qbar dQbar a b P Pbar bern bernQ n 
	  |Some 1 =>
	    let bernQ := Pol_bern_coefs_tag z Qbar a b dQbar n in
	      let Gbar := Pol_square_free G in
		let res :=  sign_at_com z a b P Pbar G Gbar bernG bernQ n in
		  (fst res, (Q, snd res))
	  |_ =>
	    let mid := rdiv (radd a b) (2 # 1) in
	      let Pbar_mid := snd (snd (Pol_eval_sign_at_isol Pbar Pbar z mid n)) in
		match Pbar_mid with
		  |None => (Pair z (a,b) P Pbar bern, (Q, None))
		  |Some Eq =>  (Singl z mid, (Q, snd (snd (Pol_eval_sign_at_isol Q Qbar z mid n))))
		  |_ =>
		    match n with
		      |O => (Pair z (a,b) P Pbar bern,(Q, None))
		      |S m =>
			match (sign_mult 
                          (snd (snd (Pol_eval_sign_at_isol Pbar Pbar z a n)))
                          Pbar_mid) with
                          |None =>  (Pair z (a,b) P Pbar bern,(Q, None))
                          |Some Lt =>
              		    let (bern',_):=Pol_bern_split_tag z bern a b mid n in
              		      let (bernG',_):=Pol_bern_split_tag z bernG a b mid n in
              			Pair_refine a mid P Pbar G bern' bernG' m
             	          |_ =>
			    let (_,bern''):=Pol_bern_split_tag z bern a b mid n in
			      let (_,bernG''):=Pol_bern_split_tag z bernG a b mid n in
				Pair_refine
				mid b P Pbar G bern'' bernG'' m
			end
		    end
		end
	end.

     (* Sign of Q at an element of an isolating list,
      previous failures are propagated*)

  Definition sign_at_root(Q Qbar:Pol)(dQbar:N)(low:Sign)(t:isol_box)(n:nat):
  isol_box*Sign:=
  match t with
    |Minf _ _ => (t, low)
    |Singl z r => 
      (Singl z r, snd (snd (Pol_eval_sign_at_isol Q Qbar z r n)))
    |Pair z (a,b) P Pbar bern =>
      let Pbar := Pol_square_free P in
	let G := Pol_gcd Q P in
	  let dG := Pol_deg G in
	    let bernG :=Pol_bern_coefs_tag z G a b dG n in
	      let res :=  (Pair_refine z Q Qbar dQbar a b P Pbar G bern bernG  n) in
                (fst res, (snd (snd res)))

  end.


  Definition  sign_list_at_root(Q Qbar:Pol)(dQbar:N)(low:Sign)(t:isol_box*(list (Pol*Sign)))(n:nat):
  isol_box*(list (Pol * Sign)) :=
  let (root, sign_list) :=  t in
    match sign_list with
      |nil => 
	let (root_res, sign_res):= sign_at_root Q Qbar dQbar low root n in
	  (root_res, (Q,sign_res)::nil)
	  |(_,None) :: _ => (root, (Q,None) :: sign_list)
      |_ :: _ =>
	let (root_res, sign_res):= sign_at_root Q Qbar dQbar low root n in
	  (root_res, (Q,sign_res)::sign_list)
    end.

  

  Definition Pol_info_eval_sign(n:nat)(a:Rat)(z:cell_point)(u:Pol_info):=
  match u with
    |Cst_sign P s => (P,s)
    |Non_cst_sign u => 
      let (P,freeP,_,_):= u in 
	(P,snd (snd (Pol_eval_sign_at_isol P freeP z a n)))
  end.
  (* find the sign col after a root, above a cell point, evaluating only if necessary *)
  Definition fill_sign_between(z:cell_point)(n:nat) :=
  fix fill_sign_between(b:Rat)(lsign:list (Pol*Sign))(lpol:list Pol_info)
    {struct lsign}:list (Pol*Sign) :=
    match lsign,lpol with
      |nil,_  => nil
      |shd::stl, nil => nil
      |shd::stl, phd::ptl =>
	match shd with
	  |(_,None) =>  shd ::(fill_sign_between b stl ptl)
	    |(_,Some Eq) => (Pol_info_eval_sign n b z phd)::(fill_sign_between b stl ptl)
	  |_ => shd :: (fill_sign_between b stl ptl)
	end
    end.


(* ci dessus mal ecrite : i lfudra prouver que l'info sur le pol dans
le couple est bien celle de la tete courante de la liste.*)


  Definition add_roots(z:cell_point)(P:Pol)(freeP:Pol)(dfreeP:N)
  (lP:list Pol_info)(n:nat) :=
  fix add_roots(l:list (isol_box*(list (Pol*Sign))))
    (low up:Rat)(lowsign upsign:Sign)
    {struct l}:list (isol_box*(list (Pol*Sign))) :=
    match l with
      |nil => nil
      |hd :: tl =>
	let tag := fst hd in
	  let prev_slist := snd hd in
	    match tag with
	      |Minf z _ =>
		let resP := root_isol_int P z freeP dfreeP  low up n in
		  let (z',slow):=(Pol_low_sign z P freeP dfreeP n) in
		    ((add_to_cst_list resP prev_slist)@
		      (Minf z' low, (P,snd slow)::prev_slist)::nil)
	      |Singl _ r =>
		if orb (rlt up r) (rzero_test (rsub r up))
		  then
		    (tag,  (P,upsign)::prev_slist)::
		    (add_roots tl low r lowsign upsign)
		  else
		    let signP_r := snd (snd (Pol_eval_sign_at_isol P freeP z r n)) in			
		      let resP := root_isol_int P z freeP dfreeP r up n in
			let prev_next_sign := fill_sign_between z n (rdiv (radd r up) (2 # 1))
			  prev_slist lP in
			  let res_r_up := (add_to_cst_list resP prev_next_sign) in
			    res_r_up @
			    ((Singl z r, (P,signP_r):: prev_slist)::
			      (add_roots tl low r  lowsign signP_r))
	      |Pair _  (a,b) Q Qbar bern =>
		let refine := sign_list_at_root P freeP dfreeP lowsign hd n in
		  match (fst refine) with
		    |Minf _ _ => (Minf z low, (P,None) :: prev_slist):: tl (*should never happen*)
		    |Singl _ r =>
		      if orb (rlt up r) (rzero_test (rsub r up))
			then
			  refine::
			    (add_roots  tl low r lowsign upsign)
			else
			  let signP_r :=
			    match snd refine with
			      |nil => (P,None)
			      |s :: tl => s
			    end in
			    let prev_next_sign :=
			      fill_sign_between z n (rdiv (radd r up) (2#1)) prev_slist lP in
			      let resP := (root_isol_int P z freeP dfreeP r up n) in
				let res_r_up := (add_to_cst_list resP prev_next_sign) in
				  res_r_up @
				  (refine::
				    (add_roots tl low r  lowsign 
				      (snd signP_r)))
		    |Pair _ (a', b') Q' Qbar' bern' =>
		      if orb (rlt up a') (rzero_test (rsub a' up))
			then
			  refine::
			    (add_roots tl  low a' lowsign upsign)
			else
			  let Pa' := snd (snd (Pol_eval_sign_at_isol P freeP z a' n)) in
			    let Pb' := snd (snd (Pol_eval_sign_at_isol P freeP z b' n)) in
			      let prev_next_sign :=
				fill_sign_between z n (rdiv (radd b' up) (2#1)) prev_slist lP in
				let resP := (root_isol_int P z freeP dfreeP b' up n) in
				  let res_b'_up := (add_to_cst_list resP prev_next_sign) in
				    match  Pb',  Pa' with
                                      |None, _ => l
                                      |_,None =>l
                                      |Some Eq, Some Eq =>
					let prev_a'_sign := map (Pol_info_eval_sign n a' z) lP in
					  res_b'_up @
					  ((Singl z b', (P,(Some Eq))::prev_next_sign)::
					    refine ::
					      (Singl z a', (P,(Some Eq))::prev_a'_sign)::
					      (add_roots tl low a'  
						lowsign Pa'))
                                      |Some Eq, Some _  =>
					res_b'_up @
					((Singl z b', (P,(Some Eq))::prev_next_sign)::
					  refine::
					    (add_roots  tl low a' 
					      lowsign Pa' ))
				      |Some _, Some Eq =>
					let prev_a'_sign := map (Pol_info_eval_sign n a' z) lP in
					  res_b'_up@
					  (refine ::
					    (Singl z a', (P,(Some Eq))::prev_a'_sign)::
					    (add_roots  tl low a'
					      lowsign Pa'))
                                      |Some _, Some _ =>
					res_b'_up @ 
					(refine::
					  (add_roots tl low a'  
					    lowsign Pa'))
				    end
		  end
	    end
    end.	



  (* flags for polynomials:if the Pol is known to have a cst sign (it is a cst),
   then gives this sign, otherwise keep the informations to be computed one and for all *)


   (*head is the biggest root, computes the isolating list*)
  Definition family_root (z:cell_point):= 
  fix family_roots(Pol_list : list Pol_info)(n:nat)
    {struct Pol_list}:list (isol_box*(list (Pol*Sign))):=
    match Pol_list with
      |nil => nil
      |i :: tl =>
	match i with
	  |Cst_sign P s =>
            match tl with
              |nil => ((Minf z r0), (P, s)::nil)::nil
              |_ =>
		let prev := family_roots tl n in
		  add_cst_sign prev P s
            end
	  |Non_cst_sign u =>
	    let (P,Pfree,dPfree, lowsign) := u in
	      let P_low := Pol_low_bound P z in 
		let P_up := Pol_up_bound P z in
		  let upsign := snd (snd (Pol_eval_sign_at_isol P Pfree z P_up n)) in
		    match tl with
		      |nil => root_isol P z Pfree dPfree P_low P_up n
		      |_ =>
			let prev := family_roots tl n in
			  add_roots z P Pfree dPfree tl n prev P_low P_up lowsign upsign
		    end
	end
    end.




  Definition sign_at_cell_up(Q Qbar:Pol)(dQbar:N)(low:Sign)(t:cell_point_up)(n:nat):=
  match t with
    |Root t => let (tag_res,sign_res) := sign_at_root Q Qbar dQbar low t n in
      (Root tag_res, (Q, sign_res))
    |Between z b =>let (cell,sign):=Pol_eval_sign_at_isol Q Qbar z b n in
      (Between cell b, (Q,snd sign))
  end.


    (*sign table for the family up to "up",included.
      up is not a root 
       head corresponds to the smallest root*)

(*
  
  Definition sign_table1 (z:cell_point)(glow gup:Rat)(n:nat):=
  fix sign_table1(Pol_list : list Pol_info)
    (isol_list : list (isol_box*(list (Pol*Sign))))
    (up:Rat)
    (res:list (cell_point_up*(list (Pol*Sign)))){struct isol_list}:
    list (cell_point_up*(list (Pol*Sign))):=
    let Sign_eval := (fun x:Rat => fun u:four_uple Pol Pol N Sign =>
    let (P,Pbar,dPbar,Plow) := u in
      Pol_eval_sign_at_isol  P Pbar z x n) in	
    match isol_list with
      |nil => res
      |hd::tl =>
	let hdTag := fst hd in
	let hdSign := snd hd in
	  match hdTag with
	    |Minf _ _ => (Between z glow, hdSign)::res
	    |Singl _ r =>
	      let bet := rdiv (radd r up) (2 # 1) in
		sign_table1 Pol_list tl r 
		((Root hdTag, hdSign) ::
		  ((Between z bet,fill_sign_between z n bet hdSign Pol_list)::res))
	    |Pair _  (a,b) _ _ _ =>
	      let bet := rdiv (radd b up) (2#1) in
		sign_table1 Pol_list tl a
		((Root hdTag, hdSign)
		  ::((Between z bet,fill_sign_between z n bet hdSign Pol_list) ::res))
	  end
    end.
*)


  Definition sign_table1 (z:cell_point)(glow gup:Rat)(n:nat):=
  fix sign_table1(Pol_list : list Pol_info)
    (isol_list : list (isol_box*(list (Pol*Sign))))
    (up:Rat)
    (res:list (cell_point_up*(list (Pol*Sign)))){struct isol_list}:
    list (cell_point_up*(list (Pol*Sign))):=
    let Sign_eval := (fun x:Rat => fun u:four_uple Pol Pol N Sign =>
    let (P,Pbar,dPbar,Plow) := u in
      Pol_eval_sign_at_isol  P Pbar z x n) in	
    match isol_list with
      |nil => res
      |hd::tl =>
	let hdTag := fst hd in
	let hdSign := snd hd in
	  match hdTag with
	    |Minf _ _ => 
		match (tail res) with
		|nil => res
		|_ => (Between z glow, hdSign)::res
		end
	    |Singl _ r =>
		match (tail res) with
		|nil => 
		let bet := rdiv (radd r up) (2 # 1) in
		sign_table1 Pol_list tl r 
		((Root hdTag, hdSign) ::res)
		|_ =>
	      let bet := rdiv (radd r up) (2 # 1) in
		sign_table1 Pol_list tl r 
		((Root hdTag, hdSign) ::
		  ((Between z bet,fill_sign_between z n bet hdSign Pol_list)::res))
		end
	    |Pair _  (a,b) _ _ _ =>
		match (tail res) with
		|nil =>
	      let bet := rdiv (radd b up) (2#1) in
		sign_table1 Pol_list tl a
		((Root hdTag, hdSign) ::res)
		|_ =>
	      let bet := rdiv (radd b up) (2#1) in
		sign_table1 Pol_list tl a
		((Root hdTag, hdSign)
		  ::((Between z bet,fill_sign_between z n bet hdSign Pol_list) ::res))
		end
	  end
    end.




 Definition up_sign_eval(m:Rat)(z:cell_point)(n:nat)(u:Pol_info):=
 match u with
   |Cst_sign P s => (P,s)
   |Non_cst_sign f =>
     let (P, Pbar,_, _):= f in
     let P_atm := (Pol_partial_eval P m) in
     let Pbar_atm := Pol_partial_eval Pbar m in
     let dPbar_atm := cdeg Pbar_atm in
     let s := clow_sign (ccell_point_proj z) P_atm Pbar_atm (cdeg Pbar_atm) n in 
       (P,snd (snd (csign_at (cmk_Cert P_atm Pbar_atm dPbar_atm s) z n)))
 end.


  Definition Pol_info_up_bound(z:cell_point)(u:Pol_info):=
  match u with
    |Cst_sign P s => r0
    |Non_cst_sign f => Pol_up_bound (four_fst f) z
  end. 


  Definition Pol_info_low_bound(z:cell_point)(u:Pol_info):=
  match u with
    |Cst_sign P s => r0
    |Non_cst_sign f => Pol_low_bound (four_fst f) z
  end. 

(*
  Definition sign_table(z:cell_point)(Pol_list:list Pol_info)(n:nat):=
  let up := rmax_list (map (Pol_info_up_bound z) Pol_list) in
    let low := rmin_list (map (Pol_info_low_bound z) Pol_list) in
      let roots := family_root z Pol_list n in
	(sign_table1 z low up n Pol_list roots up nil).
*)

  Definition sign_table(z:cell_point)(Pol_list:list Pol_info)(n:nat):=
  let up := rmax_list (map (Pol_info_up_bound z) Pol_list) in
  let low := rmin_list (map (Pol_info_low_bound z) Pol_list) in
  let up_signs := map (up_sign_eval up z n) Pol_list in 
  let roots := family_root z Pol_list n in
    (sign_table1 z low up n Pol_list roots up ((Between z up, up_signs)::nil)).


  (* Elimination of the last variable *)
  
      (* each element of llP is the list of truncations of a P in the
    initial list. for each R in tr(P), computes the subres coefs sr_j(R,
    dR/dX) where X is the current variable *)

  Definition subres_der_flat:=
  fix subres_der_flat(llP:list (list Pol))(res:list Coef)
    {struct llP}: list Coef:=
    match llP with
      |nil => nil
      |lP :: llP' =>
	let subres_der_ac := 
	  fix subres_der_ac(l:list Pol)(res:list Coef){struct l}:
	    list Coef :=
	    match l with
	      | nil => res
	      | P :: l' =>
		subres_der_ac l' ((Pol_subres_coef_list P (Pol_deriv P)) @ res)
	    end in
	    subres_der_ac lP (subres_der_flat llP' res)
    end.


      (* from the same list as above, computes all the sr_j(R,S) where R
    is in tr(P) and S in tr(Q) *)

  Definition subres_flat := 
  fix subres_flat(llP:list (list Pol))(res: list Coef)
    {struct llP}:list Coef :=
    match llP with
      |nil => res
      |lP :: llP' =>
	match llP' with
	  |nil => res
	  |lQ :: _ =>
	    let subres_peer:= 
	      fix subres_peer (u v:list Pol)(res:list Coef)
		{struct u}:
		list Coef:=
		match u with
		  |nil => res
		  |R :: u' =>
		    let dr := Pol_deg R in
		      let subres := (fun x =>
			let dx := Pol_deg x in
			  match (Ncompare dr dx) with
			    |Lt => Pol_subres_coef_list x R
			    |_ => Pol_subres_coef_list R x
			  end) in
		      subres_peer u' v ((flat_map subres v) @ res)
		end in
		subres_flat llP' 
		((flat_map (fun x => subres_peer lP x nil) llP')@res)
	end
    end.

      (* computes the projection of the family P by subresultant
    elimination and erase multiple occurences*)

 Definition ceq(P Q:Coef):= czero_test (P -- Q). 

  Definition elim(l:list Pol) :=
    let l_tr_coef := map Pol_trunc l in
      let l_tr := map (fun u => fst u) l_tr_coef in
	let l_coef := flat_map (fun u => snd u) l_tr_coef in 
	  let subres_der := subres_der_flat l_tr l_coef in
	    clean_list ceq (subres_flat l_tr subres_der).



  Definition cert_refine(z:cell_point)(P Pbar:Pol)(a b:Rat)(bern:list cCert)(n:nat):=
  let mid := rdiv (radd a b) (2#1) in
    let Pmid := Pol_partial_eval P mid in
      let Pbarmid := Pol_partial_eval Pbar mid in
	let (z, s):=csign_at (cmk_Cert Pmid Pbarmid (cdeg Pbarmid) (Some Eq)) z n in(*Some Eq is dummy*)
	  match snd s with
            |None => None
            |Some Eq => Some (Root (Singl z mid))
	    | _ => 
              let (z,Vb) := csign_at_refine z bern n in
		let test := op_sign_changes (map (fun x => snd x) Vb) in
		  let (b',b''):=Pol_bern_split_tag z bern a b mid n in
		    match test with
		      |None => None
              	      |Some 1 => Some (Root (Pair z (a,mid) P Pbar b'))
              	      |Some _ => Some (Root (Pair z (mid, b) P Pbar b''))
              	    end
	  end.

  Definition cell_point_up_refine(z:cell_point_up)(n:nat) :=
  match z with
    |Root ibox => 
      match ibox with
	|Singl z' r =>
          let res := (ccell_point_up_refine z' n) in
            match res with
              |None => None
              |Some z' => Some (Root (Singl  z' r))
            end
	|Pair z' (a,b) P Pbar c =>
          let res := (ccell_point_up_refine z' n) in
            match res with
              |None => None
              |Some z' => cert_refine z'  P Pbar a b c n
            end
        |Minf z' m =>
          let res := (ccell_point_up_refine z' n) in
            match res with
              |None => None
              |Some z' => Some (Root (Minf z' m))
            end
      end
    |Between z' b => 
      let res := (ccell_point_up_refine z' n) in
        match res with
          |None => None
          |Some z' => Some (Between z' b)
        end
  end.



  (* non_deg computes the list of the non deg forms of the list of Pols l above a cell_point,
   and the associated refinement of the cell_point. Returns a list of truncated forms of Pols in l,
  where zeros leading coefs have been supressed and intervals in z are sharp enough to give a
  strictly non-zero bound for the (non-zeros)  leading coefs of these truncations *)

  (* finds the sign of c in sign_list *)


  (* sign of a coef:either the one of a base cst or a sign to find in the sign col*)
  Definition sign_find(c:Coef):=
  match cbase_cst_sign c with
    |Some s => fun x => Some s
    |_ =>
      fix sign_find(sign_list:list (Coef*Sign)):Sign :=
	match sign_list with
	  |nil => None
	  |s::stl =>
	    if (czero_test  (c -- (fst s))) then (snd s) else sign_find stl
	end
  end.


  (*is P has a non zero leading coef abov z, then the result of mkPX P i c is also in normal form
  WARNING : not in normal form with respect to power index *)
  (*on pourrait mais ca fait des calculs pour rien*)


  Definition mkPX_above(P:Pol)(infodom:Coef*Sign)(i:positive)(c:Coef)
  (sign_col:list (Coef*Sign)):=
  match P with
    |PX _ _ _ => (PX P i c,infodom)
    |Pc p =>
      let (domP,sign_domP):= infodom in
	match sign_domP with
	  |None=>(PX P i c,infodom) (*????*)
	  |Some Eq =>
            let c_sign :=sign_find c sign_col in
              match c_sign with
                |Some Eq => (Pc c0,(c0, Some Eq))
                |_ => (Pc c,(c,c_sign))
              end
	  |Some _ => (PX P i c,infodom)
	end
  end.



  (*computes the non degenerated form of a polynomial above a cell, return the leading coef 
  of the truncation and its sign*)

  Definition Pol_non_deg (sign_col:list (Coef*Sign)) :=
  fix Pol_non_deg (P:Pol):Pol*(Coef*Sign):=
    match P with
      |Pc c => 
        let c_sign := sign_find  c sign_col in
          match c_sign with
            |None => (Pc c, (c,None))
            |Some Eq => (Pc c0, (c0, Some Eq))
            |Some _ => (Pc c, (c, c_sign))
          end
      |PX P i p =>
        let (P, infodom):=Pol_non_deg P in
          mkPX_above P infodom i p sign_col
    end.


  (* idem but returns the relevant Pol_info, also possibly  computes a refinement for z *)
  Definition Pol_non_deg_info (cad_col:cell_point * list (Coef*Sign))(P:Pol)(n:nat):=
  let (z, sign_col):= cad_col in
    let (P, infodom):=Pol_non_deg sign_col P in
      let (_, domsign) := infodom in
	match P, domsign with
	  |_, None => (z, (Cst_sign P None, infodom))
	  |Pc _, _ => (z,(Cst_sign P domsign,infodom))
	  |_,_ => 
            let Pbar := Pol_square_free P in 
              let dPbar := Pol_deg Pbar in
		let (z', Pbar_sign):=(Pol_low_sign z P Pbar dPbar n) in
		  (z', (Non_cst_sign (Four P Pbar (Pol_deg Pbar) (snd Pbar_sign)), infodom))
	end.

  (* c is known to be non zero at z, refines z to get a sharp bound on the values of c*)
  Definition cell_refine_for(c:Coef):=
  fix cell_refine_for(z:cell_point)(n:nat){struct n}:option cell_point:=
    let (a,b) := cvalue_bound z c in
      match rsign (rprod a b) with 
	|Gt => Some z
	|_ => 
          match n with
            |O => None
            |S n => let z' := ccell_point_up_refine z n in
              match z' with
		|None => None
		|Some z' => cell_refine_for z' n
              end
          end
      end.

  Definition non_deg1:=
  fix non_deg(l:list Pol)(cad_col:cell_point*(list (Coef*Sign)))(n:nat)
    (res:(list Pol_info)*(cell_point*(list(Coef*Sign)))){struct l}:
    (list Pol_info)*(cell_point*(list(Coef*Sign))):=
    match l with
      |nil => res
      |P::Pol_tl=>
        let (z, sign_col):= cad_col in 
          let (z, u) := Pol_non_deg_info cad_col P n in
            let (info_pol, info_dom):=u in 
              let (dom, dom_sign) := info_dom in
                let (z,info_pol) :=
                  (match dom_sign with
                     |None => (z, info_pol)
                     |Some Eq => (z, info_pol)
                     |Some _ => 
                       let P:= Pol_of_info_Pol info_pol in 
                         let zres:= cell_refine_for dom z n in
                           match zres with
                             |None => (z, Cst_sign P None)
                             |Some z =>(z, info_pol)
                           end
                   end) in
                  let new_cad_col :=(z, sign_col) in
                    non_deg Pol_tl new_cad_col n (info_pol::(fst res), new_cad_col)
    end.

  Definition non_deg(l:list Pol)(cad_col:cell_point*(list (Coef*Sign)))(n:nat):=
  non_deg1 l cad_col n (nil, cad_col).


  Definition one_table_up(l:list Pol)(n:nat)(cad_col:cell_point*(list (Coef*Sign))):=
  let (l',cad_col):=non_deg l cad_col n in
    let (z,_):= cad_col in
      sign_table z l' n.

  Definition Pol_cad(l:list Pol)(n:nat):=
  let elim_l := elim l in
    let cad := ccad elim_l n in
      flat_map (one_table_up l n) cad.

  Definition Pol_sign_at_for_upper(c:Cert)(z:cell_point_up)(n:nat):=
  let (P,Pbar, dPbar, slow):=c in
    match z with
      |Between z r =>
	let P_atr := Pol_partial_eval P r in
	  let Pbar_atr := Pol_partial_eval Pbar r in
	    let dPbar_atr := cdeg Pbar_atr in
	      let z':= ccell_point_proj z in
		let lowsign_at_r := clow_sign z' P_atr Pbar_atr dPbar_atr n in
		  let (z',Pol_sign):=csign_at  (cmk_Cert P_atr Pbar_atr dPbar_atr lowsign_at_r)  z n in
		    (Between z' r, (P, snd Pol_sign))
      |Root i =>
	let (i, s):= sign_at_root P Pbar dPbar slow i n in
	  (Root i, (P,s))
    end.




Definition print_cad(Pol_list:list Pol)(n:nat):=
 let table := Pol_cad Pol_list n in
 map (fun x:cell_point_up*(list (Pol*Sign)) => let (a,b):= x in (print_cell a, b)) table.


  Definition CAD_make :=@mk_cad Rat Coef (*Rat_struct*)
    (*Coef Pol*)
    P0 P1
    Pol_add Pol_mul Pol_sub Pol_opp Pol_deg mkPX 
    Pol_zero_test   Pol_of_pos  Pol_base_cst_sign Pol_pow   Pol_div
    Pol_subres_list  Pol_subres_coef_list
    (*Pol_gcd*) Pol_gcd_gcd_free   Pol_square_free   Pol_deriv 
    Pol_eval   Pol_is_base_cst 
    Pol_mkPc   cmkPc 
    Pol_mult_base_cst   Pol_div_base_cst
    Pol_partial_eval 
    cell_point  cell_point_up print_cell cell_point_up_proj cell_point_up_refine
    Pol_low_bound Pol_up_bound
    Pol_value_bound Cert mk_Cert build_Cert Cert_fst 
    Pol_low_sign_for_upper Pol_sign_at_for_upper Pol_cad print_cad.



End UP_DIM.

End MK_UP_DIM.
  (* TODO : virer les contenus constants dans polynomes, et les
    constantes dans elim (?)*)



