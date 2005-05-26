Require Import Qabs_rec.
Require Import CAD_rec.
Require Import Utils.

Section UP_DIM.

Variable Rat_struct : Rat_ops.
Let C_base := Rat Rat_struct.

Variable CAD_n : Cad Rat_struct.

Let Coef := Pol CAD_n.
Let c0 := Pol_0 CAD_n.
Let c1 := Pol_1 CAD_n.
Let cadd := Pol_add CAD_n.
Let cmul := Pol_mul CAD_n.
Let csub := Pol_sub CAD_n.
Let copp := Pol_opp CAD_n. 
Let cdeg := Pol_deg CAD_n.
Let czero_test := Pol_zero_test CAD_n.
Let cof_pos := Pol_of_pos CAD_n.
Let cpow := Pol_pow CAD_n.
Let cdiv := Pol_div CAD_n.
Let csubres_list := Pol_subres_list CAD_n.
Let subres_coef_list := Pol_subres_coef_list CAD_n.
Let cis_base_cst := Pol_is_base_cst CAD_n.
Let cmkPc := Pol_mk_Pc CAD_n.
Let cmk_coef := Pol_mk_coef CAD_n.
Let  cmult_base_cst := Pol_mult_base_cst CAD_n.
Let cdiv_base_cst :=  Pol_div_base_cst CAD_n.
Let csquare_free := Pol_square_free CAD_n.
Let csign_at := Pol_sign_at CAD_n. 
Let clow_bound := Pol_low_bound CAD_n.
Let clow_sign := Pol_low_sign CAD_n.
Let ccell_point_proj := cell_point_proj CAD_n.
Let low_cell_point := cell_point CAD_n.
Let cell_point := cell_point_up CAD_n.
Let cvalue_bound := Pol_value_bound CAD_n.
Let cCert:=Cert CAD_n.
Let cmk_Cert := mk_Cert CAD_n.
Let cCert_fst := Cert_fst CAD_n.
Let cbuild_Cert := build_Cert CAD_n.
Let ccell_point_up_refine := cell_point_up_refine CAD_n.
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

Let triple_csign_at(u:four_uple Coef Coef N Sign)(z:cell_point):=
let (P, Pbar, dPbar, low) := u in 
csign_at P Pbar dPbar low .

Let Pol_bern_coefs_tag(P:Pol)(a b:C_base)(dP:N)(z:cell_point):=
let blist := Pol_bern_coefs P a b dP in
let g:= fun u =>
  let ubar := csquare_free u in
  (Four u ubar  (cdeg ubar) (clow_sign u (ccell_point_proj z))) in
map g blist.

Let Pol_bern_split_tag(c d e:C_base)(b:list (four_uple Coef Coef N Sign))(z:cell_point):=
let bcoefs := map (fun x => four_fst x) b in
let g:= fun u =>
  let ubar := csquare_free u in
  (Four u ubar (cdeg ubar) (clow_sign u (ccell_point_proj z))) in
let split := Pol_bern_split bcoefs c d e in
let (b',b'') := split in
(map g b', map g b'').*)

     Let Pol_bern_split_tag(z:cell_point)(blist:list cCert)(c d e:C_base):=
	let bern_coef := map cCert_fst blist in
	let (b',b''):= Pol_bern_split bern_coef c d e in
       let f := fun x => cbuild_Cert x (clow_sign x (ccell_point_proj z)) in
	(map f b', map f b'').
(*rajouter z *)

Let Pol_eval_sign_at_isol(P Pbar:Pol)(z:cell_point)(c:C_base):=
let Pbar_at_c := Pol_partial_eval Pbar c in
let P_at_c := Pol_partial_eval P c in 
  csign_at (cmk_Cert P_at_c Pbar_at_c
   (cdeg Pbar_at_c) (clow_sign P_at_c (ccell_point_proj z))) z.




(*** Bounds for the roots of a polynomial above an isolated root *)

Let  sum_square_coef:=
fix sum_square_val_coef (P:Pol):Coef:=
     match P with
       |Pc p => p **  p
       |PX P' i p => (p ** p) ++ sum_square_val_coef P' 
     end.
   
Let Pol_num_bound(P:Pol)(z:cell_point):=
let n:= sum_square_coef P in
cvalue_bound z n.


Let Pol_bound(P:Pol)(z:cell_point):=
let (dP, den) := Pol_deg_coefdom P in
let (a,b):= (Pol_num_bound P z)  in
let (c,d) := (cvalue_bound z (den ** den)) in
let (res,_) :=  rdiv_int a b c d in
rprod (radd (rof_N dP)  r1) res.

Let  Pol_up_bound(P:Pol)(z:cell_point):= radd (Pol_bound P z) r1.

Let  Pol_low_bound(P:Pol)(z:cell_point):= ropp (radd (Pol_bound P z) r1).

  Let Pol_low_sign(z:cell_point)(P Pbar:Pol)(dPbar:N)(n:nat):=
  let m:= Pol_low_bound P z in
  let P_atm := (Pol_partial_eval P m) in
  let Pbar_atm := Pol_partial_eval Pbar m in
  let s := clow_sign P_atm (ccell_point_proj z) in 
    csign_at (cmk_Cert P_atm Pbar_atm dPbar s) z n.

(*propager,les args de low_sign sont pas bons *)


(* while mapping sign determination over a list of coef, also refines the cell_point,
by remembering the refinments made by the sign computations *)
Let csign_at_refine(z:cell_point)(l:list cCert)(n:nat):cell_point*list Sign:= 
let sign_refine := fix sign_refine(l:list cCert)(res:cell_point*list Sign){struct l}:
cell_point*list Sign:=
  match l with
  |nil => (z,snd res)
  |hd :: tl =>
  let (z', s):= csign_at hd z n in
  sign_refine tl (z', (s::(snd res)))
end in
sign_refine l (z,nil).

(***root isolation above an int cell point *)

(*isolates roots of P over ]c d[ above z*)
Let root_isol1(P:Pol)(z:cell_point)(ubound lbound:C_base)(Pbar:Pol)(degPbar:N):=
   fix root_isol1(res:list (isol_box*(list Sign)))
     (c d:C_base)(blist: list cCert)(n:nat){struct n}:
     list (isol_box*(list Sign)):=
     if rlt d c 
       then nil
       else
	 let (z,Vb) := csign_at_refine z blist n in
         let test := op_sign_changes Vb in
	   match test  with
             |None => (Pair z (c, d) P Pbar blist, None::nil)::res
	     |Some O => res
	     |Some (S O) =>
	       match  (sign_mult 
                           (snd (Pol_eval_sign_at_isol P Pbar z c n))
                           (snd (Pol_eval_sign_at_isol P Pbar z d n))) with
                           |None => (Pair z (c,d) P Pbar  blist, None::nil)::res
                           |Some Eq =>
                              match n with
                              |O=> (Pair z (c, d) P Pbar blist, None::nil)::res
                              |S n' => 
                              let mid := rdiv (radd d c)  (2 # 1) in
                              let (b', b''):= Pol_bern_split_tag z blist c d mid in
                              let res':= root_isol1 res c  mid  b' n' in
                                  match  snd (Pol_eval_sign_at_isol Pbar Pbar z mid n) with
                                  |None =>  (Pair z (c,d) P Pbar blist, None::nil):: res
                                  |Some Eq => root_isol1 ((Singl z mid, (Some Eq)::nil)::res')
                                  mid d b'' n'
                                  |_ => root_isol1 res'  mid d b'' n'
                                  end
                              end
                           |_ =>((Pair z (c, d) P Pbar blist), (Some Eq)::nil)::res
                           end
	     |_ =>
	       match n with
		 |O => (Pair z (c, d) P Pbar blist, None::nil)::res
		 |S n' => 
		   let mid := rdiv (radd d c)  (2 # 1) in
		     let (b', b''):= Pol_bern_split_tag  z blist c d mid in
		       let res':= root_isol1 res c  mid  b' n' in
			 match snd (Pol_eval_sign_at_isol Pbar Pbar z mid n) with
                           |None => (Pair z (c, d) P Pbar blist, None::nil)::res
			   |Some Eq =>
			     root_isol1 ((Singl z mid, (Some Eq)::nil)::res') mid d b'' n'
			   |_ =>
			     root_isol1 res'  mid d b'' n'
                        end
	       end
	   end.
Let Pol_bern_coefs_tag(z:cell_point)(P:Pol)(a b:C_base)(degPbar:N):=
let b_init := Pol_bern_coefs P a b degPbar in
let f:= fun x => cbuild_Cert x (clow_sign x (ccell_point_proj z)) in
map f b_init.

Let root_isol(P:Pol)(z:cell_point)(ubound lbound:C_base)(Pbar:Pol)(degPbar:N)(n:nat):= 
let (z', sign):=(Pol_low_sign z P Pbar degPbar n) in
root_isol1 P z ubound lbound Pbar degPbar
     ((Minf z' lbound, sign::nil)::nil)
     ubound lbound (Pol_bern_coefs_tag z P lbound ubound degPbar) n.



Let root_isol_int(P:Pol)(z:cell_point)(ubound lbound:C_base)(Pbar:Pol)(degPbar:N)
   (c d:C_base)(n:nat) := 
     root_isol1  P z ubound lbound Pbar degPbar
     nil c d (Pol_bern_coefs_tag z P c d degPbar) n.


(* Sign of Q at a root of P : *)


 (** which is not a root of Q*)
 (*   None means n was not large enough *)

    Let sign_at_non_com(z:cell_point)(Q Qbar:Pol)(dQbar:N):=
    fix sign_at_non_com(a b:C_base)(P Pbar:Pol)
    (bern bernQ:list cCert) (n:nat){struct n}: (isol_box* Sign):=
     let (z,Vb) := csign_at_refine z bernQ n in
     let test := op_sign_changes Vb in
       match test with
       |None => (Pair z (a,b) P Pbar bern, None)
       	 |Some O => (Pair z (a,b) P Pbar bern, snd (Pol_eval_sign_at_isol Q Qbar z a n))
	 | _ => 
	   let mid := rdiv (radd a b)  (2 # 1) in
	     let Pbar_mid := snd (Pol_eval_sign_at_isol Pbar Pbar z mid n) in
	       match Pbar_mid with
		|None =>(Pair z (a,b) P Pbar bern, None)
                |Some Eq => (Singl z mid , snd (Pol_eval_sign_at_isol Q Qbar z mid n))
		|_ =>
		   match n with
		     |O => (Pair z (a,b) P Pbar bern, None)
		     |S m =>
		       match (sign_mult 
                           (snd (Pol_eval_sign_at_isol P Pbar z mid n))
                           (snd (Pol_eval_sign_at_isol P Pbar z a n))) with
                           |None => (Pair z (a,b) P Pbar bern, None)
                            | Some Lt  =>
			    let (bern',_) := Pol_bern_split_tag z bern a b mid in
			     let (bernQ',_) := Pol_bern_split_tag z bernQ a b mid in
			       sign_at_non_com a mid P Pbar bern' bernQ' m
			 |_ =>
			   let (_,bern'') := Pol_bern_split_tag  z bern a b mid in
			     let (_,bernQ'') := Pol_bern_split_tag  z bernQ a b mid  in
			       sign_at_non_com mid b P Pbar bern'' bernQ'' m
		       end
		   end
        end
       end. 

  Let sign_at_com :=
   fix sign_at_com(z:cell_point)(a b:C_base)(P Pbar G Gbar:Pol)
     (bernG bernQ:list cCert)(n:nat){struct n}:
     isol_box*Sign:=
     let (z,Vb) := csign_at_refine z bernQ n in
     let test := op_sign_changes Vb in
       match test with
       |None => (Pair z (a,b) G Gbar bernG, None)
	 |Some O => (Pair z (a,b) G Gbar bernG, None) (*never!*)
	 |Some 1 => (Pair z (a,b) G Gbar bernG, (Some Eq))
	 | _ =>
	   let mid := rdiv (radd a b)  (2 # 1) in
	     let Pbar_mid := snd (Pol_eval_sign_at_isol Pbar Pbar z mid n) in
	       match Pbar_mid with
                   |None => (Pair z (a,b) G Gbar bernG, None)
		   |Some Eq => (Singl z mid, (Some Eq))
		   | _ => 
		   match n with
		     |O => (Pair z (a,b) G Gbar bernG, None)
		     |S n' =>
		       match (sign_mult 
                           (snd (Pol_eval_sign_at_isol Pbar Pbar z a n))
                           Pbar_mid) with
                         |None =>  (Pair z (a,b) G Gbar bernG, None)
			 |Some Lt =>
			   let (bernG',_):=Pol_bern_split_tag z bernG a b mid  in
			     let (bernQ',_):= Pol_bern_split_tag z bernQ a b mid in
			       sign_at_com z a mid P Pbar G Gbar bernG' bernQ' n'
			 |_ =>
			   let (_,bernG''):=Pol_bern_split_tag z bernG a b mid in
			     let (_,bernQ''):=Pol_bern_split_tag z bernQ a b mid  in
			       sign_at_com z mid b P Pbar G Gbar bernG'' bernQ'' n'
		       end
		   end
             end
       end.
  (*refines a Pair to determine the sign of Q at that root of P
    G = gcd P Q, ie up to the point where G has either a unique root or no root*)

Let Pair_refine (z:cell_point)(Q Qbar:Pol)(dQbar:N):=
 fix Pair_refine(a b:C_base)(P Pbar G:Pol)
     (bern bernG:list cCert)(n:nat){struct n}:
     isol_box*Sign:=
    let (z,Vb) := csign_at_refine z bernG n in
     let test := op_sign_changes Vb in
       match test with
         |None => (Pair z (a,b) P Pbar bern, None)
	 |Some O => 
	   let bernQ := (Pol_bern_coefs_tag z Qbar a b dQbar ) in
	     sign_at_non_com z Q Qbar dQbar a b P Pbar bern bernQ n 
	 |Some 1 =>
	   let bernQ := Pol_bern_coefs_tag z Qbar a b dQbar in
	   let Gbar := Pol_square_free G in
	     sign_at_com z a b P Pbar G Gbar bernG bernQ n
	 |_ =>
	   let mid := rdiv (radd a b) (2 # 1) in
	     let Pbar_mid := snd (Pol_eval_sign_at_isol Pbar Pbar z mid n) in
               match Pbar_mid with
               |None => (Pair z (a,b) P Pbar bern, None)
               |Some Eq =>  (Singl z mid, snd (Pol_eval_sign_at_isol Q Qbar z mid n))
		|_ =>
		   match n with
		     |O => (Pair z (a,b) P Pbar bern, None)
		     |S m =>
		       match (sign_mult 
                           (snd (Pol_eval_sign_at_isol Pbar Pbar z a n))
                           Pbar_mid) with
                           |None =>  (Pair z (a,b) P Pbar bern, None)
                           |Some Lt =>
              			   let (bern',_):=Pol_bern_split_tag z bern a b mid in
              			     let (bernG',_):=Pol_bern_split_tag z bernG a b mid in
              			       Pair_refine a mid P Pbar G bern' bernG' m
             	           |_ =>
			   let (_,bern''):=Pol_bern_split_tag z bern a b mid in
			     let (_,bernG''):=Pol_bern_split_tag z bernG a b mid in
			       Pair_refine
			       mid b P Pbar G bern'' bernG'' m
		       end
		   end
           end
       end.

   (* Sign of Q at an element of an isolating list,
    previous failures are propagated*)

  Let sign_at_root(Q Qbar:Pol)(dQbar:N)(low:Sign)(t:isol_box)(n:nat):
     isol_box*Sign:=
       match t with
	 |Minf _ _ => (t, low)
	 |Singl z r => 
	   (Singl z r, snd (Pol_eval_sign_at_isol Q Qbar z r n))
	 |Pair z (a,b) P Pbar bern =>
	   let Pbar := Pol_square_free P in
	     let G := Pol_gcd Q P in
	       let dG := Pol_deg G in
		 let bernG :=Pol_bern_coefs_tag z G a b dG in
		   Pair_refine z Q Qbar dQbar a b P Pbar G bern bernG  n
       end.


  Let  sign_list_at_root(Q Qbar:Pol)(dQbar:N)(low:Sign)(t:isol_box*(list Sign))(n:nat):
     isol_box*(list Sign) :=
     let (root, sign_list) :=  t in
       match sign_list with
	 |nil => 
	   let (root_res, sign_res):= sign_at_root Q Qbar dQbar low root n in
	     (root_res, sign_res::nil)
	 |None :: _ => (root, None :: sign_list)
	 |_ :: _ =>
	   let (root_res, sign_res):= sign_at_root Q Qbar dQbar low root n in
	     (root_res, sign_res::sign_list)
    end.

 Let add_cst_sign(l:list (isol_box*(list Sign)))(sign:Sign):=
   let add_sign := fun w => (fst w, sign::(snd w)) in
     map add_sign l.

 Let add_to_cst_list(l:list (isol_box*(list Sign)))(sign :list Sign):=
   let add_list := fun w => (fst w,  (snd w) @ sign) in
     map add_list l. 

(* find the sign col after a root, above a cell point, evaluating only if necessary *)
Let fill_sign_between(z:cell_point)(n:nat) :=
 fix fill_sign_between(b:C_base)(lsign:list Sign)(lpol:list (four_uple Pol Pol N Sign))
   {struct lsign}:list Sign :=
   match lsign,lpol with
     |nil,_  => nil
     |shd::stl, nil => nil
     |shd::stl, phd::ptl =>
       match shd with
	 |None =>  None ::(fill_sign_between b stl ptl)
	 |Some Eq => let (Phd, Pbarhd,dPbarhd, signhd):= phd in
	      (snd (Pol_eval_sign_at_isol Phd Pbarhd z b n))::(fill_sign_between b stl ptl)
	     |_ => shd :: (fill_sign_between b stl ptl)
       end
   end.

Let add_roots(z:cell_point)(P:Pol)(global_up global_l :C_base)(freeP:Pol)(dfreeP:N)
   (lP:list (four_uple Pol Pol N Sign))(n:nat) :=
fix add_roots(l:list (isol_box*(list Sign)))
   (low up:C_base)(lowsign upsign:Sign)
   {struct l}:list (isol_box*(list Sign)) :=
   match l with
     |nil => nil
     |hd :: tl =>
       let tag := fst hd in
	 let prev_slist := snd hd in
	   match tag with
	     |Minf z _ =>
	       let resP := root_isol_int P z global_up global_l freeP dfreeP  low up n in
              let (z',slow):=(Pol_low_sign z P freeP dfreeP n) in
		 ((add_to_cst_list resP prev_slist)@
		   (Minf z' low, slow::prev_slist)::nil)
	     |Singl _ r =>
	       if orb (rlt up r) (rzero_test (rsub r up))
		 then
		   (tag,  upsign::prev_slist)::
		   (add_roots tl low r lowsign upsign)
		 else
		   let signP_r := snd (Pol_eval_sign_at_isol P freeP z r n) in			
		     let resP := root_isol_int P z global_up global_l freeP dfreeP r up n in
		       let prev_next_sign := fill_sign_between z n (rdiv (radd r up) (2 # 1))
			 prev_slist lP in
			 let res_r_up := (add_to_cst_list resP prev_next_sign) in
			   res_r_up @
			   ((Singl z r, signP_r:: prev_slist)::
			     (add_roots tl low r  lowsign signP_r))
	     |Pair _  (a,b) Q Qbar bern =>
	       let refine := sign_list_at_root P freeP dfreeP lowsign hd n in
		 match (fst refine) with
		   |Minf _ _ => (Minf z low, None :: prev_slist):: tl (*should never happen*)
		   |Singl _ r =>
		     if orb (rlt up r) (rzero_test (rsub r up))
		       then
			 refine::
			   (add_roots  tl low r lowsign upsign)
		       else
			 let signP_r :=
			   match snd refine with
			     |nil => None
			     |s :: tl => s
			   end in
			   let prev_next_sign :=
			     fill_sign_between z n (rdiv (radd r up) (2#1)) prev_slist lP in
			     let resP := (root_isol_int P z global_up global_l freeP dfreeP r up n) in
			       let res_r_up := (add_to_cst_list resP prev_next_sign) in
				 res_r_up @
				 (refine::
				   (add_roots tl low r  lowsign 
				     signP_r))
		   |Pair _ (a', b') Q' Qbar' bern' =>
		     if orb (rlt up a') (rzero_test (rsub a' up))
		       then
			 refine::
			   (add_roots tl  low a' lowsign upsign)
		       else
			 let Pa' := snd (Pol_eval_sign_at_isol P freeP z a' n) in
			   let Pb' := snd (Pol_eval_sign_at_isol P freeP z b' n) in
			     let prev_next_sign :=
			       fill_sign_between z n (rdiv (radd b' up) (2#1)) prev_slist lP in
			       let resP := (root_isol_int P z global_up global_l freeP dfreeP b' up n) in
				 let res_b'_up := (add_to_cst_list resP prev_next_sign) in
				   match Pb', Pa' with
                                     |None, _ => l
                                     |_,None =>l
                                     |Some Eq, Some Eq =>
                                      let prev_a'_sign :=
					 map (fun u :four_uple Pol Pol N Sign=> let (P,freeP,_,_):= u in 
                                         snd (Pol_eval_sign_at_isol P freeP z a' n)) lP in
					 res_b'_up @
					 ((Singl z b', (Some Eq)::prev_next_sign)::
					   refine ::
					     (Singl z a', (Some Eq)::prev_a'_sign)::
					     (add_roots tl low a'  
					       lowsign Pa'))
                                    |Some Eq, Some _  =>
				       res_b'_up @
				       ((Singl z b', (Some Eq)::prev_next_sign)::
					 refine::
					   (add_roots  tl low a' 
					     lowsign Pa' ))
				     |Some _, Some Eq =>
				       let prev_a'_sign :=
					 map (fun u :four_uple Pol Pol N Sign=> let (P,freeP,_,_):= u in 
                                         snd (Pol_eval_sign_at_isol P freeP z a' n)) lP in
					 res_b'_up@
					 (refine ::
					   (Singl z a', (Some Eq)::prev_a'_sign)::
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


 (*head is the biggest root, computes the isolating list*)
Let family_root (z:cell_point):= 
 fix family_roots(Pol_list : list (four_uple Pol Pol N Sign))(n:nat)
   {struct Pol_list}:list (isol_box*(list Sign)):=
   match Pol_list with
     |nil => nil
     |u :: tl =>
     let (P,Pfree,dPfree, lowsign) := u in
     let P_low := Pol_low_bound P z in 
     let P_up := radd (Pol_up_bound P z) r1 in
     let upsign := snd (Pol_eval_sign_at_isol P Pfree z P_up n) in
       match tl with
	 |nil => root_isol P z P_up P_low Pfree dPfree n
	 |_ =>
	   let prev := family_roots tl n in
		       add_roots z P P_up P_low Pfree dPfree tl n prev P_low P_up lowsign upsign
       end
   end.


Let sign_at_cell_up(Q Qbar:Pol)(dQbar:N)(low:Sign)(t:cell_point_up)(n:nat):=
   match t with
   |Root t => let (tag_res,sign_res) := sign_at_root Q Qbar dQbar low t n in
   (Root tag_res, sign_res)
   |Between z b =>let (cell,sign):=Pol_eval_sign_at_isol Q Qbar z b n in
 (Between cell b, sign)
   end.


  (*sign table for the family up to "up",included.
    up is not a root 
     head corresponds to the smallest root*)
Let sign_table1 (z:cell_point)(glow gup:C_base)(n:nat):=
 fix sign_table1(Pol_list : list (four_uple Pol Pol N Sign))
   (isol_list : list (isol_box*(list Sign)))
  (up:C_base)
     (res:list (cell_point_up*(list Sign))){struct isol_list}:
   list (cell_point_up*(list Sign)):=
   let Sign_eval := (fun x:C_base => fun u:four_uple Pol Pol N Sign =>
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
		 match res with
		   |nil =>sign_table1 Pol_list tl r 
		     ((Root hdTag, hdSign) ::
		       ((Between z up, fill_sign_between z n bet hdSign Pol_list)::res))
		   |_ =>
		     sign_table1 Pol_list tl r 
		     ((Root hdTag, hdSign) ::
		       ((Between z bet,fill_sign_between z n bet hdSign Pol_list)::res))
		 end
	     |Pair _  (a,b) _ _ _ =>
	       let bet := rdiv (radd b up) (2#1) in
		 match res with
		   |nil =>
		     sign_table1 Pol_list tl a
		     ((Root hdTag, hdSign)
		       ::((Between z gup,fill_sign_between z n bet hdSign Pol_list) ::res))
		   |_ =>
		     sign_table1 Pol_list tl a
		     ((Root hdTag, hdSign)
		       ::((Between z bet,fill_sign_between z n bet hdSign Pol_list) ::res))
		 end
	   end
   end.

 Let sign_table(z:cell_point)(Pol_list:list (four_uple Pol Pol N Sign))(n:nat):=
   let up := radd (rmax_list (map (fun x => Pol_up_bound (four_fst x) z) Pol_list)) r1 in
   let low := rsub (ropp(rmax_list (map (fun x => Pol_low_bound (four_fst x) z) Pol_list))) r1 in
     let roots := family_root z Pol_list n in
       (sign_table1 z low up n Pol_list roots up nil).


(* Elimination of the last variable *)
    
    (* each element of llP is the list of truncations of a P in the
  initial list. for each R in tr(P), computes the subres coefs sr_j(R,
  dR/dX) where X is the current variable *)

Let subres_der_flat:=
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

Let subres_flat := 
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
  elimination *)
    Let elim(l:list Pol) :=
      let l_tr_coef := map Pol_trunc l in
      let l_tr := map (fun u => fst u) l_tr_coef in
      let l_coef := flat_map (fun u => snd u) l_tr_coef in 
      let subres_der := subres_der_flat l_tr l_coef in
	    subres_flat l_tr subres_der.



  Let cert_refine(z:cell_point)(P Pbar:Pol)(a b:C_base)(bern:list cCert)(n:nat):=
     let mid := rdiv (radd a b) (2#1) in
     let Pmid := Pol_partial_eval P mid in
     let Pbarmid := Pol_partial_eval Pbar mid in
     let (z, s):=csign_at (cmk_Cert Pmid Pbarmid (cdeg Pbarmid) (Some Eq)) z n in(*Some Eq is dummy*)
     match s with
        |None => None
        |Some Eq => Some (Root (Singl z mid))
	| _ => 
              let (z,Vb) := csign_at_refine z bern n in
              let test := op_sign_changes Vb in
              let (b',b''):=Pol_bern_split_tag z bern a b mid in
              match test with
              |None => None
              	|Some 1 => Some (Root (Pair z (a,mid) P Pbar b'))
              	|Some _ => Some (Root (Pair z (mid, b) P Pbar b''))
              	end
      end.

Let cell_point_up_refine(z:cell_point_up)(n:nat) :=
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
End UP_DIM.



(* TODO : virer les contenus constants dans polynomes, et les
  constantes dans elim (?)*)



