From mathcomp Require all_ssreflect.
Require Import ZArith QArith List String OrderedType OrderedTypeEx FMapAVL.

(* I did not have the courage to understand how to use CoqEAL
  this first version uses only vanilla Coq data structures.  It could still
  use more mathcomp functions, like "has" instead of "existsb" *)

(* FIRST PART: Vertical cell decomposition. *)
(********************************************)
(* The firstion data structures and algorithms are taken from
   github.com/ybertot/Stage_Coq, which was initially a master internship
   by Thomas Portet. *)
(* The main function is edges_to_cells.  The input should respect
  data invariants:
  - all edge extremities are inside the box defined by the bottom and
    top edge
  - all edges should have a left_pt that has a lower x coordinate than the
    right_pt
  - no two edges should cross.
  At the time of writing these lines, the proof of correctness is not
  complete, due to the complexity of the function "step".  Three important
  properties need to be satisfied:
  - edges given in the input never collide with the interior of cells,
  - points in the left_pts and right_pts sequences are vertically aligned
    and are the only potentially colliding points in these segments
  - the elements of left_pts have an x coordinate that is strictly smaller than
    the elements of right_pts *)

Notation seq := list.
(* In the original development Q is replaced by a variable numFieldType. *)
Record pt := Bpt {p_x : Q; p_y : Q}.
(* In the original development, edge have the data invariant that
  the left point has a first coordinate strictly less than the right point. *)
Record edge :=
 Bedge { left_pt : pt; right_pt : pt}.

Record event :=
  Bevent {point : pt; outgoing : seq edge}.

Record cell := Bcell  {left_pts : list pt; right_pts : list pt;
                        low : edge; high : edge}.

Definition dummy_pt := ({| p_x := 0%Q; p_y := 0%Q|}).
Notation DUMMY_PT := 
  ({| p_x := (0 # _); p_y := (0 # _)|}).

Definition dummy_edge := 
  {| left_pt := dummy_pt; right_pt := dummy_pt|}.

Notation DUMMY_EDGE :=
  ({| left_pt := DUMMY_PT; right_pt := DUMMY_PT |}).

Definition dummy_cell := 
  {| left_pts := nil; right_pts := nil; low := dummy_edge; high := dummy_edge|}.

Notation DUMMY_CELL :=
  ({| left_pts := nil; right_pts := nil; 
    low := DUMMY_EDGE; high := DUMMY_EDGE|}).

Definition dummy_event :=
  {| point := dummy_pt; outgoing := nil|}.

(* In the original development pt, edge, and cell are eq_types *)
Definition pt_eqb (a b : pt) : bool :=
  let: Bpt a_x a_y := a in
  let: Bpt b_x b_y := b in
     (Qeq_bool a_x b_x)%Q && (Qeq_bool a_y b_y).

Definition Qlt_bool (q1 q2 : Q) : bool :=
  negb (Qle_bool q2 q1).

Fixpoint add_event (p : pt) (e : edge) (inc : bool) (evs : seq event) :
  seq event :=
  match evs with
  | nil => if inc then (Bevent p nil :: nil)
           else (Bevent p (e :: nil) :: nil)
  | ev1 :: evs' =>
    let p1 := point ev1 in
    if pt_eqb p p1 then
      if inc then Bevent p1 (outgoing ev1) :: evs'
      else Bevent p1 (e :: outgoing ev1) :: evs' else
    if Qlt_bool (p_x p) (p_x p1) then
      if inc then
        Bevent p nil :: evs else
        Bevent p (e :: nil) :: evs
    else if Qeq_bool (p_x p) (p_x p1) && Qlt_bool (p_y p) (p_y p1) then
       if inc then
         Bevent p nil :: evs else
         Bevent p (e :: nil) :: evs else
    ev1 :: add_event p e inc evs'
  end.

Fixpoint edges_to_events (s : seq edge) : seq event :=
  match s with
  | nil => nil
  | e :: s' =>
    add_event (left_pt e) e false
      (add_event (right_pt e) e true (edges_to_events s'))
  end.

(* this function removes consecutives duplicates, meaning the seq needs
 to be sorted first if we want to remove all duplicates *)
Fixpoint no_dup_seq [A : Type] (eqb : A -> A -> bool) (s : seq A) : (seq A) :=
  match s with
  | nil => nil
  | a::q =>
    match q with
    | nil => s
    | b::r =>
      if eqb a b then no_dup_seq eqb q else a::(no_dup_seq eqb q)
    end
  end.

Definition valid_edge e p := (Qle_bool (p_x (left_pt e)) (p_x p)) &&
(Qle_bool (p_x p) (p_x (right_pt e))).

Definition vertical_intersection_point (p : pt) (e : edge) : option pt :=
  if valid_edge e p then Some(Bpt (p_x p) (((p_x p) - p_x (left_pt e))
   * (((p_y (right_pt e)) - p_y (left_pt e)) /
    ((p_x (right_pt e)) - p_x (left_pt e))) + p_y (left_pt e)))
    else None.

Definition close_cell (p : pt) (c : cell) :=
  match vertical_intersection_point p (low c),
        vertical_intersection_point p (high c) with
  | None, _ | _, None => c
  | Some p1, Some p2 => 
    Bcell (left_pts c) (no_dup_seq pt_eqb (p1 :: p :: p2 :: nil)) (low c) (high c)
  end.

Definition closing_cells (p : pt) (contact_cells: seq cell) : seq cell :=
  List.map (fun c => close_cell p c) contact_cells.

Fixpoint opening_cells_aux (p : pt) (out : seq edge) (low_e high_e : edge) 
  : seq cell * cell :=
      match out with
    | nil => let op0 := vertical_intersection_point p low_e in
              let op1 := vertical_intersection_point p high_e in
                      match (op0,op1) with
                          |(None,_) |(_,None)=> (nil, dummy_cell)
                          |(Some(p0),Some(p1)) =>
                              (nil , 
                              Bcell  (no_dup_seq pt_eqb (p1 :: p :: p0 :: nil)) nil low_e high_e)                      end
    | c::q => let op0 := vertical_intersection_point p low_e in
              let (s, nc) := opening_cells_aux p q c high_e in
                    match op0 with
                       | None => (nil, dummy_cell)
                       | Some(p0) =>
                        (Bcell  (no_dup_seq pt_eqb (p :: p0 :: nil)) nil low_e c :: s,
                         nc)
                    end
end.

Definition pue_formula (p : pt) (a : pt) (b : pt) : Q :=
  let: Bpt p_x p_y := p in
  let: Bpt a_x a_y := a in
  let: Bpt b_x b_y := b in
  ((b_x * p_y - p_x * b_y - (a_x * p_y - p_x * a_y) + a_x * b_y - b_x * a_y))%Q.

Definition point_under_edge (p : pt) (e : edge) : bool :=
  Qle_bool (pue_formula p (left_pt e) (right_pt e)) 0.

Definition point_strictly_under_edge (p : pt) (e : edge) : bool :=
  Qlt_bool (pue_formula p (left_pt e) (right_pt e)) 0.

Definition edge_below (e1 : edge) (e2 : edge) : bool :=
(point_under_edge (left_pt e1) e2 && 
 point_under_edge (right_pt e1) e2)
|| (negb (point_strictly_under_edge (left_pt e2) e1) && 
   negb (point_strictly_under_edge (right_pt e2) e1)).


Definition opening_cells (p : pt) (out : seq edge) (l h : edge) : seq cell :=
   let (s, c) := opening_cells_aux p (path.sort edge_below out) l h in
   seq.rcons s c.

Definition contains_point (p : pt) (c : cell)  : bool :=
   negb (point_strictly_under_edge p (low c)) && point_under_edge p (high c).

Fixpoint open_cells_decomposition_contact open_cells pt :
   option (seq cell * seq cell * cell) :=
match open_cells with
| c :: q => 
  if contains_point pt c then
    match open_cells_decomposition_contact q pt with
    | Some(cc, lc, c') => Some(c :: cc, lc, c')
    | None => Some(nil, q, c)
    end
  else
    None
| nil => None
end.

Fixpoint open_cells_decomposition_rec open_cells pt : 
  seq cell * seq cell * cell * seq cell :=
match open_cells with
| c :: q =>
  if contains_point pt c then
     match open_cells_decomposition_contact q pt with
     | Some(cc, lc, c') => (nil, c :: cc, c', lc)
     | None => (nil, nil, c, q)
     end
  else
    let '(fc, cc, c', lc) := open_cells_decomposition_rec q pt in
    (c :: fc, cc, c', lc)
| nil => (nil, nil, dummy_cell, nil)
end.

Definition open_cells_decomposition (open_cells : seq cell) (p : pt) :
   seq cell * seq cell * cell * seq cell * edge * edge :=
let '(fc, cc, c', lc) := open_cells_decomposition_rec open_cells p in
(fc, cc, c', lc, low (seq.head c' cc), high c').

Record scan_state :=
  Bscan {sc_open1 : seq cell;
         lst_open : cell;
         sc_open2 : seq cell;
         sc_closed : seq cell;
         lst_closed : cell;
         lst_high : edge;
         lst_x : Q}.

Definition update_closed_cell (c : cell) (p : pt) : cell :=
  let ptseq := right_pts c in
  let newptseq :=
    (seq.belast  (seq.head dummy_pt ptseq) (seq.behead ptseq)) ++
    (p :: seq.last dummy_pt ptseq :: nil) in
  Bcell (left_pts c) newptseq (low c) (high c).

Definition update_open_cell (c : cell) (e : event) : seq cell * cell :=
  match outgoing e with
  | nil =>
     let ptseq := left_pts c in
     let newptseq :=
       (seq.head dummy_pt ptseq :: point e :: seq.behead ptseq) in
     (nil, Bcell newptseq (right_pts c) (low c) (high c))
  | _ =>
    opening_cells_aux (point e) (path.sort edge_below (outgoing e))
        (low c) (high c)
  end.

Definition pvert_y (p : pt) (e : edge) :=
  match vertical_intersection_point p e with
    Some p' => p_y p'
  | None => 0
  end.

Definition update_open_cell_top (c : cell) (new_high : edge) (e : event) :=
  match outgoing e with
  | nil =>
    let newptseq :=
      (Bpt (p_x (point e)) (pvert_y (point e) new_high) ::
          left_pts c) in
      (nil, Bcell newptseq (right_pts c) (low c) new_high)
  | _ => 
    opening_cells_aux (point e) (path.sort edge_below (outgoing e))
        (low c) new_high
  end.

Definition step (e : event) (st : scan_state) : scan_state :=
   let p := point e in
   let '(Bscan op1 lsto op2 cls cl lhigh lx) := st in
   if negb (Qeq_bool (p_x p) lx) then
     let '(first_cells, contact_cells, last_contact, last_cells, 
           lower_edge, higher_edge) :=
       open_cells_decomposition (op1 ++ lsto :: op2) p in
     let closed := closing_cells p contact_cells in
     let last_closed := close_cell p last_contact in
     let closed_cells := cls ++ cl :: closed in
     let (new_open_cells, newlastopen) :=
       opening_cells_aux p (path.sort edge_below (outgoing e))
            lower_edge higher_edge in
     Bscan (first_cells ++ new_open_cells)
           newlastopen last_cells closed_cells 
           last_closed  higher_edge (p_x (point e))
   else if negb (point_under_edge p lhigh) then
     let '(fc', contact_cells, last_contact, last_cells,
           low_edge, higher_edge) :=
       open_cells_decomposition op2 p in
     let first_cells := op1 ++ lsto :: fc' in
(* TODO code duplication (6 lines above) *)
     let closed := closing_cells p contact_cells in
     let last_closed := close_cell p last_contact in
     let closed_cells := cls++closed in
     let (new_open_cells, newlastopen) :=
       opening_cells_aux p (path.sort edge_below (outgoing e))
            low_edge higher_edge in
     Bscan (first_cells ++ new_open_cells)
           newlastopen last_cells closed_cells last_closed
            higher_edge (p_x (point e))
   else if point_strictly_under_edge p lhigh then 
     let new_closed := update_closed_cell cl (point e) in
     let (new_opens, new_lopen) := update_open_cell lsto e in
     Bscan (op1 ++ new_opens) new_lopen op2 cls new_closed lhigh lx
   else (* here p === lhigh *)
     let '(fc', contact_cells, last_contact, last_cells, lower_edge,
                higher_edge) :=
       open_cells_decomposition (lsto :: op2) p in
     (* we know lsto was just open, so that its left limit is lx
        and its right limit is bounded by p_x (right_pt lhigh), which
        is necessarily p_x (point e). lsto is necessarily the
        first cell of contact_cells.  So the first element of
        contact_cells should not be closed. It can just be
        disregarded. *)
     let closed := closing_cells p (seq.behead contact_cells) in
     let last_closed := close_cell p last_contact in
     let (new_opens, new_lopen) :=
        update_open_cell_top lsto higher_edge e in
        Bscan (op1 ++ fc' ++ new_opens) new_lopen last_cells
          (cls ++ cl :: closed) last_closed higher_edge lx.

Definition leftmost_points (bottom top : edge) :=
  if Qlt_bool (p_x (left_pt bottom)) (p_x (left_pt top)) then
    match vertical_intersection_point (left_pt top) bottom with
    | Some pt => left_pt top :: pt :: nil
    | None => nil
    end
  else
    match vertical_intersection_point (left_pt bottom) top with
    | Some pt => pt :: left_pt bottom :: nil
    | _ => nil
    end.

Definition rightmost_points (bottom top : edge) :=
  if Qlt_bool (p_x (right_pt bottom)) (p_x (right_pt top)) then
    match vertical_intersection_point (right_pt bottom) top with
    | Some pt => right_pt bottom :: pt :: nil
    | _ => nil
    end
  else
    match vertical_intersection_point (right_pt top) bottom with
    | Some pt => pt :: right_pt top :: nil
    | _ => nil
    end.

Definition complete_last_open (bottom top : edge) (c : cell) :=
  match c with
  | Bcell lpts rpts le he =>
      Bcell lpts (rightmost_points bottom top) le he
  end.

Definition start_open_cell (bottom top : edge) :=
  Bcell (leftmost_points bottom top) nil bottom top.

Definition start (first_event : event) (bottom : edge) (top : edge) :
  scan_state :=
  let (newcells, lastopen) :=
  opening_cells_aux (point first_event)
      (path.sort edge_below (outgoing first_event)) bottom top in
      (Bscan newcells lastopen nil nil
         (close_cell (point first_event) (start_open_cell bottom top))
         top (p_x (point first_event))).

(* A manner of folding a function over list in a tail recursive way.
  TODO : figure out if this is already covered by an existing list
  generic function. *)
Fixpoint iter_list [A B : Type] (f : A -> B -> B) (s : seq A) (init : B) :=
  match s with
  | nil => init
  | a :: tl => iter_list f tl (f a init)
  end.

Definition scan (events : seq event) (bottom top : edge) : seq cell :=
  match events with
  | nil => (complete_last_open bottom top (start_open_cell bottom top) :: nil)
  | ev0 :: events =>
    let start_scan := start ev0 bottom top in
    let final_scan := iter_list step events start_scan in
      lst_closed final_scan :: map (complete_last_open bottom top)
      (lst_open final_scan :: sc_open1 final_scan ++ sc_open2 final_scan) ++
      sc_closed final_scan
  end.

(* This is the main function of vertical cell decomposition. *)
Definition edges_to_cells bottom top edges :=
  scan (edges_to_events edges) bottom top.

(* SECOND PART : computing a path in the cell graph *)
(* This code is taken from github.com/ybertot/breadth_first_search.
   the proof of this code is probably complete in that repository. *)

Section bfs.

Variable (state move : Type).
Variable (state_fmap : Type).
Variable find : state_fmap -> state -> option move.
Variable add : state_fmap -> state -> move -> state_fmap.
Variable (step : state -> list (state * move)).
Variable (state_eq_dec : forall s1 s2 : state, {s1 = s2}+{s1 <> s2}).

Variable map_order : state_fmap -> state_fmap -> Prop.
Hypothesis map_order_wf : well_founded map_order.
Hypothesis add_order : forall map s v,
  find map s = None -> map_order (add map s v) map.
Hypothesis map_order_trans : forall map2 map1 map3,
  map_order map1 map2 -> map_order map2 map3 -> map_order map1 map3.

Fixpoint bfs_aux (w w2 : list (state * move))
  (sufficient : state)
  (settled : state_fmap) : (list (state * move) * state_fmap) :=
match w with
| (s, m) :: w' =>
  match find settled s with
  | Some _ => bfs_aux w' w2 sufficient settled
  | None =>
    if state_eq_dec s sufficient then
      (nil, add settled s m)
    else
    bfs_aux w' (step s ++ w2) sufficient (add settled s m)
  end
| nil => (w2, settled)
end.

Fixpoint bfs (fuel : nat) (w : list (state * move)) (settled : state_fmap) 
  (sufficient : state)
  (round : nat) :
  (state_fmap * nat) + (list (state * move) * state_fmap) :=
  match fuel with
  | O => inr (w, settled)
  | S p =>
    match bfs_aux w nil sufficient settled with
    | (nil, s) => inl (s, round)
    | (w, s) => bfs p w s sufficient (round + 1)
    end
  end.

  (* We then explain how we build a path using the database. *)
Fixpoint make_path (db : state_fmap)
(targetb : state -> bool) (play : state -> move -> option state)
(x : state) (fuel : nat) :=
match fuel with
| O => None
| S p =>
if targetb x then
  Some nil
else
  match find db x with
  | None => None
  | Some m =>
    match play x m with
    | Some y =>
      match make_path db targetb play y p with
      | None => None
      | Some l => Some (m :: l)
      end
   | None => None
   end
  end
end.

End bfs.

(* defining the connection relation between adjacent cells.  Two cells
  are adjacent when it is possible to move from one cell directly to the
  other with colliding an obstacle edge.  In the data structure, it means
  that they share a vertical edge. *)
Record vert_edge :=
 { ve_x : Q; ve_top : Q; ve_bot : Q}.

Definition vert_edge_eqb (v1 v2 : vert_edge) :=
  let: Build_vert_edge v1x v1t v1b := v1 in
  let: Build_vert_edge v2x v2t v2b := v2 in
  Qeq_bool v1x v2x && Qeq_bool v1t v2t && 
  Qeq_bool v1b v2b.

Fixpoint seq_to_intervals_aux [A : Type] (a : A) (s : seq A) :=
match s with
| nil => nil
| b :: tl => (a, b) :: seq_to_intervals_aux b tl
end.

Definition seq_to_intervals [A : Type] (s : seq A) :=
match s with
  nil => nil
| a :: tl => seq_to_intervals_aux a tl
end.

(* Vertical edges are collected from the left_pts and right_pts sequences. *)
Definition cell_safe_exits_left (c : cell) : seq vert_edge :=
  let lx := p_x (seq.head dummy_pt (left_pts c)) in
  map (fun p => Build_vert_edge lx (p_y (fst p)) (p_y (snd p))) 
   (seq_to_intervals (left_pts c)).

Definition cell_safe_exits_right (c : cell) : seq vert_edge :=
  let lx := p_x (seq.head dummy_pt (right_pts c)) in
  map (fun p => Build_vert_edge lx (p_y (fst p)) (p_y (snd p))) 
   (seq_to_intervals (rev (right_pts c))).

Definition vert_edge_midpoint (ve : vert_edge) : pt :=
  {|p_x := ve_x ve; p_y := (ve_top ve + ve_bot ve) / 2|}.

(* connection from left to right is obtained by computing an intersection. *)
Definition lr_connected (c1 c2 : cell) : bool :=
  existsb (fun v => existsb (fun v' => vert_edge_eqb v v')
                       (cell_safe_exits_left c2))
       (cell_safe_exits_right c1).

Definition bi_connected c1 c2 :=
  lr_connected c1 c2 || lr_connected c2 c1.

Definition dummy_vert_edge :=
  {| ve_x := 0; ve_top := 0; ve_bot := 0|}.

Module natmap := FMapAVL.Make Nat_as_OT.

Definition bfs_find : natmap.t nat -> nat -> option nat :=
  (fun m k => natmap.find k m).

Definition bfs_add : natmap.t nat -> nat -> nat -> natmap.t nat :=
  (fun m k v => natmap.add k v m).

Definition reverse_step cells cell_i : seq (nat * nat) :=
  map (fun i => (i, cell_i))
    (filter (fun c_i => bi_connected (nth c_i cells dummy_cell)
                       (nth cell_i cells dummy_cell))
     (seq.iota 0 (List.length cells))).

(* To compute a path between two cells we use as input the list of cells
   and indices of two cells in this list (source and target).  This builds
   a table.  This table construction is interrupted as soon as a path
   from source_i to target_i is found, and this path is guaranteed to be
   of minimal length in terms of numbers of cells encountered. The result
   is in a sum type, where only the right variant would mean that no path
   has been found before exhaustion of some fuel.  But here, it is assumed
   that the fuel (length of cells) is going to be enough to find all cells
   connected to target_i. *)
Definition cell_connection_table (cells : seq cell) (source_i target_i : nat) :=
    bfs _ _ _ bfs_find bfs_add (reverse_step cells) eq_nat_dec
    (List.length cells) ((target_i, target_i) :: nil) (natmap.empty nat)
    source_i 0.

Definition cell_path (cells : seq cell) (source_i target_i : nat) :
  option (seq nat) :=
  match cell_connection_table cells source_i target_i with
  | inr _ => None
  | inl (table, _) =>
    make_path _ _ _ bfs_find table (fun c_i => Nat.eqb c_i target_i)
      (fun n1 n2 => Some n2) source_i (List.length cells)
  end.

(* Given two cells, we define the door from one cell to the other to
  be the common edge between these cells.  In example known so far, there
  is only one such door, but this may change in the future.  For now, we
  take arbitrarily the first one we find (the top one or the bottom one
  depending on the exits are ordered).  If the two cells are not adjacent,
  dummy_vert_edge is returned.  Maybe this should be made safer by returning
  an option type. *)
Definition lr_door (c1 c2 : cell) :=
  seq.head dummy_vert_edge
     (filter (fun x => existsb (fun x' => vert_edge_eqb x x')
                  (cell_safe_exits_left c2)) (cell_safe_exits_right c1)).

Definition midpoint (p1 p2 : pt) : pt :=
 {| p_x := (p_x p1 + p_x p2) / 2; p_y := (p_y p1 + p_y p2) / 2|}.

Definition cell_center (c : cell) :=
  midpoint
    (midpoint (seq.last dummy_pt (left_pts c)) 
              (seq.head dummy_pt (right_pts c)))
    (midpoint (seq.head dummy_pt (left_pts c))
              (seq.last dummy_pt (right_pts c))).

Record annotated_point :=
  Apt { apt_val : pt; cell_indices : seq nat}.

(* Given a sequence of cells c_i, and a sequence of indices i1, i2, ... 
   (where the ... are refered to as tl), we want to create a list of
   points, making it possible to move from door to door so that the all
   all list of points is describes a broken line moving from the door
   between i1 and i2 to the door between the last two elements of
   (i1, i2, & tl).  Adding paths to the first and last doors will make it
   easy to have a path from any point in cell i1 to any point in the last
   cell of (i1, i2, & tl). *)
Fixpoint connected_cells_path (cells : seq cell)
  (i1 i2 : nat) (tl : seq nat) :
  seq (annotated_point * annotated_point) :=
  match tl with
  | nil => nil
  | i3 :: tl' =>
    let tail_path := connected_cells_path cells i2 i3 tl' in
    let c1 := nth i1 cells dummy_cell in
    let c2 := nth i2 cells dummy_cell in
    let c3 := nth i3 cells dummy_cell in
    if lr_connected c1 c2 && lr_connected c2 c3 then
       (Apt (vert_edge_midpoint (lr_door c1 c2)) (i1 :: i2 :: nil),
           Apt (vert_edge_midpoint (lr_door c2 c3)) (i2 :: i3 :: nil)) ::
       tail_path else
    if lr_connected c3 c2 && lr_connected c2 c1 then
       (Apt (vert_edge_midpoint (lr_door c2 c1)) (i1 :: i2 :: nil),
           Apt (vert_edge_midpoint (lr_door c3 c2))
                    (i2 :: i3 :: nil)) ::
       tail_path else
    if lr_connected c1 c2 (* we assume lr_connected c3 c2 *) then
       (Apt (vert_edge_midpoint (lr_door c1 c2))
            (i1 :: i2 :: nil),
          Apt (cell_center c2) (i2 :: nil)) ::
           (Apt (cell_center c2) (i2 :: nil), 
            Apt (vert_edge_midpoint (lr_door c3 c2))
                (i2 :: i3 :: nil)) ::
           tail_path else
    (Apt (vert_edge_midpoint (lr_door c2 c1)) (i1 :: i2 :: nil), 
     Apt (cell_center c2) (i2 :: nil)) ::
        (Apt (cell_center c2) (i2 :: nil),
         Apt (vert_edge_midpoint (lr_door c2 c3))
           (i2 :: i3 :: nil)) ::
        tail_path
  end.

Definition left_limit (c : cell) := p_x (seq.last dummy_pt (left_pts c)).

Definition right_limit c := p_x (seq.last dummy_pt (right_pts c)).

(* This function is like lr_door, but it is more precise, as it 
  returns None in case the two given cells are not adjacent. *)
Definition common_vert_edge (c1 c2 : cell) : option vert_edge:=
  if Qeq_bool (right_limit c1) (left_limit c2) then
    find (fun v => existsb (fun v' => vert_edge_eqb v v')
                      (cell_safe_exits_left c2))
      (cell_safe_exits_right c1)
  else
    find (fun v => existsb (fun v' => vert_edge_eqb v v')
                      (cell_safe_exits_left c1))
      (cell_safe_exits_right c2).

(* This function computes a path (broken line) between a point
  in a cell and a point in another cell, going through the midpoint of
  the door between the two cells.  the points are annotated with the
  constraint they have to satisfied: the cells of which they have to
  be members of. This annotation is important because smoothing will
  replace these points with other points that have to satisfy the same
  constraint. *)
Definition path_adjacent_cells (cells : seq cell) (source target : pt)
  (source_i target_i : nat) : option (seq (annotated_point * annotated_point)) :=
  let source_cell := nth source_i cells dummy_cell in
  let target_cell := nth target_i cells dummy_cell in
  match common_vert_edge source_cell target_cell with
  | Some v => 
    Some ((Apt source (source_i :: nil), 
           Apt (vert_edge_midpoint v) (source_i :: target_i :: nil)) ::
              (Apt (vert_edge_midpoint v) (source_i :: target_i :: nil),
               Apt target (target_i :: nil)) :: nil)
  | None => None
  end.

Definition strict_inside_closed p c :=
  negb (point_under_edge p (low c)) &&
  point_strictly_under_edge p (high c) &&
 (Qlt_bool (left_limit c) (p_x p) &&
 (Qlt_bool (p_x p) (right_limit c))).

Definition point_to_point (bottom top : edge)
 (cells : seq cell) (source target : pt) :
  option (seq (annotated_point * annotated_point)) :=
let source_i := find 
        (fun i => strict_inside_closed source (nth i cells dummy_cell))
        (seq.iota 0 (List.length cells)) in
let target_i := find 
        (fun i => strict_inside_closed target (nth i cells dummy_cell))
        (seq.iota 0 (List.length cells)) in
match source_i, target_i with
| Some source_i, Some target_i =>
  if Nat.eqb source_i target_i then
     Some ((Apt source (source_i :: nil), 
           Apt target (target_i :: nil)) :: nil)
  else
    let cp := cell_path cells source_i target_i in
    match cp with
    | Some cp =>
      if 2 <=? List.length cp then
        let penultimate_cell_i := nth 1 (List.rev cp) 0%nat in
        match common_vert_edge 
               (nth penultimate_cell_i cells dummy_cell)
               (nth target_i cells dummy_cell),
             common_vert_edge
               (nth source_i cells dummy_cell)
               (nth (seq.head 0%nat cp) cells dummy_cell) with
        | Some last_door, Some first_door =>
          Some ((Apt source (source_i :: nil), 
                  (Apt (vert_edge_midpoint first_door)
                       (source_i :: seq.head 0%nat cp :: nil))) ::
                  connected_cells_path cells source_i (seq.head 0%nat cp)
                    (seq.behead cp) ++
                      (Apt (vert_edge_midpoint last_door)
                           (penultimate_cell_i :: target_i :: nil),
                       Apt target (target_i :: nil)) :: nil)
        | _, _ => None
        end
      else
        path_adjacent_cells cells source target source_i target_i
    | None => None
    end
| _, _ => None
end.

(* THIRD PART: Producing a smooth trajectory. *)
(* We produce a smooth trajectory by replacing every angle by a Bezier curve.
   We first add anchor points in the middle of each straight line segment.
   These anchor points only have the constraints to be in a single cell and
   the curve will pass through these anchor points no matter what
   transformation will happen later.  Then broken line paths between
   anchor points are replaced by Bezier curves, thus keeping the invariant
   that the new smooth path connects the anchor points correctly.  *)

Definition intersection (s1 s2 : seq nat) :=
  filter (fun e => existsb (fun e' => Nat.eqb e e')
                      s2) s1.

(* The point of this function is to add anchor points in the middle
  of each segment.  The annotation for these anchor points is the
  cell in which they appear, but this information is not going to play
  a significant role in the current version of the program. *)
Fixpoint break_segments (s : seq (annotated_point * annotated_point)) :
  seq (annotated_point * annotated_point) :=
  match s with
  | (Apt p1 a1, Apt p2 a2) :: tl =>
    (Apt p1 a1, Apt (midpoint p1 p2) (intersection a1 a2)) ::
    (Apt (midpoint p1 p2) (intersection a1 a2), Apt p2 a2) ::
        break_segments tl
  | nil => nil
  end. 

(* The connection at anchor points is straight (because it comes
   from a straight line segment.  The connection between two anchor points
   is a broken line (an angle).  The idea is to replace this broken line
   by a bezier curve, which by construction will be tangent with the
   initial segment.  However, there may be cases where this Bezier curve does
   not pass through the authorized door. *)
Variant curve_element :=
 straight (x y : annotated_point) | bezier (x y z : annotated_point).

(* This function assumes that every other straight line segment goes into
  an angle, and the other go into a straight connection.  The angles
  (represented by adjacent pairs) are then replace by Bezier curves. 
  the last element is left as is. *)
(* The input of this function is guaranteed to have b = b' in the second
  pattern matching rule below. *)
Fixpoint smoothen_aux (s : seq (annotated_point * annotated_point)) :
   seq curve_element :=
match s with
| nil => nil
| (a, b) :: nil => straight a b :: nil
| (a, b) :: (b', c) :: tl => bezier a b c :: smoothen_aux tl
end.

(* Here we move from a sequence of straight line segments given by pairs
  of points with anchor points to a sequence of curve elements.
  Actually only the first one and the last one are straight, all the rest
  are Bezier curve elements. *)
Definition smoothen (s : seq (annotated_point * annotated_point)) :
   seq curve_element :=
match s with
| (a, b)  :: tl => straight a b :: smoothen_aux tl
| nil => nil
end.

(* The curve produced by smoothen only guarantees to be a continuous
   path from the initial point to the last point going through the anchor
   points, but now we have lost the guarantee that this path goes through
   the doors. The next functions detect collisions and repair the curve. *)

(* We now have two functions to check whether a Bezier curve does pass
  through the door.  They implement specialized code and require fuel to
  operate. the result is an optional boolean.  When the boolean is given
  and true, we are sure the curve passes through the door, when the
  boolean is given and false, we are sure the curve hits an obstacle,
  when the boolean is not given (answer is None), we don't know, but
  for this algorithm, this is interpreted as a failure to pass through the
  door.  In practice, the fuel does not need to be big, because curve size
  is divided by 2 at each iteration.

  This function is to be used when p_x a < p_x b < p_x c and
  a b c is ccw (counter clockwise). It assumes that there is no need to
 check the bottom point. *)
Fixpoint check_bezier_ccw (fuel : nat) (v : vert_edge)
  (a b c : pt) : 
  option bool :=
match fuel with
| O => None
| S p =>
  let top_edge := Bpt (ve_x v)  (ve_top v) in
  if negb (point_under_edge top_edge (Bedge a c)) then
    Some true
  else if
     point_under_edge top_edge (Bedge a b) ||
     point_under_edge top_edge (Bedge b c)
  then 
    Some false
  else
    let b' := midpoint a b in
    let b2 := midpoint b c in
    let c' := midpoint b' b2 in
    if Qlt_bool (p_x c') (ve_x v) then
      check_bezier_ccw p v c' b2 c
    else if Qlt_bool (ve_x v) (p_x c') then
      check_bezier_ccw p v a b' c'
    else
      if Qlt_bool (p_y c') (ve_top v) then
         Some true
      else
         Some false
end.

(* This function is to be used when p_x a < p_x b < p_x c and
  a b c is cw (clockwise).
  It assumes that there is no need to check the top point. *)
Fixpoint check_bezier_cw (fuel : nat) (v : vert_edge)
  (a b c : pt) : 
  option bool :=
match fuel with
| O => None
| S p =>
  let bot_edge := Bpt (ve_x v)  (ve_bot v) in
  if point_strictly_under_edge bot_edge (Bedge a c) then
    Some true
  else if
     negb (point_strictly_under_edge bot_edge (Bedge a b)) ||
     negb (point_strictly_under_edge bot_edge (Bedge b c))
  then 
    Some false
  else
    let b' := midpoint a b in
    let b2 := midpoint b c in
    let c' := midpoint b' b2 in
    if Qlt_bool (p_x c') (ve_x v) then
      check_bezier_cw p v c' b2 c
    else if Qlt_bool (ve_x v) (p_x c') then
      check_bezier_cw p v a b' c'
    else
      if Qlt_bool (ve_bot v) (p_y c') then
         Some true
      else
         Some false
end.

(* This function verifies that the Bezier curve does pass through the
  door that was initially given has a constraint for the broken line.  This
  is done by performing a dichotomy on the Bezier curve until we either 
  see explicitely that the condition is met or that the condition is
  violated.  When the condition is violated, a new Bezier curve is proposed
  and by creating two new anchor points half way between the previous
  anchor points and the chosen point (normally the middle of the door) and
  verification starts again with the new Bezier curve, which is closer to
  the broken line trajectory.
  This function should normally be based on well-founded recursion, but
  for executability we rely on a fuel, which does not need to be enormous
  because the size of the bezier curve element is divided by 2 at each
  iteration.
  This function may replace a faulty curve element with a sequence of
  three new elements, so all results have to be concatened later. *)
Fixpoint check_curve_element_and_repair
  (fuel : nat) (cells : seq cell) (e : curve_element) :
   seq curve_element :=
match e with
| straight p1 p2 => straight p1 p2 :: nil
| bezier p1 p2 p3 =>
  if Nat.eqb (List.length (cell_indices p2)) 2 then
    let i1 := nth 0 (cell_indices p2) 0%nat in
    let i2 := nth 1 (cell_indices p2) 0%nat in
    let vedge := match common_vert_edge 
         (nth i1 cells dummy_cell) (nth i2 cells dummy_cell) with
      Some v => v
      | None => dummy_vert_edge
      end in
    let e' :=
      (if Qlt_bool (p_x (apt_val p1)) (p_x (apt_val p2)) then
        bezier p1 p2 p3
      else
        bezier p3 p2 p1) in
    match e' with
    |straight _ _ => e' :: nil
    | bezier p1' p2' p3' =>
      let check_function :=
      if Qlt_bool 0 
          (pue_formula (apt_val p1') (apt_val p2') (apt_val p3')) then
          check_bezier_ccw
      else
          check_bezier_cw in
        match check_function 20%nat vedge
                  (apt_val p1')(apt_val p2')(apt_val p3') with
        | Some true => bezier p1 p2 p3 :: nil
        | _ => 
          match fuel with
          | S p =>
            straight p1 
               (Apt (midpoint (apt_val p1) (apt_val p2)) (cell_indices p1))
              ::
              check_curve_element_and_repair p cells
                (bezier (Apt (midpoint (apt_val p1) (apt_val p2))
                       (cell_indices p1))
                 p2
                 (Apt (midpoint (apt_val p2) (apt_val p3)) (cell_indices p3)))
              ++
              straight (Apt (midpoint (apt_val p2) (apt_val p3))
                    (cell_indices p3)) p3 :: nil
          | _ =>
            straight p1 p2 :: straight p2 p3 :: nil
          end
        end
    end
  else
    (bezier p1 p2 p3 :: nil)
end.

Definition smooth_from_cells (bottom top : edge) (cells : seq cell) 
  (initial final : pt) : seq curve_element :=
  match point_to_point bottom top cells initial final with
  | Some s => List.concat (List.map (check_curve_element_and_repair 20 cells)
                              (smoothen (break_segments s)))
  | None => nil
  end.

(* This function wraps up all operations:
  - constructing the cells
  - constructing the broken line
  - constructing the smooth line
  - repairing the faulty bezier elements. *)
Definition smooth_point_to_point (bottom top : edge) (obstacles : seq edge)
  (initial final : pt) : seq curve_element :=
  let cells := edges_to_cells bottom top obstacles in
  smooth_from_cells bottom top cells initial final.

(* FOURTH PART: Displaying results. *)
(* TODO : this should probably be moved elsewhere. *)
(* This part is about producing postscript text to display examples. *)

Fixpoint positive_Z_to_decimal_string (fuel : nat) (z : Z) :=
  match fuel with
  | O => ""%string
  | S p =>
    if (z =? 0)%Z then
       ""%string
    else
    let (q, r) := Z.div_eucl z 10 in
    append (positive_Z_to_decimal_string p q) 
    match r with
    | 0%Z => "0"%string
    | 1%Z => "1"%string
    | 2%Z => "2"%string
    | 3%Z => "3"%string
    | 4%Z => "4"%string
    | 5%Z => "5"%string
    | 6%Z => "6"%string
    | 7%Z => "7"%string
    | 8%Z => "8"%string
    | _%Z => "9"%string
    end
  end.

Definition Z_to_string (z : Z) :=
  if (z =? 0)%Z then
    "0"%string
  else if (z <? 0)%Z then
    append "-" 
       (positive_Z_to_decimal_string (S (Z.abs_nat (Z.log2_up (- z)))) (- z))
  else 
    (positive_Z_to_decimal_string (S (Z.abs_nat (Z.log2_up z))) z).

Definition positive_rational_to_approx_decimal_string (x : Q) : string :=
    let frac_part := 
        (((1000 * Qnum x) / Zpos (Qden x)) mod 1000)%Z in
    let frac_part_string := 
      if (frac_part =? 0)%Z then
         "000"%string
      else if (frac_part <? 10)%Z then
        append "00" (Z_to_string frac_part)
      else if (frac_part <? 100)%Z then
        append "0" (Z_to_string frac_part)
      else 
        (Z_to_string frac_part) in
     append (Z_to_string (Qnum x / Z.pos (Qden x))) 
         (append "." frac_part_string).

Definition Q_to_approx_decimal_string (x : Q) :=
  if Qeq_bool x 0 then
    "0.000"%string
  else if Qle_bool 0 x then
    positive_rational_to_approx_decimal_string x
  else
    append "-" (positive_rational_to_approx_decimal_string (-x)).

Definition display_point (tr_x tr_y scale : Q) (p : pt) :=
  let process_coord tr scale v :=
    Q_to_approx_decimal_string (tr + scale * v) in
    append (process_coord tr_x scale (p_x p))
       (append " " (process_coord tr_y scale (p_y p))).

Definition display_edge (tr_x tr_y scale : Q) (e : edge) :=
  append (display_point tr_x tr_y scale (left_pt e))
    (append " moveto
" (append (display_point tr_x tr_y scale (right_pt e)) " lineto
")).

Definition display_segment (tr_x tr_y scale : Q) (s : pt * pt) :=
  display_edge tr_x tr_y scale (Bedge (fst s) (snd s)).

Definition weighted_sum (p1 p2 : pt) (weight1 : Q) :=
  Bpt (p_x p1 * weight1 + p_x p2 * (1 - weight1))
    (p_y p1 * weight1 + p_y p2 * (1 - weight1)).

(* The Bezer elements are quadratic elements, but postscript implements
  cubic Bezier curves, so some extra computation needs to be done.
  The mathematical elements were found on stackoverflow. *)

Definition display_curve_element (tr_x tr_y scale : Q) (e : curve_element) :=
match e with
| straight p1 p2 => display_segment tr_x tr_y scale (apt_val p1, apt_val p2)
| bezier p1 p2 p3 =>
  append (display_point tr_x tr_y scale (apt_val p1))
    (append " moveto "
      (append (display_point tr_x tr_y scale 
           (weighted_sum (apt_val p1) (apt_val p2) (1/3)))
         (append " "
           (append (display_point tr_x tr_y scale
                     (weighted_sum (apt_val p3) (apt_val p2) (1/3)))
             (append " "
                (append (display_point tr_x tr_y scale (apt_val p3))
             " curveto
"))))))
end.

Definition display_cell (tr_x tr_y scale : Q) (c : cell) :=
  display_edge tr_x tr_y scale
      {| left_pt := seq.head dummy_pt (left_pts c);
                  right_pt := seq.last dummy_pt (left_pts c) |}.

Definition display_cell_centers (tr_x tr_y scale : Q) (s : seq cell) :=
  let indices := seq.iota 0 (List.length s) in
  map (fun i =>
         append "newpath "
         (append (display_point tr_x tr_y scale 
                      (cell_center (nth i s dummy_cell)))
          (append " moveto ("
            (append (Z_to_string (Z.of_nat i))
               ") show")))) indices.

Definition postscript_header :=
("" ::
"START"  ::
"%!PS" ::
"/Times-Roman findfont" ::
"12 scalefont" ::
"setfont" :: nil)%string.

Definition postscript_end_of_file := "END"%string :: nil.

Definition display_obstacles_and_cells (tr_x tr_y scale : Q)
  (bottom top : edge)
  (obstacles : seq edge) (cells : seq cell) : seq string :=
(List.map (display_edge tr_x tr_y scale)
  (bottom :: top :: obstacles) ++
"stroke"%string ::
display_cell_centers tr_x tr_y scale cells ++
"stroke gsave [1 3] 0 setdash"%string ::
List.map
  (fun c : cell => display_cell 300 400 70 c)
  cells ++
"
stroke grestore
"%string :: nil).

Definition display_smooth_trajectory (tr_x tr_y scale : Q)
   (s : seq curve_element) :=
(List.map (display_curve_element tr_x tr_y scale) s ++
"stroke"%string :: nil).

Definition display_full_example tr_x tr_y scale
  bottom top obstacles source target extra :=
let cells := edges_to_cells bottom top obstacles in
  String.concat "
"
(postscript_header ++
 display_obstacles_and_cells tr_x tr_y scale bottom top obstacles cells ++
 display_smooth_trajectory tr_x tr_y scale
   (smooth_from_cells bottom top cells source target) ++
extra ++
postscript_end_of_file).

(* FIFTH PART : testing preconditions *)
(* As explained in the introduction, edges have to satisfy some properties,
   part of which are easy to check in linear time.  We provide a few
   functions for these checks. *)

Definition edge_cond (edges : seq edge) :=
  forallb (fun e => Qlt_bool (p_x (left_pt e)) (p_x (right_pt e))) edges.

Definition inside_box (p : pt) (bottom top : edge) :=
  negb (point_under_edge p bottom) &&
  point_strictly_under_edge p top &&
  (Qlt_bool (p_x (left_pt bottom)) (p_x p) &&
     Qlt_bool (p_x p) (p_x (right_pt bottom))) &&
  (Qlt_bool (p_x (left_pt top)) (p_x p) &&
     Qlt_bool (p_x p) (p_x (right_pt top))).

(*******  starting work on an example ******************)

Definition example_edge_list : seq edge :=
  Bedge (Bpt (-3) 0) (Bpt (-2) 1) ::
  Bedge (Bpt (-3) 0) (Bpt 0 (-3)) ::
  Bedge (Bpt 0 (-3)) (Bpt 1 (-2)) ::
  Bedge (Bpt 1 (-2)) (Bpt 3 (-1)) ::
  Bedge (Bpt 0 (3/2)) (Bpt 3 (-1)) ::
  Bedge (Bpt (-2) 1) (Bpt 0 1) ::
  Bedge (Bpt 0 1) (Bpt 1 0) ::
  Bedge (Bpt (-1) 0) (Bpt 0 (-1)) ::
  Bedge (Bpt 0 (-1)) (Bpt 1 0) :: nil.
(*
  Bedge (Bpt (-2) (-1)) (Bpt 2 1) ::
  Bedge (Bpt (4 # 5) (-1 # 5)) (Bpt 2 1) ::
  Bedge (Bpt (4 # 5) (-1 # 5)) (Bpt (17 # 5) (-5 / 2)) ::
  Bedge  (Bpt (-2) (-1)) (Bpt (17 # 5) (-5 / 2)) :: nil. *)


Lemma example_edge_cond : edge_cond example_edge_list = true.
Proof. easy. Qed.

Notation BOTTOM :=
  ({| left_pt := {| p_x := -4; p_y := -4|};
      right_pt := {| p_x := 4; p_y := -4|}|}).

Notation TOP :=
  ({| left_pt := {| p_x := -4; p_y := 2|};
      right_pt := {| p_x := 4; p_y := 2|}|}).

Definition example_bottom : edge := BOTTOM.

Definition example_top : edge := TOP.

Lemma example_inside_box :
  forallb (fun e => inside_box (point e) example_bottom example_top)
     (edges_to_events example_edge_list) = true.
Proof. easy. Qed.

Definition example_start_event :=
  seq.head dummy_event (edges_to_events example_edge_list).

Definition example_test (p1 p2 : pt) (extra : seq string) :=
  display_full_example 300 400 70 example_bottom example_top
    example_edge_list p1 p2 extra.

(* To display a more elaborate example that shows in a curved dash line
  the result of smoothening the trajectory without repaing, you can
  execute the following text.
Compute 
  let p1 := Bpt (-19/10) (-3/2) in
  let p2 := Bpt (3/2) (0) in
  let cells := edges_to_cells example_bottom example_top example_edge_list in
  match point_to_point example_bottom example_top cells
          p1 p2 with
    Some s => 
      let bad_smooth := smoothen (break_segments s) in
      example_test p1 p2
         ("[2 4] 0 setdash"%string ::
List.map (display_curve_element 300 400 70) bad_smooth ++
          "stroke"%string :: nil)
    | None => ""%string
    end.
*)

(* To display the result of smoothening with repair, you can run the following
  command. *)
Compute 
  let p1 := Bpt (-19/10) (-3/2) in
  let p2 := Bpt (1/3) (0) in
  example_test p1 p2 nil.

Definition example_cells := edges_to_cells example_bottom example_top
     example_edge_list.

Compute nth 5 example_cells dummy_cell.

Compute nth 7 example_cells dummy_cell.

Compute edges_to_events example_edge_list.
