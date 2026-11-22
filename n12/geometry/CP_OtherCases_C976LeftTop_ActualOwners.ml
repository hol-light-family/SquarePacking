(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976LeftTop/ActualOwners.lean       *)
(* (N12Compact.Completion.OtherCases.C976LeftTop.ActualOwners).              *)
(* C976-LEFT-UPPER-POINTS section 4 and the Q8/Q11 application of            *)
(* C976-LEFT-TOP-ANGLE.  The family q : Fin 12 -> OpenSquare is the five     *)
(* coordinate functions qc qs qu qv qa (i < 12); the OpenSquare unit normals *)
(* are the explicit hypothesis !i. i < 12 ==> qc i * qc i + qs i * qs i = &1 *)
(* (0 < side follows from Data.side).  Data is c976ao_data.  pullX / pullY / *)
(* pullSwap = LINSIDE_PULLX / PULLY / PULLSW, translated =                   *)
(* C976AO_INSIDE_TRANSLATED, inside_segment = C976AO_INSIDE_SEGMENT,         *)
(* UpperPoints.Input / points / steep_negative = occ976lt_input /            *)
(* OCC976UP_POINTS / OCC976UP_STEEP_NEGATIVE, TopInput = oltstsu_top,        *)
(* SouthwestSupportPoint.point_of_neighbours = OCSWSPM_POINT_OF_NEIGHBOURS,  *)
(* WallUpperMissingReach.point = WUMR_POINT, WallProfile.boundary_origin =   *)
(* OCWPBO_BOUNDARY_ORIGIN, C981CompletionCornerAdvance.point = C981CA_POINT. *)
(* Tag C976AO_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C976LeftTop_UpperPoints.ml";;
needs "n12/geometry/CP_OtherCases_SouthwestSupportPoint_Main.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_BoundaryOrigin.ml";;
needs "n12/geometry/WallUpperMissingReach.ml";;
needs "n12/geometry/CP_C981_CornerAdvance.ml";;

(* S12 inside_translated_iff *)
let C976AO_INSIDE_TRANSLATED = prove
 (`forall c s u v a x y p q.
      linside c s (u - (c * x + s * y)) (v - (--s * x + c * y)) a p q <=>
      linside c s u v a (x + p) (y + q)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* S12.Convex.inside_segment *)
let C976AO_INSIDE_SEGMENT = prove
 (`forall c s u v a x y x' y' t.
     linside c s u v a x y /\ linside c s u v a x' y' /\ &0 <= t /\ t <= &1
     ==> linside c s u v a ((&1 - t) * x + t * x') ((&1 - t) * y + t * y')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `c * ((&1 - t) * x + t * x') + s * ((&1 - t) * y + t * y') =
      (&1 - t) * (c * x + s * y) + t * (c * x' + s * y') /\
    --s * ((&1 - t) * x + t * x') + c * ((&1 - t) * y + t * y') =
      (&1 - t) * (--s * x + c * y) + t * (--s * x' + c * y')`
  (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  (MATCH_MP_TAC REAL_CONVEX_BOUND_LT ORELSE MATCH_MP_TAC REAL_CONVEX_BOUND_GT) THEN
  ASM_REAL_ARITH_TAC);;

let C976AO_Q = [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`];;
let c976ao_q i = map (fun f -> mk_comb(f, mk_small_numeral i)) C976AO_Q;;
let c976ao_in i x y = list_mk_comb(`linside`, c976ao_q i @ [x; y]);;

(* Lean: Data (structure) *)
let C976AO_FIELDS =
  [0, `&28 / &25`, `&1`; 0, `&87 / &50`, `&1`;
   1, `&1`, `&8 / &5`; 1, `&1`, `&87 / &50`; 1, `&19 / &25`, `&187 / &100`;
   4, `&1`, `&1543 / &500`; 4, `&1`, `&3`;
   5, `&33 / &20`, `&33 / &20`; 5, `&2`, `&87 / &50`; 5, `&87 / &50`, `&2`; 5, `&3 / &2`, `&2`; 5, `&2`, `&3 / &2`;
   6, `&47 / &20`, `&33 / &20`; 6, `&113 / &50`, `&2`; 7, `&113 / &50`, `&3`;
   8, `&457 / &500`, `&2`; 8, `&33 / &20`, `&47 / &20`; 8, `&1`, `&113 / &50`;
   9, `&2`, `&1`; 11, `&2`, `&1543 / &500`; 11, `&8 / &5`, `&3`; 11, `&87 / &50`, `&3`];;
let c976ao_data =
  let gen = `(forall i. i < 12 ==> &1 < qa i) /\
    (forall i j. i < 12 /\ j < 12 ==> qa i = qa j) /\
    (forall i. i < 12 ==> lcont (qc i) (qs i) (qu i) (qv i) (qa i)) /\
    (forall i j. i < 12 /\ j < 12 /\ ~(i = j)
           ==> forall x y. ~(linside (qc i) (qs i) (qu i) (qv i) (qa i) x y /\
                       linside (qc j) (qs j) (qu j) (qv j) (qa j) x y))` in
  new_definition (mk_eq(list_mk_comb(`c976ao_data:(num->real)->(num->real)->(num->real)->(num->real)->(num->real)->bool`, C976AO_Q),
    mk_conj(gen, list_mk_conj (map (fun (i, x, y) -> c976ao_in i x y) C976AO_FIELDS))));;

let C976AO_UNIT = `forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1`;;
let C976AO_DATA = list_mk_comb(`c976ao_data`, C976AO_Q);;
let c976ao_stmt hyps concl =
  list_mk_forall(C976AO_Q, mk_imp(list_mk_conj ([C976AO_UNIT; C976AO_DATA] @ hyps), concl));;
let c976ao_close stmt th =
  prove(stmt, REPEAT GEN_TAC THEN STRIP_TAC THEN ACCEPT_TAC th);;

(* ---- forward toolkit (hyps C976AO_UNIT, C976AO_DATA) ---- *)
let c976ao_parts () = CONJUNCTS (REWRITE_RULE[c976ao_data] (ASSUME C976AO_DATA));;
let c976ao_lt i = EQT_ELIM (NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` (mk_small_numeral i) `12`));;
let c976ao_side i = MP (SPEC (mk_small_numeral i) (el 0 (c976ao_parts ()))) (c976ao_lt i);;
let c976ao_pos i = MATCH_MP (REAL_ARITH `&1 < a ==> &0 < a`) (c976ao_side i);;
let c976ao_same i j = MP (SPECL [mk_small_numeral i; mk_small_numeral j] (el 1 (c976ao_parts ())))
                         (CONJ (c976ao_lt i) (c976ao_lt j));;
let c976ao_box i = MP (SPEC (mk_small_numeral i) (el 2 (c976ao_parts ()))) (c976ao_lt i);;
let c976ao_unit i = MP (SPEC (mk_small_numeral i) (ASSUME C976AO_UNIT)) (c976ao_lt i);;
let c976ao_apart i j =
  MP (SPECL [mk_small_numeral i; mk_small_numeral j] (el 3 (c976ao_parts ())))
     (end_itlist CONJ [c976ao_lt i; c976ao_lt j;
        EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral i, mk_small_numeral j)))]);;
let c976ao_field i x y =
  let tm = c976ao_in i x y in
  find (fun th -> concl th = tm) (c976ao_parts ());;
let c976ao_excl i j pt =
  let args = snd (strip_comb (concl pt)) in
  let d2 = SPECL [el 5 args; el 6 args] (c976ao_apart i j) in
  let a = lhand (rand (concl d2)) in
  NOT_INTRO (DISCH a (MP (NOT_ELIM d2) (CONJ (ASSUME a) pt)));;
let c976ao_arith hs tm = MP (REAL_ARITH (mk_imp(list_mk_conj (map concl hs), tm))) (end_itlist CONJ hs);;
let c976ao_rr tm = EQT_ELIM (REAL_RAT_REDUCE_CONV tm);;

(* layered tuples (lemma, extra args), innermost first *)
let c976ao_layers i layers =
  let step (cur, eqs) (pth, extra) =
    let t = SPECL (cur @ extra @ [`x:real`; `y:real`]) pth in
    let args = snd (strip_comb (lhs (concl t))) in
    ([el 0 args; el 1 args; el 2 args; el 3 args; el 4 args], GENL [`x:real`; `y:real`] t :: eqs) in
  rev_itlist (fun l acc -> step acc l) layers (c976ao_q i, []);;
let c976ao_exact e =
  let _, b = strip_forall (concl e) in
  let tup = fst (chop_list 5 (snd (strip_comb (lhs b)))) in
  fun tm ->
    let f, args = strip_comb tm in
    if not (is_const f && fst (dest_const f) = "linside") || length args <> 7 then failwith "exact" else
    let t5, xy = chop_list 5 args in
    if forall2 aconv t5 tup then SPECL xy e else failwith "exact";;
let c976ao_unfold eqs = EVERY_CONV (map (fun e -> ONCE_DEPTH_CONV (c976ao_exact e)) eqs);;
let c976ao_conv eqs = c976ao_unfold eqs THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV;;
let c976ao_punit i t =
  let c = el 0 t and s = el 1 t in
  let tm = mk_eq(mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` c c)
                   (mk_binop `( * ):real->real->real` s s), `&1`) in
  MP (prove(mk_imp(concl (c976ao_unit i), tm), CONV_TAC REAL_RING)) (c976ao_unit i);;
let c976ao_apply conv spec facts =
  let ants = conjuncts (lhand (concl spec)) in
  let pa tm =
    try find (fun f -> aconv (concl f) tm) facts with Failure _ ->
    let eq = conv tm in
    let r = rhs (concl eq) in
    if r = `true` then EQT_ELIM eq else
    try EQ_MP (SYM eq) (find (fun f -> aconv (concl f) r) facts)
    with Failure _ -> failwith ("c976ao_apply: " ^ string_of_term tm) in
  CONV_RULE conv (MP spec (end_itlist CONJ (map pa ants)));;
let C976AO_X = (LINSIDE_PULLX, ([]:term list)) and C976AO_Y = (LINSIDE_PULLY, ([]:term list))
and C976AO_SW = (LINSIDE_PULLSW, ([]:term list));;
let c976ao_tr dx dy = (C976AO_INSIDE_TRANSLATED, [dx; dy]);;
let C976AO_BOX_Y = prove
 (`forall c s u v a. lcont c s u v a ==> forall x y. linside c s u v a x y ==> &0 <= y`,
  REWRITE_TAC[lcont] THEN MESON_TAC[]);;
let C976AO_BOX_XY = prove
 (`forall c s u v a. lcont c s u v a ==> forall x y. linside c s u v a x y ==> &0 <= x /\ &0 <= y`,
  REWRITE_TAC[lcont] THEN MESON_TAC[]);;
(* the box bound  !x y. linside T x y ==> bound  from the container of q i *)
let c976ao_tbox i eqs t bound =
  let lin = ASSUME (list_mk_comb(`linside`, t @ [`x:real`; `y:real`])) in
  let l0 = EQ_MP (c976ao_unfold eqs (concl lin)) lin in
  let args = snd (strip_comb (concl l0)) in
  let b = MP (SPECL [el 5 args; el 6 args] (REWRITE_RULE[lcont] (c976ao_box i))) l0 in
  GENL [`x:real`; `y:real`] (DISCH (concl lin) (c976ao_arith [b] bound));;
let c976ao_hseg i (x0, x1, y, x) a b =
  MP (SPECL (c976ao_q i @ [x0; x1; y; x]) OO_HORIZONTAL_SEGMENT)
    (end_itlist CONJ [a; b; c976ao_rr (mk_binop `(<):real->real->bool` x0 x1);
       c976ao_rr (mk_binop `(<=):real->real->bool` x0 x); c976ao_rr (mk_binop `(<=):real->real->bool` x x1)]);;

(* Lean: southwest_point *)
let c976ao_southwest_point () =
  let f = c976ao_field in
  let bottomMiddle = c976ao_hseg 0 (`&28 / &25`, `&87 / &50`, `&1`, `&3 / &2`)
    (f 0 `&28 / &25` `&1`) (f 0 `&87 / &50` `&1`) in
  c976ao_apply ALL_CONV (SPECL (c976ao_q 5 @ c976ao_q 0 @ c976ao_q 6) OCSWSPM_POINT_OF_NEIGHBOURS)
    [c976ao_unit 5; c976ao_pos 5; c976ao_side 5;
     f 5 `&33 / &20` `&33 / &20`; f 5 `&2` `&87 / &50`; f 5 `&87 / &50` `&2`; f 5 `&3 / &2` `&2`;
     f 5 `&2` `&3 / &2`;
     c976ao_excl 5 8 (f 8 `&33 / &20` `&47 / &20`); c976ao_excl 5 9 (f 9 `&2` `&1`);
     c976ao_excl 5 1 (f 1 `&1` `&8 / &5`); c976ao_excl 5 1 (f 1 `&1` `&87 / &50`);
     bottomMiddle; f 0 `&87 / &50` `&1`; f 6 `&47 / &20` `&33 / &20`; f 6 `&113 / &50` `&2`;
     c976ao_apart 5 0; c976ao_apart 5 6];;
let C976AO_SOUTHWEST_POINT = c976ao_close (c976ao_stmt [] (c976ao_in 5 `&127 / &100` `&49 / &25`))
  (c976ao_southwest_point ());;

(* Lean: top_reach *)
let c976ao_top_reach () =
  let f = c976ao_field in
  let layers = [C976AO_X; C976AO_Y; C976AO_SW] in
  let t, eqs = c976ao_layers 11 layers in
  let box = MATCH_MP LCONT_PULLSW (MATCH_MP LCONT_PULLY (MATCH_MP LCONT_PULLX (c976ao_box 11))) in
  c976ao_apply (c976ao_conv eqs) (SPECL t WUMR_POINT)
    [c976ao_punit 11 t; c976ao_pos 11; c976ao_side 11; box;
     f 11 `&2` `&1543 / &500`; f 11 `&8 / &5` `&3`;
     c976ao_excl 11 7 (f 7 `&113 / &50` `&3`); c976ao_excl 11 8 (f 8 `&33 / &20` `&47 / &20`)];;
let C976AO_TOP_REACH = c976ao_close (c976ao_stmt [] (c976ao_in 11 `&36 / &25` `&3`)) (c976ao_top_reach ());;

(* the left chart (q 8).translated 1 2 *)
let C976AO_LEFT = c976ao_layers 8 [c976ao_tr `&1` `&2`];;

(* Lean: left_input *)
let c976ao_left_input () =
  let f = c976ao_field in
  let t, eqs = C976AO_LEFT in
  let conv = c976ao_conv eqs in
  let lin x y = list_mk_comb(`linside`, t @ [x; y]) in
  let point = c976ao_southwest_point () and reach = c976ao_top_reach () in
  let by tm th = let e = conv tm in
    if aconv (rhs (concl e)) (concl th) then EQ_MP (SYM e) th
    else failwith ("c976ao_left_input: " ^ string_of_term (rhs (concl e))) in
  let top =
    let lo = `&11 / &25 <= x` and hi = `x <= &37 / &50` in
    let seg = MP (SPECL (c976ao_q 11 @ [`&36 / &25`; `&87 / &50`; `&3`; `&1 + x`]) OO_HORIZONTAL_SEGMENT)
      (end_itlist CONJ [reach; f 11 `&87 / &50` `&3`; c976ao_rr `&36 / &25 < &87 / &50`;
                        c976ao_arith [ASSUME lo] `&36 / &25 <= &1 + x`;
                        c976ao_arith [ASSUME hi] `&1 + x <= &87 / &50`]) in
    GEN `x:real` (DISCH lo (DISCH hi
      (EQ_MP (SYM (conv (mk_neg (lin `x:real` `&1`)))) (c976ao_excl 8 11 seg)))) in
  let segment =
    let lo = `&0 <= t` and hi = `t <= &1` in
    let s = MP (SPECL (c976ao_q 1 @ [`&19 / &25`; `&187 / &100`; `&1`; `&87 / &50`; `t:real`]) C976AO_INSIDE_SEGMENT)
      (end_itlist CONJ [f 1 `&19 / &25` `&187 / &100`; f 1 `&1` `&87 / &50`; ASSUME lo; ASSUME hi]) in
    let px = `--(&6) / &25 + (&6 / &25) * t` and py = `--(&13) / &100 - (&13 / &100) * t` in
    let args = snd (strip_comb (concl s)) in
    let ex = REAL_ARITH (mk_eq(el 5 args, mk_binop `(+):real->real->real` `&1` px))
    and ey = REAL_ARITH (mk_eq(el 6 args, mk_binop `(+):real->real->real` `&2` py)) in
    let s' = EQ_MP (REWRITE_CONV[ex; ey] (concl s)) s in
    GEN `t:real` (DISCH lo (DISCH hi
      (EQ_MP (SYM (c976ao_unfold eqs (mk_neg (lin px py)))) (c976ao_excl 8 1 s')))) in
  let facts = [c976ao_side 8; f 8 `&457 / &500` `&2`; f 8 `&33 / &20` `&47 / &20`; f 8 `&1` `&113 / &50`;
               c976ao_excl 8 5 (f 5 `&3 / &2` `&2`); c976ao_excl 8 4 (f 4 `&1` `&3`);
               c976ao_excl 8 5 point] in
  let tm = list_mk_comb(`occ976lt_input`, t) in
  let body = rhs (concl (REWRITE_CONV[occ976lt_input] tm)) in
  let pf c =
    if is_forall c then
      (try find (fun th -> aconv (concl th) c) [top; segment]
       with Failure _ -> failwith ("c976ao_left_input forall: " ^ string_of_term c))
    else try find (fun th -> aconv (concl th) c) facts with Failure _ ->
      let e = conv c in
      EQ_MP (SYM e) (find (fun th -> aconv (concl th) (rhs (concl e))) facts) in
  EQ_MP (SYM (REWRITE_CONV[occ976lt_input] tm)) (end_itlist CONJ (map pf (conjuncts body)));;
let C976AO_LEFT_INPUT = c976ao_close (c976ao_stmt [] (list_mk_comb(`occ976lt_input`, fst C976AO_LEFT)))
  (c976ao_left_input ());;

(* Lean: left_points *)
let c976ao_left_points () =
  let t, eqs = C976AO_LEFT in
  c976ao_apply (c976ao_conv eqs) (SPECL t OCC976UP_POINTS)
    [c976ao_punit 8 t; c976ao_pos 8; c976ao_left_input ()];;
let C976AO_LEFT_POINTS = c976ao_close
  (c976ao_stmt [] (list_mk_conj [c976ao_in 8 `&5 / &4` `&3`; c976ao_in 8 `&1` `&14 / &5`; c976ao_in 8 `&32 / &25` `&3`]))
  (c976ao_left_points ());;

(* Lean: top_origin *)
let c976ao_top_origin () =
  let f = c976ao_field in
  let leftHigh = CONJUNCT1 (CONJUNCT2 (c976ao_left_points ())) in
  let foreign = MP (SPECL (c976ao_q 8 @ [`&1`; `&113 / &50`; `&14 / &5`; `&5 / &2`]) OO_VERTICAL_SEGMENT)
    (end_itlist CONJ [f 8 `&1` `&113 / &50`; leftHigh; c976ao_rr `&113 / &50 < &14 / &5`;
                      c976ao_rr `&113 / &50 <= &5 / &2`; c976ao_rr `&5 / &2 <= &14 / &5`]) in
  let tB, eqB = c976ao_layers 11 [C976AO_Y] and tK, eqK = c976ao_layers 4 [C976AO_Y] in
  let disj =
    let tm = list_mk_comb(`ldisj`, tK @ tB) in
    let eq = (REWRITE_CONV[ldisj] THENC c976ao_unfold (eqK @ eqB)) tm in
    EQ_MP (SYM eq) (GEN `x:real` (GEN `y:real` (SPECL [`x:real`; `&4 - y`] (c976ao_apart 4 11)))) in
  c976ao_apply (c976ao_conv (eqB @ eqK)) (SPECL (tB @ tK @ [`&457 / &500`; `&8 / &5`]) OCWPBO_BOUNDARY_ORIGIN)
    [c976ao_punit 11 tB; c976ao_punit 4 tK; c976ao_pos 11; c976ao_pos 4; c976ao_side 11; c976ao_same 11 4;
     MATCH_MP C976AO_BOX_Y (MATCH_MP LCONT_PULLY (c976ao_box 11));
     MATCH_MP C976AO_BOX_XY (MATCH_MP LCONT_PULLY (c976ao_box 4));
     f 11 `&2` `&1543 / &500`; f 11 `&8 / &5` `&3`; f 4 `&1` `&1543 / &500`; f 4 `&1` `&3`;
     c976ao_excl 4 8 foreign; disj];;
let C976AO_TOP_ORIGIN = c976ao_close (c976ao_stmt [] (c976ao_in 11 `&2` `&3`)) (c976ao_top_origin ());;

(* Lean: northwest_reach *)
let c976ao_northwest_reach () =
  let f = c976ao_field in
  let t, eqs = c976ao_layers 4 [C976AO_X; C976AO_SW; c976ao_tr `&3` `&3`] in
  let missing = CONJUNCT1 (CONJUNCT2 (c976ao_left_points ())) in
  c976ao_apply (c976ao_conv eqs) (SPECL t C981CA_POINT)
    [c976ao_punit 4 t; c976ao_pos 4; c976ao_side 4; c976ao_tbox 4 eqs t `y <= &1`;
     f 4 `&1` `&3`; c976ao_excl 4 8 missing; c976ao_excl 4 11 (f 11 `&87 / &50` `&3`)];;
let C976AO_NORTHWEST_REACH = c976ao_close (c976ao_stmt [] (c976ao_in 4 `&1` `&18 / &5`))
  (c976ao_northwest_reach ());;

(* Lean: steep_negative_top *)
let c976ao_steep_negative_top () =
  let f = c976ao_field in
  let tN, eqN = C976AO_LEFT and tW, eqW = c976ao_layers 11 [c976ao_tr `&1` `&2`] in
  let conv = c976ao_conv (eqN @ eqW) in
  let win x y = list_mk_comb(`linside`, tW @ [x; y]) in
  let reach = c976ao_top_reach () and origin = c976ao_top_origin () in
  let by tm th = let e = c976ao_conv eqW tm in
    if aconv (rhs (concl e)) (concl th) then EQ_MP (SYM e) th
    else failwith ("c976ao_steep: " ^ string_of_term (rhs (concl e))) in
  let top = EQ_MP (SYM (REWRITE_CONV[oltstsu_top] (list_mk_comb(`oltstsu_top`, tW))))
    (end_itlist CONJ [by (win `&11 / &25` `&1`) reach; by (win `&1` `&1`) origin;
                      by (win `&1` `&543 / &500`) (f 11 `&2` `&1543 / &500`);
                      by (mk_neg (win `&63 / &50` `&1`)) (c976ao_excl 11 7 (f 7 `&113 / &50` `&3`));
                      c976ao_tbox 11 eqW tW `y <= &2`]) in
  let disj =
    let tm = list_mk_comb(`ldisj`, tN @ tW) in
    let eq = (REWRITE_CONV[ldisj] THENC c976ao_unfold (eqN @ eqW)) tm in
    EQ_MP (SYM eq) (GEN `x:real` (GEN `y:real` (SPECL [`&1 + x`; `&2 + y`] (c976ao_apart 8 11)))) in
  c976ao_apply conv (SPECL (tN @ tW) OCC976UP_STEEP_NEGATIVE)
    [c976ao_punit 8 tN; c976ao_pos 8; c976ao_punit 11 tW; c976ao_pos 11; c976ao_left_input (); top;
     ASSUME `&0 < qc 11`; ASSUME `qs 11 <= &0`; c976ao_same 8 11; disj];;
let C976AO_STEEP_NEGATIVE_TOP = c976ao_close
  (c976ao_stmt [`&0 < qc 11`; `qs 11 <= &0`] `(&2 / &3) * qc 11 < --(qs 11)`)
  (c976ao_steep_negative_top ());;
