(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/LastSectorRawPoints.lean      *)
(* (namespace N12Compact.Completion.OtherCases.C1089.LastSectorRawPoints).   *)
(* Earlier actual-point producers for the last C1089 sector.                 *)
(* q : Fin 12 -> OpenSquare is written as five coordinate functions          *)
(*   qc qs qu qv qa : num -> real,  q i = (qc i, qs i, qu i, qv i, qa i),    *)
(* i < 12; the unit normals are the explicit hypothesis                     *)
(*   !i. i < 12 ==> qc i * qc i + qs i * qs i = &1.                         *)
(* The structure Input is c1089lsrp_input (centerY = lcy).                   *)
(* inside_segment on horizontal / vertical segments: OO_HORIZONTAL_SEGMENT / *)
(* OO_VERTICAL_SEGMENT; ContinuousBottom.reach: C1089CB_REACH;               *)
(* WallOrigins.right_low: OC1089WO_RIGHT_LOW; C981CompletionCrosspoint.point:*)
(* C981CP_POINT; ElbowPoint.points_original: OCEP_POINTS_ORIGINAL;           *)
(* LastSectorNorthwest.ordinary_pair: C1089LSNW_ORDINARY_PAIR (its Input =   *)
(* c1089lsni_input); ContinuousActual.southeast: C1089CA_SOUTHEAST;          *)
(* SingletonCorner.corner_of_seeds: C1089SC_CORNER_OF_SEEDS.  Tag C1089LSRP_.*)
(* ========================================================================= *)

needs "n12/geometry/CP_C981_Crosspoint.ml";;
needs "n12/geometry/CP_OtherCases_C1089_LastSectorNorthwest.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ContinuousActual.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ContinuousBottom.ml";;
needs "n12/geometry/CP_OtherCases_C1089_SingletonCorner.ml";;

(* Lean: Input (structure) *)
let c1089lsrp_input = new_definition
 `c1089lsrp_input (qc:num->real) (qs:num->real) (qu:num->real) (qv:num->real) (qa:num->real) <=>
    (forall i. i < 12 ==> &1 < qa i) /\
    (forall i j. i < 12 /\ j < 12 ==> qa i = qa j) /\
    (forall i. i < 12 ==> lcont (qc i) (qs i) (qu i) (qv i) (qa i)) /\
    (forall i j. i < 12 /\ j < 12 /\ ~(i = j)
           ==> forall x y. ~(linside (qc i) (qs i) (qu i) (qv i) (qa i) x y /\
                       linside (qc j) (qs j) (qu j) (qv j) (qa j) x y)) /\
    (forall i. i < 12 ==> ~linside (qc i) (qs i) (qu i) (qv i) (qa i) (&457 / &500) (&1)) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&1) (&457 / &500) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&28 / &25) (&1) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&87 / &50) (&1) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&187 / &100) (&19 / &25) /\
    (~linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&1) (&1)
     ==> linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&91 / &50) (&1) /\
         linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&49 / &25) (&19 / &25)) /\
    linside (qc 1) (qs 1) (qu 1) (qv 1) (qa 1) (&3) (&457 / &500) /\
    linside (qc 1) (qs 1) (qu 1) (qv 1) (qa 1) (&1543 / &500) (&1) /\
    linside (qc 1) (qs 1) (qu 1) (qv 1) (qa 1) (&3) (&1) /\
    linside (qc 2) (qs 2) (qu 2) (qv 2) (qa 2) (&3) (&1543 / &500) /\
    linside (qc 2) (qs 2) (qu 2) (qv 2) (qa 2) (&3) (&3) /\
    linside (qc 3) (qs 3) (qu 3) (qv 3) (qa 3) (&1) (&3) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&33 / &20) (&33 / &20) /\
    (linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&1) (&87 / &50) \/
     linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&8 / &5) (&1) \/
     linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&2) (&87 / &50)) /\
    (linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&1) (&8 / &5) \/
     linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&87 / &50) (&1) \/
     linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&87 / &50) (&2)) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&47 / &20) (&33 / &20) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&2) (&87 / &50) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&113 / &50) (&2) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&47 / &20) (&47 / &20) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&3) (&113 / &50) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&3) (&12 / &5) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&33 / &20) (&47 / &20) /\
    (linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&113 / &50) \/
     linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&8 / &5) (&3) \/
     linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&2) (&113 / &50)) /\
    (linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&12 / &5) \/
     linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&2) \/
     linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&3)) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&457 / &500) (&2) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&1) (&113 / &50) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&1) (&12 / &5) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&2) (&457 / &500) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&12 / &5) (&1) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&113 / &50) (&1) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&1543 / &500) (&2) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&87 / &50) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&8 / &5) /\
    lcy (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) <= &2 /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&2) (&1543 / &500) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&12 / &5) (&3) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&113 / &50) (&3)`;;

let C1089LSRP_Q = [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`];;
let C1089LSRP_UNIT = `forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1`;;
let C1089LSRP_IN = list_mk_comb(`c1089lsrp_input`, C1089LSRP_Q);;
let c1089lsrp_stmt vars hyps concl =
  list_mk_forall(C1089LSRP_Q @ vars,
    mk_imp(list_mk_conj([C1089LSRP_UNIT; C1089LSRP_IN] @ hyps), concl));;
let c1089lsrp_sq i = map (fun f -> mk_comb(f, mk_small_numeral i)) C1089LSRP_Q;;
let c1089lsrp_own i x y = list_mk_comb(`linside`, c1089lsrp_sq i @ [x; y]);;

(* Input.apart, as a foreign-point exclusion *)
let C1089LSRP_FOREIGN = prove
 (`forall qc qs qu qv qa i j x y.
     c1089lsrp_input qc qs qu qv qa /\ i < 12 /\ j < 12 /\ ~(i = j) /\
     linside (qc j) (qs j) (qu j) (qv j) (qa j) x y
     ==> ~linside (qc i) (qs i) (qu i) (qv i) (qa i) x y`,
  REWRITE_TAC[c1089lsrp_input] THEN MESON_TAC[]);;

(* a contradiction from two distinct squares q i, q j containing the same point *)
let C1089LSRP_CLASH_TAC (asl, w as g) =
  let owned = List.filter_map (fun (_, th) ->
     let t = concl th in
     try let f, args = strip_comb t in
         if f <> `linside` then failwith "" else
         let qf, n = dest_comb (hd args) in
         if qf <> `qc:num->real` then failwith "" else
         Some (dest_small_numeral n, (el 5 args, el 6 args))
     with _ -> None) asl in
  let pairs = flat (map (fun (m, p) -> List.filter_map (fun (n, q) ->
     if m <> n && aconv (fst p) (fst q) && aconv (snd p) (snd q) then Some (m, n, p) else None) owned)
     owned) in
  if pairs = [] then failwith "C1089LSRP_CLASH_TAC" else
  let (m, n, (x, y)) = hd pairs in
  (MP_TAC (SPECL (C1089LSRP_Q @ [mk_small_numeral m; mk_small_numeral n; x; y]) C1089LSRP_FOREIGN) THEN
   ASM_REWRITE_TAC[ARITH]) g;;

(* unfold the input (keeping it), instantiate the indexed facts *)
let C1089LSRP_START_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if concl th = C1089LSRP_IN then
    MAP_EVERY ASSUME_TAC (CONJUNCTS (REWRITE_RULE[c1089lsrp_input] th)) else NO_TAC) THEN
  C1089CA_INDEX_TAC (0 -- 11);;

let C1089LSRP_SIDE_TAC =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[REAL_NEG_MUL2] THEN FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[REAL_NEG_MUL2] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
         FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN CONV_TAC NUM_REDUCE_CONV THEN NO_TAC);
         REWRITE_TAC[ldisj] THEN REPEAT GEN_TAC THEN
         DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN C1089LSRP_CLASH_TAC;
         REPEAT (FIRST [MATCH_MP_TAC LCONT_PULLSW; MATCH_MP_TAC LCONT_PULLX; MATCH_MP_TAC LCONT_PULLY]) THEN
         FIRST_ASSUM ACCEPT_TAC;
         DISCH_TAC THEN C1089LSRP_CLASH_TAC;
         RASM_ARITH_TAC];;

let C1089LSRP_PULL_CONV =
  REWRITE_CONV[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW] THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV;;
let c1089lsrp_lemma th tp = CONV_RULE C1089LSRP_PULL_CONV (SPECL tp th);;

let c1089lsrp_pull tms t = match t with
    [c; s; u; v; a] -> map (vsubst [c, `c:real`; s, `s:real`; u, `u:real`; v, `v:real`; a, `a:real`]) tms
  | _ -> failwith "c1089lsrp_pull";;
let c1089lsrp_px = c1089lsrp_pull [`--c:real`; `s:real`; `u - &4 * c`; `--v - a - &4 * s`; `a:real`];;
let c1089lsrp_py = c1089lsrp_pull [`c:real`; `--s:real`; `u - &4 * s`; `&4 * c - v - a`; `a:real`];;
let c1089lsrp_sw = c1089lsrp_pull [`s:real`; `c:real`; `u:real`; `--v - a`; `a:real`];;

(* Lean: singleton_bar *)
let C1089LSRP_SINGLETON_BAR = prove
 (c1089lsrp_stmt [`x:real`] [`&28 / &25 <= x`; `x <= &87 / &50`] (c1089lsrp_own 0 `x:real` `&1`),
  C1089LSRP_START_TAC THEN
  MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&28 / &25`; `&87 / &50`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: bottom_advance *)
let C1089LSRP_BOTTOM_ADVANCE = prove
 (c1089lsrp_stmt [] [] (c1089lsrp_own 9 `&14 / &5` `&1`),
  C1089LSRP_START_TAC THEN
  MP_TAC (SPECL (c1089lsrp_sq 9) C1089CB_REACH) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN C1089LSRP_SIDE_TAC;
                 DISCH_THEN (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2)]);;

(* Lean: southeast_south *)
let C1089LSRP_SOUTHEAST_SOUTH = prove
 (c1089lsrp_stmt [] [] (c1089lsrp_own 5 `&2` `&3 / &2`),
  C1089LSRP_START_TAC THEN
  MP_TAC (SPECL (c1089lsrp_sq 10 @ c1089lsrp_sq 6 @ c1089lsrp_sq 5) OC1089WO_RIGHT_LOW) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN C1089LSRP_SIDE_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN (c1089lsrp_own 10 `&3` `&3 / &2`) ASSUME_TAC THENL
   [MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&36 / &25`; `&8 / &5`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC (c1089lsrp_lemma C981CP_POINT (c1089lsrp_py (c1089lsrp_sq 5))) THEN
  REPEAT CONJ_TAC THEN C1089LSRP_SIDE_TAC);;

(* an earlier theorem of this file at the assumptions (unit normals, input [, extra facts]) *)
let c1089lsrp_have ?(vars=[]) ?(extra=[]) th =
  let hs = CONJ (ASSUME C1089LSRP_UNIT) (end_itlist CONJ (ASSUME C1089LSRP_IN :: extra)) in
  ASSUME_TAC (MP (SPECL (C1089LSRP_Q @ vars) th) hs);;
let c1089lsrp_num tm = EQT_ELIM (REAL_RAT_REDUCE_CONV tm);;
let c1089lsrp_contr th (asl, w as g) =
  ACCEPT_TAC (CONTR w (MP (NOT_ELIM (find (fun h -> concl h = mk_neg (concl th)) (map snd asl))) th)) g;;
let c1089lsrp_disj x y =
  check (fun th -> is_disj (concl th) && rand (rator (lhand (concl th))) = x &&
                   rand (lhand (concl th)) = y);;

(* Lean: southwest_pair *)
let C1089LSRP_SOUTHWEST_PAIR = prove
 (c1089lsrp_stmt [] [] (mk_conj(c1089lsrp_own 4 `&1` `&87 / &50`, c1089lsrp_own 4 `&1` `&8 / &5`)),
  C1089LSRP_START_TAC THEN
  c1089lsrp_have ~vars:[`&8 / &5`]
    ~extra:[c1089lsrp_num `&28 / &25 <= &8 / &5`; c1089lsrp_num `&8 / &5 <= &87 / &50`]
    C1089LSRP_SINGLETON_BAR THEN
  c1089lsrp_have C1089LSRP_SOUTHEAST_SOUTH THEN
  SUBGOAL_THEN (c1089lsrp_own 4 `&1` `&87 / &50`) ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN2 ACCEPT_TAC (DISJ_CASES_THEN ASSUME_TAC) o
      c1089lsrp_disj `&1` `&87 / &50`) THEN
    C1089LSRP_CLASH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC (c1089lsrp_own 4 `&1` `&8 / &5`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (c1089lsrp_own 4 `&87 / &50` `&2`) ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN2 c1089lsrp_contr (DISJ_CASES_THEN ASSUME_TAC) o
      c1089lsrp_disj `&1` `&8 / &5`) THEN
    TRY (FIRST_ASSUM ACCEPT_TAC) THEN C1089LSRP_CLASH_TAC;
    ALL_TAC] THEN
  MP_TAC (c1089lsrp_lemma OCEP_POINTS_ORIGINAL (c1089lsrp_px (c1089lsrp_sq 4))) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN C1089LSRP_SIDE_TAC; STRIP_TAC] THEN
  C1089LSRP_CLASH_TAC);;

(* Lean: northwest_pair *)
let C1089LSRP_NORTHWEST_PAIR = prove
 (c1089lsrp_stmt [] [] (mk_conj(c1089lsrp_own 7 `&8 / &5` `&3`, c1089lsrp_own 7 `&87 / &50` `&3`)),
  C1089LSRP_START_TAC THEN
  c1089lsrp_have C1089LSRP_SOUTHWEST_PAIR THEN c1089lsrp_have C1089LSRP_SOUTHEAST_SOUTH THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM (CONJUNCTS_THEN ASSUME_TAC) THEN DISCH_TAC THEN
  MATCH_MP_TAC C1089LSNW_ORDINARY_PAIR THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1089lsni_input] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* Lean: southeast_east *)
let C1089LSRP_SOUTHEAST_EAST = prove
 (c1089lsrp_stmt [] [] (c1089lsrp_own 5 `&5 / &2` `&2`),
  C1089LSRP_START_TAC THEN
  c1089lsrp_have C1089LSRP_BOTTOM_ADVANCE THEN
  SUBGOAL_THEN (c1089lsrp_own 9 `&5 / &2` `&1`) ASSUME_TAC THENL
   [MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&12 / &5`; `&14 / &5`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC (c1089lsrp_lemma C981CP_POINT (c1089lsrp_px (c1089lsrp_sw (c1089lsrp_sq 5)))) THEN
  REPEAT CONJ_TAC THEN C1089LSRP_SIDE_TAC);;

(* Lean: southeast_center_and_right_origin *)
let C1089LSRP_SOUTHEAST_CENTER_AND_RIGHT_ORIGIN = prove
 (c1089lsrp_stmt [] [] (mk_conj(c1089lsrp_own 5 `&2` `&2`, c1089lsrp_own 10 `&3` `&2`)),
  REPEAT GEN_TAC THEN REWRITE_TAC[c1089lsrp_input] THEN
  DISCH_THEN (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MATCH_MP_TAC C1089CA_SOUTHEAST THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* Lean: singleton_corner *)
let C1089LSRP_SINGLETON_CORNER = prove
 (c1089lsrp_stmt [] [] (c1089lsrp_own 0 `&1` `&1`),
  C1089LSRP_START_TAC THEN
  c1089lsrp_have C1089LSRP_BOTTOM_ADVANCE THEN c1089lsrp_have C1089LSRP_SOUTHEAST_SOUTH THEN
  ASM_CASES_TAC (c1089lsrp_own 0 `&1` `&1`) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> if is_imp (concl th) && lhand (concl th) = mk_neg (c1089lsrp_own 0 `&1` `&1`)
                          then STRIP_ASSUME_TAC (MP th (ASSUME (lhand (concl th)))) else NO_TAC) THEN
  UNDISCH_TAC (mk_neg (c1089lsrp_own 0 `&1` `&1`)) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC (SPECL (c1089lsrp_sq 0 @ c1089lsrp_sq 1 @ c1089lsrp_sq 5 @ c1089lsrp_sq 6 @
                       c1089lsrp_sq 9 @ c1089lsrp_sq 10) C1089SC_CORNER_OF_SEEDS) THEN
  REPEAT CONJ_TAC THEN C1089LSRP_SIDE_TAC);;
