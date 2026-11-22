(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1090/EarlyGeometry.lean            *)
(* (namespace N12Compact.Completion.OtherCases.C1090.Early).                *)
(* C1090-SIMPLIFIED-PROOF sections 3--6 from the compulsory strict points.  *)
(* (Lean header: "Source translation only; no compilation is claimed.")     *)
(* q : Fin 12 -> OpenSquare is written as five coordinate functions          *)
(*   qc qs qu qv qa : num -> real,  q i = (qc i, qs i, qu i, qv i, qa i),    *)
(* i < 12.  The OpenSquare field unit_normal is the separate hypothesis      *)
(*   !i. i < 12 ==> qc i * qc i + qs i * qs i = &1   (side_pos follows from  *)
(* the side field).  pullX / pullY / pullSwap: LINSIDE_PULLX/Y/SW.           *)
(* C1089.ContinuousBottom.reach: C1089CB_REACH; MergedLeftSeed.              *)
(* actual_segment: C1090MLS_ACTUAL_SEGMENT; WallUpperMissingReach.point:     *)
(* WUMR_POINT; C981CompletionCrosspoint.point: C981CP_POINT;                *)
(* ElbowPoint.points_original: OCEP_POINTS_ORIGINAL; inside_segment on a    *)
(* horizontal / vertical segment: OO_HORIZONTAL_SEGMENT / OO_VERTICAL_SEGMENT.*)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ContinuousBottom.ml";;
needs "n12/geometry/CP_OtherCases_C1090_MergedLeftSeed.ml";;
needs "n12/geometry/CP_OtherCases_ElbowPoint.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;
needs "n12/geometry/WallUpperMissingReach.ml";;

(* Lean: Input (structure) *)
let c1090eg_input = new_definition
 `c1090eg_input (qc:num->real) (qs:num->real) (qu:num->real) (qv:num->real) (qa:num->real) <=>
    (forall i. i < 12 ==> &1 < qa i) /\
    (forall i j. i < 12 /\ j < 12 ==> qa i = qa j) /\
    (forall i. i < 12 ==> lcont (qc i) (qs i) (qu i) (qv i) (qa i)) /\
    (forall i j. i < 12 /\ j < 12 /\ ~(i = j)
           ==> forall x y. ~(linside (qc i) (qs i) (qu i) (qv i) (qa i) x y /\
                       linside (qc j) (qs j) (qu j) (qv j) (qa j) x y)) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&28 / &25) (&1) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&87 / &50) (&1) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&187 / &100) (&19 / &25) /\
    linside (qc 1) (qs 1) (qu 1) (qv 1) (qa 1) (&3) (&457 / &500) /\
    linside (qc 1) (qs 1) (qu 1) (qv 1) (qa 1) (&1543 / &500) (&1) /\
    linside (qc 1) (qs 1) (qu 1) (qv 1) (qa 1) (&3) (&1) /\
    linside (qc 2) (qs 2) (qu 2) (qv 2) (qa 2) (&3) (&3) /\
    linside (qc 3) (qs 3) (qu 3) (qv 3) (qa 3) (&1) (&1543 / &500) /\
    linside (qc 3) (qs 3) (qu 3) (qv 3) (qa 3) (&1) (&3) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&33 / &20) (&33 / &20) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&2) (&87 / &50) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&87 / &50) (&2) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&47 / &20) (&33 / &20) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&3) (&87 / &50) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&47 / &20) (&47 / &20) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&33 / &20) (&47 / &20) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&457 / &500) (&1) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&457 / &500) (&2) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&2) (&457 / &500) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&12 / &5) (&1) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&113 / &50) (&1) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&1543 / &500) (&2) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&113 / &50) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&12 / &5) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&2) (&1543 / &500) /\
    (linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&113 / &50) (&1) \/
     linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&113 / &50) (&2) \/
     linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&3) (&8 / &5)) /\
    (linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&2) (&113 / &50) \/
     linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&12 / &5) (&3) \/
     linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&3) (&113 / &50)) /\
    (linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&113 / &50) (&2) \/
     linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&113 / &50) (&3) \/
     linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&3) (&12 / &5)) /\
    (linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&113 / &50) \/
     linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&8 / &5) (&3) \/
     linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&2) (&113 / &50)) /\
    (linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&12 / &5) \/
     linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&2) \/
     linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&3)) /\
    (linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&113 / &50) (&3) \/
     (linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&8 / &5) (&3) /\ linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&87 / &50) (&3)))`;;

let C1090EG_UNIT = `forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1`;;

(* apart, used as  h.apart i j _ _ _ <own, point> *)
let C1090EG_FOREIGN = prove
 (`forall qc qs qu qv qa i j x y.
     c1090eg_input qc qs qu qv qa /\ i < 12 /\ j < 12 /\ ~(i = j) /\
     linside (qc j) (qs j) (qu j) (qv j) (qa j) x y
     ==> ~linside (qc i) (qs i) (qu i) (qv i) (qa i) x y`,
  REWRITE_TAC[c1090eg_input] THEN MESON_TAC[]);;

let c1090eg_q i = map (fun f -> mk_comb(f, mk_small_numeral i))
  [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`];;
let c1090eg_pull tms [c; s; u; v; a] =
  map (vsubst [c, `c:real`; s, `s:real`; u, `u:real`; v, `v:real`; a, `a:real`]) tms;;
let c1090eg_pullx = c1090eg_pull [`--c:real`; `s:real`; `u - &4 * c`; `--v - a - &4 * s`; `a:real`];;
let c1090eg_pully = c1090eg_pull [`c:real`; `--s:real`; `u - &4 * s`; `&4 * c - v - a`; `a:real`];;
let c1090eg_pullsw = c1090eg_pull [`s:real`; `c:real`; `u:real`; `--v - a`; `a:real`];;

(* square facts of q i as assumptions (needs the unit and input assumptions) *)
let C1090EG_SQUARE_TAC i =
  let n = mk_small_numeral i in
  let lt = EQT_ELIM (NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` n `12`)) in
  FIRST_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) `( * ):real->real->real`)) (concl th)
     && not (can (find_term ((=) `linside`)) (concl th))
     then let u = MP (SPEC n th) lt in
          ASSUME_TAC u THEN ASSUME_TAC (ONCE_REWRITE_RULE[REAL_ADD_SYM] u) else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `c1090eg_input qc qs qu qv qa`) (concl th) then
     let cs = CONJUNCTS (REWRITE_RULE[c1090eg_input] th) in
     let side = MP (SPEC n (el 0 cs)) lt and box = MP (SPEC n (el 2 cs)) lt in
     ASSUME_TAC side THEN ASSUME_TAC box THEN
     ASSUME_TAC (MATCH_MP (REAL_ARITH `&1 < x ==> &0 < x`) side) else NO_TAC);;

let C1090EG_UNFOLD_TAC =
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o REWRITE_RULE[c1090eg_input] o
    check (can (term_match [] `c1090eg_input qc qs qu qv qa`) o concl));;

(* a negated point of q i from a point of q j *)
let C1090EG_FOREIGN_TAC js =
  MATCH_MP_TAC C1090EG_FOREIGN THEN
  FIRST (map (fun j -> EXISTS_TAC (mk_small_numeral j) THEN ASM_REWRITE_TAC[] THEN
                       CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN NO_TAC) js);;

(* apply a geometry lemma th to a transformed tuple; side goals from the assumptions *)
let C1090EG_APPLY_TAC th tp js =
  MP_TAC (SPECL tp th) THEN
  REWRITE_TAC[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           ASM_SIMP_TAC[LCONT_PULLX; LCONT_PULLY; LCONT_PULLSW] THEN NO_TAC;
           C1090EG_FOREIGN_TAC js];
    REWRITE_TAC[]];;

(* Lean: singleton_bar *)
let C1090EG_SINGLETON_BAR = prove
 (`forall qc qs qu qv qa x. c1090eg_input qc qs qu qv qa /\ &28 / &25 <= x /\ x <= &87 / &50
     ==> linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) x (&1)`,
  REWRITE_TAC[c1090eg_input] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&28 / &25`; `&87 / &50`] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: left_bar *)
let C1090EG_LEFT_BAR = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090eg_input qc qs qu qv qa
     ==> forall y. &5 / &4 <= y ==> y <= &7 / &4 ==> linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&1) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1090EG_SQUARE_TAC 8 THEN
  MATCH_MP_TAC C1090MLS_ACTUAL_SEGMENT THEN C1090EG_UNFOLD_TAC THEN ASM_REWRITE_TAC[]);;

(* Lean: bottom_advance *)
let C1090EG_BOTTOM_ADVANCE = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090eg_input qc qs qu qv qa
     ==> linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&14 / &5) (&1) /\
         forall x. &113 / &50 <= x /\ x <= &14 / &5 ==> linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) x (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1090EG_SQUARE_TAC 9 THEN
  C1090EG_UNFOLD_TAC THEN
  C1090EG_APPLY_TAC C1089CB_REACH (c1090eg_q 9) [0; 5] THEN SIMP_TAC[]);;

(* Lean: right_advance *)
let C1090EG_RIGHT_ADVANCE = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090eg_input qc qs qu qv qa
     ==> linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&64 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1090EG_SQUARE_TAC 10 THEN
  C1090EG_UNFOLD_TAC THEN
  C1090EG_APPLY_TAC WUMR_POINT (c1090eg_pullx (c1090eg_q 10)) [5; 6]);;

(* Lean: right_bar *)
let C1090EG_RIGHT_BAR = prove
 (`forall qc qs qu qv qa y. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090eg_input qc qs qu qv qa /\
     &113 / &50 <= y /\ y <= &64 / &25
     ==> linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPEC_ALL C1090EG_RIGHT_ADVANCE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1090EG_UNFOLD_TAC THEN
  MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&113 / &50`; `&64 / &25`] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: southwest_south *)
let C1090EG_SOUTHWEST_SOUTH = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090eg_input qc qs qu qv qa
     ==> linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&2) (&3 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1090EG_SQUARE_TAC 4 THEN
  MP_TAC (SPEC_ALL C1090EG_LEFT_BAR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun y -> ASSUME_TAC (CONV_RULE REAL_RAT_REDUCE_CONV (SPEC y th)))
                         [`&8 / &5`; `&3 / &2`]) THEN
  C1090EG_UNFOLD_TAC THEN
  C1090EG_APPLY_TAC C981CP_POINT (c1090eg_pully (c1090eg_pullx (c1090eg_q 4))) [7; 5; 8]);;

(* Lean: southwest_west *)
let C1090EG_SOUTHWEST_WEST = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090eg_input qc qs qu qv qa
     ==> linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&3 / &2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1090EG_SQUARE_TAC 4 THEN
  MAP_EVERY (fun x -> ASSUME_TAC (UNDISCH_ALL (REWRITE_RULE[IMP_CONJ]
     (CONV_RULE REAL_RAT_REDUCE_CONV (SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
        `qa:num->real`; x] C1090EG_SINGLETON_BAR)))))
    [`&8 / &5`; `&3 / &2`] THEN
  C1090EG_UNFOLD_TAC THEN
  C1090EG_APPLY_TAC C981CP_POINT (c1090eg_pullsw (c1090eg_pully (c1090eg_pullx (c1090eg_q 4)))) [5; 7; 0]);;

(* Lean: southeast_g8 *)
let C1090EG_SOUTHEAST_G8 = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090eg_input qc qs qu qv qa
     ==> linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&3) (&8 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPEC_ALL C1090EG_SOUTHWEST_SOUTH) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1090EG_SQUARE_TAC 5 THEN
  C1090EG_UNFOLD_TAC THEN
  ASM_CASES_TAC `linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&3) (&8 / &5)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&113 / &50) (&2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `~linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&113 / &50) (&1)` MP_TAC THENL
     [C1090EG_FOREIGN_TAC [9]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&2) (&3 / &2)` ASSUME_TAC THENL
   [C1090EG_APPLY_TAC OCEP_POINTS_ORIGINAL (c1090eg_q 5) [6; 10] THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&2) (&3 / &2)` MP_TAC THENL
   [C1090EG_FOREIGN_TAC [5]; ASM_REWRITE_TAC[]]);;
