(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/LastSectorSupportJoin.lean    *)
(* (N12Compact.Completion.OtherCases.C1089.LastSectorSupportJoin).          *)
(* C1089-LAST-SECTOR-ENDING sections 3--5: the southeast support point is   *)
(* derived (reflected SouthwestSupportPoint.point_of_neighbours) and feeds   *)
(* the final ordinary-origin obstruction (LastOrdinaryObstruction).          *)
(* The Lean header says "This source has not been compiled."                *)
(* q : Fin 12 -> OpenSquare is written as five coordinate functions          *)
(*   qc qs qu qv qa : num -> real  (q i = (qc i, qs i, qu i, qv i, qa i)),   *)
(* i < 12; the OpenSquare invariant unit_normal of each q i is the explicit *)
(* hypothesis  !i. i < 12 ==> qc i * qc i + qs i * qs i = &1  (side_pos      *)
(* follows from the field side).  pullX is LINSIDE_PULLX, inside_segment is  *)
(* CES_INSIDE_SEGMENT, WallProfile.vertical_owned is OCWPVG_VERTICAL_OWNED.  *)
(* Tag OC1089LSSJ_.                                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1089_LastOrdinaryObstruction.ml";;
needs "n12/geometry/CP_OtherCases_SouthwestSupportPoint_Main.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;

(* Lean: BaseData (structure) *)
let oc1089lssj_base = new_definition
 `oc1089lssj_base (qc:num->real) (qs:num->real) (qu:num->real) (qv:num->real) (qa:num->real) <=>
    (forall i. i < 12 ==> &1 < qa i) /\
    (forall i j. i < 12 /\ j < 12 /\ ~(i = j)
           ==> forall x y. ~(linside (qc i) (qs i) (qu i) (qv i) (qa i) x y /\
                       linside (qc j) (qs j) (qu j) (qv j) (qa j) x y)) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&33 / &20) (&33 / &20) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&47 / &20) (&33 / &20) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&2) (&87 / &50) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&113 / &50) (&2) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&5 / &2) (&2) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&2) (&3 / &2) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&47 / &20) (&47 / &20) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&3) (&113 / &50) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&36 / &25) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&2) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&2) (&1) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&113 / &50) (&1) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&14 / &5) (&1) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&2) (&3) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&64 / &25) (&3) /\
    linside (qc 2) (qs 2) (qu 2) (qv 2) (qa 2) (&3) (&3)`;;

(* Lean: Data (structure extending BaseData) *)
let oc1089lssj_data = new_definition
 `oc1089lssj_data (qc:num->real) (qs:num->real) (qu:num->real) (qv:num->real) (qa:num->real) <=>
    oc1089lssj_base qc qs qu qv qa /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&87 / &50) (&2)`;;

(* the apart field at two literal indices *)
let OC1089LSSJ_APART = prove
 (`forall qc qs qu qv qa i j x y.
     oc1089lssj_base qc qs qu qv qa /\ i < 12 /\ j < 12 /\ ~(i = j) /\
     linside (qc j) (qs j) (qu j) (qv j) (qa j) x y
     ==> ~linside (qc i) (qs i) (qu i) (qv i) (qa i) x y`,
  REWRITE_TAC[oc1089lssj_base] THEN MESON_TAC[]);;

let OC1089LSSJ_APART_AT i j =
  let th = SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`;
                  mk_small_numeral i; mk_small_numeral j] OC1089LSSJ_APART in
  REWRITE_RULE[ARITH] th;;

(* Lean: southeast_point *)
let OC1089LSSJ_SOUTHEAST_POINT = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     oc1089lssj_data qc qs qu qv qa
     ==> linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&273 / &100) (&49 / &25)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[oc1089lssj_data] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MP_TAC(REWRITE_RULE[oc1089lssj_base] (ASSUME `oc1089lssj_base qc qs qu qv qa`)) THEN STRIP_TAC THEN
  (* bottomMiddle *)
  SUBGOAL_THEN `linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&5 / &2) (&1)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`qc 9:real`; `qs 9:real`; `qu 9:real`; `qv 9:real`; `qa 9:real`;
                  `&113 / &50`; `&1`; `&14 / &5`; `&1`; `&4 / &9`] CES_INSIDE_SEGMENT) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  (* rightBar, rightFirst, rightLast *)
  MP_TAC(SPECL [`qc 10:real`; `qs 10:real`; `qu 10:real`; `qv 10:real`; `qa 10:real`;
                `&3`; `&36 / &25`; `&2`] OCWPVG_VERTICAL_OWNED) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN `linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&8 / &5) /\
                linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&87 / &50)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  (* result: point_of_neighbours for pullX q5, pullX q9, pullX q4 *)
  MP_TAC(SPECL [`--(qc 5):real`; `qs 5:real`; `qu 5 - &4 * qc 5`; `--(qv 5) - qa 5 - &4 * qs 5`; `qa 5:real`;
                `--(qc 9):real`; `qs 9:real`; `qu 9 - &4 * qc 9`; `--(qv 9) - qa 9 - &4 * qs 9`; `qa 9:real`;
                `--(qc 4):real`; `qs 4:real`; `qu 4 - &4 * qc 4`; `--(qv 4) - qa 4 - &4 * qs 4`; `qa 4:real`]
         OCSWSPM_POINT_OF_NEIGHBOURS) THEN
  REWRITE_TAC[LINSIDE_PULLX; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `5` (ASSUME `forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1`)) THEN
  MP_TAC(SPEC `5` (ASSUME `forall i. i < 12 ==> &1 < qa i`)) THEN
  REWRITE_TAC[ARITH] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(OC1089LSSJ_APART_AT 5 6) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(OC1089LSSJ_APART_AT 5 9) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(OC1089LSSJ_APART_AT 5 10) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(OC1089LSSJ_APART_AT 5 10) THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[TAUT `~(p /\ q) <=> (q ==> ~p)`] THEN DISCH_TAC THEN
    MATCH_MP_TAC(OC1089LSSJ_APART_AT 5 9) THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[TAUT `~(p /\ q) <=> (q ==> ~p)`] THEN DISCH_TAC THEN
    MATCH_MP_TAC(OC1089LSSJ_APART_AT 5 4) THEN ASM_REWRITE_TAC[]]);;

(* Lean: impossible *)
let OC1089LSSJ_IMPOSSIBLE = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     oc1089lssj_data qc qs qu qv qa
     ==> false`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OC1089LSSJ_SOUTHEAST_POINT) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[oc1089lssj_data] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MP_TAC(REWRITE_RULE[oc1089lssj_base] (ASSUME `oc1089lssj_base qc qs qu qv qa`)) THEN STRIP_TAC THEN
  (* topInner *)
  SUBGOAL_THEN `linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&113 / &50) (&3)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`qc 11:real`; `qs 11:real`; `qu 11:real`; `qv 11:real`; `qa 11:real`;
                  `&2`; `&3`; `&64 / &25`; `&3`; `&13 / &28`] CES_INSIDE_SEGMENT) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`qc 6:real`; `qs 6:real`; `qu 6:real`; `qv 6:real`; `qa 6:real`]
    OC1089LO_EIGHT_POINT_IMPOSSIBLE) THEN
  REWRITE_TAC[] THEN
  MP_TAC(SPEC `6` (ASSUME `forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1`)) THEN
  MP_TAC(SPEC `6` (ASSUME `forall i. i < 12 ==> &1 < qa i`)) THEN
  REWRITE_TAC[ARITH] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(OC1089LSSJ_APART_AT 6 5) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(OC1089LSSJ_APART_AT 6 2) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(OC1089LSSJ_APART_AT 6 5) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(OC1089LSSJ_APART_AT 6 11) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(OC1089LSSJ_APART_AT 6 11) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(OC1089LSSJ_APART_AT 6 10) THEN ASM_REWRITE_TAC[]]);;
