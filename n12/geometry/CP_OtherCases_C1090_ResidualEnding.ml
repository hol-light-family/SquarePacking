(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1090/ResidualEnding.lean           *)
(* (namespace N12Compact.Completion.OtherCases.C1090.Residual).              *)
(* C1089-REVERSE-CYCLIC-ENDING sections 7--8: the continuous residual       *)
(* ending from the strict point table c1090ro_input.  q : Fin 12 ->          *)
(* OpenSquare is qc qs qu qv qa : num -> real with the unit-normal           *)
(* hypothesis !i. i < 12 ==> qc i * qc i + qs i * qs i = &1 (as in           *)
(* ResidualOwners.ml); auxiliary OpenSquares N, R, W are 5-tuples with       *)
(* explicit unit normal and positive side.  q.translated x y is              *)
(* (c, s, u - (c * x + s * y), v - (--s * x + c * y), a)                      *)
(* (C1090RO_INSIDE_TRANSLATED); turnFrame (c, s, u, v, a) is                 *)
(* (--s, c, v, --u - a, a) (C1090RE_TURN_INSIDE).  Used:                     *)
(* C976MergedLeft.mixed_top_advance / top_only_advance (OCC976MLTT_),        *)
(* C976NegativeTop.angle / Alternative (C976NTM_ANGLE, cc976f_alternative),  *)
(* TopOnlyLeftPoint.point_original (OCTOLP_POINT_ORIGINAL),                  *)
(* OrdinaryLeftTop.ShallowTop.impossible_from_ordinary_input                 *)
(* (OLTSTP_IMPOSSIBLE_FROM_ORDINARY_INPUT), ClosedFrames.canonical_frame     *)
(* (CLF_CANONICAL_FRAME), C981CompletionCornerAdvance.upper_wall             *)
(* (C981CA_UPPER_WALL).  Tag C1090RE_.                                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1090_ResidualOwners.ml";;
needs "n12/geometry/CP_OtherCases_C976MergedLeft_TopTransfers.ml";;
needs "n12/geometry/CP_OtherCases_C976NegativeTop_Main.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/CP_C981_CornerAdvance.ml";;

(* Lean: S12.turnFrame_inside *)
let C1090RE_TURN_INSIDE = prove
 (`forall c s u v a x y. linside (--s) c v (--u - a) a x y <=> linside c s u v a x y`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* goals P k from an assumption !i. i < 12 ==> P i (or two-index forms) *)
let C1090RE_BY_FORALL_TAC =
  FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN REWRITE_TAC[ARITH] THEN NO_TAC);;

let C1090RE_SIDE_TAC =
  FIRST
   [FIRST_ASSUM ACCEPT_TAC;
    C1090RE_BY_FORALL_TAC;
    MATCH_MP_TAC(REAL_ARITH `&1 < x ==> &0 < x`) THEN C1090RE_BY_FORALL_TAC];;

let C1090RE_FOREIGN_TAC j =
  MATCH_MP_TAC C1090RO_FOREIGN THEN EXISTS_TAC j THEN
  ASM_REWRITE_TAC[ARITH] THEN NO_TAC;;

(* ~(q i) (x, y) /\ (q j) (x, y) ==> F *)
let C1090RE_CLASH_TAC i j x y =
  MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
                `qa:num->real`; i; j; x; y] C1090RO_APART_AT) THEN
  ASM_REWRITE_TAC[ARITH];;

(* an owner of q k is below the wall y <= 4 (InsideContainer) *)
let C1090RE_BOX = prove
 (`forall qc qs qu qv qa k x y. c1090ro_input qc qs qu qv qa /\ k < 12 /\
     linside (qc k) (qs k) (qu k) (qv k) (qa k) x y ==> y <= &4`,
  REWRITE_TAC[c1090ro_input; lcont] THEN MESON_TAC[]);;

(* Lean: nonnegative_northeast_impossible *)
let C1090RE_NONNEGATIVE_NORTHEAST_IMPOSSIBLE = prove
 (`forall qc qs qu qv qa cN sN uN vN aN.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090ro_input qc qs qu qv qa /\
     cN * cN + sN * sN = &1 /\ &0 < aN /\ aN = qa 6 /\
     (forall x y. linside cN sN uN vN aN x y <=> linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) x y) /\
     &0 < cN /\ &0 <= sN /\ sN <= cN
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aN = (qa:num->real) 6`)) THEN
  MP_TAC(SPEC_ALL C1090RO_TOP_ORIGIN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1090RO_NORTHWEST_UPPER_POINTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1090RO_INPUT_TAC THEN
  SUBGOAL_THEN `forall x y. linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) x y ==> y <= &4`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC C1090RE_BOX THEN
    MAP_EVERY EXISTS_TAC [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
                          `qa:num->real`; `11`; `x:real`] THEN
    ASM_REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `ldisj cN sN uN vN (qa 6) (qc 11) (qs 11) (qu 11) (qv 11) (qa 11)` ASSUME_TAC THENL
   [REWRITE_TAC[ldisj] THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC C1090RO_APART_AT THEN ASM_REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  ASM_CASES_TAC `linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&2) (&113 / &50)` THENL
   [SUBGOAL_THEN `linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&127 / &100) (&3)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC OCC976MLTT_MIXED_TOP_ADVANCE THEN
      MAP_EVERY EXISTS_TAC [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `(qa:num->real) 6`] THEN
      REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST [C1090RE_SIDE_TAC; C1090RE_FOREIGN_TAC `5`];
      ALL_TAC] THEN
    SUBGOAL_THEN `linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&7 / &5) (&3)` ASSUME_TAC THENL
     [MATCH_MP_TAC C1090RO_SEGMENT_POINT THEN
      MAP_EVERY EXISTS_TAC [`&127 / &100`; `&3`; `&2`; `&3`; `&13 / &73`] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      ALL_TAC] THEN
    C1090RE_CLASH_TAC `7` `11` `&7 / &5` `&3`;
    MP_TAC(SPEC_ALL C1090RO_NORTHEAST_OUTER_SHARP) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&6 / &5) (&3)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC OCC976MLTT_TOP_ONLY_ADVANCE THEN
      MAP_EVERY EXISTS_TAC [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `(qa:num->real) 6`] THEN
      REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST [C1090RE_SIDE_TAC; C1090RE_FOREIGN_TAC `2`;
             X_GEN_TAC `y:real` THEN DISCH_TAC THEN DISCH_TAC THEN
             MATCH_MP_TAC C1090RO_FOREIGN THEN EXISTS_TAC `10` THEN
             ASM_REWRITE_TAC[ARITH] THEN
             MATCH_MP_TAC C1090RO_RIGHT_BAR THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&7 / &5) (&3)` ASSUME_TAC THENL
     [MATCH_MP_TAC C1090RO_SEGMENT_POINT THEN
      MAP_EVERY EXISTS_TAC [`&6 / &5`; `&3`; `&2`; `&3`; `&1 / &4`] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      ALL_TAC] THEN
    C1090RE_CLASH_TAC `7` `11` `&7 / &5` `&3`]);;

(* Lean: negative_alternative *)
let C1090RE_NEGATIVE_ALTERNATIVE = prove
 (`forall qc qs qu qv qa cN sN uN vN aN.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090ro_input qc qs qu qv qa /\
     cN * cN + sN * sN = &1 /\ &0 < aN /\
     (forall x y. linside cN sN uN vN aN x y <=>
            linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&2 + x) (&3 + y))
     ==> cc976f_alternative cN sN uN vN aN`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1090RO_TOP_ORIGIN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1090RO_SOUTHEAST_EAST) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1090RO_INPUT_TAC THEN
  REWRITE_TAC[cc976f_alternative] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_CASES_TAC `linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&2) (&113 / &50)` THEN
  ASM_REWRITE_TAC[] THENL
   [X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&2 + x) (&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC C1090RO_SEGMENT_POINT THEN
      MAP_EVERY EXISTS_TAC [`&113 / &50`; `&2`; `&5 / &2`; `&2`; `(&25 / &6) * (x - &13 / &50)`] THEN
      ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
      C1090RE_FOREIGN_TAC `5`];
    MP_TAC(SPEC_ALL C1090RO_NORTHEAST_OUTER_SHARP) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC OCTOLP_POINT_ORIGINAL THEN
    REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST [C1090RE_SIDE_TAC; C1090RE_FOREIGN_TAC `11`; C1090RE_FOREIGN_TAC `2`;
           X_GEN_TAC `y:real` THEN DISCH_TAC THEN DISCH_TAC THEN
           MATCH_MP_TAC C1090RO_FOREIGN THEN EXISTS_TAC `10` THEN
           ASM_REWRITE_TAC[ARITH] THEN
           MATCH_MP_TAC C1090RO_RIGHT_BAR THEN ASM_REWRITE_TAC[]]]);;

(* Lean: shallow_top_impossible *)
let C1090RE_SHALLOW_TOP_IMPOSSIBLE = prove
 (`forall qc qs qu qv qa cW sW uW vW aW.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090ro_input qc qs qu qv qa /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\ aW = qa 11 /\
     (forall x y. linside cW sW uW vW aW x y <=> linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) x y) /\
     &0 < cW /\ sW <= &0 /\ --sW <= (&2 / &3) * cW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW = (qa:num->real) 11`)) THEN
  MP_TAC(SPEC_ALL C1090RO_ORDINARY_INPUT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`;
    `cW:real`; `sW:real`; `uW:real`; `vW:real`; `(qa:num->real) 11`] C1090RO_TOP_INPUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1090RO_INPUT_TAC THEN
  MP_TAC(SPECL (c1090ro_t7 @
    [`cW:real`; `sW:real`; `uW - (cW * &1 + sW * &2)`; `vW - (--sW * &1 + cW * &2)`; `(qa:num->real) 11`])
    OLTSTP_IMPOSSIBLE_FROM_ORDINARY_INPUT) THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [C1090RE_SIDE_TAC; C1090RE_SIDE_TAC; C1090RE_SIDE_TAC; C1090RE_SIDE_TAC;
    C1090RE_SIDE_TAC; C1090RE_SIDE_TAC; C1090RE_SIDE_TAC; C1090RE_SIDE_TAC; C1090RE_SIDE_TAC;
    C1090RE_BY_FORALL_TAC;
    REWRITE_TAC[ldisj; C1090RO_INSIDE_TRANSLATED] THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN MATCH_MP_TAC C1090RO_APART_AT THEN ASM_REWRITE_TAC[ARITH]]);;

(* N = R.translated 2 3, T = W.translated 2 3 *)
let c1090re_sub = map (subst [`(qa:num->real) 6`, `aR:real`; `(qa:num->real) 11`, `aW:real`]);;
let c1090re_n = c1090re_sub
  [`cR:real`; `sR:real`; `uR - (cR * &2 + sR * &3)`; `vR - (--sR * &2 + cR * &3)`; `aR:real`];;
let c1090re_t = c1090re_sub
  [`cW:real`; `sW:real`; `uW - (cW * &2 + sW * &3)`; `vW - (--sW * &2 + cW * &3)`; `aW:real`];;
let c1090re_tt = c1090re_sub
  [`--sW:real`; `cW:real`; `vW - (--sW * &2 + cW * &3)`; `--(uW - (cW * &2 + sW * &3)) - aW`;
   `aW:real`];;

(* the hypotheses of C976NTM_ANGLE / C981CA_UPPER_WALL in negative_northeast_impossible *)
let C1090RE_ANGLE_SIDE_TAC =
  REWRITE_TAC[ldisj; C1090RE_TURN_INSIDE; C1090RO_INSIDE_TRANSLATED] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  FIRST
   [C1090RE_SIDE_TAC;
    UNDISCH_TAC `cW * cW + sW * sW = &1` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `cR * cR + sR * sR = &1` THEN REAL_ARITH_TAC;
    C1090RE_FOREIGN_TAC `10`; C1090RE_FOREIGN_TAC `7`;
    REPEAT GEN_TAC THEN MATCH_MP_TAC C1090RO_APART_AT THEN ASM_REWRITE_TAC[ARITH] THEN NO_TAC;
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&3 + y <= &4 ==> y <= &1`) THEN MATCH_MP_TAC C1090RE_BOX THEN
    MAP_EVERY EXISTS_TAC [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
                          `qa:num->real`; `11`; `&2 + x`] THEN
    ASM_REWRITE_TAC[ARITH] THEN NO_TAC;
    RASM_ARITH_TAC];;

(* Lean: negative_northeast_impossible *)
let C1090RE_NEGATIVE_NORTHEAST_IMPOSSIBLE = prove
 (`forall qc qs qu qv qa cR sR uR vR aR.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090ro_input qc qs qu qv qa /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\ aR = qa 6 /\
     (forall x y. linside cR sR uR vR aR x y <=> linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) x y) /\
     &0 < cR /\ sR < &0 /\ --sR <= cR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aR = (qa:num->real) 6`)) THEN
  MP_TAC(SPEC_ALL C1090RO_TOP_ORIGIN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1090RO_NORTHWEST_UPPER_POINTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL ([`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
                 `qa:num->real`] @ c1090re_n) C1090RE_NEGATIVE_ALTERNATIVE) THEN
  ASM_REWRITE_TAC[C1090RO_INSIDE_TRANSLATED] THEN DISCH_TAC THEN
  C1090RO_INPUT_TAC THEN
  MP_TAC(SPECL [`(qc:num->real) 11`; `(qs:num->real) 11`; `(qu:num->real) 11`;
                `(qv:num->real) 11`; `(qa:num->real) 11`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1090RE_SIDE_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW = (qa:num->real) 11`)) THEN
  ASM_CASES_TAC `&0 <= sW` THENL
   [MP_TAC(SPECL (c1090re_n @ c1090re_t @ [`--sR:real`]) C976NTM_ANGLE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY C1090RE_ANGLE_SIDE_TAC THEN
      MATCH_MP_TAC C981CA_UPPER_WALL THEN REPEAT CONJ_TAC THEN C1090RE_ANGLE_SIDE_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `abs sW <= cW` THEN UNDISCH_TAC `&0 <= sW` THEN REAL_ARITH_TAC;
    MP_TAC(SPECL (c1090re_n @ c1090re_tt @ [`--sR:real`]) C976NTM_ANGLE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY C1090RE_ANGLE_SIDE_TAC THEN
      MATCH_MP_TAC C981CA_UPPER_WALL THEN REPEAT CONJ_TAC THEN C1090RE_ANGLE_SIDE_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC C1090RE_SHALLOW_TOP_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
      `qa:num->real`; `cW:real`; `sW:real`; `uW:real`; `vW:real`; `(qa:num->real) 11`] THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC]);;

(* Lean: impossible *)
let C1090RE_IMPOSSIBLE = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090ro_input qc qs qu qv qa
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`(qc:num->real) 6`; `(qs:num->real) 6`; `(qu:num->real) 6`;
                `(qv:num->real) 6`; `(qa:num->real) 6`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [C1090RO_INPUT_TAC THEN CONJ_TAC THEN C1090RE_SIDE_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aN = (qa:num->real) 6`)) THEN
  ASM_CASES_TAC `&0 <= sN` THENL
   [MATCH_MP_TAC C1090RE_NONNEGATIVE_NORTHEAST_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
      `qa:num->real`; `cN:real`; `sN:real`; `uN:real`; `vN:real`; `(qa:num->real) 6`];
    MATCH_MP_TAC C1090RE_NEGATIVE_NORTHEAST_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
      `qa:num->real`; `cN:real`; `sN:real`; `uN:real`; `vN:real`; `(qa:num->real) 6`]] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `abs sN <= cN` THEN UNDISCH_TAC `&0 < cN` THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;
