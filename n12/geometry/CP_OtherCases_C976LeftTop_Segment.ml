(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976LeftTop/Segment.lean            *)
(* (namespace N12Compact.Completion.OtherCases.C976LeftTop).  Section 4: the *)
(* whole original lower segment forces one weak lower support.              *)
(* LeftInput: c976lti_left; Scalars.a0 / b0: c976lts_a0 / c976lts_b0;        *)
(* angle_upper: C976LTI_ANGLE_UPPER; SegmentCorner.crossing_order:          *)
(* SEGC_CROSSING_ORDER.  N = (c, s, u, v, a), N.unit_normal explicit.       *)
(* Tag C976LTSG_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/SegmentCorner.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_Inputs.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_Scalars.ml";;

let C976LTSG_LIN = NLIN_TAC ~deg2:false [];;
let C976LTSG_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C976LTSG_LIN; ALL_TAC];;
let C976LTSG_HAVE tm tac = SUBGOAL_THEN tm ASSUME_TAC THENL [tac; ALL_TAC];;

(* Lean: segment_support *)
let C976LTSG_SEGMENT_SUPPORT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ c976lti_left c s u v a /\ (&1 / &3) * c <= s
     ==> c976lts_a0 c s * u + c976lts_b0 c s * v >= --(&39 / &625)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C976LTI_ANGLE_UPPER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `c976lti_left c s u v a` THEN REWRITE_TAC[c976lti_left] THEN
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside; REAL_MUL_RZERO; REAL_ADD_LID; REAL_ADD_RID]) THEN
  POP_ASSUM (LABEL_TAC "segment") THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) then STRIP_ASSUME_TAC th
                                  else failwith "")) THEN
  REWRITE_TAC[c976lts_a0; c976lts_b0; real_ge] THEN
  C976LTSG_HAVE `&0 < (&13 / &100) * c + (&6 / &25) * s` C976LTSG_LIN THEN
  C976LTSG_HAVE `&0 < (&6 / &25) * c - (&13 / &100) * s` C976LTSG_LIN THEN
  C976LTSG_HAVE `(&3 * c + s) pow 2 <= &10` (NLIN_TAC [SQ_NONNEG `c - &3 * s`]) THEN
  C976LTSG_HAVE `(&113 / &100) * c - (&6 / &25) * s <= (&63 / &200) * (&3 * c + s)`
    C976LTSG_LIN THEN
  C976LTSG_HAVE `(&63 / &200) * (&3 * c + s) < &1`
    (NLIN_TAC [SQ_NONNEG `(&63 / &200) * (&3 * c + s) - &1`]) THEN
  (* E = (uE, vE), F = (uF, vF) *)
  C976LTSG_HAVE `v < (&6 / &25) * s - (&13 / &100) * c` C976LTSG_LIN THEN
  C976LTSG_HAVE `(&6 / &25) * s - (&13 / &100) * c < v + a` C976LTSG_LIN THEN
  C976LTSG_HAVE `--(&6 / &25) * c - (&13 / &100) * s < u + a` C976LTSG_LIN THEN
  C976LTSG_HAVE `--(&6 / &25) * c - (&13 / &100) * s <= u`
    (REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
     REMOVE_THEN "segment" (MP_TAC o SPEC `&0`) THEN
     REWRITE_TAC[REAL_POS; linside] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
     REWRITE_TAC[TAUT `(~p ==> false) <=> p`] THEN REPEAT CONJ_TAC THEN C976LTSG_LIN) THEN
  C976LTSG_HAVE `--(&13 / &50) * s < u + a` C976LTSG_LIN THEN
  C976LTSG_HAVE `--(&13 / &50) * c < v + a` C976LTSG_LIN THEN
  ASM_CASES_TAC `--(&13 / &50) * s <= u` THENL
   [C976LTSG_PROD `&0 <= ((&13 / &100) * c + (&6 / &25) * s) * (u - --(&13 / &50) * s)` THEN
    C976LTSG_PROD `&0 <= ((&6 / &25) * c - (&13 / &100) * s) *
                         (v - (--(&27 / &100) * s - (&1 / &25) * c))` THEN
    C976LTSG_PROD `&0 <= ((&3 / &4) * c - s) *
                         ((&467 / &5000) * c - (&351 / &10000) * (s + (&3 / &4) * c))` THEN
    C976LTSG_HAVE `&0 < c pow 2` (MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]) THEN
    C976LTSG_HAVE `&0 < (&33 / &625) * c pow 2 - (&467 / &5000) * c * s + (&351 / &10000) * s pow 2`
      C976LTSG_LIN THEN
    C976LTSG_LIN;
    C976LTSG_HAVE `u < --(&13 / &50) * s` C976LTSG_LIN THEN
    C976LTSG_HAVE `--(&13 / &50) * c <= v`
      (REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
       REMOVE_THEN "segment" (MP_TAC o SPEC `&1`) THEN
       REWRITE_TAC[REAL_POS; REAL_LE_REFL; linside] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
       REWRITE_TAC[TAUT `(~p ==> false) <=> p`] THEN REPEAT CONJ_TAC THEN C976LTSG_LIN) THEN
    MP_TAC(SPECL [`u:real`; `u + a:real`; `--(v + a):real`; `--v:real`;
                  `--(&6 / &25) * c - (&13 / &100) * s`;
                  `--((&6 / &25) * s - (&13 / &100) * c)`;
                  `--(&13 / &50) * s`; `--(--(&13 / &50) * c)`] SEGC_CROSSING_ORDER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [C976LTSG_LIN; C976LTSG_LIN; C976LTSG_LIN;
        X_GEN_TAC `t:real` THEN DISCH_TAC THEN DISCH_TAC THEN
        REMOVE_THEN "segment" (MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[linside; CONTRAPOS_THM] THEN STRIP_TAC THEN
        REPEAT CONJ_TAC THEN C976LTSG_LIN];
      DISCH_TAC THEN C976LTSG_LIN]]);;

(* Lean: upperU_strict *)
let C976LTSG_UPPERU_STRICT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ c976lti_left c s u v a /\ (&1 / &3) * c <= s
     ==> c976lts_a0 c s + c976lts_b0 c s * (&1 - c) - &39 / &625 <
         c976lts_a0 c s * (u + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C976LTSG_SEGMENT_SUPPORT) THEN
  ASM_REWRITE_TAC[real_ge] THEN DISCH_TAC THEN
  UNDISCH_TAC `c976lti_left c s u v a` THEN REWRITE_TAC[c976lti_left] THEN STRIP_TAC THEN
  C976LTSG_HAVE `&0 < c976lts_a0 c s` (REWRITE_TAC[c976lts_a0] THEN C976LTSG_LIN) THEN
  C976LTSG_HAVE `&0 < c976lts_b0 c s` (REWRITE_TAC[c976lts_b0] THEN C976LTSG_LIN) THEN
  C976LTSG_PROD `&0 <= c976lts_b0 c s * (c - (v + a))` THEN
  C976LTSG_PROD `&0 < (a - &1) * (c976lts_a0 c s + c976lts_b0 c s)` THEN
  C976LTSG_LIN);;
