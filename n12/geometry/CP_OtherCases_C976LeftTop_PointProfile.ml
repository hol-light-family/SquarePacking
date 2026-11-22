(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976LeftTop/PointProfile.lean       *)
(* (N12Compact.Completion.OtherCases.C976LeftTop.UpperPoints).               *)
(* C976-LEFT-UPPER-POINTS section 2.  Square q is c s u v a; Input / Profile *)
(* are occ976lt_input / occ976lt_profile; small_corner_margin is             *)
(* OCC976PS_SMALL_CORNER_MARGIN; sixthSlopeSine is OLTSM_SIXTHSLOPESINE;     *)
(* SegmentCorner.crossing_order is SEGC_CROSSING_ORDER;                      *)
(* CanonicalProjection.after is CCCP_AFTER.  Tag OCC976PP_.                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_PointSign.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryLeftTop_ScalarMargins.ml";;
needs "n12/geometry/SegmentCorner.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;

let OCC976PP_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

let OCC976PP_TOP_TAC x =
  FIRST_ASSUM(MP_TAC o SPEC x o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `&11 / &25`)) (concl th))) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

(* Lean: positive_profile *)
let OCC976PP_POSITIVE_PROFILE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     occ976lt_input c s u v a /\ &0 < c /\ &0 <= s /\ s <= c
     ==> occ976lt_profile c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[occ976lt_input; occ976lt_profile] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c pow 2 + s pow 2 = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY (fun tm -> MP_TAC(ASSUME tm) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside c s u v a (--(&43 / &500)) (&0)`;
    `linside c s u v a (&13 / &20) (&7 / &20)`;
    `linside c s u v a (&0) (&13 / &50)`] THEN
  SUBGOAL_THEN `--(&1 / &2) * s <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCC976PP_MISS_TAC `~linside c s u v a (&1 / &2) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCC976PP_MISS_TAC `~linside c s u v a (&0) (&1)`; ALL_TAC] THEN
  SUBGOAL_THEN `--(&27 / &100) * s - (&1 / &25) * c <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCC976PP_MISS_TAC `~linside c s u v a (&27 / &100) (--(&1 / &25))`; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(&37 / &50) * s + c < v + a` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= (&37 / &50) * c + s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN OCC976PP_TOP_TAC `&37 / &50`; ALL_TAC] THEN
  SUBGOAL_THEN `(&21 / &65) * c < s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `v + a <= c - (&11 / &25) * s` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN OCC976PP_TOP_TAC `&11 / &25`;
      ALL_TAC] THEN
    MP_TAC(SPECL [`--(u + a)`; `--u:real`; `v:real`; `v + a`;
                  `--((&37 / &50) * c + s)`; `c - (&37 / &50) * s`;
                  `--((&11 / &25) * c + s)`; `c - (&11 / &25) * s`] SEGC_CROSSING_ORDER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
      X_GEN_TAC `z:real` THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `&37 / &50 - (&3 / &10) * z` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `&11 / &25`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[linside] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `s * (u + a) + c * (v + a) <= &1` ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `s:real`] OCC976PS_SMALL_CORNER_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `&0 < s * ((u + a) - (c * &13 / &20 + s * &7 / &20)) /\
                  &0 < c * (v + a + (&1 / &2) * s - &1)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OLTSM_SIXTHSLOPESINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `u + a <= (&11 / &25) * c + s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN OCC976PP_TOP_TAC `&11 / &25`; ALL_TAC] THEN
  SUBGOAL_THEN `s < (&3 / &4) * c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `&4 / &5`; `&3 / &5`; `&26 / &25`; `&27 / &100`]
      CCCP_AFTER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
