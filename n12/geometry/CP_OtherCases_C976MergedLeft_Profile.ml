(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C976MergedLeft/Profile.lean        *)
(* (namespace N12Compact.Completion.OtherCases.C976MergedLeft).  The        *)
(* original top segment forces the positive-angle profile (section 3).      *)
(* The square q is (c, s, u, v, a) with its OpenSquare invariants;          *)
(* Input / Profile are occ976ml_input / occ976ml_profile (Inputs.ml);       *)
(* CommonCases.CanonicalScalars.bounds is CCCS_BOUNDS, SegmentCorner.       *)
(* crossing_order is SEGC_CROSSING_ORDER, small_corner_margin / top_span    *)
(* are OCC976MLS_SMALL_CORNER_MARGIN / OCC976MLS_TOP_SPAN.  Tag OCC976MLP_. *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C976MergedLeft_Scalars.ml";;
needs "n12/geometry/SegmentCorner.ml";;

let OCC976MLP_TOP = `forall x. &27 / &100 <= x ==> x <= &37 / &50 ==> ~linside c s u v a x (&1)`;;

(* an instance of the top bar, unfolded *)
let OCC976MLP_TOP_TAC x =
  MP_TAC(SPEC x (ASSUME OCC976MLP_TOP)) THEN REWRITE_TAC[linside] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[];;

(* Lean: positive_profile *)
let OCC976MLP_POSITIVE_PROFILE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ occ976ml_input c s u v a /\
               &0 < c /\ &0 <= s /\ s <= c
     ==> occ976ml_profile c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[occ976ml_input; occ976ml_profile] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; STRIP_TAC] THEN
  MAP_EVERY (fun t -> MP_TAC (ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
    [`linside c s u v a (--(&43 / &500)) (&0)`; `linside c s u v a (&13 / &20) (&7 / &20)`;
     `linside c s u v a (&0) (&13 / &50)`] THEN
  SUBGOAL_THEN `--(&1 / &2) * s <= v` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~linside c s u v a (&1 / &2) (&0)`) THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= c` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~linside c s u v a (&0) (&1)`) THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(&37 / &50) * s + c < v + a` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= (&37 / &50) * c + s` ASSUME_TAC THENL
   [OCC976MLP_TOP_TAC `&37 / &50` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&38 / &65) * c < s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `v + a <= c - (&27 / &100) * s` ASSUME_TAC THENL
     [OCC976MLP_TOP_TAC `&27 / &100` THEN RASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`--(u + a)`; `--u`; `v:real`; `v + a`; `--((&37 / &50) * c + s)`; `c - (&37 / &50) * s`;
                  `--((&27 / &100) * c + s)`; `c - (&27 / &100) * s`] SEGC_CROSSING_ORDER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
      X_GEN_TAC `z:real` THEN REPEAT STRIP_TAC THEN
      OCC976MLP_TOP_TAC `&37 / &50 - (&47 / &100) * z` THEN RASM_ARITH_TAC;
      DISCH_TAC] THEN
    SUBGOAL_THEN `s * (u + a) + c * (v + a) <= &1` ASSUME_TAC THENL
     [POP_ASSUM MP_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < s * ((u + a) - ((&13 / &20) * c + (&7 / &20) * s))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < c * (v + a + (&1 / &2) * s - &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `s:real`] OCC976MLS_SMALL_CORNER_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; DISCH_TAC] THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OCC976MLS_TOP_SPAN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `u + a <= (&27 / &100) * c + s` ASSUME_TAC THENL
   [OCC976MLP_TOP_TAC `&27 / &100` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;
