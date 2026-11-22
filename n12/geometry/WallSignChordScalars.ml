(* ========================================================================= *)
(* Port of Compact/Geometry/WallSignChordScalars.lean                        *)
(* (N12Compact.WallSignChord).  Exact scalar comparisons from                *)
(* C1092-WALL-SIGN-CHORD, Theorem 1.  Purely scalar.                         *)
(* (The Lean imports S12.ShortCluster.Projections and S12.WallGeometry are   *)
(* not used by any statement or proof here.)                                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: canonical_bounds *)
let WSCS_CANONICAL_BOUNDS = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1
         ==> &7 / &10 < c /\ c <= &1 /\ &1 + &4 / &5 * c * s <= c + s /\
             &1 - &3 / &5 * s pow 2 <= c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c - &1`; SQ_NONNEG `c - s:real`]
   [`&0 <= (c - s) * (c + s)`; `&7 / &10 < c`; `c <= &1`; `&0 <= c * s`;
    `&1 <= c + s`; `c + s <= &3 / &2`;
    `&0 <= (&3 / &2 - (c + s)) * (c + s - &1)`;
    `&0 <= (&1 - c) * (&3 * c - &2)`] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: gap_nonnegative (private) *)
let WSCS_GAP_NONNEGATIVE = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1
         ==> &0 <= &1 + c * (c + s) - &2 * c - &39 / &50 * s /\
             (&0 < s ==> &0 < &1 + c * (c + s) - &2 * c - &39 / &50 * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `z = s / (&1 + c)` THEN
  SUBGOAL_THEN `z * (&1 + c) = s` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= z` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s * z = &1 - c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN EXISTS_TAC `&1 + c` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `z * (&1 + c) = s` THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + z pow 2) * c = &1 - z pow 2 /\ (&1 + z pow 2) * s = &2 * z`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    UNDISCH_TAC `z * (&1 + c) = s` THEN UNDISCH_TAC `s * z = &1 - c` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &100 * z pow 3 - &89 * z pow 2 + &11` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (z - &89 / &150) pow 2 * (z + &89 / &300)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `&0 <= z` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 + c * (c + s) - &2 * c - &39 / &50 * s) * (&25 * (&1 + z pow 2) pow 2) =
    z * (&100 * z pow 3 - &89 * z pow 2 + &11)` ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + z pow 2) * c = &1 - z pow 2` THEN
    UNDISCH_TAC `(&1 + z pow 2) * s = &2 * z` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &25 * (&1 + z pow 2) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN
    MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN
    EXISTS_TAC `&25 * (&1 + z pow 2) pow 2` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 < z` ASSUME_TAC THENL
     [EXPAND_TAC "z" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN
    EXISTS_TAC `&25 * (&1 + z pow 2) pow 2` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[]]);;

(* Lean: wall_gaps *)
let WSCS_WALL_GAPS = prove
 (`forall c s r. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ r <= &39 / &100
           ==> &0 <= &1 + c * (c + s) - &2 * c - &2 * r * s /\
               &0 < &1 + s * (c + s) - &2 * s - &2 * r * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] WSCS_GAP_NONNEGATIVE) THEN
  MP_TAC(SPECL [`s:real`; `c:real`] WSCS_GAP_NONNEGATIVE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= s * (&39 / &100 - r)`; `&0 <= c * (&39 / &100 - r)`] THEN
  CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

(* Lean: quadratic_margin *)
let WSCS_QUADRATIC_MARGIN = prove
 (`forall c s. &0 < c /\ &0 <= s
         ==> &0 < &11 / &100 * c pow 2 + &3 / &20 * s pow 2 - &1 / &4 * c * s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_ADD_RID] THEN
    NLIN_TAC [];
    SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC [SQ_NONNEG `&22 * c - &25 * s`]]);;

(* Lean: quadratic_margin_transpose *)
let WSCS_QUADRATIC_MARGIN_TRANSPOSE = prove
 (`forall c s. &0 < c
         ==> &0 < &3 / &20 * c pow 2 + &11 / &100 * s pow 2 - &1 / &4 * c * s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  NLIN_TAC [SQ_NONNEG `&22 * s - &25 * c`; SQ_NONNEG `s:real`]);;

(* Lean: negative_u_margin *)
let WSCS_NEGATIVE_U_MARGIN = prove
 (`forall c s r. &0 < c /\ &0 < s /\ &1 - &3 / &5 * s pow 2 <= c /\ &11 / &50 <= r /\
           r * s < &43 / &500 * c
           ==> &1 < c + &43 / &500 * s pow 2 + r * c * s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 < r`; `&43 / &500 * &257 / &500 < r * r`;
    `&0 < (&43 / &500 * c - r * s) * &257 / &500`;
    `&0 < (r * r - &43 / &500 * &257 / &500) * c`;
    `&0 < r * (r * c - &257 / &500 * s)`;
    `&0 < r * c - &257 / &500 * s`;
    `&0 < s * (r * c - &257 / &500 * s)`] THEN
  NLIN_TAC ~deg2:false []);;
