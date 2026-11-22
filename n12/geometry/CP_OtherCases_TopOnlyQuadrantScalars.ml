(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/TopOnlyQuadrantScalars.lean         *)
(* (N12Compact.Completion.OtherCases.TopOnlyQuadrantScalars).  Whole-quadrant*)
(* rational bounds from the four true top-only faces.  half / quarter_data   *)
(* are C1092WPS_half / C1092WPS_QUARTER_DATA; SharpPointScalars lemmas are   *)
(* OCSPS_*; TopOnlyQuadrantProfile.Data is octoqp_data.  Tag OCTOQS_.        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_TopOnlyQuadrantProfile.ml";;
needs "n12/geometry/CP_OtherCases_SharpPointScalars.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;

let OCTOQS_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC]) tms;;

let OCTOQS_POS_CANCEL = prove
 (`forall k y. &0 < k /\ &0 < k * y ==> &0 < y`,
  MESON_TAC[REAL_LT_MUL_EQ]);;

(* Lean: bounds *)
let OCTOQS_BOUNDS = prove
 (`forall d r. &0 < d /\ &0 < r /\ d pow 2 + r pow 2 = &1 /\
     &1 < d + (&11 / &25) * r /\ &1 < (&37 / &50) * d + r
     ==> &13 / &87 < C1092WPS_half d r /\ C1092WPS_half d r < &11 / &25 /\
         &2 / &3 < d /\ r < &3 / &4 /\
         &4831 / &3869 <= d + r /\ d + r < &10 / &7 /\
         &1 < d + r - (&37 / &50) * d * r /\
         r - d - &13 / &50 - (&37 / &50) * r pow 2 < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`; `&11 / &25`] OCSPS_HALF_UPPER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`d:real`; `r:real`; `&252 / &373`; `&275 / &373`; `&11 / &25`]
    OCSPS_HALF_BEFORE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C1092WPS_QUARTER_DATA) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if free_in `C1092WPS_half d r` (concl th) then MP_TAC th
                                 else NO_TAC)) THEN
  SPEC_TAC(`C1092WPS_half d r`,`z:real`) THEN GEN_TAC THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  SUBGOAL_THEN `r <= &1` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `z < &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OCTOQS_PROD_TAC [`&0 <= (z - &1) * (&1 + d)`] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + z * z` ASSUME_TAC THENL
   [MP_TAC(SPEC `z:real` REAL_LE_SQUARE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&13 / &87 < z` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < (&87 / &50) * z - &13 / &50 ==> &13 / &87 < z`) THEN
    MATCH_MP_TAC OCTOQS_POS_CANCEL THEN EXISTS_TAC `&1 - z` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - z) * ((&87 / &50) * z - &13 / &50) =
                  (&1 + z * z) * ((&37 / &50) * d + r - &1)` SUBST1_TAC THENL
     [UNDISCH_TAC `(&1 + z * z) * d = &1 - z * z` THEN
      UNDISCH_TAC `(&1 + z * z) * r = &2 * z` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  OCTOQS_PROD_TAC [`&0 <= (&275 * d - &252 * r) * (&275 * d + &252 * r)`] THEN
  SUBGOAL_THEN `&2 / &3 < d` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OCTOQS_PROD_TAC [`&0 <= (&2 / &3 - d) * (&2 / &3 + d)`] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `r < &3 / &4` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OCTOQS_PROD_TAC [`&0 <= (r - &3 / &4) * (r + &3 / &4)`] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4831 / &3869 <= d + r` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < d + r - &4831 / &3869 ==> &4831 / &3869 <= d + r`) THEN
    MATCH_MP_TAC OCTOQS_POS_CANCEL THEN EXISTS_TAC `&1 + z * z` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(&1 + z * z) * (d + r - &4831 / &3869) =
                  (&8700 / &3869) * ((z - &13 / &87) * (&37 / &50 - z))` SUBST1_TAC THENL
     [UNDISCH_TAC `(&1 + z * z) * d = &1 - z * z` THEN
      UNDISCH_TAC `(&1 + z * z) * r = &2 * z` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d + r < &10 / &7` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OCTOQS_PROD_TAC [`&0 <= (d + r - &10 / &7) * (d + r + &10 / &7)`] THEN
    MP_TAC(SPEC `d - r:real` REAL_LE_SQUARE) THEN RASM_ARITH_TAC; ALL_TAC] THEN
  OCTOQS_PROD_TAC [`&0 <= (d + r - &4831 / &3869) * (&10 / &7 - (d + r))`] THEN
  MP_TAC(SPEC `r:real` REAL_LE_SQUARE) THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: profile_bounds *)
let OCTOQS_PROFILE_BOUNDS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ octoqp_data c s u v a
     ==> &13 / &87 < C1092WPS_half c (--s) /\ C1092WPS_half c (--s) < &11 / &25 /\
         &2 / &3 < c /\ --s < &3 / &4 /\
         &4831 / &3869 <= c - s /\ c - s < &10 / &7 /\
         &1 < c - s + (&37 / &50) * c * s /\
         --s - c - &13 / &50 - (&37 / &50) * s pow 2 < &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[octoqp_data] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `--s`] OCTOQS_BOUNDS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]);;
