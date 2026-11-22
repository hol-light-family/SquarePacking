(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCrosspointBoundaryEndpoints.lean      *)
(* (N12Compact.C1092MPPMCrosspointSupport).  Exact lower endpoint polynomial  *)
(* in STEEP-POSITIVE-BOUNDARY-SCALARS section 7.  Quarter: c1092mcs_quarter;  *)
(* the half-angle z = r / (1 + h) is C1092WPS_half h r.                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointSupportScalars.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;

(* Lean: lower_identity (private) *)
let C1092MCBE_LOWER_IDENTITY = prove
 (`forall h r z. h = (&1 - z pow 2) / (&1 + z pow 2) /\ r = &2 * z / (&1 + z pow 2)
     ==> (h + &2 * r - &2 + (&3496 / &3125) * h pow 2 -
          (&1 + &11387 / &12500) * h * r + (&14 / &25) * r pow 2 - &1 / &3125) *
         (&1 + z pow 2) pow 2 =
         (&1 - &3 * z) * (&3920 * z pow 3 - &14989 * z pow 2 + &3333 * z + &740) / &6250`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(&1 + z pow 2 = &0)` ASSUME_TAC THENL
   [MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h * (&1 + z pow 2) = &1 - z pow 2 /\ r * (&1 + z pow 2) = &2 * z`
    MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN UNDISCH_TAC `~(&1 + z pow 2 = &0)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC REAL_RING);;

(* Lean: lower_endpoint_D *)
let C1092MCBE_LOWER_ENDPOINT_D = prove
 (`forall h r. c1092mcs_quarter h r /\ &4 / &5 <= h /\ r <= &3 / &5
     ==> &1 / &3125 <= h + &2 * r - &2 + (&3496 / &3125) * h pow 2 -
                       (&1 + &11387 / &12500) * h * r + (&14 / &25) * r pow 2`,
  REWRITE_TAC[c1092mcs_quarter] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`C1092WPS_half h r`,`z:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `z <= &1 / &3` ASSUME_TAC THENL
   [MP_TAC(SPECL [`z:real`; `h - &4 / &5`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `z * (&1 + h) = r` THEN UNDISCH_TAC `r <= &3 / &5` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &3920 * z pow 3 - &14989 * z pow 2 + &3333 * z + &740` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= &1 / &3 - z` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= (&1 / &3 - z) pow 3 /\ &0 <= z * (&1 / &3 - z) pow 2 /\
      &0 <= z pow 2 * (&1 / &3 - z) /\ &0 <= z pow 3` MP_TAC THENL
     [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(h + &2 * r - &2 + (&3496 / &3125) * h pow 2 -
     (&1 + &11387 / &12500) * h * r + (&14 / &25) * r pow 2 - &1 / &3125) *
    (&1 + z pow 2) pow 2 =
    (&1 - &3 * z) * (&3920 * z pow 3 - &14989 * z pow 2 + &3333 * z + &740) / &6250`
    ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + z pow 2) * h = &1 - z pow 2` THEN
    UNDISCH_TAC `(&1 + z pow 2) * r = &2 * z` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`&1 - &3 * z`; `&3920 * z pow 3 - &14989 * z pow 2 + &3333 * z + &740`]
    REAL_LE_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 + z pow 2) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`(&1 + z pow 2) pow 2`;
    `--(h + &2 * r - &2 + (&3496 / &3125) * h pow 2 -
       (&1 + &11387 / &12500) * h * r + (&14 / &25) * r pow 2 - &1 / &3125)`] REAL_LT_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RNEG] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_REAL_ARITH_TAC);;
