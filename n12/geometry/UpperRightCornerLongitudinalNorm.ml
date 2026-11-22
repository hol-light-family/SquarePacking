(* ========================================================================= *)
(* Port of Compact/Geometry/UpperRightCornerLongitudinalNorm.lean            *)
(* (Jatloe, N12-jatloe; namespace N12Compact.UpperRightCornerLongitudinalNorm)*)
(* Continuous norm certificate for the top-wall longitudinal support: a     *)
(* half-angle quartic lying below its endpoint chord.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

(* Lean: quartic (private definition) *)
let urcln_quartic = new_definition
 `urcln_quartic (z:real) =
    -- &39551 - &315000 * z + &929102 * z pow 2 - &885000 * z pow 3 +
    &1720449 * z pow 4`;;

(* Lean: quartic_nonpos (private) *)
let URCLN_QUARTIC_NONPOS = prove
 (`forall z. &0 <= z /\ z <= &3 / &7 ==> urcln_quartic z <= &0`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `q = &929102 - &885000 * (&3 / &7 + z) +
                  &1720449 * ((&3 / &7) pow 2 + (&3 / &7) * z + z pow 2)` THEN
  SUBGOAL_THEN `&0 <= q` ASSUME_TAC THENL
  [EXPAND_TAC "q" THEN NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (z * (&3 / &7 - z)) * q` MP_TAC THENL
  [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  EXPAND_TAC "q" THEN REWRITE_TAC[urcln_quartic] THEN
  UNDISCH_TAC `&0 <= z` THEN UNDISCH_TAC `z <= &3 / &7` THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT DISCH_TAC THEN
  NLIN_TAC ~deg2:false []);;

let URCLN_NONPOS_BY_POS = prove
 (`forall e k q. &0 < k /\ k * e = q /\ q <= &0 ==> e <= &0`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: residual_nonpos *)
let URCLN_RESIDUAL_NONPOS = prove
 (`forall c s. c977cc_normal c s
         ==> &261 / &100 - (&88 / &25) * c - (&6 / &5) * s +
             (&187949 / &250000) * c pow 2 + (&57 / &100) * c * s <= &0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  UNDISCH_TAC `c977cc_normal c s` THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s / (&1 + c) /\ s / (&1 + c) <= &3 / &7` STRIP_ASSUME_TAC THENL
  [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + (s / (&1 + c)) pow 2) * c = &1 - (s / (&1 + c)) pow 2 /\
                (&1 + (s / (&1 + c)) pow 2) * s = &2 * (s / (&1 + c))`
  STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
   SUBGOAL_THEN `~(&1 + c = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC(SPEC `s / (&1 + c)` URCLN_QUARTIC_NONPOS) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`(&1 + (s / (&1 + c)) pow 2) * c = &1 - (s / (&1 + c)) pow 2`;
    `(&1 + (s / (&1 + c)) pow 2) * s = &2 * (s / (&1 + c))`] THEN
  SPEC_TAC(`s / (&1 + c)`,`z:real`) THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `(&250000 * (&1 + z pow 2) pow 2) *
    (&261 / &100 - (&88 / &25) * c - (&6 / &5) * s +
     (&187949 / &250000) * c pow 2 + (&57 / &100) * c * s) = urcln_quartic z`
  ASSUME_TAC THENL
  [REWRITE_TAC[urcln_quartic] THEN
   MAP_EVERY UNDISCH_TAC
    [`(&1 + z pow 2) * c = &1 - z pow 2`; `(&1 + z pow 2) * s = &2 * z`] THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &250000 * (&1 + z pow 2) pow 2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
   MATCH_MP_TAC REAL_POW_LT THEN
   MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC URCLN_NONPOS_BY_POS THEN
  MAP_EVERY EXISTS_TAC [`&250000 * (&1 + z pow 2) pow 2`; `urcln_quartic z`] THEN
  ASM_REWRITE_TAC[]);;
