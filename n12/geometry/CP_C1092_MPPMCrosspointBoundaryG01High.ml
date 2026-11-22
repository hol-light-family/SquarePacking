(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCrosspointBoundaryG01High.lean        *)
(* (N12Compact.C1092MPPMCrosspointSupport), BOUNDARY-SCALARS section 4.2.   *)
(* Normal is c977cc_normal; G01, kC, deltaC, C0, FE, Quarter are c1092mcs_*; *)
(* P, Q, FE_after, coefficient_bounds are c1092mcbc_ / C1092MCBC_*; steep    *)
(* bounds C1092G10_STEEP_BOUNDS; norm_lt C1092NPP_NORM_LT; quarter_data      *)
(* C1092WPS_QUARTER_DATA; UnitCircleChord CCUCC_*.                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryCoefficients.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryG10Clamp.ml";;
needs "n12/geometry/CP_C1092_MPPMNonpositivePredecessorScalars.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;

let C1092G01H_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092G01H_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092G01H_LP_TAC; ALL_TAC];;

let C1092G01H_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

(* Lean: highQuartic (private definition) *)
let c1092g01h_highQuartic = new_definition
 `c1092g01h_highQuartic (c:real) (s:real) (A:real) (B:real) (z:real) =
    (s - B) + &2 * (c + s - A) * z + (&4 * c - &2 * s) * z pow 2 -
    &2 * (c + s + A) * z pow 3 + (s + B) * z pow 4`;;

(* Lean: coefficients (private); A, B written out *)
let C1092G01H_COEFFICIENTS = prove
 (`forall c s d t. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t
     ==> &2 * c + (&543 / &500) * s - &1 + s * c1092mcbc_P d t <= c + s /\
         s * (&2 - c1092mcbc_Q d t) <= s /\
         (&2 * c + (&543 / &500) * s - &1 + s * c1092mcbc_P d t) +
         s * (&2 - c1092mcbc_Q d t) <= &2 * c + (&549 / &250) * s - &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MCBC_COEFFICIENT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092G01H_NORMAL_TAC THEN
  MP_TAC(SPECL [`&4 / &5`; `&3 / &5`; `c:real`; `s:real`; `&3`; `&1`] CCUCC_DECREASING) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN RASM_ARITH_TAC;
                  DISCH_TAC] THEN
  C1092G01H_PROD `&0 <= s * (&213 / &1000 - c1092mcbc_P d t)` THEN
  C1092G01H_PROD `&0 <= s * (&1 - (&2 - c1092mcbc_Q d t))` THEN
  C1092G01H_PROD `&0 <= s * (&111 / &100 - (c1092mcbc_P d t + &2 - c1092mcbc_Q d t))` THEN
  C1092G01H_LP_TAC);;

(* Lean: quartic_nonnegative (private) *)
let C1092G01H_QUARTIC_NONNEGATIVE = prove
 (`forall c s A B z. c977cc_normal c s /\ &3 / &5 <= s /\ A <= c + s /\ B <= s /\
               A + B <= &2 * c + (&549 / &250) * s - &1 /\ &0 <= z /\ z <= &5 / &12
               ==> &0 <= c1092g01h_highQuartic c s A B z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092G10_STEEP_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092G01H_NORMAL_TAC THEN
  ABBREV_TAC `b0 = s - B` THEN
  ABBREV_TAC `b1 = b0 + (c + s - A) * (&5 / &12) / &2` THEN
  ABBREV_TAC `b2 = b0 + (c + s - A) * (&5 / &12) + (&4 * c - &2 * s) * (&5 / &12) pow 2 / &6` THEN
  ABBREV_TAC `b3 = b0 + (&3 / &2) * (c + s - A) * (&5 / &12) + (&2 * c - s) * (&5 / &12) pow 2 -
                   (c + s + A) * (&5 / &12) pow 3 / &2` THEN
  ABBREV_TAC `b4 = c1092g01h_highQuartic c s A B (&5 / &12)` THEN
  SUBGOAL_THEN `&0 <= b0 /\ &0 <= b1 /\ &0 <= b2 /\ &0 <= b3` STRIP_ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["b3"; "b2"; "b1"; "b0"] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
   C1092G01H_LP_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`&411 / &1000`; `&557 / &1000`; `c:real`; `s:real`; `&7 / &10`] C1092NPP_NORM_LT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  SUBGOAL_THEN `b4 = (&1 + (&5 / &12) pow 2) pow 2 *
      ((c - s) * (&120 / &169) pow 2 + (c + s) * (&120 / &169) * (&119 / &169) + s -
       A * (&120 / &169) - B * (&119 / &169))` ASSUME_TAC THENL
  [EXPAND_TAC "b4" THEN REWRITE_TAC[c1092g01h_highQuartic] THEN
   CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= b4` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN C1092G01H_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&5 / &12) pow 4 * c1092g01h_highQuartic c s A B z =
      b0 * (&5 / &12 - z) pow 4 + &4 * b1 * z * (&5 / &12 - z) pow 3 +
      &6 * b2 * z pow 2 * (&5 / &12 - z) pow 2 + &4 * b3 * z pow 3 * (&5 / &12 - z) +
      b4 * z pow 4` ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["b4"; "b3"; "b2"; "b1"; "b0"] THEN
   REWRITE_TAC[c1092g01h_highQuartic] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&5 / &12) pow 4 * c1092g01h_highQuartic c s A B z` MP_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
   REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
   TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV(LAND_CONV REAL_RAT_REDUCE_CONV)) THEN REAL_ARITH_TAC);;

(* the half-angle identity of G01_high_nonnegative *)
let C1092G01H_HIGH_IDENTITY = prove
 (`forall c s A B z h r. (&1 + z pow 2) * r = &1 - z pow 2 /\ (&1 + z pow 2) * h = &2 * z
     ==> c1092g01h_highQuartic c s A B z =
         (&1 + z pow 2) pow 2 *
         ((c - s) * h pow 2 + (c + s) * h * r + s - A * h - B * r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + z pow 2` ASSUME_TAC THENL
  [MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h = (&2 * z) / (&1 + z pow 2) /\ r = (&1 - z pow 2) / (&1 + z pow 2)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
  [ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1092g01h_highQuartic] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `&0 < x ==> ~(x = &0)`)) THEN
  CONV_TAC REAL_FIELD);;

(* Lean: G01_high_nonnegative *)
let C1092G01H_G01_HIGH_NONNEGATIVE = prove
 (`forall c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\
                 c1092mcs_quarter h r /\ h <= r
                 ==> &0 <= c1092mcs_G01 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092G01H_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092G01H_NORMAL_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcs_quarter] o
    check (fun th -> can (term_match [] `c1092mcs_quarter x y`) (concl th))) THEN
  C1092G01H_PROD `&0 <= (c - s) * r` THEN C1092G01H_PROD `&0 <= s * (r - h)` THEN
  C1092G01H_PROD `&0 <= (d - t) * r` THEN C1092G01H_PROD `&0 <= t * (r - h)` THEN
  SUBGOAL_THEN `&0 <= c1092mcs_deltaC c s h r /\ &0 <= c1092mcs_deltaE d t h r`
  STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[c1092mcs_deltaC; c1092mcs_deltaE] THEN C1092G01H_LP_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `r:real`] C1092MCBC_FE_AFTER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `c1092mcs_G01 c s d t h r =
     (c - s) * h pow 2 + (c + s) * h * r + s -
     (&2 * c + (&543 / &500) * s - &1 + s * c1092mcbc_P d t) * h -
     s * (&2 - c1092mcbc_Q d t) * r` ASSUME_TAC THENL
  [ASM_SIMP_TAC[c1092mcs_G01; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
   REWRITE_TAC[c1092mcs_kC; c1092mcs_deltaC; c1092mcs_C0] THEN
   UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`r:real`; `h:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN
                  REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`C1092WPS_half r h`,`z:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN DISCH_TAC THEN
  C1092G01H_PROD `&0 <= (&1 + z pow 2) * (r - h)` THEN
  SUBGOAL_THEN `z <= &5 / &12` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092G01H_PROD `&0 < (z - &5 / &12) * (z + &5 / &12 + &2)` THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092G01H_LP_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`;
                `&2 * c + (&543 / &500) * s - &1 + s * c1092mcbc_P d t`;
                `s * (&2 - c1092mcbc_Q d t)`; `z:real`] C1092G01H_QUARTIC_NONNEGATIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`;
                `&2 * c + (&543 / &500) * s - &1 + s * c1092mcbc_P d t`;
                `s * (&2 - c1092mcbc_Q d t)`; `z:real`; `h:real`; `r:real`]
    C1092G01H_HIGH_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (&1 + z pow 2) pow 2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_POW_LT THEN RASM_ARITH_TAC; ALL_TAC] THEN
  C1092G01H_PROD `&0 < (&1 + z pow 2) pow 2 * --c1092mcs_G01 c s d t h r` THEN
  UNDISCH_TAC `&0 <= c1092g01h_highQuartic c s
                 (&2 * c + (&543 / &500) * s - &1 + s * c1092mcbc_P d t)
                 (s * (&2 - c1092mcbc_Q d t)) z` THEN
  UNDISCH_TAC `&0 < (&1 + z pow 2) pow 2 * --c1092mcs_G01 c s d t h r` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;
