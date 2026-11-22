(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MixedWideCrossingScalars.lean            *)
(* (N12Compact.C1092MixedWideCrossingScalars).  Uniform rational margins for *)
(* the mixed-wide-wall crossing.                                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;

let C1092MWCS_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092MWCS_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MWCS_LIN_TAC; DISCH_TAC];;

let C1092MWCS_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MWCS_LIN_TAC; DISCH_TAC];;

(* Lean: small *)
let C1092MWCS_SMALL = prove
 (`forall c s z. &0 < c /\ &0 < s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
           &0 < z /\ z < &1 / &2 /\ z * (&1 + c) = s /\
           (&1 + z pow 2) * s = &2 * z /\ &2 / &5 < (&1 - z) pow 2 / &2
           ==> z < &53 / &500 /\ &97 / &100 < c /\ s < &21 / &100 /\
               z <= (&51 / &100) * s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `z < &53 / &500` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`&0 <= (z - &53 / &500) * ((&1 - z) + &447 / &500)`] THEN
    C1092MWCS_LIN_TAC ORELSE NLIN_TAC [];
    ALL_TAC] THEN
  C1092MWCS_LE_MUL_TAC `&53 / &500 - z` `&2 - (&21 / &100) * (&53 / &500 + z)` THEN
  SUBGOAL_THEN `s < &21 / &100` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MWCS_LE_MUL_TAC `&1 + z * z` `s - &21 / &100` THEN
    NLIN_TAC [SQ_NONNEG `z:real`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&97 / &100 < c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MWCS_LE_MUL_TAC `&97 / &100 - c` `&97 / &100 + c` THEN
    C1092MWCS_LT_MUL_TAC `&21 / &100 - s` `&21 / &100 + s` THEN
    C1092MWCS_LIN_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  C1092MWCS_LE_MUL_TAC `s:real` `(&51 / &100) * (&1 + c) - &1` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC [] [`&0 < (z - (&51 / &100) * s) * (&1 + c)`] THEN
  C1092MWCS_LIN_TAC);;

(* Lean: margins *)
let C1092MWCS_MARGINS = prove
 (`forall c s d t z. &0 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1 /\
               &0 < d /\ &0 <= t /\ d pow 2 + t pow 2 = &1 /\
               &5 / &4 < d + t /\ &0 <= z /\ z < &53 / &500 /\
               &97 / &100 < c /\ s < &21 / &100 /\ z <= (&51 / &100) * s /\
               z * (&1 + c) = s
               ==> &7 / &25 < t /\ &0 < c * t - s * d /\
                   &0 < t * (&1 - z - c + (&2 / &5) * s) +
                        (c * t - s * d) * (d + t - &1) /\
                   &0 < d * (--z * (c + s) + (&13 / &50) * s pow 2) +
                        t * ((&1 - z) * s - (&13 / &50) * s * c + &2 / &5)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `t:real`] [`c <= &1`; `d <= &1`] THEN
  SUBGOAL_THEN `&7 / &25 < t` ASSUME_TAC THENL
   [C1092MWCS_LT_MUL_TAC `d + t - &5 / &4` `d + t + &5 / &4` THEN
    C1092MWCS_LE_MUL_TAC `t:real` `&1 - d` THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MWCS_LE_MUL_TAC `&7 / &25 - t` `t:real` THEN C1092MWCS_LIN_TAC;
    ALL_TAC] THEN
  C1092MWCS_LT_MUL_TAC `t:real` `c - &97 / &100` THEN
  C1092MWCS_LE_MUL_TAC `s:real` `&1 - d` THEN
  C1092MWCS_LE_MUL_TAC `t:real` `&21 / &100 - s` THEN
  SUBGOAL_THEN `(&11 / &50) * t < c * t - s * d` ASSUME_TAC THENL
   [C1092MWCS_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c * t - s * d` ASSUME_TAC THENL [C1092MWCS_LIN_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [C1092MWCS_LE_MUL_TAC `t:real` `(&1 - z - c + (&2 / &5) * s) - --(&11 / &100) * s` THEN
    C1092MWCS_LT_MUL_TAC `t:real` `&21 / &100 - s` THEN
    C1092MWCS_LT_MUL_TAC `(c * t - s * d) - (&11 / &50) * t` `d + t - &1` THEN
    C1092MWCS_LT_MUL_TAC `t:real` `(&11 / &50) * (d + t - &1) - &11 / &200` THEN
    C1092MWCS_LIN_TAC;
    ALL_TAC] THEN
  C1092MWCS_LE_MUL_TAC `z:real` `(&121 / &200) * (&1 + c) - (c + s)` THEN
  C1092MWCS_LE_MUL_TAC `s:real` `s:real` THEN
  C1092MWCS_LE_MUL_TAC `d:real`
    `--z * (c + s) + (&13 / &50) * s * s + (&121 / &200) * s` THEN
  C1092MWCS_LE_MUL_TAC `s:real` `&1 - z - (&13 / &50) * c - &317 / &500` THEN
  C1092MWCS_LE_MUL_TAC `t:real` `s * (&1 - z - (&13 / &50) * c - &317 / &500)` THEN
  C1092MWCS_LE_MUL_TAC `s:real` `t - &7 / &25` THEN
  C1092MWCS_LIN_TAC);;
