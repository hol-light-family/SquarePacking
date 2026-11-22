(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/MergedTopScalars.lean               *)
(* (namespace N12Compact.Completion.OtherCases.MergedTopScalars).           *)
(* Exact one-angle margins in the merged-top obstruction.                   *)
(* CanonicalScalars.bounds: CCCS_BOUNDS.                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

(* Lean: steep_data *)
let OCMTS_STEEP_DATA = prove
 (`forall c t. &0 < c /\ &0 <= t /\ t <= c /\ c pow 2 + t pow 2 = &1 /\
         &27 / &20 * c - &1 / &20 * t < &1001 / &1000
         ==> &5 * c < &6 * t /\ &16 / &25 < t /\ t < &5 / &7 /\
             &7 / &10 < c /\ c <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `&5 * c < &6 * t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&96 / &125 < c` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      NLIN_FACTS_TAC []
       [`&0 <= (&5 * c - &6 * t) * (&5 * c + &6 * t)`;
        `&0 <= (&96 / &125 - c) * (&96 / &125 + c)`] THEN
      NLIN_TAC ~deg2:false [];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 < (&6 * t - &5 * c) * (&6 * t + &5 * c)`;
    `&0 <= (c - t) * (c + t)`] THEN
  CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THENL
   [NLIN_FACTS_TAC [] [`&0 <= (&16 / &25 - t) * (&16 / &25 + t)`];
    NLIN_FACTS_TAC [] [`&0 <= (t - &5 / &7) * (t + &5 / &7)`]] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: u_margin *)
let OCMTS_U_MARGIN = prove
 (`forall c t. &7 / &10 < c /\ c <= &1 /\ &16 / &25 <= t /\ t <= &5 / &7 /\
         c pow 2 + t pow 2 = &1
         ==> &0 < c - &27 / &20 + &7 / &10 * t * (c + t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 - &3 / &5 * t pow 2 <= c` ASSUME_TAC THENL
   [NLIN_FACTS_TAC [] [`&0 <= (&1 - c) * (&3 / &5 * (&1 + c) - &1)`] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  SUBGOAL_THEN `t pow 2 <= &25 / &49` ASSUME_TAC THENL
   [NLIN_FACTS_TAC [] [`&0 <= (&5 / &7 - t) * (&5 / &7 + t)`] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < --(&7 / &20) + &7 / &10 * t + &1 / &10 * t pow 2 - &21 / &50 * t pow 3`
    ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= &7 / &10 + &1 / &10 * (t + &16 / &25) -
        &21 / &50 * (t pow 2 + &16 / &25 * t + (&16 / &25) pow 2)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (t - &16 / &25) * (&7 / &10 + &1 / &10 * (t + &16 / &25) -
        &21 / &50 * (t pow 2 + &16 / &25 * t + (&16 / &25) pow 2))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (c - (&1 - &3 / &5 * t pow 2)) * (&1 + &7 / &10 * t)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  REAL_ARITH_TAC);;

(* Lean: v_margin *)
let OCMTS_V_MARGIN = prove
 (`forall c t. &7 / &10 < c /\ &16 / &25 <= t /\ t <= &5 / &7
         ==> &0 < t - &3 / &5 - &3 / &4 * t pow 2 + &13 / &20 * c * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (t - &16 / &25) * (&291 / &200 - &3 / &4 * (t + &16 / &25))`
    MP_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&13 / &20 * t) * (c - &7 / &10)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;
