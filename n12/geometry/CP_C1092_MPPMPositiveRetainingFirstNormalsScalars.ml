(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMPositiveRetainingFirstNormalsScalars *)
(* .lean (N12Compact.C1092MPPMPositiveRetainingFirstNormals).  Exact        *)
(* unit-circle margins for POSITIVE-RETAINING-FIRST-NORMALS.                 *)
(* Normal is c977cc_normal.                                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C1092PRFN_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let C1092PRFN_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [MATCH_ACCEPT_TAC REAL_LE_POW_2; RASM_ARITH_TAC]; ALL_TAC];;

(* Lean: sine_small *)
let C1092PRFN_SINE_SMALL = prove
 (`forall c s. c977cc_normal c s ==> s < &71 / &100`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092PRFN_NORMAL_TAC THEN
  C1092PRFN_PROD `&0 <= (c - s) * (c + s)` THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092PRFN_PROD `&0 <= (s - &71 / &100) * (s + &71 / &100)` THEN
  RASM_ARITH_TAC);;

(* Lean: relative *)
let C1092PRFN_RELATIVE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t
     ==> &0 < c * d + s * t /\ c * d + s * t <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRFN_NORMAL_TAC THEN
  C1092PRFN_PROD `&0 < c * d` THEN C1092PRFN_PROD `&0 <= s * t` THEN
  SUBGOAL_THEN `(c * d + s * t) pow 2 + (c * t - s * d) pow 2 = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `c * t - s * d:real` REAL_LE_POW_2) THEN
  UNDISCH_TAC `(c * d + s * t) pow 2 + (c * t - s * d) pow 2 = &1` THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`c * d + s * t`,`X:real`) THEN SPEC_TAC(`(c * t - s * d) pow 2`,`Y:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN NLIN_TAC [SQ_NONNEG `X - &1`]);;

(* Lean: transverse_base *)
let C1092PRFN_TRANSVERSE_BASE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t
     ==> s + (&13 / &50) * (c * d + s * t) * d < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092PRFN_SINE_SMALL) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092PRFN_RELATIVE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092PRFN_NORMAL_TAC THEN
  C1092PRFN_PROD `&0 <= (&1 - (c * d + s * t)) * d` THEN
  RASM_ARITH_TAC);;

(* Lean: successor_up *)
let C1092PRFN_SUCCESSOR_UP = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t
     ==> (c * d + s * t) * (s - &1) + (c * t - s * d) * (c + s - &1) + (&13 / &50) * d < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRFN_NORMAL_TAC THEN
  C1092PRFN_PROD `&0 <= (c - s) * (&1 - (c + s) / &2)` THEN
  SUBGOAL_THEN `&13 / &50 - c + s - s pow 2 <= --(&6 / &25)` ASSUME_TAC THENL
  [NLIN_TAC []; ALL_TAC] THEN
  C1092PRFN_PROD `&0 <= (&3 / &2 - c - s) * (c + s - &1 / &2)` THEN
  SUBGOAL_THEN `(&1 - c) * (&1 - s) <= &1 / &8` ASSUME_TAC THENL
  [NLIN_TAC []; ALL_TAC] THEN
  C1092PRFN_PROD `&0 <= d * (--(&6 / &25) - (&13 / &50 - c + s - s pow 2))` THEN
  C1092PRFN_PROD `&0 <= t * (&1 / &8 - (&1 - c) * (&1 - s))` THEN
  SUBGOAL_THEN `(c * d + s * t) * (s - &1) + (c * t - s * d) * (c + s - &1) + (&13 / &50) * d =
                d * (&13 / &50 - c + s - s pow 2) + t * ((&1 - c) * (&1 - s))` SUBST1_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: successor_down *)
let C1092PRFN_SUCCESSOR_DOWN = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ c * t - s * d <= &0
     ==> (c * d + s * t) * (s - &1) + (c * t - s * d) + (&13 / &50) * d < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092PRFN_SINE_SMALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092PRFN_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= c + s pow 2 - s` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `s - &1 / &2`]; ALL_TAC] THEN
  C1092PRFN_PROD `&0 <= --(c * t - s * d) * (c + s pow 2 - s)` THEN
  C1092PRFN_PROD `&0 < d * --(&13 / &50 * c - &1 + s)` THEN
  SUBGOAL_THEN `c * ((c * d + s * t) * (s - &1) + (c * t - s * d) + (&13 / &50) * d) =
                d * (&13 / &50 * c - &1 + s) + (c * t - s * d) * (c + s pow 2 - s)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092PRFN_PROD `&0 <= c * ((c * d + s * t) * (s - &1) + (c * t - s * d) + (&13 / &50) * d)` THEN
  RASM_ARITH_TAC);;
