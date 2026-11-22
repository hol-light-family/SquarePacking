(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingNegativeCrosspointG01.lean    *)
(* (N12Compact.C1092MPPMMissingNegativeCrosspointSupport).  The remaining    *)
(* central/boundary scalar G01star in MISSING-NEGATIVE-WALL-SCALARS.         *)
(* Normal: c977cc_normal; Quarter, kC, deltaC, C0: c1092mncs_*;              *)
(* G01, G01star, FE: c1092mmncs_*; FE_first_cap / FE_second_cap:            *)
(* C1092MMNCE_FE_FIRST_CAP / _SECOND_CAP; normal_bounds C977CC_NORMAL_BOUNDS;*)
(* C1092MPPMCrosspointSupport.steep_bounds C1092G10_STEEP_BOUNDS;            *)
(* sine_order / cosine_order C977CSB_SINE_ORDER / C977CSB_COSINE_ORDER;      *)
(* UnitCircleChord.increasing CCUCC_INCREASING; G01_low/middle/high_model    *)
(* C1092MNG01M_*.  The local lets A, B are written out.  Tag C1092MNG01_.    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointG01Models.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointEnvelope.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryG10Clamp.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C1092MNG01_LIN =
  REPEAT CONJ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2; REAL_NOT_LE]) THEN
  REWRITE_TAC[REAL_POW_2] THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NLIN_TAC ~deg2:false []);;

let C1092MNG01_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092MNG01_LIN; ALL_TAC];;

let C1092MNG01_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C1092MNG01_LIN; ALL_TAC];;

let C1092MNG01_UNFOLD_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th) ||
                               can (term_match [] `c1092mncs_quarter x y`) (concl th)) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC
      (REWRITE_RULE[c977cc_normal; c1092mncs_quarter; c1092mcs_quarter] th)) ns);;

(* Lean: before_formula (private) *)
let C1092MNG01_BEFORE_FORMULA = prove
 (`forall c s d t h r. c1092mncs_quarter h r /\ c1092mncs_deltaC c s h r <= &0
     ==> c1092mmncs_G01 c s d t h r =
         c * h * (h - &2) + s * (&1 + h * r - &2 * r - h - c1092mmncs_FE d t h r) + h`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mncs_quarter; c1092mcs_quarter] THEN STRIP_TAC THEN
  REWRITE_TAC[c1092mmncs_G01] THEN
  ASM_SIMP_TAC[REAL_ARITH `x <= &0 ==> abs x = --x`] THEN
  REWRITE_TAC[c1092mncs_kC; c1092mncs_deltaC; c1092mncs_C0] THEN
  UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING);;

(* Lean: after_formula (private) *)
let C1092MNG01_AFTER_FORMULA = prove
 (`forall c s d t h r. c1092mncs_quarter h r /\ &0 <= c1092mncs_deltaC c s h r
     ==> c1092mmncs_G01 c s d t h r =
         c * h * (h + r - &2) + s * (r * (h + r - &2) - h - c1092mmncs_FE d t h r) + h`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mncs_quarter; c1092mcs_quarter] THEN STRIP_TAC THEN
  REWRITE_TAC[c1092mmncs_G01] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  REWRITE_TAC[c1092mncs_kC; c1092mncs_deltaC; c1092mncs_C0] THEN
  UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING);;

(* Lean: first_before (private) *)
let C1092MNG01_FIRST_BEFORE = prove
 (`forall epsilon c s d t h r. c977cc_normal c s /\ c977cc_normal d t /\ &252 / &373 <= t /\
     c1092mncs_quarter h r /\ epsilon <= &43 / &500 /\ c1092mncs_deltaC c s h r <= &0
     ==> c * (h * (h - &2)) + s * (&1 + h * r - (&61 / &50) * r - (&112 / &125) * h) + h <=
         c1092mmncs_G01star epsilon c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `r:real`] C1092MMNCE_FE_FIRST_CAP) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`]
    C1092MNG01_BEFORE_FORMULA) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C1092MNG01_UNFOLD_TAC THEN
  C1092MNG01_PROD `&0 <= s * ((--(&19 / &100) * h - (&39 / &50) * r) - c1092mmncs_FE d t h r)` THEN
  C1092MNG01_PROD `&0 <= (&43 / &500 - epsilon) * (s * h)` THEN
  REWRITE_TAC[c1092mmncs_G01star] THEN C1092MNG01_LIN);;

(* Lean: first_after (private) *)
let C1092MNG01_FIRST_AFTER = prove
 (`forall epsilon c s d t h r. c977cc_normal c s /\ c977cc_normal d t /\ &252 / &373 <= t /\
     c1092mncs_quarter h r /\ epsilon <= &43 / &500 /\ &0 <= c1092mncs_deltaC c s h r
     ==> c * (h * (h + r - &2)) + s * (r * (h + r - &61 / &50) - (&112 / &125) * h) + h <=
         c1092mmncs_G01star epsilon c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `r:real`] C1092MMNCE_FE_FIRST_CAP) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`]
    C1092MNG01_AFTER_FORMULA) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C1092MNG01_UNFOLD_TAC THEN
  C1092MNG01_PROD `&0 <= s * ((--(&19 / &100) * h - (&39 / &50) * r) - c1092mmncs_FE d t h r)` THEN
  C1092MNG01_PROD `&0 <= (&43 / &500 - epsilon) * (s * h)` THEN
  REWRITE_TAC[c1092mmncs_G01star] THEN C1092MNG01_LIN);;

(* Lean: second_after (private) *)
let C1092MNG01_SECOND_AFTER = prove
 (`forall epsilon c s d t h r. c977cc_normal c s /\ c977cc_normal d t /\ &252 / &373 <= t /\
     c1092mncs_quarter h r /\ epsilon <= &43 / &500 /\ &0 <= c1092mncs_deltaC c s h r
     ==> c * (h * (h + r - &2)) + s * (r * (h + r - &17 / &25) - (&182 / &125) * h) + h <=
         c1092mmncs_G01star epsilon c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `r:real`] C1092MMNCE_FE_SECOND_CAP) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`]
    C1092MNG01_AFTER_FORMULA) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C1092MNG01_UNFOLD_TAC THEN
  C1092MNG01_PROD `&0 <= s * (((&37 / &100) * h - (&33 / &25) * r) - c1092mmncs_FE d t h r)` THEN
  C1092MNG01_PROD `&0 <= (&43 / &500 - epsilon) * (s * h)` THEN
  REWRITE_TAC[c1092mmncs_G01star] THEN C1092MNG01_LIN);;

(* Lean: low (private) *)
let C1092MNG01_LOW = prove
 (`forall epsilon c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\
     &252 / &373 <= t /\ c1092mncs_quarter h r /\ epsilon <= &43 / &500 /\
     &4 / &5 <= h /\ r <= &3 / &5
     ==> &1 / &100 <= c1092mmncs_G01star epsilon c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092G10_STEEP_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  C1092MNG01_UNFOLD_TAC THEN
  C1092MNG01_PROD `&0 <= c * (&3 / &5 - r)` THEN
  C1092MNG01_PROD `&0 <= s * (h - &4 / &5)` THEN
  SUBGOAL_THEN `c1092mncs_deltaC c s h r <= &0` ASSUME_TAC THENL
   [REWRITE_TAC[c1092mncs_deltaC] THEN C1092MNG01_LIN; ALL_TAC] THEN
  MP_TAC(SPECL [`epsilon:real`; `c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`]
    C1092MNG01_FIRST_BEFORE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `h <= &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MNG01_PROD `&0 < (h - &1) * (h + &1)` THEN
    C1092MNG01_PROD `&0 <= r * r` THEN C1092MNG01_LIN; ALL_TAC] THEN
  C1092MNG01_PROD `&0 <= (&4 / &5 - c) * (h * (&2 - h))` THEN
  ASM_CASES_TAC `&0 <= &1 + h * r - (&61 / &50) * r - (&112 / &125) * h` THENL
   [C1092MNG01_PROD `&0 <= (s - &3 / &5) * (&1 + h * r - (&61 / &50) * r - (&112 / &125) * h)` THEN
    MP_TAC(SPECL [`&3 / &5`; `h:real`; `r:real`] C1092MNG01M_G01_LOW_MODEL);
    C1092MNG01_PROD `&0 <= (&71 / &100 - s) * --(&1 + h * r - (&61 / &50) * r - (&112 / &125) * h)` THEN
    MP_TAC(SPECL [`&71 / &100`; `h:real`; `r:real`] C1092MNG01M_G01_LOW_MODEL)] THEN
  (ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    DISCH_TAC]) THEN
  C1092MNG01_LIN);;

(* Lean: middle (private) *)
let C1092MNG01_MIDDLE = prove
 (`forall epsilon c s d t h r. c977cc_normal c s /\ c977cc_normal d t /\ &252 / &373 <= t /\
     c977cc_normal h r /\ &3 / &5 <= r /\ epsilon <= &43 / &500
     ==> &1 / &100 <= c1092mmncs_G01star epsilon c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092G10_STEEP_BOUNDS) THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092MNG01M_G01_MIDDLE_MODEL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `c1092mncs_quarter h r` ASSUME_TAC THENL
   [UNDISCH_TAC `c977cc_normal h r` THEN
    REWRITE_TAC[c977cc_normal; c1092mncs_quarter; c1092mcs_quarter] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  C1092MNG01_UNFOLD_TAC THEN
  SUBGOAL_THEN `h + r <= &283 / &200` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPEC `h - r:real` REAL_LE_SQUARE) THEN DISCH_TAC THEN
    C1092MNG01_PROD `&0 < (h + r - &283 / &200) * (h + r + &283 / &200)` THEN
    C1092MNG01_LIN; ALL_TAC] THEN
  ASM_CASES_TAC `c1092mncs_deltaC c s h r <= &0` THENL
   [C1092MNG01_PROD `&0 <= (h - r) * (&81 / &500 - (h - r) / &2)` THEN
    C1092MNG01_FACT `&0 <= &1 + h * r - (&61 / &50) * r - (&112 / &125) * h` THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C977CSB_SINE_ORDER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c1092mncs_deltaC c s h r <= &0` THEN
      REWRITE_TAC[c1092mncs_deltaC] THEN REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C977CSB_COSINE_ORDER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C1092MNG01_PROD `&0 <= (h - c) * (h * (&2 - h))` THEN
    C1092MNG01_PROD `&0 <= (s - r) * (&1 + h * r - (&61 / &50) * r - (&112 / &125) * h)` THEN
    MP_TAC(SPECL [`epsilon:real`; `c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`]
      C1092MNG01_FIRST_BEFORE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `h * (h * (h - &2)) + r * (&1 + h * r - (&61 / &50) * r - (&112 / &125) * h) + h =
                  &2 * h + r - &2 - (&112 / &125) * h * r + (&39 / &50) * r pow 2` ASSUME_TAC THENL
     [UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092MNG01_LIN;
    ALL_TAC] THEN
  C1092MNG01_PROD `&0 <= r * (&71 / &50 - (h + r))` THEN
  C1092MNG01_FACT `r * (h + r - &61 / &50) - (&112 / &125) * h <= &0` THEN
  C1092MNG01_PROD `&0 <= h * ((&112 / &125) * h - (&39 / &50) * r)` THEN
  MP_TAC(SPECL [`h:real`; `r:real`; `c:real`; `s:real`] C977CSB_SINE_ORDER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(c1092mncs_deltaC c s h r <= &0)` THEN
    REWRITE_TAC[c1092mncs_deltaC] THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`h:real`; `r:real`; `c:real`; `s:real`;
                `--(h * (h + r - &2))`; `--(r * (h + r - &61 / &50) - (&112 / &125) * h)`]
    CCUCC_INCREASING) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(C1092MNG01_PROD `&0 <= h * (&2 - (h + r))` THEN C1092MNG01_LIN) THEN
    C1092MNG01_LIN;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`epsilon:real`; `c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`]
    C1092MNG01_FIRST_AFTER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `h * (h * (h + r - &2)) + r * (r * (h + r - &61 / &50) - (&112 / &125) * h) + h =
                &2 * h + r - &2 - (&112 / &125) * h * r + (&39 / &50) * r pow 2` ASSUME_TAC THENL
   [UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092MNG01_LIN);;

(* Lean: high (private) *)
let C1092MNG01_HIGH = prove
 (`forall epsilon c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\
     &252 / &373 <= t /\ c1092mncs_quarter h r /\ epsilon <= &43 / &500 /\ h <= r
     ==> &1 / &100 <= c1092mmncs_G01star epsilon c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092G10_STEEP_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  C1092MNG01_UNFOLD_TAC THEN
  C1092MNG01_PROD `&0 <= (c - s) * r` THEN
  C1092MNG01_PROD `&0 <= s * (r - h)` THEN
  SUBGOAL_THEN `&0 <= c1092mncs_deltaC c s h r` ASSUME_TAC THENL
   [REWRITE_TAC[c1092mncs_deltaC] THEN C1092MNG01_LIN; ALL_TAC] THEN
  MP_TAC(SPECL [`epsilon:real`; `c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`]
    C1092MNG01_SECOND_AFTER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `h + r <= &2` ASSUME_TAC THENL
   [MP_TAC(SPEC `h - r:real` REAL_LE_SQUARE) THEN MP_TAC(SPEC `h + r - &2` REAL_LE_SQUARE) THEN
    REPEAT DISCH_TAC THEN C1092MNG01_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= h + r` ASSUME_TAC THENL
   [C1092MNG01_PROD `&0 <= h * r` THEN C1092MNG01_PROD `&0 <= h + r` THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MNG01_PROD `&0 < (&1 - (h + r)) * (&1 + (h + r))` THEN C1092MNG01_LIN; ALL_TAC] THEN
  C1092MNG01_PROD `&0 <= (&4 / &5 - c) * (h * (&2 - (h + r)))` THEN
  ASM_CASES_TAC `&0 <= r * (h + r - &17 / &25) - (&182 / &125) * h` THENL
   [C1092MNG01_PROD `&0 <= (s - &3 / &5) * (r * (h + r - &17 / &25) - (&182 / &125) * h)` THEN
    C1092MNG01_PROD `&0 <= h * (h + r - &1)` THEN
    C1092MNG01_FACT `h / &5 + (&3 / &5) * (r * (h + r - &17 / &25) - (&182 / &125) * h) <=
                     c1092mmncs_G01star epsilon c s d t h r` THEN
    ASM_CASES_TAC `&1 / &20 <= h` THENL [C1092MNG01_LIN; ALL_TAC] THEN
    SUBGOAL_THEN `&99 / &100 <= r` ASSUME_TAC THENL
     [C1092MNG01_PROD `&0 <= (&1 / &20 - h) * (&1 / &20 + h)` THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092MNG01_PROD `&0 < (&99 / &100 - r) * (&99 / &100 + r)` THEN C1092MNG01_LIN;
      ALL_TAC] THEN
    C1092MNG01_PROD `&0 <= (r - &99 / &100) * (h + r - &17 / &25)` THEN
    C1092MNG01_FACT `&1 / &5 <= r * (h + r - &17 / &25) - (&182 / &125) * h` THEN
    C1092MNG01_LIN;
    C1092MNG01_PROD `&0 <= (&71 / &100 - s) * --(r * (h + r - &17 / &25) - (&182 / &125) * h)` THEN
    MP_TAC(SPECL [`h:real`; `r:real`] C1092MNG01M_G01_HIGH_MODEL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092MNG01_LIN]);;

(* Lean: G01star_lower *)
let C1092MNG01_G01STAR_LOWER = prove
 (`forall epsilon c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\
     &252 / &373 <= t /\ c1092mncs_quarter h r /\ epsilon <= &43 / &500
     ==> &1 / &100 <= c1092mmncs_G01star epsilon c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `r <= &3 / &5` THENL
   [MATCH_MP_TAC C1092MNG01_LOW THEN ASM_REWRITE_TAC[] THEN
    C1092MNG01_UNFOLD_TAC THEN
    C1092MNG01_PROD `&0 <= (&3 / &5 - r) * (&3 / &5 + r)` THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MNG01_PROD `&0 < (&4 / &5 - h) * (&4 / &5 + h)` THEN C1092MNG01_LIN;
    ALL_TAC] THEN
  ASM_CASES_TAC `h <= r` THENL
   [MATCH_MP_TAC C1092MNG01_HIGH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC C1092MNG01_MIDDLE THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  UNDISCH_TAC `c1092mncs_quarter h r` THEN
  REWRITE_TAC[c977cc_normal; c1092mncs_quarter; c1092mcs_quarter] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
