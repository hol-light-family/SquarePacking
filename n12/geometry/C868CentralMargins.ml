(* ========================================================================= *)
(* Port of Compact/Geometry/C868CentralMargins.lean                          *)
(* (N12Compact.C868CentralMargins).  Continuous support margins for the      *)
(* southwest central square.  Purely scalar; Normal C S is c977cc_normal.    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

(* Unfold both normals, add their bounds as assumptions. *)
let C868CM_NORMALS_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (find_term (fun t -> try fst(dest_const t) = "c977cc_normal"
                                with _ -> false)) (concl th)
    then (ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
          ASSUME_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2] th))
    else NO_TAC));;

(* Lean: sum_bound (private) *)
let C868CM_SUM_BOUND = prove
 (`forall C S. c977cc_normal C S ==> C + S <= &17 / &12`,
  REPEAT STRIP_TAC THEN C868CM_NORMALS_TAC THEN
  NLIN_TAC [SQ_NONNEG `C - S:real`; SQ_NONNEG `C + S - &17 / &12`]);;

(* Lean: endpointI (private) *)
let C868CM_ENDPOINTI = prove
 (`forall C S. c977cc_normal C S ==> &0 <= &1 - &1 / &20 * C - &27 / &20 * S`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP C868CM_SUM_BOUND) THEN
  C868CM_NORMALS_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: endpointIII (private) *)
let C868CM_ENDPOINTIII = prove
 (`forall C S. c977cc_normal C S ==> &0 <= &1 - &13 / &20 * C - &3 / &4 * S`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP C868CM_SUM_BOUND) THEN
  C868CM_NORMALS_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: cone_above (private) *)
let C868CM_CONE_ABOVE = prove
 (`forall c s C S p q.
      c977cc_normal c s /\ c977cc_normal C S /\ &0 <= s * C - c * S /\
      &0 <= C * p + S * q /\ &0 <= p + q
      ==> &0 <= c * p + s * q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C868CM_NORMALS_TAC THEN
  ASM_CASES_TAC `C:real = S` THENL
   [SUBGOAL_THEN `c:real = s` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
       [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `C:real = S`)) THEN
      NLIN_TAC [];
      ALL_TAC] THEN
    NLIN_FACTS_TAC [] [`&0 <= s * (p + q)`] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 < C - S` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= (c - s) * (C * p + S * q)`; `&0 <= (s * C - c * S) * (p + q)`] THEN
    NLIN_TAC []]);;

(* Lean: cone_below (private) *)
let C868CM_CONE_BELOW = prove
 (`forall c s C S p q.
      c977cc_normal c s /\ c977cc_normal C S /\ &0 <= c * S - s * C /\
      &0 <= C * p + S * q /\ &0 <= p
      ==> &0 <= c * p + s * q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C868CM_NORMALS_TAC THEN
  ASM_CASES_TAC `S = &0` THENL
   [SUBGOAL_THEN `s = &0` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
       [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `S = &0`)) THEN
      NLIN_TAC [];
      ALL_TAC] THEN
    NLIN_FACTS_TAC [] [`&0 <= c * p`] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 < S` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= s * (C * p + S * q)`; `&0 <= (c * S - s * C) * p`] THEN
    NLIN_TAC []]);;

(* Lean: margin_above (private) *)
let C868CM_MARGIN_ABOVE = prove
 (`forall c s C S U V.
      c977cc_normal c s /\ c977cc_normal C S /\ &0 <= s * C - c * S /\
      &0 <= U - &33 / &20 * C - &47 / &20 * S /\
      &0 <= (C + S) * U + (C - S) * V - &4
      ==> &0 <= (c * C + s * S) * U + (s * C - c * S) * V - &33 / &20 * c - &47 / &20 * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `C:real`; `S:real`;
                `C * U - S * V - &33 / &20`; `S * U + C * V - &47 / &20`]
    C868CM_CONE_ABOVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `c977cc_normal C S` THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `C * (C * U - S * V - &33 / &20) + S * (S * U + C * V - &47 / &20) =
                    U - &33 / &20 * C - &47 / &20 * S` (fun th -> ASM_REWRITE_TAC[th]) THEN
      UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN CONV_TAC REAL_RING;
      ASM_REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

(* Lean: margin_below (private) *)
let C868CM_MARGIN_BELOW = prove
 (`forall c s C S U V.
      c977cc_normal c s /\ c977cc_normal C S /\ s * C - c * S <= &0 /\
      &0 <= U - &33 / &20 * C - &47 / &20 * S /\
      &0 <= C * U - S * V - &33 / &20
      ==> &0 <= (c * C + s * S) * U + (s * C - c * S) * V - &33 / &20 * c - &47 / &20 * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `C:real`; `S:real`;
                `C * U - S * V - &33 / &20`; `S * U + C * V - &47 / &20`]
    C868CM_CONE_BELOW) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `c977cc_normal C S` THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `C * (C * U - S * V - &33 / &20) + S * (S * U + C * V - &47 / &20) =
                    U - &33 / &20 * C - &47 / &20 * S` (fun th -> ASM_REWRITE_TAC[th]) THEN
      UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN CONV_TAC REAL_RING];
    REAL_ARITH_TAC]);;

let C868CM_MODE_TAC th endpoint =
  MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C868CM_SUM_BOUND o
    check (fun th -> concl th = `c977cc_normal C S`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP endpoint o
    check (fun th -> concl th = `c977cc_normal C S`)) THEN
  C868CM_NORMALS_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC];;

(* Lean: modeI_nonneg *)
let C868CM_MODEI_NONNEG = prove
 (`forall c s C S.
      c977cc_normal c s /\ c977cc_normal C S /\ &0 <= s * C - c * S
      ==> &0 <= (c * C + s * S) * (&1 + &8 / &5 * C + S) +
                (s * C - c * S) * (&2 * C - &87 / &50 * S) -
                &33 / &20 * c - &47 / &20 * s`,
  REPEAT STRIP_TAC THEN C868CM_MODE_TAC C868CM_MARGIN_ABOVE C868CM_ENDPOINTI THEN
  NLIN_FACTS_TAC []
   [`&0 <= (C + S - &1) * (&17 / &12 - (C + S))`;
    `&0 <= &3 / &5 + (C + S) - (C + S) * (C + S)`; `&0 <= S * (C - S)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: modeI_nonpos *)
let C868CM_MODEI_NONPOS = prove
 (`forall c s C S.
      c977cc_normal c s /\ c977cc_normal C S /\ s * C - c * S <= &0
      ==> &0 <= (c * C + s * S) * (&1 + &8 / &5 * C + S) +
                (s * C - c * S) * (&87 / &50 * C - &2 * S) -
                &33 / &20 * c - &47 / &20 * s`,
  REPEAT STRIP_TAC THEN C868CM_MODE_TAC C868CM_MARGIN_BELOW C868CM_ENDPOINTI THEN
  NLIN_FACTS_TAC [SQ_NONNEG `C - S:real`] [`C * S <= &1 / &2`; `&0 <= S * S`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: modeII_nonneg *)
let C868CM_MODEII_NONNEG = prove
 (`forall c s C S.
      c977cc_normal c s /\ c977cc_normal C S /\ &0 <= s * C - c * S /\
      &13 * S <= C
      ==> &0 <= (c * C + s * S) * (&2 * C + &87 / &50 * S) +
                (s * C - c * S) * (&1 + &8 / &5 * C - S) -
                &33 / &20 * c - &47 / &20 * s`,
  REPEAT STRIP_TAC THEN C868CM_MODE_TAC C868CM_MARGIN_ABOVE C868CM_ENDPOINTI THEN
  SUBGOAL_THEN `S <= &1 / &13` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`&0 <= S * (&1 - S)`; `&0 <= C * S`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: modeIII_nonneg *)
let C868CM_MODEIII_NONNEG = prove
 (`forall c s C S.
      c977cc_normal c s /\ c977cc_normal C S /\ &0 <= s * C - c * S
      ==> &0 <= (c * C + s * S) * (&1 + C + &8 / &5 * S) +
                (s * C - c * S) * (&1 + C - &8 / &5 * S) -
                &33 / &20 * c - &47 / &20 * s`,
  REPEAT STRIP_TAC THEN C868CM_MODE_TAC C868CM_MARGIN_ABOVE C868CM_ENDPOINTIII THEN
  NLIN_FACTS_TAC [] [`&0 <= (&1 - C) * (&3 * C - &2)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: modeIII_nonpos *)
let C868CM_MODEIII_NONPOS = prove
 (`forall c s C S.
      c977cc_normal c s /\ c977cc_normal C S /\ s * C - c * S <= &0
      ==> &0 <= (c * C + s * S) * (&1 + C + &8 / &5 * S) +
                (s * C - c * S) * (&87 / &50 * C - &2 * S) -
                &33 / &20 * c - &47 / &20 * s`,
  REPEAT STRIP_TAC THEN C868CM_MODE_TAC C868CM_MARGIN_BELOW C868CM_ENDPOINTIII THEN
  NLIN_FACTS_TAC [SQ_NONNEG `C - S:real`] [`C * S <= &1 / &2`; `&0 <= C * (&1 - C)`] THEN
  NLIN_TAC ~deg2:false []);;
