(* ========================================================================= *)
(* Port of Compact/Geometry/CentralNegativeFarUpper.lean                     *)
(* (namespace N12Compact.CentralNegativeFarUpper).                           *)
(* An incoming positive central axis and the full negative bottom wall       *)
(* exclude the upper-U escape of the farther point (2.86,1).  Squares D, B   *)
(* are 5-tuples (B.s = -t, D.s = -r); Lean upper/lower are ABT_upper/        *)
(* ABT_lower; own_coefficients is CNNB_OWN_COEFFICIENTS.                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/CentralNegativeNeighborBounds.ml";;
needs "n12/geometry/CentralNegativeBottomAxes.ml";;

let CNFU_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

let CNFU_NONPOS_CANCEL = prove
 (`forall k x. &0 < k /\ &0 <= k * (&0 - x) ==> x <= &0`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: scalar_entrance (private) *)
let CNFU_SCALAR_ENTRANCE = prove
 (`forall C S c t. c977cc_normal C S /\ c977cc_normal c t /\
     &0 < C * (&43 / &50 - c - t + (&7 / &50) * t pow 2 + c * t) +
          S * (--(t pow 2) + (&7 / &50) * c * t - c + t)
     ==> &3 / &5 < t /\ S < C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CNNB_OWN_COEFFICIENTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - t`] [`c * t <= &1 / &2`] THEN
  SUBGOAL_THEN `&3 / &5 < t` ASSUME_TAC THENL
   [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
    NLIN_FACTS_TAC [SQ_NONNEG `t:real`]
     [`t pow 2 <= &9 / &25`; `&4 / &5 <= c`;
      `&43 / &50 - c - t + (&7 / &50) * t pow 2 + c * t <= &0`;
      `--(t pow 2) + (&7 / &50) * c * t - c + t <= &0`;
      `&0 <= C * --(&43 / &50 - c - t + (&7 / &50) * t pow 2 + c * t)`;
      `&0 <= S * --(--(t pow 2) + (&7 / &50) * c * t - c + t)`] THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  NLIN_FACTS_TAC []
   [`&9 / &25 <= t pow 2`;
    `(&43 / &50 - c - t + (&7 / &50) * t pow 2 + c * t) +
     (--(t pow 2) + (&7 / &50) * c * t - c + t) <= &0`] THEN
  REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
  SUBGOAL_THEN `(S:real) = C` SUBST_ALL_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`S <= C`; `C <= S`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= C * --((&43 / &50 - c - t + (&7 / &50) * t pow 2 + c * t) +
                  (--(t pow 2) + (&7 / &50) * c * t - c + t))`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: mixed_margin (private) *)
let CNFU_MIXED_MARGIN = prove
 (`forall C S c t d r. c977cc_normal C S /\ c977cc_normal c t /\ c977cc_normal d r /\
     c <= &4 / &5 /\ r * c - d * t <= &0
     ==> (C * d - S * r) * (&2 * c + &3 * t - &1) + (r * c - d * t) * (C * c - S * t) +
         &2 * (r * c - d * t) * (C + S) - (C * c - S * t) * ((&143 / &50) * r + d) <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  let X = `d * (c + t - &1 - c * t) + r * c * (c - &43 / &50)`
  and Y = `r * (&1 - (&7 / &50) * t - c * t) - d * t * (&1 - t)`
  and V = `(c + &7 / &50) * (c - t) + &1 - c` in
  let sub tm = subst [X,`XX:real`; Y,`YY:real`; V,`VV:real`] tm in
  NLIN_FACTS_TAC [] (map sub
   [`&0 <= (&1 - c) * (&1 - t)`; `&0 <= d * ((&1 - c) * (&1 - t))`;
    `&0 <= r * c`; `&0 <= (r * c) * (&43 / &50 - c)`; `XX <= &0`;
    `&0 <= (c + &7 / &50) * (c - t)`; `&0 <= VV`;
    `c - &1 + (&7 / &50) * t <= &0`;
    `&0 <= (c - t) * --(c - &1 + (&7 / &50) * t)`;
    `&0 <= d * ((c - t) * --(c - &1 + (&7 / &50) * t))`;
    `&0 <= --(r * c - d * t) * VV`]) THEN
  SUBGOAL_THEN (sub `XX + YY <= &0`) ASSUME_TAC THENL
   [MATCH_MP_TAC CNFU_NONPOS_CANCEL THEN
    EXISTS_TAC `c:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; NLIN_TAC ~deg2:false []];
    ALL_TAC] THEN
  NLIN_FACTS_TAC [] (map sub
   [`&0 <= (C - S) * --XX`; `&0 <= S * --(XX + YY)`]) THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: impossible *)
let CNFU_IMPOSSIBLE = prove
 (`forall cD sD uD vD aD cB sB uB vB aB r t C S.
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal C S /\ c977cc_normal cB t /\ c977cc_normal cD r /\
     sB = --t /\ sD = --r /\ &1 <= aB /\
     linside cD sD uD vD aD (&143 / &50) (&1) /\
     uB + aB <= (&143 / &50) * cB - t /\ vB + aB <= &2 * cB + &3 * t /\
     &2 * (C + S) < ABT_lower cB sB uB vB aB C S /\
     (ABT_upper cD sD uD vD aD t cB <= vB \/ vD + aD <= ABT_lower cB sB uB vB aB r cD)
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sB:real = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sD:real = --r`)) THEN
  C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= cB * (C - S)`; `&0 <= S * (cB - t)`; `&0 <= C * cB - S * t`;
    `&0 <= C * t + S * cB`] THEN
  MP_TAC(SPECL [`cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`; `t:real`;
                `C:real`; `S:real`] C977NCO_LOWER_NEGATIVE_POS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (C * cB - S * t) * (((&143 / &50) * cB - t) - (uB + aB))`;
    `&0 <= (C * t + S * cB) * ((&2 * cB + &3 * t) - (vB + aB))`;
    `&0 <= ((C * cB - S * t) + (C * t + S * cB)) * (aB - &1)`] THEN
  SUBGOAL_THEN `&0 < C * (&43 / &50 - cB - t + (&7 / &50) * t pow 2 + cB * t) +
                     S * (--(t pow 2) + (&7 / &50) * cB * t - cB + t)` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false
     [CNFU_EQ_HINT `(&143 / &50) * C + &2 * S` (ASSUME `cB pow 2 + t pow 2 = &1`)];
    ALL_TAC] THEN
  MP_TAC(SPECL [`C:real`; `S:real`; `cB:real`; `t:real`] CNFU_SCALAR_ENTRANCE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  NLIN_FACTS_TAC []
   [`&9 / &25 < t pow 2`; `cB <= &4 / &5`; `cB + (&7 / &50) * t < &1`;
    `&0 < cB * (C - S)`; `&0 < C * cB - S * t`] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [MP_TAC(SPECL [`cD:real`; `--r`; `uD:real`; `vD:real`; `aD:real`;
                  `&143 / &50`; `&1`; `t:real`; `cB:real`] ABT_STRICT_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cD:real`; `--r`; `uD:real`; `vD:real`; `aD:real`;
                `&143 / &50`; `&1`; `r:real`; `cD:real`] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`cD:real`; `--r`; `uD:real`; `vD:real`; `aD:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&143 / &50) * r + cD < ABT_lower cB (--t) uB vB aB r cD` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`&0 <= r * t + cD * cB`] THEN
  ASM_CASES_TAC `&0 <= r * cB - cD * t` THENL
   [MP_TAC(SPECL [`cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`; `t:real`;
                  `r:real`; `cD:real`] C977NCO_LOWER_NEGATIVE_POS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    (let X = `(&7 / &50) * t pow 2 + cB * t - cB - t`
    and Y = `&1 - t pow 2 + (&7 / &50) * cB * t + t - cB` in
    let sub tm = subst [X,`XX:real`; Y,`YY:real`] tm in
    NLIN_FACTS_TAC [] (map sub
     [`&0 <= (r * cB - cD * t) * (((&143 / &50) * cB - t) - (uB + aB))`;
      `&0 <= (r * t + cD * cB) * ((&2 * cB + &3 * t) - (vB + aB))`;
      `&0 <= ((r * cB - cD * t) + (r * t + cD * cB)) * (aB - &1)`;
      `&0 <= cB * (&1 - t)`; `&0 <= t * (&1 - (&7 / &50) * t)`; `XX <= &0`;
      `&0 <= (r * cB - cD * t) * --XX`;
      `&0 <= cD * (&1 - cB - (&7 / &50) * t)`]) THEN
    SUBGOAL_THEN (sub `r * XX + cD * YY <= &0`) ASSUME_TAC THENL
     [MATCH_MP_TAC CNFU_NONPOS_CANCEL THEN EXISTS_TAC `cB:real` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      NLIN_TAC ~deg2:false
       [CNFU_EQ_HINT `cD * ((&7 / &50) * t - &1)` (ASSUME `cB pow 2 + t pow 2 = &1`)];
      ALL_TAC] THEN
    NLIN_TAC ~deg2:false
     [CNFU_EQ_HINT `(&143 / &50) * r + &2 * cD` (ASSUME `cB pow 2 + t pow 2 = &1`)]);
    POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    SUBGOAL_THEN `ABT_lower cB (--t) uB vB aB r cD =
                  (r * cB - cD * t) * (uB + aB) + (r * t + cD * cB) * vB` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
      SUBGOAL_THEN `abs(r * cB + cD * --t) = --(r * cB - cD * t) /\
                    abs(--r * --t + cD * cB) = r * t + cD * cB` (fun th -> REWRITE_TAC[th]) THENL
       [CONJ_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
    MP_TAC(SPECL [`C:real`; `S:real`; `cB:real`; `t:real`; `cD:real`; `r:real`]
      CNFU_MIXED_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= cD * (C - S)`; `&0 <= S * (cD - r)`; `&0 <= C * cD - S * r`;
      `&0 <= --(r * cB - cD * t) * (ABT_lower cB (--t) uB vB aB C S - &2 * (C + S))`;
      `&0 < (C * cB - S * t) * (ABT_lower cB (--t) uB vB aB r cD - ((&143 / &50) * r + cD))`;
      `&0 <= (C * cD - S * r) * (&2 * cB + &3 * t - &1 - vB)`;
      `&0 <= --(r * cB - cD * t) * (C * cB - S * t)`;
      `&0 <= (--(r * cB - cD * t) * (C * cB - S * t)) * (aB - &1)`] THEN
    NLIN_TAC ~deg2:false
     [CNFU_EQ_HINT `(C * cD - S * r) * vB` (ASSUME `cB pow 2 + t pow 2 = &1`);
      CNFU_EQ_HINT `--(r * cB - cD * t)` (ASSUME `ABT_lower cB (--t) uB vB aB C S =
         (C * cB - S * t) * uB + (C * t + S * cB) * vB`);
      CNFU_EQ_HINT `C * cB - S * t` (ASSUME `ABT_lower cB (--t) uB vB aB r cD =
                  (r * cB - cD * t) * (uB + aB) + (r * t + cD * cB) * vB`)]]);;
