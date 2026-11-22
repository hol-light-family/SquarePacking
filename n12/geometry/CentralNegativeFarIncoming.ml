(* ========================================================================= *)
(* Port of Compact/Geometry/CentralNegativeFarIncoming.lean                  *)
(* (namespace N12Compact.CentralNegativeFarIncoming).                        *)
(* A negative central incoming support reduces to the horizontal test.       *)
(* Squares are 5-tuples (B.s = -t, D.s = -r); Lean upper/lower are           *)
(* ABT_upper/ABT_lower; CentralNegativeFarUpper.impossible is                *)
(* CNFU_IMPOSSIBLE.                                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/CentralNegativeFarUpper.ml";;

let CNFI_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

let CNFI_LE_CANCEL = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

let CNFI_POS_CANCEL = prove
 (`forall k x. &0 < k /\ &0 < k * (x - &2) ==> &2 < x`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: horizontal_nonpos (private) *)
let CNFI_HORIZONTAL_NONPOS = prove
 (`forall c t. c977cc_normal c t /\ t <= &63 / &100
         ==> &43 / &50 - c - t + (&7 / &50) * t pow 2 + c * t <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC []
   [`t pow 2 <= (&63 / &100) pow 2`; `&77 / &100 <= c`; `&6031 / &10000 <= c pow 2`;
    `&0 <= t * (&63 / &100 - t)`;
    `&0 <= &63 / &100 + t - (&63 / &100) pow 2 - (&63 / &100) * t - t pow 2`;
    `&0 <= (&63 / &100 - t) * (&63 / &100 + t - (&63 / &100) pow 2 - (&63 / &100) * t -
                               t pow 2)`;
    `t pow 2 * (&1 - t) <= &146853 / &1000000`;
    `&0 <= (c pow 2 - &6031 / &10000) * (&1 + c)`;
    `&0 <= (&6031 / &10000) * (c - &77 / &100)`] THEN
  MATCH_MP_TAC(REAL_ARITH `forall x. &0 <= &0 - x ==> x <= &0`) THEN
  MATCH_MP_TAC CNFI_LE_CANCEL THEN EXISTS_TAC `&1 + c` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC ~deg2:false
   [CNFI_EQ_HINT `t - &1 + (&7 / &50) * (&1 + c)` (ASSUME `c pow 2 + t pow 2 = &1`)]);;

(* Lean: parallel_short (private) *)
let CNFI_PARALLEL_SHORT = prove
 (`forall c t. c977cc_normal c t ==> (&43 / &50) * c + t / &2 <= &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_TAC [SQ_NONNEG `c - &43 / &50`; SQ_NONNEG `t - &1 / &2`]);;

(* Lean: last_margin (private) *)
let CNFI_LAST_MARGIN = prove
 (`forall C S c t. c977cc_normal C S /\ c977cc_normal c t /\ C * t - S * c <= &0
     ==> C * (&43 / &50 - c - (&51 / &100) * t pow 2 + (&13 / &20) * c * t) -
         S * (&3 / &20 - (&13 / &20) * t pow 2 - (&51 / &100) * c * t + t) <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CNFI_PARALLEL_SHORT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  let X = `&43 / &50 - c - (&51 / &100) * t pow 2 + (&13 / &20) * c * t`
  and Y = `&3 / &20 - (&13 / &20) * t pow 2 - (&51 / &100) * c * t + t` in
  let sub tm = subst [X,`XX:real`; Y,`YY:real`] tm in
  NLIN_FACTS_TAC [SQ_NONNEG `c - t`] (map sub
   [`&0 <= (c + t - &1) * (&10 / &7 - (c + t))`; `&0 <= c * t`;
    `&1 + (&41 / &50) * c * t <= c + t`;
    `&0 <= (c - t) * (c + t)`; `t pow 2 <= &1 / &2`; `c * t <= &1 / &2`;
    `XX - YY <= &0`]) THEN
  SUBGOAL_THEN (sub `c * XX - t * YY = (&43 / &50) * c + t / &2 - &1`) ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_CASES_TAC `c:real = t` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(S:real) = C` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `S <= C /\ C <= S ==> (S:real) = C`) THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC CNFI_LE_CANCEL THEN EXISTS_TAC `t:real` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; NLIN_TAC ~deg2:false []]; ALL_TAC] THEN
    NLIN_FACTS_TAC [] (map (subst [`t:real`,`c:real`] o sub)
     [`&0 <= C * --(XX - YY)`]) THEN
    NLIN_TAC ~deg2:false [];
    SUBGOAL_THEN `&0 < c - t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_FACTS_TAC [] (map sub
     [`&0 <= (C - S) * (&1 - ((&43 / &50) * c + t / &2))`;
      `&0 <= (S * c - C * t) * --(XX - YY)`;
      `&0 <= (c - t) * --(C * XX - S * YY)`]) THEN
    MATCH_MP_TAC(REAL_ARITH `forall x. &0 <= &0 - x ==> x <= &0`) THEN
    MATCH_MP_TAC CNFI_LE_CANCEL THEN EXISTS_TAC `c - t` THEN
    ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false []]);;

(* Lean: horizontal *)
let CNFI_HORIZONTAL = prove
 (`forall cB sB uB vB aB t C S.
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal C S /\ c977cc_normal cB t /\ sB = --t /\ &1 <= aB /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     uB + aB <= (&143 / &50) * cB - t /\ vB + aB <= &2 * cB + &3 * t /\
     cB + (&13 / &5) * t <= vB /\
     &2 * C - (&3 / &2) * S < ABT_lower cB sB uB vB aB C (--S)
     ==> &2 < ABT_lower cB sB uB vB aB (&1) (&0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sB:real = --t`)) THEN
  C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= C * cB`; `&0 <= S * t`; `&0 <= C * cB + S * t`] THEN
  SUBGOAL_THEN `ABT_lower cB (--t) uB vB aB (&1) (&0) = cB * uB + t * vB` SUBST1_TAC THENL
   [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
    SUBGOAL_THEN `abs(&1 * cB + &0 * --t) = cB /\ abs(--(&1) * --t + &0 * cB) = t`
      (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= C * t - S * cB` THENL
   [SUBGOAL_THEN `ABT_lower cB (--t) uB vB aB C (--S) =
                  (C * cB + S * t) * uB + (C * t - S * cB) * vB` ASSUME_TAC THENL
     [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
      SUBGOAL_THEN `abs(C * cB + --S * --t) = C * cB + S * t /\
                    abs(--C * --t + --S * cB) = C * t - S * cB` (fun th -> REWRITE_TAC[th]) THENL
       [CONJ_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
    (let X = `&43 / &50 - cB - t + (&7 / &50) * t pow 2 + cB * t`
    and Y = `&1 / &2 - t pow 2 + (&7 / &50) * cB * t + t - cB` in
    let sub tm = subst [X,`XX:real`; Y,`YY:real`] tm in
    NLIN_FACTS_TAC [] (map sub
     [`&0 <= (C * cB + S * t) * (((&143 / &50) * cB - t) - (uB + aB))`;
      `&0 <= (C * t - S * cB) * ((&2 * cB + &3 * t) - (vB + aB))`;
      `&0 <= ((C * cB + S * t) + (C * t - S * cB)) * (aB - &1)`]) THEN
    SUBGOAL_THEN (sub `&0 < C * XX - S * YY`) ASSUME_TAC THENL
     [NLIN_TAC ~deg2:false
       [CNFI_EQ_HINT `(&143 / &50) * C - &2 * S` (ASSUME `cB pow 2 + t pow 2 = &1`)];
      ALL_TAC] THEN
    SUBGOAL_THEN `&63 / &100 < t` ASSUME_TAC THENL
     [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
      MP_TAC(SPECL [`cB:real`; `t:real`] CNFI_HORIZONTAL_NONPOS) THEN
      MP_TAC(SPECL [`cB:real`; `t:real`] CNFI_PARALLEL_SHORT) THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN (sub `cB * XX - t * YY = (&43 / &50) * cB + t / &2 - &1`) ASSUME_TAC THENL
       [UNDISCH_TAC `cB pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      ASM_CASES_TAC `&0 < t` THENL
       [NLIN_FACTS_TAC [] (map sub
         [`&0 <= (C * t - S * cB) * --XX`;
          `&0 <= S * (&1 - ((&43 / &50) * cB + t / &2))`;
          `&0 < t * (C * XX - S * YY)`]) THEN
        NLIN_TAC ~deg2:false
         [CNFI_EQ_HINT `S:real` (ASSUME (sub `cB * XX - t * YY = (&43 / &50) * cB + t / &2 - &1`))];
        SUBGOAL_THEN `t = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `S = &0` SUBST_ALL_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH `&0 <= S /\ S <= &0 ==> S = &0`) THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC(REAL_ARITH `forall x. &0 <= &0 - x ==> x <= &0`) THEN
          MATCH_MP_TAC CNFI_LE_CANCEL THEN EXISTS_TAC `cB:real` THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC; NLIN_TAC ~deg2:false []]; ALL_TAC] THEN
        NLIN_FACTS_TAC [] [`&0 <= C * --(&43 / &50 - cB - &0 + (&7 / &50) * &0 pow 2 +
                                          cB * &0)`] THEN
        NLIN_TAC ~deg2:false []];
      ALL_TAC] THEN
    NLIN_FACTS_TAC [SQ_NONNEG `cB - t`]
     [`&0 <= t * (((&143 / &50) * cB - t) - (uB + aB))`;
      `&0 <= cB * (vB - (cB + (&13 / &5) * t))`;
      `&0 <= t * (aB - &1)`; `cB * t <= &1 / &2`;
      `&3 / &2 < --t * uB + cB * vB`;
      `&0 <= S * ((--t * uB + cB * vB) - &3 / &2)`] THEN
    MATCH_MP_TAC CNFI_POS_CANCEL THEN EXISTS_TAC `C:real` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; NLIN_TAC ~deg2:false []]);
    ALL_TAC] THEN
  POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
  SUBGOAL_THEN `ABT_lower cB (--t) uB vB aB C (--S) =
                (C * cB + S * t) * uB + (C * t - S * cB) * (vB + aB)` ASSUME_TAC THENL
   [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
    SUBGOAL_THEN `abs(C * cB + --S * --t) = C * cB + S * t /\
                  abs(--C * --t + --S * cB) = --(C * t - S * cB)` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  UNDISCH_TAC `linside cB (--t) uB vB aB (&47 / &20) (&33 / &20)` THEN
  SIMP_TAC[C977NCO_NEGATIVE_BANDS] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`; `cB:real`; `t:real`] CNFI_LAST_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (C * cB + S * t) * (((&143 / &50) * cB - t) - (uB + aB))`;
    `&0 <= --(C * t - S * cB) * ((vB + aB) - (t * &47 / &20 + cB * &33 / &20))`;
    `&0 <= (C * cB + S * t) * (aB - &1)`] THEN
  NLIN_TAC ~deg2:false
   [CNFI_EQ_HINT `(&143 / &50) * C - (&33 / &20) * S` (ASSUME `cB pow 2 + t pow 2 = &1`)]);;

(* Lean: impossible *)
let CNFI_IMPOSSIBLE = prove
 (`forall cD sD uD vD aD cB sB uB vB aB r t C S.
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal C S /\ c977cc_normal cB t /\ c977cc_normal cD r /\
     sB = --t /\ sD = --r /\ &1 <= aB /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     linside cD sD uD vD aD (&143 / &50) (&1) /\
     uB + aB <= (&143 / &50) * cB - t /\ vB + aB <= &2 * cB + &3 * t /\
     cB + (&13 / &5) * t <= vB /\
     &2 * C - (&3 / &2) * S < ABT_lower cB sB uB vB aB C (--S) /\
     (ABT_upper cD sD uD vD aD t cB <= vB \/ vD + aD <= ABT_lower cB sB uB vB aB r cD)
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `t:real`;
                `C:real`; `S:real`] CNFI_HORIZONTAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `r:real`; `t:real`; `&1`; `&0`] CNFU_IMPOSSIBLE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE
     (REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC) ORELSE
     (CONV_TAC REAL_RAT_REDUCE_CONV THEN FIRST_ASSUM ACCEPT_TAC));
    REWRITE_TAC[]]);;
