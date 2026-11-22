(* ========================================================================= *)
(* Port of Compact/Geometry/C849NegativeLeftScalar.lean                      *)
(* (namespace N12Compact.C849NegativeLeftScalar).                            *)
(* Negative-L support margins for the actual negative-B endgame.             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* p * (l - r) = 0 from |- l = r : a hint for linear combinations.          *)
let C849NLS_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* Lean: frame_bounds *)
let C849NLS_FRAME_BOUNDS = prove
 (`forall c t. &0 < c /\ &0 <= t /\ t <= c /\ c pow 2 + t pow 2 = &1
         ==> &707 / &1000 <= c /\ c <= &1 /\ t <= &71 / &100 /\ c * t <= &1 / &2 /\
             &1 - c <= (&293 / &500) * t pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - &707 / &1000`; SQ_NONNEG `t:real`;
                  SQ_NONNEG `t - &71 / &100`; SQ_NONNEG `c - t`]
   [`&0 <= (c - t) * (c + t)`; `&707 / &1000 <= c`; `c <= &1`; `t <= &71 / &100`;
    `c * t <= &1 / &2`; `&0 <= (&1 - c) * ((&293 / &500) * (&1 + c) - &1)`] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

(* Lean: coefficient_two (private) *)
let C849NLS_COEFFICIENT_TWO = prove
 (`forall c t. &0 < c /\ &0 <= t /\ t <= c /\ c pow 2 + t pow 2 = &1
         ==> &2 + (&13 / &50) * t pow 2 + (&1 / &2) * c * t - c - t <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] C849NLS_FRAME_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `(&1 / &2) * t - (&13 / &50) * c`;
                  SQ_NONNEG `(&13 / &50) * t + (&1 / &2) * c - &4 / &7`]
   [`&0 <= t * (&71 / &100 - t)`; `&1 - c <= (&3 / &7) * t`;
    `(&13 / &50) * t + (&1 / &2) * c <= &4 / &7`;
    `&0 <= t * (&4 / &7 - ((&13 / &50) * t + (&1 / &2) * c))`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: coefficient_zero (private) *)
let C849NLS_COEFFICIENT_ZERO = prove
 (`forall c t. &0 < c /\ &0 <= t /\ t <= c /\ c pow 2 + t pow 2 = &1 /\ t <= (&3 / &5) * c
         ==> &2 - c - (&7 / &20) * t pow 2 - (&3 / &20) * c * t <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - &4 / &5`; SQ_NONNEG `t:real`]
   [`&0 <= ((&3 / &5) * c - t) * ((&3 / &5) * c + t)`; `&4 / &5 <= c`; `c <= &1`;
    `&0 <= (&1 - c) * ((&5 / &9) * (&1 + c) - &1)`; `&1 - c <= (&5 / &9) * t pow 2`;
    `&0 <= t * ((&3 / &5) * c - t)`; `&0 <= c * t`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: coefficient_one (private) *)
let C849NLS_COEFFICIENT_ONE = prove
 (`forall c t. &0 < c /\ &0 <= t /\ t <= c /\ c pow 2 + t pow 2 = &1 /\ (&3 / &5) * c <= t
         ==> &113 / &50 - c - (&61 / &100) * t pow 2 - (&13 / &20) * c * t <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] C849NLS_FRAME_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (&2 / &5 - c + t) * (&2 / &5 + c - t)`; `&21 / &50 <= c * t`] THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `t:real`]);;

(* Lean: nonnegative_relative_margin (private) *)
let C849NLS_NONNEGATIVE_RELATIVE_MARGIN = prove
 (`forall c t C u A Q.
     &0 < c /\ &0 <= t /\ t <= c /\ c pow 2 + t pow 2 = &1 /\
     &0 < C /\ &0 <= u /\ u <= C /\ C pow 2 + u pow 2 = &1 /\
     &0 <= t * C - c * u /\ A <= &1 /\ Q <= --t
     ==> A * C pow 2 + Q * C * u + (&457 / &500) * u pow 2 - C <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] C849NLS_FRAME_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`C:real`; `u:real`] C849NLS_FRAME_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `C:real`; SQ_NONNEG `u:real`]
   [`&0 <= (&1 - A) * C pow 2`; `&0 <= C * u`; `&0 <= (--t - Q) * (C * u)`;
    `&0 <= u * (t * C - c * u)`; `&0 <= (c - &1 / &2) * u pow 2`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: negative_relative_margin (private) *)
let C849NLS_NEGATIVE_RELATIVE_MARGIN = prove
 (`forall c t C u.
     &0 < c /\ &0 <= t /\ t <= c /\ c pow 2 + t pow 2 = &1 /\
     &0 < C /\ &0 <= u /\ u <= C /\ C pow 2 + u pow 2 = &1 /\
     t * C - c * u <= &0
     ==> C pow 2 * (&2 - c) + (&457 / &500) * u pow 2 - C - (&1 / &2 + t) * C * u +
         (&293 / &500) * c * C * (t * C - c * u) <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] C849NLS_FRAME_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`C:real`; `u:real`] C849NLS_FRAME_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `C:real`]
   [`&0 <= u * (C - u)`;
    `C pow 2 + (&457 / &500) * u pow 2 - C - (&1 / &2) * C * u <= &0`;
    `&0 <= t * C`; `(t * C) * (t * C - c * u) <= &0`;
    `&0 <= C pow 2 * (&1 - c)`] THEN
  SUBGOAL_THEN `c * (C pow 2 * (&1 - c) - t * C * u) <= &0` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false
     [C849NLS_EQ_HINT `C pow 2` (ASSUME `c pow 2 + t pow 2 = &1`)]; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`C pow 2 * (&1 - c) - t * C * u <= &0`; `&0 <= c * C`;
    `((&293 / &500) * c * C) * (t * C - c * u) <= &0`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: impossible *)
let C849NLS_IMPOSSIBLE = prove
 (`forall a c t C u U V W.
     &1 < a /\ &0 < c /\ &0 <= t /\ t <= c /\ c pow 2 + t pow 2 = &1 /\
     &0 < C /\ &0 <= u /\ u <= C /\ C pow 2 + u pow 2 = &1 /\
     a * C - (&457 / &500) * u pow 2 - &2 * C * u <= C * W /\
     U + a <= &2 * c - (&5 / &2) * t /\
     V <= (&33 / &20) * t + (&47 / &20) * c /\
     &2 * t + (&1543 / &500) * c <= V + a /\
     (U + a <= (&113 / &50) * c - &3 * t \/ V + a <= (&113 / &50) * t + &3 * c) /\
     W <= (c * C + t * u) * U + (t * C - c * u) * (V + a / &2) - a / &2 * abs(t * C - c * u)
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] C849NLS_FRAME_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 < c * C`; `&0 <= t * u`; `&0 < c * C + t * u`; `&0 <= C * (c * C + t * u)`;
    `&0 < (a - &1) * (C * (&1 + c * C + t * u))`;
    `C * (c * C + t * u) * (U + a) <= C * (c * C + t * u) * (&2 * c - (&5 / &2) * t)`] THEN
  ASM_CASES_TAC `&0 <= (t * C - c * u)` THENL
   [SUBGOAL_THEN `abs (t * C - c * u) = (t * C - c * u)` SUBST_ALL_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`C * W <= C * ((c * C + t * u) * U + (t * C - c * u) * (V + a / &2) - a / &2 * (t * C - c * u))`;
      `&0 <= C * (t * C - c * u)`] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [NLIN_FACTS_TAC []
       [`C * (t * C - c * u) * V <= C * (t * C - c * u) * ((&33 / &20) * t + (&47 / &20) * c)`] THEN
      ASM_CASES_TAC `t <= (&3 / &5) * c` THENL
       [MP_TAC(SPECL [`c:real`; `t:real`] C849NLS_COEFFICIENT_ZERO) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
        NLIN_FACTS_TAC [SQ_NONNEG `t:real`]
         [`-- (&1 / &2) + (&7 / &20) * c * t + (&3 / &20) * c pow 2 - t <= --t`] THEN
        MP_TAC(SPECL [`c:real`; `t:real`; `C:real`; `u:real`;
          `&2 - c - (&7 / &20) * t pow 2 - (&3 / &20) * c * t`;
          `-- (&1 / &2) + (&7 / &20) * c * t + (&3 / &20) * c pow 2 - t`]
          C849NLS_NONNEGATIVE_RELATIVE_MARGIN) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC];
        MP_TAC(SPECL [`c:real`; `t:real`] C849NLS_COEFFICIENT_ONE) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
        NLIN_FACTS_TAC [SQ_NONNEG `t:real`]
         [`-- &1 + (&61 / &100) * c * t + (&13 / &20) * c pow 2 - t <= --t`] THEN
        MP_TAC(SPECL [`c:real`; `t:real`; `C:real`; `u:real`;
          `&113 / &50 - c - (&61 / &100) * t pow 2 - (&13 / &20) * c * t`;
          `-- &1 + (&61 / &100) * c * t + (&13 / &20) * c pow 2 - t`]
          C849NLS_NONNEGATIVE_RELATIVE_MARGIN) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
        NLIN_FACTS_TAC []
         [`C * (c * C + t * u) * (U + a) <=
           C * (c * C + t * u) * ((&113 / &50) * c - &3 * t)`]];
      MP_TAC(SPECL [`c:real`; `t:real`] C849NLS_COEFFICIENT_TWO) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      NLIN_FACTS_TAC [SQ_NONNEG `&1 - c`]
       [`-- (&1 / &2) - (&13 / &50) * c * t - (&1 / &2) * c pow 2 - t + c <= --t`] THEN
      MP_TAC(SPECL [`c:real`; `t:real`; `C:real`; `u:real`;
        `&2 + (&13 / &50) * t pow 2 + (&1 / &2) * c * t - c - t`;
        `-- (&1 / &2) - (&13 / &50) * c * t - (&1 / &2) * c pow 2 - t + c`]
        C849NLS_NONNEGATIVE_RELATIVE_MARGIN) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      NLIN_FACTS_TAC []
       [`C * (t * C - c * u) * (V + a) <= C * (t * C - c * u) * ((&113 / &50) * t + &3 * c)`;
        `&0 < (a - &1) * (C * (&1 + c * C + t * u + (t * C - c * u)))`]];
    POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    SUBGOAL_THEN `abs (t * C - c * u) = --(t * C - c * u)` SUBST_ALL_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`C * W <= C * ((c * C + t * u) * U + (t * C - c * u) * (V + a / &2) - a / &2 * --(t * C - c * u))`;
      `C * (t * C - c * u) <= &0`;
      `C * (t * C - c * u) * (V + a) <= C * (t * C - c * u) * (&2 * t + (&1543 / &500) * c)`] THEN
    MP_TAC(SPECL [`c:real`; `t:real`; `C:real`; `u:real`]
      C849NLS_NEGATIVE_RELATIVE_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC]] THEN
  NLIN_TAC ~deg2:false
   [C849NLS_EQ_HINT `C pow 2` (ASSUME `c pow 2 + t pow 2 = &1`);
    C849NLS_EQ_HINT `C * u` (ASSUME `c pow 2 + t pow 2 = &1`)]);;
