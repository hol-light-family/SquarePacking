(* ========================================================================= *)
(* Port of Compact/Geometry/C849NegativeSupport.lean                         *)
(* (namespace N12Compact.C849NegativeSupport).                               *)
(* Uniform wall support for the negative-B transverse axis.                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C849NegativeLeftScalar.ml";;

let C849NS_LT_CANCEL = prove
 (`forall k x y. &0 < k /\ k * x < k * y ==> x < y`,
  MESON_TAC[REAL_LT_LMUL_EQ]);;

(* Lean: positive_shallow (private) *)
let C849NS_POSITIVE_SHALLOW = prove
 (`forall C S. &0 < C /\ &0 <= S /\ S <= C /\ C pow 2 + S pow 2 = &1
         ==> &0 <= &1 - (&19 / &25) * S + C * S - (&9 / &5) * C + (&4 / &5) * C pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] C849NLS_FRAME_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&19 / &25 <= C + S / &10` ASSUME_TAC THENL
   [ASM_CASES_TAC `S <= &3 / &5` THENL
     [NLIN_FACTS_TAC [SQ_NONNEG `C - &4 / &5`]
       [`&0 <= S * (&3 / &5 - S)`; `&4 / &5 <= C`] THEN RASM_ARITH_TAC;
      RASM_ARITH_TAC];
    ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`&0 <= S * ((C + S / &10) - &19 / &25)`] THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `&1 - C`]);;

(* Lean: positive_steep (private) *)
let C849NS_POSITIVE_STEEP = prove
 (`forall C S. &0 < C /\ &0 <= S /\ S <= C /\ C pow 2 + S pow 2 = &1
         ==> &0 <= &1 - (&19 / &25) * S + C * S + C pow 2 - &2 * C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] C849NLS_FRAME_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_CASES_TAC `&19 / &25 <= C` THENL
   [NLIN_FACTS_TAC [] [`&0 <= S * (C - &19 / &25)`] THEN
    NLIN_TAC ~deg2:false [SQ_NONNEG `&1 - C`];
    NLIN_FACTS_TAC []
     [`&0 <= (&19 / &25 - C) * (&31 / &25 - C)`; `&0 <= S * (C - &7 / &10)`] THEN
    NLIN_TAC ~deg2:false []]);;

(* Lean: negative_margin (private) *)
let C849NS_NEGATIVE_MARGIN = prove
 (`forall C u. &0 < C /\ &0 <= u /\ u <= C /\ C pow 2 + u pow 2 = &1
         ==> &0 <= (&19 / &25) * u - (&9 / &5) * C + (&9 / &5) * C pow 2 - (&1 / &5) * C * u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `u:real`] C849NLS_FRAME_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `u:real`]
   [`&0 <= &14 / &25 + (&14 / &25) * C + (&1 / &5) * u pow 2 - (&9 / &5) * C * u`;
    `&0 <= u * (&14 / &25 + (&14 / &25) * C + (&1 / &5) * u pow 2 - (&9 / &5) * C * u)`] THEN
  SUBGOAL_THEN
   `&0 <= (&1 + C) * ((&19 / &25) * u - (&9 / &5) * C + (&9 / &5) * C pow 2 -
                      (&1 / &5) * C * u)` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false
     [C849NLS_EQ_HINT `(&9 / &5) * C - (&1 / &5) * u` (ASSUME `C pow 2 + u pow 2 = &1`)];
    ALL_TAC] THEN
  NLIN_TAC []);;

(* Lean: sum_bound (private) *)
let C849NS_SUM_BOUND = prove
 (`forall C u. C pow 2 + u pow 2 = &1 ==> C + u <= &10 / &7`,
  REPEAT STRIP_TAC THEN NLIN_TAC [SQ_NONNEG `C - u`; SQ_NONNEG `C + u - &10 / &7`]);;

(* Lean: support *)
let C849NS_SUPPORT = prove
 (`forall a c t C S X Y R.
     &1 < a /\ &0 < c /\ &0 <= t /\ t <= c /\ &0 < C /\ abs S <= C /\
     C pow 2 + S pow 2 = &1 /\
     a * (C + abs S) / &2 <= C * (X + a / &2) - S * (Y + a / &2) /\
     --(&19 / &25) * S + (&187 / &100) * C <= Y /\
     X <= (&457 / &500) * C + &2 * S /\
     R = (t * C + c * S) * (X + a / &2) + (c * C - t * S) * (Y + a / &2) +
         a / &2 * (abs(t * C + c * S) + abs(c * C - t * S))
     ==> (&33 / &20) * t + (&47 / &20) * c < R \/
         ((&4 / &5) * c <= t /\ t + (&287 / &100) * c < R)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `--C <= S /\ S <= C` STRIP_ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= S` THENL
   [(* S >= 0 *)
    SUBGOAL_THEN `abs S = S` SUBST_ALL_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= t * C + c * S`; `&0 <= (c - t) * C`; `&0 <= t * (C - S)`;
      `&0 <= c * C - t * S`] THEN
    SUBGOAL_THEN `abs(t * C + c * S) = t * C + c * S /\ abs(c * C - t * S) = c * C - t * S`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= (t * C + c * S) * (C * X - S * Y - a * S)`;
      `&0 <= c * (Y - (--(&19 / &25) * S + (&187 / &100) * C))`;
      `&0 <= C * (t * C + c * S)`;
      `&0 < (a - &1) * (c + C * (t * C + c * S))`] THEN
    ABBREV_TAC `R = (t * C + c * S) * (X + a / &2) + (c * C - t * S) * (Y + a / &2) +
         a / &2 * ((t * C + c * S) + (c * C - t * S))` THEN
    SUBGOAL_THEN `c * (&1 - (&19 / &25) * S + (&187 / &100) * C + C * S) + t * C pow 2 < C * R`
      ASSUME_TAC THENL
     [EXPAND_TAC "R" THEN NLIN_TAC ~deg2:false
       [C849NLS_EQ_HINT `c * (Y + a)` (ASSUME `C pow 2 + S pow 2 = &1`)];
      ALL_TAC] THEN
    MP_TAC(SPECL [`C:real`; `S:real`] C849NLS_FRAME_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_CASES_TAC `t <= (&4 / &5) * c` THENL
     [MP_TAC(SPECL [`C:real`; `S:real`] C849NS_POSITIVE_SHALLOW) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      NLIN_FACTS_TAC []
       [`&0 <= c * (&1 - (&19 / &25) * S + C * S - (&9 / &5) * C + (&4 / &5) * C pow 2)`;
        `&0 <= C * (&33 / &20 - C)`;
        `&0 <= ((&4 / &5) * c - t) * (C * (&33 / &20 - C))`] THEN
      DISJ1_TAC THEN MATCH_MP_TAC C849NS_LT_CANCEL THEN EXISTS_TAC `C:real` THEN
      ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false [];
      MP_TAC(SPECL [`C:real`; `S:real`] C849NS_POSITIVE_STEEP) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      NLIN_FACTS_TAC []
       [`&0 <= c * (&1 - (&19 / &25) * S + C * S + C pow 2 - &2 * C)`;
        `&0 <= C * (&1 - C)`; `&0 <= (c - t) * (C * (&1 - C))`] THEN
      DISJ2_TAC THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC C849NS_LT_CANCEL THEN EXISTS_TAC `C:real` THEN
      ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false []];
    ALL_TAC] THEN
  (* S < 0 *)
  POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
  SUBGOAL_THEN `abs S = --S` SUBST_ALL_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C pow 2 + (--S) pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= C * X - S * Y`; `&0 < c * C`; `&0 <= t * --S`; `&0 < c * C - t * S`] THEN
  SUBGOAL_THEN `abs(c * C - t * S) = c * C - t * S` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[REAL_ABS_REFL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(SPECL [`C:real`; `--S`] C849NLS_FRAME_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`C:real`; `--S`] C849NS_SUM_BOUND) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `&0 <= t * C + c * S` THENL
   [SUBGOAL_THEN `abs(t * C + c * S) = t * C + c * S` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= (t * C + c * S) * (C * X - S * Y)`;
      `&0 <= c * (Y - ((&19 / &25) * --S + (&187 / &100) * C))`;
      `&0 < C * ((t * C + c * S) + (c * C - t * S))`;
      `&0 < (a - &1) * (C * ((t * C + c * S) + (c * C - t * S)))`] THEN
    ABBREV_TAC `R = (t * C + c * S) * (X + a / &2) + (c * C - t * S) * (Y + a / &2) +
         a / &2 * ((t * C + c * S) + (c * C - t * S))` THEN
    SUBGOAL_THEN `c * ((&19 / &25) * --S + (&187 / &100) * C + C pow 2 - C * --S) +
                  t * (C pow 2 + C * --S) < C * R` ASSUME_TAC THENL
     [EXPAND_TAC "R" THEN NLIN_TAC ~deg2:false
       [C849NLS_EQ_HINT `c * Y` (ASSUME `C pow 2 + S pow 2 = &1`)];
      ALL_TAC] THEN
    MP_TAC(SPECL [`C:real`; `--S`] C849NS_NEGATIVE_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= c * ((&19 / &25) * --S - (&9 / &5) * C + (&9 / &5) * C pow 2 -
                  (&1 / &5) * C * --S)`] THEN
    ASM_CASES_TAC `t <= (&4 / &5) * c` THENL
     [NLIN_FACTS_TAC []
       [`&0 <= C * (&33 / &20 - C - --S)`;
        `&0 <= ((&4 / &5) * c - t) * (C * (&33 / &20 - C - --S))`] THEN
      DISJ1_TAC THEN MATCH_MP_TAC C849NS_LT_CANCEL THEN EXISTS_TAC `C:real` THEN
      ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false [];
      NLIN_FACTS_TAC []
       [`&0 <= C * (&1 - C)`; `&0 <= --S * (&1 - --S)`; `&1 <= C + --S`;
        `&0 <= C * (C + --S - &1)`;
        `&0 <= (t - (&4 / &5) * c) * (C * (C + --S - &1))`] THEN
      DISJ2_TAC THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC C849NS_LT_CANCEL THEN EXISTS_TAC `C:real` THEN
      ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false []];
    POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    SUBGOAL_THEN `abs(t * C + c * S) = --(t * C + c * S)` (fun th -> REWRITE_TAC[th]) THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
    DISJ1_TAC THEN
    NLIN_FACTS_TAC []
     [`(((&457 / &500) * C - &2 * --S) - X) * (t * C + c * S) <= &0`;
      `&0 <= (c * C - t * S) * (Y - ((&19 / &25) * --S + (&187 / &100) * C))`;
      `&0 < (a - &1) * (c * C - t * S)`] THEN
    SUBGOAL_THEN
     `c * (C - &12 / &25 + (&13 / &100) * (--S) pow 2 - (&77 / &500) * C * --S) +
      t * (--S - &92 / &125 - (&77 / &500) * (--S) pow 2 - (&13 / &100) * C * --S) +
      (&33 / &20) * t + (&47 / &20) * c <
      (t * C + c * S) * (X + a / &2) + (c * C - t * S) * (Y + a / &2) +
      a / &2 * (--(t * C + c * S) + (c * C - t * S))` ASSUME_TAC THENL
     [NLIN_TAC ~deg2:false
       [C849NLS_EQ_HINT `c:real` (ASSUME `C pow 2 + (--S) pow 2 = &1`);
        C849NLS_EQ_HINT `t:real` (ASSUME `C pow 2 + (--S) pow 2 = &1`)];
      ALL_TAC] THEN
    NLIN_FACTS_TAC [SQ_NONNEG `S:real`]
     [`&0 <= C * --S`;
      `--S - &92 / &125 - (&77 / &500) * (--S) pow 2 - (&13 / &100) * C * --S <= &0`;
      `&0 <= --(--S - &92 / &125 - (&77 / &500) * (--S) pow 2 - (&13 / &100) * C * --S) *
             --(t * C + c * S)`;
      `&0 < &1 - (&12 / &25) * C - (&89 / &100) * --S`;
      `&0 < c * (&1 - (&12 / &25) * C - (&89 / &100) * --S)`] THEN
    SUBGOAL_THEN
     `&0 < C * (c * (C - &12 / &25 + (&13 / &100) * (--S) pow 2 - (&77 / &500) * C * --S) +
               t * (--S - &92 / &125 - (&77 / &500) * (--S) pow 2 - (&13 / &100) * C * --S))`
      ASSUME_TAC THENL
     [NLIN_TAC ~deg2:false
       [C849NLS_EQ_HINT `c * (&1 - (&77 / &500) * --S)` (ASSUME `C pow 2 + (--S) pow 2 = &1`)];
      ALL_TAC] THEN
    NLIN_TAC []]);;
