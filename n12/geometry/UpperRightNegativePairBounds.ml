(* ========================================================================= *)
(* Port of Compact/Geometry/UpperRightNegativePairBounds.lean                *)
(* (namespace N12Compact.UpperRightNegativePairBounds).                      *)
(* Three continuous support margins for the negative northeast corner and    *)
(* negative top square.  Normal c s is c977cc_normal c s;                    *)
(* UpperRightNegativeTopBounds.arc is URNTB_ARC.                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/UpperRightNegativeTopBounds.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

(* p * (l - r) = 0 from |- l = r *)
let URNPB_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* Lean: plus *)
let URNPB_PLUS = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s
     ==> &0 <= e + f - &33 / &20 + (&13 / &20) * f pow 2 +
              e pow 2 * (c + (&13 / &20) * s pow 2 - (&1 / &20) * c * s) +
              e * f * (s - &11 / &10 - (&1 / &20) * s pow 2 - (&13 / &20) * c * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `f:real`] URNTB_ARC) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s - &1 / &2`; SQ_NONNEG `e:real`]
   [`&0 <= e * f`; `&0 <= (&1 - c) * ((&3 / &5) * c - &2 / &5)`;
    `&1 - c <= (&3 / &5) * s pow 2`; `&0 <= s * (&1 - c)`;
    `&79 / &80 <= c + (&13 / &20) * s pow 2 - (&1 / &20) * c * s`;
    `&0 <= &1 - s / &20 - (&13 / &20) * c`;
    `&0 <= s * (&1 - s / &20 - (&13 / &20) * c)`;
    `--(&11 / &10) <= s - &11 / &10 - (&1 / &20) * s pow 2 - (&13 / &20) * c * s`;
    `&0 <= e pow 2 * ((c + (&13 / &20) * s pow 2 - (&1 / &20) * c * s) - &79 / &80)`;
    `&0 <= (e * f) * ((s - &11 / &10 - (&1 / &20) * s pow 2 - (&13 / &20) * c * s) +
                      &11 / &10)`;
    `&1 + (&4 / &5) * e * f <= e + f`; `&0 <= e * (e - f)`] THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `e:real`]);;

(* Lean: minus *)
let URNPB_MINUS = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s /\ e * s <= f * c
     ==> &0 <= e + f - &33 / &20 + (&13 / &20) * f pow 2 +
              e pow 2 * (c - s + (&13 / &20) * s pow 2 + (&61 / &100) * c * s) +
              e * f * (c + s - &44 / &25 + (&61 / &100) * s pow 2 - (&13 / &20) * c * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `f:real`] URNTB_ARC) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] URNTB_ARC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`]
   [`&0 <= e * f`; `&0 <= c * s`;
    `--(&19 / &25) <= c + s - &44 / &25 + (&61 / &100) * s pow 2 - (&13 / &20) * c * s`;
    `&0 <= (e * f) * ((c + s - &44 / &25 + (&61 / &100) * s pow 2 - (&13 / &20) * c * s) +
                      &19 / &25)`;
    `&0 <= &1 - (&63 / &100) * c - s / &50`;
    `&0 <= (c - s) * (&1 - (&63 / &100) * c - s / &50)`] THEN
  SUBGOAL_THEN `&63 / &100 <= c - s + (&13 / &20) * s pow 2 + (&61 / &100) * c * s`
    ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false [URNPB_EQ_HINT `&63 / &100` (ASSUME `c pow 2 + s pow 2 = &1`)];
    ALL_TAC] THEN
  ASM_CASES_TAC `&2 / &5 <= f` THENL
   [NLIN_FACTS_TAC [SQ_NONNEG `e:real`]
     [`&0 <= e pow 2 * ((c - s + (&13 / &20) * s pow 2 + (&61 / &100) * c * s) - &63 / &100)`;
      `&0 <= (&3 / &50) * f - e / &50`; `&0 <= e * ((&3 / &50) * f - e / &50)`] THEN
    NLIN_TAC ~deg2:false [];
    POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    MP_TAC(SPECL [`e:real`; `f:real`; `c:real`; `s:real`] C977CSB_SINE_ORDER) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    NLIN_FACTS_TAC [] [`&0 <= (&2 / &5 - s) * (&2 / &5 + s)`] THEN
    SUBGOAL_THEN `&9 / &10 <= c` ASSUME_TAC THENL
     [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
      NLIN_FACTS_TAC [] [`&0 <= (&9 / &10 - c) * (&9 / &10 + c)`] THEN
      NLIN_TAC ~deg2:false []; ALL_TAC] THEN
    NLIN_FACTS_TAC [SQ_NONNEG `s - &7 / &20`; SQ_NONNEG `e:real`]
     [`&0 <= s * (c - &9 / &10)`;
      `&4 / &5 <= c - s + (&13 / &20) * s pow 2 + (&61 / &100) * c * s`;
      `&0 <= e pow 2 * ((c - s + (&13 / &20) * s pow 2 + (&61 / &100) * c * s) - &4 / &5)`] THEN
    NLIN_TAC ~deg2:false [SQ_NONNEG `e:real`]]);;

(* Lean: upper *)
let URNPB_UPPER = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s /\ e * s <= f * c
     ==> &0 <= e * f * (&1 - c) + s * (e + f - f pow 2 + e * f * (c - &44 / &25) -
              e pow 2 * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `f:real`] URNTB_ARC) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `e:real`]
   [`&0 <= e * f`; `&0 <= e * (e - f)`;
    `&0 <= e + f - f pow 2 - (&44 / &25) * e * f`;
    `&0 <= e * (f * c - e * s)`;
    `&0 <= e + f - f pow 2 + e * f * (c - &44 / &25) - e pow 2 * s`;
    `&0 <= (e * f) * (&1 - c)`;
    `&0 <= s * (e + f - f pow 2 + e * f * (c - &44 / &25) - e pow 2 * s)`] THEN
  NLIN_TAC ~deg2:false []);;
