(* ========================================================================= *)
(* Port of Compact/Completion/C981/ShortRows/CoreScalars.lean                 *)
(* (N12Compact.C981CompletionShortScalars).  Continuous margins for the      *)
(* four-diamond central owner.                                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C981SR_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal; REAL_POW_2] th)) ns);;

let C981SR_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   REWRITE_TAC[REAL_LE_SQUARE] THEN ASM_REAL_ARITH_TAC; ALL_TAC];;

let C981SR_POS_OF_MUL = prove
 (`forall y k. &0 < k /\ &0 < k * y ==> &0 < y`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`&0`; `y:real`; `k:real`] REAL_LT_LMUL_EQ) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO]);;

(* Lean: Core (definition) *)
let c981sr_core = new_definition
 `c981sr_core (c:real) s <=>
    &24 / &25 <= c /\ c <= &1 /\ &0 <= s /\ s <= &13 / &50 /\ s <= (&9 / &35) * c`;;

let C981SR_CORE_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c981sr_core x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (REWRITE_RULE[c981sr_core] th)) ns);;

(* Lean: core_bounds *)
let C981SR_CORE_BOUNDS = prove
 (`forall c s. c977cc_normal c s /\ &35 * s <= &9 * c ==> c981sr_core c s`,
  REPEAT STRIP_TAC THEN C981SR_NORMAL_TAC THEN REWRITE_TAC[c981sr_core] THEN
  C981SR_PROD `&0 <= (&9 * c - &35 * s) * (&9 * c + &35 * s)` THEN
  SUBGOAL_THEN `&24 / &25 <= c` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C981SR_PROD `&0 <= (&24 / &25 - c) * (&24 / &25 + c)` THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: defect (private) *)
let C981SR_DEFECT = prove
 (`forall b t. c977cc_normal b t ==> &1 - b <= (&3 / &5) * t pow 2`,
  REPEAT STRIP_TAC THEN C981SR_NORMAL_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  C981SR_PROD `&0 <= (b - &2 / &3) * (&1 - b)` THEN ASM_REAL_ARITH_TAC);;

(* Lean: backward_u *)
let C981SR_BACKWARD_U = prove
 (`forall c s b t. c981sr_core c s /\ &0 < b /\ t <= &0 /\ --b <= t
     ==> &0 < b * (c - &7 / &10 + (&7 / &20) * s pow 2 + (&61 / &100) * c * s) +
              t * (s + &9 / &100 + (&61 / &100) * s pow 2 - (&7 / &20) * c * s)`,
  REPEAT STRIP_TAC THEN C981SR_CORE_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  C981SR_PROD `&0 <= s * (c - &24 / &25)` THEN
  C981SR_PROD `&0 <= s * (&1 - c)` THEN
  C981SR_PROD `&0 <= s * (&13 / &50 - s)` THEN
  C981SR_PROD `&0 <= s * s` THEN
  SUBGOAL_THEN `&0 <= s + &9 / &100 + (&61 / &100) * s * s - (&7 / &20) * c * s /\
                &13 / &100 < (c - &7 / &10 + (&7 / &20) * s * s + (&61 / &100) * c * s) -
                             (s + &9 / &100 + (&61 / &100) * s * s - (&7 / &20) * c * s)`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C981SR_PROD `&0 <= (s + &9 / &100 + (&61 / &100) * s * s - (&7 / &20) * c * s) * (t + b)` THEN
  C981SR_PROD `&0 < b * ((c - &7 / &10 + (&7 / &20) * s * s + (&61 / &100) * c * s) -
                         (s + &9 / &100 + (&61 / &100) * s * s - (&7 / &20) * c * s))` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: positive_own_v *)
let C981SR_POSITIVE_OWN_V = prove
 (`forall c s b t. c981sr_core c s /\ c977cc_normal b t
     ==> b * (&37 / &50 + (&61 / &100) * s pow 2 - (&7 / &20) * c * s + s) +
         t * (&27 / &20 - (&7 / &20) * s pow 2 - (&61 / &100) * c * s - c) < &1`,
  REPEAT STRIP_TAC THEN C981SR_CORE_TAC THEN C981SR_NORMAL_TAC THEN
  REWRITE_TAC[REAL_POW_2] THEN
  C981SR_PROD `&0 <= s * (c - &24 / &25)` THEN
  C981SR_PROD `&0 <= s * (&13 / &50 - s)` THEN
  C981SR_PROD `&0 <= s * s` THEN
  SUBGOAL_THEN
   `b * (&37 / &50 + (&83 / &100) * s) + t * (&39 / &100 - (&29 / &50) * s) < &1`
  ASSUME_TAC THENL
  [SUBGOAL_THEN `(&37 / &50 + (&83 / &100) * s) * (&37 / &50 + (&83 / &100) * s) +
                 (&39 / &100 - (&29 / &50) * s) * (&39 / &100 - (&29 / &50) * s) < &1`
   MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `(b * (&37 / &50 + (&83 / &100) * s) + t * (&39 / &100 - (&29 / &50) * s)) pow 2 +
     (b * (&39 / &100 - (&29 / &50) * s) - t * (&37 / &50 + (&83 / &100) * s)) pow 2 =
     (&37 / &50 + (&83 / &100) * s) * (&37 / &50 + (&83 / &100) * s) +
     (&39 / &100 - (&29 / &50) * s) * (&39 / &100 - (&29 / &50) * s)` MP_TAC THENL
   [UNDISCH_TAC `b * b + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   MP_TAC(SPEC `b * (&39 / &100 - (&29 / &50) * s) - t * (&37 / &50 + (&83 / &100) * s)`
     REAL_LE_POW_2) THEN
   SPEC_TAC(`b * (&37 / &50 + (&83 / &100) * s) + t * (&39 / &100 - (&29 / &50) * s)`,
            `X:real`) THEN
   SPEC_TAC(`b * (&39 / &100 - (&29 / &50) * s) - t * (&37 / &50 + (&83 / &100) * s)`,
            `Y:real`) THEN
   SPEC_TAC(`(&37 / &50 + (&83 / &100) * s) * (&37 / &50 + (&83 / &100) * s) +
             (&39 / &100 - (&29 / &50) * s) * (&39 / &100 - (&29 / &50) * s)`,`N:real`) THEN
   REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN REPEAT DISCH_TAC THEN
   NLIN_TAC [SQ_NONNEG `X - &1`]; ALL_TAC] THEN
  C981SR_PROD `&0 <= b * ((&37 / &50 + (&83 / &100) * s) -
       (&37 / &50 + (&61 / &100) * s * s - (&7 / &20) * c * s + s))` THEN
  C981SR_PROD `&0 <= t * ((&39 / &100 - (&29 / &50) * s) -
       (&27 / &20 - (&7 / &20) * s * s - (&61 / &100) * c * s - c))` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: negative_low *)
let C981SR_NEGATIVE_LOW = prove
 (`forall c s b u. c981sr_core c s /\ c977cc_normal b u
     ==> &0 < c * (b - &37 / &50 + (&13 / &20) * u pow 2 + (&9 / &20) * b * u) +
              s * (--(&7 / &20) - (&9 / &20) * u pow 2 + (&13 / &20) * b * u - u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `u:real`] C981SR_DEFECT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C981SR_CORE_TAC THEN C981SR_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  C981SR_PROD `&0 <= (b - u) * (b + u)` THEN
  C981SR_PROD `&0 <= b * u` THEN
  C981SR_PROD `&0 <= u * (&1 - b)` THEN
  C981SR_PROD `&0 <= u * (b - &7 / &10)` THEN
  C981SR_PROD `&0 <= u * u` THEN
  SUBGOAL_THEN `&0 <= b - &37 / &50 + (&13 / &20) * u * u + (&9 / &20) * b * u /\
                --(&7 / &20) - (&9 / &20) * u * u + (&13 / &20) * b * u - u <= &0`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C981SR_PROD `&0 <= (b - &37 / &50 + (&13 / &20) * u * u + (&9 / &20) * b * u) *
                     (c - &24 / &25)` THEN
  C981SR_PROD `&0 <= --(--(&7 / &20) - (&9 / &20) * u * u + (&13 / &20) * b * u - u) *
                     (&13 / &50 - s)` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: negative_steep *)
let C981SR_NEGATIVE_STEEP = prove
 (`forall c s b u. c981sr_core c s /\ c977cc_normal b u /\ (&10 / &37) * b <= u
     ==> &0 < c * ((&13 / &20) * b * u - (&9 / &100) * u pow 2) -
              s * (&7 / &20 + (&13 / &20) * u pow 2 + (&9 / &100) * b * u)`,
  REPEAT STRIP_TAC THEN C981SR_CORE_TAC THEN C981SR_NORMAL_TAC THEN
  REWRITE_TAC[REAL_POW_2] THEN
  C981SR_PROD `&0 <= b * u` THEN
  C981SR_PROD `&0 <= u * (b - u)` THEN
  C981SR_PROD `&0 <= (u - (&10 / &37) * b) * (b - u)` THEN
  C981SR_PROD `&0 <= u * u` THEN
  SUBGOAL_THEN `&0 < (&3 / &5) * b * u - (&13 / &50) * u * u - &23 / &250` ASSUME_TAC THENL
  [NLIN_TAC []; ALL_TAC] THEN
  C981SR_PROD `&0 <= ((&13 / &20) * b * u - (&9 / &100) * u * u) * (c - &24 / &25)` THEN
  C981SR_PROD `&0 <= (&7 / &20 + (&13 / &20) * u * u + (&9 / &100) * b * u) *
                     (&13 / &50 - s)` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: positive_small *)
let C981SR_POSITIVE_SMALL = prove
 (`forall c s b t. c981sr_core c s /\ c977cc_normal b t /\ t <= &13 / &50
     ==> &0 < c * (b - &37 / &50 + (&13 / &20) * t pow 2 - (&13 / &20) * b * t) +
              s * (--(&7 / &20) - (&13 / &20) * t pow 2 - (&13 / &20) * b * t + t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `t:real`] C981SR_DEFECT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C981SR_CORE_TAC THEN C981SR_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  C981SR_PROD `&0 <= t * (&1 - b)` THEN
  C981SR_PROD `&0 <= t * (&13 / &50 - t)` THEN
  C981SR_PROD `&0 <= t * (b - t)` THEN
  C981SR_PROD `&0 <= (t - &5 / &13) * (t - &5 / &13)` THEN
  C981SR_PROD `&0 <= t * t` THEN
  SUBGOAL_THEN `&0 <= b - &37 / &50 + (&13 / &20) * t * t - (&13 / &20) * b * t /\
                --(&7 / &20) - (&13 / &20) * t * t - (&13 / &20) * b * t + t <= &0`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C981SR_PROD `&0 <= (b - &37 / &50 + (&13 / &20) * t * t - (&13 / &20) * b * t) *
                     (c - &24 / &25)` THEN
  C981SR_PROD `&0 <= --(--(&7 / &20) - (&13 / &20) * t * t - (&13 / &20) * b * t + t) *
                     (&13 / &50 - s)` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: positive_low *)
let C981SR_POSITIVE_LOW = prove
 (`forall c s b t. c981sr_core c s /\ c977cc_normal b t
     ==> &0 < c * (b - &37 / &50 + (&13 / &20) * t pow 2 - (&9 / &20) * b * t) +
              s * (--(&7 / &20) - (&9 / &20) * t pow 2 - (&13 / &20) * b * t + t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `t:real`] C981SR_DEFECT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C981SR_CORE_TAC THEN C981SR_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  SUBGOAL_THEN `b * t <= &1 / &2` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `b - t:real`]; ALL_TAC] THEN
  C981SR_PROD `&0 <= t * (b - t)` THEN
  C981SR_PROD `&0 <= (t - &5 / &11) * (t - &5 / &11)` THEN
  C981SR_PROD `&0 <= t * t` THEN
  SUBGOAL_THEN `&0 <= b - &37 / &50 + (&13 / &20) * t * t - (&9 / &20) * b * t /\
                --(&7 / &20) - (&9 / &20) * t * t - (&13 / &20) * b * t + t <= &0`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C981SR_PROD `&0 <= (b - &37 / &50 + (&13 / &20) * t * t - (&9 / &20) * b * t) *
                     (c - &24 / &25)` THEN
  C981SR_PROD `&0 <= --(--(&7 / &20) - (&9 / &20) * t * t - (&13 / &20) * b * t + t) *
                     (&13 / &50 - s)` THEN
  SUBGOAL_THEN `&7 / &5 - (&5 / &12) * (b - t) * (b - t) <= b + t` ASSUME_TAC THENL
  [C981SR_PROD `&0 <= ((b + t) - &1) * (&10 / &7 - (b + t))` THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&24 / &25) * b + (&13 / &50) * t + (&507 / &1000) * t * t -
                     (&601 / &1000) * b * t - &4007 / &5000` ASSUME_TAC THENL
  [C981SR_PROD `&0 <= (b - t) * (&10 / &7 - (b + t))` THEN
   C981SR_PROD `&0 <= (b - t - &1 / &7) * (b - t - &1 / &7)` THEN
   NLIN_TAC []; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: positive_lower_u *)
let C981SR_POSITIVE_LOWER_U = prove
 (`forall c s b t. c981sr_core c s /\ c977cc_normal b t /\ &0 <= c * t - s * b
     ==> &0 < c * (b + t - &37 / &50 - (&1 / &5) * b * t) +
              s * (--(&4 / &5) - (&1 / &5) * t pow 2 - b + t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `t:real`] C981SR_DEFECT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C981SR_CORE_TAC THEN C981SR_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  C981SR_PROD `&0 <= t * t` THEN
  SUBGOAL_THEN `--(&4 / &5) - (&1 / &5) * t * t - b + t <= &0` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `t <= (&9 / &35) * b` THENL
  [MATCH_MP_TAC C981SR_POS_OF_MUL THEN EXISTS_TAC `b:real` THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   C981SR_PROD `&0 < c * (&1 - (&37 / &50) * b - t)` THEN
   C981SR_PROD `&0 <= (c * t - s * b) * --(--(&4 / &5) - (&1 / &5) * t * t - b + t)` THEN
   SUBGOAL_THEN
    `b * (c * (b + t - &37 / &50 - (&1 / &5) * b * t) +
          s * (--(&4 / &5) - (&1 / &5) * t * t - b + t)) =
     c * (&1 - (&37 / &50) * b - t) +
     (c * t - s * b) * --(--(&4 / &5) - (&1 / &5) * t * t - b + t)` SUBST1_TAC THENL
   [UNDISCH_TAC `b * b + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC;
   SUBGOAL_THEN `&6 / &25 <= t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&24 / &25 <= b` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
     C981SR_PROD `&0 < (&24 / &25 - b) * (&24 / &25 + b)` THEN
     C981SR_PROD `&0 < (&6 / &25 - t) * (&6 / &25 + t)` THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `t <= &3 / &4` ASSUME_TAC THENL
   [C981SR_PROD `&0 <= (b - t) * (b + t)` THEN NLIN_TAC []; ALL_TAC] THEN
   C981SR_PROD `&0 <= t * (&1 - b)` THEN
   C981SR_PROD `&0 <= (t - &6 / &25) * (&3 / &4 - t)` THEN
   SUBGOAL_THEN `&0 < (b + t - &37 / &50 - (&1 / &5) * b * t) +
                      (&9 / &35) * (--(&4 / &5) - (&1 / &5) * t * t - b + t)`
   ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   C981SR_PROD `&0 < c * ((b + t - &37 / &50 - (&1 / &5) * b * t) +
                          (&9 / &35) * (--(&4 / &5) - (&1 / &5) * t * t - b + t))` THEN
   C981SR_PROD `&0 <= --(--(&4 / &5) - (&1 / &5) * t * t - b + t) * ((&9 / &35) * c - s)` THEN
   ASM_REAL_ARITH_TAC]);;
