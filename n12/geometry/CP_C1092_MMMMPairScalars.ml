(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMMPairScalars.lean                      *)
(* (namespace N12Compact.C1092MMMMPairScalars).                              *)
(* Normal is c977cc_normal; normal_bounds is C977CC_NORMAL_BOUNDS.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C1092MPS_NORMAL_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `c977cc_normal x y`) (concl th) then
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th)
    else NO_TAC));;

(* products of two factors whose signs follow linearly from the assumptions *)
let C1092MPS_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     REPEAT CONJ_TAC THEN
     FIRST [ASM_REAL_ARITH_TAC; MATCH_ACCEPT_TAC REAL_LE_POW_2; NLIN_TAC []];
     ALL_TAC]) tms;;

(* x <= 0 from b * x <= 0 with b > 0 *)
let C1092MPS_POS_MUL = prove
 (`forall b x. &0 < b /\ b * x <= &0 ==> x <= &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < b * x` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]);;

(* Lean: sine_bound *)
let C1092MPS_SINE_BOUND = prove
 (`forall b t. c977cc_normal b t ==> t <= &5 / &7`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092MPS_NORMAL_TAC THEN
  C1092MPS_PROD_TAC [`&0 <= (b - t) * (b + t)`] THEN
  NLIN_TAC [SQ_NONNEG `t - &5 / &7`]);;

(* Lean: negative_transverse_ge *)
let C1092MPS_NEGATIVE_TRANSVERSE_GE = prove
 (`forall d r b t. c977cc_normal d r /\ c977cc_normal b t /\ &0 <= b * r - t * d
     ==> d * (&1 - b + t - t pow 2) + r * (--(&39 / &100) - b - t + b * t) <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPS_NORMAL_TAC THEN
  MATCH_MP_TAC C1092MPS_POS_MUL THEN EXISTS_TAC `b:real` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `b - t`] [`b * t <= &1 / &2`] THEN
  C1092MPS_PROD_TAC
   [`&0 <= d * (&1 + &39 / &100 * t - b)`;
    `&0 <= (b * r - t * d) * (&39 / &100 + b + t - b * t)`] THEN
  SUBGOAL_THEN
   `b * (d * (&1 - b + t - t pow 2) + r * (--(&39 / &100) - b - t + b * t)) =
    d * (b - &1 - (&39 / &100) * t) +
    (b * r - t * d) * (--(&39 / &100) - b - t + b * t)` SUBST1_TAC THENL
   [UNDISCH_TAC `b pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: one_minus *)
let C1092MPS_ONE_MINUS = prove
 (`forall b t. c977cc_normal b t ==> &1 - b <= (&3 / &5) * t pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092MPS_NORMAL_TAC THEN
  C1092MPS_PROD_TAC [`&0 <= t pow 2 * ((&3 / &5) * (&1 + b) - &1)`] THEN
  SUBGOAL_THEN `&0 <= (&3 / &5) * t pow 2 - (&1 - b)` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (&1 + b) * ((&1 - b) - (&3 / &5) * t pow 2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 <= t pow 2 * ((&3 / &5) * (&1 + b) - &1)` THEN
    UNDISCH_TAC `b pow 2 + t pow 2 = &1` THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* Lean: negative_transverse_le *)
let C1092MPS_NEGATIVE_TRANSVERSE_LE = prove
 (`forall d r b t. c977cc_normal d r /\ c977cc_normal b t /\ &0 < t
     ==> d * (&1 - b - (&13 / &20) * t pow 2 - (&1 / &25) * b * t) +
         r * (--(&7 / &20) - (&1 / &25) * t pow 2 + (&13 / &20) * b * t - t) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `t:real`] C1092MPS_ONE_MINUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092MPS_NORMAL_TAC THEN
  C1092MPS_PROD_TAC [`&0 < b * t`; `&0 <= t * (&1 - b)`] THEN
  SUBGOAL_THEN `&1 - b - (&13 / &20) * t pow 2 - (&1 / &25) * b * t < &0 /\
                --(&7 / &20) - (&1 / &25) * t pow 2 + (&13 / &20) * b * t - t <= &0`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `t:real`]; ALL_TAC] THEN
  C1092MPS_PROD_TAC
   [`&0 < d * --(&1 - b - (&13 / &20) * t pow 2 - (&1 / &25) * b * t)`;
    `&0 <= r * --(--(&7 / &20) - (&1 / &25) * t pow 2 + (&13 / &20) * b * t - t)`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: negative_longitudinal_ge *)
let C1092MPS_NEGATIVE_LONGITUDINAL_GE = prove
 (`forall d r b t. c977cc_normal d r /\ c977cc_normal b t /\ &0 <= b * r - t * d
     ==> b * (&7 / &10 - d - (&7 / &20) * r pow 2 - (&3 / &20) * d * r) +
         t * (&17 / &20 - r - (&3 / &20) * r pow 2 + (&7 / &20) * d * r) <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C1092MPS_SINE_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092MPS_NORMAL_TAC THEN
  MATCH_MP_TAC C1092MPS_POS_MUL THEN EXISTS_TAC `d:real` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MPS_PROD_TAC [`&0 <= (d - r) * (d + r)`; `&0 <= d * r`] THEN
  SUBGOAL_THEN `r pow 2 <= &1 / &2` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &17 / &20 - r - (&3 / &20) * r pow 2 + (&7 / &20) * d * r`
    ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MPS_PROD_TAC
   [`&0 <= b * (&1 - (&7 / &10) * (d + r))`;
    `&0 <= (b * r - t * d) * (&17 / &20 - r - (&3 / &20) * r pow 2 + (&7 / &20) * d * r)`] THEN
  SUBGOAL_THEN
   `d * (b * (&7 / &10 - d - (&7 / &20) * r pow 2 - (&3 / &20) * d * r) +
         t * (&17 / &20 - r - (&3 / &20) * r pow 2 + (&7 / &20) * d * r)) =
    b * ((&7 / &10) * (d + r) - &1) -
    (b * r - t * d) * (&17 / &20 - r - (&3 / &20) * r pow 2 + (&7 / &20) * d * r)`
   SUBST1_TAC THENL
   [UNDISCH_TAC `d pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: negative_longitudinal_le *)
let C1092MPS_NEGATIVE_LONGITUDINAL_LE = prove
 (`forall d r b t. c977cc_normal d r /\ c977cc_normal b t
     ==> b + t - (b * d + t * r) * (&1 - (&7 / &20) * (d + r)) <= &27 / &28`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPS_NORMAL_TAC THEN
  C1092MPS_PROD_TAC
   [`&0 <= (&1 - (&7 / &20) * (d + r)) * ((b - t) * (d - r))`;
    `&0 <= (d + r - &1) * (&13 / &20 - (&7 / &20) * (d + r))`] THEN
  SUBGOAL_THEN `&13 / &20 <= (d + r) * (&1 - (&7 / &20) * (d + r))` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MPS_PROD_TAC
   [`&0 <= (b + t) * ((d + r) * (&1 - (&7 / &20) * (d + r)) - &13 / &20)`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: positive_longitudinal *)
let C1092MPS_POSITIVE_LONGITUDINAL = prove
 (`forall d r. c977cc_normal d r
     ==> &7 / &10 - d - (&7 / &20) * r pow 2 - (&3 / &20) * d * r <= &0 /\
         --(&17 / &20) + r + (&3 / &20) * r pow 2 - (&7 / &20) * d * r < &0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C1092MPS_SINE_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092MPS_NORMAL_TAC THEN
  C1092MPS_PROD_TAC [`&0 <= d * r`; `&0 <= r * (d - r)`] THEN
  CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `r:real`]);;

(* Lean: positive_transverse *)
let C1092MPS_POSITIVE_TRANSVERSE = prove
 (`forall d r b t. c977cc_normal d r /\ c977cc_normal b t /\ &0 < t
     ==> --d * (b + t - &1 - (&61 / &100) * b * t) +
         r * (t - b - &39 / &100 - (&61 / &100) * t pow 2) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPS_NORMAL_TAC THEN
  C1092MPS_PROD_TAC [`&0 < b * t`] THEN
  SUBGOAL_THEN `&1 < b + t` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `b + t - &1 - (&61 / &100) * b * t =
                (b + t - &1) * (&1 - (&61 / &200) * (b + t + &1))` ASSUME_TAC THENL
   [UNDISCH_TAC `b pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092MPS_PROD_TAC [`&0 < (b + t - &1) * (&1 - (&61 / &200) * (b + t + &1))`] THEN
  SUBGOAL_THEN `t - b - &39 / &100 - (&61 / &100) * t pow 2 <= &0` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `t:real`]; ALL_TAC] THEN
  C1092MPS_PROD_TAC
   [`&0 < d * (b + t - &1 - (&61 / &100) * b * t)`;
    `&0 <= r * --(t - b - &39 / &100 - (&61 / &100) * t pow 2)`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: small_of_support *)
let C1092MPS_SMALL_OF_SUPPORT = prove
 (`forall d r b t a u v.
     c977cc_normal d r /\ c977cc_normal b t /\ &1 < a /\ &0 < u /\ &0 < v /\
     u <= (&7 / &20) * (d + r) /\
     a * (&1 + b * r + t * d) <= b + t + (b * r + t * d) * u - (b * d - t * r) * v
     ==> r < &7 / &50 /\ &99 / &100 < d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C1092MPS_SINE_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092MPS_NORMAL_TAC THEN
  C1092MPS_PROD_TAC [`&0 <= (b - t) * d`; `&0 <= t * (d - r)`; `&0 <= b * r`;
                     `&0 <= t * d`] THEN
  SUBGOAL_THEN `&0 <= b * d - t * r /\ &0 <= b * r + t * d` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MPS_PROD_TAC
   [`&0 < (a - &1) * (&1 + b * r + t * d)`;
    `&0 <= (b * r + t * d) * ((&7 / &20) * (d + r) - u)`;
    `&0 <= (b * d - t * r) * v`] THEN
  ABBREV_TAC `FF = &1 - r * (&1 - (&7 / &20) * (d + r))` THEN
  ABBREV_TAC `GG = &1 - d * (&1 - (&7 / &20) * (d + r))` THEN
  SUBGOAL_THEN `&1 < b * FF + t * GG` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["FF"; "GG"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(b * FF + t * GG) pow 2 + (t * FF - b * GG) pow 2 = FF pow 2 + GG pow 2`
    ASSUME_TAC THENL
   [UNDISCH_TAC `b pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&1 < FF pow 2 + GG pow 2` ASSUME_TAC THENL
   [C1092MPS_PROD_TAC [`&0 < (b * FF + t * GG - &1) * (b * FF + t * GG + &1)`] THEN
    MP_TAC(SPEC `t * FF - b * GG` REAL_LE_POW_2) THEN
    UNDISCH_TAC `(b * FF + t * GG) pow 2 + (t * FF - b * GG) pow 2 = FF pow 2 + GG pow 2` THEN
    UNDISCH_TAC `&0 < (b * FF + t * GG - &1) * (b * FF + t * GG + &1)` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `FF pow 2 + GG pow 2 - &1 =
                &2 - (&27 / &10) * (d + r) + (&329 / &400) * (d + r) pow 2` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["FF"; "GG"] THEN
    UNDISCH_TAC `d pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `d + r < &113 / &100` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MPS_PROD_TAC
     [`&0 <= (d + r - &113 / &100) * (&27 / &10 - (&329 / &400) * (d + r + &113 / &100))`] THEN
    POP_ASSUM MP_TAC THEN
    UNDISCH_TAC `FF pow 2 + GG pow 2 - &1 =
                 &2 - (&27 / &10) * (d + r) + (&329 / &400) * (d + r) pow 2` THEN
    UNDISCH_TAC `&1 < FF pow 2 + GG pow 2` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r < &7 / &50` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MPS_PROD_TAC
     [`&0 <= (r - &7 / &50) * (&99 / &50 - &2 * r)`;
      `&0 < (&113 / &100 - r - d) * (&113 / &100 - r + d)`] THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092MPS_PROD_TAC
   [`&0 <= (&99 / &100 - d) * (&99 / &100 + d)`;
    `&0 < (&7 / &50 - r) * (&7 / &50 + r)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: small_negative_longitudinal *)
let C1092MPS_SMALL_NEGATIVE_LONGITUDINAL = prove
 (`forall d r b t. c977cc_normal d r /\ c977cc_normal b t /\ r < &7 / &50 /\ &99 / &100 < d
     ==> b * (&27 / &20 - d - (&7 / &20) * d * r - (&17 / &20) * r pow 2) +
         t * (&1 + r - (&17 / &20) * d * r + (&7 / &20) * r pow 2) < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C1092MPS_ONE_MINUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092MPS_NORMAL_TAC THEN
  C1092MPS_PROD_TAC [`&0 <= d * r`; `&0 <= r * (&1 - d)`;
                     `&0 <= (&7 / &50 - r) * (&7 / &50 + r)`;
                     `&0 <= r * (d - &99 / &100)`;
                     `&0 <= r * (&47 / &250 - (&1 / &10) * r)`] THEN
  ABBREV_TAC `FF = &27 / &20 - d - (&7 / &20) * d * r - (&17 / &20) * r pow 2` THEN
  ABBREV_TAC `GG = &1 + r - (&17 / &20) * d * r + (&7 / &20) * r pow 2` THEN
  SUBGOAL_THEN `&0 <= FF /\ FF <= &9 / &25 /\ &1 <= GG /\ FF + GG <= &27 / &20`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["FF"; "GG"] THEN REPEAT CONJ_TAC THEN
    NLIN_TAC [SQ_NONNEG `r:real`]; ALL_TAC] THEN
  C1092MPS_PROD_TAC [`&0 <= (GG - FF) * (GG + FF)`; `&0 <= FF * GG`] THEN
  C1092MPS_PROD_TAC [`&0 <= (b + t) * ((GG - FF) * (GG + FF))`;
                     `&0 <= (b - t) pow 2 * (FF * GG)`] THEN
  C1092MPS_PROD_TAC [`&0 <= (b - t) * ((b + t) * ((GG - FF) * (GG + FF)))`] THEN
  SUBGOAL_THEN `(FF + GG) pow 2 - &2 * (b * FF + t * GG) pow 2 =
                (b - t) * ((b + t) * ((GG - FF) * (GG + FF))) +
                &2 * ((b - t) pow 2 * (FF * GG))` ASSUME_TAC THENL
   [UNDISCH_TAC `b pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `(FF + GG) pow 2 <= (&27 / &20) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * (b * FF + t * GG) pow 2 <= (&27 / &20) pow 2` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`b * FF + t * GG`,`x:real`) THEN GEN_TAC THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN
  NLIN_TAC [SQ_NONNEG `x - &1`]);;

(* Lean: small_negative_transverse *)
let C1092MPS_SMALL_NEGATIVE_TRANSVERSE = prove
 (`forall d r b t. c977cc_normal d r /\ c977cc_normal b t /\ r < &7 / &50 /\
             &99 / &100 < d /\ &0 < t
     ==> d * (&1 - b - (&13 / &20) * t pow 2 - (&1 / &25) * b * t) +
         r * (&7 / &20 + (&1 / &25) * t pow 2 - (&13 / &20) * b * t + t) < r / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPS_NORMAL_TAC THEN
  C1092MPS_PROD_TAC [`&0 <= t pow 2 * ((&59 / &100) * (&1 + b) - &1)`;
                     `&0 < b * t`; `&0 <= t * (b - &7 / &10)`] THEN
  SUBGOAL_THEN `&1 - b <= (&59 / &100) * t pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MPS_PROD_TAC [`&0 < (&1 + b) * ((&1 - b) - (&59 / &100) * t pow 2)`] THEN
    POP_ASSUM MP_TAC THEN
    UNDISCH_TAC `&0 <= t pow 2 * ((&59 / &100) * (&1 + b) - &1)` THEN
    UNDISCH_TAC `b pow 2 + t pow 2 = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `f = &1 - b - (&13 / &20) * t pow 2 - (&1 / &25) * b * t` THEN
  ABBREV_TAC `g = &7 / &20 + (&1 / &25) * t pow 2 - (&13 / &20) * b * t + t` THEN
  SUBGOAL_THEN `f < &0 /\ f <= --(&3 / &50) * t pow 2 - (&1 / &25) * b * t`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `t:real`]; ALL_TAC] THEN
  ASM_CASES_TAC `g <= &1 / &2` THENL
   [C1092MPS_PROD_TAC [`&0 < d * --f`; `&0 <= r * (&1 / &2 - g)`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  C1092MPS_PROD_TAC [`&0 < (d - &99 / &100) * --f`;
                     `&0 < (&7 / &50 - r) * (g - &1 / &2)`] THEN
  SUBGOAL_THEN `--(&21 / &1000) + (&2429 / &50000) * t - (&269 / &5000) * t pow 2 < &0`
    ASSUME_TAC THENL [NLIN_TAC [SQ_NONNEG `t - &2429 / &5380`]; ALL_TAC] THEN
  UNDISCH_TAC `&7 / &20 + (&1 / &25) * t pow 2 - (&13 / &20) * b * t + t = g` THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: small_positive_longitudinal *)
let C1092MPS_SMALL_POSITIVE_LONGITUDINAL = prove
 (`forall d r. c977cc_normal d r /\ r < &7 / &50 /\ &99 / &100 < d
     ==> &7 / &10 - d - (&7 / &20) * r pow 2 + (&3 / &20) * d * r < &0 /\
         --(&17 / &20) - r + (&3 / &20) * r pow 2 + (&7 / &20) * d * r < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPS_NORMAL_TAC THEN
  C1092MPS_PROD_TAC [`&0 <= r * (&1 - d)`; `&0 <= (&7 / &50 - r) * (&7 / &50 + r)`;
                     `&0 <= d * r`] THEN
  CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `r:real`]);;

(* Lean: small_positive_transverse *)
let C1092MPS_SMALL_POSITIVE_TRANSVERSE = prove
 (`forall d r b t. c977cc_normal d r /\ c977cc_normal b t /\ r < &7 / &50 /\
             &99 / &100 < d /\ &9 / &20 < t /\ b < &9 / &10
     ==> &0 < d * (b + t - &1 - (&61 / &100) * b * t) -
              r * (b - t - &11 / &100 + (&61 / &100) * t pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `t:real`] C1092MPS_SINE_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092MPS_NORMAL_TAC THEN
  C1092MPS_PROD_TAC [`&0 <= (b - t) * (b + t)`] THEN
  SUBGOAL_THEN `t pow 2 <= &1 / &2` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&67 / &50 < b + t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MPS_PROD_TAC [`&0 <= (t - &9 / &20) * (&89 / &50 - &2 * t)`;
                       `&0 <= (&67 / &50 - t - b) * (&67 / &50 - t + b)`] THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  C1092MPS_PROD_TAC
   [`&0 < (b + t - &67 / &50) * (&1 - (&61 / &200) * (b + t + &67 / &50))`] THEN
  SUBGOAL_THEN `b + t - &1 - (&61 / &100) * b * t - &48671 / &500000 =
                (b + t - &67 / &50) * (&1 - (&61 / &200) * (b + t + &67 / &50))`
    ASSUME_TAC THENL
   [UNDISCH_TAC `b pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&19 / &200 < b + t - &1 - (&61 / &100) * b * t /\
                b - t - &11 / &100 + (&61 / &100) * t pow 2 < &129 / &200`
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MPS_PROD_TAC
   [`&0 < (d - &99 / &100) * (b + t - &1 - (&61 / &100) * b * t)`;
    `&0 <= r * (&129 / &200 - (b - t - &11 / &100 + (&61 / &100) * t pow 2))`] THEN
  ASM_REAL_ARITH_TAC);;
