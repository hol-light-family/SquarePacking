(* ========================================================================= *)
(* Port of Compact/Geometry/UpperRightNegativeTopBounds.lean (Jatloe,        *)
(* N12-jatloe; namespace N12Compact.UpperRightNegativeTopBounds).            *)
(* Continuous margins for a positive northeast corner and a negative top    *)
(* square.                                                                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/UpperRightCornerLongitudinalBounds.ml";;

let URNTB_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let URNTB_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;

let URNTB_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN
                  (FIRST_ASSUM ACCEPT_TAC ORELSE CONV_TAC REAL_RAT_REDUCE_CONV ORELSE
                   RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

(* Lean: arc *)
let URNTB_ARC = prove
 (`forall c s. c977cc_normal c s ==> &1 + (&41 / &50) * c * s <= c + s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN URNTB_NORMAL_TAC THEN
  URNTB_PROD_TAC `c + s - &1` `&1 - (&41 / &100) * (c + s + &1)` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: products (private) *)
let URNTB_PRODUCTS = prove
 (`forall c s. c977cc_normal c s ==> &0 <= c * s /\ c * s <= &1 / &2 /\ s <= &5 / &7`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN URNTB_NORMAL_TAC THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC;
   NLIN_TAC [SQ_NONNEG `c - s:real`]; RASM_ARITH_TAC]);;

(* Lean: forward_lower *)
let URNTB_FORWARD_LOWER = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s
     ==> &0 <= &1 + e * (c + s - &44 / &25 + (&61 / &100) * s pow 2 - (&13 / &20) * c * s) +
               f * (c - s - &5 / &4 + (&13 / &20) * s pow 2 + (&61 / &100) * c * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  URNTB_USE URNTB_PRODUCTS [`c:real`; `s:real`] THEN
  URNTB_USE URNTB_ARC [`c:real`; `s:real`] THEN
  URNTB_USE URCLB_DISK_MARGIN [`e:real`; `f:real`; `&19 / &25`; `&31 / &50`] THEN
  URNTB_NORMAL_TAC THEN
  SUBGOAL_THEN `--(&19 / &25) <= c + s - &44 / &25 + (&61 / &100) * s pow 2 -
                                 (&13 / &20) * c * s` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false [SQ_NONNEG `s:real`]; ALL_TAC] THEN
  URNTB_PROD_TAC `c - s` `&1 - (&63 / &100) * c - s / &50` THEN
  SUBGOAL_THEN `c - s - &5 / &4 + (&13 / &20) * s pow 2 + (&61 / &100) * c * s + &31 / &50 =
                (c - s) * (&1 - (&63 / &100) * c - s / &50)` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  URNTB_PROD_TAC `e:real`
    `(c + s - &44 / &25 + (&61 / &100) * s pow 2 - (&13 / &20) * c * s) - --(&19 / &25)` THEN
  URNTB_PROD_TAC `f:real`
    `c - s - &5 / &4 + (&13 / &20) * s pow 2 + (&61 / &100) * c * s + &31 / &50` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: forward_upper *)
let URNTB_FORWARD_UPPER = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s
     ==> &0 <= s + e * (&1 - c - (&44 / &25) * s + c * s) + f * ((&2 / &5) * s - s pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  URNTB_USE URNTB_PRODUCTS [`c:real`; `s:real`] THEN
  URNTB_USE URCLB_DISK_MARGIN [`e:real`; `f:real`; `&19 / &25`; `&11 / &35`] THEN
  URNTB_NORMAL_TAC THEN
  URNTB_PROD_TAC `&1 - c` `&1 - s` THEN
  URNTB_PROD_TAC `s:real` `&5 / &7 - s` THEN
  URNTB_PROD_TAC `e:real` `(&1 - c) * (&1 - s)` THEN
  URNTB_PROD_TAC `f:real` `s * (&5 / &7 - s)` THEN
  URNTB_PROD_TAC `s:real` `&1 - &19 / &25 * e - &11 / &35 * f` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: coefficients (private) *)
let URNTB_COEFFICIENTS = prove
 (`forall e f. c977cc_normal e f
     ==> --(&19 / &25) <= e + f - &63 / &50 - e pow 2 / &2 - (&3 / &5) * e * f /\
         --(&1 / &20) <= e - f - (&3 / &5) * e pow 2 + e * f / &2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  URNTB_USE URNTB_PRODUCTS [`e:real`; `f:real`] THEN
  URNTB_USE URNTB_ARC [`e:real`; `f:real`] THEN URNTB_NORMAL_TAC THEN
  CONJ_TAC THENL
  [NLIN_TAC ~deg2:false [SQ_NONNEG `f:real`];
   URNTB_PROD_TAC `e - f` `&1 - (&3 / &5) * e` THEN NLIN_TAC ~deg2:false []]);;

(* Lean: reverse_lower_upper *)
let URNTB_REVERSE_LOWER_UPPER = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s
     ==> &0 <= &1 + c * (e + f - &63 / &50 - e pow 2 / &2 - (&3 / &5) * e * f) +
               s * (e - f - (&3 / &5) * e pow 2 + e * f / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  URNTB_USE URNTB_COEFFICIENTS [`e:real`; `f:real`] THEN
  URNTB_USE URCLB_DISK_MARGIN [`c:real`; `s:real`; `&19 / &25`; `&1 / &20`] THEN
  URNTB_NORMAL_TAC THEN
  URNTB_PROD_TAC `c:real`
    `(e + f - &63 / &50 - e pow 2 / &2 - (&3 / &5) * e * f) - --(&19 / &25)` THEN
  URNTB_PROD_TAC `s:real` `(e - f - (&3 / &5) * e pow 2 + e * f / &2) - --(&1 / &20)` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: reverse_upper_upper *)
let URNTB_REVERSE_UPPER_UPPER = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s
     ==> &0 <= c + s - &1 +
               s * (c * (e + f - &63 / &50 - e pow 2 / &2 - (&3 / &5) * e * f) +
                    s * (e - f - (&3 / &5) * e pow 2 + e * f / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  URNTB_USE URNTB_COEFFICIENTS [`e:real`; `f:real`] THEN
  URNTB_USE URNTB_PRODUCTS [`c:real`; `s:real`] THEN
  URNTB_USE URNTB_ARC [`c:real`; `s:real`] THEN
  URNTB_NORMAL_TAC THEN
  URNTB_PROD_TAC `c * s`
    `(e + f - &63 / &50 - e pow 2 / &2 - (&3 / &5) * e * f) - --(&19 / &25)` THEN
  URNTB_PROD_TAC `s pow 2` `(e - f - (&3 / &5) * e pow 2 + e * f / &2) - --(&1 / &20)` THEN
  URNTB_PROD_TAC `s:real` `c - s` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: reverse_lower_lower *)
let URNTB_REVERSE_LOWER_LOWER = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s
     ==> &0 <= c * (&1 - e) * (&1 - f) + f * (&1 - (&19 / &25) * c) + s * f * (&1 - f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN URNTB_NORMAL_TAC THEN
  URNTB_PROD_TAC `c:real` `&1 - e` THEN
  URNTB_PROD_TAC `c * (&1 - e)` `&1 - f` THEN
  URNTB_PROD_TAC `f:real` `&1 - (&19 / &25) * c` THEN
  URNTB_PROD_TAC `s:real` `f:real` THEN
  URNTB_PROD_TAC `s * f` `&1 - f` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: reverse_upper_lower *)
let URNTB_REVERSE_UPPER_LOWER = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s
     ==> &0 <= c * f * (&1 - c) + s * c * (&1 - e) * (&1 - f) +
               s * f * (&1 - s * f - (&19 / &25) * c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  URNTB_USE URNTB_PRODUCTS [`e:real`; `f:real`] THEN
  URNTB_USE URCLB_DISK_MARGIN [`c:real`; `s:real`; `&19 / &25`; `&11 / &35`] THEN
  URNTB_NORMAL_TAC THEN
  URNTB_PROD_TAC `&1 - c` `(&3 / &5) * c - &2 / &5` THEN
  NLIN_FACTS_TAC [] [`(&2 / &5) * s pow 2 <= c * (&1 - c)`] THEN
  URNTB_PROD_TAC `s pow 2` `&5 / &7 - f` THEN
  URNTB_PROD_TAC `s:real` `&1 - &19 / &25 * c - &11 / &35 * s` THEN
  SUBGOAL_THEN `&0 <= c * (&1 - c) + s * (&1 - s * f - (&19 / &25) * c)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  URNTB_PROD_TAC `f:real` `c * (&1 - c) + s * (&1 - s * f - (&19 / &25) * c)` THEN
  URNTB_PROD_TAC `s:real` `c:real` THEN
  URNTB_PROD_TAC `s * c` `&1 - e` THEN
  URNTB_PROD_TAC `(s * c) * (&1 - e)` `&1 - f` THEN
  NLIN_TAC ~deg2:false []);;
