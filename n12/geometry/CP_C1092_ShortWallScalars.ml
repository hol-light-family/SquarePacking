(* ========================================================================= *)
(* Port of Compact/Completion/C1092/ShortWallScalars.lean                    *)
(* (N12Compact.C1092ShortWallScalars).  Continuous scalar lemmas for the     *)
(* short-wall two-wall theorem.  Normal c s is c977cc_normal c s.            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

let C1092SWS_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092SWS_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092SWS_LIN_TAC; DISCH_TAC];;

(* unfold every c977cc_normal assumption and add its bounds *)
let C1092SWS_NORMAL_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `c977cc_normal x y`) (concl th) then
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2] th)
    else failwith "no"));;

(* Lean: allowance *)
let C1092SWS_allowance = new_definition
 `C1092SWS_allowance (c:real) (s:real) = (&1 - c) * (c + s - &1) / &2`;;

(* Lean: narrow_bounds *)
let C1092SWS_NARROW_BOUNDS = prove
 (`forall c s. c977cc_normal c s /\ &4 * s <= c
         ==> &24 / &25 <= c /\ s <= &1 / &4 /\ &1 - c <= (&25 / &49) * s pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092SWS_NORMAL_TAC THEN
  C1092SWS_LE_MUL_TAC `c - &4 * s` `c + &4 * s` THEN
  SUBGOAL_THEN `&24 / &25 <= c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`&0 < (&24 / &25 - c) * (c + &24 / &25)`] THEN
    C1092SWS_LIN_TAC;
    ALL_TAC] THEN
  C1092SWS_LE_MUL_TAC `c - &24 / &25` `&1 - c` THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN CONJ_TAC THEN C1092SWS_LIN_TAC);;

(* Lean: allowance_bounds *)
let C1092SWS_ALLOWANCE_BOUNDS = prove
 (`forall c s. c977cc_normal c s /\ &4 * s <= c
         ==> &0 <= C1092SWS_allowance c s /\ C1092SWS_allowance c s <= s / &50 /\
             C1092SWS_allowance c s <= &1 / &200`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092SWS_NARROW_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092SWS_NORMAL_TAC THEN
  C1092SWS_LE_MUL_TAC `&1 - c` `c + s - &1` THEN
  C1092SWS_LE_MUL_TAC `&1 / &25 - (&1 - c)` `c + s - &1` THEN
  C1092SWS_LE_MUL_TAC `&1 - c` `s - (c + s - &1)` THEN
  REWRITE_TAC[C1092SWS_allowance] THEN REPEAT CONJ_TAC THEN C1092SWS_LIN_TAC);;

(* Lean: cubic_baseline *)
let C1092SWS_CUBIC_BASELINE = prove
 (`forall c s. c977cc_normal c s /\ &4 * s <= c
         ==> (&2 / &5) * s pow 3 <=
             s pow 2 / &2 - (&1 - c) * (&1 - s) - s * C1092SWS_allowance c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092SWS_NARROW_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092SWS_NORMAL_TAC THEN
  C1092SWS_LE_MUL_TAC `s:real` `&1 / &4 - s` THEN
  C1092SWS_LE_MUL_TAC `s:real` `&1 - c` THEN
  SUBGOAL_THEN `(&8 / &5) * s <= s * (&3 - c - s) - (&1 - c)` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092SWS_LIN_TAC; ALL_TAC] THEN
  C1092SWS_LE_MUL_TAC `&1 - c` `s * (&3 - c - s) - (&1 - c) - (&8 / &5) * s` THEN
  SUBGOAL_THEN `&0 <= s * ((&1 - c) * (&1 - c))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_SQUARE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `s pow 2 / &2 - (&1 - c) * (&1 - s) - s * C1092SWS_allowance c s =
    (&1 - c) * (s * (&3 - c - s) - (&1 - c)) / &2 /\
    s * (&1 - c) * (&1 - c) = &2 * s * (&1 - c) - s pow 3`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[C1092SWS_allowance] THEN CONJ_TAC THEN
    UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN C1092SWS_LIN_TAC);;

(* Lean: negative_wall_baseline *)
let C1092SWS_NEGATIVE_WALL_BASELINE = prove
 (`forall c s. c977cc_normal c s /\ &4 * s <= c
         ==> &9 / &100 <= c - s - &303 / &500 + s pow 2 + c * s / &2 -
                          c * C1092SWS_allowance c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092SWS_NARROW_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092SWS_ALLOWANCE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092SWS_NORMAL_TAC THEN
  C1092SWS_LE_MUL_TAC `&1 - c` `C1092SWS_allowance c s` THEN
  C1092SWS_LE_MUL_TAC `c:real` `s:real` THEN
  C1092SWS_LE_MUL_TAC `s:real` `s:real` THEN
  REWRITE_TAC[REAL_POW_2] THEN C1092SWS_LIN_TAC);;

(* Lean: central_positive_below *)
let C1092SWS_CENTRAL_POSITIVE_BELOW = prove
 (`forall c s r t. c977cc_normal c s /\ c977cc_normal r t /\ &4 * s <= c /\ t <= s
             ==> &0 <= r * (&1 + c * r + s * t - &2 * c) - (&457 / &500) * s * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092SWS_NARROW_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `r:real`; `t:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092SWS_NORMAL_TAC THEN
  C1092SWS_LE_MUL_TAC `r:real` `r - c` THEN
  C1092SWS_LE_MUL_TAC `r:real` `&1 - c` THEN
  C1092SWS_LE_MUL_TAC `s:real` `t:real` THEN
  C1092SWS_LE_MUL_TAC `r * (&1 - c)` `&1 - r` THEN
  C1092SWS_LE_MUL_TAC `s * t` `r - &457 / &500` THEN
  C1092SWS_LIN_TAC);;

(* Lean: central_negative_below *)
let C1092SWS_CENTRAL_NEGATIVE_BELOW = prove
 (`forall c s r t. c977cc_normal c s /\ c977cc_normal r t /\ &4 * s <= c
             ==> &0 <= r + (c * r - s * t) * (r + t) - &2 * c * r +
                       (&457 / &500) * s * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092SWS_NORMAL_TAC THEN
  SUBGOAL_THEN `t / &2 <= r + t - &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `(&1 + r) * (&2 * r + t - &2) = t * (&1 + r - &2 * t)` ASSUME_TAC THENL
     [UNDISCH_TAC `r * r + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092SWS_LE_MUL_TAC `t:real` `&1 + r - &2 * t` THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`(&1 + r) * (&2 * r + t - &2) < &0`] THEN
    C1092SWS_LIN_TAC;
    ALL_TAC] THEN
  C1092SWS_LE_MUL_TAC `r:real` `&1 - c` THEN
  C1092SWS_LE_MUL_TAC `c:real` `r:real` THEN
  C1092SWS_LE_MUL_TAC `c * r` `r + t - &1 - t / &2` THEN
  C1092SWS_LE_MUL_TAC `s:real` `t:real` THEN
  C1092SWS_LE_MUL_TAC `s * t` `&3 / &5 - (r + t - &457 / &500)` THEN
  C1092SWS_LE_MUL_TAC `t:real` `c - &4 * s` THEN
  C1092SWS_LE_MUL_TAC `c:real` `t:real` THEN
  C1092SWS_LE_MUL_TAC `c * t` `r / &2 - &3 / &20` THEN
  C1092SWS_LIN_TAC);;

(* Lean: steep_short_point *)
let C1092SWS_STEEP_SHORT_POINT = prove
 (`forall c s. c977cc_normal c s /\ &16 * c / &25 <= s
         ==> ((&1293 / &1250) * c + (&591 / &2500) * s) pow 2 <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092SWS_NORMAL_TAC THEN
  C1092SWS_LE_MUL_TAC `s - &16 * c / &25` `s + &3 * c / &25` THEN
  C1092SWS_LE_MUL_TAC `c:real` `c:real` THEN
  C1092SWS_LE_MUL_TAC `c:real` `s:real` THEN
  C1092SWS_LE_MUL_TAC `s:real` `s:real` THEN
  REWRITE_TAC[REAL_POW_2] THEN C1092SWS_LIN_TAC);;

(* Lean: moderate_short_point *)
let C1092SWS_MODERATE_SHORT_POINT = prove
 (`forall c s. c977cc_normal c s /\ c <= &4 * s
         ==> &303 / &500 <= (&197 / &500) * c + s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092SWS_NORMAL_TAC THEN
  C1092SWS_LE_MUL_TAC `&4 * s - c` `&4 * s + &6 * c` THEN
  C1092SWS_LE_MUL_TAC `c:real` `s:real` THEN
  C1092SWS_LE_MUL_TAC `s:real` `s:real` THEN
  SUBGOAL_THEN `(&303 / &500) * (&303 / &500) <=
                ((&197 / &500) * c + s) * ((&197 / &500) * c + s)` MP_TAC THENL
   [C1092SWS_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&197 / &500) * c + s` MP_TAC THENL
   [C1092SWS_LIN_TAC; ALL_TAC] THEN
  SPEC_TAC(`(&197 / &500) * c + s`,`x:real`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT STRIP_TAC THEN NLIN_TAC []);;
