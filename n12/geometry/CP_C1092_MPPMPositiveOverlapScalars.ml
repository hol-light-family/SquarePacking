(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMPositiveOverlapScalars.lean          *)
(* (N12Compact.C1092MPPMPositiveOverlap).  Exact scalar comparisons for the  *)
(* centered positive overlap.  Frame is c1092onh_frame; CommonCases bounds   *)
(* is CCCS_BOUNDS; NonpositivePredecessor: C1092NPP_*.                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNonpositivePredecessorScalars.ml";;

let C1092POS_PROD = C1092ONH_PROD;;

(* Lean: first_exit *)
let C1092POS_FIRST_EXIT = prove
 (`forall c s d t. c1092onh_frame c s /\ c1092onh_frame d t /\ &0 < t
     ==> (c * d - s * t) * (d + (&2 / &5) * t) + (c * t + s * d) * t <
         (c * d - s * t) + (c * t + s * d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092ONH_FRAME_TAC THEN
  C1092POS_PROD `&0 < d * t` THEN
  SUBGOAL_THEN `&1 - d - t + (&2 / &5) * d * t < &0 /\ t - d - (&2 / &5) * t * t <= &0`
  STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL [RASM_ARITH_TAC; C1092POS_PROD `&0 <= t * t` THEN RASM_ARITH_TAC];
   ALL_TAC] THEN
  C1092POS_PROD `&0 < c * --(&1 - d - t + (&2 / &5) * d * t)` THEN
  C1092POS_PROD `&0 <= s * --(t - d - (&2 / &5) * t * t)` THEN
  SUBGOAL_THEN `(c * d - s * t) * (d + (&2 / &5) * t) + (c * t + s * d) * t -
                ((c * d - s * t) + (c * t + s * d)) =
                c * (&1 - d - t + (&2 / &5) * d * t) + s * (t - d - (&2 / &5) * t * t)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `d * d + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: first_target *)
let C1092POS_FIRST_TARGET = prove
 (`forall c s d t. c1092onh_frame c s /\ c1092onh_frame d t /\ &0 < t
     ==> d + (&2 / &5) * t + (&7 / &20) * (c * t + s * d) * (c + s) < &1 + c * t + s * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092ONH_FRAME_TAC THEN
  C1092POS_PROD `&0 <= s * (d - t)` THEN
  C1092POS_PROD `&0 <= (c * t + s * d - t * (c + s)) * (&1 - (&7 / &20) * (c + s))` THEN
  C1092POS_PROD `&0 <= (c + s - &1) * (&13 / &20 - (&7 / &20) * (c + s))` THEN
  C1092POS_PROD `&0 <= t * ((c + s) * (&1 - (&7 / &20) * (c + s)) - &13 / &20)` THEN
  RASM_ARITH_TAC);;

(* Lean: final_source *)
let C1092POS_FINAL_SOURCE = prove
 (`forall c s d t. c1092onh_frame c s /\ c1092onh_frame d t /\ &0 < t
     ==> (c * d - s * t) * (d + t) + (c * t + s * d) * (t - (&2 / &5) * d) <
         (c * d - s * t) + (c * t + s * d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092ONH_FRAME_TAC THEN
  C1092POS_PROD `&0 < d * t` THEN
  SUBGOAL_THEN `&1 - d - t + (&3 / &5) * d * t < &0 /\
                t - d - &2 / &5 - (&3 / &5) * t * t <= &0` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL [RASM_ARITH_TAC; C1092POS_PROD `&0 <= t * t` THEN RASM_ARITH_TAC];
   ALL_TAC] THEN
  C1092POS_PROD `&0 < c * --(&1 - d - t + (&3 / &5) * d * t)` THEN
  C1092POS_PROD `&0 <= s * --(t - d - &2 / &5 - (&3 / &5) * t * t)` THEN
  SUBGOAL_THEN `(c * d - s * t) * (d + t) + (c * t + s * d) * (t - (&2 / &5) * d) -
                ((c * d - s * t) + (c * t + s * d)) =
                c * (&1 - d - t + (&3 / &5) * d * t) +
                s * (t - d - &2 / &5 - (&3 / &5) * t * t)` ASSUME_TAC THENL
  [UNDISCH_TAC `d * d + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: shallow *)
let C1092POS_SHALLOW = prove
 (`forall c s d t H. c1092onh_frame c s /\ c1092onh_frame d t /\
     H <= (&7 / &20) * (c + s) /\
     &1 + c * t + s * d < d + t + (c * t + s * d) * H
     ==> c + s < &113 / &100 /\ s < &7 / &50`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092NPP_RELATIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092ONH_FRAME_TAC THEN
  C1092POS_PROD `&0 <= (c * t + s * d) * ((&7 / &20) * (c + s) - H)` THEN
  ABBREV_TAC `P = &1 - s * (&1 - (&7 / &20) * (c + s))` THEN
  ABBREV_TAC `Q = &1 - c * (&1 - (&7 / &20) * (c + s))` THEN
  SUBGOAL_THEN `&1 < P * d + Q * t` ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["P"; "Q"] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(P * d + Q * t) * (P * d + Q * t) + (P * t - Q * d) * (P * t - Q * d) =
                P * P + Q * Q` ASSUME_TAC THENL
  [UNDISCH_TAC `d * d + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `P * P + Q * Q - &1 =
                &2 - (&27 / &10) * (c + s) + (&329 / &400) * (c + s) * (c + s)`
  ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["P"; "Q"] THEN UNDISCH_TAC `c * c + s * s = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092POS_PROD `&0 < (P * d + Q * t - &1) * (P * d + Q * t + &1)` THEN
  C1092POS_PROD `&0 <= (P * t - Q * d) * (P * t - Q * d)` THEN
  SUBGOAL_THEN `&0 < &2 - (&27 / &10) * (c + s) + (&329 / &400) * (c + s) * (c + s)`
  ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c + s < &113 / &100` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092POS_PROD `&0 <= (c + s - &113 / &100) *
                         --(--(&27 / &10) + (&329 / &400) * (c + s + &113 / &100))` THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092POS_PROD `&0 <= (s - &7 / &50) * --(s + &7 / &50 - &113 / &100)` THEN
  C1092POS_PROD `&0 < (&113 / &100 - s - c) * (&113 / &100 - s + c)` THEN
  RASM_ARITH_TAC);;

(* Lean: last_impossible *)
let C1092POS_LAST_IMPOSSIBLE = prove
 (`forall c s d t H. c1092onh_frame c s /\ c1092onh_frame d t /\
     H <= (&7 / &20) * (c + s) /\ H <= s /\
     &1 + c * t + s * d < d + t + (c * t + s * d) * H
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `H:real`] C1092POS_SHALLOW) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092NPP_RELATIVE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&1 - s + s pow 2`; `&1 - c + c * s`; `d:real`; `t:real`; `&1`]
    C1092NPP_NORM_LE) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `c1092onh_frame d t` THEN SIMP_TAC[c1092onh_frame]; REAL_ARITH_TAC;
    ALL_TAC] THEN
   C1092ONH_FRAME_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
   C1092POS_PROD `&0 <= s * (&1 / &5 - s)` THEN
   C1092POS_PROD `&0 <= c * s` THEN
   C1092POS_PROD `&0 <= s * (&1 - c)` THEN
   SUBGOAL_THEN `&0 <= &1 - s + s * s /\ &0 <= &1 - c + c * s /\
                 &1 - s + s * s <= &1 - (&4 / &5) * s /\ &1 - c + c * s <= &2 * s`
   STRIP_ASSUME_TAC THENL
   [C1092POS_PROD `&0 <= s * s` THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   C1092POS_PROD `&0 <= (&1 - (&4 / &5) * s - (&1 - s + s * s)) *
                         (&1 - (&4 / &5) * s + (&1 - s + s * s))` THEN
   C1092POS_PROD `&0 <= (&2 * s - (&1 - c + c * s)) * (&2 * s + (&1 - c + c * s))` THEN
   C1092POS_PROD `&0 <= s * (&8 / &5 - (&116 / &25) * s)` THEN
   RASM_ARITH_TAC;
   DISCH_TAC] THEN
  C1092ONH_FRAME_TAC THEN
  C1092POS_PROD `&0 <= (c * t + s * d) * (s - H)` THEN
  REWRITE_TAC[REAL_POW_2] THEN UNDISCH_TAC
   `(&1 - s + s pow 2) * d + (&1 - c + c * s) * t <= &1` THEN
  REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN RASM_ARITH_TAC);;
