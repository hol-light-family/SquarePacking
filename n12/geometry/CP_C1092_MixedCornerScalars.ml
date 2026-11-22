(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MixedCornerScalars.lean                   *)
(* (namespace N12Compact.C1092MixedCornerScalars).                           *)
(* Normal is c977cc_normal.                                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C1092MCS_NORMAL_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `c977cc_normal x y`) (concl th) then
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th)
    else NO_TAC));;

let C1092MCS_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     REPEAT CONJ_TAC THEN
     FIRST [ASM_REAL_ARITH_TAC; MATCH_ACCEPT_TAC REAL_LE_POW_2; NLIN_TAC []];
     ALL_TAC]) tms;;

(* Lean: elementary *)
let C1092MCS_ELEMENTARY = prove
 (`forall c s. c977cc_normal c s ==> &7 / &10 < c /\ s pow 2 <= &1 / &2 /\ c * s <= &1 / &2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092MCS_NORMAL_TAC THEN
  C1092MCS_PROD_TAC [`&0 <= (c - s) * (c + s)`] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `c - s`]);;

(* Lean: common *)
let C1092MCS_COMMON = prove
 (`forall d r. c977cc_normal d r /\ &0 < r
     ==> &1 / &10 <= d - &9 / &10 + (&4 / &5) * r pow 2 /\
         &0 < r * (&1 - (&4 / &5) * d) /\ &0 < d + r - (&9 / &10) * d * r /\
         &1 / &50 <= d - &9 / &10 + (&4 / &5) * r pow 2 -
                     (&2 / &5) * (r * (&1 - (&4 / &5) * d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MCS_NORMAL_TAC THEN
  C1092MCS_PROD_TAC [`&0 <= (&1 - d) * ((&4 / &5) * d - &1 / &5)`;
                     `&0 < r * (&1 - (&4 / &5) * d)`;
                     `&0 <= r * (&1 - (&9 / &10) * d)`;
                     `&0 <= (&1 - d) * ((&4 / &5) * d - &1 / &5 - (&8 / &25) * r)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN NLIN_TAC []);;

(* Lean: nonnegative_pair *)
let C1092MCS_NONNEGATIVE_PAIR = prove
 (`forall d r c s. c977cc_normal d r /\ c977cc_normal c s /\ &0 < r
     ==> d * ((&1 / &5) * c pow 2 + (&1 / &2) * c * s - c) +
         r * (&1 / &10 + (&1 / &2) * s pow 2 - s + (&1 / &5) * c * s) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MCS_ELEMENTARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MCS_NORMAL_TAC THEN
  SUBGOAL_THEN `(&1 / &5) * c pow 2 + (&1 / &2) * c * s - c <= --(&1 / &4) /\
                ((&1 / &5) * c pow 2 + (&1 / &2) * c * s - c) +
                (&1 / &10 + (&1 / &2) * s pow 2 - s + (&1 / &5) * c * s) <= --(&1 / &5)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `s:real`]; ALL_TAC] THEN
  C1092MCS_PROD_TAC
   [`&0 <= (d - r) * --((&1 / &5) * c pow 2 + (&1 / &2) * c * s - c)`;
    `&0 < r * --(((&1 / &5) * c pow 2 + (&1 / &2) * c * s - c) +
                 (&1 / &10 + (&1 / &2) * s pow 2 - s + (&1 / &5) * c * s))`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: upper_u_pair *)
let C1092MCS_UPPER_U_PAIR = prove
 (`forall d r c s. c977cc_normal d r /\ c977cc_normal c s /\ &0 < r /\ s < (&2 / &5) * c
     ==> &9 / &10 < c /\ s < &2 / &5 /\
         d * ((&1 / &5) * c pow 2 - (&1 / &2) * c * s - c) +
         r * (&1 / &10 + (&1 / &2) * s pow 2 + s - (&1 / &5) * c * s) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MCS_NORMAL_TAC THEN
  C1092MCS_PROD_TAC [`&0 < ((&2 / &5) * c - s) * ((&2 / &5) * c + s)`;
                     `&0 <= c * s`] THEN
  SUBGOAL_THEN `&9 / &10 < c /\ s < &2 / &5` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [NLIN_TAC []; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  C1092MCS_PROD_TAC [`&0 < (&2 / &5 - s) * (&2 / &5 + s)`] THEN
  SUBGOAL_THEN `(&1 / &5) * c pow 2 - (&1 / &2) * c * s - c < --(&7 / &10) /\
                &1 / &10 + (&1 / &2) * s pow 2 + s - (&1 / &5) * c * s < &29 / &50`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `s:real`]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  C1092MCS_PROD_TAC
   [`&0 <= (d - r) * --((&1 / &5) * c pow 2 - (&1 / &2) * c * s - c)`;
    `&0 < r * --(((&1 / &5) * c pow 2 - (&1 / &2) * c * s - c) +
                 (&1 / &10 + (&1 / &2) * s pow 2 + s - (&1 / &5) * c * s))`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: upper_v_pair *)
let C1092MCS_UPPER_V_PAIR = prove
 (`forall d r c s. c977cc_normal d r /\ c977cc_normal c s /\ &0 < r
     ==> d * ((&1 / &5) * s pow 2 - s) + r * (&3 / &5 - c + (&1 / &5) * c * s) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MCS_ELEMENTARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MCS_NORMAL_TAC THEN
  C1092MCS_PROD_TAC [`&0 <= s * (&1 - (&1 / &5) * s)`] THEN
  C1092MCS_PROD_TAC [`&0 <= d * (s * (&1 - (&1 / &5) * s))`;
                     `&0 < r * --(&3 / &5 - c + (&1 / &5) * c * s)`] THEN
  ASM_REAL_ARITH_TAC);;
