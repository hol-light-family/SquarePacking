(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNonpositivePredecessorScalars.lean    *)
(* (N12Compact.C1092MPPMNonpositivePredecessor).  Scalar comparisons from    *)
(* C1092-MIXED-NEGATIVE-H, sections 4--7.  Frame is c1092onh_frame;           *)
(* CommonCases bounds is CCCS_BOUNDS.                                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMOrdinaryNegativeHalfpointScalars.ml";;

let C1092NPP_PROD = C1092ONH_PROD;;

(* both frames: bounds plus unfolded definition, in c * c form *)
let C1092NPP_SETUP_TAC = C1092ONH_FRAME_TAC;;

(* Lean: norm_lt *)
let C1092NPP_NORM_LT = prove
 (`forall A B c s r. c pow 2 + s pow 2 = &1 /\ &0 < r /\ A pow 2 + B pow 2 < r pow 2
     ==> A * c + B * s < r`,
  MATCH_ACCEPT_TAC C1092ONH_LINEAR_NORM);;

(* Lean: norm_le *)
let C1092NPP_NORM_LE = prove
 (`forall A B c s r. c pow 2 + s pow 2 = &1 /\ &0 < r /\ A pow 2 + B pow 2 <= r pow 2
     ==> A * c + B * s <= r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(A * c + B * s) * (A * c + B * s) + (A * s - B * c) * (A * s - B * c) =
                A * A + B * B` MP_TAC THENL
  [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPEC `A * s - B * c:real` REAL_LE_SQUARE) THEN
  UNDISCH_TAC `A * A + B * B <= r * r` THEN UNDISCH_TAC `&0 < r` THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`A * c + B * s`,`X:real`) THEN
  SPEC_TAC(`(A * s - B * c) * (A * s - B * c)`,`Y:real`) THEN
  SPEC_TAC(`A * A + B * B`,`N:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `r * r < X * X` MP_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: relative *)
let C1092NPP_RELATIVE = prove
 (`forall c s d t. c1092onh_frame c s /\ c1092onh_frame d t
     ==> &0 <= c * d - s * t /\ &0 <= c * t + s * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092NPP_SETUP_TAC THEN
  C1092NPP_PROD `&0 <= (c - s) * d` THEN C1092NPP_PROD `&0 <= s * (d - t)` THEN
  C1092NPP_PROD `&0 <= c * t` THEN C1092NPP_PROD `&0 <= s * d` THEN
  CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

let C1092NPP_UNIT_TAC =
  FIRST_ASSUM(fun th -> if can (term_match [] `c1092onh_frame x y`) (concl th)
    then ACCEPT_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2(REWRITE_RULE[c1092onh_frame] th))))
    else NO_TAC);;

(* Lean: transverse *)
let C1092NPP_TRANSVERSE = prove
 (`forall c s d t. c1092onh_frame c s /\ c1092onh_frame d t
     ==> (&63 / &50) * c + (&3 / &2) * s - (c * d - s * t) * ((&37 / &50) * d - t / &2) <
         &1 + c * t + s * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&1 / &2`; `&37 / &50`; `d:real`; `t:real`; `&9 / &10`] C1092NPP_NORM_LT) THEN
  ANTS_TAC THENL
  [CONV_TAC REAL_RAT_REDUCE_CONV THEN UNDISCH_TAC `c1092onh_frame d t` THEN
   SIMP_TAC[c1092onh_frame]; DISCH_TAC] THEN
  C1092NPP_SETUP_TAC THEN
  ABBREV_TAC `A = &13 / &25 - t + (&37 / &50) * t * t + d * t / &2` THEN
  ABBREV_TAC `B = &1 - d + d * d / &2 + (&37 / &50) * d * t` THEN
  SUBGOAL_THEN `A <= &13 / &25` ASSUME_TAC THENL
  [EXPAND_TAC "A" THEN
   C1092NPP_PROD `&0 <= t * (&1 - ((&37 / &50) * t + d / &2))` THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `A + B < &69 / &50` ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
   C1092NPP_PROD `&0 <= (&10 / &7 - (d + t)) * ((&31 / &50) * (&10 / &7 + d + t) - &1)` THEN
   C1092NPP_PROD `&0 <= (d + t) * (d - t)` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `A * c + B * s < &1` ASSUME_TAC THENL
  [ASM_CASES_TAC `B <= A` THENL
   [C1092NPP_PROD `&0 <= (&13 / &25 - A) * c` THEN
    C1092NPP_PROD `&0 <= (&13 / &25 - B) * s` THEN ASM_REAL_ARITH_TAC;
    C1092NPP_PROD `&0 <= (c - s) * (B - A)` THEN
    C1092NPP_PROD `&0 < (&69 / &50 - (A + B)) * (c + s)` THEN ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `(&63 / &50) * c + (&3 / &2) * s - (c * d - s * t) * ((&37 / &50) * d - t / &2) -
                (c * t + s * d) = A * c + B * s` MP_TAC THENL
  [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN UNDISCH_TAC `d * d + t * t = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: first_source *)
let C1092NPP_FIRST_SOURCE = prove
 (`forall c s d t. c1092onh_frame c s /\ c1092onh_frame d t
     ==> (&3 / &2) * c - (&6 / &25) * (c * t + s * d) * t < &1 + c * d - s * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&4 / &5`; `&3 / &5`; `c:real`; `s:real`; `&1`] C1092NPP_NORM_LE) THEN
  ANTS_TAC THENL
  [CONV_TAC REAL_RAT_REDUCE_CONV THEN UNDISCH_TAC `c1092onh_frame c s` THEN
   SIMP_TAC[c1092onh_frame]; DISCH_TAC] THEN
  C1092NPP_SETUP_TAC THEN
  SUBGOAL_THEN `t < &5 / &7` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092NPP_PROD `&0 <= (d - t) * (d + t)` THEN
   C1092NPP_PROD `&0 <= (t - &5 / &7) * (t + &5 / &7)` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092NPP_PROD `&0 <= t * t` THEN
  C1092NPP_PROD `&0 <= t * (d - &7 / &10)` THEN
  C1092NPP_PROD `&0 < (&4 / &5 - (&3 / &2 - d - (&6 / &25) * t * t)) * c` THEN
  C1092NPP_PROD `&0 <= (&3 / &5 - t * (&1 - (&6 / &25) * d)) * s` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: first_target *)
let C1092NPP_FIRST_TARGET = prove
 (`forall c s d t. c1092onh_frame c s /\ c1092onh_frame d t
     ==> (&3 / &2) * d + (&63 / &50) * c * (c * t + s * d) <
         &1 + (c * d - s * t) + (c * t + s * d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&1`; `&1`; `c:real`; `s:real`; `&99 / &70`] C1092NPP_NORM_LT) THEN
  MP_TAC(SPECL [`&18 / &25`; `&63 / &100`; `d:real`; `t:real`; `&1`] C1092NPP_NORM_LT) THEN
  REPEAT(ANTS_TAC THENL
  [CONV_TAC REAL_RAT_REDUCE_CONV THEN C1092NPP_UNIT_TAC; DISCH_TAC]) THEN
  C1092NPP_SETUP_TAC THEN
  C1092NPP_PROD `&0 <= (&99 / &70 - (c + s)) * ((&63 / &100) * (&99 / &70 + c + s) - &1)` THEN
  SUBGOAL_THEN `&3 / &2 - c - s + (&63 / &50) * c * s < &18 / &25` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092NPP_PROD `&0 <= (c - s) * (&1 - (&63 / &100) * (c + s))` THEN
  SUBGOAL_THEN `s - c + (&63 / &50) * c * c <= &63 / &100` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092NPP_PROD `&0 < (&18 / &25 - (&3 / &2 - c - s + (&63 / &50) * c * s)) * d` THEN
  C1092NPP_PROD `&0 <= (&63 / &100 - (s - c + (&63 / &50) * c * c)) * t` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: second_source *)
let C1092NPP_SECOND_SOURCE = prove
 (`forall c s d t. c1092onh_frame c s /\ c1092onh_frame d t /\
     &99 / &100 < c /\ s < &9 / &100
     ==> (&793 / &500) * c - s - (&6 / &25) * (c * t + s * d) * t < &1 + c * d - s * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092NPP_RELATIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092NPP_SETUP_TAC THEN
  C1092NPP_PROD `&0 < (c - &99 / &100) * d` THEN
  C1092NPP_PROD `&0 <= s * (&1 - t)` THEN
  C1092NPP_PROD `&0 <= (c * t + s * d) * t` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: second_target *)
let C1092NPP_SECOND_TARGET = prove
 (`forall c s d t. c1092onh_frame c s /\ c1092onh_frame d t /\
     &99 / &100 < c /\ s < &9 / &100
     ==> (&793 / &500) * d + t + (c * t + s * d) * ((&13 / &50) * c - (&43 / &500) * s) <
         &1 + (c * d - s * t) + (c * t + s * d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&3 / &5`; `&9 / &25`; `d:real`; `t:real`; `&1`] C1092NPP_NORM_LT) THEN
  ANTS_TAC THENL
  [CONV_TAC REAL_RAT_REDUCE_CONV THEN C1092NPP_UNIT_TAC; DISCH_TAC] THEN
  C1092NPP_SETUP_TAC THEN
  C1092NPP_PROD `&0 <= c * s` THEN
  C1092NPP_PROD `&0 <= s * s` THEN
  C1092NPP_PROD `&0 <= s * (&1 - (&13 / &50) * c)` THEN
  SUBGOAL_THEN `&793 / &500 - c - s + (&13 / &50) * c * s - (&43 / &500) * s * s < &3 / &5 /\
                &1 + s - c + (&13 / &50) * c * c - (&43 / &500) * c * s < &9 / &25`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092NPP_PROD `&0 < (&3 / &5 - (&793 / &500 - c - s + (&13 / &50) * c * s -
                                   (&43 / &500) * s * s)) * d` THEN
  C1092NPP_PROD `&0 <= (&9 / &25 - (&1 + s - c + (&13 / &50) * c * c -
                                    (&43 / &500) * c * s)) * t` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: third_source *)
let C1092NPP_THIRD_SOURCE = prove
 (`forall c s d t. c1092onh_frame c s /\ c1092onh_frame d t
     ==> (&19 / &25) * c - s - (&6 / &25) * (c * t + s * d) * t < c * d - s * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092NPP_SETUP_TAC THEN
  C1092NPP_PROD `&0 <= d * (&1 - d)` THEN
  C1092NPP_PROD `&0 <= d * t` THEN
  SUBGOAL_THEN `&0 < d + (&6 / &25) * t * t - &19 / &25 /\
                &0 <= &1 - t + (&6 / &25) * d * t` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092NPP_PROD `&0 < c * (d + (&6 / &25) * t * t - &19 / &25)` THEN
  C1092NPP_PROD `&0 <= s * (&1 - t + (&6 / &25) * d * t)` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: third_target *)
let C1092NPP_THIRD_TARGET = prove
 (`forall c s d t. c1092onh_frame c s /\ c1092onh_frame d t /\
     &49 / &50 < c /\ s < &9 / &50
     ==> (&19 / &25) * d + t + (&413 / &500) * (c * t + s * d) * s < &1 + c * t + s * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&19 / &25`; `&17 / &100`; `d:real`; `t:real`; `&1`] C1092NPP_NORM_LT) THEN
  ANTS_TAC THENL
  [CONV_TAC REAL_RAT_REDUCE_CONV THEN C1092NPP_UNIT_TAC; DISCH_TAC] THEN
  C1092NPP_SETUP_TAC THEN
  C1092NPP_PROD `&0 < (c - &49 / &50) * (&1 - (&413 / &500) * s)` THEN
  SUBGOAL_THEN `&83 / &100 < c * (&1 - (&413 / &500) * s)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092NPP_PROD `&0 <= (c * (&1 - (&413 / &500) * s) - &83 / &100) * t` THEN
  C1092NPP_PROD `&0 <= (s * d) * (&1 - (&413 / &500) * s)` THEN
  ASM_REAL_ARITH_TAC);;
