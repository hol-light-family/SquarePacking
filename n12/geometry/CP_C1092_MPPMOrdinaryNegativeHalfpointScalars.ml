(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMOrdinaryNegativeHalfpointScalars.lean *)
(* (N12Compact.C1092MPPMOrdinaryNegativeHalfpoint).  Exact scalar part of    *)
(* C1092-MPPM-ORDINARY-NEGATIVE-HALFPOINT.  The quartic certificate is       *)
(* checked here in the homogeneous form in s and 1 + c instead of through    *)
(* x = s / (1 + c).                                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

let C1092ONH_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC];;

let C1092ONH_POS_OF_MUL = prove
 (`forall k x. &0 < k /\ &0 < x * k ==> &0 < x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= --x * k` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: Frame *)
let c1092onh_frame = new_definition
 `c1092onh_frame (c:real) s <=> &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1`;;

let C1092ONH_FRAME_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c1092onh_frame x y`) o concl) ths in
    MAP_EVERY (fun th ->
      let th' = REWRITE_RULE[c1092onh_frame] th in
      STRIP_ASSUME_TAC (MATCH_MP CCCS_BOUNDS th') THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[REAL_POW_2] th')) ns);;

(* Lean: linear_norm (private) *)
let C1092ONH_LINEAR_NORM = prove
 (`forall A B c s r. c pow 2 + s pow 2 = &1 /\ &0 < r /\ A pow 2 + B pow 2 < r pow 2
     ==> A * c + B * s < r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(A * c + B * s) * (A * c + B * s) + (A * s - B * c) * (A * s - B * c) =
                A * A + B * B` MP_TAC THENL
  [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPEC `A * s - B * c:real` REAL_LE_SQUARE) THEN
  UNDISCH_TAC `A * A + B * B < r * r` THEN UNDISCH_TAC `&0 < r` THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`A * c + B * s`,`X:real`) THEN
  SPEC_TAC(`(A * s - B * c) * (A * s - B * c)`,`Y:real`) THEN
  SPEC_TAC(`A * A + B * B`,`N:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `r * r <= X * X` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: relative *)
let C1092ONH_RELATIVE = prove
 (`forall c s d t. c1092onh_frame c s /\ c1092onh_frame d t
     ==> &0 < c * d + s * t /\ (c * d + s * t) pow 2 + (c * t - s * d) pow 2 = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092ONH_FRAME_TAC THEN CONJ_TAC THENL
  [C1092ONH_PROD `&0 < c * d` THEN C1092ONH_PROD `&0 <= s * t` THEN ASM_REAL_ARITH_TAC;
   REWRITE_TAC[REAL_POW_2] THEN
   UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `d * d + t * t = &1` THEN
   CONV_TAC REAL_RING]);;

(* Lean: source_coordinates *)
let C1092ONH_SOURCE_COORDINATES = prove
 (`forall c s d t. d pow 2 + t pow 2 = &1
     ==> c = (c * d + s * t) * d + (c * t - s * d) * t /\
         s = (c * d + s * t) * t - (c * t - s * d) * d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
  CONJ_TAC THEN UNDISCH_TAC `d * d + t * t = &1` THEN CONV_TAC REAL_RING);;

(* Lean: coefficient (private) *)
let C1092ONH_COEFFICIENT = prove
 (`forall c s. c pow 2 + s pow 2 = &1 ==> (&793 / &500) * c + s - &1 < &9 / &10`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&793 / &500`; `&1`; `c:real`; `s:real`; `&19 / &10`] C1092ONH_LINEAR_NORM) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

(* Lean: c_positive *)
let C1092ONH_C_POSITIVE = prove
 (`forall c s d t. c1092onh_frame c s /\ c1092onh_frame d t /\ &0 <= c * t - s * d
     ==> (&793 / &500) * c + s < &1 + (c * d + s * t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092ONH_RELATIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&443 / &500`; `&3 / &10`; `c:real`; `s:real`; `&1`] C1092ONH_LINEAR_NORM) THEN
  ANTS_TAC THENL
  [UNDISCH_TAC `c1092onh_frame c s` THEN SIMP_TAC[c1092onh_frame] THEN
   CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  C1092ONH_FRAME_TAC THEN
  SUBGOAL_THEN `c + s = (c * d + s * t) * (d + t) - (c * t - s * d) * (d - t)` ASSUME_TAC THENL
  [UNDISCH_TAC `d * d + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092ONH_PROD `&0 <= (c * t - s * d) * (d - t)` THEN
  C1092ONH_PROD `&0 <= (c * d + s * t) * (&10 / &7 - (d + t))` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: c_negative *)
let C1092ONH_C_NEGATIVE = prove
 (`forall c s d t. c1092onh_frame c s /\ c1092onh_frame d t /\ c * t - s * d <= &0
     ==> (&793 / &500) * c + s + (c * t - s * d) * ((&37 / &50) * d - t / &2) <
         &1 + (c * d + s * t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092ONH_RELATIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&9 / &10`; `&13 / &50`; `c * d + s * t`; `--(c * t - s * d)`; `&1`]
    C1092ONH_LINEAR_NORM) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[REAL_POW_NEG; ARITH] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092ONH_COEFFICIENT) THEN
  ANTS_TAC THENL
  [UNDISCH_TAC `c1092onh_frame d t` THEN SIMP_TAC[c1092onh_frame]; DISCH_TAC] THEN
  C1092ONH_FRAME_TAC THEN
  C1092ONH_PROD `&0 < (&9 / &10 - ((&793 / &500) * d + t - &1)) * (c * d + s * t)` THEN
  C1092ONH_PROD `&0 <= (&13 / &50 - ((&13 / &50) * d - (&543 / &500) * t)) * --(c * t - s * d)` THEN
  SUBGOAL_THEN
   `(&793 / &500) * c + s + (c * t - s * d) * ((&37 / &50) * d - t / &2) - (c * d + s * t) =
    ((&793 / &500) * d + t - &1) * (c * d + s * t) +
    ((&13 / &50) * d - (&543 / &500) * t) * --(c * t - s * d)` ASSUME_TAC THENL
  [UNDISCH_TAC `d * d + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: e_positive *)
let C1092ONH_E_POSITIVE = prove
 (`forall c s d t. c1092onh_frame c s /\ c1092onh_frame d t /\ &0 <= c * t - s * d
     ==> (&543 / &500) * (c * d + s * t) * c + (&7 / &20) * (c * t - s * d) * (c - s) +
         d / &2 + t < &1 + (c * d + s * t) + (c * t - s * d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092ONH_RELATIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&9 / &10`; `&7 / &20`; `c * d + s * t`; `c * t - s * d`; `&1`]
    C1092ONH_LINEAR_NORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092ONH_COEFFICIENT) THEN
  ANTS_TAC THENL
  [UNDISCH_TAC `c1092onh_frame c s` THEN SIMP_TAC[c1092onh_frame]; DISCH_TAC] THEN
  C1092ONH_FRAME_TAC THEN
  C1092ONH_PROD `&0 < (&9 / &10 - ((&793 / &500) * c + s - &1)) * (c * d + s * t)` THEN
  C1092ONH_PROD `&0 <= (&7 / &20 - ((&27 / &20) * c - (&17 / &20) * s - &1)) * (c * t - s * d)` THEN
  SUBGOAL_THEN
   `(&543 / &500) * (c * d + s * t) * c + (&7 / &20) * (c * t - s * d) * (c - s) +
    d / &2 + t - (c * d + s * t) - (c * t - s * d) =
    ((&793 / &500) * c + s - &1) * (c * d + s * t) +
    ((&27 / &20) * c - (&17 / &20) * s - &1) * (c * t - s * d)` ASSUME_TAC THENL
  [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: coefficient_norm *)
let C1092ONH_COEFFICIENT_NORM = prove
 (`forall c s. c1092onh_frame c s
     ==> (&1 / &2 - c + (&543 / &500) * c pow 2 + (&7 / &20) * s * (c + s)) pow 2 +
         (&1 - s + (&543 / &500) * c * s - (&7 / &20) * c * (c + s)) pow 2 < &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092ONH_FRAME_TAC THEN
  ABBREV_TAC `w = &1 + c` THEN
  SUBGOAL_THEN `&0 < w` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s * s + &2 * s * w <= w * w` ASSUME_TAC THENL
  [SUBGOAL_THEN `s * s + &2 * s * w - w * w = &2 * (s - c) * w` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
   C1092ONH_PROD `&0 <= (c - s) * w` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s <= &5 / &12 * w` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092ONH_PROD `&0 <= (s - &5 / &12 * w) * (s + &5 / &12 * w)` THEN
   C1092ONH_PROD `&0 < w * w` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092ONH_PROD `&0 <= (&5 / &12 * w - s) * (&5 / &12 * w + s)` THEN
  C1092ONH_PROD `&0 <= ((s * s) * s) * (&1016750 * w - &763737 * s)` THEN
  C1092ONH_PROD `&0 <= ((&5 / &12 * w - s) * (&5 / &12 * w + s)) * (w * w)` THEN
  C1092ONH_PROD `&0 <= (&5 / &12 * w - s) * ((w * w) * w)` THEN
  C1092ONH_PROD `&0 < (w * w) * (w * w)` THEN
  C1092ONH_PROD `&0 < w * w` THEN
  SUBGOAL_THEN `&0 < --(&763737) * s pow 4 + &1016750 * s pow 3 * w -
                     &126776 * s pow 2 * w pow 2 - &16750 * s * w pow 3 +
                     &29263 * w pow 4` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 - ((&1 / &2 - c + (&543 / &500) * c pow 2 + (&7 / &20) * s * (c + s)) pow 2 +
           (&1 - s + (&543 / &500) * c * s - (&7 / &20) * c * (c + s)) pow 2)) *
    (&500000 * w pow 2) =
    --(&763737) * s pow 4 + &1016750 * s pow 3 * w -
    &126776 * s pow 2 * w pow 2 - &16750 * s * w pow 3 + &29263 * w pow 4`
  ASSUME_TAC THENL
  [EXPAND_TAC "w" THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < &1 - x ==> x < &1`) THEN
  MATCH_MP_TAC C1092ONH_POS_OF_MUL THEN EXISTS_TAC `&500000 * w pow 2` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC);;

(* Lean: e_negative *)
let C1092ONH_E_NEGATIVE = prove
 (`forall c s d t. c1092onh_frame c s /\ c1092onh_frame d t
     ==> d / &2 + t - (c * d + s * t) * (&1 - (&543 / &500) * c) +
         (&7 / &20) * --(c * t - s * d) * (c + s) < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&1 / &2 - c + (&543 / &500) * c pow 2 + (&7 / &20) * s * (c + s)`;
                `&1 - s + (&543 / &500) * c * s - (&7 / &20) * c * (c + s)`;
                `d:real`; `t:real`; `&1`] C1092ONH_LINEAR_NORM) THEN
  ANTS_TAC THENL
  [REWRITE_TAC[REAL_LT_01; REAL_POW_ONE] THEN CONJ_TAC THENL
   [UNDISCH_TAC `c1092onh_frame d t` THEN SIMP_TAC[c1092onh_frame];
    MATCH_MP_TAC C1092ONH_COEFFICIENT_NORM THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;
