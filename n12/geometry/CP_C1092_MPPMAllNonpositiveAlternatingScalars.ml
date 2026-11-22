(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMAllNonpositiveAlternatingScalars.lean*)
(* (N12Compact.C1092MPPMAllNonpositive), ALL-NEGATIVE-MIXED-FORWARD-ENDING   *)
(* sections 4--5 scalar bounds.  Normal is c977cc_normal (normal_bounds =    *)
(* C977CC_NORMAL_BOUNDS); cosine_order / sine_order are C977CSB_*;           *)
(* CommonCases.UnitCircleChord.increasing is CCUCC_INCREASING.               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMAllNonpositiveCore.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointEnvelope.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

let C1092ANAS_LIN = NLIN_TAC ~deg2:false [];;

let C1092ANAS_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C1092ANAS_LIN; ALL_TAC];;

let C1092ANAS_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092ANAS_LIN; ALL_TAC];;

let C1092ANAS_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal; REAL_POW_2] th)) ns);;

let C1092ANAS_CANCEL = prove
 (`forall k x. &0 < k /\ &0 <= k * x ==> &0 <= x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:real`; `--x`] REAL_LT_MUL) THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;

(* Lean: sine_small *)
let C1092ANAS_SINE_SMALL = prove
 (`forall c s. c977cc_normal c s ==> s < &71 / &100`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092ANAS_NORMAL_TAC THEN
  C1092ANAS_PROD `&0 <= (c - s) * (c + s)` THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092ANAS_PROD `&0 <= (s - &71 / &100) * (s + &71 / &100)` THEN
  C1092ANAS_LIN);;

(* Lean: MissingBounds (structure) *)
let c1092anas_missingBounds = new_definition
 `c1092anas_missingBounds (b:real) (r:real) <=>
    b < &369 / &500 /\ &27 / &40 < r /\ r < &71 / &100 /\
    &141 / &100 < b + r /\ b - r < &31 / &500`;;

(* Lean: missing_bounds *)
let C1092ANAS_MISSING_BOUNDS = prove
 (`forall b r. c977cc_normal b r /\ &252 / &373 <= r ==> c1092anas_missingBounds b r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c977cc_normal (&275 / &373) (&252 / &373)` ASSUME_TAC THENL
  [REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC(SPECL [`b:real`; `r:real`; `&275 / &373`; `&252 / &373`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`b:real`; `r:real`] C1092ANAS_SINE_SMALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal b r`)) THEN
  MP_TAC(SPECL [`b:real`; `r:real`; `&275 / &373`; `&252 / &373`; `&1`; `&1`]
    CCUCC_INCREASING) THEN
  ANTS_TAC THENL
  [RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN ASM_REWRITE_TAC[] THEN
   CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
   DISCH_TAC] THEN
  REWRITE_TAC[c1092anas_missingBounds] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
    filter (fun th -> not (can (term_match [] `c977cc_normal x y`) (concl th)))) THEN
  REAL_ARITH_TAC);;

(* Lean: predecessorF, predecessorG (definitions) *)
let c1092anas_predecessorF = new_definition
 `c1092anas_predecessorF (b:real) (r:real) = &1 + b * r - b - r`;;
let c1092anas_predecessorG = new_definition
 `c1092anas_predecessorG (b:real) (r:real) = b pow 2 - b + r`;;

(* Lean: predecessor_coefficients *)
let C1092ANAS_PREDECESSOR_COEFFICIENTS = prove
 (`forall b r. c977cc_normal b r /\ &252 / &373 <= r
     ==> c1092anas_predecessorF b r < &43 / &500 /\
         &12 / &25 < c1092anas_predecessorG b r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `r:real`] C1092ANAS_MISSING_BOUNDS) THEN
  ASM_REWRITE_TAC[c1092anas_missingBounds] THEN STRIP_TAC THEN
  C1092ANAS_NORMAL_TAC THEN
  SUBGOAL_THEN `b + r <= &99 / &70` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092ANAS_PROD `&0 < (b + r - &99 / &70) * (b + r + &99 / &70)` THEN
   NLIN_TAC [SQ_NONNEG `b - r:real`];
   ALL_TAC] THEN
  C1092ANAS_PROD `&0 <= (&99 / &70 - (b + r)) * (&99 / &70 + (b + r) - &2)` THEN
  C1092ANAS_PROD `&0 <= (&31 / &500 - (b - r)) * (&1 - (b + r) / &2)` THEN
  C1092ANAS_FACT `(b - r) * (&1 - (b + r) / &2) <= (&31 / &500) * (&59 / &200)` THEN
  REWRITE_TAC[c1092anas_predecessorF; c1092anas_predecessorG; REAL_POW_2] THEN
  CONJ_TAC THEN C1092ANAS_LIN);;

(* Lean: preliminary_angle *)
let C1092ANAS_PRELIMINARY_ANGLE = prove
 (`forall c s H. c977cc_normal c s /\ --(&13 / &50) * s < H /\
           H < (&43 / &500) * c - (&12 / &25) * s
     ==> &110 * s < &43 * c /\ &23 / &25 < c /\ s < &19 / &50`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092ANAS_NORMAL_TAC THEN
  C1092ANAS_FACT `&110 * s < &43 * c` THEN
  C1092ANAS_FACT `&5 * s < &2 * c` THEN
  C1092ANAS_PROD `&0 < (&2 * c - &5 * s) * (&2 * c + &5 * s)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THENL
  [C1092ANAS_PROD `&0 <= (&23 / &25 - c) * (&23 / &25 + c)`;
   C1092ANAS_PROD `&0 <= (s - &19 / &50) * (s + &19 / &50)`] THEN
  C1092ANAS_LIN);;

(* Lean: heightGap (definition) *)
let c1092anas_heightGap = new_definition
 `c1092anas_heightGap (c:real) (s:real) =
    c + s - &1 - (&13 / &25) * c * s - (&43 / &500) * c pow 2`;;

(* Lean: heightGap_order *)
let C1092ANAS_HEIGHTGAP_ORDER = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\
             &23 / &25 < c /\ &23 / &25 < d /\
             s < &19 / &50 /\ t < &19 / &50 /\ s <= t
     ==> c1092anas_heightGap c s <= c1092anas_heightGap d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092ANAS_NORMAL_TAC THEN
  C1092ANAS_PROD `&0 <= (c + d) * (&1 - (&13 / &25) * d - &12 / &25)` THEN
  C1092ANAS_PROD `&0 <= (s + t) *
     (&1 - (&1 - (&13 / &25) * s - (&43 / &500) * (c + d)))` THEN
  ABBREV_TAC `A = (c + d) * (&1 - (&13 / &25) * d) -
                  (s + t) * (&1 - (&13 / &25) * s - (&43 / &500) * (c + d))` THEN
  SUBGOAL_THEN `&0 <= A` ASSUME_TAC THENL
  [EXPAND_TAC "A" THEN C1092ANAS_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `(c + d) * (c1092anas_heightGap d t - c1092anas_heightGap c s) = (t - s) * A`
    ASSUME_TAC THENL
  [EXPAND_TAC "A" THEN REWRITE_TAC[c1092anas_heightGap] THEN
   UNDISCH_TAC `d * d + t * t = &1` THEN UNDISCH_TAC `c * c + s * s = &1` THEN
   CONV_TAC REAL_RING;
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (c + d) * (c1092anas_heightGap d t - c1092anas_heightGap c s)`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c + d:real`;
                `c1092anas_heightGap d t - c1092anas_heightGap c s`] C1092ANAS_CANCEL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: heightGap_positive *)
let C1092ANAS_HEIGHTGAP_POSITIVE = prove
 (`forall c s. c977cc_normal c s /\ &23 / &25 < c /\ s < &19 / &50 /\ c <= &4 * s
     ==> &0 < c1092anas_heightGap c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c977cc_normal (&40 / &41) (&9 / &41)` ASSUME_TAC THENL
  [REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `&9 / &41 <= s` ASSUME_TAC THENL
  [MATCH_MP_TAC C977CSB_SINE_ORDER THEN
   MAP_EVERY EXISTS_TAC [`c:real`; `&40 / &41`] THEN ASM_REWRITE_TAC[] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
     check (fun th -> concl th = `c977cc_normal c s`)) THEN
   ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC(SPECL [`&40 / &41`; `&9 / &41`; `c:real`; `s:real`] C1092ANAS_HEIGHTGAP_ORDER) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `c1092anas_heightGap (&40 / &41) (&9 / &41) = &16 / &8405` SUBST1_TAC THENL
  [REWRITE_TAC[c1092anas_heightGap] THEN CONV_TAC REAL_RAT_REDUCE_CONV; REAL_ARITH_TAC]);;
