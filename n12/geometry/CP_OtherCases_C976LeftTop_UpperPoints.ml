(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976LeftTop/UpperPoints.lean        *)
(* (N12Compact.Completion.OtherCases.C976LeftTop.UpperPoints).              *)
(* C976-LEFT-UPPER-POINTS Theorem 1 and Corollary 2.  Square q is c s u v a  *)
(* (unit normal and 0 < a explicit); Input / Profile are occ976lt_input /    *)
(* occ976lt_profile, LeftInput is c976lti_left, TopInput is oltstsu_top.     *)
(* An existential OpenSquare r is ?cr sr ur vr ar with its invariants        *)
(* cr*cr+sr*sr = 1 and 0 < ar.  upper_v_span / inward_span / farther_margin  *)
(* OCC976PS_UPPER_V_SPAN / _INWARD_SPAN / _FARTHER_MARGIN, upperU_strict     *)
(* OCC976PS_UPPERU_STRICT, positive_profile OCC976PP_POSITIVE_PROFILE,       *)
(* nonpositive_impossible OCC976PG_NONPOSITIVE_IMPOSSIBLE, Input.reframe     *)
(* OCC976LT_INPUT_REFRAME, ClosedFrames.canonical_frame CLF_CANONICAL_FRAME, *)
(* C976LeftTop.steep_negative C976LTMN_STEEP_NEGATIVE.  Tag OCC976UP_.      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_PointSupport.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_PointSign.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_PointScalars.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_Main.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let OCC976UP_LIN = REPEAT CONJ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  NLIN_TAC ~deg2:false [];;

let OCC976UP_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN OCC976UP_LIN; ALL_TAC];;

let OCC976UP_UNFOLD_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[occ976lt_input; occ976lt_profile]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside c s u v a (--(&43 / &500)) (&0)`; `linside c s u v a (&13 / &20) (&7 / &20)`;
    `linside c s u v a (&0) (&13 / &50)`];;

(* Lean: high_point *)
let OCC976UP_HIGH_POINT = prove
 (`forall c s u v a x.
     c * c + s * s = &1 /\ &0 < a /\
     occ976lt_input c s u v a /\ occ976lt_profile c s u v a /\
     &1 / &4 <= x /\ x <= &7 / &25
     ==> linside c s u v a x (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c pow 2 + s pow 2 = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `(&7 / &25) * c + s < u + a` ASSUME_TAC THENL
   [ASM_CASES_TAC `s <= (&37 / &65) * c` THENL
     [OCC976UP_UNFOLD_TAC THEN OCC976UP_LIN; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] OCC976PS_UPPERU_STRICT) THEN
    MP_TAC(SPECL [`c:real`; `s:real`] OCC976PS_FARTHER_MARGIN) THEN
    ASM_REWRITE_TAC[] THEN OCC976UP_UNFOLD_TAC THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN OCC976UP_LIN; DISCH_TAC] THEN
    ANTS_TAC THENL [OCC976UP_LIN; DISCH_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[occ976ps_lowerAlpha; occ976ps_lowerBeta]) THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OCC976UP_PROD `&0 <= ((&13 / &100) * c + (&6 / &25) * s) * (((&7 / &25) * c + s) - (u + a))` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN OCC976UP_LIN;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OCC976PS_UPPER_V_SPAN) THEN
  OCC976UP_UNFOLD_TAC THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN OCC976UP_LIN; DISCH_TAC] THEN
  OCC976UP_PROD `&0 <= c * (x - &1 / &4)` THEN
  OCC976UP_PROD `&0 <= c * (&7 / &25 - x)` THEN
  OCC976UP_PROD `&0 <= s * (&7 / &25 - x)` THEN
  OCC976UP_PROD `&0 <= s * (x - &1 / &4)` THEN
  REWRITE_TAC[linside] THEN OCC976UP_LIN);;

(* Lean: inward_point *)
let OCC976UP_INWARD_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     occ976lt_input c s u v a /\ occ976lt_profile c s u v a
     ==> linside c s u v a (&0) (&4 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OCC976PS_INWARD_SPAN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; DISCH_TAC] THEN
  OCC976UP_UNFOLD_TAC THEN REWRITE_TAC[linside] THEN OCC976UP_LIN);;

(* Lean: frame *)
let OCC976UP_FRAME = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ occ976lt_input c s u v a
     ==> exists cr sr ur vr ar. cr * cr + sr * sr = &1 /\ &0 < ar /\ ar = a /\
           (forall x y. linside cr sr ur vr ar x y <=> linside c s u v a x y) /\
           occ976lt_profile cr sr ur vr ar /\
           linside cr sr ur vr ar (&1 / &4) (&1) /\
           linside cr sr ur vr ar (&0) (&4 / &5) /\
           linside cr sr ur vr ar (&7 / &25) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  SUBGOAL_THEN `occ976lt_input cr sr ur vr ar` ASSUME_TAC THENL
   [MATCH_MP_TAC OCC976LT_INPUT_REFRAME THEN
    MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= sr` THENL
   [SUBGOAL_THEN `occ976lt_profile cr sr ur vr ar` ASSUME_TAC THENL
     [MATCH_MP_TAC OCC976PP_POSITIVE_PROFILE THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `abs sr <= cr` THEN ASM_REWRITE_TAC[real_abs];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(MATCH_MP_TAC OCC976UP_INWARD_POINT THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    MATCH_MP_TAC OCC976UP_HIGH_POINT THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `false ==> p`) THEN MATCH_MP_TAC OCC976PG_NONPOSITIVE_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`; `--sr`] THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG] THEN
  UNDISCH_TAC `abs sr <= cr` THEN UNDISCH_TAC `~(&0 <= sr)` THEN
  REWRITE_TAC[real_abs] THEN ASM_REAL_ARITH_TAC);;

(* Lean: points *)
let OCC976UP_POINTS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ occ976lt_input c s u v a
     ==> linside c s u v a (&1 / &4) (&1) /\ linside c s u v a (&0) (&4 / &5) /\
         linside c s u v a (&7 / &25) (&1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP OCC976UP_FRAME) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(el 3 (CONJUNCTS th))] THEN REWRITE_TAC[th]));;

(* Lean: left_input *)
let OCC976UP_LEFT_INPUT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     occ976lt_input c s u v a /\ occ976lt_profile c s u v a
     ==> c976lti_left c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&1 / &4`]
    OCC976UP_HIGH_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[occ976lt_input; occ976lt_profile]) THEN
  ASM_REWRITE_TAC[c976lti_left; REAL_ARITH `--(&43) / &500 = --(&43 / &500)`]);;

(* Lean: steep_negative *)
let OCC976UP_STEEP_NEGATIVE = prove
 (`forall cN sN uN vN aN cW sW uW vW aW.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     occ976lt_input cN sN uN vN aN /\ oltstsu_top cW sW uW vW aW /\
     &0 < cW /\ sW <= &0 /\ aN = aW /\
     ldisj cN sN uN vN aN cW sW uW vW aW
     ==> (&2 / &3) * cW < --sW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aN:real = aW`)) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aW:real`] OCC976UP_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ar:real = aW`)) THEN
  MATCH_MP_TAC C976LTMN_STEEP_NEGATIVE THEN
  MAP_EVERY EXISTS_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `aW:real`; `uW:real`; `vW:real`; `aW:real`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN FIRST
   [MATCH_MP_TAC OCC976UP_LEFT_INPUT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OCC976LT_INPUT_REFRAME THEN
    MAP_EVERY EXISTS_TAC [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aW:real`] THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `ldisj cN sN uN vN aW cW sW uW vW aW` THEN ASM_REWRITE_TAC[ldisj]]);;
