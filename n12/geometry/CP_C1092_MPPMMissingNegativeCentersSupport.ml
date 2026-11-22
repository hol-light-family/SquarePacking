(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingNegativeCentersSupport.lean   *)
(* (N12Compact.C1092MPPMMissingNegativeCenters).  Whole-square support       *)
(* comparisons for the two actual boundary-center theorems.  Square C is     *)
(* c s u v a (the Lean local c := C.c, s := -C.s is c, --s here); Data is  *)
(* c1092mncsp_data; StrongFaces: c1092mnpg_strong_faces; Normal:             *)
(* c977cc_normal; Quarter: c1092mcs_quarter; lower / upper: ABT_lower /      *)
(* ABT_upper (formulas, lower_np, upper_np: C1092WS_ thms); width0:          *)
(* c1092sbs_width0; supportRadius: tss_support_radius; signed_widths:        *)
(* C1092SW_SIGNED_WIDTHS; UnitCircleChord.increasing: CCUCC_INCREASING;      *)
(* bounds, bottom_plus, ...: C1092MNCS_ thms; bottomValue / leftValue:      *)
(* c1092mpbes_bottomValue / c1092mpbes_leftValue.  Tag C1092MNCSP_.          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCentersScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeProfile.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingPositiveBoundEnvelopesBottom.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/CP_C1092_ShallowBoundarySupport.ml";;
needs "n12/geometry/CP_C1092_ShallowWidths.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;

(* Lean: Data (structure) *)
let c1092mncsp_data = new_definition
 `c1092mncsp_data (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    c977cc_normal c (--s) /\
    linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
    linside c s u v a (--(&1)) (--(&13 / &50)) /\
    c1092mnpg_strong_faces c s u v a`;;

let C1092MNCSP_LIN = NLIN_TAC ~deg2:false [];;

let C1092MNCSP_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092MNCSP_LIN; ALL_TAC];;

(* Lean: Data.large *)
let C1092MNCSP_DATA_LARGE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c1092mncsp_data c s u v a
     ==> &252 / &373 <= --s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mncsp_data; c1092mnpg_strong_faces] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (can (term_match [] `c977cc_normal c s`) o concl)) THEN
  MP_TAC(SPECL [`&275 / &373`; `&252 / &373`; `c:real`; `--s`; `&11 / &25`; `&1`]
    CCUCC_INCREASING) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC);;

(* Lean: negative_widths *)
let C1092MNCSP_NEGATIVE_WIDTHS = prove
 (`forall cq sq (uq:real) (vq:real) aq c s.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ c977cc_normal c s
     ==> aq * (&1 + s * (c + s)) / &2 <=
           s * (aq * c1092sbs_width0 cq sq / &2) + tss_support_radius cq sq aq (--c) s /\
         aq * (&1 + c * (c + s)) / &2 <=
           c * (aq * c1092sbs_width0 cq sq / &2) + tss_support_radius cq sq aq (--c) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `sq:real`; `cq:real`] C1092SW_SIGNED_WIDTHS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(--c * cq + s * sq) = abs(c * cq - s * sq) /\
                abs(-- --c * sq + s * cq) = abs(c * sq + s * cq)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[tss_support_radius; c1092sbs_width0] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= aq / &2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN (MP_TAC o MATCH_MP REAL_LE_LMUL o CONJ (ASSUME `&0 <= aq / &2`))) THEN
  REAL_ARITH_TAC);;

let C1092MNCSP_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `c1092mncsp_data c s u v a`) (concl th)
    then MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092MNCSP_DATA_LARGE) THEN
         ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
         STRIP_ASSUME_TAC(REWRITE_RULE[c1092mncsp_data; c1092mnpg_strong_faces; c1092mnpg_faces] th)
    else NO_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (can (term_match [] `c977cc_normal c s`) o concl)) THEN
  MP_TAC(ASSUME `linside c s u v a (--(&7 / &20)) (--(&7 / &20))`) THEN
  REWRITE_TAC[linside] THEN STRIP_TAC;;

(* Lean: northwest *)
let C1092MNCSP_NORTHWEST = prove
 (`forall c s u v a h t.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c1092mncsp_data c s u v a /\ c1092mcs_quarter h t
     ==> ABT_lower c s u v a (--h) t < (&1 / &5) * h - &2 * t + (a / &2) * (&1 + t pow 2 + h * t) /\
         &2 * h + (&1 / &5) * t - (a / &2) * (&1 + h pow 2 + h * t) < ABT_upper c s u v a (--h) t`,
  C1092MNCSP_SETUP_TAC THEN
  MP_TAC(ASSUME `c1092mcs_quarter h t`) THEN REWRITE_TAC[c1092mcs_quarter] THEN STRIP_TAC THEN
  MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN MP_TAC(SPEC `h:real` REAL_LE_POW_2) THEN
  REPEAT DISCH_TAC THEN
  ABBREV_TAC `k = c * h + --s * t` THEN ABBREV_TAC `sg = c * t - --s * h` THEN
  C1092MNCSP_PROD `&0 <= c * h` THEN C1092MNCSP_PROD `&0 <= --s * t` THEN
  C1092MNCSP_PROD `&0 <= h * t` THEN
  SUBGOAL_THEN `&0 <= k` ASSUME_TAC THENL [EXPAND_TAC "k" THEN C1092MNCSP_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `--h * c + t * s = --k /\ -- --h * s + t * c = sg` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["k"; "sg"] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a - c <= u + a /\ u <= --s - (&14 / &25) * c - a /\
                v <= --(&13 / &50) * --s - a /\ --(&7 / &20) * (c + --s) <= v + a`
    STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN C1092MNCSP_LIN; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= sg` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `--h`; `t:real`; `--k`; `sg:real`]
      C1092WS_LOWER_NP) THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `--h`; `t:real`; `--k`; `sg:real`]
      C1092WS_UPPER_NP) THEN
    ASM_REWRITE_TAC[REAL_ARITH `--k <= &0 <=> &0 <= k`] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN
    MP_TAC(SPECL [`c:real`; `--s`; `h:real`; `t:real`] C1092MNCS_BOTTOM_PLUS) THEN
    MP_TAC(SPECL [`c:real`; `--s`; `h:real`; `t:real`] C1092MNCS_LEFT_PLUS) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    C1092MNCSP_PROD `&0 <= k * ((u + a) - (a - c))` THEN
    C1092MNCSP_PROD `&0 <= sg * ((--(&13 / &50) * --s - a) - v)` THEN
    C1092MNCSP_PROD `&0 <= k * ((--s - (&14 / &25) * c - a) - u)` THEN
    C1092MNCSP_PROD `&0 <= sg * ((v + a) - --(&7 / &20) * (c + --s))` THEN
    C1092MNCSP_PROD `&0 < (a - &1) * ((&1 + t pow 2 + h * t) / &2 + k + sg)` THEN
    C1092MNCSP_PROD `&0 < (a - &1) * ((&1 + h pow 2 + h * t) / &2 + k)` THEN
    SUBGOAL_THEN
     `(&1 / &5) * h - &2 * t + (a / &2) * (&1 + t pow 2 + h * t) -
        (--k * (a - c) + sg * (--(&13 / &50) * --s - a)) =
      c1092mpbes_bottomValue (&1) (c1092mncs_bottomPlusA c (--s)) (c1092mncs_bottomPlusB c (--s)) h t +
        (a - &1) * ((&1 + t pow 2 + h * t) / &2 + k + sg) /\
      --k * (--s - (&14 / &25) * c - a) + sg * (--(&7 / &20) * (c + --s)) -
        (&2 * h + (&1 / &5) * t - (a / &2) * (&1 + h pow 2 + h * t)) =
      c1092mpbes_leftValue (&1) (c1092mncs_leftPlusA c (--s)) (c1092mncs_leftPlusB c (--s)) h t +
        (a - &1) * ((&1 + h pow 2 + h * t) / &2 + k)`
      STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["k"; "sg"] THEN
      REWRITE_TAC[c1092mpbes_bottomValue; c1092mpbes_leftValue; c1092mncs_bottomPlusA;
                  c1092mncs_bottomPlusB; c1092mncs_leftPlusA; c1092mncs_leftPlusB] THEN
      CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    CONJ_TAC THEN C1092MNCSP_LIN;
    SUBGOAL_THEN `sg <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `--h`; `t:real`] C1092WS_FORMULAS) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= k ==> min (--k) (&0) = --k /\ max (--k) (&0) = &0`;
                 REAL_ARITH `x <= &0 ==> min x (&0) = x /\ max x (&0) = &0`] THEN
    REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`c:real`; `--s`; `h:real`; `t:real`] C1092MNCS_BOTTOM_MINUS) THEN
    MP_TAC(SPECL [`c:real`; `--s`; `h:real`; `t:real`] C1092MNCS_LEFT_MINUS) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    C1092MNCSP_PROD `&0 <= k * ((u + a) - (a - c))` THEN
    C1092MNCSP_PROD `&0 <= --sg * ((v + a) - --(&7 / &20) * (c + --s))` THEN
    C1092MNCSP_PROD `&0 <= k * ((--s - (&14 / &25) * c - a) - u)` THEN
    C1092MNCSP_PROD `&0 <= --sg * ((--(&13 / &50) * --s - a) - v)` THEN
    C1092MNCSP_PROD `&0 < (a - &1) * ((&1 + t pow 2 + h * t) / &2 + k)` THEN
    C1092MNCSP_PROD `&0 < (a - &1) * ((&1 + h pow 2 + h * t) / &2 + k - sg)` THEN
    SUBGOAL_THEN
     `(&1 / &5) * h - &2 * t + (a / &2) * (&1 + t pow 2 + h * t) -
        (--k * (a - c) + sg * (--(&7 / &20) * (c + --s))) =
      c1092mpbes_bottomValue (&1) (c1092mncs_bottomMinusA c (--s)) (c1092mncs_bottomMinusB c (--s)) h t +
        (a - &1) * ((&1 + t pow 2 + h * t) / &2 + k) /\
      --k * (--s - (&14 / &25) * c - a) + sg * (--(&13 / &50) * --s - a) -
        (&2 * h + (&1 / &5) * t - (a / &2) * (&1 + h pow 2 + h * t)) =
      c1092mpbes_leftValue (&1) (c1092mncs_leftMinusA c (--s)) (c1092mncs_leftMinusB c (--s)) h t +
        (a - &1) * ((&1 + h pow 2 + h * t) / &2 + k - sg)`
      STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["k"; "sg"] THEN
      REWRITE_TAC[c1092mpbes_bottomValue; c1092mpbes_leftValue; c1092mncs_bottomMinusA;
                  c1092mncs_bottomMinusB; c1092mncs_leftMinusA; c1092mncs_leftMinusB] THEN
      CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    CONJ_TAC THEN C1092MNCSP_LIN]);;

(* Lean: northeast *)
let C1092MNCSP_NORTHEAST = prove
 (`forall c s u v a h t.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c1092mncsp_data c s u v a /\
     &0 <= h /\ &0 < t /\ h < (&413 / &500) * t
     ==> ABT_lower c s u v a h t < --(&2 / &5) * h - t /\ --h < ABT_upper c s u v a h t`,
  C1092MNCSP_SETUP_TAC THEN
  MP_TAC(SPECL [`c:real`; `--s`] C1092MNCS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `lm = c * h - --s * t` THEN ABBREV_TAC `mu = --s * h + c * t` THEN
  SUBGOAL_THEN `lm < &0` ASSUME_TAC THENL
   [C1092MNCSP_PROD `&0 < t * (--s - (&413 / &500) * c)` THEN
    C1092MNCSP_PROD `&0 < c * ((&413 / &500) * t - h)` THEN
    EXPAND_TAC "lm" THEN C1092MNCSP_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mu` ASSUME_TAC THENL
   [C1092MNCSP_PROD `&0 <= --s * h` THEN C1092MNCSP_PROD `&0 < c * t` THEN
    EXPAND_TAC "mu" THEN C1092MNCSP_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `h * c + t * s = lm /\ --h * s + t * c = mu` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["lm"; "mu"] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `h:real`; `t:real`; `lm:real`; `mu:real`]
    C1092WS_LOWER_NP) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `h:real`; `t:real`; `lm:real`; `mu:real`]
    C1092WS_UPPER_NP) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN `a - c <= u + a /\ u <= --s - (&14 / &25) * c - a /\
                v <= --(&13 / &50) * --s - a /\ --(&7 / &20) * (c + --s) <= v + a`
    STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN C1092MNCSP_LIN; ALL_TAC] THEN
  C1092MNCSP_PROD `&0 <= --lm * ((u + a) - (a - c))` THEN
  C1092MNCSP_PROD `&0 <= mu * ((--(&13 / &50) * --s - a) - v)` THEN
  C1092MNCSP_PROD `&0 <= --lm * ((--s - (&14 / &25) * c - a) - u)` THEN
  C1092MNCSP_PROD `&0 <= mu * ((v + a) - --(&7 / &20) * (c + --s))` THEN
  C1092MNCSP_PROD `&0 < (a - &1) * (mu - lm)` THEN
  C1092MNCSP_PROD `&0 < (a - &1) * --lm` THEN
  SUBGOAL_THEN `c - --s - &3 / &5 + (&37 / &50) * --s pow 2 <= &0 /\
                &1 + (&37 / &50) * c * --s - (c + --s) < &0 /\
                &0 <= &11 / &25 - c + (&21 / &100) * --s pow 2 + (&13 / &20) * c * --s /\
                &0 < --s - (&13 / &20) * --s pow 2 - &7 / &20 + (&21 / &100) * c * --s`
    STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_ARITH `c * --s = --(c * s)`]) THEN
    REWRITE_TAC[REAL_ARITH `c * --s = --(c * s)`] THEN
    REPEAT CONJ_TAC THEN C1092MNCSP_LIN; ALL_TAC] THEN
  C1092MNCSP_PROD `&0 <= h * --(c - --s - &3 / &5 + (&37 / &50) * --s pow 2)` THEN
  C1092MNCSP_PROD `&0 < t * --(&1 + (&37 / &50) * c * --s - (c + --s))` THEN
  C1092MNCSP_PROD `&0 <= h * (&11 / &25 - c + (&21 / &100) * --s pow 2 + (&13 / &20) * c * --s)` THEN
  C1092MNCSP_PROD `&0 < t * (--s - (&13 / &20) * --s pow 2 - &7 / &20 + (&21 / &100) * c * --s)` THEN
  SUBGOAL_THEN
   `lm * (&1 - c) + mu * (--(&13 / &50) * --s - &1) + (&2 / &5) * h + t =
      h * (c - --s - &3 / &5 + (&37 / &50) * --s pow 2) + t * (&1 + (&37 / &50) * c * --s - (c + --s)) /\
    lm * (--s - (&14 / &25) * c - &1) + mu * (--(&7 / &20) * (c + --s)) + h =
      h * (&11 / &25 - c + (&21 / &100) * --s pow 2 + (&13 / &20) * c * --s) +
      t * (--s - (&13 / &20) * --s pow 2 - &7 / &20 + (&21 / &100) * c * --s)`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["lm"; "mu"] THEN
    CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  CONJ_TAC THEN C1092MNCSP_LIN);;
