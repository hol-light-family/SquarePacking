(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallOppositeEscape.lean                   *)
(* Normal is c977cc_normal; the opposite square D has sD = --S.              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/FullAuxWallRightSupport.ml";;
needs "n12/geometry/FullAuxWallLowerCorner.ml";;

let FAWOE_NORMALS_TAC =
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC));;

(* Lean: lower_v_margin (private) *)
let FAWOE_LOWER_V_MARGIN = prove
 (`forall c s C S. c977cc_normal c s /\ c977cc_normal C S /\ &4 * s <= c
     ==> (&13 / &50) * s <= (c * S + s * C) * (&1 - S - (&13 / &50) * C)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN FAWOE_NORMALS_TAC THEN
  NLIN_FACTS_TAC [] [`&1 / &10 <= &1 - S - (&13 / &50) * C`] THEN
  SUBGOAL_THEN `&13 / &50 <= (&4 * S + C) * (&1 - S - (&13 / &50) * C)` ASSUME_TAC THENL
   [ASM_CASES_TAC `&13 / &20 <= S` THENL
     [NLIN_FACTS_TAC []
       [`&0 <= (&4 * S + C) * ((&1 - S - (&13 / &50) * C) - &1 / &10)`] THEN
      NLIN_TAC [];
      NLIN_FACTS_TAC []
       [`&0 <= (&4 * S + C) * ((&1 - S - (&13 / &50) * C) - (&37 / &50 - S))`;
        `&0 <= (&37 / &50 - S) * (C - &7 / &10)`; `&0 <= S * (&13 / &20 - S)`] THEN
      NLIN_TAC []];
    ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (c - &4 * s) * S`;
    `&0 <= ((c - &4 * s) * S) * (&1 - S - (&13 / &50) * C)`;
    `&0 <= s * ((&4 * S + C) * (&1 - S - (&13 / &50) * C) - &13 / &50)`] THEN
  NLIN_TAC []);;

(* Lean: narrow_of_cut (private) *)
let FAWOE_NARROW_OF_CUT = prove
 (`forall c s C S u v. c977cc_normal c s /\ c977cc_normal C S /\ &0 < s /\
     &4 * s <= c /\ &0 < u /\ &0 < v /\
     &1 - C + (&13 / &50) * S < u /\
     (c * C - s * S) * u + (c * S + s * C) * v < (&13 / &50) * s
     ==> &4 * S < C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN FAWOE_NORMALS_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (&4 * S - C) * (&4 * S + C)`; `C <= &34 / &35`;
    `&0 <= (C - &7 / &10) * (&34 / &35 - C)`;
    `&13 / &150 <= C - (&187 / &200) * C pow 2`;
    `&0 <= s * (C - S)`; `&0 <= C * (c - &4 * s)`;
    `(&3 / &4) * c * C <= c * C - s * S`; `&0 < (&3 / &4) * c * C`;
    `(&3 / &4) * c * C * (&1 - C + (&13 / &50) * S) < (&3 / &4) * c * C * u`;
    `&0 <= u * ((c * C - s * S) - (&3 / &4) * c * C)`;
    `&0 <= ((&39 / &200) * c * C) * (&4 * S - C)`;
    `&0 <= ((&3 / &4) * c) * ((C - (&187 / &200) * C pow 2) - &13 / &150)`;
    `&0 <= c * S + s * C`; `&0 <= (c * S + s * C) * v`] THEN
  NLIN_TAC []);;

(* Lean: narrow_and_left *)
let FAWOE_NARROW_AND_LEFT = prove
 (`forall cD sD uD vD aD c s S.
     c977cc_normal c s /\ &0 < s /\ &4 * s <= c /\
     sD = --S /\ c977cc_normal cD S /\ &1 < aD /\
     linside cD sD uD vD aD (&2) (&2) /\ linside cD sD uD vD aD (&2) (&3 / &2) /\
     ~linside cD sD uD vD aD (&1) (&87 / &50) /\
     (c * cD - s * S) * (uD + aD - &2 * (cD - S)) +
     (c * S + s * cD) * (vD + aD - &2 * (cD + S)) < (&13 / &50) * s
     ==> &4 * S < cD /\ linside cD sD uD vD aD (&11 / &10) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `sD = --S` o concl)) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `cD:real`; `S:real`] FAWOE_LOWER_V_MARGIN) THEN
  MP_TAC(SPECL [`cD:real`; `S:real`] C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `u = uD + aD - &2 * (cD - S)` THEN
  ABBREV_TAC `v = vD + aD - &2 * (cD + S)` THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside cD (--S) uD vD aD (&2) (&2)`; `linside cD (--S) uD vD aD (&2) (&3 / &2)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN FAWOE_NORMALS_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 < u`; `&0 < v`; `&0 < c * cD - s * S`; `&0 < c * S + s * cD`] THEN
  SUBGOAL_THEN `cD - (&87 / &50) * S <= uD` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `vD < S + (&87 / &50) * cD` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      NLIN_FACTS_TAC []
       [`&1 - S - (&13 / &50) * cD < v`;
        `(c * S + s * cD) * (&1 - S - (&13 / &50) * cD) < (c * S + s * cD) * v`;
        `&0 <= (c * cD - s * S) * u`] THEN
      RASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ASSUME `~linside cD (--S) uD vD aD (&1) (&87 / &50)`) THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 - cD + (&13 / &50) * S < u` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `cD:real`; `S:real`; `u:real`; `v:real`] FAWOE_NARROW_OF_CUT) THEN
  ANTS_TAC THENL [REWRITE_TAC[c977cc_normal] THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
                  DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (cD - &4 * S) * (cD + &4 * S)`; `&9 / &10 <= cD`;
    `&0 <= s * (cD - S)`; `&0 <= cD * (c - &4 * s)`; `&0 <= c * (cD - &9 / &10)`;
    `(&27 / &40) * c <= c * cD - s * S`] THEN
  SUBGOAL_THEN `u < &1 / &10` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`(c * cD - s * S) * (&1 / &10) <= (c * cD - s * S) * u`;
      `&0 <= (c * S + s * cD) * v`] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;
