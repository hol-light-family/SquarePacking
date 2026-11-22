(* ========================================================================= *)
(* Port of Compact/Completion/C1092/ShortWallCrossing.lean                   *)
(* (N12Compact.C1092ShortWallCrossing).  The half-angle crossing with the    *)
(* short endpoint 1197/500 is impossible.                                    *)
(* S12.short_projections is FSAF_SHORT_PROJECTIONS.                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralWallPairSupport.ml";;
needs "n12/geometry/CentralWallEscape.ml";;
needs "n12/geometry/FourSquareAForced.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let C1092SWC_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092SWC_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092SWC_LIN_TAC; DISCH_TAC];;

let C1092SWC_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092SWC_LIN_TAC; DISCH_TAC];;

let C1092SWC_MISS_TAC pats =
  FIRST_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && is_conj(rand(concl th)) &&
    forall (fun p -> can (find_term ((=) p)) (concl th)) pats)) THEN
  REWRITE_TAC[TAUT `(~p ==> false) <=> p`] THEN REPEAT CONJ_TAC THEN C1092SWC_LIN_TAC;;

(* Lean: lower_face (private) *)
let C1092SWC_LOWER_FACE = prove
 (`forall c s u v a z.
     &0 < c /\ &0 <= s /\ &0 <= z /\ z < &197 / &500 /\
     linside c s u v a (&1543 / &500) (&2) /\
     linside c s u v a (&3) (&1197 / &500) /\
     ~linside c s u v a (&3) (&2 + z)
     ==> c * &3 + s * (&2 + z) <= u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  C1092SWC_LE_MUL_TAC `s:real` `&197 / &500 - z` THEN
  C1092SWC_LE_MUL_TAC `c:real` `z:real` THEN
  C1092SWC_LT_MUL_TAC `c:real` `&197 / &500 - z` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C1092SWC_MISS_TAC [`c * &3`; `s * (&2 + z)`]);;

(* Lean: outer_point *)
let C1092SWC_OUTER_POINT = prove
 (`forall c s u v a.
     &1 < a /\ c977cc_normal c s /\
     linside c s u v a (&113 / &50) (&2) /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     --(&47 / &20) * s + (&33 / &20) * c <= v /\
     v + a <= &3 * c - (&1197 / &500) * s /\
     ~linside c s u v a (&33 / &20) (&47 / &20)
     ==> linside c s u v a (&47 / &20) (&53 / &20)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&47 / &20 - &33 / &20`; `&53 / &20 - &47 / &20`]
    FSAF_SHORT_PROJECTIONS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&1197 / &500 - &47 / &20`; `&3 - &53 / &20`]
    FSAF_SHORT_PROJECTIONS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  SUBGOAL_THEN `c * (&33 / &20) + s * (&47 / &20) <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092SWC_MISS_TAC [`c * &33 / &20`; `s * &47 / &20`]; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C1092SWC_LIN_TAC);;

(* Lean: alternatives (private) *)
let C1092SWC_ALTERNATIVES = prove
 (`forall cA sA uA vA aA cR sR uR vR aR z.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ aA = aR /\
     &0 < cA /\ &0 <= sA /\ &12 * sA <= &5 * cA /\
     &0 < cR /\ &0 <= sR /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     --(&47 / &20) * sA + (&33 / &20) * cA <= vA /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&1197 / &500) /\
     &0 <= z /\ z < &197 / &500 /\
     linside cA sA uA vA aA (&3) (&2 + z) /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> uA + aA <= ABT_lower cR sR uR vR aR cA sA \/
         ABT_upper cA sA uA vA aA cR sR <= uR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aR`)) THEN
  NLIN_FACTS_TAC [SQ_NONNEG `sA:real`] [`cA <= &1`] THEN
  C1092SWC_LE_MUL_TAC `cR:real` `z:real` THEN
  C1092SWC_LT_MUL_TAC `cR:real` `&197 / &500 - z` THEN
  let sqA = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
  and sqR = [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] in
  let dirs = [`cA:real`,`sA:real`; `--sA`,`cA:real`; `cR:real`,`sR:real`; `--sR`,`cR:real`] in
  ABT_ALL_SB_TAC [sqA,(`&113 / &50`,`&2`); sqA,(`&3`,`&2 + z`);
                  sqR,(`&1543 / &500`,`&2`); sqR,(`&3`,`&1197 / &500`)] dirs THEN
  ABT_OWN_TAC sqA THEN ABT_OWN_TAC sqR THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  FIRST [DISJ1_TAC THEN C1092SWC_LIN_TAC; DISJ2_TAC THEN C1092SWC_LIN_TAC;
         MATCH_MP_TAC(TAUT `false ==> p`) THEN C1092SWC_LIN_TAC]);;

(* Lean: central_axis_impossible *)
let C1092SWC_CENTRAL_AXIS_IMPOSSIBLE = prove
 (`forall cA sA uA (vA:real) aA cR sR uR vR aR.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ aA = aR /\ lcont cR sR uR vR aR /\
     &0 < cA /\ &0 <= sA /\ &0 < cR /\ &0 <= sR /\
     &12 * sA <= &5 * cA /\ &0 <= cA * sR - sA * cR /\
     &2 * cA + &2 * sA <= uA /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&1197 / &500) /\
     uA + aA <= ABT_lower cR sR uR vR aR cA sA
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aR`)) THEN
  C1092SWC_LT_MUL_TAC `cA:real` `cR:real` THEN C1092SWC_LE_MUL_TAC `sA:real` `sR:real` THEN
  SUBGOAL_THEN `&0 < cA * cR + sA * sR` ASSUME_TAC THENL [C1092SWC_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] CWPS_SUPPORT_FORMULAS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092SWC_LIN_TAC; STRIP_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `sA:real`] [`cA <= &1`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  (* shallow *)
  SUBGOAL_THEN `sR < cR` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092SWC_LT_MUL_TAC `cA * cR + sA * sR` `cR * &1543 / &500 + sR * &2 - uR` THEN
    C1092SWC_LE_MUL_TAC `cA * sR - sA * cR` `vR + aA - (--sR * &3 + cR * &1197 / &500)` THEN
    C1092SWC_LE_MUL_TAC `sR - cR` `(&197 / &500) * cA - (&43 / &500) * sA` THEN
    C1092SWC_LE_MUL_TAC `cR:real` `(&77 / &250) * cA - (&12 / &25) * sA` THEN
    C1092SWC_LE_MUL_TAC `cR:real`
      `(sR - cR) * ((&197 / &500) * cA - (&43 / &500) * sA) +
       cR * ((&77 / &250) * cA - (&12 / &25) * sA)` THEN
    SUBGOAL_THEN
     `(cA * cR + sA * sR) * (cR * &1543 / &500 + sR * &2) -
      (cA * sR - sA * cR) * (--sR * &3 + cR * &1197 / &500) =
      (&1543 / &500) * cA + &2 * sA -
      (cA * sR - sA * cR) * ((&197 / &500) * cR + (&43 / &500) * sR) /\
      (cA * sR - sA * cR) * ((&197 / &500) * cR + (&43 / &500) * sR) -
      (&43 / &500) * cA =
      cR * ((sR - cR) * ((&197 / &500) * cA - (&43 / &500) * sA) +
            cR * ((&77 / &250) * cA - (&12 / &25) * sA))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN UNDISCH_TAC `cR * cR + sR * sR = &1` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    C1092SWC_LIN_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] CWE_RIGHT_WALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092SWC_LE_MUL_TAC `cA * cR + sA * sR` `&4 - (cR * (uR + aA) - sR * vR)` THEN
  C1092SWC_LE_MUL_TAC `sA:real` `--sR * &1543 / &500 + cR * &2 - vR` THEN
  SUBGOAL_THEN `(cA * cR + sA * sR) * sR - cR * (cA * sR - sA * cR) = sA` ASSUME_TAC THENL
   [UNDISCH_TAC `cR * cR + sR * sR = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `cR * ABT_lower cR sR uR vR aA cA sA =
    (cA * cR + sA * sR) * (cR * (uR + aA) - sR * vR) + sA * vR -
    aA * cR * ((cA * cR + sA * sR) + (cA * sR - sA * cR))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cR * cR + sR * sR = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cR:real`; `sR:real`] CWPM_PARALLEL_MARGIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN REPEAT CONJ_TAC THEN C1092SWC_LIN_TAC;
    DISCH_TAC] THEN
  C1092SWC_LE_MUL_TAC `cR:real`
    `&1 + (cA - sA) * cR + (cA + sA) * sR - &2 * cA - (&457 / &500) * sA * (sR / cR)` THEN
  SUBGOAL_THEN `sA * (cR * (sR / cR)) = sA * sR` ASSUME_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC REAL_DIV_LMUL THEN C1092SWC_LIN_TAC; ALL_TAC] THEN
  C1092SWC_LT_MUL_TAC `aA - &1`
    `cR * (&1 + (cA * cR + sA * sR) + (cA * sR - sA * cR))` THEN
  C1092SWC_LE_MUL_TAC `cR:real` `ABT_lower cR sR uR vR aA cA sA - (uA + aA)` THEN
  C1092SWC_LE_MUL_TAC `cR:real` `uA - (&2 * cA + &2 * sA)` THEN
  C1092SWC_LIN_TAC);;

(* Lean: impossible *)
let C1092SWC_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cR sR uR vR aR z.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ aA = aR /\ lcont cR sR uR vR aR /\
     c977cc_normal cA sA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&2) (&2) /\
     vA + aA <= &3 * cA - (&1197 / &500) * sA /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&1197 / &500) /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     &0 <= z /\ z < &197 / &500 /\
     (&1 + cA) * z = sA /\ sA * z = &1 - cA /\
     linside cA sA uA vA aA (&3) (&2 + z)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aR`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  SUBGOAL_THEN `&0 < cA` ASSUME_TAC THENL [C1092SWC_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] CLF_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = aA`)) THEN
  SUBGOAL_THEN `lcont cW sW uW vW aA /\ ldisj cA sA uA vA aA cW sW uW vW aA /\
                linside cW sW uW vW aA (&1543 / &500) (&2) /\
                linside cW sW uW vW aA (&3) (&1197 / &500)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[lcont; ldisj] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[lcont; ldisj]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`; `z:real`]
    C1092SWC_LOWER_FACE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `ldisj cA sA uA vA aA cW sW uW vW aA` THEN
    REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&3`; `&2 + z`]) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`; `z:real`]
    CWE_WALL_INEQUALITIES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `z:real`] CWE_HALF_ANGLE_LT) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `z:real`] CWE_SLOPE_OF_HALF_ANGLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    CWPA_CENTRAL_LOWER_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SWC_LIN_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    C1092SWC_OUTER_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`] CWPA_COSINE_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN REPEAT CONJ_TAC THEN C1092SWC_LIN_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cW:real`; `sW:real`; `z:real`] CWPA_WALL_ANGLE_ORDER) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`; `z:real`]
    C1092SWC_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SWC_LIN_TAC; STRIP_TAC] THENL
   [MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`]
      C1092SWC_CENTRAL_AXIS_IMPOSSIBLE);
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`]
      CWPS_WALL_AXIS_IMPOSSIBLE)] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092SWC_LIN_TAC);;
