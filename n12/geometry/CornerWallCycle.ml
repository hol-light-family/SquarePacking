(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallCycle.lean                             *)
(* (namespace N12Compact.CornerWallCycle).                                   *)
(* A complete support-selector sector for three actual squares O, L, W.      *)
(* Squares are 5-tuples (cO sO uO vO aO) etc.; Lean upper/lower are         *)
(* ABT_upper/ABT_lower; bottom is cwcb_bottom; left_wall is FSBL_LEFT_WALL;  *)
(* corner_faces is C696PC_CORNER_FACES and LeftWallNegativeFaces.faces is    *)
(* LWNF_FACES.  Normal c s is c977cc_normal c s.                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CornerWallCycleBounds.ml";;
needs "n12/geometry/C696PositiveCorner.ml";;
needs "n12/geometry/LeftWallNegativeFaces.ml";;

(* Lean: relative_nonnegative (private) *)
let CWC_RELATIVE_NONNEGATIVE = prove
 (`forall c s l r. c977cc_normal c s /\ c977cc_normal l r ==> &0 <= c * l - s * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= l * (c - s)`; `&0 <= s * (l - r)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: cross_order (private) *)
let CWC_CROSS_ORDER = prove
 (`forall c s l r. c977cc_normal c s /\ c977cc_normal l r /\ r <= s ==> c * r <= s * l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `l:real`; `r:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= c * (s - r)`; `&0 <= s * (l - c)`] THEN
  NLIN_TAC ~deg2:false []);;

(* The common closing step of transverse_sector (Lean: the local `close`). *)
let CWC_CLOSE = prove
 (`forall c s d t P wl H U Lo aL aW vW.
     &0 < c /\ &0 < d /\ &0 <= c * t + d * s /\ &0 <= P /\ &0 <= wl /\
     &0 <= (d / c) * cwcb_bottom c s + &1 + P - t - &3 * d /\
     c * U - d * H - aL * c * P = (c * t + d * s) * wl + d * (Lo - H) /\
     H <= Lo /\ U <= vW /\ vW + aW <= t + &3 * d /\ aL = aW /\
     cwcb_bottom c s < H /\ &1 < aL
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aW`)) THEN
  SUBGOAL_THEN `c * ((d / c) * cwcb_bottom c s) = d * cwcb_bottom c s` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (c * t + d * s) * wl`; `&0 <= d * (Lo - H)`;
    `&0 <= c * (vW - U)`; `&0 <= c * ((t + &3 * d) - (vW + aL))`;
    `&0 <= c * ((d / c) * cwcb_bottom c s + &1 + P - t - &3 * d)`;
    `&0 < d * (H - cwcb_bottom c s)`; `&0 < c * (aL - &1)`;
    `&0 < (c * (aL - &1)) * (&1 + P)`] THEN
  NLIN_TAC ~deg2:false []);;

(* rewrite the band forms of the two supports, then a pure field identity *)
let CWC_FIELD_TAC =
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can (term_match [] `ABT_upper c s u v a x y`)
                  (lhs(concl th)) then REWRITE_TAC[th] else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can (term_match [] `ABT_lower c s u v a x y`)
                  (lhs(concl th)) then REWRITE_TAC[th] else NO_TAC) THEN
  UNDISCH_TAC `~(cO = &0)` THEN CONV_TAC REAL_FIELD;;

(* Lean: transverse_sector *)
let CWC_TRANSVERSE_SECTOR = prove
 (`forall cO sO (uO:real) vO aO cL sL uL vL aL cW sW (uW:real) vW aW t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cO sO /\ c977cc_normal cW t /\ sW = --t /\
     &0 < cL /\ abs sL <= cL /\ &1 < aL /\ aL = aW /\ lcont cL sL uL vL aL /\
     sO <= t /\
     cwcb_bottom cO sO < vO + aO /\
     vW + aW <= t + &3 * cW /\
     vO + aO <= ABT_lower cL sL uL vL aL (--sO) cO /\
     ABT_upper cL sL uL vL aL t cW <= vW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[lcx] THEN DISCH_TAC] THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `~(cO = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`&0 <= cO * t + cW * sO`] THEN
  let CLOSE_TAC sl P wl ptac =
    MATCH_MP_TAC CWC_CLOSE THEN
    MAP_EVERY EXISTS_TAC [`cO:real`; `sO:real`; `cW:real`; `t:real`; P; wl; `vO + aO`;
      mk_comb(mk_comb(mk_comb(mk_comb(mk_comb(mk_comb(mk_comb(
        `ABT_upper`,`cL:real`),sl),`uL:real`),`vL:real`),`aL:real`),`t:real`),`cW:real`);
      mk_comb(mk_comb(mk_comb(mk_comb(mk_comb(mk_comb(mk_comb(
        `ABT_lower`,`cL:real`),sl),`uL:real`),`vL:real`),`aL:real`),`--sO`),`cO:real`);
      `aL:real`; `aW:real`; `vW:real`] THEN
    REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC; CWC_FIELD_TAC; ptac; ASM_REAL_ARITH_TAC] in
  ASM_CASES_TAC `&0 <= sL` THENL
   [SUBGOAL_THEN `c977cc_normal cL sL` ASSUME_TAC THENL
     [REWRITE_TAC[c977cc_normal] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
    MP_TAC(SPECL [`cW:real`; `t:real`; `cL:real`; `sL:real`] CWC_RELATIVE_NONNEGATIVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs sL = sL` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= cL * uL - sL * (vL + aL)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_FACTS_TAC [] [`&0 <= cO * cL + sO * sL`; `&0 <= t * cL + cW * sL`] THEN
    SUBGOAL_THEN `ABT_upper cL sL uL vL aL t cW =
                  (t * cL + cW * sL) * (uL + aL) + (cW * cL - t * sL) * (vL + aL)`
      ASSUME_TAC THENL
     [REWRITE_TAC[C977NCO_UPPER_IN_BANDS] THEN
      SUBGOAL_THEN `abs(t * cL + cW * sL) = t * cL + cW * sL /\
                    abs(--t * sL + cW * cL) = cW * cL - t * sL` (fun th -> REWRITE_TAC[th]) THENL
       [CONJ_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
    ASM_CASES_TAC `sL <= sO` THENL
     [MP_TAC(SPECL [`cO:real`; `sO:real`; `cL:real`; `sL:real`] CWC_CROSS_ORDER) THEN
      MP_TAC(SPECL [`cO:real`; `sO:real`; `cW:real`; `t:real`; `cL:real`; `sL:real`]
        CWCB_POSITIVE_COEFFICIENT) THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `ABT_lower cL sL uL vL aL (--sO) cO =
                    (cO * sL - sO * cL) * (uL + aL) + (cO * cL + sO * sL) * vL`
        ASSUME_TAC THENL
       [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
        SUBGOAL_THEN `abs(--sO * cL + cO * sL) = sO * cL - cO * sL /\
                      abs(-- --sO * sL + cO * cL) = cO * cL + sO * sL`
          (fun th -> REWRITE_TAC[th]) THENL
         [CONJ_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= cW * sO / cO` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
      CLOSE_TAC `sL:real` `cL * (t + cW) + (cW * sO / cO) * (cL + sL)` `cL * uL - sL * (vL + aL)`
       (MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REAL_ARITH_TAC);
      POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
      MP_TAC(SPECL [`cL:real`; `sL:real`; `cO:real`; `sO:real`] CWC_CROSS_ORDER) THEN
      MP_TAC(SPECL [`cO:real`; `sO:real`; `cW:real`; `t:real`; `cL:real`; `sL:real`]
        CWCB_POSITIVE_LARGE_COEFFICIENT) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `ABT_lower cL sL uL vL aL (--sO) cO =
                    (cO * sL - sO * cL) * uL + (cO * cL + sO * sL) * vL`
        ASSUME_TAC THENL
       [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
        SUBGOAL_THEN `abs(--sO * cL + cO * sL) = cO * sL - sO * cL /\
                      abs(-- --sO * sL + cO * cL) = cO * cL + sO * sL`
          (fun th -> REWRITE_TAC[th]) THENL
         [CONJ_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= sO / cO` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CLOSE_TAC `sL:real` `cL * (t + cW) + cW * sL * (&1 + sO / cO)` `cL * uL - sL * (vL + aL)`
       (MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC)];
    POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    ABBREV_TAC `r = --sL` THEN
    SUBGOAL_THEN `sL = --r` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `c977cc_normal cL r` ASSUME_TAC THENL
     [REWRITE_TAC[c977cc_normal] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      UNDISCH_TAC `cL * cL + --r * --r = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`cO:real`; `sO:real`; `cL:real`; `r:real`] CWC_RELATIVE_NONNEGATIVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs(--r) = r` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= cL * uL + r * vL` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_FACTS_TAC [] [`&0 <= sO * cL + cO * r`; `&0 <= t * r + cW * cL`] THEN
    MP_TAC(SPECL [`cL:real`; `--r`; `uL:real`; `vL:real`; `aL:real`; `r:real`;
                  `--sO`; `cO:real`] C977NCO_LOWER_NEGATIVE_NONPOS) THEN
    ANTS_TAC THENL [REWRITE_TAC[] THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    ASM_CASES_TAC `r <= t` THENL
     [MP_TAC(SPECL [`cW:real`; `t:real`; `cL:real`; `r:real`] CWC_CROSS_ORDER) THEN
      MP_TAC(SPECL [`cO:real`; `sO:real`; `cW:real`; `t:real`; `cL:real`; `r:real`]
        CWCB_NEGATIVE_COEFFICIENT) THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
      MP_TAC(SPECL [`cL:real`; `--r`; `uL:real`; `vL:real`; `aL:real`; `r:real`;
                    `t:real`; `cW:real`] C977NCO_UPPER_NEGATIVE_POS) THEN
      ANTS_TAC THENL [REWRITE_TAC[] THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN `&0 <= cW * sO / cO` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
      CLOSE_TAC `--r` `cL * (t + cW + cW * sO / cO) + t * r` `cL * uL + r * vL`
       (MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REAL_ARITH_TAC);
      POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
      MP_TAC(SPECL [`cL:real`; `r:real`; `cW:real`; `t:real`] CWC_CROSS_ORDER) THEN
      MP_TAC(SPECL [`cO:real`; `sO:real`; `cW:real`; `t:real`; `cL:real`; `r:real`]
        CWCB_NEGATIVE_LARGE_COEFFICIENT) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT DISCH_TAC THEN
      MP_TAC(SPECL [`cL:real`; `--r`; `uL:real`; `vL:real`; `aL:real`; `r:real`;
                    `t:real`; `cW:real`] C977NCO_UPPER_NEGATIVE_NONPOS) THEN
      ANTS_TAC THENL [REWRITE_TAC[] THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN `&0 <= sO / cO` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CLOSE_TAC `--r` `cW * cL * (&1 + sO / cO) + r * (t + cW)` `cL * uL + r * vL`
       (MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC)]]);;

(* Lean: original_transverse_sector *)
let CWC_ORIGINAL_TRANSVERSE_SECTOR = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cO sO /\ c977cc_normal cW t /\ sW = --t /\
     &0 < cL /\ abs sL <= cL /\ &1 < aL /\ aO = aL /\ aL = aW /\
     lcont cO sO uO vO aO /\ lcont cL sL uL vL aL /\ lcont cW sW uW vW aW /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     ~linside cO sO uO vO aO (&1) (&1) /\
     ~linside cO sO uO vO aO (&2) (&457 / &500) /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     linside cW sW uW vW aW (&1) (&113 / &50) /\
     ~linside cW sW uW vW aW (&1) (&2) /\
     ~linside cW sW uW vW aW (&457 / &500) (&3) /\
     sO <= t /\
     vO + aO <= ABT_lower cL sL uL vL aL (--sO) cO /\
     ABT_upper cL sL uL vL aL t cW <= vW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`] C696PC_CORNER_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`] LWNF_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `cwcb_bottom cO sO <= c696cm_boundary cO sO` ASSUME_TAC THENL
   [REWRITE_TAC[CWCB_BOTTOM_DEF; c696cm_boundary] THEN
    SUBGOAL_THEN `&0 <= sO pow 2 / cO` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
    `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
    `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`] CWC_TRANSVERSE_SECTOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]]);;
