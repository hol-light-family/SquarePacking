(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveBLeftReduction.lean                      *)
(* (N12Compact.PositiveBLeftReduction).  Positive-B reduction for the        *)
(* unfinished 849/851 configuration.                                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/LeftUpperCover.ml";;
needs "n12/geometry/C849PositiveSupport.ml";;

let PBLR_SP_TAC c s dx dy =
  MP_TAC(SPECL [c; s; dx; dy] FSAF_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  STRIP_TAC;;

(* Lean: low_inside *)
let PBLR_LOW_INSIDE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < c /\ &0 <= s /\ s <= c /\ &1 < a /\
      lclosed c s u v a (&33 / &20) (&47 / &20) /\
      lclosed c s u v a (&8 / &5) (&3) /\
      u + a <= (&113 / &50) * c + &3 * s /\
      -- &2 * s + (&5 / &2) * c <= v
      ==> linside c s u v a (&7 / &5) (&5 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FSAF_SP_TAC `&43 / &50` `&1 / &2` THEN
  FSAF_SP_TAC `--(&3 / &5)` `&0` THEN
  LUC_LIN_TAC);;

(* Lean: coupled_faces *)
let PBLR_COUPLED_FACES = prove
 (`forall cB sB uB vB aB cL sL uL vL aL.
      cB * cB + sB * sB = &1 /\ cL * cL + sL * sL = &1 /\
      &0 < cB /\ &0 <= sB /\ sB <= cB /\ &0 < cL /\ abs sL <= cL /\
      &1 < aB /\ &1 < aL /\
      lcont cL sL uL vL aL /\
      lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
      lclosed cB sB uB vB aB (&8 / &5) (&3) /\
      uB + aB <= (&113 / &50) * cB + &3 * sB /\
      -- &2 * sB + (&5 / &2) * cB <= vB /\
      lclosed cL sL uL vL aL (&457 / &500) (&2) /\
      lclosed cL sL uL vL aL (&1) (&12 / &5) /\
      ~linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
      ~linside cL sL uL vL aL (&33 / &20) (&33 / &20) /\
      ldisj cB sB uB vB aB cL sL uL vL aL
      ==> cB + (&283 / &100) * sB <= uB /\
          --sL * (&19 / &25) + cL * (&187 / &100) <= vL`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] PBLR_LOW_INSIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`]
    LUC_HIGH_OF_NOT_LOW) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~linside cB sB uB vB aB (&1) (&283 / &100)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `cB - &7 / &10`; SQ_NONNEG `cB - sB`;
                  SQ_NONNEG `cB + sB - &10 / &7`]
   [`&0 <= (cB - sB) * (cB + sB)`; `&7 / &10 <= cB`; `cB + sB <= &10 / &7`] THEN
  UNDISCH_THEN `~linside cL sL uL vL aL (&19 / &25) (&187 / &100)` (K ALL_TAC) THEN
  UNDISCH_THEN `~linside cL sL uL vL aL (&33 / &20) (&33 / &20)` (K ALL_TAC) THEN
  LUC_LIN_TAC);;

(* Lean: upper_left_marker_modes *)
let PBLR_UPPER_LEFT_MARKER_MODES = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < c /\ &0 <= s /\ &1 < a /\
      lclosed c s u v a (&33 / &20) (&47 / &20) /\
      lclosed c s u v a (&8 / &5) (&3) /\
      -- &2 * s + (&5 / &2) * c <= v /\
      ~linside c s u v a (&1) (&3)
      ==> c + &3 * s <= u \/
          (v + a <= --s + &3 * c /\ a <= s + c / &2 /\ &3 * c / &4 < s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `c + &3 * s <= u` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `v + a <= --s + &3 * c /\ a <= s + c / &2` STRIP_ASSUME_TAC THENL
   [LUC_LIN_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= c * (&3 * c / &4 - s)`; `&1 < s + c / &2`] THEN
  NLIN_TAC [SQ_NONNEG `s + c / &2 - &1`]);;

(* Lean: not_lower_U_of_right_cap *)
let PBLR_NOT_LOWER_U_OF_RIGHT_CAP = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < c /\ &0 <= s /\ &1 < a /\
      lclosed c s u v a (&33 / &20) (&47 / &20) /\
      -- &2 * s + (&5 / &2) * c <= v /\
      u + a <= (&1043 / &500) * c + &3 * s
      ==> ~(c + &3 * s <= u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lclosed] THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&3 * c <= &7 * s /\ &500 / &543 < c` STRIP_ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (&7 * s - &3 * c) * (&7 * s + &3 * c)`;
    `&0 < (c - &500 / &543) * (c + &500 / &543)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: no_longitudinal_gap *)
let PBLR_NO_LONGITUDINAL_GAP = prove
 (`forall c s a support.
      &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ &1 < a /\ a <= s + c / &2 /\
      c + (&283 / &100) * s <= support /\
      support + a <= (&1043 / &500) * c + &3 * s
      ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&3 * c / &4 < s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`&0 <= c * (&3 * c / &4 - s)`; `&1 < s + c / &2`] THEN
    NLIN_TAC [SQ_NONNEG `s + c / &2 - &1`];
    ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - &4 / &5`; SQ_NONNEG `c - s`;
                  SQ_NONNEG `c + s - &10 / &7`]
   [`&0 < (s - &3 * c / &4) * (s + &3 * c / &4)`; `c <= &4 / &5`;
    `c + s <= &10 / &7`] THEN
  RASM_ARITH_TAC);;

let PBLR_CAP_TERM = `uL + aB <=
      (cB * cL + sB * sL) * uB +
      (cB * sL - sB * cL) * (vB + aB / &2) -
      aB / &2 * abs (cB * sL - sB * cL)`;;
let PBLR_UNIT_TAC =
  MP_TAC(AP_TERM `(*) cL` (ASSUME `cB * cB + sB * sB = &1`)) THEN
  MP_TAC(AP_TERM `(*) sL` (ASSUME `cB * cB + sB * sB = &1`));;

(* Lean: impossible_with_right_cap *)
let PBLR_IMPOSSIBLE_WITH_RIGHT_CAP = prove
 (`forall cB sB uB vB aB cL sL uL vL aL.
      cB * cB + sB * sB = &1 /\ cL * cL + sL * sL = &1 /\
      &0 < cB /\ &0 <= sB /\ sB <= cB /\ &0 < cL /\ abs sL <= cL /\
      &1 < aB /\ aB = aL /\
      lcont cL sL uL vL aL /\
      lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
      lclosed cB sB uB vB aB (&8 / &5) (&3) /\
      -- &2 * sB + (&5 / &2) * cB <= vB /\
      uB + aB <= (&1043 / &500) * cB + &3 * sB /\
      ~linside cB sB uB vB aB (&1) (&3) /\
      lclosed cL sL uL vL aL (&457 / &500) (&2) /\
      lclosed cL sL uL vL aL (&1) (&12 / &5) /\
      ~linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
      ~linside cL sL uL vL aL (&33 / &20) (&33 / &20) /\
      ldisj cB sB uB vB aB cL sL uL vL aL
      ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aB:real = aL`)) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`]
    PBLR_COUPLED_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    PBLR_UPPER_LEFT_MARKER_MODES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
      PBLR_NOT_LOWER_U_OF_RIGHT_CAP) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `cL:real`; `sL:real`] FSBL_DOT_NONNEG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`]
    FSBL_LEFT_UPPER_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`]
    BLL_TWO_DIRECTED_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [(* B axis *)
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                  `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`]
      FSBL_RIGHT_AXIS_CAP) THEN
    ASM_REWRITE_TAC[tss_support_radius] THEN
    REWRITE_TAC[REAL_ARITH `cB * cL + sB * sL = cL * cB + sL * sB`;
                REAL_ARITH `abs(--cB * sL + sB * cL) = abs(cB * sL - sB * cL)`] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`] FSBL_LEFT_WALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`] LCENTRE_COORDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(SPECL [`aB:real`; `cB:real`; `sB:real`; `cL:real`; `sL:real`;
                  `lcx cL sL uL vL aB`; `lcy cL sL uL vL aB`] FSL_LEFT_SUPPORT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MATCH_MP_TAC PBLR_NO_LONGITUDINAL_GAP THEN
    MAP_EVERY EXISTS_TAC
     [`cB:real`; `sB:real`; `aB:real`;
      `cB * lcx cL sL uL vL aB + sB * lcy cL sL uL vL aB +
       aB / &2 * (cB * cL + sB * sL + abs(cB * sL - sB * cL))`] THEN
    ASM_REWRITE_TAC[REAL_POW_2] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_ARITH `cL * cB + sL * sB = cB * cL + sB * sL`]) THEN
    ASM_REAL_ARITH_TAC;
    (* L axis *)
    MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`;
                  `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
      FSBL_LEFT_AXIS_CAP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
        can (find_term ((=) `C977CB_pairRadius`)) (concl th))) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                  `cL:real`; `sL:real`] FSBL_MINIMUM_PROJECTION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC C849PS_L_AXIS_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`cB:real`; `sB:real`; `cL:real`; `sL:real`; `uL + aB`] THEN
    ASM_REWRITE_TAC[REAL_POW_2] THEN
    REPEAT CONJ_TAC THEN DISCH_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `&0 <= sL`)) THEN
      SUBGOAL_THEN `&0 <= (aB - &1) * (&1 + sL / cL)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN
        SUBGOAL_THEN `&0 <= sL / cL` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `sL <= &0`)) THEN
      UNDISCH_TAC `&1 < aB` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
      UNDISCH_TAC PBLR_CAP_TERM THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
      MP_TAC(SPECL [`cB * cL + sB * sL`; `uB + aB`; `&1043 / &500 * cB + &3 * sB`]
        REAL_LE_LMUL) THEN
      MP_TAC(SPECL [`cB * sL - sB * cL`; `vB + aB`; `--sB + &3 * cB`]
        REAL_LE_LMUL) THEN
      MP_TAC(SPECL [`aB - &1`; `cB * cL + sB * sL + (cB * sL - sB * cL)`] REAL_LE_MUL) THEN
      ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      PBLR_UNIT_TAC THEN
      REAL_ARITH_TAC;
      UNDISCH_TAC PBLR_CAP_TERM THEN
      ASM_SIMP_TAC[REAL_ARITH `x <= &0 ==> abs x = --x`] THEN
      MP_TAC(SPECL [`cB * cL + sB * sL`; `uB + aB`; `&1043 / &500 * cB + &3 * sB`]
        REAL_LE_LMUL) THEN
      MP_TAC(MATCH_MP REAL_LE_LMUL (CONJ
        (MATCH_MP (REAL_ARITH `x <= &0 ==> &0 <= --x`) (ASSUME `cB * sL - sB * cL <= &0`))
        (ASSUME `-- &2 * sB + &5 / &2 * cB <= vB`))) THEN
      MP_TAC(SPECL [`aB - &1`; `cB * cL + sB * sL - (cB * sL - sB * cL)`] REAL_LE_MUL) THEN
      ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      PBLR_UNIT_TAC THEN
      REAL_ARITH_TAC]]);;
