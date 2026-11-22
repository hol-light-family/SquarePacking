(* ========================================================================= *)
(* Port of Compact/Geometry/FourSquareBLBridge.lean                          *)
(* (N12Compact.FourSquareBLBridge).  Elimination of the wrong lower face of  *)
(* L and support bounds connecting B/L to the scalar contradiction.          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FourSquareBCorner.ml";;
needs "n12/geometry/BLLongitudinal.ml";;

(* Lean: left_wall *)
let FSBL_LEFT_WALL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &0 <= c /\ lcont c s u v a
     ==> a * (c + abs s) / &2 <= lcx c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lcont] THEN STRIP_TAC THEN
  SUBGOAL_THEN `forall x y. linside c s u v a x y ==> &0 <= x /\ &0 <= y` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= s` THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 <= s ==> abs s = s`] THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
      TSS_POSITIVE_FRAME_WALL_BOUNDS) THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[REAL_ARITH `~(&0 <= s) ==> abs s = --s`] THEN
    MP_TAC(SPECL [`--s:real`; `c:real`; `v:real`; `--u - a:real`; `a:real`]
      TSS_POSITIVE_FRAME_WALL_BOUNDS) THEN
    ASM_REWRITE_TAC[LSEC_TURN_INSIDE; LSEC_TURN_CENTRE] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REAL_ARITH_TAC]);;

(* Lean: radius (private) *)
let FSBL_RADIUS = prove
 (`forall cq sq aq cr sr ar.
     C977CB_pairRadius cq sq aq cr sr ar =
     aq / &2 + tss_support_radius cr sr ar cq sq`,
  REWRITE_TAC[C977CB_pairRadius; tss_support_radius;
    REAL_ARITH `abs(--cq * sr + sq * cr) = abs(cq * sr - sq * cr)`]);;

(* Lean: right_axis_cap *)
let FSBL_RIGHT_AXIS_CAP = prove
 (`forall cq sq uq vq aq cr sr ur vr ar.
     cq * cq + sq * sq = &1 /\
     C977CB_pairRadius cq sq aq cr sr ar <=
       cq * (lcx cq sq uq vq aq - lcx cr sr ur vr ar) +
       sq * (lcy cq sq uq vq aq - lcy cr sr ur vr ar)
     ==> cq * lcx cr sr ur vr ar + sq * lcy cr sr ur vr ar +
         tss_support_radius cr sr ar cq sq <= uq`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FSBL_RADIUS] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

(* Lean: left_axis_cap *)
let FSBL_LEFT_AXIS_CAP = prove
 (`forall cq sq uq vq aq cr sr ur vr ar.
     cq * cq + sq * sq = &1 /\
     C977CB_pairRadius cq sq aq cr sr ar <=
       cq * (lcx cr sr ur vr ar - lcx cq sq uq vq aq) +
       sq * (lcy cr sr ur vr ar - lcy cq sq uq vq aq)
     ==> uq + aq <= cq * lcx cr sr ur vr ar + sq * lcy cr sr ur vr ar -
                    tss_support_radius cr sr ar cq sq`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FSBL_RADIUS] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

(* Lean: dot_nonneg *)
let FSBL_DOT_NONNEG = prove
 (`forall cB sB cL sL.
     &0 <= cB /\ &0 <= sB /\ sB <= cB /\ &0 <= cL /\ abs sL <= cL
     ==> &0 <= cB * cL + sB * sL`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_ABS_BOUNDS] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= (cB - sB) * cL`; `&0 <= sB * (cL + sL)`] THEN
  NLIN_TAC []);;

let FSBL_SP_TAC dx dy =
  MP_TAC(SPECL [`c:real`; `s:real`; dx; dy] FSAF_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  STRIP_TAC;;

(* Lean: left_point_of_lower_U *)
let FSBL_LEFT_POINT_OF_LOWER_U = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     &0 < c /\ abs s <= c /\ &1 < a /\
     lclosed c s u v a (&457 / &500) (&2) /\
     lclosed c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&33 / &20) (&33 / &20) /\
     c * (&19 / &25) + s * (&187 / &100) <= u
     ==> linside c s u v a (&13 / &10) (&12 / &5)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lclosed; linside; REAL_ABS_BOUNDS] THEN STRIP_TAC THEN
  FSBL_SP_TAC `&89 / &100` `--(&11 / &50)` THEN
  FSBL_SP_TAC `&27 / &50` `&53 / &100` THEN
  FSBL_SP_TAC `--(&7 / &20)` `&3 / &4` THEN
  SUBGOAL_THEN `--s * (&33 / &20) + c * (&33 / &20) <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FSBC_MISS_TAC [`&33 / &20`]; ALL_TAC] THEN
  FSBC_ARITH_TAC);;

(* Lean: right_point_of_upper_corner *)
let FSBL_RIGHT_POINT_OF_UPPER_CORNER = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     &0 < c /\ &0 <= s /\ s <= c /\ &1 < a /\
     lclosed c s u v a (&33 / &20) (&47 / &20) /\
     lclosed c s u v a (&8 / &5) (&3) /\
     u + a <= &2 * c + (&1543 / &500) * s /\
     v + a <= --s + (&1543 / &500) * c
     ==> linside c s u v a (&13 / &10) (&12 / &5)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lclosed; linside] THEN STRIP_TAC THEN
  FSBL_SP_TAC `&7 / &10` `&343 / &500` THEN
  FSBL_SP_TAC `--(&3 / &10)` `&343 / &500` THEN
  FSBC_ARITH_TAC);;

(* Lean: missing_below_V *)
let FSBL_MISSING_BELOW_V = prove
 (`forall cB sB uB vB aB cL sL uL vL aL.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     &0 < cB /\ &0 <= sB /\ sB <= cB /\
     &0 < cL /\ abs sL <= cL /\
     &1 < aB /\ &1 < aL /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     lclosed cB sB uB vB aB (&8 / &5) (&3) /\
     lclosed cL sL uL vL aL (&457 / &500) (&2) /\
     lclosed cL sL uL vL aL (&1) (&12 / &5) /\
     ~linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
     ~linside cL sL uL vL aL (&33 / &20) (&33 / &20) /\
     uB + aB <= &2 * cB + (&1543 / &500) * sB /\
     vB + aB <= --sB + (&1543 / &500) * cB /\
     ldisj cB sB uB vB aB cL sL uL vL aL
     ==> --sL * (&19 / &25) + cL * (&187 / &100) <= vL`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `cL * (&19 / &25) + sL * (&187 / &100) <= uL` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside cL sL uL vL aL (&19 / &25) (&187 / &100)` THEN
    REWRITE_TAC[linside] THEN
    UNDISCH_TAC `lclosed cL sL uL vL aL (&457 / &500) (&2)` THEN
    UNDISCH_TAC `lclosed cL sL uL vL aL (&1) (&12 / &5)` THEN
    REWRITE_TAC[lclosed] THEN
    UNDISCH_TAC `abs sL <= cL` THEN UNDISCH_TAC `&0 < cL` THEN
    UNDISCH_TAC `uL < cL * (&19 / &25) + sL * (&187 / &100)` THEN
    UNDISCH_TAC `vL < --sL * (&19 / &25) + cL * (&187 / &100)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `ldisj cB sB uB vB aB cL sL uL vL aL` THEN
  REWRITE_TAC[ldisj; NOT_FORALL_THM] THEN
  MAP_EVERY EXISTS_TAC [`&13 / &10`; `&12 / &5`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FSBL_RIGHT_POINT_OF_UPPER_CORNER THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FSBL_LEFT_POINT_OF_LOWER_U THEN ASM_REWRITE_TAC[]]);;

(* Lean: left_upper_bounds *)
let FSBL_LEFT_UPPER_BOUNDS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &0 < c /\
     lcont c s u v a /\
     lclosed c s u v a (&457 / &500) (&2) /\
     --s * (&19 / &25) + c * (&187 / &100) <= v
     ==> (&0 <= s ==> a * (&1 + s / c) + (&187 / &100) * s -
                      (&19 / &25) * s pow 2 / c <= u + a) /\
         (s <= &0 ==> a - (&457 / &500) * s pow 2 / c + &2 * s <= u + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN FSBC_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `c * (u + a) = lcx c s u v a + s * (v + a / &2) + a * c / &2`
    ASSUME_TAC THENL
   [REWRITE_TAC[lcx] THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lclosed]) THEN
  SUBGOAL_THEN `~(c = &0)` ASSUME_TAC THENL [FSBC_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [GSYM(MATCH_MP REAL_LE_RMUL_EQ (ASSUME `&0 < c`))] THENL
   [SUBGOAL_THEN `(a * (&1 + s / c) + (&187 / &100) * s - (&19 / &25) * s pow 2 / c) * c =
                  a * (c + s) + (&187 / &100) * s * c - (&19 / &25) * s pow 2`
      SUBST1_TAC THENL
     [UNDISCH_TAC `~(c = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`s * (--s * (&19 / &25) + c * (&187 / &100)) <= s * v`] THEN
    UNDISCH_TAC `a * (c + abs s) / &2 <= lcx c s u v a` THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= s ==> abs s = s`] THEN
    REWRITE_TAC[REAL_POW_2] THEN FSBC_ARITH_TAC;
    SUBGOAL_THEN `(a - (&457 / &500) * s pow 2 / c + &2 * s) * c =
                  a * c - (&457 / &500) * s pow 2 + &2 * s * c`
      SUBST1_TAC THENL
     [UNDISCH_TAC `~(c = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`s * (--s * (&457 / &500) + c * &2) <= s * v`] THEN
    UNDISCH_TAC `a * (c + abs s) / &2 <= lcx c s u v a` THEN
    ASM_SIMP_TAC[REAL_ARITH `s <= &0 ==> abs s = --s`] THEN
    REWRITE_TAC[REAL_POW_2] THEN FSBC_ARITH_TAC]);;

(* Lean: minimum_projection *)
let FSBL_MINIMUM_PROJECTION = prove
 (`forall cB sB uB vB aB cL sL.
     &0 <= cB * cL + sB * sL
     ==> cL * lcx cB sB uB vB aB + sL * lcy cB sB uB vB aB -
         tss_support_radius cB sB aB cL sL =
         (cB * cL + sB * sL) * uB +
         (cB * sL - sB * cL) * (vB + aB / &2) -
         aB / &2 * abs(cB * sL - sB * cL)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[tss_support_radius; lcx; lcy;
    REAL_ARITH `cL * cB + sL * sB = cB * cL + sB * sL`;
    REAL_ARITH `--cL * sB + sL * cB = cB * sL - sB * cL`] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  CONV_TAC REAL_RING);;

(* Lean: right_minimum_bounds *)
let FSBL_RIGHT_MINIMUM_BOUNDS = prove
 (`forall cB sB uB vB aB cL sL uL vL aL.
     cB * cB + sB * sB = &1 /\ cL * cL + sL * sL = &1 /\
     &0 <= cB * cL + sB * sL /\
     uB + aB <= &2 * cB + (&1543 / &500) * sB /\
     vB + aB <= --sB + (&1543 / &500) * cB /\
     -- &2 * sB + (&5 / &2) * cB <= vB /\
     C977CB_pairRadius cL sL aL cB sB aB <=
       cL * (lcx cB sB uB vB aB - lcx cL sL uL vL aL) +
       sL * (lcy cB sB uB vB aB - lcy cL sL uL vL aL)
     ==> (&0 <= cB * sL - sB * cL ==>
          uL + aL <= cL * (&1 + cB pow 2) + sL * (&1543 / &500 + cB * sB) -
                     aB * ((cB * cL + sB * sL) + (cB * sL - sB * cL))) /\
         (cB * sL - sB * cL <= &0 ==>
          uL + aL <= cL * (&2 + (&293 / &500) * cB * sB) +
                     sL * (&5 / &2 + (&293 / &500) * sB pow 2) -
                     aB * ((cB * cL + sB * sL) - (cB * sL - sB * cL)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    FSBL_LEFT_AXIS_CAP) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `cL:real`; `sL:real`]
    FSBL_MINIMUM_PROJECTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `D = cB * cL + sB * sL` THEN
  ABBREV_TAC `K = cB * sL - sB * cL` THEN
  SUBGOAL_THEN `D * (uB + aB) <= D * (&2 * cB + (&1543 / &500) * sB)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `K * (vB + aB) <= K * (--sB + (&1543 / &500) * cB)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `D * (&2 * cB + (&1543 / &500) * sB) + K * (--sB + (&1543 / &500) * cB) =
                  cL * (&1 + cB pow 2) + sL * (&1543 / &500 + cB * sB)` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["D"; "K"] THEN UNDISCH_TAC `cB * cB + sB * sB = &1` THEN
      CONV_TAC REAL_RING; ALL_TAC] THEN
    UNDISCH_TAC `uL + aL <= D * uB + K * (vB + aB / &2) - aB / &2 * abs K` THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN FSBC_ARITH_TAC;
    SUBGOAL_THEN `K * vB <= K * (-- &2 * sB + (&5 / &2) * cB)` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `forall k x y:real. (--k) * x <= (--k) * y ==> k * y <= k * x`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN FSBC_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `D * (&2 * cB + (&1543 / &500) * sB) + K * (-- &2 * sB + (&5 / &2) * cB) =
                  cL * (&2 + (&293 / &500) * cB * sB) +
                  sL * (&5 / &2 + (&293 / &500) * sB pow 2)` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["D"; "K"] THEN UNDISCH_TAC `cB * cB + sB * sB = &1` THEN
      CONV_TAC REAL_RING; ALL_TAC] THEN
    UNDISCH_TAC `uL + aL <= D * uB + K * (vB + aB / &2) - aB / &2 * abs K` THEN
    ASM_SIMP_TAC[REAL_ARITH `x <= &0 ==> abs x = --x`] THEN FSBC_ARITH_TAC]);;
