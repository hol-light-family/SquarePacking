(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallNegativeLeft.lean (Jatloe,            *)
(* N12-jatloe; namespace N12Compact.FullAuxWallNegativeLeft).                *)
(* Full-square support at the genuine left container wall in the            *)
(* positive-opposite/positive-upper sector, with the actual negative         *)
(* canonical frame of L (L.s = -r is sL = --r).  Normal is c977cc_normal;    *)
(* upper/lower are ABT_upper/ABT_lower; lower_pp: FAWTE_LOWER_PP;            *)
(* FullAuxWallSmallOffset.cosine: FAWSO_COSINE; FourSquareBLBridge.left_wall:*)
(* FSBL_LEFT_WALL; FullAuxWallSharpClearance.excess: FAWSC_EXCESS;           *)
(* FullAuxWallLeftResidual.no_opposite_v / negative_v_order / no_upper_v /   *)
(* K / Q: FAWLR_NO_OPPOSITE_V / FAWLR_NEGATIVE_V_ORDER / FAWLR_NO_UPPER_V /  *)
(* fawlr_k / fawlr_q; FullAuxWallPositiveUpperAngleSupport.sine:             *)
(* FAWPUAS_SINE; dot_le_one: C977CSB_DOT_LE_ONE; the axis split             *)
(* (faceSeparation_of_disjoint + separated + radius identities):            *)
(* ABT_FOUR_AXES.  The Lean local abbreviations (d, h, u, F, G) are written  *)
(* out.  The OpenSquare invariants are explicit hypotheses.                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/FullAuxWallTopEndpoint.ml";;
needs "n12/geometry/FullAuxWallLeftResidual.ml";;
needs "n12/geometry/FullAuxWallSmallOffset.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/FullAuxWallSharpClearance.ml";;
needs "n12/geometry/FullAuxWallPositiveUpperAngleSupport.ml";;

let FAWNL_LIN = NLIN_TAC ~deg2:false [];;

let FAWNL_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let FAWNL_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC THEN
   FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; FAWNL_LIN]; ALL_TAC];;

let FAWNL_IN_TAC t = STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t));;

let FAWNL_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE FAWNL_LIN);
                  DISCH_TAC];;

(* Lean: half_arc (private) *)
let FAWNL_HALF_ARC = prove
 (`forall l r. c977cc_normal l r ==> r / &2 <= l + r - &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FAWNL_NORMAL_TAC THEN
  FAWNL_PROD `&0 <= r * (&1 + l - &2 * r)` THEN
  SUBGOAL_THEN `(&1 + l) * (&2 * l + r - &2) = r * (&1 + l - &2 * r)` ASSUME_TAC THENL
  [UNDISCH_TAC `l pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FAWNL_PROD `&0 < (&1 + l) * (&2 - (&2 * l + r))` THEN FAWNL_LIN);;

(* upper support with both coefficients nonnegative *)
let FAWNL_UPPER_PP = prove
 (`forall c s u v a x y. &0 <= x * c + y * s /\ &0 <= --x * s + y * c
     ==> ABT_upper c s u v a x y = (x * c + y * s) * (u + a) + (--x * s + y * c) * (v + a)`,
  REPEAT STRIP_TAC THEN C981NP_FORM_TAC);;

(* lower support with a nonnegative first and nonpositive second coefficient *)
let FAWNL_LOWER_PN = prove
 (`forall c s u v a x y. &0 <= x * c + y * s /\ --x * s + y * c <= &0
     ==> ABT_lower c s u v a x y = (x * c + y * s) * u + (--x * s + y * c) * (v + a)`,
  REPEAT STRIP_TAC THEN C981NP_FORM_TAC);;

(* Lean: upper_support *)
let FAWNL_UPPER_SUPPORT = prove
 (`forall cL sL uL vL aL r X Y.
     cL * cL + sL * sL = &1 /\ &0 < aL /\
     sL = --r /\ c977cc_normal cL r /\ c977cc_normal X Y /\ &0 < Y /\
     lcont cL sL uL vL aL /\ linside cL sL uL vL aL (&457 / &500) (&2)
     ==> &2 * Y * cL + (&457 / &500) * Y * r + aL * (cL * X - r * Y) * (cL + r) <
         cL * ABT_upper cL sL uL vL aL X Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sL = --r`)) THEN
  FAWNL_NORMAL_TAC THEN
  FAWNL_PROD `&0 <= X * (cL - r)` THEN FAWNL_PROD `&0 <= r * (X - Y)` THEN
  FAWNL_PROD `&0 <= r * X` THEN FAWNL_PROD `&0 <= cL * Y` THEN
  SUBGOAL_THEN `&0 <= cL * X - r * Y /\ &0 <= r * X + cL * Y` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN FAWNL_LIN; ALL_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `--r`; `uL:real`; `vL:real`; `aL:real`; `X:real`; `Y:real`]
    FAWNL_UPPER_PP) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FAWNL_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `--r`; `uL:real`; `vL:real`; `aL:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN FAWNL_LIN; ALL_TAC] THEN
  REWRITE_TAC[lcx; REAL_ABS_NEG] THEN
  SUBGOAL_THEN `abs r = r` SUBST1_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= cL * uL + r * vL` ASSUME_TAC THENL [FAWNL_LIN; ALL_TAC] THEN
  FAWNL_PROD `&0 <= (cL * X - r * Y) * (cL * uL + r * vL)` THEN
  FAWNL_IN_TAC `linside cL (--r) uL vL aL (&457 / &500) (&2)` THEN
  FAWNL_PROD `&0 < Y * ((vL + aL) - (-- --r * &457 / &500 + cL * &2))` THEN
  SUBGOAL_THEN
   `cL * ABT_upper cL (--r) uL vL aL X Y =
    (cL * X - r * Y) * (cL * uL + r * vL) + Y * (vL + aL) + aL * (cL * X - r * Y) * (cL + r)`
   ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cL pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  FAWNL_LIN);;

(* Lean: no_central_u *)
let FAWNL_NO_CENTRAL_U = prove
 (`forall cL sL uL vL aL cD sD uD (vD:real) aD r.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     sL = --r /\ c977cc_normal cL r /\ c977cc_normal cD sD /\
     &1 < aL /\ aL = aD /\ lcont cL sL uL vL aL /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\
     &25 * sD <= &9 * cD /\ &1 / &20 < sD /\
     uD + aD - &2 * (cD + sD) <= &1 / &1000 /\
     ABT_upper cL sL uL vL aL cD sD <= uD
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aD`)) THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `r:real`;
                `cD:real`; `sD:real`] FAWNL_UPPER_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN FAWNL_LIN; DISCH_TAC] THEN
  FAWNL_USE FAWSO_COSINE [`cD:real`; `sD:real`] THEN
  FAWNL_NORMAL_TAC THEN
  FAWNL_PROD `&0 <= (cL - r) * sD` THEN
  FAWNL_PROD `&0 <= cL * (cD - sD - &29 / &50)` THEN
  SUBGOAL_THEN `&2 / &5 <= cL * cD - r * sD` ASSUME_TAC THENL [FAWNL_LIN; ALL_TAC] THEN
  FAWNL_PROD `&0 <= cL * (uD - ABT_upper cL sL uL vL aL cD sD)` THEN
  FAWNL_PROD `&0 <= (cL * cD - r * sD) * (cL + r)` THEN
  FAWNL_PROD `&0 < (aL - &1) * (cL + (cL * cD - r * sD) * (cL + r))` THEN
  SUBGOAL_THEN
   `cL * (&1 - cD - (uD + aL - &2 * (cD + sD))) + (cL * cD - r * sD) * (cL + r - &1) -
    (&43 / &500) * sD * r < &0` ASSUME_TAC THENL [FAWNL_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `sD pow 2 / &2 <= &1 - cD` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `&1 - cD`]; ALL_TAC] THEN
  FAWNL_PROD `&0 < (sD - &1 / &20) * (sD + &1 / &20)` THEN
  SUBGOAL_THEN `&0 < &1 - cD - (uD + aL - &2 * (cD + sD))` ASSUME_TAC THENL
  [FAWNL_LIN; ALL_TAC] THEN
  FAWNL_PROD `&0 < cL * (&1 - cD - (uD + aL - &2 * (cD + sD)))` THEN
  MP_TAC(SPECL [`cL:real`; `r:real`] FAWNL_HALF_ARC) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FAWNL_PROD `&0 <= (cL * cD - r * sD) * ((cL + r - &1) - r / &2)` THEN
  FAWNL_PROD `&0 <= r * ((cL * cD - r * sD) / &2 - (&43 / &500) * sD)` THEN
  FAWNL_LIN);;

(* Lean: no_left_v *)
let FAWNL_NO_LEFT_V = prove
 (`forall cL sL uL vL aL cD sD uD vD aD r.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     sL = --r /\ c977cc_normal cL r /\ c977cc_normal cD sD /\ &1 < aD /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\
     linside cD sD uD vD aD (&2) (&3 / &2) /\
     uD + aD - &2 * (cD + sD) <= &1 / &112 /\
     vL + aL <= ABT_lower cD sD uD vD aD r cL
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sL = --r`)) THEN
  FAWNL_NORMAL_TAC THEN
  FAWNL_PROD `&0 <= r * cD` THEN FAWNL_PROD `&0 <= cL * sD` THEN
  FAWNL_PROD `&0 <= cD * (cL - r)` THEN FAWNL_PROD `&0 <= r * (cD - sD)` THEN
  SUBGOAL_THEN `&0 <= r * cD + cL * sD /\ &0 <= cL * cD - r * sD` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN FAWNL_LIN; ALL_TAC] THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`; `r:real`; `cL:real`]
    FAWTE_LOWER_PP) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FAWNL_LIN; DISCH_TAC] THEN
  FAWNL_IN_TAC `linside cD sD uD vD aD (&2) (&3 / &2)` THEN
  FAWNL_IN_TAC `linside cL (--r) uL vL aL (&457 / &500) (&2)` THEN
  FAWNL_PROD `&0 <= (r * cD + cL * sD) * (&2 * (cD + sD) + &1 / &112 - &1 - uD)` THEN
  FAWNL_PROD `&0 <= (cL * cD - r * sD) * ((--sD * &2 + cD * (&3 / &2)) - vD)` THEN
  FAWNL_PROD `&0 <= cD * sD` THEN
  SUBGOAL_THEN `&0 <= &543 / &500 - cD + (&1 / &2) * cD * sD + cD / &112` ASSUME_TAC THENL
  [FAWNL_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `sD <= &5 / &7` ASSUME_TAC THENL [FAWNL_LIN; ALL_TAC] THEN
  FAWNL_PROD `&0 <= (cD + sD - &1) * (&1 - sD / &2 - &1 / &112)` THEN
  SUBGOAL_THEN
   `(&543 / &500 - cD + (&1 / &2) * cD * sD + cD / &112) +
    (--(&1 / &2) - sD + (&1 / &2) * sD pow 2 + sD / &112) < &0` ASSUME_TAC THENL
  [FAWNL_LIN; ALL_TAC] THEN
  FAWNL_PROD `&0 <= (cL - r) * (&543 / &500 - cD + (&1 / &2) * cD * sD + cD / &112)` THEN
  SUBGOAL_THEN
   `cL * ((&543 / &500 - cD + (&1 / &2) * cD * sD + cD / &112) +
          (--(&1 / &2) - sD + (&1 / &2) * sD pow 2 + sD / &112)) < &0` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_ARITH `x * y < &0 <=> &0 < x * --y`] THEN
   MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN FAWNL_LIN; ALL_TAC] THEN
  SUBGOAL_THEN
   `(r * cD + cL * sD) * (&2 * (cD + sD) + &1 / &112 - &1) +
    (cL * cD - r * sD) * ((&3 / &2) * cD - &2 * sD) - ((&457 / &500) * r + &2 * cL) =
    r * (&543 / &500 - cD + (&1 / &2) * cD * sD + cD / &112) +
    cL * (--(&1 / &2) - sD + (&1 / &2) * sD pow 2 + sD / &112)` ASSUME_TAC THENL
  [UNDISCH_TAC `cD pow 2 + sD pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  FAWNL_LIN);;

(* Lean: cosine97 (private) *)
let FAWNL_COSINE97 = prove
 (`forall C S. c977cc_normal C S /\ S <= &11 / &50 ==> &97 / &100 <= C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWNL_NORMAL_TAC THEN
  FAWNL_PROD `&0 <= (&11 / &50 - S) * (&11 / &50 + S)` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FAWNL_PROD `&0 < (&97 / &100 - C) * (&97 / &100 + C)` THEN FAWNL_LIN);;

(* Lean: defect_bound (private) *)
let FAWNL_DEFECT_BOUND = prove
 (`forall C S. c977cc_normal C S /\ S <= &11 / &50 /\ &1 / &20 < S
         ==> (&1 - C) * (&1 - S) - (&2 / &5) * S pow 2 < &1 / &1000`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FAWNL_USE FAWNL_COSINE97 [`C:real`; `S:real`] THEN FAWNL_NORMAL_TAC THEN
  FAWNL_PROD `&0 < S * S` THEN
  SUBGOAL_THEN `C < &1` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`; `&1 / &1000`] FAWSC_EXCESS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN FAWNL_LIN; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Lean: tilt_of_left_u *)
let FAWNL_TILT_OF_LEFT_U = prove
 (`forall cL sL uL vL aL cD sD uD vD aD r.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     sL = --r /\ c977cc_normal cL r /\ c977cc_normal cD sD /\
     &1 < aD /\ aL = aD /\ sD <= &11 / &50 /\ &1 / &20 < sD /\
     linside cD sD uD vD aD (&2) (&2) /\ linside cL sL uL vL aL (&1) (&8 / &5) /\
     cD - (&8 / &5) * sD <= vD /\
     uD + aD - &2 * (cD + sD) <= &1 / &1000 /\
     uL + aL <= ABT_lower cD sD uD vD aD cL (--r)
     ==> r < &1 / &50`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sL = --r`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aL:real = aD`)) THEN
  FAWNL_USE FAWNL_DEFECT_BOUND [`cD:real`; `sD:real`] THEN
  FAWNL_USE FAWNL_COSINE97 [`cD:real`; `sD:real`] THEN
  MP_TAC(SPECL [`cL:real`; `r:real`; `cD:real`; `sD:real`] C977CSB_DOT_LE_ONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FAWNL_NORMAL_TAC THEN
  FAWNL_PROD `&0 <= cD * (cL - r)` THEN FAWNL_PROD `&0 <= r * (cD - sD)` THEN
  FAWNL_PROD `&0 <= r * cD` THEN FAWNL_PROD `&0 <= cL * sD` THEN FAWNL_PROD `&0 <= r * sD` THEN
  SUBGOAL_THEN `&0 <= cL * cD - r * sD /\ &0 <= r * cD + cL * sD /\ cL * cD - r * sD <= &1`
    STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN FAWNL_LIN; ALL_TAC] THEN
  FAWNL_IN_TAC `linside cD sD uD vD aD (&2) (&2)` THEN
  FAWNL_IN_TAC `linside cL (--r) uL vL aD (&1) (&8 / &5)` THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`; `cL:real`; `--r`]
    FAWNL_LOWER_PN) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FAWNL_LIN; DISCH_TAC] THEN
  FAWNL_PROD `&0 <= (r * cD + cL * sD) * (vD - (cD - (&8 / &5) * sD))` THEN
  FAWNL_PROD `&0 <= (aD - &1) * ((cL * cD - r * sD) + (r * cD + cL * sD))` THEN
  SUBGOAL_THEN
   `(cL * cD - r * sD) * (&2 * (cD + sD)) - (r * cD + cL * sD) * (cD - (&8 / &5) * sD) -
    ((cL * cD - r * sD) + (r * cD + cL * sD)) - (cL - (&8 / &5) * r) =
    cL * ((&1 - cD) * (&1 - sD) - (&2 / &5) * sD pow 2) +
    r * (&3 / &5 - sD pow 2 - (&2 / &5) * cD * sD + sD - cD)` ASSUME_TAC THENL
  [UNDISCH_TAC `cD pow 2 + sD pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < cL * ((&1 - cD) * (&1 - sD) - (&2 / &5) * sD pow 2) +
         r * (&3 / &5 - sD pow 2 - (&2 / &5) * cD * sD + sD - cD) +
         (cL * cD - r * sD) * (uD + aD - &2 * (cD + sD))` ASSUME_TAC THENL
  [FAWNL_LIN; ALL_TAC] THEN
  FAWNL_PROD `&0 <= cD * sD` THEN
  SUBGOAL_THEN `&3 / &5 - sD pow 2 - (&2 / &5) * cD * sD + sD - cD <= --(&3 / &20)`
    ASSUME_TAC THENL [NLIN_TAC ~deg2:false [SQ_NONNEG `sD:real`]; ALL_TAC] THEN
  FAWNL_PROD `&0 <= cL * (&1 / &1000 - ((&1 - cD) * (&1 - sD) - (&2 / &5) * sD pow 2))` THEN
  FAWNL_PROD `&0 <= r * (--(&3 / &20) - (&3 / &5 - sD pow 2 - (&2 / &5) * cD * sD + sD - cD))` THEN
  SUBGOAL_THEN `&0 <= uD + aD - &2 * (cD + sD)` ASSUME_TAC THENL [FAWNL_LIN; ALL_TAC] THEN
  FAWNL_PROD `&0 <= (&1 - (cL * cD - r * sD)) * (uD + aD - &2 * (cD + sD))` THEN
  FAWNL_LIN);;

let FAWNL_QL = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`];;
let FAWNL_QD = [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`];;
let FAWNL_QB = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`];;

(* Lean: small_tilt *)
let FAWNL_SMALL_TILT = prove
 (`forall cL sL uL vL aL cD sD uD vD aD r.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     sL = --r /\ c977cc_normal cL r /\ c977cc_normal cD sD /\
     &1 < aD /\ aL = aD /\ lcont cL sL uL vL aL /\
     sD <= &11 / &50 /\ &1 / &20 < sD /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\ linside cL sL uL vL aL (&1) (&8 / &5) /\
     linside cD sD uD vD aD (&2) (&2) /\ linside cD sD uD vD aD (&2) (&3 / &2) /\
     linside cD sD uD vD aD (&6 / &5) (&19 / &10) /\
     cD - (&8 / &5) * sD <= vD /\
     uD + aD - &2 * (cD + sD) <= &1 / &1000 /\
     ldisj cL sL uL vL aL cD sD uD vD aD
     ==> r < &1 / &50`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FAWNL_USE FAWNL_COSINE97 [`cD:real`; `sD:real`] THEN
  MP_TAC(SPECL (FAWNL_QL @ FAWNL_QD) FAWLR_NO_OPPOSITE_V) THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT(ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  REWRITE_TAC[TAUT `(p ==> false) <=> ~p`; DE_MORGAN_THM; REAL_NOT_LE] THEN STRIP_TAC THEN
  MP_TAC(SPECL (FAWNL_QL @ FAWNL_QD @ [`r:real`]) FAWNL_NO_CENTRAL_U) THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT(ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC ORELSE FAWNL_LIN; ALL_TAC]) THEN
  REWRITE_TAC[TAUT `(p ==> false) <=> ~p`; REAL_NOT_LE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sL = --r`)) THEN
  MP_TAC(SPECL ([`cL:real`; `--r`; `uL:real`; `vL:real`; `aL:real`] @ FAWNL_QD @ [`r:real`]) FAWNL_NO_LEFT_V) THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT(ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC ORELSE FAWNL_LIN; ALL_TAC]) THEN
  REWRITE_TAC[TAUT `(p ==> false) <=> ~p`; REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL ([`cL:real`; `--r`; `uL:real`; `vL:real`; `aL:real`] @ FAWNL_QD @ [`r:real`]) FAWNL_TILT_OF_LEFT_U) THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT(ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC ORELSE FAWNL_LIN; ALL_TAC]) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[TAUT `(p ==> q) <=> ~p \/ q`; REAL_NOT_LE]) THEN
  FAWNL_NORMAL_TAC THEN
  let qL = [`cL:real`; `--r`; `uL:real`; `vL:real`; `aL:real`] in
  let mk = (`&457 / &500`,`&2`) and lo = (`&1`,`&8 / &5`) and ce = (`&2`,`&2`) in
  let d1 = (`cL:real`,`--r`) and d2 = (`-- --r`,`cL:real`) and d3 = (`cD:real`,`sD:real`) in
  MAP_EVERY (fun (sq,p,d) -> FAWLR_SB_TAC sq p d)
   [FAWNL_QD,ce,d1; qL,mk,d1; FAWNL_QD,ce,d2; qL,lo,d2; FAWNL_QD,ce,d3; qL,mk,d3] THEN
  MP_TAC(SPECL (qL @ FAWNL_QD) ABT_FOUR_AXES) THEN ANTS_TAC THENL [FAWLR_ANTS_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL qL ABT_OWNU) THEN ANTS_TAC THENL [FAWLR_ANTS_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL qL ABT_OWNV) THEN ANTS_TAC THENL [FAWLR_ANTS_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL FAWNL_QD ABT_OWNU) THEN ANTS_TAC THENL [FAWLR_ANTS_TAC; STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NEG_NEG]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl))) THEN
  FAWNL_LIN);;

(* Lean: no_upper_left_v (private) *)
let FAWNL_NO_UPPER_LEFT_V = prove
 (`forall cL sL uL vL aL cB sB uB vB aB r.
     sL = --r /\ c977cc_normal cL r /\ c977cc_normal cB sB /\
     &1 < aB /\ r < &1 / &50 /\ &3 / &10 < sB /\
     uB + aB <= (&8 / &5) * cB + &3 * sB /\ vB + aB <= &3 * cB - sB /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\
     vL + aL <= ABT_lower cB sB uB vB aB r cL
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (FAWNL_QL @ FAWNL_QB @ [`r:real`]) FAWLR_NEGATIVE_V_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FAWNL_NORMAL_TAC THEN
  FAWNL_PROD `&0 <= (cB + sB - &1) * (&3 / &2 - (cB + sB))` THEN
  SUBGOAL_THEN `(&4 / &5) * cB * sB <= cB + sB - &1` ASSUME_TAC THENL [FAWNL_LIN; ALL_TAC] THEN
  FAWNL_PROD `&0 <= sB * (cB - &7 / &10)` THEN
  SUBGOAL_THEN `&1 / &25 <= fawlr_k cB sB` ASSUME_TAC THENL
  [REWRITE_TAC[fawlr_k] THEN FAWNL_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `fawlr_q cB sB <= &343 / &500` ASSUME_TAC THENL
  [REWRITE_TAC[fawlr_q] THEN NLIN_TAC [SQ_NONNEG `sB:real`]; ALL_TAC] THEN
  FAWNL_PROD `&0 <= cL * (fawlr_k cB sB - &1 / &25)` THEN
  FAWNL_PROD `&0 <= r * (&343 / &500 - fawlr_q cB sB)` THEN
  FAWNL_LIN);;

(* Lean: upper_axis *)
let FAWNL_UPPER_AXIS = prove
 (`forall cL sL uL vL aL cB sB uB vB aB r.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     sL = --r /\ c977cc_normal cL r /\ c977cc_normal cB sB /\
     &1 < aB /\ aL = aB /\ r < &1 / &50 /\ &3 / &10 < sB /\
     uB + aB <= (&8 / &5) * cB + &3 * sB /\ vB + aB <= &3 * cB - sB /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\ linside cL sL uL vL aL (&1) (&8 / &5) /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\ linside cB sB uB vB aB (&1) (&12 / &5) /\
     ldisj cL sL uL vL aL cB sB uB vB aB
     ==> ABT_upper cL sL uL vL aL cB sB <= uB`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(SPECL (FAWNL_QL @ FAWNL_QB) FAWLR_NO_UPPER_V) THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT(ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  REWRITE_TAC[TAUT `(p ==> false) <=> ~p`; DE_MORGAN_THM; REAL_NOT_LE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sL = --r`)) THEN
  MP_TAC(SPECL ([`cL:real`; `--r`; `uL:real`; `vL:real`; `aL:real`] @ FAWNL_QB @ [`r:real`]) FAWNL_NO_UPPER_LEFT_V) THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT(ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC ORELSE FAWNL_LIN; ALL_TAC]) THEN
  REWRITE_TAC[TAUT `(p ==> false) <=> ~p`; REAL_NOT_LE] THEN DISCH_TAC THEN
  FAWNL_NORMAL_TAC THEN
  let qL = [`cL:real`; `--r`; `uL:real`; `vL:real`; `aL:real`] in
  let mk = (`&457 / &500`,`&2`) and lo = (`&1`,`&8 / &5`) and hi = (`&1`,`&12 / &5`)
  and bm = (`&33 / &20`,`&47 / &20`) in
  let d1 = (`cL:real`,`--r`) and d2 = (`-- --r`,`cL:real`) and d3 = (`cB:real`,`sB:real`) in
  MAP_EVERY (fun (sq,p,d) -> FAWLR_SB_TAC sq p d)
   [qL,lo,d1; FAWNL_QB,hi,d1; FAWNL_QB,bm,d1; qL,mk,d1;
    qL,lo,d2; FAWNL_QB,hi,d2; FAWNL_QB,hi,d3; qL,mk,d3] THEN
  MP_TAC(SPECL (qL @ FAWNL_QB) ABT_FOUR_AXES) THEN ANTS_TAC THENL [FAWLR_ANTS_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL qL ABT_OWNV) THEN ANTS_TAC THENL [FAWLR_ANTS_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL FAWNL_QB ABT_OWNU) THEN ANTS_TAC THENL [FAWLR_ANTS_TAC; STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NEG_NEG]) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl))) THEN
  FAWNL_LIN);;

(* Lean: upper_steep *)
let FAWNL_UPPER_STEEP = prove
 (`forall cL sL uL vL aL cB sB uB (vB:real) aB r.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     sL = --r /\ c977cc_normal cL r /\ c977cc_normal cB sB /\
     &1 < aL /\ aL = aB /\ r < &1 / &50 /\ &3 / &10 < sB /\
     lcont cL sL uL vL aL /\ linside cL sL uL vL aL (&457 / &500) (&2) /\
     uB + aB <= (&8 / &5) * cB + &3 * sB /\
     ABT_upper cL sL uL vL aL cB sB <= uB
     ==> &23 / &50 < sB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aB`)) THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `r:real`;
                `cB:real`; `sB:real`] FAWNL_UPPER_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN FAWNL_LIN; DISCH_TAC] THEN
  FAWNL_NORMAL_TAC THEN
  FAWNL_PROD `&0 <= cB * (cL - r)` THEN FAWNL_PROD `&0 <= r * (cB - sB)` THEN
  SUBGOAL_THEN `&0 <= cL * cB - r * sB` ASSUME_TAC THENL [FAWNL_LIN; ALL_TAC] THEN
  FAWNL_PROD `&0 <= cL * (uB - ABT_upper cL sL uL vL aL cB sB)` THEN
  FAWNL_PROD `&0 <= cL * ((&8 / &5) * cB + &3 * sB - (uB + aL))` THEN
  FAWNL_PROD `&0 <= (cL * cB - r * sB) * (cL + r)` THEN
  FAWNL_PROD `&0 < (aL - &1) * (cL + (cL * cB - r * sB) * (cL + r))` THEN
  SUBGOAL_THEN
   `cL * (&1 - (&3 / &5) * cB - sB) + (cL * cB - r * sB) * (cL + r - &1) -
    (&43 / &500) * sB * r < &0` ASSUME_TAC THENL [FAWNL_LIN; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `cB <= &1 - sB pow 2 / &2` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `&1 - cB`]; ALL_TAC] THEN
  FAWNL_PROD `&0 <= (&23 / &50 - sB) * (&1 - (&3 / &10) * (&23 / &50 + sB))` THEN
  SUBGOAL_THEN `&3 / &1000 <= &1 - (&3 / &5) * cB - sB` ASSUME_TAC THENL
  [FAWNL_LIN; ALL_TAC] THEN
  FAWNL_PROD `&0 <= cL * ((&1 - (&3 / &5) * cB - sB) - &3 / &1000)` THEN
  FAWNL_PROD `&0 <= (cL * cB - r * sB) * (cL + r - &1)` THEN
  FAWNL_PROD `&0 <= r * (&23 / &50 - sB)` THEN
  SUBGOAL_THEN `sB * r <= &23 / &2500` ASSUME_TAC THENL [FAWNL_LIN; ALL_TAC] THEN
  FAWNL_LIN);;

(* Lean: impossible *)
let FAWNL_IMPOSSIBLE = prove
 (`forall cL sL uL vL aL cD sD uD vD aD cB sB uB vB aB r.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     sL = --r /\ c977cc_normal cL r /\ c977cc_normal cD sD /\ c977cc_normal cB sB /\
     &1 < aD /\ aL = aD /\ aD = aB /\ lcont cL sL uL vL aL /\
     sD <= &11 / &50 /\ &1 / &20 < sD /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\ linside cL sL uL vL aL (&1) (&8 / &5) /\
     linside cD sD uD vD aD (&2) (&2) /\ linside cD sD uD vD aD (&2) (&3 / &2) /\
     linside cD sD uD vD aD (&6 / &5) (&19 / &10) /\
     cD - (&8 / &5) * sD <= vD /\
     uD + aD - &2 * (cD + sD) <= &1 / &1000 /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\ linside cB sB uB vB aB (&1) (&12 / &5) /\
     uB + aB <= (&8 / &5) * cB + &3 * sB /\ vB + aB <= &3 * cB - sB /\
     &3 / &10 < sB /\ sD * cB <= cD * sB /\
     (vD + aD <= ABT_lower cB sB uB vB aB (--sD) cD \/
      ABT_upper cD sD uD vD aD (--sB) cB <= vB) /\
     ldisj cL sL uL vL aL cD sD uD vD aD /\ ldisj cL sL uL vL aL cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(SPECL (FAWNL_QL @ FAWNL_QD @ [`r:real`]) FAWNL_SMALL_TILT) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `aL:real = aB /\ &1 < aB /\ &1 < aL` STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL (FAWNL_QL @ FAWNL_QB @ [`r:real`]) FAWNL_UPPER_AXIS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL (FAWNL_QL @ FAWNL_QB @ [`r:real`]) FAWNL_UPPER_STEEP) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL (FAWNL_QD @ FAWNL_QB) FAWPUAS_SINE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  FAWNL_LIN);;
