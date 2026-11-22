(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveWallUpperUPositiveLeft.lean (Jatloe,     *)
(* N12-jatloe; namespace N12Compact.PositiveWallUpperUPositiveLeft).         *)
(* The full positive-left-singleton sector of the positive-wall upper-U      *)
(* escape.  Normal is c977cc_normal; upper/lower are ABT_upper/ABT_lower;    *)
(* O.s = -t is written sO = --t.                                             *)
(* FourSquareBLBridge.left_wall: FSBL_LEFT_WALL;                             *)
(* CornerSingletonPair.alternatives/Directed: CSP_ALTERNATIVES/CSP_directed; *)
(* LeftSingletonWallSeparation.alternatives: LSWS_ALTERNATIVES.              *)
(* The OpenSquare invariants are explicit hypotheses.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/FullAuxWallPositiveOpposite.ml";;
needs "n12/geometry/PositiveCornerSmallBottom.ml";;
needs "n12/geometry/CornerSingletonPair.ml";;
needs "n12/geometry/LeftSingletonWallSeparation.ml";;

let PWUUPL_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PWUUPL_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let PWUUPL_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PWUUPL_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC;
           REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC];
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

let PWUUPL_POS_OF_MUL = prove
 (`forall k y. &0 <= k /\ &0 < k * y ==> &0 < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: left_wall (private) *)
let PWUUPL_LEFT_WALL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ c977cc_normal c s /\ lcont c s u v a
     ==> &0 <= c * u - s * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] FSBL_LEFT_WALL) THEN
  PWUUPL_NORMAL_TAC THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lcx] THEN
  SUBGOAL_THEN `abs s = s` SUBST1_TAC THENL
  [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: corner (private) *)
let PWUUPL_CORNER = prove
 (`forall c s u v a p q. c * c + s * s = &1 /\ u <= p /\ p <= u + a /\ v <= q /\ q <= v + a
     ==> lclosed c s u v a (c * p - s * q) (s * p + c * q)`,
  ACCEPT_TAC FAWPO_BANDS_CLOSED);;

(* Lean: half_defect (private) *)
let PWUUPL_HALF_DEFECT = prove
 (`forall l r. c977cc_normal l r ==> &2 * (&1 - l) <= r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN PWUUPL_NORMAL_TAC THEN
  PWUUPL_PROD_TAC `&1 - l` `&5 * l - &3` THEN NLIN_TAC []);;

(* Lean: bottom_cosine (private) *)
let PWUUPL_BOTTOM_COSINE = prove
 (`forall c t. c977cc_normal c t /\ t <= &1 / &5 ==> &9 / &10 <= c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PWUUPL_NORMAL_TAC THEN
  PWUUPL_PROD_TAC `t:real` `&1 / &5 - t` THEN
  NLIN_TAC [SQ_NONNEG `c - &9 / &10`]);;

(* Lean: relative_positive (private) *)
let PWUUPL_RELATIVE_POSITIVE = prove
 (`forall c t l r. c977cc_normal c t /\ c977cc_normal l r /\ t <= &1 / &5
     ==> &0 < c * l - t * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PWUUPL_NORMAL_TAC THEN
  PWUUPL_PRODLT_TAC `c - t` `l:real` THEN PWUUPL_PROD_TAC `t:real` `l - r` THEN
  NLIN_TAC ~deg2:false []);;

let PWUUPL_UPPER_SIGNS = prove
 (`forall c s u v a nx ny k h.
     nx * c + ny * s = k /\ --nx * s + ny * c = h
     ==> (&0 <= k /\ &0 <= h ==> ABT_upper c s u v a nx ny = k * (u + a) + h * (v + a)) /\
         (&0 <= k /\ h <= &0 ==> ABT_upper c s u v a nx ny = k * (u + a) + h * v) /\
         (k <= &0 /\ &0 <= h ==> ABT_upper c s u v a nx ny = k * u + h * (v + a)) /\
         (k <= &0 /\ h <= &0 ==> ABT_upper c s u v a nx ny = k * u + h * v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `forall c s u v a nx ny.
     ABT_upper c s u v a nx ny =
     (nx * c + ny * s) * u + (--nx * s + ny * c) * v +
     a / &2 * ((nx * c + ny * s) + abs(nx * c + ny * s)) +
     a / &2 * ((--nx * s + ny * c) + abs(--nx * s + ny * c))` (fun th -> REWRITE_TAC[th]) THENL
  [REWRITE_TAC[ABT_upper; tss_support_radius; lcx; lcy] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_ARITH `x <= &0 ==> abs x = --x`] THEN
  REAL_ARITH_TAC);;

let PWUUPL_UPPER_TAC sq nx ny k h n =
  MP_TAC(SPECL (sq @ [nx; ny; k; h]) PWUUPL_UPPER_SIGNS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o el n o CONJUNCTS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

(* Lean: not_left_axis *)
let PWUUPL_NOT_LEFT_AXIS = prove
 (`forall cO sO uO vO aO cL sL uL vL aL t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     sO = --t /\ c977cc_normal cO t /\ c977cc_normal cL sL /\ t <= &1 / &5 /\
     &1 < aO /\ t * (uO + aO) <= cO * vO /\
     uO + aO <= &2 * cO - (&457 / &500) * t /\
     linside cL sL uL vL aL (&1) (&1) /\
     ABT_upper cO sO uO vO aO (--sL) cL <= vL
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sO = --t`)) THEN
  PWUUPL_USE PWUUPL_RELATIVE_POSITIVE [`cO:real`; `t:real`; `cL:real`; `sL:real`] THEN
  PWUUPL_NORMAL_TAC THEN
  PWUUPL_PROD_TAC `sL:real` `cO:real` THEN PWUUPL_PROD_TAC `cL:real` `t:real` THEN
  SUBGOAL_THEN `&0 <= sL * cO + cL * t /\ &0 <= cL * cO - sL * t` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  PWUUPL_UPPER_TAC [`cO:real`; `--t`; `uO:real`; `vO:real`; `aO:real`] `--sL` `cL:real`
    `--(sL * cO + cL * t)` `cL * cO - sL * t` 2 THEN
  PWUUPL_PROD_TAC `cL * cO - sL * t` `cO * vO - t * (uO + aO)` THEN
  PWUUPL_PROD_TAC `sL:real` `&2 * cO - (&457 / &500) * t - uO - aO` THEN
  PWUUPL_PROD_TAC `cL * cO - sL * t` `cO + t` THEN
  SUBGOAL_THEN `&0 < sL + (cL * cO - sL * t) * (cO + t)` ASSUME_TAC THENL
  [PWUUPL_PRODLT_TAC `cL * cO - sL * t` `cO + t` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  PWUUPL_PRODLT_TAC `aO - &1` `sL + (cL * cO - sL * t) * (cO + t)` THEN
  PWUUPL_PROD_TAC `cO:real` `cL - sL` THEN
  PWUUPL_PROD_TAC `cO * (cL - sL)` `cO + t - &1` THEN
  PWUUPL_PROD_TAC `t:real` `&1 / &5 - t` THEN
  SUBGOAL_THEN `&0 <= (&457 / &500) * t - &2 * cO * (&1 - cO)` ASSUME_TAC THENL
  [NLIN_TAC []; ALL_TAC] THEN
  PWUUPL_PROD_TAC `sL:real` `(&457 / &500) * t - &2 * cO * (&1 - cO)` THEN
  SUBGOAL_THEN
   `cO * ((--(sL * cO + cL * t) * uO + (cL * cO - sL * t) * (vO + aO)) - (cL - sL)) =
    (cL * cO - sL * t) * (cO * vO - t * (uO + aO)) +
    sL * (&2 * cO - (&457 / &500) * t - uO - aO) +
    (aO - &1) * (sL + (cL * cO - sL * t) * (cO + t)) +
    cO * (cL - sL) * (cO + t - &1) +
    sL * ((&457 / &500) * t - &2 * cO * (&1 - cO))` ASSUME_TAC THENL
  [UNDISCH_TAC `cO pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `cL - sL < --(sL * cO + cL * t) * uO + (cL * cO - sL * t) * (vO + aO)`
    ASSUME_TAC THENL
  [ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN MATCH_MP_TAC PWUUPL_POS_OF_MUL THEN
   EXISTS_TAC `cO:real` THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  MP_TAC(ASSUME `linside cL sL uL vL aL (&1) (&1)`) THEN REWRITE_TAC[linside] THEN
  RASM_ARITH_TAC);;

(* Lean: left_upper_face *)
let PWUUPL_LEFT_UPPER_FACE = prove
 (`forall cO (sO:real) uO (vO:real) aO cL sL uL vL aL t.
     cL * cL + sL * sL = &1 /\ &0 < aL /\
     c977cc_normal cO t /\ c977cc_normal cL sL /\ t <= &1 / &5 /\
     aO = aL /\ &1 < aL /\ lcont cL sL uL vL aL /\
     uO + aO <= &2 * cO - (&457 / &500) * t /\
     ABT_upper cL sL uL vL aL cO (--t) <= uO
     ==> (&957 / &500) * cL < vL + aL`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aL`)) THEN
  PWUUPL_USE PWUUPL_BOTTOM_COSINE [`cO:real`; `t:real`] THEN
  PWUUPL_USE PWUUPL_HALF_DEFECT [`cL:real`; `sL:real`] THEN
  PWUUPL_USE PWUUPL_RELATIVE_POSITIVE [`cO:real`; `t:real`; `cL:real`; `sL:real`] THEN
  PWUUPL_USE PWUUPL_LEFT_WALL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] THEN
  PWUUPL_NORMAL_TAC THEN
  PWUUPL_USE PWUUPL_CORNER [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
    `uL + aL:real`; `vL:real`] THEN
  PWUUPL_USE ABT_CLOSED_BOUNDS [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
    `cL * (uL + aL) - sL * vL`; `sL * (uL + aL) + cL * vL`; `cO:real`; `--t`] THEN
  SUBGOAL_THEN `cO * (cL * (uL + aL) - sL * vL) - t * (sL * (uL + aL) + cL * vL) <= uO`
    ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PWUUPL_PROD_TAC `cO * cL - t * sL` `cL * uL - sL * (vL + aL)` THEN
  PWUUPL_PROD_TAC `cL:real`
    `uO - (cO * (cL * (uL + aL) - sL * vL) - t * (sL * (uL + aL) + cL * vL))` THEN
  PWUUPL_PROD_TAC `cL:real` `&2 * cO - (&457 / &500) * t - uO - aL` THEN
  PWUUPL_PROD_TAC `cO * cL - t * sL` `cL + sL` THEN
  PWUUPL_PRODLT_TAC `aL - &1` `(cO * cL - t * sL) * (cL + sL) + t + cL` THEN
  PWUUPL_PROD_TAC `cO - &9 / &10` `cL:real` THEN
  PWUUPL_PROD_TAC `t:real` `&10 / &7 - (cL + sL)` THEN
  SUBGOAL_THEN `&0 <= cO * cL / &2 - t * (cL + sL)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PWUUPL_PROD_TAC `cO:real` `cL:real` THEN
  PWUUPL_PROD_TAC `cO * cL` `cL + sL - &1 - sL / &2` THEN
  PWUUPL_PROD_TAC `cL:real` `&1 - cO` THEN
  PWUUPL_PROD_TAC `t:real` `&1 - cL` THEN
  PWUUPL_PROD_TAC `sL:real` `cO * cL / &2 - t * (cL + sL)` THEN
  SUBGOAL_THEN
   `&0 <= (cO * cL - t * sL) * (cL + sL) + t + cL - &2 * cO * cL - cL * t`
   ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN
   `t * (vL + aL - (&957 / &500) * cL) =
    (cO * cL - t * sL) * (cL * uL - sL * (vL + aL)) +
    cL * (uO - (cO * (cL * (uL + aL) - sL * vL) - t * (sL * (uL + aL) + cL * vL))) +
    cL * (&2 * cO - (&457 / &500) * t - uO - aL) +
    (aL - &1) * ((cO * cL - t * sL) * (cL + sL) + t + cL) +
    ((cO * cL - t * sL) * (cL + sL) + t + cL - &2 * cO * cL - cL * t)` ASSUME_TAC THENL
  [UNDISCH_TAC `cL pow 2 + sL pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN MATCH_MP_TAC PWUUPL_POS_OF_MUL THEN
  EXISTS_TAC `t:real` THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: not_longitudinal (private) *)
let PWUUPL_NOT_LONGITUDINAL = prove
 (`forall cL sL uL vL aL cW sW uW vW aW.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cL sL /\ &1 < aL /\ lcont cL sL uL vL aL /\
     (&957 / &500) * cL < vL + aL /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     uL + aL <= ABT_lower cW sW uW vW aW cL sL
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PWUUPL_USE PWUUPL_LEFT_WALL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] THEN
  PWUUPL_NORMAL_TAC THEN
  PWUUPL_USE ABT_STRICT_BOUNDS [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
    `&457 / &500`; `&2`; `cL:real`; `sL:real`] THEN
  PWUUPL_PROD_TAC `sL:real` `vL + aL - (&957 / &500) * cL` THEN
  PWUUPL_PRODLT_TAC `cL:real` `aL - &1` THEN
  PWUUPL_PROD_TAC `cL:real` `&1 - (&457 / &500) * cL - (&43 / &500) * sL` THEN
  PWUUPL_PROD_TAC `cL:real` `ABT_lower cW sW uW vW aW cL sL - (uL + aL)` THEN
  PWUUPL_PRODLT_TAC `cL:real`
    `(cL * &457 / &500 + sL * &2) - ABT_lower cW sW uW vW aW cL sL` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: not_left_transverse (private) *)
let PWUUPL_NOT_LEFT_TRANSVERSE = prove
 (`forall cL sL (uL:real) vL aL cW sW uW vW aW.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cL sL /\ c977cc_normal cW sW /\
     aL = aW /\ &1 < aL /\ lcont cW sW uW vW aW /\
     (&957 / &500) * cL < vL + aL /\
     uW + aW <= cW + (&1457 / &500) * sW /\
     vL + aL <= ABT_lower cW sW uW vW aW (--sL) cL
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aW`)) THEN
  PWUUPL_USE PWUUPL_LEFT_WALL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aL:real`] THEN
  PWUUPL_NORMAL_TAC THEN
  PWUUPL_USE PWUUPL_CORNER [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aL:real`;
    `uW:real`; `vW:real`] THEN
  PWUUPL_USE ABT_CLOSED_BOUNDS [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aL:real`;
    `cW * uW - sW * vW`; `sW * uW + cW * vW`; `--sL`; `cL:real`] THEN
  SUBGOAL_THEN `vL + aL <= (cL * sW - sL * cW) * uW + (cL * cW + sL * sW) * vW`
    ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PWUUPL_PROD_TAC `cL:real` `cW:real` THEN PWUUPL_PROD_TAC `sL:real` `sW:real` THEN
  PWUUPL_PROD_TAC `cL:real` `cW + (&1457 / &500) * sW - uW - aL` THEN
  PWUUPL_PROD_TAC `cL * cW + sL * sW` `cW * uW - sW * (vW + aL)` THEN
  PWUUPL_PROD_TAC `sW:real`
    `(cL * sW - sL * cW) * uW + (cL * cW + sL * sW) * vW - (vL + aL)` THEN
  SUBGOAL_THEN
   `cL * (cW + (&1457 / &500) * sW) - aL * (cL + (cL * cW + sL * sW) * sW) -
    sW * (vL + aL) =
    cL * (cW + (&1457 / &500) * sW - uW - aL) +
    (cL * cW + sL * sW) * (cW * uW - sW * (vW + aL)) +
    sW * ((cL * sW - sL * cW) * uW + (cL * cW + sL * sW) * vW - (vL + aL))`
   ASSUME_TAC THENL
  [UNDISCH_TAC `cW pow 2 + sW pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  PWUUPL_PROD_TAC `cL * cW + sL * sW` `sW:real` THEN
  PWUUPL_PRODLT_TAC `aL - &1` `cL + (cL * cW + sL * sW) * sW` THEN
  PWUUPL_PROD_TAC `sW:real` `vL + aL - (&957 / &500) * cL` THEN
  PWUUPL_PROD_TAC `cL:real` `&1 - cW` THEN
  PWUUPL_PROD_TAC `cL * (&1 - cW)` `&1 - sW` THEN
  PWUUPL_PROD_TAC `sL:real` `sW pow 2` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: not_wall_transverse (private) *)
let PWUUPL_NOT_WALL_TRANSVERSE = prove
 (`forall cO (sO:real) uO (vO:real) aO cL sL uL vL aL cW sW uW vW aW t.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cO t /\ c977cc_normal cL sL /\ c977cc_normal cW sW /\
     t <= &1 / &5 /\ aO = aL /\ aL = aW /\ &1 < aL /\
     lcont cL sL uL vL aL /\ lcont cW sW uW vW aW /\
     uO + aO <= &2 * cO - (&457 / &500) * t /\
     uW + aW <= cW + (&1457 / &500) * sW /\
     ABT_upper cL sL uL vL aL cO (--t) <= uO /\
     ABT_upper cL sL uL vL aL (--sW) cW <= vW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aL`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aW`)) THEN
  PWUUPL_USE PWUUPL_LEFT_WALL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] THEN
  PWUUPL_USE PWUUPL_LEFT_WALL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aL:real`] THEN
  PWUUPL_USE PWUUPL_HALF_DEFECT [`cL:real`; `sL:real`] THEN
  PWUUPL_NORMAL_TAC THEN
  PWUUPL_USE PWUUPL_CORNER [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
    `uL + aL:real`; `vL:real`] THEN
  PWUUPL_USE PWUUPL_CORNER [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
    `uL:real`; `vL + aL:real`] THEN
  PWUUPL_USE ABT_CLOSED_BOUNDS [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
    `cL * (uL + aL) - sL * vL`; `sL * (uL + aL) + cL * vL`; `cO:real`; `--t`] THEN
  PWUUPL_USE ABT_CLOSED_BOUNDS [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
    `cL * uL - sL * (vL + aL)`; `sL * uL + cL * (vL + aL)`; `--sW`; `cW:real`] THEN
  SUBGOAL_THEN `cO * ((cL * uL - sL * (vL + aL)) + aL * (cL + sL)) - t * (sL * (uL + aL) + cL * vL) <= uO` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `--sW * (cL * uL - sL * (vL + aL)) + cW * ((sL * (uL + aL) + cL * vL) + aL * (cL - sL)) <= vW` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PWUUPL_PROD_TAC `cW:real` `cO - t` THEN PWUUPL_PROD_TAC `t:real` `cW - sW` THEN
  SUBGOAL_THEN `&0 <= cW * cO - sW * t` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PWUUPL_PROD_TAC `cW * cO - sW * t` `(cL * uL - sL * (vL + aL))` THEN
  PWUUPL_PROD_TAC `cW:real` `uO - (cO * ((cL * uL - sL * (vL + aL)) + aL * (cL + sL)) - t * (sL * (uL + aL) + cL * vL))` THEN
  PWUUPL_PROD_TAC `t:real` `vW - (--sW * (cL * uL - sL * (vL + aL)) + cW * ((sL * (uL + aL) + cL * vL) + aL * (cL - sL)))` THEN
  PWUUPL_PROD_TAC `cW:real` `&2 * cO - (&457 / &500) * t - uO - aL` THEN
  PWUUPL_PROD_TAC `cO:real` `cL + sL` THEN PWUUPL_PROD_TAC `t:real` `cL - sL` THEN
  PWUUPL_PRODLT_TAC `cW:real` `aL - &1` THEN
  PWUUPL_PRODLT_TAC `cW * (aL - &1)` `(cO * (cL + sL) + t * (cL - sL)) + &1` THEN
  PWUUPL_PROD_TAC `(cO + t) / &2` `sL - &2 * (&1 - cL)` THEN
  PWUUPL_PROD_TAC `(cO - &3 * t) / &2` `sL:real` THEN
  SUBGOAL_THEN `&0 <= (cO * (cL + sL) + t * (cL - sL)) + &1 - &2 * cO - t` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PWUUPL_PROD_TAC `cW:real` `(cO * (cL + sL) + t * (cL - sL)) + &1 - &2 * cO - t` THEN
  SUBGOAL_THEN `(&957 / &500) * cW < vW` ASSUME_TAC THENL
  [ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN MATCH_MP_TAC PWUUPL_POS_OF_MUL THEN
   EXISTS_TAC `t:real` THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PWUUPL_PROD_TAC `cW:real` `cW + (&1457 / &500) * sW - uW - aL` THEN
  PWUUPL_PROD_TAC `sW:real` `vW - (&957 / &500) * cW` THEN
  PWUUPL_PRODLT_TAC `aL - &1` `cW + sW` THEN
  PWUUPL_PROD_TAC `&1 - cW` `cW + sW` THEN
  PWUUPL_PROD_TAC `cW:real` `sW:real` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: impossible_relaxed *)
let PWUUPL_IMPOSSIBLE_RELAXED = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     sO = --t /\ c977cc_normal cO t /\ c977cc_normal cL sL /\ c977cc_normal cW sW /\
     &0 < t /\ t <= &1 / &5 /\ aO = aL /\ aL = aW /\ &1 < aL /\
     lcont cL sL uL vL aL /\ lcont cW sW uW vW aW /\
     t * (uO + aO) <= cO * vO /\
     uO + aO <= &2 * cO - (&457 / &500) * t /\
     uW + aW <= cW + (&1457 / &500) * sW /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     linside cL sL uL vL aL (&457 / &500) (&1) /\
     linside cL sL uL vL aL (&1) (&1) /\
     linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     ldisj cO sO uO vO aO cL sL uL vL aL /\
     ldisj cL sL uL vL aL cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sO = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aL`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aW`)) THEN
  PWUUPL_NORMAL_TAC THEN
  let sqO = [`cO:real`; `--t`; `uO:real`; `vO:real`; `aL:real`]
  and sqL = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`]
  and sqW = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aL:real`] in
  PWUUPL_USE ABT_OWNU sqO THEN PWUUPL_USE ABT_OWNV sqL THEN
  SUBGOAL_THEN `ABT_upper cL sL uL vL aL cO (--t) <= uO` ASSUME_TAC THENL
  [PWUUPL_USE CSP_ALTERNATIVES (sqO @ sqL) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[CSP_directed]) THEN
   FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THEN
   TRY(RASM_ARITH_TAC) THEN
   MATCH_MP_TAC(TAUT `false ==> p`) THEN
   MATCH_MP_TAC(SPECL (sqO @ sqL @ [`t:real`]) PWUUPL_NOT_LEFT_AXIS) THEN
   REPEAT CONJ_TAC THEN
   FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC]; ALL_TAC] THEN
  PWUUPL_USE PWUUPL_LEFT_UPPER_FACE (sqO @ sqL @ [`t:real`]) THEN
  let close th tms =
    MATCH_MP_TAC(SPECL tms th) THEN REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC] in
  PWUUPL_USE LSWS_ALTERNATIVES (sqL @ sqW) THENL
  [close PWUUPL_NOT_LONGITUDINAL (sqL @ sqW);
   close PWUUPL_NOT_LEFT_TRANSVERSE (sqL @ sqW);
   PWUUPL_USE ABT_STRICT_BOUNDS (sqL @ [`&19 / &25`; `&187 / &100`; `cW:real`; `sW:real`]) THEN
   RASM_ARITH_TAC;
   close PWUUPL_NOT_WALL_TRANSVERSE (sqO @ sqL @ sqW @ [`t:real`])]);;

(* Lean: marker_cap *)
let PWUUPL_MARKER_CAP = prove
 (`forall c s u (v:real) a. c977cc_normal c s /\ u + a <= (&457 / &500) * c + &3 * s
     ==> u + a <= c + (&1457 / &500) * s`,
  REWRITE_TAC[c977cc_normal] THEN REPEAT STRIP_TAC THEN RASM_ARITH_TAC);;

(* Lean: impossible *)
let PWUUPL_IMPOSSIBLE = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     sO = --t /\ c977cc_normal cO t /\ c977cc_normal cL sL /\ c977cc_normal cW sW /\
     &0 < t /\ t <= &1 / &5 /\ aO = aL /\ aL = aW /\ &1 < aL /\
     lcont cL sL uL vL aL /\ lcont cW sW uW vW aW /\
     t * (uO + aO) <= cO * vO /\
     uO + aO <= &2 * cO - (&457 / &500) * t /\
     uW + aW <= cW + (&72 / &25) * sW /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     linside cL sL uL vL aL (&457 / &500) (&1) /\
     linside cL sL uL vL aL (&1) (&1) /\
     linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     ldisj cO sO uO vO aO cL sL uL vL aL /\
     ldisj cL sL uL vL aL cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
    `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
    `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`]
    PWUUPL_IMPOSSIBLE_RELAXED) THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         PWUUPL_NORMAL_TAC THEN RASM_ARITH_TAC]);;
