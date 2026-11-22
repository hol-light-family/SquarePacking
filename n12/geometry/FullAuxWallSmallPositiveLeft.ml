(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallSmallPositiveLeft.lean (Jatloe,       *)
(* N12-jatloe; namespace N12Compact.FullAuxWallSmallPositiveLeft).           *)
(* The genuine small positive left-wall frame cannot use its own            *)
(* longitudinal separator against the steep upper square.  Normal is         *)
(* c977cc_normal; lower is ABT_lower; cosine_order: C977CSB_COSINE_ORDER;    *)
(* FourSquareBLBridge.left_wall: FSBL_LEFT_WALL.  The Lean local            *)
(* abbreviations alpha, h are written out.  The OpenSquare invariants are    *)
(* explicit hypotheses.                                                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/FullAuxWallTopEndpoint.ml";;
needs "n12/geometry/FullAuxWallPositiveLeftAxes.ml";;

let FAWSPL_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let FAWSPL_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let FAWSPL_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

(* Lean: margin (private) *)
let FAWSPL_MARGIN = prove
 (`forall l r b t. c977cc_normal l r /\ c977cc_normal b t /\ r <= &1 / &5 /\ &3 / &10 < t
     ==> l pow 2 * ((&8 / &5) - b - (&3 / &5) * t pow 2 + (&3 / &5) * b * t) +
         l * r * ((&2 / &5) - t + (&3 / &5) * t pow 2 + (&3 / &5) * b * t) +
         (&457 / &500) * r pow 2 - l <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWSPL_NORMAL_TAC THEN
  FAWSPL_PROD_TAC `b:real` `&10 / &7 - (b + t)` THEN
  FAWSPL_PROD_TAC `t:real` `&10 / &7 - (b + t)` THEN
  NLIN_FACTS_TAC []
   [`(&8 / &5) - b - (&3 / &5) * t pow 2 + (&3 / &5) * b * t <= &9 / &10`;
    `(&2 / &5) - t + (&3 / &5) * t pow 2 + (&3 / &5) * b * t <= &9 / &25`] THEN
  FAWSPL_PROD_TAC `l pow 2`
    `&9 / &10 - ((&8 / &5) - b - (&3 / &5) * t pow 2 + (&3 / &5) * b * t)` THEN
  SUBGOAL_THEN `&0 <= l * r` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  FAWSPL_PROD_TAC `l * r` `&9 / &25 - ((&2 / &5) - t + (&3 / &5) * t pow 2 + (&3 / &5) * b * t)` THEN
  FAWSPL_PROD_TAC `&1 - l` `&3 * l - &2` THEN
  SUBGOAL_THEN `&1 - l <= (&3 / &5) * r pow 2` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWSPL_PROD_TAC `&1 / &5 - r` `&1 / &5 + r` THEN
  FAWSPL_PROD_TAC `r:real` `&1 - l` THEN
  NLIN_TAC ~deg2:false []);;

(* the lower support of B in the direction of L when alpha >= 0 >= -h *)
let FAWSPL_LOWER_PN = prove
 (`forall c s u v a x y. &0 <= x * c + y * s /\ --x * s + y * c <= &0
     ==> ABT_lower c s u v a x y = (x * c + y * s) * u + (--x * s + y * c) * (v + a)`,
  REPEAT STRIP_TAC THEN C981NP_FORM_TAC);;

(* Lean: no_left_u *)
let FAWSPL_NO_LEFT_U = prove
 (`forall cL sL uL vL aL cB sB uB vB aB.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cL sL /\ c977cc_normal cB sB /\ aL = aB /\ &1 < aB /\
     sL <= &1 / &5 /\ &3 / &10 < sB /\
     lcont cL sL uL vL aL /\ linside cL sL uL vL aL (&457 / &500) (&2) /\
     linside cB sB uB vB aB (&1) (&12 / &5) /\
     uB + aB <= (&8 / &5) * cB + &3 * sB /\
     uL + aL <= ABT_lower cB sB uB vB aB cL sL
     ==> false`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aL:real = aB`)) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `cL:real`; `sL:real`] C977CSB_COSINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`] FSBL_LEFT_WALL) THEN
  FAWSPL_NORMAL_TAC THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lcx] THEN
  SUBGOAL_THEN `abs sL = sL` SUBST1_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= cL * uL - sL * (vL + aB)` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[linside]
    (ASSUME `linside cL sL uL vL aB (&457 / &500) (&2)`)) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[linside]
    (ASSUME `linside cB sB uB vB aB (&1) (&12 / &5)`)) THEN
  FAWSPL_PRODLT_TAC `cL:real` `cB:real` THEN FAWSPL_PROD_TAC `sL:real` `sB:real` THEN
  FAWSPL_PRODLT_TAC `cL:real` `sB - sL` THEN FAWSPL_PROD_TAC `sL:real` `cL - cB` THEN
  SUBGOAL_THEN `&0 < cL * sB - sL * cB` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `cL:real`; `sL:real`]
    FAWSPL_LOWER_PN) THEN
  ANTS_TAC THENL [CONJ_TAC THEN NLIN_TAC ~deg2:false []; DISCH_TAC] THEN
  SUBGOAL_THEN `ABT_lower cB sB uB vB aB cL sL =
                (cL * cB + sL * sB) * uB - (cL * sB - sL * cB) * (vB + aB)` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FAWSPL_PROD_TAC `sL:real` `(vL + aB) - (--sL * (&457 / &500) + cL * &2)` THEN
  SUBGOAL_THEN `cL * aB + &2 * cL * sL - (&457 / &500) * sL pow 2 <= cL * (uL + aB)`
    ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cL * (cL * cB + sL * sB)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cL * (cL * sB - sL * cB)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cL * (&1 + (cL * cB + sL * sB))` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  FAWSPL_PROD_TAC `cL * (cL * cB + sL * sB)` `(&8 / &5) * cB + &3 * sB - (uB + aB)` THEN
  FAWSPL_PRODLT_TAC `cL * (cL * sB - sL * cB)` `(vB + aB) - (--sB * &1 + cB * (&12 / &5))` THEN
  FAWSPL_PROD_TAC `cL:real`
    `((cL * cB + sL * sB) * uB - (cL * sB - sL * cB) * (vB + aB)) - (uL + aB)` THEN
  FAWSPL_PRODLT_TAC `cL * (&1 + (cL * cB + sL * sB))` `aB - &1` THEN
  SUBGOAL_THEN
   `cL * ((cL * cB + sL * sB) * ((&8 / &5) * cB + &3 * sB) -
          (cL * sB - sL * cB) * ((&12 / &5) * cB - sB)) -
    cL * (&1 + (cL * cB + sL * sB)) - &2 * cL * sL + (&457 / &500) * sL pow 2 =
    cL pow 2 * ((&8 / &5) - cB - (&3 / &5) * sB pow 2 + (&3 / &5) * cB * sB) +
    cL * sL * ((&2 / &5) - sB + (&3 / &5) * sB pow 2 + (&3 / &5) * cB * sB) +
    (&457 / &500) * sL pow 2 - cL` ASSUME_TAC THENL
  [UNDISCH_TAC `cB pow 2 + sB pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `cB:real`; `sB:real`] FAWSPL_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  NLIN_TAC ~deg2:false []);;
