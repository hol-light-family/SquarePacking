(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveBottomNextAxes.lean (Jatloe, N12-jatloe) *)
(* (namespace N12Compact.PositiveBottomNextAxes).                            *)
(* Positive bottom singletons extend past the inner bottom-wall point; only  *)
(* the forward directed axes survive.  Lean upper/lower are ABT_upper/       *)
(* ABT_lower; the SAT step is ABT_FOUR_AXES.                                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C696PositiveCorner.ml";;

let PBNA_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PBNA_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let PBNA_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PBNA_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

let PBNA_UPPER_PN = prove
 (`forall c s u v a nx ny. &0 <= nx * c + ny * s /\ --nx * s + ny * c <= &0
     ==> ABT_upper c s u v a nx ny = (nx * c + ny * s) * (u + a) + (--nx * s + ny * c) * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ABT_upper; tss_support_radius; lcx; lcy] THEN
  ASM_SIMP_TAC[REAL_ARITH `x <= &0 ==> abs x = --x`; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  REAL_ARITH_TAC);;

let PBNA_POS_BY_POS = prove
 (`forall k y. &0 < k /\ &0 < k * y ==> &0 < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: negative_projection *)
let PBNA_NEGATIVE_PROJECTION = prove
 (`forall cO sO uO vO aO d r.
     c977cc_normal cO sO /\ c977cc_normal d r /\ &1 < aO /\ &0 < sO /\
     vO + aO <= cO - sO /\ &0 <= sO * uO + cO * vO
     ==> &2 * d - r < ABT_upper cO sO uO vO aO d (--r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PBNA_NORMAL_TAC THEN
  PBNA_PROD_TAC `cO:real` `d - r` THEN PBNA_PROD_TAC `r:real` `cO - sO` THEN
  SUBGOAL_THEN `&0 <= d * cO - r * sO` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PBNA_PROD_TAC `d:real` `sO:real` THEN PBNA_PROD_TAC `r:real` `cO:real` THEN
  PBNA_USE PBNA_UPPER_PN
    [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`; `d:real`; `--r`] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (can (term_match [] `ABT_upper c s u v a nx ny = e`) o concl)) THEN
  PBNA_PROD_TAC `d * cO - r * sO` `sO * uO + cO * vO` THEN
  PBNA_PROD_TAC `d:real` `cO - sO - (vO + aO)` THEN
  PBNA_PROD_TAC `sO:real` `d * cO - r * sO` THEN
  PBNA_PRODLT_TAC `aO - &1` `d + sO * (d * cO - r * sO)` THEN
  PBNA_PROD_TAC `d:real` `&1 - cO` THEN PBNA_PROD_TAC `r:real` `sO:real` THEN
  PBNA_PROD_TAC `&1 - sO` `d * (&1 - cO) + r * sO` THEN
  SUBGOAL_THEN
   `sO * (((d * cO + --r * sO) * (uO + aO) + (--d * sO + --r * cO) * vO) - (&2 * d - r)) =
    (d * cO - r * sO) * (sO * uO + cO * vO) + d * (cO - sO - (vO + aO)) +
    (aO - &1) * (d + sO * (d * cO - r * sO)) + (&1 - sO) * (d * (&1 - cO) + r * sO)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `cO pow 2 + sO pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN MATCH_MP_TAC PBNA_POS_BY_POS THEN
  EXISTS_TAC `sO:real` THEN CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: positive_wall *)
let PBNA_POSITIVE_WALL = prove
 (`forall cO sO uO vO aO cD sD uD vD aD.
     c977cc_normal cO sO /\ c977cc_normal cD sD /\ aO = aD /\ &1 < aO /\
     vO + aO <= cO - sO /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     linside cD sD uD vD aD (&2) (&457 / &500) /\
     ldisj cO sO uO vO aO cD sD uD vD aD
     ==> uO + aO <= ABT_lower cD sD uD vD aD cO sO \/ ABT_upper cO sO uO vO aO cD sD <= uD`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aD`)) THEN
  PBNA_NORMAL_TAC THEN
  SUBGOAL_THEN `cO * cO + sO * sO = &1 /\ cD * cD + sD * sD = &1 /\ &0 < aD`
  STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `cO pow 2 + sO pow 2 = &1` THEN CONV_TAC REAL_RING;
    UNDISCH_TAC `cD pow 2 + sD pow 2 = &1` THEN CONV_TAC REAL_RING;
    RASM_ARITH_TAC]; ALL_TAC] THEN
  let sqO = [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aD:real`]
  and sqD = [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`] in
  MP_TAC(SPECL sqO ABT_OWNU) THEN MP_TAC(SPECL sqO ABT_OWNV) THEN
  MP_TAC(SPECL sqD ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY (fun (sq,(x,y),(nx,ny)) -> ABT_SB_TAC sq x y nx ny)
   [sqO,(`&1`,`&457 / &500`),(`cO:real`,`sO:real`);
    sqD,(`&2`,`&457 / &500`),(`cO:real`,`sO:real`);
    sqO,(`&1`,`&457 / &500`),(`--sO`,`cO:real`);
    sqD,(`&2`,`&457 / &500`),(`--sO`,`cO:real`);
    sqO,(`&1`,`&457 / &500`),(`cD:real`,`sD:real`);
    sqD,(`&2`,`&457 / &500`),(`cD:real`,`sD:real`);
    sqO,(`&28 / &25`,`&1`),(`--sD`,`cD:real`);
    sqO,(`&187 / &100`,`&19 / &25`),(`--sD`,`cD:real`);
    sqD,(`&2`,`&457 / &500`),(`--sD`,`cD:real`)] THEN
  MP_TAC(SPECL (sqO @ sqD) ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN RASM_ARITH_TAC);;

(* Lean: negative_wall *)
let PBNA_NEGATIVE_WALL = prove
 (`forall cO sO uO vO aO cD sD uD vD aD r.
     sD = --r /\ c977cc_normal cO sO /\ c977cc_normal cD r /\ aO = aD /\ &1 < aO /\
     &0 < sO /\ vO + aO <= cO - sO /\ &0 <= sO * uO + cO * vO /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     linside cD sD uD vD aD (&2) (&457 / &500) /\
     linside cD sD uD vD aD (&2) (&1) /\
     ldisj cO sO uO vO aO cD sD uD vD aD
     ==> uO + aO <= ABT_lower cD sD uD vD aD cO sO \/ ABT_upper cO sO uO vO aO r cD <= vD`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aD`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sD = --r`)) THEN
  PBNA_USE PBNA_NEGATIVE_PROJECTION
    [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aD:real`; `cD:real`; `r:real`] THEN
  PBNA_NORMAL_TAC THEN
  SUBGOAL_THEN `cO * cO + sO * sO = &1 /\ cD * cD + --r * --r = &1 /\ &0 < aD`
  STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `cO pow 2 + sO pow 2 = &1` THEN CONV_TAC REAL_RING;
    UNDISCH_TAC `cD pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING;
    RASM_ARITH_TAC]; ALL_TAC] THEN
  let sqO = [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aD:real`]
  and sqD = [`cD:real`; `--r`; `uD:real`; `vD:real`; `aD:real`] in
  MP_TAC(SPECL sqO ABT_OWNU) THEN MP_TAC(SPECL sqO ABT_OWNV) THEN
  MP_TAC(SPECL sqD ABT_OWNV) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY (fun (sq,(x,y),(nx,ny)) -> ABT_SB_TAC sq x y nx ny)
   [sqO,(`&1`,`&457 / &500`),(`cO:real`,`sO:real`);
    sqD,(`&2`,`&457 / &500`),(`cO:real`,`sO:real`);
    sqO,(`&1`,`&457 / &500`),(`--sO`,`cO:real`);
    sqD,(`&2`,`&457 / &500`),(`--sO`,`cO:real`);
    sqD,(`&2`,`&1`),(`cD:real`,`--r`);
    sqO,(`&1`,`&457 / &500`),(`cD:real`,`--r`);
    sqD,(`&2`,`&457 / &500`),(`cD:real`,`--r`);
    sqO,(`&187 / &100`,`&19 / &25`),(`r:real`,`cD:real`);
    sqD,(`&2`,`&457 / &500`),(`r:real`,`cD:real`)] THEN
  MP_TAC(SPECL (sqO @ sqD) ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN
  REPEAT STRIP_TAC THEN RASM_ARITH_TAC);;
