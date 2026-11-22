(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallPositiveLeftAxes.lean (Jatloe,        *)
(* N12-jatloe; namespace N12Compact.FullAuxWallPositiveLeftAxes).            *)
(* The actual left-marker lower U face of the steep upper square removes the *)
(* negative relative-angle V selector; every positive left-wall V separator  *)
(* is impossible.  Normal is c977cc_normal; upper/lower are ABT_upper /      *)
(* ABT_lower; lower_np: FAWTE_LOWER_NP; positive_v_order / no_upper_v:       *)
(* FAWLR_POSITIVE_V_ORDER / FAWLR_NO_UPPER_V; faceSeparation_of_disjoint +   *)
(* separated + radius identities: ABT_FOUR_AXES.                             *)
(* The OpenSquare invariants are explicit hypotheses.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/FullAuxWallTopEndpoint.ml";;
needs "n12/geometry/FullAuxWallLeftResidual.ml";;

(* Lean: no_left_v *)
let FAWPLX_NO_LEFT_V = prove
 (`forall cL sL uL vL aL cB sB uB vB aB.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cL sL /\ c977cc_normal cB sB /\ &1 < aB /\
     uB + aB <= (&8 / &5) * cB + &3 * sB /\ vB + aB <= &3 * cB - sB /\
     (&457 / &500) * cB + &2 * sB <= uB /\
     &1 < (&343 / &500) * cB + sB /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\
     vL + aL <= ABT_lower cB sB uB vB aB (--sL) cL
     ==> false`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    FAWLR_POSITIVE_V_ORDER) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  FAWLR_NORMAL_TAC THEN
  FAWLR_PROD_TAC `cL:real` `cB:real` THEN FAWLR_PROD_TAC `sL:real` `sB:real` THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `--sL`; `cL:real`]
    FAWTE_LOWER_NP) THEN
  ANTS_TAC THENL [CONJ_TAC THEN NLIN_TAC ~deg2:false []; DISCH_TAC] THEN
  SUBGOAL_THEN `ABT_lower cB sB uB vB aB (--sL) cL =
                (cL * sB - sL * cB) * (uB + aB) + (cL * cB + sL * sB) * vB` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `(&457 / &500) * cB + &2 * sB < uB + aB` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `vB < &2 * cB - (&457 / &500) * sB` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`sL * cB - cL * sB`; `uB + aB - ((&457 / &500) * cB + &2 * sB)`]
    REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  FAWLR_PROD_TAC `cL * cB + sL * sB` `&2 * cB - (&457 / &500) * sB - vB` THEN
  SUBGOAL_THEN
   `(cL * sB - sL * cB) * ((&457 / &500) * cB + &2 * sB) +
    (cL * cB + sL * sB) * (&2 * cB - (&457 / &500) * sB) =
    &2 * cL - (&457 / &500) * sL` ASSUME_TAC THENL
  [UNDISCH_TAC `cB pow 2 + sB pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(ASSUME `linside cL sL uL vL aL (&457 / &500) (&2)`) THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: alternatives *)
let FAWPLX_ALTERNATIVES = prove
 (`forall cL sL uL vL aL cB sB uB vB aB.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cL sL /\ c977cc_normal cB sB /\ aL = aB /\ &1 < aB /\
     uB + aB <= (&8 / &5) * cB + &3 * sB /\ vB + aB <= &3 * cB - sB /\
     (&457 / &500) * cB + &2 * sB <= uB /\
     &1 < (&343 / &500) * cB + sB /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\
     linside cL sL uL vL aL (&1) (&8 / &5) /\ linside cB sB uB vB aB (&1) (&12 / &5) /\
     ldisj cL sL uL vL aL cB sB uB vB aB
     ==> uL + aL <= ABT_lower cB sB uB vB aB cL sL \/
         ABT_upper cL sL uL vL aL cB sB <= uB`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] FAWPLX_NO_LEFT_V) THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT(ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  REWRITE_TAC[TAUT `(p ==> false) <=> ~p`; REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] FAWLR_NO_UPPER_V) THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT(ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  REWRITE_TAC[TAUT `(p ==> false) <=> ~p`; DE_MORGAN_THM; REAL_NOT_LE] THEN STRIP_TAC THEN
  FAWLR_NORMAL_TAC THEN
  let qL = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`]
  and qB = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] in
  let mk = (`&457 / &500`,`&2`) and lo = (`&1`,`&8 / &5`) and hi = (`&1`,`&12 / &5`) in
  let d1 = (`cL:real`,`sL:real`) and d2 = (`--sL`,`cL:real`)
  and d3 = (`cB:real`,`sB:real`) in
  MAP_EVERY (fun (sq,p,d) -> FAWLR_SB_TAC sq p d)
   [qB,hi,d1; qL,mk,d1; qB,hi,d2; qL,lo,d2; qB,hi,d3; qL,mk,d3] THEN
  MP_TAC(SPECL (qL @ qB) ABT_FOUR_AXES) THEN ANTS_TAC THENL [FAWLR_ANTS_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL qL ABT_OWNU) THEN ANTS_TAC THENL [FAWLR_ANTS_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL qB ABT_OWNU) THEN ANTS_TAC THENL [FAWLR_ANTS_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL qL ABT_OWNV) THEN ANTS_TAC THENL [FAWLR_ANTS_TAC; STRIP_TAC] THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl))) THEN
  RASM_ARITH_TAC);;
