(* ========================================================================= *)
(* Port of Compact/Geometry/LeftSingletonWallSeparation.lean                 *)
(* (N12Compact.LeftSingletonWallSeparation).  Separation of the left         *)
(* singleton L and the left wall square W.                                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;

let LSWS_SQ_L = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`];;
let LSWS_SQ_W = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aL:real`];;

let LSWS_START_TAC =
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aW`));;

let LSWS_DIRS = [`cL:real`,`sL:real`; `--sL`,`cL:real`; `cW:real`,`sW:real`; `--sW`,`cW:real`];;

(* Lean: alternatives *)
let LSWS_ALTERNATIVES = prove
 (`forall cL sL uL vL aL cW sW uW vW aW.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     &0 < cL /\ &0 <= sL /\ &0 < cW /\ &0 <= sW /\ aL = aW /\
     linside cL sL uL vL aL (&457 / &500) (&1) /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     ldisj cL sL uL vL aL cW sW uW vW aW
     ==> uL + aL <= ABT_lower cW sW uW vW aW cL sL \/
         vL + aL <= ABT_lower cW sW uW vW aW (--sL) cL \/
         ABT_upper cL sL uL vL aL cW sW <= uW \/
         ABT_upper cL sL uL vL aL (--sW) cW <= vW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN LSWS_START_TAC THEN
  ABT_ALL_SB_TAC [LSWS_SQ_L,(`&457 / &500`,`&1`); LSWS_SQ_W,(`&457 / &500`,`&2`)]
    LSWS_DIRS THEN
  ABT_OWN_TAC LSWS_SQ_L THEN ABT_OWN_TAC LSWS_SQ_W THEN ABT_ARITH_TAC);;

(* Lean: singleton_tilt *)
let LSWS_SINGLETON_TILT = prove
 (`forall cL sL uL vL aL cW sW uW vW aW.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     &0 < cL /\ &0 <= sL /\ &1 < aL /\ lcont cL sL uL vL aL /\
     linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     uL + aL <= ABT_lower cW sW uW vW aW cL sL
     ==> cL / &4 < sL`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL LSWS_SQ_L TSS_POSITIVE_FRAME_WALL_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ABT_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `lcont cL sL uL vL aL` THEN REWRITE_TAC[lcont] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[lcx] THEN STRIP_TAC THEN
  ABT_SB_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    `&457 / &500` `&2` `cL:real` `sL:real` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  NLIN_FACTS_TAC [SQ_NONNEG `sL:real`; SQ_NONNEG `cL - &1`]
   [`sL * (vL + aL) <= cL * uL`; `cL <= &1`;
    `&0 <= cL * (&1 - cL)`; `&0 <= cL * (cL / &4 - sL)`;
    `&0 <= (cL / &4 - sL) * (cL / &4 + sL)`;
    `sL * (--sL * (&19 / &25) + cL * (&187 / &100)) <= sL * (vL + aL)`;
    `cL < cL * aL`;
    `cL * (uL + aL) <= cL * ABT_lower cW sW uW vW aW cL sL`;
    `cL * ABT_lower cW sW uW vW aW cL sL < cL * (cL * &457 / &500 + sL * &2)`] THEN
  ABT_ARITH_TAC);;

(* Lean: wall_tilt *)
let LSWS_WALL_TILT = prove
 (`forall cL sL uL vL aL cW sW uW vW aW.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     linside cL sL uL vL aL (&1) (&1) /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     ABT_upper cL sL uL vL aL cW sW <= uW
     ==> (&43 / &500) * cW < sW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABT_SB_TAC LSWS_SQ_L `&1` `&1` `cW:real` `sW:real` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN ABT_ARITH_TAC);;

(* Lean: guarded_alternatives *)
let LSWS_GUARDED_ALTERNATIVES = prove
 (`forall cL sL uL vL aL cW sW uW vW aW.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     &0 < cL /\ &0 <= sL /\ &0 < cW /\ &0 <= sW /\ aL = aW /\ &1 < aL /\
     lcont cL sL uL vL aL /\
     linside cL sL uL vL aL (&457 / &500) (&1) /\
     linside cL sL uL vL aL (&1) (&1) /\
     linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     ldisj cL sL uL vL aL cW sW uW vW aW
     ==> (cL / &4 < sL /\ uL + aL <= ABT_lower cW sW uW vW aW cL sL) \/
         vL + aL <= ABT_lower cW sW uW vW aW (--sL) cL \/
         ((&43 / &500) * cW < sW /\ ABT_upper cL sL uL vL aL cW sW <= uW) \/
         ABT_upper cL sL uL vL aL (--sW) cW <= vW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    LSWS_ALTERNATIVES) THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    LSWS_SINGLETON_TILT) THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    LSWS_WALL_TILT) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* Lean: negative_wall_alternatives *)
let LSWS_NEGATIVE_WALL_ALTERNATIVES = prove
 (`forall cL sL uL vL aL cW sW uW vW aW.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     &0 < cL /\ abs sL <= cL /\
     &0 < cW /\ sW <= &0 /\ --cW <= sW /\
     aL = aW /\ &1 < aL /\ lcont cL sL uL vL aL /\
     linside cL sL uL vL aL (&457 / &500) (&1) /\
     linside cL sL uL vL aL (&1) (&1) /\
     linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     ldisj cL sL uL vL aL cW sW uW vW aW
     ==> (cL / &4 < sL /\ uL + aL <= ABT_lower cW sW uW vW aW cL sL) \/
         vL + aL <= ABT_lower cW sW uW vW aW (--sL) cL \/
         ABT_upper cL sL uL vL aL (--sW) cW <= vW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    LSWS_SINGLETON_TILT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  LSWS_START_TAC THEN
  ABT_ALL_SB_TAC [LSWS_SQ_L,(`&457 / &500`,`&1`); LSWS_SQ_L,(`&1`,`&1`);
                  LSWS_SQ_L,(`&19 / &25`,`&187 / &100`);
                  LSWS_SQ_W,(`&457 / &500`,`&2`)] LSWS_DIRS THEN
  ABT_OWN_TAC LSWS_SQ_L THEN ABT_OWN_TAC LSWS_SQ_W THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
    filter (fun th -> let t = concl th in not(is_forall t) &&
      (is_imp t || is_real_rel t || (is_neg t && is_real_rel(rand t))))) THEN
  REAL_ARITH_TAC);;
