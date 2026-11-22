(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallMarkerNegativeCorner.lean              *)
(* (namespace N12Compact.CornerWallMarkerNegativeCorner).                    *)
(* The bottom marker narrows the backward negative-left separator.           *)
(* Squares are 5-tuples (L.s = -r); Lean lower is ABT_lower; bottom_wall is  *)
(* TSS_BOTTOM_WALL.                                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/CornerWallNegativeShared.ml";;

let CWMNC_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* Lean: bottom_support *)
let CWMNC_BOTTOM_SUPPORT = prove
 (`forall cO sO uO vO aO l r H.
     cO * cO + sO * sO = &1 /\ &0 < aO /\
     c977cc_normal cO sO /\ c977cc_normal l r /\
     lcont cO sO uO vO aO /\ uO + aO <= H
     ==> cO * ABT_lower cO sO uO vO aO l (--r) <=
         l * H - aO * (cO * (sO * l + cO * r) + l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`] TSS_BOTTOM_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lcy] THEN
  SUBGOAL_THEN `abs sO = sO` SUBST1_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; DISCH_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= cO * (l - r)`; `&0 <= r * (cO - sO)`; `&0 <= l * cO - sO * r`;
    `&0 <= sO * l + cO * r`] THEN
  REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
  SUBGOAL_THEN `abs(l * cO + --r * sO) = l * cO - sO * r /\
                abs(--l * sO + --r * cO) = sO * l + cO * r` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= sO * uO + cO * vO`; `&0 <= (sO * l + cO * r) * (sO * uO + cO * vO)`;
    `&0 <= l * (H - (uO + aO))`] THEN
  NLIN_TAC ~deg2:false [CWMNC_EQ_HINT `l * uO` (ASSUME `cO pow 2 + sO pow 2 = &1`)]);;

(* Lean: restrictions *)
let CWMNC_RESTRICTIONS = prove
 (`forall cO sO uO vO aO cL sL uL vL aL r.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     c977cc_normal cO sO /\ c977cc_normal cL r /\ sL = --r /\
     &1 < aL /\ aO = aL /\ lcont cO sO uO vO aO /\
     uO + aO <= &2 * cO + (&457 / &500) * sO /\
     linside cL sL uL vL aL (&1) (&1) /\
     uL + aL <= ABT_lower cO sO uO vO aO cL (--r) /\
     &4 / &5 <= cO /\ sO <= &3 / &5
     ==> cO < &457 / &500 /\ &3 / &5 < r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`; `cL:real`; `r:real`;
                `&2 * cO + (&457 / &500) * sO`] CWMNC_BOTTOM_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  UNDISCH_TAC `linside cL sL uL vL aL (&1) (&1)` THEN
  ASM_REWRITE_TAC[linside] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aL`)) THEN
  C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC []
   [`cL - r < uL + aL`; `&0 < cO * ((uL + aL) - (cL - r))`;
    `&0 <= cO * (ABT_lower cO sO uO vO aL cL (--r) - (uL + aL))`;
    `&0 <= sO * cL`; `&0 <= cO * r`; `&0 <= cO * (sO * cL + cO * r)`;
    `&0 < cO * (sO * cL + cO * r) + cL`;
    `&0 < (aL - &1) * (cO * (sO * cL + cO * r) + cL)`;
    `&0 < cL * ((cO - &1) + sO * (&457 / &500 - cO)) + cO * r * (&1 - cO)`] THEN
  SUBGOAL_THEN `cO < &457 / &500` ASSUME_TAC THENL
   [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
    NLIN_FACTS_TAC [SQ_NONNEG `&1 - cO`]
     [`&0 <= cO * (&1 - cO)`; `&0 <= (cO * (&1 - cO)) * (cL - r)`;
      `&0 <= sO * (cO - &457 / &500)`; `&0 <= cL * (&1 - cO) pow 2`;
      `&0 <= cL * (sO * (cO - &457 / &500))`] THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(&3 / &4) * cL < r` ASSUME_TAC THENL
   [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
    NLIN_FACTS_TAC []
     [`&0 <= cO * (&1 - cO)`; `&0 <= (cO * (&1 - cO)) * ((&3 / &4) * cL - r)`;
      `&0 <= (&3 / &5 - sO) * (&457 / &500 - cO)`;
      `&0 <= (cO - &4 / &5) * ((&3 / &4) * cO - &11 / &20)`;
      `&0 < (&1 - cO) * (&1 - (&3 / &4) * cO) + sO * (cO - &457 / &500)`;
      `&0 < cL * ((&1 - cO) * (&1 - (&3 / &4) * cO) + sO * (cO - &457 / &500))`] THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
  NLIN_FACTS_TAC []
   [`&0 < (r - (&3 / &4) * cL) * ((&3 / &4) * cL + r)`;
    `&0 <= (&3 / &5 - r) * (&3 / &5 + r)`] THEN
  NLIN_TAC ~deg2:false []);;
