(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallPositiveLeftNeighbor.lean              *)
(* (N12Compact.FullAuxWallPositiveLeftNeighbor).  The opposite central       *)
(* square's own U separator cannot coexist with the genuine left wall once   *)
(* that wall has sine at least 4/25.  Normal is c977cc_normal (bounds        *)
(* C977CC_NORMAL_BOUNDS), cosine_order / sine_order are C977CSB_*, upper is  *)
(* ABT_upper (band form C981SF_UPPER_IN_BANDS), InsideContainer is lcont,    *)
(* FourSquareBLBridge.left_wall is FSBL_LEFT_WALL.  Lean variables C S of    *)
(* the scalar lemmas are written dc ds.  The Lean lets alpha, H, u, K are    *)
(* written out.  Tag FAWPLN_.                                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FullAuxWallSmallPositiveLeftB.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let FAWPLN_LIN = NLIN_TAC ~deg2:false [];;

let FAWPLN_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FAWPLN_LIN; ALL_TAC];;

let FAWPLN_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [FAWPLN_LIN; ALL_TAC];;

(* X * (c * c + s * s) = X from an assumption c * c + s * s = &1 *)
let FAWPLN_UNIT x u = SUBGOAL_THEN (mk_eq(mk_binop `( * ):real->real->real` x u, x)) ASSUME_TAC
  THENL [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC];;

let FAWPLN_NORMAL_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `c977cc_normal x y`) (concl th) then
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2] th)
    else NO_TAC));;

let FAWPLN_CONTRA = ONCE_REWRITE_TAC[GSYM REAL_NOT_LT; GSYM REAL_NOT_LE] THEN DISCH_TAC;;

(* Lean: cosine_small (private) *)
let FAWPLN_COSINE_SMALL = prove
 (`forall l r. c977cc_normal l r /\ r <= &3 / &10 ==> &19 / &20 <= l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWPLN_NORMAL_TAC THEN
  FAWPLN_PROD `&0 <= (&3 / &10 - r) * (&3 / &10 + r)` THEN
  FAWPLN_CONTRA THEN
  FAWPLN_PROD `&0 <= (&19 / &20 - l) * (&19 / &20 + l)` THEN FAWPLN_LIN);;

(* Lean: diagonal (private) *)
let FAWPLN_DIAGONAL = prove
 (`forall l r u. c977cc_normal l r /\ &4 / &25 <= r /\ r <= &3 / &10 /\ u <= &1 / &1000
     ==> &0 < l * (&2 - &2 * l - u) - (&457 / &500) * r pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`l:real`; `r:real`] FAWPLN_COSINE_SMALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN FAWPLN_NORMAL_TAC THEN
  FAWPLN_PROD `&0 <= (r - &4 / &25) * (r + &4 / &25)` THEN
  FAWPLN_PROD `&0 <= (r * r) * ((&543 / &500) * l - &457 / &500 - &1177 / &10000)` THEN
  FAWPLN_PROD `&0 <= (&1 - l) * (l + &2)` THEN
  FAWPLN_PROD `&0 <= (l * (&1 + l)) * (&1 / &1000 - u)` THEN
  FAWPLN_UNIT `&2 * l` `l * l + r * r` THEN
  FAWPLN_FACT `&0 < (&1 + l) * (l * (&2 - &2 * l - u) - (&457 / &500) * r * r)` THEN
  REWRITE_TAC[REAL_POW_2] THEN FAWPLN_CONTRA THEN
  FAWPLN_PROD `&0 <= (&1 + l) * --(l * (&2 - &2 * l - u) - (&457 / &500) * r * r)` THEN
  FAWPLN_LIN);;

(* Lean: below *)
let FAWPLN_BELOW = prove
 (`forall dc ds l r u. c977cc_normal dc ds /\ c977cc_normal l r /\
     ds <= &11 / &50 /\ &4 / &25 <= r /\ u <= &1 / &1000 /\ r <= ds
     ==> &0 < l * (&1 + (l * dc + r * ds) - &2 * dc - u) - (&457 / &500) * ds * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`l:real`; `r:real`] FAWPLN_COSINE_SMALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`l:real`; `r:real`; `u:real`] FAWPLN_DIAGONAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`dc:real`; `ds:real`; `l:real`; `r:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FAWPLN_NORMAL_TAC THEN
  FAWPLN_PROD `&0 <= (l - dc) * (l * (&2 - l))` THEN
  FAWPLN_PROD `&0 <= (ds - r) * (r * (l - &457 / &500))` THEN
  FAWPLN_UNIT `l:real` `l * l + r * r` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN FAWPLN_LIN);;

(* Lean: above *)
let FAWPLN_ABOVE = prove
 (`forall dc ds l r u. c977cc_normal dc ds /\ c977cc_normal l r /\
     ds <= &11 / &50 /\ &4 / &25 <= r /\ u <= &1 / &1000 /\ ds <= r
     ==> &0 < l * (&1 + (l * dc + r * ds) + (r * dc - l * ds) - &2 * dc - u) -
              (&457 / &500) * ds * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `r <= &3 / &10` THENL
   [MP_TAC(SPECL [`l:real`; `r:real`; `u:real`] FAWPLN_DIAGONAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`l:real`; `r:real`; `dc:real`; `ds:real`] C977CSB_COSINE_ORDER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FAWPLN_NORMAL_TAC THEN
    FAWPLN_PROD `&0 <= (r - ds) * (dc + l - r - ds)` THEN
    SUBGOAL_THEN `&0 <= r - ds - (dc - l)` ASSUME_TAC THENL
     [FAWPLN_CONTRA THEN FAWPLN_PROD `&0 < (dc + l) * --(r - ds - (dc - l))` THEN FAWPLN_LIN;
      ALL_TAC] THEN
    FAWPLN_PROD `&0 <= (r - ds - (dc - l)) * (l * (&2 - l - r))` THEN
    FAWPLN_PROD `&0 <= r * (&457 / &500 - r)` THEN
    FAWPLN_PROD `&0 <= (&1 - l) * (&1 - l)` THEN
    FAWPLN_FACT `&0 <= (&457 / &500) * r - &2 * l * (&1 - l)` THEN
    FAWPLN_PROD `&0 <= (r - ds) * ((&457 / &500) * r - &2 * l * (&1 - l))` THEN
    FAWPLN_UNIT `l:real` `l * l + r * r` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN FAWPLN_LIN;
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    FAWPLN_NORMAL_TAC THEN
    FAWPLN_PROD `&0 <= (r - &3 / &10) * (l - &3 / &10)` THEN
    SUBGOAL_THEN `&5 / &4 <= l + r` ASSUME_TAC THENL
     [FAWPLN_CONTRA THEN
      FAWPLN_PROD `&0 <= (&5 / &4 - (l + r)) * (l + r + &13 / &20)` THEN FAWPLN_LIN;
      ALL_TAC] THEN
    FAWPLN_PROD `&0 <= l * (l - r)` THEN
    FAWPLN_FACT `&0 <= l * (l - r) + (&457 / &500) * r` THEN
    FAWPLN_PROD `&0 <= (&1 - l) * (l - r)` THEN
    FAWPLN_FACT `l * (l - r) + (&457 / &500) * r <= l` THEN
    FAWPLN_PROD `&0 <= (&1 - dc) * (l * (&2 - l - r))` THEN
    FAWPLN_PROD `&0 <= (&11 / &50 - ds) * (l * (l - r) + (&457 / &500) * r)` THEN
    FAWPLN_PROD `&0 <= l * (&1 / &1000 - u)` THEN
    FAWPLN_PROD `&0 <= l * ((l + r) - &5 / &4)` THEN
    FAWPLN_LIN]);;

(* Lean: impossible *)
let FAWPLN_IMPOSSIBLE = prove
 (`forall cL sL uL vL aL cD sD uD (vD:real) aD.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     c977cc_normal cL sL /\ c977cc_normal cD sD /\ &1 < aD /\ aL = aD /\
     lcont cL sL uL vL aL /\ linside cL sL uL vL aL (&457 / &500) (&2) /\
     sD <= &11 / &50 /\ &4 / &25 <= sL /\
     uD + aD - &2 * (cD + sD) <= &1 / &1000 /\
     ABT_upper cL sL uL vL aL cD sD <= uD
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aL:real = aD`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cL sL`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cD sD`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> concl th = `c977cc_normal cL sL`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> concl th = `c977cc_normal cD sD`)) THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aD:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN FAWPLN_LIN; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= s ==> abs s = s`; lcx] THEN DISCH_TAC THEN
  FAWPLN_FACT `sL * (vL + aD) <= cL * (uL + aD) - cL * aD` THEN
  FAWPLN_PROD `&0 < cL * cD` THEN FAWPLN_PROD `&0 <= sL * sD` THEN
  FAWPLN_FACT `&0 < cL * cD + sL * sD` THEN
  FAWPLN_PROD `&0 <= (cL * cD + sL * sD) * ((cL * (uL + aD) - cL * aD) - sL * (vL + aD))` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  FAWPLN_PROD `&0 <= sD * ((vL + aD) - (--sL * (&457 / &500) + cL * &2))` THEN
  FAWPLN_UNIT `sD * vL` `cL * cL + sL * sL` THEN
  FAWPLN_UNIT `sD * aD` `cL * cL + sL * sL` THEN
  FAWPLN_UNIT `sD:real` `cL * cL + sL * sL` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C981SF_UPPER_IN_BANDS]) THEN
  SUBGOAL_THEN `abs(cD * cL + sD * sL) = cL * cD + sL * sD`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC(REAL_ARITH `x = y /\ &0 < y ==> abs x = y`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= sL * cD - cL * sD` THENL
   [SUBGOAL_THEN `abs(--cD * sL + sD * cL) = sL * cD - cL * sD`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [MATCH_MP_TAC(REAL_ARITH `x = --y /\ &0 <= y ==> abs x = y`) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`cL:real`; `sL:real`; `cD:real`; `sD:real`] C977CSB_SINE_ORDER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN FAWPLN_LIN; DISCH_TAC] THEN
    MP_TAC(SPECL [`cD:real`; `sD:real`; `cL:real`; `sL:real`; `uD + aD - &2 * (cD + sD)`]
      FAWPLN_ABOVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FAWPLN_PROD `&0 <= cL * (uD - ((cD * cL + sD * sL) * (uL + aD / &2) +
       (--cD * sL + sD * cL) * (vL + aD / &2) +
       aD / &2 * ((cL * cD + sL * sD) + (sL * cD - cL * sD))))` THEN
    FAWPLN_PROD `&0 < (aD - &1) * (cL * (&1 + (cL * cD + sL * sD) + (sL * cD - cL * sD)))` THEN
    FAWPLN_LIN;
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    SUBGOAL_THEN `abs(--cD * sL + sD * cL) = --(sL * cD - cL * sD)`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [MATCH_MP_TAC(REAL_ARITH `x = y /\ &0 <= y ==> abs x = y`) THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; FAWPLN_LIN]; ALL_TAC] THEN
    MP_TAC(SPECL [`cD:real`; `sD:real`; `cL:real`; `sL:real`] C977CSB_SINE_ORDER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN FAWPLN_LIN; DISCH_TAC] THEN
    MP_TAC(SPECL [`cD:real`; `sD:real`; `cL:real`; `sL:real`; `uD + aD - &2 * (cD + sD)`]
      FAWPLN_BELOW) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FAWPLN_PROD `&0 <= cL * (uD - ((cD * cL + sD * sL) * (uL + aD / &2) +
       (--cD * sL + sD * cL) * (vL + aD / &2) +
       aD / &2 * ((cL * cD + sL * sD) + --(sL * cD - cL * sD))))` THEN
    FAWPLN_PROD `&0 < (aD - &1) * (cL * (&1 + (cL * cD + sL * sD)))` THEN
    FAWPLN_LIN]);;
