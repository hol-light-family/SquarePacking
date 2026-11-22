(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallNegativeCycle.lean                     *)
(* (N12Compact.FullAuxWallNegativeCycle).  A complete signed sector of the  *)
(* full auxiliary-wall configuration: the opposite central square D has     *)
(* sD = --S with c977cc_normal cD S; B may have either sign.                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FullAuxWallTopEndpoint.ml";;
needs "n12/geometry/FullAuxWallOppositeAxes.ml";;
needs "n12/geometry/FullAuxWallSmallTopAngle.ml";;

let FAWNC_PROD = FAWTE_PROD;;

let FAWNC_NORMALS_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal; REAL_POW_2] th)) ns) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]);;

(* Lean: no_opposite_v (private) *)
let FAWNC_NO_OPPOSITE_V = prove
 (`forall cD sD uD vD aD cB sB uB vB aB S.
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     sD = --S /\ c977cc_normal cD S /\ c977cc_normal cB sB /\ &1 < aB /\
     linside cD sD uD vD aD (&2) (&2) /\
     uB + aB <= (&8 / &5) * cB + &3 * sB /\ vB + aB <= &3 * cB - sB /\
     vD + aD <= ABT_lower cB sB uB vB aB S cD
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sD:real = --S`)) THEN
  FAWNC_NORMALS_TAC THEN
  FAWTE_UNFOLD_TAC `linside cD (--S) uD vD aD (&2) (&2)` THEN
  SUBGOAL_THEN `&0 <= S * cB + cD * sB` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FAWNC_PROD `&0 <= (cD - S) * cB` THEN
  FAWNC_PROD `&0 <= S * (cB - sB)` THEN
  SUBGOAL_THEN `&0 <= --S * sB + cD * cB` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `S:real`; `cD:real`]
    FAWTE_LOWER_PP) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  FAWNC_PROD `&0 <= (cB + sB - &1) * (&3 / &2 - (cB + sB))` THEN
  FAWNC_PROD `&0 <= cB * sB` THEN
  SUBGOAL_THEN `&0 <= cB + sB - &1 - (&3 / &5) * cB * sB` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FAWNC_PROD `&0 <= sB * sB` THEN
  FAWNC_PROD `&0 <= cD * (cB + sB - &1 - (&3 / &5) * cB * sB)` THEN
  FAWNC_PROD `&0 <= S * (cB - sB + &2 / &5 + (&3 / &5) * sB * sB)` THEN
  FAWNC_PROD `&0 <= (S * cB + cD * sB) * ((&8 / &5) * cB + &3 * sB - &1 - uB)` THEN
  FAWNC_PROD `&0 <= (--S * sB + cD * cB) * (&3 * cB - sB - &1 - vB)` THEN
  SUBGOAL_THEN
   `(S * cB + cD * sB) * ((&8 / &5) * cB + &3 * sB - &1) +
    (--S * sB + cD * cB) * (&3 * cB - sB - &1) - &2 * (cD + S) =
    --cD * (cB + sB - &1 - (&3 / &5) * cB * sB) -
    S * (cB - sB + &2 / &5 + (&3 / &5) * sB * sB)` MP_TAC THENL
  [UNDISCH_TAC `cB * cB + sB * sB = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: impossible_of_cut *)
let FAWNC_IMPOSSIBLE_OF_CUT = prove
 (`forall cD sD uD vD aD cB sB uB vB aB c s S.
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal c s /\ &0 < s /\ &4 * s <= c /\
     sD = --S /\ c977cc_normal cD S /\
     &0 < cB /\ --cB <= sB /\ sB <= cB /\
     &1 < aD /\ aD = aB /\
     linside cD sD uD vD aD (&2) (&2) /\
     linside cD sD uD vD aD (&33 / &20) (&33 / &20) /\
     linside cD sD uD vD aD (&2) (&3 / &2) /\
     ~linside cD sD uD vD aD (&1) (&87 / &50) /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&1) (&113 / &50) /\
     linside cB sB uB vB aB (&1) (&12 / &5) /\
     ~linside cB sB uB vB aB (&8 / &5) (&3) /\
     ~linside cB sB uB vB aB (&1) (&3) /\
     ~linside cB sB uB vB aB (&457 / &500) (&2) /\
     ldisj cD sD uD vD aD cB sB uB vB aB /\
     (c * cD - s * S) * (uD + aD - &2 * (cD - S)) +
     (c * S + s * cD) * (vD + aD - &2 * (cD + S)) < (&13 / &50) * s
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sD:real = --S`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aD:real = aB`)) THEN
  MP_TAC(SPECL [`cD:real`; `--S:real`; `uD:real`; `vD:real`; `aB:real`;
                `c:real`; `s:real`; `S:real`] FAWOE_NARROW_AND_LEFT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`cD:real`; `--S:real`; `uD:real`; `vD:real`; `aB:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `S:real`]
    FAWTE_TRANSVERSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_CASES_TAC `&0 <= sB` THENL
  [SUBGOAL_THEN `c977cc_normal cB sB` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2]; ALL_TAC] THEN
   MP_TAC(SPECL [`cD:real`; `--S:real`; `uD:real`; `vD:real`; `aB:real`;
                 `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `S:real`]
     FAWTE_POSITIVE_V) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
   SUBGOAL_THEN `uB + aB <= (&8 / &5) * cB + &3 * sB` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside cB sB uB vB aB (&8 / &5) (&3)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `linside cB sB uB vB aB (&33 / &20) (&47 / &20)` THEN
    UNDISCH_TAC `linside cB sB uB vB aB (&1) (&12 / &5)` THEN
    REWRITE_TAC[linside] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] FAWOC_CORNER_CAP) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [MP_TAC(SPECL [`cD:real`; `--S:real`; `uD:real`; `vD:real`; `aB:real`;
                  `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `S:real`]
      FAWNC_NO_OPPOSITE_V) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   FAWNC_NORMALS_TAC THEN
   SUBGOAL_THEN `&0 <= sB * cD + cB * S` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   FAWNC_PROD `&0 <= (cD - S) * cB` THEN
   FAWNC_PROD `&0 <= S * (cB - sB)` THEN
   SUBGOAL_THEN `&0 <= cB * cD - sB * S` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `ABT_upper cD (--S) uD vD aB (--sB) cB =
                 --(sB * cD + cB * S) * uD + (cB * cD - sB * S) * (vD + aB)` ASSUME_TAC THENL
   [C981NP_FORM_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `ABT_upper cD (--S) uD vD aB (--sB) cB =
     &2 * (cB - sB) + aB * (sB * cD + cB * S) -
     (sB * cD + cB * S) * (uD + aB - &2 * (cD - S)) +
     (cB * cD - sB * S) * (vD + aB - &2 * (cD + S))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cD * cD + S * S = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
   FAWTE_UNFOLD_TAC `linside cD (--S) uD vD aB (&2) (&2)` THEN
   MP_TAC(SPECL [`aB:real`; `c:real`; `s:real`; `cD:real`; `S:real`; `cB:real`; `sB:real`;
                 `uD + aB - &2 * (cD - S)`; `vD + aB - &2 * (cD + S)`]
     FAWSTA_SMALL_TOP_ANGLE) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    RASM_ARITH_TAC; DISCH_TAC] THEN
   UNDISCH_TAC `~linside cB sB uB vB aB (&457 / &500) (&2)` THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC FAWOC_TWO_CAPS_MARKER THEN ASM_REWRITE_TAC[];
   UNDISCH_TAC `~linside cB sB uB vB aB (&8 / &5) (&3)` THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC FAWTE_NEGATIVE_POINT THEN
   MAP_EVERY EXISTS_TAC [`cD:real`; `--S:real`; `uD:real`; `vD:real`; `aB:real`;
                         `S:real`; `--sB:real`] THEN
   ASM_REWRITE_TAC[REAL_NEG_NEG; c977cc_normal; REAL_POW_2; REAL_MUL_LNEG;
     REAL_MUL_RNEG] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: negative_opposite_impossible *)
let FAWNC_NEGATIVE_OPPOSITE_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cD sD uD vD aD cB sB uB vB aB S.
     cA * cA + sA * sA = &1 /\ &0 < aA /\
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cA sA /\ &0 < sA /\ &4 * sA <= cA /\
     sD = --S /\ c977cc_normal cD S /\
     &0 < cB /\ --cB <= sB /\ sB <= cB /\
     &1 < aA /\ aA = aD /\ aD = aB /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     linside cA sA uA vA aA (&5 / &2) (&3) /\
     vA + aA <= &3 * cA - (&12 / &5) * sA /\
     linside cD sD uD vD aD (&2) (&2) /\
     linside cD sD uD vD aD (&33 / &20) (&33 / &20) /\
     linside cD sD uD vD aD (&2) (&3 / &2) /\
     ~linside cD sD uD vD aD (&1) (&87 / &50) /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&1) (&113 / &50) /\
     linside cB sB uB vB aB (&1) (&12 / &5) /\
     ~linside cB sB uB vB aB (&8 / &5) (&3) /\
     ~linside cB sB uB vB aB (&1) (&3) /\
     ~linside cB sB uB vB aB (&457 / &500) (&2) /\
     ldisj cA sA uA vA aA cD sD uD vD aD /\
     ldisj cD sD uD vD aD cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cA sA`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cD S`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cD S`)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`; `S:real`] FAWOA_CUT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cA:real`; `sA:real`; `S:real`] FAWNC_IMPOSSIBLE_OF_CUT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]]);;
