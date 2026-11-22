(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingBoundaryShallow.lean           *)
(* (N12Compact.C1092MPPMMissingBoundaryShallow).  Full local Theorem 1 of   *)
(* MISSING-BOUNDARY-SHALLOW-ANGLE.  Square C is cC sC uC vC aC, square B is *)
(* cB sB uB vB aB; Input / BoundaryFaces are c1092mbsg_input /               *)
(* c1092mbsg_boundary_faces; crossCos / crossSin are c1092mbs_crossCos /     *)
(* c1092mbs_crossSin; upper / lower are ABT_upper / ABT_lower.  Tag          *)
(* C1092MBSH_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingBoundaryShallowGeometry.ml";;


(* unfold Input, cross signs, boundary strict bounds and boundary faces *)
let C1092MBSH_SETUP_TAC =
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    C1092MBSG_BOUNDARY_FACES) THEN
  ASM_REWRITE_TAC[c1092mbsg_boundary_faces] THEN STRIP_TAC THEN
  UNDISCH_TAC `c1092mbsg_input cC sC uC vC aC cB sB uB vB aB` THEN
  REWRITE_TAC[c1092mbsg_input] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cB:real`; `--sB`] C1092MBS_CROSS_BOUNDS) THEN
  MP_TAC(SPECL [`cB:real`; `--sB`] C1092MBS_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = aB`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mbs_crossCos; c1092mbs_crossSin]) THEN
  REWRITE_TAC[c1092mbs_crossCos; c1092mbs_crossSin];;

let C1092MBSH_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC]) tms;;

(* Lean: lower_on_negative_u (private) *)
let C1092MBSH_LOWER_ON_NEGATIVE_U = prove
 (`forall cC sC uC vC aC cB sB uB vB aB. cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092mbsg_input cC sC uC vC aC cB sB uB vB aB
     ==> ABT_lower cC sC uC vC aC (--cB) (--sB) =
         --c1092mbs_crossCos cC sC cB (--sB) * (uC + aC) +
         c1092mbs_crossSin cC sC cB (--sB) * vC`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cB:real`; `--sB`] C1092MBS_CROSS_BOUNDS) THEN
  UNDISCH_TAC `c1092mbsg_input cC sC uC vC aC cB sB uB vB aB` THEN
  REWRITE_TAC[c1092mbsg_input] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[C981SF_LOWER_IN_BANDS; c1092mbs_crossCos; c1092mbs_crossSin] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `abs(--cB * cC + --sB * sC) = cC * cB - sC * --sB /\
                abs(-- --cB * sC + --sB * cC) = cC * --sB + sC * cB`
    (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: upper_on_central_v (private) *)
let C1092MBSH_UPPER_ON_CENTRAL_V = prove
 (`forall cC sC uC vC aC cB sB uB vB aB. cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092mbsg_input cC sC uC vC aC cB sB uB vB aB
     ==> ABT_upper cB sB uB vB aB (--sC) cC =
         --c1092mbs_crossSin cC sC cB (--sB) * uB +
         c1092mbs_crossCos cC sC cB (--sB) * (vB + aB)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cB:real`; `--sB`] C1092MBS_CROSS_BOUNDS) THEN
  UNDISCH_TAC `c1092mbsg_input cC sC uC vC aC cB sB uB vB aB` THEN
  REWRITE_TAC[c1092mbsg_input] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[C981SF_UPPER_IN_BANDS; c1092mbs_crossCos; c1092mbs_crossSin] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `abs(--sC * cB + cC * sB) = cC * --sB + sC * cB /\
                abs(-- --sC * sB + cC * cB) = cC * cB - sC * --sB`
    (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: lower_on_boundary_v (private) *)
let C1092MBSH_LOWER_ON_BOUNDARY_V = prove
 (`forall cC sC uC vC aC cB sB uB vB aB. cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092mbsg_input cC sC uC vC aC cB sB uB vB aB
     ==> ABT_lower cC sC uC vC aC (--sB) cB =
         c1092mbs_crossSin cC sC cB (--sB) * uC +
         c1092mbs_crossCos cC sC cB (--sB) * vC`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cB:real`; `--sB`] C1092MBS_CROSS_BOUNDS) THEN
  UNDISCH_TAC `c1092mbsg_input cC sC uC vC aC cB sB uB vB aB` THEN
  REWRITE_TAC[c1092mbsg_input] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[C981SF_LOWER_IN_BANDS; c1092mbs_crossCos; c1092mbs_crossSin] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `abs(--sB * cC + cB * sC) = cC * --sB + sC * cB /\
                abs(-- --sB * sC + cB * cC) = cC * cB - sC * --sB`
    (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]);;

let C1092MBSH_SPEC th =
  SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
         `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] th;;

let C1092MBSH_MARGIN_TAC th extra =
  MP_TAC(SPECL ([`cC:real`; `sC:real`; `cB:real`; `--sB`] @ extra) th) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mbs_crossCos; c1092mbs_crossSin]);;

(* Lean: no_negative_u *)
let C1092MBSH_NO_NEGATIVE_U = prove
 (`forall cC sC uC vC aC cB sB uB vB aB. cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092mbsg_input cC sC uC vC aC cB sB uB vB aB /\
     ABT_upper cB sB uB vB aB (--cB) (--sB) <= ABT_lower cC sC uC vC aC (--cB) (--sB)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(C1092MBSH_SPEC C1092MBSH_LOWER_ON_NEGATIVE_U) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[OCWPVG_UPPER_NEG]) THEN
  C1092MBSH_SETUP_TAC THEN
  C1092MBSH_MARGIN_TAC C1092MBS_NORTHWEST_MARGIN [] THEN
  C1092MBSH_PROD_TAC
   [`&0 <= cB * (--cB - (vB + aB))`;
    `&0 <= --sB * (cC * cB - sC * --sB)`;
    `&0 <= --sB * (cC * --sB + sC * cB)`;
    `&0 <= (--sB * (cC * cB - sC * --sB)) * (uC - (--cC - sC / &2))`;
    `&0 <= (--sB * (cC * --sB + sC * cB)) * (sC - (vC + aB))`;
    `&0 <= --sB * ((cC * cB - sC * --sB) + (cC * --sB + sC * cB))`] THEN
  C1092MBSH_PROD_TAC
   [`&0 < (aB - &1) * (cB - sB + --sB * ((cC * cB - sC * --sB) + (cC * --sB + sC * cB)))`;
    `&0 <= --sB * ((--(cC * cB - sC * --sB) * (uC + aB) + (cC * --sB + sC * cB) * vC) -
                   --uB)`] THEN
  RASM_ARITH_TAC);;

(* Lean: no_central_v *)
let C1092MBSH_NO_CENTRAL_V = prove
 (`forall cC sC uC vC aC cB sB uB vB aB. cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092mbsg_input cC sC uC vC aC cB sB uB vB aB /\
     ABT_upper cB sB uB vB aB (--sC) cC <= ABT_lower cC sC uC vC aC (--sC) cC
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(C1092MBSH_SPEC C1092MBSH_UPPER_ON_CENTRAL_V) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  C1092MBSH_SETUP_TAC THEN
  C1092MBSH_MARGIN_TAC C1092MBS_CENTRAL_MARGIN [] THEN
  SUBGOAL_THEN `--sB * (--(cC * --sB + sC * cB) * uB + (cC * cB - sC * --sB) * (vB + aB) - vC) -
      (aB * ((cC * --sB + sC * cB) * (cB - sB) - sB) - &2 * (cC * --sB + sC * cB) +
       sC * (cB + sB)) =
      (cC * --sB + sC * cB) * (&2 - aB * (cB - sB) - (--sB * uB - cB * (vB + aB))) +
      sC * (--cB - (vB + aB)) + --sB * (sC - aB - vC)` ASSUME_TAC THENL
   [UNDISCH_TAC `cB * cB + sB * sB = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092MBSH_PROD_TAC
   [`&0 <= (cC * --sB + sC * cB) *
            ((&2 - aB * (cB - sB)) - (--sB * uB - cB * (vB + aB)))`;
    `&0 <= sC * (--cB - (vB + aB))`;
    `&0 <= --sB * (sC - (vC + aB))`;
    `&0 < (cC * --sB + sC * cB) * (cB - sB)`] THEN
  C1092MBSH_PROD_TAC
   [`&0 < (aB - &1) * ((cC * --sB + sC * cB) * (cB - sB) - sB)`;
    `&0 <= --sB * (vC - (--(cC * --sB + sC * cB) * uB + (cC * cB - sC * --sB) * (vB + aB)))`] THEN
  RASM_ARITH_TAC);;

(* Lean: no_large_boundary_v *)
let C1092MBSH_NO_LARGE_BOUNDARY_V = prove
 (`forall cC sC uC vC aC cB sB uB vB aB. cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092mbsg_input cC sC uC vC aC cB sB uB vB aB /\ cB <= &4 * --sB /\
     ABT_upper cB sB uB vB aB (--sB) cB <= ABT_lower cC sC uC vC aC (--sB) cB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(C1092MBSH_SPEC C1092MBSH_LOWER_ON_BOUNDARY_V) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  C1092MBSH_SETUP_TAC THEN
  C1092MBSH_MARGIN_TAC C1092MBS_NORTHEAST_MARGIN [] THEN
  C1092MBSH_PROD_TAC
   [`&0 <= --sB * (uB - (--cB - (&543 / &500) * sB))`;
    `&0 <= cB * (cC * --sB + sC * cB)`;
    `&0 <= cB * (cC * cB - sC * --sB)`;
    `&0 <= (cB * (cC * --sB + sC * cB)) * (--aB - uC)`;
    `&0 <= (cB * (cC * cB - sC * --sB)) * (sC - (vC + aB))`;
    `&0 <= cB * (((cC * --sB + sC * cB) * uC + (cC * cB - sC * --sB) * vC) - (vB + aB))`;
    `&0 <= cB * ((cC * cB - sC * --sB) + (cC * --sB + sC * cB))`] THEN
  C1092MBSH_PROD_TAC
   [`&0 < (aB - &1) * (cB - sB + cB * ((cC * cB - sC * --sB) + (cC * --sB + sC * cB)))`] THEN
  RASM_ARITH_TAC);;

(* Lean: shallow *)
let C1092MBSH_SHALLOW = prove
 (`forall cC sC uC vC aC cB sB uB vB aB. cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092mbsg_input cC sC uC vC aC cB sB uB vB aB ==> --sB / cB < &1 / &4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(C1092MBSH_SPEC C1092MBSG_SEPARATORS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(C1092MBSH_SPEC C1092MBSH_NO_NEGATIVE_U) THEN
  MP_TAC(C1092MBSH_SPEC C1092MBSH_NO_CENTRAL_V) THEN
  MP_TAC(C1092MBSH_SPEC C1092MBSH_NO_LARGE_BOUNDARY_V) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  UNDISCH_TAC `c1092mbsg_input cC sC uC vC aC cB sB uB vB aB` THEN
  REWRITE_TAC[c1092mbsg_input] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `--sB`] C1092MBS_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < cB` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `cB <= &4 * --sB` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[]);;
