(* ========================================================================= *)
(* Port of Compact/Geometry/FourSquarePositive.lean                          *)
(*                                                                           *)
(* Squares A, B, L, R as 5-tuples (cA,sA,uA,vA,aA) etc.  InsideContainer is  *)
(* lcont, disjointness ldisj, supportRadius tss_support_radius.              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/FourSquareLongitudinal.ml";;
needs "n12/geometry/FourSquareAAll.ml";;

let FSP_LDISJ_SYM = prove
 (`forall c s u v a c' s' u' v' a'.
     ldisj c s u v a c' s' u' v' a' ==> ldisj c' s' u' v' a' c s u v a`,
  REWRITE_TAC[ldisj] THEN MESON_TAC[]);;

(* MP_TAC a lemma instance and discharge its antecedent from the assumptions *)
let FSP_USE th =
  MP_TAC th THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM ldisj] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC; DISCH_TAC];;

(* Lean: impossible *)
let FSP_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cB sB uB vB aB cL sL uL vL aL cR sR uR vR aR.
     cA * cA + sA * sA = &1 /\ cB * cB + sB * sB = &1 /\
     cL * cL + sL * sL = &1 /\ cR * cR + sR * sR = &1 /\
     &1 < aB /\ aB <= &1001 / &1000 /\
     aA = aB /\ aB = aL /\ aB = aR /\
     &0 < cB /\ &0 <= sB /\ sB <= cB /\
     &0 < cL /\ abs sL <= cL /\
     lcont cB sB uB vB aB /\ lcont cL sL uL vL aL /\ lcont cR sR uR vR aR /\
     lclosed cA sA uA vA aA (&2) (&113 / &50) /\
     lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     lclosed cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     lclosed cB sB uB vB aB (&8 / &5) (&3) /\
     lclosed cB sB uB vB aB (&87 / &50) (&3) /\
     ~linside cB sB uB vB aB (&1) (&1543 / &500) /\
     ~linside cB sB uB vB aB (&2) (&1543 / &500) /\
     lclosed cL sL uL vL aL (&457 / &500) (&2) /\
     lclosed cL sL uL vL aL (&1) (&12 / &5) /\
     ~linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
     ~linside cL sL uL vL aL (&33 / &20) (&33 / &20) /\
     lclosed cR sR uR vR aR (&3) (&12 / &5) /\
     lclosed cR sR uR vR aR (&1543 / &500) (&2) /\
     ~linside cR sR uR vR aR (&81 / &25) (&187 / &100) /\
     ldisj cA sA uA vA aA cB sB uB vB aB /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ldisj cB sB uB vB aB cL sL uL vL aL /\
     ldisj cB sB uB vB aB cR sR uR vR aR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `aA:real = aB` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aB:real = aL` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aB:real = aR` o concl)) THEN
  (* highA, rowA *)
  FSP_USE(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
                 `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                 `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aB:real`] FSAA_POINT) THEN
  FSP_USE(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`] FSAF_ROW_POINT) THEN
  (* short *)
  ASSUME_TAC(MATCH_MP FSP_LDISJ_SYM
    (ASSUME `ldisj cA sA uA vA aB cB sB uB vB aB`)) THEN
  FSP_USE(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
                 `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                 `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`;
                 `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aB:real`] FSBC_NO_LONG_SECTION) THEN
  FSP_USE(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] FSBC_CENTER_ABOVE_RADIUS) THEN
  FSP_USE(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] FSBC_UPPER_CORNER) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
  FSP_USE(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] FSBC_CORNER_STEEP) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
  (* rowMissing, targetMissing *)
  FSP_USE(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                 `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`;
                 `&1`; `&12 / &5`] OUTSIDE_OF_CLOSED) THEN
  SUBGOAL_THEN `~linside cB sB uB vB aB (&2) (&5 / &2)` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cA sA uA vA aB cB sB uB vB aB` THEN REWRITE_TAC[ldisj] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  FSP_USE(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] FSBC_FORCED_LOWER_V) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
  (* axes, lowV, dot *)
  FSP_USE(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                 `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`] BLL_TWO_DIRECTED_ALTERNATIVES) THEN
  FSP_USE(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                 `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`] FSBL_MISSING_BELOW_V) THEN
  FSP_USE(SPECL [`cB:real`; `sB:real`; `cL:real`; `sL:real`] FSBL_DOT_NONNEG) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [(* B axis *)
    FSP_USE(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                   `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`] FSBL_RIGHT_AXIS_CAP) THEN
    FSP_USE(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`] FSBL_LEFT_WALL) THEN
    MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`] LCENTRE_COORDS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs(cB * cL + sB * sL) = cB * cL + sB * sL /\
                  abs(--cB * sL + sB * cL) = abs(cB * sL - sB * cL)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[tss_support_radius]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `abs(cB * cL + sB * sL) = cB * cL + sB * sL`;
                                ASSUME `abs(--cB * sL + sB * cL) = abs(cB * sL - sB * cL)`]) THEN
    MATCH_MP_TAC(SPECL [`aB:real`; `cB:real`; `sB:real`; `cL:real`; `sL:real`;
                        `lcx cL sL uL vL aB`; `lcy cL sL uL vL aB`] FSL_B_AXIS_IMPOSSIBLE) THEN
    REWRITE_TAC[REAL_POW_2] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
    (* L axis *)
    FSP_USE(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`] FSBL_LEFT_UPPER_BOUNDS) THEN
    FSP_USE(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                   `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`] FSBL_RIGHT_MINIMUM_BOUNDS) THEN
    MATCH_MP_TAC(SPECL [`aB:real`; `cB:real`; `sB:real`; `cL:real`; `sL:real`;
                        `uL + aB:real`] FSL_L_AXIS_IMPOSSIBLE) THEN
    REWRITE_TAC[REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
    REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC]);;
