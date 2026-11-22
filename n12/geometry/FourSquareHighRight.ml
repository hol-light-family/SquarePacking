(* ========================================================================= *)
(* Port of Compact/Geometry/FourSquareHighRight.lean                         *)
(*                                                                           *)
(* Premises A B L R (the structure) becomes the hypothesis list, with        *)
(* lsquare for the OpenSquare invariants, as in FST_STMT.                    *)
(* FSHR_POSITIVE_CORE is the nonnegative-B branch of the Lean proof (the     *)
(* same argument as FourSquarePositive.impossible after its forced A point). *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FourSquareTemplate.ml";;

let FSHR_POSITIVE_CORE = prove
 (`forall cA sA uA vA aA cB sB uB vB aB cL sL uL vL aL cR sR uR vR aR.
     cA * cA + sA * sA = &1 /\ cB * cB + sB * sB = &1 /\
     cL * cL + sL * sL = &1 /\ cR * cR + sR * sR = &1 /\
     &1 < aB /\ aB <= &1001 / &1000 /\
     aA = aB /\ aB = aL /\ aB = aR /\
     &0 < cB /\ &0 <= sB /\ sB <= cB /\
     &0 < cL /\ abs sL <= cL /\
     lcont cB sB uB vB aB /\ lcont cL sL uL vL aL /\ lcont cR sR uR vR aR /\
     lclosed cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&2) (&5 / &2) /\
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
     ldisj cA sA uA vA aA cB sB uB vB aB /\
     ldisj cB sB uB vB aB cL sL uL vL aL /\
     ldisj cB sB uB vB aB cR sR uR vR aR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `aA:real = aB` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aB:real = aL` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aB:real = aR` o concl)) THEN
  (* rowA *)
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

(* Lean: impossible (the structure Premises is the hypothesis list) *)
let FSHR_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cB sB uB vB aB cL sL uL vL aL cR sR uR vR aR.
     lsquare cA sA uA vA aA /\ lsquare cB sB uB vB aB /\
     lsquare cL sL uL vL aL /\ lsquare cR sR uR vR aR /\
     &1 < aB /\ aB <= &1001 / &1000 /\
     aA = aB /\ aB = aL /\ aB = aR /\
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
     ldisj cA sA uA vA aA cB sB uB vB aB /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ldisj cB sB uB vB aB cL sL uL vL aL /\
     ldisj cB sB uB vB aB cR sR uR vR aR /\
     linside cR sR uR vR aR (&3) (&5 / &2)
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lsquare] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `aA:real = aB` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aB:real = aL` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aB:real = aR` o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcont; ldisj]) THEN
  FST_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
                  `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                  `&33 / &20`; `&47 / &20`] OUTSIDE_OF_CLOSED) THEN
  FST_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
                  `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aB:real`;
                  `&3`; `&12 / &5`] OUTSIDE_OF_CLOSED) THEN
  SUBGOAL_THEN `~linside cA sA uA vA aB (&3) (&5 / &2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`] CLF_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `aq:real = aB` o concl)) THEN
  FST_STEP(SPECL [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aB:real`] FSAN_POINT_OF_HIGHER_R) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cb:real`; `sb:real`; `ub:real`; `vb:real`; `ab:real`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cl:real`; `sl:real`; `ul:real`; `vl:real`; `al:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `al:real = aB` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `ab:real = aB` o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcont; ldisj]) THEN
  ASM_CASES_TAC `&0 <= sb` THENL
   [(* nonnegative canonical B *)
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
                  `cb:real`; `sb:real`; `ub:real`; `vb:real`; `aB:real`;
                  `cl:real`; `sl:real`; `ul:real`; `vl:real`; `aB:real`;
                  `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aB:real`] FSHR_POSITIVE_CORE) THEN
    REWRITE_TAC[lcont; ldisj] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    (* negative canonical B *)
    SUBGOAL_THEN `forall x y. ~(linside cB sB uB vB aB x y /\ linside cA sA uA vA aB x y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FST_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`] FSAF_ROW_POINT) THEN
  FST_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
                  `cb:real`; `sb:real`; `ub:real`; `vb:real`; `aB:real`;
                  `cl:real`; `sl:real`; `ul:real`; `vl:real`; `aB:real`;
                  `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aB:real`] FSBC_NO_LONG_SECTION) THEN
  FST_STEP(SPECL [`cb:real`; `sb:real`; `ub:real`; `vb:real`; `aB:real`;
                  `cl:real`; `sl:real`; `ul:real`; `vl:real`; `aB:real`;
                  `&1`; `&12 / &5`] OUTSIDE_OF_CLOSED) THEN
  SUBGOAL_THEN `~linside cB sB uB vB aB (&2) (&5 / &2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cb:real`; `sb:real`; `ub:real`; `vb:real`; `aB:real`;
                `cl:real`; `sl:real`; `ul:real`; `vl:real`; `aB:real`] FSBNC_EXCLUDE) THEN
  REWRITE_TAC[lcont; ldisj] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;
