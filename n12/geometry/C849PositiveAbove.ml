(* ========================================================================= *)
(* Port of Compact/Geometry/C849PositiveAbove.lean                           *)
(* (N12Compact.C849PositiveAbove).  The positive-B / upper-U-C sector of     *)
(* 849/851 is impossible.                                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/PositiveBLeftReduction.ml";;

(* Lean: c_missing_faces *)
let C849PA_C_MISSING_FACES = prove
 (`forall c s u v a.
      &0 < c /\ &0 <= s /\
      lclosed c s u v a (&113 / &50) (&3) /\
      lclosed c s u v a (&3) (&1543 / &500) /\
      ~linside c s u v a (&1543 / &500) (&3)
      ==> u + a <= c * (&1543 / &500) + s * &3 \/
          --s * (&1543 / &500) + c * &3 <= v`,
  REWRITE_TAC[linside; lclosed] THEN REAL_ARITH_TAC);;

(* Lean: c_forced_point *)
let C849PA_C_FORCED_POINT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < c /\ &0 <= s /\ &1 < a /\
      linside c s u v a (&113 / &50) (&3) /\
      lclosed c s u v a (&213 / &100) (&81 / &25) /\
      lclosed c s u v a (&3) (&1543 / &500) /\
      u + a <= c * (&1543 / &500) + s * &3
      ==> linside c s u v a (&1043 / &500) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  LUC_LIN_TAC);;

(* Lean: b_right_cap *)
let C849PA_B_RIGHT_CAP = prove
 (`forall cB sB uB vB aB cC sC uC vC aC.
      &0 < cB /\ &0 <= sB /\ sB <= cB /\
      lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
      lclosed cB sB uB vB aB (&8 / &5) (&3) /\
      lclosed cB sB uB vB aB (&2) (&1543 / &500) /\
      linside cC sC uC vC aC (&1043 / &500) (&3) /\
      ldisj cB sB uB vB aB cC sC uC vC aC
      ==> uB + aB <= (&1043 / &500) * cB + &3 * sB`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~linside cB sB uB vB aB (&1043 / &500) (&3)` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  LUC_LIN_TAC);;

(* Lean: b_lower_face *)
let C849PA_B_LOWER_FACE = prove
 (`forall c s u v a.
      &0 < c /\ &0 <= s /\
      lclosed c s u v a (&33 / &20) (&47 / &20) /\
      linside c s u v a (&2) (&1543 / &500) /\
      ~linside c s u v a (&2) (&5 / &2)
      ==> -- &2 * s + (&5 / &2) * c <= v`,
  REWRITE_TAC[linside; lclosed] THEN REAL_ARITH_TAC);;

(* Lean: impossible *)
let C849PA_IMPOSSIBLE = prove
 (`forall cB sB uB vB aB cL sL uL vL aL cC sC uC vC aC.
      cB * cB + sB * sB = &1 /\ cL * cL + sL * sL = &1 /\
      cC * cC + sC * sC = &1 /\
      &0 < cB /\ &0 <= sB /\ sB <= cB /\ &0 < cL /\ abs sL <= cL /\
      &0 < cC /\ &0 <= sC /\
      &1 < aB /\ &1 < aC /\ aB = aL /\
      lcont cL sL uL vL aL /\
      lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
      lclosed cB sB uB vB aB (&8 / &5) (&3) /\
      linside cB sB uB vB aB (&2) (&1543 / &500) /\
      ~linside cB sB uB vB aB (&2) (&5 / &2) /\
      ~linside cB sB uB vB aB (&1) (&3) /\
      lclosed cL sL uL vL aL (&457 / &500) (&2) /\
      lclosed cL sL uL vL aL (&1) (&12 / &5) /\
      ~linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
      ~linside cL sL uL vL aL (&33 / &20) (&33 / &20) /\
      linside cC sC uC vC aC (&113 / &50) (&3) /\
      lclosed cC sC uC vC aC (&213 / &100) (&81 / &25) /\
      lclosed cC sC uC vC aC (&3) (&1543 / &500) /\
      uC + aC <= cC * (&1543 / &500) + sC * &3 /\
      ldisj cB sB uB vB aB cL sL uL vL aL /\
      ldisj cB sB uB vB aB cC sC uC vC aC
      ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`]
    C849PA_C_FORCED_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`]
    C849PA_B_RIGHT_CAP) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[LINSIDE_CLOSED]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    C849PA_B_LOWER_FACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC PBLR_IMPOSSIBLE_WITH_RIGHT_CAP THEN
  MAP_EVERY EXISTS_TAC [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                        `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] THEN
  ASM_REWRITE_TAC[]);;
