(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/C974976Origins.lean                *)
(* (N12Compact.CommonCases.C974976Central).  The original C974/C976          *)
(* top-origin and southeast-lower / bottom-origin transfers.  Squares are    *)
(* 5-tuples (L = cL sL uL vL aL etc.); InsideContainer is lcont; apart is    *)
(* ldisj; EndingInput is cc974c_ending.  WallLowerReach.point = WLR_POINT,   *)
(* OriginalOwners.vertical_segment = OO_VERTICAL_SEGMENT,                    *)
(* WallProfile.boundary_origin = OCWPBO_BOUNDARY_ORIGIN, C1090.Residual-     *)
(* CentralPoints = C1090RCP_*, UpperBarPoint.point_original =               *)
(* OCUBP_POINT_ORIGINAL, translated = OCCE_INSIDE_TRANSLATED, pullX/pullY =  *)
(* LINSIDE_PULLX/Y.  Tag CC974O_.                                            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_C974976Central.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;
needs "n12/geometry/WallLowerReach.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_BoundaryOrigin.ml";;
needs "n12/geometry/CP_OtherCases_C1090_ResidualCentralPoints.ml";;

let CC974O_SIDE_TAC =
  REWRITE_TAC[REAL_NEG_MUL2] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  TRY (CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC) THEN TRY RASM_ARITH_TAC;;

(* Lean: top_origin *)
let CC974O_TOP_ORIGIN = prove
 (`forall cL sL uL vL aL cT sT uT vT aT cK sK uK vK aK.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cT * cT + sT * sT = &1 /\ &0 < aT /\
     cK * cK + sK * sK = &1 /\ &0 < aK /\
     &1 < aL /\ &1 < aT /\ aT = aK /\
     lcont cL sL uL vL aL /\ lcont cT sT uT vT aT /\ lcont cK sK uK vK aK /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\ linside cL sL uL vL aL (&1) (&12 / &5) /\
     ~linside cL sL uL vL aL (&1) (&87 / &50) /\ ~linside cL sL uL vL aL (&87 / &50) (&2) /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\ linside cT sT uT vT aT (&8 / &5) (&3) /\
     linside cK sK uK vK aK (&1) (&1543 / &500) /\ linside cK sK uK vK aK (&1) (&3) /\
     ldisj cK sK uK vK aK cL sL uL vL aL /\ ldisj cK sK uK vK aK cT sT uT vT aT
     ==> linside cT sT uT vT aT (&2) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] WLR_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `&1`; `&12 / &5`; `&64 / &25`; `&5 / &2`] OO_VERTICAL_SEGMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  SUBGOAL_THEN `(forall x y. linside cT sT uT vT aT x (&4 - y) ==> &0 <= y) /\
                (forall x y. linside cK sK uK vK aK x (&4 - y) ==> &0 <= x /\ &0 <= y)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `lcont cT sT uT vT aT`; UNDISCH_TAC `lcont cK sK uK vK aK`] THEN
    REWRITE_TAC[lcont] THEN DISCH_THEN(MP_TAC o SPECL [`x:real`; `&4 - y`]) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  SUBGOAL_THEN `~linside cK sK uK vK aK (&1) (&5 / &2) /\
                (forall x y. ~(linside cK sK uK vK aK x (&4 - y) /\
                         linside cT sT uT vT aT x (&4 - y)))`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cT:real`; `--sT:real`; `uT - &4 * sT`; `&4 * cT - vT - aT`; `aT:real`;
                `cK:real`; `--sK:real`; `uK - &4 * sK`; `&4 * cK - vK - aK`; `aK:real`;
                `&457 / &500`; `&8 / &5`] OCWPBO_BOUNDARY_ORIGIN) THEN
  REWRITE_TAC[LINSIDE_PULLY; ldisj] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN CC974O_SIDE_TAC);;

(* the two transfers of southeast_lower (Lean: local have transfer) *)
let CC974O_TRANSFER = prove
 (`forall cS sS uS vS aS cN sN uN vN aN a b.
     cS * cS + sS * sS = &1 /\ &0 < aS /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     cc974c_ending cS sS uS vS aS cN sN uN vN aN /\
     linside cS sS uS vS aS (&113 / &50) (&2) /\
     c1090rcp_parameters a b /\ linside cN sN uN vN aN (&2 + a) (&2 + b)
     ==> linside cS sS uS vS aS (&3) (&3 / &2)`,
  REPEAT GEN_TAC THEN CC974C_UNFOLD_TAC THEN
  MP_TAC(SPECL [`cS:real`; `sS:real`; `uS - (cS * &2 + sS * &2)`; `vS - (--sS * &2 + cS * &2)`;
                `aS:real`; `a:real`; `b:real`] C1090RCP_SOUTHEAST_POINT) THEN
  REWRITE_TAC[OCCE_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Lean: southeast_lower *)
let CC974O_SOUTHEAST_LOWER = prove
 (`forall cS sS uS vS aS cN sN uN vN aN.
     cS * cS + sS * sS = &1 /\ &0 < aS /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     cc974c_ending cS sS uS vS aS cN sN uN vN aN /\
     linside cS sS uS vS aS (&113 / &50) (&2)
     ==> linside cS sS uS vS aS (&3) (&3 / &2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `cc974c_input cS sS uS vS aS cN sN uN vN aN` ASSUME_TAC THENL
   [ASM_MESON_TAC[cc974c_ending]; ALL_TAC] THEN
  MP_TAC(SPEC_ALL CC974C_NORTHEAST_G7) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL CC974C_NORTHEAST_F7) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC CC974O_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] THEN
  ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(MAP_EVERY ASSUME_TAC o rev) THEN
  UNDISCH_TAC `cc974c_ending cS sS uS vS aS cN sN uN vN aN` THEN CC974C_UNFOLD_TAC THEN
  ASM_CASES_TAC `linside cN sN uN vN aN (&2) (&113 / &50)` THENL
   [MP_TAC(SPECL [`cN:real`; `sN:real`; `uN - (cN * &2 + sN * &2)`;
                  `vN - (--sN * &2 + cN * &2)`; `aN:real`] C1090RCP_MIXED_POINT) THEN
    REWRITE_TAC[OCCE_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MAP_EVERY EXISTS_TAC [`&21 / &50`; `&4 / &25`];
    MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`]
      OCUBP_POINT_ORIGINAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MAP_EVERY EXISTS_TAC [`&21 / &40`; `&1 / &8`]] THEN
  REWRITE_TAC[c1090rcp_parameters] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[]);;

(* Lean: bottom_origin *)
let CC974O_BOTTOM_ORIGIN = prove
 (`forall cB sB uB vB aB cK sK uK vK aK cS sS uS vS aS.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     cS * cS + sS * sS = &1 /\ &0 < aS /\
     &1 < aB /\ aB = aK /\ lcont cB sB uB vB aB /\ lcont cK sK uK vK aK /\
     linside cB sB uB vB aB (&2) (&457 / &500) /\ linside cB sB uB vB aB (&12 / &5) (&1) /\
     linside cK sK uK vK aK (&3) (&457 / &500) /\ linside cK sK uK vK aK (&3) (&1) /\
     linside cS sS uS vS aS (&3) (&3 / &2) /\
     ldisj cK sK uK vK aK cS sS uS vS aS /\ ldisj cK sK uK vK aK cB sB uB vB aB
     ==> linside cB sB uB vB aB (&2) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(forall x y. linside cB sB uB vB aB (&4 - x) y ==> &0 <= y) /\
                (forall x y. linside cK sK uK vK aK (&4 - x) y ==> &0 <= x /\ &0 <= y)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `lcont cB sB uB vB aB`; UNDISCH_TAC `lcont cK sK uK vK aK`] THEN
    REWRITE_TAC[lcont] THEN DISCH_THEN(MP_TAC o SPECL [`&4 - x`; `y:real`]) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  SUBGOAL_THEN `~linside cK sK uK vK aK (&3) (&3 / &2) /\
                (forall x y. ~(linside cK sK uK vK aK (&4 - x) y /\
                         linside cB sB uB vB aB (&4 - x) y))`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`--cB:real`; `sB:real`; `uB - &4 * cB`; `--vB - aB - &4 * sB`; `aB:real`;
                `--cK:real`; `sK:real`; `uK - &4 * cK`; `--vK - aK - &4 * sK`; `aK:real`;
                `&457 / &500`; `&8 / &5`] OCWPBO_BOUNDARY_ORIGIN) THEN
  REWRITE_TAC[LINSIDE_PULLX; ldisj] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN CC974O_SIDE_TAC);;
