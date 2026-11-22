(* ========================================================================= *)
(* Port of Compact/Geometry/MergedLeftNegative.lean                          *)
(* (N12Compact.MergedLeftNegative).  The nonpositive canonical-angle sector  *)
(* of the merged left central owner, by reflection to MergedRightWallSector. *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/MergedLeftCornerSector.ml";;
needs "n12/geometry/MergedRightWallSector.ml";;

(* B = turnFrame (turnFrame (pullX A)) as a 5-tuple. *)
let MLN_B_INSIDE = prove
 (`forall c s u v a x y.
      linside c (--s) (&4 * c - u - a) (v + &4 * s) a x y <=>
      linside c s u v a (&4 - x) y`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: point *)
let MLN_POINT = prove
 (`forall cA sA uA vA aA cL sL uL vL aL.
     cA * cA + sA * sA = &1 /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     &1 < aA /\ aA = aL /\ lcont cL sL uL vL aL /\
     &0 < cA /\ sA <= &0 /\ --sA <= cA /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&1) (&87 / &50) /\
     ~linside cA sA uA vA aA (&1) (&113 / &50) /\
     ~linside cA sA uA vA aA (&8 / &5) (&3) /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\
     linside cL sL uL vL aL (&1) (&12 / &5) /\
     ldisj cA sA uA vA aA cL sL uL vL aL
     ==> linside cA sA uA vA aA (&2) (&2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cA:real`; `--sA`; `uA - &4 * sA`; `&4 * cA - vA - aA`; `aA:real`]
    MLCS_SECTOR) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LINSIDE_PULLY] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `--sA <= &16 / &25 * cA` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aL`)) THEN
  MP_TAC(SPECL [`cA:real`; `--sA`; `&4 * cA - uA - aA`; `vA + &4 * sA`; `aA:real`;
                `--cL`; `sL:real`; `uL - &4 * cL`; `--vL - aA - &4 * sL`; `aA:real`]
    MRWS_POINT) THEN
  REWRITE_TAC[MLN_B_INSIDE; LINSIDE_PULLX; ldisj] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  ASM_SIMP_TAC[LCONT_PULLX] THEN REPEAT CONJ_TAC THEN
  TRY(ASM_REAL_ARITH_TAC) THEN ASM_MESON_TAC[]);;
