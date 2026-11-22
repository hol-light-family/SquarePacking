(* ========================================================================= *)
(* Port of Compact/Geometry/SouthwestCornerTranspose.lean (Jatloe,           *)
(* N12-jatloe; namespace N12Compact.SouthwestCornerTranspose).               *)
(* The positive-central sector with the left singleton missing its inner     *)
(* corner is the transpose of SNC_POINT.  Lean's                             *)
(* turnFrame^3 (pullSwap A) is the 5-tuple (cA, --sA, vA, uA, aA), whose     *)
(* inside is A's inside transposed (SCT_TRANSPOSE_INSIDE); pullSwap is the   *)
(* map of LINSIDE_PULLSW / LCONT_PULLSW in p2_base.ml.                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/SouthwestNegativeCorner.ml";;

let SCT_TRANSPOSE_INSIDE = prove
 (`forall c s u v a x y. linside c (--s) v u a x y <=> linside c s u v a y x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: point *)
let SCT_POINT = prove
 (`forall cO sO uO vO aO cA sA uA vA aA cL sL uL vL aL.
     cL * cL + sL * sL = &1 /\
     c977cc_normal cA sA /\ aL = aA /\ &1 < aA /\ lcont cL sL uL vL aL /\
     linside cL sL uL vL aL (&457 / &500) (&1) /\
     linside cL sL uL vL aL (&1) (&28 / &25) /\
     linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
     ~linside cL sL uL vL aL (&1) (&1) /\
     ~linside cL sL uL vL aL (&457 / &500) (&2) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&87 / &50) (&1) /\
     ldisj cL sL uL vL aL cA sA uA vA aA /\
     ldisj cA sA uA vA aA cO sO uO vO aO
     ==> linside cA sA uA vA aA (&2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`sL:real`; `cL:real`; `uL:real`; `--vL - aL`; `aL:real`;
                `cA:real`; `--sA`; `vA:real`; `uA:real`; `aA:real`;
                `sO:real`; `cO:real`; `uO:real`; `--vO - aO`; `aO:real`; `sA:real`]
    SNC_POINT) THEN
  REWRITE_TAC[SCT_TRANSPOSE_INSIDE; LINSIDE_PULLSW] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[LCONT_PULLSW] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  REWRITE_TAC[ldisj; SCT_TRANSPOSE_INSIDE; LINSIDE_PULLSW] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [UNDISCH_TAC `cL * cL + sL * sL = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[]);;
