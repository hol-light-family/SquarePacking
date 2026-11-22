(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualInwardReduction.lean           *)
(* (N12Compact.C1092MPPMActualInward).  Exhaustive original-family inward    *)
(* reduction.  (Lean header: "Source only, uncompiled".)  Conventions of     *)
(* CP_C1092_MPPMActualInwardMissingEnds.ml / MPPMActualInwardSymmetry.ml /   *)
(* MPPMActualPositiveOrder.ml: owners p i at mask EL i c1092wc_code (side l);*)
(* Inward / Ordinary c1092mcc_inward / c1092mcc_ordinary; NorthOrdinary /    *)
(* NorthInward c1092mais_northOrdinary / c1092mais_northInward;              *)
(* C1092MPPMActualPositiveOrder.Ordinary c1092mpapo_ordinary; rotation i     *)
(* EL i c1092mpapo_rotation (halfTurn = rotation 2 = (F,T,T)).  The pulled   *)
(* packing (rotation i).pullPacking p is (d1,d2,e1,e2) with c1092ot_pk;      *)
(* family / context transport via c1092mpapo_rot_tac and                     *)
(* C1092MPAPO_ROTATION_CONTEXT; half_inside / half_inward / half_ordinary /  *)
(* owners_transport are applied as c1092mpapo_pull_tac (owner 4 of the      *)
(* pulled packing rewritten to the original owner).  Used: centered_sign     *)
(* C1092MPAIP_CENTERED_SIGN, centered_far / missing_outer_far C1092MPAIF_*,  *)
(* missing_center_outer C1092MAIME_MISSING_CENTER_OUTER, centered_oioi /     *)
(* opposed_missing_oioi C1092MPAIO_*, north_cover C1092MAIS_NORTH_COVER,     *)
(* ordinary_or_inward C1092MANO_ORDINARY_OR_INWARD.  Tag C1092MAIR_.         *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualInwardMissingEnds.ml";;
needs "n12/geometry/CP_C1092_MPPMActualInwardFar.ml";;
needs "n12/geometry/CP_C1092_MPPMActualInwardOIOI.ml";;

let C1092MAIR_BASE = Printf.sprintf "%s /\\ %s" C1092AE_HYP C1092MPPE_CTX;;
let C1092MAIR_INW = Printf.sprintf "%s /\\ c1092mcc_inward %s /\\ ~c1092mcc_ordinary %s"
  C1092MAIR_BASE C1092MCC_OWN4 C1092MCC_OWN4;;
let C1092MAIR_D4 = c1092mpapo_d4 "";;
let C1092MAIR_D5 = C1092MAIR_D4 @ [`l:real`];;

(* C's sign from canonical_frame + centered_sign: Normal C.c (-C.s) *)
let C1092MAIR_NEG_NORMAL_TAC =
  SUBGOAL_THEN `c977cc_normal cC (--sC)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
    MAP_EVERY UNDISCH_TAC [`sC < &0`; `abs sC <= cC`; `cC * cC + sC * sC = &1`] THEN REAL_ARITH_TAC;
    ALL_TAC];;

let c1092mair_use th =
  MP_TAC(SPECL C1092MPPE_V th) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC];;

(* the half-turned packing d = halfTurn.pullPacking p with its family and context *)
let C1092MAIR_HALF_TAC =
  c1092mpapo_rot_tac "" 2 THEN
  c1092mpapo_rot_use C1092MPAPO_ROTATION_CONTEXT "" 2 THEN DISCH_TAC;;

(* apply th (a statement about a packing d1 d2 e1 e2 l) to d, translating owner 4 of d *)
let c1092mair_half_use th =
  MP_TAC(SPECL C1092MAIR_D5 th) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[c1092mcc_inward; c1092mcc_ordinary] THEN
  c1092mpapo_pull_tac C1092MAIR_D4 `(false,true,true)` [4] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mais_northInward; c1092mais_northOrdinary]) THEN
  ASM_REWRITE_TAC[];;

(* Lean: opposite_nonordinary *)
let C1092MAIR_OPPOSITE_NONORDINARY = prove
 (parse_term (Printf.sprintf "!%s. %s ==> ~c1092mais_northOrdinary %s" C1092AE_P C1092MAIR_INW C1092AE_P),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c1092mais_northOrdinary] THEN STRIP_TAC THEN
  ASM_CASES_TAC (parse_term (c1092mpais_in 4 "&2" "&2")) THENL
   [c1092mpaif_canon_tac 4 "C" THEN
    MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIP_CENTERED_SIGN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092MAIR_NEG_NORMAL_TAC THEN
    MATCH_MP_TAC (SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIF_CENTERED_FAR) THEN
    ASM_REWRITE_TAC[];
    c1092mair_use C1092MAIME_MISSING_CENTER_OUTER THEN
    MATCH_MP_TAC (SPECL C1092MPPE_V C1092MPAIF_MISSING_OUTER_FAR) THEN
    ASM_REWRITE_TAC[]]);;

(* Lean: opposite_inward *)
let C1092MAIR_OPPOSITE_INWARD = prove
 (parse_term (Printf.sprintf "!%s. %s ==> c1092mais_northInward %s" C1092AE_P C1092MAIR_INW C1092AE_P),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpai_use C1092MAIS_NORTH_COVER THEN
  MP_TAC(SPECL C1092MPPE_V C1092MAIR_OPPOSITE_NONORDINARY) THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[]);;

(* Lean: north_missing_outer *)
let C1092MAIR_NORTH_MISSING_OUTER = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ c1092mais_northInward %s /\\ ~c1092mais_northOrdinary %s /\\ ~%s ==> %s"
    C1092AE_P C1092MAIR_BASE C1092AE_P C1092AE_P (c1092mpais_in 6 "&2" "&2") (c1092mpais_in 6 "&3" "&12 / &5")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MAIR_HALF_TAC THEN
  c1092mair_half_use C1092MAIME_MISSING_CENTER_OUTER);;

let C1092MAIR_CENTER = c1092mpais_in 4 "&2" "&2";;

(* Lean: centered_nonordinary_impossible *)
let C1092MAIR_CENTERED_NONORDINARY_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> F" C1092AE_P C1092MAIR_INW C1092MAIR_CENTER),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mair_use C1092MAIR_OPPOSITE_INWARD THEN
  c1092mair_use C1092MAIR_OPPOSITE_NONORDINARY THEN
  SUBGOAL_THEN (mk_neg (parse_term (c1092mpais_in 6 "&2" "&2"))) ASSUME_TAC THENL
   [MP_TAC(SPECL (C1092MPPE_V @ [`4`; `6`]) C1092WC_OWNERS_DISJOINT) THEN
    ASM_REWRITE_TAC[ldisj; ARITH] THEN
    DISCH_THEN(MP_TAC o SPECL [`&2`; `&2`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  c1092mair_use C1092MAIR_NORTH_MISSING_OUTER THEN
  c1092mpaif_canon_tac 4 "C" THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIP_CENTERED_SIGN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092MAIR_NEG_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mais_northInward; c1092mais_northOrdinary]) THEN
  MATCH_MP_TAC (SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIO_CENTERED_OIOI) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: nonordinary_impossible *)
let C1092MAIR_NONORDINARY_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s. %s ==> F" C1092AE_P C1092MAIR_INW),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC (parse_term C1092MAIR_CENTER) THENL
   [MATCH_MP_TAC (SPECL C1092MPPE_V C1092MAIR_CENTERED_NONORDINARY_IMPOSSIBLE) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  c1092mair_use C1092MAIME_MISSING_CENTER_OUTER THEN
  c1092mair_use C1092MAIR_OPPOSITE_INWARD THEN
  c1092mair_use C1092MAIR_OPPOSITE_NONORDINARY THEN
  ASM_CASES_TAC (parse_term (c1092mpais_in 6 "&2" "&2")) THENL
   [C1092MAIR_HALF_TAC THEN
    c1092mair_half_use C1092MAIR_CENTERED_NONORDINARY_IMPOSSIBLE;
    c1092mair_use C1092MAIR_NORTH_MISSING_OUTER THEN
    RULE_ASSUM_TAC(REWRITE_RULE[c1092mais_northInward; c1092mais_northOrdinary]) THEN
    MATCH_MP_TAC (SPECL C1092MPPE_V C1092MPAIO_OPPOSED_MISSING_OIOI) THEN
    ASM_REWRITE_TAC[]]);;

(* Lean: southwest_ordinary *)
let C1092MAIR_SOUTHWEST_ORDINARY = prove
 (parse_term (Printf.sprintf "!%s. %s ==> c1092mcc_ordinary %s" C1092AE_P C1092MAIR_BASE C1092MCC_OWN4),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REFUTE_THEN ASSUME_TAC THEN
  c1092mpai_use C1092MANO_ORDINARY_OR_INWARD THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL C1092MPPE_V C1092MAIR_NONORDINARY_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]);;

(* Lean: ordinary *)
let C1092MAIR_ORDINARY = prove
 (parse_term (Printf.sprintf "!%s. %s ==> c1092mpapo_ordinary %s" C1092AE_P C1092MAIR_BASE C1092AE_P),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpai_use C1092MAIR_SOUTHWEST_ORDINARY THEN REWRITE_TAC[c1092mcc_ordinary] THEN STRIP_TAC THEN
  MAP_EVERY (fun i ->
    let k = string_of_int i in
    let d4 = c1092mpapo_d4 k in
    c1092mpapo_rot_tac k i THEN
    c1092mpapo_rot_use C1092MPAPO_ROTATION_CONTEXT k i THEN DISCH_TAC THEN
    MP_TAC(SPECL (d4 @ [`l:real`]) C1092MAIR_SOUTHWEST_ORDINARY) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[c1092mcc_ordinary] THEN
    c1092mpapo_pull_tac d4 (el i C1092MPAPO_ROTS) [4] THEN STRIP_TAC) [1; 2; 3] THEN
  REWRITE_TAC[c1092mpapo_ordinary] THEN ASM_REWRITE_TAC[]);;
