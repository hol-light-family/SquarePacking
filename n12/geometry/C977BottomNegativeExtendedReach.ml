(* ========================================================================= *)
(* Port of Compact/Bridge/C977BottomNegativeExtendedReach.lean               *)
(* (N12Compact.C977BottomNegativeExtendedReach).  Every nonpositive          *)
(* canonical frame D of owner 9 reaches (2.86,1).  Conventions of            *)
(* C977BottomExtendedReach.ml; D = cD sD uD vD aD with explicit unit normal  *)
(* and positive side; swapFrame D is (cD, --sD, vD, uD, aD) with             *)
(* inside_swapFrame = SCT_TRANSPOSE_INSIDE.  WallDiagonalFarReach.point:     *)
(* WDFR_POINT.  Tag C977BNER_.                                               *)
(* ========================================================================= *)

needs "n12/geometry/WallDiagonalFarReach.ml";;
needs "n12/geometry/C977BottomExtendedReach.ml";;
needs "n12/geometry/SouthwestCornerTranspose.ml";;

(* Lean: frame_point *)
let C977BNER_FRAME_POINT = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l cD sD uD vD aD t. %s /\\ cD * cD + sD * sD = &1 /\\ &0 < aD /\\
      sD = --t /\\ c977cc_normal cD t /\\ aD = l /\\
      (!x y. linside cD sD uD vD aD x y <=> linside %s x y) /\\
      ~linside %s (&1) (&1)
      ==> linside cD sD uD vD aD (&143 / &50) (&1)"
   C977WC_HYP (c977wc_sq 9) (c977wc_sq 0)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aD:real = l`)) THEN
  MP_TAC(SPECL [`cD:real`; `--sD`; `vD:real`; `uD:real`; `l:real`] WDFR_POINT) THEN
  REWRITE_TAC[SCT_TRANSPOSE_INSIDE; lcont] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977WC_BOTTOM_AUXILIARY) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977CRE_CENTRAL_POINTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  C977WC_FACTS_TAC 0 THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 0`] C977MCP_CODE_ONE_MISSING_POINTS) THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT; c977mcg_points] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "ldisj %s %s" (c977wc_sq 9) (c977wc_sq 0))) MP_TAC THENL
   [C977WC_LDISJ_TAC 9 0; ALL_TAC] THEN
  REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&49 / &25`; `&19 / &25`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "ldisj %s %s" (c977wc_sq 9) (c977wc_sq 5))) MP_TAC THENL
   [C977WC_LDISJ_TAC 9 5; ALL_TAC] THEN
  REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&2`; `&3 / &2`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C977WC_FACTS_TAC 9 THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "linside %s (&2) (&457 / &500) /\\ lcont %s"
    (c977wc_sq 9) (c977wc_sq 9))) STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C977WC_TO_OO_TAC 9 THENL
     [ACCEPT_TAC(C977WC_INST (oo_seed 8192 (`&2`, `&457 / &500`))); ASM_SIMP_TAC[OO_BOX]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `cD * cD + sD * sD = &1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(SPECL [`y:real`; `x:real`] (REWRITE_RULE[lcont]
      (ASSUME (parse_term (Printf.sprintf "lcont %s" (c977wc_sq 9)))))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;
