(* ========================================================================= *)
(* Port of Compact/Bridge/C977NextBottomWall.lean                            *)
(* (N12Compact.C977NextBottomWall).  The actual bottom wall and southeast    *)
(* pair exclude a shallow negative bottom singleton in C977.  (Lean header:  *)
(* "Source only, uncompiled"; the statements are proved here as written.)    *)
(* Conventions of C977PositiveWallOwnedWest.ml / SwapReduction.ml:           *)
(* p.square (orderedOwner p i) is c977wc_sq i; transposePacking p is the     *)
(* packing (c2, c1, b, a, l) (C977SR_TRANSPOSE_FAMILY, C977SR_TRANSPOSE_INSIDE);*)
(* an OpenSquare D is cD sD uD vD aD with unit normal and positive side;     *)
(* swapFrame D is (cD, --sD, vD, uD, aD) (CCPI_INSIDE_SWAPFRAME).            *)
(* NegativeBottomNextWall / NegativeBottomInnerWall .impossible: NBNW_ /     *)
(* NBIW_IMPOSSIBLE; ClosedFrames.canonical_frame: CLF_CANONICAL_FRAME.       *)
(* Tag C977NBW_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/C977PositiveWallOwnedWest.ml";;
needs "n12/geometry/NegativeBottomNextWall.ml";;
needs "n12/geometry/NegativeBottomInnerWall.ml";;
needs "n12/geometry/SwapReduction.ml";;
needs "n12/geometry/CentralCenterPairIncoming.ml";;
needs "n12/geometry/C977CenterIncoming.ml";;

(* Lean: inside_swapFrame (private) *)
let C977NBW_INSIDE_SWAPFRAME = CCPI_INSIDE_SWAPFRAME;;

(* Lean: transposed_wall_owner *)
let C977NBW_TRANSPOSED_WALL_OWNER = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> c977av_ordered_owner c2 c1 b a l 8 = c977av_ordered_owner c1 c2 a b l 9`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP C977SR_TRANSPOSE_FAMILY (C977CI_HYPS ())) THEN STRIP_TAC THEN
  MATCH_MP_TAC OWNMASK_INJ THEN
  MAP_EVERY EXISTS_TAC [`c2:num->real`; `c1:num->real`; `b:num->real`; `a:num->real`; `l:real`] THEN
  REWRITE_TAC[c977av_ordered_owner; OIDX_LT] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN
  GEN_REWRITE_TAC RAND_CONV [C977SR_CODE_RAW] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `9`]
    C977AV_ORDERED_OWNER_CODE) THEN
  MP_TAC(SPECL [`c2:num->real`; `c1:num->real`; `b:num->real`; `a:num->real`; `l:real`; `8`]
    C977AV_ORDERED_OWNER_CODE) THEN
  ASM_REWRITE_TAC[ARITH; C977AV_CODE_EL.(8); C977AV_CODE_EL.(9)] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[C977SR_TRANSPOSE_DIAGONAL; c981cr_diag_mask 8192]);;

(* Lean: apart (private) is C977CRC_APART_AT 0 9 *)

let C977NBW_DHYP = Printf.sprintf
  "%s /\\ cD * cD + sD * sD = &1 /\\ &0 < aD /\\ aD = l /\\
   (!x y. linside cD sD uD vD aD x y <=> linside %s x y)"
  C977WC_HYP (c977wc_sq 9);;

(* Lean: negative_frame_point *)
let C977NBW_NEGATIVE_FRAME_POINT = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l cD sD uD vD aD r. %s /\\ sD = --r /\\ c977cc_normal cD r
      ==> linside cD sD uD vD aD (&2) (&1)" C977NBW_DHYP),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c977cc_normal cD (--sD)` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_NEG_NEG]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `sD = --r`)) THEN
  MP_TAC(MATCH_MP C977SR_TRANSPOSE_FAMILY (C977CI_HYPS ())) THEN STRIP_TAC THEN
  ASSUME_TAC(MP (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977NBW_TRANSPOSED_WALL_OWNER) (C977CI_HYPS ())) THEN
  ONCE_REWRITE_TAC[GSYM C977NBW_INSIDE_SWAPFRAME] THEN
  MATCH_MP_TAC (SPECL [`c2:num->real`; `c1:num->real`; `b:num->real`; `a:num->real`; `l:real`;
                       `cD:real`; `--sD:real`; `vD:real`; `uD:real`; `aD:real`] C977PWOW_FRAME_POINT) THEN
  REPEAT CONJ_TAC THEN FIRST
   [FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `cD * cD + sD * sD = &1` THEN REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[C977NBW_INSIDE_SWAPFRAME] THEN
    REWRITE_TAC[C977SR_TRANSPOSE_INSIDE] THEN ASM_REWRITE_TAC[]]);;

(* Lean: excludes_of_small_bottom *)
let C977NBW_EXCLUDES_OF_SMALL_BOTTOM = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l cO sO uO vO aO t. %s /\\ cO * cO + sO * sO = &1 /\\ &0 < aO /\\
      sO = --t /\\ c977cc_normal cO t /\\ t <= &1 / &5 /\\ aO = l /\\
      (!x y. linside cO sO uO vO aO x y <=> linside %s x y) /\\
      ~linside %s (&1) (&1)
      ==> F" C977WC_HYP (c977wc_sq 0) (c977wc_sq 0)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = l`)) THEN
  C977WC_FACTS_TAC 9 THEN
  MP_TAC(SPECL (c977crc_comps 9) CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aD:real = l`)) THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&1) (&457 / &500) /\\ linside %s (&28 / &25) (&1) /\\
     linside %s (&87 / &50) (&1) /\\ linside %s (&187 / &100) (&19 / &25) /\\ lcont %s /\\
     linside %s (&2) (&457 / &500) /\\ ~linside %s (&3) (&457 / &500) /\\ lcont %s"
    (c977wc_sq 0) (c977wc_sq 0) (c977wc_sq 0) (c977wc_sq 0) (c977wc_sq 0)
    (c977wc_sq 9) (c977wc_sq 9) (c977wc_sq 9))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977WC_TO_OO_TAC 0 THEN ACCEPT_TAC(C977WC_INST (oo_seed 1 (`&1`, `&457 / &500`)));
      C977WC_TO_OO_TAC 0 THEN ACCEPT_TAC(C977WC_INST (oo_seed 1 (`&28 / &25`, `&1`)));
      C977WC_TO_OO_TAC 0 THEN ACCEPT_TAC(C977WC_INST (oo_seed 1 (`&87 / &50`, `&1`)));
      C977WC_TO_OO_TAC 0 THEN ACCEPT_TAC(C977WC_INST (oo_seed 1 (`&187 / &100`, `&19 / &25`)));
      C977WC_TO_OO_TAC 0 THEN ASM_SIMP_TAC[OO_BOX];
      C977WC_TO_OO_TAC 9 THEN ACCEPT_TAC(C977WC_INST (oo_seed 8192 (`&2`, `&457 / &500`)));
      C977WC_TO_OO_TAC 9 THEN MP_TAC(C977WC_INST (oo_missing 8192 2)) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      C977WC_TO_OO_TAC 9 THEN ASM_SIMP_TAC[OO_BOX]];
    ALL_TAC] THEN
  ASSUME_TAC(MP (C977CRC_APART_AT 0 9) (C977CI_HYPS ())) THEN
  (* the facts of O and D *)
  SUBGOAL_THEN (parse_term (Printf.sprintf "lcont cO sO uO vO l" )) ASSUME_TAC THENL
   [UNDISCH_TAC (parse_term (Printf.sprintf "lcont %s" (c977wc_sq 0))) THEN
    REWRITE_TAC[lcont] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "lcont cD sD uD vD l" )) ASSUME_TAC THENL
   [UNDISCH_TAC (parse_term (Printf.sprintf "lcont %s" (c977wc_sq 9))) THEN
    REWRITE_TAC[lcont] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ldisj cO sO uO vO l cD sD uD vD l /\
    linside cO sO uO vO l (&1) (&457 / &500) /\ linside cO sO uO vO l (&28 / &25) (&1) /\
    linside cO sO uO vO l (&87 / &50) (&1) /\ linside cO sO uO vO l (&187 / &100) (&19 / &25) /\
    ~linside cO sO uO vO l (&1) (&1) /\
    linside cD sD uD vD l (&2) (&457 / &500) /\ ~linside cD sD uD vD l (&3) (&457 / &500)`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[ldisj] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2]) THEN
  ASM_CASES_TAC `&0 <= sD` THENL
   [MATCH_MP_TAC (SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `l:real`;
                         `cD:real`; `sD:real`; `uD:real`; `vD:real`; `l:real`; `t:real`] NBNW_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `linside cD sD uD vD l (&2) (&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC C977NBW_NEGATIVE_FRAME_POINT THEN
    MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                          `--sD:real`] THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG; c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC (SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `l:real`;
                       `cD:real`; `sD:real`; `uD:real`; `vD:real`; `l:real`; `t:real`; `--sD:real`]
                  NBIW_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG; c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC);;
