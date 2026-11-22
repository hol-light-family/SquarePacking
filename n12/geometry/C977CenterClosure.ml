(* ========================================================================= *)
(* Port of Compact/Bridge/C977CenterClosure.lean (N12Compact.C977CenterClosure)*)
(* The complete original C977 ending (Lean header: "Source only, awaiting    *)
(* Lean replay").  Conventions of C977CenterIncoming.ml: p.square            *)
(* (orderedOwner p i) is c977wc_sq i; the family q is qc qs qu qv qa with    *)
(* C977CI_QHYP and C977CI_CANON; Normal is c977cc_normal.  Used:             *)
(* C977PositiveBottomWallClosure.bottom_excludes C977PBWC_BOTTOM_EXCLUDES,   *)
(* C977NegativeBottomPositiveWall.frame_excludes C977NBPW_FRAME_EXCLUDES,    *)
(* C977NegativeBottomNegativeWall.frame_excludes C977NBNW_FRAME_EXCLUDES,    *)
(* C977SignedCentralCorner.frame_cap C977SCC_FRAME_CAP,                      *)
(* ClosedFrames.canonical_frame CLF_CANONICAL_FRAME (Lean `choose` is        *)
(* SKOLEM_THM), C977SignedEscapeClosure.excludes_case_of_center_ending       *)
(* C977SEC_EXCLUDES_CASE_OF_CENTER_ENDING.  ExcludesCase 977 is              *)
(* excl_case 977; the retained row is 508 (CC_C977_RowIdentity.ml).          *)
(* Tag C977CCL_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/C977NegativeBottomNegativeWall.ml";;
needs "n12/geometry/C977NegativeBottomPositiveWall.ml";;
needs "n12/geometry/C977SignedEscapeClosure.ml";;
needs "n12/geometry/CC_C977_RowIdentity.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: frame_excludes *)
let C977CCL_FRAME_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\ %s /\\
      ~linside %s (&1) (&1) /\\ linside %s (&2) (&2)
      ==> F"
   C977CI_QHYP C977CI_CANON (c977wc_sq 0) (c977wc_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CI_INST_TAC [0; 6; 9] THEN
  ASM_CASES_TAC `&0 <= (qs:num->real) 0` THENL
   [C977SCC_NORMAL_TAC 0 false `&0 <= (qs:num->real) 0` THEN
    MATCH_MP_TAC (SPECL C977SCC_VQ C977PBWC_BOTTOM_EXCLUDES) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  C977SCC_NORMAL_TAC 0 true `~(&0 <= (qs:num->real) 0)` THEN
  MP_TAC(SPECL C977SCC_VQ C977SCC_FRAME_CAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  C977SCC_NORMAL_TAC 6 true `(qs:num->real) 6 < &0` THEN
  ASM_CASES_TAC `&0 <= (qs:num->real) 9` THENL
   [C977SCC_NORMAL_TAC 9 false `&0 <= (qs:num->real) 9` THEN
    MATCH_MP_TAC (SPECL (C977SCC_VQ @ [`--((qs:num->real) 0)`; `--((qs:num->real) 6)`])
      C977NBPW_FRAME_EXCLUDES) THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG];
    C977SCC_NORMAL_TAC 9 true `~(&0 <= (qs:num->real) 9)` THEN
    MATCH_MP_TAC (SPECL (C977SCC_VQ @ [`--((qs:num->real) 0)`; `--((qs:num->real) 9)`; `--((qs:num->real) 6)`])
      C977NBNW_FRAME_EXCLUDES) THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG]]);;

(* the canonical frames of the actual squares (Lean: choose ... canonical_frame) *)
let C977CCL_CANONICAL_FAMILY =
  let sqi = c977pco_sqv "i" in
  let args = snd (strip_comb (parse_term ("linside " ^ sqi ^ " (x:real) (y:real)"))) in
  let tup = [el 0 args; el 1 args; el 2 args; el 3 args; el 4 args] in
  prove
   (parse_term (Printf.sprintf
     "!c1 c2 a b l. %s ==> !i. ?qc qs qu qv qa. i < 12 ==>
        qc * qc + qs * qs = &1 /\\ &0 < qa /\\ &0 < qc /\\ abs qs <= qc /\\ qa = l /\\
        (!x y. linside qc qs qu qv qa x y <=> linside %s x y)"
     C977WC_HYP sqi),
    REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
    ASM_CASES_TAC `i < 12` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                  `c977av_ordered_owner c1 c2 a b l i`] NPACK_SQ) THEN
    REWRITE_TAC[c977av_ordered_owner; OIDX_LT] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM c977av_ordered_owner] THEN STRIP_TAC THEN
    MP_TAC(SPECL tup CLF_CANONICAL_FRAME) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
    MAP_EVERY EXISTS_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
    ASM_REWRITE_TAC[]);;

(* Lean: center_excludes *)
let C977CCL_CENTER_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l. %s /\\ ~linside %s (&1) (&1) /\\ linside %s (&2) (&2) ==> F"
   C977WC_HYP (c977wc_sq 0) (c977wc_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C977SCC_V5 C977CCL_CANONICAL_FAMILY) THEN ASM_REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `qc:num->real` (X_CHOOSE_THEN `qs:num->real` (X_CHOOSE_THEN `qu:num->real`
    (X_CHOOSE_THEN `qv:num->real` (X_CHOOSE_THEN `qa:num->real` ASSUME_TAC))))) THEN
  MATCH_MP_TAC (SPECL C977SCC_VQ C977CCL_FRAME_EXCLUDES) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall (concl th) &&
    can (find_term ((=) `qc:num->real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* Lean: excludes *)
let C977CCL_EXCLUDES = prove
 (`excl_case 977`,
  MATCH_MP_TAC C977SEC_EXCLUDES_CASE_OF_CENTER_ENDING THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL C977SCC_V5 C977CCL_CENTER_EXCLUDES) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> fst (strip_comb (concl th)) = `c977mcp_strengthened`)) THEN
  SIMP_TAC[c977mcp_strengthened; c977cr_mce]);;

(* the assembly form *)
let C977CCL_EXCLUDED_ROW = ri_excluded_row 508 C977CCL_EXCLUDES;;
