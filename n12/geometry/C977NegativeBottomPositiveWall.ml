(* ========================================================================= *)
(* Port of Compact/Bridge/C977NegativeBottomPositiveWall.lean                *)
(* (N12Compact.C977NegativeBottomPositiveWall).  The original negative       *)
(* singleton / positive bottom-wall cell is excluded with both central       *)
(* incoming axes and every central sign kept.  Conventions of                *)
(* C977PositiveBottomWallClosure.ml / C977NegativeBottomNegativeWall.ml:     *)
(* p.square (orderedOwner p i) is c977wc_sq i; q is qc qs qu qv qa with      *)
(* C977CI_QHYP and C977CI_CANON; Normal is c977cc_normal.  Used:             *)
(* C977NegativeCorner.corner_face C977NCO_CORNER_FACE,                       *)
(* NegativeBottomNextAxes.marker_escape / positive_wall NBNA_*,              *)
(* C977NextBottomWall.excludes_of_small_bottom                               *)
(* C977NBW_EXCLUDES_OF_SMALL_BOTTOM, CentralNegativeBottomAxes.alternatives  *)
(* CNBA_ALTERNATIVES, NegativeBottomWallCentralAxis.own_transverse           *)
(* NBWCA_OWN_TRANSVERSE, PositiveBottomWallCentralAxis.                      *)
(* negative_bottom_wall_axis PBWCA_NEGATIVE_BOTTOM_WALL_AXIS,                *)
(* C977PositiveBottomWallClosure.wall_axis_excludes                          *)
(* C977PBWC_WALL_AXIS_EXCLUDES.  Tag C977NBPW_.                              *)
(* ========================================================================= *)

needs "n12/geometry/C977PositiveBottomWallClosure.ml";;
needs "n12/geometry/NegativeBottomNextAxes.ml";;
needs "n12/geometry/NegativeBottomWallCentralAxis.ml";;

(* Lean: frame_excludes *)
let C977NBPW_FRAME_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa s t. %s /\\ %s /\\
      qs 0 = --s /\\ c977cc_normal (qc 0) s /\\ c977cc_normal (qc 9) (qs 9) /\\
      qs 6 = --t /\\ c977cc_normal (qc 6) t /\\
      ~linside %s (&1) (&1) /\\ linside %s (&2) (&2)
      ==> F"
   C977CI_QHYP C977CI_CANON (c977wc_sq 0) (c977wc_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(qv:num->real) 6 + qa 6 <= &2 * qc 6 + &3 * t ==>
                ~((qv:num->real) 9 + qa 9 <= ABT_lower (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (--(qs 9)) (qc 9))`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (SPECL (C977SCC_VQ @ [`t:real`]) C977PBWC_WALL_AXIS_EXCLUDES) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  C977PBWC_SETUP_TAC THEN
  MP_TAC(SPECL (c977ci_ql 0 @ [`s:real`]) C977NCO_CORNER_FACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL (c977ci_ql 0 @ [`s:real`]) NBNA_MARKER_ESCAPE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [MATCH_MP_TAC (SPECL (C977SCC_V5 @ c977ci_ql 0 @ [`s:real`]) C977NBW_EXCLUDES_OF_SMALL_BOTTOM) THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(qs:num->real) 6 = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(qs:num->real) 0 = --s`)) THEN
  C977NBNW_CAPV_TAC THEN
  let q0 = [`(qc:num->real) 0`; `--s`; `(qu:num->real) 0`; `(qv:num->real) 0`; `l:real`] in
  MP_TAC(SPECL (q0 @ c977ci_ql 9 @ [`s:real`]) NBNA_POSITIVE_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL (c977ci_ql 9 @ c977pbwc_q6 @ [`t:real`]) CNBA_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC o check (fun th -> is_disj (concl th) &&
      c977scc_has "ABT_lower" (lhand (concl th)) && c977scc_has "ABT_upper" (rand (concl th)))) THENL
     [MATCH_MP_TAC (SPECL (q0 @ c977ci_ql 9 @ c977pbwc_q6 @ [`s:real`; `t:real`]) NBWCA_OWN_TRANSVERSE) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
      MATCH_MP_TAC (SPECL (q0 @ c977ci_ql 9 @ c977pbwc_q6 @ [`s:real`; `t:real`])
        PBWCA_NEGATIVE_BOTTOM_WALL_AXIS) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC];
    UNDISCH_TAC `(qv:num->real) 6 + l <= &2 * qc 6 + &3 * t ==>
      ~((qv:num->real) 9 + l <= ABT_lower (qc 6) (--t) (qu 6) (qv 6) l (--(qs 9)) (qc 9))` THEN
    ASM_REWRITE_TAC[]]);;
