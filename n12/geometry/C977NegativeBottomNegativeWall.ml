(* ========================================================================= *)
(* Port of Compact/Bridge/C977NegativeBottomNegativeWall.lean                *)
(* (N12Compact.C977NegativeBottomNegativeWall).  The original nonpositive    *)
(* singleton / nonpositive bottom-wall cell is empty.  Conventions of        *)
(* C977SignedCentralCorner.ml / C977NegativeCentralFarFloor.ml: p.square     *)
(* (orderedOwner p i) is c977wc_sq i; the family q is qc qs qu qv qa with    *)
(* C977CI_QHYP and C977CI_CANON; Normal is c977cc_normal.  Used:             *)
(* NegativeBottomNegativeWallClosure.impossible NBNWCL_IMPOSSIBLE,           *)
(* NegativeBottomNextAxes.marker_escape NBNA_MARKER_ESCAPE,                  *)
(* C977NegativeCorner.corner_face C977NCO_CORNER_FACE,                       *)
(* C977NextBottomWall.excludes_of_small_bottom / negative_frame_point,       *)
(* C977BottomNegativeExtendedReach.frame_point, C977SignedCentralCorner.     *)
(* frame_cap, C977NegativeCentralFarFloor.frame_bounds, C977OuterWings.points,*)
(* code_one_anchors / code_one_missing_points (C977AN_ / C977MCP_).          *)
(* Tag C977NBNW_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/C977NegativeCentralFarFloor.ml";;
needs "n12/geometry/C977NextBottomWall.ml";;
needs "n12/geometry/NegativeBottomNegativeWallClosure.ml";;
needs "n12/geometry/NegativeBottomNextAxes.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/C977OuterWings.ml";;
needs "n12/geometry/MissingCornerPoints.ml";;

(* original facts of slots 0 and 9 (after C977SCC_SETUP_TAC: it fails on a second &1 < l) *)
let C977NBNW_SLOT0_TAC =
  C977WC_FACTS_TAC 0 THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 0`] C977MCP_CODE_ONE_MISSING_POINTS) THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT; c977mcg_points] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 0`] C977AN_CODE_ONE_ANCHORS) THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT; c977mcg_anchors] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&1) (&457 / &500) /\\ ~linside %s (&2) (&457 / &500) /\\ lcont %s /\\
     linside %s (&2) (&457 / &500) /\\ lcont %s"
    (c977wc_sq 0) (c977wc_sq 0) (c977wc_sq 0) (c977wc_sq 9) (c977wc_sq 9))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977WC_TO_OO_TAC 0 THEN ACCEPT_TAC(C977WC_INST (oo_seed 1 (`&1`, `&457 / &500`)));
      C977WC_TO_OO_TAC 0 THEN MP_TAC(C977WC_INST (oo_missing 1 13)) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      C977WC_TO_OO_TAC 0 THEN ASM_SIMP_TAC[OO_BOX];
      C977WC_TO_OO_TAC 9 THEN ACCEPT_TAC(C977WC_INST (oo_seed 8192 (`&2`, `&457 / &500`)));
      C977WC_TO_OO_TAC 9 THEN ASM_SIMP_TAC[OO_BOX]];
    ALL_TAC] THEN
  ASSUME_TAC(C977CI_LDISJ 0 9);;

(* q versions of original point facts of slot i (after C977CI_SUBST_TAC) *)
let C977NBNW_Q_TAC i pts =
  let ql = c977ci_ql i in
  let goal = list_mk_conj (map (fun (neg, x, y) ->
      let t = list_mk_comb(`linside`, ql @ [x; y]) in if neg then mk_neg t else t) pts) in
  let is_eqv th =
    let c = concl th in
    is_forall c && (let b = snd (strip_forall c) in
      is_iff b && (let l = lhand b in fst (strip_comb l) = `linside` &&
                   butlast (butlast (snd (strip_comb l))) = ql)) in
  SUBGOAL_THEN goal STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eqv th then REWRITE_TAC[th] else NO_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let C977NBNW_LCONT_TAC i =
  SUBGOAL_THEN (list_mk_comb(`lcont`, c977ci_ql i)) ASSUME_TAC THENL
   [UNDISCH_TAC (parse_term (Printf.sprintf "lcont %s" (c977wc_sq i))) THEN
    REWRITE_TAC[lcont] THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let C977NBNW_LDISJ_TAC i j =
  SUBGOAL_THEN (list_mk_comb(`ldisj`, c977ci_ql i @ c977ci_ql j)) ASSUME_TAC THENL
   [REWRITE_TAC[ldisj] THEN ASM_REWRITE_TAC[C977CI_LDISJ i j]; ALL_TAC];;

(* capV of the bottom wall (slot 6), after the substitution qs 6 = --t *)
let C977NBNW_CAPV_TAC =
  SUBGOAL_THEN `(qv:num->real) 6 + l <= &2 * qc 6 + &3 * t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside ((qc:num->real) 6) (--t) ((qu:num->real) 6) ((qv:num->real) 6) l (&3) (&2)` THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `linside ((qc:num->real) 6) (--t) ((qu:num->real) 6) ((qv:num->real) 6) l (&47 / &20) (&33 / &20)` THEN
    UNDISCH_TAC `linside ((qc:num->real) 6) (--t) ((qu:num->real) 6) ((qv:num->real) 6) l (&3) (&8 / &5)` THEN
    UNDISCH_TAC `c977cc_normal ((qc:num->real) 6) t` THEN
    UNDISCH_TAC `&0 < (qc:num->real) 6` THEN
    UNDISCH_TAC `&2 * (qc:num->real) 6 + &3 * t < (qv:num->real) 6 + l` THEN
    REWRITE_TAC[linside; c977cc_normal] THEN REAL_ARITH_TAC;
    ALL_TAC];;

(* common setup of both C977 bottom/negative-wall closers: all facts of the  *)
(* slots 0, 9, 6 as q facts, separations, caps (r t: wall and bottom angles) *)
let C977NBNW_SETUP_TAC =
  C977CI_INST_TAC [0; 5; 6; 9; 10] THEN
  MP_TAC(SPECL C977SCC_VQ C977SCC_FRAME_CAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL (C977SCC_VQ @ [`r:real`; `t:real`]) C977NCFF_FRAME_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL (C977SCC_V5 @ c977ci_qt 9 @ [`r:real`]) C977BNER_FRAME_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL (C977SCC_V5 @ c977ci_qt 9 @ [`r:real`]) C977NBW_NEGATIVE_FRAME_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL C977SCC_V5 C977OW_POINTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C977SCC_SETUP_TAC THEN
  C977NBNW_SLOT0_TAC THEN
  C977NBNW_Q_TAC 0 [false, `&1`, `&457 / &500`; false, `&28 / &25`, `&1`; false, `&87 / &50`, `&1`;
                   false, `&187 / &100`, `&19 / &25`; false, `&49 / &25`, `&19 / &25`;
                   true, `&1`, `&1`; true, `&2`, `&457 / &500`] THEN
  C977NBNW_Q_TAC 6 [false, `&3`, `&8 / &5`] THEN
  C977NBNW_Q_TAC 9 [false, `&2`, `&457 / &500`; false, `&13 / &5`, `&1`] THEN
  C977NBNW_LCONT_TAC 0 THEN C977NBNW_LCONT_TAC 9 THEN
  C977NBNW_LDISJ_TAC 0 9 THEN C977NBNW_LDISJ_TAC 9 6;;

(* Lean: frame_excludes *)
let C977NBNW_FRAME_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa s r t. %s /\\ %s /\\
      qs 0 = --s /\\ c977cc_normal (qc 0) s /\\
      qs 9 = --r /\\ c977cc_normal (qc 9) r /\\ qs 6 = --t /\\ c977cc_normal (qc 6) t /\\
      ~linside %s (&1) (&1) /\\ linside %s (&2) (&2)
      ==> F"
   C977CI_QHYP C977CI_CANON (c977wc_sq 0) (c977wc_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977NBNW_SETUP_TAC THEN
  (* steep: the shallow marker face is excluded by the next bottom wall *)
  MP_TAC(SPECL (c977ci_ql 0 @ [`s:real`]) C977NCO_CORNER_FACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL (c977ci_ql 0 @ [`s:real`]) NBNA_MARKER_ESCAPE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [MATCH_MP_TAC (SPECL (C977SCC_V5 @ c977ci_ql 0 @ [`s:real`]) C977NBW_EXCLUDES_OF_SMALL_BOTTOM) THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(qs:num->real) 6 = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(qs:num->real) 9 = --r`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(qs:num->real) 0 = --s`)) THEN
  C977NBNW_CAPV_TAC THEN
  MATCH_MP_TAC (SPECL [`(qc:num->real) 0`; `--s`; `(qu:num->real) 0`; `(qv:num->real) 0`; `l:real`;
                       `(qc:num->real) 9`; `--r`; `(qu:num->real) 9`; `(qv:num->real) 9`; `l:real`;
                       `(qc:num->real) 6`; `--t`; `(qu:num->real) 6`; `(qv:num->real) 6`; `l:real`;
                       `s:real`; `r:real`; `t:real`] NBNWCL_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC);;
