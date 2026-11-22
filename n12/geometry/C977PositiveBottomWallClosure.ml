(* ========================================================================= *)
(* Port of Compact/Bridge/C977PositiveBottomWallClosure.lean                 *)
(* (N12Compact.C977PositiveBottomWallClosure).  The original positive bottom *)
(* singleton and positive next wall retain only the wall-owned upward        *)
(* separator, which is incompatible with either central orientation (Lean    *)
(* header: "Source only, awaiting Lean replay").  Conventions of             *)
(* C977CenterIncoming.ml / C977NegativeBottomNegativeWall.ml: p.square       *)
(* (orderedOwner p i) is c977wc_sq i; the family q is qc qs qu qv qa with    *)
(* C977CI_QHYP and C977CI_CANON; Normal is c977cc_normal; lower / upper are  *)
(* ABT_lower / ABT_upper.  Used: C696PositiveCorner.corner_faces             *)
(* C696PC_CORNER_FACES, PositiveBottomNextAxes.positive_wall                 *)
(* PBNA_POSITIVE_WALL, CentralNegativeBottomAxes.alternatives                *)
(* CNBA_ALTERNATIVES, PositiveBottomWallCentralAxis.impossible               *)
(* PBWCA_IMPOSSIBLE, CentralNegativePositiveBottom.impossible CNPB_IMPOSSIBLE,*)
(* CentralNegativeSignedPositiveBottom.impossible CNSPB_IMPOSSIBLE,          *)
(* PositiveBottomWallNeighborAxis.impossible PBWNA_IMPOSSIBLE,               *)
(* C977SignedCentralCorner.frame_cap C977SCC_FRAME_CAP, C977CenterIncoming.  *)
(* frame_cover C977CI_FRAME_COVER, C977CentralReach.central_points           *)
(* C977CRE_CENTRAL_POINTS, C977PositiveBottomNegativeWall.wall_positive      *)
(* C977PBNW_WALL_POSITIVE, C977NegativeNeighbor.bottom_positive              *)
(* C977NN_BOTTOM_POSITIVE; the capV argument (negative_bands) is             *)
(* C977NBNW_CAPV_TAC.  Tag C977PBWC_.                                        *)
(* ========================================================================= *)

needs "n12/geometry/C977PositiveBottomNegativeWall.ml";;
needs "n12/geometry/PositiveBottomWallCentralAxis.ml";;
needs "n12/geometry/CentralNegativePositiveBottom.ml";;
needs "n12/geometry/PositiveBottomWallNeighborAxis.ml";;
needs "n12/geometry/CentralNegativeSignedPositiveBottom.ml";;
needs "n12/geometry/C977NegativeNeighbor.ml";;
needs "n12/geometry/C696PositiveCorner.ml";;
needs "n12/geometry/PositiveBottomNextAxes.ml";;
needs "n12/geometry/CentralNegativeBottomAxes.ml";;

let c977pbwc_q6 = [`(qc:num->real) 6`; `--t`; `(qu:num->real) 6`; `(qv:num->real) 6`; `l:real`];;

(* all q facts of the slots 0, 9, 6 (frame_outgoing; needs the missing corner and the center) *)
let C977PBWC_SETUP_TAC =
  C977CI_INST_TAC [0; 5; 6; 9; 10] THEN
  MP_TAC(SPECL C977SCC_VQ C977SCC_FRAME_CAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
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

(* Lean: frame_outgoing *)
let C977PBWC_FRAME_OUTGOING = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa t. %s /\\ %s /\\
      c977cc_normal (qc 0) (qs 0) /\\ c977cc_normal (qc 9) (qs 9) /\\
      qs 6 = --t /\\ c977cc_normal (qc 6) t /\\
      ~linside %s (&1) (&1) /\\ linside %s (&2) (&2)
      ==> qv 6 + qa 6 <= &2 * qc 6 + &3 * t /\\
          qv 9 + qa 9 <= ABT_lower (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (--(qs 9)) (qc 9)"
   C977CI_QHYP C977CI_CANON (c977wc_sq 0) (c977wc_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977PBWC_SETUP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(qs:num->real) 6 = --t`)) THEN
  C977NBNW_CAPV_TAC THEN
  MP_TAC(SPECL (c977ci_ql 0) C696PC_CORNER_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL (c977ci_ql 0 @ c977ci_ql 9) PBNA_POSITIVE_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL (c977ci_ql 9 @ c977pbwc_q6 @ [`t:real`]) CNBA_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun d -> CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    DISJ_CASES_THEN ASSUME_TAC d THENL
     [MATCH_MP_TAC(TAUT `false ==> p`) THEN
      MATCH_MP_TAC (SPECL (c977ci_ql 0 @ c977ci_ql 9 @ c977pbwc_q6 @ [`t:real`]) PBWCA_IMPOSSIBLE) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]]]));;

(* Lean: wall_axis_excludes *)
let C977PBWC_WALL_AXIS_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa t. %s /\\ %s /\\
      c977cc_normal (qc 9) (qs 9) /\\ qs 6 = --t /\\ c977cc_normal (qc 6) t /\\
      linside %s (&2) (&2) /\\
      qv 6 + qa 6 <= &2 * qc 6 + &3 * t /\\
      qv 9 + qa 9 <= ABT_lower (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (--(qs 9)) (qc 9)
      ==> F"
   C977CI_QHYP C977CI_CANON (c977wc_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CI_INST_TAC [5; 6; 9] THEN
  MP_TAC(SPECL C977SCC_VQ C977CI_FRAME_COVER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  MP_TAC(SPECL C977SCC_V5 C977CRE_CENTRAL_POINTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "linside %s (&2) (&457 / &500) /\\ lcont %s"
    (c977wc_sq 9) (c977wc_sq 9))) STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [C977WC_TO_OO_TAC 9 THEN ACCEPT_TAC(C977WC_INST (oo_seed 8192 (`&2`, `&457 / &500`)));
      C977WC_TO_OO_TAC 9 THEN ASM_SIMP_TAC[OO_BOX]];
    ALL_TAC] THEN
  MP_TAC(SPECL C977SCC_V5 OO_SIDE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C977CI_SUBST_TAC THEN
  C977NBNW_Q_TAC 5 [false, `&2`, `&2`; false, `&2`, `&3 / &2`] THEN
  C977NBNW_Q_TAC 9 [false, `&2`, `&457 / &500`] THEN
  C977NBNW_LCONT_TAC 9 THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(qs:num->real) 6 = --t`)) THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th -> is_disj (concl th) &&
    c977scc_has "ABT_lower" (lhand (concl th)))) THENL
   [ASM_CASES_TAC `&0 <= (qs:num->real) 5` THENL
     [C977SCC_NORMAL_TAC 5 false `&0 <= (qs:num->real) 5` THEN
      MATCH_MP_TAC (SPECL (c977ci_ql 9 @ c977pbwc_q6 @ [`t:real`; `(qc:num->real) 5`; `(qs:num->real) 5`])
        CNPB_IMPOSSIBLE) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      FIRST [RASM_ARITH_TAC;
             MATCH_MP_TAC C977SCC_STRICT THEN
             MAP_EVERY EXISTS_TAC [`(qu:num->real) 5`; `(qv:num->real) 5`; `l:real`] THEN ASM_REWRITE_TAC[]];
      C977SCC_NORMAL_TAC 5 true `~(&0 <= (qs:num->real) 5)` THEN
      MATCH_MP_TAC (SPECL (c977ci_ql 9 @ c977pbwc_q6 @ [`t:real`; `(qc:num->real) 5`; `--((qs:num->real) 5)`])
        CNSPB_IMPOSSIBLE) THEN
      ASM_REWRITE_TAC[REAL_NEG_NEG] THEN
      MP_TAC(SPECL (c977ci_ql 5 @ [list_mk_comb(`ABT_lower`, c977pbwc_q6 @ [`(qc:num->real) 5`; `(qs:num->real) 5`])])
        C977SCC_STRICT_LOW) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC (SPECL (c977ci_ql 5 @ c977ci_ql 9 @ c977pbwc_q6 @ [`t:real`]) PBWNA_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
    MP_TAC(ASSUME `c977cc_normal ((qc:num->real) 6) t`) THEN REWRITE_TAC[c977cc_normal] THEN
    STRIP_TAC THEN NLIN_TAC ~deg2:false []]);;

(* Lean: frame_excludes *)
let C977PBWC_FRAME_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa t. %s /\\ %s /\\
      c977cc_normal (qc 0) (qs 0) /\\ c977cc_normal (qc 9) (qs 9) /\\
      qs 6 = --t /\\ c977cc_normal (qc 6) t /\\
      ~linside %s (&1) (&1) /\\ linside %s (&2) (&2)
      ==> F"
   C977CI_QHYP C977CI_CANON (c977wc_sq 0) (c977wc_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C977SCC_VQ @ [`t:real`]) C977PBWC_FRAME_OUTGOING) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC (SPECL (C977SCC_VQ @ [`t:real`]) C977PBWC_WALL_AXIS_EXCLUDES) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: bottom_excludes *)
let C977PBWC_BOTTOM_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\ %s /\\
      c977cc_normal (qc 0) (qs 0) /\\
      ~linside %s (&1) (&1) /\\ linside %s (&2) (&2)
      ==> F"
   C977CI_QHYP C977CI_CANON (c977wc_sq 0) (c977wc_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CI_INST_TAC [6; 9] THEN
  MP_TAC(SPECL C977SCC_VQ C977SCC_FRAME_CAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  C977SCC_NORMAL_TAC 6 true `(qs:num->real) 6 < &0` THEN
  MP_TAC(SPECL (C977SCC_VQ @ [`--((qs:num->real) 6)`]) C977PBNW_WALL_POSITIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_NEG_NEG]; DISCH_TAC] THEN
  C977SCC_NORMAL_TAC 9 false `&0 < (qs:num->real) 9` THEN
  MATCH_MP_TAC (SPECL (C977SCC_VQ @ [`--((qs:num->real) 6)`]) C977PBWC_FRAME_EXCLUDES) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG]);;

(* Lean: positive_central_excludes *)
let C977PBWC_POSITIVE_CENTRAL_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\ %s /\\
      c977cc_normal (qc 5) (qs 5) /\\
      ~linside %s (&1) (&1) /\\ linside %s (&2) (&2)
      ==> F"
   C977CI_QHYP C977CI_CANON (c977wc_sq 0) (c977wc_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CI_INST_TAC [0; 6] THEN
  MP_TAC(SPECL C977SCC_VQ C977SCC_FRAME_CAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  C977SCC_NORMAL_TAC 6 true `(qs:num->real) 6 < &0` THEN
  MP_TAC(SPECL (C977SCC_VQ @ [`--((qs:num->real) 6)`]) C977NN_BOTTOM_POSITIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_NEG_NEG; REAL_SUB_RNEG] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  C977SCC_NORMAL_TAC 0 false `&0 < (qs:num->real) 0` THEN
  MATCH_MP_TAC (SPECL C977SCC_VQ C977PBWC_BOTTOM_EXCLUDES) THEN
  ASM_REWRITE_TAC[]);;
