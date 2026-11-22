(* ========================================================================= *)
(* Port of Compact/Bridge/C977WallMiddle.lean (N12Compact.C977WallMiddle).   *)
(* The all-angle paired-corner ending forces the actual wall midpoints.      *)
(* Conventions of C977NortheastShift.ml: p.square (orderedOwner p i) is      *)
(* c977wc_sq i, the family q is qc qs qu qv qa with C977CI_QHYP (shape and   *)
(* equivalent for i < 12); canonical (|s| <= c) is stated for i < 12;        *)
(* transposePacking p is (c2, c1, b, a, l).  C977NortheastShift.right_shift_ *)
(* excludes: C977NES_RIGHT_SHIFT_EXCLUDES; CentralRightCornerAlternatives.   *)
(* positive_wall_missing: CRCA_POSITIVE_WALL_MISSING; C977CenterCorner-      *)
(* Alternatives.negative_wall_point: C977CCA_NEGATIVE_WALL_POINT;            *)
(* transpose_family / transpose_inside: C977SR_TRANSPOSE_FAMILY /            *)
(* C977SR_TRANSPOSE_INSIDE; the index identity is c977nes_owner 10.          *)
(* Tag C977WM_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/C977NortheastShift.ml";;
needs "n12/geometry/C977CenterCornerAlternatives.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let C977WM_CANON = "(!i. i < 12 ==> abs (qs i) <= qc i)";;

(* the facts of frame q i *)
let C977WM_Q_TAC i =
  let n = mk_small_numeral i in
  FIRST_ASSUM(fun th -> if is_forall (concl th) && length (fst (strip_forall (concl th))) = 3
    then ASSUME_TAC(REWRITE_RULE[ARITH] (SPEC n th)) else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1 /\ &0 < qa i`) (concl th)
    then STRIP_ASSUME_TAC(REWRITE_RULE[ARITH] (SPEC n th)) else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `forall i. i < 12 ==> qa i = l`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ARITH] (SPEC n th)) else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `forall i. i < 12 ==> abs (qs i) <= qc i`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ARITH] (SPEC n th)) else NO_TAC);;

let C977WM_EQ10 = parse_term (Printf.sprintf
  "!x y. linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) x y <=> linside %s x y" (c977wc_sq 10));;

(* Lean: right_frame_point *)
let C977WM_RIGHT_FRAME_POINT = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\ %s
      ==> linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&2)" C977CI_QHYP C977WM_CANON),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C977WM_Q_TAC 3 THEN C977WM_Q_TAC 10 THEN C977WM_Q_TAC 11 THEN
  ASM_CASES_TAC `&0 <= qs 10` THENL
   [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[ASSUME C977WM_EQ10]) THEN
    SUBGOAL_THEN (parse_term (Printf.sprintf
      "linside %s (&1543 / &500) (&2) /\\ linside %s (&3) (&12 / &5)"
      (c977wc_sq 10) (c977wc_sq 10))) STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [C977CRCH_SEED_TAC 10 16384 (`&1543 / &500`, `&2`); C977CRCH_AUX_TAC 10 19];
      ALL_TAC] THEN
    SUBGOAL_THEN `c977cc_normal (qc 10) (qs 10)` ASSUME_TAC THENL
     [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&3 * qc 10 + &2 * qs 10 <= qu 10` ASSUME_TAC THENL
     [MATCH_MP_TAC CRCA_POSITIVE_WALL_MISSING THEN EXISTS_TAC `(qv:num->real) 10` THEN
      EXISTS_TAC `(qa:num->real) 10` THEN ASM_REWRITE_TAC[ASSUME C977WM_EQ10];
      ALL_TAC] THEN
    MP_TAC(SPECL (C977NES_V5 @ C977NES_QV) C977NES_RIGHT_SHIFT_EXCLUDES) THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL (C977NES_V5 @ [`(qc:num->real) 10`; `(qs:num->real) 10`; `(qu:num->real) 10`;
                  `(qv:num->real) 10`; `(qa:num->real) 10`; `--(qs:num->real) 10`])
      C977CCA_NEGATIVE_WALL_POINT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_NEG_NEG; c977cc_normal; REAL_POW_2; REAL_NEG_MUL2] THEN RASM_ARITH_TAC;
      SIMP_TAC[]]]);;

let C977WM_COMPS_I =
  let w = "(c977av_ordered_owner c1 c2 a b l i)" in
  map parse_term
   [Printf.sprintf "(a:num->real) %s" w; Printf.sprintf "(b:num->real) %s" w;
    Printf.sprintf "a %s * c1 %s + b %s * (c2:num->real) %s - l / &2" w w w w;
    Printf.sprintf "--b %s * c1 %s + a %s * (c2:num->real) %s - l / &2" w w w w; "l:real"];;

(* Lean: right_point *)
let C977WM_RIGHT_POINT = prove
 (parse_term (Printf.sprintf "!c1 c2 a b l. %s ==> linside %s (&3) (&2)" C977WC_HYP (c977wc_sq 10)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "!i. ?c' s' u' v' a'. i < 12 ==>
       c' * c' + s' * s' = &1 /\\ &0 < a' /\\ &0 < c' /\\ abs s' <= c' /\\ a' = l /\\
       (!x y. linside c' s' u' v' a' x y <=> linside %s x y)" (c977pco_sqv "i")))
    MP_TAC THENL
   [X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i < 12` THEN ASM_REWRITE_TAC[EXISTS_SIMP] THEN
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                  `c977av_ordered_owner c1 c2 a b l i`] NPACK_SQ) THEN
    REWRITE_TAC[c977av_ordered_owner; OIDX_LT] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM c977av_ordered_owner] THEN STRIP_TAC THEN
    MP_TAC(SPECL C977WM_COMPS_I CLF_CANONICAL_FRAME) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `qc:num->real` (X_CHOOSE_THEN `qs:num->real` (X_CHOOSE_THEN `qu:num->real`
    (X_CHOOSE_THEN `qv:num->real` (X_CHOOSE_THEN `qa:num->real` ASSUME_TAC))))) THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "%s /\\ %s" C977CI_QHYP C977WM_CANON)) MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP C977WM_RIGHT_FRAME_POINT th)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `10`) THEN REWRITE_TAC[ARITH] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* Lean: top_point *)
let C977WM_TOP_POINT = prove
 (parse_term (Printf.sprintf "!c1 c2 a b l. %s ==> linside %s (&2) (&3)" C977WC_HYP (c977wc_sq 11)),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C977WM_RIGHT_POINT o MATCH_MP C977SR_TRANSPOSE_FAMILY) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP (c977nes_owner 10) th]) THEN
  REWRITE_TAC[C977SR_TRANSPOSE_INSIDE]);;
