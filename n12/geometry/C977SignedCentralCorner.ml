(* ========================================================================= *)
(* Port of Compact/Bridge/C977SignedCentralCorner.lean                       *)
(* (N12Compact.C977SignedCentralCorner).  The original missing-bottom-corner *)
(* root forces the genuine negative southeast cap for every signed central   *)
(* frame.  Conventions of C977CenterIncoming.ml / C977CenterCornerAlternatives*)
(* .ml: p.square (orderedOwner p i) is c977wc_sq i; the family q is          *)
(* qc qs qu qv qa with C977CI_QHYP and C977CI_CANON; Normal is c977cc_normal; *)
(* upper / lower are ABT_upper / ABT_lower.  Used: C977CI_FRAME_COVER,       *)
(* C977CCA_ORDERED_AXIS_ALTERNATIVES, C977CCA_ALL_FRAME_ALTERNATIVES,        *)
(* CRCA_CANONICAL_CORNER_FACES, CBTR_INWARD_CAP, CBTR_POINT, CSBR_IMPOSSIBLE,*)
(* CSBR_NEGATIVE_IMPOSSIBLE, CNI_LOWER_BOUND, ABT_STRICT_BOUNDS,             *)
(* C977BER_POINT (BottomExtendedReach.point), C977WM_RIGHT_POINT,            *)
(* C977RCS_SOUTHEAST_CORNER; the pruned-domain point dLow of slot 9 is       *)
(* C977WC_BOTTOM_AUXILIARY.  Tag C977SCC_.                                   *)
(* ========================================================================= *)

needs "n12/geometry/C977CenterIncoming.ml";;
needs "n12/geometry/C977CenterCornerAlternatives.ml";;
needs "n12/geometry/C977BottomExtendedReach.ml";;
needs "n12/geometry/C977WallMiddle.ml";;
needs "n12/geometry/CentralBottomTransverse.ml";;
needs "n12/geometry/CentralNegativeIncoming.ml";;
needs "n12/geometry/CentralSteeperBottomReach.ml";;

let C977SCC_V5 = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let C977SCC_VQ = C977SCC_V5 @ [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`];;

(* noShift (local fact) *)
let C977SCC_NO_SHIFT = prove
 (`forall c s u v a. linside c s u v a (&3) (&2) /\ &0 <= s /\ &3 * c + &2 * s <= u ==> false`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* positiveFloor (local fact) *)
let C977SCC_POSITIVE_FLOOR = prove
 (`forall c s u v a. c977cc_normal c s /\ abs s <= c /\
     linside c s u v a (&47 / &20) (&33 / &20) /\ linside c s u v a (&3) (&87 / &50) /\
     ~linside c s u v a (&3) (&1)
     ==> c - &3 * s <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CRCA_CANONICAL_CORNER_FACES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `linside c s u v a (&3) (&87 / &50)` THEN UNDISCH_TAC `c977cc_normal c s` THEN
  UNDISCH_TAC `u + a <= &3 * c + s` THEN REWRITE_TAC[linside; c977cc_normal] THEN REAL_ARITH_TAC);;

(* the strict bounds of the center square from its points and an axis cap *)
let C977SCC_STRICT = prove
 (`forall c s u v a L. linside c s u v a (&2) (&2) /\ u + a <= L ==> &2 * (c + s) < L`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
let C977SCC_STRICT_LOW = prove
 (`forall c s u v a L. linside c s u v a (&2) (&3 / &2) /\ u + a <= L ==> &2 * c + (&3 / &2) * s < L`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* q i point facts from the original ones via the equivalence (after C977CI_SUBST_TAC) *)
let C977SCC_Q_TAC i pts =
  SUBGOAL_THEN (list_mk_conj (map (fun (neg, x, y) ->
      let t = list_mk_comb(`linside`, c977ci_ql i @ [x; y]) in if neg then mk_neg t else t) pts))
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC];;

(* all original-square facts, substitution of the sides, and their q versions *)
let C977SCC_SETUP_TAC =
  C977CI_FACTS_TAC THEN C977CCA_MISSING_TAC THEN
  MP_TAC(SPECL C977SCC_V5 C977WM_RIGHT_POINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL C977SCC_V5 C977WC_BOTTOM_AUXILIARY) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL C977SCC_V5 C977BER_POINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASSUME_TAC(C977CI_LDISJ 6 9) THEN ASSUME_TAC(C977CI_LDISJ 6 10) THEN
  C977CI_SUBST_TAC THEN
  C977SCC_Q_TAC 6 [false, `&47 / &20`, `&33 / &20`; false, `&3`, `&87 / &50`; true, `&3`, `&1`;
                   true, `&3`, `&2`; true, `&12 / &5`, `&1`; true, `&13 / &5`, `&1`] THEN
  C977SCC_Q_TAC 5 [false, `&2`, `&2`; false, `&2`, `&3 / &2`] THEN
  C977SCC_Q_TAC 10 [false, `&3`, `&2`];;

(* c977cc_normal (qc i) (+-qs i) from canonical, the sign and the unit normal *)
let C977SCC_NORMAL_TAC i neg sign =
  let n = mk_small_numeral i in
  let s = mk_comb(`qs:num->real`, n) and c = mk_comb(`qc:num->real`, n) in
  SUBGOAL_THEN (list_mk_comb(`c977cc_normal`, [c; if neg then mk_comb(`(--):real->real`, s) else s]))
    ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC (mk_binop `(<=):real->real->bool` (mk_comb(`abs:real->real`, s)) c) THEN
    UNDISCH_TAC sign THEN REAL_ARITH_TAC;
    ALL_TAC];;

let C977SCC_DISJ_TAC f =
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj (concl th) && f (concl th)));;

let c977scc_has name tm = can (find_term (fun t -> is_const t && fst (dest_const t) = name)) tm;;

(* the three incoming alternatives of frame_cover *)
let C977SCC_OWN_TAC =
    ASM_CASES_TAC `&0 <= (qs:num->real) 5 * qc 6 - (qc:num->real) 5 * qs 6` THENL
     [MP_TAC(SPECL C977SCC_VQ C977CCA_ORDERED_AXIS_ALTERNATIVES) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      C977SCC_DISJ_TAC (fun t -> true) THEN ASM_REWRITE_TAC[] THEN
      C977SCC_SETUP_TAC THEN MATCH_MP_TAC(TAUT `false ==> p`) THEN MATCH_MP_TAC C977SCC_NO_SHIFT THEN
      MAP_EVERY EXISTS_TAC (c977ci_ql 10) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    C977SCC_SETUP_TAC THEN
    ASM_CASES_TAC `&0 <= (qs:num->real) 6` THENL
     [C977SCC_NORMAL_TAC 6 false `&0 <= (qs:num->real) 6` THEN
      MP_TAC(SPECL (c977ci_ql 6) C977SCC_POSITIVE_FLOOR) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      MP_TAC(SPECL (c977ci_ql 6) CBTR_INWARD_CAP) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      MATCH_MP_TAC(TAUT `false ==> p`) THEN
      ASM_CASES_TAC `&0 <= (qs:num->real) 5` THENL
       [C977SCC_NORMAL_TAC 5 false `&0 <= (qs:num->real) 5` THEN
        MATCH_MP_TAC (SPECL (c977ci_ql 6 @ [`(qc:num->real) 5`; `(qs:num->real) 5`]) CSBR_IMPOSSIBLE) THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [UNDISCH_TAC `~(&0 <= (qs:num->real) 5 * qc 6 - (qc:num->real) 5 * qs 6)`  THEN REAL_ARITH_TAC;
          MATCH_MP_TAC C977SCC_STRICT THEN
          MAP_EVERY EXISTS_TAC [`(qu:num->real) 5`; `(qv:num->real) 5`; `l:real`] THEN ASM_REWRITE_TAC[]];
        C977SCC_NORMAL_TAC 5 true `~(&0 <= (qs:num->real) 5)` THEN
        MATCH_MP_TAC (SPECL (c977ci_ql 6 @ [`(qc:num->real) 5`; `(qs:num->real) 5`]) CSBR_NEGATIVE_IMPOSSIBLE) THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC C977SCC_STRICT_LOW THEN
          MAP_EVERY EXISTS_TAC [`(qu:num->real) 5`; `(qv:num->real) 5`; `l:real`] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(SPECL (c977ci_ql 6) CRCA_CANONICAL_CORNER_FACES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(&0 <= (qs:num->real) 6)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `false ==> p`) THEN
    SUBGOAL_THEN `(qs:num->real) 5 < &0` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`(qs:num->real) 5`; `(qc:num->real) 6`] REAL_LE_MUL) THEN
      MP_TAC(SPECL [`(qc:num->real) 5`; `--((qs:num->real) 6)`] REAL_LT_MUL) THEN
      UNDISCH_TAC `~(&0 <= (qs:num->real) 5 * qc 6 - (qc:num->real) 5 * qs 6)` THEN
      UNDISCH_TAC `~(&0 <= (qs:num->real) 6)` THEN
      UNDISCH_TAC `&0 < (qc:num->real) 5` THEN UNDISCH_TAC `&0 < (qc:num->real) 6` THEN
      UNDISCH_TAC `&0 <= (qs:num->real) 5` THEN
      REWRITE_TAC[REAL_MUL_RNEG] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    C977SCC_NORMAL_TAC 5 true `(qs:num->real) 5 < &0` THEN
    C977SCC_NORMAL_TAC 6 true `~(&0 <= (qs:num->real) 6)` THEN
    MP_TAC(SPECL (c977ci_ql 6) CBTR_INWARD_CAP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(SPECL (c977ci_ql 6 @ [`--((qs:num->real) 6)`; `(qc:num->real) 5`; `--((qs:num->real) 5)`])
      CNI_LOWER_BOUND) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `&1 < l` THEN REAL_ARITH_TAC;
        UNDISCH_TAC `~(&0 <= (qs:num->real) 5 * qc 6 - (qc:num->real) 5 * qs 6)` THEN REAL_ARITH_TAC;
        UNDISCH_TAC `(qc:num->real) 6 - &3 * qs 6 <= qv 6` THEN REAL_ARITH_TAC;
        UNDISCH_TAC `(qu:num->real) 6 + l <= &3 * qc 6 + &2 * qs 6` THEN REAL_ARITH_TAC];
      REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC] THEN
    POP_ASSUM MP_TAC THEN
    MP_TAC(SPECL (c977ci_ql 5 @ [list_mk_comb(`ABT_lower`, c977ci_ql 6 @ [`(qc:num->real) 5`; `(qs:num->real) 5`])])
      C977SCC_STRICT_LOW) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;;

let C977SCC_NEIGHBOR_TAC =
    MP_TAC(SPECL C977SCC_VQ C977CCA_ALL_FRAME_ALTERNATIVES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    C977SCC_DISJ_TAC (fun t -> true) THEN ASM_REWRITE_TAC[] THEN
    C977SCC_SETUP_TAC THEN MATCH_MP_TAC(TAUT `false ==> p`) THEN MATCH_MP_TAC C977SCC_NO_SHIFT THEN
    MAP_EVERY EXISTS_TAC (c977ci_ql 10) THEN ASM_REWRITE_TAC[];;

let C977SCC_TRANSVERSE_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) &&
    c977scc_has "ABT_lower" (concl th) && not (is_forall (concl th)))) THEN
  C977SCC_SETUP_TAC THEN
  SUBGOAL_THEN `&0 <= (qs:num->real) 6` ASSUME_TAC THENL
   [UNDISCH_TAC `&3 * (qc:num->real) 6 < &7 * qs 6` THEN UNDISCH_TAC `&0 < (qc:num->real) 6` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  C977SCC_NORMAL_TAC 6 false `&0 <= (qs:num->real) 6` THEN
  MP_TAC(SPECL (c977ci_ql 6) C977SCC_POSITIVE_FLOOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL (c977ci_ql 6) CBTR_INWARD_CAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL (c977ci_ql 5 @ [`&2`; `&3 / &2`; `--((qs:num->real) 6)`; `(qc:num->real) 6`])
    ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    UNDISCH_TAC `(qc:num->real) 6 * qc 6 + qs 6 * qs 6 = &1` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MATCH_MP_TAC(TAUT `false ==> p`) THEN
  UNDISCH_TAC `~linside ((qc:num->real) 6) ((qs:num->real) 6) ((qu:num->real) 6) ((qv:num->real) 6) l (&13 / &5) (&1)` THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC CBTR_POINT THEN ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false [];;

(* Lean: frame_cap *)
let C977SCC_FRAME_CAP = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\ %s /\\
      ~linside %s (&1) (&1) /\\ linside %s (&2) (&2)
      ==> qs 6 < &0 /\\ qu 6 + qa 6 <= &3 * qc 6 + qs 6"
   C977CI_QHYP C977CI_CANON (c977wc_sq 0) (c977wc_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CI_INST_TAC [5; 6; 10] THEN
  MP_TAC(SPECL C977SCC_VQ C977CI_FRAME_COVER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  C977SCC_DISJ_TAC (fun t -> c977scc_has "ABT_lower" (lhand t)) THENL
   [C977SCC_OWN_TAC; ALL_TAC] THEN
  C977SCC_DISJ_TAC (fun t -> c977scc_has "ABT_upper" (lhand t)) THENL
   [C977SCC_NEIGHBOR_TAC; C977SCC_TRANSVERSE_TAC]);;
