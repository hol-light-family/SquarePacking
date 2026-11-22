(* ========================================================================= *)
(* Port of Compact/Bridge/C977NegativeNeighbor.lean                          *)
(* (N12Compact.C977NegativeNeighbor).  The remaining negative southeast-     *)
(* central cap in the original C977 family.  Conventions of                  *)
(* C977CenterIncoming.ml: p.square (orderedOwner p i) is c977wc_sq i; the    *)
(* family q : Fin 12 -> OpenSquare is qc qs qu qv qa with C977CI_QHYP (its   *)
(* OpenSquare fields, shape and equivalent) and C977CI_CANON (canonical);    *)
(* Normal is c977cc_normal.  CentralNegativeNeighbor.own_axis / neighbor_axis*)
(* CNN_OWN_AXIS / CNN_NEIGHBOR_AXIS; CentralSteeperNegativeBottom.small_bottom*)
(* CSNB_SMALL_BOTTOM; C977NextBottomWall.excludes_of_small_bottom            *)
(* C977NBW_EXCLUDES_OF_SMALL_BOTTOM; C977CenterIncoming.positive_right_      *)
(* alternatives C977CI_POSITIVE_RIGHT_ALTERNATIVES; C977CenterCaps.frame_caps*)
(* C977CC_FRAME_CAPS; C977OuterWings.points C977OW_POINTS; C977WallMiddle.   *)
(* right_point C977WM_RIGHT_POINT.  The code-one anchors and marker facts of *)
(* slot 0 are the seeds of mask 1 (oo_seed / oo_missing).  Tag C977NN_.      *)
(* ========================================================================= *)

needs "n12/geometry/C977CenterIncoming.ml";;
needs "n12/geometry/C977WallMiddle.ml";;
needs "n12/geometry/C977NextBottomWall.ml";;
needs "n12/geometry/C977OuterWings.ml";;
needs "n12/geometry/CentralNegativeNeighbor.ml";;
needs "n12/geometry/CentralSteeperNegativeBottom.ml";;

let C977NN_V5 = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let C977NN_VQ = C977NN_V5 @ [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`];;

(* q i point facts from the original ones via the equivalence (after C977CI_SUBST_TAC) *)
let C977NN_Q_TAC i pts =
  SUBGOAL_THEN (list_mk_conj (map (fun (neg, x, y) ->
      let t = list_mk_comb(`linside`, c977ci_ql i @ [x; y]) in if neg then mk_neg t else t) pts))
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC];;

(* Lean: frame_sharpen *)
let C977NN_FRAME_SHARPEN = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa t. %s /\\ %s /\\
      c977cc_normal (qc 5) (qs 5) /\\ qs 6 = --t /\\ c977cc_normal (qc 6) t /\\
      linside %s (&2) (&2) /\\ qu 6 + qa 6 <= &3 * qc 6 - t
      ==> qs 5 < &2 / &5 /\\ qu 5 + qa 5 <= &2 * (qc 5 + qs 5) + (&9 / &100) * qc 5"
   C977CI_QHYP C977CI_CANON (c977wc_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C977NN_VQ C977CI_POSITIVE_RIGHT_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  C977CI_INST_TAC [5; 6] THEN
  MP_TAC(SPECL (C977NN_V5 @ c977ci_qt 5) C977CC_FRAME_CAPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  C977CI_FACTS_TAC THEN
  MP_TAC(SPECL C977NN_V5 C977OW_POINTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL C977NN_V5 C977WM_RIGHT_POINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASSUME_TAC(C977CI_LDISJ 6 10) THEN
  C977CI_SUBST_TAC THEN
  C977NN_Q_TAC 6 [false, `&47 / &20`, `&33 / &20`; false, `&3`, `&8 / &5`; true, `&3`, `&2`] THEN
  C977NN_Q_TAC 5 [false, `&2`, `&2`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(qs:num->real) 6 = --t`)) THEN
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
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj (concl th) &&
    can (find_term (fun t -> is_const t && fst (dest_const t) = "ABT_lower")) (concl th))) THENL
   [MATCH_MP_TAC (SPECL (c977ci_ql 5 @ [`(qc:num->real) 6`; `--t`; `(qu:num->real) 6`;
                         `(qv:num->real) 6`; `l:real`; `t:real`]) CNN_OWN_AXIS);
    MATCH_MP_TAC (SPECL (c977ci_ql 5 @ [`(qc:num->real) 6`; `--t`; `(qu:num->real) 6`;
                         `(qv:num->real) 6`; `l:real`; `t:real`]) CNN_NEIGHBOR_AXIS)] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: negative_bottom_excludes *)
let C977NN_NEGATIVE_BOTTOM_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa t r. %s /\\ %s /\\
      c977cc_normal (qc 5) (qs 5) /\\ qs 6 = --t /\\ c977cc_normal (qc 6) t /\\
      qs 0 = --r /\\ c977cc_normal (qc 0) r /\\
      ~linside %s (&1) (&1) /\\ linside %s (&2) (&2) /\\ qu 6 + qa 6 <= &3 * qc 6 - t
      ==> F"
   C977CI_QHYP C977CI_CANON (c977wc_sq 0) (c977wc_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C977NN_VQ @ [`t:real`]) C977NN_FRAME_SHARPEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  C977CI_INST_TAC [0; 5] THEN
  MP_TAC(SPECL (C977NN_V5 @ c977ci_qt 5) C977CC_FRAME_CAPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL C977NN_V5 C977CRE_CENTRAL_DATA) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&1) (&457 / &500) /\\ linside %s (&28 / &25) (&1) /\\
     linside %s (&187 / &100) (&19 / &25) /\\ ~linside %s (&2) (&457 / &500) /\\ lcont %s"
    (c977wc_sq 0) (c977wc_sq 0) (c977wc_sq 0) (c977wc_sq 0) (c977wc_sq 0))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977WC_TO_OO_TAC 0 THEN ACCEPT_TAC(C977WC_INST (oo_seed 1 (`&1`, `&457 / &500`)));
      C977WC_TO_OO_TAC 0 THEN ACCEPT_TAC(C977WC_INST (oo_seed 1 (`&28 / &25`, `&1`)));
      C977WC_TO_OO_TAC 0 THEN ACCEPT_TAC(C977WC_INST (oo_seed 1 (`&187 / &100`, `&19 / &25`)));
      C977WC_TO_OO_TAC 0 THEN MP_TAC(C977WC_INST (oo_missing 1 13)) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      C977WC_TO_OO_TAC 0 THEN ASM_SIMP_TAC[OO_BOX]];
    ALL_TAC] THEN
  MP_TAC(SPECL C977NN_V5 OO_SIDE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASSUME_TAC(C977CI_LDISJ 0 5) THEN
  C977CI_SUBST_TAC THEN
  C977NN_Q_TAC 0 [false, `&1`, `&457 / &500`; false, `&28 / &25`, `&1`;
                  false, `&187 / &100`, `&19 / &25`; true, `&1`, `&1`; true, `&2`, `&457 / &500`] THEN
  C977NN_Q_TAC 5 [false, `&33 / &20`, `&33 / &20`; false, `&2`, `&87 / &50`] THEN
  SUBGOAL_THEN `lcont ((qc:num->real) 0) ((qs:num->real) 0) ((qu:num->real) 0) ((qv:num->real) 0) l /\
                ldisj ((qc:num->real) 0) ((qs:num->real) 0) ((qu:num->real) 0) ((qv:num->real) 0) l
                      ((qc:num->real) 5) ((qs:num->real) 5) ((qu:num->real) 5) ((qv:num->real) 5) l`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[lcont] THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[lcont]) THEN ASM_MESON_TAC[];
      REWRITE_TAC[ldisj] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL (c977ci_ql 0 @ c977ci_ql 5 @ [`r:real`]) CSNB_SMALL_BOTTOM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL (C977NN_V5 @ c977ci_ql 0 @ [`r:real`]) C977NBW_EXCLUDES_OF_SMALL_BOTTOM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[]]);;

(* Lean: bottom_positive *)
let C977NN_BOTTOM_POSITIVE = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa t. %s /\\ %s /\\
      c977cc_normal (qc 5) (qs 5) /\\ qs 6 = --t /\\ c977cc_normal (qc 6) t /\\
      ~linside %s (&1) (&1) /\\ linside %s (&2) (&2) /\\ qu 6 + qa 6 <= &3 * qc 6 - t
      ==> &0 < qs 0"
   C977CI_QHYP C977CI_CANON (c977wc_sq 0) (c977wc_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `c977cc_normal ((qc:num->real) 0) (--((qs:num->real) 0))` ASSUME_TAC THENL
   [C977CI_INST_TAC [0] THEN
    REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs ((qs:num->real) 0) <= qc 0` THEN UNDISCH_TAC `(qs:num->real) 0 <= &0` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL (C977NN_VQ @ [`t:real`; `--((qs:num->real) 0)`]) C977NN_NEGATIVE_BOTTOM_EXCLUDES) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG]);;
