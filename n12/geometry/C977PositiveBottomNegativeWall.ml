(* ========================================================================= *)
(* Port of Compact/Bridge/C977PositiveBottomNegativeWall.lean                *)
(* (N12Compact.C977PositiveBottomNegativeWall).  The original positive       *)
(* singleton / nonpositive bottom-wall branch is excluded (Lean header:      *)
(* "Source only; no Lean replay has run").  Conventions and setup tactics of *)
(* C977NegativeBottomNegativeWall.ml (C977NBNW_SETUP_TAC: q facts of slots   *)
(* 0, 6, 9, caps, separations).  PositiveBottomNegativeWallClosure.impossible*)
(* is PBNWCL_IMPOSSIBLE.  Tag C977PBNW_.                                     *)
(* ========================================================================= *)

needs "n12/geometry/C977NegativeBottomNegativeWall.ml";;
needs "n12/geometry/PositiveBottomNegativeWallClosure.ml";;

(* Lean: frame_excludes *)
let C977PBNW_FRAME_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa r t. %s /\\ %s /\\
      c977cc_normal (qc 0) (qs 0) /\\
      qs 9 = --r /\\ c977cc_normal (qc 9) r /\\ qs 6 = --t /\\ c977cc_normal (qc 6) t /\\
      ~linside %s (&1) (&1) /\\ linside %s (&2) (&2)
      ==> F"
   C977CI_QHYP C977CI_CANON (c977wc_sq 0) (c977wc_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977NBNW_SETUP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(qs:num->real) 6 = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(qs:num->real) 9 = --r`)) THEN
  C977NBNW_CAPV_TAC THEN
  MATCH_MP_TAC (SPECL [`(qc:num->real) 0`; `(qs:num->real) 0`; `(qu:num->real) 0`; `(qv:num->real) 0`; `l:real`;
                       `(qc:num->real) 9`; `--r`; `(qu:num->real) 9`; `(qv:num->real) 9`; `l:real`;
                       `(qc:num->real) 6`; `--t`; `(qu:num->real) 6`; `(qv:num->real) 6`; `l:real`;
                       `r:real`; `t:real`] PBNWCL_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: wall_positive *)
let C977PBNW_WALL_POSITIVE = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa t. %s /\\ %s /\\
      c977cc_normal (qc 0) (qs 0) /\\ qs 6 = --t /\\ c977cc_normal (qc 6) t /\\
      ~linside %s (&1) (&1) /\\ linside %s (&2) (&2)
      ==> &0 < qs 9"
   C977CI_QHYP C977CI_CANON (c977wc_sq 0) (c977wc_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C977CI_INST_TAC [9] THEN
  MATCH_MP_TAC (SPECL (C977SCC_VQ @ [`--((qs:num->real) 9)`; `t:real`]) C977PBNW_FRAME_EXCLUDES) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG; c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `abs ((qs:num->real) 9) <= qc 9` THEN UNDISCH_TAC `(qs:num->real) 9 <= &0` THEN
  REAL_ARITH_TAC);;
