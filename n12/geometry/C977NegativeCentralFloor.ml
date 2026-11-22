(* ========================================================================= *)
(* Port of Compact/Bridge/C977NegativeCentralFloor.lean                      *)
(* (N12Compact.C977NegativeCentralFloor).  The actual farther bottom-wall    *)
(* point forces the lower V face of the negative southeast central square.   *)
(* Conventions of C977SignedCentralCorner.ml / C977CenterIncoming.ml: the    *)
(* family q is qc qs qu qv qa with C977CI_QHYP and C977CI_CANON;             *)
(* p.square (orderedOwner p i) is c977wc_sq i; Normal is c977cc_normal.      *)
(* CentralNegativeBottomUpper.lower_face CNBU_LOWER_FACE,                    *)
(* CentralNegativeIncomingBottom.lower_face CNIB_LOWER_FACE, normal_bounds   *)
(* C977CC_NORMAL_BOUNDS, strict_bounds ABT_STRICT_BOUNDS, negative_bands     *)
(* C977NCO_NEGATIVE_BANDS (unfolded linside).  Tag C977NCF_.                 *)
(* ========================================================================= *)

needs "n12/geometry/C977SignedCentralCorner.ml";;
needs "n12/geometry/C977OuterWings.ml";;
needs "n12/geometry/CentralNegativeBottomUpper.ml";;
needs "n12/geometry/CentralNegativeIncomingBottom.ml";;

let C977NCF_Q6 = [`(qc:num->real) 6`; `--t`; `(qu:num->real) 6`; `(qv:num->real) 6`; `l:real`];;

(* the own-axis branch (after the setup and qs 6 = --t) *)
let C977NCF_OWN_TAC =
  ASM_CASES_TAC `&0 <= (qs:num->real) 5` THENL
   [C977SCC_NORMAL_TAC 5 false `&0 <= (qs:num->real) 5` THEN
    MATCH_MP_TAC (SPECL (C977NCF_Q6 @ [`t:real`; `(qc:num->real) 5`; `(qs:num->real) 5`]) CNBU_LOWER_FACE) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `&1 < l` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC C977SCC_STRICT THEN
      MAP_EVERY EXISTS_TAC [`(qu:num->real) 5`; `(qv:num->real) 5`; `l:real`] THEN ASM_REWRITE_TAC[]];
    C977SCC_NORMAL_TAC 5 true `~(&0 <= (qs:num->real) 5)` THEN
    MATCH_MP_TAC (SPECL (C977NCF_Q6 @ [`t:real`; `(qc:num->real) 5`; `--((qs:num->real) 5)`]) CNIB_LOWER_FACE) THEN
    REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `&1 < l` THEN REAL_ARITH_TAC;
      MP_TAC(SPECL (c977ci_ql 5 @ [list_mk_comb(`ABT_lower`, C977NCF_Q6 @ [`(qc:num->real) 5`; `(qs:num->real) 5`])])
        C977SCC_STRICT_LOW) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]];;

(* the neighboring-axis branch *)
let C977NCF_NEIGHBOR_TAC =
  MP_TAC(SPECL [`(qc:num->real) 6`; `t:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (c977ci_ql 5 @ [`&2`; `&3 / &2`; `(qc:num->real) 6`; `--t`]) ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c977cc_normal ((qc:num->real) 6) t` THEN
    REWRITE_TAC[c977cc_normal; REAL_POW_NEG; ARITH] THEN SIMP_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `~((qu:num->real) 6 + l <= (&13 / &5) * qc 6 - t)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(&3 / &5) * (qc:num->real) 6 + t / &2 <= &1` ASSUME_TAC THENL
     [UNDISCH_TAC `c977cc_normal ((qc:num->real) 6) t` THEN REWRITE_TAC[c977cc_normal] THEN
      STRIP_TAC THEN NLIN_TAC [SQ_NONNEG `(qc:num->real) 6 - &3 / &5`; SQ_NONNEG `t - &1 / &2`];
      ALL_TAC] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~linside ((qc:num->real) 6) (--t) ((qu:num->real) 6) ((qv:num->real) 6) l (&13 / &5) (&1)` THEN
  REWRITE_TAC[] THEN
  UNDISCH_TAC `linside ((qc:num->real) 6) (--t) ((qu:num->real) 6) ((qv:num->real) 6) l (&47 / &20) (&33 / &20)` THEN
  UNDISCH_TAC `c977cc_normal ((qc:num->real) 6) t` THEN
  UNDISCH_TAC `&7 / &10 <= (qc:num->real) 6` THEN
  UNDISCH_TAC `~((qu:num->real) 6 + l <= (&13 / &5) * qc 6 - t)` THEN
  UNDISCH_TAC `(qv:num->real) 6 < qc 6 + &13 / &5 * t` THEN
  REWRITE_TAC[linside; c977cc_normal] THEN REAL_ARITH_TAC;;

(* Lean: frame_floor *)
let C977NCF_FRAME_FLOOR = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa t. %s /\\ %s /\\
      qs 6 = --t /\\ c977cc_normal (qc 6) t /\\
      ~linside %s (&1) (&1) /\\ linside %s (&2) (&2)
      ==> qc 6 + (&13 / &5) * t <= qv 6"
   C977CI_QHYP C977CI_CANON (c977wc_sq 0) (c977wc_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CI_INST_TAC [5; 6; 10] THEN
  MP_TAC(SPECL C977SCC_VQ C977CI_FRAME_COVER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  MP_TAC(SPECL C977SCC_V5 C977OW_POINTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C977SCC_SETUP_TAC THEN
  C977SCC_Q_TAC 6 [false, `&3`, `&8 / &5`] THEN
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
  C977SCC_DISJ_TAC (fun t -> c977scc_has "ABT_lower" (lhand t)) THENL
   [C977NCF_OWN_TAC; ALL_TAC] THEN
  C977SCC_DISJ_TAC (fun t -> c977scc_has "ABT_upper" (lhand t)) THENL
   [C977NCF_NEIGHBOR_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) &&
    c977scc_has "ABT_lower" (concl th) && not (is_forall (concl th)))) THEN
  UNDISCH_TAC `&3 * (qc:num->real) 6 < &7 * --t` THEN UNDISCH_TAC `&0 < (qc:num->real) 6` THEN
  UNDISCH_TAC `c977cc_normal ((qc:num->real) 6) t` THEN REWRITE_TAC[c977cc_normal] THEN
  REAL_ARITH_TAC);;
