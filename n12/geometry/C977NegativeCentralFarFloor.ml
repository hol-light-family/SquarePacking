(* ========================================================================= *)
(* Port of Compact/Bridge/C977NegativeCentralFarFloor.lean                   *)
(* (N12Compact.C977NegativeCentralFarFloor).  The farther bottom-wall point  *)
(* sharpens the negative southeast-central floor and bounds its angle.       *)
(* Conventions of C977SignedCentralCorner.ml / C977NegativeCentralFloor.ml   *)
(* (family q = qc qs qu qv qa with C977CI_QHYP, C977CI_CANON).               *)
(* CentralNegativeBottomAxes.alternatives CNBA_ALTERNATIVES,                 *)
(* CentralNegativeFarUpper.impossible CNFU_IMPOSSIBLE,                       *)
(* CentralNegativeFarIncoming.impossible CNFI_IMPOSSIBLE,                    *)
(* C977BottomNegativeExtendedReach.frame_point C977BNER_FRAME_POINT,         *)
(* C977SignedCentralCorner.frame_cap C977SCC_FRAME_CAP,                      *)
(* C977NegativeCentralFloor.frame_floor C977NCF_FRAME_FLOOR.  Tag C977NCFF_. *)
(* ========================================================================= *)

needs "n12/geometry/C977NegativeCentralFloor.ml";;
needs "n12/geometry/C977BottomNegativeExtendedReach.ml";;
needs "n12/geometry/CentralNegativeBottomAxes.ml";;
needs "n12/geometry/CentralNegativeFarUpper.ml";;
needs "n12/geometry/CentralNegativeFarIncoming.ml";;

let C977NCFF_Q9 = [`(qc:num->real) 9`; `--r`; `(qu:num->real) 9`; `(qv:num->real) 9`; `l:real`];;

(* noUpper, own-axis branch *)
let C977NCFF_OWN_TAC =
  ASM_CASES_TAC `&0 <= (qs:num->real) 5` THENL
   [C977SCC_NORMAL_TAC 5 false `&0 <= (qs:num->real) 5` THEN
    MATCH_MP_TAC (SPECL (C977NCFF_Q9 @ C977NCF_Q6 @ [`r:real`; `t:real`; `(qc:num->real) 5`; `(qs:num->real) 5`])
      CNFU_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&1 < l` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC C977SCC_STRICT THEN
      MAP_EVERY EXISTS_TAC [`(qu:num->real) 5`; `(qv:num->real) 5`; `l:real`] THEN ASM_REWRITE_TAC[]];
    C977SCC_NORMAL_TAC 5 true `~(&0 <= (qs:num->real) 5)` THEN
    MATCH_MP_TAC (SPECL (C977NCFF_Q9 @ C977NCF_Q6 @ [`r:real`; `t:real`; `(qc:num->real) 5`; `--((qs:num->real) 5)`])
      CNFI_IMPOSSIBLE) THEN
    REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&1 < l` THEN REAL_ARITH_TAC;
      MP_TAC(SPECL (c977ci_ql 5 @ [list_mk_comb(`ABT_lower`, C977NCF_Q6 @ [`(qc:num->real) 5`; `(qs:num->real) 5`])])
        C977SCC_STRICT_LOW) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]];;

(* noUpper, neighboring-axis branch *)
let C977NCFF_NEIGHBOR_TAC =
  MP_TAC(SPECL (c977ci_ql 5 @ [`&2`; `&3 / &2`; `(qc:num->real) 6`; `--t`]) ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c977cc_normal ((qc:num->real) 6) t` THEN
    REWRITE_TAC[c977cc_normal; REAL_POW_NEG; ARITH] THEN SIMP_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `(&43 / &50) * (qc:num->real) 6 + t / &2 <= &1` ASSUME_TAC THENL
   [UNDISCH_TAC `c977cc_normal ((qc:num->real) 6) t` THEN REWRITE_TAC[c977cc_normal] THEN
    STRIP_TAC THEN NLIN_TAC [SQ_NONNEG `(qc:num->real) 6 - &43 / &50`; SQ_NONNEG `t - &1 / &2`];
    ALL_TAC] THEN
  NLIN_TAC ~deg2:false [];;

(* Lean: frame_bounds *)
let C977NCFF_FRAME_BOUNDS = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa r t. %s /\\ %s /\\
      qs 9 = --r /\\ c977cc_normal (qc 9) r /\\ qs 6 = --t /\\ c977cc_normal (qc 6) t /\\
      ~linside %s (&1) (&1) /\\ linside %s (&2) (&2)
      ==> qc 6 + (&143 / &50) * t <= qv 6 /\\ t < &3 / &10"
   C977CI_QHYP C977CI_CANON (c977wc_sq 0) (c977wc_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CI_INST_TAC [5; 6; 9; 10] THEN
  MP_TAC(SPECL C977SCC_VQ C977SCC_FRAME_CAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL (C977SCC_VQ @ [`t:real`]) C977NCF_FRAME_FLOOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL C977SCC_VQ C977CI_FRAME_COVER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  MP_TAC(SPECL (C977SCC_V5 @ c977ci_qt 9 @ [`r:real`]) C977BNER_FRAME_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL C977SCC_V5 C977OW_POINTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "linside %s (&2) (&457 / &500)" (c977wc_sq 9))) ASSUME_TAC THENL
   [C977WC_TO_OO_TAC 9 THEN ACCEPT_TAC(C977WC_INST (oo_seed 8192 (`&2`, `&457 / &500`))); ALL_TAC] THEN
  ASSUME_TAC(C977CI_LDISJ 9 6) THEN
  C977SCC_SETUP_TAC THEN
  C977SCC_Q_TAC 6 [false, `&3`, `&8 / &5`] THEN
  C977SCC_Q_TAC 9 [false, `&2`, `&457 / &500`; false, `&13 / &5`, `&1`] THEN
  SUBGOAL_THEN `ldisj ((qc:num->real) 9) ((qs:num->real) 9) ((qu:num->real) 9) ((qv:num->real) 9) l
                      ((qc:num->real) 6) ((qs:num->real) 6) ((qu:num->real) 6) ((qv:num->real) 6) l`
    ASSUME_TAC THENL [REWRITE_TAC[ldisj] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(qs:num->real) 6 = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(qs:num->real) 9 = --r`)) THEN
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
  (* separation *)
  MP_TAC(SPECL (C977NCFF_Q9 @ C977NCF_Q6 @ [`t:real`]) CNBA_ALTERNATIVES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(qu:num->real) 6 + l <= &3 * qc 6 + --t` THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `~linside ((qc:num->real) 6) (--t) ((qu:num->real) 6) ((qv:num->real) 6) l (&143 / &50) (&1)`
    ASSUME_TAC THENL
   [UNDISCH_TAC (list_mk_comb(`ldisj`, C977NCFF_Q9 @ C977NCF_Q6)) THEN
    REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&143 / &50`; `&1`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* noUpper *)
  SUBGOAL_THEN `~((qu:num->real) 6 + l <= (&143 / &50) * qc 6 - t)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    C977SCC_DISJ_TAC (fun t -> c977scc_has "ABT_lower" (lhand t)) THENL
     [C977NCFF_OWN_TAC; ALL_TAC] THEN
    C977SCC_DISJ_TAC (fun t -> c977scc_has "ABT_upper" (lhand t) &&
                               rand (lhand t) = `(qu:num->real) 6`) THENL
     [C977NCFF_NEIGHBOR_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj (concl th) &&
      c977scc_has "ABT_lower" (concl th) && not (is_forall (concl th)))) THEN
    UNDISCH_TAC `&3 * (qc:num->real) 6 < &7 * --t` THEN UNDISCH_TAC `&0 < (qc:num->real) 6` THEN
    UNDISCH_TAC `c977cc_normal ((qc:num->real) 6) t` THEN REWRITE_TAC[c977cc_normal] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`(qc:num->real) 6`; `t:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* floor *)
  SUBGOAL_THEN `(qc:num->real) 6 + (&143 / &50) * t <= qv 6` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside ((qc:num->real) 6) (--t) ((qu:num->real) 6) ((qv:num->real) 6) l (&143 / &50) (&1)` THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `linside ((qc:num->real) 6) (--t) ((qu:num->real) 6) ((qv:num->real) 6) l (&47 / &20) (&33 / &20)` THEN
    UNDISCH_TAC `c977cc_normal ((qc:num->real) 6) t` THEN
    UNDISCH_TAC `&7 / &10 <= (qc:num->real) 6` THEN
    UNDISCH_TAC `~((qu:num->real) 6 + l <= (&143 / &50) * qc 6 - t)` THEN
    UNDISCH_TAC `(qv:num->real) 6 < qc 6 + &143 / &50 * t` THEN
    REWRITE_TAC[linside; c977cc_normal] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* t < 3/10 *)
  SUBGOAL_THEN `&1 < (qc:num->real) 6 + (&7 / &50) * t` ASSUME_TAC THENL
   [UNDISCH_TAC `(qc:num->real) 6 + (&143 / &50) * t <= qv 6` THEN
    UNDISCH_TAC `(qv:num->real) 6 + l <= &2 * qc 6 + &3 * t` THEN
    UNDISCH_TAC `&1 < l` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&1 + (qc:num->real) 6`; `(qc:num->real) 6 + (&7 / &50) * t - &1`] REAL_LT_MUL) THEN
  MP_TAC(SPECL [`t:real`; `&1 - (qc:num->real) 6`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`t:real`; `t - &7 / &25`] REAL_LE_MUL) THEN
  UNDISCH_TAC `c977cc_normal ((qc:num->real) 6) t` THEN REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
  UNDISCH_TAC `&3 / &10 <= t` THEN UNDISCH_TAC `(qc:num->real) 6 <= &1` THEN
  UNDISCH_TAC `&7 / &10 <= (qc:num->real) 6` THEN
  UNDISCH_TAC `&1 < (qc:num->real) 6 + (&7 / &50) * t` THEN
  REAL_ARITH_TAC);;
