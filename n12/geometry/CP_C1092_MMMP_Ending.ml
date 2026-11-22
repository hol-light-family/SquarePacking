(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/Ending.lean                         *)
(* (N12Compact.C1092MMMPEnding).  The complete final MMMP pair               *)
(* contradiction, conditional only on the actual NE square's face table.     *)
(* clockwise (c,s,u,v,a) = (c, s, --v - a, u, a), inside_clockwise:          *)
(* C1092MEA_INSIDE_CLOCKWISE; EndingAxes.alternatives: C1092MEA_ALTERNATIVES;*)
(* MMMMFirstPair.result: C1092MFP_RESULT; FinalScalars39: C1092FS39_*;       *)
(* CanonicalProjection.after: CCCP_AFTER; short_projections: WFP_SP;         *)
(* lower_pn / upper_nn: C1092WS_LOWER_PN / C1092MEA_UPPER_NN;                *)
(* ClosedFrames.canonical_frame: CLF_CANONICAL_FRAME.                        *)
(* W is written cW sW uW vW aW, N is written cN sN uN vN aN.                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_EndingAxes.ml";;
needs "n12/geometry/CP_C1092_MMMP_FinalScalars39.ml";;
needs "n12/geometry/CP_C1092_MMMMFirstPair.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let C1092MEND_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092MEND_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MEND_LIN_TAC; DISCH_TAC];;

let C1092MEND_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MEND_LIN_TAC; DISCH_TAC];;

let C1092MEND_NORMAL_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2] th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths));;

(* add expanded copies of the positive linside assumptions *)
let C1092MEND_EXPAND_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> let t = concl th in not(is_neg t) && not(is_forall t) &&
       can (find_term ((=) `linside`)) t) ths));;

let C1092MEND_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C1092MEND_LIN_TAC;;

(* Lean: Profile (definition) *)
let c1092mend_profile = new_definition
 `c1092mend_profile (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    (&2 / &5) * s <= u /\ (&14 / &25) * c - s <= v /\ u + a <= c + s /\ v + a <= c`;;

(* Lean: cosine_cap (private) *)
let C1092MEND_COSINE_CAP = prove
 (`forall b t. c977cc_normal b t /\ &252 / &373 <= t ==> b <= &275 / &373`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MEND_NORMAL_TAC THEN
  C1092MEND_LE_MUL_TAC `t - &252 / &373` `t + &252 / &373` THEN
  MP_TAC(SPEC `b - &275 / &373` REAL_LE_SQUARE) THEN DISCH_TAC THEN
  C1092MEND_LIN_TAC);;

(* Lean: negative (private) *)
let C1092MEND_NEGATIVE = prove
 (`forall cW sW uW vW aW cN sN uN vN aN.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     &1 < aW /\ aW = aN /\
     c977cc_normal cW (--sW) /\ c977cc_normal cN sN /\ &252 / &373 <= sN /\
     c1092mend_profile cN sN uN vN aN /\
     linside cW sW uW vW aW (&0) (&0) /\
     linside cW sW uW vW aW (--(&1 / &2)) (&0) /\
     linside cW sW uW vW aW (--(&1 / &2)) (&1 / &2) /\
     linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
     ~linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\
     linside cN sN uN vN aN (&7 / &20) (&7 / &20) /\
     linside cN sN uN vN aN (&13 / &50) (&1) /\
     linside cN sN uN vN aN (&2 / &5) (&1) /\
     ldisj cW sW uW vW aW cN sN uN vN aN
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aW:real = aN`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mend_profile] o
    check (fun th -> can (term_match [] `c1092mend_profile c s u v a`) (concl th))) THEN
  C1092MEND_NORMAL_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `--vW - aW`; `uW:real`; `aW:real`;
                `cN:real`; `sN:real`; `--vN - aW`; `uN:real`; `aW:real`] C1092MFP_RESULT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[C1092MEA_INSIDE_CLOCKWISE; REAL_NEG_NEG; REAL_NEG_0; ldisj] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN ASM_REWRITE_TAC[REAL_ABS_BOUNDS] THEN
    REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           (fun (asl,w as g) -> if is_forall w then ASM_MESON_TAC[] g else NO_TAC g);
           (fun (asl,w as g) -> if is_neg w then
              (REWRITE_TAC[linside] THEN STRIP_TAC THEN C1092MEND_LIN_TAC) g else NO_TAC g);
           C1092MEND_LIN_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[C1092MFP_result] THEN STRIP_TAC THEN
  C1092MEND_EXPAND_TAC THEN
  (* support in the original frame *)
  SUBGOAL_THEN
   `(cN * cW + sN * sW) * (uW + aW) + (cN * --sW + sN * cW) * (vW + aW) <= cN + sN - aW`
    ASSUME_TAC THENL [C1092MEND_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cN <= &275 / &373` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092MEND_COSINE_CAP THEN EXISTS_TAC `sN:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `&275 / &373`; `&252 / &373`; `&18`; `&7`] CCCP_AFTER) THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[REAL_POW_2] THEN C1092MEND_LIN_TAC;
    CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC] THEN
  (* alpha = cN * cW + sN * sW >= 0 *)
  C1092MEND_LE_MUL_TAC `cN - sN` `cW:real` THEN
  C1092MEND_LE_MUL_TAC `sN:real` `cW - --sW` THEN
  C1092MEND_LE_MUL_TAC `cN * cW + sN * sW` `uW + aW` THEN
  C1092MEND_LE_MUL_TAC `--sW` `cN - sN` THEN
  C1092MEND_LE_MUL_TAC `vW + aW` `(cN * --sW + sN * cW) - sN * (cW + --sW)` THEN
  SUBGOAL_THEN `(cW + --sW) * (vW + aW) < &11 / &18` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MEND_LE_MUL_TAC `sN:real` `(cW + --sW) * (vW + aW) - &11 / &18` THEN
    C1092MEND_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(&7 / &20) * (cW + --sW) <= vW` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MEND_MISS_TAC `~linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20))`; ALL_TAC] THEN
  C1092MEND_LE_MUL_TAC `(cW + --sW) - &1` `&13 / &20 - (&7 / &20) * (cW + --sW)` THEN
  C1092MEND_LT_MUL_TAC `cW + --sW` `(vW + aW) - (&1 - (&7 / &20) * (cW + --sW))` THEN
  C1092MEND_LIN_TAC);;

(* Lean: positive (private) *)
let C1092MEND_POSITIVE = prove
 (`forall cW sW uW vW aW cN sN uN vN aN.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     &1 < aW /\ aW = aN /\
     c977cc_normal cW sW /\ c977cc_normal cN sN /\ &252 / &373 <= sN /\
     c1092mend_profile cN sN uN vN aN /\
     linside cW sW uW vW aW (&0) (&0) /\
     linside cW sW uW vW aW (--(&1 / &2)) (&0) /\
     linside cW sW uW vW aW (--(&1 / &2)) (&1 / &2) /\
     linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
     ~linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\
     ~linside cW sW uW vW aW (--(&1)) (&39 / &100) /\
     linside cN sN uN vN aN (&7 / &20) (&7 / &20) /\
     ldisj cW sW uW vW aW cN sN uN vN aN
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aW:real = aN`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mend_profile] o
    check (fun th -> can (term_match [] `c1092mend_profile c s u v a`) (concl th))) THEN
  C1092MEND_NORMAL_TAC THEN
  SUBGOAL_THEN `~linside cW sW uW vW aW (&7 / &20) (&7 / &20)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ldisj]; ALL_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `cN:real`; `sN:real`; `uN:real`; `vN:real`; `aW:real`] C1092MEA_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092MEND_LIN_TAC; DISCH_TAC] THEN
  C1092MEND_EXPAND_TAC THEN
  SUBGOAL_THEN `cN <= &275 / &373` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092MEND_COSINE_CAP THEN EXISTS_TAC `sN:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cW * &37 / &50 + sW * &13 / &20 <= &1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`cW:real`; `sW:real`; `&37 / &50`; `&13 / &20`] WFP_SHORT_PROJECTIONS) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  (* vCap, uCap, vFloor in the original frame *)
  SUBGOAL_THEN `uW + aW <= (&7 / &20) * (cW + sW)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MEND_MISS_TAC `~linside cW sW uW vW aW (&7 / &20) (&7 / &20)`; ALL_TAC] THEN
  SUBGOAL_THEN `--vW <= (&7 / &20) * (cW - sW)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MEND_MISS_TAC `~linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20))`; ALL_TAC] THEN
  SUBGOAL_THEN `(&39 / &100) * sW - cW <= uW` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MEND_MISS_TAC `~linside cW sW uW vW aW (--(&1)) (&39 / &100)`; ALL_TAC] THEN
  (* shallow *)
  SUBGOAL_THEN `&8 * sW < &7 * cW` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MEND_LE_MUL_TAC `&8 * sW - &7 * cW` `&8 * sW + &7 * cW` THEN
    SUBGOAL_THEN `&200 / &263 < cW` ASSUME_TAC THENL [C1092MEND_LIN_TAC; ALL_TAC] THEN
    C1092MEND_LT_MUL_TAC `cW - &200 / &263` `cW + &200 / &263` THEN
    C1092MEND_LIN_TAC; ALL_TAC] THEN
  (* alpha = cN * cW + sN * sW, beta = sN * cW - cN * sW *)
  C1092MEND_LT_MUL_TAC `cN:real` `cW:real` THEN C1092MEND_LE_MUL_TAC `sN:real` `sW:real` THEN
  C1092MEND_LT_MUL_TAC `cW:real` `sN - (&7 / &8) * cN` THEN
  C1092MEND_LT_MUL_TAC `cN:real` `(&7 / &8) * cW - sW` THEN
  SUBGOAL_THEN `&0 < cN * cW + sN * sW /\ &0 < sN * cW - cN * sW` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092MEND_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(cN * cW + sN * sW) * (cN * cW + sN * sW) +
                (sN * cW - cN * sW) * (sN * cW - cN * sW) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `cW * cW + sW * sW = &1` THEN UNDISCH_TAC `cN * cN + sN * sN = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `cN * cW + sN * sW <= &1 /\ &1 <= (cN * cW + sN * sW) + (sN * cW - cN * sW)`
    STRIP_ASSUME_TAC THENL
   [C1092MEND_LT_MUL_TAC `cN * cW + sN * sW` `sN * cW - cN * sW` THEN
    MP_TAC(SPEC `sN * cW - cN * sW` REAL_LE_SQUARE) THEN
    MP_TAC(SPEC `(cN * cW + sN * sW) - &1` REAL_LE_SQUARE) THEN REPEAT DISCH_TAC THEN
    CONJ_TAC THENL
     [C1092MEND_LIN_TAC;
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092MEND_LT_MUL_TAC `&1 - ((cN * cW + sN * sW) + (sN * cW - cN * sW))`
        `&1 + ((cN * cW + sN * sW) + (sN * cW - cN * sW))` THEN
      C1092MEND_LIN_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < vN + aW /\ uN < &1 / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092MEND_LIN_TAC; ALL_TAC] THEN
  (* formulas *)
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aW:real`; `cW:real`; `sW:real`;
                `cN * cW + sN * sW`; `--(sN * cW - cN * sW)`] C1092WS_LOWER_PN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092MEND_LIN_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `cN:real`; `sN:real`;
                `cN * cW + sN * sW`; `sN * cW - cN * sW`] C1092MEA_UPPER_NN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092MEND_LIN_TAC;
    DISCH_TAC] THEN
  (* lowOwn *)
  SUBGOAL_THEN `(cN * cW + sN * sW) * uN < &1 / &2` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 <= uN` THENL
     [C1092MEND_LE_MUL_TAC `&1 - (cN * cW + sN * sW)` `uN:real` THEN C1092MEND_LIN_TAC;
      C1092MEND_LE_MUL_TAC `cN * cW + sN * sW` `--uN` THEN C1092MEND_LIN_TAC];
    ALL_TAC] THEN
  C1092MEND_LT_MUL_TAC `sN * cW - cN * sW` `vN + aW` THEN
  SUBGOAL_THEN `ABT_lower cN sN uN vN aW cW sW < &1 / &2` ASSUME_TAC THENL
   [C1092MEND_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 < vW + aW` ASSUME_TAC THENL [C1092MEND_LIN_TAC; ALL_TAC] THEN
  (* sLowU *)
  SUBGOAL_THEN `uW < cW * --(&7 / &20) + sW * --(&7 / &20)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 / &2 < uW + aW` ASSUME_TAC THENL [C1092MEND_LIN_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [C1092MEND_LIN_TAC;
      C1092MEND_LT_MUL_TAC `cN * cW + sN * sW` `uW + aW - &1 / &2` THEN
      C1092MEND_LT_MUL_TAC `sN * cW - cN * sW` `vW + aW - &1 / &2` THEN
      C1092MEND_LIN_TAC];
    ALL_TAC] THEN
  (* hFace and aFace *)
  SUBGOAL_THEN `aW - (&7 / &20) * cW + (&7 / &20) * sW <= vW + aW` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MEND_MISS_TAC `~linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20))`; ALL_TAC] THEN
  SUBGOAL_THEN `aW - cW + (&39 / &100) * sW <= uW + aW` ASSUME_TAC THENL
   [SUBGOAL_THEN `sW + (&39 / &100) * cW < vW + aW` ASSUME_TAC THENL
     [C1092MEND_LIN_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MEND_MISS_TAC `~linside cW sW uW vW aW (--(&1)) (&39 / &100)`; ALL_TAC] THEN
  C1092MEND_LT_MUL_TAC `aW - &1` `&1 + (cN * cW + sN * sW) + (sN * cW - cN * sW)` THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [(* own *)
    C1092MEND_LE_MUL_TAC `cN * cW + sN * sW` `(cN + sN - aW) - uN` THEN
    C1092MEND_LE_MUL_TAC `sN * cW - cN * sW` `(vN + aW) - (aW + (&2 / &5) * cN - sN)` THEN
    MP_TAC(SPECL [`cW:real`; `sW:real`; `cN:real`; `sN:real`] C1092FS39_OWN_POSITIVE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MEND_LIN_TAC; ALL_TAC] THEN
    REWRITE_TAC[C1092FS39_ownMargin] THEN DISCH_TAC THEN
    C1092MEND_LE_MUL_TAC `sN * cW - cN * sW` `cN:real` THEN
    C1092MEND_LIN_TAC;
    (* neighbor *)
    C1092MEND_LE_MUL_TAC `cN * cW + sN * sW` `(uW + aW) - (aW - cW + (&39 / &100) * sW)` THEN
    C1092MEND_LE_MUL_TAC `sN * cW - cN * sW`
      `(vW + aW) - (aW - (&7 / &20) * cW + (&7 / &20) * sW)` THEN
    MP_TAC(SPECL [`cW:real`; `sW:real`; `cN:real`; `sN:real`] C1092FS39_NEIGHBOR_POSITIVE) THEN
    ASM_REWRITE_TAC[C1092FS39_neighborMargin] THEN DISCH_TAC THEN
    C1092MEND_LIN_TAC]);;

(* Lean: impossible *)
let C1092MEND_IMPOSSIBLE = prove
 (`forall cW sW uW vW aW cN sN uN vN aN.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     &1 < aW /\ aW = aN /\
     c977cc_normal cN sN /\ &252 / &373 <= sN /\
     c1092mend_profile cN sN uN vN aN /\
     linside cW sW uW vW aW (&0) (&0) /\
     linside cW sW uW vW aW (--(&1 / &2)) (&0) /\
     linside cW sW uW vW aW (--(&1 / &2)) (&1 / &2) /\
     linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
     ~linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\
     ~linside cW sW uW vW aW (--(&1)) (&39 / &100) /\
     linside cN sN uN vN aN (&7 / &20) (&7 / &20) /\
     linside cN sN uN vN aN (&13 / &50) (&1) /\
     linside cN sN uN vN aN (&2 / &5) (&1) /\
     ldisj cW sW uW vW aW cN sN uN vN aN
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aW:real = aN`)) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `u:real`
    (X_CHOOSE_THEN `v:real` (X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a:real = aW`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  ASM_CASES_TAC `&0 <= s` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `aW:real`;
                  `cN:real`; `sN:real`; `uN:real`; `vN:real`; `aW:real`] C1092MEND_POSITIVE) THEN
    ASM_REWRITE_TAC[ldisj; c977cc_normal; REAL_POW_2] THEN RASM_ARITH_TAC;
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `aW:real`;
                  `cN:real`; `sN:real`; `uN:real`; `vN:real`; `aW:real`] C1092MEND_NEGATIVE) THEN
    ASM_REWRITE_TAC[ldisj; c977cc_normal; REAL_POW_2] THEN RASM_ARITH_TAC]);;
