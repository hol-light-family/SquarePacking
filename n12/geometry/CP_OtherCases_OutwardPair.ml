(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OutwardPair.lean                    *)
(* (namespace N12Compact.Completion.OtherCases.OutwardPair).  Coupled-       *)
(* support theorem for the outward southeast square A (cA sA uA vA aA) and   *)
(* the inward northeast square N (cN sN uN vN aN).  OutwardPairFaces.frame:  *)
(* OCOPF_FRAME (its square n is cn sn un vn aA); half: C1092WPS_half;        *)
(* SharpPointScalars.half_before / half_after: OCSPS_HALF_BEFORE / _AFTER;   *)
(* OutwardPairScalars.first_margin / second_margin: OCOPS_FIRST_MARGIN /     *)
(* OCOPS_SECOND_MARGIN; WallProfile.upper_in_bands / upper_neg / lower_neg:  *)
(* OCWPSG_UPPER_IN_BANDS / OCWPVG_UPPER_NEG / OCWPVG_LOWER_NEG.              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_OutwardPairFaces.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;
needs "n12/geometry/CP_OtherCases_SharpPointScalars.ml";;
needs "n12/geometry/CongruentSAT.ml";;

let OCOP_LIN =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (fun g -> if is_eq(snd g) then (REAL_ARITH_TAC ORELSE RASM_ARITH_TAC) g
            else NLIN_TAC ~deg2:false [] g));;

let OCOP_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   OCOP_LIN; ALL_TAC];;

let OCOP_CONTRA_TAC =
  FIRST_ASSUM(fun th -> if is_neg(concl th) then
    FIRST_ASSUM(fun th' -> if concl th' = rand(concl th)
                           then ACCEPT_TAC(EQ_MP (EQF_INTRO th) th') else NO_TAC)
    else NO_TAC);;

(* Lean: cone (local), for the pair A (with sA = --t) and its northeast frame n *)
let OCOP_CONE = prove
 (`forall cA t uA vA aA cn sn un vn nx ny.
     cA * cA + --t * --t = &1 /\ &0 < aA /\ cn * cn + sn * sn = &1 /\
     linside cA (--t) uA vA aA (&7 / &20) (--(&7 / &20)) /\
     linside cA (--t) uA vA aA (&21 / &40) (&1 / &8) /\
     linside cn sn un vn aA (&7 / &20) (&7 / &20) /\
     linside cn sn un vn aA (&0) (&13 / &50) /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cA (--t) uA vA aA nx ny <= ABT_lower cn sn un vn aA nx ny
     ==> &0 < ny /\ &0 < --(&21 / &40) * nx + &27 / &200 * ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (sq,(x,y)) ->
      MP_TAC(SPECL (sq @ [x; y; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC)
   [[`cA:real`; `--t`; `uA:real`; `vA:real`; `aA:real`], (`&7 / &20`,`--(&7 / &20)`);
    [`cA:real`; `--t`; `uA:real`; `vA:real`; `aA:real`], (`&21 / &40`,`&1 / &8`);
    [`cn:real`; `sn:real`; `un:real`; `vn:real`; `aA:real`], (`&7 / &20`,`&7 / &20`);
    [`cn:real`; `sn:real`; `un:real`; `vn:real`; `aA:real`], (`&0`,`&13 / &50`)] THEN
  OCOP_LIN);;

(* Lean: rejectFirst (local) *)
let OCOP_REJECT_FIRST = prove
 (`forall cA t uA vA aA cn sn un vn.
     cA * cA + --t * --t = &1 /\ cn * cn + sn * sn = &1 /\ &0 < aA /\ &1 < aA /\
     &0 < cA /\ &0 < t /\ C1092WPS_half cA t < &3 / &10 /\
     uA + aA <= cA + t /\ --cA + &4 / &5 * t <= vA /\ vn + aA <= cn /\
     &0 < cA * cn - t * sn /\ &0 < cA * sn + t * cn
     ==> ~(ABT_upper cA (--t) uA vA aA (--sn) cn <= ABT_lower cn sn un vn aA (--sn) cn)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cn:real`; `sn:real`; `un:real`; `vn:real`; `aA:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
  REWRITE_TAC[OCWPSG_UPPER_IN_BANDS] THEN
  REWRITE_TAC[REAL_ARITH `--sn * cA + cn * --t = --(cA * sn + t * cn) /\
                          -- --sn * --t + cn * cA = cA * cn - t * sn`; REAL_ABS_NEG] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN DISCH_TAC THEN
  OCOP_PROD `&0 <= (cA * sn + t * cn) * ((cA + t) - (uA + aA))` THEN
  OCOP_PROD `&0 <= (cA * cn - t * sn) * (vA - (--cA + &4 / &5 * t))` THEN
  OCOP_PROD `&0 < (aA - &1) * (&1 + (cA * sn + t * cn) + (cA * cn - t * sn))` THEN
  MP_TAC(SPECL [`cA:real`; `t:real`; `cn:real`; `sn:real`] OCOPS_FIRST_MARGIN) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_POW_2] THEN OCOP_LIN; DISCH_TAC] THEN
  OCOP_LIN);;

(* Lean: rejectSecond (local) *)
let OCOP_REJECT_SECOND = prove
 (`forall cA t uA vA aA cn sn un vn.
     cA * cA + --t * --t = &1 /\ cn * cn + sn * sn = &1 /\ &0 < aA /\ &1 < aA /\
     &0 < cA /\ &0 <= t /\ t <= cA /\ C1092WPS_half cA t < &3 / &10 /\
     &0 < cn /\ &0 <= sn /\ sn <= cn /\
     uA + aA <= cA + t /\ &7 / &20 * (sn - cn) <= un /\ vn + aA <= cn /\
     &0 < cA * cn - t * sn /\ &0 < cA * sn + t * cn
     ==> ~(ABT_upper cn sn un vn aA cA (--t) <= ABT_lower cA (--t) uA vA aA cA (--t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `--t`; `uA:real`; `vA:real`; `aA:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
  REWRITE_TAC[OCWPSG_UPPER_IN_BANDS] THEN
  REWRITE_TAC[REAL_ARITH `cA * cn + --t * sn = cA * cn - t * sn /\
                          --cA * sn + --t * cn = --(cA * sn + t * cn)`; REAL_ABS_NEG] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN DISCH_TAC THEN
  OCOP_PROD `&0 <= (cA * cn - t * sn) * (un - &7 / &20 * (sn - cn))` THEN
  OCOP_PROD `&0 <= (cA * sn + t * cn) * (cn - (vn + aA))` THEN
  OCOP_PROD `&0 < (aA - &1) * (&1 + (cA * cn - t * sn) + (cA * sn + t * cn))` THEN
  MP_TAC(SPECL [`cA:real`; `t:real`; `cn:real`; `sn:real`] OCOPS_SECOND_MARGIN) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_POW_2] THEN OCOP_LIN; DISCH_TAC] THEN
  OCOP_LIN);;

(* Lean: impossible *)
let OCOP_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cN sN uN vN aN t.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     &1 < aA /\ aA = aN /\ sA = --t /\ &0 < cA /\ &0 <= t /\ t <= cA /\
     &13 / &87 < C1092WPS_half cA t /\ C1092WPS_half cA t < &143 / &500 /\
     uA + aA <= cA + t /\ --cA + &4 / &5 * t <= vA /\
     linside cA sA uA vA aA (&7 / &20) (--(&7 / &20)) /\
     linside cA sA uA vA aA (&21 / &40) (&1 / &8) /\
     linside cN sN uN vN aN (&7 / &20) (&7 / &20) /\
     linside cN sN uN vN aN (&0) (&13 / &50) /\
     linside cN sN uN vN aN (&13 / &50) (&1) /\
     ~linside cN sN uN vN aN (--(&7 / &20)) (&7 / &20) /\
     ~linside cN sN uN vN aN (&0) (&1) /\ ~linside cN sN uN vN aN (&1) (&1) /\
     ldisj cA sA uA vA aA cN sN uN vN aN
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sA:real = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aN`)) THEN
  SUBGOAL_THEN `cA pow 2 + t pow 2 = &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN OCOP_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `~linside cN sN uN vN aA (&21 / &40) (&1 / &8)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `ldisj cA (--t) uA vA aA cN sN uN vN aA` THEN
    REWRITE_TAC[ldisj; NOT_FORALL_THM] THEN
    MAP_EVERY EXISTS_TAC [`&21 / &40`; `&1 / &8`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aA:real`] OCOPF_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cn:real` (X_CHOOSE_THEN `sn:real` (X_CHOOSE_THEN `un:real`
    (X_CHOOSE_THEN `vn:real` (X_CHOOSE_THEN `an:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `an:real = aA`)) THEN
  SUBGOAL_THEN `linside cn sn un vn aA (&7 / &20) (&7 / &20) /\
                linside cn sn un vn aA (&0) (&13 / &50) /\
                ldisj cA (--t) uA vA aA cn sn un vn aA` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `ldisj cA (--t) uA vA aA cN sN uN vN aA` THEN
    ASM_REWRITE_TAC[ldisj];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `&13 / &87 < C1092WPS_half cA t` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[C1092WPS_half; real_div; REAL_MUL_LZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `t:real`; `&229551 / &270449`; `&143000 / &270449`; `&143 / &500`]
    OCSPS_HALF_BEFORE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN OCOP_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `t:real`; `&3700 / &3869`; `&1131 / &3869`; `&13 / &87`]
    OCSPS_HALF_AFTER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN OCOP_LIN; DISCH_TAC] THEN
  SUBGOAL_THEN `t < cA /\ &1131 * cA <= &3700 * t /\ C1092WPS_half cA t < &3 / &10`
    STRIP_ASSUME_TAC THENL [OCOP_LIN; ALL_TAC] THEN
  OCOP_PROD `&0 < cn * (cA - t)` THEN OCOP_PROD `&0 <= t * (cn - sn)` THEN
  OCOP_PROD `&0 <= cA * sn` THEN OCOP_PROD `&0 < t * cn` THEN
  SUBGOAL_THEN `&0 < cA * cn - t * sn /\ &0 < cA * sn + t * cn` STRIP_ASSUME_TAC THENL
   [OCOP_LIN; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `t:real`; `uA:real`; `vA:real`; `aA:real`;
                `cn:real`; `sn:real`; `un:real`; `vn:real`] OCOP_REJECT_FIRST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN OCOP_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `t:real`; `uA:real`; `vA:real`; `aA:real`;
                `cn:real`; `sn:real`; `un:real`; `vn:real`] OCOP_REJECT_SECOND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN OCOP_LIN; DISCH_TAC] THEN
  let A = [`cA:real`; `--t`; `uA:real`; `vA:real`; `aA:real`]
  and N = [`cn:real`; `sn:real`; `un:real`; `vn:real`; `aA:real`] in
  let cone nx ny = SPECL [`cA:real`; `t:real`; `uA:real`; `vA:real`; `aA:real`;
                          `cn:real`; `sn:real`; `un:real`; `vn:real`; nx; ny] OCOP_CONE in
  let neg t = mk_comb(`(--):real->real`, t) in
  let reverse nx ny = SUBGOAL_THEN
    (mk_comb(mk_comb(`(<=):real->real->bool`,
      list_mk_comb(`ABT_upper`, A @ [neg nx; neg ny])),
      list_mk_comb(`ABT_lower`, N @ [neg nx; neg ny])))
    ASSUME_TAC THENL
    [REWRITE_TAC[OCWPVG_UPPER_NEG; OCWPVG_LOWER_NEG] THEN OCOP_LIN; ALL_TAC] in
  let use nx ny =
    MP_TAC(cone nx ny) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_NEG; ARITH; REAL_POW_2] THEN OCOP_LIN;
      STRIP_TAC THEN OCOP_LIN] in
  MP_TAC(SPECL (A @ N) CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `--t`; `aA:real`; `cn:real`; `sn:real`; `aA:real`] ABT_PARALLEL_RADIUS) THEN
  MP_TAC(SPECL [`cA:real`; `--t`; `aA:real`; `cn:real`; `sn:real`; `aA:real`] ABT_TRANSVERSE_RADIUS) THEN
  MP_TAC(SPECL [`cn:real`; `sn:real`; `aA:real`; `cA:real`; `--t`; `aA:real`] ABT_PARALLEL_RADIUS) THEN
  MP_TAC(SPECL [`cn:real`; `sn:real`; `aA:real`; `cA:real`; `--t`; `aA:real`] ABT_TRANSVERSE_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[C977CB_faceSep] o
    check (can (term_match [] `C977CB_faceSep a b c d e f g h i j`) o concl)) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   (map (fun (nx, ny, forward, backward) ->
      MP_TAC(SPECL (A @ N @ [nx; ny]) ABT_SEPARATED) THEN
      ANTS_TAC THENL [OCOP_LIN; ALL_TAC] THEN
      DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL [forward; backward])
    [`cA:real`, `--t`,
       use `cA:real` `--t`,
       OCOP_CONTRA_TAC;
     `-- --t`, `cA:real`,
       use `-- --t` `cA:real`,
       (reverse `-- --t` `cA:real` THEN use (neg `-- --t`) (neg `cA:real`));
     `cn:real`, `sn:real`,
       use `cn:real` `sn:real`,
       (reverse `cn:real` `sn:real` THEN use (neg `cn:real`) (neg `sn:real`));
     `--sn`, `cn:real`,
       OCOP_CONTRA_TAC,
       (reverse `--sn` `cn:real` THEN use (neg `--sn`) (neg `cn:real`))]));;
