(* ========================================================================= *)
(* Port of Compact/Geometry/UpperRightNegativeCornerPositiveTop.lean.         *)
(* The negative-corner (sE = --f) / positive-top sector.                     *)
(* K = cE*cT - f*sT and H = cE*sT + f*cT are written out.                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/UpperRightCornerTopLongitudinal.ml";;
needs "n12/geometry/UpperRightNegativeTopReach.ml";;

let URNCPT_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

(* support formulas: unfold, eliminate abs by cases *)
let URNCPT_FORM_TAC =
  REWRITE_TAC[C977NCO_UPPER_IN_BANDS; C977NCO_LOWER_IN_BANDS] THEN
  (fun (asl,w as g) ->
     let abss = setify(find_terms (fun t -> is_comb t &&
                  rator t = `abs:real->real`) w) in
     let eqs = map (fun t -> let x = rand t in
        try TAC_PROOF((asl, mk_eq(t,x)), RASM_ARITH_TAC) with Failure _ ->
        TAC_PROOF((asl, mk_eq(t,mk_comb(`(--):real->real`,x))), RASM_ARITH_TAC))
        abss in
     (REWRITE_TAC eqs THEN REAL_ARITH_TAC) g);;

(* Lean: coefficient (private) *)
let URNCPT_COEFFICIENT = prove
 (`forall c s. c977cc_normal c s
     ==> --(&4 / &5) <= c - &9 / &5 + (&7 / &10) * s pow 2 /\
         --(&3 / &8) <= --s + (&7 / &10) * c * s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 - c) * ((&7 / &10) * c - &3 / &10) /\
                &0 <= s * (c - &7 / &10)` MP_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: first_margin (private) *)
let URNCPT_FIRST_MARGIN = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s
     ==> &0 < &1 + e * (c - &9 / &5 + (&7 / &10) * s pow 2) +
              f * (--s + (&7 / &10) * c * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] URNCPT_COEFFICIENT) THEN
  MP_TAC(SPECL [`e:real`; `f:real`; `&4 / &5`; `&3 / &8`] URCLB_DISK_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= e * ((c - &9 / &5 + (&7 / &10) * s pow 2) + &4 / &5) /\
                &0 <= f * ((--s + (&7 / &10) * c * s) + &3 / &8)` MP_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: second_margin (private) *)
let URNCPT_SECOND_MARGIN = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s
     ==> &0 < &1 - (&13 / &10) * c + (e * c - f * s) * (&1 - e / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&169 / &200`; `&91 / &200`] URCLB_DISK_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `&91 / &200 <= e * (&1 - e / &2)` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= (e - &7 / &10) * (&1 - e)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ((e - f) * s) * (&1 - e / &2) /\
                &0 <= (c - s) * (e * (&1 - e / &2) - &91 / &200)` MP_TAC THENL
  [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: third_margin (private) *)
let URNCPT_THIRD_MARGIN = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s
     ==> &0 <= e + f - &1 + e * f * (c - &9 / &5 + (&7 / &10) * s pow 2) +
               e pow 2 * s * (&1 - (&7 / &10) * c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] URNCPT_COEFFICIENT) THEN
  MP_TAC(SPECL [`e:real`; `f:real`] URNTB_ARC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= (e * f) * ((c - &9 / &5 + (&7 / &10) * s pow 2) + &4 / &5) /\
                &0 <= (e pow 2 * s) * (&1 - (&7 / &10) * c) /\ &0 <= e * f` MP_TAC THENL
  [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
   REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: fourth_margin (private) *)
let URNCPT_FOURTH_MARGIN = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s
     ==> &0 < c * (&1 / &2 + f - f * (e + f) / &2) +
              s * (e - &11 / &10 + f * (f - e) / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `f:real`] URNTB_ARC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `&1 / &2 <= &1 / &2 + f - f * (e + f) / &2` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= f * (&1 - (e + f) / &2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `e * f <= &1 / &2` ASSUME_TAC THENL
  [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC [SQ_NONNEG `e - f:real`];
   ALL_TAC] THEN
  SUBGOAL_THEN `&3 / &10 <= (&1 / &2 + f - f * (e + f) / &2) +
                            (e - &11 / &10 + f * (f - e) / &2)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (c - s) * ((&1 / &2 + f - f * (e + f) / &2) - &3 / &10) /\
    &0 <= s * (((&1 / &2 + f - f * (e + f) / &2) +
                (e - &11 / &10 + f * (f - e) / &2)) - &3 / &10)` MP_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: point *)
let URNCPT_POINT = prove
 (`forall cE sE uE vE aE cT sT uT vT aT f.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cT * cT + sT * sT = &1 /\ &0 < aT /\
     sE = --f /\ c977cc_normal cE f /\ c977cc_normal cT sT /\
     aE = aT /\ &1 < aE /\ lcont cE sE uE vE aE /\
     linside cE sE uE vE aE (&3) (&3) /\
     linside cE sE uE vE aE (&16 / &5) (&3) /\
     linside cE sE uE vE aE (&3) (&7 / &2) /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     ~linside cT sT uT vT aT (&87 / &50) (&3) /\
     ~linside cT sT uT vT aT (&47 / &20) (&47 / &20) /\
     ldisj cE sE uE vE aE cT sT uT vT aT
     ==> linside cE sE uE vE aE (&7 / &2) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aE:real = aT`)) THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aE:real`] URCTL_TOP_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `f:real`]
    URNTR_TOP_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MAP_EVERY (fun th -> MP_TAC(SPECL [`cE:real`; `f:real`; `cT:real`; `sT:real`] th))
   [URNCPT_FIRST_MARGIN; URNCPT_SECOND_MARGIN; URNCPT_THIRD_MARGIN; URNCPT_FOURTH_MARGIN] THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sE:real = --f`)) THEN
  C977CSB_NORMAL_TAC THEN
  URNCPT_UNFOLD_TAC `linside cE (--f) uE vE aE (&3) (&3)` THEN
  URNCPT_UNFOLD_TAC `linside cE (--f) uE vE aE (&16 / &5) (&3)` THEN
  URNCPT_UNFOLD_TAC `linside cE (--f) uE vE aE (&3) (&7 / &2)` THEN
  URNCPT_UNFOLD_TAC `linside cT sT uT vT aE (&12 / &5) (&3)` THEN
  SUBGOAL_THEN `uE + aE <= (&7 / &2) * cE - &3 * f` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside cE (--f) uE vE aE (&7 / &2) (&3)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cE * cT - f * sT /\ &0 <= cE * sT + f * cT` STRIP_ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= cE * (cT - sT) /\ &0 <= sT * (cE - f) /\
                 &0 <= cE * sT /\ &0 <= f * cT` MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `ABT_upper cT sT uT vT aE cE (--f) =
      (cE * cT - f * sT) * (uT + aE) - (cE * sT + f * cT) * vT /\
    ABT_upper cT sT uT vT aE (-- --f) cE =
      (cE * sT + f * cT) * (uT + aE) + (cE * cT - f * sT) * (vT + aE) /\
    ABT_lower cE (--f) uE vE aE cT sT =
      (cE * cT - f * sT) * uE + (cE * sT + f * cT) * vE /\
    ABT_upper cE (--f) uE vE aE (--sT) cT =
      --(cE * sT + f * cT) * uE + (cE * cT - f * sT) * (vE + aE)`
  STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN URNCPT_FORM_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `--f:real`; `uE:real`; `vE:real`; `aE:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cE:real`; `--f:real`; `uE:real`; `vE:real`; `aE:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aE:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aE:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `--f:real`; `uE:real`; `vE:real`; `aE:real`;
                `cT:real`; `sT:real`; `uT:real`; `vT:real`; `aE:real`]
    CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[C977CB_faceSep]] THEN
  let sep nx ny = SPECL [`cE:real`; `--f:real`; `uE:real`; `vE:real`; `aE:real`;
                   `cT:real`; `sT:real`; `uT:real`; `vT:real`; `aE:real`; nx; ny]
                  ABT_SEPARATED in
  let sb sq x y nx ny =
    let c,s',u,v = sq in
    MP_TAC(SPECL [c; s'; u; v; `aE:real`; x; y; nx; ny] ABT_STRICT_BOUNDS) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
     ASM_REAL_ARITH_TAC; STRIP_TAC] in
  let qE = (`cE:real`,`--f:real`,`uE:real`,`vE:real`)
  and qT = (`cT:real`,`sT:real`,`uT:real`,`vT:real`) in
  let use_sep nx ny swap radius =
    MP_TAC(sep nx ny) THEN ANTS_TAC THENL
    [(if swap then MATCH_MP_TAC(REAL_ARITH `b + a <= x ==> a + b <= x:real`)
      else ALL_TAC) THEN
     MP_TAC radius THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
     ASM_REWRITE_TAC[]; ALL_TAC] in
  let prod tm = SUBGOAL_THEN tm ASSUME_TAC THENL
    [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
     ALL_TAC] in
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
  [use_sep `cE:real` `--f:real` false
     (SPECL [`cE:real`; `--f:real`; `aE:real`; `cT:real`; `sT:real`; `aE:real`]
       ABT_PARALLEL_RADIUS) THEN
   sb qE `&3` `&3` `cE:real` `--f:real` THEN
   sb qT `&2` `&1543 / &500` `cE:real` `--f:real` THEN
   DISCH_THEN DISJ_CASES_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   prod `&0 <= (cE * cT - f * sT) * (uT - ((&17 / &10) * cT + &3 * sT))` THEN
   prod `&0 <= (cE * sT + f * cT) * ((&3 * cT - (&12 / &5) * sT) - vT)` THEN
   SUBGOAL_THEN `&0 < (&1 + (cE * cT - f * sT)) * (aE - &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `(cE * cT - f * sT) * ((&17 / &10) * cT + &3 * sT) -
     (cE * sT + f * cT) * (&3 * cT - (&12 / &5) * sT) + (cE * cT - f * sT) + &1 -
     ((&7 / &2) * cE - &3 * f) =
     &1 + cE * (cT - &9 / &5 + (&7 / &10) * sT pow 2) + f * (--sT + (&7 / &10) * cT * sT)`
   MP_TAC THENL
   [UNDISCH_TAC `cT pow 2 + sT pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   RASM_ARITH_TAC;
   use_sep `-- --f:real` `cE:real` false
     (SPECL [`cE:real`; `--f:real`; `aE:real`; `cT:real`; `sT:real`; `aE:real`]
       ABT_TRANSVERSE_RADIUS) THEN
   sb qE `&3` `&7 / &2` `-- --f:real` `cE:real` THEN
   sb qT `&12 / &5` `&3` `-- --f:real` `cE:real` THEN
   DISCH_THEN DISJ_CASES_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   prod `&0 <= (cE * (cE * sT + f * cT)) * (uT - ((&17 / &10) * cT + &3 * sT))` THEN
   prod `&0 <= (cE * (cE * cT - f * sT)) * ((vT + aE) - (&3 * cT - (&12 / &5) * sT))` THEN
   prod `&0 <= cE * (vE - ((cE * sT + f * cT) * (uT + aE) +
                            (cE * cT - f * sT) * (vT + aE)))` THEN
   prod `&0 <= f * (((&7 / &2) * cE - &3 * f) - (uE + aE))` THEN
   SUBGOAL_THEN `&0 < (cE * (cE * sT + f * cT) + cE + f) * (aE - &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `&0 <= cE * (cE * sT + f * cT)` MP_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
   SUBGOAL_THEN
    `cE * ((cE * sT + f * cT) * ((&17 / &10) * cT + &3 * sT) +
           (cE * cT - f * sT) * (&3 * cT - (&12 / &5) * sT)) +
     cE * (cE * sT + f * cT) + cE + f - (&4 + f * ((&7 / &2) * cE - &3 * f)) =
     cE + f - &1 + cE * f * (cT - &9 / &5 + (&7 / &10) * sT pow 2) +
     cE pow 2 * sT * (&1 - (&7 / &10) * cT)` MP_TAC THENL
   [UNDISCH_TAC `cT pow 2 + sT pow 2 = &1` THEN UNDISCH_TAC `cE pow 2 + f pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
   RASM_ARITH_TAC;
   use_sep `cT:real` `sT:real` true
     (SPECL [`cT:real`; `sT:real`; `aE:real`; `cE:real`; `--f:real`; `aE:real`]
       ABT_PARALLEL_RADIUS) THEN
   sb qE `&3` `&3` `cT:real` `sT:real` THEN
   sb qT `&2` `&1543 / &500` `cT:real` `sT:real` THEN
   DISCH_THEN DISJ_CASES_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   prod `&0 <= (cE * cT - f * sT) * (((&7 / &2) * cE - &3 * f) - (uE + aE))` THEN
   prod `&0 <= (cE * sT + f * cT) * ((&3 * f + &3 * cE) - vE)` THEN
   SUBGOAL_THEN `&0 < (&1 + (cE * cT - f * sT)) * (aE - &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `(cE * cT - f * sT) * ((&7 / &2) * cE - &3 * f) +
     (cE * sT + f * cT) * (&3 * f + &3 * cE) =
     &3 * (cT + sT) + (&1 / &2) * cE * (cE * cT - f * sT)` MP_TAC THENL
   [UNDISCH_TAC `cE pow 2 + f pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   RASM_ARITH_TAC;
   use_sep `--sT:real` `cT:real` true
     (SPECL [`cT:real`; `sT:real`; `aE:real`; `cE:real`; `--f:real`; `aE:real`]
       ABT_TRANSVERSE_RADIUS) THEN
   sb qE `&3` `&3` `--sT:real` `cT:real` THEN
   sb qT `&12 / &5` `&3` `--sT:real` `cT:real` THEN
   DISCH_THEN DISJ_CASES_TAC THENL [ALL_TAC; RASM_ARITH_TAC] THEN
   prod `&0 <= (cE * sT + f * cT) * (((&7 / &2) * cE - &3 * f) - (uE + aE))` THEN
   prod `&0 <= (cE * cT - f * sT) * ((vE + aE) - (&3 * f + (&7 / &2) * cE))` THEN
   prod `&0 <= (cE * sT + f * cT) * (aE - &1)` THEN
   SUBGOAL_THEN
    `--(cE * sT + f * cT) * ((&7 / &2) * cE - &3 * f) +
     (cE * cT - f * sT) * (&3 * f + (&7 / &2) * cE) + (cE * sT + f * cT) -
     (&3 * cT - (&12 / &5) * sT) =
     cT * (&1 / &2 + f - f * (cE + f) / &2) + sT * (cE - &11 / &10 + f * (f - cE) / &2)`
   MP_TAC THENL
   [UNDISCH_TAC `cE pow 2 + f pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   RASM_ARITH_TAC]);;
