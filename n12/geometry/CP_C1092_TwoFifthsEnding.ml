(* ========================================================================= *)
(* Port of Compact/Completion/C1092/TwoFifthsEnding.lean                     *)
(* (N12Compact.C1092TwoFifths).  The northeast square forbids both closed   *)
(* right-slope intervals at most 2/5; with the southeast comparison this    *)
(* excludes the three-square profile.  Northeast/Right/Input are             *)
(* C1092TF_northeast / C1092TF_right / C1092TF_input; the Lean lets          *)
(* b t d r k q C D are written out.                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSoutheastComparison.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsNortheastScalars.ml";;

let C1092TFEN_LIN = NLIN_TAC ~deg2:false [];;

let C1092TFEN_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092TFEN_LIN; ALL_TAC];;

let C1092TFEN_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C1092TFEN_LIN; ALL_TAC];;

let C1092TFEN_RING tm units = SUBGOAL_THEN tm ASSUME_TAC THENL
  [MAP_EVERY UNDISCH_TAC units THEN CONV_TAC REAL_RING; ALL_TAC];;

let C1092TFEN_ANTS = REPEAT CONJ_TAC THEN (REAL_ARITH_TAC ORELSE C1092TFEN_LIN);;

let C1092TFEN_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

(* Lean: north_normal (private) *)
let C1092TFEN_NORTH_NORMAL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ C1092TF_northeast c s u v a ==> c977cc_normal c s`,
  REWRITE_TAC[C1092TF_northeast; c977cc_normal; REAL_POW_2] THEN REPEAT STRIP_TAC THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: north_transverse (private) *)
let C1092TFEN_NORTH_TRANSVERSE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a ==> ABT_upper c s u v a s (--c) = --v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `--s:real`; `c:real`]
    C1092TFSU_UPPER_NEG) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG] THEN SIMP_TAC[]);;

(* northeast facts, with north bounds, as assumptions *)
let C1092TFEN_NORTH_TAC =
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] C1092TFEN_NORTH_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[C1092TF_northeast] o
    check (fun th -> can (term_match [] `C1092TF_northeast c s u v a`) (concl th))) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`] C1092TFNS_NORTH_BOUNDS) THEN
  ASM_REWRITE_TAC[C1092TFNS_northBounds; REAL_POW_2] THEN STRIP_TAC THEN
  C1092TFEN_UNFOLD_TAC `linside cN sN uN vN aN (&2 / &5) (&1)` THEN
  C1092TFEN_UNFOLD_TAC `linside cN sN uN vN aN (&7 / &20) (&7 / &20)`;;

let C1092TFEN_RIGHT_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[C1092TF_right] o
    check (fun th -> can (term_match [] `C1092TF_right c s u v a`) (concl th))) THEN
  MAP_EVERY (fun y ->
    SUBGOAL_THEN (list_mk_comb(`linside cR sR uR vR aN (&1)`, [y])) ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 1)) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC])
   [`&2 / &5`; `--(&13 / &50)`; `&0`; `&7 / &20`];;

(* Lean: north_longitudinal_blocked (private) *)
let C1092TFEN_NORTH_LONGITUDINAL_BLOCKED = prove
 (`forall cN sN uN vN aN cR sR uR vR aR.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     C1092TF_northeast cN sN uN vN aN /\ C1092TF_right cR sR uR vR aR
     ==> ~(uN + aN <= ABT_lower cR sR uR vR aR cN sN)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN C1092TFEN_NORTH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[C1092TF_right] o
    check (fun th -> can (term_match [] `C1092TF_right c s u v a`) (concl th))) THEN
  SUBGOAL_THEN `linside cR sR uR vR aR (&1) (--(&13 / &50))` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1)) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                `&1`; `--(&13 / &50)`; `cN:real`; `sN:real`] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; STRIP_TAC] THEN
  C1092TFEN_LIN);;

let C1092TFEN_PRE_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aN:real = aR`)) THEN
  SUBGOAL_THEN `~(uN + aN <= ABT_lower cR sR uR vR aN cN sN)` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092TFEN_NORTH_LONGITUDINAL_BLOCKED THEN EXISTS_TAC `vN:real` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_upper cN sN uN vN aN sN (--cN) = --vN` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092TFEN_NORTH_TRANSVERSE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  C1092TFEN_NORTH_TAC THEN C1092TFEN_RIGHT_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> is_comb(concl th) && rator(concl th) = `c977cc_normal cR`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> is_comb(concl th) && rator(concl th) = `c977cc_normal cR`));;

(* Lean: northeast_negative_impossible *)
let C1092TFEN_NORTHEAST_NEGATIVE_IMPOSSIBLE = prove
 (`forall cN sN uN vN aN cR sR uR vR aR r.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     C1092TF_northeast cN sN uN vN aN /\ C1092TF_right cR sR uR vR aR /\ aN = aR /\
     sR = --r /\ c977cc_normal cR r /\ r <= (&2 / &5) * cR /\
     ldisj cN sN uN vN aN cR sR uR vR aR
     ==> false`,
  C1092TFEN_PRE_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aN:real`; `&7 / &20`; `&7 / &20`]
    C1092TFSU_NEGATIVE_AXES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    C1092TFEN_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aN:real`; `sN:real`; `--cN:real`]
    C1092TFSU_WALL_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092TFEN_ANTS; DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sR:real = --r`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NEG_NEG]) THEN
  C1092TFEN_UNFOLD_TAC `linside cR (--r) uR vR aN (&1) (&2 / &5)` THEN
  C1092TFEN_UNFOLD_TAC `linside cR (--r) uR vR aN (&1) (--(&13 / &50))` THEN
  C1092TFEN_PROD `&0 < cR * (cN - (&2 / &5) * sN)` THEN
  C1092TFEN_PROD `&0 <= sN * ((&2 / &5) * cR - r)` THEN
  C1092TFEN_PROD `&0 < sN * cR` THEN C1092TFEN_PROD `&0 <= cN * r` THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o check (is_disj o concl)) THENL
   [(* own *)
    C1092TFEN_LIN;
    (* transverse *)
    MP_TAC(SPECL [`cN:real`; `sN:real`; `cR:real`; `r:real`] C1092TFNS_NEGATIVE_WIDTH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs(--r) = r /\ abs(sN * cR + --cN * --r) = sN * cR + cN * r /\
                  abs(--sN * --r + --cN * cR) = cN * cR - sN * r`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[REAL_ABS_NEG] THEN REPEAT CONJ_TAC THEN
      TRY(MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN C1092TFEN_LIN THEN NO_TAC) THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ (x = y \/ x = --y) ==> abs x = y`) THEN
      (CONJ_TAC THENL [C1092TFEN_LIN; REAL_ARITH_TAC]); ALL_TAC] THEN
    C1092TFEN_PROD `&0 < (aN - &1) * ((&2 * sN + cN) * cR + cN * r)` THEN
    C1092TFEN_LIN;
    (* wallU *)
    MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `cR:real`; `--r:real`;
                  `cN * cR - sN * r`; `--(sN * cR + cN * r)`] C1092TFSU_UPPER_POS_NEG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092TFEN_ANTS; DISCH_TAC] THEN
    C1092TFEN_PROD `&0 <= (cN * cR - sN * r) * (uN - (&2 / &5) * sN)` THEN
    C1092TFEN_PROD `&0 <= (sN * cR + cN * r) * (cN - aN - vN)` THEN
    C1092TFEN_PROD `&0 < (aN - &1) * ((cN * cR - sN * r) + (sN * cR + cN * r))` THEN
    C1092TFEN_RING
     `(cN * cR - sN * r) + (sN * cR + cN * r) + (&2 / &5) * sN * (cN * cR - sN * r) -
      cN * (sN * cR + cN * r) =
      cR * (cN + sN - (&3 / &5) * cN * sN) + r * (cN - sN - &1 + (&3 / &5) * sN * sN)`
     [`cN * cN + sN * sN = &1`] THEN
    C1092TFEN_PROD `&0 < cR * ((cN + sN - (&3 / &5) * cN * sN) - &11 / &10)` THEN
    C1092TFEN_PROD `&0 <= r * ((cN - sN - &1 + (&3 / &5) * sN * sN) + &2 / &5 + &23 / &125)` THEN
    C1092TFEN_LIN;
    (* wallV *)
    MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                  `&2 / &5`; `&1`; `r:real`; `cR:real`] ABT_STRICT_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    C1092TFEN_LIN]);;

(* Lean: northeast_positive_impossible *)
let C1092TFEN_NORTHEAST_POSITIVE_IMPOSSIBLE = prove
 (`forall cN sN uN vN aN cR sR uR vR aR.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     C1092TF_northeast cN sN uN vN aN /\ C1092TF_right cR sR uR vR aR /\ aN = aR /\
     c977cc_normal cR sR /\ sR <= (&2 / &5) * cR /\
     ldisj cN sN uN vN aN cR sR uR vR aR
     ==> false`,
  C1092TFEN_PRE_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aN:real`; `&7 / &20`; `&7 / &20`]
    C1092TFSU_POSITIVE_AXES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    C1092TFEN_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aN:real`; `sN:real`; `--cN:real`]
    C1092TFSU_WALL_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092TFEN_ANTS; DISCH_TAC] THEN
  C1092TFEN_UNFOLD_TAC `linside cR sR uR vR aN (&1) (&0)` THEN
  C1092TFEN_PROD `&0 < cN * cR` THEN C1092TFEN_PROD `&0 <= sN * sR` THEN
  C1092TFEN_PROD `&0 < cR * (sN - (&2 / &5) * cN)` THEN
  C1092TFEN_PROD `&0 <= cN * ((&2 / &5) * cR - sR)` THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o check (is_disj o concl)) THENL
   [(* own *)
    C1092TFEN_LIN;
    (* transverse *)
    MP_TAC(SPECL [`cN:real`; `sN:real`; `cR:real`; `sR:real`] C1092TFNS_POSITIVE_WIDTH) THEN
    ASM_REWRITE_TAC[C1092TFNS_northBounds; REAL_POW_2] THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs sR = sR /\ abs(sN * cR + --cN * sR) = sN * cR - cN * sR /\
                  abs(--sN * sR + --cN * cR) = cN * cR + sN * sR`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REPEAT CONJ_TAC THEN
      TRY(MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN C1092TFEN_LIN THEN NO_TAC) THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ (x = y \/ x = --y) ==> abs x = y`) THEN
      (CONJ_TAC THENL [C1092TFEN_LIN; REAL_ARITH_TAC]); ALL_TAC] THEN
    C1092TFEN_PROD `&0 <= (&2 * sN - cN) * sR` THEN
    C1092TFEN_PROD `&0 < (aN - &1) * ((&2 * sN + cN) * cR + (&2 * sN - cN) * sR)` THEN
    C1092TFEN_LIN;
    (* wallU *)
    MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `cR:real`; `sR:real`;
                  `cN * cR + sN * sR`; `--(sN * cR - cN * sR)`] C1092TFSU_UPPER_POS_NEG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092TFEN_ANTS; DISCH_TAC] THEN
    C1092TFEN_PROD `&0 <= (cN * cR + sN * sR) * (uN - (&2 / &5) * sN)` THEN
    C1092TFEN_PROD `&0 <= (sN * cR - cN * sR) * (cN - aN - vN)` THEN
    C1092TFEN_PROD `&0 < (aN - &1) * ((cN * cR + sN * sR) + (sN * cR - cN * sR))` THEN
    C1092TFEN_RING
     `(cN * cR + sN * sR) + (sN * cR - cN * sR) + (&2 / &5) * sN * (cN * cR + sN * sR) -
      cN * (sN * cR - cN * sR) =
      cR * (cN + sN - (&3 / &5) * cN * sN) + sR * (&1 + sN - cN - (&3 / &5) * sN * sN)`
     [`cN * cN + sN * sN = &1`] THEN
    C1092TFEN_PROD `&0 < sN * (&1 - (&3 / &5) * sN)` THEN
    C1092TFEN_FACT `&0 < &1 + sN - cN - (&3 / &5) * sN * sN` THEN
    C1092TFEN_PROD `&0 < cR * ((cN + sN - (&3 / &5) * cN * sN) - &1)` THEN
    C1092TFEN_PROD `&0 <= sR * (&1 + sN - cN - (&3 / &5) * sN * sN)` THEN
    C1092TFEN_LIN;
    (* wallV *)
    MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                  `&47 / &100`; `&3 / &25`; `sR:real`; `--cR:real`] ABT_STRICT_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
      ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aN:real`;
                  `&1`; `&2 / &5`; `sR:real`; `--cR:real`] ABT_STRICT_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
      ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aN:real`] C1092TFSU_LOWER_OPPOSITE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C1092TFEN_LIN]);;

(* Lean: impossible *)
let C1092TFEN_IMPOSSIBLE = prove
 (`forall cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     C1092TF_input cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C1092TF_input] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] C1092TF_CANONICAL_RIGHT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cQ:real` (X_CHOOSE_THEN `sQ:real` (X_CHOOSE_THEN `uQ:real`
    (X_CHOOSE_THEN `vQ:real` (X_CHOOSE_THEN `aQ:real` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                `cQ:real`; `sQ:real`; `uQ:real`; `vQ:real`; `aQ:real`] C1092TF_RIGHT_REFRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aQ:real = aR`)) THEN
  SUBGOAL_THEN `ldisj cE sE uE vE aE cQ sQ uQ vQ aR /\ ldisj cN sN uN vN aN cQ sQ uQ vQ aR`
    STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN REWRITE_TAC[ldisj] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ABS_BOUNDS]) THEN
  ASM_CASES_TAC `&0 <= sQ` THENL
   [SUBGOAL_THEN `c977cc_normal cQ sQ` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                  `cQ:real`; `sQ:real`; `uQ:real`; `vQ:real`; `aR:real`]
      C1092TFSC_SOUTHEAST_POSITIVE_SMALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MATCH_MP_TAC C1092TFEN_NORTHEAST_POSITIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                          `cQ:real`; `sQ:real`; `uQ:real`; `vQ:real`; `aR:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_normal cQ (--sQ)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cQ:real`; `sQ:real`; `uQ:real`; `vQ:real`; `aR:real`; `--sQ:real`]
    C1092TFSC_SOUTHEAST_NEGATIVE_SMALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_NEG_NEG]; DISCH_TAC] THEN
  MATCH_MP_TAC C1092TFEN_NORTHEAST_NEGATIVE_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                        `cQ:real`; `sQ:real`; `uQ:real`; `vQ:real`; `aR:real`; `--sQ:real`] THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC);;
