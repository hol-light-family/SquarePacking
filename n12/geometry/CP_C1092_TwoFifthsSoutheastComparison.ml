(* ========================================================================= *)
(* Port of Compact/Completion/C1092/TwoFifthsSoutheastComparison.lean        *)
(* (N12Compact.C1092TwoFifths).  The southeast square forces the canonical  *)
(* right slope below 2/5.  Southeast / Right are C1092TF_southeast /         *)
(* C1092TF_right; half is C1092WPS_half; upper/lower are ABT_upper/ABT_lower.*)
(* The Lean lets c s d r z A H B k q P Q are written out.                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSoutheastScalars.ml";;

let C1092TFSC_LIN = NLIN_TAC ~deg2:false [];;

let C1092TFSC_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092TFSC_LIN; ALL_TAC];;

let C1092TFSC_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C1092TFSC_LIN; ALL_TAC];;

let C1092TFSC_CONTRA = ONCE_REWRITE_TAC[GSYM REAL_NOT_LT; GSYM REAL_NOT_LE] THEN DISCH_TAC;;

let C1092TFSC_RING tm units = SUBGOAL_THEN tm ASSUME_TAC THENL
  [MAP_EVERY UNDISCH_TAC units THEN CONV_TAC REAL_RING; ALL_TAC];;

let C1092TFSC_POS_OF_MUL = prove
 (`forall k x. &0 < k /\ &0 < k * x ==> &0 < x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= k * --x` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* the southeast facts: unfolded structure, south bounds with z abbreviated *)
let C1092TFSC_SOUTH_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[C1092TF_southeast] o
    check (fun th -> can (term_match [] `C1092TF_southeast c s u v a`) (concl th))) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`] C1092TFSS_SOUTH_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  REWRITE_TAC[C1092TFSS_southBounds] THEN STRIP_TAC THEN
  ABBREV_TAC `z = C1092WPS_half cE sE` THEN
  POP_ASSUM(fun eq -> RULE_ASSUM_TAC(REWRITE_RULE[eq]) THEN ASSUME_TAC eq);;

let C1092TFSC_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

(* Lean: south_faces (private) *)
let C1092TFSC_SOUTH_FACES = prove
 (`forall cE sE uE vE aE.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ C1092TF_southeast cE sE uE vE aE
     ==> uE < &0 /\ --(&13 / &50) * sE < vE + aE /\
         aE - C1092WPS_half cE sE < uE + aE /\ &1 - C1092WPS_half cE sE < uE + aE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[C1092TF_southeast] o
    check (fun th -> can (term_match [] `C1092TF_southeast c s u v a`) (concl th))) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`] C1092TFSS_SOUTH_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  REWRITE_TAC[C1092TFSS_southBounds] THEN
  SPEC_TAC(`C1092WPS_half cE sE`,`z:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  C1092TFSC_UNFOLD_TAC `linside cE sE uE vE aE (&0) (--(&13 / &50))` THEN
  C1092TFSC_UNFOLD_TAC `linside cE sE uE vE aE (&13 / &50) (&0)` THEN
  C1092TFSC_PROD `&0 <= cE * --(vE + aE)` THEN
  C1092TFSC_PROD `&0 < (aE - &1) * cE` THEN
  C1092TFSC_FACT `&0 < sE * (uE + aE - (aE - z))` THEN
  MP_TAC(SPECL [`sE:real`; `uE + aE - (aE - z)`] C1092TFSC_POS_OF_MUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THEN C1092TFSC_LIN);;

(* Lean: south_transverse_blocked (private) *)
let C1092TFSC_SOUTH_TRANSVERSE_BLOCKED = prove
 (`forall cE sE uE vE aE cR sR uR vR aR.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     C1092TF_southeast cE sE uE vE aE /\ C1092TF_right cR sR uR vR aR /\
     ABT_upper cE sE uE vE aE sE (--cE) <= ABT_lower cR sR uR vR aR sE (--cE)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C1092TF_southeast; C1092TF_right]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  SUBGOAL_THEN `linside cR sR uR vR aR (&1) (&2 / &5)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `&0`; `--(&13 / &50)`; `sE:real`; `--cE:real`] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                `&1`; `&2 / &5`; `sE:real`; `--cE:real`] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  C1092TFSC_LIN);;

let C1092TFSC_RIGHT_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[C1092TF_right] o
    check (fun th -> can (term_match [] `C1092TF_right c s u v a`) (concl th))) THEN
  MAP_EVERY (fun y ->
    SUBGOAL_THEN (list_mk_comb(`linside cR sR uR vR aE (&1)`, [y])) ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 1)) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC])
   [`&2 / &5`; `--(&13 / &50)`; `&0`];;

(* Lean: southeast_negative_small *)
let C1092TFSC_SOUTHEAST_NEGATIVE_SMALL = prove
 (`forall cE sE uE vE aE cR sR uR vR aR r.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     C1092TF_southeast cE sE uE vE aE /\ C1092TF_right cR sR uR vR aR /\ aE = aR /\
     sR = --r /\ c977cc_normal cR r /\ ldisj cE sE uE vE aE cR sR uR vR aR
     ==> r < (&2 / &5) * cR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aE:real = aR`)) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] C1092TFSC_SOUTH_FACES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092TFSC_SOUTH_TAC THEN C1092TFSC_RIGHT_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aE:real`; `&13 / &50`; `&0`]
    C1092TFSU_NEGATIVE_AXES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    C1092TFSC_LIN; DISCH_TAC] THEN
  SUBGOAL_THEN `~(ABT_upper cE sE uE vE aE sE (--cE) <= ABT_lower cR sR uR vR aE sE (--cE))`
    ASSUME_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC C1092TFSC_SOUTH_TRANSVERSE_BLOCKED THEN
    MAP_EVERY EXISTS_TAC [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                          `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aE:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sR:real = --r`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NEG_NEG]) THEN
  C1092TFSC_UNFOLD_TAC `linside cR (--r) uR vR aE (&1) (&2 / &5)` THEN
  C1092TFSC_UNFOLD_TAC `linside cR (--r) uR vR aE (&1) (--(&13 / &50))` THEN
  C1092TFSC_PROD `&0 < (cE - sE) * cR` THEN C1092TFSC_PROD `&0 <= sE * (cR - r)` THEN
  C1092TFSC_PROD `&0 < sE * cR` THEN C1092TFSC_PROD `&0 <= cE * r` THEN
  C1092TFSC_CONTRA THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o check (is_disj o concl)) THENL
   [(* own *)
    MP_TAC(SPECL [`cR:real`; `--r:real`; `uR:real`; `vR:real`; `aE:real`; `cE:real`; `sE:real`;
                  `cE * cR - sE * r`; `sE * cR + cE * r`] C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      (REAL_ARITH_TAC ORELSE C1092TFSC_LIN); DISCH_TAC] THEN
    C1092TFSC_PROD `&0 < (cE * cR - sE * r) * ((cR - (&2 / &5) * r) - uR)` THEN
    C1092TFSC_PROD `&0 < (sE * cR + cE * r) * ((r - (&13 / &50) * cR) - vR)` THEN
    C1092TFSC_RING
     `(cE * cR - sE * r) * (cR - (&2 / &5) * r) + (sE * cR + cE * r) * (r - (&13 / &50) * cR) =
      cE - (&33 / &50) * cE * cR * r - sE * ((&13 / &50) * cR * cR - (&2 / &5) * r * r)`
     [`cR * cR + r * r = &1`] THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `z:real`; `cR:real`; `r:real`] C1092TFSS_NEGATIVE_LOSS) THEN
    ASM_REWRITE_TAC[C1092TFSS_southBounds; REAL_POW_2] THEN DISCH_TAC THEN
    C1092TFSC_LIN;
    (* transverse *)
    C1092TFSC_LIN;
    (* wallU *)
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `cR:real`; `--r:real`;
                  `cE * cR - sE * r`; `--(sE * cR + cE * r)`] C1092TFSU_UPPER_POS_NEG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      (REAL_ARITH_TAC ORELSE C1092TFSC_LIN); DISCH_TAC] THEN
    C1092TFSC_PROD `&0 < (cE * cR - sE * r) * ((uE + aE) - (&1 - z))` THEN
    C1092TFSC_PROD `&0 <= (sE * cR + cE * r) * (aE - (vE + aE) - &1)` THEN
    C1092TFSC_RING
     `(cE * cR - sE * r) * (&1 - z) + (sE * cR + cE * r) - cR = (&1 - sE) * (cR * z + r)`
     [`sE * z = &1 - cE`; `z * (&1 + cE) = sE`] THEN
    C1092TFSC_PROD `&0 < cR * z` THEN
    C1092TFSC_PROD `&0 < (&1 - sE) * (cR * z + r)` THEN
    C1092TFSC_LIN;
    (* wallV *)
    MP_TAC(REWRITE_RULE[REAL_NEG_NEG]
     (SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `-- --r:real`; `cR:real`;
             `sE * cR + cE * r`; `cE * cR - sE * r`] C1092TFSU_UPPER_POS_POS)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      (REAL_ARITH_TAC ORELSE C1092TFSC_LIN); DISCH_TAC] THEN
    C1092TFSC_PROD `&0 < (sE * cR + cE * r) * ((uE + aE) - (&1 - z))` THEN
    C1092TFSC_PROD `&0 < (cE * cR - sE * r) * ((vE + aE) + (&13 / &50) * sE)` THEN
    C1092TFSC_PROD `&0 < sE * (&1 - z - (&13 / &50) * cE)` THEN
    C1092TFSC_PROD `&0 < (cE - &47 / &50) * (&1 - z)` THEN
    C1092TFSC_PROD `&0 <= sE * sE` THEN
    C1092TFSC_FACT `--(&13 / &60) < cE * (&1 - z) + (&13 / &50) * sE * sE - &1` THEN
    C1092TFSC_PROD `&0 < cR * (sE * (&1 - z - (&13 / &50) * cE))` THEN
    C1092TFSC_PROD `&0 <= r * (cE * (&1 - z) + (&13 / &50) * sE * sE - &1 + &13 / &60)` THEN
    C1092TFSC_FACT `&0 < (sE * cR + cE * r) * (&1 - z) - (&13 / &50) * sE * (cE * cR - sE * r) -
                         (r - (&13 / &50) * cR)` THEN
    C1092TFSC_LIN]);;

(* Lean: southeast_positive_upper (private) *)
let C1092TFSC_SOUTHEAST_POSITIVE_UPPER = prove
 (`forall cE sE uE vE aE d r.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ C1092TF_southeast cE sE uE vE aE /\
     &0 < d /\ &0 < cE * d + sE * r /\ &0 <= cE * r - sE * d
     ==> (cE * d + sE * r) * (&1 - C1092WPS_half cE sE) < ABT_upper cE sE uE vE aE d r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `d:real`; `r:real`;
                `cE * d + sE * r`; `cE * r - sE * d`] C1092TFSU_UPPER_POS_POS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  C1092TFSC_SOUTH_TAC THEN
  SUBGOAL_THEN `sE * ((aE * (cE + sE) - &1) / sE) = aE * (cE + sE) - &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`(aE * (cE + sE) - &1) / sE`,`B:real`) THEN GEN_TAC THEN DISCH_TAC THEN
  C1092TFSC_PROD `&0 <= cE * --(vE + aE)` THEN
  C1092TFSC_FACT `&0 < sE * ((uE + aE) - B)` THEN
  MP_TAC(SPECL [`sE:real`; `(uE + aE) - B`] C1092TFSC_POS_OF_MUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092TFSC_PROD `&0 < (aE - &1) * (cE + sE)` THEN
  C1092TFSC_FACT `&0 < sE * (B - (&1 - z))` THEN
  MP_TAC(SPECL [`sE:real`; `B - (&1 - z)`] C1092TFSC_POS_OF_MUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092TFSC_PROD `&0 < d * ((uE + aE) - B)` THEN
  C1092TFSC_PROD `&0 <= (cE * r - sE * d) * (sE * (uE + aE) + cE * (vE + aE) - sE * B)` THEN
  C1092TFSC_RING
   `cE * (((cE * d + sE * r) * (uE + aE) + (cE * r - sE * d) * (vE + aE)) -
          (cE * d + sE * r) * B) =
    d * ((uE + aE) - B) + (cE * r - sE * d) * (sE * (uE + aE) + cE * (vE + aE) - sE * B)`
   [`cE * cE + sE * sE = &1`] THEN
  MP_TAC(SPECL [`cE:real`;
     `((cE * d + sE * r) * (uE + aE) + (cE * r - sE * d) * (vE + aE)) - (cE * d + sE * r) * B`]
     C1092TFSC_POS_OF_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092TFSC_LIN; DISCH_TAC] THEN
  C1092TFSC_PROD `&0 < (cE * d + sE * r) * (B - (&1 - z))` THEN
  C1092TFSC_LIN);;

(* Lean: southeast_positive_small *)
let C1092TFSC_SOUTHEAST_POSITIVE_SMALL = prove
 (`forall cE sE uE vE aE cR sR uR vR aR.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     C1092TF_southeast cE sE uE vE aE /\ C1092TF_right cR sR uR vR aR /\ aE = aR /\
     c977cc_normal cR sR /\ ldisj cE sE uE vE aE cR sR uR vR aR
     ==> sR < (&2 / &5) * cR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aE:real = aR`)) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] C1092TFSC_SOUTH_FACES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aE:real`; `sR:real`; `--cR:real`]
    C1092TFSU_WALL_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    C1092TFSC_LIN; DISCH_TAC] THEN
  C1092TFSC_SOUTH_TAC THEN C1092TFSC_RIGHT_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aE:real`; `&13 / &50`; `&0`]
    C1092TFSU_POSITIVE_AXES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    C1092TFSC_LIN; DISCH_TAC] THEN
  SUBGOAL_THEN `~(ABT_upper cE sE uE vE aE sE (--cE) <= ABT_lower cR sR uR vR aE sE (--cE))`
    ASSUME_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC C1092TFSC_SOUTH_TRANSVERSE_BLOCKED THEN
    MAP_EVERY EXISTS_TAC [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                          `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aE:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  C1092TFSC_UNFOLD_TAC `linside cR sR uR vR aE (&1) (&2 / &5)` THEN
  C1092TFSC_UNFOLD_TAC `linside cR sR uR vR aE (&1) (--(&13 / &50))` THEN
  C1092TFSC_PROD `&0 < cE * cR` THEN C1092TFSC_PROD `&0 <= sE * sR` THEN
  C1092TFSC_CONTRA THEN
  C1092TFSC_PROD `&0 < ((&2 / &5) * cE - sE) * cR` THEN
  C1092TFSC_PROD `&0 <= cE * (sR - (&2 / &5) * cR)` THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o check (is_disj o concl)) THENL
   [(* own *)
    MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aE:real`; `cE:real`; `sE:real`;
                  `cE * cR + sE * sR`; `--(cE * sR - sE * cR)`] C1092WS_LOWER_PN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      (REAL_ARITH_TAC ORELSE C1092TFSC_LIN); DISCH_TAC] THEN
    C1092TFSC_PROD `&0 < (cE * cR + sE * sR) * ((cR - (&13 / &50) * sR) - uR)` THEN
    C1092TFSC_PROD `&0 < (cE * sR - sE * cR) * ((vR + aE) - (--sR + (&2 / &5) * cR))` THEN
    C1092TFSC_RING
     `(cE * cR + sE * sR) * (cR - (&13 / &50) * sR) - (cE * sR - sE * cR) * (--sR + (&2 / &5) * cR) =
      cE - (&33 / &50) * cE * cR * sR + sE * ((&2 / &5) * cR * cR - (&13 / &50) * sR * sR)`
     [`cR * cR + sR * sR = &1`] THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `z:real`; `cR:real`; `sR:real`] C1092TFSS_POSITIVE_LOSS) THEN
    ASM_REWRITE_TAC[C1092TFSS_southBounds; REAL_POW_2] THEN DISCH_TAC THEN
    C1092TFSC_LIN;
    (* transverse *)
    C1092TFSC_LIN;
    (* wallU *)
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `cR:real`; `sR:real`]
      C1092TFSC_SOUTHEAST_POSITIVE_UPPER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092TFSC_LIN;
                    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
    C1092TFSC_PROD `&0 < sE * (&1 - z)` THEN
    C1092TFSC_PROD `&0 < cR * ((&2 / &5) * (&13 / &50 + sE * (&1 - z)) - z * (cE + sE))` THEN
    C1092TFSC_PROD `&0 <= (sR - (&2 / &5) * cR) * (&13 / &50 + sE * (&1 - z))` THEN
    C1092TFSC_RING
     `(cE * cR + sE * sR) * (&1 - z) - cR + (&13 / &50) * sR =
      --cR * (z * (cE + sE)) + sR * (&13 / &50 + sE * (&1 - z))`
     [`sE * z = &1 - cE`] THEN
    C1092TFSC_LIN;
    (* wallV *)
    C1092TFSC_PROD `&0 < (cE - &47 / &50) * cR` THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `sR:real`; `--cR:real`;
                  `cE * sR - sE * cR`; `--(cE * cR + sE * sR)`] C1092TFSU_UPPER_POS_NEG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      (REAL_ARITH_TAC ORELSE C1092TFSC_LIN); DISCH_TAC] THEN
    C1092TFSC_PROD `&0 <= (cE * sR - sE * cR) * (uE + aE)` THEN
    C1092TFSC_PROD `&0 <= (cE * cR + sE * sR) * (--vE - aE)` THEN
    SUBGOAL_THEN `abs sR = sR /\ abs(sR * cR + --cR * sR) = &0 /\
                  abs(--sR * sR + --cR * cR) = &1` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
        FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
      REWRITE_TAC[REAL_ARITH `sR * cR + --cR * sR = &0`; REAL_ABS_0;
                  REAL_ARITH `--sR * sR + --cR * cR = --(cR * cR + sR * sR)`] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `ABT_lower cR sR uR vR aE sR (--cR)`)) (concl th) &&
      can (find_term ((=) `abs`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aE:real`] C1092TFSU_LOWER_OPPOSITE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C1092TFSC_PROD `&0 <= sR * (cR + sR)` THEN
    C1092TFSC_PROD `&0 < (aE - &1) * (&1 + sR * (cR + sR))` THEN
    C1092TFSC_PROD `&0 <= sR * (cR - sR)` THEN
    MP_TAC(SPEC `sR - &1` REAL_LE_SQUARE) THEN DISCH_TAC THEN
    C1092TFSC_FACT `ABT_lower cR sR uR vR aE sR (--cR) < &1 / &2` THEN
    C1092TFSC_PROD `&0 < (aE - &1) * (cE * cR + sE * sR)` THEN
    C1092TFSC_LIN]);;
