(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MixedCornerObstruction.lean               *)
(* (N12Compact.C1092MixedCornerObstruction).  The actual mixed wall L cannot *)
(* be disjoint from a corner K owning both vertical anchors while K omits    *)
(* the upper point (1/5,1).  L = cL sL uL vL aL, K = cK sK uK vK aK.         *)
(* lower/upper: ABT_lower/ABT_upper; WholeSupports: C1092WS_*;               *)
(* MixedCornerSupports: C1092MCSUP_*; MixedCornerScalars: C1092MCS_*;        *)
(* MixedCornerAxes: C1092MCA_*; canonical_frame: CLF_CANONICAL_FRAME.        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MixedCornerAxes.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let C1092MCO_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092MCO_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092MCO_LP_TAC; ALL_TAC];;

let C1092MCO_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
                  FIRST [REAL_ARITH_TAC; C1092MCO_LP_TAC]; DISCH_TAC];;

let C1092MCO_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let C1092MCO_STRICT_TAC (c,s,u,v) (x,y) (nx,ny) =
  MP_TAC(SPECL [c; s; u; v; `aL:real`; x; y; nx; ny] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
   REPEAT CONJ_TAC THEN RASM_ARITH_TAC; STRIP_TAC];;

(* the unit equations multiplied by the other square's coordinates *)
let C1092MCO_UNITS_TAC =
  SUBGOAL_THEN `sL * (cK * cK + sK * sK) = sL /\ cK * (cL * cL + sL * sL) = cK`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC];;

let C1092MCO_qL = (`cL:real`,`sL:real`,`uL:real`,`vL:real`);;

(* Lean: nonnegative (private) *)
let C1092MCO_NONNEGATIVE = prove
 (`forall cL sL uL vL aL cK sK uK vK aK.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     &1 < aL /\ aL = aK /\ c977cc_normal cL sL /\ &0 < sL /\ c977cc_normal cK sK /\
     linside cL sL uL vL aL (&0) (&2 / &5) /\ --(&2 / &5) * cL <= vL /\
     linside cK sK uK vK aK (&0) (&1 / &2) /\ linside cK sK uK vK aK (&0) (&1) /\
     ~linside cK sK uK vK aK (&1 / &5) (&1) /\
     ldisj cL sL uL vL aL cK sK uK vK aK
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aK`)) THEN
  SUBGOAL_THEN `~linside cL sL uL vL aL (&0) (&1 / &2)` ASSUME_TAC THENL
  [DISCH_TAC THEN UNDISCH_TAC `ldisj cL sL uL vL aL cK sK uK vK aL` THEN
   REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&0`; `&1 / &2`]) THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  C1092MCO_USE C1092MCSUP_UPPER_CAP [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] THEN
  C1092MCO_USE C1092MCS_ELEMENTARY [`cK:real`; `sK:real`] THEN
  C1092MCO_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < cK` ASSUME_TAC THENL [C1092MCO_LP_TAC; ALL_TAC] THEN
  C1092MCO_UNITS_TAC THEN
  C1092MCO_USE C1092MCA_ALTERNATIVES
    [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
     `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aL:real`] THEN
  C1092MCO_STRICT_TAC C1092MCO_qL (`&0`,`&2 / &5`) (`cK:real`,`sK:real`) THEN
  C1092MCO_USE C1092MCSUP_UP_LEFT
    [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `cK:real`; `sK:real`] THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th) THEN
  SUBGOAL_THEN `uK + aL <= (&1 / &5) * cK + sK` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   UNDISCH_TAC `~linside cK sK uK vK aL (&1 / &5) (&1)` THEN REWRITE_TAC[linside] THEN
   C1092MCO_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sK <= &3 / &4` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  C1092MCO_PROD `&0 < cL * cK` THEN C1092MCO_PROD `&0 <= sL * sK` THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN ASSUME_TAC) o
    check (is_disj o concl)) THENL
  [ASM_CASES_TAC `&0 <= sL * cK - cL * sK` THENL
   [C1092MCO_USE C1092WS_LOWER_NN
      [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aL:real`; `cL:real`; `sL:real`;
       `cL * cK + sL * sK`; `sL * cK - cL * sK`] THEN
    C1092MCO_PROD `&0 < (cL * cK + sL * sK) * (((&1 / &5) * cK + sK - &1) - uK)` THEN
    C1092MCO_PROD `&0 <= (sL * cK - cL * sK) * (cK / &2 - vK)` THEN
    C1092MCO_USE C1092MCS_NONNEGATIVE_PAIR [`cL:real`; `sL:real`; `cK:real`; `sK:real`] THEN
    C1092MCO_LP_TAC;
    C1092MCO_USE C1092WS_LOWER_PN
      [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aL:real`; `cL:real`; `sL:real`;
       `cL * cK + sL * sK`; `sL * cK - cL * sK`] THEN
    C1092MCO_PROD `&0 < (cL * cK + sL * sK) * --uK` THEN
    C1092MCO_PROD `&0 <= --(sL * cK - cL * sK) * (vK + aL)` THEN
    C1092MCO_LP_TAC];
   C1092MCO_LP_TAC;
   C1092MCO_LP_TAC]);;

(* Lean: nonpositive (private) *)
let C1092MCO_NONPOSITIVE = prove
 (`forall cL sL uL vL aL cK sK uK vK aK.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     &1 < aL /\ aL = aK /\ c977cc_normal cL sL /\ &0 < sL /\ c977cc_normal cK (--sK) /\
     linside cL sL uL vL aL (&0) (&2 / &5) /\ --(&2 / &5) * cL <= vL /\
     linside cK sK uK vK aK (&0) (&1 / &2) /\ linside cK sK uK vK aK (&0) (&1) /\
     ~linside cK sK uK vK aK (&1 / &5) (&1) /\
     ldisj cL sL uL vL aL cK sK uK vK aK
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aK`)) THEN
  C1092MCO_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < cK` ASSUME_TAC THENL [C1092MCO_LP_TAC; ALL_TAC] THEN
  C1092MCO_UNITS_TAC THEN
  C1092MCO_USE C1092MCA_ALTERNATIVES
    [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
     `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aL:real`] THEN
  C1092MCO_USE C1092MCS_COMMON [`cL:real`; `sL:real`] THEN
  C1092MCO_STRICT_TAC C1092MCO_qL (`&0`,`&2 / &5`) (`cK:real`,`sK:real`) THEN
  C1092MCO_STRICT_TAC C1092MCO_qL (`&0`,`&2 / &5`) (`--sK:real`,`cK:real`) THEN
  C1092MCO_PROD `&0 <= cL * (cK - --sK)` THEN C1092MCO_PROD `&0 <= --sK * (cL - sL)` THEN
  C1092MCO_PROD `&0 <= cL * --sK` THEN C1092MCO_PROD `&0 < sL * cK` THEN
  SUBGOAL_THEN `&0 <= cL * cK + sL * sK /\ &0 < --cL * sK + sL * cK` STRIP_ASSUME_TAC THENL
  [C1092MCO_LP_TAC; ALL_TAC] THEN
  C1092MCO_USE C1092WS_LOWER_NN
    [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aL:real`; `cL:real`; `sL:real`;
     `cL * cK + sL * sK`; `--cL * sK + sL * cK`] THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th) THEN
  SUBGOAL_THEN `uK + aL <= (&1 / &5) * cK + sK \/ vK + aL <= cK - (&1 / &5) * sK`
  ASSUME_TAC THENL
  [ASM_CASES_TAC `uK + aL <= (&1 / &5) * cK + sK` THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   UNDISCH_TAC `~linside cK sK uK vK aL (&1 / &5) (&1)` THEN REWRITE_TAC[linside] THEN
   C1092MCO_LP_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term ((=) `(&1 / &5) * cK + sK`)) (concl th))) THENL
  [(* upper-u exit *)
   SUBGOAL_THEN `--sK < (&2 / &5) * cK` ASSUME_TAC THENL [C1092MCO_LP_TAC; ALL_TAC] THEN
   C1092MCO_USE C1092MCS_UPPER_U_PAIR [`cL:real`; `sL:real`; `cK:real`; `--sK:real`] THEN
   FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN ASSUME_TAC) o
     check (fun th -> is_disj(concl th) &&
       can (find_term ((=) `ABT_lower cK sK uK vK aL cL sL`)) (concl th))) THENL
   [C1092MCO_PROD `&0 <= (cL * cK + sL * sK) * (((&1 / &5) * cK + sK - &1) - uK)` THEN
    C1092MCO_PROD `&0 < (--cL * sK + sL * cK) * (cK / &2 - vK)` THEN
    C1092MCO_LP_TAC;
    C1092MCO_LP_TAC;
    C1092MCO_USE C1092MCSUP_UPPER_NN
      [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `--sK:real`; `cK:real`;
       `--cL * sK + sL * cK`; `cL * cK + sL * sK`] THEN
    C1092MCO_PROD `&0 < (--cL * sK + sL * cK) * ((uL + aL) - (&2 / &5) * sL)` THEN
    C1092MCO_PROD `&0 <= (cL * cK + sL * sK) * ((vL + aL) - (&1 - (&2 / &5) * cL))` THEN
    C1092MCO_PROD `&0 < cK * (cL - &9 / &10 + (&4 / &5) * sL pow 2 -
                               (&2 / &5) * (sL * (&1 - (&4 / &5) * cL)))` THEN
    C1092MCO_PROD `&0 < ((&2 / &5) * cK - --sK) * (sL * (&1 - (&4 / &5) * cL))` THEN
    C1092MCO_LP_TAC];
   (* upper-v exit *)
   FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN ASSUME_TAC) o
     check (fun th -> is_disj(concl th) &&
       can (find_term ((=) `ABT_lower cK sK uK vK aL cL sL`)) (concl th))) THENL
   [C1092MCO_PROD `&0 <= (cL * cK + sL * sK) * (sK - uK)` THEN
    C1092MCO_PROD `&0 < (--cL * sK + sL * cK) * ((cK - (&1 / &5) * sK - &1) - vK)` THEN
    C1092MCO_USE C1092MCS_UPPER_V_PAIR [`cL:real`; `sL:real`; `cK:real`; `--sK:real`] THEN
    C1092MCO_LP_TAC;
    C1092MCO_LP_TAC;
    C1092MCO_LP_TAC]]);;

(* Lean: impossible *)
let C1092MCO_IMPOSSIBLE = prove
 (`forall cL sL uL vL aL cK sK uK vK aK.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     &1 < aL /\ aL = aK /\ c977cc_normal cL sL /\ &0 < sL /\
     linside cL sL uL vL aL (&0) (&2 / &5) /\ --(&2 / &5) * cL <= vL /\
     linside cK sK uK vK aK (&0) (&1 / &2) /\ linside cK sK uK vK aK (&0) (&1) /\
     ~linside cK sK uK vK aK (&1 / &5) (&1) /\
     ldisj cL sL uL vL aL cK sK uK vK aK
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ldisj cL sL uL vL aL cR sR uR vR aR` ASSUME_TAC THENL
  [UNDISCH_TAC `ldisj cL sL uL vL aL cK sK uK vK aK` THEN ASM_REWRITE_TAC[ldisj]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= sR` THENL
  [MATCH_MP_TAC C1092MCO_NONNEGATIVE; MATCH_MP_TAC C1092MCO_NONPOSITIVE] THEN
  MAP_EVERY EXISTS_TAC [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                        `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] THEN
  ASM_REWRITE_TAC[c977cc_normal] THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ABS_BOUNDS]) THEN ASM_REAL_ARITH_TAC);;
