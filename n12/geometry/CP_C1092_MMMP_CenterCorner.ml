(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/CenterCorner.lean                    *)
(* (N12Compact.C1092MMMPCenterCorner).  The left-wall centre cut replaces    *)
(* the lower-face hypothesis of MixedCornerObstruction.  L = cL sL uL vL aL, *)
(* K = cK sK uK vK aK; centerX/centerY are lcx/lcy; upper/lower ABT_*;       *)
(* MixedCorner tools: C1092MCO / C1092MCS / C1092MCSUP / C1092MCA tags.      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MixedCornerObstruction.ml";;
needs "n12/geometry/CP_C1092_MMMP_LeftCenterFaces.ml";;

(* Lean: up_left *)
let C1092MMCC_UP_LEFT = prove
 (`forall c s u v a nx ny.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     lcx c s u v a <= &0 /\ &0 <= lcy c s u v a /\
     nx pow 2 + ny pow 2 = &1 /\ nx <= &0 /\ &0 <= ny
     ==> ny / &2 < ABT_upper c s u v a nx ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ABT_upper; tss_support_radius] THEN
  ABBREV_TAC `U = nx * c + ny * s` THEN ABBREV_TAC `V = --nx * s + ny * c` THEN
  SUBGOAL_THEN `U * U + V * V = &1` ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["U"; "V"] THEN UNDISCH_TAC `c * c + s * s = &1` THEN
   UNDISCH_TAC `nx pow 2 + ny pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= abs U + abs V` ASSUME_TAC THENL
  [MP_TAC(SPEC `U:real` REAL_ABS_POS) THEN MP_TAC(SPEC `V:real` REAL_ABS_POS) THEN
   MP_TAC(SPEC `U:real` REAL_POW2_ABS) THEN MP_TAC(SPEC `V:real` REAL_POW2_ABS) THEN
   REWRITE_TAC[REAL_POW_2] THEN REPEAT DISCH_TAC THEN
   REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092MCO_PROD `&0 <= abs U * abs V` THEN
   C1092MCO_PROD `&0 < (&1 - (abs U + abs V)) * (&1 + (abs U + abs V))` THEN
   C1092MCO_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ny <= &1` ASSUME_TAC THENL
  [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC [SQ_NONNEG `nx:real`]; ALL_TAC] THEN
  C1092MCO_PROD `&0 <= --nx * --lcx c s u v a` THEN
  C1092MCO_PROD `&0 <= ny * lcy c s u v a` THEN
  C1092MCO_PROD `&0 < (a - &1) * (abs U + abs V)` THEN
  C1092MCO_LP_TAC);;

(* Lean: up_right *)
let C1092MMCC_UP_RIGHT = prove
 (`forall cL sL uL vL aL c s.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ &1 < aL /\ c977cc_normal cL sL /\ &0 < sL /\
     linside cL sL uL vL aL (&0) (&2 / &5) /\ &0 <= lcy cL sL uL vL aL /\
     c977cc_normal c s /\ s < (&2 / &5) * c
     ==> c / &2 < ABT_upper cL sL uL vL aL s c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MCO_NORMAL_TAC THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th) THEN
  C1092MCO_PROD `&0 < cL * (c - s)` THEN C1092MCO_PROD `&0 <= s * (cL - sL)` THEN
  C1092MCO_PROD `&0 <= s * cL` THEN C1092MCO_PROD `&0 < c * sL` THEN
  SUBGOAL_THEN `&0 < c * cL - s * sL /\ &0 < s * cL + c * sL` STRIP_ASSUME_TAC THENL
  [C1092MCO_LP_TAC; ALL_TAC] THEN
  C1092MCO_USE C1092MCSUP_UPPER_NN
    [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `s:real`; `c:real`;
     `s * cL + c * sL`; `c * cL - s * sL`] THEN
  SUBGOAL_THEN `s * (uL + aL) * (cL * cL + sL * sL) = s * (uL + aL)` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcy]) THEN
  C1092MCO_PROD `&0 <= s * ((uL + aL) - (&2 / &5) * sL)` THEN
  C1092MCO_PROD `&0 <= (c * cL - s * sL) * (sL * (uL + aL / &2) + cL * (vL + aL / &2))` THEN
  C1092MCO_PROD `&0 < (aL - &1) * ((c * cL - s * sL) * (cL + sL))` THEN
  SUBGOAL_THEN `&1 < cL + sL / &2` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT; REAL_NOT_LT] THEN
   REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092MCO_PROD `&0 < sL * (cL - (&3 / &4) * sL)` THEN
   C1092MCO_PROD `&0 <= (&1 - (cL + sL / &2)) * (&1 + (cL + sL / &2))` THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092MCO_LP_TAC; ALL_TAC] THEN
  C1092MCO_PROD `&0 < cL * ((cL + sL / &2) - &1)` THEN
  C1092MCO_PROD `&0 < sL * (cL / &2 - (&2 / &5) * (cL + sL - &4 / &5))` THEN
  SUBGOAL_THEN `&0 < cL * (cL + sL - &1) - (&2 / &5) * sL * (cL + sL - &4 / &5)` ASSUME_TAC
  THENL [C1092MCO_LP_TAC; ALL_TAC] THEN
  C1092MCO_PROD `&0 < c * (cL * (cL + sL - &1) - (&2 / &5) * sL * (cL + sL - &4 / &5))` THEN
  C1092MCO_PROD `&0 < ((&2 / &5) * c - s) * (sL * (cL + sL - &4 / &5))` THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092MCO_PROD `&0 <= cL * (c / &2 - ABT_upper cL sL uL vL aL s c)` THEN
  FIRST_ASSUM(ASSUME_TAC o AP_TERM `(*) (cL:real)` o check (fun th ->
    is_eq(concl th) && lhand(concl th) = `ABT_upper cL sL uL vL aL s c`)) THEN
  C1092MCO_LP_TAC);;

(* Lean: left_blocked (private) *)
let C1092MMCC_LEFT_BLOCKED = prove
 (`forall cL sL uL vL aL cK sK uK vK aK nx ny.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     &1 < aL /\ lcx cL sL uL vL aL <= &0 /\ &0 <= lcy cL sL uL vL aL /\
     linside cL sL uL vL aL (&0) (&2 / &5) /\ linside cK sK uK vK aK (&0) (&1 / &2) /\
     nx pow 2 + ny pow 2 = &1 /\ nx <= &0 /\
     ABT_upper cL sL uL vL aL nx ny <= ABT_lower cK sK uK vK aK nx ny
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                `nx:real`; `ny:real`] C1092MCSUP_UPWARD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `nx:real`; `ny:real`] C1092MMCC_UP_LEFT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                `&0`; `&1 / &2`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: reverse_blocked (private) *)
let C1092MMCC_REVERSE_BLOCKED = C1092MCA_REVERSE_BLOCKED;;

(* Lean: alternatives *)
let C1092MMCC_ALTERNATIVES = prove
 (`forall cL sL uL vL aL cK sK uK vK aK.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     &1 < aL /\ aL = aK /\ c977cc_normal cL sL /\ &0 < sL /\ &0 < cK /\
     lcx cL sL uL vL aL <= &0 /\ &0 <= lcy cL sL uL vL aL /\
     linside cL sL uL vL aL (&0) (&2 / &5) /\
     linside cK sK uK vK aK (&0) (&1 / &2) /\
     ldisj cL sL uL vL aL cK sK uK vK aK
     ==> uL + aL <= ABT_lower cK sK uK vK aK cL sL \/
         ABT_upper cL sL uL vL aL cK sK <= uK \/
         ABT_upper cL sL uL vL aL (--sK) cK <= vK`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aK`)) THEN
  SUBGOAL_THEN `&0 < cL` ASSUME_TAC THENL
  [FIRST_ASSUM(MP_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cL pow 2 + sL pow 2 = &1 /\ (--sL) pow 2 + cL pow 2 = &1 /\
                cK pow 2 + sK pow 2 = &1 /\ (--sK) pow 2 + cK pow 2 = &1 /\
                (--cK) pow 2 + (--sK) pow 2 = &1` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aL:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aL:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aL:real`] ABT_FOUR_AXES) THEN
  ASM_REWRITE_TAC[] THEN
  let lb nx ny =
    MATCH_MP_TAC(TAUT `false ==> p`) THEN
    MATCH_MP_TAC C1092MMCC_LEFT_BLOCKED THEN
    MAP_EVERY EXISTS_TAC [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                          `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aL:real`; nx; ny] THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC
  and rb nx ny =
    MATCH_MP_TAC(TAUT `false ==> p`) THEN
    MATCH_MP_TAC C1092MMCC_REVERSE_BLOCKED THEN
    MAP_EVERY EXISTS_TAC [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                          `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aL:real`; nx; ny] THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC in
  REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
  [ASM_REWRITE_TAC[];
   rb `cL:real` `sL:real`;
   lb `--sL:real` `cL:real`;
   rb `--sL:real` `cL:real`;
   ASM_REWRITE_TAC[];
   MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `cK:real`; `sK:real`]
     C1092MCSUP_NEGATIVE_SUPPORT) THEN
   MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aL:real`; `cK:real`; `sK:real`]
     C1092MCSUP_NEGATIVE_SUPPORT) THEN
   REPEAT STRIP_TAC THEN lb `--cK:real` `--sK:real`;
   ASM_REWRITE_TAC[];
   rb `--sK:real` `cK:real`]);;

(* Lean: nonnegative (private) *)
let C1092MMCC_NONNEGATIVE = prove
 (`forall cL sL uL vL aL cK sK uK vK aK.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     &1 < aL /\ aL = aK /\ c977cc_normal cL sL /\ &0 < sL /\ c977cc_normal cK sK /\
     linside cL sL uL vL aL (&0) (&2 / &5) /\ lcx cL sL uL vL aL <= &0 /\ &0 <= lcy cL sL uL vL aL /\
     linside cK sK uK vK aK (&0) (&1 / &2) /\ linside cK sK uK vK aK (&0) (&1) /\
     ~linside cK sK uK vK aK (&1 / &5) (&1) /\
     ldisj cL sL uL vL aL cK sK uK vK aK
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aK`)) THEN
  C1092MCO_USE C1092MCS_ELEMENTARY [`cK:real`; `sK:real`] THEN
  C1092MCO_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < cK` ASSUME_TAC THENL [C1092MCO_LP_TAC; ALL_TAC] THEN
  C1092MCO_UNITS_TAC THEN
  C1092MCO_USE C1092MMCC_ALTERNATIVES
    [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
     `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aL:real`] THEN
  C1092MCO_STRICT_TAC C1092MCO_qL (`&0`,`&2 / &5`) (`cK:real`,`sK:real`) THEN
  SUBGOAL_THEN `(--sK) pow 2 + cK pow 2 = &1` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MCO_USE C1092MMCC_UP_LEFT
    [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `--sK:real`; `cK:real`] THEN
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
let C1092MMCC_NONPOSITIVE = prove
 (`forall cL sL uL vL aL cK sK uK vK aK.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     &1 < aL /\ aL = aK /\ c977cc_normal cL sL /\ &0 < sL /\ c977cc_normal cK (--sK) /\
     linside cL sL uL vL aL (&0) (&2 / &5) /\ lcx cL sL uL vL aL <= &0 /\ &0 <= lcy cL sL uL vL aL /\
     linside cK sK uK vK aK (&0) (&1 / &2) /\ linside cK sK uK vK aK (&0) (&1) /\
     ~linside cK sK uK vK aK (&1 / &5) (&1) /\
     ldisj cL sL uL vL aL cK sK uK vK aK
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aK`)) THEN
  C1092MCO_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < cK` ASSUME_TAC THENL [C1092MCO_LP_TAC; ALL_TAC] THEN
  C1092MCO_UNITS_TAC THEN
  C1092MCO_USE C1092MMCC_ALTERNATIVES
    [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
     `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aL:real`] THEN
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
    MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `cK:real`; `--sK:real`]
      C1092MMCC_UP_RIGHT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN
                    FIRST [REAL_ARITH_TAC; C1092MCO_LP_TAC]; DISCH_TAC] THEN
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
let C1092MMCC_IMPOSSIBLE = prove
 (`forall cL sL uL vL aL cK sK uK vK aK.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     &1 < aL /\ aL = aK /\ c977cc_normal cL sL /\ &0 < sL /\
     linside cL sL uL vL aL (&0) (&2 / &5) /\ lcx cL sL uL vL aL <= &0 /\ &0 <= lcy cL sL uL vL aL /\
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
  [MATCH_MP_TAC C1092MMCC_NONNEGATIVE; MATCH_MP_TAC C1092MMCC_NONPOSITIVE] THEN
  MAP_EVERY EXISTS_TAC [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                        `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] THEN
  ASM_REWRITE_TAC[c977cc_normal] THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ABS_BOUNDS]) THEN ASM_REAL_ARITH_TAC);;
