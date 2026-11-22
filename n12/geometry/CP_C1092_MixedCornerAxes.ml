(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MixedCornerAxes.lean                      *)
(* (N12Compact.C1092MixedCornerAxes).  Complete separating-axis reduction    *)
(* for the actual mixed wall L and its paired corner K.                      *)
(* lower/upper: ABT_lower/ABT_upper; MixedCornerSupports: C1092MCSUP_*;      *)
(* the SAT step is ABT_FOUR_AXES; Normal is c977cc_normal.                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MixedCornerSupports.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* Lean: left_blocked *)
let C1092MCA_LEFT_BLOCKED = prove
 (`forall cL sL uL vL aL cK sK uK vK aK nx ny.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     &1 < aL /\ c977cc_normal cL sL /\ &0 < sL /\
     linside cL sL uL vL aL (&0) (&2 / &5) /\ --(&2 / &5) * cL <= vL /\
     uL + aL <= sL / &2 /\ linside cK sK uK vK aK (&0) (&1 / &2) /\
     nx pow 2 + ny pow 2 = &1 /\ nx <= &0 /\
     ABT_upper cL sL uL vL aL nx ny <= ABT_lower cK sK uK vK aK nx ny
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                `nx:real`; `ny:real`] C1092MCSUP_UPWARD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `ny:real`; `--nx:real`] C1092MCSUP_UP_LEFT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
                  REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC] THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                `&0`; `&1 / &2`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: reverse_blocked (private) *)
let C1092MCA_REVERSE_BLOCKED = prove
 (`forall cL sL uL vL aL cK sK uK vK aK nx ny.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     linside cL sL uL vL aL (&0) (&2 / &5) /\ linside cK sK uK vK aK (&0) (&1 / &2) /\
     nx pow 2 + ny pow 2 = &1 /\ &0 <= ny /\
     ABT_upper cK sK uK vK aK nx ny <= ABT_lower cL sL uL vL aL nx ny
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `&0`; `&2 / &5`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                `&0`; `&1 / &2`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: alternatives *)
let C1092MCA_ALTERNATIVES = prove
 (`forall cL sL uL vL aL cK sK uK vK aK.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     &1 < aL /\ aL = aK /\ c977cc_normal cL sL /\ &0 < sL /\ &0 < cK /\
     linside cL sL uL vL aL (&0) (&2 / &5) /\ --(&2 / &5) * cL <= vL /\
     linside cK sK uK vK aK (&0) (&1 / &2) /\
     ldisj cL sL uL vL aL cK sK uK vK aK
     ==> uL + aL <= ABT_lower cK sK uK vK aK cL sL \/
         ABT_upper cL sL uL vL aL cK sK <= uK \/
         ABT_upper cL sL uL vL aL (--sK) cK <= vK`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aK`)) THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] C1092MCSUP_UPPER_CAP) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   UNDISCH_TAC `ldisj cL sL uL vL aL cK sK uK vK aL` THEN REWRITE_TAC[ldisj] THEN
   DISCH_THEN(MP_TAC o SPECL [`&0`; `&1 / &2`]) THEN ASM_REWRITE_TAC[];
   DISCH_TAC] THEN
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
    MATCH_MP_TAC C1092MCA_LEFT_BLOCKED THEN
    MAP_EVERY EXISTS_TAC [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                          `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aL:real`; nx; ny] THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC
  and rb nx ny =
    MATCH_MP_TAC(TAUT `false ==> p`) THEN
    MATCH_MP_TAC C1092MCA_REVERSE_BLOCKED THEN
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
