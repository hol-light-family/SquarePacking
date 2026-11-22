(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardOmittedFar.lean                *)
(* (namespace N12Compact.C1092MPPMInwardOmittedFar).  Full local             *)
(* CENTERED-INWARD-OMITTED-G-FAR-ENDING ("Source only").                     *)
(* Squares C, E, R are cC sC uC vC aC, cE sE uE vE aE, cR sR uR vR aR.       *)
(* Normal: c977cc_normal; normal_bounds: C977CC_NORMAL_BOUNDS; half:         *)
(* C1092WPS_half; NegativeSuccessor: c1092ifsu_negsucc; far_cap:             *)
(* C1092IOFB_FAR_CAP; Scalars.*: C1092IOFS_* (sourceGap / targetGap:         *)
(* c1092iofs_sourceGap / _targetGap); signed_axes: C1092SPTS_SIGNED_AXES;    *)
(* lower / upper: ABT_lower / ABT_upper; strict_bounds / ownU:               *)
(* ABT_STRICT_BOUNDS / ABT_OWNU; lower_nn: C1092WS_LOWER_NN; upper_pos_neg:  *)
(* C1092TFSU_UPPER_POS_NEG.  Structure Input: c1092iof_input (the OpenSquare *)
(* unit normals / positive sides are explicit hypotheses).  Tag C1092IOF_.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardOmittedFarScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMSteepPositiveThreeSquareGeometry.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardOmittedFarBar.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalSuccessor.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;

let C1092IOF_LIN = NLIN_TAC ~deg2:false [];;

let C1092IOF_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC THEN
   C1092IOF_LIN; ALL_TAC];;

(* Lean: omitted_lower *)
let C1092IOF_OMITTED_LOWER = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ c977cc_normal c (--s) /\
     linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
     C1092WPS_half c (--s) <= &21 / &100 /\ v + a <= &17 / &125 /\
     ~linside c s u v a (--(&1)) (--(&2 / &5))
     ==> --c - (&2 / &5) * s <= u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `--s`] C1092IOFS_SOURCE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~linside c s u v a (--(&1)) (--(&2 / &5))` THEN REWRITE_TAC[] THEN
  UNDISCH_TAC `linside c s u v a (--(&7 / &20)) (--(&7 / &20))` THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN C1092IOF_LIN);;

(* Lean: Input (structure) *)
let c1092iof_input = new_definition
 `c1092iof_input (cC:real) (sC:real) (uC:real) (vC:real) (aC:real)
                 (cE:real) (sE:real) (uE:real) (vE:real) (aE:real)
                 (cR:real) (sR:real) (uR:real) (vR:real) (aR:real) <=>
    &1 < aC /\
    aC = aE /\
    c977cc_normal cC (--sC) /\
    C1092WPS_half cC (--sC) <= &21 / &100 /\
    --cC - (&2 / &5) * sC <= uC /\
    vC + aC <= &17 / &125 /\
    linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
    linside cC sC uC vC aC (--(&1 / &2)) (&0) /\
    c1092ifsu_negsucc cE sE uE vE aE /\
    (forall y. --(&14 / &25) <= y /\ y <= &0 ==> linside cR sR uR vR aR (&1) y) /\
    ldisj cC sC uC vC aC cE sE uE vE aE /\
    ldisj cE sE uE vE aE cR sR uR vR aR`;;

(* Lean: axes (private), the local cone *)
let C1092IOF_CONE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cC sC uC vC aC (--(&1 / &2)) (&0) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&1 / &2) (--(&1)) /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cC sC uC vC aC nx ny <= ABT_lower cE sE uE vE aE nx ny
     ==> &0 < nx /\ &0 < nx - ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (sq,(x,y)) ->
      MP_TAC(SPECL (sq @ [x; y; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC)
   [[`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`], (`--(&7 / &20)`, `--(&7 / &20)`);
    [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`], (`--(&1 / &2)`, `&0`);
    [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`], (`&7 / &20`, `--(&7 / &20)`);
    [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`], (`&1 / &2`, `--(&1)`)] THEN
  CONJ_TAC THEN C1092IOF_LIN);;

(* Lean: axes (private) *)
let C1092IOF_AXES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c1092iof_input cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR
     ==> uC + aC <= ABT_lower cE sE uE vE aE cC sC \/
         ABT_upper cC sC uC vC aC cE sE <= uE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092iof_input] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifsu_negsucc] o
    check (fun th -> concl th = `c1092ifsu_negsucc cE sE uE vE aC`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cC (--sC)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cE (--sE)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cC (--sC)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cE (--sE)`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] C1092SPTS_SIGNED_AXES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  POP_ASSUM(fun th ->
    let nxny = let args = snd(strip_comb(lhand(concl th))) in [el 5 args; el 6 args] in
    MP_TAC(SPECL ([`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                   `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] @ nxny) C1092IOF_CONE) THEN
    ASM_REWRITE_TAC[th]) THEN
  (ANTS_TAC THENL
    [UNDISCH_TAC `cC * cC + sC * sC = &1` THEN UNDISCH_TAC `cE * cE + sE * sE = &1` THEN
     CONV_TAC REAL_RING;
     DISCH_TAC THEN MATCH_MP_TAC(TAUT `false ==> p`) THEN C1092IOF_LIN]));;

(* Lean: impossible *)
let C1092IOF_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c1092iof_input cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092IOF_AXES) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `c1092iof_input cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR` THEN
  REWRITE_TAC[c1092iof_input] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] C1092IOFB_FAR_CAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifsu_negsucc] o
    check (fun th -> concl th = `c1092ifsu_negsucc cE sE uE vE aC`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cC (--sC)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cE (--sE)`)) THEN
  SUBGOAL_THEN `&237 / &763 <= C1092WPS_half cE (--sE)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`] C1092IOFS_SOURCE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `--sE`] C1092IOFS_ENDPOINT_ORDER) THEN
  ASM_REWRITE_TAC[c1092iofs_d0; c1092iofs_t0] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&14 / &25 <= --sE` ASSUME_TAC THENL [C1092IOF_LIN; ALL_TAC] THEN
  (* kp *)
  SUBGOAL_THEN `&0 < cC * cE + sC * sE` ASSUME_TAC THENL
   [C1092IOF_PROD `&0 < cC * cE` THEN
    C1092IOF_PROD `&0 <= (--sC) * (--sE)` THEN C1092IOF_LIN; ALL_TAC] THEN
  (* deltaPositive *)
  SUBGOAL_THEN `&0 < sC * cE - cC * sE` ASSUME_TAC THENL
   [C1092IOF_PROD `&0 <= (cC - &91 / &100) * (--sE)` THEN
    C1092IOF_PROD `&0 <= (--sC) * (&1 - cE)` THEN C1092IOF_LIN; ALL_TAC] THEN
  C1092IOF_PROD `&0 < (aC - &1) * (&1 + (cC * cE + sC * sE) + (sC * cE - cC * sE))` THEN
  STRIP_TAC THENL
   [MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cC:real`; `sC:real`;
                  `cC * cE + sC * sE`; `sC * cE - cC * sE`] C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092IOF_LIN;
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
    MP_TAC(SPECL [`cC:real`; `--sC`; `cE:real`; `--sE`] C1092IOFS_SOURCE_POSITIVE) THEN
    ASM_REWRITE_TAC[c1092iofs_sourceGap; c1092iofs_a] THEN DISCH_TAC THEN
    C1092IOF_PROD `&0 <= (cC * cE + sC * sE) * ((cE - sE) - (uE + aC))` THEN
    C1092IOF_PROD `&0 <= (sC * cE - cC * sE) * ((--sE - (&14 / &25) * cE) - (vE + aC))` THEN
    C1092IOF_LIN;
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cE:real`; `sE:real`;
                  `cC * cE + sC * sE`; `--(sC * cE - cC * sE)`] C1092TFSU_UPPER_POS_NEG) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092IOF_LIN;
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
    MP_TAC(SPECL [`cC:real`; `--sC`; `cE:real`; `--sE`] C1092IOFS_TARGET_POSITIVE) THEN
    ASM_REWRITE_TAC[c1092iofs_targetGap; c1092iofs_a] THEN DISCH_TAC THEN
    C1092IOF_PROD `&0 <= (cC * cE + sC * sE) * (uC - (--cC - (&2 / &5) * sC))` THEN
    C1092IOF_PROD `&0 <= (sC * cE - cC * sE) * (&17 / &125 - (vC + aC))` THEN
    C1092IOF_LIN]);;
