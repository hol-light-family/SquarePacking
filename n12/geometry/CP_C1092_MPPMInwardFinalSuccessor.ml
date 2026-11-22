(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalSuccessor.lean            *)
(* (namespace N12Compact.C1092MPPMInwardFinal).  Successor faces and the     *)
(* square-normal cover shared by both inward endings.                        *)
(* Squares C, E are the tuples cC sC uC vC aC, cE sE uE vE aE.  Normal:      *)
(* c977cc_normal; half: C1092WPS_half (quarter_data: C1092WPS_QUARTER_DATA); *)
(* FC / FE / alpha: c1092mifss_FC / c1092mifss_FE / c1092mifss_alpha;        *)
(* lower / upper: ABT_lower / ABT_upper; lower_nn: C1092WS_LOWER_NN;         *)
(* upper_pos_neg: C1092TFSU_UPPER_POS_NEG; ownU: ABT_OWNU;                   *)
(* faceSeparation_of_disjoint: CSAT_FACESEPARATION_OF_DISJOINT.              *)
(* Structure NegativeSuccessor E: c1092ifsu_negsucc.                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalMargins.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalSuccessorScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveRetainingSteepScalars.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/CongruentSAT.ml";;
needs "n12/geometry/C977ChainBridge.ml";;

let C1092IFSU_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

(* Lean: width_half *)
let C1092IFSU_WIDTH_HALF = prove
 (`forall k d t. c977cc_normal d t /\ --(&1) < k /\ &1 < t + k * d
     ==> (&1 - k) / (&1 + k) < C1092WPS_half d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`C1092WPS_half d t`, `z:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  ASSUME_TAC(SPEC `z:real` REAL_LE_POW_2) THEN
  SUBGOAL_THEN `k * ((&1 + z pow 2) * d) = k * (&1 - z pow 2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  C1092PRS_PROD `&0 < (&1 + z pow 2) * ((t + k * d) - &1)` THEN
  SUBGOAL_THEN `&0 < (&1 + k) * z - (&1 - k)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092PRS_PROD `&0 <= (&1 - z) * ((&1 - k) - (&1 + k) * z)` THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + k` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN NLIN_TAC ~deg2:false []);;

(* Lean: NegativeSuccessor (structure) *)
let c1092ifsu_negsucc = new_definition
 `c1092ifsu_negsucc (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    c977cc_normal c (--s) /\
    linside c s u v a (&7 / &20) (--(&7 / &20)) /\
    linside c s u v a (&13 / &50) (--(&1)) /\
    linside c s u v a (&1 / &2) (--(&1)) /\
    --(&13 / &50) * s <= u /\ u + a <= c - s /\
    --(&543 / &500) * c <= v /\ v + a <= --s - &2 / &5 * c`;;

let C1092IFSU_OPEN_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifsu_negsucc] o
    check (can (term_match [] `c1092ifsu_negsucc a b c d e`) o concl)) THEN
  C1092PRS_NORMAL_TAC;;

(* the angle bound  (1 - k) / (1 + k) < half c (--s), evaluated *)
let C1092IFSU_ANGLE_TAC k =
  MP_TAC(SPECL [k; `c:real`; `--s`] C1092IFSU_WIDTH_HALF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; RASM_ARITH_TAC];
    DISCH_THEN(ASSUME_TAC o CONV_RULE(LAND_CONV REAL_RAT_REDUCE_CONV))];;

(* Lean: successor_far *)
let C1092IFSU_SUCCESSOR_FAR = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c1092ifsu_negsucc c s u v a /\
     ~linside c s u v a (&1) (--(&36 / &85))
     ==> v + a <= --s - &36 / &85 * c /\ &2869 / &14131 < C1092WPS_half c (--s)`,
  C1092IFSU_OPEN_TAC THEN C1092IFSU_ANGLE_TAC `&343 / &500` THEN
  MP_TAC(SPECL [`c:real`; `--s`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  ASSUME_TAC(SPEC `C1092WPS_half c (--s)` REAL_LE_POW_2) THEN
  SUBGOAL_THEN `c - &139 / &850 * s <= &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092PRS_PROD `&0 < (&1 + C1092WPS_half c (--s) pow 2) * ((c - &139 / &850 * s) - &1)` THEN
    C1092PRS_PROD `&0 <= (&2 * C1092WPS_half c (--s)) * (C1092WPS_half c (--s) - &139 / &850)` THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  SUBGOAL_THEN `c - &36 / &85 * s < u + a` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= --s - &36 / &85 * c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside c s u v a (&1) (--(&36 / &85))` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `linside c s u v a (&7 / &20) (--(&7 / &20))` THEN
    UNDISCH_TAC `linside c s u v a (&13 / &50) (--(&1))` THEN
    REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN C1092IFSU_ANGLE_TAC `&5631 / &8500` THEN ASM_REWRITE_TAC[]);;

(* Lean: successor_bottom *)
let C1092IFSU_SUCCESSOR_BOTTOM = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c1092ifsu_negsucc c s u v a /\
     v + a <= --s - &36 / &85 * c /\ ~linside c s u v a (&0) (--(&1))
     ==> --c <= v /\ &18 / &67 < C1092WPS_half c (--s)`,
  C1092IFSU_OPEN_TAC THEN
  SUBGOAL_THEN `s < &0 /\ u < --s` STRIP_ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--c <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside c s u v a (&0) (--(&1))` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `linside c s u v a (&13 / &50) (--(&1))` THEN
    REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN C1092IFSU_ANGLE_TAC `&49 / &85` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* longitudinal_axes                                                         *)
(* ------------------------------------------------------------------------- *)

let C1092IFSU_C = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `a:real`];;
let C1092IFSU_E = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `a:real`];;

let C1092IFSU_SB_TAC sq (x, y) (nx, ny) =
  MP_TAC(SPECL (sq @ [x; y; nx; ny]) ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_2; REAL_NEG_MUL2] THEN RASM_ARITH_TAC;
    STRIP_TAC];;

(* Lean: rightward / downward (local): from a separation  upper C n <= lower E n *)
let C1092IFSU_RIGHTWARD = prove
 (`forall cC sC uC vC cE sE uE vE a nx ny.
     cC * cC + sC * sC = &1 /\ cE * cE + sE * sE = &1 /\ &0 < a /\ nx pow 2 + ny pow 2 = &1 /\
     linside cC sC uC vC a (--(&7 / &20)) (--(&7 / &20)) /\
     linside cE sE uE vE a (&7 / &20) (--(&7 / &20)) /\
     ABT_upper cC sC uC vC a nx ny <= ABT_lower cE sE uE vE a nx ny ==> &0 < nx`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092IFSU_SB_TAC C1092IFSU_C (`--(&7 / &20)`, `--(&7 / &20)`) (`nx:real`, `ny:real`) THEN
  C1092IFSU_SB_TAC C1092IFSU_E (`&7 / &20`, `--(&7 / &20)`) (`nx:real`, `ny:real`) THEN
  RASM_ARITH_TAC);;
let C1092IFSU_DOWNWARD = prove
 (`forall cC sC uC vC cE sE uE vE a nx ny.
     cC * cC + sC * sC = &1 /\ cE * cE + sE * sE = &1 /\ &0 < a /\ nx pow 2 + ny pow 2 = &1 /\
     linside cC sC uC vC a (&0) (--(&13 / &50)) /\
     linside cE sE uE vE a (&1 / &2) (--(&1)) /\
     ABT_upper cC sC uC vC a nx ny <= ABT_lower cE sE uE vE a nx ny
     ==> &0 < &1 / &2 * nx - &37 / &50 * ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092IFSU_SB_TAC C1092IFSU_C (`&0`, `--(&13 / &50)`) (`nx:real`, `ny:real`) THEN
  C1092IFSU_SB_TAC C1092IFSU_E (`&1 / &2`, `--(&1)`) (`nx:real`, `ny:real`) THEN
  RASM_ARITH_TAC);;

(* Lean: reverse (WallProfile) for the pair C, E *)
let C1092IFSU_REVERSE = prove
 (`forall cC sC uC vC cE sE uE vE a nx ny.
     ABT_upper cE sE uE vE a nx ny <= ABT_lower cC sC uC vC a nx ny
     ==> ABT_upper cC sC uC vC a (--nx) (--ny) <= ABT_lower cE sE uE vE a (--nx) (--ny)`,
  REWRITE_TAC[OCWPVG_UPPER_NEG; OCWPVG_LOWER_NEG] THEN REAL_ARITH_TAC);;

(* use rightward / downward at a normal; the separation is an assumption, or
   (rev) its reverse at the opposite normal *)
let C1092IFSU_CA = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aE:real`];;
let C1092IFSU_EA = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`];;

let C1092IFSU_DIR_TAC lemma rev nx ny =
  let neg t = let t' = mk_comb(`(--):real->real`, t) in
              try rhs(concl(REWRITE_CONV[REAL_NEG_NEG] t')) with _ -> t' in
  (if rev then
     MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `cE:real`; `sE:real`;
                   `uE:real`; `vE:real`; `aE:real`; neg nx; neg ny] C1092IFSU_REVERSE) THEN
     ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC]
   else ALL_TAC) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `cE:real`; `sE:real`;
                `uE:real`; `vE:real`; `aE:real`; nx; ny] lemma) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_2; REAL_NEG_MUL2] THEN RASM_ARITH_TAC;
    DISCH_TAC];;

(* Lean: longitudinal_axes *)
let C1092IFSU_LONGITUDINAL_AXES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     aC = aE /\ c977cc_normal cC (--sC) /\ c977cc_normal cE (--sE) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     linside cC sC uC vC aC (&0) (--(&13 / &50)) /\
     linside cE sE uE vE aE (&1 / &2) (--(&1)) /\
     ldisj cC sC uC vC aC cE sE uE vE aE
     ==> uC + aC <= ABT_lower cE sE uE vE aE cC sC \/
         ABT_upper cC sC uC vC aC cE sE <= uE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = aE`)) THEN
  C1092PRS_NORMAL_TAC THEN
  MP_TAC(SPECL (C1092IFSU_CA @ C1092IFSU_EA) CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `aE:real`; `cE:real`; `sE:real`; `aE:real`] ABT_PARALLEL_RADIUS) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `aE:real`; `cE:real`; `sE:real`; `aE:real`] ABT_TRANSVERSE_RADIUS) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `aE:real`; `cC:real`; `sC:real`; `aE:real`] ABT_PARALLEL_RADIUS) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `aE:real`; `cC:real`; `sC:real`; `aE:real`] ABT_TRANSVERSE_RADIUS) THEN
  MP_TAC(SPECL C1092IFSU_CA ABT_OWNU) THEN MP_TAC(SPECL C1092IFSU_EA ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[C977CB_faceSep] o
    check (can (term_match [] `C977CB_faceSep a b c d e f g h i j`) o concl)) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   (map (fun (nx, ny, direct, back) ->
      MP_TAC(SPECL (C1092IFSU_CA @ C1092IFSU_EA @ [nx; ny]) ABT_SEPARATED) THEN
      ANTS_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL [direct; back])
    [`cC:real`, `sC:real`,
       (DISJ1_TAC THEN RASM_ARITH_TAC),
       (C1092IFSU_DIR_TAC C1092IFSU_RIGHTWARD true `--cC` `--sC` THEN RASM_ARITH_TAC);
     `--sC`, `cC:real`,
       (C1092IFSU_DIR_TAC C1092IFSU_DOWNWARD false `--sC` `cC:real` THEN RASM_ARITH_TAC),
       (C1092IFSU_DIR_TAC C1092IFSU_RIGHTWARD true `sC:real` `--cC` THEN RASM_ARITH_TAC);
     `cE:real`, `sE:real`,
       (DISJ2_TAC THEN RASM_ARITH_TAC),
       (C1092IFSU_DIR_TAC C1092IFSU_RIGHTWARD true `--cE` `--sE` THEN RASM_ARITH_TAC);
     `--sE`, `cE:real`,
       (C1092IFSU_DIR_TAC C1092IFSU_DOWNWARD false `--sE` `cE:real` THEN RASM_ARITH_TAC),
       (C1092IFSU_DIR_TAC C1092IFSU_RIGHTWARD true `sE:real` `--cE` THEN RASM_ARITH_TAC)]));;

(* Lean: successor_impossible *)
let C1092IFSU_SUCCESSOR_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE beta H.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aC /\ aC = aE /\ c977cc_normal cC (--sC) /\ c1092ifsu_negsucc cE sE uE vE aE /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cC sC uC vC aC (&0) (--(&13 / &50)) /\
     aC - cC - beta * sC <= uC + aC /\ vC + aC <= H /\
     vE + aE <= --sE - &36 / &85 * cE /\ &0 < sC * cE - cC * sE /\
     &0 < c1092mifss_FC beta cC (--sC) cE (--sE) /\
     &0 < c1092mifss_FE beta H cC (--sC) cE (--sE) /\
     ldisj cC sC uC vC aC cE sE uE vE aE ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] C1092IFSU_LONGITUDINAL_AXES) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifsu_negsucc] o
    check (can (term_match [] `c1092ifsu_negsucc a b c d e`) o concl)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = aE`)) THEN
  C1092PRS_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mifss_FC; c1092mifss_FE; c1092mifss_alpha]) THEN
  C1092PRS_PROD `&0 < cC * cE` THEN C1092PRS_PROD `&0 <= --sC * --sE` THEN
  SUBGOAL_THEN `&0 < cC * cE + sC * sE` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  C1092PRS_PROD `&0 < (aE - &1) * (&1 + (cC * cE + sC * sE) + (sC * cE - cC * sE))` THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `cC:real`; `sC:real`;
                  `cC * cE + sC * sE`; `sC * cE - cC * sE`] C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    C1092PRS_PROD `&0 <= (cC * cE + sC * sE) * (cE - sE - aE - uE)` THEN
    C1092PRS_PROD `&0 <= (sC * cE - cC * sE) * (--sE - &36 / &85 * cE - aE - vE)` THEN
    NLIN_TAC ~deg2:false [];
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aE:real`; `cE:real`; `sE:real`;
                  `cC * cE + sC * sE`; `--(sC * cE - cC * sE)`] C1092TFSU_UPPER_POS_NEG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    C1092PRS_PROD `&0 <= (cC * cE + sC * sE) * (uC + cC + beta * sC)` THEN
    C1092PRS_PROD `&0 <= (sC * cE - cC * sE) * (H - aE - vC)` THEN
    NLIN_TAC ~deg2:false []]);;
