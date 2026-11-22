(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMPositiveNegativeRetainingSupport.lean*)
(* (namespace N12Compact.C1092MPPMPositiveNegativeRetaining).  Signed-axis   *)
(* comparison for a positive source C and a retaining nonpositive physical   *)
(* successor E; the bar belongs to a third square R.                         *)
(* The structures Input / Profile are the predicates c1092pnrsup_input /     *)
(* c1092pnrsup_profile.  Scalars.*: C1092PNRS_*, c1092pnrs_P/Q; lower/upper: *)
(* ABT_lower / ABT_upper; C1092WholeSupports: C1092WS_*;                     *)
(* MPPMNonpositivePredecessor: C1092NPP_RELATIVE, C1092NPPT_POSITIVE_AXES;   *)
(* SuccessorFaces: c1092anc_successorFaces; Frame: c1092onh_frame.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveNegativeRetainingScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMNonpositivePredecessor.ml";;
needs "n12/geometry/CP_C1092_MPPMAllNonpositiveCore.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;

(* Lean: Input (structure) *)
let c1092pnrsup_input = new_definition
 `c1092pnrsup_input cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR <=>
    &1 < aC /\ aC = aE /\ c977cc_normal cC sC /\ c977cc_normal cE (--sE) /\
    linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
    --cC - sC <= uC /\ vC + aC <= sC /\
    linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
    linside cE sE uE vE aE (&13 / &50) (--(&1)) /\
    linside cE sE uE vE aE (&2 / &5) (--(&1)) /\
    linside cE sE uE vE aE (&0) (--(&13 / &50)) /\
    c1092anc_successorFaces cE sE uE vE aE /\
    ~linside cE sE uE vE aE (&1 / &2) (&0) /\
    ldisj cC sC uC vC aC cE sE uE vE aE /\
    ldisj cE sE uE vE aE cR sR uR vR aR /\
    (forall y. --(&14 / &25) <= y ==> y <= &0 ==> linside cR sR uR vR aR (&1) y)`;;

(* Lean: Profile (structure) *)
let c1092pnrsup_profile = new_definition
 `c1092pnrsup_profile (cE:real) (sE:real) (uE:real) (vE:real) (aE:real) <=>
    &0 < --sE /\ (--sE) / cE < &1 / &4 /\ --uE < &43 / &500 /\
    &97 / &100 < cE /\ --sE < &1 / &4`;;

let C1092PNRSUP_LIN_TAC =
  REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NLIN_TAC ~deg2:false []);;

let C1092PNRSUP_SQ_HYPS =
  `cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
   cR * cR + sR * sR = &1 /\ &0 < aR /\
   c1092pnrsup_input cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR`;;

let C1092PNRSUP_INTRO_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092pnrsup_input] o
    check (can (term_match [] `c1092pnrsup_input a b c d e f g h i j k l m n o'`) o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092anc_successorFaces] o
    check (can (term_match [] `c1092anc_successorFaces a b c d e`) o concl)) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th) THEN
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths)) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> try fst(strip_comb(concl th)) = `linside` with _ -> false) ths));;

(* Lean: negative *)
let C1092PNRSUP_NEGATIVE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c1092pnrsup_input cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR
     ==> &0 < --sE`,
  C1092PNRSUP_INTRO_TAC THEN C1092PNRSUP_LIN_TAC);;

(* Lean: next_face *)
let C1092PNRSUP_NEXT_FACE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c1092pnrsup_input cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR
     ==> vE + aE <= --sE / &2`,
  C1092PNRSUP_INTRO_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ASSUME `~linside cE sE uE vE aE (&1 / &2) (&0)`) THEN
  REWRITE_TAC[linside; DE_MORGAN_THM; REAL_NOT_LT] THEN
  STRIP_TAC THEN C1092PNRSUP_LIN_TAC);;

(* Lean: height_envelope *)
let C1092PNRSUP_HEIGHT_ENVELOPE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c1092pnrsup_input cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR
     ==> --uE < (&43 / &500) * cE + sE / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092PNRSUP_NEGATIVE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092PNRSUP_NEXT_FACE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092pnrsup_input] o
    check (can (term_match [] `c1092pnrsup_input a b c d e f g h i j k l m n o'`) o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092anc_successorFaces] o
    check (can (term_match [] `c1092anc_successorFaces a b c d e`) o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aC:real = aE` o concl)) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th) THEN
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths)) THEN
  SUBGOAL_THEN `c1092onh_frame cC sC /\ c1092onh_frame cE (--sE)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092onh_frame] THEN C1092PNRSUP_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092NPP_RELATIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the three supports *)
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cC:real`; `sC:real`;
                `cC * cE - sC * --sE`; `cC * --sE + sC * cE`] C1092WS_LOWER_NN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `sC:real`; `--cC`;
                `cC * --sE + sC * cE`; `--(cC * cE - sC * --sE)`] C1092WS_LOWER_PN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `ABT_upper cC sC uC vC aC cE sE =
                (cC * cE - sC * --sE) * (uC + aC) - (cC * --sE + sC * cE) * vC`
    ASSUME_TAC THENL
   [MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cE:real`; `sE:real`]
      C1092WS_FORMULAS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `cE * cC + sE * sC = cC * cE - sC * --sE /\
                  --cE * sC + sE * cC = --(cC * --sE + sC * cE)` STRIP_ASSUME_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> max x (&0) = x`;
                 REAL_ARITH `&0 <= x ==> max (--x) (&0) = &0`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] C1092NPPT_POSITIVE_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> try fst(strip_comb(concl th)) = `linside` with _ -> false) ths)) THEN
  let k = `cC * cE - sC * --sE` and l = `cC * --sE + sC * cE` in
  let ( ++ ) x y = mk_comb(mk_comb(`(+):real->real->real`,x),y) in
  SUBGOAL_THEN (mk_comb(mk_comb(`(<=):real->real->bool`,l),`&1`)) ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
    NLIN_TAC [SQ_NONNEG `cC - --sE`; SQ_NONNEG `sC - cE`];
    ALL_TAC] THEN
  MP_TAC(SPECL [k; `uE:real`; `(&13 / &50) * --sE`] REAL_LE_LMUL) THEN
  MP_TAC(SPECL [l; `uE:real`; `(&13 / &50) * --sE`] REAL_LE_LMUL) THEN
  MP_TAC(SPECL [l; `vE:real`; `--sE / &2 - aC`] REAL_LE_LMUL) THEN
  MP_TAC(SPECL [k; `aC - cE`; `vE + aC`] REAL_LE_LMUL) THEN
  MP_TAC(SPECL [k; `aC - cC - sC`; `uC + aC`] REAL_LE_LMUL) THEN
  MP_TAC(SPECL [l; `vC:real`; `sC - aC`] REAL_LE_LMUL) THEN
  MP_TAC(SPECL [`aC - &1`; `&1` ++ l] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`aC - &1`; `&1` ++ k] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`aC - &1`; k ++ l] REAL_LE_MUL) THEN
  REPEAT(ANTS_TAC THENL [C1092PNRSUP_LIN_TAC; DISCH_TAC]) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092PNRS_FIRST_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092PNRS_TRANSVERSE_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092PNRS_ENVELOPE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092pnrs_P; c1092pnrs_Q; REAL_POW_2]) THEN
  SUBGOAL_THEN `cE * (cC * cC + sC * sC) = cE` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN ASSUME_TAC) o
    check (is_disj o concl)) THEN
  C1092PNRSUP_LIN_TAC);;
