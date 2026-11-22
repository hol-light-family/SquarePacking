(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMPositiveOverlapLocal.lean            *)
(* (namespace N12Compact.C1092MPPMPositiveOverlap).  The actual C/E pair in  *)
(* CENTERED-POSITIVE-OVERLAP.  Squares C = (cC, ..), E = (cE, ..).           *)
(* Inputs / SuccessorFaces are the predicates c1092pol_inputs /              *)
(* c1092pol_successorFaces; ForwardInputs: c1092pcs_forwardInputs;           *)
(* RigidCharts.swap Q = (c, --s, v, u, a) (C1092RC_INSIDE_SWAP);             *)
(* NortheastNegativeFaces.faces: C1092MNNF_FACES; MMMMNegativeNeighbor.      *)
(* impossible_faces: C1092MNN_IMPOSSIBLE_FACES; overlap scalars: C1092POS_*; *)
(* S12.inside_segment: explicit convex combination (linear arithmetic).      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveOverlapScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMNonpositivePredecessor.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveCrosspointSeeds.ml";;
needs "n12/geometry/CP_C1092_MMMP_NortheastNegativeFaces.ml";;
needs "n12/geometry/CP_C1092_MMMMNegativeNeighbor.ml";;
needs "n12/geometry/CP_C1092_RigidCharts.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;

(* Lean: Inputs (structure) *)
let c1092pol_inputs = new_definition
 `c1092pol_inputs cC sC uC vC aC cE sE uE vE aE <=>
    c1092pcs_forwardInputs cC sC uC vC aC /\
    linside cC sC uC vC aC (&0) (--(&13 / &50)) /\
    linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
    linside cE sE uE vE aE (&13 / &50) (--(&1)) /\
    linside cE sE uE vE aE (&2 / &5) (--(&1)) /\
    ~linside cE sE uE vE aE (&1) (--(&39 / &100)) /\
    ~linside cE sE uE vE aE (&0) (--(&543 / &500)) /\
    ~linside cE sE uE vE aE (&1) (--(&1)) /\
    ~linside cE sE uE vE aE (&1) (&0) /\
    ~linside cE sE uE vE aE (&1) (--(&2 / &5)) /\
    ldisj cC sC uC vC aC cE sE uE vE aE`;;

(* Lean: SuccessorFaces (structure) *)
let c1092pol_successorFaces = new_definition
 `c1092pol_successorFaces (c:real) s u v a <=>
    --(&13 / &50) * s <= u /\ u + a <= c - s /\
    --(&543 / &500) * c <= v /\ v + a <= --s`;;

let C1092POL_LIN_TAC =
  REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NLIN_TAC ~deg2:false []);;

(* linear arithmetic with a missing-point hypothesis n = `~linside ...` *)
let C1092POL_NFACT_TAC n t =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [MP_TAC(ASSUME n) THEN REWRITE_TAC[linside; DE_MORGAN_THM; REAL_NOT_LT] THEN
    STRIP_TAC THEN C1092POL_LIN_TAC; ALL_TAC];;

let C1092POL_NCONTRA_TAC n =
  MP_TAC(ASSUME n) THEN REWRITE_TAC[linside; DE_MORGAN_THM; REAL_NOT_LT] THEN
  STRIP_TAC THEN C1092POL_LIN_TAC;;

let C1092POL_UNFOLD_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> try fst(strip_comb(concl th)) = `linside` with _ -> false) ths)) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th) THEN
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths));;

let C1092POL_INPUTS_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092pol_inputs; c1092pcs_forwardInputs] o
    check (can (term_match [] `c1092pol_inputs a b c d e f g h i j`) o concl));;

(* ~linside at (x,y) of one square from ldisj and the other's ownership *)
let C1092POL_APART_TAC apart (x,y) known =
  ASSUME_TAC(REWRITE_RULE[ASSUME known]
    (SPECL [x; y] (REWRITE_RULE[ldisj] (ASSUME apart))));;

let c1092pol_apart = `ldisj cC sC uC vC aC cE sE uE vE aE`;;

(* Lean: center_caps (private) *)
let C1092POL_CENTER_CAPS = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aC /\ c977cc_normal cC sC /\
     c1092pol_inputs cC sC uC vC aC cE sE uE vE aE /\ linside cC sC uC vC aC (&0) (&0)
     ==> uC + aC <= (&7 / &20) * (cC - sC) /\ vC + aC <= (&7 / &20) * (cC + sC)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092POL_INPUTS_TAC THEN
  C1092POL_APART_TAC c1092pol_apart (`&7 / &20`,`--(&7 / &20)`)
    `linside cE sE uE vE aE (&7 / &20) (--(&7 / &20))` THEN
  C1092POL_UNFOLD_TAC THEN
  C1092POL_NFACT_TAC `~linside cC sC uC vC aC (--(&7 / &20)) (&7 / &20)`
    `vC + aC <= (&7 / &20) * (cC + sC)` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C1092POL_NCONTRA_TAC `~linside cC sC uC vC aC (&7 / &20) (--(&7 / &20))`);;

(* Lean: lower_crosspoint (private) *)
let C1092POL_LOWER_CROSSPOINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ c977cc_normal c s /\
     linside c s u v a (&0) (&0) /\ linside c s u v a (--(&1 / &2)) (&0) /\
     v + a <= (&7 / &20) * (c + s)
     ==> linside c s u v a (&0) (--(&1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092POL_UNFOLD_TAC THEN
  MP_TAC(SPECL [`&17 / &20`; `&7 / &20`; `c:real`; `s:real`; `&1`] C1092NPP_NORM_LT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  REWRITE_TAC[linside] THEN C1092POL_LIN_TAC);;

(* Lean: successor_negative (private) *)
let C1092POL_SUCCESSOR_NEGATIVE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aC /\ aC = aE /\ c977cc_normal cC sC /\ abs sE <= cE /\
     c1092pol_inputs cC sC uC vC aC cE sE uE vE aE /\
     linside cC sC uC vC aC (&0) (&0) /\ linside cC sC uC vC aC (--(&1 / &2)) (&0) /\
     linside cC sC uC vC aC (&0) (--(&1 / &2))
     ==> sE < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092POL_INPUTS_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aC:real = aE` o concl)) THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `linside cC sC uC vC aC (&0) (--(&39 / &100))` ASSUME_TAC THENL
   [UNDISCH_TAC `linside cC sC uC vC aC (&0) (&0)` THEN
    UNDISCH_TAC `linside cC sC uC vC aC (&0) (--(&1 / &2))` THEN
    REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  let ap = `ldisj cC sC uC vC aC cE sE uE vE aC` in
  C1092POL_APART_TAC ap (`&0`,`--(&39 / &100)`) `linside cC sC uC vC aC (&0) (--(&39 / &100))` THEN
  C1092POL_APART_TAC ap (`&0`,`--(&1 / &2)`) `linside cC sC uC vC aC (&0) (--(&1 / &2))` THEN
  SUBGOAL_THEN `c1092mnnf_faces cE (--sE) vE uE aC` MP_TAC THENL
   [MATCH_MP_TAC C1092MNNF_FACES THEN
    REWRITE_TAC[C1092RC_INSIDE_SWAP; REAL_NEG_NEG] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[c977cc_normal] THEN
    UNDISCH_TAC `abs sE <= cE` THEN UNDISCH_TAC `&0 <= sE` THEN
    UNDISCH_TAC `cE * cE + sE * sE = &1` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    REWRITE_TAC[c1092mnnf_faces] THEN STRIP_TAC] THEN
  MATCH_MP_TAC C1092MNN_IMPOSSIBLE_FACES THEN
  MAP_EVERY EXISTS_TAC [`cC:real`; `--sC`; `vC:real`; `uC:real`; `aC:real`;
                        `cE:real`; `--sE`; `vE:real`; `uE:real`; `aC:real`] THEN
  REWRITE_TAC[C1092RC_INSIDE_SWAP; REAL_NEG_NEG] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  (fun g ->
    if can (term_match [] `ldisj a b c d e f g h i j`) (snd g) then
      (REWRITE_TAC[ldisj; C1092RC_INSIDE_SWAP] THEN
       UNDISCH_TAC `ldisj cC sC uC vC aC cE sE uE vE aC` THEN
       REWRITE_TAC[ldisj] THEN MESON_TAC[]) g
    else
      (REWRITE_TAC[c977cc_normal; REAL_NEG_NEG] THEN
       UNDISCH_TAC `c977cc_normal cC sC` THEN UNDISCH_TAC `abs sE <= cE` THEN
       UNDISCH_TAC `&0 <= sE` THEN UNDISCH_TAC `cE * cE + sE * sE = &1` THEN
       UNDISCH_TAC `cC * cC + sC * sC = &1` THEN
       MAP_EVERY (fun t -> UNDISCH_TAC t)
         [`--cE + --sE <= vE`; `vE + aC <= --(&39 / &100) * cE`;
          `uE + aC <= cE + &39 / &100 * --sE`] THEN
       REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN REAL_ARITH_TAC) g));;

(* Lean: successor_faces (private) *)
let C1092POL_SUCCESSOR_FACES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aE /\ c977cc_normal cE (--sE) /\
     c1092pol_inputs cC sC uC vC aC cE sE uE vE aE
     ==> c1092pol_successorFaces cE sE uE vE aE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092POL_INPUTS_TAC THEN
  C1092POL_APART_TAC c1092pol_apart (`&0`,`--(&13 / &50)`)
    `linside cC sC uC vC aC (&0) (--(&13 / &50))` THEN
  C1092POL_UNFOLD_TAC THEN REWRITE_TAC[c1092pol_successorFaces] THEN
  let nInner = `~linside cE sE uE vE aE (&0) (--(&13 / &50))`
  and nCorner = `~linside cE sE uE vE aE (&1) (--(&1))`
  and nBottom = `~linside cE sE uE vE aE (&0) (--(&543 / &500))`
  and nRight = `~linside cE sE uE vE aE (&1) (&0)` in
  SUBGOAL_THEN `--(&13 / &50) * sE <= uE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092POL_NFACT_TAC nInner `vE + aE <= --(&13 / &50) * cE` THEN
    C1092POL_NFACT_TAC nCorner `uE + aE <= cE - sE` THEN
    C1092POL_NFACT_TAC nBottom `--(&543 / &500) * sE <= uE` THEN
    C1092POL_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `vE + aE <= --sE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092POL_NFACT_TAC nRight `uE + aE <= cE` THEN C1092POL_LIN_TAC;
    ALL_TAC] THEN
  C1092POL_NFACT_TAC nCorner `uE + aE <= cE - sE` THEN
  SUBGOAL_THEN `--(&543 / &500) * cE <= vE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092POL_NFACT_TAC nBottom `--(&543 / &500) * sE <= uE` THEN C1092POL_LIN_TAC;
    ALL_TAC] THEN
  C1092POL_LIN_TAC);;

(* Lean: center_absent *)
let C1092POL_CENTER_ABSENT = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aC /\ aC = aE /\ c977cc_normal cC sC /\ &0 < cE /\ abs sE <= cE /\
     c1092pol_inputs cC sC uC vC aC cE sE uE vE aE
     ==> ~linside cC sC uC vC aC (&0) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aC:real = aE` o concl)) THEN
  let sqs = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
             `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`]
  and sqC = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] in
  MP_TAC(SPECL sqs C1092POL_CENTER_CAPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `c1092pcs_forwardInputs cC sC uC vC aC` ASSUME_TAC THENL
   [UNDISCH_TAC `c1092pol_inputs cC sC uC vC aC cE sE uE vE aC` THEN
    SIMP_TAC[c1092pol_inputs];
    ALL_TAC] THEN
  MP_TAC(SPECL sqC C1092PCS_FORWARD_PROFILE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[C1092PCS_FORWARDINPUTS_CORE]; ALL_TAC] THEN
  REWRITE_TAC[c1092pcs_forwardFaces] THEN STRIP_TAC THEN
  MP_TAC(SPECL sqC C1092PCS_CROSSPOINT_OF_FORWARD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL sqC C1092POL_LOWER_CROSSPOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL sqs C1092POL_SUCCESSOR_NEGATIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `c977cc_normal cE (--sE)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal] THEN UNDISCH_TAC `abs sE <= cE` THEN
    UNDISCH_TAC `sE < &0` THEN UNDISCH_TAC `cE * cE + sE * sE = &1` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL sqs C1092POL_SUCCESSOR_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[c1092pol_successorFaces] THEN STRIP_TAC THEN
  C1092POL_INPUTS_TAC THEN
  C1092POL_UNFOLD_TAC THEN
  SUBGOAL_THEN `c1092onh_frame cC sC /\ c1092onh_frame cE (--sE)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092onh_frame] THEN C1092POL_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092NPP_RELATIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  let k = `cC * cE - sC * --sE` and j = `cC * --sE + sC * cE` in
  let mul x y = mk_comb(mk_comb(`( * ):real->real->real`,x),y) in
  let add x y = mk_comb(mk_comb(`(+):real->real->real`,x),y) in
  SUBGOAL_THEN (mk_comb(mk_comb(`(<):real->real->bool`,`&0`),j)) ASSUME_TAC THENL
   [MP_TAC(SPECL [`cC:real`; `--sE`] REAL_LT_MUL) THEN
    MP_TAC(SPECL [`sC:real`; `cE:real`] REAL_LE_MUL) THEN
    REPEAT(ANTS_TAC THENL [C1092POL_LIN_TAC; DISCH_TAC]) THEN C1092POL_LIN_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cC:real`; `sC:real`;
                k; j] C1092WS_LOWER_NN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN (mk_eq(`ABT_upper cC sC uC vC aC cE sE`,
     mk_comb(mk_comb(`(-):real->real->real`, mul k `uC + aC`), mul j `vC:real`)))
    ASSUME_TAC THENL
   [MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cE:real`; `sE:real`]
      C1092WS_FORMULAS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN (mk_conj(mk_eq(`cE * cC + sE * sC`,k),
                          mk_eq(`--cE * sC + sE * cC`,mk_comb(`(--):real->real`,j))))
      STRIP_ASSUME_TAC THENL [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> max x (&0) = x`;
                 REAL_ARITH `&0 < x ==> max (--x) (&0) = &0`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] C1092NPPT_POSITIVE_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN (mk_disj(mk_comb(mk_comb(`(<=):real->real->bool`,`uC + aC`),
                                add (mul k `uE:real`) (mul j `vE:real`)),
                        mk_comb(mk_comb(`(<=):real->real->bool`,
                          mk_comb(mk_comb(`(-):real->real->real`, mul k `uC + aC`), mul j `vC:real`)),
                          `uE:real`)))
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th])
      (DISJ_CASES_THEN2 MP_TAC (fun th -> REWRITE_TAC[th])) o check (is_disj o concl)) THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`;
                  `&7 / &20`; `--(&7 / &20)`; `sC:real`; `--cC`] ABT_STRICT_BOUNDS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN
      REWRITE_TAC[REAL_POW_2; c977cc_normal] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN C1092POL_LIN_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [j; `vE + aC`; `--sE`] REAL_LE_LMUL) THEN
  MP_TAC(SPECL [j; `vC + aC`; `(&7 / &20) * (cC + sC)`] REAL_LE_LMUL) THEN
  MP_TAC(SPECL [k; `uC + aC`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`aC - &1`; add k j] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`aC - &1`; add `&1` j] REAL_LT_MUL) THEN
  REPEAT(ANTS_TAC THENL [C1092POL_LIN_TAC; ALL_TAC] THEN DISCH_TAC) THEN
  MAP_EVERY (fun th -> MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] th) THEN
                       ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092POL_LIN_TAC; DISCH_TAC])
    [C1092POS_FIRST_EXIT; C1092POS_FIRST_TARGET; C1092POS_FINAL_SOURCE] THEN
  SUBGOAL_THEN `vE + aC <= --sE - (&2 / &5) * cE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092POL_NFACT_TAC `~linside cE sE uE vE aC (&1) (--(&2 / &5))`
      `uE + aC <= cE + (&2 / &5) * --sE` THEN
    MP_TAC(SPECL [k; `uE + aC`; `cE + (&2 / &5) * --sE`] REAL_LE_LMUL) THEN
    ANTS_TAC THENL [C1092POL_LIN_TAC; DISCH_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN C1092POL_LIN_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [k; `uE + aC`; `cE + --sE`] REAL_LE_LMUL) THEN
  MP_TAC(SPECL [j; `vE + aC`; `--sE - (&2 / &5) * cE`] REAL_LE_LMUL) THEN
  REPEAT(ANTS_TAC THENL [C1092POL_LIN_TAC; ALL_TAC] THEN DISCH_TAC) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [C1092POL_LIN_TAC;
    MATCH_MP_TAC C1092POS_LAST_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `cE:real`; `--sE`; `vC + aC`] THEN
    ASM_REWRITE_TAC[] THEN C1092POL_LIN_TAC]);;
