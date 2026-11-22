(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C972NortheastSign.lean             *)
(* (namespaces N12Compact.FiniteCases.C972Local and .C972).  The remaining   *)
(* C972 northeast square has positive canonical sine.  OpenSquares E, N are  *)
(* cE sE uE vE aE / cN sN uN vN aN (unit normal and positive side explicit); *)
(* Normal = c977cc_normal; upper / lower / supportRadius = ABT_upper /       *)
(* ABT_lower / tss_support_radius; pairRadius / FaceSeparation =            *)
(* C977CB_pairRadius / C977CB_faceSep; strict_bounds / closed_bounds /       *)
(* separated / parallel_radius / transverse_radius = ABT_*;                  *)
(* faceSeparation_of_disjoint = CSAT_FACESEPARATION_OF_DISJOINT; upper_in_   *)
(* bands / lower_in_bands = C981SF_*; WallProfile.vertex / upper_neg /       *)
(* lower_neg = OCWPVG_*; NortheastScalars.* = FC972NS_*.                     *)
(* C972 part: conventions of CP_FiniteCases_C972SoutheastPositive.ml (owners *)
(* p 6 / 7 / 3 = masks 512 / 1024 / 48; E, N with C972SP_SQ_E-style facts:   *)
(* unit normal, positive side, side = l, actual equivalence at (2+x, 2+y)).  *)
(* exists_positive_southeast / southeast_support_profile C972SP_*,           *)
(* southeast_missing_halfpoint / northeast_origin C972UE_*, southeast_lower_ *)
(* face / southeast_height_positive C972RF_*, northeast_missing_f5           *)
(* C972UR_*, fixed C972CS_FIXED_TAC (missing_top included), seed oo_seed,    *)
(* apart c972mc_apart, ClosedFrames.canonical_frame CLF_CANONICAL_FRAME.     *)
(* Tag C972NSG_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C972NortheastSignScalars.ml";;
needs "n12/geometry/CP_FiniteCases_C972ResidualFaces.ml";;
needs "n12/geometry/CP_OtherCases_SupportBands.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;
needs "n12/geometry/CP_FiniteCases_C972UpperReduction.ml";;

let C972NSG_N = [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`];;
let C972NSG_E = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`];;
let c972nsg_head c th = is_comb (concl th) && fst (strip_comb (concl th)) = c;;
let C972NSG_LIN_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

(* a negated linside assumption at a literal point: prove its four bands *)
let c972nsg_not_tac tm =
  UNDISCH_TAC (mk_neg tm) THEN REWRITE_TAC[linside] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[] THEN C972NSG_LIN_TAC;;

(* Lean: NegativeNorth (structure) *)
let c972nsg_negativeNorth = new_definition
 `c972nsg_negativeNorth (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    (&543 / &500) * s <= u /\ (&13 / &50) * c <= v /\ v + a <= c - s /\ &0 < u + a`;;

(* Lean: negative_north_faces *)
let C972NSG_NEGATIVE_NORTH_FACES = prove
 (`forall cN sN uN vN aN. cN * cN + sN * sN = &1 /\ &0 < aN /\ &1 < aN /\ c977cc_normal cN (--sN) /\
     linside cN sN uN vN aN (&7 / &20) (&7 / &20) /\ linside cN sN uN vN aN (&0) (&1) /\
     ~linside cN sN uN vN aN (&0) (&13 / &50) /\ ~linside cN sN uN vN aN (&0) (&543 / &500) /\
     ~linside cN sN uN vN aN (&1) (&1) /\ ~linside cN sN uN vN aN (&1) (&543 / &500)
     ==> c972nsg_negativeNorth cN sN uN vN aN`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2; REAL_NEG_MUL2] o
    check (c972nsg_head `c977cc_normal`)) THEN
  SUBGOAL_THEN `linside cN sN uN vN aN (&7 / &20) (&7 / &20) /\ linside cN sN uN vN aN (&0) (&1)` MP_TAC THENL
   [ASM_REWRITE_TAC[]; REWRITE_TAC[linside] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN STRIP_TAC] THEN
  SUBGOAL_THEN `(&13 / &50) * cN <= vN` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    c972nsg_not_tac `linside cN sN uN vN aN (&0) (&13 / &50)`; ALL_TAC] THEN
  SUBGOAL_THEN `(&543 / &500) * sN <= uN` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `vN + aN <= (&543 / &500) * cN` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      c972nsg_not_tac `linside cN sN uN vN aN (&0) (&543 / &500)`; ALL_TAC] THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `vN + aN <= --sN + (&543 / &500) * cN` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    c972nsg_not_tac `linside cN sN uN vN aN (&1) (&543 / &500)`; ALL_TAC] THEN
  SUBGOAL_THEN `&87 / &500 < --sN` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `cN + (&43 / &500) * --sN < &1` ASSUME_TAC THENL
   [NLIN_FACTS_TAC [SQ_NONNEG `cN - &1`]
     [`cN <= &1 - (sN * sN) / &2`; `&0 < --sN * (--sN - &43 / &250)`] THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `vN + aN <= cN + --sN` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    c972nsg_not_tac `linside cN sN uN vN aN (&1) (&1)`; ALL_TAC] THEN
  REWRITE_TAC[c972nsg_negativeNorth] THEN C972NSG_LIN_TAC);;

(* Lean: NortheastSignInput (structure) *)
let c972nsg_input = new_definition
 `c972nsg_input (cE:real) (sE:real) (uE:real) (vE:real) (aE:real)
                (cN:real) (sN:real) (uN:real) (vN:real) (aN:real) <=>
    &1 < aE /\ aE = aN /\ c977cc_normal cE sE /\ &0 < sE /\ &4 / &5 < cE /\ sE < &1 / &2 /\
    linside cE sE uE vE aE (&1) (--(&13 / &50)) /\ linside cE sE uE vE aE (&0) (&0) /\
    --sE - cE / &2 <= vE /\
    c977cc_normal cN (--sN) /\ linside cN sN uN vN aN (&7 / &20) (&7 / &20) /\
    linside cN sN uN vN aN (&0) (&1) /\
    ~linside cN sN uN vN aN (&0) (&13 / &50) /\ ~linside cN sN uN vN aN (&0) (&543 / &500) /\
    ~linside cN sN uN vN aN (&1) (&1) /\ ~linside cN sN uN vN aN (&1) (&543 / &500) /\
    ldisj cE sE uE vE aE cN sN uN vN aN`;;

(* Lean: upper_pp (private) *)
let C972NSG_UPPER_PP = prove
 (`forall c s u v a nx ny. &0 <= nx * c + ny * s /\ &0 <= --nx * s + ny * c
     ==> ABT_upper c s u v a nx ny = (nx * c + ny * s) * (u + a) + (--nx * s + ny * c) * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C981SF_UPPER_IN_BANDS] THEN
  ASM_REWRITE_TAC[real_abs] THEN REAL_ARITH_TAC);;

(* Lean: lower_np (private) *)
let C972NSG_LOWER_NP = prove
 (`forall c s u v a nx ny. nx * c + ny * s <= &0 /\ &0 <= --nx * s + ny * c
     ==> ABT_lower c s u v a nx ny = (nx * c + ny * s) * (u + a) + (--nx * s + ny * c) * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C981SF_LOWER_IN_BANDS] THEN
  ASM_CASES_TAC `nx * c + ny * s = &0` THEN ASM_REWRITE_TAC[real_abs; REAL_LE_REFL] THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(&0 <= nx * c + ny * s)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* the two positive cross products j, k of the frames *)
let C972NSG_JK = prove
 (`forall cE sE cN r. c977cc_normal cE sE /\ c977cc_normal cN r /\ &0 < sE /\ &4 / &5 < cE /\ sE < &1 / &2
     ==> &0 < r * cE + cN * sE /\ &0 < cN * cE - r * sE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cN:real`; `r:real`] C977CC_NORMAL_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  CONJ_TAC THENL
   [NLIN_FACTS_TAC [] [`&0 <= r * cE`; `&0 < cN * sE`] THEN NLIN_TAC ~deg2:false [];
    NLIN_FACTS_TAC [] [`&0 < cN * (cE - sE)`; `&0 <= sE * (cN - r)`] THEN NLIN_TAC ~deg2:false []]);;

let C972NSG_SQ_E = `cE * cE + sE * sE = &1 /\ &0 < aE`;;
let C972NSG_SQ_N = `cN * cN + sN * sN = &1 /\ &0 < aN`;;

(* the cone of separating normals (Lean: cone, inside northeast_negative_impossible) *)
let C972NSG_CONE = prove
 (`forall cE sE uE vE aE cN sN uN vN aN nx ny.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     linside cE sE uE vE aE (&0) (&0) /\ linside cN sN uN vN aN (&0) (&1) /\
     nx pow 2 + ny pow 2 = &1 /\ ABT_upper cE sE uE vE aE nx ny <= ABT_lower cN sN uN vN aN nx ny
     ==> &0 < ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C972NSG_E @ [`&0`; `&0`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL (C972NSG_N @ [`&0`; `&1`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* the reversed separation as a cone instance (Lean: reverse) *)
let C972NSG_CONE_REV = prove
 (`forall cE sE uE vE aE cN sN uN vN aN nx ny.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     linside cE sE uE vE aE (&0) (&0) /\ linside cN sN uN vN aN (&0) (&1) /\
     nx pow 2 + ny pow 2 = &1 /\ ABT_upper cN sN uN vN aN nx ny <= ABT_lower cE sE uE vE aE nx ny
     ==> &0 < --ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPECL (C972NSG_E @ C972NSG_N @ [`--nx:real`; `--ny:real`]) C972NSG_CONE) THEN
  ASM_REWRITE_TAC[OCWPVG_UPPER_NEG; OCWPVG_LOWER_NEG; REAL_POW_NEG; ARITH] THEN ASM_REAL_ARITH_TAC);;

let C972NSG_EN = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aN:real`];;
let c972nsg_cone_gen th nx ny =
  MP_TAC(REWRITE_RULE[REAL_POW_NEG; ARITH; REAL_NEG_NEG; REAL_POW_2; REAL_NEG_MUL2]
    (SPECL (C972NSG_EN @ C972NSG_N @ [nx; ny]) th)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; RASM_ARITH_TAC];;
let c972nsg_cone = c972nsg_cone_gen C972NSG_CONE;;
let c972nsg_cone_rev = c972nsg_cone_gen C972NSG_CONE_REV;;

let c972nsg_sep q r nx ny rad swap =
    let radargs = if swap then [`cN:real`; `sN:real`; `aN:real`; `cE:real`; `sE:real`; `aN:real`]
                  else [`cE:real`; `sE:real`; `aN:real`; `cN:real`; `sN:real`; `aN:real`] in
    DISCH_THEN(fun ax -> MP_TAC(SPECL (q @ r @ [nx; ny]) ABT_SEPARATED) THEN
    ANTS_TAC THENL
     [(if swap then GEN_REWRITE_TAC LAND_CONV [REAL_ADD_SYM] else ALL_TAC) THEN
      MP_TAC(SPECL radargs rad) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC THEN ACCEPT_TAC ax];
      ALL_TAC]);;

let C972NSG_INPUT_HYPS = `cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     c972nsg_input cE sE uE vE aE cN sN uN vN aN`;;

(* Lean: northeast_negative_impossible *)
let C972NSG_NORTHEAST_NEGATIVE_IMPOSSIBLE = prove
 (`forall cE sE uE vE aE cN sN uN vN aN.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     c972nsg_input cE sE uE vE aE cN sN uN vN aN ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c972nsg_input] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aE:real = aN`)) THEN
  MP_TAC(SPECL C972NSG_N C972NSG_NEGATIVE_NORTH_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c972nsg_negativeNorth] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `cN:real`; `--sN`] C972NSG_JK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o check (fun th -> concl th = `c977cc_normal cE sE`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o check (fun th -> concl th = `c977cc_normal cN (--sN)`)) THEN
  SUBGOAL_THEN `linside cE sE uE vE aN (&1) (--(&13 / &50)) /\ linside cN sN uN vN aN (&7 / &20) (&7 / &20)` MP_TAC THENL
   [ASM_REWRITE_TAC[]; REWRITE_TAC[linside] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `cE - (&13 / &50) * sE < uE + aN /\ &1 - sE - cE / &2 < vE + aN` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL (C972NSG_EN @ C972NSG_N) CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN MP_TAC o REWRITE_RULE[C977CB_faceSep]) THENL
   [(* EU *)
    c972nsg_sep C972NSG_EN C972NSG_N `cE:real` `sE:real` ABT_PARALLEL_RADIUS false THEN STRIP_TAC THENL
     [MP_TAC(SPECL (C972NSG_EN @ [`&1`; `--(&13 / &50)`; `cE:real`; `sE:real`]) ABT_STRICT_BOUNDS) THEN
      MP_TAC(SPECL (C972NSG_N @ [`&0`; `&1`; `cE:real`; `sE:real`]) ABT_STRICT_BOUNDS) THEN
      ASM_REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC;
      c972nsg_cone_rev `cE:real` `sE:real`];
    (* EV *)
    c972nsg_sep C972NSG_EN C972NSG_N `--sE:real` `cE:real` ABT_TRANSVERSE_RADIUS false THEN STRIP_TAC THENL
     [MP_TAC(SPECL C972NSG_EN ABT_OWNV) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(SPECL (C972NSG_N @ [`--sE:real`; `cE:real`]) C972NSG_LOWER_NP) THEN
      ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
      MP_TAC(SPECL [`cE:real`; `sE:real`; `cN:real`; `--sN`] FC972NS_SOURCE_TRANSVERSE) THEN
      ASM_REWRITE_TAC[fc972ns_A; fc972ns_B] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < (--sN * cE + cN * sE) * (uN + aN - (&1 - (&543 / &500) * --sN)) /\
                    &0 < (cN * cE - --sN * sE) * ((&7 / &20) * (cN + --sN) - vN)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&1 - sE - cE / &2 + (--sN * cE + cN * sE) * (&1 - (&543 / &500) * --sN) -
                    (&7 / &20) * (cN * cE - --sN * sE) * (cN + --sN) =
                    &1 - cE * (&17 / &20 - --sN + (&92 / &125) * --sN pow 2 + (&7 / &20) * cN * --sN) -
                    sE * (&1 - cN - (&7 / &20) * --sN pow 2 + (&92 / &125) * cN * --sN)` ASSUME_TAC THENL
       [UNDISCH_TAC `cN * cN + sN * sN = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      NLIN_TAC ~deg2:false [];
      c972nsg_cone_rev `--sE:real` `cE:real`];
    (* NU *)
    c972nsg_sep C972NSG_EN C972NSG_N `cN:real` `sN:real` ABT_PARALLEL_RADIUS true THEN STRIP_TAC THENL
     [c972nsg_cone `cN:real` `sN:real`;
      MP_TAC(SPECL C972NSG_N ABT_OWNU) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(SPECL (C972NSG_EN @ [`&0`; `&0`; `--cN:real`; `--sN:real`]) ABT_STRICT_BOUNDS) THEN
      ASM_REWRITE_TAC[REAL_POW_NEG; REAL_POW_2; ARITH; OCWPVG_UPPER_NEG] THEN RASM_ARITH_TAC];
    (* NV *)
    c972nsg_sep C972NSG_EN C972NSG_N `--sN:real` `cN:real` ABT_TRANSVERSE_RADIUS true THEN STRIP_TAC THENL
     [MP_TAC(SPECL C972NSG_N ABT_OWNV) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(SPECL (C972NSG_EN @ [`--sN:real`; `cN:real`]) C972NSG_UPPER_PP) THEN
      ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
      MP_TAC(SPECL [`cE:real`; `sE:real`; `cN:real`; `--sN`] FC972NS_NORTH_TRANSVERSE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < (--sN * cE + cN * sE) * (uE + aN - (cE - (&13 / &50) * sE)) /\
                    &0 < (cN * cE - --sN * sE) * (vE + aN - (&1 - sE - cE / &2))` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(--sN * cE + cN * sE) * (cE - (&13 / &50) * sE) + (cN * cE - --sN * sE) * (&1 - sE - cE / &2) -
                    (&7 / &20) * (cN + --sN) =
                    cN * (cE - &61 / &100 - (&6 / &25) * cE pow 2) +
                    --sN * (&13 / &20 - sE + (&6 / &25) * cE * sE)` ASSUME_TAC THENL
       [UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      NLIN_TAC ~deg2:false [];
      c972nsg_cone_rev `--sN:real` `cN:real`]]);;

(* ------------------------------------------------------------------------- *)
(* namespace C972                                                            *)
(* ------------------------------------------------------------------------- *)

let C972NSG_ACT_N = c972sp_actual C972NSG_N 1024;;
let C972NSG_SQ_N4 = [`cN * cN + sN * sN = &1`; `&0 < aN`; `aN:real = l`; C972NSG_ACT_N];;

(* the positive southeast square E with its support data as assumptions *)
let C972NSG_SOUTHEAST_TAC =
  MP_TAC(SPEC_ALL C972UE_SOUTHEAST_MISSING_HALFPOINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972SP_EXISTS_POSITIVE_SOUTHEAST) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(itlist (fun v t -> X_CHOOSE_THEN v t) C972SP_E STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cE sE`)) THEN
  SUBGOAL_THEN `&0 < cE /\ abs sE <= cE` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `c977cc_normal cE sE` THEN REWRITE_TAC[c977cc_normal] THEN
    ASM_REWRITE_TAC[real_abs] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  C972SP_USE_TAC (C972MC_V5 @ C972SP_E) C972SP_SOUTHEAST_SUPPORT_PROFILE THEN
  C972SP_USE_TAC (C972MC_V5 @ C972SP_E) C972RF_SOUTHEAST_HEIGHT_POSITIVE THEN
  C972SP_USE_TAC (C972MC_V5 @ C972SP_E) C972RF_SOUTHEAST_LOWER_FACE THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c983fss_data] o check (c972nsg_head `c983fss_data`));;

(* Lean: southeast_center *)
let C972NSG_SOUTHEAST_CENTER = prove
 (c972mc_stmt [] (c972mc_own 512 `&2` `&2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C972NSG_SOUTHEAST_TAC THEN
  SUBGOAL_THEN `linside cE sE uE vE aE (&0) (&0)` MP_TAC THENL
   [REWRITE_TAC[linside] THEN C972NSG_LIN_TAC;
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[]]);;

(* Lean: northeast_positive *)
let C972NSG_NORTHEAST_POSITIVE = prove
 (c972swp_stmt C972NSG_N (C972NSG_SQ_N4 @ [`&0 < cN`; `abs sN <= cN`]) `&0 < sN`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C972NSG_SOUTHEAST_TAC THEN
  MAP_EVERY (fun th -> MP_TAC(SPEC_ALL th) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC])
    [C972NSG_SOUTHEAST_CENTER; C972UE_NORTHEAST_ORIGIN; C972UR_NORTHEAST_MISSING_F5] THEN
  ASSUME_TAC (c972mc_seed 48 (`&3`, `&1543 / &500`)) THEN
  C972CS_FIXED_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C972SP_E @ C972NSG_N) C972NSG_NORTHEAST_NEGATIVE_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[c972nsg_input; ldisj] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[c972mc_apart 512 1024] THEN NO_TAC;
         REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_NEG_MUL2] THEN
           MAP_EVERY UNDISCH_TAC [`abs sN <= cN`; `sN <= &0`; `cN * cN + sN * sN = &1`] THEN
           REAL_ARITH_TAC;
         DISCH_TAC THEN C972CS_CLASH_TAC;
         RASM_ARITH_TAC]);;

(* Lean: exists_positive_northeast *)
let C972NSG_EXISTS_POSITIVE_NORTHEAST = prove
 (c972swp_stmt [] []
    (list_mk_exists(C972NSG_N, list_mk_conj (C972NSG_SQ_N4 @ [`c977cc_normal cN sN`; `&0 < sN`]))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL (c972ss_tr22 (c972mc_tuple 1024)) CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ACCEPT_TAC (c972mc_unit 1024); MP_TAC C972MC_SIDE THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC C972NSG_N THEN STRIP_TAC THEN
  SUBGOAL_THEN C972NSG_ACT_N ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) `linside`)) (concl th)
                           then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[C972NF_TRANSLATED]; ALL_TAC] THEN
  SUBGOAL_THEN `aN:real = l` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  C972SP_USE_TAC (C972MC_V5 @ C972NSG_N) C972NSG_NORTHEAST_POSITIVE THEN
  MAP_EVERY EXISTS_TAC C972NSG_N THEN REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN RASM_ARITH_TAC]);;
