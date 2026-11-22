(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C972NortheastPositiveEnding.lean   *)
(* (namespaces N12Compact.FiniteCases.C972Local and .C972).  The two         *)
(* remaining positive actual central squares cannot separate; C972 family    *)
(* excluded.  Conventions of CP_FiniteCases_C972NortheastSign.ml (E, N =     *)
(* cE sE uE vE aE / cN sN uN vN aN, upper / lower = ABT_upper / ABT_lower,   *)
(* the cone / reverse / separation steps c972nsg_cone(_rev) / c972nsg_sep);  *)
(* C983.F4SoutheastSignSupports.Data = c983fss_data; PositiveNorth           *)
(* c972npf_positiveNorth; NortheastPositiveScalars.* = C972NPS_* /           *)
(* c972nps_*.  C972 part: exists_positive_southeast / southeast_support_     *)
(* profile C972SP_*, exists_positive_northeast / southeast_center            *)
(* C972NSG_*, northeast_positive_faces C972NPF_*, southeast_lower_face       *)
(* C972RF_*, northeast_origin C972UE_*, fixed C972CS_FIXED_TAC, apart        *)
(* c972mc_apart.  Tag C972NPE_.                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C972NortheastPositiveFaces.ml";;
needs "n12/geometry/CP_FiniteCases_C972NortheastPositiveScalars.ml";;

(* Lean: PositivePairInput (structure) *)
let c972npe_input = new_definition
 `c972npe_input (cE:real) (sE:real) (uE:real) (vE:real) (aE:real)
                (cN:real) (sN:real) (uN:real) (vN:real) (aN:real) <=>
    &1 < aE /\ aE = aN /\ c977cc_normal cE sE /\ c977cc_normal cN sN /\ &0 < sN /\
    c983fss_data cE sE uE vE aE /\
    linside cE sE uE vE aE (&0) (&0) /\ linside cE sE uE vE aE (&1) (--(&13 / &50)) /\
    --sE - cE / &2 <= vE /\
    linside cN sN uN vN aN (&7 / &20) (&7 / &20) /\ linside cN sN uN vN aN (&0) (&1) /\
    c972npf_positiveNorth cN sN uN vN aN /\
    ldisj cE sE uE vE aE cN sN uN vN aN`;;

(* Lean: upper_pp (private) *)
let C972NPE_UPPER_PP = C972NSG_UPPER_PP;;

(* Lean: upper_np (private) *)
let C972NPE_UPPER_NP = prove
 (`forall c s u v a nx ny. nx * c + ny * s <= &0 /\ &0 <= --nx * s + ny * c
     ==> ABT_upper c s u v a nx ny = (nx * c + ny * s) * u + (--nx * s + ny * c) * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C981SF_UPPER_IN_BANDS] THEN
  ASM_CASES_TAC `nx * c + ny * s = &0` THEN ASM_REWRITE_TAC[real_abs; REAL_LE_REFL] THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(&0 <= nx * c + ny * s)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: lower_pp (private) *)
let C972NPE_LOWER_PP = prove
 (`forall c s u v a nx ny. &0 <= nx * c + ny * s /\ &0 <= --nx * s + ny * c
     ==> ABT_lower c s u v a nx ny = (nx * c + ny * s) * u + (--nx * s + ny * c) * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C981SF_LOWER_IN_BANDS] THEN
  ASM_REWRITE_TAC[real_abs] THEN REAL_ARITH_TAC);;

(* Lean: lower_np (private) *)
let C972NPE_LOWER_NP = C972NSG_LOWER_NP;;

(* Lean: upper_self_v (private) *)
let C972NPE_UPPER_SELF_V = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a ==> ABT_upper c s u v a (--s) c = v + a`,
  SIMP_TAC[ABT_OWNV]);;

(* Lean: lower_self_v (private) *)
let C972NPE_LOWER_SELF_V = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a ==> ABT_lower c s u v a (--s) c = v`,
  SIMP_TAC[ABT_OWNV]);;

(* the product facts for the four transverse alternatives *)
let c972npe_prod_tac tms =
  SUBGOAL_THEN (list_mk_conj tms) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC;
           MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC];
    ALL_TAC];;

(* Lean: positive_pair_impossible *)
let C972NPE_POSITIVE_PAIR_IMPOSSIBLE = prove
 (`forall cE sE uE vE aE cN sN uN vN aN.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     c972npe_input cE sE uE vE aE cN sN uN vN aN ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c972npe_input; c983fss_data; c972npf_positiveNorth] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aE:real = aN`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o check (fun th -> concl th = `c977cc_normal cE sE`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o check (fun th -> concl th = `c977cc_normal cN sN`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o check (fun th -> concl th = `c977cc_normal cN sN`)) THEN
  SUBGOAL_THEN `&0 < cE * cN + sE * sN` ASSUME_TAC THENL
   [NLIN_FACTS_TAC [] [`&0 < cE * cN`; `&0 <= sE * sN`] THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `linside cE sE uE vE aN (&1) (--(&13 / &50)) /\ linside cN sN uN vN aN (&7 / &20) (&7 / &20)` MP_TAC THENL
   [ASM_REWRITE_TAC[]; REWRITE_TAC[linside] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `uE < &0 /\ cE - (&13 / &50) * sE < uE + aN /\ &1 - sE - cE / &2 < vE + aN /\
                &0 < &1 - sE - cE / &2 /\ vN < (&543 / &500) * cN - &1 /\
                &1 + (&13 / &50) * sN < uN + aN` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
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
     [MP_TAC(SPECL C972NSG_EN C972NPE_UPPER_SELF_V) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ASM_CASES_TAC `&0 <= cE * sN - sE * cN` THENL
       [MP_TAC(SPECL (C972NSG_N @ [`--sE:real`; `cE:real`]) C972NPE_LOWER_PP) THEN
        ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
        c972npe_prod_tac [`&0 <= (cE * sN - sE * cN) * ((&7 / &20) * (cN + sN) - uN)`;
                          `&0 < (cE * cN + sE * sN) * (((&543 / &500) * cN - &1) - vN)`] THEN
        MP_TAC(SPECL [`cE:real`; `sE:real`; `cN:real`; `sN:real`] C972NPS_SOURCE_AXIS_STEEPER) THEN
        ASM_REWRITE_TAC[c972nps_aplus; c972nps_bplus] THEN DISCH_TAC THEN
        SUBGOAL_THEN `(&1 - sE - cE / &2) - (cE * sN - sE * cN) * ((&7 / &20) * (cN + sN)) -
                      (cE * cN + sE * sN) * ((&543 / &500) * cN - &1) =
                      &1 - cE * (&793 / &500 - cN - &92 / &125 * sN pow 2 + &7 / &20 * cN * sN) -
                      sE * (&13 / &20 - sN + &7 / &20 * sN pow 2 + &92 / &125 * cN * sN)` ASSUME_TAC THENL
         [UNDISCH_TAC `cN * cN + sN * sN = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
        NLIN_TAC ~deg2:false [];
        MP_TAC(SPECL [`cE:real`; `sE:real`; `cN:real`; `sN:real`] C972NPS_RELATIVE_ORDER) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
        MP_TAC(SPECL (C972NSG_N @ [`--sE:real`; `cE:real`]) C972NPE_LOWER_NP) THEN
        ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
        c972npe_prod_tac [`&0 <= --(cE * sN - sE * cN) * ((uN + aN) - (&1 + (&13 / &50) * sN))`;
                          `&0 < (cE * cN + sE * sN) * (((&543 / &500) * cN - &1) - vN)`] THEN
        MP_TAC(SPECL [`cE:real`; `sE:real`; `cN:real`; `sN:real`] C972NPS_SOURCE_AXIS_SHALLOWER) THEN
        ASM_REWRITE_TAC[c972nps_aminus; c972nps_bminus] THEN DISCH_TAC THEN
        SUBGOAL_THEN `(&1 - sE - cE / &2) - (cE * sN - sE * cN) * (&1 + (&13 / &50) * sN) -
                      (cE * cN + sE * sN) * ((&543 / &500) * cN - &1) =
                      &1 - cE * (&793 / &500 - cN + sN - &413 / &500 * sN pow 2) -
                      sE * (&1 - cN - sN + &413 / &500 * cN * sN)` ASSUME_TAC THENL
         [UNDISCH_TAC `cN * cN + sN * sN = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
        NLIN_TAC ~deg2:false []];
      c972nsg_cone_rev `--sE:real` `cE:real`];
    (* NU *)
    c972nsg_sep C972NSG_EN C972NSG_N `cN:real` `sN:real` ABT_PARALLEL_RADIUS true THEN STRIP_TAC THENL
     [MP_TAC(SPECL (C972NSG_EN @ [`&1`; `--(&13 / &50)`; `cN:real`; `sN:real`]) ABT_STRICT_BOUNDS) THEN
      MP_TAC(SPECL (C972NSG_N @ [`&7 / &20`; `&7 / &20`; `cN:real`; `sN:real`]) ABT_STRICT_BOUNDS) THEN
      ASM_REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC;
      c972nsg_cone_rev `cN:real` `sN:real`];
    (* NV *)
    c972nsg_sep C972NSG_EN C972NSG_N `--sN:real` `cN:real` ABT_TRANSVERSE_RADIUS true THEN STRIP_TAC THENL
     [MP_TAC(SPECL C972NSG_N C972NPE_LOWER_SELF_V) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ASM_CASES_TAC `&0 <= cE * sN - sE * cN` THENL
       [MP_TAC(SPECL [`cN:real`; `sN:real`; `cE:real`; `sE:real`] C972NPS_RELATIVE_ORDER) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
        MP_TAC(SPECL (C972NSG_EN @ [`--sN:real`; `cN:real`]) C972NPE_UPPER_NP) THEN
        ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
        MP_TAC(SPECL [`cE:real`; `sE:real`; `cN:real`; `sN:real`] C972NPS_ALPHA_LOWER) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        MP_TAC(SPECL [`cN:real`; `sN:real`] C972NPS_RIGHT_PROJECTION) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        c972npe_prod_tac [`&0 <= (cE * sN - sE * cN) * --uE`;
                          `&0 < (cE * cN + sE * sN) * ((vE + aN) - (&1 - sE - cE / &2))`;
                          `&0 <= ((cE * cN + sE * sN) - cN) * (&1 - sE - cE / &2)`;
                          `&0 <= cN * ((&1 - sE - cE / &2) - (&1 / &2 - sN))`] THEN
        NLIN_TAC ~deg2:false [];
        MP_TAC(SPECL [`cE:real`; `sE:real`; `cN:real`; `sN:real`] C972NPS_RELATIVE_ORDER) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
        MP_TAC(SPECL (C972NSG_EN @ [`--sN:real`; `cN:real`]) C972NPE_UPPER_PP) THEN
        ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
        c972npe_prod_tac [`&0 <= --(cE * sN - sE * cN) * ((uE + aN) - (cE - (&13 / &50) * sE))`;
                          `&0 < (cE * cN + sE * sN) * ((vE + aN) - (&1 - sE - cE / &2))`] THEN
        MP_TAC(SPECL [`cE:real`; `sE:real`; `cN:real`; `sN:real`] C972NPS_NORTH_AXIS_SHALLOWER) THEN
        ASM_REWRITE_TAC[c972nps_p; c972nps_q] THEN DISCH_TAC THEN
        SUBGOAL_THEN `--(cE * sN - sE * cN) * (cE - (&13 / &50) * sE) +
                      (cE * cN + sE * sN) * (&1 - sE - cE / &2) - ((&543 / &500) * cN - &1) =
                      &1 - cN * (&673 / &500 - cE + &6 / &25 * cE pow 2) -
                      sN * (&1 - sE + &6 / &25 * cE * sE)` ASSUME_TAC THENL
         [UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
        NLIN_TAC ~deg2:false []];
      c972nsg_cone_rev `--sN:real` `cN:real`]]);;

(* Lean: family_impossible *)
let C972NPE_FAMILY_IMPOSSIBLE = prove
 (c972mc_stmt [] `false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < &0 ==> false`) THEN
  C972NSG_SOUTHEAST_TAC THEN
  MP_TAC(SPEC_ALL C972NSG_EXISTS_POSITIVE_NORTHEAST) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(itlist (fun v t -> X_CHOOSE_THEN v t) C972NSG_N STRIP_ASSUME_TAC) THEN
  C972SP_USE_TAC (C972MC_V5 @ C972NSG_N) C972NPF_NORTHEAST_POSITIVE_FACES THEN
  MAP_EVERY (fun th -> MP_TAC(SPEC_ALL th) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC])
    [C972NSG_SOUTHEAST_CENTER; C972UE_NORTHEAST_ORIGIN] THEN
  C972CS_FIXED_TAC THEN
  MATCH_MP_TAC(TAUT `false ==> &0 < &0`) THEN
  MATCH_MP_TAC (SPECL (C972SP_E @ C972NSG_N) C972NPE_POSITIVE_PAIR_IMPOSSIBLE) THEN
  REWRITE_TAC[c972npe_input; ldisj; ASSUME C972SP_ACT_E; ASSUME C972NSG_ACT_N] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[c972mc_apart 512 1024] THEN NO_TAC;
         REWRITE_TAC[c983fss_data] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         RASM_ARITH_TAC]);;
