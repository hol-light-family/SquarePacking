(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingPositiveBoundProfiles.lean    *)
(* (namespace N12Compact.C1092MPPMMissingPositiveBoundaries).               *)
(* The structures Data / Profile are the predicates c1092mpbp_data /         *)
(* c1092mpbp_profile of the square C = (c, s, u, v, a).  Normal:             *)
(* c977cc_normal; half / quarter_data: C1092WPS_half / C1092WPS_QUARTER_DATA;*)
(* MPPMMissingPositiveFaces.Inputs: c1092mmpf_inputs.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingPositiveFaces.ml";;
needs "n12/geometry/CP_C1092_ShallowCentralScalars.ml";;

(* Lean: Data (structure) *)
let c1092mpbp_data = new_definition
 `c1092mpbp_data c s u v a <=>
    c977cc_normal c s /\
    linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
    linside c s u v a (--(&1)) (--(&13 / &50)) /\
    linside c s u v a (--(&1)) (--(&2 / &5)) /\
    linside c s u v a (--(&1)) (--(&1 / &2)) /\
    ~linside c s u v a (--(&1)) (--(&1)) /\
    ~linside c s u v a (--(&1)) (&0) /\
    ~linside c s u v a (--(&13 / &50)) (&0) /\
    ~linside c s u v a (--(&14 / &25)) (--(&1)) /\
    ~linside c s u v a (--(&13 / &50)) (--(&1))`;;

(* Lean: Data.of_inputs *)
let C1092MPBP_DATA_OF_INPUTS = prove
 (`forall c s u v a.
     c977cc_normal c s /\ c1092mmpf_inputs c s u v a /\ ~linside c s u v a (--(&1)) (&0)
     ==> c1092mpbp_data c s u v a`,
  REWRITE_TAC[c1092mpbp_data; c1092mmpf_inputs] THEN MESON_TAC[]);;

(* Lean: Profile (structure) *)
let c1092mpbp_profile = new_definition
 `c1092mpbp_profile c s u v a <=>
    --c - s <= u /\ u + a <= --(&13 / &50) * c /\
    (&14 / &25) * s - c <= v /\ v + a <= s /\ &0 < s /\
    a <= (&37 / &50) * c + s /\ a <= c + (&11 / &25) * s /\
    &13 / &87 < C1092WPS_half c s /\ C1092WPS_half c s < &1 / &2`;;

let C1092MPBP_LIN_TAC =
  REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NLIN_TAC ~deg2:false []);;

(* linear arithmetic with one missing-point hypothesis ~linside c s u v a x y *)
let C1092MPBP_NFACT_TAC (x,y) t =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [MP_TAC(ASSUME (mk_neg(list_mk_comb(`linside c s u v a`,[x; y])))) THEN
    REWRITE_TAC[linside; DE_MORGAN_THM; REAL_NOT_LT] THEN
    STRIP_TAC THEN C1092MPBP_LIN_TAC; ALL_TAC];;

let C1092MPBP_INTRO_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mpbp_data] o
    check (can (term_match [] `c1092mpbp_data c s u v a`) o concl)) THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `c977cc_normal x y`) (concl th) then
    STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) else NO_TAC) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> try fst(strip_comb(concl th)) = `linside` with _ -> false) ths));;

let C1092MPBP_HALF_TAC =
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [C1092MPBP_LIN_TAC; ALL_TAC] THEN
  ABBREV_TAC `q = C1092WPS_half c s` THEN STRIP_TAC;;

(* Lean: profile *)
let C1092MPBP_PROFILE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ c1092mpbp_data c s u v a
     ==> c1092mpbp_profile c s u v a`,
  C1092MPBP_INTRO_TAC THEN REWRITE_TAC[c1092mpbp_profile] THEN
  C1092MPBP_NFACT_TAC (`--(&1)`,`&0`) `v + a <= s` THEN
  SUBGOAL_THEN `--c - s <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MPBP_NFACT_TAC (`--(&1)`,`--(&1)`) `s - c <= v` THEN C1092MPBP_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= --(&13 / &50) * c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MPBP_NFACT_TAC (`--(&13 / &50)`,`&0`) `v + a <= (&13 / &50) * s` THEN
    C1092MPBP_NFACT_TAC (`--(&13 / &50)`,`--(&1)`) `u + a <= --(&13 / &50) * c - s` THEN
    C1092MPBP_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&3 / &10) * c + s < &1` ASSUME_TAC THENL [C1092MPBP_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&14 / &25) * s - c <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MPBP_NFACT_TAC (`--(&14 / &25)`,`--(&1)`) `u + a <= --(&14 / &25) * c - s` THEN
    C1092MPBP_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [C1092MPBP_LIN_TAC; ALL_TAC] THEN
  C1092MPBP_HALF_TAC THEN
  SUBGOAL_THEN `q < &1 / &2` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[C1092WPS_half] THEN
    SUBGOAL_THEN `&0 < &1 + c` ASSUME_TAC THENL [C1092MPBP_LIN_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN C1092MPBP_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + q pow 2) * ((&37 / &50) * c + s - &1) = (&1 - q) * (&87 * q - &13) / &50`
    ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + q pow 2) * c = &1 - q pow 2` THEN
    UNDISCH_TAC `(&1 + q pow 2) * s = &2 * q` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `&13 / &87 < q` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`&1 + q * q`; `(&37 / &50) * c + s - &1`] REAL_LT_MUL) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [NLIN_TAC []; C1092MPBP_LIN_TAC]; DISCH_TAC] THEN
    MP_TAC(SPECL [`&1 - q`; `&13 - &87 * q`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [C1092MPBP_LIN_TAC; DISCH_TAC] THEN
    C1092MPBP_LIN_TAC;
    ALL_TAC] THEN
  C1092MPBP_LIN_TAC);;

(* Lean: central_bounds *)
let C1092MPBP_CENTRAL_BOUNDS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ c1092mpbp_data c s u v a
     ==> &7 / &10 < c /\ &29 / &100 < s /\ s < &71 / &100 /\ c * s <= &1 / &2 /\
         &156 / &125 < c + s /\ &0 <= c - s /\ c - s < &133 / &200 /\
         (&61 / &200) * c < s /\ c < &3700 / &3869 /\ &1131 / &3869 < s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092MPBP_PROFILE) THEN
  ASM_REWRITE_TAC[c1092mpbp_profile] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if can (term_match [] `c1092mpbp_data c s u v a`) (concl th)
    then STRIP_ASSUME_TAC(REWRITE_RULE[c1092mpbp_data] th) else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `c977cc_normal x y`) (concl th) then
    STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) else NO_TAC) THEN
  C1092MPBP_HALF_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `&0 < &1 + q * q` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `c < &3700 / &3869` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`&1 + q * q`; `c - &3700 / &3869`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [C1092MPBP_LIN_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`q - &13 / &87`; `q + &13 / &87`] REAL_LT_MUL) THEN
    ANTS_TAC THENL [C1092MPBP_LIN_TAC; DISCH_TAC] THEN
    C1092MPBP_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1131 / &3869 < s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`&1 + q * q`; `&1131 / &3869 - s`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [C1092MPBP_LIN_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`q - &13 / &87`; `&87 / &13 - q`] REAL_LT_MUL) THEN
    ANTS_TAC THENL [C1092MPBP_LIN_TAC; DISCH_TAC] THEN
    C1092MPBP_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&156 / &125 < c + s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`&1 + q * q`; `&156 / &125 - (c + s)`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [C1092MPBP_LIN_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`q - &13 / &87`; `&1 / &2 - q`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [C1092MPBP_LIN_TAC; DISCH_TAC] THEN
    C1092MPBP_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c * s <= &1 / &2 /\ &7 / &10 < c /\ s < &71 / &100` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `c - s:real`]; ALL_TAC] THEN
  C1092MPBP_LIN_TAC);;
