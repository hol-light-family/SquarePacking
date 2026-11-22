(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMPositiveCrosspointSeeds.lean         *)
(* (N12Compact.C1092MPPMPositiveCrosspointSeeds).  C1092-MPPM-POSITIVE-      *)
(* CROSSPOINT-SEEDS, sections 2--3.  The square C is c s u v a; Normal is    *)
(* c977cc_normal; MissingPositiveFaces Inputs/Faces/profile are              *)
(* c1092mmpf_inputs / c1092mmpf_faces / C1092MMPF_PROFILE.                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingPositiveFaces.ml";;

let C1092PCS_LIN_TAC (asl,w as g) =
  let rec ok t = is_real_rel t || (is_neg t && is_real_rel (rand t)) ||
                 (is_conj t && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

(* use the exclusion ~linside c s u v a x y (after unfolding) *)
let C1092PCS_MISS_TAC x y =
  UNDISCH_TAC (mk_neg(list_mk_comb(`linside c s u v a`,[x;y]))) THEN
  REWRITE_TAC[linside; DE_MORGAN_THM; REAL_NOT_LT] THEN
  REPEAT CONJ_TAC THEN FIRST [NLIN_TAC ~deg2:false []; C1092PCS_LIN_TAC];;

let C1092PCS_LP_TAC =
  REPEAT CONJ_TAC THEN FIRST [NLIN_TAC ~deg2:false []; C1092PCS_LIN_TAC];;

(* prove a face fact by contradiction with an excluded point *)
let C1092PCS_FACT_TAC t x y =
  SUBGOAL_THEN t ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN C1092PCS_MISS_TAC x y; ALL_TAC];;

let C1092PCS_SETUP_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th);;

(* Lean: ForwardCore (structure) *)
let c1092pcs_forwardCore = new_definition
 `c1092pcs_forwardCore c s u v a <=>
    linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
    linside c s u v a (--(&1)) (--(&13 / &50)) /\
    linside c s u v a (--(&1)) (--(&2 / &5)) /\
    linside c s u v a (--(&13 / &50)) (&0) /\
    ~linside c s u v a (--(&1)) (--(&1)) /\
    ~linside c s u v a (--(&1)) (&0) /\
    ~linside c s u v a (--(&2 / &5)) (--(&1))`;;

(* Lean: ForwardInputs (structure) *)
let c1092pcs_forwardInputs = new_definition
 `c1092pcs_forwardInputs c s u v a <=>
    linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
    linside c s u v a (--(&1)) (--(&13 / &50)) /\
    linside c s u v a (--(&1)) (--(&2 / &5)) /\
    linside c s u v a (--(&13 / &50)) (&0) /\
    ~linside c s u v a (--(&1)) (--(&1)) /\
    ~linside c s u v a (--(&1)) (&0) /\
    ~linside c s u v a (--(&2 / &5)) (--(&1)) /\
    ~linside c s u v a (--(&14 / &25)) (--(&1)) /\
    ~linside c s u v a (--(&7 / &20)) (&7 / &20)`;;

(* Lean: ForwardInputs.core *)
let C1092PCS_FORWARDINPUTS_CORE = prove
 (`forall c s u v a. c1092pcs_forwardInputs c s u v a ==> c1092pcs_forwardCore c s u v a`,
  REWRITE_TAC[c1092pcs_forwardInputs; c1092pcs_forwardCore] THEN MESON_TAC[]);;

(* Lean: ForwardFaces (structure) *)
let c1092pcs_forwardFaces = new_definition
 `c1092pcs_forwardFaces c s u v a <=>
    --c - s <= u /\ (&2 / &5) * s - c <= v /\ v + a <= s`;;

(* Lean: forward_profile *)
let C1092PCS_FORWARD_PROFILE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c977cc_normal c s /\
               c1092pcs_forwardCore c s u v a
               ==> c1092pcs_forwardFaces c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092pcs_forwardCore] THEN STRIP_TAC THEN
  C1092PCS_SETUP_TAC THEN
  C1092PCS_FACT_TAC `v + a <= s` `--(&1)` `&0` THEN
  SUBGOAL_THEN `--c - s <= u` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092PCS_FACT_TAC `s - c <= v` `--(&1)` `--(&1)` THEN C1092PCS_LP_TAC; ALL_TAC] THEN
  C1092PCS_FACT_TAC `(&2 / &5) * s - c <= v` `--(&2 / &5)` `--(&1)` THEN
  ASM_REWRITE_TAC[c1092pcs_forwardFaces]);;

(* Lean: half_width (private) *)
let C1092PCS_HALF_WIDTH = prove
 (`forall c s. c977cc_normal c s /\ C1092WPS_half c s <= &1 / &3 ==> s + c / &2 <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092PCS_SETUP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092PCS_LP_TAC; ALL_TAC] THEN
  UNDISCH_TAC `C1092WPS_half c s <= &1 / &3` THEN
  SPEC_TAC(`C1092WPS_half c s`,`q:real`) THEN GEN_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 - q) * (&1 - &3 * q)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN C1092PCS_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + q pow 2) * (&1 - s - c / &2) = (&1 - q) * (&1 - &3 * q) / &2`
  ASSUME_TAC THENL
  [UNDISCH_TAC `(&1 + q pow 2) * c = &1 - q pow 2` THEN
   UNDISCH_TAC `(&1 + q pow 2) * s = &2 * q` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (&1 + q pow 2) * --(&1 - s - c / &2)` MP_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN MP_TAC(SPEC `q:real` REAL_LE_POW_2) THEN
   C1092PCS_LP_TAC; ALL_TAC] THEN
  C1092PCS_LP_TAC);;

(* Lean: half_identity (private) *)
let C1092PCS_HALF_IDENTITY = prove
 (`forall c s. c977cc_normal c s ==> s * C1092WPS_half c s = &1 - c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  C1092PCS_SETUP_TAC THEN
  REWRITE_TAC[C1092WPS_half] THEN
  SUBGOAL_THEN `~(&1 + c = &0)` MP_TAC THENL [C1092PCS_LP_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_FIELD);;

(* Lean: crosspoint_of_forward *)
let C1092PCS_CROSSPOINT_OF_FORWARD = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c977cc_normal c s /\
               c1092pcs_forwardInputs c s u v a
               ==> linside c s u v a (--(&1 / &2)) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092PCS_FORWARD_PROFILE) THEN
  ASM_SIMP_TAC[C1092PCS_FORWARDINPUTS_CORE; c1092pcs_forwardFaces] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092PCS_HALF_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `c1092pcs_forwardInputs c s u v a` THEN
  REWRITE_TAC[c1092pcs_forwardInputs] THEN STRIP_TAC THEN
  C1092PCS_SETUP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092PCS_LP_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `s / &2 < v + a` ASSUME_TAC THENL
  [ASM_CASES_TAC `&1 / &10 <= C1092WPS_half c s` THENL
   [SUBGOAL_THEN `&0 <= s * (C1092WPS_half c s - &1 / &10)` MP_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN C1092PCS_LP_TAC; ALL_TAC] THEN
    UNDISCH_TAC `s * C1092WPS_half c s = &1 - c` THEN C1092PCS_LP_TAC;
    SUBGOAL_THEN `&0 <= (&1 / &10 - C1092WPS_half c s) * (&1 + c)` MP_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN C1092PCS_LP_TAC; ALL_TAC] THEN
    UNDISCH_TAC `C1092WPS_half c s * (&1 + c) = s` THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `s <= &1 / &5` ASSUME_TAC THENL [C1092PCS_LP_TAC; ALL_TAC] THEN
    C1092PCS_FACT_TAC `(&14 / &25) * s - c <= v` `--(&14 / &25)` `--(&1)` THEN
    C1092PCS_LP_TAC]; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN C1092PCS_LP_TAC);;

(* Lean: crosspoint_of_missing *)
let C1092PCS_CROSSPOINT_OF_MISSING = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c977cc_normal c s /\
               c1092mmpf_inputs c s u v a /\ C1092WPS_half c s <= &1 / &3
               ==> linside c s u v a (--(&1 / &2)) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092MMPF_PROFILE) THEN
  ASM_REWRITE_TAC[c1092mmpf_faces] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092PCS_HALF_WIDTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `c1092mmpf_inputs c s u v a` THEN
  REWRITE_TAC[c1092mmpf_inputs] THEN STRIP_TAC THEN
  C1092PCS_SETUP_TAC THEN
  REWRITE_TAC[linside] THEN C1092PCS_LP_TAC);;

(* Lean: halfpoint_of_next_crosspoint *)
let C1092PCS_HALFPOINT_OF_NEXT_CROSSPOINT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c977cc_normal c s /\
               &0 < s /\ c1092pcs_forwardCore c s u v a /\
               ~linside c s u v a (--(&7 / &20)) (&7 / &20) /\
               C1092WPS_half c s <= &1 / &3 /\
               ~linside c s u v a (&0) (--(&1 / &2))
               ==> u + a <= --s / &2 /\ ~linside c s u v a (&0) (--(&13 / &50)) /\
                   linside c s u v a (--(&1)) (--(&1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092PCS_FORWARD_PROFILE) THEN
  ASM_REWRITE_TAC[c1092pcs_forwardFaces] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092PCS_HALF_WIDTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `c1092pcs_forwardCore c s u v a` THEN
  REWRITE_TAC[c1092pcs_forwardCore] THEN STRIP_TAC THEN
  C1092PCS_SETUP_TAC THEN
  SUBGOAL_THEN `u + a <= --s / &2` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092PCS_FACT_TAC `--c / &2 <= v` `&0` `--(&1 / &2)` THEN C1092PCS_LP_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `v < s - c / &2` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&13 * s < &3 * c` ASSUME_TAC THENL [C1092PCS_LP_TAC; ALL_TAC] THEN
   C1092PCS_FACT_TAC `v + a <= (&7 / &20) * (c + s)` `--(&7 / &20)` `&7 / &20` THEN
   C1092PCS_LP_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [REWRITE_TAC[linside] THEN C1092PCS_LP_TAC;
   REWRITE_TAC[linside] THEN C1092PCS_LP_TAC]);;
