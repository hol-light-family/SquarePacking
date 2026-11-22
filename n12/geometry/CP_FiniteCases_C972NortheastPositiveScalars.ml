(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C972NortheastPositiveScalars.lean  *)
(* (namespace N12Compact.FiniteCases.C972Local.NortheastPositiveScalars).   *)
(* Margins for the two remaining transverse axes in C972.  Normal /         *)
(* normal_bounds: c977cc_normal / C977CC_NORMAL_BOUNDS; UnitCircleChord.    *)
(* cosine_order / increasing: CCUCC_COSINE_ORDER / CCUCC_INCREASING;        *)
(* SharpPointScalars.arc: OCSPS_ARC.                                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;
needs "n12/geometry/CP_OtherCases_SharpPointScalars.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C972NPS_NORMAL_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `c977cc_normal x y`) (concl th) then
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th)
    else NO_TAC));;

(* Lean: relative_order *)
let C972NPS_RELATIVE_ORDER = prove
 (`forall c s d r. c977cc_normal c s /\ c977cc_normal d r /\ c * r <= s * d
             ==> r <= s /\ c <= d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C972NPS_NORMAL_TAC THEN
  SUBGOAL_THEN `r <= s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `r:real`] CCUCC_COSINE_ORDER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `&0 < c * (r - s) /\ &0 <= s * (c - d)` MP_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `c * r <= s * d` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`d:real`; `r:real`; `c:real`; `s:real`] CCUCC_COSINE_ORDER) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: alpha_lower *)
let C972NPS_ALPHA_LOWER = prove
 (`forall c s d r. c977cc_normal c s /\ c977cc_normal d r /\ s <= r
             ==> d <= c * d + s * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C972NPS_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 - d) * (&1 - c) /\ &0 <= s * (r - s) /\ &0 <= c * (&1 - c)`
    MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN REAL_ARITH_TAC);;

(* Lean: right_projection *)
let C972NPS_RIGHT_PROJECTION = prove
 (`forall d r. c977cc_normal d r ==> &293 / &500 * d + d * r < &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C972NPS_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `d <= &1 - r * r / &2` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `d - &1`]; ALL_TAC] THEN
  NLIN_TAC [SQ_NONNEG `d - &5 / &4 * r`; SQ_NONNEG `r:real`]);;

(* Lean: P *)
let c972nps_p = new_definition
 `c972nps_p (c:real) (s:real) = &673 / &500 - c + &6 / &25 * c pow 2`;;
(* Lean: Q *)
let c972nps_q = new_definition
 `c972nps_q (c:real) (s:real) = &1 - s + &6 / &25 * c * s`;;

(* Lean: north_axis_shallower *)
let C972NPS_NORTH_AXIS_SHALLOWER = prove
 (`forall c s d r. c977cc_normal c s /\ c977cc_normal d r /\
             &4 / &5 < c /\ s < &1 / &2 /\ r <= s
             ==> &0 < &1 - d * c972nps_p c s - r * c972nps_q c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C972NPS_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= c * s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c972nps_p c s /\ &0 <= c972nps_q c s /\
                &0 <= c972nps_q c s * c - c972nps_p c s * s` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c972nps_p; c972nps_q] THEN
    MP_TAC(SPEC `c:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `r:real`;
                `c972nps_p c s`; `c972nps_q c s`] CCUCC_INCREASING) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `c972nps_p c s * c + c972nps_q c s * s = &793 / &500 * c + s - &1`
    ASSUME_TAC THENL
   [REWRITE_TAC[c972nps_p; c972nps_q] THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&793 / &500 * c + s < &2` ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
    DISCH_TAC THEN
    NLIN_TAC [SQ_NONNEG `c - &793 / &500 * s`; SQ_NONNEG `&793 / &500 * c + s - &2`];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: Aplus *)
let c972nps_aplus = new_definition
 `c972nps_aplus (d:real) r = &793 / &500 - d - &92 / &125 * r pow 2 + &7 / &20 * d * r`;;
(* Lean: Bplus *)
let c972nps_bplus = new_definition
 `c972nps_bplus (d:real) r = &13 / &20 - r + &7 / &20 * r pow 2 + &92 / &125 * d * r`;;

(* Lean: source_axis_steeper *)
let C972NPS_SOURCE_AXIS_STEEPER = prove
 (`forall c s d r. c977cc_normal c s /\ c977cc_normal d r
             ==> &0 < &1 - c * c972nps_aplus d r - s * c972nps_bplus d r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C972NPS_NORMAL_TAC THEN
  SUBGOAL_THEN `r <= &5 / &7` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 - d <= &3 / &5 * r pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (&1 - d) * (d - &2 / &3)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `d pow 2 + r pow 2 = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c972nps_aplus d r <= &18 / &25` ASSUME_TAC THENL
   [REWRITE_TAC[c972nps_aplus] THEN
    MP_TAC(SPEC `d - &7 / &5 * r` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `r:real` REAL_LE_POW_2) THEN
    UNDISCH_TAC `&1 - d <= &3 / &5 * r pow 2` THEN
    UNDISCH_TAC `d pow 2 + r pow 2 = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c972nps_bplus d r <= &13 / &20` ASSUME_TAC THENL
   [REWRITE_TAC[c972nps_bplus] THEN
    SUBGOAL_THEN `&0 <= r * (&1 - (&7 / &20 * r + &92 / &125 * d))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&18 / &25 * c + &13 / &20 * s < &1` ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
    DISCH_TAC THEN
    NLIN_TAC [SQ_NONNEG `&13 / &20 * c - &18 / &25 * s`;
              SQ_NONNEG `&18 / &25 * c + &13 / &20 * s - &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c * (&18 / &25 - c972nps_aplus d r) /\
                &0 <= s * (&13 / &20 - c972nps_bplus d r)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&18 / &25 * c + &13 / &20 * s < &1` THEN REAL_ARITH_TAC);;

(* Lean: Aminus *)
let c972nps_aminus = new_definition
 `c972nps_aminus (d:real) r = &793 / &500 - d + r - &413 / &500 * r pow 2`;;
(* Lean: Bminus *)
let c972nps_bminus = new_definition
 `c972nps_bminus (d:real) r = &1 - d - r + &413 / &500 * d * r`;;

(* Lean: source_axis_shallower *)
let C972NPS_SOURCE_AXIS_SHALLOWER = prove
 (`forall c s d r. c977cc_normal c s /\ c977cc_normal d r /\ &0 < r /\ c <= d
             ==> &0 < &1 - c * c972nps_aminus d r - s * c972nps_bminus d r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C972NPS_NORMAL_TAC THEN
  SUBGOAL_THEN `r <= &5 / &7` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c972nps_aminus d r` ASSUME_TAC THENL
   [REWRITE_TAC[c972nps_aminus] THEN
    SUBGOAL_THEN `&0 <= r * (&1 - &413 / &500 * r)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `d <= &1` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `r:real`] OCSPS_ARC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `c972nps_bminus d r <= &0` ASSUME_TAC THENL
   [REWRITE_TAC[c972nps_bminus] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d * c972nps_aminus d r < &1` ASSUME_TAC THENL
   [REWRITE_TAC[c972nps_aminus] THEN
    SUBGOAL_THEN `d <= &1 - r pow 2 / &2` ASSUME_TAC THENL
     [MP_TAC(SPEC `d - &1` REAL_LE_POW_2) THEN
      UNDISCH_TAC `d pow 2 + r pow 2 = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= r pow 2 * (d - &7 / &10)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
      let t = concl th in
      not(can (find_term (fun x -> x = `c:real` || x = `s:real`)) t) &&
      not(can (find_term (fun x -> is_const x && fst(dest_const x) = "c977cc_normal")) t)))) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[REAL_POW_2] THEN REPEAT STRIP_TAC THEN
    NLIN_TAC [SQ_NONNEG `d - &5 / &4 * r`; SQ_NONNEG `r:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (d - c) * c972nps_aminus d r /\
                &0 <= s * --c972nps_bminus d r` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `d * c972nps_aminus d r < &1` THEN REAL_ARITH_TAC);;
