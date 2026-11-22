(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/InwardOuterArmHalfpoint.lean        *)
(* (N12Compact.C1092MMMPInwardOuterArmHalfpoint; Lean header: "compiler      *)
(* acceptance has not been tested").  INWARD-OUTER-ARM-HALFPOINT Theorem 1   *)
(* and Corollary 2.  Conventions of CP_C1092_MMMP_BottomOrigin.ml (forward   *)
(* toolkit c1092mo_; the chart (pullSwap (pullY q)).translated 2 2 is        *)
(* c1092mss_chart q, C1092MSS_INSIDE_CHART).  An OpenSquare C is c s u v a   *)
(* with its invariants as hypotheses.  CommonCases.CanonicalScalars.bounds   *)
(* CCCS_BOUNDS; quarter_data C1092WPS_QUARTER_DATA; half_identities          *)
(* C1092MPIH_HALF_IDENTITIES; short_projections WFP_SHORT_PROJECTIONS;       *)
(* canonical_frame CLF_CANONICAL_FRAME; z = half c s is the term             *)
(* C1092WPS_half c s.  Tag C1092MIOA_.                                       *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_BottomOrigin.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

let C1092MIOA_LIN = NLIN_TAC ~deg2:false [];;
let C1092MIOA_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside; TAUT `~p ==> false <=> p`] THEN
  REPEAT CONJ_TAC THEN C1092MIOA_LIN;;
let C1092MIOA_UNFOLD_TAC =
  RULE_ASSUM_TAC(fun th -> let t = concl th in
    if is_comb t && fst (strip_comb t) = `linside` then REWRITE_RULE[linside] th else th);;

(* Lean: negative_impossible (private) *)
let C1092MIOA_NEGATIVE_IMPOSSIBLE = prove
 (`forall c s0 u v a s.
     c * c + s0 * s0 = &1 /\ &0 < a /\ s0 = --s /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s0 u v a (&7 / &20) (&7 / &20) /\ linside c s0 u v a (&0) (&13 / &50) /\
     linside c s0 u v a (&13 / &50) (&0) /\ linside c s0 u v a (&2 / &5) (&1) /\
     ~linside c s0 u v a (&13 / &50) (&1) /\ ~linside c s0 u v a (&1) (&2 / &5)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s0:real = --s`)) THEN
  MP_TAC(SPECL [`c:real`; `--s`; `&37 / &50`; `--(&3 / &5)`] WFP_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC] THEN
  C1092MIOA_UNFOLD_TAC THEN
  SUBGOAL_THEN `&13 / &50 * c - s <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MIOA_MISS_TAC `~linside c (--s) u v a (&13 / &50) (&1)`; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c - &2 / &5 * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MIOA_MISS_TAC `~linside c (--s) u v a (&1) (&2 / &5)`; ALL_TAC] THEN
  C1092MIOA_LIN);;

let C1092MIOA_Z = `C1092WPS_half c s`;;
let c1092mioa_z str = vsubst [C1092MIOA_Z, `Z:real`] (parse_term str);;

(* Lean: positive_point (private) *)
let C1092MIOA_POSITIVE_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&7 / &20) (&7 / &20) /\ linside c s u v a (&0) (&13 / &50) /\
     linside c s u v a (&13 / &50) (&0) /\ linside c s u v a (&2 / &5) (&1) /\
     ~linside c s u v a (&0) (&0) /\ ~linside c s u v a (&13 / &50) (&1) /\
     (forall y. &13 / &50 <= y ==> y <= &2 / &5 ==> ~linside c s u v a (&1) y)
     ==> linside c s u v a (&1 / &2) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MIOA_UNFOLD_TAC THEN
  SUBGOAL_THEN `&0 <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MIOA_MISS_TAC `~linside c s u v a (&0) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [C1092MIOA_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= c - &13 / &50 * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MIOA_MISS_TAC `~linside c s u v a (&13 / &50) (&1)`; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `u + a <= c / &2 + s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MIOA_MISS_TAC `~linside c s u v a (&1 / &2) (&1)`; ALL_TAC] THEN
  SUBGOAL_THEN `&1 < c / &2 + s` ASSUME_TAC THENL [C1092MIOA_LIN; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MPIH_HALF_IDENTITIES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; STRIP_TAC] THEN
  SUBGOAL_THEN (c1092mioa_z "&0 < Z") ASSUME_TAC THENL
   [REWRITE_TAC[C1092WPS_half] THEN MATCH_MP_TAC REAL_LT_DIV THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (c1092mioa_z "Z < &1") ASSUME_TAC THENL
   [REWRITE_TAC[C1092WPS_half] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < c ==> &0 < &1 + c`] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  (* large *)
  SUBGOAL_THEN (c1092mioa_z "&1 / &3 < Z") ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN (c1092mioa_z "&0 < (&1 + Z pow 2) * (c / &2 + s - &1)") ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [MP_TAC(SPEC C1092MIOA_Z REAL_LE_POW_2) THEN REAL_ARITH_TAC; RASM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN (c1092mioa_z "&0 <= (&1 - Z) * (&1 - &3 * Z)") ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    C1092MIOA_LIN;
    ALL_TAC] THEN
  (* sLarge *)
  SUBGOAL_THEN `&1 + c < &3 * s` ASSUME_TAC THENL
   [SUBGOAL_THEN (c1092mioa_z "&0 < (Z - &1 / &3) * (&1 + c)") ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    C1092MIOA_LIN;
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 / &5 < s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (&4 / &5 - c) * (&4 / &5 + c)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&3 / &5 - s) * (&3 / &5 + s)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    C1092MIOA_LIN;
    ALL_TAC] THEN
  SUBGOAL_THEN (c1092mioa_z "&0 < Z * (s + &13 / &50 * c - &37 / &50)") ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  (* the strict point (1, z) *)
  SUBGOAL_THEN (c1092mioa_z "linside c s u v a (&1) Z") ASSUME_TAC THENL
   [REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C1092MIOA_LIN; ALL_TAC] THEN
  ASM_CASES_TAC (c1092mioa_z "Z <= &2 / &5") THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC C1092MIOA_Z o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&3 / &5`; `&37 / &50`] WFP_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC] THEN
  SUBGOAL_THEN (c1092mioa_z "&0 < s * (Z - &2 / &5)") ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `linside c s u v a (&1) (&2 / &5)` ASSUME_TAC THENL
   [REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C1092MIOA_LIN; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&2 / &5` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: point *)
let C1092MIOA_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&7 / &20) (&7 / &20) /\ linside c s u v a (&0) (&13 / &50) /\
     linside c s u v a (&13 / &50) (&0) /\ linside c s u v a (&2 / &5) (&1) /\
     ~linside c s u v a (&0) (&0) /\ ~linside c s u v a (&13 / &50) (&1) /\
     (forall y. &13 / &50 <= y ==> y <= &2 / &5 ==> ~linside c s u v a (&1) y)
     ==> linside c s u v a (&1 / &2) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (find_term ((=) `lclosed`)) (concl th))) THEN
  FIRST_X_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) `u':real`)) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a':real = a`)) THEN
  ASM_CASES_TAC `&0 <= s'` THENL
   [MATCH_MP_TAC C1092MIOA_POSITIVE_POINT THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs s' <= c'` THEN UNDISCH_TAC `&0 <= s'` THEN REAL_ARITH_TAC;
    MATCH_MP_TAC(TAUT `false ==> p`) THEN
    MATCH_MP_TAC (SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a:real`; `--s':real`]
      C1092MIOA_NEGATIVE_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN
    FIRST_ASSUM(MP_TAC o SPEC `&2 / &5` o check (is_forall o concl)) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs s' <= c'` THEN UNDISCH_TAC `~(&0 <= s')` THEN REAL_ARITH_TAC]);;

let C1092MIOA_OUTER = c1092mmpe_in 5 "&3" "&8 / &5";;

(* Lean: halfpoint_of_outer *)
let C1092MIOA_HALFPOINT_OF_OUTER = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s /\\ %s ==> %s" C1092AE_P C1092AE_HYP C1092MMPE_CTX
    C1092MSS_NEAR C1092MIOA_OUTER (c1092mmpe_in 5 "&3" "&3 / &2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MSS_INWARD_PAIR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC C1092MO_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
  let o5 = c1092mo_own 5 in
  let tC = c1092mss_chart o5 in
  let bottom = c1092mo_use C1092MBP_PAIR in
  let hy = `&13 / &50 <= y` and hu = `y <= &2 / &5` in
  let foreign = MATCH_MP OO_HORIZONTAL_SEGMENT (end_itlist CONJ
    [CONJUNCT2 bottom; CONJUNCT1 bottom; REAL_ARITH `&113 / &50 < &12 / &5`;
     MP (REAL_ARITH (mk_imp(hy, `&113 / &50 <= &2 + y`))) (ASSUME hy);
     MP (REAL_ARITH (mk_imp(hu, `&2 + y <= &12 / &5`))) (ASSUME hu)]) in
  let bar = GEN `y:real` (DISCH hy (DISCH hu (c1092mo_excl 5 9 foreign))) in
  MP_TAC(SPECL tC C1092MIOA_POINT) THEN
  REWRITE_TAC[C1092MSS_INSIDE_CHART] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[REAL_ARITH `&2 - &1 = &1`] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MATCH_MP C1092MSS_CHART_UNIT (c1092mo_unit 5); c1092mo_pos (); c1092mo_side ();
      c1092mo_seed 5 (`&47 / &20`, `&33 / &20`);
      c1092mo_excl 5 7 (c1092mo_use C1092MPC_NORTHWEST_CENTER);
      c1092mo_excl 5 10 (ASSUME (c1092mo_in 10 `&3` `&87 / &50`))] THEN
    ACCEPT_TAC bar;
    SIMP_TAC[]]);;

(* Lean: bottom_origin_of_outer *)
let C1092MIOA_BOTTOM_ORIGIN_OF_OUTER = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s /\\ %s ==> %s" C1092AE_P C1092AE_HYP C1092MMPE_CTX
    C1092MSS_NEAR C1092MIOA_OUTER C1092MBO_ORIGIN),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092MIOA_HALFPOINT_OF_OUTER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092MBOE_CORNER_HALFPOINT) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC C1092MO_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
  ACCEPT_TAC(c1092mo_excl 1 5 (ASSUME (c1092mo_in 5 `&3` `&3 / &2`))));;

(* Lean: bottom_origin_of_near *)
let C1092MIOA_BOTTOM_ORIGIN_OF_NEAR = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> %s" C1092AE_P C1092AE_HYP C1092MMPE_CTX
    C1092MSS_NEAR C1092MBO_ORIGIN),
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC (parse_term C1092MIOA_OUTER) THENL
   [MATCH_MP_TAC C1092MIOA_BOTTOM_ORIGIN_OF_OUTER; MATCH_MP_TAC C1092MBO_POINT_OF_NEAR] THEN
  ASM_REWRITE_TAC[]);;
