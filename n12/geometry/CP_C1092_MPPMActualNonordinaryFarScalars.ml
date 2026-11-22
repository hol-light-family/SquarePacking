(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualNonordinaryFarScalars.lean     *)
(* (N12Compact.C1092MPPMActualNonordinary).  The two endpoint margins of     *)
(* ELBOW-EXCLUSION sections 2.4-2.5.  CanonicalProjection.before / after are *)
(* CCCP_BEFORE / CCCP_AFTER; Normal is c977cc_normal.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMActualNonordinaryScalars.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;

let C1092MANF_LIN = NLIN_TAC ~deg2:false [];;

let C1092MANF_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092MANF_LIN; ALL_TAC];;

let C1092MANF_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C1092MANF_LIN; ALL_TAC];;

let C1092MANF_CONTRA = ONCE_REWRITE_TAC[GSYM REAL_NOT_LT; GSYM REAL_NOT_LE] THEN DISCH_TAC;;

let C1092MANF_NORMALS_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal; REAL_POW_2] th)) ns);;

(* Lean: half_form (private) *)
let C1092MANF_HALF_FORM = prove
 (`forall c s. c977cc_normal c s /\ &0 < c
         ==> c = (&1 - (s / (&1 + c)) pow 2) / (&1 + (s / (&1 + c)) pow 2) /\
             s = (&2 * (s / (&1 + c))) / (&1 + (s / (&1 + c)) pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MPIH_HALF_IDENTITIES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c977cc_normal c s` THEN SIMP_TAC[c977cc_normal];
    ALL_TAC] THEN
  REWRITE_TAC[C1092WPS_half] THEN
  SPEC_TAC(`s / (&1 + c)`,`z:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + z pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN
  MAP_EVERY UNDISCH_TAC [`z * (&1 + c) = s`; `s * z = &1 - c`] THEN CONV_TAC REAL_RING);;

(* 0 < lhs(c,s) via the half-angle z = s/(1+c): lhs = num(z) / den(z) *)
let C1092MANF_ENDPOINT_TAC ex num den prods =
  SUBGOAL_THEN (mk_comb(mk_comb(`(<):real->real->bool`, `&0`), ex)) ASSUME_TAC THENL
   [MP_TAC(SPECL [`c:real`; `s:real`] C1092MANF_HALF_FORM) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < s / (&1 + c)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `s / (&1 + c) < &7 / &50` THEN
    SPEC_TAC(`s / (&1 + c)`,`z:real`) THEN GEN_TAC THEN
    DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `&0 < &1 + z pow 2` ASSUME_TAC THENL
     [MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN (mk_eq(ex, mk_comb(mk_comb(`(/):real->real->real`, num), den))) SUBST1_TAC
    THENL
     [FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `c:real`)) THEN
      FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `s:real`)) THEN
      UNDISCH_TAC `&0 < &1 + z pow 2` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_2; REAL_ARITH `z pow 3 = z * z * z`;
                  REAL_ARITH `z pow 4 = (z * z) * (z * z)`] THEN
      MAP_EVERY C1092MANF_PROD prods THEN C1092MANF_LIN;
      MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]];
    ALL_TAC];;

(* Lean: far_angle *)
let C1092MANF_FAR_ANGLE = prove
 (`forall d t. c977cc_normal d t /\ &1 < t + (&263 / &500) * d
         ==> &60 * d < &91 * t /\ d < &91 / &109`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&60 * d < &91 * t` ASSUME_TAC THENL
   [C1092MANF_CONTRA THEN
    UNDISCH_TAC `c977cc_normal d t` THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`d:real`; `t:real`; `&91 / &109`; `&60 / &109`; `&263 / &500`; `&1`]
      CCCP_BEFORE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN C1092MANF_NORMALS_TAC THEN
  C1092MANF_PROD `&0 < (&91 * t - &60 * d) * (&91 * t + &60 * d)` THEN
  C1092MANF_CONTRA THEN
  C1092MANF_PROD `&0 <= (d - &91 / &109) * (d + &91 / &109)` THEN
  C1092MANF_LIN);;

(* Lean: far_source_transverse *)
let C1092MANF_FAR_SOURCE_TRANSVERSE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\
             &24 / &25 < c /\ &0 < s /\ s < &7 / &25 /\ c + s < &31 / &25 /\
             d <= &91 / &109
             ==> &0 < &1 - (&7 / &20) * (c + s) + (c * d - s * t) * (&1 - (&543 / &500) * d) +
                      (c * t + s * d) * (&1 - d - t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092MANS_RELATIVE_BOUNDS) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MANS_NORMAL_SUM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  C1092MANF_PROD `&0 <= (c * d - s * t) * (&1 - (&543 / &500) * d)` THEN
  C1092MANF_PROD `&0 <= (&1 - (c * t + s * d)) * (d + t - &1)` THEN
  C1092MANF_LIN);;

(* Lean: far_transverse_segment *)
let C1092MANF_FAR_TRANSVERSE_SEGMENT = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\
             &24 / &25 < c /\ &0 < s /\ s < &7 / &25 /\ c + s < &31 / &25 /\
             s / (&1 + c) < &7 / &50 /\ &60 * d <= &91 * t
             ==> &0 < &1 - d - t + (c * d - s * t) * (&1 - c - (&2 / &5) * s) +
                      (c * t + s * d) * (&1 - (&543 / &500) * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MANF_ENDPOINT_TAC
   `&1 - (&2 - c - s + (&43 / &500) * s pow 2 + (&2 / &5) * c * s) * (&91 / &109) -
         (&1 - c + s + (&43 / &500) * c * s - (&2 / &5) * s pow 2) * (&60 / &109)`
   `(&10 * z + &3) * (&750 - &3380 * z + &2879 * z pow 2 - &3550 * z pow 3)`
   `&13625 * (&1 + z pow 2) pow 2`
   [`&0 <= (z * z) * (&2879 - &3550 * z)`; `&0 < &10 * z + &3`;
    `&0 < (&10 * z + &3) * (&750 - &3380 * z + &2879 * (z * z) - &3550 * (z * z * z))`] THEN
  C1092MANF_NORMALS_TAC THEN
  C1092MANF_PROD `&0 <= c * s` THEN C1092MANF_PROD `&0 <= s * s` THEN
  C1092MANF_PROD `&0 < s * (&1 - (&2 / &5) * s)` THEN
  C1092MANF_PROD `&0 <= (&1 - c) * s` THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `&91 / &109`; `&60 / &109`;
                `&2 - c - s + (&43 / &500) * s * s + (&2 / &5) * c * s`;
                `&1 - c + s + (&43 / &500) * c * s - (&2 / &5) * s * s`] CCCP_AFTER) THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[REAL_POW_2] THEN
    REPEAT CONJ_TAC THEN C1092MANF_LIN; DISCH_TAC] THEN
  SUBGOAL_THEN
   `&1 - d - t + (c * d - s * t) * (&1 - c - (&2 / &5) * s) +
    (c * t + s * d) * (&1 - (&543 / &500) * s) =
    &1 - (&2 - c - s + (&43 / &500) * s * s + (&2 / &5) * c * s) * d -
         (&1 - c + s + (&43 / &500) * c * s - (&2 / &5) * s * s) * t` SUBST1_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092MANF_LIN);;

(* Lean: far_oblique_segment *)
let C1092MANF_FAR_OBLIQUE_SEGMENT = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\
             &24 / &25 < c /\ &0 < s /\ s < &7 / &25 /\
             s / (&1 + c) < &7 / &50 /\ &60 * d <= &91 * t
             ==> &0 < ((&13 / &50) * s + (&43 / &500) * c) *
                      (&1 - d - t - (&13 / &50) * s * (c * d - s * t)) +
                      (c * t + s * d) * (((&13 / &50) * s + (&43 / &500) * c) +
                        ((&13 / &50) * c - (&43 / &500) * s) +
                        (&13 / &50) * s * ((&13 / &50) * c - (&43 / &500) * s) - &7059 / &25000)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MANF_ENDPOINT_TAC
   `((&13 / &50) * s + (&43 / &500) * c) -
    ((&43 / &500) * c + (&7059 / &12500) * s - (&173 / &500) * c * s - (&87 / &500) * s pow 2) *
      (&91 / &109) -
    ((&9209 / &25000) * c - &173 / &500 + (&481 / &2500) * s - (&87 / &500) * c * s +
     (&173 / &500) * s pow 2) * (&60 / &109)`
   `&129105 * z pow 4 - &478247 * z pow 3 + &68175 * z pow 2 + &45828 * z + &645`
   `&340625 * (&1 + z pow 2) pow 2`
   [`&0 <= (z * z) * (&68175 - &478247 * z)`; `&0 <= (z * z) * (z * z)`] THEN
  C1092MANF_NORMALS_TAC THEN
  C1092MANF_PROD `&0 <= (&1 - c) * s` THEN
  C1092MANF_PROD `&0 <= (&7 / &25 - s) * s` THEN
  C1092MANF_PROD `&0 <= s * s` THEN
  MP_TAC(SPEC `&1 - c` REAL_LE_SQUARE) THEN DISCH_TAC THEN
  C1092MANF_FACT `c <= &1 - s * s / &2` THEN
  C1092MANF_PROD `&0 <= (c - &24 / &25) * s` THEN
  C1092MANF_PROD `&0 <= (&7 / &25 - s) * (&7 / &25 + s)` THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `&91 / &109`; `&60 / &109`;
                `(&43 / &500) * c + (&7059 / &12500) * s - (&173 / &500) * c * s -
                 (&87 / &500) * s * s`;
                `(&9209 / &25000) * c - &173 / &500 + (&481 / &2500) * s -
                 (&87 / &500) * c * s + (&173 / &500) * s * s`] CCCP_AFTER) THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[REAL_POW_2] THEN
    REPEAT CONJ_TAC THEN C1092MANF_LIN; DISCH_TAC] THEN
  SUBGOAL_THEN
   `((&13 / &50) * s + (&43 / &500) * c) * (&1 - d - t - (&13 / &50) * s * (c * d - s * t)) +
    (c * t + s * d) * (((&13 / &50) * s + (&43 / &500) * c) +
      ((&13 / &50) * c - (&43 / &500) * s) +
      (&13 / &50) * s * ((&13 / &50) * c - (&43 / &500) * s) - &7059 / &25000) =
    ((&13 / &50) * s + (&43 / &500) * c) -
    ((&43 / &500) * c + (&7059 / &12500) * s - (&173 / &500) * c * s - (&87 / &500) * s * s) * d -
    ((&9209 / &25000) * c - &173 / &500 + (&481 / &2500) * s - (&87 / &500) * c * s +
     (&173 / &500) * s * s) * t` SUBST1_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092MANF_LIN);;
