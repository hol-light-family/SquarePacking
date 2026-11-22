(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/PositiveInwardHalfangle.lean         *)
(* (namespace N12Compact.C1092MMMPPositiveInwardHalfangle).                  *)
(* half: C1092WPS_half; Normal: c977cc_normal; short_projections:            *)
(* WFP_SHORT_PROJECTIONS.                                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let C1092MPIH_LIN_TAC (asl,w as g) =
  let rec ok t = is_real_rel t || (is_neg t && is_real_rel (rand t)) ||
                 (is_conj t && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

let C1092MPIH_MISS_TAC x y =
  UNDISCH_TAC (mk_neg(list_mk_comb(`linside c s u v a`,[x;y]))) THEN
  REWRITE_TAC[linside; DE_MORGAN_THM; REAL_NOT_LT] THEN C1092MPIH_LIN_TAC;;

let C1092MPIH_FACT_TAC t x y =
  SUBGOAL_THEN t ASSUME_TAC THENL [C1092MPIH_MISS_TAC x y; ALL_TAC];;

let C1092MPIH_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     REPEAT CONJ_TAC THEN C1092MPIH_LIN_TAC; ALL_TAC]) tms;;

(* Lean: half_identities *)
let C1092MPIH_HALF_IDENTITIES = prove
 (`forall c s. &0 < c /\ c pow 2 + s pow 2 = &1
         ==> C1092WPS_half c s * (&1 + c) = s /\ s * C1092WPS_half c s = &1 - c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C1092WPS_half] THEN
  SUBGOAL_THEN `~(&1 + c = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_FIELD);;

let C1092MPIH_PREP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) || is_forall(concl th) then th
                           else REWRITE_RULE[linside] th);;

(* Lean: entrance *)
let C1092MPIH_ENTRANCE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ c977cc_normal c s /\
     linside c s u v a (&7 / &20) (&7 / &20) /\
     linside c s u v a (&0) (&13 / &50) /\
     linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&0) (&0) /\
     ~linside c s u v a (&2 / &5) (&1) /\
     ~linside c s u v a (&1) (&13 / &50)
     ==> &0 <= u /\ &0 < s /\ v + a <= c - (&2 / &5) * s /\
         &0 < C1092WPS_half c s /\ C1092WPS_half c s < &13 / &50 /\
         &2331 / &2669 < c /\ s < &1300 / &2669`,
  C1092MPIH_PREP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MPIH_HALF_IDENTITIES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C1092WPS_half c s <=> &0 < s` MP_TAC THENL
   [REWRITE_TAC[C1092WPS_half] THEN
    SUBGOAL_THEN `&0 < &1 + c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO]; ALL_TAC] THEN
  SPEC_TAC(`C1092WPS_half c s`,`z:real`) THEN GEN_TAC THEN
  DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`c:real`; `s:real`; `&37 / &50`; `&3 / &5`] WFP_SHORT_PROJECTIONS)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092MPIH_FACT_TAC `&0 <= u` `&0` `&0` THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [C1092MPIH_LIN_TAC; ALL_TAC] THEN
  C1092MPIH_PROD_TAC [`&0 <= (c - s) * ((&41 / &50) * c + (&1 / &50) * s)`] THEN
  SUBGOAL_THEN `(&2 / &5) * c + s < &1` ASSUME_TAC THENL
   [NLIN_FACTS_TAC [] [`((&2 / &5) * c + s) * ((&2 / &5) * c + s) <= &49 / &50`] THEN
    NLIN_TAC [SQ_NONNEG `(&2 / &5) * c + s - &1`]; ALL_TAC] THEN
  C1092MPIH_FACT_TAC `v + a <= c - (&2 / &5) * s` `&2 / &5` `&1` THEN
  SUBGOAL_THEN `z < &13 / &50` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MPIH_PROD_TAC [`&0 <= s * (z - &13 / &50)`] THEN
    C1092MPIH_MISS_TAC `&1` `&13 / &50`; ALL_TAC] THEN
  C1092MPIH_PROD_TAC [`&0 < (&13 / &50 - z) * (&1 + c)`] THEN
  SUBGOAL_THEN `&2331 / &2669 < c` ASSUME_TAC THENL
   [C1092MPIH_PROD_TAC [`&0 < (&13 * (&1 + c) - &50 * s) * (&13 * (&1 + c) + &50 * s)`] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MPIH_PROD_TAC [`&0 <= (&1 + c) * (&2331 - &2669 * c)`] THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  C1092MPIH_PROD_TAC [`&0 < (c - &2331 / &2669) * (c + &2331 / &2669)`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092MPIH_PROD_TAC [`&0 <= (s - &1300 / &2669) * (s + &1300 / &2669)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: point *)
let C1092MPIH_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ c977cc_normal c s /\
     linside c s u v a (&7 / &20) (&7 / &20) /\
     linside c s u v a (&0) (&13 / &50) /\
     linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&0) (&0) /\
     ~linside c s u v a (&2 / &5) (&1) /\
     ~linside c s u v a (&1 / &2) (&1) /\
     ~linside c s u v a (&1) (&13 / &50)
     ==> linside c s u v a (&1) (C1092WPS_half c s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092MPIH_ENTRANCE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MPIH_HALF_IDENTITIES) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`C1092WPS_half c s`,`z:real`) THEN GEN_TAC THEN
  REPEAT(DISCH_THEN(fun th -> if is_conj(concl th) then
          CONJUNCTS_THEN ASSUME_TAC th else ASSUME_TAC th)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && not(is_neg(concl th))
          then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th) THEN
  C1092MPIH_FACT_TAC `v + a <= c - s / &2` `&1 / &2` `&1` THEN
  SUBGOAL_THEN `z * c = s - z /\ s * z * z = &2 * z - s` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [C1092MPIH_LIN_TAC; ALL_TAC] THEN
    UNDISCH_TAC `z * (&1 + c) = s` THEN UNDISCH_TAC `s * z = &1 - c` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092MPIH_PROD_TAC [`&0 < s * z`] THEN
  C1092MPIH_PROD_TAC [`&0 < (s * z) * (&1 - z / &2)`] THEN
  REWRITE_TAC[linside] THEN C1092MPIH_LIN_TAC);;

(* Lean: small_angle_of_bar *)
let C1092MPIH_SMALL_ANGLE_OF_BAR = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ c977cc_normal c s /\
     linside c s u v a (&7 / &20) (&7 / &20) /\
     linside c s u v a (&0) (&13 / &50) /\
     linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&0) (&0) /\
     ~linside c s u v a (&2 / &5) (&1) /\
     (forall y. &0 <= y /\ y <= &2 / &5 ==> ~linside c s u v a (&1) y)
     ==> s + (&2 / &5) * c < &3 / &5 /\ s < &21 / &100 /\ &97 / &100 < c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092MPIH_ENTRANCE) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MPIH_HALF_IDENTITIES) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`C1092WPS_half c s`,`z:real`) THEN GEN_TAC THEN
  REPEAT(DISCH_THEN(fun th -> if is_conj(concl th) then
          CONJUNCTS_THEN ASSUME_TAC th else ASSUME_TAC th)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && not(is_neg(concl th))
          then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) || is_forall(concl th) then th
                           else REWRITE_RULE[linside] th) THEN
  SUBGOAL_THEN `z * c = s - z` ASSUME_TAC THENL [C1092MPIH_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s + (&2 / &5) * c < &3 / &5` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MPIH_PROD_TAC [`&0 <= z * ((s + (&2 / &5) * c) - &3 / &5)`] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real` o check (is_forall o concl)) THEN
    REWRITE_TAC[linside] THEN C1092MPIH_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s < &21 / &100` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MPIH_PROD_TAC [`&0 <= (s - &21 / &100) * (&3 / &5 - s)`;
      `&0 < (&3 / &2 - (&5 / &2) * s - c) * (&3 / &2 - (&5 / &2) * s + c)`] THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  C1092MPIH_PROD_TAC [`&0 < (&21 / &100 - s) * (&21 / &100 + s)`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092MPIH_PROD_TAC [`&0 <= (&97 / &100 - c) * (&97 / &100 + c)`] THEN
  NLIN_TAC ~deg2:false []);;
