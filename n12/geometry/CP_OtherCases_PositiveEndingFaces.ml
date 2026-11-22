(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/PositiveEndingFaces.lean            *)
(* (namespace N12Compact.Completion.OtherCases.PositiveEndingFaces).  True  *)
(* full faces and a strictly owned point for the positive southeast owner.  *)
(* half / quarter_data: C1092WPS_half / C1092WPS_QUARTER_DATA;              *)
(* BottomBarSupport.positive: CCBBS_POSITIVE; CanonicalScalars.bounds:      *)
(* CCCS_BOUNDS.  Square E is c s u v a.                                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_BottomBarSupport.ml";;
needs "n12/geometry/CP_OtherCases_PositiveEndingScalars.ml";;

(* Lean: Data (structure) *)
let ocpef_data = new_definition
 `ocpef_data (c:real) s u v a <=>
    &113 / &125 < c /\ c <= &1 /\ &0 < s /\ s < &43 / &100 /\ s <= c /\ &1 < a /\
    u + a <= c /\ &0 < u + a /\
    &0 < C1092WPS_half c s /\ C1092WPS_half c s < &9 / &40 /\
    linside c s u v a (&0) (--(C1092WPS_half c s)) /\
    (--(&13 / &50) * s - c <= v \/ --(&1) <= s * u + c * v)`;;

let OCPEF_KEEP_TAC keep =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_forall t || (can (find_term ((=) `linside`)) t && not (mem t keep))
    then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

(* Lean: faces *)
let OCPEF_FACES = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ &0 < s /\ s <= c /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&1) (--(&13 / &50)) /\
      ~linside c s u v a (&1) (&0) /\ ~linside c s u v a (&21 / &40) (&1 / &8) /\
      (forall x. &13 / &50 <= x ==> x <= &4 / &5 ==> ~linside c s u v a x (--(&1)))
      ==> ocpef_data c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let mk = `linside c s u v a (&7 / &20) (--(&7 / &20))`
  and el = `linside c s u v a (&13 / &50) (&0)`
  and ou = `linside c s u v a (&1) (--(&13 / &50))` in
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `u + a <= c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCPEF_KEEP_TAC [`~linside c s u v a (&1) (&0)`; el; ou]; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= &1 / &8 * c - &21 / &40 * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCPEF_KEEP_TAC [`~linside c s u v a (&21 / &40) (&1 / &8)`; mk; el; ou]; ALL_TAC] THEN
  SUBGOAL_THEN `&53 * s < &25 * c` ASSUME_TAC THENL [OCPEF_KEEP_TAC [el]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&25 * c - &53 * s) * (&25 * c + &53 * s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&113 / &125 < c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (&113 / &125 - c) * (&113 / &125 + c)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    OCPEF_KEEP_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `s < &43 / &100` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (s - &43 / &100) * (s + &43 / &100)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    OCPEF_KEEP_TAC []; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CCBBS_POSITIVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST [ASM_REAL_ARITH_TAC;
           REPEAT STRIP_TAC THEN
           FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (is_forall o concl)) THEN
           ASM_REWRITE_TAC[];
           OCPEF_KEEP_TAC [mk]];
    DISCH_TAC] THEN
  ABBREV_TAC `z = C1092WPS_half c s` THEN
  SUBGOAL_THEN `&0 < z` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `z * (&1 + c) = s` THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `z < &9 / &40` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (&1 + z pow 2) * (&25 * c - &53 * s)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (z - &9 / &40) * (z + &9 / &40)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    OCPEF_KEEP_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `s * z = &1 - c` ASSUME_TAC THENL
   [SUBGOAL_THEN `(&1 + c) * (s * z - (&1 - c)) = &0` MP_TAC THENL
     [UNDISCH_TAC `z * (&1 + c) = s` THEN UNDISCH_TAC `c * c + s * s = &1` THEN
      CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= z * (&1 - c) /\ &0 < z * (c - &13 / &50 * (&1 + c))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ocpef_data] THEN
  REPEAT CONJ_TAC THEN TRY(OCPEF_KEEP_TAC [ou]) THEN
  OCPEF_KEEP_TAC [mk; el]);;
