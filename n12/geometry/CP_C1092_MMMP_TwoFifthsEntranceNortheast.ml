(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/TwoFifthsEntranceNortheast.lean     *)
(* (N12Compact.C1092MMMPTwoFifthsEntrance).  The unconditional northeast     *)
(* portion of the two-fifths entrance.  Conventions of                       *)
(* CP_C1092_MMMP_NortheastActualSign.ml (PositiveActual p N is               *)
(* c1092mnas_pos c1 c2 a b l cN sN uN vN aN) and CP_C1092_MMMP_Origins.ml.  *)
(* TopOnlyLeftPoint.positive_faces OCTOLP_POSITIVE_FACES, SharpPointScalars. *)
(* half_lower OCSPS_HALF_LOWER (half = C1092WPS_half), OutwardScalars.       *)
(* increasing_projection CCOS_INCREASING_PROJECTION, TopOrigin.point         *)
(* C1092MMTO_POINT, RightFar.point C1092MRF_POINT, TwoFifths.Northeast       *)
(* C1092TF_northeast.  Tag C1092MTFEN_.                                      *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_TwoFifthsData.ml";;
needs "n12/geometry/CP_C1092_MMMP_TopOrigin.ml";;
needs "n12/geometry/CP_C1092_MMMP_NortheastActualSign.ml";;
needs "n12/geometry/CP_C1092_MMMP_RightFar.ml";;
needs "n12/geometry/CP_OtherCases_TopOnlyLeftPoint.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;

(* Lean: NortheastCore (structure) *)
let c1092mtfen_core = new_definition
 `c1092mtfen_core (c:real) s u v a <=>
    &1 < a /\ &0 < c /\ &0 < s /\ s <= c /\
    &1 + c < &4 * s /\
    (&2 / &5) * s <= u /\ (&2 / &5) * c - s <= v /\
    u + a <= c + s /\ v + a <= c /\
    linside c s u v a (&7 / &20) (&7 / &20) /\
    linside c s u v a (&2 / &5) (&1) /\
    linside c s u v a (&47 / &100) (&3 / &25)`;;

(* Lean: northeast_faces *)
let C1092MTFEN_NORTHEAST_FACES = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ &0 < s /\ s <= c /\
     linside c s u v a (&7 / &20) (&7 / &20) /\
     linside c s u v a (&13 / &50) (&1) /\ linside c s u v a (&2 / &5) (&1) /\
     ~linside c s u v a (&0) (&13 / &50) /\
     ~linside c s u v a (&0) (&2 / &5) /\
     ~linside c s u v a (&0) (&1) /\ ~linside c s u v a (&1) (&1) /\
     ~linside c s u v a (&1) (&13 / &50) /\
     ~linside c s u v a (&1) (&2 / &5)
     ==> c1092mtfen_core c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] OCTOLP_POSITIVE_FACES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < s` THEN REAL_ARITH_TAC; STRIP_TAC] THEN
  OCTOLP_CU_TAC THEN
  OCTOLP_STEP `(&2 / &5) * s <= u` [`~linside c s u v a (&0) (&2 / &5)`] THEN
  OCTOLP_STEP `(&2 / &5) * c - s <= v` [`~linside c s u v a (&1) (&2 / &5)`] THEN
  SUBGOAL_THEN `&1 < (&3 / &5) * c + s` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(&2 / &5) * c - s <= v`; `v + a <= c`; `&1 < a`] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 + c < &4 * s` ASSUME_TAC THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `&3 / &5`] OCSPS_HALF_LOWER) THEN
    ASM_REWRITE_TAC[REAL_POW_2] THEN ANTS_TAC THENL
     [UNDISCH_TAC `&0 < s` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[C1092WPS_half] THEN
    SUBGOAL_THEN `s / (&1 + c) * (&1 + c) = s` MP_TAC THENL
     [MATCH_MP_TAC REAL_DIV_RMUL THEN UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`s / (&1 + c)`, `h:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `&1 / &4 < h` ASSUME_TAC THENL
     [UNDISCH_TAC `&1 - &3 / &5 < (&1 + &3 / &5) * h` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (h - &1 / &4) * (&1 + c)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN
      MAP_EVERY UNDISCH_TAC [`&1 / &4 < h`; `&0 < c`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `h * (&1 + c) = s` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&22 / &25) * c + (&47 / &100) * s < &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `(&47 / &100) * c - (&22 / &25) * s` REAL_LE_SQUARE) THEN
    MP_TAC(SPEC `(&22 / &25) * c + (&47 / &100) * s - &1` REAL_LE_SQUARE) THEN
    UNDISCH_TAC `c * c + s * s = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&53 / &100`; `&22 / &25`] CCOS_INCREASING_PROJECTION) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN ANTS_TAC THENL
   [UNDISCH_TAC `&0 < s` THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[c1092mtfen_core] THEN ASM_REWRITE_TAC[linside] THEN
  MAP_EVERY UNDISCH_TAC [`&13 / &50 * s <= u`; `--s + &13 / &50 * c <= v`;
    `u + a <= c + s`; `v + a <= c`; `(&2 / &5) * s <= u`; `(&2 / &5) * c - s <= v`;
    `&1 < a`; `&0 < c`; `&0 < s`; `s <= c`; `c <= &1`;
    `(&22 / &25) * c + (&47 / &100) * s < &1`; `&53 / &100 * c + &22 / &25 * s < &1`] THEN
  REAL_ARITH_TAC);;

(* Lean: northeast_core *)
let C1092MTFEN_NORTHEAST_CORE = prove
 (parse_term (Printf.sprintf "!%s cN sN uN vN aN. %s /\\ %s /\\ c1092mnas_pos %s cN sN uN vN aN
      ==> c1092mtfen_core cN sN uN vN aN" C1092AE_P C1092AE_HYP C1092MMPE_CTX C1092AE_P),
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mnas_pos] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aN:real = l`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cN sN`)) THEN
  MATCH_MP_TAC C1092MTFEN_NORTHEAST_FACES THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC C1092MO_CODE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  let ne = c1092mo_use C1092MMPE_NORTHEAST_PAIR and nw = c1092mo_use C1092MMPE_NORTHWEST_PAIR in
  let wa = c1092mo_use C1092MMPE_WALL_AUXILIARIES in
  let inner = CONV_RULE REAL_RAT_REDUCE_CONV (MATCH_MP C1092WC_INSIDE_SEGMENT
    (end_itlist CONJ [c1092mo_use C1092MPC_NORTHWEST_CENTER; c1092mo_use C1092MPC_NORTHWEST_NORTH;
                      REAL_ARITH `&0 <= &4 / &5`; REAL_ARITH `&4 / &5 <= &1`])) in
  REWRITE_TAC[c1092mo_seed 6 (`&47 / &20`, `&47 / &20`); CONJUNCT1 ne; CONJUNCT2 ne;
    c1092mo_excl 6 7 (CONJUNCT1 nw); c1092mo_excl 6 7 inner;
    c1092mo_excl 6 11 (c1092mo_use C1092MMTO_POINT);
    c1092mo_excl 6 2 (c1092mo_seed 2 (`&3`, `&3`));
    c1092mo_excl 6 10 (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 wa)));
    c1092mo_excl 6 10 (c1092mo_use C1092MRF_POINT)] THEN
  MP_TAC(c1092mo_side ()) THEN UNDISCH_TAC `&0 < sN` THEN UNDISCH_TAC `sN <= cN` THEN
  UNDISCH_TAC `&7 / &10 <= cN` THEN REAL_ARITH_TAC);;

(* Lean: northeast_sharp *)
let C1092MTFEN_NORTHEAST_SHARP = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> %s" C1092AE_P C1092AE_HYP C1092MMPE_CTX
    (c1092mmpe_in 6 "&247 / &100" "&53 / &25")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MNAS_EXISTS_POSITIVE) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC))
    [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092MTFEN_NORTHEAST_CORE) THEN ASM_REWRITE_TAC[c1092mtfen_core] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `c1092mnas_pos c1 c2 a b l cN sN uN vN aN` THEN REWRITE_TAC[c1092mnas_pos] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&47 / &100`; `&3 / &25`] o check (is_forall o concl)) THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONV_TAC C1092MO_CODE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[]);;

(* Lean: NortheastCore.complete *)
let C1092MTFEN_NORTHEASTCORE_COMPLETE = prove
 (`forall c s u v a:real. c1092mtfen_core c s u v a /\ &3 * s <= &1 + c ==> C1092TF_northeast c s u v a`,
  REWRITE_TAC[c1092mtfen_core; C1092TF_northeast] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;
