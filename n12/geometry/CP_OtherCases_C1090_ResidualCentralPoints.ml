(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1090/ResidualCentralPoints.lean    *)
(* (namespace N12Compact.Completion.OtherCases.C1090.ResidualCentralPoints). *)
(* C974-C976-CENTRAL-CROSSPOINTS, Theorems 3 and 4.  The square is written  *)
(* c s u v l (side l), because Lean's parameters are called a b.  In the    *)
(* *_negative lemmas Lean's s (with q.s = -s) is r.  canonical_frame:       *)
(* CLF_CANONICAL_FRAME; CanonicalScalars.bounds: CCCS_BOUNDS.               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let C1090RCP_LIN_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

let C1090RCP_FRAME_TAC =
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `l:real`] CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `l1:real`] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && can (find_term ((=) `linside`)) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]
    else NO_TAC));;

(* Lean: short_projection (private) *)
let C1090RCP_SHORT_PROJECTION = prove
 (`forall c s a b. c pow 2 + s pow 2 = &1 /\ a pow 2 + b pow 2 < &1
             ==> a * c + b * s < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a * c + b * s) pow 2 + (a * s - b * c) pow 2 = a pow 2 + b pow 2`
    ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC [SQ_NONNEG `a * s - b * c`; SQ_NONNEG `a * c + b * s - &1`]);;

let C1090RCP_SP a b =
  let th = SPECL [`c:real`; `s:real`; a; b] C1090RCP_SHORT_PROJECTION in
  CONV_RULE (LAND_CONV (RAND_CONV REAL_RAT_REDUCE_CONV)) th;;

(* Lean: mixed_positive (private) *)
let C1090RCP_MIXED_POSITIVE = prove
 (`forall c s u v l.
      c * c + s * s = &1 /\ &0 < l /\
      &1 < l /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v l (&7 / &20) (&7 / &20) /\
      linside c s u v l (&0) (&13 / &50) /\
      linside c s u v l (&13 / &50) (&1) /\
      ~linside c s u v l (--(&7 / &20)) (&7 / &20) /\
      ~linside c s u v l (&0) (&1) /\
      ~linside c s u v l (&1) (&1) /\
      ~linside c s u v l (&1) (&13 / &50)
      ==> linside c s u v l (&21 / &50) (&4 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  MP_TAC(C1090RCP_SP `&21 / &25` `&21 / &50`) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
  SUBGOAL_THEN `--(&7 / &20) * c + (&7 / &20) * s <= u` ASSUME_TAC THENL
   [C1090RCP_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v + l <= c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `s <= u` ASSUME_TAC THENL [C1090RCP_LIN_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `v + l <= c - s` ASSUME_TAC THENL [C1090RCP_LIN_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `--(&1) * s + (&13 / &50) * c <= v` ASSUME_TAC THENL
     [C1090RCP_LIN_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1090RCP_LIN_TAC);;

(* Lean: mixed_negative (private) *)
let C1090RCP_MIXED_NEGATIVE = prove
 (`forall c s u v l r.
      c * c + s * s = &1 /\ &0 < l /\ s = --r /\
      &1 < l /\ &0 < c /\ &0 <= r /\ r <= c /\
      linside c s u v l (&7 / &20) (&7 / &20) /\
      linside c s u v l (&0) (&13 / &50) /\
      linside c s u v l (&13 / &50) (&1) /\
      ~linside c s u v l (&0) (&1) /\
      ~linside c s u v l (&1) (&1)
      ==> linside c s u v l (&21 / &50) (&4 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(s:real) = --r`)) THEN
  MP_TAC(SPECL [`c:real`; `r:real`] CCCS_BOUNDS) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `r:real`; `&21 / &50`; `&21 / &25`] C1090RCP_SHORT_PROJECTION) THEN
  CONV_TAC(LAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV)) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `--r <= u` ASSUME_TAC THENL [C1090RCP_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v + l <= c + r` ASSUME_TAC THENL [C1090RCP_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v < (&21 / &50) * r + (&4 / &25) * c` ASSUME_TAC THENL
   [ASM_CASES_TAC `(&5 / &21) * c <= r` THEN C1090RCP_LIN_TAC; ALL_TAC] THEN
  C1090RCP_LIN_TAC);;

(* Lean: mixed_point *)
let C1090RCP_MIXED_POINT = prove
 (`forall c s u v l.
      c * c + s * s = &1 /\ &0 < l /\ &1 < l /\
      linside c s u v l (&7 / &20) (&7 / &20) /\
      linside c s u v l (&0) (&13 / &50) /\
      linside c s u v l (&13 / &50) (&1) /\
      ~linside c s u v l (--(&7 / &20)) (&7 / &20) /\
      ~linside c s u v l (&0) (&1) /\
      ~linside c s u v l (&1) (&1) /\
      ~linside c s u v l (&1) (&13 / &50)
      ==> linside c s u v l (&21 / &50) (&4 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1090RCP_FRAME_TAC THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MATCH_MP_TAC C1090RCP_MIXED_POSITIVE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC C1090RCP_MIXED_NEGATIVE THEN EXISTS_TAC `--s1` THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: Parameters (structure) *)
let c1090rcp_parameters = new_definition
 `c1090rcp_parameters (a:real) (b:real) <=>
    &2 / &5 <= a /\ a <= &11 / &20 /\ &1 / &10 <= b /\ b <= &1 / &5 /\
    &13 / &50 + b <= a /\ a + b <= &37 / &50`;;

(* Lean: southeast_positive (private) *)
let C1090RCP_SOUTHEAST_POSITIVE = prove
 (`forall c s u v l a b.
      c * c + s * s = &1 /\ &0 < l /\ c1090rcp_parameters a b /\
      &1 < l /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v l (&7 / &20) (--(&7 / &20)) /\
      linside c s u v l (&13 / &50) (&0) /\
      linside c s u v l (&1) (--(&13 / &50)) /\
      ~linside c s u v l a b
      ==> linside c s u v l (&1) (--(&1 / &2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1090rcp_parameters] THEN STRIP_TAC THEN
  MP_TAC(C1090RCP_SP `&7 / &10` `&3 / &5`) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC []
   [`&2 / &5 * c <= a * c`; `a * s <= &11 / &20 * s`; `&1 / &10 * c <= b * c`;
    `&0 <= (c - s) * (&13 / &50 + b)`; `&0 <= c * (&37 / &50 - (a + b))`;
    `&0 <= (c - s) * (a - &7 / &20)`; `&0 <= s * b`;
    `c * (&1 / &4) <= c * (&7 / &10 + b - a)`;
    `&2 / &5 * s <= a * s`; `b * c <= &1 / &5 * c`] THEN
  SUBGOAL_THEN `v + l <= --s * a + c * b` ASSUME_TAC THENL
   [C1090RCP_LIN_TAC; ALL_TAC] THEN
  C1090RCP_LIN_TAC);;

(* Lean: southeast_negative (private) *)
let C1090RCP_SOUTHEAST_NEGATIVE = prove
 (`forall c s u v l r a b.
      c * c + s * s = &1 /\ &0 < l /\ s = --r /\ c1090rcp_parameters a b /\
      &1 < l /\ &0 < c /\ &0 <= r /\ r <= c /\
      linside c s u v l (&7 / &20) (--(&7 / &20)) /\
      linside c s u v l (&13 / &50) (&0) /\
      linside c s u v l (&1) (--(&13 / &50)) /\
      ~linside c s u v l (&0) (--(&1 / &2)) /\
      ~linside c s u v l a b
      ==> linside c s u v l (&1) (--(&1 / &2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1090rcp_parameters] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(s:real) = --r`)) THEN
  MP_TAC(SPECL [`c:real`; `r:real`] CCCS_BOUNDS) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `r:real`; `&7 / &10`; `&11 / &20`] C1090RCP_SHORT_PROJECTION) THEN
  CONV_TAC(LAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV)) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (c - r) * b`; `&0 <= c * (a - (&13 / &50 + b))`;
    `&2 / &5 * r <= a * r`; `&1 / &10 * c <= b * c`; `a * c <= &11 / &20 * c`;
    `&0 <= r * (&13 / &50 + b)`;
    `a * r <= &11 / &20 * r`; `b * c <= &1 / &5 * c`; `&0 <= r * (&1 - a)`] THEN
  SUBGOAL_THEN `v + l <= r * a + c * b` ASSUME_TAC THENL
   [C1090RCP_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 / &2) * r <= u` ASSUME_TAC THENL
   [C1090RCP_LIN_TAC; ALL_TAC] THEN
  C1090RCP_LIN_TAC);;

(* Lean: southeast_point *)
let C1090RCP_SOUTHEAST_POINT = prove
 (`forall c s u v l a b.
      c * c + s * s = &1 /\ &0 < l /\ c1090rcp_parameters a b /\ &1 < l /\
      linside c s u v l (&7 / &20) (--(&7 / &20)) /\
      linside c s u v l (&13 / &50) (&0) /\
      linside c s u v l (&1) (--(&13 / &50)) /\
      ~linside c s u v l (&0) (--(&1 / &2)) /\
      ~linside c s u v l a b
      ==> linside c s u v l (&1) (--(&1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1090RCP_FRAME_TAC THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MATCH_MP_TAC C1090RCP_SOUTHEAST_POSITIVE THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC C1090RCP_SOUTHEAST_NEGATIVE THEN
    MAP_EVERY EXISTS_TAC [`--s1`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC]);;
