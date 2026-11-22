(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/InwardShortBarPoint.lean            *)
(* (namespace N12Compact.Completion.OtherCases.InwardShortBarPoint).        *)
(* A short genuine bottom segment completes the inward central triangle.    *)
(* short_projections: WFP_SP; canonical_frame: CLF_CANONICAL_FRAME;         *)
(* CanonicalScalars.bounds: CCCS_BOUNDS;                                    *)
(* LowerCornerSupport.horizontal: OCLCS_HORIZONTAL.                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;
needs "n12/geometry/CP_OtherCases_LowerCornerSupport.ml";;

let OCISBP_KEEP_TAC keep =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_forall t || (is_neg t && can (find_term ((=) `linside`)) t &&
       not (mem (rand(rator(rand t))) keep)) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

let OCISBP_LIN_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

(* Lean: positive (private) *)
let OCISBP_POSITIVE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&0) (--(&13 / &50)) /\
      ~linside c s u v a (&1) (--(&13 / &50)) /\
      (forall x. &13 / &50 <= x /\ x <= &7 / &20 ==> ~linside c s u v a x (--(&1)))
      ==> linside c s u v a (&1 / &20) (--(&1 / &20))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REFUTE_THEN ASSUME_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  MAP_EVERY (fun x -> FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[] o
      CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_LE_CONV) o SPEC x o check (is_forall o concl)))
    [`&13 / &50`; `&7 / &20`] THEN
  MP_TAC(WFP_SP `&21 / &100` `&19 / &20`) THEN
  MP_TAC(WFP_SP `&19 / &20` `&21 / &100`) THEN
  MP_TAC(WFP_SP `&13 / &20` `&37 / &50`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `v + a <= --(&1 / &20) * (c + s)` ASSUME_TAC THENL
   [OCISBP_KEEP_TAC [`&1 / &20`]; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c - s * &13 / &50` ASSUME_TAC THENL
   [OCISBP_KEEP_TAC [`&1`]; ALL_TAC] THEN
  SUBGOAL_THEN `c * &13 / &50 - s <= u` ASSUME_TAC THENL
   [OCISBP_KEEP_TAC [`&13 / &50`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [OCISBP_KEEP_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `--s * &7 / &20 - c <= v` ASSUME_TAC THENL
   [OCISBP_KEEP_TAC [`&7 / &20`]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `&13 / &50`; `&7 / &20`] OCLCS_HORIZONTAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (fun g -> if is_forall(snd g) then
       (X_GEN_TAC `x:real` THEN DISCH_TAC THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
        ASM_REWRITE_TAC[]) g
     else (TRY(FIRST_ASSUM ACCEPT_TAC) THEN OCISBP_KEEP_TAC []) g);
    DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= s * ((c - s * &13 / &50) - (u + a)) /\
                &0 <= c * (--(&1 / &20) * (c + s) - (v + a)) /\
                &0 < (a - &1) * (c + s) /\ &0 <= s * (&1 - c)`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL;
      MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `s - &5 / &14` REAL_LE_SQUARE) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &1 / &20 - &3 / &20 * c * s + &21 / &100 * s * s` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: negative (private; stated with s = --t, t >= 0) *)
let OCISBP_NEGATIVE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&0) (--(&13 / &50)) /\
      ~linside c s u v a (&1) (--(&13 / &50)) /\
      ~linside c s u v a (&7 / &20) (--(&1))
      ==> linside c s u v a (&1 / &20) (--(&1 / &20))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REFUTE_THEN ASSUME_TAC THEN
  MP_TAC(WFP_SP `&19 / &20` `--(&21 / &100)`) THEN
  MP_TAC(WFP_SP `&37 / &50` `--(&13 / &20)`) THEN
  MP_TAC(WFP_SP `&3 / &10` `--(&19 / &20)`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 / &20 * (c - s) <= u` ASSUME_TAC THENL
   [OCISBP_KEEP_TAC [`&1 / &20`]; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= --s - c * &13 / &50` ASSUME_TAC THENL
   [OCISBP_KEEP_TAC [`&1`]; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c * &7 / &20 - s` ASSUME_TAC THENL
   [OCISBP_KEEP_TAC [`&7 / &20`]; ALL_TAC] THEN
  OCISBP_KEEP_TAC []);;

(* Lean: point *)
let OCISBP_POINT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&13 / &50) (&0) /\
      linside c s u v a (&0) (--(&13 / &50)) /\
      ~linside c s u v a (&1) (--(&13 / &50)) /\
      (forall x. &13 / &50 <= x /\ x <= &7 / &20 ==> ~linside c s u v a x (--(&1)))
      ==> linside c s u v a (&1 / &20) (--(&1 / &20))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN PURE_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = a`)) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && can (find_term ((=) `linside`)) (concl th) &&
       length(fst(strip_forall(concl th))) = 2
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]
    else NO_TAC)) THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MATCH_MP_TAC OCISBP_POSITIVE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC OCISBP_NEGATIVE THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV]);;
