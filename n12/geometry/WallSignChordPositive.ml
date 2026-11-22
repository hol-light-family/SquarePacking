(* ========================================================================= *)
(* Port of Compact/Geometry/WallSignChordPositive.lean                       *)
(* (N12Compact.WallSignChord.positive_point).  The four strict bands in the  *)
(* positive canonical frame.  centerX/centerY are lcx/lcy.                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallSignChordScalars.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

(* Lean: positive_point *)
let WSCP_POSITIVE_POINT = prove
 (`forall c s u v a r.
      c * c + s * s = &1 /\ &1 < a /\ &0 <= c /\ &0 <= s /\ s <= c /\
      a * (c + s) / &2 - &1 <= lcx c s u v a /\
      &0 <= lcy c s u v a /\
      linside c s u v a (--(&43 / &500)) (&0) /\
      ~linside c s u v a (&13 / &20) (&7 / &20) /\
      &11 / &50 <= r /\ r <= &39 / &100
      ==> linside c s u v a (&0) r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] WSCS_CANONICAL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `r:real`] WSCS_WALL_GAPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] WSCS_QUADRATIC_MARGIN) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lcy c s u v a = s * (u + a / &2) + c * (v + a / &2)` ASSUME_TAC THENL
   [REWRITE_TAC[lcy]; ALL_TAC] THEN
  MP_TAC(WFP_SP `&13 / &20` `--(&1 / &25)`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c /\ &0 < r` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside; REAL_POW_2]) THEN
  REWRITE_TAC[linside] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_RZERO; REAL_ADD_LID; REAL_MUL_LZERO;
                              REAL_ADD_RID]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
  NLIN_FACTS_TAC [] [`&0 <= r * s`] THEN
  SUBGOAL_THEN `u < s * r` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v < c * r` ASSUME_TAC THENL
   [NLIN_FACTS_TAC [] [`&0 < c * (r - &43 / &500)`] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s * r < u + a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`&0 <= c * (lcx c s u v a - (a * (c + s) / &2 - &1))`; `&0 <= s * lcy c s u v a`;
      `&0 < (a - &1) * (&1 + c * (c + s))`] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `u < c * &13 / &20 + s * &7 / &20` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v < --s * &13 / &20 + c * &7 / &20` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`&0 <= c * (&39 / &100 - r)`] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `--s * &13 / &20 + c * &7 / &20 < v + a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`&0 <= s * (c * --(&43 / &500) - u)`;
      `&0 <= c * ((--s * &13 / &20 + c * &7 / &20) - (v + a))`;
      `&0 <= (a - &1) * (c - s)`; `c * (&7 / &20 * c - &1 / &2) < &0`;
      `s * (&1 / &2 - &92 / &125 * c) <= &0`] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c * &13 / &20 + s * &7 / &20` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(u < c * &13 / &20 + s * &7 / &20 /\
                   c * &13 / &20 + s * &7 / &20 < u + a /\
                   v < --s * &13 / &20 + c * &7 / &20 /\
                   --s * &13 / &20 + c * &7 / &20 < v + a)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= s * ((c * &13 / &20 + s * &7 / &20) - (u + a))`;
    `&0 <= c * (c * r - (v + a))`; `&0 < (a - &1) * (c + s)`;
    `&0 <= (c * c) * (&39 / &100 - r)`] THEN
  NLIN_TAC ~deg2:false []);;
