(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveWallOwnedWestFaces.lean (Jatloe,         *)
(* N12-jatloe; namespace N12Compact.PositiveWallOwnedWestFaces).             *)
(* Positive-wall faces when the central square owns (1,2).  Normal is        *)
(* c977cc_normal; PositiveWallMarker.upper_faces: PWM_UPPER_FACES;           *)
(* FourSquareBLBridge.left_wall: FSBL_LEFT_WALL.                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/PositiveWallMarker.ml";;

let PWOWF_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PWOWF_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let PWOWF_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PWOWF_MISSING_TAC t =
  UNDISCH_TAC t THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

(* Lean: lower_face *)
let PWOWF_LOWER_FACE = prove
 (`forall c s u v a.
     c977cc_normal c s /\ linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&12 / &5) /\ ~linside c s u v a (&1) (&2)
     ==> &2 * c - s <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PWOWF_NORMAL_TAC THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside c s u v a (&457 / &500) (&2)`; `linside c s u v a (&1) (&12 / &5)`] THEN
  PWOWF_MISSING_TAC `~linside c s u v a (&1) (&2)`);;

(* Lean: sum_margin (private) *)
let PWOWF_SUM_MARGIN = prove
 (`forall d t. c977cc_normal d t ==> &1 + (&4 / &5) * d * t <= d + t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN PWOWF_NORMAL_TAC THEN
  PWOWF_PROD_TAC `d + t - &1` `&3 / &2 - (d + t)` THEN NLIN_TAC ~deg2:false []);;

(* Lean: upper_v *)
let PWOWF_UPPER_V = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     c977cc_normal c s /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&457 / &500) (&2) /\ linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&1) (&2) /\ ~linside c s u v a (&19 / &25) (&187 / &100) /\
     ~linside c s u v a (&457 / &500) (&3) /\ ~linside c s u v a (&4 / &5) (&3)
     ==> v + a <= &3 * c - (&457 / &500) * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] PWOWF_LOWER_FACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] PWM_UPPER_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  PWOWF_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lcx] THEN
  SUBGOAL_THEN `abs s = s` SUBST1_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `s * (v + a) <= c * u` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside c s u v a (&457 / &500) (&2)`; `linside c s u v a (&1) (&12 / &5)`] THEN
  PWOWF_PRODLT_TAC `a - &1` `c + s` THEN
  PWOWF_PROD_TAC `s:real` `v - (&2 * c - s)` THEN
  PWOWF_PROD_TAC `c:real` `(&457 / &500) * c + &3 * s - (u + a)` THEN
  SUBGOAL_THEN `(&43 / &500) * c pow 2 < (&1 - c) * (&1 - s)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PWOWF_PROD_TAC `c:real` `&1 - c` THEN
  SUBGOAL_THEN `&1 - c <= s pow 2` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `c / &4 < s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   PWOWF_PROD_TAC `c / &4 - s` `c / &4 + s` THEN
   PWOWF_PROD_TAC `s:real` `&1 - c` THEN
   PWOWF_PRODLT_TAC `c:real` `c:real` THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_CASES_TAC `u + a <= (&4 / &5) * c + &3 * s` THENL
  [SUBGOAL_THEN `(&187 / &100) * c - (&19 / &25) * s <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(&19 / &25) * c + (&187 / &100) * s <= u` ASSUME_TAC THENL
    [PWOWF_MISSING_TAC `~linside c s u v a (&19 / &25) (&187 / &100)`; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
   PWOWF_PROD_TAC `s:real` `v - ((&187 / &100) * c - (&19 / &25) * s)` THEN
   PWOWF_PROD_TAC `c:real` `(&4 / &5) * c + &3 * s - (u + a)` THEN
   MP_TAC(SPECL [`c:real`; `s:real`] PWOWF_SUM_MARGIN) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN `c * s <= &1 / &2` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `c - s:real`]; ALL_TAC] THEN
   MATCH_MP_TAC(TAUT `false ==> p`) THEN NLIN_TAC ~deg2:false [SQ_NONNEG `s:real`];
   ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= &3 * c - (&4 / &5) * s` ASSUME_TAC THENL
  [PWOWF_MISSING_TAC `~linside c s u v a (&4 / &5) (&3)`; ALL_TAC] THEN
  SUBGOAL_THEN `&1 < c + s / &5` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PWOWF_PRODLT_TAC `c + s / &5 - &1` `c + &1` THEN
  PWOWF_PROD_TAC `s:real` `&1 - c` THEN
  SUBGOAL_THEN `s < &2 / &5` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  PWOWF_PRODLT_TAC `&2 / &5 - s` `&2 / &5 + s` THEN
  SUBGOAL_THEN `&21 / &25 < c pow 2` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PWOWF_PRODLT_TAC `c + s / &5 - &1` `&1 - s` THEN
  MATCH_MP_TAC(TAUT `false ==> p`) THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `s - &1 / &2`]);;

(* Lean: tilt *)
let PWOWF_TILT = prove
 (`forall d t a lo. c977cc_normal d t /\ &1 < a /\ &2 * d - t <= lo /\
              lo + a <= &3 * d - (&457 / &500) * t
     ==> &0 < t /\ t < &43 / &250`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PWOWF_NORMAL_TAC THEN
  SUBGOAL_THEN `&1 < d + (&43 / &500) * t` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  PWOWF_PRODLT_TAC `d + (&43 / &500) * t - &1` `d + &1` THEN
  PWOWF_PROD_TAC `t:real` `&1 - d` THEN
  NLIN_TAC []);;
