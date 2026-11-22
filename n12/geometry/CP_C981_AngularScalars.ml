(* ========================================================================= *)
(* Port of Compact/Completion/C981/AngularScalars.lean                        *)
(* (N12Compact.C981CompletionAngularScalars).  The rational scalar ending in *)
(* C981-COMMON-CYCLE Theorem 3.                                               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_HalfAngle.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C981AS_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC];;

(* Lean: impossible *)
let C981AS_IMPOSSIBLE = prove
 (`forall d r b t. c977cc_normal d r /\ c977cc_normal b t /\
     &7 / &18 <= c981ha_half b t /\
     &1 < b * (&1 - r * (&1 - (&7 / &20) * (d + r))) +
          t * (&1 - d * (&1 - (&7 / &20) * (d + r)))
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal; REAL_POW_2] th)) ns) THEN
  SUBGOAL_THEN `&7 * (&1 + b) <= &18 * t` ASSUME_TAC THENL
  [UNDISCH_TAC `&7 / &18 <= c981ha_half b t` THEN REWRITE_TAC[c981ha_half] THEN
   ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&7 / &10 <= b ==> &0 < &1 + b`] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `H = d + r` THEN ABBREV_TAC `q = &1 - (&7 / &20) * H` THEN
  ABBREV_TAC `FF = &1 - r * q` THEN ABBREV_TAC `G = &1 - d * q` THEN
  SUBGOAL_THEN `&1 < FF * FF + G * G` ASSUME_TAC THENL
  [SUBGOAL_THEN `(b * FF + t * G) * (b * FF + t * G) + (b * G - t * FF) * (b * G - t * FF) =
                 FF * FF + G * G` MP_TAC THENL
   [UNDISCH_TAC `b * b + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   MP_TAC(SPEC `b * G - t * FF` REAL_LE_SQUARE) THEN
   UNDISCH_TAC `&1 < b * FF + t * G` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
   SPEC_TAC(`b * FF + t * G`,`X:real`) THEN SPEC_TAC(`b * G - t * FF`,`Y:real`) THEN
   SPEC_TAC(`FF * FF + G * G`,`N:real`) THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
   NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `FF * FF + G * G - &1 = &2 - (&27 / &10) * H + (&329 / &400) * H * H`
  ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["FF"; "G"; "q"; "H"] THEN
   UNDISCH_TAC `d * d + r * r = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `H < &113 / &100` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `(H - &113 / &100) * (--(&27 / &10) + (&329 / &400) * (H + &113 / &100)) <= &0`
   MP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= a * --b ==> a * b <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r < &7 / &50` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C981AS_PROD `&0 <= (&113 / &100 - r - d) * (&113 / &100 - r + d)` THEN
   C981AS_PROD `&0 <= (r - &7 / &50) * (&99 / &100 - r)` THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&99 / &100 < d` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C981AS_PROD `&0 <= (&99 / &100 - d) * (&99 / &100 + d)` THEN
   C981AS_PROD `&0 < (&7 / &50 - r) * (&7 / &50 + r)` THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1209 / &2000 < q /\ q <= &1` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C981AS_PROD `&0 <= r * (q - &1209 / &2000)` THEN
  C981AS_PROD `&0 <= r * (&1 - q)` THEN
  SUBGOAL_THEN `FF <= &1 - (&1209 / &2000) * r /\ &43 / &50 < FF` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 - d <= (&3 / &5) * r * r` ASSUME_TAC THENL
  [C981AS_PROD `&0 <= (&1 - d) * (&3 * d - &2)` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `G = &7 / &20 + (&1 - d) - (&7 / &20) * r * r + (&7 / &20) * d * r`
  ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["G"; "q"; "H"] THEN
   UNDISCH_TAC `d * d + r * r = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C981AS_PROD `&0 <= r * (&1 - d)` THEN
  C981AS_PROD `&0 <= r * (&7 / &50 - r)` THEN
  SUBGOAL_THEN `G <= &7 / &20 + (&77 / &200) * r` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&252 / &373 <= t` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C981AS_PROD `&0 < (&275 / &373 - b) * (&275 / &373 + b)` THEN
   C981AS_PROD `&0 < (&252 / &373 - t) * (&252 / &373 + t)` THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&275 * b + &252 * t <= &373` ASSUME_TAC THENL
  [SUBGOAL_THEN `(&275 * b + &252 * t) * (&275 * b + &252 * t) <= &373 * &373` MP_TAC THENL
   [MP_TAC(SPEC `&252 * b - &275 * t` REAL_LE_SQUARE) THEN
    UNDISCH_TAC `b * b + t * t = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SPEC_TAC(`&275 * b + &252 * t`,`w:real`) THEN GEN_TAC THEN DISCH_TAC THEN
   NLIN_TAC [SQ_NONNEG `w - &373`]; ALL_TAC] THEN
  C981AS_PROD `&0 <= FF * (&373 - &275 * b - &252 * t)` THEN
  C981AS_PROD `&0 <= (t - &252 / &373) * (&252 * FF - &275 * G)` THEN
  ASM_REAL_ARITH_TAC);;
