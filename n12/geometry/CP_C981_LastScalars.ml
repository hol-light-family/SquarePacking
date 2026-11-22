(* ========================================================================= *)
(* Port of Compact/Completion/C981/LastScalars.lean                           *)
(* (N12Compact.C981CompletionLastScalars).  Exact scalar bounds for the last *)
(* two C981 cycles at the thirty-degree threshold.                            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_AngularScalars.ml";;

let C981LS_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC];;

let C981LS_NORMALS_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal; REAL_POW_2] th)) ns);;

(* Lean: half_endpoint_refined *)
let C981LS_HALF_ENDPOINT_REFINED = prove
 (`forall b t FF G. c977cc_normal b t /\ &1 / &2 <= t /\ &43 / &50 <= FF /\ G <= &41 / &100
     ==> b * FF + t * G <= (&751 / &867) * FF + G / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C981LS_NORMALS_TAC THEN
  SUBGOAL_THEN `&867 * b + &500 * t <= &1001` ASSUME_TAC THENL
  [SUBGOAL_THEN `(&867 * b + &500 * t) * (&867 * b + &500 * t) +
                 (&500 * b - &867 * t) * (&500 * b - &867 * t) = &1001689`
   MP_TAC THENL
   [UNDISCH_TAC `b * b + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   MP_TAC(SPEC `&500 * b - &867 * t` REAL_LE_SQUARE) THEN
   POP_ASSUM_LIST(K ALL_TAC) THEN
   SPEC_TAC(`&867 * b + &500 * t`,`X:real`) THEN
   SPEC_TAC(`(&500 * b - &867 * t) * (&500 * b - &867 * t)`,`Y:real`) THEN
   REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
   REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&1001 * &1001 < X * X` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C981LS_PROD `&0 <= FF * (&1001 - &867 * b - &500 * t)` THEN
  C981LS_PROD `&0 <= (t - &1 / &2) * (&500 * FF - &867 * G)` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: half_endpoint *)
let C981LS_HALF_ENDPOINT = prove
 (`forall b t FF G. c977cc_normal b t /\ &1 / &2 <= t /\ &43 / &50 <= FF /\ G <= &41 / &100
     ==> b * FF + t * G <= (&867 / &1000) * FF + G / &2`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    MP_TAC(MATCH_MP C981LS_HALF_ENDPOINT_REFINED th) THEN MP_TAC th) THEN
  REAL_ARITH_TAC);;

(* Lean: marker_cut_small *)
let C981LS_MARKER_CUT_SMALL = prove
 (`forall d r b t. c977cc_normal d r /\ c977cc_normal b t /\
     &1 < b * (&1 - r * (&1 - (&7 / &20) * (d + r))) +
          t * (&1 - d * (&1 - (&7 / &20) * (d + r)))
     ==> r < &7 / &50 /\ &99 / &100 < d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C981LS_NORMALS_TAC THEN
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
   C981LS_PROD `&0 <= (&113 / &100 - r - d) * (&113 / &100 - r + d)` THEN
   C981LS_PROD `&0 <= (r - &7 / &50) * (&99 / &100 - r)` THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C981LS_PROD `&0 <= (&99 / &100 - d) * (&99 / &100 + d)` THEN
  C981LS_PROD `&0 < (&7 / &50 - r) * (&7 / &50 + r)` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: negative_impossible *)
let C981LS_NEGATIVE_IMPOSSIBLE = prove
 (`forall d r b t. c977cc_normal d r /\ c977cc_normal b t /\ &1 / &2 <= t /\
     &1 < b * (&1 - r * (&1 - (&7 / &20) * (d + r))) +
          t * (&1 - d * (&1 - (&7 / &20) * (d + r))) /\
     &1 < b * (&1 - r + (&13 / &50) * d * r + r pow 2) +
          t * (&1 - d + (&13 / &50) * d pow 2 + d * r)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`; `b:real`; `t:real`] C981LS_MARKER_CUT_SMALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C981LS_NORMALS_TAC THEN
  C981LS_PROD `&0 <= d * r` THEN
  C981LS_PROD `&0 <= r * (&1 - d)` THEN
  C981LS_PROD `&0 <= (&1 - d) * (&3 * d - &2)` THEN
  C981LS_PROD `&0 <= (&7 / &50 - r) * (&7 / &50 + r)` THEN
  C981LS_PROD `&0 <= r * (&7 / &50 - r)` THEN
  C981LS_PROD `&0 <= r * r` THEN
  SUBGOAL_THEN `&1 - d <= (&3 / &5) * r * r` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`b:real`; `t:real`;
     `&1 - r + (&13 / &50) * d * r + r pow 2`;
     `&1 - d + (&13 / &50) * d pow 2 + d * r`] C981LS_HALF_ENDPOINT) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[REAL_POW_2] THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&1 < b * (&1 - r + (&13 / &50) * d * r + r pow 2) +
          t * (&1 - d + (&13 / &50) * d pow 2 + d * r)` THEN
  REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC);;
