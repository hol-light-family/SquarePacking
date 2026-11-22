(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/FinalScalars39.lean                 *)
(* (N12Compact.C1092MMMPFinalScalars39).  The final MMMP scalar              *)
(* contradictions using the strict left-wall endpoint 2.39.                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMMPairScalars.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;

let C1092FS39_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092FS39_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092FS39_LIN_TAC; DISCH_TAC];;

let C1092FS39_NORMAL_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths));;

(* Lean: short (private) *)
let C1092FS39_SHORT = prove
 (`forall d r x y. d pow 2 + r pow 2 = &1 /\ x pow 2 + y pow 2 < &1
             ==> x * d + y * r < &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x * d + y * r) pow 2 + (x * r - y * d) pow 2 = x pow 2 + y pow 2`
    ASSUME_TAC THENL
   [UNDISCH_TAC `d pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `(x * d + y * r) pow 2 < &1` MP_TAC THENL
   [MP_TAC(SPEC `x * r - y * d` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`x * d + y * r`,`p:real`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
  NLIN_TAC [SQ_NONNEG `p - &1`]);;

(* Lean: ownMargin *)
let C1092FS39_ownMargin = new_definition
 `C1092FS39_ownMargin (d:real) (r:real) (b:real) (t:real) =
    &1 - d + (&39 / &100) * r - (b * d + t * r) * (b + t - &1) +
    (t * d - b * r) * (&1 + (&39 / &100) * b - t)`;;

(* Lean: neighborMargin *)
let C1092FS39_neighborMargin = new_definition
 `C1092FS39_neighborMargin (d:real) (r:real) (b:real) (t:real) =
    &1 - b - t + (b * d + t * r) * (&1 - d + (&39 / &100) * r) +
    (t * d - b * r) * (&1 - (&7 / &20) * d + (&7 / &20) * r)`;;

(* Lean: own_positive *)
let C1092FS39_OWN_POSITIVE = prove
 (`forall d r b t. c977cc_normal d r /\ c977cc_normal b t /\ &3 / &5 <= t
             ==> &0 < C1092FS39_ownMargin d r b t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `t:real`] C1092MPS_SINE_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092FS39_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092FS39_LE_MUL_TAC `t - &3 / &5` `t + &3 / &5` THEN
  C1092FS39_LE_MUL_TAC `b - t` `b + t` THEN
  SUBGOAL_THEN `&9 / &25 <= t * t /\ t * t <= &1 / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092FS39_LIN_TAC; ALL_TAC] THEN
  C1092FS39_LE_MUL_TAC `t * t - &9 / &25` `&16 / &25 - t * t` THEN
  C1092FS39_LE_MUL_TAC `b:real` `t:real` THEN
  SUBGOAL_THEN `&12 / &25 <= b * t` ASSUME_TAC THENL
   [SUBGOAL_THEN `(b * t) * (b * t) = (&1 - t * t) * (t * t)` ASSUME_TAC THENL
     [UNDISCH_TAC `b * b + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`(b * t) * (b * t) < &144 / &625`] THEN C1092FS39_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&7 / &5 <= b + t /\ b <= &4 / &5` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THENL
     [NLIN_FACTS_TAC [] [`(b + t) * (b + t) < &49 / &25`] THEN C1092FS39_LIN_TAC;
      NLIN_FACTS_TAC [] [`&16 / &25 < b * b`] THEN C1092FS39_LIN_TAC];
    ALL_TAC] THEN
  (* K = 2 - b - t + 3/5 b t, L = b - t + 3/5 t^2 *)
  C1092FS39_LE_MUL_TAC `b + t - &7 / &5` `&1 - (&3 / &10) * (b + t + &7 / &5)` THEN
  C1092FS39_LE_MUL_TAC `t - &3 / &5` `&1 - (&3 / &5) * (t + &3 / &5)` THEN
  SUBGOAL_THEN
   `(&2 - b - t + (&3 / &5) * b * t) - &111 / &125 =
    (b + t - &7 / &5) * ((&3 / &10) * (b + t + &7 / &5) - &1)` ASSUME_TAC THENL
   [UNDISCH_TAC `b * b + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `b * t <= &1 / &2` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `b - t`]; ALL_TAC] THEN
  ABBREV_TAC `K1 = &2 - b - t + (&3 / &5) * b * t + (&1 / &100) * b * t` THEN
  ABBREV_TAC `L1 = b - t + (&3 / &5) * t * t + (&1 / &100) * t * t` THEN
  SUBGOAL_THEN `&0 <= K1 /\ K1 <= &893 / &1000 /\ &0 <= L1 /\ L1 <= &421 / &1000`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K1"; "L1"] THEN REPEAT CONJ_TAC THEN C1092FS39_LIN_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `r:real`; `K1:real`; `L1:real`] C1092FS39_SHORT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    C1092FS39_LE_MUL_TAC `&893 / &1000 - K1` `&893 / &1000 + K1` THEN
    C1092FS39_LE_MUL_TAC `&421 / &1000 - L1` `&421 / &1000 + L1` THEN
    C1092FS39_LIN_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `C1092FS39_ownMargin d r b t = &1 - K1 * d - L1 * r` SUBST1_TAC THENL
   [REWRITE_TAC[C1092FS39_ownMargin] THEN MAP_EVERY EXPAND_TAC ["K1"; "L1"] THEN
    UNDISCH_TAC `b * b + t * t = &1` THEN CONV_TAC REAL_RING;
    C1092FS39_LIN_TAC]);;

(* Lean: K, L (private defs) *)
let C1092FS39_K = new_definition
 `C1092FS39_K (d:real) (r:real) =
    &2 - d + r - (&13 / &20) * r pow 2 - (&37 / &50) * d * r`;;

let C1092FS39_L = new_definition
 `C1092FS39_L (d:real) (r:real) =
    &27 / &20 - d - r - (&37 / &50) * r pow 2 + (&13 / &20) * d * r`;;

(* Lean: coefficient_bounds (private) *)
let C1092FS39_COEFFICIENT_BOUNDS = prove
 (`forall d r. c977cc_normal d r ==> &1 <= C1092FS39_K d r /\ C1092FS39_L d r <= &7 / &20`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092FS39_NORMAL_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`; `&3 / &4`; `&13 / &20`] C1092FS39_SHORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092FS39_LE_MUL_TAC `r:real` `&1 - (&3 / &4) * d - (&13 / &20) * r` THEN
  C1092FS39_LE_MUL_TAC `d:real` `r:real` THEN
  C1092FS39_LE_MUL_TAC `d * r` `&2 - (&13 / &20) * (&1 + d + r)` THEN
  SUBGOAL_THEN `(&1 + d + r) * (&1 - d - r + (&13 / &20) * d * r) =
                d * r * ((&13 / &20) * (&1 + d + r) - &2)` ASSUME_TAC THENL
   [UNDISCH_TAC `d * d + r * r = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&1 - d - r + (&13 / &20) * d * r <= &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`&0 < (&1 + d + r) * (&1 - d - r + (&13 / &20) * d * r)`] THEN
    C1092FS39_LIN_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[C1092FS39_K; C1092FS39_L; REAL_POW_2] THEN
  SUBGOAL_THEN `&0 <= r * r` ASSUME_TAC THENL [REWRITE_TAC[REAL_LE_SQUARE]; ALL_TAC] THEN
  CONJ_TAC THEN C1092FS39_LIN_TAC);;

(* Lean: endpoint_positive (private) *)
let C1092FS39_ENDPOINT_POSITIVE = prove
 (`forall d r. c977cc_normal d r
         ==> &0 < &1 - (&275 / &373) * C1092FS39_K d r - (&252 / &373) * C1092FS39_L d r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092FS39_NORMAL_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092FS39_LIN_TAC; ALL_TAC] THEN
  ABBREV_TAC `w = C1092WPS_half d r` THEN STRIP_TAC THEN
  SUBGOAL_THEN `w <= &1 / &2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`&0 < (w - &1 / &2) * (&1 + d)`] THEN C1092FS39_LIN_TAC;
    ALL_TAC] THEN
  C1092FS39_LE_MUL_TAC `&1 / &2 - w` `&1 / &2 + w` THEN
  SUBGOAL_THEN `&0 <= w pow 2 /\ w pow 2 <= &1 / &4` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN C1092FS39_LIN_TAC; ALL_TAC] THEN
  C1092FS39_LE_MUL_TAC `w pow 2` `&42652 - &12540 * w - &104420 * w pow 2` THEN
  SUBGOAL_THEN
   `&100 * &373 * (&1 + w pow 2) pow 2 *
    (&1 - (&275 / &373) * C1092FS39_K d r - (&252 / &373) * C1092FS39_L d r) =
    &980 + &3340 * w + w pow 2 * (&42652 - &12540 * w - &104420 * w pow 2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[C1092FS39_K; C1092FS39_L] THEN
    UNDISCH_TAC `(&1 + w pow 2) * d = &1 - w pow 2` THEN
    UNDISCH_TAC `(&1 + w pow 2) * r = &2 * w` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &100 * &373 * (&1 + w pow 2) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_POW_LT THEN C1092FS39_LIN_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`&0`; `&1 - (&275 / &373) * C1092FS39_K d r - (&252 / &373) * C1092FS39_L d r`;
                `&100 * &373 * (&1 + w pow 2) pow 2`] REAL_LT_LMUL_EQ) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  C1092FS39_LIN_TAC);;

(* Lean: neighbor_positive *)
let C1092FS39_NEIGHBOR_POSITIVE = prove
 (`forall d r b t. c977cc_normal d r /\ c977cc_normal b t /\ &252 / &373 <= t
             ==> &0 < C1092FS39_neighborMargin d r b t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C1092FS39_COEFFICIENT_BOUNDS) THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C1092FS39_ENDPOINT_POSITIVE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092FS39_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092FS39_LE_MUL_TAC `t - &252 / &373` `t + &252 / &373` THEN
  SUBGOAL_THEN `b <= &275 / &373` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`&0 < (b - &275 / &373) * (b + &275 / &373)`] THEN
    C1092FS39_LIN_TAC;
    ALL_TAC] THEN
  C1092FS39_LE_MUL_TAC `t - &252 / &373` `(t + &252 / &373) - (&7 / &20) * (b + &275 / &373)` THEN
  SUBGOAL_THEN
   `(b + &275 / &373) * ((b - &275 / &373) + (&7 / &20) * (t - &252 / &373)) =
    (t - &252 / &373) * ((&7 / &20) * (b + &275 / &373) - (t + &252 / &373))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `b * b + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `(b - &275 / &373) + (&7 / &20) * (t - &252 / &373) <= &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`&0 < (b + &275 / &373) * ((b - &275 / &373) + (&7 / &20) * (t - &252 / &373))`] THEN
    C1092FS39_LIN_TAC;
    ALL_TAC] THEN
  C1092FS39_LE_MUL_TAC `C1092FS39_K d r - &1` `&275 / &373 - b` THEN
  C1092FS39_LE_MUL_TAC `t - &252 / &373` `&7 / &20 - C1092FS39_L d r` THEN
  SUBGOAL_THEN `C1092FS39_neighborMargin d r b t =
                &1 - b * C1092FS39_K d r - t * C1092FS39_L d r` SUBST1_TAC THENL
   [REWRITE_TAC[C1092FS39_neighborMargin; C1092FS39_K; C1092FS39_L] THEN
    UNDISCH_TAC `d * d + r * r = &1` THEN CONV_TAC REAL_RING;
    C1092FS39_LIN_TAC]);;
