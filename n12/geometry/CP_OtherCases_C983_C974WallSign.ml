(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/C974WallSign.lean              *)
(* (N12Compact.Completion.OtherCases.C983.C974MissingCorner).  The two      *)
(* remaining actual-axis comparisons of MISSING-CORNER-WALL-SIGN 1.3-1.6    *)
(* and its Theorem 1.  Conventions of CP_OtherCases_C983_C974MissingCorner  *)
(* Supports.ml (Input K W = c974mc_input, invariants explicit in            *)
(* C974MCS_INV; lower / upper = ABT_lower / ABT_upper, lower_in_bands /     *)
(* upper_in_bands C981SF_LOWER/UPPER_IN_BANDS, strict_bounds                *)
(* ABT_STRICT_BOUNDS, separator_cone / separating_u / upper_self            *)
(* C974MCS_SEPARATOR_CONE / C974MCS_SEPARATING_U / C974MCS_UPPER_SELF);     *)
(* singleton_wall / singleton_quadrant / Input.reframeK / reframeW          *)
(* C974MC_*; wall_negative_caps C974WNC_WALL_NEGATIVE_CAPS; quadrant_half / *)
(* negative_wall_scalar C974WSS_*; singleton_canonical_positive             *)
(* C974SGN_SINGLETON_CANONICAL_POSITIVE; canonical_frame                    *)
(* CLF_CANONICAL_FRAME.  (Lean header: "this has not been replayed in       *)
(* Lean".)  Tag C974WS_.                                                     *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_C974WallNegativeCaps.ml";;
needs "n12/geometry/CP_OtherCases_C983_C974WallSignScalars.ml";;

let C974WS_LIN = NLIN_TAC ~deg2:false [];;
let C974WS_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     REPEAT CONJ_TAC THEN C974WS_LIN;
     ALL_TAC]) tms;;
let C974WS_KV = [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`]
and C974WS_WV = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`];;
let C974WS_WT = [`cW:real`; `--t`; `uW:real`; `vW:real`; `aW:real`];;
let C974WS_WTK = [`cW:real`; `--t`; `uW:real`; `vW:real`; `aK:real`];;

(* Lean: negative_wall_impossible *)
let C974WS_NEGATIVE_WALL_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s %s t. %s /\\ &0 < cK /\\ &0 < sK /\\ vK + aK <= &0 /\\
     sW = --t /\\ &0 < cW /\\ &0 <= t /\\ t <= cW ==> F" C974MCS_K C974MCS_W C974MCS_INV),
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sW:real = --t`)) THEN
  MP_TAC(SPECL (C974WS_KV @ C974WS_WT) C974MC_SINGLETON_WALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C974WS_KV @ C974WS_WT @ [`t:real`]) C974WNC_WALL_NEGATIVE_CAPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  let cone_tac nx ny =
    DISCH_TAC THEN MP_TAC(SPECL (C974WS_KV @ C974WS_WT @ [nx; ny]) C974MCS_SEPARATOR_CONE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_NEG_NEG] THEN STRIP_TAC THEN C974WS_LIN in
  SUBGOAL_THEN `~(ABT_upper cK sK uK vK aK (-- --t) cW <= ABT_lower cW (--t) uW vW aW (-- --t) cW)`
    ASSUME_TAC THENL [cone_tac `-- --t` `cW:real`; ALL_TAC] THEN
  SUBGOAL_THEN `~(ABT_upper cK sK uK vK aK (--t) (--cW) <= ABT_lower cW (--t) uW vW aW (--t) (--cW))`
    ASSUME_TAC THENL [cone_tac `--t` `--cW`; ALL_TAC] THEN
  MP_TAC(SPECL (C974WS_KV @ C974WS_WT) C974MCS_SEPARATING_U) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  (DISCH_TAC THEN C974MCS_OPEN_TAC THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`] C974WSS_QUADRANT_HALF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `x = sK / (&1 + cK)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + x pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_var (lhs (concl th)) &&
      (lhs (concl th) = `cK:real` || lhs (concl th) = `sK:real`)
    then MP_TAC th THEN ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN DISCH_TAC else NO_TAC)) THEN
  SUBGOAL_THEN `x * (&1 + cK) = sK` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    UNDISCH_TAC `&0 < cK` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aK:real = aW`)) THEN
  NLIN_FACTS_TAC [] [`sK < &1`; `cW <= &1`; `t < &1 / &3`] THEN
  NLIN_FACTS_TAC [] [`&9 / &10 < cW`] THEN
  C974WS_PROD_TAC [`&0 <= cK * t`; `&0 < sK * cW`] THEN
  SUBGOAL_THEN `&0 < cK * t + sK * cW` ASSUME_TAC THENL [C974WS_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `uW - cW < &0 /\ uK < &0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `linside cW (--t) uW vW aK (&1) (&0)` THEN
    UNDISCH_TAC `linside cK sK uK vK aK (&0) (--(&43 / &500))` THEN
    REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN C974WS_LIN; ALL_TAC] THEN
  C974WS_PROD_TAC [`&0 <= cK * --(vK + aK)`; `&0 < (aK - &1) * (cK + sK)`] THEN
  SUBGOAL_THEN `&0 < sK * (uK + aK - (&1 - x))` ASSUME_TAC THENL [C974WS_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `&1 - x < uK + aK` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C974WS_PROD_TAC [`&0 <= sK * ((&1 - x) - (uK + aK))`] THEN C974WS_LIN; ALL_TAC]) THEN
  (FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj (concl th) &&
     can (find_term ((=) `ABT_upper`)) (concl th)))) THENL
  [(* alongK *)
  (MP_TAC(SPECL (C974WS_KV @ C974WS_WTK @ [`cK:real`; `sK:real`]) C974MCS_SEPARATOR_CONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; STRIP_TAC] THEN
  C974WS_PROD_TAC [`&0 <= t * (&90 * cK - &43 * sK)`; `&0 < cK * (&20 * cW - &77 * t)`;
                   `&0 < cK * cW`] THEN
  SUBGOAL_THEN `&0 < cK * cW - sK * t` ASSUME_TAC THENL [C974WS_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `x < &2 / &3` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C974WS_PROD_TAC [`&0 <= (&1 + cK) * (x - &2 / &3)`] THEN
    NLIN_FACTS_TAC [] [`&2 * (&1 + cK) <= &3 * sK`] THEN
    NLIN_FACTS_TAC [] [`&43 / &92 < cK`] THEN
    C974WS_PROD_TAC [`&0 <= (&3 * sK - &2 * (&1 + cK)) * (&3 * sK + &2 * (&1 + cK))`;
                     `&0 < cK * (cK - &43 / &92)`] THEN
    C974WS_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_lower cW (--t) uW vW aK cK sK =
                cK + (cK * cW - sK * t) * (uW - cW) + (cK * t + sK * cW) * (vW - t)` ASSUME_TAC THENL
   [REWRITE_TAC[C981SF_LOWER_IN_BANDS] THEN
    SUBGOAL_THEN `cK * cW + sK * --t = cK * cW - sK * t /\ --cK * --t + sK * cW = cK * t + sK * cW`
      (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    UNDISCH_TAC `cW * cW + --t * --t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL C974WS_KV C974MCS_UPPER_SELF) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `uK + aK <= cK + (cK * cW - sK * t) * (uW - cW) + (cK * t + sK * cW) * (vW - t)`
    ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`ABT_upper cK sK uK vK aK cK sK <= ABT_lower cW (--t) uW vW aK cK sK`;
      `ABT_upper cK sK uK vK aK cK sK = uK + aK`;
      `ABT_lower cW (--t) uW vW aK cK sK =
       cK + (cK * cW - sK * t) * (uW - cW) + (cK * t + sK * cW) * (vW - t)`] THEN
    REAL_ARITH_TAC; ALL_TAC]) THEN
  (FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj (concl th) &&
     not (can (find_term ((=) `ABT_upper`)) (concl th))))) THENL
  [(* uCap *) (C974WS_PROD_TAC [`&0 <= (cK * cW - sK * t) * (cW - ((uW - cW) + aK))`;
                   `&0 <= (cK * t + sK * cW) * ((t + cW / &2) - ((vW - t) + aK))`;
                   `&0 < (aK - &1) * ((cK * cW - sK * t) + (cK * t + sK * cW))`] THEN
  SUBGOAL_THEN `&1 - cK - x + (cK * cW - sK * t) * (&1 - cW) +
                (cK * t + sK * cW) * (&1 - t - cW / &2) < &0` ASSUME_TAC THENL
   [C974WS_LIN; ALL_TAC] THEN
  ABBREV_TAC `y = t / (&1 + cW)` THEN
  SUBGOAL_THEN `&0 < &1 + cW` ASSUME_TAC THENL [C974WS_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `y * (&1 + cW) = t` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    UNDISCH_TAC `&0 < &1 + cW` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= y` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THEN C974WS_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `y < &1 / &7` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C974WS_PROD_TAC [`&0 <= (&1 + cW) * (y - &1 / &7)`] THEN C974WS_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `t * y = &1 - cW` ASSUME_TAC THENL
   [MP_TAC(SPECL [`t * y`; `&1 - cW`; `&1 + cW`] REAL_EQ_MUL_RCANCEL) THEN
    SUBGOAL_THEN `~(&1 + cW = &0)` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `&0 < &1 + cW` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY UNDISCH_TAC [`y * (&1 + cW) = t`; `cW * cW + --t * --t = &1`] THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + y pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `y:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `cW:real`; `t:real`; `x:real`; `y:real`]
    C974WSS_NEGATIVE_WALL_SCALAR) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_EQ_RDIV_EQ; REAL_LT_IMP_LE] THEN
    REPEAT CONJ_TAC THEN
    MAP_EVERY UNDISCH_TAC [`y * (&1 + cW) = t`; `t * y = &1 - cW`] THEN CONV_TAC REAL_RING;
    DISCH_TAC THEN C974WS_LIN]);
   (* cHigh *) (C974WS_PROD_TAC [`&0 < (cK * cW - sK * t) * --(uW - cW)`;
                   `&0 <= (cK * t + sK * cW) * (t - ((vW - t) + aK))`;
                   `&0 < (cK * t + sK * cW) * (aK - &1)`] THEN
  SUBGOAL_THEN `&1 - x < cK - (cK * t + sK * cW) * (&1 - t)` ASSUME_TAC THENL
   [C974WS_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= cK + sK` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C974WS_PROD_TAC [`&0 < (&1 - (cK + sK)) * (&1 + cK + sK)`; `&0 < cK * sK`] THEN
    C974WS_LIN; ALL_TAC] THEN
  C974WS_PROD_TAC [`&0 <= x * (cK + &2 * sK - &1)`; `&0 < cW * (&1 / &3 - t)`] THEN
  SUBGOAL_THEN `x * (&1 - sK) <= sK / &2 /\ &3 / &5 < cW * (&1 - t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C974WS_LIN; ALL_TAC] THEN
  C974WS_PROD_TAC [`&0 < sK * (cW * (&1 - t) - &3 / &5)`; `&0 <= (cK * t) * (&1 - t)`] THEN
  C974WS_LIN)];
  (* alongW *)
  (MP_TAC(SPECL (C974WS_WTK @ [`&1`; `&0`; `cW:real`; `--t`]) ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `ABT_upper cK sK uK vK aK cW (--t) < cW` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`ABT_upper cK sK uK vK aK cW (--t) <= ABT_lower cW (--t) uW vW aK cW (--t)`;
      `ABT_lower cW (--t) uW vW aK cW (--t) < cW * &1 + --t * &0`] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_upper cK sK uK vK aK cW (--t) =
     (cK * cW - sK * t) * (uK + aK / &2) - (cK * t + sK * cW) * (vK + aK / &2) +
     aK / &2 * (abs (cK * cW - sK * t) + abs (cK * t + sK * cW))` MP_TAC THENL
   [REWRITE_TAC[C981SF_UPPER_IN_BANDS] THEN
    SUBGOAL_THEN `cW * cK + --t * sK = cK * cW - sK * t /\
                  --cW * sK + --t * cK = --(cK * t + sK * cW)` (fun th -> REWRITE_TAC[th]) THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_NEG] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `&0 <= cK * cW - sK * t` THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `ABT_upper cK sK uK vK aK cW (--t)`)) THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN DISCH_TAC THEN
    C974WS_PROD_TAC [`&0 <= (cK * cW - sK * t) * ((sK * uK + cK * (vK + aK)) - (aK * cK - &1))`;
                     `&0 < sK * (cK * t + sK * cW)`; `&0 <= (cK * cW - sK * t) * cK`;
                     `&0 <= sK * (cK * cW - sK * t)`] THEN
    C974WS_PROD_TAC [`&0 <= (sK * (cK * t + sK * cW) + (cK * cW - sK * t) * cK) * --(vK + aK)`;
                     `&0 < sK * (cW - ((cK * cW - sK * t) * (uK + aK / &2) -
                        (cK * t + sK * cW) * (vK + aK / &2) +
                        aK / &2 * ((cK * cW - sK * t) + (cK * t + sK * cW))))`;
                     `&0 < (aK - &1) * (sK * ((cK * cW - sK * t) + (cK * t + sK * cW)) +
                                         (cK * cW - sK * t) * cK)`] THEN
    SUBGOAL_THEN `(cK * cW - sK * t) * (sK * x - (&1 - cK)) = &0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sK * ((cK * cW - sK * t) * (&1 - x) + (cK * t + sK * cW) - cW) < &0`
      ASSUME_TAC THENL [C974WS_LIN; ALL_TAC] THEN
    SUBGOAL_THEN `sK * ((cK * cW - sK * t) * (&1 - x) + (cK * t + sK * cW) - cW) =
                  sK * ((&1 - sK) * (cW * x + t))` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`sK * x = &1 - cK`; `x * (&1 + cK) = sK`] THEN
      CONV_TAC REAL_RING; ALL_TAC] THEN
    C974WS_PROD_TAC [`&0 < cW * x`] THEN
    C974WS_PROD_TAC [`&0 < (&1 - sK) * (cW * x + t)`] THEN
    C974WS_PROD_TAC [`&0 <= sK * ((&1 - sK) * (cW * x + t))`] THEN
    C974WS_LIN;
    SUBGOAL_THEN `cK * cW - sK * t < &0` ASSUME_TAC THENL [C974WS_LIN; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `ABT_upper cK sK uK vK aK cW (--t)`)) THEN
    ASM_SIMP_TAC[REAL_ARITH `x < &0 ==> abs x = --x`] THEN DISCH_TAC THEN
    C974WS_PROD_TAC [`&0 < --(cK * cW - sK * t) * --uK`;
                     `&0 < (cK * t + sK * cW) * (aK - (vK + aK) - &1)`] THEN
    SUBGOAL_THEN `cK * t + sK * cW < cW` ASSUME_TAC THENL [C974WS_LIN; ALL_TAC] THEN
    C974WS_PROD_TAC [`&0 < cK * --(cK * cW - sK * t)`; `&0 < cW * (&1 - sK)`;
                     `&0 < sK * (cW - (cK * t + sK * cW))`] THEN
    SUBGOAL_THEN `cW * (cK * cK + sK * sK) = cW` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
    C974WS_LIN])]);;

(* Lean: wall_canonical_positive *)
let C974WS_WALL_CANONICAL_POSITIVE = prove
 (parse_term (Printf.sprintf "!%s %s. %s /\\ &0 < cW /\\ abs sW <= cW ==> &0 < sW"
    C974MCS_K C974MCS_W C974MCS_INV),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C974WS_KV @ C974WS_WV) C974MC_SINGLETON_QUADRANT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cR:real` (X_CHOOSE_THEN `sR:real` (X_CHOOSE_THEN `uR:real`
    (X_CHOOSE_THEN `vR:real` (X_CHOOSE_THEN `aR:real` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `c974mc_input cR sR uR vR aR cW sW uW vW aW` ASSUME_TAC THENL
   [MATCH_MP_TAC C974MC_INPUT_REFRAMEK THEN MAP_EVERY EXISTS_TAC C974WS_KV THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL ([`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] @ C974WS_WV @ [`--sW`])
    C974WS_NEGATIVE_WALL_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG] THEN
  MAP_EVERY UNDISCH_TAC [`sW <= &0`; `abs sW <= cW`] THEN REAL_ARITH_TAC);;

(* Lean: positive_frames *)
let C974WS_POSITIVE_FRAMES = prove
 (parse_term (Printf.sprintf "!%s %s. %s ==>
     ?cA sA uA vA aA cB sB uB vB aB.
       cA * cA + sA * sA = &1 /\\ &0 < aA /\\ cB * cB + sB * sB = &1 /\\ &0 < aB /\\
       aA = aK /\\ aB = aW /\\
       (!x y. linside cA sA uA vA aA x y <=> linside cK sK uK vK aK x y) /\\
       (!x y. linside cB sB uB vB aB x y <=> linside cW sW uW vW aW x y) /\\
       &0 < sA /\\ sA <= cA /\\ &0 < sB /\\ sB <= cB"
    C974MCS_K C974MCS_W C974MCS_INV),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C974WS_KV CLF_CANONICAL_FRAME) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cA:real` (X_CHOOSE_THEN `sA:real` (X_CHOOSE_THEN `uA:real`
    (X_CHOOSE_THEN `vA:real` (X_CHOOSE_THEN `aA:real` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(SPECL C974WS_WV CLF_CANONICAL_FRAME) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cB:real` (X_CHOOSE_THEN `sB:real` (X_CHOOSE_THEN `uB:real`
    (X_CHOOSE_THEN `vB:real` (X_CHOOSE_THEN `aB:real` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `c974mc_input cA sA uA vA aA cW sW uW vW aW` ASSUME_TAC THENL
   [MATCH_MP_TAC C974MC_INPUT_REFRAMEK THEN MAP_EVERY EXISTS_TAC C974WS_KV THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c974mc_input cA sA uA vA aA cB sB uB vB aB` ASSUME_TAC THENL
   [MATCH_MP_TAC C974MC_INPUT_REFRAMEW THEN MAP_EVERY EXISTS_TAC C974WS_WV THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  let qA = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
  and qB = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] in
  MP_TAC(SPECL (qA @ qB) C974WS_WALL_CANONICAL_POSITIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL (qA @ qB) C974SGN_SINGLETON_CANONICAL_POSITIVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < sB`; `abs sB <= cB`] THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  MAP_EVERY EXISTS_TAC (qA @ qB) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`abs sA <= cA`; `abs sB <= cB`] THEN REAL_ARITH_TAC);;
