(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/C974WallSignScalars.lean       *)
(* (N12Compact.Completion.OtherCases.C983.C974MissingCorner).  The           *)
(* continuous rectangle estimate (12)--(13) of MISSING-CORNER-WALL-SIGN      *)
(* §1.6.  The private wallPolynomial is c974wss_wallpoly.  Tag C974WSS_.     *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_C974SingletonSign.ml";;

(* Lean: quadrant_half *)
let C974WSS_QUADRANT_HALF = prove
 (`forall l h. &0 < l /\ &0 < h /\ l pow 2 + h pow 2 = &1
         ==> let x = h / (&1 + l) in
             &0 < x /\ h * x = &1 - l /\ l = (&1 - x pow 2) / (&1 + x pow 2) /\
             h = (&2 * x) / (&1 + x pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `x = h / (&1 + l)` THEN
  SUBGOAL_THEN `&0 < &1 + l` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < l` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x * (&1 + l) = h` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    UNDISCH_TAC `&0 < &1 + l` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h * x = &1 - l` ASSUME_TAC THENL
   [MP_TAC(SPECL [`h * x`; `&1 - l`; `&1 + l`] REAL_EQ_MUL_RCANCEL) THEN
    SUBGOAL_THEN `~(&1 + l = &0)` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `&0 < &1 + l` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY UNDISCH_TAC [`x * (&1 + l) = h`; `l pow 2 + h pow 2 = &1`] THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + x pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [EXPAND_TAC "x" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
    MAP_EVERY UNDISCH_TAC [`x * (&1 + l) = h`; `h * x = &1 - l`] THEN CONV_TAC REAL_RING;
    MAP_EVERY UNDISCH_TAC [`x * (&1 + l) = h`; `h * x = &1 - l`] THEN CONV_TAC REAL_RING]);;

(* Lean: wallPolynomial (private def) *)
let c974wss_wallpoly = new_definition
 `c974wss_wallpoly (x:real) y =
    x pow 2 * (&2 - x) + y * (&1 - &4 * x - x pow 2) +
    y pow 2 * (--(&2) * x pow 3 + &6 * x pow 2 - &2) +
    y pow 3 * (--(&3) * x pow 2 - &4 * x + &3) +
    y pow 4 * (--(x pow 3) + &4 * x pow 2 - &4 * x - &2)`;;

(* a polynomial fact: linear, a product of two nonnegative factors, or nlinarith *)
let C974WSS_FACTS_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [FIRST [NLIN_TAC ~deg2:false [];
            MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
              FIRST [MATCH_ACCEPT_TAC REAL_LE_POW_2;
                     MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[];
                     NLIN_TAC ~deg2:false []];
            MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[];
            NLIN_TAC [];
            (fun g -> failwith ("C974WSS_FACTS_TAC: " ^ string_of_term t))];
     ALL_TAC]) tms;;

(* Lean: wallPolynomial_pos (private) *)
let C974WSS_WALLPOLY_POS = prove
 (`forall x y. &0 < x /\ x <= &2 / &3 /\ &0 <= y /\ y <= &1 / &7 ==> &0 < c974wss_wallpoly x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c974wss_wallpoly] THEN
  C974WSS_FACTS_TAC
   [`x pow 2 <= &4 / &9`; `x pow 3 <= &8 / &27`;
    `&0 <= x pow 2 * (&6 - &2 * x)`;
    `--(&2) <= --(&2) * x pow 3 + &6 * x pow 2 - &2`;
    `--(&1) <= --(&3) * x pow 2 - &4 * x + &3`;
    `--(&5) <= --(x pow 3) + &4 * x pow 2 - &4 * x - &2`;
    `y pow 2 <= y / &7`;
    `&0 <= y * (y / &7 - y pow 2)`; `y pow 3 <= y / &49`;
    `&0 <= y * (y / &49 - y pow 3)`; `y pow 4 <= y / &343`;
    `&2 * y pow 2 + y pow 3 + &5 * y pow 4 <= y / &3`;
    `&0 <= y pow 2 * ((--(&2) * x pow 3 + &6 * x pow 2 - &2) + &2)`;
    `&0 <= y pow 3`; `&0 <= y pow 4`;
    `&0 <= y pow 3 * ((--(&3) * x pow 2 - &4 * x + &3) + &1)`;
    `&0 <= y pow 4 * ((--(x pow 3) + &4 * x pow 2 - &4 * x - &2) + &5)`;
    `&0 <= x pow 2 * (&2 - x - y - &25 / &21)`;
    `&0 <= y * (&1 / &7 - y)`] THEN
  SUBGOAL_THEN
   `(&25 / &21) * (x - &42 * y / &25) pow 2 + (&14 / &75) * y <=
    x pow 2 * (&2 - x) + y * (&1 - &4 * x - x pow 2) +
    y pow 2 * (--(&2) * x pow 3 + &6 * x pow 2 - &2) +
    y pow 3 * (--(&3) * x pow 2 - &4 * x + &3) +
    y pow 4 * (--(x pow 3) + &4 * x pow 2 - &4 * x - &2)` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_CASES_TAC `y = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    NLIN_FACTS_TAC [] [`&0 < x pow 2`; `&0 < x pow 2 * (&2 - x)`] THEN
    NLIN_TAC ~deg2:false [];
    SUBGOAL_THEN `&0 < y` ASSUME_TAC THENL
     [UNDISCH_TAC `~(y = &0)` THEN UNDISCH_TAC `&0 <= y` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC ~deg2:false [SQ_NONNEG `x - &42 * y / &25`]]);;

(* Lean: negative_wall_scalar *)
let C974WSS_NEGATIVE_WALL_SCALAR = prove
 (`forall l h d t x y.
     &0 < x /\ x <= &2 / &3 /\ &0 <= y /\ y <= &1 / &7 /\
     l = (&1 - x pow 2) / (&1 + x pow 2) /\ h = (&2 * x) / (&1 + x pow 2) /\
     d = (&1 - y pow 2) / (&1 + y pow 2) /\ t = (&2 * y) / (&1 + y pow 2)
     ==> &0 < &1 - l - x + (l * d - h * t) * (&1 - d) +
              (l * t + h * d) * (&1 - t - d / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + x pow 2 /\ &0 < &1 + y pow 2` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN MP_TAC(SPEC `y:real` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `l * (&1 + x pow 2) = &1 - x pow 2 /\ h * (&1 + x pow 2) = &2 * x /\
                d * (&1 + y pow 2) = &1 - y pow 2 /\ t * (&1 + y pow 2) = &2 * y`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 - l - x + (l * d - h * t) * (&1 - d) + (l * t + h * d) * (&1 - t - d / &2)) *
    ((&1 + x pow 2) * (&1 + y pow 2) pow 2) = c974wss_wallpoly x y` ASSUME_TAC THENL
   [REWRITE_TAC[c974wss_wallpoly] THEN
    MAP_EVERY UNDISCH_TAC
     [`l * (&1 + x pow 2) = &1 - x pow 2`; `h * (&1 + x pow 2) = &2 * x`;
      `d * (&1 + y pow 2) = &1 - y pow 2`; `t * (&1 + y pow 2) = &2 * y`] THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`x:real`; `y:real`] C974WSS_WALLPOLY_POS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && rand (concl th) = `c974wss_wallpoly x y`
                          then SUBST1_TAC(SYM th) else NO_TAC) THEN
  SUBGOAL_THEN `&0 < (&1 + x pow 2) * (&1 + y pow 2) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP] THEN
  SPEC_TAC(`(&1 + x pow 2) * (&1 + y pow 2) pow 2`, `D:real`) THEN
  SPEC_TAC(`&1 - l - x + (l * d - h * t) * (&1 - d) + (l * t + h * d) * (&1 - t - d / &2)`,
           `E:real`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= --E * D` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 < E * D` THEN REAL_ARITH_TAC);;
