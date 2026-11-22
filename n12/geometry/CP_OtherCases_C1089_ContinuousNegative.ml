(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/ContinuousNegative.lean       *)
(* (N12Compact.Completion.OtherCases.C1089.ContinuousNegative).  The         *)
(* remaining negative-frame step of C1089-CONTINUOUS-REDUCTION Theorem 3.    *)
(* InsideContainer: lcont; InwardMissingProfile.profile: C1092IMP_PROFILE;   *)
(* NearCrossing.point: C1092NCR_POINT; InwardCrossingConflict.impossible:    *)
(* C1092ICC_IMPOSSIBLE; half: C1092WPS_half.  The chart                      *)
(* translate (swap X) (-2) (-2) of X = (c, s, u, v, a) is the 5-tuple        *)
(* (c, --s, v + &2 * c - &2 * s, u + &2 * c + &2 * s, a).                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_NearCrossing.ml";;
needs "n12/geometry/CP_C1092_InwardMissingProfile.ml";;
needs "n12/geometry/CP_C1092_InwardCrossingConflict.ml";;
needs "n12/geometry/CP_C1092_RigidCharts.ml";;

let OCCN_LIN_TAC = NLIN_TAC ~deg2:false [];;

let OCCN_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN OCCN_LIN_TAC; DISCH_TAC];;

(* Lean: S12.inside_distance_bound (local copy) *)
let OCCN_INSIDE_DISTANCE_BOUND = prove
 (`forall c s u v a x y x' y'.
     c * c + s * s = &1 /\ &0 < a /\
     linside c s u v a x y /\ linside c s u v a x' y'
     ==> (x - x') pow 2 + (y - y') pow 2 < &2 * a pow 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x - x') pow 2 + (y - y') pow 2 =
     ((c * x + s * y) - (c * x' + s * y')) pow 2 +
     ((--s * x + c * y) - (--s * x' + c * y')) pow 2` SUBST1_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ABBREV_TAC `du = (c * x + s * y) - (c * x' + s * y')` THEN
  ABBREV_TAC `dv = (--s * x + c * y) - (--s * x' + c * y')` THEN
  SUBGOAL_THEN `&0 < a - du /\ &0 < a + du /\ &0 < a - dv /\ &0 < a + dv`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["du"; "dv"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN NLIN_TAC []);;

(* the chart translate (swap X) (-2) (-2) *)
let OCCN_CHART = prove
 (`forall c s u v a x y.
     linside c (--s) (v + &2 * c - &2 * s) (u + &2 * c + &2 * s) a x y <=>
     linside c s u v a (y - &2) (x - &2)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: right_box (private) *)
let OCCN_RIGHT_BOX = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ a <= &7 / &5 /\
     (forall x y. linside c s u v a x y ==> x <= &4) /\
     linside c s u v a (&1543 / &500) (&2)
     ==> lcont c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[lcont] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `x:real`; `y:real`; `&1543 / &500`; `&2`] OCCN_INSIDE_DISTANCE_BOUND) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
  SUBGOAL_THEN `x <= &4` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  OCCN_LE_MUL_TAC `&7 / &5 - a` `&7 / &5 + a` THEN
  MP_TAC(SPEC `y - &2` REAL_LE_SQUARE) THEN MP_TAC(SPEC `x - &1543 / &500` REAL_LE_SQUARE) THEN
  REPEAT DISCH_TAC THEN
  REPEAT CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THENL
   [OCCN_LE_MUL_TAC `--x` `&3086 / &500 - x`;
    OCCN_LE_MUL_TAC `--y` `&4 - y`;
    OCCN_LE_MUL_TAC `y - &4` `y:real`] THEN
  OCCN_LIN_TAC);;

(* Lean: impossible *)
let OCCN_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cW sW uW vW aW cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aC /\ aC = aW /\ aC = aB /\ &0 < cC /\ sC <= &0 /\ --sC <= cC /\
     linside cC sC uC vC aC (&7 / &20) (&7 / &20) /\
     linside cC sC uC vC aC (&0) (&13 / &50) /\
     linside cC sC uC vC aC (&13 / &50) (&0) /\
     ~linside cC sC uC vC aC (&0) (&0) /\
     ~linside cC sC uC vC aC (&1) (&2 / &5) /\
     ~linside cC sC uC vC aC (&2 / &5) (&1) /\
     ~linside cC sC uC vC aC (--(&7 / &20)) (&7 / &20) /\
     linside cW sW uW vW aW (&543 / &500) (&0) /\
     linside cW sW uW vW aW (&1) (&13 / &50) /\
     linside cW sW uW vW aW (&1) (&39 / &100) /\
     (forall x y. linside cW sW uW vW aW x y ==> x <= &2) /\ &0 <= lcy cW sW uW vW aW /\
     (forall x y. linside cB sB uB vB aB x y ==> y <= &2) /\
     linside cB sB uB vB aB (&0) (&543 / &500) /\
     linside cB sB uB vB aB (&2 / &5) (&1) /\
     ldisj cC sC uC vC aC cW sW uW vW aW /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `aC:real = aW` || concl th = `aC:real = aB`))) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092IMP_PROFILE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[C1092IMP_profile] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c977cc_normal cC (--sC)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
    UNDISCH_TAC `cC * cC + sC * sC = &1` THEN UNDISCH_TAC `--sC <= cC` THEN
    UNDISCH_TAC `sC < &0` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  SUBGOAL_THEN `aC <= &7 / &5` ASSUME_TAC THENL [OCCN_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`;
                `cC:real`; `--sC`] C1092NCR_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_NEG_NEG]; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + cC` ASSUME_TAC THENL [OCCN_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + cC) * (--sC / (&1 + cC)) = --sC /\
                --sC * (--sC / (&1 + cC)) = &1 - cC` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `cC * cC + sC * sC = &1` THEN UNDISCH_TAC `&0 < &1 + cC` THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= --sC / (&1 + cC)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THEN OCCN_LIN_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `C1092WPS_half`)) (concl th))) THEN
  REWRITE_TAC[C1092WPS_half] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cB:real`; `--sB`; `vB + &2 * cB - &2 * sB`; `uB + &2 * cB + &2 * sB`; `aC:real`]
    OCCN_RIGHT_BOX) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OCCN_CHART] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST [UNDISCH_TAC `cB * cB + sB * sB = &1` THEN REAL_ARITH_TAC;
           REPEAT GEN_TAC THEN DISCH_TAC THEN
           SUBGOAL_THEN `x - &2 <= &2` MP_TAC THENL [ASM_MESON_TAC[]; REAL_ARITH_TAC];
           OCCN_LIN_TAC];
    DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`; `vC + &2 * cC - &2 * sC`; `uC + &2 * cC + &2 * sC`; `aC:real`;
                `cB:real`; `--sB`; `vB + &2 * cB - &2 * sB`; `uB + &2 * cB + &2 * sB`; `aC:real`;
                `--sC / (&1 + cC)`] C1092ICC_IMPOSSIBLE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OCCN_CHART; ldisj] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[REAL_ARITH `(&2 + z) - &2 = z`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           (fun (asl,w as g) -> if is_forall w then ASM_MESON_TAC[] g else NO_TAC g);
           UNDISCH_TAC `cC * cC + sC * sC = &1` THEN REAL_ARITH_TAC;
           UNDISCH_TAC `cB * cB + sB * sB = &1` THEN REAL_ARITH_TAC;
           OCCN_LIN_TAC];
    REWRITE_TAC[]]);;
