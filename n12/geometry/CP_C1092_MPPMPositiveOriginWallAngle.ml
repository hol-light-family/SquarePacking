(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMPositiveOriginWallAngle.lean         *)
(* (N12Compact.C1092MPPMPositiveOriginWallAngle; Lean header: "Source only,  *)
(* uncompiled").  POSITIVE-ORIGIN-OWNED-WALL-ANGLE Theorem 1 and its literal *)
(* Q4/Q8 application.  Squares C = cC sC uC vC aC, L = cL sL uL vL aL with   *)
(* their OpenSquare invariants as hypotheses; upper / lower are ABT_upper /  *)
(* ABT_lower, supportRadius is tss_support_radius, pairRadius is            *)
(* C977CB_pairRadius, Normal is c977cc_normal.  Used: ABTransverse          *)
(* strict_bounds / ownU / ownV / separated / parallel_radius /               *)
(* transverse_radius (ABT_ names), CongruentSAT.faceSeparation_of_disjoint   *)
(* CSAT_FACESEPARATION_OF_DISJOINT, TwoFifths.Support reverse / lower_neg    *)
(* C1092TFSU_REVERSE / C1092TFSU_LOWER_NEG, WholeSupports lower_nn /         *)
(* lower_np / upper_np C1092WS_LOWER_NN / _NP / C1092WS_UPPER_NP,            *)
(* S12.square_support_bound C1092MPWS_SQUARE_SUPPORT_BOUND.  The Lean lets   *)
(* c, s, d, t, k, ell are the polynomials cC, sC, cL, --sL, cC * cL - sC * t,*)
(* sC * cL + cC * t (t = --sL after a substitution).  Conventions for the    *)
(* packing part: CP_C1092_MPPMActualPositiveOrder.ml (Ordinary p is          *)
(* c1092mpapo_ordinary, ActualFrame p C is c1092psa_frame); ActualLeftFrame  *)
(* is c1092powa_leftFrame.  Tag C1092POWA_.                                  *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualPositiveOrder.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/CongruentSAT.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C1092POWA_C5 = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let C1092POWA_L5 = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`];;
let C1092POWA_SQ = `cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\ &0 < aL`;;

(* the cone of a separating axis (the local `cone` of axes) *)
let C1092POWA_CONE = prove
 (`forall cC sC uC vC aC cL sL uL vL aL nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     nx pow 2 + ny pow 2 = &1 /\
     linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\ linside cC sC uC vC aC (--(&1)) (&0) /\
     linside cL sL uL vL aL (--(&543 / &500)) (&0) /\ linside cL sL uL vL aL (--(&1)) (&13 / &50) /\
     ABT_upper cC sC uC vC aC nx ny <= ABT_lower cL sL uL vL aL nx ny
     ==> nx < &0 /\ &0 < ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (q, x, y) ->
    MP_TAC(SPECL (q @ [x; y; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC)
   [C1092POWA_C5, `--(&1)`, `&0`; C1092POWA_L5, `--(&543 / &500)`, `&0`;
    C1092POWA_C5, `--(&1)`, `--(&13 / &50)`; C1092POWA_L5, `--(&1)`, `&13 / &50`] THEN
  CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

let C1092POWA_AXES_HYPS =
 "cC * cC + sC * sC = &1 /\\ &0 < aC /\\ cL * cL + sL * sL = &1 /\\ &0 < aL /\\ aC = aL /\\
     c977cc_normal cC sC /\\ &0 < sC /\\ c977cc_normal cL (--sL) /\\
     linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\\ linside cC sC uC vC aC (--(&1)) (&0) /\\
     linside cL sL uL vL aL (--(&543 / &500)) (&0) /\\ linside cL sL uL vL aL (--(&1)) (&13 / &50) /\\
     ldisj cC sC uC vC aC cL sL uL vL aL";;

(* close a branch with a separation fact s: either s is a goal disjunct or its cone is impossible *)
let c1092powa_close s =
  (REWRITE_TAC[s] THEN NO_TAC) ORELSE
  (let args = snd (strip_comb (lhand (concl s))) in
   let nx = el 5 args and ny = el 6 args in
   MP_TAC(SPECL (C1092POWA_C5 @ C1092POWA_L5 @ [nx; ny]) C1092POWA_CONE) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[s] THEN
     MAP_EVERY (fun t -> UNDISCH_TAC t) [`cC * cC + sC * sC = &1`; `cL * cL + sL * sL = &1`] THEN
     CONV_TAC REAL_RING;
     STRIP_TAC THEN MATCH_MP_TAC(TAUT `false ==> p`) THEN RASM_ARITH_TAC]);;

let c1092powa_sep_case nx ny rad face =
  MP_TAC(SPECL (C1092POWA_C5 @ C1092POWA_L5 @ [nx; ny]) ABT_SEPARATED) THEN
  ANTS_TAC THENL [MP_TAC face THEN MP_TAC rad THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN (fun s -> c1092powa_close s ORELSE
                                        c1092powa_close (MATCH_MP C1092TFSU_REVERSE s)));;

(* Lean: axes (private) *)
let C1092POWA_AXES = prove
 (parse_term ("!cC sC uC vC aC cL sL uL vL aL. " ^ C1092POWA_AXES_HYPS ^
   " ==> ABT_upper cC sC uC vC aC (--sC) cC <= ABT_lower cL sL uL vL aL (--sC) cC \\/
         ABT_upper cC sC uC vC aC (--cL) (--sL) <= ABT_lower cL sL uL vL aL (--cL) (--sL)"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(MATCH_MP C977CC_NORMAL_BOUNDS (ASSUME t)) THEN STRIP_TAC)
    [`c977cc_normal cC sC`; `c977cc_normal cL (--sL)`] THEN
  MP_TAC(SPECL (C1092POWA_C5 @ C1092POWA_L5) CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[C977CB_faceSep]] THEN
  let sqC = ASSUME `cC * cC + sC * sC = &1` and sqL = ASSUME `cL * cL + sL * sL = &1` in
  let cl = [`cC:real`; `sC:real`; `aC:real`; `cL:real`; `sL:real`; `aL:real`]
  and lc = [`cL:real`; `sL:real`; `aL:real`; `cC:real`; `sC:real`; `aC:real`] in
  let case n1 n2 rad = POP_ASSUM(c1092powa_sep_case n1 n2 rad) in
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [case `cC:real` `sC:real` (MP (SPECL cl ABT_PARALLEL_RADIUS) sqC);
    case `--sC` `cC:real` (MP (SPECL cl ABT_TRANSVERSE_RADIUS) sqC);
    case `cL:real` `sL:real` (MP (SPECL lc ABT_PARALLEL_RADIUS) sqL);
    case `--sL` `cL:real` (MP (SPECL lc ABT_TRANSVERSE_RADIUS) sqL)]);;

(* the transverse branch of steep, scalar form (k = c * d - s * t, ell = s * d + c * t) *)
let C1092POWA_TRANSVERSE_SCALARS = prove
 (`forall c s d t uL vL aL vC.
     c * c + s * s = &1 /\ d * d + t * t = &1 /\ &7 / &10 <= c /\ s <= c /\ &0 < s /\
     &12 / &13 <= d /\ d <= &1 /\ &0 < t /\ &1 < aL /\
     --(&2) <= d * uL + t * vL /\ vL + aL <= d - (&543 / &500) * t /\
     s < vC + aL /\
     vC + aL <= --(s * d + c * t) * (uL + aL) + (c * d - s * t) * vL
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s * d + c * t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d * (vC + aL) <= d * (--(s * d + c * t) * (uL + aL) + (c * d - s * t) * vL)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(s * d + c * t) * --(&2) <= (s * d + c * t) * (d * uL + t * vL)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * (vL + aL) <= c * (d - (&543 / &500) * t)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d * s < d * (vC + aL)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (aL - &1) * ((s * d + c * t) * d + c)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (c * t) * (d - &457 / &500)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `s * d <= s` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `s * d <= s * &1 ==> s * d <= s`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - d) * (s * d - c) <= &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x * --y ==> x * y <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((s * d + c * t) * t + (c * d - s * t) * d) * vL = c * vL` ASSUME_TAC THENL
   [UNDISCH_TAC `d * d + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  POP_ASSUM_LIST(fun ths -> MP_TAC(end_itlist CONJ (filter (fun th ->
    let c = concl th in is_binop `(<):real->real->bool` c || is_binop `(<=):real->real->bool` c || is_eq c) ths))) THEN
  CONV_TAC REAL_ARITH);;

(* the longitudinal branch of steep, scalar form *)
let C1092POWA_LONGITUDINAL_SCALARS = prove
 (`forall c s d t uC vC aL.
     c * c + s * s = &1 /\ &7 / &10 <= c /\ c <= &1 /\ &0 < s /\ &12 / &13 <= d /\ &0 < t /\ &1 < aL /\
     uC + aL <= --(&13 / &50) * c /\ s < vC + aL /\
     (&49 / &120) * d <= c * d - s * t /\
     --(c * d - s * t) * uC + (s * d + c * t) * (vC + aL) < (&543 / &500) * d
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c * d - s * t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s * d + c * t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(c * d - s * t) * (uC + aL) >= --(c * d - s * t) * (--(&13 / &50) * c)` ASSUME_TAC THENL
   [REWRITE_TAC[real_ge; REAL_MUL_LNEG; REAL_LE_NEG2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(s * d + c * t) * s < (s * d + c * t) * (vC + aL)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (aL - &1) * (c * d - s * t)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&13 / &50) * (c * d - s * t) <= (&1 - (&37 / &50) * c) * (c * d - s * t)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d * (c * c + s * s) = d` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  POP_ASSUM_LIST(fun ths -> MP_TAC(end_itlist CONJ (filter (fun th ->
    let c = concl th in is_binop `(<):real->real->bool` c || is_binop `(<=):real->real->bool` c ||
                        is_binop `(>=):real->real->bool` c || is_eq c) ths))) THEN
  CONV_TAC REAL_ARITH);;

let C1092POWA_STEEP_HYPS =
 "cC * cC + sC * sC = &1 /\\ &0 < aC /\\ cL * cL + sL * sL = &1 /\\ &0 < aL /\\
     &1 < aC /\\ aC = aL /\\ c977cc_normal cC sC /\\ &0 < sC /\\ c977cc_normal cL (--sL) /\\
     linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\\ linside cC sC uC vC aC (--(&1)) (&0) /\\
     uC + aC <= --(&13 / &50) * cC /\\
     linside cL sL uL vL aL (--(&543 / &500)) (&0) /\\ linside cL sL uL vL aL (--(&1)) (&13 / &50) /\\
     ~linside cL sL uL vL aL (--(&543 / &500)) (&1) /\\
     (!x y. linside cL sL uL vL aL x y ==> --(&2) <= x) /\\
     ldisj cC sC uC vC aC cL sL uL vL aL";;

let C1092POWA_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092POWA_KPOS_TAC =
  MP_TAC(ASSUME `&49 / &120 * cL <= cC * cL - sC * t`) THEN MP_TAC(ASSUME `&12 / &13 <= cL`) THEN
  REAL_ARITH_TAC;;
let C1092POWA_SIGN_TAC =
  FIRST [REAL_ARITH_TAC; C1092POWA_KPOS_TAC;
         MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> --(x + y) <= &0`) THEN CONJ_TAC THEN
           MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
         MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> --y <= &0`) THEN C1092POWA_KPOS_TAC;
         MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];;
let C1092POWA_GET_TAC f = FIRST_X_ASSUM(fun th -> if f (concl th) then MP_TAC th else NO_TAC);;
let c1092powa_head_is c tm = is_comb tm && fst (strip_comb tm) = c;;
let C1092POWA_DHEIGHT_TAC =
  UNDISCH_TAC `linside cC sC uC vC aC (--(&1)) (&0)` THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

(* Lean: steep *)
let C1092POWA_STEEP = prove
 (parse_term ("!cC sC uC vC aC cL sL uL vL aL. " ^ C1092POWA_STEEP_HYPS ^ " ==> &5 * cL < &12 * --sL"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092POWA_C5 @ C1092POWA_L5) C1092POWA_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MAP_EVERY (fun t -> MP_TAC(MATCH_MP C977CC_NORMAL_BOUNDS (ASSUME t)) THEN STRIP_TAC)
    [`c977cc_normal cC sC`; `c977cc_normal cL (--sL)`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o check (fun th -> concl th = `c977cc_normal cC sC`)) THEN
  (* the wall support and the supports of both branches, before the substitution of sL *)
  MP_TAC(SPECL (C1092POWA_L5 @ [`--(&1)`; `&0`; `&2`]) C1092MPWS_SQUARE_SUPPORT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`] o check (fun th -> is_forall (concl th) &&
      is_imp (snd (strip_forall (concl th))) && not (mem `l:real` (frees (concl th))))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL (C1092POWA_L5 @ [`&1`; `&0`; `cL:real`; `--sL`]) C1092WS_LOWER_NN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `--(&2) <= cL * uL + --sL * vL` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_comb (lhs (concl th)) &&
        fst (strip_comb (lhs (concl th))) = `ABT_lower` then SUBST1_TAC (SYM th) else NO_TAC) THEN
    UNDISCH_TAC `--(&1) * lcx cL sL uL vL aL + &0 * lcy cL sL uL vL aL +
                 tss_support_radius cL sL aL (--(&1)) (&0) <= &2` THEN
    REWRITE_TAC[ABT_lower; tss_support_radius; REAL_MUL_LZERO; REAL_ADD_RID; REAL_MUL_LNEG;
                REAL_MUL_LID; REAL_NEG_NEG; REAL_ABS_NEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL C1092POWA_C5 ABT_OWNV) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092POWA_L5 @ [`--(&543 / &500)`; `&0`; `--cL`; `--sL`]) ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cL * cL + sL * sL = &1` THEN CONV_TAC REAL_RING; STRIP_TAC] THEN
  (* bad, t := --sL *)
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  X_CHOOSE_THEN `t:real` SUBST_ALL_TAC (MESON[REAL_NEG_NEG] `exists t:real. sL = --t`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NEG_NEG]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aL`)) THEN
  SUBGOAL_THEN `cL * cL + t * t = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `cL * cL + --t * --t = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&12 / &13 <= cL` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `t <= &5 / &13` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `~linside cL (--t) uL vL aC (--(&1)) (&0)` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cC sC uC vC aC cL (--t) uL vL aC` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`--(&1)`; `&0`]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `uL + aC <= --cL` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside cL (--t) uL vL aC (--(&1)) (&0)` THEN REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN REWRITE_TAC[linside] THEN C1092POWA_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `t = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `cL = &1` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `cL <= &1 /\ &1 <= cL ==> cL = &1`) THEN
      CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
    C1092POWA_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `vL + aC <= cL - (&543 / &500) * t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside cL (--t) uL vL aC (--(&543 / &500)) (&1)` THEN REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN REWRITE_TAC[linside] THEN C1092POWA_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&49 / &120) * cL <= cC * cL - sC * t` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (cC - sC) * t /\ &0 <= cC * (&5 * cL - &12 * t) /\ &0 <= cL * (cC - &7 / &10)`
      MP_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [(* transverse *)
    MP_TAC(SPECL [`cL:real`; `--t`; `uL:real`; `vL:real`; `aC:real`; `--sC`; `cC:real`;
                  `--(sC * cL + cC * t)`; `cC * cL - sC * t`] C1092WS_LOWER_NP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092POWA_SIGN_TAC; DISCH_TAC] THEN
    MATCH_MP_TAC (SPECL [`cC:real`; `sC:real`; `cL:real`; `t:real`; `uL:real`; `vL:real`; `aC:real`; `vC:real`]
      C1092POWA_TRANSVERSE_SCALARS) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [C1092POWA_DHEIGHT_TAC;
      C1092POWA_GET_TAC (fun c -> is_binop `(<=):real->real->bool` c && c1092powa_head_is `ABT_upper` (lhand c)) THEN
      ASM_REWRITE_TAC[]];
    (* longitudinal *)
    MP_TAC(SPECL (C1092POWA_C5 @ [`--cL`; `t:real`; `--(cC * cL - sC * t)`; `sC * cL + cC * t`]) C1092WS_UPPER_NP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092POWA_SIGN_TAC; DISCH_TAC] THEN
    MATCH_MP_TAC (SPECL [`cC:real`; `sC:real`; `cL:real`; `t:real`; `uC:real`; `vC:real`; `aC:real`]
      C1092POWA_LONGITUDINAL_SCALARS) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [C1092POWA_DHEIGHT_TAC;
      C1092POWA_GET_TAC (fun c -> is_binop `(<=):real->real->bool` c && c1092powa_head_is `ABT_upper` (lhand c)) THEN
      C1092POWA_GET_TAC (fun c -> is_binop `(<):real->real->bool` c && c1092powa_head_is `ABT_lower` (lhand c) &&
                                  rand (lhand c) = `t:real`) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]);;

(* Lean: ActualLeftFrame (structure) *)
let c1092powa_leftFrame = new_definition
 `c1092powa_leftFrame (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real)
                      (cL:real) (sL:real) (uL:real) (vL:real) (aL:real) <=>
    aL = l /\
    forall x y. linside cL sL uL vL aL x y <=>
          linside (ooc c1 c2 a b l (EL 8 c1092wc_code)) (oos c1 c2 a b l (EL 8 c1092wc_code))
                  (oou c1 c2 a b l (EL 8 c1092wc_code)) (oov c1 c2 a b l (EL 8 c1092wc_code)) l
                  (&2 + x) (&2 + y)`;;

(* Lean: actual_steep *)
let C1092POWA_ACTUAL_STEEP = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC cL sL uL vL aL. %s /\\ ~%s /\\ %s /\\
      cC * cC + sC * sC = &1 /\\ &0 < aC /\\ c1092psa_frame c1 c2 a b l cC sC uC vC aC /\\
      c977cc_normal cC sC /\\ &0 < sC /\\
      cL * cL + sL * sL = &1 /\\ &0 < aL /\\ c1092powa_leftFrame c1 c2 a b l cL sL uL vL aL /\\
      c977cc_normal cL (--sL)
      ==> &5 * cL < &12 * --sL"
    C1092AE_P C1092MPAPO_HYPS (c1092mppe_in 4 "&87 / &50" "&2") (c1092mppe_in 4 "&1" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPAPO_ORD_TAC THEN
  c1092mpapo_use C1092MPAPO_FAR_POINTS THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAPO_CV) C1092PSA_MISSING_PROFILE) THEN
  ASM_REWRITE_TAC[c1092mmpf_faces] THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MPPE_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092powa_leftFrame; c1092psa_frame] o
    check (fun th -> c1092mpapo_head `c1092powa_leftFrame` th || c1092mpapo_head `c1092psa_frame` th))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l` || concl th = `aL:real = l`))) THEN
  MATCH_MP_TAC (SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `l:real`;
                       `cL:real`; `sL:real`; `uL:real`; `vL:real`; `l:real`] C1092POWA_STEEP) THEN
  ASM_REWRITE_TAC[ldisj] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  let wa = c1092psa_wa () in
  REWRITE_TAC[c1092psa_seed 8 (`&457 / &500`, `&2`); CONJUNCT1 wa;
              c1092psa_excl 8 3 (c1092psa_seed 3 (`&457 / &500`, `&3`)); c1092psa_apart 4 8] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[lcont] (c1092psa_box 8))) THEN
  REAL_ARITH_TAC);;
