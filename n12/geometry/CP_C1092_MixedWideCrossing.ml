(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MixedWideCrossing.lean                    *)
(* (N12Compact.C1092MixedWideCrossing).  A genuine mixed wall forces the     *)
(* missing half-angle crossing in its actual inward neighbour.               *)
(* Squares: C = cC sC uC vC aC (central), W = cW sW uW vW aW (wall).         *)
(* lower/upper: ABT_lower/ABT_upper; centerY: lcy; SAT step: ABT_FOUR_AXES;  *)
(* MixedWideWall.canonical_profile: C1092MWW_CANONICAL_PROFILE;              *)
(* MixedWideCrossingScalars: C1092MWCS_SMALL / C1092MWCS_MARGINS;            *)
(* square_support_bound: C1092MPWS_SQUARE_SUPPORT_BOUND; support formulas:   *)
(* C1092WS_FORMULAS.                                                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/CP_C1092_MixedWideWall.ml";;
needs "n12/geometry/CP_C1092_MixedWideCrossingScalars.ml";;
needs "n12/geometry/CP_C1092_MMMP_PhysicalWallSupport.ml";;

let C1092MWC_LIN_TAC (asl,w as g) =
  let rec ok t = is_real_rel t || (is_neg t && is_real_rel (rand t)) ||
                 (is_conj t && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

(* REAL_ARITH from the listed assumptions only *)
let C1092MWC_ARITH_WITH tms =
  MAP_EVERY (fun t -> MP_TAC(ASSUME t)) tms THEN REAL_ARITH_TAC;;

let C1092MWC_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092MWC_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [MATCH_ACCEPT_TAC REAL_LE_POW_2; NLIN_TAC ~deg2:false []; C1092MWC_LIN_TAC]; ALL_TAC];;

let C1092MWC_FRAME_POS = prove
 (`forall x y. x * x + y * y = &1 /\ abs y <= x ==> &0 < x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_ABS_BOUNDS] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (x - y) * (x + y) /\ &0 <= --x * x` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: centered_frame *)
let C1092MWC_CENTERED_FRAME = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a
     ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\
           &0 < c' /\ abs s' <= c' /\ a' = a /\
           lcy c' s' u' v' a' = lcy c s u v a /\
           (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y)`,
  let tac wits = MAP_EVERY EXISTS_TAC wits THEN
    REWRITE_TAC[linside; lcy] THEN REPEAT CONJ_TAC THEN
    TRY(REPEAT GEN_TAC THEN REAL_ARITH_TAC) THEN
    TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC C1092MWC_FRAME_POS THEN
    FIRST (map (fun w -> EXISTS_TAC w THEN ASM_REAL_ARITH_TAC)
             [`s:real`; `c:real`; `--s:real`; `--c:real`]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `abs s <= c` THENL
  [tac [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]; ALL_TAC] THEN
  ASM_CASES_TAC `abs c <= --s` THENL
  [tac [`--s:real`; `c:real`; `v:real`; `--u - a:real`; `a:real`]; ALL_TAC] THEN
  ASM_CASES_TAC `abs s <= --c` THENL
  [tac [`--c:real`; `--s:real`; `--u - a:real`; `--v - a:real`; `a:real`]; ALL_TAC] THEN
  tac [`s:real`; `--c:real`; `--v - a:real`; `u:real`; `a:real`]);;

(* Lean: negative_axes *)
let C1092MWC_NEGATIVE_AXES = prove
 (`forall cC sC uC vC aC cW sW uW vW aW rho.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     aC = aW /\ &0 < cC /\ sC < &0 /\ &0 < cW /\ sW < &0 /\
     linside cC sC uC vC aC (&13 / &50) (&0) /\ &2 / &5 < rho /\
     linside cC sC uC vC aC (&1) rho /\
     linside cW sW uW vW aW (&543 / &500) (&0) /\
     linside cW sW uW vW aW (&1) (&2 / &5) /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> uC + aC <= ABT_lower cW sW uW vW aW cC sC \/
         ABT_upper cC sC uC vC aC cW sW <= uW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  SUBGOAL_THEN `cC pow 2 + sC pow 2 = &1 /\ (--sC) pow 2 + cC pow 2 = &1 /\
                cW pow 2 + sW pow 2 = &1 /\ (--sW) pow 2 + cW pow 2 = &1`
  STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  let sb (c,s,u,v) (x,y) (nx,ny) =
    MP_TAC(SPECL [c; s; u; v; `aC:real`; x; y; nx; ny] ABT_STRICT_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] in
  let qC = (`cC:real`,`sC:real`,`uC:real`,`vC:real`)
  and qW = (`cW:real`,`sW:real`,`uW:real`,`vW:real`) in
  sb qW (`&543 / &500`,`&0`) (`cC:real`,`sC:real`) THEN
  sb qW (`&1`,`&2 / &5`) (`--sC:real`,`cC:real`) THEN
  sb qW (`&543 / &500`,`&0`) (`--sC:real`,`cC:real`) THEN
  sb qC (`&13 / &50`,`&0`) (`cW:real`,`sW:real`) THEN
  sb qC (`&1`,`rho:real`) (`--sW:real`,`cW:real`) THEN
  sb qC (`&13 / &50`,`&0`) (`--sW:real`,`cW:real`) THEN
  C1092MWC_PROD `&0 < cC * (rho - &2 / &5)` THEN
  C1092MWC_PROD `&0 < cW * (rho - &2 / &5)` THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] ABT_FOUR_AXES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC; C1092MWC_LIN_TAC]);;

(* Lean: support_impossible *)
let C1092MWC_SUPPORT_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cW sW uW vW aW c s z rho.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     cC = c /\ sC = --s /\ &1 < aC /\ aC <= &1001 / &1000 /\ aC = aW /\
     &0 < c /\ &0 < s /\ z * (&1 + c) = s /\ s * z = &1 - c /\
     linside cC sC uC vC aC (&13 / &50) (&0) /\
     linside cC sC uC vC aC (&7 / &20) (&7 / &20) /\
     --z <= uC /\ linside cC sC uC vC aC (&1) rho /\ &2 / &5 < rho /\
     &0 <= z /\ z < &53 / &500 /\ &97 / &100 < c /\ s < &21 / &100 /\
     z <= (&51 / &100) * s /\
     linside cW sW uW vW aW (&543 / &500) (&0) /\
     linside cW sW uW vW aW (&1) (--(&39 / &100)) /\
     linside cW sW uW vW aW (&1) (&2 / &5) /\
     ~linside cW sW uW vW aW (&1) (--(&2 / &5)) /\
     (forall x y. linside cW sW uW vW aW x y ==> x <= &2) /\ lcy cW sW uW vW aW <= &0 /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `cC:real = c`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sC:real = --s`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  SUBGOAL_THEN `c pow 2 + s pow 2 = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `c * c + --s * --s = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~linside cW sW uW vW aC (&7 / &20) (&7 / &20)` ASSUME_TAC THENL
  [UNDISCH_TAC `ldisj c (--s) uC vC aC cW sW uW vW aC` THEN REWRITE_TAC[ldisj] THEN
   DISCH_THEN(MP_TAC o SPECL [`&7 / &20`; `&7 / &20`]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`]
    C1092MWC_CENTERED_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`d:real`; `sV:real`; `uV:real`; `vV:real`; `aV:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aV:real = aC`)) THEN
  MP_TAC(SPECL [`d:real`; `sV:real`; `uV:real`; `vV:real`; `aC:real`]
    C1092MWW_CANONICAL_PROFILE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `ldisj c (--s) uC vC aC d sV uV vV aC /\
                linside d sV uV vV aC (&543 / &500) (&0) /\
                linside d sV uV vV aC (&1) (&2 / &5) /\
                (forall x y. linside d sV uV vV aC x y ==> x <= &2)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[ldisj] THEN ASM_MESON_TAC[ldisj]; ALL_TAC] THEN
  SUBGOAL_THEN `exists t. sV = --t` (X_CHOOSE_THEN `t:real` SUBST_ALL_TAC) THENL
  [EXISTS_TAC `--sV:real` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d pow 2 + t pow 2 = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `d * d + --t * --t = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `z:real`] C1092MWCS_MARGINS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MWC_LIN_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--s:real`; `uC:real`; `vC:real`; `aC:real`;
                `d:real`; `--t:real`; `uV:real`; `vV:real`; `aC:real`; `rho:real`]
    C1092MWC_NEGATIVE_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MWC_LIN_TAC; ALL_TAC] THEN
  (* support formulas *)
  C1092MWC_PROD `&0 < c * d` THEN C1092MWC_PROD `&0 <= s * t` THEN
  SUBGOAL_THEN `ABT_lower d (--t) uV vV aC c (--s) =
                (c * d + s * t) * uV + (c * t - s * d) * vV` ASSUME_TAC THENL
  [MP_TAC(SPECL [`d:real`; `--t:real`; `uV:real`; `vV:real`; `aC:real`; `c:real`; `--s:real`]
     C1092WS_FORMULAS) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
   SUBGOAL_THEN `min (c * d + --s * --t) (&0) = &0 /\ min (--c * --t + --s * d) (&0) = &0`
   (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN C1092MWC_LIN_TAC; REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `ABT_upper c (--s) uC vC aC d (--t) =
                (c * d + s * t) * (uC + aC) - (c * t - s * d) * vC` ASSUME_TAC THENL
  [MP_TAC(SPECL [`c:real`; `--s:real`; `uC:real`; `vC:real`; `aC:real`; `d:real`; `--t:real`]
     C1092WS_FORMULAS) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
   SUBGOAL_THEN `max (d * c + --t * --s) (&0) = c * d + s * t /\
                 max (--d * --s + --t * c) (&0) = &0`
   (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN C1092MWC_LIN_TAC; REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `d * (uV + aC) + t * (vV + aC) <= &2` ASSUME_TAC THENL
  [MP_TAC(SPECL [`d:real`; `--t:real`; `uV:real`; `vV:real`; `aC:real`; `&1`; `&0`; `&2`]
     C1092MPWS_SQUARE_SUPPORT_BOUND) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_ARITH `&1 * x + &0 * y = x`];
                   ALL_TAC] THEN
   REWRITE_TAC[lcx; lcy; tss_support_radius] THEN
   SUBGOAL_THEN `abs(&1 * d + &0 * --t) = d /\ abs(-- &1 * --t + &0 * d) = t`
   (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN C1092MWC_LIN_TAC; REAL_ARITH_TAC];
   ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th) THEN
  SUBGOAL_THEN `vC < (&13 / &50) * s /\ uV < d - (&2 / &5) * t` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN C1092MWC_LIN_TAC; ALL_TAC] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
  [(* the central axis *)
   SUBGOAL_THEN `t * ABT_lower d (--t) uV vV aC c (--s) =
                 s * uV + (c * t - s * d) * (d * uV + t * vV)` ASSUME_TAC THENL
   [UNDISCH_TAC `ABT_lower d (--t) uV vV aC c (--s) =
                 (c * d + s * t) * uV + (c * t - s * d) * vV` THEN
    UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   C1092MWC_PROD `&0 < s * ((d - (&2 / &5) * t) - uV)` THEN
   C1092MWC_PROD `&0 <= (c * t - s * d) * (&2 - (d * (uV + aC) + t * (vV + aC)))` THEN
   C1092MWC_PROD `&0 <= t * (ABT_lower d (--t) uV vV aC c (--s) - (aC - z))` THEN
   C1092MWC_PROD `&0 <= (c * t - s * d) * (d + t)` THEN
   C1092MWC_PROD `&0 < (aC - &1) * (t + (c * t - s * d) * (d + t))` THEN
   C1092MWC_ARITH_WITH
    [`t * ABT_lower d (--t) uV vV aC c (--s) =
      s * uV + (c * t - s * d) * (d * uV + t * vV)`;
     `&0 < s * ((d - (&2 / &5) * t) - uV)`;
     `&0 <= (c * t - s * d) * (&2 - (d * (uV + aC) + t * (vV + aC)))`;
     `&0 <= t * (ABT_lower d (--t) uV vV aC c (--s) - (aC - z))`;
     `&0 < (aC - &1) * (t + (c * t - s * d) * (d + t))`;
     `&0 < t * (&1 - z - c + (&2 / &5) * s) + (c * t - s * d) * (d + t - &1)`];
   (* the wall axis *)
   RULE_ASSUM_TAC(REWRITE_RULE[REAL_NEG_NEG]) THEN
   C1092MWC_PROD `&0 <= (c * d + s * t) * (uC + z)` THEN
   C1092MWC_PROD `&0 < (c * t - s * d) * ((&13 / &50) * s - vC)` THEN
   C1092MWC_PROD `&0 < (c * d + s * t) * (aC - &1)` THEN
   SUBGOAL_THEN `d * (s * z) = d * (&1 - c)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   C1092MWC_ARITH_WITH
    [`ABT_upper c (--s) uC vC aC d (--t) =
      (c * d + s * t) * (uC + aC) - (c * t - s * d) * vC`;
     `ABT_upper c (--s) uC vC aC d (--t) <= uV`;
     `uV < d - (&2 / &5) * t`;
     `&0 <= (c * d + s * t) * (uC + z)`;
     `&0 < (c * t - s * d) * ((&13 / &50) * s - vC)`;
     `&0 < (c * d + s * t) * (aC - &1)`;
     `d * (s * z) = d * (&1 - c)`;
     `&0 < d * (--z * (c + s) + (&13 / &50) * s pow 2) +
           t * ((&1 - z) * s - (&13 / &50) * s * c + &2 / &5)`]]);;

(* Lean: point *)
let C1092MWC_POINT = prove
 (`forall cC sC uC vC aC cW sW uW vW aW c s z.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     cC = c /\ sC = --s /\ &1 < aC /\ aC <= &1001 / &1000 /\ aC = aW /\
     &0 < c /\ &0 <= s /\ s <= c /\ z * (&1 + c) = s /\ s * z = &1 - c /\
     linside cC sC uC vC aC (&0) (&13 / &50) /\
     linside cC sC uC vC aC (&13 / &50) (&0) /\
     linside cC sC uC vC aC (&7 / &20) (&7 / &20) /\ &0 <= vC /\
     linside cW sW uW vW aW (&543 / &500) (&0) /\
     linside cW sW uW vW aW (&1) (--(&39 / &100)) /\
     linside cW sW uW vW aW (&1) (&2 / &5) /\
     ~linside cW sW uW vW aW (&1) (--(&2 / &5)) /\
     (forall x y. linside cW sW uW vW aW x y ==> x <= &2) /\ lcy cW sW uW vW aW <= &0 /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> uC < --z /\ linside cC sC uC vC aC z (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `cC:real = c`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sC:real = --s`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  SUBGOAL_THEN `c pow 2 + s pow 2 = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `c * c + --s * --s = &1` THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `uC < --(&13 / &50) * s /\ --(&13 / &50) * s < uC + aC /\
                vC < (&13 / &50) * s` STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `linside c (--s) uC vC aC (&0) (&13 / &50)` THEN
   UNDISCH_TAC `linside c (--s) uC vC aC (&13 / &50) (&0)` THEN
   ASM_REWRITE_TAC[linside] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [C1092MWC_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `s:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < z` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092MWC_PROD `&0 <= --z * (&1 + c)` THEN C1092MWC_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `z < &1 / &2` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092MWC_PROD `&0 <= (z - &1 / &2) * (&1 + c)` THEN
   SUBGOAL_THEN `&1 <= c` ASSUME_TAC THENL [C1092MWC_LP_TAC; ALL_TAC] THEN
   C1092MWC_PROD `&0 <= (c - &1) * (c + &1)` THEN C1092MWC_PROD `&0 < s * s` THEN
   C1092MWC_ARITH_WITH [`&0 <= (c - &1) * (c + &1)`; `&0 < s * s`;
                        `c pow 2 + s pow 2 = &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + z pow 2) * c = &1 - z pow 2 /\ (&1 + z pow 2) * s = &2 * z`
  STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN UNDISCH_TAC `z * (&1 + c) = s` THEN UNDISCH_TAC `s * z = &1 - c` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `uC < --z` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   ABBREV_TAC `r0 = (&1 - z) pow 2 / &2` THEN
   SUBGOAL_THEN `c - s * r0 = &1 - z /\ s + c * r0 = &1 - r0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r0" THEN CONJ_TAC THEN
    UNDISCH_TAC `z * (&1 + c) = s` THEN UNDISCH_TAC `s * z = &1 - c` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= r0 /\ r0 <= &1 / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r0" THEN C1092MWC_PROD `&0 <= z * (&2 - z)` THEN
    MP_TAC(SPEC `&1 - z` REAL_LE_POW_2) THEN DISCH_TAC THEN C1092MWC_LP_TAC; ALL_TAC] THEN
   RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th) THEN
   ASM_CASES_TAC `&2 / &5 < r0` THENL
   [SUBGOAL_THEN `linside c (--s) uC vC aC (&1) r0` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[linside] THEN
     C1092MWC_PROD `&0 <= s * (&1 / &2 - r0)` THEN C1092MWC_PROD `&0 <= c * r0` THEN
     C1092MWC_LP_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `z:real`] C1092MWCS_SMALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MWC_LP_TAC; STRIP_TAC] THEN
    MATCH_MP_TAC C1092MWC_SUPPORT_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`c:real`; `--s:real`; `uC:real`; `vC:real`; `aC:real`;
                          `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`;
                          `c:real`; `s:real`; `z:real`; `r0:real`] THEN
    ASM_REWRITE_TAC[linside] THEN C1092MWC_LP_TAC;
    SUBGOAL_THEN `s + (&2 / &5) * c <= &1` ASSUME_TAC THENL
    [C1092MWC_PROD `&0 <= (c - s) * ((&41 / &50) * c + (&1 / &50) * s)` THEN
     SUBGOAL_THEN `(s + (&2 / &5) * c) pow 2 <= &49 / &50` ASSUME_TAC THENL
     [C1092MWC_LP_TAC; ALL_TAC] THEN
     REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
     C1092MWC_PROD `&0 < (s + (&2 / &5) * c - &1) * (s + (&2 / &5) * c + &1)` THEN
     C1092MWC_LP_TAC; ALL_TAC] THEN
    UNDISCH_TAC `ldisj c (--s) uC vC aC cW sW uW vW aC` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&1`; `&2 / &5`]) THEN ASM_REWRITE_TAC[linside] THEN
    C1092MWC_PROD `&0 <= s * (&2 / &5 - r0)` THEN C1092MWC_LP_TAC];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[linside] THEN
  C1092MWC_PROD `&0 <= z * (&1 - c)` THEN
  SUBGOAL_THEN `c * z - s = --z /\ s * z + c = &1` STRIP_ASSUME_TAC THENL
  [C1092MWC_ARITH_WITH [`z * (&1 + c) = s`; `s * z = &1 - c`]; ALL_TAC] THEN
  C1092MWC_LP_TAC);;
