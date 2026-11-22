(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/TwoFifthsEntranceNorthwestGeometry  *)
(* .lean (N12Compact.C1092MMMPTwoFifthsEntrance).  The shared E/W support    *)
(* entrance to the upper-third theorem.  Squares E = (cE,sE,uE,vE,aE),       *)
(* W = (cW,sW,uW,vW,aW) with explicit OpenSquare invariants; apart is ldisj; *)
(* C1092TwoFifths.Southeast is C1092TF_southeast; Normal is c977cc_normal    *)
(* (normal_bounds C977CC_NORMAL_BOUNDS).  Scalars.south_bounds              *)
(* C1092TFSS_SOUTH_BOUNDS; lower / upper ABT_lower / ABT_upper,             *)
(* strict_bounds ABT_STRICT_BOUNDS, ownU / ownV ABT_OWNU / ABT_OWNV,        *)
(* faceSeparation_of_disjoint + separated + radii ABT_FOUR_AXES;             *)
(* TwoFifths.Support reverse / lower_neg / upper_pos_pos C1092TFSU_*;        *)
(* lower_nn / lower_np / upper_np C1092WS_*; S12.short_projections           *)
(* WFP_SHORT_PROJECTIONS.  Tag C1092MTFNW_.                                   *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_TwoFifthsEntranceSoutheast.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSoutheastScalars.ml";;
needs "n12/geometry/CP_C1092_MMMP_LeftFar.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let C1092MTFNW_LIN = NLIN_TAC ~deg2:false [];;
let C1092MTFNW_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     REPEAT CONJ_TAC THEN C1092MTFNW_LIN;
     ALL_TAC]) tms;;
let C1092MTFNW_EV = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
and C1092MTFNW_WV = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`];;

let C1092MTFNW_SOUTH_TAC =
  MP_TAC(SPECL [`cE:real`; `sE:real`] C1092TFSS_SOUTH_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  REWRITE_TAC[C1092TFSS_southBounds] THEN
  SPEC_TAC(`C1092WPS_half cE sE`, `z:real`) THEN GEN_TAC THEN STRIP_TAC;;

(* rewrite with the support-formula assumptions only *)
let C1092MTFNW_SUPPORT_TAC =
  ASSUM_LIST(fun ths -> REWRITE_TAC (filter (fun th -> let c = concl th in
    is_eq c && is_comb (lhs c) &&
    (let f = fst (strip_comb (lhs c)) in f = `ABT_lower` || f = `ABT_upper`)) ths));;

let C1092MTFNW_SE_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[C1092TF_southeast] o
    check (can (term_match [] `C1092TF_southeast c s u v a`) o concl));;

(* Lean: southeast_height *)
let C1092MTFNW_SOUTHEAST_HEIGHT = prove
 (`forall cE sE uE vE aE.
     cE * cE + sE * sE = &1 /\ &0 < aE /\
     C1092TF_southeast cE sE uE vE aE /\ uE + aE <= cE - (&13 / &50) * sE
     ==> --(&1 / &80) < vE + aE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MTFNW_SE_TAC THEN C1092MTFNW_SOUTH_TAC THEN
  C1092MTFNW_PROD_TAC [`&0 <= (cE - &12 / &13) * (&1 - cE)`] THEN
  SUBGOAL_THEN `&1 - cE <= (&13 / &25) * sE pow 2` ASSUME_TAC THENL
   [C1092MTFNW_LIN; ALL_TAC] THEN
  C1092MTFNW_PROD_TAC [`&0 <= (&1 - sE) * ((&13 / &25) * sE pow 2 - (&1 - cE))`;
                       `&0 <= sE * ((cE - (&13 / &50) * sE) - (uE + aE))`;
                       `&0 < (aE - &1) * (cE + sE)`] THEN
  SUBGOAL_THEN `--(&13 / &50) * sE pow 2 + (&13 / &25) * sE pow 3 < cE * (vE + aE)`
    ASSUME_TAC THENL [C1092MTFNW_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (sE - &1 / &3) pow 2 * ((&13 / &25) * (sE + &1 / &6))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN C1092MTFNW_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `--(&13 / &1350) < cE * (vE + aE)` ASSUME_TAC THENL
   [C1092MTFNW_LIN; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092MTFNW_PROD_TAC [`&0 <= cE * (--(&1 / &80) - (vE + aE))`] THEN
  C1092MTFNW_LIN);;

(* Lean: northwest_cone (private) *)
let C1092MTFNW_NORTHWEST_CONE = prove
 (`forall cE sE uE vE aE cW sW uW vW aW nx ny.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     nx pow 2 + ny pow 2 = &1 /\
     linside cE sE uE vE aE (&0) (--(&13 / &50)) /\
     linside cE sE uE vE aE (&13 / &50) (&0) /\
     linside cW sW uW vW aW (--(&13 / &50)) (&0) /\
     linside cW sW uW vW aW (&0) (&13 / &50) /\
     ABT_upper cE sE uE vE aE nx ny <= ABT_lower cW sW uW vW aW nx ny
     ==> nx < &0 /\ &0 < ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let sb q x y = SPECL (q @ [x; y; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS in
  MP_TAC(sb C1092MTFNW_EV `&13 / &50` `&0`) THEN MP_TAC(sb C1092MTFNW_WV `--(&13 / &50)` `&0`) THEN
  MP_TAC(sb C1092MTFNW_EV `&0` `--(&13 / &50)`) THEN MP_TAC(sb C1092MTFNW_WV `&0` `&13 / &50`) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC
   `ABT_upper cE sE uE vE aE nx ny <= ABT_lower cW sW uW vW aW nx ny` THEN
  REAL_ARITH_TAC);;

let C1092MTFNW_UNITS = prove
 (`forall c s. c * c + s * s = &1
         ==> c pow 2 + s pow 2 = &1 /\ (--c) pow 2 + (--s) pow 2 = &1 /\
             (--s) pow 2 + c pow 2 = &1 /\ s pow 2 + (--c) pow 2 = &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN
  UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING);;

(* Lean: northwest_axes *)
let C1092MTFNW_NORTHWEST_AXES = prove
 (`forall cE sE uE vE aE cW sW uW vW aW.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     aE = aW /\ &0 < cE /\ &0 < sE /\ &0 < cW /\
     linside cE sE uE vE aE (&0) (--(&13 / &50)) /\
     linside cE sE uE vE aE (&13 / &50) (&0) /\
     linside cW sW uW vW aW (--(&13 / &50)) (&0) /\
     linside cW sW uW vW aW (&0) (&13 / &50) /\
     ldisj cE sE uE vE aE cW sW uW vW aW
     ==> vE + aE <= ABT_lower cW sW uW vW aW (--sE) cE \/
         ABT_upper cE sE uE vE aE (--cW) (--sW) <= --(uW + aW) \/
         ABT_upper cE sE uE vE aE (--sW) cW <= vW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aE:real = aW`)) THEN
  let qE = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aW:real`] and qW = C1092MTFNW_WV in
  MP_TAC(SPECL [`cE:real`; `sE:real`] C1092MTFNW_UNITS) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`] C1092MTFNW_UNITS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL (qE @ qW) ABT_FOUR_AXES) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  let own q = CONJ (ASSUME (list_mk_comb(`(=):real->real->bool`,
      [mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` (el 0 q) (el 0 q))
                 (mk_binop `( * ):real->real->real` (el 1 q) (el 1 q)); `&1`])))
      (ASSUME `&0 < aW`) in
  let owns = [MP (SPECL qE ABT_OWNV) (own qE); MP (SPECL qW ABT_OWNV) (own qW);
              MP (SPECL qW ABT_OWNU) (own qW)] in
  let pat = `ABT_upper a b c d e (nx:real) (ny:real) <= ABT_lower f g h i j nx ny` in
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    if not (can (term_match [] pat) (concl th)) then NO_TAC else
    let args = snd (strip_comb (lhand (concl th))) in
    let th' =
      if el 0 args = `cE:real` then th else
      REWRITE_RULE[REAL_NEG_NEG] (MATCH_MP C1092TFSU_REVERSE th) in
    let args' = snd (strip_comb (lhand (concl th'))) in
    (MP_TAC th' THEN REWRITE_TAC (C1092TFSU_LOWER_NEG :: owns) THEN SIMP_TAC[] THEN NO_TAC) ORELSE
    (MP_TAC(SPECL (qE @ qW @ [el 5 args'; el 6 args']) C1092MTFNW_NORTHWEST_CONE) THEN
     ASM_REWRITE_TAC[th'] THEN STRIP_TAC THEN
     MATCH_MP_TAC(TAUT `false ==> p`) THEN C1092MTFNW_LIN)));;

(* Lean: negative_northwest_impossible *)
let C1092MTFNW_NEGATIVE_NORTHWEST_IMPOSSIBLE = prove
 (`forall cE sE uE vE aE cW sW uW vW aW.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     C1092TF_southeast cE sE uE vE aE /\ aE = aW /\
     c977cc_normal cW (--sW) /\ &99 / &100 < cW /\ --sW < &7 / &50 /\
     --(&1 / &80) < vE + aE /\ vW + aW < &25 / &33 /\
     linside cW sW uW vW aW (&0) (&0) /\
     linside cW sW uW vW aW (--(&13 / &50)) (&0) /\
     linside cW sW uW vW aW (&0) (&13 / &50) /\
     ldisj cE sE uE vE aE cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MTFNW_SE_TAC THEN C1092MTFNW_SOUTH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (can (term_match [] `c977cc_normal x y`) o concl)) THEN
  C1092MTFNW_PROD_TAC [`&0 <= (&8 / &25 - sE) * --sW`; `&0 < (cE - &47 / &50) * cW`;
                       `&0 < sE * cW`; `&0 <= cE * --sW`;
                       `&0 <= sE * (&1 - cW)`; `&0 <= --sW * (&1 - cE)`] THEN
  SUBGOAL_THEN `&22 / &25 < cE * cW + sE * sW /\ &0 < sE * cW - cE * sW /\
                sE * cW - cE * sW < &23 / &50` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN C1092MTFNW_LIN; ALL_TAC] THEN
  MP_TAC(SPECL (C1092MTFNW_EV @ C1092MTFNW_WV) C1092MTFNW_NORTHWEST_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MTFNW_LIN; ALL_TAC] THEN
  UNDISCH_TAC `linside cW sW uW vW aW (&0) (&0)` THEN REWRITE_TAC[linside] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MTFNW_WV @ [`--sE`; `cE:real`; `--(sE * cW - cE * sW)`;
                                 `cE * cW + sE * sW`]) C1092WS_LOWER_NP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN (REAL_ARITH_TAC ORELSE C1092MTFNW_LIN); DISCH_TAC] THEN
  MP_TAC(SPECL (C1092MTFNW_EV @ [`--cW`; `--sW`; `--(cE * cW + sE * sW)`;
                                 `sE * cW - cE * sW`]) C1092WS_UPPER_NP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN (REAL_ARITH_TAC ORELSE C1092MTFNW_LIN); DISCH_TAC] THEN
  STRIP_TAC THENL
   [(* own *)
    UNDISCH_TAC `vE + aE <= ABT_lower cW sW uW vW aW (--sE) cE` THEN C1092MTFNW_SUPPORT_TAC THEN
    DISCH_TAC THEN
    C1092MTFNW_PROD_TAC [`&0 < (sE * cW - cE * sW) * (uW + aW)`;
                         `&0 < (cE * cW + sE * sW) * (--(&8 / &33) - vW)`] THEN
    C1092MTFNW_LIN;
    (* opposite *)
    UNDISCH_TAC `ABT_upper cE sE uE vE aE (--cW) (--sW) <= --(uW + aW)` THEN C1092MTFNW_SUPPORT_TAC THEN
    DISCH_TAC THEN
    UNDISCH_TAC `linside cE sE uE vE aE (&0) (--(&13 / &50))` THEN
    UNDISCH_TAC `linside cE sE uE vE aE (&13 / &50) (&0)` THEN
    REWRITE_TAC[linside] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REPEAT STRIP_TAC THEN
    C1092MTFNW_PROD_TAC [`&0 < (cE * cW + sE * sW) * (--(&13 / &50) * sE - uE)`;
                         `&0 < (sE * cW - cE * sW) * (vE + aE + (&13 / &50) * sE)`;
                         `&0 < sE * ((cE * cW + sE * sW) - (sE * cW - cE * sW))`] THEN
    C1092MTFNW_LIN;
    (* transverse *)
    MP_TAC(SPECL C1092MTFNW_WV ABT_OWNV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(SPECL (C1092MTFNW_EV @ C1092MTFNW_WV @ [`--sW`; `cW:real`]) C1092MTFNW_NORTHWEST_CONE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN C1092MTFNW_SUPPORT_TAC THEN REPEAT CONJ_TAC THEN
      FIRST [FIRST_ASSUM ACCEPT_TAC;
             UNDISCH_TAC `cW * cW + sW * sW = &1` THEN REAL_ARITH_TAC];
      STRIP_TAC THEN C1092MTFNW_LIN]]);;

(* Lean: positive_northwest_height *)
let C1092MTFNW_POSITIVE_NORTHWEST_HEIGHT = prove
 (`forall cE sE uE vE aE cW sW uW vW aW.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     C1092TF_southeast cE sE uE vE aE /\ aE = aW /\
     c977cc_normal cW sW /\ --(&1 / &80) < vE + aE /\
     linside cW sW uW vW aW (&0) (&0) /\
     linside cW sW uW vW aW (--(&13 / &50)) (&0) /\
     linside cW sW uW vW aW (&0) (&13 / &50) /\
     ldisj cE sE uE vE aE cW sW uW vW aW
     ==> &24 / &25 < vW + aW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MTFNW_SE_TAC THEN
  MP_TAC(SPECL (C1092MTFNW_EV @ C1092MTFNW_WV) C1092MTFNW_NORTHWEST_AXES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN C1092MTFNW_LIN;
    DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aE:real = aW`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (can (term_match [] `c977cc_normal x y`) o concl)) THEN
  C1092MTFNW_PROD_TAC [`&0 < cW * cE`; `&0 <= sW * sE`;
                       `&0 <= (cW - sW) * cE`; `&0 <= (cW + sW) * sE`;
                       `&0 <= (cE - sE) * cW`; `&0 <= sW * (cE + sE)`] THEN
  SUBGOAL_THEN `&0 < cW * cE + sW * sE /\
                &0 <= (cW * cE + sW * sE) - (sW * cE - cW * sE) /\
                &0 <= (cW * cE + sW * sE) + (sW * cE - cW * sE)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN C1092MTFNW_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `(cW * cE + sW * sE) pow 2 + (sW * cE - cW * sE) pow 2 = &1` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`cW * cW + sW * sW = &1`; `cE * cE + sE * sE = &1`] THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092MTFNW_PROD_TAC [`&0 <= ((cW * cE + sW * sE) - (sW * cE - cW * sE)) *
                              ((cW * cE + sW * sE) + (sW * cE - cW * sE))`] THEN
  SUBGOAL_THEN `&7 / &10 < cW * cE + sW * sE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MTFNW_PROD_TAC [`&0 <= (cW * cE + sW * sE) * (&7 / &10 - (cW * cE + sW * sE))`] THEN
    C1092MTFNW_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `cW * cE + sW * sE <= &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MTFNW_PROD_TAC [`&0 < ((cW * cE + sW * sE) - &1) * ((cW * cE + sW * sE) + &1)`] THEN
    MP_TAC(SPEC `sW * cE - cW * sE` REAL_LE_POW_2) THEN DISCH_TAC THEN
    C1092MTFNW_LIN; ALL_TAC] THEN
  UNDISCH_TAC `linside cW sW uW vW aW (&0) (&0)` THEN REWRITE_TAC[linside] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN STRIP_TAC THEN
  MP_TAC(ASSUME `linside cE sE uE vE aW (&0) (--(&13 / &50))`) THEN
  MP_TAC(ASSUME `linside cE sE uE vE aW (&13 / &50) (&0)`) THEN
  REWRITE_TAC[linside] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `uE < &0 /\ &0 < uE + aW` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092MTFNW_LIN; ALL_TAC] THEN
  let qE = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aW:real`] in
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_disj (concl th))) THENL
   [(* own *)
    SUBGOAL_THEN `ABT_lower cW sW uW vW aW (--sE) cE <= (cW * cE + sW * sE) * vW` ASSUME_TAC THENL
     [ASM_CASES_TAC `&0 <= sW * cE - cW * sE` THENL
       [MP_TAC(SPECL (C1092MTFNW_WV @ [`--sE`; `cE:real`; `sW * cE - cW * sE`;
                                      `cW * cE + sW * sE`]) C1092WS_LOWER_NN) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
          (REAL_ARITH_TAC ORELSE C1092MTFNW_LIN); DISCH_THEN SUBST1_TAC] THEN
        C1092MTFNW_PROD_TAC [`&0 <= (sW * cE - cW * sE) * --uW`] THEN C1092MTFNW_LIN;
        MP_TAC(SPECL (C1092MTFNW_WV @ [`--sE`; `cE:real`; `sW * cE - cW * sE`;
                                      `cW * cE + sW * sE`]) C1092WS_LOWER_NP) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
          (REAL_ARITH_TAC ORELSE C1092MTFNW_LIN); DISCH_THEN SUBST1_TAC] THEN
        C1092MTFNW_PROD_TAC [`&0 <= --(sW * cE - cW * sE) * (uW + aW)`] THEN C1092MTFNW_LIN];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MTFNW_PROD_TAC [`&0 < (cW * cE + sW * sE) * (--(&1 / &25) - vW)`] THEN
    C1092MTFNW_LIN;
    (* opposite *)
    MP_TAC(SPECL (C1092MTFNW_WV) ABT_OWNU) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(SPECL (qE @ C1092MTFNW_WV @ [`--cW`; `--sW`]) C1092MTFNW_NORTHWEST_CONE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_POW_2; C1092TFSU_LOWER_NEG] THEN C1092MTFNW_SUPPORT_TAC THEN
      REPEAT CONJ_TAC THEN
      FIRST [FIRST_ASSUM ACCEPT_TAC;
             UNDISCH_TAC `cW * cW + sW * sW = &1` THEN REAL_ARITH_TAC];
      STRIP_TAC THEN C1092MTFNW_LIN];
    (* transverse *)
    SUBGOAL_THEN `(cW * cE + sW * sE) * (vE + aW) <= ABT_upper cE sE uE vE aW (--sW) cW`
      ASSUME_TAC THENL
     [ASM_CASES_TAC `&0 <= sW * cE - cW * sE` THENL
       [MP_TAC(SPECL (qE @ [`--sW`; `cW:real`; `--(sW * cE - cW * sE)`;
                            `cW * cE + sW * sE`]) C1092WS_UPPER_NP) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
          (REAL_ARITH_TAC ORELSE C1092MTFNW_LIN); DISCH_THEN SUBST1_TAC] THEN
        C1092MTFNW_PROD_TAC [`&0 <= (sW * cE - cW * sE) * --uE`] THEN C1092MTFNW_LIN;
        MP_TAC(SPECL (qE @ [`--sW`; `cW:real`; `--(sW * cE - cW * sE)`;
                            `cW * cE + sW * sE`]) C1092TFSU_UPPER_POS_POS) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
          (REAL_ARITH_TAC ORELSE C1092MTFNW_LIN); DISCH_THEN SUBST1_TAC] THEN
        C1092MTFNW_PROD_TAC [`&0 <= --(sW * cE - cW * sE) * (uE + aW)`] THEN C1092MTFNW_LIN];
      ALL_TAC] THEN
    C1092MTFNW_PROD_TAC [`&0 < (cW * cE + sW * sE) * (vE + aW + &1 / &80)`] THEN
    C1092MTFNW_LIN]);;

(* Lean: positive_northwest_faces *)
let C1092MTFNW_POSITIVE_NORTHWEST_FACES = prove
 (`forall cW sW uW vW aW.
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     &1 < aW /\ c977cc_normal cW sW /\
     linside cW sW uW vW aW (&0) (&0) /\
     linside cW sW uW vW aW (--(&1 / &2)) (&1 / &2) /\
     ~linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\
     ~linside cW sW uW vW aW (&7 / &20) (&7 / &20) /\
     ~linside cW sW uW vW aW (--(&1)) (&39 / &100)
     ==> &8 * sW < &7 * cW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (can (term_match [] `c977cc_normal x y`) o concl)) THEN
  C1092MTFF_STEP `uW + aW <= (&7 / &20) * (cW + sW)`
    [`~linside cW sW uW vW aW (&7 / &20) (&7 / &20)`] THEN
  C1092MTFF_STEP `--(&7 / &20) * (cW - sW) <= vW`
    [`~linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20))`] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `&37 / &50`; `&13 / &20`] WFP_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC] THEN
  C1092MTFF_STEP `--cW + (&39 / &100) * sW <= uW`
    [`~linside cW sW uW vW aW (--(&1)) (&39 / &100)`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&200 / &263 < cW` ASSUME_TAC THENL [C1092MTFNW_LIN; ALL_TAC] THEN
  C1092MTFNW_PROD_TAC [`&0 <= (&8 * sW - &7 * cW) * (&8 * sW + &7 * cW)`;
                       `&0 < (cW - &200 / &263) * (cW + &200 / &263)`] THEN
  C1092MTFNW_LIN);;

(* Lean: positive_northwest_left_face *)
let C1092MTFNW_POSITIVE_NORTHWEST_LEFT_FACE = prove
 (`forall cW sW uW vW aW.
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cW sW /\ &8 * sW < &7 * cW /\ &24 / &25 < vW + aW /\
     linside cW sW uW vW aW (&0) (&0) /\
     ~linside cW sW uW vW aW (--(&1)) (&2 / &5)
     ==> aW - cW + (&2 / &5) * sW <= uW + aW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (can (term_match [] `c977cc_normal x y`) o concl)) THEN
  C1092MTFNW_PROD_TAC [`&0 <= (&7 * cW - &8 * sW) * ((&307 / &25) * cW + (&28 / &25) * sW)`] THEN
  SUBGOAL_THEN `sW + (&2 / &5) * cW < &24 / &25` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `sW + (&2 / &5) * cW - &24 / &25`]; ALL_TAC] THEN
  C1092MTFF_STEP `aW - cW + (&2 / &5) * sW <= uW + aW`
    [`~linside cW sW uW vW aW (--(&1)) (&2 / &5)`] THEN
  ASM_REWRITE_TAC[]);;
