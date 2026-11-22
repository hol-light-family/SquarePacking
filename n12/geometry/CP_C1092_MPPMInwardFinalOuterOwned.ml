(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalOuterOwned.lean           *)
(* (namespace N12Compact.C1092MPPMInwardFinal).  INWARD-OUTER-OWNED-ANGLE,   *)
(* Theorem 1 and Corollary 2.  Squares C, B, K are the tuples cC sC uC vC aC,*)
(* cB .., cK .. (unit normals and positive sides as explicit hypotheses).    *)
(* OuterOwnedInput: c1092ifow_input; MissingProfile:                         *)
(* c1092miff_missing_profile; Normal: c977cc_normal; half: C1092WPS_half;    *)
(* BottomCorner / bottom_origin: c1092ifc_bottomCorner /                     *)
(* C1092IFC_BOTTOM_ORIGIN; ClosedFrames.canonical_frame: CLF_CANONICAL_FRAME;*)
(* the scalar lemmas: C1092IFOO_* (OuterOwnedScalars).  C.translated 2 2 is  *)
(* the tuple cC sC (uC - &2 * (cC + sC)) (vC - &2 * (cC - sC)) aC            *)
(* (C1092IFOW_TRANSLATE).  Real.sqrt 13 is sqrt(&13).                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalOuterOwnedScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalFloor.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalCentered.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: OuterOwnedInput (structure) *)
let c1092ifow_input = new_definition
 `c1092ifow_input cC sC uC vC aC cB sB uB vB aB <=>
    &1 < aC /\
    linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
    linside cC sC uC vC aC (&0) (--(&13 / &50)) /\
    linside cC sC uC vC aC (--(&13 / &50)) (&0) /\
    linside cC sC uC vC aC (--(&1)) (--(&2 / &5)) /\
    ~linside cC sC uC vC aC (&0) (&0) /\
    ~linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
    (forall x. --(&2 / &5) <= x /\ x <= --(&13 / &50) ==> linside cB sB uB vB aB x (--(&1))) /\
    ldisj cC sC uC vC aC cB sB uB vB aB`;;

(* unfold the positive linside facts of C into band inequalities *)
let C1092IFOW_UNFOLD_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `linside cC sC uC vC aC x y`) (concl th)
    then STRIP_ASSUME_TAC(REWRITE_RULE[linside] th) else NO_TAC));;

(* refute a point of C: from an omitted point  ~linside C P *)
let C1092IFOW_OMIT_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

(* refute a point (x0, -1) of C on the bar of B *)
let C1092IFOW_BAR_TAC x0 =
  FIRST_ASSUM(fun bar -> if is_forall(concl bar) && not (is_forall(snd(dest_forall(concl bar))))
    && can (find_term ((=) `cB:real`)) (concl bar)
    then MP_TAC(SPEC x0 bar) else NO_TAC) THEN
  REPEAT(ANTS_TAC THENL [RASM_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN(fun bth -> FIRST_ASSUM(fun ap ->
    if can (term_match [] `forall x y. ~(linside cC sC uC vC aC x y /\ linside cB sB uB vB aB x y)`) (concl ap)
    then MP_TAC(SPECL [x0; `--(&1)`] ap) THEN REWRITE_TAC[bth] else NO_TAC)) THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

let C1092IFOW_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
     FIRST [RASM_ARITH_TAC; MATCH_ACCEPT_TAC REAL_LE_POW_2];
     ALL_TAC]) tms;;

(* apply an implication assumption with the given conclusion *)
let C1092IFOW_USE_TAC pat =
  FIRST_ASSUM(fun th -> if is_imp(concl th) && rand(concl th) = pat
                        then MATCH_MP_TAC th else NO_TAC);;

let C1092IFOW_OPEN_TAC =
  REWRITE_TAC[c1092ifow_input; ldisj; IMP_CONJ] THEN REPEAT DISCH_TAC THEN C1092IFOW_UNFOLD_TAC;;

(* Lean: outer_nonnegative_impossible *)
let C1092IFOW_OUTER_NONNEGATIVE_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aC /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cC sC uC vC aC (--(&13 / &50)) (&0) /\
     linside cC sC uC vC aC (--(&1)) (--(&2 / &5)) /\
     ~linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
     (forall x. --(&2 / &5) <= x /\ x <= --(&13 / &50) ==> linside cB sB uB vB aB x (--(&1))) /\
     ldisj cC sC uC vC aC cB sB uB vB aB /\
     c977cc_normal cC sC
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj; IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  C1092IFOW_UNFOLD_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`] C1092IFOO_OUTER_SHORT_WIDTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; STRIP_TAC] THEN
  C1092MIFS_NORMAL_TAC THEN
  SUBGOAL_THEN `vC + aC <= sC - (&13 / &50) * cC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092IFOW_OMIT_TAC `~linside cC sC uC vC aC (--(&1)) (--(&13 / &50))`; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 / &5) * sC - cC <= vC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092IFOW_BAR_TAC `--(&2 / &5)`; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: outer_owned_negative *)
let C1092IFOW_OUTER_OWNED_NEGATIVE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ifow_input cC sC uC vC aC cB sB uB vB aB /\ abs sC <= cC
     ==> sC < &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092ifow_input] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MATCH_MP_TAC C1092IFOW_OUTER_NONNEGATIVE_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                        `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
  ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
  UNDISCH_TAC `abs sC <= cC` THEN ASM_REAL_ARITH_TAC);;

(* Lean: outer_owned_faces *)
let C1092IFOW_OUTER_OWNED_FACES = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ifow_input cC sC uC vC aC cB sB uB vB aB /\
     c977cc_normal cC (--sC) /\ sC < &0
     ==> --cC - (&13 / &50) * sC <= uC /\ vC + aC <= &0 /\
         --cC + (&2 / &5) * sC <= vC /\
         ((--cC + (&13 / &50) * sC <= vC /\ aC <= cC - (&13 / &50) * sC /\
           C1092WPS_half cC (--sC) < &13 / &50) \/
          (uC + aC <= --(&13 / &50) * cC - sC /\ cC < --(&2) * sC))`,
  REPEAT GEN_TAC THEN C1092IFOW_OPEN_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
              check (fun th -> concl th = `c977cc_normal cC (--sC)`)) THEN
  MP_TAC(SPECL [`cC:real`; `--sC`] C1092IFOO_OUTER_LOWER_HALF) THEN
  MP_TAC(SPECL [`cC:real`; `--sC`] C1092IFOO_OUTER_UPPER_SLOPE) THEN
  MP_TAC(SPECL [`cC:real`; `--sC`] C1092IFOO_OUTER_SHORT_WIDTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  C1092MIFS_NORMAL_TAC THEN
  SUBGOAL_THEN `vC + aC <= &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092IFOW_OMIT_TAC `~linside cC sC uC vC aC (&0) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `--cC - (&13 / &50) * sC <= uC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092IFOW_OMIT_TAC `~linside cC sC uC vC aC (--(&1)) (--(&13 / &50))`; ALL_TAC] THEN
  SUBGOAL_THEN `--cC + (&2 / &5) * sC <= vC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `--(&2 / &5) * cC - sC < uC + aC` ASSUME_TAC THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
    C1092IFOW_BAR_TAC `--(&2 / &5)`; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `--cC + (&13 / &50) * sC <= vC` THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `aC <= cC - (&13 / &50) * sC` ASSUME_TAC THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN C1092IFOW_USE_TAC `C1092WPS_half cC (--sC) < &13 / &50` THEN
    RASM_ARITH_TAC;
    DISJ2_TAC THEN
    SUBGOAL_THEN `uC + aC <= --(&13 / &50) * cC - sC` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092IFOW_BAR_TAC `--(&13 / &50)`; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `cC < &2 * --sC` MP_TAC THENL
     [C1092IFOW_USE_TAC `cC < &2 * --sC` THEN RASM_ARITH_TAC; REAL_ARITH_TAC]]);;

(* Lean: outer_owned_polynomial *)
let C1092IFOW_OUTER_OWNED_POLYNOMIAL = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ifow_input cC sC uC vC aC cB sB uB vB aB /\
     c977cc_normal cC (--sC) /\ sC < &0
     ==> &0 < C1092WPS_half cC (--sC) pow 2 - &2 * C1092WPS_half cC (--sC) + &12 / &25`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092IFOW_OUTER_OWNED_FACES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  UNDISCH_TAC `c1092ifow_input cC sC uC vC aC cB sB uB vB aB` THEN C1092IFOW_OPEN_TAC THEN
  MP_TAC(SPECL [`cC:real`; `--sC`] C1092IFAS_CANONICAL_HALF_BOUNDS) THEN
  MP_TAC(SPECL [`cC:real`; `--sC`] C1092IFOO_OUTER_Q_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  C1092MIFS_NORMAL_TAC THEN
  ABBREV_TAC `z = C1092WPS_half cC (--sC)` THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term ((=) `uC + aC`)) (concl th))) THENL
   [MP_TAC(SPEC `z - &13 / &50` REAL_LE_POW_2) THEN
    UNDISCH_TAC `z < &13 / &50` THEN UNDISCH_TAC `&0 <= z` THEN
    UNDISCH_TAC `z pow 2 - &2 * z + &12 / &25 <= &0` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + z pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  C1092IFOW_PROD_TAC [`&0 <= z * --(z pow 2 - &2 * z + &12 / &25)`] THEN
  SUBGOAL_THEN `z <= &1 - cC - (&13 / &50) * sC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092IFOW_PROD_TAC [`&0 < (&1 + z pow 2) * (z - (&1 - cC - (&13 / &50) * sC))`] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  C1092IFOW_PROD_TAC [`&0 <= --sC * ((&1 - cC - (&13 / &50) * sC) - z)`] THEN
  SUBGOAL_THEN `&0 <= cC - sC - &1 + cC * sC + (&13 / &50) * sC pow 2` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092IFOW_PROD_TAC [`&0 <= --sC * (uC - (--cC - (&13 / &50) * sC))`;
                      `&0 <= cC * (--aC - vC)`; `&0 < (aC - &1) * (cC - sC)`] THEN
  SUBGOAL_THEN `sC * (uC + aC) + cC * vC < --(&1)` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `xl = (vC + cC) / --sC` THEN
  ABBREV_TAC `xr = (uC + aC + sC) / cC` THEN
  SUBGOAL_THEN `xl * --sC = vC + cC /\ xr * cC = uC + aC + sC` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["xl"; "xr"] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(&2 / &5) <= xl` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092IFOW_PROD_TAC [`&0 < --(xl + &2 / &5) * --sC`] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `xr <= --(&13 / &50)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092IFOW_PROD_TAC [`&0 < (xr + &13 / &50) * cC`] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--sC * cC * (xr - xl) = --(&1) - (sC * (uC + aC) + cC * vC)` ASSUME_TAC THENL
   [UNDISCH_TAC `xl * --sC = vC + cC` THEN UNDISCH_TAC `xr * cC = uC + aC + sC` THEN
    UNDISCH_TAC `cC * cC + sC * sC = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `xl < xr` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092IFOW_PROD_TAC [`&0 <= (--sC * cC) * (xl - xr)`] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `x = (xl + xr) / &2` THEN
  SUBGOAL_THEN `--(&2 / &5) <= x /\ x <= --(&13 / &50) /\ xl < x /\ x < xr` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN RASM_ARITH_TAC; ALL_TAC] THEN
  C1092IFOW_PROD_TAC [`&0 < --sC * (x - xl)`; `&0 < cC * (xr - x)`;
                      `&0 <= cC * (x + &2 / &5)`; `&0 <= --sC * (--(&13 / &50) - x)`] THEN
  C1092IFOW_BAR_TAC `x:real`);;

(* Lean: outer_owned_profile *)
let C1092IFOW_OUTER_OWNED_PROFILE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ifow_input cC sC uC vC aC cB sB uB vB aB /\ abs sC <= cC
     ==> c1092miff_missing_profile cC sC uC vC aC /\
         C1092WPS_half cC (--sC) < &1 - sqrt(&13) / &5 /\
         C1092WPS_half cC (--sC) < &279 / &1000`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092IFOW_OUTER_OWNED_NEGATIVE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `c977cc_normal cC (--sC)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN UNDISCH_TAC `abs sC <= cC` THEN
    UNDISCH_TAC `cC * cC + sC * sC = &1` THEN UNDISCH_TAC `sC < &0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC_ALL C1092IFOW_OUTER_OWNED_FACES) THEN
  MP_TAC(SPEC_ALL C1092IFOW_OUTER_OWNED_POLYNOMIAL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cC:real`; `--sC`] C1092IFOO_OUTER_ANGLE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `c1092ifow_input cC sC uC vC aC cB sB uB vB aB` THEN
  REWRITE_TAC[c1092ifow_input; c1092miff_missing_profile] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[]);;

(* Lean: outer_owned_halfpoint *)
let C1092IFOW_OUTER_OWNED_HALFPOINT = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ifow_input cC sC uC vC aC cB sB uB vB aB /\ abs sC <= cC
     ==> linside cC sC uC vC aC (--(&1)) (--(&1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092IFOW_OUTER_OWNED_PROFILE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `c1092miff_missing_profile cC sC uC vC aC`) THEN
  REWRITE_TAC[c1092miff_missing_profile] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(SPECL [`cC:real`; `--sC`] C1092IFOO_OUTER_HALFPOINT_PROJECTION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  C1092MIFS_NORMAL_TAC THEN
  UNDISCH_TAC `c1092ifow_input cC sC uC vC aC cB sB uB vB aB` THEN C1092IFOW_OPEN_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV REAL_RAT_REDUCE_CONV)) THEN
  C1092IFOW_UNFOLD_TAC THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: outer_owned_frame *)
let C1092IFOW_OUTER_OWNED_FRAME = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ifow_input cC sC uC vC aC cB sB uB vB aB
     ==> exists cD sD uD vD aD. cD * cD + sD * sD = &1 /\ &0 < aD /\ aD = aC /\
           (forall x y. linside cD sD uD vD aD x y <=> linside cC sC uC vC aC x y) /\
           c1092miff_missing_profile cD sD uD vD aD /\
           C1092WPS_half cD (--sD) < &1 - sqrt(&13) / &5 /\
           linside cC sC uC vC aC (--(&1)) (--(&1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aD:real = aC`)) THEN
  MAP_EVERY EXISTS_TAC [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aC:real`] THEN
  SUBGOAL_THEN `c1092ifow_input cD sD uD vD aC cB sB uB vB aB` ASSUME_TAC THENL
   [UNDISCH_TAC `c1092ifow_input cC sC uC vC aC cB sB uB vB aB` THEN
    ASM_REWRITE_TAC[c1092ifow_input; ldisj]; ALL_TAC] THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    C1092IFOW_OUTER_OWNED_PROFILE) THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    C1092IFOW_OUTER_OWNED_HALFPOINT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
     can (find_term ((=) `linside cD sD uD vD aC x y`)) (concl th)
     then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: outer_owned_origin *)
let C1092IFOW_OUTER_OWNED_ORIGIN = prove
 (`forall cC sC uC vC aC cB sB uB vB aB cK sK uK vK aK.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     cK * cK + sK * sK = &1 /\ &0 < aK /\
     c1092ifow_input cC sC uC vC aC cB sB uB vB aB /\
     c1092ifc_bottomCorner cB sB uB vB aB cK sK uK vK aK /\
     ldisj cC sC uC vC aC cK sK uK vK aK
     ==> linside cB sB uB vB aB (&0) (--(&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    C1092IFOW_OUTER_OWNED_FRAME) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC C1092IFC_BOTTOM_ORIGIN THEN
  MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                        `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: inside_translated_iff at (2,2) *)
let C1092IFOW_TRANSLATE = prove
 (`forall c s u v a x y.
     linside c s (u - &2 * (c + s)) (v - &2 * (c - s)) a x y <=>
     linside c s u v a (&2 + x) (&2 + y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: outer_owned_halfpoint_original *)
let C1092IFOW_OUTER_OWNED_HALFPOINT_ORIGINAL = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aC /\
     linside cC sC uC vC aC (&33 / &20) (&33 / &20) /\
     linside cC sC uC vC aC (&2) (&87 / &50) /\
     linside cC sC uC vC aC (&87 / &50) (&2) /\
     linside cC sC uC vC aC (&1) (&8 / &5) /\
     ~linside cC sC uC vC aC (&2) (&2) /\
     ~linside cC sC uC vC aC (&1) (&87 / &50) /\
     (forall x. &8 / &5 <= x /\ x <= &87 / &50 ==> linside cB sB uB vB aB x (&1)) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> linside cC sC uC vC aC (&1) (&3 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC - &2 * (cC + sC)`; `vC - &2 * (cC - sC)`; `aC:real`;
                `cB:real`; `sB:real`; `uB - &2 * (cB + sB)`; `vB - &2 * (cB - sB)`; `aB:real`]
    C1092IFOW_OUTER_OWNED_FRAME) THEN
  REWRITE_TAC[c1092ifow_input; ldisj; C1092IFOW_TRANSLATE] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN RASM_ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN ASM_REWRITE_TAC[]];
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;
