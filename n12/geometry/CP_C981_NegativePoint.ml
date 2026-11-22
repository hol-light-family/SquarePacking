(* ========================================================================= *)
(* Port of Compact/Completion/C981/NegativePoint.lean                         *)
(* (N12Compact.C981CompletionNegativePoint).  The standalone negative-       *)
(* neighbour point of the C981 ending.  D has sD = --S, B has sB = --t;      *)
(* h = cB*S - t*cD and d = t*S + cB*cD are written out.                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;

let C981NP_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

(* support formulas: unfold, resolve each abs from the sign facts *)
let C981NP_FORM_TAC =
  REWRITE_TAC[C981SF_UPPER_IN_BANDS; C981SF_LOWER_IN_BANDS] THEN
  (fun (asl,w as g) ->
     let abss = setify(find_terms (fun t -> is_comb t &&
                  rator t = `abs:real->real`) w) in
     let eqs = map (fun t -> let x = rand t in
        try TAC_PROOF((asl, mk_eq(t,x)), RASM_ARITH_TAC) with Failure _ ->
        TAC_PROOF((asl, mk_eq(t,mk_comb(`(--):real->real`,x))), RASM_ARITH_TAC))
        abss in
     (REWRITE_TAC eqs THEN REAL_ARITH_TAC) g);;

let C981NP_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL ORELSE
           MATCH_MP_TAC REAL_LE_ADD) THEN CONJ_TAC) THEN
   REWRITE_TAC[REAL_LE_SQUARE] THEN ASM_REAL_ARITH_TAC; ALL_TAC];;

let C981NP_NONPOS_OF_MUL = prove
 (`forall x k. &0 < k /\ k * x <= &0 ==> x <= &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < k * x` MP_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let C981NP_MUL_NONPOS = prove
 (`forall a b. &0 <= a /\ b <= &0 ==> a * b <= &0`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`a:real`; `--b:real`] REAL_LE_MUL) THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: lower_pp (private) *)
let C981NP_LOWER_PP = prove
 (`forall c s u v a x y. &0 <= x * c + y * s /\ &0 <= --x * s + y * c
     ==> ABT_lower c s u v a x y = (x * c + y * s) * u + (--x * s + y * c) * v`,
  REPEAT STRIP_TAC THEN C981NP_FORM_TAC);;

(* Lean: lower_np (private) *)
let C981NP_LOWER_NP = prove
 (`forall c s u v a x y. x * c + y * s <= &0 /\ &0 <= --x * s + y * c
     ==> ABT_lower c s u v a x y = (x * c + y * s) * (u + a) + (--x * s + y * c) * v`,
  REPEAT STRIP_TAC THEN C981NP_FORM_TAC);;

(* Lean: defect (private) *)
let C981NP_DEFECT = prove
 (`forall b t. c977cc_normal b t ==> &1 - b <= (&3 / &5) * t pow 2`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  UNDISCH_TAC `c977cc_normal b t` THEN REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
  STRIP_TAC THEN C981NP_PROD `&0 <= (&1 - b) * (&3 * b - &2)` THEN ASM_REAL_ARITH_TAC);;

(* Lean: point *)
let C981NP_POINT = prove
 (`forall cD sD uD vD aD cB sB uB vB aB S t.
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     sD = --S /\ c977cc_normal cD S /\ sB = --t /\ c977cc_normal cB t /\
     &1 < aB /\
     linside cD sD uD vD aD (&2) (&2) /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&1) (&12 / &5) /\
     (vD + aD <= ABT_lower cB sB uB vB aB S cD \/
      ABT_upper cD sD uD vD aD (--sB) cB <= vB)
     ==> linside cB sB uB vB aB (&8 / &5) (&3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`cB:real`; `t:real`] C981NP_DEFECT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sB:real = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sD:real = --S`)) THEN
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal; REAL_POW_2] th)) ns) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C981NP_UNFOLD_TAC `linside cD (--S) uD vD aD (&2) (&2)` THEN
  C981NP_UNFOLD_TAC `linside cB (--t) uB vB aB (&33 / &20) (&47 / &20)` THEN
  C981NP_UNFOLD_TAC `linside cB (--t) uB vB aB (&1) (&12 / &5)` THEN
  SUBGOAL_THEN `&3 * cB + (&8 / &5) * t < vB + aB` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [C981NP_PROD `&0 <= t * S + cB * cD` THEN
    C981NP_PROD `&0 <= (t * S + cB * cD) * ((&3 * cB + (&8 / &5) * t - &1) - vB)` THEN
    ASM_CASES_TAC `&0 <= cB * S - t * cD` THENL
    [SUBGOAL_THEN `ABT_lower cB (--t) uB vB aB S cD =
                   (cB * S - t * cD) * uB + (t * S + cB * cD) * vB` ASSUME_TAC THENL
     [C981NP_FORM_TAC; ALL_TAC] THEN
     C981NP_PROD `&0 <= (cB * S - t * cD) * ((cB - (&12 / &5) * t) - uB)` THEN
     SUBGOAL_THEN `--(&1) - t + (&3 / &5) * t * t + (&3 / &5) * cB * t <= &0` ASSUME_TAC THENL
     [C981NP_PROD `&0 <= t * (&1 - cB)` THEN C981NP_PROD `&0 <= t * (cB - t)` THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN
      `cD * (&1 - cB - (&3 / &5) * t * t + (&3 / &5) * cB * t) +
       S * (--(&1) - t + (&3 / &5) * t * t + (&3 / &5) * cB * t) <= &0` ASSUME_TAC THENL
     [MATCH_MP_TAC C981NP_NONPOS_OF_MUL THEN EXISTS_TAC `cB:real` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
       `cB * (cD * (&1 - cB - (&3 / &5) * t * t + (&3 / &5) * cB * t) +
              S * (--(&1) - t + (&3 / &5) * t * t + (&3 / &5) * cB * t)) =
        cD * (cB - &1 - (&2 / &5) * t) +
        (cB * S - t * cD) * (--(&1) - t + (&3 / &5) * t * t + (&3 / &5) * cB * t)`
      SUBST1_TAC THENL
      [UNDISCH_TAC `cB * cB + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= &0 /\ b <= &0 ==> a + b <= &0`) THEN CONJ_TAC THEN
      MATCH_MP_TAC C981NP_MUL_NONPOS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN
      `(cB * S - t * cD) * (cB - (&12 / &5) * t) +
       (t * S + cB * cD) * (&3 * cB + (&8 / &5) * t - &1) - &2 * (cD + S) =
       cD * (&1 - cB - (&3 / &5) * t * t + (&3 / &5) * cB * t) +
       S * (--(&1) - t + (&3 / &5) * t * t + (&3 / &5) * cB * t)` MP_TAC THENL
     [UNDISCH_TAC `cB * cB + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
     RASM_ARITH_TAC;
     SUBGOAL_THEN `ABT_lower cB (--t) uB vB aB S cD =
                   (cB * S - t * cD) * (uB + aB) + (t * S + cB * cD) * vB` ASSUME_TAC THENL
     [C981NP_FORM_TAC; ALL_TAC] THEN
     C981NP_PROD `&0 <= --(cB * S - t * cD) * ((uB + aB) - ((&33 / &20) * cB - (&47 / &20) * t))` THEN
     SUBGOAL_THEN `&1 - cB - (&13 / &20) * t * t - (&1 / &20) * cB * t <= &0 /\
                   --(&7 / &20) - (&1 / &20) * t * t + (&13 / &20) * cB * t - t <= &0`
     STRIP_ASSUME_TAC THENL
     [C981NP_PROD `&0 <= cB * t` THEN C981NP_PROD `&0 <= t * (&1 - cB)` THEN
      C981NP_PROD `&0 <= t * t` THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `cD * (&1 - cB - (&13 / &20) * t * t - (&1 / &20) * cB * t) <= &0 /\
                   S * (--(&7 / &20) - (&1 / &20) * t * t + (&13 / &20) * cB * t - t) <= &0`
     STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC C981NP_MUL_NONPOS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN
      `(cB * S - t * cD) * ((&33 / &20) * cB - (&47 / &20) * t) +
       (t * S + cB * cD) * (&3 * cB + (&8 / &5) * t - &1) - &2 * (cD + S) =
       cD * (&1 - cB - (&13 / &20) * t * t - (&1 / &20) * cB * t) +
       S * (--(&7 / &20) - (&1 / &20) * t * t + (&13 / &20) * cB * t - t)` MP_TAC THENL
     [UNDISCH_TAC `cB * cB + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
     RASM_ARITH_TAC];
    MP_TAC(SPECL [`cD:real`; `--S:real`; `uD:real`; `vD:real`; `aD:real`; `&2`; `&2`;
                  `-- --t:real`; `cB:real`] ABT_STRICT_BOUNDS) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[REAL_POW_2; REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;
