(* ========================================================================= *)
(* Port of Compact/Cases/C868/UpperNegativeOutwardSeparation.lean            *)
(* (N12Compact.C868 and N12Compact.C868.UpperNegativeOutward, Jatloe).       *)
(* H = cH sH uH vH aH (merged square, Input = ocmpnuf_input), B = cB sB uB   *)
(* vB aB (Faces = c868op_faces).  ABTransverse upper / lower = ABT_upper /    *)
(* ABT_lower, strict_bounds / ownU / separated / parallel_radius /           *)
(* transverse_radius = ABT_*; CongruentSAT.faceSeparation_of_disjoint =      *)
(* CSAT_FACESEPARATION_OF_DISJOINT (C977CB_faceSep);                          *)
(* C981CompletionSupportForms.upper_in_bands = C981SF_UPPER_IN_BANDS;         *)
(* UnitCircleChord.cross_order = CCUCC_CROSS_ORDER; Lean                      *)
(* ∀ x y, ¬(H.Inside x y ∧ B.Inside x y) = ldisj H B.  Tag C868SP_.          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/UpperNegativeOutwardProfile.ml";;
needs "n12/geometry/UpperNegativeOutwardScalars.ml";;
needs "n12/geometry/UpperNegativeInward.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/CongruentSAT.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;

let C868SP_H = [`cH:real`; `sH:real`; `uH:real`; `vH:real`; `aH:real`];;
let C868SP_B = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`];;

(* discharge also unit-direction equalities *)
let C868SP_DISCH_TAC =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE (CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC) ORELSE
   (REWRITE_TAC[REAL_POW_2; REAL_NEG_MUL2] THEN
    ASSUM_LIST(fun ths -> MP_TAC (end_itlist CONJ (filter (fun th ->
      is_eq(concl th) && type_of(lhs(concl th)) = `:real` &&
      can (find_term (fun t -> t = `(*):real->real->real`)) (concl th)) ths))) THEN
    REAL_ARITH_TAC) ORELSE
   NLIN_TAC ~deg2:false []);;
let C868SP_USE tms th =
  MP_TAC (SPECL tms th) THEN ANTS_TAC THENL
   [C868SP_DISCH_TAC; DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))];;

(* &0 <= x * y  from  &0 <= x  and  &0 <= y  (linear consequences of assumptions) *)
let C868SP_PROD x y =
  SUBGOAL_THEN (mk_binop `(<=):real->real->bool` `&0` (mk_binop `(*):real->real->real` x y))
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC];;

(* the facts of Input H and Faces B, with the normal bounds *)
let C868SP_SETUP_TAC =
  TRY(FIRST_ASSUM(fun th ->
    if fst(strip_comb(concl th)) = `ocmpnuf_input` then
      let th1 = REWRITE_RULE[ocmpnuf_input] th in
      STRIP_ASSUME_TAC th1 THEN
      STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS (CONJUNCT1 th1)) THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] (CONJUNCT1 th1))
    else NO_TAC)) THEN
  TRY(FIRST_ASSUM(fun th ->
    if fst(strip_comb(concl th)) = `c868op_faces` then
      let th1 = REWRITE_RULE[c868op_faces] th in
      STRIP_ASSUME_TAC th1 THEN
      STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS (CONJUNCT1 th1)) THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] (CONJUNCT1 th1))
    else NO_TAC));;

(* Lean: projection (private) *)
let C868SP_PROJECTION = prove
 (`forall cH sH uH vH aH cB sB uB vB aB.
     cH * cH + sH * sH = &1 /\ &0 < aH /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     ocmpnuf_input cH sH uH vH aH /\
     &543 / &500 * sH <= uH /\
     linside cB sB uB vB aB (&21 / &40) (&1 / &8) /\
     ldisj cH sH uH vH aH cB sB uB vB aB
     ==> &1000 < &525 * cH - &961 * sH`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C868SP_SETUP_TAC THEN
  C868SP_USE C868SP_H OCMPNUF_TOP_LOWER_TILT THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C868SP_USE C868SP_H OCMPNUF_SHARP_POINT THEN
  UNDISCH_TAC `ldisj cH sH uH vH aH cB sB uB vB aB` THEN
  REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&21 / &40`; `&1 / &8`]) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: right_axis_overlap *)
let C868SP_RIGHT_AXIS_OVERLAP = prove
 (`forall cH sH uH vH aH cB sB uB vB aB.
     cH * cH + sH * sH = &1 /\ &0 < aH /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     ocmpnuf_input cH sH uH vH aH /\ c868op_faces cB sB uB vB aB /\
     aH = aB /\ &543 / &500 * sH <= uH /\
     linside cB sB uB vB aB (&21 / &40) (&1 / &8) /\
     ldisj cH sH uH vH aH cB sB uB vB aB
     ==> uB < ABT_upper cH sH uH vH aH cB sB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C868SP_USE (C868SP_H @ C868SP_B) C868SP_PROJECTION THEN
  C868SP_USE C868SP_H OCMPNUF_LOWER_V THEN
  C868SP_SETUP_TAC THEN
  C868SP_USE [`cH:real`; `--sH`] C868OS_STEEP_OF_PROJECTION THEN
  C868SP_USE [`cB:real`; `--sB`] C868OS_OUTWARD_SINE_CAP THEN
  C868SP_USE [`cH:real`; `--sH`; `cB:real`; `--sB`] C868OS_RIGHT_AXIS_MARGIN THEN
  C868SP_USE [`cB:real`; `--sB`; `cH:real`; `--sH`] CCUCC_CROSS_ORDER THEN
  C868SP_PROD `cB:real` `cH:real` THEN C868SP_PROD `--sB` `--sH` THEN
  SUBGOAL_THEN `&0 <= cB * cH + sB * sH` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= --cB * sH + sB * cH` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  REWRITE_TAC[C981SF_UPPER_IN_BANDS] THEN
  SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`;
           ASSUME `&0 <= cB * cH + sB * sH`; ASSUME `&0 <= --cB * sH + sB * cH`] THEN
  C868SP_PROD `cB * cH + sB * sH` `uH - &543 / &500 * sH` THEN
  C868SP_PROD `--cB * sH + sB * cH` `vH - &13 / &50 * sH` THEN
  C868SP_PROD `&1 + (cB * cH + sB * sH) + (--cB * sH + sB * cH)` `aH - &1` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: separation *)
let C868SP_SEPARATION = prove
 (`forall cH sH uH vH aH cB sB uB vB aB.
     cH * cH + sH * sH = &1 /\ &0 < aH /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     ocmpnuf_input cH sH uH vH aH /\ c868op_faces cB sB uB vB aB /\
     aH = aB /\ &543 / &500 * sH <= uH /\
     linside cB sB uB vB aB (&7 / &20) (--(&7 / &20)) /\
     linside cB sB uB vB aB (&21 / &40) (&1 / &8) /\
     ldisj cH sH uH vH aH cB sB uB vB aB
     ==> uH + aH <= ABT_lower cB sB uB vB aB cH sH`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C868SP_USE (C868SP_H @ C868SP_B) C868SP_RIGHT_AXIS_OVERLAP THEN
  C868SP_USE C868SP_H OCMPNUF_TOP_LOWER_TILT THEN
  C868SP_USE (C868SP_H @ C868SP_B) CSAT_FACESEPARATION_OF_DISJOINT THEN
  C868SP_SETUP_TAC THEN
  C868SP_USE C868SP_H ABT_OWNU THEN C868SP_USE C868SP_B ABT_OWNU THEN
  let unitH = ASSUME `cH * cH + sH * sH = &1` and unitB = ASSUME `cB * cB + sB * sB = &1` in
  let sep q r nx ny e = REWRITE_RULE[e] (SPECL (q @ r @ [nx; ny]) ABT_SEPARATED) in
  let e1 = MP (SPECL [`cH:real`; `sH:real`; `aH:real`; `cB:real`; `sB:real`; `aB:real`]
                 ABT_PARALLEL_RADIUS) unitH
  and e2 = MP (SPECL [`cH:real`; `sH:real`; `aH:real`; `cB:real`; `sB:real`; `aB:real`]
                 ABT_TRANSVERSE_RADIUS) unitH
  and e3 = ONCE_REWRITE_RULE[REAL_ADD_SYM]
            (MP (SPECL [`cB:real`; `sB:real`; `aB:real`; `cH:real`; `sH:real`; `aH:real`]
                 ABT_PARALLEL_RADIUS) unitB)
  and e4 = ONCE_REWRITE_RULE[REAL_ADD_SYM]
            (MP (SPECL [`cB:real`; `sB:real`; `aB:real`; `cH:real`; `sH:real`; `aH:real`]
                 ABT_TRANSVERSE_RADIUS) unitB) in
  let case th = MP_TAC th THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
                DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) in
  let sb sq x y nx ny = C868SP_USE (sq @ [x; y; nx; ny]) ABT_STRICT_BOUNDS in
  let mH = `--(&7 / &20)` and pH = `&7 / &20` in
  FIRST_X_ASSUM(MP_TAC o check (fun th -> fst(strip_comb(concl th)) = `C977CB_faceSep`)) THEN
  REWRITE_TAC[C977CB_faceSep] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
  [case (sep C868SP_H C868SP_B `cH:real` `sH:real` e1) THENL
   [NLIN_TAC ~deg2:false [];
    sb C868SP_B pH mH `cH:real` `sH:real` THEN sb C868SP_H mH pH `cH:real` `sH:real` THEN
    NLIN_TAC ~deg2:false []];
   case (sep C868SP_H C868SP_B `--sH` `cH:real` e2) THENL
   [sb C868SP_H pH pH `--sH` `cH:real` THEN sb C868SP_B pH mH `--sH` `cH:real` THEN
    NLIN_TAC ~deg2:false [];
    sb C868SP_B `&21 / &40` `&1 / &8` `--sH` `cH:real` THEN
    sb C868SP_H mH pH `--sH` `cH:real` THEN NLIN_TAC ~deg2:false []];
   case (sep C868SP_H C868SP_B `cB:real` `sB:real` e3) THENL
   [NLIN_TAC ~deg2:false [];
    sb C868SP_B pH mH `cB:real` `sB:real` THEN sb C868SP_H mH pH `cB:real` `sB:real` THEN
    NLIN_TAC ~deg2:false []];
   case (sep C868SP_H C868SP_B `--sB` `cB:real` e4) THENL
   [sb C868SP_H pH pH `--sB` `cB:real` THEN sb C868SP_B pH mH `--sB` `cB:real` THEN
    NLIN_TAC ~deg2:false [];
    sb C868SP_B `&21 / &40` `&1 / &8` `--sB` `cB:real` THEN
    sb C868SP_H mH pH `--sB` `cB:real` THEN NLIN_TAC ~deg2:false []]]);;

(* Lean: negative_upper_outward_separation *)
let C868SP_NEGATIVE_UPPER_OUTWARD_SEPARATION = prove
 (`forall c1 c2 a b l cH sH uH vH aH.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     cH * cH + sH * sH = &1 /\ &0 < aH /\
     c977cc_normal cH (--sH) /\ aH = l /\
     (forall x y. linside cH sH uH vH aH x y <=>
            linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                    (oov c1 c2 a b l 3072) l x y) /\
     ~linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512)
              (oov c1 c2 a b l 512) l (&113 / &50) (&2) /\
     &543 / &500 * sH <= uH - (cH * &2 + sH * &2)
     ==> exists cB sB uB vB aB.
           cB * cB + sB * sB = &1 /\ &0 < aB /\ aB = l /\
           (forall x y. linside cB sB uB vB aB x y <=>
                  linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512)
                          (oov c1 c2 a b l 512) l x y) /\
           c868op_faces cB sB (uB - (cB * &2 + sB * &2)) (vB - (--sB * &2 + cB * &2)) aB /\
           (uH - (cH * &2 + sH * &2)) + aH <=
             ABT_lower cB sB (uB - (cB * &2 + sB * &2)) (vB - (--sB * &2 + cB * &2)) aB cH sH`,
  C868UI_INTRO_TAC THEN
  C868UI_APP_TAC C868UI_NEGATIVE_UPPER_INPUT THEN
  C868UI_APP_TAC C868OP_SOUTHEAST_OUTWARD_PROFILE THEN
  MAP_EVERY ASSUME_TAC (CONJUNCTS (c868ui_app C868SE_SOUTHEAST_OUTWARD_POINTS
    [ASSUME (mk_neg (c868ui_lin 512 `&113 / &50` `&2`))])) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `cB:real` (X_CHOOSE_THEN `sB:real` (X_CHOOSE_THEN `uB:real`
    (X_CHOOSE_THEN `vB:real` (X_CHOOSE_THEN `aB:real` STRIP_ASSUME_TAC)))) o
    check (is_exists o concl)) THEN
  MAP_EVERY EXISTS_TAC [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
  REPEAT(CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  MATCH_MP_TAC (SPECL [`cH:real`; `sH:real`; `uH - (cH * &2 + sH * &2)`;
      `vH - (--sH * &2 + cH * &2)`; `aH:real`;
      `cB:real`; `sB:real`; `uB - (cB * &2 + sB * &2)`;
      `vB - (--sB * &2 + cB * &2)`; `aB:real`] C868SP_SEPARATION) THEN
  REWRITE_TAC[ldisj] THEN C868UI_TRANSLATE_TAC THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (UNDISCH_TAC `aH:real = l` THEN UNDISCH_TAC `aB:real = l` THEN REAL_ARITH_TAC) ORELSE
   ACCEPT_TAC (c868_seed_f 512 (`&47 / &20`, `&33 / &20`)) ORELSE
   (REPEAT GEN_TAC THEN ACCEPT_TAC (SPECL [`&2 + x`; `&2 + y`]
      (REWRITE_RULE[ldisj] (c868_apart_f 3072 512))))));;
