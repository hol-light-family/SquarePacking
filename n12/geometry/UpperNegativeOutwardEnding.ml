(* ========================================================================= *)
(* Port of Compact/Cases/C868/UpperNegativeOutwardEnding.lean                *)
(* (N12Compact.C868 and N12Compact.C868.UpperNegativeOutward, Jatloe).       *)
(* Lean private axisMargin is RemainingScalars' leftMargin                    *)
(* (c868rs_leftmargin, the identical polynomial); left_axis_weak /           *)
(* left_axis_margin = C868RS_LEFT_AXIS_WEAK / C868RS_LEFT_AXIS_MARGIN;        *)
(* C981CompletionSupportForms.lower_in_bands = C981SF_LOWER_IN_BANDS.         *)
(* Squares H = cH sH uH vH aH, B = cB sB uB vB aB as in Separation.  Tag     *)
(* C868OE_.                                                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/UpperNegativeOutwardSeparation.ml";;
needs "n12/geometry/UpperNegativeOutwardRemainingScalars.ml";;
needs "n12/geometry/UpperNegativeNear.ml";;

(* Lean: left_axis_gap (private) *)
let C868OE_LEFT_AXIS_GAP = prove
 (`forall cH sH uH vH aH cB sB uB vB aB.
     cH * cH + sH * sH = &1 /\ &0 < aH /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     ocmpnuf_input cH sH uH vH aH /\ c868op_faces cB sB uB vB aB /\
     aH = aB /\ &1000 < &525 * cH + &961 * --sH
     ==> c868rs_leftmargin cH (--sH) cB (--sB) + uH - &543 / &500 * sH <=
         uH + aH - ABT_lower cB sB uB vB aB cH sH`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aH:real = aB`)) THEN
  C868SP_SETUP_TAC THEN
  C868SP_USE [`cH:real`; `--sH`] C868OS_STEEP_OF_PROJECTION THEN
  C868SP_USE [`cB:real`; `--sB`] C868OS_OUTWARD_SINE_CAP THEN
  C868SP_USE [`cB:real`; `--sB`; `cH:real`; `--sH`] CCUCC_CROSS_ORDER THEN
  C868SP_PROD `cB:real` `cH:real` THEN C868SP_PROD `--sB` `--sH` THEN
  SUBGOAL_THEN `&0 <= cH * cB + sH * sB` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= --sH * cB + cH * sB` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `--cH * sB + sH * cB <= &0` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  REWRITE_TAC[C981SF_LOWER_IN_BANDS] THEN
  SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_ARITH `x <= &0 ==> abs x = --x`;
           ASSUME `&0 <= cH * cB + sH * sB`; ASSUME `--cH * sB + sH * cB <= &0`] THEN
  SUBGOAL_THEN
   `(cH * cB + sH * sB) * (cB - sB) + (--sH * cB + cH * sB) * (cB + &4 / &5 * sB) =
    cH - sH + &1 / &5 * --sB * (--sH * cB + cH * sB)` ASSUME_TAC THENL
  [UNDISCH_TAC `cB * cB + sB * sB = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C868SP_PROD `cH * cB + sH * sB` `(cB - sB) - (uB + aB)` THEN
  C868SP_PROD `--sH * cB + cH * sB` `vB - (--(&4 / &5) * sB - cB)` THEN
  C868SP_PROD `&1 + (cH * cB + sH * sB) + (--sH * cB + cH * sB)` `aB - &1` THEN
  REWRITE_TAC[c868rs_leftmargin] THEN NLIN_TAC ~deg2:false []);;

(* Lean: top_lower_impossible *)
let C868OE_TOP_LOWER_IMPOSSIBLE = prove
 (`forall cH sH uH vH aH cB sB uB vB aB.
     cH * cH + sH * sH = &1 /\ &0 < aH /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     ocmpnuf_input cH sH uH vH aH /\ c868op_faces cB sB uB vB aB /\
     aH = aB /\ &543 / &500 * sH <= uH /\
     linside cB sB uB vB aB (&7 / &20) (--(&7 / &20)) /\
     linside cB sB uB vB aB (&21 / &40) (&1 / &8) /\
     --(&1 / &20) * (cH - sH) <= vH /\
     (&13 / &50 * cH + sH <= uH \/ vH + aH <= cH - &13 / &50 * sH) /\
     ldisj cH sH uH vH aH cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  C868SP_USE (C868SP_H @ C868SP_B) C868SP_PROJECTION THEN
  C868SP_USE (C868SP_H @ C868SP_B) C868SP_SEPARATION THEN
  C868SP_USE (C868SP_H @ C868SP_B) C868OE_LEFT_AXIS_GAP THEN
  C868SP_SETUP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
  [C868SP_USE [`cH:real`; `--sH`; `cB:real`; `--sB`] C868RS_LEFT_AXIS_WEAK THEN
   NLIN_TAC ~deg2:false [];
   C868SP_USE [`cH:real`; `--sH`; `cB:real`; `--sB`] C868RS_LEFT_AXIS_MARGIN THEN
   NLIN_TAC ~deg2:false []]);;

(* Lean: negative_upper_top_cap *)
let C868OE_NEGATIVE_UPPER_TOP_CAP = prove
 (`forall c1 c2 a b l cH sH uH vH aH.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     cH * cH + sH * sH = &1 /\ &0 < aH /\
     c977cc_normal cH (--sH) /\ aH = l /\
     (forall x y. linside cH sH uH vH aH x y <=>
            linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                    (oov c1 c2 a b l 3072) l x y)
     ==> (vH - (--sH * &2 + cH * &2)) + aH <= &543 / &500 * cH`,
  C868UI_INTRO_TAC THEN
  C868UI_APP_TAC C868UI_NEGATIVE_UPPER_INPUT THEN
  MP_TAC (SPECL [`cH:real`; `sH:real`; `uH - (cH * &2 + sH * &2)`;
                 `vH - (--sH * &2 + cH * &2)`; `aH:real`] OCMPNUF_TOP_MARKER_FACES) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  let missing = c868_mp C868IC_SOUTHEAST_OUTWARD_REQUIRED in
  ASSUME_TAC missing THEN
  C868UI_APP_TAC C868OP_SOUTHEAST_OUTWARD_PROFILE THEN
  MAP_EVERY ASSUME_TAC (CONJUNCTS (c868ui_app C868SE_SOUTHEAST_OUTWARD_POINTS [missing])) THEN
  C868UI_APP_TAC C868NR_NEGATIVE_UPPER_NEAR_LOWER THEN
  C868UI_APP_TAC C868NR_NEGATIVE_UPPER_TOP_RIGHT_FACES THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `cB:real` (X_CHOOSE_THEN `sB:real` (X_CHOOSE_THEN `uB:real`
    (X_CHOOSE_THEN `vB:real` (X_CHOOSE_THEN `aB:real` STRIP_ASSUME_TAC)))) o
    check (is_exists o concl)) THEN
  MATCH_MP_TAC (TAUT `false ==> p`) THEN
  MATCH_MP_TAC (SPECL [`cH:real`; `sH:real`; `uH - (cH * &2 + sH * &2)`;
      `vH - (--sH * &2 + cH * &2)`; `aH:real`;
      `cB:real`; `sB:real`; `uB - (cB * &2 + sB * &2)`;
      `vB - (--sB * &2 + cB * &2)`; `aB:real`] C868OE_TOP_LOWER_IMPOSSIBLE) THEN
  REWRITE_TAC[ldisj] THEN C868UI_TRANSLATE_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE REAL_RAT_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (UNDISCH_TAC `aH:real = l` THEN UNDISCH_TAC `aB:real = l` THEN REAL_ARITH_TAC) ORELSE
   ACCEPT_TAC (c868_seed_f 512 (`&47 / &20`, `&33 / &20`)) ORELSE
   (REPEAT GEN_TAC THEN ACCEPT_TAC (SPECL [`&2 + x`; `&2 + y`]
      (REWRITE_RULE[ldisj] (c868_apart_f 3072 512))))));;
