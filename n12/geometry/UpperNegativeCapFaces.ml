(* ========================================================================= *)
(* Port of Compact/Cases/C868/UpperNegativeCapFaces.lean (N12Compact.C868    *)
(* and N12Compact.C868.UpperNegativeCap, Jatloe).                            *)
(* Input = ocmpnuf_input; lower_v / lower_u = OCMPNUF_LOWER_V / _U.          *)
(* Squares and translations as in UpperNegativeInward.ml.  Tag C868CF_.      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/UpperNegativeOutwardEnding.ml";;

(* Lean: UpperNegativeCap.sharp_upper *)
let C868CF_SHARP_UPPER = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ ocmpnuf_input c s u v a /\
     v + a <= &543 / &500 * c /\
     ~linside c s u v a (&21 / &40) (&1 / &8)
     ==> u + a <= &21 / &40 * c + &1 / &8 * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C868UI_USE C868UI_SQ OCMPNUF_LOWER_V THEN C868UI_INPUT_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C868UI_POINT_TAC `~linside c s u v a (&21 / &40) (&1 / &8)`);;

(* Lean: UpperNegativeCap.lower_tilt *)
let C868CF_LOWER_TILT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ ocmpnuf_input c s u v a /\
     u + a <= &21 / &40 * c + &1 / &8 * s
     ==> c < -- &5 * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C868UI_USE C868UI_SQ OCMPNUF_LOWER_U THEN C868UI_INPUT_TAC THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: UpperNegativeCap.near_upper *)
let C868CF_NEAR_UPPER = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ ocmpnuf_input c s u v a /\
     v + a <= &543 / &500 * c /\ c < -- &5 * s /\
     ~linside c s u v a (&23 / &50) (&1 / &100)
     ==> u + a <= &23 / &50 * c + &1 / &100 * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C868UI_USE C868UI_SQ OCMPNUF_LOWER_V THEN C868UI_INPUT_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C868UI_POINT_TAC `~linside c s u v a (&23 / &50) (&1 / &100)`);;

(* Lean: UpperNegativeCap.span *)
let C868CF_SPAN = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ ocmpnuf_input c s u v a /\
     u + a <= &23 / &50 * c + &1 / &100 * s
     ==> &1 < &18 / &25 * c - &99 / &100 * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C868UI_USE C868UI_SQ OCMPNUF_LOWER_U THEN C868UI_INPUT_TAC THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: negative_upper_southeast_caps *)
let C868CF_NEGATIVE_UPPER_SOUTHEAST_CAPS = prove
 (`forall c1 c2 a b l cH sH uH vH aH.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     cH * cH + sH * sH = &1 /\ &0 < aH /\
     c977cc_normal cH (--sH) /\ aH = l /\
     (forall x y. linside cH sH uH vH aH x y <=>
            linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                    (oov c1 c2 a b l 3072) l x y)
     ==> (uH - (cH * &2 + sH * &2)) + aH <= &21 / &40 * cH + &1 / &8 * sH /\
         (uH - (cH * &2 + sH * &2)) + aH <= &23 / &50 * cH + &1 / &100 * sH /\
         &1 < &18 / &25 * cH - &99 / &100 * sH`,
  C868UI_INTRO_TAC THEN
  C868UI_APP_TAC C868UI_NEGATIVE_UPPER_INPUT THEN
  C868UI_APP_TAC C868OE_NEGATIVE_UPPER_TOP_CAP THEN
  let missing = c868_mp C868IC_SOUTHEAST_OUTWARD_REQUIRED in
  let pts = c868ui_app C868SE_SOUTHEAST_OUTWARD_POINTS [missing] in
  let ht = [`cH:real`; `sH:real`; `uH - (cH * &2 + sH * &2)`;
            `vH - (--sH * &2 + cH * &2)`; `aH:real`] in
  SUBGOAL_THEN
   `~linside cH sH (uH - (cH * &2 + sH * &2)) (vH - (--sH * &2 + cH * &2)) aH
             (&21 / &40) (&1 / &8) /\
    ~linside cH sH (uH - (cH * &2 + sH * &2)) (vH - (--sH * &2 + cH * &2)) aH
             (&23 / &50) (&1 / &100)` STRIP_ASSUME_TAC THENL
  [C868UI_TRANSLATE_TAC THEN
   C868UI_FACTS_TAC [c868ui_excl 3072 512 (CONJUNCT2 pts);
                     c868ui_excl 3072 512 (CONJUNCT1 pts)];
   ALL_TAC] THEN
  C868UI_USE ht C868CF_SHARP_UPPER THEN
  C868UI_USE ht C868CF_LOWER_TILT THEN
  C868UI_USE ht C868CF_NEAR_UPPER THEN
  C868UI_USE ht C868CF_SPAN THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;
