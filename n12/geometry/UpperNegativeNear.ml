(* ========================================================================= *)
(* Port of Compact/Cases/C868/UpperNegativeNear.lean (N12Compact.C868 and    *)
(* N12Compact.C868.UpperNegativeNear, Jatloe).                               *)
(* Normal / normal_bounds = c977cc_normal / C977CC_NORMAL_BOUNDS,            *)
(* CanonicalProjection.after = CCCP_AFTER.  A square H is c s u v a; Lean    *)
(* H.translated 2 2 as in UpperNegativeInward.ml.  Tag C868NR_.              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/UpperNegativeInwardCenter.ml";;
needs "n12/geometry/CP_OtherCases_MergedPending_NegativeUpperFaces.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;

let C868NR_NORMAL_TAC =
  FIRST_ASSUM(fun th ->
    if fst(strip_comb(concl th)) = `c977cc_normal` then
      STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)
    else NO_TAC);;

(* Lean: UpperNegativeNear.lower_v *)
let C868NR_LOWER_V = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ c977cc_normal c (--s) /\
     linside c s u v a (--(&7 / &20)) (&7 / &20) /\
     linside c s u v a (&7 / &20) (&7 / &20) /\
     ~linside c s u v a (--(&1 / &20)) (--(&1 / &20))
     ==> --(&1 / &20) * (c - s) <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C868NR_NORMAL_TAC THEN
  C868UI_UNFOLD_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C868UI_POINT_TAC `~linside c s u v a (--(&1 / &20)) (--(&1 / &20))`);;

(* Lean: UpperNegativeNear.top_cap_tilt *)
let C868NR_TOP_CAP_TILT = prove
 (`forall c s (u:real) v a.
     c * c + s * s = &1 /\ &0 < a /\ c977cc_normal c (--s) /\ &1 < a /\
     --(&1 / &20) * (c - s) <= v /\ v + a <= &543 / &500 * c
     ==> --(&3) * s < &2 * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C868NR_NORMAL_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C868UI_USE [`c:real`; `--s`; `&45 / &53`; `&28 / &53`; `&142 / &125`; `&1 / &20`]
    CCCP_AFTER THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: UpperNegativeNear.top_right_faces *)
let C868NR_TOP_RIGHT_FACES = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ c977cc_normal c (--s) /\
     linside c s u v a (&7 / &20) (&7 / &20) /\
     ~linside c s u v a (&13 / &50) (&1)
     ==> &13 / &50 * c + s <= u \/ v + a <= c - &13 / &50 * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C868NR_NORMAL_TAC THEN
  C868UI_UNFOLD_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT; GSYM DE_MORGAN_THM] THEN STRIP_TAC THEN
  C868UI_POINT_TAC `~linside c s u v a (&13 / &50) (&1)`);;

(* Lean: negative_upper_near_lower *)
let C868NR_NEGATIVE_UPPER_NEAR_LOWER = prove
 (`forall c1 c2 a b l cH sH uH vH aH.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     cH * cH + sH * sH = &1 /\ &0 < aH /\
     c977cc_normal cH (--sH) /\
     (forall x y. linside cH sH uH vH aH x y <=>
            linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                    (oov c1 c2 a b l 3072) l x y)
     ==> --(&1 / &20) * (cH - sH) <= vH - (--sH * &2 + cH * &2)`,
  C868UI_INTRO_TAC THEN
  MATCH_MP_TAC (SPECL [`cH:real`; `sH:real`; `uH - (cH * &2 + sH * &2)`;
                       `vH - (--sH * &2 + cH * &2)`; `aH:real`] C868NR_LOWER_V) THEN
  C868UI_TRANSLATE_TAC THEN
  C868UI_FACTS_TAC
   [c868_seed_f 3072 (`&33 / &20`, `&47 / &20`);
    c868_seed_f 3072 (`&47 / &20`, `&47 / &20`);
    c868ui_excl 3072 256 (c868_mp C868IC_SOUTHWEST_NEAR_POINT)]);;

(* Lean: negative_upper_top_right_faces *)
let C868NR_NEGATIVE_UPPER_TOP_RIGHT_FACES = prove
 (`forall c1 c2 a b l cH sH uH vH aH.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     cH * cH + sH * sH = &1 /\ &0 < aH /\
     c977cc_normal cH (--sH) /\
     (forall x y. linside cH sH uH vH aH x y <=>
            linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                    (oov c1 c2 a b l 3072) l x y)
     ==> &13 / &50 * cH + sH <= uH - (cH * &2 + sH * &2) \/
         (vH - (--sH * &2 + cH * &2)) + aH <= cH - &13 / &50 * sH`,
  C868UI_INTRO_TAC THEN
  MATCH_MP_TAC (SPECL [`cH:real`; `sH:real`; `uH - (cH * &2 + sH * &2)`;
                       `vH - (--sH * &2 + cH * &2)`; `aH:real`] C868NR_TOP_RIGHT_FACES) THEN
  C868UI_TRANSLATE_TAC THEN
  C868UI_FACTS_TAC
   [c868_seed_f 3072 (`&47 / &20`, `&47 / &20`);
    c868_excl_f 3072 16 (c868_mp C868AO_ADDITIONAL_INSIDE.(1))]);;
