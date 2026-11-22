(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C1091/DirectDomains.lean.          *)
(* C1091's actual 3/3-exemption owner domains and the points they force.    *)
(* Owners (Lean owners p i = owner (masks i)): 0 -> 1, 4 -> 258, 5 -> 512,  *)
(* 6 -> 1024, 7 -> 2048, 8 -> 4096, 9 -> 8192, 10 -> 16384, 11 -> 32768.    *)
(* The private cut lemmas (decide over the allowed lists) are evaluated      *)
(* inside OO_DOMAIN_CASES_TAC.                                               *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1091_OriginalData.ml";;
needs "n12/geometry/Helpers.ml";;

let C1091DD_F = `c1091od_family`;;

(* Lean: exemption_count *)
let C1091DD_EXEMPTION_COUNT = prove
 (`forall k. k < 2 ==> CARD (c1091od_family INTER auxex k) = 3`,
  REWRITE_TAC[ARITH_RULE `k < 2 <=> k = 0 \/ k = 1`] THEN GEN_TAC THEN
  DISCH_THEN (DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[card_exempt C1091DD_F 0; card_exempt C1091DD_F 1]);;

(* Lean: northwest, left, bottom, right, top (ofCombined), northeast (ofTransformedCombined) *)
let C1091DD_NORTHWEST = ro_combined C1091DD_F 13;;
let C1091DD_LEFT = ro_combined C1091DD_F 17;;
let C1091DD_BOTTOM = ro_combined C1091DD_F 19;;
let C1091DD_RIGHT = ro_combined C1091DD_F 21;;
let C1091DD_TOP = ro_combined C1091DD_F 24;;
let C1091DD_NORTHEAST =
  ro_transformed C1091DD_F 1024 (false, true, false) 13 RO_REFLECTXF RO_REFLECTXG
    (mlh_reflected_allowed 13);;

let own_tm m x y = list_mk_comb(`linside`,
  [list_mk_comb(`ooc`, [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; mk_small_numeral m]);
   list_mk_comb(`oos`, [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; mk_small_numeral m]);
   list_mk_comb(`oou`, [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; mk_small_numeral m]);
   list_mk_comb(`oov`, [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; mk_small_numeral m]);
   `l:real`; x; y]);;

(* Lean: left_pair *)
let C1091DD_LEFT_PAIR = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1091od_family /\
     linside (ooc c1 c2 a b l 258) (oos c1 c2 a b l 258) (oou c1 c2 a b l 258) (oov c1 c2 a b l 258) l
             (&1) (&87 / &50)
     ==> linside (ooc c1 c2 a b l 4096) (oos c1 c2 a b l 4096) (oou c1 c2 a b l 4096) (oov c1 c2 a b l 4096) l
                 (&1) (&113 / &50) /\
         linside (ooc c1 c2 a b l 4096) (oos c1 c2 a b l 4096) (oou c1 c2 a b l 4096) (oov c1 c2 a b l 4096) l
                 (&1) (&12 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  OO_ABSENT_TAC C1091DD_F 4096 0 258 THEN
  REWRITE_TAC[oo_aux_point 1; oo_aux_point 11] THEN OO_DOMAIN_CASES_TAC C1091DD_LEFT);;

(* Lean: bottom_far *)
let C1091DD_BOTTOM_FAR = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1091od_family /\
     linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512) (oov c1 c2 a b l 512) l
             (&2) (&87 / &50)
     ==> linside (ooc c1 c2 a b l 8192) (oos c1 c2 a b l 8192) (oou c1 c2 a b l 8192) (oov c1 c2 a b l 8192) l
                 (&12 / &5) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (own_tm 1 `&8 / &5` `&1`) ASSUME_TAC THENL
   [MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&28 / &25`; `&87 / &50`] THEN
    ASM_SIMP_TAC[c1091od_seed 0 (`&28 / &25`, `&1`); c1091od_seed 0 (`&87 / &50`, `&1`)] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  OO_ABSENT_TAC C1091DD_F 8192 2 1 THEN OO_ABSENT_TAC C1091DD_F 8192 4 512 THEN
  REWRITE_TAC[oo_aux_point 6] THEN OO_DOMAIN_CASES_TAC C1091DD_BOTTOM);;

(* Lean: right_pair *)
let C1091DD_RIGHT_PAIR = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1091od_family /\
     linside (ooc c1 c2 a b l 1024) (oos c1 c2 a b l 1024) (oou c1 c2 a b l 1024) (oov c1 c2 a b l 1024) l
             (&3) (&113 / &50)
     ==> linside (ooc c1 c2 a b l 16384) (oos c1 c2 a b l 16384) (oou c1 c2 a b l 16384)
                 (oov c1 c2 a b l 16384) l (&3) (&87 / &50) /\
         linside (ooc c1 c2 a b l 16384) (oos c1 c2 a b l 16384) (oou c1 c2 a b l 16384)
                 (oov c1 c2 a b l 16384) l (&3) (&8 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  OO_ABSENT_TAC C1091DD_F 16384 9 1024 THEN
  REWRITE_TAC[oo_aux_point 8; oo_aux_point 18] THEN OO_DOMAIN_CASES_TAC C1091DD_RIGHT);;

(* Lean: top_pair *)
let C1091DD_TOP_PAIR = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1091od_family /\
     linside (ooc c1 c2 a b l 2048) (oos c1 c2 a b l 2048) (oou c1 c2 a b l 2048) (oov c1 c2 a b l 2048) l
             (&8 / &5) (&3)
     ==> linside (ooc c1 c2 a b l 32768) (oos c1 c2 a b l 32768) (oou c1 c2 a b l 32768)
                 (oov c1 c2 a b l 32768) l (&12 / &5) (&3) /\
         linside (ooc c1 c2 a b l 32768) (oos c1 c2 a b l 32768) (oou c1 c2 a b l 32768)
                 (oov c1 c2 a b l 32768) l (&113 / &50) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  OO_ABSENT_TAC C1091DD_F 32768 3 2048 THEN
  REWRITE_TAC[oo_aux_point 7; oo_aux_point 17] THEN OO_DOMAIN_CASES_TAC C1091DD_TOP);;

(* Lean: northwest_cover *)
let C1091DD_NORTHWEST_COVER = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1091od_family /\
     linside (ooc c1 c2 a b l 4096) (oos c1 c2 a b l 4096) (oou c1 c2 a b l 4096) (oov c1 c2 a b l 4096) l
             (&1) (&12 / &5)
     ==> linside (ooc c1 c2 a b l 2048) (oos c1 c2 a b l 2048) (oou c1 c2 a b l 2048) (oov c1 c2 a b l 2048) l
                 (&87 / &50) (&2) \/
         linside (ooc c1 c2 a b l 2048) (oos c1 c2 a b l 2048) (oou c1 c2 a b l 2048) (oov c1 c2 a b l 2048) l
                 (&87 / &50) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  OO_ABSENT_TAC C1091DD_F 2048 11 4096 THEN
  REWRITE_TAC[oo_aux_point 13; oo_aux_point 14] THEN OO_DOMAIN_CASES_TAC C1091DD_NORTHWEST);;

(* Lean: northeast_outer *)
let C1091DD_NORTHEAST_OUTER = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1091od_family /\
     linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512) (oov c1 c2 a b l 512) l
             (&113 / &50) (&2) /\
     linside (ooc c1 c2 a b l 32768) (oos c1 c2 a b l 32768) (oou c1 c2 a b l 32768) (oov c1 c2 a b l 32768) l
             (&113 / &50) (&3)
     ==> linside (ooc c1 c2 a b l 1024) (oos c1 c2 a b l 1024) (oou c1 c2 a b l 1024) (oov c1 c2 a b l 1024) l
                 (&3) (&12 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  OO_ABSENT_TAC C1091DD_F 1024 16 512 THEN OO_ABSENT_TAC C1091DD_F 1024 17 32768 THEN
  REWRITE_TAC[oo_aux_point 19] THEN OO_DOMAIN_CASES_TAC C1091DD_NORTHEAST);;
