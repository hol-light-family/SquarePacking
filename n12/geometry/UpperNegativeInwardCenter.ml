(* ========================================================================= *)
(* Port of Compact/Cases/C868/UpperNegativeInwardCenter.lean                 *)
(* (N12Compact.C868, Jatloe).                                                *)
(* CommonCases.MergedNearPoint.points = CCMNP_POINTS, SouthwestPoint.point = *)
(* CCSWP_POINT, S12.inside_segment = CES_INSIDE_SEGMENT.  Lean's             *)
(* pullSwap (pullX (H.translated (-4) 0)) is the quarter turn                *)
(* (s, --c, u, v, a) of (c, s, u, v, a) (C868IC_QUARTER_TURN).                *)
(* Packing toolkit from UpperNegativeInward.ml.  Tag C868IC_.                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/UpperNegativeInward.ml";;
needs "n12/geometry/AdditionalOwnership.ml";;
needs "n12/geometry/CP_CommonCases_MergedNearPoint.ml";;
needs "n12/geometry/CP_CommonCases_SouthwestPoint.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;

(* Lean: inside_pullSwap / inside_pullX / inside_translated_iff composed *)
let C868IC_QUARTER_TURN = prove
 (`forall c s u v a x y. linside s (--c) u v a x y <=> linside c s u v a (--y) x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: merged_inward_low_points *)
let C868IC_MERGED_INWARD_LOW_POINTS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (--(&7 / &20)) (&7 / &20) /\
     linside c s u v a (&7 / &20) (&7 / &20) /\
     ~linside c s u v a (--(&13 / &50)) (&0) /\
     ~linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (--(&13 / &50)) (&1) /\
     ~linside c s u v a (&13 / &50) (&1) /\
     ~linside c s u v a (&0) (&543 / &500)
     ==> linside c s u v a (--(&1 / &20)) (--(&1 / &20)) /\
         linside c s u v a (&1 / &20) (--(&1 / &20)) /\
         linside c s u v a (&0) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN RULE_ASSUM_TAC(CONV_RULE REAL_RAT_REDUCE_CONV) THEN
  MP_TAC(SPECL [`s:real`; `--c:real`; `u:real`; `v:real`; `a:real`] CCMNP_POINTS) THEN
  REWRITE_TAC[C868IC_QUARTER_TURN] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c * c + s * s = &1` THEN REAL_ARITH_TAC;
   STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `linside c s u v a (-- &1 / &20) (-- &1 / &20)` THEN
  UNDISCH_TAC `linside c s u v a (&7 / &20) (&7 / &20)` THEN
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* merged_inward_low_points at the original coordinates of (owner 3072):
   the square translated by (2,2) (helper for upper_inward_low_points) *)
let C868IC_MERGED_ORIGINAL = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&87 / &50) (&2) /\
     ~linside c s u v a (&113 / &50) (&2) /\
     ~linside c s u v a (&87 / &50) (&3) /\
     ~linside c s u v a (&113 / &50) (&3) /\
     ~linside c s u v a (&2) (&1543 / &500)
     ==> linside c s u v a (&39 / &20) (&39 / &20) /\
         linside c s u v a (&41 / &20) (&39 / &20) /\
         linside c s u v a (&2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`;
                `a:real`] C868IC_MERGED_INWARD_LOW_POINTS) THEN
  REWRITE_TAC[C868UI_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[]);;

(* Lean: upper_inward_low_points *)
let C868IC_UPPER_INWARD_LOW_POINTS = prove
 (`forall c1 c2 a b l.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512)
             (oov c1 c2 a b l 512) l (&113 / &50) (&2)
     ==> linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                 (oov c1 c2 a b l 3072) l (&39 / &20) (&39 / &20) /\
         linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                 (oov c1 c2 a b l 3072) l (&41 / &20) (&39 / &20) /\
         linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                 (oov c1 c2 a b l 3072) l (&2) (&2)`,
  C868UI_INTRO_TAC THEN
  MATCH_MP_TAC (SPECL (c868_own 3072) C868IC_MERGED_ORIGINAL) THEN
  C868UI_FACTS_TAC
   [c868_unit 3072; C868_POS;
    c868_seed_f 3072 (`&33 / &20`, `&47 / &20`);
    c868_seed_f 3072 (`&47 / &20`, `&47 / &20`);
    c868_excl_f 3072 256 (c868_forced_f 1);
    c868ui_excl 3072 512 (ASSUME (c868ui_lin 512 `&113 / &50` `&2`));
    c868_excl_f 3072 32768 (c868_forced_f 2);
    c868_excl_f 3072 16 (c868_mp C868AO_ADDITIONAL_INSIDE.(1));
    c868_excl_f 3072 32768 (c868_seed_f 32768 (`&2`, `&1543 / &500`))]);;

(* Lean: southwest_near_point *)
let C868IC_SOUTHWEST_NEAR_POINT =
  let seg m (x0, y0) (x1, y1) t th0 th1 =
    CONV_RULE REAL_RAT_REDUCE_CONV
      (MP (SPECL (c868_own m @ [x0; y0; x1; y1; t]) CES_INSIDE_SEGMENT)
          (CONJ th0 (CONJ th1 (EQT_ELIM (REAL_RAT_REDUCE_CONV
             (mk_conj(mk_binop `(<=):real->real->bool` `&0` t,
                      mk_binop `(<=):real->real->bool` t `&1`))))))) in
  let bottomLow = c868_forced_f 3 and bottomHigh = c868_forced_f 5 in
  let leftLow = c868_forced_f 4 and leftHigh = c868_forced_f 6 in
  let bottomMiddle = seg 1 (`&8 / &5`, `&1`) (`&87 / &50`, `&1`) `&5 / &14` bottomLow bottomHigh in
  let leftMiddle = seg 2 (`&1`, `&8 / &5`) (`&1`, `&87 / &50`) `&5 / &14` leftLow leftHigh in
  prove
   (`forall c1 c2 a b l.
       NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family
       ==> linside (ooc c1 c2 a b l 256) (oos c1 c2 a b l 256) (oou c1 c2 a b l 256)
                   (oov c1 c2 a b l 256) l (&39 / &20) (&39 / &20)`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC (SPECL (c868_own 256) CCSWP_POINT) THEN
    C868UI_FACTS_TAC
     [c868_unit 256;
      c868_seed_f 256 (`&33 / &20`, `&33 / &20`);
      c868_forced_f 0; c868_forced_f 1;
      c868ui_excl 256 2 leftMiddle;
      c868ui_excl 256 1 bottomHigh;
      c868ui_excl 256 1 bottomMiddle;
      c868ui_excl 256 2 leftHigh]);;

(* Lean: southeast_inward_impossible *)
let C868IC_SOUTHEAST_INWARD_IMPOSSIBLE = prove
 (`forall c1 c2 a b l.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512)
             (oov c1 c2 a b l 512) l (&113 / &50) (&2)
     ==> false`,
  C868UI_INTRO_TAC THEN
  C868UI_APP_TAC C868IC_UPPER_INWARD_LOW_POINTS THEN
  MP_TAC (c868ui_excl 3072 256 (c868_mp C868IC_SOUTHWEST_NEAR_POINT)) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: southeast_outward_required *)
let C868IC_SOUTHEAST_OUTWARD_REQUIRED = prove
 (`forall c1 c2 a b l.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family
     ==> ~linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512)
                  (oov c1 c2 a b l 512) l (&113 / &50) (&2)`,
  MESON_TAC[C868IC_SOUTHEAST_INWARD_IMPOSSIBLE]);;
