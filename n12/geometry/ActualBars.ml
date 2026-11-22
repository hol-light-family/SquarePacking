(* ========================================================================= *)
(* Port of Compact/Cases/C868/ActualBars.lean (N12Compact.C868).             *)
(* Continuous wall reach of the original C868 owners 8192 (bottom), 4096     *)
(* (left) and 16416 (right).                                                 *)
(* ContinuousBottom.reach_of_far = C1089CB_REACH_OF_FAR,                     *)
(* C981CompletionWallAdvance.point = C981WA_POINT,                           *)
(* OriginalOwners.vertical_segment = OO_VERTICAL_SEGMENT,                    *)
(* S12.inside_center_distance = C1092WCR_INSIDE_CENTER_DISTANCE,             *)
(* WallSignChord.chord = WSC_CHORD (on pullX, LINSIDE_PULLX).                *)
(* Tag C868AB_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/ActualCrosspoints.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ContinuousBottom.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/C1092WallCenterRegion.ml";;
needs "n12/geometry/WallSignChord.ml";;

(* Lean: bottom_bar *)
let C868AB_BOTTOM_BAR = c868_check
 `forall c1 c2 a b l x. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     &113 / &50 <= x /\ x <= &14 / &5
     ==> linside (ooc c1 c2 a b l 8192) (oos c1 c2 a b l 8192) (oou c1 c2 a b l 8192)
                 (oov c1 c2 a b l 8192) l x (&1)`
 (let facts = [c868_seed_f 8192 (`&2`, `&457 / &500`); c868_mp C868AO_ADDITIONAL_INSIDE.(4);
               c868_excl_f 8192 1 (c868_seed_f 1 (`&87 / &50`, `&1`));
               c868_excl_f 8192 1 (c868_seed_f 1 (`&187 / &100`, `&19 / &25`));
               c868_excl_f 8192 512 (c868_seed_f 512 (`&47 / &20`, `&33 / &20`))] in
  let r = CONJUNCT2 (CONJUNCT2 (c868_apply C1089CB_REACH_OF_FAR (c868_own 8192) facts)) in
  let h = `&113 / &50 <= x /\ x <= &14 / &5` in
  c868_genx [`x:real`] [h] (MP (SPEC `x:real` r) (ASSUME h)));;

(* Lean: left_bar *)
let C868AB_LEFT_BAR = c868_check
 `forall c1 c2 a b l y. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     &113 / &50 <= y /\ y <= &14 / &5
     ==> linside (ooc c1 c2 a b l 4096) (oos c1 c2 a b l 4096) (oou c1 c2 a b l 4096)
                 (oov c1 c2 a b l 4096) l (&1) y`
 (let near = c868_mp C868AO_ADDITIONAL_INSIDE.(2) in
  let facts = [c868_seed_f 4096 (`&457 / &500`, `&2`); c868_mp C868AO_ADDITIONAL_INSIDE.(3);
               c868_excl_f 4096 2 (c868_seed_f 2 (`&1`, `&87 / &50`));
               c868_excl_f 4096 2 (c868_seed_f 2 (`&19 / &25`, `&187 / &100`));
               c868_excl_f 4096 3072 (c868_seed_f 3072 (`&33 / &20`, `&47 / &20`))] in
  let last = c868_apply C981WA_POINT (c868_own 4096) facts in
  let h = `&113 / &50 <= y /\ y <= &14 / &5` in
  let hy = ASSUME h in
  let seg = c868_apply OO_VERTICAL_SEGMENT (c868_own 4096 @ [`&1`; `&113 / &50`; `&14 / &5`; `y:real`])
              [near; last; CONJUNCT1 hy; CONJUNCT2 hy] in
  c868_genx [`y:real`] [h] seg);;

(* Lean: right_center *)
let C868AB_RIGHT_CENTER = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family
     ==> &9 / &4 < lcy (ooc c1 c2 a b l 16416) (oos c1 c2 a b l 16416) (oou c1 c2 a b l 16416)
                       (oov c1 c2 a b l 16416) l /\
         lcy (ooc c1 c2 a b l 16416) (oos c1 c2 a b l 16416) (oou c1 c2 a b l 16416)
             (oov c1 c2 a b l 16416) l < &11 / &4`,
  let c868ab_lo = c868_seed 16416 (`&1543 / &500`, `&2`)
  and c868ab_hi = c868_seed 16416 (`&1543 / &500`, `&3`) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP c868ab_lo) THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP c868ab_hi) THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP OO_SIDE o CONJUNCT1) THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP OO_SIDE_LE o CONJUNCT1) THEN
  FIRST_ASSUM (ASSUME_TAC o SPEC `16416` o MATCH_MP OO_UNIT o CONJUNCT1) THEN
  MAP_EVERY (fun p -> MP_TAC (SPECL (c868_own 16416 @ p) C1092WCR_INSIDE_CENTER_DISTANCE) THEN
                      ASM_REWRITE_TAC[] THEN DISCH_TAC) [[`&1543 / &500`; `&2`]; [`&1543 / &500`; `&3`]] THEN
  POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC o filter (fun th -> not (can (find_term ((=) `linside`)) (concl th)) &&
                                                          not (can (find_term ((=) `NPACK`)) (concl th)))) THEN
  ABBREV_TAC `X = lcx (ooc c1 c2 a b l 16416) (oos c1 c2 a b l 16416) (oou c1 c2 a b l 16416)
                      (oov c1 c2 a b l 16416) l` THEN
  ABBREV_TAC `Y = lcy (ooc c1 c2 a b l 16416) (oos c1 c2 a b l 16416) (oou c1 c2 a b l 16416)
                      (oov c1 c2 a b l 16416) l` THEN
  RULE_ASSUM_TAC (REWRITE_RULE[REAL_POW_2]) THEN
  CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  NLIN_TAC [SQ_NONNEG `&1543 / &500 - X`]);;

(* Lean: right_bar *)
let C868AB_RIGHT_BAR = c868_check
 `forall c1 c2 a b l y. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     &111 / &50 <= y /\ y <= &11 / &4
     ==> linside (ooc c1 c2 a b l 16416) (oos c1 c2 a b l 16416) (oou c1 c2 a b l 16416)
                 (oov c1 c2 a b l 16416) l (&3) y`
 (let [c; s; u; v; a] = c868_own 16416 in
  let px = [mk_comb(`(--):real->real`, c); s; mk_binop `(-):real->real->real` u (mk_binop `(*):real->real->real` `&4` c);
            list_mk_comb(`(-):real->real->real`, [mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, v)) a;
                                                 mk_binop `(*):real->real->real` `&4` s]); a] in
  let h = `&111 / &50 <= y /\ y <= &11 / &4` in
  let hy = ASSUME h in
  let goal = list_mk_comb(`linside`, c868_own 16416 @ [`&3`; `y:real`]) in
  let near = ASSUME `y <= &239 / &100` and far = ASSUME `~(y <= &239 / &100)` in
  (* chord branch *)
  let ch = SPECL (px @ [`y:real`]) WSC_CHORD in
  let ch = CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) (REWRITE_RULE[LINSIDE_PULLX] ch) in
  let box = c868_prove [c868_box 16416] (mk_forall(`x:real`, mk_forall(`y:real`,
                    mk_imp(list_mk_comb(`linside`, c868_own 16416 @ [`&4 - x`; `y:real`]), `&0 <= x`))))
                  (POP_ASSUM MP_TAC THEN REWRITE_TAC[lcont] THEN
                  DISCH_THEN (fun th -> REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP th)) THEN
                  REAL_ARITH_TAC) in
  let cy = c868_prove [CONJUNCT1 (c868_mp C868AB_RIGHT_CENTER)]
             (mk_binop `(<=):real->real->bool` `&2` (list_mk_comb(`lcy`, px)))
             (POP_ASSUM MP_TAC THEN REWRITE_TAC[lcy] THEN REAL_ARITH_TAC) in
  let chf = [c868_seed_f 16416 (`&1543 / &500`, `&2`);
             c868_excl_f 16416 3072 (c868_seed_f 3072 (`&47 / &20`, `&47 / &20`));
             box; cy; CONJUNCT1 hy; near] in
  let b1 = c868_discharge chf ch in
  (* segment branch *)
  let b2 = c868_apply OO_VERTICAL_SEGMENT (c868_own 16416 @ [`&3`; `&9 / &4`; `&11 / &4`; `y:real`])
             [c868_seed_f 16416 (`&3`, `&9 / &4`); c868_seed_f 16416 (`&3`, `&11 / &4`);
              MP (REAL_ARITH `~(y <= &239 / &100) ==> &9 / &4 <= y`) far; CONJUNCT2 hy] in
  c868_genx [`y:real`] [h] (DISJ_CASES (SPEC `y <= &239 / &100` EXCLUDED_MIDDLE) b1 b2));;
