(* ========================================================================= *)
(* Port of Compact/Cases/C868/NegativeCornerSector.lean (N12Compact.C868).   *)
(* Negative lower square A (owner 256) / positive upper square H (owner      *)
(* 3072) with the corner (1,1) missing from owner 1 is impossible.           *)
(* SouthwestCentralReach.left = SWCR_LEFT, SouthwestNegativeCorner.point =   *)
(* SNC_POINT, C868UpperPointNegative.point = C868UPN_POINT.  Tag C868NC_.    *)
(* ========================================================================= *)

needs "n12/geometry/PositiveSector.ml";;
needs "n12/geometry/C868UpperPointNegative.ml";;
needs "n12/geometry/SouthwestNegativeCorner.ml";;
needs "n12/geometry/SouthwestCentralReach.ml";;

(* Lean: negative_corner_frames_impossible *)
let C868NC_NEGATIVE_CORNER_FRAMES_IMPOSSIBLE = c868_check
 `forall c1 c2 a b l cA sA uA vA aA cH sH uH vH aH.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cH * cH + sH * sH = &1 /\ &0 < aH /\
     c977cc_normal cA (--sA) /\ c977cc_normal cH sH /\ aA = l /\ aH = l /\
     (forall x y. linside cA sA uA vA aA x y <=>
            linside (ooc c1 c2 a b l 256) (oos c1 c2 a b l 256) (oou c1 c2 a b l 256)
                    (oov c1 c2 a b l 256) l x y) /\
     (forall x y. linside cH sH uH vH aH x y <=>
            linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                    (oov c1 c2 a b l 3072) l x y) /\
     ~linside (ooc c1 c2 a b l 1) (oos c1 c2 a b l 1) (oou c1 c2 a b l 1) (oov c1 c2 a b l 1) l (&1) (&1)
     ==> false`
 (let corner = `~linside (ooc c1 c2 a b l 1) (oos c1 c2 a b l 1) (oou c1 c2 a b l 1)
                         (oov c1 c2 a b l 1) l (&1) (&1)` in
  let hs = [`cA * cA + sA * sA = &1`; `&0 < aA`; `cH * cH + sH * sH = &1`; `&0 < aH`;
            `c977cc_normal cA (--sA)`; `c977cc_normal cH sH`; `aA:real = l`; `aH:real = l`;
            C868PS_IA; C868PS_IH; corner] in
  let ia = ASSUME C868PS_IA and ih = ASSUME C868PS_IH in
  let sa = ASSUME `aA:real = l` and sh = ASSUME `aH:real = l` in
  let base = map ASSUME (subtract hs [C868PS_IA; C868PS_IH]) @
    [TRANS sa (SYM sh); SYM sa; MP (REAL_ARITH `aA = l /\ &1 < l ==> &1 < aA`) (CONJ sa C868_SIDE);
     REAL_ARITH `sA = --(--sA)`] in
  let afacts = map (c868_to ia)
     [c868_seed_f 256 (`&33 / &20`, `&33 / &20`); c868_forced_f 0; c868_forced_f 1;
      c868_excl_f 256 3072 (c868_seed_f 3072 (`&47 / &20`, `&47 / &20`));
      c868_excl_f 256 3072 (c868_seed_f 3072 (`&33 / &20`, `&47 / &20`));
      c868_excl_f 256 512 (c868_seed_f 512 (`&47 / &20`, `&33 / &20`))] in
  let ofacts = [c868_seed_f 1 (`&28 / &25`, `&1`); c868_forced_f 5;
                c868_seed_f 2 (`&1`, `&28 / &25`); c868_forced_f 6;
                c868_seed_f 1 (`&1`, `&457 / &500`); c868_seed_f 1 (`&187 / &100`, `&19 / &25`);
                c868_excl_f 1 8192 (c868_seed_f 8192 (`&2`, `&457 / &500`))] in
  let sqa = C868PS_SQ_A and sqh = C868PS_SQ_H in
  let dA1 = c868_disj_tr (Some ia) None (c868_apart_f 256 1) (list_mk_comb(`ldisj`, sqa @ c868_own 1)) in
  let d1A = c868_disj_tr None (Some ia) (c868_apart_f 1 256) (list_mk_comb(`ldisj`, c868_own 1 @ sqa)) in
  let dA2 = c868_disj_tr (Some ia) None (c868_apart_f 256 2) (list_mk_comb(`ldisj`, sqa @ c868_own 2)) in
  let dAH = c868_disj_tr (Some ia) (Some ih) (c868_apart_f 256 3072) (list_mk_comb(`ldisj`, sqa @ sqh)) in
  let left = c868_apply SWCR_LEFT (sqa @ c868_own 1) (base @ afacts @ ofacts @ [dA1]) in
  let centre = c868_apply SNC_POINT (c868_own 1 @ sqa @ c868_own 2 @ [`--sA`])
                 (base @ afacts @ ofacts @ [left; d1A; dA2]) in
  let hfacts = map (c868_to ih)
     [c868_seed_f 3072 (`&33 / &20`, `&47 / &20`); c868_seed_f 3072 (`&47 / &20`, `&47 / &20`)] in
  let high = c868_apply C868UPN_POINT (sqa @ sqh) (base @ afacts @ hfacts @ [centre; dAH]) in
  let res = c868_back ih high in
  c868_genx (sqa @ sqh) hs (c868_clash 3072 32768 res (c868_forced_f 2)));;

(* Lean: remaining_canonical_frames *)
let C868NC_REMAINING_CANONICAL_FRAMES = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family
     ==> exists cA sA uA vA aA cH sH uH vH aH.
           cA * cA + sA * sA = &1 /\ &0 < aA /\ cH * cH + sH * sH = &1 /\ &0 < aH /\
           &0 < cA /\ abs sA <= cA /\ &0 < cH /\ abs sH <= cH /\ aA = l /\ aH = l /\
           (forall x y. linside cA sA uA vA aA x y <=>
                  linside (ooc c1 c2 a b l 256) (oos c1 c2 a b l 256) (oou c1 c2 a b l 256)
                          (oov c1 c2 a b l 256) l x y) /\
           (forall x y. linside cH sH uH vH aH x y <=>
                  linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                          (oov c1 c2 a b l 3072) l x y) /\
           (sH < &0 \/
            sA < &0 /\ linside (ooc c1 c2 a b l 1) (oos c1 c2 a b l 1) (oou c1 c2 a b l 1)
                                (oov c1 c2 a b l 1) l (&1) (&1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM (MP_TAC o MATCH_MP C868PS_REMAINING_FRAMES) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC (C868PS_SQ_A @ C868PS_SQ_H) THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC (C868PS_SQ_A @ C868PS_SQ_H) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `sH < &0` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sA < &0` ASSUME_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC (TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MP_TAC (SPECL (C868OW_VARS @ C868PS_SQ_A @ C868PS_SQ_H) C868NC_NEGATIVE_CORNER_FRAMES_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
  REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC);;
