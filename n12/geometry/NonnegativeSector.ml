(* ========================================================================= *)
(* Port of Compact/Cases/C868/NonnegativeSector.lean (N12Compact.C868).      *)
(* The nonnegative merged-upper sector of the original C868 family is        *)
(* impossible; every canonical frame of owner 3072 has negative sine.        *)
(* UpperNonnegative.impossible (with its Input structure unfolded) =         *)
(* C868UN_IMPOSSIBLE; ClosedFrames.canonical_frame = CLF_CANONICAL_FRAME.     *)
(* Tag C868NS_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/UpperCenter.ml";;
needs "n12/geometry/UpperNonnegative.ml";;

(* Lean: nonnegative_upper_frames_impossible *)
let C868NS_NONNEGATIVE_UPPER_FRAMES_IMPOSSIBLE = c868_check
 `forall c1 c2 a b l cA sA uA vA aA cH sH uH vH aH.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cH * cH + sH * sH = &1 /\ &0 < aH /\
     &0 < cA /\ abs sA <= cA /\ c977cc_normal cH sH /\ aA = l /\ aH = l /\
     (forall x y. linside cA sA uA vA aA x y <=>
            linside (ooc c1 c2 a b l 256) (oos c1 c2 a b l 256) (oou c1 c2 a b l 256)
                    (oov c1 c2 a b l 256) l x y) /\
     (forall x y. linside cH sH uH vH aH x y <=>
            linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                    (oov c1 c2 a b l 3072) l x y)
     ==> false`
 (let sqa = C868PS_SQ_A and sqh = C868PS_SQ_H in
  let hs = [`cA * cA + sA * sA = &1`; `&0 < aA`; `cH * cH + sH * sH = &1`; `&0 < aH`;
            `&0 < cA`; `abs sA <= cA`; `c977cc_normal cH sH`; `aA:real = l`; `aH:real = l`;
            C868PS_IA; C868PS_IH] in
  let h k = ASSUME (el k hs) in
  let ia = ASSUME C868PS_IA and ih = ASSUME C868PS_IH in
  let sa = h 7 and sh = h 8 in
  let nonneg = ASSUME `&0 <= sA` and neg = ASSUME `~(&0 <= sA)` in
  (* positive branch *)
  let na = c868_prove [nonneg; h 5; h 0] `c977cc_normal cA sA`
             (REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC) in
  let pos = MP (SPECL (C868OW_VARS @ sqa @ sqh) C868PS_POSITIVE_FRAMES_IMPOSSIBLE)
              (end_itlist CONJ (CONJUNCTS (ASSUME C868_H) @ [h 0; h 1; h 2; h 3; na; h 6; sa; sh; ia; ih])) in
  (* negative branch *)
  let ha = c868_prove [neg; h 5; h 0] `c977cc_normal cA (--sA)`
             (REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC) in
  let bounds = MATCH_MP C977CC_NORMAL_BOUNDS (h 6) in
  let hn = REWRITE_RULE[c977cc_normal] (h 6) in
  let center = MP (SPECL (C868OW_VARS @ sqh) C868UC_UPPER_NONNEGATIVE_CENTER)
      (end_itlist CONJ (CONJUNCTS (ASSUME C868_H) @
         [h 2; h 3; MP (REAL_ARITH `&7 / &10 <= cH ==> &0 < cH`) (CONJUNCT1 bounds);
          CONJUNCT1 hn; CONJUNCT1 (CONJUNCT2 hn); sh; ih])) in
  let cross = c868_mp C868AC_SOUTHWEST_CROSSPOINTS in
  let afacts = map (c868_to ia)
     [c868_seed_f 256 (`&33 / &20`, `&33 / &20`); c868_forced_f 0; c868_forced_f 1;
      CONJUNCT1 cross; CONJUNCT2 cross;
      c868_excl_f 256 1 (c868_forced_f 3); c868_excl_f 256 2 (c868_forced_f 4)] in
  let hfacts = map (c868_to ih)
     [c868_seed_f 3072 (`&33 / &20`, `&47 / &20`); c868_seed_f 3072 (`&47 / &20`, `&47 / &20`);
      c868_excl_f 3072 32768 (c868_forced_f 2);
      c868_excl_f 3072 16 (c868_mp C868AO_ADDITIONAL_INSIDE.(1))] in
  let dAH = c868_disj_tr (Some ia) (Some ih) (c868_apart_f 256 3072) (list_mk_comb(`ldisj`, sqa @ sqh)) in
  let base = [h 0; h 1; h 2; h 3; ha; h 6; TRANS sa (SYM sh);
              MP (REAL_ARITH `aA:real = l /\ &1 < l ==> &1 < aA`) (CONJ sa C868_SIDE); center; dAH] in
  let negf = c868_apply C868UN_IMPOSSIBLE (sqa @ sqh) (base @ afacts @ hfacts) in
  c868_genx (sqa @ sqh) hs (DISJ_CASES (SPEC `&0 <= sA` EXCLUDED_MIDDLE) pos negf));;

(* Lean: upper_negative_required *)
let C868NS_UPPER_NEGATIVE_REQUIRED = prove
 (`forall c1 c2 a b l cH sH uH vH aH.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     cH * cH + sH * sH = &1 /\ &0 < aH /\
     &0 < cH /\ abs sH <= cH /\ aH = l /\
     (forall x y. linside cH sH uH vH aH x y <=>
            linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                    (oov c1 c2 a b l 3072) l x y)
     ==> sH < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP OO_SIDE) THEN
  MP_TAC (SPECL (c868_own 256) CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[OO_UNIT]; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC C868PS_SQ_A THEN STRIP_TAC THEN
  MP_TAC (SPECL (C868OW_VARS @ C868PS_SQ_A @ C868PS_SQ_H) C868NS_NONNEGATIVE_UPPER_FRAMES_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC);;
