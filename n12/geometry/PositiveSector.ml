(* ========================================================================= *)
(* Port of Compact/Cases/C868/PositiveSector.lean (N12Compact.C868).         *)
(* The all-positive canonical frame sector of owners 256 (A) and 3072 (H) is *)
(* impossible (C868UpperPoint.point = C868UP_POINT).  Lean OpenSquares A, H  *)
(* are c s u v a with unit normal and positive side; their equal shape and   *)
(* pointwise equality with the owners are explicit hypotheses.               *)
(* ClosedFrames.canonical_frame = CLF_CANONICAL_FRAME.  Tag C868PS_.         *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C868_Ownership.ml";;
needs "n12/geometry/C868UpperPoint.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let C868PS_SQ_A = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`];;
let C868PS_SQ_H = [`cH:real`; `sH:real`; `uH:real`; `vH:real`; `aH:real`];;
let C868PS_IA = `forall x y. linside cA sA uA vA aA x y <=>
                   linside (ooc c1 c2 a b l 256) (oos c1 c2 a b l 256) (oou c1 c2 a b l 256)
                           (oov c1 c2 a b l 256) l x y`;;
let C868PS_IH = `forall x y. linside cH sH uH vH aH x y <=>
                   linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                           (oov c1 c2 a b l 3072) l x y`;;

(* Lean: positive_frames_impossible *)
let C868PS_POSITIVE_FRAMES_IMPOSSIBLE = c868_check
 `forall c1 c2 a b l cA sA uA vA aA cH sH uH vH aH.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cH * cH + sH * sH = &1 /\ &0 < aH /\
     c977cc_normal cA sA /\ c977cc_normal cH sH /\ aA = l /\ aH = l /\
     (forall x y. linside cA sA uA vA aA x y <=>
            linside (ooc c1 c2 a b l 256) (oos c1 c2 a b l 256) (oou c1 c2 a b l 256)
                    (oov c1 c2 a b l 256) l x y) /\
     (forall x y. linside cH sH uH vH aH x y <=>
            linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                    (oov c1 c2 a b l 3072) l x y)
     ==> false`
 (let hs = [`cA * cA + sA * sA = &1`; `&0 < aA`; `cH * cH + sH * sH = &1`; `&0 < aH`;
            `c977cc_normal cA sA`; `c977cc_normal cH sH`; `aA:real = l`; `aH:real = l`; C868PS_IA; C868PS_IH] in
  let ia = ASSUME C868PS_IA and ih = ASSUME C868PS_IH in
  let sa = ASSUME `aA:real = l` and sh = ASSUME `aH:real = l` in
  let facts = map (c868_to ia)
     [c868_seed_f 256 (`&33 / &20`, `&33 / &20`); c868_forced_f 0; c868_forced_f 1;
      c868_excl_f 256 1 (c868_forced_f 3); c868_excl_f 256 2 (c868_forced_f 4)] @
   map (c868_to ih)
     [c868_seed_f 3072 (`&33 / &20`, `&47 / &20`); c868_seed_f 3072 (`&47 / &20`, `&47 / &20`)] @
   map ASSUME (butlast (butlast hs)) @
   [TRANS sa (SYM sh); MP (REAL_ARITH `aA = l /\ &1 < l ==> &1 < aA`) (CONJ sa C868_SIDE);
    c868_disj_tr (Some ia) (Some ih) (c868_apart_f 256 3072)
      (list_mk_comb(`ldisj`, C868PS_SQ_A @ C868PS_SQ_H))] in
  let res = c868_back ih (c868_apply C868UP_POINT (C868PS_SQ_A @ C868PS_SQ_H) facts) in
  c868_genx (C868PS_SQ_A @ C868PS_SQ_H) hs (c868_clash 3072 32768 res (c868_forced_f 2)));;

(* Lean: remaining_frames *)
let C868PS_REMAINING_FRAMES = prove
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
           (sA < &0 \/ sH < &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP OO_SIDE o CONJUNCT1) THEN
  MAP_EVERY (fun (m, sq) ->
    MP_TAC (SPECL (c868_own m) CLF_CANONICAL_FRAME) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[OO_UNIT]; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC sq THEN STRIP_TAC)
   [256, C868PS_SQ_A; 3072, C868PS_SQ_H] THEN
  MAP_EVERY EXISTS_TAC (C868PS_SQ_A @ C868PS_SQ_H) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE; GSYM DE_MORGAN_THM] THEN STRIP_TAC THEN
  MP_TAC (SPECL (C868OW_VARS @ C868PS_SQ_A @ C868PS_SQ_H) C868PS_POSITIVE_FRAMES_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC);;
