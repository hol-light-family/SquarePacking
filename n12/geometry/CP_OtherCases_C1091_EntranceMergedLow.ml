(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1091/EntranceMergedLow.lean        *)
(* (N12Compact.Completion.OtherCases.C1091.EntranceMergedLow).  A direct     *)
(* C1091 entrance lemma for the merged marker owner.  Local square q is      *)
(* c s u v a.  short_projections is WFP_SHORT_PROJECTIONS; canonical_frame   *)
(* is CLF_CANONICAL_FRAME.  The *_original theorems are stated for a         *)
(* normalized packing NPACK c1 c2 a b l with family c1091od_family; Lean's   *)
(* owners p 0, 4, 8 are the owners of masks 1, 258, 4096; q.translated 1 1  *)
(* is the explicit square of OC1091EML_TRANSLATE.  Tag OC1091EML_.          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/CP_OtherCases_C1091_OriginalData.ml";;

let OC1091EML_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

let OC1091EML_SP_TAC dx dy =
  MP_TAC(SPECL [`c:real`; `s:real`; dx; dy] WFP_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC];;

let OC1091EML_UNFOLD_TAC =
  MAP_EVERY (fun tm -> MP_TAC(ASSUME tm) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside c s u v a (--(&43 / &500)) (&0)`; `linside c s u v a (&13 / &20) (&13 / &20)`];;

(* Lean: positive (private) *)
let OC1091EML_POSITIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (--(&43 / &500)) (&0) /\ linside c s u v a (&13 / &20) (&13 / &20) /\
     ~linside c s u v a (&3 / &5) (&0) /\ &0 < c /\ &0 <= s /\ s <= c
     ==> linside c s u v a (&0) (&37 / &50)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OC1091EML_UNFOLD_TAC THEN
  SUBGOAL_THEN `--(&3 / &5) * s <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OC1091EML_MISS_TAC `~linside c s u v a (&3 / &5) (&0)`; ALL_TAC] THEN
  OC1091EML_SP_TAC `&37 / &50` `&3 / &5` THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: nonpositive (private) *)
let OC1091EML_NONPOSITIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (--(&43 / &500)) (&0) /\ linside c s u v a (&13 / &20) (&13 / &20) /\
     ~linside c s u v a (&3 / &25) (&0) /\ ~linside c s u v a (&3 / &5) (&0) /\
     &0 < c /\ s <= &0
     ==> linside c s u v a (&0) (&37 / &50)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OC1091EML_UNFOLD_TAC THEN
  SUBGOAL_THEN `u + a <= (&3 / &5) * c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OC1091EML_MISS_TAC `~linside c s u v a (&3 / &5) (&0)`; ALL_TAC] THEN
  OC1091EML_SP_TAC `&3 / &5` `--(&37 / &50)` THEN
  OC1091EML_SP_TAC `&1` `&0` THEN
  SUBGOAL_THEN `(&37 / &50) * c < v + a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OC1091EML_MISS_TAC `~linside c s u v a (&3 / &25) (&0)`; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

let OC1091EML_FRAME_TAC =
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cr:real` (X_CHOOSE_THEN `sr:real` (X_CHOOSE_THEN `ur:real`
    (X_CHOOSE_THEN `vr:real` (X_CHOOSE_THEN `ar:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ar:real = a`)) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
     can (find_term ((=) `linside`)) (concl th) &&
     is_iff(snd(strip_forall(concl th))) then
     RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC);;

(* Lean: point *)
let OC1091EML_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (--(&43 / &500)) (&0) /\ linside c s u v a (&13 / &20) (&13 / &20) /\
     ~linside c s u v a (&3 / &25) (&0) /\ ~linside c s u v a (&3 / &5) (&0)
     ==> linside c s u v a (&0) (&37 / &50)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OC1091EML_FRAME_TAC THEN
  ASM_CASES_TAC `&0 <= sr` THENL
   [MATCH_MP_TAC OC1091EML_POSITIVE; MATCH_MP_TAC OC1091EML_NONPOSITIVE] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: nonpositive_wall_impossible (private) *)
let OC1091EML_NONPOSITIVE_WALL_IMPOSSIBLE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (--(&43 / &500)) (&0) /\ linside c s u v a (&13 / &20) (&13 / &20) /\
     ~linside c s u v a (&3 / &25) (&0) /\ ~linside c s u v a (--(&43 / &500)) (&1) /\
     &0 < c /\ s <= &0 /\ --s <= c
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OC1091EML_UNFOLD_TAC THEN
  SUBGOAL_THEN `u + a <= (&3 / &25) * c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OC1091EML_MISS_TAC `~linside c s u v a (&3 / &25) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `--(&43 / &500) * c + s <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OC1091EML_MISS_TAC `~linside c s u v a (--(&43 / &500)) (&1)`; ALL_TAC] THEN
  OC1091EML_SP_TAC `&603 / &1000` `--(&603 / &1000)` THEN
  RASM_ARITH_TAC);;

(* Lean: positive_profile (private) *)
let OC1091EML_POSITIVE_PROFILE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (--(&43 / &500)) (&0) /\ linside c s u v a (&13 / &20) (&13 / &20) /\
     ~linside c s u v a (&3 / &25) (&0) /\ ~linside c s u v a (--(&43 / &500)) (&1) /\
     &0 < c /\ &0 <= s /\ s <= c
     ==> --(&3 / &25) * s <= v /\ &2 * s < c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OC1091EML_UNFOLD_TAC THEN
  SUBGOAL_THEN `--(&3 / &25) * s <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OC1091EML_MISS_TAC `~linside c s u v a (&3 / &25) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= c + (&43 / &500) * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OC1091EML_MISS_TAC `~linside c s u v a (--(&43 / &500)) (&1)`; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 < c + (&103 / &500) * s` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < s * ((&1 - (&103 / &500) pow 2) * s - (&206 / &500) * c)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (c + (&103 / &500) * s - &1) * (c + (&103 / &500) * s + &1)`
  ASSUME_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) THEN RASM_ARITH_TAC);;

(* Lean: positive_inner (private) *)
let OC1091EML_POSITIVE_INNER = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (--(&43 / &500)) (&0) /\ linside c s u v a (&13 / &20) (&13 / &20) /\
     ~linside c s u v a (&3 / &25) (&0) /\ ~linside c s u v a (--(&43 / &500)) (&1) /\
     &0 < c /\ &0 <= s /\ s <= c
     ==> linside c s u v a (&23 / &50) (&99 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL OC1091EML_POSITIVE_PROFILE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  OC1091EML_UNFOLD_TAC THEN OC1091EML_SP_TAC `&1` `&0` THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: inner *)
let OC1091EML_INNER = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (--(&43 / &500)) (&0) /\ linside c s u v a (&13 / &20) (&13 / &20) /\
     ~linside c s u v a (&3 / &25) (&0) /\ ~linside c s u v a (--(&43 / &500)) (&1)
     ==> linside c s u v a (&23 / &50) (&99 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OC1091EML_FRAME_TAC THEN
  ASM_CASES_TAC `&0 <= sr` THENL
   [MATCH_MP_TAC OC1091EML_POSITIVE_INNER THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(TAUT `false ==> p`) THEN MATCH_MP_TAC OC1091EML_NONPOSITIVE_WALL_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `a:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: positive_alternative (private) *)
let OC1091EML_POSITIVE_ALTERNATIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (--(&43 / &500)) (&0) /\ linside c s u v a (&13 / &20) (&13 / &20) /\
     ~linside c s u v a (&3 / &25) (&0) /\ ~linside c s u v a (--(&43 / &500)) (&1) /\
     &0 < c /\ &0 <= s /\ s <= c
     ==> linside c s u v a (&1 / &2) (&1) \/ linside c s u v a (&23 / &50) (&101 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL OC1091EML_POSITIVE_PROFILE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  OC1091EML_UNFOLD_TAC THEN OC1091EML_SP_TAC `&1` `&0` THEN
  ASM_CASES_TAC `c <= &34 * s` THENL
   [DISJ2_TAC THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;
    DISJ1_TAC THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC]);;

(* Lean: alternative *)
let OC1091EML_ALTERNATIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (--(&43 / &500)) (&0) /\ linside c s u v a (&13 / &20) (&13 / &20) /\
     ~linside c s u v a (&3 / &25) (&0) /\ ~linside c s u v a (--(&43 / &500)) (&1)
     ==> linside c s u v a (&1 / &2) (&1) \/ linside c s u v a (&23 / &50) (&101 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OC1091EML_FRAME_TAC THEN
  ASM_CASES_TAC `&0 <= sr` THENL
   [MATCH_MP_TAC OC1091EML_POSITIVE_ALTERNATIVE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(TAUT `false ==> p`) THEN MATCH_MP_TAC OC1091EML_NONPOSITIVE_WALL_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `a:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The original-packing instances.                                           *)
(* ------------------------------------------------------------------------- *)

(* Lean: inside_translated_iff at (1,1): (q.translated 1 1).Inside x y <=> q.Inside (1+x) (1+y) *)
let OC1091EML_TRANSLATE = prove
 (`forall c s u v a x y.
     linside c s (u - c - s) (v + s - c) a x y <=> linside c s u v a (&1 + x) (&1 + y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let oc1091eml_own m =
  map (fun f -> list_mk_comb(f, [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
                                 `l:real`; mk_small_numeral m]))
      [`ooc`; `oos`; `oou`; `oov`];;

let oc1091eml_trans m =
  match oc1091eml_own m with
    [c; s; u; v] ->
      let th = SPECL [c; s; u; v; `l:real`; `x:real`; `y:real`] OC1091EML_TRANSLATE in
      let args = snd(strip_comb(lhs(concl th))) in
      [el 0 args; el 1 args; el 2 args; el 3 args; el 4 args]
  | _ -> failwith "oc1091eml_trans";;

let OC1091EML_PACK_TAC =
  let vars = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] in
  let fam = `c1091od_family` in
  MAP_EVERY (fun th -> MP_TAC(SPECL vars th) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC)
   [C1091OD_MERGED_MARKERS; c1091od_seed 0 (`&28 / &25`, `&1`);
    c1091od_seed 0 (`&87 / &50`, `&1`); c1091od_seed 8 (`&457 / &500`, `&2`);
    oo_apart fam 258 1; oo_apart fam 258 4096] THEN
  MP_TAC(SPECL (vars @ [`258`]) OO_UNIT) THEN MP_TAC(SPECL vars OO_SIDE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN (list_mk_comb(`linside`, oc1091eml_own 1 @ [`l:real`; `&8 / &5`; `&1`]))
  ASSUME_TAC THENL
   [MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&28 / &25`; `&87 / &50`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]);;

let OC1091EML_ORIGINAL_TAC th =
  REPEAT GEN_TAC THEN STRIP_TAC THEN OC1091EML_PACK_TAC THEN
  MP_TAC(SPECL (oc1091eml_trans 258) th) THEN
  REWRITE_TAC[OC1091EML_TRANSLATE] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN ASM_MESON_TAC[];;

(* Lean: original *)
let OC1091EML_ORIGINAL = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1091od_family
     ==> linside (ooc c1 c2 a b l 258) (oos c1 c2 a b l 258) (oou c1 c2 a b l 258)
                 (oov c1 c2 a b l 258) l (&1) (&87 / &50)`,
  OC1091EML_ORIGINAL_TAC OC1091EML_POINT);;

(* Lean: inner_original *)
let OC1091EML_INNER_ORIGINAL = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1091od_family
     ==> linside (ooc c1 c2 a b l 258) (oos c1 c2 a b l 258) (oou c1 c2 a b l 258)
                 (oov c1 c2 a b l 258) l (&73 / &50) (&199 / &100)`,
  OC1091EML_ORIGINAL_TAC OC1091EML_INNER);;

(* Lean: alternative_original *)
let OC1091EML_ALTERNATIVE_ORIGINAL = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1091od_family
     ==> linside (ooc c1 c2 a b l 258) (oos c1 c2 a b l 258) (oou c1 c2 a b l 258)
                 (oov c1 c2 a b l 258) l (&3 / &2) (&2) \/
         linside (ooc c1 c2 a b l 258) (oos c1 c2 a b l 258) (oou c1 c2 a b l 258)
                 (oov c1 c2 a b l 258) l (&73 / &50) (&201 / &100)`,
  OC1091EML_ORIGINAL_TAC OC1091EML_ALTERNATIVE);;
