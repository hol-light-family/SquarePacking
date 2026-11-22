(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976LeftTop/PointSupport.lean       *)
(* (N12Compact.Completion.OtherCases.C976LeftTop.UpperPoints).  The lower-   *)
(* segment support of C976-LEFT-UPPER-POINTS.  Input / Profile are           *)
(* occ976lt_input / occ976lt_profile; SegmentCorner.crossing_order is        *)
(* SEGC_CROSSING_ORDER; lowerAlpha / lowerBeta are occ976ps_lowerAlpha /     *)
(* occ976ps_lowerBeta.  The OpenSquare invariants are explicit hypotheses.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/SegmentCorner.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_PointInputs.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_PointProfile.ml";;

(* Lean: lowerAlpha (definition) *)
let occ976ps_lowerAlpha = new_definition
 `occ976ps_lowerAlpha (c:real) (s:real) = (&13 / &100) * c + (&6 / &25) * s`;;

(* Lean: lowerBeta (definition) *)
let occ976ps_lowerBeta = new_definition
 `occ976ps_lowerBeta (c:real) (s:real) = (&6 / &25) * c - (&13 / &100) * s`;;

let OCC976PS_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let OCC976PS_UNFOLD_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[occ976lt_input; occ976lt_profile]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside c s u v a (--(&43 / &500)) (&0)`; `linside c s u v a (&13 / &20) (&7 / &20)`;
    `linside c s u v a (&0) (&13 / &50)`];;

let OCC976PS_SEGMENT_TAC t =
  FIRST_ASSUM(MP_TAC o SPEC t o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `&13 / &100`)) (concl th))) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

(* Lean: lower_segment_support *)
let OCC976PS_LOWER_SEGMENT_SUPPORT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     occ976lt_input c s u v a /\ occ976lt_profile c s u v a /\ (&1 / &3) * c <= s
     ==> --(&39 / &625) <= occ976ps_lowerAlpha c s * u + occ976ps_lowerBeta c s * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCC976PS_UNFOLD_TAC THEN
  REWRITE_TAC[occ976ps_lowerAlpha; occ976ps_lowerBeta] THEN
  SUBGOAL_THEN `(&113 / &100) * c - (&6 / &25) * s < &1` ASSUME_TAC THENL
  [SUBGOAL_THEN `(&63 / &200) * (&3 * c + s) < &1` MP_TAC THENL
   [NLIN_TAC [SQ_NONNEG `c - &3 * s`]; RASM_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `--(&6 / &25) * c - (&13 / &100) * s <= u` ASSUME_TAC THENL
  [OCC976PS_SEGMENT_TAC `&0`; ALL_TAC] THEN
  ASM_CASES_TAC `--(&13 / &50) * s <= u` THENL
  [OCC976PS_PROD_TAC `(&13 / &100) * c + (&6 / &25) * s` `u - --(&13 / &50) * s` THEN
   OCC976PS_PROD_TAC `(&6 / &25) * c - (&13 / &100) * s`
     `v - (--(&27 / &100) * s - (&1 / &25) * c)` THEN
   OCC976PS_PROD_TAC `(&3 / &4) * c - s`
     `(&467 / &5000) * c - (&351 / &10000) * (s + (&3 / &4) * c)` THEN
   MP_TAC(SPECL [`c:real`; `c:real`] REAL_LT_MUL) THEN
   ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  SUBGOAL_THEN `--(&13 / &50) * c <= v` ASSUME_TAC THENL
  [OCC976PS_SEGMENT_TAC `&1`; ALL_TAC] THEN
  MP_TAC(SPECL [`u:real`; `u + a:real`; `--(v + a)`; `--v:real`;
                `--(&6 / &25) * c - (&13 / &100) * s`; `--((&6 / &25) * s - (&13 / &100) * c)`;
                `--(&13 / &50) * s`; `--(--(&13 / &50) * c)`] SEGC_CROSSING_ORDER) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
   X_GEN_TAC `t:real` THEN DISCH_TAC THEN DISCH_TAC THEN
   FIRST_ASSUM((fun th -> MP_TAC(MP (MP (SPEC `t:real` th) (ASSUME `&0 <= t`))
       (ASSUME `t <= &1`))) o check (fun th -> is_forall(concl th) &&
     can (find_term ((=) `&13 / &100`)) (concl th))) THEN
   REWRITE_TAC[linside] THEN
   MATCH_MP_TAC(TAUT `(a ==> b) ==> ~b ==> ~a`) THEN STRIP_TAC THEN
   REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];
   DISCH_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: upperU_strict *)
let OCC976PS_UPPERU_STRICT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     occ976lt_input c s u v a /\ occ976lt_profile c s u v a /\ (&1 / &3) * c <= s
     ==> occ976ps_lowerAlpha c s + occ976ps_lowerBeta c s * (&1 - c) - &39 / &625 <
         occ976ps_lowerAlpha c s * (u + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    OCC976PS_LOWER_SEGMENT_SUPPORT) THEN
  ASM_REWRITE_TAC[] THEN OCC976PS_UNFOLD_TAC THEN
  REWRITE_TAC[occ976ps_lowerAlpha; occ976ps_lowerBeta] THEN DISCH_TAC THEN
  OCC976PS_PROD_TAC `(&6 / &25) * c - (&13 / &100) * s` `c - (v + a)` THEN
  MP_TAC(SPECL [`a - &1`; `((&13 / &100) * c + (&6 / &25) * s) +
                ((&6 / &25) * c - (&13 / &100) * s)`] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  NLIN_TAC ~deg2:false []);;
