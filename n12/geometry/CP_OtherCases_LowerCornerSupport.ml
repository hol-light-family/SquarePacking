(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/LowerCornerSupport.lean (Jatloe,    *)
(* N12-jatloe; namespace N12Compact.Completion.OtherCases.LowerCornerSupport)*)
(* A horizontal foreign segment joining two lower face exits bounds the      *)
(* closed lower vertex.  SegmentCorner.crossing_order is SEGC_CROSSING_ORDER;*)
(* q.unit_normal is the explicit hypothesis c * c + s * s = &1.              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/SegmentCorner.ml";;

(* Lean: horizontal *)
let OCLCS_HORIZONTAL = prove
 (`forall c s u v a lo hi.
     c * c + s * s = &1 /\ lo < hi /\
     c * lo - s <= u /\
     (v < --s * lo - c /\ --s * lo - c < v + a) /\
     (u < c * hi - s /\ c * hi - s < u + a) /\
     --s * hi - c <= v /\
     (forall x. lo <= x ==> x <= hi ==> ~linside c s u v a x (--(&1)))
     ==> --(&1) <= s * u + c * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:real`; `u + a`; `--(v + a)`; `--v`;
                `c * lo - s`; `s * lo + c`; `c * hi - s`; `s * hi + c`]
    SEGC_CROSSING_ORDER) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
   X_GEN_TAC `z:real` THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `(&1 - z) * lo + z * hi` o check (is_forall o concl)) THEN
   ANTS_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
   ANTS_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC;
   DISCH_TAC] THEN
  SUBGOAL_THEN
   `(--v - (s * lo + c)) * ((c * hi - s) - (c * lo - s)) -
    (u - (c * lo - s)) * ((s * hi + c) - (s * lo + c)) =
    --(hi - lo) * (s * u + c * v + &1)` ASSUME_TAC THENL
  [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (hi - lo) * (s * u + c * v + &1)` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`hi - lo`; `--(s * u + c * v + &1)`] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;
