(* ========================================================================= *)
(* Port of Compact/Bridge/CongruentSAT.lean (N12Compact.CongruentSAT).       *)
(* Separating axes for disjoint original squares with equal side lengths.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ScalarSATSigned.ml";;
needs "n12/geometry/C977ChainBridge.ml";;

(* helper: the normalisation step `normalize` of the Lean proof *)
let CSAT_NORMALIZE = prove
 (`forall p f m. &0 < f /\ abs p < f + f * m ==> abs(p / f) < &1 + m`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_LT_LDIV_EQ; REAL_ARITH `&0 < f ==> abs f = f`] THEN
  ASM_REAL_ARITH_TAC);;

(* helper: the `scale` step of the Lean proof *)
let CSAT_SCALE = prove
 (`forall f w. &0 < f /\ abs w < &1 ==> abs(f * w) < f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < f ==> abs f = f`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_LT_LMUL_EQ]);;

(* helper: the algebraic core of faceSeparation_of_disjoint.  With f the     *)
(* half side and (dx,dy) the centre displacement, a common point Q+(ex,ey)   *)
(* exists when all four projections are smaller than the pair radius.       *)
let CSAT_CORE = prove
 (`forall cq sq cr sr f dx dy.
     cq * cq + sq * sq = &1 /\ cr * cr + sr * sr = &1 /\ &0 < f /\
     abs(cq * dx + sq * dy) <
       f + f * (abs(cq * cr + sq * sr) + abs(cq * sr - sq * cr)) /\
     abs(--sq * dx + cq * dy) <
       f + f * (abs(cq * cr + sq * sr) + abs(cq * sr - sq * cr)) /\
     abs(cr * dx + sr * dy) <
       f + f * (abs(cq * cr + sq * sr) + abs(cq * sr - sq * cr)) /\
     abs(--sr * dx + cr * dy) <
       f + f * (abs(cq * cr + sq * sr) + abs(cq * sr - sq * cr))
     ==> exists ex ey. abs(cq * ex + sq * ey) < f /\ abs(--sq * ex + cq * ey) < f /\
                 abs(cr * (ex - dx) + sr * (ey - dy)) < f /\
                 abs(--sr * (ex - dx) + cr * (ey - dy)) < f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cq * cr + sq * sr`; `cq * sr - sq * cr`;
                `(cq * dx + sq * dy) / f`; `(--sq * dx + cq * dy) / f`;
                `(cr * dx + sr * dy) / f`; `(--sr * dx + cr * dy) / f`] SSS_OVERLAP) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC C977WC_NORMAL_PAIR_UNIT THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `cq * cq + sq * sq = &1` THEN UNDISCH_TAC `&0 < f` THEN
      CONV_TAC REAL_FIELD;
      UNDISCH_TAC `cq * cq + sq * sq = &1` THEN UNDISCH_TAC `&0 < f` THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC CSAT_NORMALIZE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CSAT_NORMALIZE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CSAT_NORMALIZE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CSAT_NORMALIZE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SSS_overlap] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` (X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`f * (cq * x - sq * y)`; `f * (sq * x + cq * y)`] THEN
  SUBGOAL_THEN
   `cq * f * (cq * x - sq * y) + sq * f * (sq * x + cq * y) = f * x /\
    --sq * f * (cq * x - sq * y) + cq * f * (sq * x + cq * y) = f * y /\
    cr * (f * (cq * x - sq * y) - dx) + sr * (f * (sq * x + cq * y) - dy) =
      f * ((cq * cr + sq * sr) * x + (cq * sr - sq * cr) * y - (cr * dx + sr * dy) / f) /\
    --sr * (f * (cq * x - sq * y) - dx) + cr * (f * (sq * x + cq * y) - dy) =
      f * (--(cq * sr - sq * cr) * x + (cq * cr + sq * sr) * y -
           (--sr * dx + cr * dy) / f)`
  (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `cq * cq + sq * sq = &1` THEN UNDISCH_TAC `&0 < f` THEN
    CONV_TAC REAL_FIELD;
    REPEAT CONJ_TAC THEN MATCH_MP_TAC CSAT_SCALE THEN ASM_REWRITE_TAC[]]);;

(* Lean: faceSeparation_of_disjoint *)
let CSAT_FACESEPARATION_OF_DISJOINT = prove
 (`forall cq sq uq vq aq cr sr ur vr ar.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ cr * cr + sr * sr = &1 /\ &0 < ar /\
     aq = ar /\
     ldisj cq sq uq vq aq cr sr ur vr ar
     ==> C977CB_faceSep cq sq uq vq aq cr sr ur vr ar`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aq:real = ar`)) THEN
  REWRITE_TAC[C977CB_faceSep; C977CB_pairRadius] THEN
  REWRITE_TAC[REAL_ARITH `abs(cr * cq + sr * sq) = abs(cq * cr + sq * sr) /\
                          abs(cr * sq - sr * cq) = abs(cq * sr - sq * cr)`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT; GSYM DE_MORGAN_THM] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `cr:real`; `sr:real`; `ar / &2`;
                `lcx cr sr ur vr ar - lcx cq sq uq vq ar`;
                `lcy cr sr ur vr ar - lcy cq sq uq vq ar`] CSAT_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ex:real` (X_CHOOSE_THEN `ey:real` (fun bth ->
    FIRST_X_ASSUM(MP_TAC o SPECL [`lcx cq sq uq vq ar + ex`; `lcy cq sq uq vq ar + ey`] o
                  REWRITE_RULE[ldisj]) THEN
    MP_TAC bth))) THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `ar:real`] LCENTRE_COORDS) THEN
  MP_TAC(SPECL [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
