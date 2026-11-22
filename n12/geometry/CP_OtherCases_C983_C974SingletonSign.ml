(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/C974SingletonSign.lean         *)
(* (N12Compact.Completion.OtherCases.C983.C974MissingCorner).                *)
(* MISSING-CORNER-WALL-SIGN Theorem 2: with the adjacent actual W in its     *)
(* positive canonical frame, the nonpositive canonical frame of K is         *)
(* impossible.  Conventions of CP_OtherCases_C983_C974MissingCornerSupports  *)
(* .ml (Input K W = c974mc_input, OpenSquare invariants explicit in          *)
(* C974MCS_INV).  turnFrame (c,s,u,v,a) = (--s,c,v,--u-a,a); Input.reframeK  *)
(* C974MC_INPUT_REFRAMEK; singleton_negative_cap                             *)
(* C974MC_SINGLETON_NEGATIVE_CAP; positive_support_obstruction               *)
(* C974MCS_POSITIVE_SUPPORT_OBSTRUCTION.                                     *)
(* (Lean header: "this is not a compiler acceptance claim".)  Tag C974SGN_.  *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_C974MissingCornerSupports.ml";;

(* Lean: quarter_defect *)
let C974SGN_QUARTER_DEFECT = prove
 (`forall l h x. &0 < l /\ &0 < h /\ l pow 2 + h pow 2 = &1 /\ x * (&1 + l) = h
           ==> x * (&1 - h) <= l / &4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `h:real`; SQ_NONNEG `l:real`]
   [`l <= &1`; `h <= &1`; `&0 < (&1 + h) * (&1 + l)`;
    `&0 <= (&1 - h) * (&1 + l)`; `&0 <= (&2 * h) * (&1 - l)`;
    `&4 * h * l <= (&1 + h) * (&1 + l)`] THEN
  SUBGOAL_THEN `x * (&1 - h) * ((&1 + h) * (&1 + l)) = h * l pow 2` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`l pow 2 + h pow 2 = &1`; `x * (&1 + l) = h`] THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`&0 <= l * ((&1 + h) * (&1 + l) - &4 * h * l)`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `l / &4 * ((&1 + h) * (&1 + l)) < (x * (&1 - h)) * ((&1 + h) * (&1 + l))`
    MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN NLIN_TAC ~deg2:false []);;

(* Lean: noncanonical_scalars *)
let C974SGN_NONCANONICAL_SCALARS = prove
 (`forall l h d t x.
     &0 < l /\ &0 < h /\ l <= h /\ l pow 2 + h pow 2 = &1 /\
     &0 < d /\ &0 <= t /\ t <= d /\ d pow 2 + t pow 2 = &1 /\
     x * (&1 + l) = h
     ==> &0 <= &1 - d + (&1 - h) * (d * x - t) /\
         &0 < (l * d + h * t) * (&1 - d) + (h * d - l * t) * (&1 - d / &2) - x * (&1 - h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`l:real`; `h:real`; `x:real`] C974SGN_QUARTER_DEFECT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `t:real`]
   [`h < &1`; `d <= &1`;
    `&0 <= (h - l) * (h + l)`; `&7 / &10 < h`;
    `&0 <= (d - t) * (d + t)`; `&7 / &10 < d`;
    `&2 / &5 * (&1 + l) < x * (&1 + l)`] THEN
  SUBGOAL_THEN `&2 / &5 < x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC `&1 + l` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < l` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `(&3 / &10) * d - (&22 / &25) * t`]
   [`(&22 / &25) * d + (&3 / &10) * t < &1`] THEN
  SUBGOAL_THEN `&0 <= &1 - d + (&1 - h) * (d * x - t)` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 <= d * x - t` THENL
     [NLIN_FACTS_TAC [] [`&0 <= (&1 - h) * (d * x - t)`] THEN NLIN_TAC ~deg2:false [];
      NLIN_FACTS_TAC []
       [`&0 < (h - &7 / &10) * --(d * x - t)`; `&0 < d * (x - &2 / &5)`] THEN
      NLIN_TAC ~deg2:false []];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  NLIN_FACTS_TAC []
   [`&0 < d * (&1 - d / &2)`; `&0 <= t * (&1 - d)`;
    `&0 < d * (&1 - d / &2) + t * (&1 - d)`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `d - &3 * t`] [`&3 * d + t < &13 / &4`] THEN
  NLIN_FACTS_TAC []
   [`&0 < d * (&13 / &4 - (&3 * d + t))`;
    `&21 / &80 < d * (&4 - &3 * d - t) / &2`;
    `&0 <= (h - l) * (d * (&1 - d / &2) + t * (&1 - d))`;
    `&0 < l * (d * (&4 - &3 * d - t) / &2 - &21 / &80)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: steep_quadrant_impossible *)
let C974SGN_STEEP_QUADRANT_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s %s. %s /\\ &0 < cK /\\ &0 < sK /\\ cK <= sK /\\
     &0 < cW /\\ &0 <= sW /\\ sW <= cW /\\ vK + aK <= &0 ==> F"
     C974MCS_K C974MCS_W C974MCS_INV),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (sK - cK) * cW`; `&0 <= cK * (cW - sW)`; `&0 <= sK * cW - cK * sW`] THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    C974MCS_POSITIVE_SUPPORT_OBSTRUCTION) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `cW:real`; `sW:real`; `sK / (&1 + cK)`]
    C974SGN_NONCANONICAL_SCALARS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    UNDISCH_TAC `&0 < cK` THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* Lean: singleton_canonical_positive *)
let C974SGN_SINGLETON_CANONICAL_POSITIVE = prove
 (parse_term (Printf.sprintf "!%s %s. %s /\\ &0 < cK /\\ abs sK <= cK /\\
     &0 < cW /\\ &0 <= sW /\\ sW <= cW ==> &0 < sK"
     C974MCS_K C974MCS_W C974MCS_INV),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    C974MC_SINGLETON_NEGATIVE_CAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c974mc_input (--sK) cK vK (--uK - aK) aK cW sW uW vW aW` ASSUME_TAC THENL
   [MATCH_MP_TAC C974MC_INPUT_REFRAMEK THEN
    MAP_EVERY EXISTS_TAC [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`] THEN
    ASM_REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`--sK`; `cK:real`; `vK:real`; `--uK - aK`; `aK:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    C974SGN_STEEP_QUADRANT_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `abs sK <= cK` THEN UNDISCH_TAC `cK * cK + sK * sK = &1` THEN
  UNDISCH_TAC `sK < &0` THEN UNDISCH_TAC `&0 <= uK` THEN REAL_ARITH_TAC);;
