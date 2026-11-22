(* ========================================================================= *)
(* Port of Compact/Geometry/C868UpperPointMargins.lean                       *)
(* (N12Compact.C868UpperPointMargins).  Continuous margins for the upper     *)
(* point of the C868 central pair.  Purely scalar; Normal is c977cc_normal.  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C868UPM_NORMALS_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (find_term (fun t -> try fst(dest_const t) = "c977cc_normal"
                                with _ -> false)) (concl th)
    then (ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
          STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2] th))
    else NO_TAC)) THEN
  REWRITE_TAC[REAL_POW_2];;

(* Lean: axis_cone (private) *)
let C868UPM_AXIS_CONE = prove
 (`forall c s C S p q.
      c977cc_normal c s /\ c977cc_normal C S /\ &0 <= s * C - c * S /\
      &0 <= p /\ &0 <= c * p + s * q
      ==> &0 <= C * p + S * q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C868UPM_NORMALS_TAC THEN
  ASM_CASES_TAC `s = &0` THENL
   [SUBGOAL_THEN `S = &0` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
       [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = &0`)) THEN
      NLIN_TAC [];
      ALL_TAC] THEN
    NLIN_FACTS_TAC [] [`&0 <= C * p`] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= S * (c * p + s * q)`; `&0 <= (s * C - c * S) * p`] THEN
    NLIN_TAC []]);;

(* Lean: diagonal_cone (private) *)
let C868UPM_DIAGONAL_CONE = prove
 (`forall c s C S p q.
      c977cc_normal c s /\ c977cc_normal C S /\ s * C - c * S <= &0 /\
      &0 <= c * p + s * q /\ &0 <= p + q
      ==> &0 <= C * p + S * q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C868UPM_NORMALS_TAC THEN
  ASM_CASES_TAC `c:real = s` THENL
   [SUBGOAL_THEN `C:real = S` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
       [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `c:real = s`)) THEN
      NLIN_TAC [];
      ALL_TAC] THEN
    NLIN_FACTS_TAC [] [`&0 <= S * (p + q)`] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 < c - s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= (C - S) * (c * p + s * q)`; `&0 <= (c * S - s * C) * (p + q)`] THEN
    NLIN_TAC []]);;

(* Lean: axis_margin (private) *)
let C868UPM_AXIS_MARGIN = prove
 (`forall c s. c977cc_normal c s
         ==> &0 <= c - &1 + &9 / &100 * c * s + &13 / &20 * s pow 2`,
  REPEAT STRIP_TAC THEN C868UPM_NORMALS_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (&1 - c) * (&13 / &20 * c - &7 / &20)`; `&0 <= c * s`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: above *)
let C868UPM_ABOVE = prove
 (`forall c s C S.
      c977cc_normal c s /\ c977cc_normal C S /\ &0 <= s * C - c * S
      ==> &0 <= (c * C + s * S) - C +
                (s * C - c * S) * (&9 / &100 * c + &13 / &20 * s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `C:real`; `S:real`;
                `c - &1 + s * (&9 / &100 * c + &13 / &20 * s)`;
                `s - c * (&9 / &100 * c + &13 / &20 * s)`] C868UPM_AXIS_CONE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP C868UPM_AXIS_MARGIN o
      check (fun th -> concl th = `c977cc_normal c s`)) THEN
    C868UPM_NORMALS_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
    NLIN_TAC ~deg2:false [];
    REAL_ARITH_TAC]);;

(* Lean: below *)
let C868UPM_BELOW = prove
 (`forall c s C S.
      c977cc_normal c s /\ c977cc_normal C S /\ s * C - c * S <= &0
      ==> &0 <= (c * C + s * S) - C -
                (s * C - c * S) * (&61 / &100 * c - &13 / &20 * s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `C:real`; `S:real`;
                `c - &1 - s * (&61 / &100 * c - &13 / &20 * s)`;
                `s + c * (&61 / &100 * c - &13 / &20 * s)`] C868UPM_DIAGONAL_CONE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN C868UPM_NORMALS_TAC THEN CONJ_TAC THENL
     [NLIN_TAC ~deg2:false [];
      NLIN_FACTS_TAC []
       [`&0 <= (c + s - &1) * (&3 / &2 - (c + s))`;
        `&4 / &5 * c * s <= c + s - &1`; `&0 <= c * s`] THEN
      NLIN_TAC [SQ_NONNEG `c - s:real`; SQ_NONNEG `s:real`]];
    REAL_ARITH_TAC]);;

(* Lean: steep_coefficients (private) *)
let C868UPM_STEEP_COEFFICIENTS = prove
 (`forall c s. c977cc_normal c s /\ &61 * c <= &65 * s
         ==> &1 / &4 <= s - &7 / &20 - &13 / &20 * s pow 2 + &61 / &100 * c * s /\
             --(&1 / &5) <= &61 / &100 * s pow 2 + &13 / &20 * c * s - c /\
             &61 / &100 * s pow 2 + &13 / &20 * c * s - c <= --(&7 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C868UPM_NORMALS_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - &3 / &4`; SQ_NONNEG `c - s:real`]
   [`&0 <= (&65 * s - &61 * c) * (&65 * s + &61 * c)`;
    `c <= &3 / &4`; `&2 / &3 <= s`;
    `&0 <= (s - &2 / &3) * (s + &2 / &3)`; `&4 / &9 <= s * s`;
    `&0 <= (c - s) * (c + s)`; `s * s <= &1 / &2`;
    `&0 <= (c - &7 / &10) * s`; `&7 / &15 <= c * s`; `c * s <= &1 / &2`] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

(* Lean: steep *)
let C868UPM_STEEP = prove
 (`forall c s C S.
      c977cc_normal c s /\ c977cc_normal C S /\ &61 * c <= &65 * s /\
      &61 * S <= &35 * C
      ==> &0 <= C * (s - &7 / &20 - &13 / &20 * s pow 2 + &61 / &100 * c * s) +
                S * (&61 / &100 * s pow 2 + &13 / &20 * c * s - c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C868UPM_STEEP_COEFFICIENTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `A1 = s - &7 / &20 - &13 / &20 * s pow 2 + &61 / &100 * c * s` THEN
  ABBREV_TAC `A2 = &61 / &100 * s pow 2 + &13 / &20 * c * s - c` THEN
  STRIP_TAC THEN C868UPM_NORMALS_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= C * (A1 - &1 / &4)`; `&0 <= S * (A2 - --(&1 / &5))`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: negative_above *)
let C868UPM_NEGATIVE_ABOVE = prove
 (`forall c s C Tn.
      c977cc_normal c s /\ c977cc_normal C Tn
      ==> &0 <= (c * C - s * Tn) - C + &13 / &50 * Tn +
                (s * C + c * Tn) * (&9 / &100 * c + &13 / &20 * s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C868UPM_AXIS_MARGIN o
    check (fun th -> concl th = `c977cc_normal c s`)) THEN
  ABBREV_TAC `M = c - &1 + &9 / &100 * c * s + &13 / &20 * s pow 2` THEN
  DISCH_TAC THEN C868UPM_NORMALS_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (C - Tn) * M`; `&0 <= &1 - &13 / &20 * c + &9 / &100 * s`;
    `&0 <= (c - s) * (&1 - &13 / &20 * c + &9 / &100 * s)`;
    `&0 <= Tn * ((c - s) * (&1 - &13 / &20 * c + &9 / &100 * s))`] THEN
  SUBGOAL_THEN
   `(c * C - s * Tn) - C + &13 / &50 * Tn + (s * C + c * Tn) * (&9 / &100 * c + &13 / &20 * s) =
    (C - Tn) * M + Tn * ((c - s) * (&1 - &13 / &20 * c + &9 / &100 * s))`
   SUBST1_TAC THENL
   [EXPAND_TAC "M" THEN
    UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING;
    ASM_REAL_ARITH_TAC]);;

(* Lean: negative_steep *)
let C868UPM_NEGATIVE_STEEP = prove
 (`forall c s C Tn.
      c977cc_normal c s /\ c977cc_normal C Tn /\ &61 * c <= &65 * s
      ==> &0 <= C * (s - &7 / &20 - &13 / &20 * s pow 2 + &61 / &100 * c * s) +
                Tn * (&13 / &50 - (&61 / &100 * s pow 2 + &13 / &20 * c * s - c))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C868UPM_STEEP_COEFFICIENTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `A1 = s - &7 / &20 - &13 / &20 * s pow 2 + &61 / &100 * c * s` THEN
  ABBREV_TAC `A2 = &61 / &100 * s pow 2 + &13 / &20 * c * s - c` THEN
  STRIP_TAC THEN C868UPM_NORMALS_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= C * A1`; `&0 <= Tn * (&13 / &50 - A2)`] THEN
  ASM_REAL_ARITH_TAC);;
