(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F4OuterScalars.lean            *)
(* (namespace N12Compact.Completion.OtherCases.C983.F4OuterScalars).         *)
(* Whole-interval estimates of C983-F4-TOP-ONLY-8208-ENDING s4 and           *)
(* C983-F4-MIXED-NEGATIVE-8208-ENDING s4.  Lean-local `let`s are expanded.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;

(* Lean: outer_cap *)
let C983F4O_OUTER_CAP = prove
 (`forall c s. &19 / &20 < c /\ &0 < s /\ s < &3 / &10 /\ c pow 2 + s pow 2 = &1 /\
         s / (&1 + c) < &3 / &20
         ==> c + s / &2 - &1 < &42 / &409`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&20 * s < &3 * (&1 + c)` ASSUME_TAC THENL
   [UNDISCH_TAC `s / (&1 + c) < &3 / &20` THEN
    SUBGOAL_THEN `&0 < &1 + c` (fun th -> SIMP_TAC[th; REAL_LT_LDIV_EQ]) THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `s < &120 / &409` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`&0 < (&3 * c - (&20 * s - &3)) * (&3 * c + (&20 * s - &3))`;
      `&0 <= s * (&409 * s - &120)`] THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 < (&120 / &409 - s) * ((c + &391 / &409) / &2 - (s + &120 / &409))`] THEN
  SUBGOAL_THEN `((&451 / &409) - (c + s / &2)) * (c + &391 / &409) =
     (&120 / &409 - s) * ((c + &391 / &409) / &2 - (s + &120 / &409))` ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`&0 < (&451 / &409) - (c + s / &2)`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: cosine_quadratic (private) *)
let C983F4O_COSINE_QUADRATIC = prove
 (`forall d r. &0 < d /\ d pow 2 + r pow 2 = &1 ==> d <= &1 - r pow 2 / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN NLIN_TAC [SQ_NONNEG `d - &1`]);;

(* Lean: positive_angle *)
let C983F4O_POSITIVE_ANGLE = prove
 (`forall d r. &0 < d /\ &0 <= r /\ d pow 2 + r pow 2 = &1 /\ &1 < r + (&19 / &25) * d
         ==> &13 / &50 < r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C983F4O_COSINE_QUADRATIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (&13 / &50 - r) * (&1 - (&19 / &50) * (r + &13 / &50))`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: cubic_floor (private) *)
let C983F4O_CUBIC_FLOOR = prove
 (`forall r. &13 / &50 <= r /\ r <= &3 / &5
       ==> &1401 / &12500 <= (&37 / &50) * r - r pow 2 + (&13 / &100) * r pow 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (r - &13 / &50) * (&461 / &500 - (&13 / &100) * (r + &13 / &50))`;
    `&0 <= (&461 / &500) * r - &467 / &2500 - (&13 / &100) * r pow 2`;
    `&0 <= (&3 / &5 - r) * ((&461 / &500) * r - &467 / &2500 - (&13 / &100) * r pow 2)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: product_floor (private) *)
let C983F4O_PRODUCT_FLOOR = prove
 (`forall d r. &0 < d /\ &3 / &5 <= r /\ r <= d /\ d pow 2 + r pow 2 = &1
         ==> &12 / &25 <= d * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [] [`&0 < r`; `&9 / &25 <= r pow 2`; `r pow 2 <= &1 / &2`;
    `&0 <= (r pow 2 - &9 / &25) * (&16 / &25 - r pow 2)`] THEN
  SUBGOAL_THEN `(d * r) pow 2 = r pow 2 - r pow 4` ASSUME_TAC THENL
   [UNDISCH_TAC `d pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`(&12 / &25) pow 2 <= (d * r) pow 2`; `&0 < d * r`] THEN
  NLIN_TAC []);;

(* Lean: positive_support *)
let C983F4O_POSITIVE_SUPPORT = prove
 (`forall c s d r A V.
     &19 / &20 < c /\ &0 < s /\ s < &3 / &10 /\ c pow 2 + s pow 2 = &1 /\
     &0 < d /\ &0 <= r /\ r <= d /\ d pow 2 + r pow 2 = &1 /\
     &13 / &50 < r /\ &0 < A /\
     (&13 / &50) * d < --V /\ &1 - r - (&13 / &50) * d < --V
     ==> &42 / &409 < (c * d - s * r) * A - (c * r + s * d) * V`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [] [`&0 < c`; `&0 < r`; `&0 <= s * (d - r)`; `&0 < d * (c - s)`] THEN
  NLIN_FACTS_TAC [] [`&0 < c * d - s * r`; `&0 < c * r`; `&0 < s * d`] THEN
  NLIN_FACTS_TAC [] [`&0 < c * r + s * d`; `&0 < (c * d - s * r) * A`] THEN
  ASM_CASES_TAC `r <= &3 / &5` THENL
   [MP_TAC(SPECL [`d:real`; `r:real`] C983F4O_COSINE_QUADRATIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(SPEC `r:real` C983F4O_CUBIC_FLOOR) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    NLIN_FACTS_TAC [SQ_NONNEG `r:real`]
     [`&0 < &37 / &50 - r + (&13 / &100) * r pow 2`;
      `&37 / &50 - r + (&13 / &100) * r pow 2 < --V`] THEN
    NLIN_FACTS_TAC []
     [`&0 < (c * r + s * d) * (--V - (&37 / &50 - r + (&13 / &100) * r pow 2))`;
      `&0 < (c - &19 / &20) * r`] THEN
    NLIN_FACTS_TAC [] [`(&19 / &20) * r < c * r + s * d`] THEN
    NLIN_FACTS_TAC []
     [`&0 < (&37 / &50 - r + (&13 / &100) * r pow 2) *
            ((c * r + s * d) - (&19 / &20) * r)`] THEN
    NLIN_TAC ~deg2:false [];
    MP_TAC(SPECL [`d:real`; `r:real`] C983F4O_PRODUCT_FLOOR) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 < (c * r + s * d) * (--V - (&13 / &50) * d)`;
      `&0 < s * d pow 2`; `&0 < d * r`;
      `&0 < (c - &19 / &20) * (d * r)`] THEN
    NLIN_TAC ~deg2:false []]);;

(* Lean: negative_chord (private) *)
let C983F4O_NEGATIVE_CHORD = prove
 (`forall d r. &0 < d /\ &39 / &100 < r /\ r <= d /\ d pow 2 + r pow 2 = &1
         ==> (&1 - (&1412 / &3479)) / &2 + (&1412 / &3479) * r pow 2 <= d * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [] [`&0 < r`; `&1521 / &10000 <= r pow 2`; `r pow 2 <= &1 / &2`] THEN
  ABBREV_TAC `u = r pow 2` THEN
  ABBREV_TAC `L = (&1 - (&1412 / &3479)) / &2 + (&1412 / &3479) * u` THEN
  SUBGOAL_THEN `&0 <= L /\
     &0 <= (&1 + (&1412 / &3479) pow 2) * u - (&1 - &1412 / &3479) pow 2 / &2`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (&1 / &2 - u) *
       ((&1 + (&1412 / &3479) pow 2) * u - (&1 - &1412 / &3479) pow 2 / &2)`] THEN
  SUBGOAL_THEN `u - u pow 2 - L pow 2 = (&1 / &2 - u) *
       ((&1 + (&1412 / &3479) pow 2) * u - (&1 - &1412 / &3479) pow 2 / &2) /\
     (d * r) pow 2 = u - u pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "L" THEN CONV_TAC REAL_RING;
      MAP_EVERY UNDISCH_TAC [`d pow 2 + u = &1`; `r pow 2 = u`] THEN
      CONV_TAC REAL_RING]; ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`L pow 2 <= (d * r) pow 2`; `&0 < d * r`] THEN
  NLIN_TAC []);;

(* Lean: negative_support *)
let C983F4O_NEGATIVE_SUPPORT = prove
 (`forall c s d r.
     &19 / &20 < c /\ &0 < s /\ s < &3 / &10 /\ c pow 2 + s pow 2 = &1 /\
     &0 < d /\ &39 / &100 < r /\ r <= d /\ d pow 2 + r pow 2 = &1
     ==> &42 / &409 < c * ((&61 / &100) * d * r - (&7 / &20) * r pow 2) +
                      s * ((&61 / &100) * r pow 2 + (&7 / &20) * d * r - &7 / &20)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [] [`&0 < c`; `&0 < r`; `&1521 / &10000 <= r pow 2`;
                     `r pow 2 <= &1 / &2`] THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C983F4O_NEGATIVE_CHORD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `A = ((&61 / &100) * c + (&7 / &20) * s) * (&1 - &1412 / &3479) / &2 -
                  (&7 / &20) * s` THEN
  ABBREV_TAC `B = ((&61 / &100) * c + (&7 / &20) * s) * (&1412 / &3479) -
                  (&7 / &20) * c + (&61 / &100) * s` THEN
  NLIN_FACTS_TAC []
   [`&0 <= ((&61 / &100) * c + (&7 / &20) * s) *
       (d * r - ((&1 - (&1412 / &3479)) / &2 + (&1412 / &3479) * r pow 2))`] THEN
  SUBGOAL_THEN `A + B * r pow 2 <= c * ((&61 / &100) * d * r - (&7 / &20) * r pow 2) +
      s * ((&61 / &100) * r pow 2 + (&7 / &20) * d * r - &7 / &20) /\
      &2343 / &20000 < A + B * (&1521 / &10000)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN CONJ_TAC THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`&0 <= c * s`] THEN
  NLIN_FACTS_TAC [] [`&1 <= c + s`] THEN
  SUBGOAL_THEN `&13 / &100 <= A + B * (&1 / &2)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= B` THENL
   [NLIN_FACTS_TAC [] [`&0 <= B * (r pow 2 - &1521 / &10000)`] THEN
    NLIN_TAC ~deg2:false [];
    NLIN_FACTS_TAC [] [`&0 <= --B * (&1 / &2 - r pow 2)`] THEN
    NLIN_TAC ~deg2:false []]);;

(* Lean: negative_own_support *)
let C983F4O_NEGATIVE_OWN_SUPPORT = prove
 (`forall c s d r.
     &19 / &20 < c /\ &0 < s /\ s < &3 / &10 /\ c pow 2 + s pow 2 = &1 /\
     &0 < d /\ &39 / &100 < r /\ d pow 2 + r pow 2 = &1
     ==> (c * d + s * r) * (c + s / &2 - &1) - (c * r - s * d) * (s / &2) <
         (&13 / &50) * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`&0 < c`; `c <= &1`] THEN
  NLIN_FACTS_TAC [] [`&0 < (r - &39 / &100) * (r + &39 / &100)`] THEN
  NLIN_FACTS_TAC [] [`d < &921 / &1000`] THEN
  NLIN_FACTS_TAC [] [`&0 < s * (&3 / &10 - s)`] THEN
  ABBREV_TAC `A = (c - &1) pow 2 / &2 + c * s / &2` THEN
  ABBREV_TAC `B = s pow 2 / &2 - s + c * s / &2 - &13 / &50` THEN
  NLIN_FACTS_TAC [] [`(c - &1) pow 2 < &1 / &400`; `&0 <= s * (&1 - c)`;
                     `&0 <= c * s`] THEN
  SUBGOAL_THEN `&0 <= A /\ A < &1 / &800 + s / &2 /\
     B <= s pow 2 / &2 - s / &2 - &13 / &50 /\ B < &0` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    MP_TAC(SQ_NONNEG `c - &1`) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= A * (&921 / &1000 - d) /\
    &0 < (&1 / &800 + s / &2 - A) * (&921 / &1000) /\
    &0 < (r - &39 / &100) * --B /\
    &0 <= (&39 / &100) * ((s pow 2 / &2 - s / &2 - &13 / &50) - B) /\
    &0 < (&3 / &10 - s) * (&531 / &2000 + (&39 / &200) * (s + &3 / &10))`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    (MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(c * d + s * r) * (c + s / &2 - &1) - (c * r - s * d) * (s / &2) -
     (&13 / &50) * r = d * A + r * B` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
