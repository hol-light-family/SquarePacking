(* ========================================================================= *)
(* Port of Compact/Geometry/DoubleAuxWallMargins.lean (Jatloe, N12-jatloe)   *)
(* (namespace N12Compact.DoubleAuxWallMargins).                              *)
(* Continuous scalar estimates for the wall owning both auxiliary points.    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

(* Adds |- &0 <= a * b (resp. &0 < a * b) from linear-arithmetic facts.      *)
let DAWM_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let DAWM_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

(* Lean: wall_bounds (private) *)
let DAWM_WALL_BOUNDS = prove
 (`forall C S. &0 < C /\ &0 <= S /\ C pow 2 + S pow 2 = &1 /\
         &0 < &1 + (&9 / &10) * C * S - C - S
         ==> C <= &1 /\ S <= &1 /\ &11 / &9 < C + S /\ C + S <= &10 / &7 /\
             (&21 / &80) * C < S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `S:real`; SQ_NONNEG `C:real`] [`C <= &1`; `S <= &1`] THEN
  DAWM_PROD_TAC `C:real` `S:real` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `C - S:real`] [`&1 <= C + S`; `C + S <= &10 / &7`] THEN
  SUBGOAL_THEN `&11 / &9 < C + S` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   DAWM_PROD_TAC `C + S - &1` `&11 - &9 * (C + S)` THEN NLIN_TAC [];
   ALL_TAC] THEN
  DAWM_PRODLT_TAC `C + S - &11 / &9` `C + S + &11 / &9` THEN
  NLIN_FACTS_TAC [] [`&20 / &81 < C * S`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  DAWM_PROD_TAC `&21 * C - &80 * S` `&80 * C - &21 * S` THEN NLIN_TAC []);;

(* Lean: wall_margins (private) *)
let DAWM_WALL_MARGINS = prove
 (`forall C S. &0 < C /\ &0 <= S /\ C pow 2 + S pow 2 = &1 /\
         &0 < &1 + (&9 / &10) * C * S - C - S
         ==> &1 + (&9 / &10) * C * S - C - S <= (&137 / &850) * C * (&4 * S - C) /\
             &1 + (&9 / &10) * C * S - C - S <=
               C * ((&8 / &17) * S - (&37 / &850) * C)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] DAWM_WALL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  DAWM_PROD_TAC `C + S - &1` `&10 / &7 - (C + S)` THEN
  NLIN_FACTS_TAC [] [`(&14 / &17) * C * S <= C + S - &1`] THEN
  DAWM_PROD_TAC `C:real` `S - C / &4` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `C:real`]
    [`&1 + (&9 / &10) * C * S - C - S <= C * ((&8 / &17) * S - (&37 / &850) * C)`] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `S <= (&3 / &10) * C` THENL
  [SUBGOAL_THEN `C + S <= &13 / &10` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   DAWM_PROD_TAC `C + S - &1` `&13 / &10 - (C + S)` THEN
   NLIN_FACTS_TAC [] [`(&20 / &23) * C * S <= C + S - &1`] THEN
   DAWM_PROD_TAC `C:real` `S - (&21 / &80) * C` THEN
   NLIN_TAC [SQ_NONNEG `C:real`];
   DAWM_PROD_TAC `C:real` `S - (&3 / &10) * C` THEN
   NLIN_TAC [SQ_NONNEG `C:real`]]);;

(* Lean: bounds *)
let DAWM_BOUNDS = prove
 (`forall c s C S. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ &4 * s <= c /\
             &0 < C /\ &0 <= S /\ C pow 2 + S pow 2 = &1 /\
             &0 < &1 + (&9 / &10) * C * S - C - S
             ==> &0 < c * S - s * C /\
                 &0 <= (C + S - &1) * (c * C + s * S) - (&9 / &10) * s * C /\
                 &0 <= C * (c * S - s * C) * ((&1 / &2) * c + (&37 / &50) * s) -
                       (&1 + (&9 / &10) * C * S - C - S)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] DAWM_WALL_BOUNDS) THEN
  MP_TAC(SPECL [`C:real`; `S:real`] DAWM_WALL_MARGINS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
  [(* cross *)
   DAWM_PRODLT_TAC `c:real` `S - C / &4` THEN
   DAWM_PROD_TAC `C:real` `c / &4 - s` THEN NLIN_TAC ~deg2:false [];
   (* middle *)
   SUBGOAL_THEN `&0 <= c * C + s * S` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
   DAWM_PROD_TAC `C + S - &11 / &9` `c * C + s * S` THEN
   DAWM_PROD_TAC `C:real` `c - &4 * s` THEN
   DAWM_PROD_TAC `s:real` `S - C / &4` THEN
   DAWM_PROD_TAC `s:real` `C:real` THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c * s` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  DAWM_PROD_TAC `c - &4 * s` `c + &4 * s` THEN
  NLIN_FACTS_TAC [] [`s pow 2 <= &1 / &17`] THEN
  DAWM_PROD_TAC `c - &4 * s` `&4 * c - s` THEN
  NLIN_FACTS_TAC [] [`c * s <= &4 / &17`] THEN
  SUBGOAL_THEN `(c * S - s * C) * ((&1 / &2) * c + (&37 / &50) * s) =
                S / &2 + ((&37 / &50) * S - C / &2) * (c * s) -
                (S / &2 + (&37 / &50) * C) * s pow 2` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  DAWM_PROD_TAC `S / &2 + (&37 / &50) * C` `&1 / &17 - s pow 2` THEN
  ASM_CASES_TAC `&37 * S <= &25 * C` THENL
  [DAWM_PROD_TAC `C / &2 - (&37 / &50) * S` `&4 / &17 - c * s` THEN
   SUBGOAL_THEN `(&137 / &850) * (&4 * S - C) <=
                 (c * S - s * C) * ((&1 / &2) * c + (&37 / &50) * s)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   DAWM_PROD_TAC `C:real`
     `(c * S - s * C) * ((&1 / &2) * c + (&37 / &50) * s) - (&137 / &850) * (&4 * S - C)` THEN
   NLIN_TAC ~deg2:false [];
   DAWM_PROD_TAC `(&37 / &50) * S - C / &2` `c * s` THEN
   SUBGOAL_THEN `(&8 / &17) * S - (&37 / &850) * C <=
                 (c * S - s * C) * ((&1 / &2) * c + (&37 / &50) * s)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   DAWM_PROD_TAC `C:real`
     `(c * S - s * C) * ((&1 / &2) * c + (&37 / &50) * s) -
      ((&8 / &17) * S - (&37 / &850) * C)` THEN
   NLIN_TAC ~deg2:false []]);;
