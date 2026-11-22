(* ========================================================================= *)
(* Port of Compact/Geometry/SteepElbowTopSegment.lean (Jatloe, N12-jatloe).   *)
(* A steep centre-escaping elbow meets the top segment (1.6,3)-(2.26,3).     *)
(* Normal: c977cc_normal; normal_bounds: C977CC_NORMAL_BOUNDS;               *)
(* CentralWallEscape.crossing_point: CWE_CROSSING_POINT;                     *)
(* pullSwap: LINSIDE_PULLSW; S12.inside_segment: CES_INSIDE_SEGMENT.         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralWallEscape.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

(* Lean: endpoint *)
let SETS_ENDPOINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ &0 <= s /\ c <= s /\
     linside c s u v a (&2) (&113 / &50) /\
     linside c s u v a (&113 / &50) (&2) /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&2) (&2) /\
     ~linside c s u v a (&3) (&12 / &5) /\
     (&13 / &50) * c + s <= &1
     ==> linside c s u v a (&113 / &50) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c977cc_normal s c` ASSUME_TAC THENL
  [REWRITE_TAC[c977cc_normal] THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `c * c + s * s = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  SUBGOAL_THEN `(&3 / &5) * c + (&37 / &50) * s <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `(&37 / &50) * c - (&3 / &5) * s`;
             SQ_NONNEG `(&3 / &5) * c + (&37 / &50) * s - &1`]; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 * (c + s) <= u` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(&3) * s + (&12 / &5) * c <= v` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: impossible *)
let SETS_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cT sT uT vT aT.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cT * cT + sT * sT = &1 /\ &0 < aT /\
     &1 < aA /\ &0 < cA /\ &0 <= sA /\ cA <= sA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&2) (&2) /\
     ~linside cA sA uA vA aA (&3) (&12 / &5) /\
     ~linside cA sA uA vA aA (&3) (&5 / &2) /\
     linside cT sT uT vT aT (&8 / &5) (&3) /\
     linside cT sT uT vT aT (&113 / &50) (&3) /\
     ldisj cA sA uA vA aA cT sT uT vT aT
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sA` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_normal sA cA` ASSUME_TAC THENL
  [REWRITE_TAC[c977cc_normal] THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `cA * cA + sA * sA = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  ABBREV_TAC `z = cA / (&1 + sA)` THEN
  SUBGOAL_THEN `(&1 + sA) * z = cA /\ cA * z = &1 - sA` STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "z" THEN UNDISCH_TAC `&0 < sA` THEN
   UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= z` ASSUME_TAC THENL
  [EXPAND_TAC "z" THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `ldisj cA sA uA vA aA cT sT uT vT aT` THEN REWRITE_TAC[ldisj] THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `&13 / &50 <= z` THENL
  [SUBGOAL_THEN `(&13 / &50) * cA + sA <= &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= cA * (z - &13 / &50)` MP_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `cA * z = &1 - sA` THEN REAL_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`&113 / &50`; `&3`]) THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SETS_ENDPOINT THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `cA <= (&16 / &25) * sA` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= (&1 + sA) * (&13 / &50 - z)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `(&1 + sA) * z = cA` THEN UNDISCH_TAC `&7 / &10 <= sA` THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `linside cA sA uA vA aA (&2 + z) (&3)` ASSUME_TAC THENL
  [MP_TAC(SPECL [`sA:real`; `cA:real`; `uA:real`; `--vA - aA`; `aA:real`; `z:real`]
     CWE_CROSSING_POINT) THEN
   REWRITE_TAC[LINSIDE_PULLSW] THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&2 + z`; `&3`]) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aT:real`;
                `&8 / &5`; `&3`; `&113 / &50`; `&3`; `(&20 + &50 * z) / &33`]
    CES_INSIDE_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN
  BINOP_TAC THEN REAL_ARITH_TAC);;
