(* ========================================================================= *)
(* Port of Compact/Geometry/RightWallOuterSegment.lean (Jatloe, N12-jatloe).  *)
(* An outer horizontal segment from (3.2,3) to (3.5,3) blocks the lower-U    *)
(* escape of a positive right wall: a closed point of the wall at height 3   *)
(* lies on the segment.                                                      *)
(* Normal: c977cc_normal; normal_bounds: C977CC_NORMAL_BOUNDS;               *)
(* CentralWallEscape.right_wall: CWE_RIGHT_WALL;                             *)
(* ClosedPointExclusion.outside_of_closed: OUTSIDE_OF_CLOSED.                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralWallEscape.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

(* Lean: affine_between (private) *)
let RWOS_AFFINE_BETWEEN = prove
 (`forall k b low high x a z.
     (low < k * a + b /\ k * a + b < high) /\
     (low < k * z + b /\ k * z + b < high) /\
     a <= x /\ x <= z
     ==> low < k * x + b /\ k * x + b < high`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `&0 <= k` THENL
  [SUBGOAL_THEN `&0 <= k * (x - a) /\ &0 <= k * (z - x)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC];
   SUBGOAL_THEN `&0 <= --k * (x - a) /\ &0 <= --k * (z - x)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC]] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: row_segment (private) *)
let RWOS_ROW_SEGMENT = prove
 (`forall c s u v a x.
     linside c s u v a (&16 / &5) (&3) /\ linside c s u v a (&7 / &2) (&3) /\
     &16 / &5 <= x /\ x <= &7 / &2
     ==> linside c s u v a x (&3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s * &3`; `u:real`; `u + a:real`; `x:real`;
                `&16 / &5`; `&7 / &2`] RWOS_AFFINE_BETWEEN) THEN
  MP_TAC(SPECL [`--s:real`; `c * &3`; `v:real`; `v + a:real`; `x:real`;
                `&16 / &5`; `&7 / &2`] RWOS_AFFINE_BETWEEN) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: circle_margin (private) *)
let RWOS_CIRCLE_MARGIN = prove
 (`forall d t. c977cc_normal d t ==> &1 + d * t - t pow 2 / &2 <= d + t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(ASSUME `c977cc_normal d t`) THEN REWRITE_TAC[c977cc_normal] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= t pow 2 * (d + &2 * t - &1)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * (&1 + d) * (d + t - &1 - d * t + t pow 2 / &2) =
                t pow 2 * (d + &2 * t - &1)` ASSUME_TAC THENL
  [UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= d + t - &1 - d * t + t pow 2 / &2
                           ==> &1 + d * t - t pow 2 / &2 <= d + t`) THEN
  SUBGOAL_THEN `&0 <= (&1 + d) * (d + t - &1 - d * t + t pow 2 / &2)` MP_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + d` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`d + t - &1 - d * t + t pow 2 / &2`,`X:real`) THEN
  SPEC_TAC(`&1 + d`,`K:real`) THEN REPEAT STRIP_TAC THEN NLIN_TAC []);;

let RWOS_POS_OF_MUL = prove
 (`forall k p. &0 < k /\ &0 < k * p ==> &0 < p`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: impossible *)
let RWOS_IMPOSSIBLE = prove
 (`forall cR sR uR vR aR cE sE uE vE aE.
     cR * cR + sR * sR = &1 /\ &0 < aR /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c977cc_normal cR sR /\ &1 < aR /\ lcont cR sR uR vR aR /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     &3 * cR + &2 * sR <= uR /\
     linside cE sE uE vE aE (&16 / &5) (&3) /\
     linside cE sE uE vE aE (&7 / &2) (&3) /\
     ldisj cE sE uE vE aE cR sR uR vR aR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(ASSUME `c977cc_normal cR sR`) THEN
  REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < cR` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`]
    CWE_RIGHT_WALL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `sR = &0` THENL
  [SUBGOAL_THEN `cR = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `sR = &0` THEN DISCH_THEN SUBST_ALL_TAC THEN
   REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN NLIN_TAC [];
    ALL_TAC] THEN
   UNDISCH_TAC `cR * (uR + aR) - sR * vR <= &4` THEN
   UNDISCH_TAC `&3 * cR + &2 * sR <= uR` THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sR` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 / &5) * cR + sR < &1` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `linside cR sR uR vR aR (&1543 / &500) (&2)` THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  SUBGOAL_THEN `vR + aR <= &3 * cR - (&16 / &5) * sR` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   UNDISCH_TAC `ldisj cE sE uE vE aE cR sR uR vR aR` THEN
   REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&16 / &5`; `&3`]) THEN
   ASM_REWRITE_TAC[] THEN REWRITE_TAC[linside] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `H = vR + aR` THEN
  ABBREV_TAC `X = (&3 * cR - H) / sR` THEN
  SUBGOAL_THEN `sR * X = &3 * cR - H` ASSUME_TAC THENL
  [EXPAND_TAC "X" THEN UNDISCH_TAC `&0 < sR` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `sR * uR + cR * H < &3` ASSUME_TAC THENL
  [SUBGOAL_THEN `sR * uR < sR * (cR * &1543 / &500 + sR * &2) /\
                 cR * H <= cR * (&3 * cR - (&16 / &5) * sR) /\
                 &0 <= cR * sR /\ &0 <= sR * sR` MP_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
     REWRITE_TAC[REAL_LE_SQUARE]]; ALL_TAC] THEN
   UNDISCH_TAC `cR * cR + sR * sR = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&3 < sR * (uR + aR) + cR * H` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `&0 < x - &3 ==> &3 < x`) THEN
   MATCH_MP_TAC RWOS_POS_OF_MUL THEN EXISTS_TAC `sR:real` THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `&0 <= cR * (&4 - cR * (uR + aR) + sR * vR) /\
                 &0 <= (&1 - cR) * (&1 - sR) /\
                 &0 < (aR - &1) * (&1 + cR * sR)` MP_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC REAL_LTE_ADD THEN REWRITE_TAC[REAL_LT_01] THEN
     MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
   SUBGOAL_THEN `sR * (sR * (uR + aR) + cR * H - &3) =
                 cR * (&4 - cR * (uR + aR) + sR * vR) + (uR - (&3 * cR + &2 * sR)) +
                 (aR - &1) * (&1 + cR * sR) + (&1 - cR) * (&1 - sR)` MP_TAC THENL
   [EXPAND_TAC "H" THEN UNDISCH_TAC `cR * cR + sR * sR = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
   REPEAT DISCH_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sR * (cR * X + &3 * sR) = &3 - cR * H` ASSUME_TAC THENL
  [UNDISCH_TAC `sR * X = &3 * cR - H` THEN UNDISCH_TAC `cR * cR + sR * sR = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `lclosed cR sR uR vR aR X (&3)` ASSUME_TAC THENL
  [REWRITE_TAC[lclosed] THEN
   SUBGOAL_THEN `uR <= cR * X + &3 * sR /\ cR * X + &3 * sR <= uR + aR`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP REAL_LT_LMUL o CONJ (ASSUME `&0 < sR`)) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `sR * X = &3 * cR - H` THEN EXPAND_TAC "H" THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&16 / &5 <= X` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP REAL_LT_LMUL o CONJ (ASSUME `&0 < sR`) o
     check (fun th -> concl th = `X < &16 / &5`)) THEN
   EXPAND_TAC "H" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `X < &7 / &2` ASSUME_TAC THENL
  [MP_TAC(SPECL [`cR:real`; `sR:real`] RWOS_CIRCLE_MARGIN) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 <= cR * (uR - (&3 * cR + &2 * sR)) /\
                 &0 < (aR - &1) * (cR + sR)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `sR * (sR * X) = sR * (&3 * cR - H)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `sR pow 2 * (X - &7 / &2) < &0` MP_TAC THENL
   [UNDISCH_TAC `sR * (sR * X) = sR * (&3 * cR - H)` THEN EXPAND_TAC "H" THEN
    UNDISCH_TAC `cR * (uR + aR) - sR * vR <= &4` THEN
    UNDISCH_TAC `&1 + cR * sR - sR pow 2 / &2 <= cR + sR` THEN
    UNDISCH_TAC `&0 <= cR * (uR - (&3 * cR + &2 * sR))` THEN
    UNDISCH_TAC `&0 < (aR - &1) * (cR + sR)` THEN
    UNDISCH_TAC `cR * cR + sR * sR = &1` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[GSYM REAL_NOT_LE] THEN REPEAT DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                `X:real`; `&3`] OUTSIDE_OF_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM ldisj] THEN
  MATCH_MP_TAC RWOS_ROW_SEGMENT THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;
