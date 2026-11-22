(* ========================================================================= *)
(* Port of Compact/Geometry/DiagonalWallSegment.lean (Jatloe, N12-jatloe).    *)
(* A neighbouring square owning both ends of the diagonal segment from       *)
(* (3,12/5) to (12/5,3) excludes two outer points of an elbow square and     *)
(* meets every middle-angle centre escape.                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralWallCenter.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let DWS_SEGMENT_TAC sq p0 p1 t =
  let c,s,u,v,a = sq and (x0,y0) = p0 and (x1,y1) = p1 in
  MP_TAC(SPECL [c; s; u; v; a; x0; y0; x1; y1; t] CES_INSIDE_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC;;

(* Lean: missing_top *)
let DWS_MISSING_TOP = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     linside cR sR uR vR aR (&12 / &5) (&3) /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> ~linside cA sA uA vA aA (&5 / &2) (&3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN DISCH_TAC THEN
  DWS_SEGMENT_TAC (`cA:real`,`sA:real`,`uA:real`,`vA:real`,`aA:real`)
    (`&5 / &2`,`&3`) (`&113 / &50`,`&2`) `&5 / &62` THEN
  DWS_SEGMENT_TAC (`cR:real`,`sR:real`,`uR:real`,`vR:real`,`aR:real`)
    (`&12 / &5`,`&3`) (`&3`,`&12 / &5`) `&25 / &186` THEN
  ASM_MESON_TAC[]);;

(* Lean: missing_right *)
let DWS_MISSING_RIGHT = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     linside cR sR uR vR aR (&12 / &5) (&3) /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> ~linside cA sA uA vA aA (&3) (&5 / &2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN DISCH_TAC THEN
  DWS_SEGMENT_TAC (`cA:real`,`sA:real`,`uA:real`,`vA:real`,`aA:real`)
    (`&3`,`&5 / &2`) (`&2`,`&113 / &50`) `&5 / &62` THEN
  DWS_SEGMENT_TAC (`cR:real`,`sR:real`,`uR:real`,`vR:real`,`aR:real`)
    (`&3`,`&12 / &5`) (`&12 / &5`,`&3`) `&25 / &186` THEN
  ASM_MESON_TAC[]);;

(* Lean: middle_margin (private) *)
let DWS_MIDDLE_MARGIN = prove
 (`forall c s. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ c <= s /\ s <= &2 * c
         ==> &0 < c + s - &21 / &20 - (&7 / &10) * c * s`,
  REWRITE_TAC[REAL_POW_2] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c + s <= &10 / &7` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `c - s:real`; SQ_NONNEG `c + s - &10 / &7`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&2 * c - s) * (&2 * s - c)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&4 / &3 <= c + s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 <= (&4 / &3 - (c + s)) * (c + s + &4 / &3)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (c + s - &4 / &3) * (&1 - (&7 / &20) * (c + s + &4 / &3))`
  MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: middle_impossible *)
let DWS_MIDDLE_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ &0 < cA /\ &0 <= sA /\ cA <= sA /\ sA <= &2 * cA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&2) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     linside cR sR uR vR aR (&12 / &5) (&3) /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CWPA_UNFOLD_TAC `linside cA sA uA vA aA (&2) (&113 / &50)` THEN
  CWPA_UNFOLD_TAC `linside cA sA uA vA aA (&113 / &50) (&2)` THEN
  CWPA_UNFOLD_TAC `linside cA sA uA vA aA (&47 / &20) (&47 / &20)` THEN
  SUBGOAL_THEN `&2 * (cA + sA) <= uA` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside cA sA uA vA aA (&2) (&2)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exists k. &12 * (cA + sA) * k = &13 * sA - cA` STRIP_ASSUME_TAC THENL
  [EXISTS_TAC `(&13 * sA - cA) / (&12 * (cA + sA))` THEN
   UNDISCH_TAC `&0 < cA` THEN UNDISCH_TAC `&0 <= sA` THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= k /\ k <= &1` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                `&3`; `&12 / &5`; `&12 / &5`; `&3`; `k:real`] CES_INSIDE_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `(&1 - k) * &3 + k * &12 / &5 = &3 - &3 / &5 * k /\
                          (&1 - k) * &12 / &5 + k * &3 = &12 / &5 + &3 / &5 * k`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `linside cA sA uA vA aA (&3 - &3 / &5 * k) (&12 / &5 + &3 / &5 * k)`
  MP_TAC THENL
  [ALL_TAC;
   UNDISCH_TAC `ldisj cA sA uA vA aA cR sR uR vR aR` THEN REWRITE_TAC[ldisj] THEN
   ASM_MESON_TAC[]] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`] DWS_MIDDLE_MARGIN) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(cA + sA) * (&2 * (cA + sA) + &1 -
                 (cA * (&3 - &3 / &5 * k) + sA * (&12 / &5 + &3 / &5 * k))) =
    cA + sA - &21 / &20 - (&7 / &10) * cA * sA` ASSUME_TAC THENL
  [UNDISCH_TAC `&12 * (cA + sA) * k = &13 * sA - cA` THEN
   UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * (cA + sA) + &1 -
                (cA * (&3 - &3 / &5 * k) + sA * (&12 / &5 + &3 / &5 * k))`
  ASSUME_TAC THENL
  [MP_TAC(SPECL [`&0`; `&2 * (cA + sA) + &1 -
                (cA * (&3 - &3 / &5 * k) + sA * (&12 / &5 + &3 / &5 * k))`;
                 `cA + sA:real`] REAL_LT_LMUL_EQ) THEN
   REWRITE_TAC[REAL_MUL_RZERO] THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= k * (sA - cA)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;
