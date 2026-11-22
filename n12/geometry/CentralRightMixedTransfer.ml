(* ========================================================================= *)
(* Port of Compact/Geometry/CentralRightMixedTransfer.lean                   *)
(* (namespace N12Compact.CentralRightMixedTransfer).                         *)
(* Full-square support transfers in the centre-owned right chain.  Lean      *)
(* `upper B d t` is ABT_upper cB sB uB vB aB d t; upper_in_bands is          *)
(* C977NCO_UPPER_IN_BANDS.  Normal c s is c977cc_normal c s.                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralRightCornerSupport.ml";;

let CRMT_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

let CRMT_LE_CANCEL = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: steeper_direction_margin *)
let CRMT_STEEPER_DIRECTION_MARGIN = prove
 (`forall c s d t. c977cc_normal c s /\ &0 <= d /\ &0 <= c * t - s * d
     ==> d <= c * d + s * t - (&13 / &50) * s * (c * t - s * d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= d * (&1 - c)`; `&0 <= s * (c * t - s * d)`;
    `&0 <= (s * (c * t - s * d)) * (&1 - (&13 / &50) * c)`] THEN
  MATCH_MP_TAC CRMT_LE_CANCEL THEN EXISTS_TAC `c:real` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC ~deg2:false [CRMT_EQ_HINT `d:real` (ASSUME `c pow 2 + s pow 2 = &1`)]);;

(* Lean: steeper_margin *)
let CRMT_STEEPER_MARGIN = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &0 <= c * t - s * d
     ==> d <= c * d + s * t - (&13 / &50) * s * (c * t - s * d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CRMT_STEEPER_DIRECTION_MARGIN THEN
  ASM_REWRITE_TAC[] THEN C977CSB_NORMAL_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: steeper_direction_reach *)
let CRMT_STEEPER_DIRECTION_REACH = prove
 (`forall cB sB uB vB aB d t.
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cB sB /\ &0 < d /\ &0 <= t /\ &1 < aB /\
     linside cB sB uB vB aB (&113 / &50) (&2) /\
     &2 * (cB + sB) <= uB /\ &0 <= cB * t - sB * d
     ==> &3 * d + &2 * t < ABT_upper cB sB uB vB aB d t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `d:real`; `t:real`] CRMT_STEEPER_DIRECTION_MARGIN) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  UNDISCH_TAC `linside cB sB uB vB aB (&113 / &50) (&2)` THEN
  REWRITE_TAC[linside] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [] [`&0 < d * cB`; `&0 <= t * sB`; `&0 < d * cB + t * sB`] THEN
  REWRITE_TAC[C977NCO_UPPER_IN_BANDS] THEN
  SUBGOAL_THEN `abs(d * cB + t * sB) = d * cB + t * sB /\
                abs(--d * sB + t * cB) = --d * sB + t * cB` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (d * cB + t * sB) * (uB - &2 * (cB + sB))`;
    `&0 <= (t * cB - d * sB) * ((vB + aB) - (--sB * &113 / &50 + cB * &2))`;
    `&0 < (aB - &1) * (d * cB + t * sB)`] THEN
  NLIN_TAC ~deg2:false [CRMT_EQ_HINT `&2 * (d + t)` (ASSUME `cB pow 2 + sB pow 2 = &1`)]);;

(* Lean: steeper_reach *)
let CRMT_STEEPER_REACH = prove
 (`forall cB sB uB vB aB d t.
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cB sB /\ c977cc_normal d t /\ &1 < aB /\
     linside cB sB uB vB aB (&113 / &50) (&2) /\
     &2 * (cB + sB) <= uB /\ &0 <= cB * t - sB * d
     ==> &3 * d + &2 * t < ABT_upper cB sB uB vB aB d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CRMT_STEEPER_DIRECTION_REACH THEN
  ASM_REWRITE_TAC[] THEN C977CSB_NORMAL_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: steeper_wall_shift *)
let CRMT_STEEPER_WALL_SHIFT = prove
 (`forall cB sB uB vB aB cR sR uR (vR:real) aR.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     c977cc_normal cB sB /\ c977cc_normal cR sR /\ &1 < aB /\
     linside cB sB uB vB aB (&113 / &50) (&2) /\
     &2 * (cB + sB) <= uB /\ &0 <= cB * sR - sB * cR /\
     ABT_upper cB sB uB vB aB cR sR <= uR
     ==> &3 * cR + &2 * sR < uR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `cR:real`; `sR:real`]
    CRMT_STEEPER_REACH) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: half_angle_coefficient (private) *)
let CRMT_HALF_ANGLE_COEFFICIENT = prove
 (`forall c s. c977cc_normal c s ==> s <= (&7 / &20) * (c + s) * (&1 + c)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= (c - &7 / &10) * (c + s + &17 / &10)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: shallower_margin *)
let CRMT_SHALLOWER_MARGIN = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &0 <= s * d - c * t
     ==> &1 <= c * d + s * t + (&7 / &20) * (c + s) * (s * d - c * t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CRMT_HALF_ANGLE_COEFFICIENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  let K = `c * d + s * t` and G = `s * d - c * t` in
  let sub tm = subst [K,`KK:real`; G,`GG:real`] tm in
  SUBGOAL_THEN (sub `KK pow 2 + GG pow 2 = &1`) ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`c pow 2 + s pow 2 = &1`; `d pow 2 + t pow 2 = &1`] THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_FACTS_TAC [] (map sub
   [`&0 <= c * d`; `&0 <= s * t`; `&0 <= KK`;
    `&0 <= s * (&1 - d)`; `&0 <= t * (&1 + c)`]) THEN
  SUBGOAL_THEN (sub `GG * (&1 + c) <= s * (&1 + KK)`) ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false [CRMT_EQ_HINT `t:real` (ASSUME `c pow 2 + s pow 2 = &1`)];
    ALL_TAC] THEN
  NLIN_FACTS_TAC [] (map sub
   [`&0 <= (&1 + KK) * ((&7 / &20) * (c + s) * (&1 + c) - s)`;
    `&0 <= (&1 + c) * ((&7 / &20) * (c + s) * (&1 + KK) - GG)`;
    `&0 <= (&7 / &20) * (c + s) * (&1 + KK) - GG`;
    `&0 <= GG * ((&7 / &20) * (c + s) * (&1 + KK) - GG)`]) THEN
  MATCH_MP_TAC CRMT_LE_CANCEL THEN EXISTS_TAC (sub `&1 + KK`) THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC ~deg2:false [CRMT_EQ_HINT `&1` (ASSUME (sub `KK pow 2 + GG pow 2 = &1`))]);;

(* Lean: shallower_reach *)
let CRMT_SHALLOWER_REACH = prove
 (`forall cB sB uB vB aB d t.
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cB sB /\ c977cc_normal d t /\ &1 < aB /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     &2 * (cB + sB) <= uB /\ &0 <= sB * d - cB * t
     ==> &2 * (d + t) + &1 < ABT_upper cB sB uB vB aB d t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `d:real`; `t:real`] CRMT_SHALLOWER_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `linside cB sB uB vB aB (&47 / &20) (&33 / &20)` THEN
  REWRITE_TAC[linside] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [] [`&0 < d * cB`; `&0 <= t * sB`; `&0 < d * cB + t * sB`] THEN
  REWRITE_TAC[C977NCO_UPPER_IN_BANDS] THEN
  SUBGOAL_THEN `abs(d * cB + t * sB) = d * cB + t * sB /\
                abs(--d * sB + t * cB) = d * sB - t * cB` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (d * cB + t * sB) * (uB - &2 * (cB + sB))`;
    `&0 <= (d * sB - t * cB) * ((--sB * &47 / &20 + cB * &33 / &20) - vB)`;
    `&0 < (aB - &1) * (d * cB + t * sB)`] THEN
  NLIN_TAC ~deg2:false [CRMT_EQ_HINT `&2 * (d + t)` (ASSUME `cB pow 2 + sB pow 2 = &1`)]);;
