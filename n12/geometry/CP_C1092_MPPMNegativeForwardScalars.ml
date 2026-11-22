(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeForwardScalars.lean          *)
(* (N12Compact.C1092MPPMNegativeForward).  Exact all-angle scalar estimates  *)
(* for NEGATIVE-FORWARD-POSITIVE-H, sections 3 and 5.                        *)
(* Normal is c977cc_normal; half / quarter_data are C1092WPS_half /          *)
(* C1092WPS_QUARTER_DATA.                                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;

let C1092NFS_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let C1092NFS_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [MATCH_ACCEPT_TAC REAL_LE_POW_2; RASM_ARITH_TAC]; ALL_TAC];;

(* Lean: source_angle *)
let C1092NFS_SOURCE_ANGLE = prove
 (`forall c s. c977cc_normal c s /\ &1 < c + (&13 / &50) * s
         ==> &0 < s /\ &87 / &100 < c /\ s < &49 / &100 /\ c < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092NFS_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&87 / &100 < c` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `s < &49 / &100` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN NLIN_TAC []);;

(* Lean: disk_bound (private) *)
let C1092NFS_DISK_BOUND = prove
 (`forall c s P R. c pow 2 + s pow 2 = &1 /\ P pow 2 + R pow 2 <= &1 ==> P * c + R * s <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(P * c + R * s) pow 2 + (P * s - R * c) pow 2 = P pow 2 + R pow 2`
  ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPEC `P * s - R * c:real` REAL_LE_POW_2) THEN
  UNDISCH_TAC `(P * c + R * s) pow 2 + (P * s - R * c) pow 2 = P pow 2 + R pow 2` THEN
  UNDISCH_TAC `P pow 2 + R pow 2 <= &1` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`P * c + R * s`,`X:real`) THEN SPEC_TAC(`(P * s - R * c) pow 2`,`Y:real`) THEN
  SPEC_TAC(`P pow 2 + R pow 2`,`N:real`) THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  NLIN_TAC []);;

(* the half-angle form of the disk defect (identity step of longitudinal_margin) *)
let C1092NFS_LONG_IDENTITY = prove
 (`forall d t y. (&1 + y pow 2) * d = &1 - y pow 2 /\ (&1 + y pow 2) * t = &2 * y
     ==> (&1 + y pow 2) pow 2 *
         (&1 - (&1 - t + t pow 2 / &2 + (&37 / &50) * d * t) pow 2 -
               (&1 - d + d * t / &2 - (&37 / &50) * t pow 2) pow 2) =
         (&2 / &625) * y * (&325 - &1647 * y + &3425 * y pow 2 - &1250 * y pow 3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + y pow 2` ASSUME_TAC THENL
  [MP_TAC(SPEC `y:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d = (&1 - y pow 2) / (&1 + y pow 2) /\ t = (&2 * y) / (&1 + y pow 2)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
  [ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `&0 < x ==> ~(x = &0)`)) THEN
  CONV_TAC REAL_FIELD);;

(* Lean: longitudinal_margin *)
let C1092NFS_LONGITUDINAL_MARGIN = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t
     ==> &0 <= &1 + (c * t + s * d) - c - (c * t + s * d) * d - (c * t + s * d) * t / &2 +
               (&13 / &50) * (c * d - s * t) * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092NFS_NORMAL_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`C1092WPS_half d t`,`y:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `y:real` REAL_LE_POW_2) THEN DISCH_TAC THEN
  C1092NFS_PROD `&0 <= (&1 + y pow 2) * (d - t)` THEN
  SUBGOAL_THEN `y <= &5 / &12` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `y:real`] C1092NFS_LONG_IDENTITY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  C1092NFS_PROD `&0 <= y pow 2 * ((&3425 - &1250 * y) - &17425 / &6)` THEN
  SUBGOAL_THEN `&0 < &325 - &1647 * y + &3425 * y pow 2 - &1250 * y pow 3` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `y - &4941 / &17425`]; ALL_TAC] THEN
  C1092NFS_PROD `&0 <= y * (&325 - &1647 * y + &3425 * y pow 2 - &1250 * y pow 3)` THEN
  ABBREV_TAC `P = &1 - t + t pow 2 / &2 + (&37 / &50) * d * t` THEN
  ABBREV_TAC `R = &1 - d + d * t / &2 - (&37 / &50) * t pow 2` THEN
  SUBGOAL_THEN `P pow 2 + R pow 2 <= &1` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `&0 <= &1 - x ==> x <= &1`) THEN
   MATCH_MP_TAC(CONJUNCT1 C1092WPS_CANCEL) THEN EXISTS_TAC `(&1 + y pow 2) pow 2` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN MP_TAC(SPEC `y:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_ARITH `&1 - (a + b) = &1 - a - b`] THEN ASM_REWRITE_TAC[] THEN
    RASM_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `P:real`; `R:real`] C1092NFS_DISK_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `&1 + (c * t + s * d) - c - (c * t + s * d) * d - (c * t + s * d) * t / &2 +
                (&13 / &50) * (c * d - s * t) * t = &1 - P * c - R * s` SUBST1_TAC THENL
  [MAP_EVERY EXPAND_TAC ["P"; "R"] THEN UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: transverse_margin *)
let C1092NFS_TRANSVERSE_MARGIN = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &87 / &100 < c /\ s < &49 / &100
     ==> &0 < &1 + (c * d - s * t) + (c * t + s * d) - d - t / &2 - (c * t + s * d) * c -
              (&7 / &20) * (c * d - s * t) * (c - s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092NFS_NORMAL_TAC THEN
  ABBREV_TAC `P = &1 - c - s + (&13 / &20) * c * s + (&7 / &20) * c pow 2` THEN
  ABBREV_TAC `R = &3 / &2 - c + s - (&7 / &20) * c * s - (&13 / &20) * s pow 2` THEN
  SUBGOAL_THEN `P < &2 / &5` ASSUME_TAC THENL
  [EXPAND_TAC "P" THEN
   C1092NFS_PROD `&0 <= s * (&1 - (&13 / &20) * c)` THEN
   C1092NFS_PROD `&0 < (c - &87 / &100) * (&1 - (&7 / &20) * (c + &87 / &100))` THEN
   REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `R < &41 / &50` ASSUME_TAC THENL
  [EXPAND_TAC "R" THEN
   C1092NFS_PROD `&0 <= c * (c - &87 / &100)` THEN
   NLIN_TAC [SQ_NONNEG `s - &1391 / &2600`]; ALL_TAC] THEN
  C1092NFS_PROD `&0 < d * (&2 / &5 - P)` THEN
  C1092NFS_PROD `&0 <= t * (&41 / &50 - R)` THEN
  SUBGOAL_THEN `(&2 / &5) * d + (&41 / &50) * t < &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `(&2 / &5) * t - (&41 / &50) * d`]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 + (c * d - s * t) + (c * t + s * d) - d - t / &2 - (c * t + s * d) * c -
                (&7 / &20) * (c * d - s * t) * (c - s) = &1 - P * d - R * t` SUBST1_TAC THENL
  [MAP_EVERY EXPAND_TAC ["P"; "R"] THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;
