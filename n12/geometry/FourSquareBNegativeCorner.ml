(* ========================================================================= *)
(* Port of Compact/Geometry/FourSquareBNegativeCorner.lean                   *)
(* (N12Compact.FourSquareBNegativeCorner).  Complete exclusion of the        *)
(* negative canonical B branch in the original square model.                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FourSquareBNegative.ml";;

(* Lean: center_above_radius *)
let FSBNC_CENTER_ABOVE_RADIUS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     &0 < c /\ s <= &0 /\ --s <= c /\ &1 < a /\ a <= &1001 / &1000 /\
     lclosed c s u v a (&8 / &5) (&3) /\
     ~scap_longsec c s u v a (&12 / &5)
     ==> &12 / &5 + (c - s + &2 * c * s) / &2 < lcy c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c + s`] [`c - s <= &10 / &7`; `--c * s <= &1 / &2`] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&8 / &5`; `&3`;
                `&0`; `&1`] TSS_CLOSED_SUPPORT) THEN
  ASM_REWRITE_TAC[tss_support_radius] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_ADD_LID; REAL_NEG_0] THEN
  ASM_SIMP_TAC[REAL_ARITH `s <= &0 ==> abs s = --s`;
               REAL_ARITH `&0 < c ==> abs c = c`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `a * (c - s) <= &1001 / &1000 * (c - s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN FSBC_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&12 / &5 - (c - s + &2 * c * s) / &2 <= lcy c s u v a` ASSUME_TAC THENL
   [UNDISCH_TAC `abs(&3 - lcy c s u v a) <= a / &2 * (--s + c)` THEN
    FSBC_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  UNDISCH_TAC `~scap_longsec c s u v a (&12 / &5)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC LSEC_HORIZONTAL_LONG_SECTION THEN
  ASM_REWRITE_TAC[lsec_radius] THEN CONJ_TAC THENL [FSBC_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * s <= &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= c * --s ==> c * s <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN FSBC_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `s <= &0 ==> abs s = --s`;
               REAL_ARITH `&0 < c ==> abs c = c`] THEN
  FSBC_ARITH_TAC);;

(* Lean: upper_corner *)
let FSBNC_UPPER_CORNER = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     &0 < c /\ s <= &0 /\ --s <= c /\ &1 < a /\ a <= &1001 / &1000 /\
     lclosed c s u v a (&33 / &20) (&47 / &20) /\
     lclosed c s u v a (&8 / &5) (&3) /\
     lclosed c s u v a (&87 / &50) (&3) /\
     ~linside c s u v a (&1) (&1543 / &500) /\
     ~linside c s u v a (&2) (&1543 / &500) /\
     ~scap_longsec c s u v a (&12 / &5)
     ==> v + a <= -- &2 * s + (&1543 / &500) * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    FSBNC_CENTER_ABOVE_RADIUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN FSBC_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lclosed; linside; lcy]) THEN
  SUBGOAL_THEN `c + s * (&1543 / &500) <= u \/
                v + a <= --s + c * (&1543 / &500)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT; GSYM DE_MORGAN_THM] THEN STRIP_TAC THEN
    FSBC_MISS_TAC [`c * &1`; `&1543 / &500`]; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= &2 * c + s * (&1543 / &500) \/
                v + a <= -- &2 * s + c * (&1543 / &500)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT; GSYM DE_MORGAN_THM] THEN STRIP_TAC THEN
    FSBC_MISS_TAC [`c * &2`; `&1543 / &500`]; ALL_TAC] THEN
  SUBGOAL_THEN `~(v + a <= --s + c * (&1543 / &500))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `-- &300 * s <= &43 * c` ASSUME_TAC THENL [FSBC_ARITH_TAC; ALL_TAC] THEN
    NLIN_FACTS_TAC [SQ_NONNEG `s:real`]
     [`&0 <= (&43 * c + &300 * s) * (&43 * c - &300 * s)`;
      `&47 / &50 <= c`; `--c * s <= &43 / &300`;
      `s * (u + a) <= s * (c * &87 / &50 + s * &3)`;
      `c * (v + a) <= c * (--s + c * (&1543 / &500))`;
      `&0 <= (a - &1) * (c + s)`] THEN
    NLIN_TAC [];
    ALL_TAC] THEN
  SUBGOAL_THEN `c + s * (&1543 / &500) <= u` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
    lhand(lhand(concl th)) = `u + a:real`)) THEN
  FSBC_ARITH_TAC);;

(* Lean: exclude *)
let FSBNC_EXCLUDE = prove
 (`forall cB sB uB vB aB cL sL uL vL aL.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     &0 < cB /\ sB <= &0 /\ --sB <= cB /\
     &0 < cL /\ abs sL <= cL /\
     &1 < aB /\ aB <= &1001 / &1000 /\ &1 < aL /\
     lcont cL sL uL vL aL /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     lclosed cB sB uB vB aB (&8 / &5) (&3) /\
     lclosed cB sB uB vB aB (&87 / &50) (&3) /\
     lclosed cL sL uL vL aL (&457 / &500) (&2) /\
     lclosed cL sL uL vL aL (&1) (&12 / &5) /\
     ~linside cB sB uB vB aB (&1) (&1543 / &500) /\
     ~linside cB sB uB vB aB (&2) (&1543 / &500) /\
     ~linside cB sB uB vB aB (&1) (&12 / &5) /\
     ~linside cB sB uB vB aB (&2) (&5 / &2) /\
     ~linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
     ~linside cL sL uL vL aL (&33 / &20) (&33 / &20) /\
     ldisj cB sB uB vB aB cL sL uL vL aL /\
     ~scap_longsec cB sB uB vB aB (&12 / &5)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    FSBNC_UPPER_CORNER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    FSBN_FORCED_FACES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    FSBN_RIGHT_POINTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `ldisj cB sB uB vB aB cL sL uL vL aL` THEN
  REWRITE_TAC[ldisj] THEN DISCH_TAC THEN
  SUBGOAL_THEN `--sL * (&19 / &25) + cL * (&187 / &100) <= vL` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `cL * (&19 / &25) + sL * (&187 / &100) <= uL` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      UNDISCH_TAC `~linside cL sL uL vL aL (&19 / &25) (&187 / &100)` THEN
      REWRITE_TAC[linside] THEN
      UNDISCH_TAC `lclosed cL sL uL vL aL (&457 / &500) (&2)` THEN
      UNDISCH_TAC `lclosed cL sL uL vL aL (&1) (&12 / &5)` THEN
      REWRITE_TAC[lclosed] THEN
      UNDISCH_TAC `abs sL <= cL` THEN UNDISCH_TAC `&0 < cL` THEN
      UNDISCH_TAC `uL < cL * (&19 / &25) + sL * (&187 / &100)` THEN
      UNDISCH_TAC `vL < --sL * (&19 / &25) + cL * (&187 / &100)` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&13 / &10`; `&12 / &5`]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FSBL_LEFT_POINT_OF_LOWER_U THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`]
    FSBN_LEFT_COVER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`&13 / &10`; `&12 / &5`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`&1`; `&67 / &25`])] THEN
  ASM_REWRITE_TAC[]);;
