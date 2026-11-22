(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/NearCrossingSupport.lean            *)
(* (N12Compact.C1092MMMPNearCrossingSupport).  The two genuine support       *)
(* sources after a hypothetical missing crossing.  Normal: c977cc_normal;    *)
(* NearCrossingScalars: C1092NCS_*; CenterCrosspointSupport.negative_axes:   *)
(* C1092CCSP_NEGATIVE_AXES; the wall bound x <= 2 enters through the corner  *)
(* lemma C1092CCSP_CORNER (in place of PhysicalWallSupport.own_lt/lower_le); *)
(* exists_positive_frame: LSEC_POSITIVE_FRAME_RADIUS; penalty:               *)
(* C1092SWP_PENALTY.                                                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_NearCrossingScalars.ml";;
needs "n12/geometry/CP_C1092_MMMP_CenterCrosspointSupport.ml";;

let C1092NCSP_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092NCSP_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092NCSP_LIN_TAC; DISCH_TAC];;

let C1092NCSP_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092NCSP_LIN_TAC; DISCH_TAC];;

(* Lean: fixed (private) *)
let C1092NCSP_FIXED = prove
 (`forall cC sC uC vC aC cW sW uW vW aW c s z h b rho.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     cC = c /\ sC = --s /\ cW = h /\ sW = --b /\
     c977cc_normal c s /\ &0 < s /\ s <= &1 / &4 /\
     &0 <= h /\ &0 <= b /\ &1 < aC /\ aC = aW /\
     &0 <= z /\ z <= &1 / &2 /\ z * (&1 + c) = s /\ s * z = &1 - c /\
     --z <= uC /\ &0 <= vC /\
     linside cC sC uC vC aC (&13 / &50) (&0) /\ &13 / &50 < rho /\
     linside cC sC uC vC aC (&1) rho /\
     linside cW sW uW vW aW (&543 / &500) (&0) /\
     linside cW sW uW vW aW (&1) (&13 / &50) /\
     (forall x y. linside cW sW uW vW aW x y ==> x <= &2) /\
     &0 <= lcy cW sW uW vW aW /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    let t = concl th in is_eq t && is_var(lhand t) &&
      mem (fst(dest_var(lhand t))) ["cC"; "sC"; "cW"; "sW"]))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths)) THEN
  MP_TAC(SPECL [`c:real`; `--s`; `uC:real`; `vC:real`; `aC:real`;
                `h:real`; `--b`; `uW:real`; `vW:real`; `aC:real`; `rho:real`]
    C1092CCSP_NEGATIVE_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN C1092NCSP_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`h:real`; `--b`; `uW:real`; `vW:real`; `aC:real`] C1092CCSP_CORNER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092NCSP_LIN_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`h:real`; `--b`; `uW:real`; `vW:real`; `aC:real`] LCENTRE_COORDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`h:real`; `--b`; `uW:real`; `vW:real`; `aC:real`] LCENTRE_COORDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--s`; `uC:real`; `vC:real`; `aC:real`; `h:real`; `--b`]
    C1092WS_FORMULAS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`h:real`; `--b`; `uW:real`; `vW:real`; `aC:real`; `c:real`; `--s`]
    C1092WS_FORMULAS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `b:real`] C1092SWP_PENALTY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `h * h + --b * --b = &1` THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `h * h + b * b = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `h * h + --b * --b = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c * h + s * b` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < h + b` ASSUME_TAC THENL
     [UNDISCH_TAC `h * h + b * b = &1` THEN UNDISCH_TAC `&0 <= h` THEN UNDISCH_TAC `&0 <= b` THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT DISCH_TAC THEN NLIN_TAC []; ALL_TAC] THEN
    C1092NCSP_LT_MUL_TAC `s:real` `h + b` THEN
    C1092NCSP_LE_MUL_TAC `c - s` `h:real` THEN C1092NCSP_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(c * b - s * h) = abs(s * h - c * b)` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
  THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  (* ownWall *)
  C1092NCSP_LE_MUL_TAC `b:real` `lcy h (--b) uW vW aC` THEN
  C1092NCSP_LE_MUL_TAC `h:real` `b:real` THEN
  SUBGOAL_THEN `&0 <= h pow 2 /\ &0 <= c pow 2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE]; ALL_TAC] THEN
  C1092NCSP_LT_MUL_TAC `aC - &1` `&1 + h pow 2 + h * b` THEN
  SUBGOAL_THEN `h * (uW + aC) + b * (vW + aC) = lcx h (--b) uW vW aC + aC * (h + b) / &2`
    ASSUME_TAC THENL [REWRITE_TAC[lcx] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  C1092NCSP_LE_MUL_TAC `h:real` `&2 - aC * (h + b) / &2 - lcx h (--b) uW vW aC` THEN
  (* wallNormal *)
  C1092NCSP_LE_MUL_TAC `c:real` `&2 - aC * (h + b) / &2 - lcx h (--b) uW vW aC` THEN
  C1092NCSP_LE_MUL_TAC `s:real` `lcy h (--b) uW vW aC` THEN
  C1092NCSP_LE_MUL_TAC `c:real` `s:real` THEN
  C1092NCSP_LT_MUL_TAC `aC - &1`
    `c * (h + b) + (c * h + s * b) + abs(s * h - c * b)` THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `z:real`] C1092NCS_ENDPOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `ABT_lower h (--b) uW vW aC c (--s) < &1 - z` ASSUME_TAC THENL
   [REWRITE_TAC[ABT_lower; tss_support_radius] THEN
    SUBGOAL_THEN `abs(c * h + --s * --b) = c * h + s * b /\
                  abs(--c * --b + --s * h) = abs(s * h - c * b)`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
    C1092NCSP_LIN_TAC;
    ALL_TAC] THEN
  DISCH_THEN DISJ_CASES_TAC THENL [C1092NCSP_LIN_TAC; ALL_TAC] THEN
  (* foreign *)
  ASM_CASES_TAC `&0 <= s * h - c * b` THENL
   [SUBGOAL_THEN `max (h * c + --b * --s) (&0) = h * c + --b * --s /\
                  max (--h * --s + --b * c) (&0) = --h * --s + --b * c`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[real_max] THEN CONJ_TAC THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `z:real`; `h:real`; `b:real`] C1092NCS_FIRST) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; DISCH_TAC] THEN
    C1092NCSP_LT_MUL_TAC `c * h + s * b` `(uC + aC) - (&1 - z)` THEN
    C1092NCSP_LE_MUL_TAC `s * h - c * b` `(vC + aC) - &1` THEN
    SUBGOAL_THEN `(c * h + s * b) * (&1 - z) + (s * h - c * b) = h * (c + z) + b * (s - &1)`
      ASSUME_TAC THENL
     [UNDISCH_TAC `z * (&1 + c) = s` THEN UNDISCH_TAC `s * z = &1 - c` THEN
      CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092NCSP_LIN_TAC;
    SUBGOAL_THEN `max (h * c + --b * --s) (&0) = h * c + --b * --s /\
                  max (--h * --s + --b * c) (&0) = &0`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[real_max] THEN CONJ_TAC THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `z:real`; `h:real`; `b:real`] C1092NCS_SECOND) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_POW_2] THEN
      UNDISCH_TAC `~(&0 <= s * h - c * b)` THEN REAL_ARITH_TAC;
      DISCH_TAC] THEN
    SUBGOAL_THEN `vC < (&13 / &50) * s` ASSUME_TAC THENL
     [UNDISCH_TAC `linside c (--s) uC vC aC (&13 / &50) (&0)` THEN
      REWRITE_TAC[linside] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    C1092NCSP_LT_MUL_TAC `c * h + s * b` `(uC + aC) - (&1 - z)` THEN
    C1092NCSP_LE_MUL_TAC `--(s * h - c * b)` `(&13 / &50) * s - vC` THEN
    C1092NCSP_LIN_TAC]);;

(* Lean: impossible *)
let C1092NCSP_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cW sW uW vW aW c s z rho.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     cC = c /\ sC = --s /\ c977cc_normal c s /\ &0 < s /\ s <= &1 / &4 /\
     &1 < aC /\ aC = aW /\
     &0 <= z /\ z <= &1 / &2 /\ z * (&1 + c) = s /\ s * z = &1 - c /\
     --z <= uC /\ &0 <= vC /\
     linside cC sC uC vC aC (&13 / &50) (&0) /\ &13 / &50 < rho /\
     linside cC sC uC vC aC (&1) rho /\
     linside cW sW uW vW aW (&543 / &500) (&0) /\
     linside cW sW uW vW aW (&1) (&13 / &50) /\
     (forall x y. linside cW sW uW vW aW x y ==> x <= &2) /\
     &0 <= lcy cW sW uW vW aW /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    let t = concl th in is_eq t && is_var(lhand t) &&
      mem (fst(dest_var(lhand t))) ["cC"; "sC"]))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`]
    LSEC_POSITIVE_FRAME_RADIUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`p:real`; `q:real`; `u0:real`; `v0:real`; `a0:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a0:real = aC`)) THEN
  MP_TAC(SPECL [`c:real`; `--s`; `uC:real`; `vC:real`; `aC:real`;
                `q:real`; `--p`; `--v0 - aC`; `u0:real`; `aC:real`;
                `c:real`; `s:real`; `z:real`; `q:real`; `p:real`; `rho:real`]
    C1092NCSP_FIXED) THEN
  SUBGOAL_THEN `forall x y. linside q (--p) (--v0 - aC) u0 aC x y <=> linside cW sW uW vW aC x y`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `p:real`)) (concl th) then REWRITE_TAC[GSYM th] else failwith "no") THEN
    REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lcy q (--p) (--v0 - aC) u0 aC = lcy cW sW uW vW aC` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can (find_term ((=) `lcy`)) (concl th) &&
      can (find_term ((=) `p:real`)) (concl th) then REWRITE_TAC[GSYM th] else failwith "no") THEN
    REWRITE_TAC[lcy] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ldisj] THEN RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(UNDISCH_TAC `p * p + q * q = &1` THEN REAL_ARITH_TAC) THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[]]);;
