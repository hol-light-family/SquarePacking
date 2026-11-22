(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/CenterCrosspoint.lean               *)
(* (N12Compact.C1092MMMPCenterCrosspoint).  A center-to-crosspoint theorem   *)
(* for two original physical squares.  Normal: c977cc_normal;                *)
(* CenterCrosspointSupport.impossible: C1092CCSP_IMPOSSIBLE;                 *)
(* ClosedFrames.canonical_frame: CLF_CANONICAL_FRAME; centerY: lcy.          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_CenterCrosspointSupport.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let C1092MCC_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092MCC_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MCC_LIN_TAC; DISCH_TAC];;

let C1092MCC_NORMAL_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths));;

let C1092MCC_EXPAND_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> not(is_neg(concl th)) &&
     can (find_term ((=) `linside`)) (concl th) &&
     not(is_forall(concl th))))) THEN
  REWRITE_TAC[linside] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC);;

let C1092MCC_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C1092MCC_LIN_TAC;;

(* Lean: nonnegative_point *)
let C1092MCC_NONNEGATIVE_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ c977cc_normal c s /\ &1 < a /\
     linside c s u v a (&0) (&0) /\
     linside c s u v a (&7 / &20) (&7 / &20) /\
     linside c s u v a (&0) (&13 / &50) /\
     ~linside c s u v a (&7 / &20) (--(&7 / &20))
     ==> linside c s u v a (&0) (&1 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MCC_NORMAL_TAC THEN
  C1092MCC_EXPAND_TAC THEN
  SUBGOAL_THEN `--(&7 / &20) * (c + s) <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MCC_MISS_TAC `~linside c s u v a (&7 / &20) (--(&7 / &20))`; ALL_TAC] THEN
  SUBGOAL_THEN `(&17 / &20) * c + (&7 / &20) * s < &1` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `(&7 / &20) * c - (&17 / &20) * s`;
              SQ_NONNEG `(&17 / &20) * c + (&7 / &20) * s - &1`]; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C1092MCC_LIN_TAC);;

(* Lean: negative (private) *)
let C1092MCC_NEGATIVE = prove
 (`forall cC sC uC vC aC cW sW uW vW aW c s.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     cC = c /\ sC = --s /\ c977cc_normal c s /\ &1 < aC /\ aC = aW /\
     linside cC sC uC vC aC (&0) (&0) /\
     linside cC sC uC vC aC (&7 / &20) (&7 / &20) /\
     linside cC sC uC vC aC (&0) (&13 / &50) /\
     linside cC sC uC vC aC (&13 / &50) (&0) /\
     ~linside cC sC uC vC aC (--(&7 / &20)) (&7 / &20) /\
     ~linside cC sC uC vC aC (&7 / &20) (--(&7 / &20)) /\
     linside cW sW uW vW aW (&543 / &500) (&0) /\
     linside cW sW uW vW aW (&1) (&13 / &50) /\
     (forall y. &0 <= y ==> y <= &39 / &100 ==> linside cW sW uW vW aW (&1) y) /\
     (forall x y. linside cW sW uW vW aW x y ==> x <= &2) /\
     &0 <= lcy cW sW uW vW aW /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> linside cC sC uC vC aC (&0) (&1 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    let t = concl th in is_eq t && is_var(lhand t) &&
      mem (fst(dest_var(lhand t))) ["cC"; "sC"]))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  C1092MCC_NORMAL_TAC THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> let t = concl th in not(is_neg t) && not(is_forall t) &&
       can (find_term ((=) `linside`)) t && can (find_term ((=) `uC:real`)) t) ths)) THEN
  SUBGOAL_THEN `--(&7 / &20) * (c + s) <= uC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MCC_MISS_TAC `~linside c (--s) uC vC aC (--(&7 / &20)) (&7 / &20)`; ALL_TAC] THEN
  SUBGOAL_THEN `--(&7 / &20) * (c - s) <= vC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MCC_MISS_TAC `~linside c (--s) uC vC aC (&7 / &20) (--(&7 / &20))`; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `--s / &2 <= uC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MCC_MISS_TAC `~linside c (--s) uC vC aC (&0) (&1 / &2)`; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [C1092MCC_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + c` ASSUME_TAC THENL [C1092MCC_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(s / (&1 + c)) * (&1 + c) = s /\ &0 < s / (&1 + c)` MP_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `&0 < &1 + c` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SPEC_TAC(`s / (&1 + c)`,`z:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `s * z = &1 - c` ASSUME_TAC THENL
   [SUBGOAL_THEN `(s * z) * (&1 + c) = (&1 - c) * (&1 + c)` MP_TAC THENL
     [UNDISCH_TAC `z * (&1 + c) = s` THEN UNDISCH_TAC `c * c + --s * --s = &1` THEN
      CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[REAL_EQ_MUL_RCANCEL] THEN UNDISCH_TAC `&0 < &1 + c` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c < &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MCC_LE_MUL_TAC `c - &1` `c + &1` THEN
    MP_TAC(SPECL [`s:real`; `s:real`] REAL_LT_MUL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN C1092MCC_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `z < &1 / &2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MCC_LE_MUL_TAC `z - &1 / &2` `&1 + c` THEN C1092MCC_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + z * z) * c = &1 - z * z /\ (&1 + z * z) * s = &2 * z`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN UNDISCH_TAC `z * (&1 + c) = s` THEN UNDISCH_TAC `s * z = &1 - c` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  (* short *)
  SUBGOAL_THEN `z + (&17 / &20) * c - (&7 / &20) * s < &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= z * z` ASSUME_TAC THENL [REWRITE_TAC[REAL_LE_SQUARE]; ALL_TAC] THEN
    C1092MCC_LE_MUL_TAC `z * z` `&1 / &2 - z` THEN
    MP_TAC(SPEC `z - &1 / &9` REAL_LE_SQUARE) THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < &3 / &20 - (&3 / &10) * z + (&37 / &20) * z * z - z * z * z`
      ASSUME_TAC THENL [C1092MCC_LIN_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 + z * z) * (&1 - z - (&17 / &20) * c + (&7 / &20) * s) =
                  &3 / &20 - (&3 / &10) * z + (&37 / &20) * z * z - z * z * z`
      ASSUME_TAC THENL
     [UNDISCH_TAC `(&1 + z * z) * c = &1 - z * z` THEN
      UNDISCH_TAC `(&1 + z * z) * s = &2 * z` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MCC_LE_MUL_TAC `&1 + z * z` `--(&1 - z - (&17 / &20) * c + (&7 / &20) * s)` THEN
    C1092MCC_LIN_TAC; ALL_TAC] THEN
  (* owned *)
  SUBGOAL_THEN `linside c (--s) uC vC aC (&1) (&1 / &2 - z)` ASSUME_TAC THENL
   [REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C1092MCC_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `z < &11 / &100` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&1 / &2 - z` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `&39 / &100`)) (concl th))) THEN
    ANTS_TAC THENL [C1092MCC_LIN_TAC; ALL_TAC] THEN
    ANTS_TAC THENL [C1092MCC_LIN_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[ldisj]; ALL_TAC] THEN
  C1092MCC_LE_MUL_TAC `z:real` `&1 - c` THEN
  MP_TAC(SPECL [`c:real`; `--s`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`;
                `c:real`; `s:real`; `&1 / &2 - z`] C1092CCSP_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN C1092MCC_LIN_TAC);;

(* Lean: point *)
let C1092MCC_POINT = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     &1 < aC /\ aC = aW /\
     linside cC sC uC vC aC (&0) (&0) /\
     linside cC sC uC vC aC (&7 / &20) (&7 / &20) /\
     linside cC sC uC vC aC (&0) (&13 / &50) /\
     linside cC sC uC vC aC (&13 / &50) (&0) /\
     ~linside cC sC uC vC aC (--(&7 / &20)) (&7 / &20) /\
     ~linside cC sC uC vC aC (&7 / &20) (--(&7 / &20)) /\
     linside cW sW uW vW aW (&543 / &500) (&0) /\
     linside cW sW uW vW aW (&1) (&13 / &50) /\
     (forall y. &0 <= y ==> y <= &39 / &100 ==> linside cW sW uW vW aW (&1) y) /\
     (forall x y. linside cW sW uW vW aW x y ==> x <= &2) /\
     &0 <= lcy cW sW uW vW aW /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> linside cC sC uC vC aC (&0) (&1 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `u:real`
    (X_CHOOSE_THEN `v:real` (X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a:real = aC`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  ASM_CASES_TAC `&0 <= s` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `aC:real`]
      C1092MCC_NONNEGATIVE_POINT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN RASM_ARITH_TAC;
                    ASM_REWRITE_TAC[]];
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `aC:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`;
                  `c:real`; `--s`] C1092MCC_NEGATIVE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ldisj; REAL_NEG_NEG; c977cc_normal; REAL_POW_2] THEN
                    RASM_ARITH_TAC;
                    ASM_REWRITE_TAC[]]]);;
