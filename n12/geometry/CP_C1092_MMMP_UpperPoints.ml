(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/UpperPoints.lean                    *)
(* (N12Compact.C1092MMMPUpperPoints).  The strict northwest point needed by  *)
(* the genuine left-wall transfer; both canonical signs are covered.         *)
(* Conventions of CP_C1092_MMMP_NortheastEarlyActual.ml / CP_C1092_MMMP_     *)
(* InwardTips.ml (forward toolkit c1092mo_).  (owners p 7).translated 2 2 is *)
(* the tuple of C1092MUP_INSIDE_TRANSLATED; canonical_frame is               *)
(* CLF_CANONICAL_FRAME; short_projections WFP_SHORT_PROJECTIONS; Normal is   *)
(* c977cc_normal (normal_bounds C977CC_NORMAL_BOUNDS).  Tag C1092MUP_.       *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_NortheastEarlyActual.ml";;
needs "n12/geometry/CP_C1092_MMMP_InwardTips.ml";;

let C1092MUP_CAP_TAC =
  SUBGOAL_THEN `u + a <= &7 / &50 * c + s / &2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];
    ALL_TAC];;

(* Lean: positive (private) *)
let C1092MUP_POSITIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ c977cc_normal c s /\ &1 < a /\
     linside c s u v a (&0) (&0) /\ linside c s u v a (--(&1 / &2)) (&1 / &2) /\
     linside c s u v a (&0) (&1 / &2) /\ linside c s u v a (--(&61 / &100)) (&61 / &100) /\
     ~linside c s u v a (&7 / &50) (&1 / &2)
     ==> linside c s u v a (--(&81 / &100)) (&1 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&19 / &20`; `&3 / &10`] WFP_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside; c977cc_normal]) THEN
  C1092MUP_CAP_TAC THEN REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

(* Lean: negative (private) *)
let C1092MUP_NEGATIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ c977cc_normal c (--s) /\ &1 < a /\
     --s < &7 / &50 /\ &99 / &100 < c /\
     linside c s u v a (&0) (&0) /\ linside c s u v a (--(&1 / &2)) (&0) /\
     linside c s u v a (--(&1 / &100)) (&27 / &50) /\ linside c s u v a (--(&61 / &100)) (&61 / &100) /\
     ~linside c s u v a (&7 / &50) (&1 / &2)
     ==> linside c s u v a (--(&81 / &100)) (&1 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside; c977cc_normal]) THEN
  C1092MUP_CAP_TAC THEN REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

(* S12 inside_translated_iff at (2, 2) *)
let C1092MUP_INSIDE_TRANSLATED = prove
 (`forall c s u v a x y.
     linside c s (u - (c * &2 + s * &2)) (v - (--s * &2 + c * &2)) a x y <=>
     linside c s u v a (&2 + x) (&2 + y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: northwest_point *)
let C1092MUP_NORTHWEST_POINT = prove
 (c1092mmpe_stmt 7 "&119 / &100" "&11 / &5",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092NEEA_UPPER_POINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092MIT_SECOND_TIP) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL C1092MMPE_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  let o7 = c1092ae_own C1092AE_P 7 in
  let [c; s; u; v; a] = fst (chop_list 5 (snd (strip_comb (parse_term (c1092mmpe_in 7 "x" "y"))))) in
  let tq = [c; s; mk_binop `(-):real->real->real` u (parse_term (Printf.sprintf "%s * &2 + %s * &2" (string_of_term c) (string_of_term s)));
            mk_binop `(-):real->real->real` v (parse_term (Printf.sprintf "--%s * &2 + %s * &2" (string_of_term s) (string_of_term c))); a] in
  ignore o7;
  MP_TAC(SPECL tq CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OO_UNIT; REAL_ARITH `&1 < l ==> &0 < l`];
    ALL_TAC] THEN
  REWRITE_TAC[C1092MUP_INSIDE_TRANSLATED; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "linside cC sC uC vC aC (--(&81 / &100)) (&1 / &5)")) MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[]] THEN
  ASM_CASES_TAC `&0 <= sC` THENL
   [MATCH_MP_TAC C1092MUP_POSITIVE;
    MP_TAC(SPECL (C1092MMPE_V @ [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`])
      C1092NEEA_SMALL_NORTHWEST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
      UNDISCH_TAC `abs sC <= cC` THEN UNDISCH_TAC `~(&0 <= sC)` THEN REAL_ARITH_TAC;
      STRIP_TAC] THEN
    MATCH_MP_TAC C1092MUP_NEGATIVE] THEN
  ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  CONV_TAC C1092MO_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
  ASM_REWRITE_TAC[c1092mo_use C1092MPC_NORTHWEST_CENTER; c1092mo_use C1092MPC_NORTHWEST_DIAGONAL;
    c1092mo_use C1092MPC_NORTHWEST_NORTH; c1092mo_use C1092MPC_NORTHWEST_LONG_DIAGONAL;
    c1092mo_use C1092MO_NORTHWEST_LEFT;
    c1092mo_excl 7 6 (ASSUME (c1092mo_in 6 `&107 / &50` `&5 / &2`))] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;
