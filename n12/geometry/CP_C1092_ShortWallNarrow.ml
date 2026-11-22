(* ========================================================================= *)
(* Port of Compact/Completion/C1092/ShortWallNarrow.lean                     *)
(* (N12Compact.C1092ShortWallNarrow).  The central-angle entrance for the    *)
(* short-wall theorem.  S12.Convex.inside_segment is replaced by direct      *)
(* linear arithmetic; S12.short_projections is FSAF_SHORT_PROJECTIONS.        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_ShortWallCrossing.ml";;
needs "n12/geometry/CP_C1092_ShortWallScalars.ml";;

let C1092SWN_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092SWN_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092SWN_LIN_TAC; DISCH_TAC];;

let C1092SWN_MISS_TAC pats =
  FIRST_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && is_conj(rand(concl th)) &&
    forall (fun p -> can (find_term ((=) p)) (concl th)) pats)) THEN
  REWRITE_TAC[TAUT `(~p ==> false) <=> p`] THEN REPEAT CONJ_TAC THEN C1092SWN_LIN_TAC;;

(* Lean: NarrowData (structure) *)
let C1092SWN_narrowData = new_definition
 `C1092SWN_narrowData (c:real) s u v a <=>
    &0 < s /\ &4 * s < c /\ &2 * (c + s) <= u /\
    --(&47 / &20) * s + (&33 / &20) * c <= v /\
    v + a <= &3 * c - (&1197 / &500) * s /\
    linside c s u v a (&5 / &2) (&3)`;;

(* Lean: of_missing *)
let C1092SWN_OF_MISSING = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ aA = aR /\ lcont cR sR uR vR aR /\
     c977cc_normal cA sA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&1197 / &500) (&3) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&1197 / &500) /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ~linside cA sA uA vA aA (&2) (&2)
     ==> C1092SWN_narrowData cA sA uA vA aA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  SUBGOAL_THEN `&0 < cA` ASSUME_TAC THENL [C1092SWN_LIN_TAC; ALL_TAC] THEN
  (* keep copies of the original memberships for later lemmas *)
  SUBGOAL_THEN `&2 * (cA + sA) <= uA` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside cA sA uA vA aA (&2) (&2)` THEN REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN REWRITE_TAC[linside] THEN
    REPEAT CONJ_TAC THEN C1092SWN_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `vA + aA <= &3 * cA - (&1197 / &500) * sA` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside cA sA uA vA aA (&1197 / &500) (&3)` THEN REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN REWRITE_TAC[linside] THEN
    REPEAT CONJ_TAC THEN C1092SWN_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sA` ASSUME_TAC THENL
   [UNDISCH_TAC `linside cA sA uA vA aA (&2) (&113 / &50)` THEN REWRITE_TAC[linside] THEN
    STRIP_TAC THEN C1092SWN_LIN_TAC;
    ALL_TAC] THEN
  (* sector *)
  SUBGOAL_THEN `sA < (&16 / &25) * cA` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`] C1092SWS_STEEP_SHORT_POINT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SWN_LIN_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `(&1293 / &1250) * cA + (&591 / &2500) * sA <= &1` ASSUME_TAC THENL
     [POP_ASSUM MP_TAC THEN SPEC_TAC(`(&1293 / &1250) * cA + (&591 / &2500) * sA`,`w:real`) THEN
      GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
      NLIN_TAC [SQ_NONNEG `w - &1`];
      ALL_TAC] THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`; `&1197 / &500 - &3793 / &1250`; `&3 - &5591 / &2500`]
      FSAF_SHORT_PROJECTIONS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      FIRST_ASSUM ACCEPT_TAC;
      STRIP_TAC] THEN
    UNDISCH_TAC `ldisj cA sA uA vA aA cR sR uR vR aR` THEN
    REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&3793 / &1250`; `&5591 / &2500`]) THEN
    REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN REWRITE_TAC[linside] THEN
    REPEAT CONJ_TAC THEN C1092SWN_LIN_TAC;
    ALL_TAC] THEN
  (* the half angle z *)
  SUBGOAL_THEN `exists z. &0 <= z /\ (&1 + cA) * z = sA /\ sA * z = &1 - cA /\ z < &197 / &500`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `sA / (&1 + cA)` THEN
    SUBGOAL_THEN `&0 < &1 + cA` ASSUME_TAC THENL [C1092SWN_LIN_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THEN C1092SWN_LIN_TAC;
      MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN UNDISCH_TAC `&0 < &1 + cA` THEN
      CONV_TAC REAL_FIELD;
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN C1092SWN_LIN_TAC];
    ALL_TAC] THEN
  (* narrow *)
  SUBGOAL_THEN `&4 * sA < cA` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`] C1092SWS_MODERATE_SHORT_POINT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C1092SWN_LE_MUL_TAC `z:real` `(&197 / &500) * cA + sA - &303 / &500` THEN
    C1092SWN_LE_MUL_TAC `sA:real` `z:real` THEN
    C1092SWN_LE_MUL_TAC `cA:real` `z:real` THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                  `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`; `z:real`]
      C1092SWC_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN REWRITE_TAC[linside] THEN
    REPEAT CONJ_TAC THEN C1092SWN_LIN_TAC;
    ALL_TAC] THEN
  (* the high point *)
  SUBGOAL_THEN `linside cA sA uA vA aA (&5 / &2) (&3)` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `z:real`]
      CWE_CROSSING_POINT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SWN_LIN_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                  `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`; `z:real`]
      C1092SWC_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    CWPA_CENTRAL_LOWER_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SWN_LIN_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[C1092SWN_narrowData]);;
