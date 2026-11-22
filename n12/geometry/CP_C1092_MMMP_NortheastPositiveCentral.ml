(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/NortheastPositiveCentral.lean        *)
(* (namespace N12Compact.C1092MMMPNortheastPositiveCentral).                 *)
(* Faces: c1092mnnf_faces; MMMMPairAxes.alternatives: C1092MPA_ALTERNATIVES; *)
(* NortheastSignScalars: C1092MNSS_*; lower_pn / lower_np: C1092WS_*.        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_NortheastNegativeFaces.ml";;
needs "n12/geometry/CP_C1092_MMMP_NortheastSignScalars.ml";;
needs "n12/geometry/CP_C1092_MMMMPairAxes.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;

let C1092MNPC_LIN_TAC (asl,w as g) =
  let rec ok t = is_real_rel t || (is_neg t && is_real_rel (rand t)) ||
                 (is_conj t && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

let C1092MNPC_MISS_TAC x y =
  UNDISCH_TAC (mk_neg(list_mk_comb(`linside cC sC uC vC aC`,[x;y]))) THEN
  REWRITE_TAC[linside; DE_MORGAN_THM; REAL_NOT_LT] THEN C1092MNPC_LIN_TAC;;

let C1092MNPC_FACT_TAC t x y =
  SUBGOAL_THEN t ASSUME_TAC THENL [C1092MNPC_MISS_TAC x y; ALL_TAC];;

let C1092MNPC_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     REPEAT CONJ_TAC THEN C1092MNPC_LIN_TAC; ALL_TAC]) tms;;

(* Lean: impossible *)
let C1092MNPC_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aC /\ aC = aB /\ c977cc_normal cC sC /\ c977cc_normal cB (--sB) /\
     linside cC sC uC vC aC (&0) (&0) /\
     linside cC sC uC vC aC (--(&1 / &2)) (&0) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     ~linside cC sC uC vC aC (&7 / &20) (--(&7 / &20)) /\
     ~linside cC sC uC vC aC (--(&7 / &20)) (&7 / &20) /\
     ~linside cC sC uC vC aC (--(&39 / &100)) (--(&1)) /\
     linside cB sB uB vB aB (--(&7 / &20)) (&7 / &20) /\
     linside cB sB uB vB aB (--(&1)) (&2 / &5) /\
     c1092mnnf_faces cB sB uB vB aB /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cB:real`; `--sB:real`] C1092MNSS_LONGITUDINAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cC sC`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cC sC`)) THEN
  SUBGOAL_THEN `vC + aC <= (&7 / &20) * (cC + sC) /\
                uC + aC <= (&7 / &20) * (cC - sC) /\
                (&37 / &50) * cC + (&13 / &20) * sC < &1 /\
                aC + (&39 / &100) * sC - cC <= vC + aC` STRIP_ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
      not(is_neg(concl th)) &&
      can (find_term (fun t -> t = `cB:real` || t = `sB:real`)) (concl th)))) THEN
    RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th) THEN
    C1092MNPC_FACT_TAC `vC + aC <= (&7 / &20) * (cC + sC)` `--(&7 / &20)` `&7 / &20` THEN
    SUBGOAL_THEN `uC + aC <= (&7 / &20) * (cC - sC)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092MNPC_MISS_TAC `&7 / &20` `--(&7 / &20)`; ALL_TAC] THEN
    NLIN_FACTS_TAC [SQ_NONNEG `(&13 / &20) * cC - (&37 / &50) * sC`;
                    SQ_NONNEG `(&37 / &50) * cC + (&13 / &20) * sC - &1`]
     [`(&37 / &50) * cC + (&13 / &20) * sC < &1`] THEN
    SUBGOAL_THEN `aC + (&39 / &100) * sC - cC <= vC + aC` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN `uC < --(&39 / &100) * cC - sC` ASSUME_TAC THENL
       [C1092MNPC_LIN_TAC; ALL_TAC] THEN
      C1092MNPC_MISS_TAC `--(&39 / &100)` `--(&1)`; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cB (--sB)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mnnf_faces] o
    check (fun th -> can (term_match [] `c1092mnnf_faces c s u v a`) (concl th))) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cB:real`; `--sB:real`] C1092MNSS_TRANSVERSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `&0`; `&0`; `--sB:real`; `cB:real`] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)))) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`]
    C1092MPA_ALTERNATIVES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN C1092MNPC_LIN_TAC; ALL_TAC] THEN
  C1092MNPC_PROD_TAC [`&0 <= (cB - --sB) * cC`; `&0 <= --sB * (cC - sC)`;
                      `&0 <= cB * sC`; `&0 < --sB * cC`] THEN
  SUBGOAL_THEN `&0 <= cB * cC + sB * sC /\ &0 < cB * sC - sB * cC` STRIP_ASSUME_TAC THENL
   [C1092MNPC_LIN_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `cB:real`; `sB:real`; `cB * cC + sB * sC`; `sB * cC - cB * sC`]
      C1092WS_LOWER_PN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MNPC_LIN_TAC; DISCH_TAC] THEN
    C1092MNPC_PROD_TAC
     [`&0 <= (cB * cC + sB * sC) * ((&7 / &20) * (cC - sC) - (uC + aC))`;
      `&0 <= (cB * sC - sB * cC) * ((vC + aC) - (aC + (&39 / &100) * sC - cC))`;
      `&0 < (aC - &1) * (&1 + (cB * cC + sB * sC) + (cB * sC - sB * cC))`] THEN
    SUBGOAL_THEN
     `cB + --sB + (cB * cC + sB * sC) * (&7 / &20) * (cC - sC) +
      (cB * sC - sB * cC) * (cC - (&39 / &100) * sC) -
      (cB * cC + sB * sC) - (cB * sC - sB * cC) =
      cB * (&27 / &20 - cC - sC + (&13 / &20) * cC * sC - (&37 / &50) * sC pow 2) +
      --sB * (&2 + sC - cC - (&37 / &50) * cC * sC - (&13 / &20) * sC pow 2)`
      ASSUME_TAC THENL
     [UNDISCH_TAC `cC pow 2 + sC pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092MNPC_LIN_TAC;
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`;
                  `--sC:real`; `cC:real`; `sB * cC - cB * sC`; `cB * cC + sB * sC`]
      C1092WS_LOWER_NP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MNPC_LIN_TAC; DISCH_TAC] THEN
    C1092MNPC_PROD_TAC
     [`&0 <= (cB * sC - sB * cC) * (uB - (--cB + sB))`;
      `&0 <= (cB * cC + sB * sC) * ((cB + (&39 / &100) * sB) - (vB + aC))`;
      `&0 < (aC - &1) * ((cB * sC - sB * cC) + (cB * cC + sB * sC))`] THEN
    SUBGOAL_THEN
     `(cB * sC - sB * cC) * (cB + --sB - &1) +
      (cB * cC + sB * sC) * (cB - (&39 / &100) * --sB - &1) =
      --cC * (cB + --sB - &1 - (&61 / &100) * cB * --sB) +
      sC * (&1 - cB + --sB - (&61 / &100) * --sB pow 2)` ASSUME_TAC THENL
     [UNDISCH_TAC `cB pow 2 + --sB pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092MNPC_LIN_TAC;
    C1092MNPC_LIN_TAC]);;
