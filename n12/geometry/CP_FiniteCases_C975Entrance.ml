(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C975Entrance.lean.                *)
(* Original C975 compulsory points.  Lean  auxiliaries p mask  is            *)
(* ooaux c1 c2 a b l mask;  natAuxOwners p k (ownerIndex p mask)  is         *)
(*   auxown k (c1 (oidx c1 c2 a b l mask)) (c2 ..) (a ..) (b ..) l.          *)
(* The structure Compulsory is the predicate c975e_compulsory.  The local    *)
(* foreign (auxiliary_disjoint) is applied inside OO_EXCLUDE_ALL_TAC; the    *)
(* C975FiniteCuts cuts are re-evaluated by OO_DOMAIN_CASES_TAC on the        *)
(* C975Domains domains (same allowed lists), except top (C975FC_TOP on the   *)
(* half domain C975D_TOPG).  Tag C975E_.                                     *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C975FiniteCuts.ml";;

(* Lean: Compulsory (structure) *)
let c975e_compulsory = new_definition
 `c975e_compulsory (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) <=>
    (2 IN ooaux c1 c2 a b l 1 /\ 12 IN ooaux c1 c2 a b l 1) /\
    (0 IN ooaux c1 c2 a b l 2 /\ 10 IN ooaux c1 c2 a b l 2) /\
    (6 IN ooaux c1 c2 a b l 8192 /\ 15 IN ooaux c1 c2 a b l 8192) /\
    (4 IN ooaux c1 c2 a b l 256 /\ 13 IN ooaux c1 c2 a b l 256) /\
    (1 IN ooaux c1 c2 a b l 4096 /\ 11 IN ooaux c1 c2 a b l 4096) /\
    (8 IN ooaux c1 c2 a b l 512 /\
     (16 IN ooaux c1 c2 a b l 512 \/ 18 IN ooaux c1 c2 a b l 512)) /\
    (9 IN ooaux c1 c2 a b l 16384 /\ 19 IN ooaux c1 c2 a b l 16384) /\
    14 IN ooaux c1 c2 a b l 34816 /\
    ((5 IN ooaux c1 c2 a b l 1024 \/ 7 IN ooaux c1 c2 a b l 1024) /\
     (16 IN ooaux c1 c2 a b l 1024 \/ 17 IN ooaux c1 c2 a b l 1024))`;;

(* Lean: g_combined (private) *)
let C975E_G_COMBINED = prove
 (`forall c1 c2 a b l mask j.
     j IN auxown 1 (c1 (oidx c1 c2 a b l mask)) (c2 (oidx c1 c2 a b l mask))
                   (a (oidx c1 c2 a b l mask)) (b (oidx c1 c2 a b l mask)) l <=>
     j + 10 IN ooaux c1 c2 a b l mask`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ooaux; AUXOWN2; IN_UNION; IN_IMAGE] THEN
  MATCH_MP_TAC(TAUT `~p /\ (q <=> r) ==> (q <=> p \/ r)`) THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC (SPECL [`0`; `c1 (oidx c1 c2 a b l mask):real`; `c2 (oidx c1 c2 a b l mask):real`;
                   `a (oidx c1 c2 a b l mask):real`; `b (oidx c1 c2 a b l mask):real`; `l:real`]
                  AUXOWN_SUBSET10) THEN
    REWRITE_TAC[ARITH_RULE `0 < 2`; SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `j + 10`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `j + 10 = x + 10 <=> x = j`] THEN MESON_TAC[]]);;

(* the F half at a low index is the ooaux membership *)
let C975E_F_COMBINED = prove
 (`forall c1 c2 a b l mask j. j < 10 ==>
     (j IN auxown 0 (c1 (oidx c1 c2 a b l mask)) (c2 (oidx c1 c2 a b l mask))
                    (a (oidx c1 c2 a b l mask)) (b (oidx c1 c2 a b l mask)) l <=>
      j IN ooaux c1 c2 a b l mask)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ooaux; AUXOWN2; IN_UNION; IN_IMAGE] THEN
  MATCH_MP_TAC(TAUT `~q ==> (p <=> p \/ q)`) THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
  GEN_TAC THEN MATCH_MP_TAC(TAUT `~a ==> ~(a /\ b)`) THEN ASM_ARITH_TAC);;

let C975E_DOMS = [1, C975D_SOUTHWEST; 2, C975D_LEFT_SINGLETON; 8192, C975D_BOTTOM;
                  256, C975D_SOUTHWEST_CENTRAL; 4096, C975D_LEFT; 512, C975D_SOUTHEAST;
                  16384, C975D_RIGHT; 1024, C975D_NORTHEAST];;

(* Lean: compulsory *)
let C975E_COMPULSORY = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c975d_family
     ==> c975e_compulsory c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(2 IN ooaux c1 c2 a b l 1 /\ 12 IN ooaux c1 c2 a b l 1) /\
                (0 IN ooaux c1 c2 a b l 2 /\ 10 IN ooaux c1 c2 a b l 2) /\
                (6 IN ooaux c1 c2 a b l 8192 /\ 15 IN ooaux c1 c2 a b l 8192) /\
                (4 IN ooaux c1 c2 a b l 256 /\ 13 IN ooaux c1 c2 a b l 256) /\
                (1 IN ooaux c1 c2 a b l 4096 /\ 11 IN ooaux c1 c2 a b l 4096)`
    STRIP_ASSUME_TAC THENL
   [OO_CHAIN_TAC C975D_F C975E_DOMS
      [1, [2; 12]; 2, [0; 10]; 8192, [6; 15]; 256, [4; 13]; 4096, [1; 11]];
    ALL_TAC] THEN
  SUBGOAL_THEN `8 IN ooaux c1 c2 a b l 512 /\
                (16 IN ooaux c1 c2 a b l 512 \/ 18 IN ooaux c1 c2 a b l 512)`
    (CONJUNCTS_THEN ASSUME_TAC) THENL
   [OO_EXCLUDE_ALL_TAC C975D_F 512 THEN OO_DOMAIN_CASES_TAC C975D_SOUTHEAST; ALL_TAC] THEN
  SUBGOAL_THEN `9 IN ooaux c1 c2 a b l 16384 /\ 19 IN ooaux c1 c2 a b l 16384`
    STRIP_ASSUME_TAC THENL
   [OO_CHAIN_TAC C975D_F C975E_DOMS [16384, [9; 19]]; ALL_TAC] THEN
  SUBGOAL_THEN `14 IN ooaux c1 c2 a b l 34816` ASSUME_TAC THENL
   [OO_EXCLUDE_ALL_TAC C975D_F 34816 THEN
    REWRITE_TAC[ARITH_RULE `14 = 4 + 10`; GSYM C975E_G_COMBINED] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] C975FC_TOP) THEN
    REWRITE_TAC[C975E_G_COMBINED] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HDOM_OWNER THEN EXISTS_TAC C975D_F THEN
    ASM_REWRITE_TAC[C975D_TOPG; in_fam 34816 C975D_F];
    ALL_TAC] THEN
  SUBGOAL_THEN `(5 IN ooaux c1 c2 a b l 1024 \/ 7 IN ooaux c1 c2 a b l 1024) /\
                (16 IN ooaux c1 c2 a b l 1024 \/ 17 IN ooaux c1 c2 a b l 1024)`
    ASSUME_TAC THENL
   [OO_EXCLUDE_ALL_TAC C975D_F 1024 THEN OO_DOMAIN_CASES_TAC C975D_NORTHEAST; ALL_TAC] THEN
  ASM_REWRITE_TAC[c975e_compulsory]);;

(* Lean: top_alternatives *)
let C975E_TOP_ALTERNATIVES = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c975d_family
     ==> 3 IN ooaux c1 c2 a b l 34816 \/ 5 IN ooaux c1 c2 a b l 34816 \/
         7 IN ooaux c1 c2 a b l 34816`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPEC_ALL C975E_COMPULSORY) THEN ASM_REWRITE_TAC[c975e_compulsory] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `exists j. j < 10 /\ j IN ooaux c1 c2 a b l 34816` MP_TAC THENL
   [MP_TAC (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                   `c975d_family`; `0`; `oidx c1 c2 a b l 34816`] PK_BUDGET) THEN
    MP_TAC (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                   `c975d_family`; `34816`] OO_CODE) THEN
    ASM_REWRITE_TAC[in_fam 34816 C975D_F] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[ARITH_RULE `0 < 2`; OIDX_LT; pklow_thm 34816 0] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(auxown 0 (c1 (oidx c1 c2 a b l 34816)) (c2 (oidx c1 c2 a b l 34816))
                     (a (oidx c1 c2 a b l 34816)) (b (oidx c1 c2 a b l 34816)) l = {})`
      MP_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC
       `1 <= CARD (auxown 0 (c1 (oidx c1 c2 a b l 34816)) (c2 (oidx c1 c2 a b l 34816))
                   (a (oidx c1 c2 a b l 34816)) (b (oidx c1 c2 a b l 34816)) l)` THEN
      ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN (X_CHOOSE_TAC `j:num`) THEN
    EXISTS_TAC `j:num` THEN
    SUBGOAL_THEN `j < 10` ASSUME_TAC THENL
     [MP_TAC (SPECL [`0`; `c1 (oidx c1 c2 a b l 34816):real`; `c2 (oidx c1 c2 a b l 34816):real`;
                     `a (oidx c1 c2 a b l 34816):real`; `b (oidx c1 c2 a b l 34816):real`; `l:real`]
                    AUXOWN_SUBSET10) THEN
      REWRITE_TAC[ARITH_RULE `0 < 2`; SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[C975E_F_COMBINED];
    ALL_TAC] THEN
  OO_EXCLUDE_ALL_TAC C975D_F 34816 THEN
  DISCH_THEN (X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  UNDISCH_TAC `j < 10` THEN SPEC_TAC (`j:num`, `j:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;
