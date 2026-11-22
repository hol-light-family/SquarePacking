(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C896Entrance.lean.                *)
(* Compulsory points of the original C896 family.                           *)
(* Lean  natAuxOwners p 0 (ownerIndex p mask)  is                           *)
(*   auxown 0 (c1 (oidx c1 c2 a b l mask)) (c2 ..) (a ..) (b ..) l           *)
(* (c896e_fown below); Lean  auxiliaries p mask  is  ooaux c1 c2 a b l mask. *)
(* The structure Compulsory is the predicate c896e_compulsory.              *)
(* The private  foreign  (auxiliary_disjoint) is applied inside             *)
(* OO_CHAIN_TAC / OO_EXCLUDE_ALL_TAC.                                       *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C896Domains.ml";;

let c896e_fown m =
  let iv = list_mk_comb(`oidx`, [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; m]) in
  list_mk_comb(`auxown`, [`0`; mk_comb(`c1:num->real`, iv); mk_comb(`c2:num->real`, iv);
                          mk_comb(`a:num->real`, iv); mk_comb(`b:num->real`, iv); `l:real`]);;

(* Lean: Compulsory (structure) *)
let c896e_compulsory = new_definition
 `c896e_compulsory (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) <=>
    (2 IN ooaux c1 c2 a b l 1 /\ 12 IN ooaux c1 c2 a b l 1) /\
    (0 IN ooaux c1 c2 a b l 2 /\ 10 IN ooaux c1 c2 a b l 2) /\
    (7 IN ooaux c1 c2 a b l 16 /\ 17 IN ooaux c1 c2 a b l 16) /\
    (6 IN ooaux c1 c2 a b l 8192 /\ 15 IN ooaux c1 c2 a b l 8192) /\
    (1 IN ooaux c1 c2 a b l 4096 /\ 11 IN ooaux c1 c2 a b l 4096) /\
    (3 IN ooaux c1 c2 a b l 32768 /\ 14 IN ooaux c1 c2 a b l 32768) /\
    (5 IN ooaux c1 c2 a b l 2048 /\ 13 IN ooaux c1 c2 a b l 2048) /\
    9 IN ooaux c1 c2 a b l 1024 /\
    (8 IN ooaux c1 c2 a b l 16384 /\ 18 IN ooaux c1 c2 a b l 16384) /\
    4 IN ooaux c1 c2 a b l 768`;;

(* Lean: f_combined (private) *)
let C896E_F_COMBINED = prove
 (mk_forall(`c1:num->real`, mk_forall(`c2:num->real`, mk_forall(`a:num->real`, mk_forall(`b:num->real`,
   mk_forall(`l:real`, mk_forall(`mask:num`, mk_forall(`index:num`,
     mk_imp(`index < 10`, mk_iff(mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, `index:num`), c896e_fown `mask:num`),
                                 `index IN ooaux c1 c2 a b l mask`))))))))),
  REPEAT STRIP_TAC THEN REWRITE_TAC[ooaux; AUXOWN2; IN_UNION; IN_IMAGE] THEN
  MATCH_MP_TAC(TAUT `~q ==> (p <=> p \/ q)`) THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
  GEN_TAC THEN MATCH_MP_TAC(TAUT `~a ==> ~(a /\ b)`) THEN ASM_ARITH_TAC);;

let c896e_fcomb m j =
  MP (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
             mk_small_numeral m; mk_small_numeral j] C896E_F_COMBINED)
     (EQT_ELIM (NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` (mk_small_numeral j) `10`)));;

(* Lean: ordinary_f_card *)
let C896E_ORDINARY_F_CARD = prove
 (mk_forall(`c1:num->real`, mk_forall(`c2:num->real`, mk_forall(`a:num->real`, mk_forall(`b:num->real`,
   mk_forall(`l:real`, mk_forall(`mask:num`,
     mk_imp(`NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c896d_family /\
             mask IN c896d_family /\ ~(mask IN auxex 0)`,
            mk_eq(mk_comb(`CARD:(num->bool)->num`, c896e_fown `mask:num`), `1`)))))))),
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                 `c896d_family`; `0`; `oidx c1 c2 a b l mask`] PK_BUDGET) THEN
  MP_TAC (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                 `c896d_family`; `mask:num`] OO_CODE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_RULE `0 < 2`] THEN
  ASM_REWRITE_TAC[pkup; pklow; C896D_F_COUNT] THEN ARITH_TAC);;

(* Lean: singleton_points (private) *)
let C896E_SINGLETON_POINTS = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c896d_family
     ==> (2 IN ooaux c1 c2 a b l 1 /\ 12 IN ooaux c1 c2 a b l 1) /\
         (0 IN ooaux c1 c2 a b l 2 /\ 10 IN ooaux c1 c2 a b l 2) /\
         (7 IN ooaux c1 c2 a b l 16 /\ 17 IN ooaux c1 c2 a b l 16)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [OO_SEED_MEM_TAC C896D_F 1 2 [(`&28 / &25`, `&1`); (`&87 / &50`, `&1`)];
    OO_SEED_MEM_TAC C896D_F 1 12 [(`&87 / &50`, `&1`)];
    OO_SEED_MEM_TAC C896D_F 2 0 [(`&1`, `&87 / &50`)];
    OO_SEED_MEM_TAC C896D_F 2 10 [(`&1`, `&28 / &25`); (`&1`, `&87 / &50`)];
    OO_SEED_MEM_TAC C896D_F 16 7 [(`&113 / &50`, `&3`); (`&72 / &25`, `&3`)];
    OO_SEED_MEM_TAC C896D_F 16 17 [(`&113 / &50`, `&3`)]]);;

(* Lean: northeast_cut (private); the list is the allowed list of northeastF *)
let C896E_NE_ALLOWED = rand (concl C896D_NORTHEAST_F);;
let C896E_NORTHEAST_CUT =
  let () = if C896E_NE_ALLOWED = `[{5}; {7}; {9}]` then () else failwith "C896E: northeastF list" in
  prove
   (`forall s. MEM s [{5}; {7}; {9}] /\ ~(5 IN s) /\ ~(7 IN s) ==> 9 IN s`,
    OO_LIST_CUT_TAC []);;

let C896E_DOMS = [8192, C896D_BOTTOM; 4096, C896D_LEFT; 32768, C896D_TOP; 2048, C896D_NORTHWEST;
                  16384, C896D_RIGHT];;

(* Lean: compulsory *)
let C896E_COMPULSORY = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c896d_family
     ==> c896e_compulsory c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPEC_ALL C896E_SINGLETON_POINTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(6 IN ooaux c1 c2 a b l 8192 /\ 15 IN ooaux c1 c2 a b l 8192) /\
                (1 IN ooaux c1 c2 a b l 4096 /\ 11 IN ooaux c1 c2 a b l 4096) /\
                (3 IN ooaux c1 c2 a b l 32768 /\ 14 IN ooaux c1 c2 a b l 32768) /\
                (5 IN ooaux c1 c2 a b l 2048 /\ 13 IN ooaux c1 c2 a b l 2048)` STRIP_ASSUME_TAC THENL
   [OO_CHAIN_TAC C896D_F C896E_DOMS [8192, [6; 15]; 4096, [1; 11]; 32768, [3; 14]; 2048, [5; 13]];
    ALL_TAC] THEN
  SUBGOAL_THEN `9 IN ooaux c1 c2 a b l 1024` ASSUME_TAC THENL
   [OO_EXCLUDE_ALL_TAC C896D_F 1024 THEN
    REWRITE_TAC[GSYM (c896e_fcomb 1024 9)] THEN MATCH_MP_TAC C896E_NORTHEAST_CUT THEN
    REWRITE_TAC[c896e_fcomb 1024 5; c896e_fcomb 1024 7] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HDOM_OWNER THEN EXISTS_TAC C896D_F THEN
    ASM_REWRITE_TAC[C896D_NORTHEAST_F; in_fam 1024 C896D_F];
    ALL_TAC] THEN
  SUBGOAL_THEN `8 IN ooaux c1 c2 a b l 16384 /\ 18 IN ooaux c1 c2 a b l 16384` STRIP_ASSUME_TAC THENL
   [OO_CHAIN_TAC C896D_F C896E_DOMS [16384, [8; 18]]; ALL_TAC] THEN
  SUBGOAL_THEN `exists j. j < 10 /\ j IN ooaux c1 c2 a b l 768` MP_TAC THENL
   [MP_TAC (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `768`]
                  C896E_ORDINARY_F_CARD) THEN
    ASM_REWRITE_TAC[in_fam 768 C896D_F; EQF_ELIM (AUXEX_CONV `768 IN auxex 0`)] THEN DISCH_TAC THEN
    SUBGOAL_THEN (mk_neg (mk_eq (c896e_fown `768`, `{}:num->bool`))) MP_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && rhs (concl th) = `1`)) THEN
      ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN (X_CHOOSE_TAC `j:num`) THEN
    EXISTS_TAC `j:num` THEN
    SUBGOAL_THEN `j < 10` ASSUME_TAC THENL
     [MP_TAC (SPECL [`0`; `c1 (oidx c1 c2 a b l 768):real`; `c2 (oidx c1 c2 a b l 768):real`;
                     `a (oidx c1 c2 a b l 768):real`; `b (oidx c1 c2 a b l 768):real`; `l:real`]
                    AUXOWN_SUBSET10) THEN
      REWRITE_TAC[ARITH_RULE `0 < 2`; SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[C896E_F_COMBINED];
    ALL_TAC] THEN
  OO_EXCLUDE_ALL_TAC C896D_F 768 THEN
  DISCH_THEN (X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  UNDISCH_TAC `j < 10` THEN SPEC_TAC (`j:num`, `j:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
  ASM_REWRITE_TAC[c896e_compulsory]);;
