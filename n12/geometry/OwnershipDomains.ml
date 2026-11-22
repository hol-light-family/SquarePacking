(* ========================================================================= *)
(* Port of Completion/Cases/C981/OwnershipDomains.lean                      *)
(* (S12Completion.C981).  The twelve certified owner domains of case C981   *)
(* and the enumerated ownership vectors.                                     *)
(*   family = ccc981ri_family (CC_C981_RowIdentity.ml);                      *)
(*   case976Family = c981dsub_case976_family (Subset.ml);                    *)
(*   CertifiedDomain family d  = a theorem |- cdom ccc981ri_family m al;     *)
(*   .ofCombined _ combinedSpecN = ro_combined fam N;                        *)
(*   .ofDirectProduct + direct_check_transport = pk_product of               *)
(*     c981dr_direct_check_transport (DomainReuse.ml), which re-checks the   *)
(*     budget equality auxiliary_budget_eq;                                  *)
(*   refineQueries d qs = c981dr_refine_queries d [(mask, kind, owned)..]    *)
(*     (the queries query976_N are C981DSQ_QUERY976_N of Queries00..08.ml);  *)
(*   enumerateAssignments = pc_enum (PrefixCoverage.ml);                     *)
(*   ownershipVector p = c981ow_vector c1 c2 a b l (CC_C981_Ownership.ml);   *)
(*   assignments = c981odm_assignments.                                      *)
(* certified_domain_assignments_mem is proved here for these domains from    *)
(* the completeness of pc_enum (C981ODM_ENUM_COMPLETE, Lean                  *)
(* enumerateAssignments_complete), CDOM_OWNER and OO_AUX_DISJOINT.           *)
(* ========================================================================= *)

needs "n12/geometry/CC_C981_Ownership.ml";;
needs "n12/geometry/DomainReuse.ml";;
needs "n12/geometry/Subset.ml";;
needs "n12/geometry/PrefixCoverage.ml";;
needs "n12/geometry/RelaxedOwnerDomain.ml";;

(* Lean: auxiliary_budget_eq *)
let C981ODM_AUXILIARY_BUDGET_EQ = prove
 (`forall k. k < 2 ==> CARD (c981dsub_case976_family INTER auxex k) =
                 CARD (ccc981ri_family INTER auxex k)`,
  REWRITE_TAC[ARITH_RULE `k < 2 <=> k = 0 \/ k = 1`] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[card_exempt `c981dsub_case976_family` 0; card_exempt `ccc981ri_family` 0;
              card_exempt `c981dsub_case976_family` 1; card_exempt `ccc981ri_family` 1]);;

let C981ODM_FAM = `ccc981ri_family`;;
let C981ODM_SUB = `c981dsub_case976_family`;;

(* Lean: .ofDirectProduct _ w0 w1 (direct_check_transport ..) (direct_check_transport ..) rfl *)
let c981odm_direct_product w0 w1 =
  if w0.dmask <> w1.dmask then failwith "c981odm_direct_product: masks" else
  pk_product (c981dr_direct_check_transport w0 C981ODM_SUB C981ODM_FAM 0)
             (c981dr_direct_check_transport w1 C981ODM_SUB C981ODM_FAM 1);;

(* Lean: domain0 *)
let C981ODM_DOMAIN0 = ro_combined C981ODM_FAM 1;;
(* Lean: domain1 *)
let C981ODM_DOMAIN1 = ro_combined C981ODM_FAM 3;;
(* Lean: corner2 *)
let C981ODM_CORNER2 = c981odm_direct_product c981dsub_single976_2_0 c981dsub_single976_2_1;;
(* Lean: domain2 *)
let C981ODM_DOMAIN2 = c981dr_refine_queries C981ODM_CORNER2
  [(12, 2, [15]); (12, 2, [8]); (12, 2, [8; 15])];;
(* Lean: corner3 *)
let C981ODM_CORNER3 = c981odm_direct_product c981dsub_single976_3_0 c981dsub_single976_3_1;;
(* Lean: domain3 *)
let C981ODM_DOMAIN3 = c981dr_refine_queries C981ODM_CORNER3
  [(48, 2, [17]); (48, 2, [9]); (48, 2, [9; 17])];;
(* Lean: corner4 *)
let C981ODM_CORNER4 = c981odm_direct_product c981dsub_single976_4_0 c981dsub_single976_4_1;;
(* Lean: domain4 *)
let C981ODM_DOMAIN4 = c981dr_refine_queries C981ODM_CORNER4
  [(192, 2, [14]); (192, 2, [1]); (192, 2, [1; 14])];;
(* Lean: domain5 *)
let C981ODM_DOMAIN5 = ro_combined C981ODM_FAM 8;;
(* Lean: central6 *)
let C981ODM_CENTRAL6 = c981odm_direct_product c981dsub_single976_7_0 c981dsub_single976_7_1;;
(* Lean: centralQueries (query976_649 .. query976_705), as (mask, kind, owned) *)
let c981odm_central_queries = [
  (1024, 2, [5; 16; 18]);
  (1024, 2, [3; 5; 16]);
  (1024, 2, [3; 5; 13; 16]);
  (1024, 2, [3; 5; 14; 16]);
  (1024, 2, [3; 5; 17]);
  (1024, 2, [3; 5; 13; 17]);
  (1024, 2, [3; 5; 16; 17]);
  (1024, 2, [3; 5; 16; 18]);
  (1024, 2, [3; 5; 19]);
  (1024, 2, [3; 5; 16; 19]);
  (1024, 2, [3; 5; 17; 19]);
  (1024, 2, [4; 5; 17]);
  (1024, 2, [4; 5; 13; 17]);
  (1024, 2, [4; 5; 14; 17]);
  (1024, 2, [4; 5; 16; 18]);
  (1024, 2, [4; 5; 19]);
  (1024, 2, [4; 5; 17; 19]);
  (1024, 2, [7; 13; 16]);
  (1024, 2, [7; 14; 16]);
  (1024, 2, [7; 13; 17]);
  (1024, 2, [7; 14; 17]);
  (1024, 2, [7; 16; 18]);
  (1024, 2, [5; 7; 14; 16]);
  (1024, 2, [5; 7; 16; 18]);
  (1024, 2, [5; 8; 17]);
  (1024, 2, [5; 8; 13; 17]);
  (1024, 2, [5; 8; 14; 17]);
  (1024, 2, [5; 8; 16; 18]);
  (1024, 2, [5; 8; 19]);
  (1024, 2, [5; 8; 16; 19]);
  (1024, 2, [5; 8; 17; 19]);
  (1024, 2, [9; 13; 16]);
  (1024, 2, [9; 14; 16]);
  (1024, 2, [9; 13; 17]);
  (1024, 2, [9; 14; 17]);
  (1024, 2, [9; 16; 18]);
  (1024, 2, [4; 9; 13; 16]);
  (1024, 2, [4; 9; 14; 16]);
  (1024, 2, [4; 9; 17]);
  (1024, 2, [4; 9; 13; 17]);
  (1024, 2, [4; 9; 14; 17]);
  (1024, 2, [4; 9; 16; 18]);
  (1024, 2, [4; 9; 19]);
  (1024, 2, [4; 9; 17; 19]);
  (1024, 2, [5; 9; 16; 18]);
  (1024, 2, [7; 9; 13; 16]);
  (1024, 2, [7; 9; 14; 16]);
  (1024, 2, [7; 9; 13; 17]);
  (1024, 2, [7; 9; 14; 17]);
  (1024, 2, [7; 9; 16; 18]);
  (1024, 2, [8; 9; 13; 16]);
  (1024, 2, [8; 9; 14; 16]);
  (1024, 2, [8; 9; 17]);
  (1024, 2, [8; 9; 13; 17]);
  (1024, 2, [8; 9; 14; 17]);
  (1024, 2, [8; 9; 19]);
  (1024, 2, [8; 9; 17; 19])];;

(* Lean: domain6 *)
let C981ODM_DOMAIN6 = c981dr_refine_queries C981ODM_CENTRAL6 c981odm_central_queries;;
(* Lean: domain7 *)
let C981ODM_DOMAIN7 = ro_combined C981ODM_FAM 13;;
(* Lean: domain8 *)
let C981ODM_DOMAIN8 = ro_combined C981ODM_FAM 17;;
(* Lean: domain9 *)
let C981ODM_DOMAIN9 = ro_combined C981ODM_FAM 19;;
(* Lean: domain10 *)
let C981ODM_DOMAIN10 = ro_combined C981ODM_FAM 21;;
(* Lean: domain11 *)
let C981ODM_DOMAIN11 = ro_combined C981ODM_FAM 24;;

(* Lean: domains *)
let C981ODM_DOMAINS =
  [C981ODM_DOMAIN0; C981ODM_DOMAIN1; C981ODM_DOMAIN2; C981ODM_DOMAIN3; C981ODM_DOMAIN4;
   C981ODM_DOMAIN5; C981ODM_DOMAIN6; C981ODM_DOMAIN7; C981ODM_DOMAIN8; C981ODM_DOMAIN9;
   C981ODM_DOMAIN10; C981ODM_DOMAIN11];;

let () =
  if map cdom_mask C981ODM_DOMAINS <> C981OW_MASKS then
    failwith "C981ODM_DOMAINS: masks differ from ownerMasks";
  if exists (fun th -> cdom_fam th <> C981ODM_FAM) C981ODM_DOMAINS then
    failwith "C981ODM_DOMAINS: family";;

(* Lean: assignments *)
let c981odm_assignments = new_definition
  (mk_eq(`c981odm_assignments:((num->bool)list)list`,
         list_mk_comb(`pc_enum`,
           [mk_list(map (fun th -> rand (concl th)) C981ODM_DOMAINS, `:(num->bool)list`);
            `{}:num->bool`])));;

(* Lean: S12.enumerateAssignments_complete *)
let C981ODM_ENUM_COMPLETE = prove
 (`forall ds actual used. ALL2 (\x d. MEM x d) actual ds /\ PAIRWISE DISJOINT actual /\
                    (forall x. MEM x actual ==> DISJOINT x used)
                    ==> MEM actual (pc_enum ds used)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; pc_enum; MEM] THEN
  REWRITE_TAC[PC_MEM_FLATMAP; PAIRWISE; MEM] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `h':num->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `DISJOINT (h':num->bool) used` (fun th -> REWRITE_TAC[th]) THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MEM_MAP; CONS_11] THEN EXISTS_TAC `t':(num->bool)list` THEN
  REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  REWRITE_TAC[SET_RULE `forall a b c:num->bool. DISJOINT a (b UNION c) <=> DISJOINT a b /\ DISJOINT a c`] THEN
  ASM_MESON_TAC[DISJOINT_SYM]);;

(* Lean: ownership_mem_assignments *)
let C981ODM_OWNERSHIP_MEM_ASSIGNMENTS =
  let hyp = mk_conj(`NPACK c1 c2 a b l`, mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, C981ODM_FAM)) in
  let h = ASSUME hyp in
  let hnp = CONJUNCT1 h and hrow = CONJUNCT2 h in
  let mems = map (fun d ->
      MATCH_MP CDOM_OWNER (CONJ d (CONJ hnp (CONJ hrow (in_fam (cdom_mask d) C981ODM_FAM)))))
    C981ODM_DOMAINS in
  let rec pairs l = match l with [] -> [] | x :: r -> map (fun y -> (x, y)) r @ pairs r in
  let disj (mi, mj) =
    let ne = EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral mi, mk_small_numeral mj))) in
    MATCH_MP OO_AUX_DISJOINT
      (end_itlist CONJ [hnp; hrow; in_fam mi C981ODM_FAM; in_fam mj C981ODM_FAM; ne]) in
  let disjs = map disj (pairs C981OW_MASKS) in
  let vec = (REWRITE_CONV[c981ow_vector; c981ow_masks; MAP] THENC DEPTH_CONV BETA_CONV)
              `c981ow_vector c1 c2 a b l` in
  let goal = mk_comb(mk_comb(`MEM:((num->bool)list)->((num->bool)list)list->bool`,
                             `c981ow_vector c1 c2 a b l`), `c981odm_assignments`) in
  let th = prove(mk_imp(hyp, goal), DISCH_TAC THEN
    REWRITE_TAC[vec; c981odm_assignments] THEN MATCH_MP_TAC C981ODM_ENUM_COMPLETE THEN
    REWRITE_TAC[ALL2; PAIRWISE; ALL; DISJOINT_EMPTY] THEN BETA_TAC THEN
    REWRITE_TAC(mems @ disjs)) in
  GENL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] th;;
