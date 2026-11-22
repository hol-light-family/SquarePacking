(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C715/Entrance.lean.                *)
(* Final genuine C715 coverage.  domains = C715RD_DOMAINS (OCaml list of     *)
(* |- cdom c715ri_family m al); domains.map allowed is the HOL list         *)
(* c715e_allowed; enumerateAssignments is pc_enum (PrefixCoverage.ml);       *)
(* actualVector p is c715e_actual_vector c1 c2 a b l (natCombinedOwners p    *)
(* (ownerIndex p m) = ooaux c1 c2 a b l m); ownerCode = c715ri_owner_code.  *)
(* domain_masks / domain_members / domain_distinct are checks on the OCaml   *)
(* list (the masks are numerals of the theorems).  certified_domain_         *)
(* assignments_mem is proved here from CDOM_OWNER, OO_AUX_DISJOINT and the   *)
(* completeness of pc_enum (C715E_ENUM_COMPLETE, Lean                        *)
(* enumerateAssignments_complete).  Tag C715E_.                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C715_RefinedDomains.ml";;
needs "n12/geometry/PrefixCoverage.ml";;

let C715E_FAM = `c715ri_family`;;
let C715E_MASKS = [1; 2; 12; 16; 32; 192; 512; 2304; 4096; 8192; 17408; 32768];;

(* Lean: domain_masks *)
let C715E_DOMAIN_MASKS = (map cdom_mask C715RD_DOMAINS = C715E_MASKS);;
if not C715E_DOMAIN_MASKS then failwith "C715E: domain_masks";;

(* Lean: domain_members *)
let C715E_DOMAIN_MEMBERS = map (fun th -> in_fam (cdom_mask th) C715E_FAM) C715RD_DOMAINS;;

(* Lean: domain_distinct *)
let C715E_DOMAIN_DISTINCT = (length (setify C715E_MASKS) = length C715E_MASKS);;
if not C715E_DOMAIN_DISTINCT then failwith "C715E: domain_distinct";;
if exists (fun th -> cdom_fam th <> C715E_FAM) C715RD_DOMAINS then failwith "C715E: family";;

(* domains.map CertifiedDomain.allowed *)
let c715e_allowed = new_definition
  (mk_eq(`c715e_allowed:((num->bool)list)list`,
         mk_list(map (fun th -> rand (concl th)) C715RD_DOMAINS, `:(num->bool)list`)));;

(* Lean: CoverProperty *)
let c715e_cover_property = new_definition
 `c715e_cover_property (v:(num->bool)list) <=>
    5 IN EL 10 v /\ 6 IN EL 9 v /\ 9 IN EL 4 v /\
    ((16 IN EL 6 v /\ 18 IN EL 10 v) \/ (16 IN EL 10 v /\ 18 IN EL 6 v))`;;

(* Lean: compact_cover (private) *)
let C715E_COMPACT_COVER =
  let als = dest_list (rhs (concl c715e_allowed)) in
  let chain = pc_chain_of_tables `[[]:(num->bool)list]` als in
  let targets = rand (concl chain) in
  let triv = prove(mk_forall(`a:(num->bool)list`,
                     mk_imp(mk_comb(mk_comb(`MEM:(num->bool)list->((num->bool)list)list->bool`, `a:(num->bool)list`), targets),
                            mk_comb(mk_comb(`MEM:(num->bool)list->((num->bool)list)list->bool`, `a:(num->bool)list`), targets))),
                   REWRITE_TAC[]) in
  let th = MATCH_MP PC_CASES_OF_CHAIN (CONJ chain triv) in
  prove
   (`forall v. MEM v (pc_enum c715e_allowed {}) ==> c715e_cover_property v`,
    REWRITE_TAC[c715e_allowed] THEN GEN_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP th) THEN REWRITE_TAC[MEM] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[c715e_cover_property] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: actualVector *)
let c715e_actual_vector = new_definition
 `c715e_actual_vector c1 c2 a b l =
    MAP (\m. ooaux c1 c2 a b l m) [1;2;12;16;32;192;512;2304;4096;8192;17408;32768]`;;

(* Lean: actual_vector_map  (domains.map (fun d => .. d.mask) = actualVector p) *)
let C715E_ACTUAL_VECTOR_MAP = prove
 (mk_forall(`c1:num->real`, list_mk_forall([`c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
    mk_eq(mk_list(map (fun th -> ooaux_tm (cdom_mask th)) C715RD_DOMAINS, `:num->bool`),
          `c715e_actual_vector c1 c2 a b l`))),
  REWRITE_TAC[c715e_actual_vector; MAP]);;

(* Lean: actual_entry *)
let C715E_ACTUAL_ENTRY = prove
 (`forall c1 c2 a b l j. j < 12
     ==> EL j (c715e_actual_vector c1 c2 a b l) = ooaux c1 c2 a b l (EL j c715ri_owner_code)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `j < 12 <=> j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/
                                    j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11`] THEN
  REWRITE_TAC[c715e_actual_vector; c715ri_owner_code; MAP] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* Lean: S12.enumerateAssignments_complete *)
let C715E_ENUM_COMPLETE = prove
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

(* Lean: certified_domain_assignments_mem (for these domains) *)
let C715E_ASSIGNMENTS_MEM =
  let hyp = mk_conj(`NPACK c1 c2 a b l`, mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, C715E_FAM)) in
  let h = ASSUME hyp in
  let hnp = CONJUNCT1 h and hrow = CONJUNCT2 h in
  let mems = map (fun d ->
      MATCH_MP CDOM_OWNER (CONJ d (CONJ hnp (CONJ hrow (in_fam (cdom_mask d) C715E_FAM)))))
    C715RD_DOMAINS in
  let rec pairs l = match l with [] -> [] | x :: r -> map (fun y -> (x, y)) r @ pairs r in
  let disj (mi, mj) =
    let ne = EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral mi, mk_small_numeral mj))) in
    MATCH_MP OO_AUX_DISJOINT
      (end_itlist CONJ [hnp; hrow; in_fam mi C715E_FAM; in_fam mj C715E_FAM; ne]) in
  let disjs = map disj (pairs C715E_MASKS) in
  let goal = `MEM (c715e_actual_vector c1 c2 a b l) (pc_enum c715e_allowed {})` in
  let th = prove(mk_imp(hyp, goal), DISCH_TAC THEN
    REWRITE_TAC[GSYM C715E_ACTUAL_VECTOR_MAP; c715e_allowed] THEN
    MATCH_MP_TAC C715E_ENUM_COMPLETE THEN
    REWRITE_TAC[ALL2; PAIRWISE; ALL; DISJOINT_EMPTY] THEN BETA_TAC THEN
    REWRITE_TAC(mems @ disjs)) in
  GENL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] th;;

(* Lean: actual_cover *)
let C715E_ACTUAL_COVER = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c715ri_family
     ==> c715e_cover_property (c715e_actual_vector c1 c2 a b l)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C715E_COMPACT_COVER THEN
  MATCH_MP_TAC C715E_ASSIGNMENTS_MEM THEN ASM_REWRITE_TAC[]);;
