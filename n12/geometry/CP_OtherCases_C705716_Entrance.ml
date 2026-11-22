(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C705716/Entrance.lean.            *)
(* The unique auxiliary labels of C705 (b = false, family                   *)
(* c705716ri_family_f) and C716 (b = true, c705716ri_family_t).             *)
(* domains b = fst / snd C705716RD_DOMAINS (theorems |- cdom fam m al);     *)
(* domain_masks / domain_members / domain_distinct are OCaml checks on these *)
(* theorems (they fail otherwise); enumerateAssignments is pc_enum;         *)
(* certified_domain_assignments_mem is C705716E_ASSIGNMENTS_MEM (via the    *)
(* local copy C705716E_ENUM_COMPLETE of S12.enumerateAssignments_complete). *)
(* natCombinedOwners p (ownerIndex p m) is ooaux c1 c2 a b l m, ownerCode b *)
(* is c705716ri_owner_code b.  Statements at b are stated at the literal    *)
(* bools F / T (OCaml pairs).  Tag C705716E_.                                *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C705716_RefinedDomains.ml";;
needs "n12/geometry/PrefixCoverage.ml";;

let C705716E_FAMS = (`c705716ri_family_f`, `c705716ri_family_t`);;
let c705716e_sel bb (f, t) = if bb then t else f;;
let c705716e_masks bb = [1; 2; 12; 16; 32; 192; (if bb then 512 else 256); (if bb then 3328 else 3584);
                         4096; 8192; 16384; 32768];;

(* Lean: domain_masks *)
let C705716E_DOMAIN_MASKS =
  let ok bb = map cdom_mask (c705716e_sel bb C705716RD_DOMAINS) = c705716e_masks bb in
  if not (ok false && ok true) then failwith "C705716E_DOMAIN_MASKS" else (ok false, ok true);;

(* Lean: domain_members  (m IN family b, for every domain) *)
let C705716E_DOMAIN_MEMBERS =
  let mems bb = map (fun d -> in_fam (cdom_mask d) (c705716e_sel bb C705716E_FAMS))
                    (c705716e_sel bb C705716RD_DOMAINS) in
  (mems false, mems true);;

(* Lean: domain_distinct *)
let C705716E_DOMAIN_DISTINCT =
  let ok bb = let ms = c705716e_masks bb in length (setify ms) = length ms in
  if not (ok false && ok true) then failwith "C705716E_DOMAIN_DISTINCT" else (ok false, ok true);;

(* Lean: expectedVector *)
let c705716e_expected_vector = new_definition
 `c705716e_expected_vector (bb:bool) : (num->bool)list =
    [{2, 12}; {0, 10}; {}; {7, 17}; {9, 19}; {}; {4, (if bb then 16 else 13)};
     {5, (if bb then 13 else 16)}; {1, 11}; {6, 15}; {8, 18}; {3, 14}]`;;

let c705716e_bool bb = if bb then `true` else `false`;;
let c705716e_allowed bb =
  mk_list(map (fun d -> rand (concl d)) (c705716e_sel bb C705716RD_DOMAINS), `:(num->bool)list`);;

(* Lean: complete_singletons (private) *)
let C705716E_COMPLETE_SINGLETONS = (fun f -> (f false, f true)) (fun bb ->
  prove(mk_eq(c705716e_allowed bb,
              mk_comb(`MAP (\s:num->bool. [s])`, mk_comb(`c705716e_expected_vector`, c705716e_bool bb))),
        REWRITE_TAC[c705716e_expected_vector; MAP] THEN CONV_TAC NUM_REDUCE_CONV));;

let C705716E_ENUM_SINGLETONS = prove
 (`forall e used v. MEM v (pc_enum (MAP (\s:num->bool. [s]) e) used) ==> v = e`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; pc_enum; MEM; pc_flatmap; APPEND_NIL] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[MEM; MEM_MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:(num->bool)list` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[CONS_11] THEN ASM_MESON_TAC[]);;

(* Lean: compact_cover (private) *)
let C705716E_COMPACT_COVER = (fun f -> (f false, f true)) (fun bb ->
  let e = mk_comb(`c705716e_expected_vector`, c705716e_bool bb) in
  let goal = mk_forall(`v:(num->bool)list`,
    mk_imp(mk_comb(mk_comb(`MEM:(num->bool)list->((num->bool)list)list->bool`, `v:(num->bool)list`),
                   list_mk_comb(`pc_enum`, [c705716e_allowed bb; `{}:num->bool`])),
           mk_eq(`v:(num->bool)list`, e))) in
  prove(goal, REWRITE_TAC[c705716e_sel bb C705716E_COMPLETE_SINGLETONS; C705716E_ENUM_SINGLETONS]));;

(* Lean: actualVector *)
let c705716e_actual_vector = new_definition
 `c705716e_actual_vector (bb:bool) (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) =
    MAP (\m. ooaux c1 c2 a b l m)
      [1; 2; 12; 16; 32; 192; (if bb then 512 else 256); (if bb then 3328 else 3584);
       4096; 8192; 16384; 32768]`;;

(* Lean: actual_vector_map *)
let C705716E_ACTUAL_VECTOR_MAP = (fun f -> (f false, f true)) (fun bb ->
  let vec = mk_list(map (fun d -> ooaux_tm (cdom_mask d)) (c705716e_sel bb C705716RD_DOMAINS), `:num->bool`) in
  prove(mk_eq(vec, list_mk_comb(`c705716e_actual_vector`,
                     [c705716e_bool bb; `c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`])),
        REWRITE_TAC[c705716e_actual_vector; MAP]));;

(* Lean: actual_entry *)
let C705716E_ACTUAL_ENTRY = prove
 (`forall bb c1 c2 a b l j. j < 12
     ==> EL j (c705716e_actual_vector bb c1 c2 a b l) = ooaux c1 c2 a b l (EL j (c705716ri_owner_code bb))`,
  MAP_EVERY X_GEN_TAC [`bb:bool`; `c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[c705716e_actual_vector; c705716ri_owner_code; MAP] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* S12.enumerateAssignments_complete *)
let C705716E_ENUM_COMPLETE = prove
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

(* S12.certified_domain_assignments_mem for domains b *)
let C705716E_ASSIGNMENTS_MEM = (fun f -> (f false, f true)) (fun bb ->
  let fam = c705716e_sel bb C705716E_FAMS and doms = c705716e_sel bb C705716RD_DOMAINS in
  let hyp = mk_conj(`NPACK c1 c2 a b l`, mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam)) in
  let h = ASSUME hyp in
  let hnp = CONJUNCT1 h and hrow = CONJUNCT2 h in
  let ms = map cdom_mask doms in
  let mems = map (fun d ->
      MATCH_MP CDOM_OWNER (CONJ d (CONJ hnp (CONJ hrow (in_fam (cdom_mask d) fam))))) doms in
  let rec pairs l = match l with [] -> [] | x :: r -> map (fun y -> (x, y)) r @ pairs r in
  let disj (mi, mj) =
    let ne = EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral mi, mk_small_numeral mj))) in
    MATCH_MP OO_AUX_DISJOINT (end_itlist CONJ [hnp; hrow; in_fam mi fam; in_fam mj fam; ne]) in
  let disjs = map disj (pairs ms) in
  let vec = mk_list(map ooaux_tm ms, `:num->bool`) in
  let goal = mk_comb(mk_comb(`MEM:((num->bool)list)->((num->bool)list)list->bool`, vec),
                     list_mk_comb(`pc_enum`, [c705716e_allowed bb; `{}:num->bool`])) in
  let th = prove(mk_imp(hyp, goal), DISCH_TAC THEN MATCH_MP_TAC C705716E_ENUM_COMPLETE THEN
    REWRITE_TAC[ALL2; PAIRWISE; ALL; DISJOINT_EMPTY] THEN BETA_TAC THEN
    REWRITE_TAC(mems @ disjs)) in
  GENL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] th);;

(* Lean: actual_cover *)
let C705716E_ACTUAL_COVER = (fun f -> (f false, f true)) (fun bb ->
  let fam = c705716e_sel bb C705716E_FAMS in
  let hyp = mk_conj(`NPACK c1 c2 a b l`, mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam)) in
  let av = list_mk_comb(`c705716e_actual_vector`,
             [c705716e_bool bb; `c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]) in
  let member = UNDISCH (SPEC_ALL (c705716e_sel bb C705716E_ASSIGNMENTS_MEM)) in
  let cover = MATCH_MP (c705716e_sel bb C705716E_COMPACT_COVER) member in
  let th = REWRITE_RULE[c705716e_sel bb C705716E_ACTUAL_VECTOR_MAP] cover in
  GENL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    (DISCH hyp (EQ_MP (REFL (concl th)) th)) |> fun t ->
  if rand (rator (snd (dest_imp (snd (strip_forall (concl t)))))) = av then t
  else failwith "C705716E_ACTUAL_COVER");;
