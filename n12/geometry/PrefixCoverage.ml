(* ========================================================================= *)
(* Port of Compact/Bridge/PrefixCoverage.lean (N12Compact.PrefixCoverage).   *)
(* A checked sequence of small literal front covers replaces one large       *)
(* reduction of the ownership Cartesian product.  Finsets of naturals are    *)
(* num->bool sets, Lean lists are HOL lists; Lean Disjoint is DISJOINT,      *)
(* List.Forall2 is ALL2, List.Pairwise is PAIRWISE.                           *)
(* S12.enumerateAssignments (source/S12/DomainEnumeration.lean) is ported   *)
(* here as pc_enum (flatMap = pc_flatmap).                                   *)
(* OCaml: pc_extensions_conv evaluates pc_extensions on literal tables;     *)
(* pc_chain_of_tables before [choice_1; ..] proves                          *)
(*   |- pc_chain before [choice_1; ..] after   (after computed and checked). *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

let pc_flatmap = new_recursive_definition list_RECURSION
 `(pc_flatmap (f:A->B list) [] = []) /\
  (pc_flatmap f (CONS h t) = APPEND (f h) (pc_flatmap f t))`;;

let PC_MEM_FLATMAP = prove
 (`forall (f:A->B list) l x. MEM x (pc_flatmap f l) <=> exists y. MEM y l /\ MEM x (f y)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[pc_flatmap; MEM; MEM_APPEND] THEN
  MESON_TAC[]);;

(* Lean: S12.enumerateAssignments *)
let pc_enum = new_recursive_definition list_RECURSION
 `(pc_enum [] (used:num->bool) = [[]:(num->bool)list]) /\
  (pc_enum (CONS (d:(num->bool)list) ds) used =
     pc_flatmap (\x. if DISJOINT x used then MAP (CONS x) (pc_enum ds (used UNION x)) else []) d)`;;

(* Lean: StepCheck *)
let pc_stepcheck = new_definition
 `pc_stepcheck (before:((num->bool)list)list) (choices:(num->bool)list) after <=>
    forall front. MEM front before ==> forall x. MEM x choices ==>
      (forall y. MEM y front ==> DISJOINT x y) ==> MEM (APPEND front [x]) after`;;

(* Lean: extensions *)
let pc_extensions = new_definition
 `pc_extensions (before:((num->bool)list)list) (choices:(num->bool)list) =
    pc_flatmap (\front. MAP (\x. APPEND front [x])
                          (FILTER (\x. ALL (\y. DISJOINT x y) front) choices)) before`;;

(* Lean: stepCheck_extensions *)
let PC_STEPCHECK_EXTENSIONS = prove
 (`forall before choices. pc_stepcheck before choices (pc_extensions before choices)`,
  REWRITE_TAC[pc_stepcheck; pc_extensions; PC_MEM_FLATMAP] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `front:(num->bool)list` THEN ASM_REWRITE_TAC[MEM_MAP; MEM_FILTER] THEN
  EXISTS_TAC `x:num->bool` THEN ASM_REWRITE_TAC[GSYM ALL_MEM]);;

(* Lean: stepCheck_of_extensions_eq *)
let PC_STEPCHECK_OF_EXTENSIONS_EQ = prove
 (`forall before choices after. pc_extensions before choices = after
     ==> pc_stepcheck before choices after`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[PC_STEPCHECK_EXTENSIONS]);;

(* Lean: Chain (inductive) *)
let pc_chain_RULES, pc_chain_INDUCT, pc_chain_CASES = new_inductive_definition
 `(forall before. pc_chain (before:((num->bool)list)list) [] before) /\
  (forall before next after choice choices.
     pc_stepcheck before choice next /\ pc_chain next choices after
     ==> pc_chain before (CONS choice choices) after)`;;

let PC_APPEND_SNOC = prove
 (`forall front (h:num->bool) t. APPEND front (CONS h t) = APPEND (APPEND front [h]) t`,
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

(* Lean: Chain.sound *)
let PC_CHAIN_SOUND = prove
 (`forall before choices after. pc_chain before choices after
     ==> forall front actual. MEM front before /\ ALL2 (\x d. MEM x d) actual choices /\
                        PAIRWISE DISJOINT actual /\
                        (forall x. MEM x actual ==> forall y. MEM y front ==> DISJOINT x y)
                        ==> MEM (APPEND front actual) after`,
  MATCH_MP_TAC pc_chain_INDUCT THEN CONJ_TAC THENL
  [GEN_TAC THEN REPEAT GEN_TAC THEN
   STRUCT_CASES_TAC(ISPEC `actual:(num->bool)list` list_CASES) THEN
   REWRITE_TAC[ALL2; APPEND_NIL] THEN MESON_TAC[];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[pc_stepcheck; RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `actual:(num->bool)list` list_CASES) THEN
  REWRITE_TAC[ALL2; PAIRWISE; MEM; GSYM ALL_MEM] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[PC_APPEND_SNOC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MEM_APPEND; MEM] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[DISJOINT_SYM]);;

(* Lean: enumerate_valid *)
let PC_ENUMERATE_VALID = prove
 (`forall choices actual used. MEM actual (pc_enum choices used)
     ==> ALL2 (\x d. MEM x d) actual choices /\ PAIRWISE DISJOINT actual /\
         (forall x. MEM x actual ==> DISJOINT x used)`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC[pc_enum; MEM] THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC[ALL2; PAIRWISE; MEM];
   ALL_TAC] THEN
  REWRITE_TAC[pc_enum; PC_MEM_FLATMAP] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num->bool` STRIP_ASSUME_TAC) THEN
  POP_ASSUM MP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[MEM; MEM_MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:(num->bool)list` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`xs:(num->bool)list`; `(used:num->bool) UNION x`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ALL2; PAIRWISE; MEM; GSYM ALL_MEM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SET_RULE `forall a b c:num->bool. DISJOINT a (b UNION c) <=> DISJOINT a b /\ DISJOINT a c`]) THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[DISJOINT_SYM]);;

(* Lean: cases_of_chain *)
let PC_CASES_OF_CHAIN = prove
 (`forall choices targets cases.
     pc_chain [[]] choices targets /\ (forall a. MEM a targets ==> MEM a cases)
     ==> forall a. MEM a (pc_enum choices {}) ==> MEM a cases`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `a:(num->bool)list` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PC_ENUMERATE_VALID) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`[]:(num->bool)list`; `a:(num->bool)list`] o
    MATCH_MP PC_CHAIN_SOUND) THEN
  ASM_REWRITE_TAC[MEM; APPEND]);;

(* ------------------------------------------------------------------------- *)
(* Evaluation on literal tables (Lean: decide on StepCheck / extensions).    *)
(* ------------------------------------------------------------------------- *)

let PC_DISJ_CONV =
  REWRITE_CONV[DISJOINT_INSERT; DISJOINT_EMPTY; IN_INSERT; NOT_IN_EMPTY] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV[];;

let pc_extensions_conv tm =
  (REWRITE_CONV[pc_extensions; pc_flatmap] THENC
   REWRITE_CONV[FILTER; ALL] THENC DEPTH_CONV BETA_CONV THENC
   ONCE_DEPTH_CONV (fun t -> if is_comb t && is_comb (rator t) &&
                                rator (rator t) = `DISJOINT:(num->bool)->(num->bool)->bool`
                             then PC_DISJ_CONV t else failwith "") THENC
   REWRITE_CONV[] THENC REWRITE_CONV[MAP; APPEND] THENC DEPTH_CONV BETA_CONV THENC
   REWRITE_CONV[APPEND]) tm;;

(* |- pc_chain before [c_1; ..; c_n] after, each step by its extensions *)
let pc_chain_of_tables before choices =
  let rec go b cs = match cs with
      [] -> ISPEC b (CONJUNCT1 pc_chain_RULES)
    | c :: rest ->
        let e = pc_extensions_conv (list_mk_comb(`pc_extensions`, [b; c])) in
        let step = MATCH_MP PC_STEPCHECK_OF_EXTENSIONS_EQ e in
        let tl = go (rhs (concl e)) rest in
        MATCH_MP (CONJUNCT2 pc_chain_RULES) (CONJ step tl) in
  go before choices;;
