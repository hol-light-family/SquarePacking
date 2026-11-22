(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Prefix01.lean                       *)
(* (S12Completion.C981.Coverage.prefix01, step01).  Lean StepCheck is         *)
(* pc_stepcheck (PrefixCoverage.ml); its decide +kernel proof is the producer *)
(* c981cov_step_check before_def choices_def after_def (also used by the     *)
(* later Prefix steps): it computes pc_extensions on the literal tables and   *)
(* proves the step either from extensions = after or, if the literal after    *)
(* lists them differently, by checking each extension is MEM after (literal  *)
(* set equalities decided by setlit_eq_dconv).  Tag C981CP01_ / c981cov_.    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/PrefixCoverage.ml";;
needs "n12/geometry/AllowedData.ml";;
needs "n12/geometry/Prefix00.ml";;

let C981CP01_STEPCHECK_SUBSET = prove
 (`forall before choices after:((num->bool)list)list.
     (forall x. MEM x (pc_extensions before choices) ==> MEM x after)
     ==> pc_stepcheck before choices after`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`before:((num->bool)list)list`; `choices:(num->bool)list`]
    PC_STEPCHECK_EXTENSIONS) THEN
  REWRITE_TAC[pc_stepcheck] THEN ASM_MESON_TAC[]);;

let c981cov_mem_conv =
  REWRITE_CONV[MEM; CONS_11; NOT_CONS_NIL; GSYM NOT_CONS_NIL] THENC
  DEPTH_CONV setlit_eq_dconv THENC REWRITE_CONV[];;

(* front-by-front evaluation of pc_extensions on literal tables (linear in the
   number of fronts; pc_extensions_conv is applied to one front at a time) *)
let C981CP01_EXT_NIL = prove
 (`forall c. pc_extensions [] (c:(num->bool)list) = []`,
  REWRITE_TAC[pc_extensions; pc_flatmap]);;
let C981CP01_EXT_CONS = prove
 (`forall f fs c. pc_extensions (CONS f fs) (c:(num->bool)list) =
            APPEND (pc_extensions [f] c) (pc_extensions fs c)`,
  REWRITE_TAC[pc_extensions; pc_flatmap; APPEND_NIL]);;

let rec c981cov_append_conv tm =
  (REWR_CONV (CONJUNCT1 APPEND) ORELSEC
   (REWR_CONV (CONJUNCT2 APPEND) THENC RAND_CONV c981cov_append_conv)) tm;;

let C981CP01_EXT_ONE = prove
 (`forall f c. pc_extensions [f] (c:(num->bool)list) =
         MAP (\x. APPEND f [x]) (FILTER (\x. ALL (\y. DISJOINT x y) f) c)`,
  REWRITE_TAC[pc_extensions; pc_flatmap; APPEND_NIL]);;

(* DISJOINT of two literal sets (memoised) *)
let C981CP01_DISJ_TBL = Hashtbl.create 1000;;
let c981cov_disj_conv tm =
  try Hashtbl.find C981CP01_DISJ_TBL tm with Not_found ->
  let th = PC_DISJ_CONV tm in Hashtbl.add C981CP01_DISJ_TBL tm th; th;;

let C981CP01_AND_T = TAUT `true /\ p <=> p` and C981CP01_AND_F = TAUT `false /\ p <=> false`;;

(* ALL (\y. DISJOINT h y) [literal sets]  <=> T / F *)
let rec c981cov_all_conv tm =
  (REWR_CONV (CONJUNCT1 ALL) ORELSEC
   (REWR_CONV (CONJUNCT2 ALL) THENC LAND_CONV (BETA_CONV THENC c981cov_disj_conv) THENC
    (REWR_CONV C981CP01_AND_F ORELSEC
     (REWR_CONV C981CP01_AND_T THENC c981cov_all_conv)))) tm;;

let rec c981cov_filter_conv tm =
  (REWR_CONV (CONJUNCT1 FILTER) ORELSEC
   (REWR_CONV (CONJUNCT2 FILTER) THENC
    RATOR_CONV (RATOR_CONV (RAND_CONV (BETA_CONV THENC c981cov_all_conv))) THENC
    ((REWR_CONV (CONJUNCT1 (SPEC_ALL COND_CLAUSES)) THENC RAND_CONV c981cov_filter_conv) ORELSEC
     (REWR_CONV (CONJUNCT2 (SPEC_ALL COND_CLAUSES)) THENC c981cov_filter_conv)))) tm;;

let rec c981cov_map_conv tm =
  (REWR_CONV (CONJUNCT1 MAP) ORELSEC
   (REWR_CONV (CONJUNCT2 MAP) THENC
    LAND_CONV (BETA_CONV THENC c981cov_append_conv) THENC RAND_CONV c981cov_map_conv)) tm;;

let c981cov_ext_one_conv =
  REWR_CONV C981CP01_EXT_ONE THENC RAND_CONV c981cov_filter_conv THENC c981cov_map_conv;;

let rec c981cov_ext_conv tm =
  let fronts = rand (rator tm) in
  if is_const fronts then REWR_CONV C981CP01_EXT_NIL tm else
    (REWR_CONV C981CP01_EXT_CONS THENC
     COMB2_CONV (RAND_CONV c981cov_ext_one_conv) c981cov_ext_conv THENC
     c981cov_append_conv) tm;;

(* |- pc_stepcheck b c a  for definitions |- b = .., |- c = .., |- a = .. *)
let c981cov_step_check bdef cdef adef =
  let b = lhs(concl bdef) and c = lhs(concl cdef) and a = lhs(concl adef) in
  let e = (REWRITE_CONV[bdef; cdef] THENC c981cov_ext_conv)
            (list_mk_comb(`pc_extensions`, [b; c])) in
  if rhs(concl e) = rhs(concl adef) then
    MATCH_MP PC_STEPCHECK_OF_EXTENSIONS_EQ (TRANS e (SYM adef))
  else
    let xs = dest_list (rhs(concl e)) and al = rhs(concl adef) in
    let mems = map (fun x ->
      EQT_ELIM (c981cov_mem_conv (mk_comb(mk_comb(
        mk_const("MEM",[type_of x, aty]), x), al)))) xs in
    let ante = prove
     (mk_forall(`x:(num->bool)list`,
        mk_imp(list_mk_comb(`MEM:((num->bool)list)->(((num->bool)list)list)->bool`,
                            [`x:(num->bool)list`; lhs(concl e)]),
               list_mk_comb(`MEM:((num->bool)list)->(((num->bool)list)list)->bool`,
                            [`x:(num->bool)list`; a]))),
      GEN_TAC THEN REWRITE_TAC[e; MEM] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[adef] THEN FIRST(map ACCEPT_TAC mems)) in
    MATCH_MP C981CP01_STEPCHECK_SUBSET ante;;

(* Lean: prefix01 *)
let c981cov_prefix01 = new_definition
 `c981cov_prefix01 : ((num->bool)list)list = [[{2, 12}]; [{2, 10, 12}]]`;;

(* Lean: step01 *)
let C981CP01_STEP01 = c981cov_step_check c981cov_prefix00 c981cov_allowed0 c981cov_prefix01;;
