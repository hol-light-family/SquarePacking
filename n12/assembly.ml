(* ========================================================================= *)
(* Final assembly of the s(12) = 4 port (Jatloe: Compact/Assembly/Final,     *)
(* Remaining117.optimality).                                                 *)
(*                                                                           *)
(* s12_no_packing tbl : tbl is a list of theorems |- EXCLUDED_ROW ri for     *)
(* retained rows ri.  The result is                                          *)
(*     H |- forall t. packs 12 t /\ t < &4 ==> false                          *)
(* where H consists of EXCLUDED_ROW ri for the retained rows not yet in tbl  *)
(* (so with all 117 cases supplied, H is empty).  From it:                   *)
(*     assemble_s12 tbl   H |- square_packing_side 12 = &4                   *)
(*     s12_packs tbl      H |- forall t. packs 12 t <=> &4 <= t              *)
(* Needs S12_REDUCED_117 (n12/phase1/step6_run.ml) and PACKS_12_4.             *)
(* ========================================================================= *)

let S12_SIDE_OF_NO_PACKING = prove
 (`(forall t. packs 12 t /\ t < &4 ==> false) ==> square_packing_side 12 = &4`,
  DISCH_TAC THEN REWRITE_TAC[square_packing_side] THEN
  MATCH_MP_TAC REAL_INF_UNIQUE THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_NOT_LT];
    REPEAT STRIP_TAC THEN EXISTS_TAC `&4` THEN ASM_REWRITE_TAC[PACKS_12_4]]);;

let PACKS_12_OF_NO_PACKING = prove
 (`(forall t. packs 12 t /\ t < &4 ==> false) ==> (forall t. packs 12 t <=> &4 <= t)`,
  DISCH_TAC THEN GEN_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[REAL_NOT_LT];
    DISCH_TAC THEN MATCH_MP_TAC PACKS_MONO THEN EXISTS_TAC `&4` THEN
    ASM_REWRITE_TAC[PACKS_12_4]]);;

let s12_no_packing (thms : thm list) =
  let ex = Array.make 577 None in
  List.iter (fun th ->
      let r = rand(rand(rand(snd(strip_exists(rand(concl th)))))) in
      let ri = index r (map ROW_LIST (0--576)) in
      if not (aconv (concl th) (EXCLUDED_ROW ri)) then failwith "assemble_s12: bad case theorem" else
      if not (mem ri RETAINED_IDX) then failwith "assemble_s12: not a retained row" else
      ex.(ri) <- Some th) thms;
  let get ri = match ex.(ri) with Some th -> th | None -> ASSUME (EXCLUDED_ROW ri) in
  let missing = filter (fun ri -> ex.(ri) = None) RETAINED_IDX in
  Printf.printf "assemble_s12: %d of %d retained rows proved, %d assumed\n%!"
    (length RETAINED_IDX - length missing) (length RETAINED_IDX) (length missing);
  let goal0 = `forall t. packs 12 t /\ t < &4 ==> false` in
  let goal = if missing = [] then goal0 else
    mk_imp(list_mk_conj (map EXCLUDED_ROW missing), goal0) in
  let nop = prove(goal,
    (if missing = [] then ALL_TAC else DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
    GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP S12_REDUCED_117) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
                         `l:real`; `r:num list`] THEN
    REWRITE_TAC[RETAINED; MEM] THEN STRIP_TAC THEN
    UNDISCH_TAC `IMAGE binarysum (FFP c1 c2 a b l) = set_of_list r` THEN
    UNDISCH_TAC `NPACK c1 c2 a b l` THEN
    FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    W(fun (_, w) ->
      (* w = NPACK .. ==> IMAGE binarysum (FFP ..) = set_of_list ROW ==> F *)
      let r = rand(rand(lhand(rand w))) in
      let ri = index r (map ROW_LIST (0--576)) in
      MP_TAC (get ri) THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
      DISCH_THEN(MP_TAC o SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`;
                                 `b:num->real`; `l:real`]) THEN
      REWRITE_TAC[DE_MORGAN_THM] THEN CONV_TAC TAUT)) in
  let nop = if missing = [] then nop else
    let hs = map (fun ri -> ASSUME (EXCLUDED_ROW ri)) missing in
    MP nop (end_itlist CONJ hs) in
  nop;;

let assemble_s12 thms = MP S12_SIDE_OF_NO_PACKING (s12_no_packing thms);;
let s12_packs thms = MP PACKS_12_OF_NO_PACKING (s12_no_packing thms);;
