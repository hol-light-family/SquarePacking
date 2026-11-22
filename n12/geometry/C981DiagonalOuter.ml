(* ========================================================================= *)
(* Phase 2: Compact/Bridge/C981DiagonalOuter.lean                            *)
(* (namespace N12Compact.C981DiagonalOuter).  Original C981 auxiliary        *)
(* ownership {9,17} of owner 6 gives the two diagonal endpoints and misses   *)
(* both inner and outer pairs; the vector is excluded by that owner's square *)
(* alone (DiagonalOuterPoint.impossible = DOP_IMPOSSIBLE).                   *)
(* v[6]! is EL 6 v; ExcludesVector is c981vd_excludes_vector (VectorData).   *)
(* ========================================================================= *)

needs "n12/geometry/VectorData.ml";;
needs "n12/geometry/DiagonalOuterPoint.ml";;
needs "n12/geometry/Bridge_C981Row27.ml";;

(* Lean: Check *)
let c981do_check = new_definition
 `c981do_check (v:(num->bool)list) <=>
    17 IN EL 6 v /\ 9 IN EL 6 v /\ ~(5 IN EL 6 v) /\ ~(16 IN EL 6 v) /\
    ~(7 IN EL 6 v) /\ ~(19 IN EL 6 v)`;;

let C981DO_ENTRY6 = prove
 (`forall c1 c2 a b l (v:(num->bool)list). c981ow_vector c1 c2 a b l = v
     ==> ooaux c1 c2 a b l 1024 = EL 6 v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `v:(num->bool)list`; `6`] C981OW_OWNERSHIP_ENTRY_AT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `6 < 12`; c981ow_masks] THEN
  CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV EL_CONV))) THEN REWRITE_TAC[]);;

(* Lean: excludes *)
let C981DO_EXCLUDES = prove
 (`forall v. c981do_check v ==> c981vd_excludes_vector v`,
  GEN_TAC THEN REWRITE_TAC[c981do_check; c981vd_excludes_vector] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C981DO_ENTRY6) THEN
  MP_TAC(SPECL (c981br_owner 6) DOP_IMPOSSIBLE) THEN
  REWRITE_TAC(map oo_aux_point [17; 9; 5; 16; 7; 19]) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[OO_UNIT; OO_SIDE; REAL_ARITH `&1 < l ==> &0 < l`]);;

(* Lean: coveredIds *)
let c981do_covered_ids = new_definition
 `c981do_covered_ids = [7; 110]`;;

(* Lean: covered_checked *)
let C981DO_COVERED_CHECKED = prove
 (`forall i. MEM i c981do_covered_ids ==> c981do_check (EL i c981vd_representative_vectors)`,
  GEN_TAC THEN REWRITE_TAC[c981do_covered_ids; MEM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[c981br_rep_el 7; c981br_rep_el 110; c981do_check] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: covered_excluded *)
let C981DO_COVERED_EXCLUDED = prove
 (`forall i. MEM i c981do_covered_ids ==> c981vd_excludes_vector (EL i c981vd_representative_vectors)`,
  MESON_TAC[C981DO_COVERED_CHECKED; C981DO_EXCLUDES]);;
