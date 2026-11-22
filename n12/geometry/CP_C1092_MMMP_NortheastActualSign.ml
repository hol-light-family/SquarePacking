(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/NortheastActualSign.lean            *)
(* (N12Compact.C1092MMMPNortheastActualSign).  The local northeast sign      *)
(* theorem applied to the original MMMP owners.  Conventions of              *)
(* CP_C1092_MMMP_PointCore.ml / CP_C1092_MMMP_Origins.ml (charts via         *)
(* c1092mo_layers; clockwise is C1092MEA_INSIDE_CLOCKWISE).  The structure   *)
(* PositiveActual p N is the predicate c1092mnas_pos c1 c2 a b l cN sN uN vN *)
(* aN on the coordinates of N (with the OpenSquare invariants).              *)
(* ClosedFrames.canonical_frame CLF_CANONICAL_FRAME,                         *)
(* C1092MMMPNortheastSign.positive C1092MNSG_POSITIVE, inside_segment        *)
(* C1092WC_INSIDE_SEGMENT.  Tag C1092MNAS_.                                  *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_PointCore.ml";;
needs "n12/geometry/CP_C1092_MMMP_NortheastSign.ml";;
needs "n12/geometry/CP_C1092_MMMP_EndingAxes.ml";;

(* Lean: PositiveActual (structure; fields side, actual, normal, positive) *)
let c1092mnas_pos = new_definition
 `c1092mnas_pos c1 c2 a b l (cN:real) (sN:real) (uN:real) (vN:real) (aN:real) <=>
    (cN * cN + sN * sN = &1 /\ &0 < aN) /\
    aN = l /\
    (forall x y. linside cN sN uN vN aN x y <=>
           linside (ooc c1 c2 a b l (EL 6 c1092wc_code)) (oos c1 c2 a b l (EL 6 c1092wc_code))
                   (oou c1 c2 a b l (EL 6 c1092wc_code)) (oov c1 c2 a b l (EL 6 c1092wc_code)) l
                   (&2 + x) (&2 + y)) /\
    c977cc_normal cN sN /\
    &0 < sN`;;

(* the right wall tip: local_wall_segment at wall 2 *)
let C1092MNAS_RIGHT_TIP = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P C1092MMPE_CTX (c1092mmpe_in 10 "&3" "&239 / &100")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MMPE_V @ [`c1092mmpe_mmmp`; `2`; `&161 / &100`]) C1092WC_LOCAL_WALL_SEGMENT) THEN
  ASM_REWRITE_TAC[c1092wc_pmx; c1092wc_pmy; c1092wc_by; c1092mmpe_mmmp; ARITH] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]);;

let C1092MNAS_CW = (C1092MEA_INSIDE_CLOCKWISE, ([]:term list));;

(* Lean: exists_positive *)
let C1092MNAS_EXISTS_POSITIVE = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> ?cN sN uN vN aN. c1092mnas_pos %s cN sN uN vN aN"
    C1092AE_P C1092AE_HYP C1092MMPE_CTX C1092AE_P),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let tq, eqq = c1092mo_layers 6 [c1092mo_tr `&2` `&2`] in
  let tC, eqC = c1092mo_layers 7 [c1092mo_tr `&2` `&2`; C1092MNAS_CW] in
  let tN = [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] in
  let tB = [`cN:real`; `sN:real`; `--vN - aN`; `uN:real`; `aN:real`] in
  let eqB = GENL [`x:real`; `y:real`] (SPECL (tN @ [`x:real`; `y:real`]) C1092MEA_INSIDE_CLOCKWISE) in
  let ne = c1092mo_use C1092MMPE_NORTHEAST_PAIR in
  let center = c1092mo_use C1092MPC_NORTHWEST_CENTER and north = c1092mo_use C1092MPC_NORTHWEST_NORTH in
  let ltip = CONV_RULE C1092MO_CODE_CONV (UNDISCH (SPECL C1092MMPE_V C1092MPC_LEFT_TIP)) in
  let rtip = CONV_RULE C1092MO_CODE_CONV (UNDISCH (SPECL C1092MMPE_V C1092MNAS_RIGHT_TIP)) in
  let middle = CONV_RULE REAL_RAT_REDUCE_CONV (MATCH_MP C1092WC_INSIDE_SEGMENT (CONJ center (CONJ north
      (CONJ (REAL_ARITH `&0 <= &39 / &50`) (REAL_ARITH `&39 / &50 <= &1`))))) in
  let facts = [c1092mo_punit 7 tC; c1092mo_pos (); c1092mo_side ();
               center; north; c1092mo_use C1092MO_NORTHWEST_LEFT;
               c1092mo_seed 7 (`&33 / &20`, `&47 / &20`);
               c1092mo_excl 7 4 (c1092mo_seed 4 (`&33 / &20`, `&33 / &20`));
               c1092mo_excl 7 6 (c1092mo_seed 6 (`&47 / &20`, `&47 / &20`));
               c1092mo_excl 7 8 ltip;
               c1092mo_seed 6 (`&47 / &20`, `&47 / &20`); CONJUNCT1 ne; CONJUNCT2 ne;
               c1092mo_excl 6 7 middle; c1092mo_excl 6 10 rtip;
               c1092mo_excl 6 11 (c1092mo_seed 11 (`&2`, `&1543 / &500`));
               c1092mo_excl 6 2 (c1092mo_seed 2 (`&3`, `&3`));
               c1092mo_excl 6 7 north; c1092mo_apart 7 6] in
  MP_TAC(MP (SPECL tq CLF_CANONICAL_FRAME) (CONJ (c1092mo_punit 6 tq) (c1092mo_pos ()))) THEN
  DISCH_THEN(X_CHOOSE_THEN `cN:real` (X_CHOOSE_THEN `sN:real` (X_CHOOSE_THEN `uN:real`
    (X_CHOOSE_THEN `vN:real` (X_CHOOSE_THEN `aN:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_ASSUM(fun equiv -> if is_forall (concl equiv) &&
      (match strip_comb (lhs (snd (strip_forall (concl equiv)))) with (f, args) ->
         f = `linside` && el 0 args = `cN:real`) then
   (SUBGOAL_THEN `&0 < sN` ASSUME_TAC THENL
     [MP_TAC(SPECL (tC @ tB) C1092MNSG_POSITIVE) THEN
      REWRITE_TAC[ldisj] THEN CONV_TAC (c1092mo_conv (eqC @ [eqB; equiv] @ eqq)) THEN
      ANTS_TAC THENL
       [MAP_EVERY ASSUME_TAC facts THEN REPEAT CONJ_TAC THEN
        FIRST [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM (ACCEPT_TAC o SYM);
               REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC];
        SIMP_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC tN THEN REWRITE_TAC[c1092mnas_pos] THEN
    CONV_TAC C1092MO_CODE_CONV THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[equiv] THEN REWRITE_TAC (map (fun e -> SPEC_ALL e) eqq);
      REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `abs sN <= cN` THEN UNDISCH_TAC `&0 < sN` THEN REAL_ARITH_TAC])
    else NO_TAC));;
