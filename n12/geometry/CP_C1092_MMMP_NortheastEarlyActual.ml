(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/NortheastEarlyActual.lean           *)
(* (N12Compact.C1092MMMPNortheastEarlyActual).  The genuine northeast upper  *)
(* faces and strict upper point before the top origin.  Conventions of       *)
(* CP_C1092_MMMP_NortheastActualSign.ml (PositiveActual N is c1092mnas_pos)  *)
(* and CP_C1092_MMMP_RightFar.ml.  clockwise q = (c, s, --v - a, u, a)       *)
(* (C1092MEA_INSIDE_CLOCKWISE: inside x y <=> q inside y (--x)).             *)
(* NortheastEarlyFaces Data / faces / upper_point / small_central:          *)
(* c1092nef_data / C1092NEF_FACES / C1092NEF_UPPER_POINT /                   *)
(* C1092NEF_SMALL_CENTRAL.  An OpenSquare B is cB sB uB vB aB with its       *)
(* invariants as hypotheses; Profile p B is c1092neea_profile.               *)
(* Tag C1092NEEA_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_RightFar.ml";;
needs "n12/geometry/CP_C1092_MMMP_NortheastEarlyFaces.ml";;
needs "n12/geometry/CP_C1092_MMMP_NortheastActualSign.ml";;

(* Lean: Profile (structure) *)
let c1092neea_profile = new_definition
 `c1092neea_profile (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real)
                    (cB:real) (sB:real) (uB:real) (vB:real) (aB:real) <=>
    aB = l /\
    (forall x y. linside cB sB uB vB aB x y <=>
           linside (ooc c1 c2 a b l (EL 6 c1092wc_code)) (oos c1 c2 a b l (EL 6 c1092wc_code))
                   (oou c1 c2 a b l (EL 6 c1092wc_code)) (oov c1 c2 a b l (EL 6 c1092wc_code)) l
                   (&2 + y) (&2 - x)) /\
    c977cc_normal cB sB /\ &0 < sB /\ c1092nef_data cB sB uB vB aB`;;

let C1092NEEA_NEG = REAL_ARITH `forall x. &2 + --x = &2 - x`;;

(* Lean: exists_profile *)
let C1092NEEA_EXISTS_PROFILE = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> ?cB sB uB vB aB. cB * cB + sB * sB = &1 /\\ &0 < aB /\\
      c1092neea_profile c1 c2 a b l cB sB uB vB aB" C1092AE_P C1092AE_HYP C1092MMPE_CTX),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MRF_POINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092MNAS_EXISTS_POSITIVE) THEN ASM_REWRITE_TAC[c1092mnas_pos] THEN
  MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC))
    [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aN:real = l`)) THEN
  MAP_EVERY EXISTS_TAC [`cN:real`; `sN:real`; `--vN - l`; `uN:real`; `l:real`] THEN
  REWRITE_TAC[c1092neea_profile; C1092MEA_INSIDE_CLOCKWISE] THEN ASM_REWRITE_TAC[C1092NEEA_NEG] THEN
  MATCH_MP_TAC C1092NEF_FACES THEN REWRITE_TAC[C1092MEA_INSIDE_CLOCKWISE] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC C1092MO_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  let ne = c1092mo_use C1092MMPE_NORTHEAST_PAIR in
  let middle = CONV_RULE REAL_RAT_REDUCE_CONV (MATCH_MP C1092WC_INSIDE_SEGMENT
    (end_itlist CONJ [c1092mo_use C1092MPC_NORTHWEST_CENTER; c1092mo_use C1092MPC_NORTHWEST_NORTH;
                      REAL_ARITH `&0 <= &4 / &5`; REAL_ARITH `&4 / &5 <= &1`])) in
  let rfar = CONV_RULE C1092MO_CODE_CONV (ASSUME (parse_term (c1092mmpe_in 10 "&3" "&12 / &5"))) in
  ASM_REWRITE_TAC[CONJUNCT1 ne; c1092mo_seed 6 (`&47 / &20`, `&47 / &20`);
    c1092mo_excl 6 7 middle; c1092mo_excl 6 10 rfar;
    c1092mo_excl 6 11 (c1092mo_seed 11 (`&2`, `&1543 / &500`));
    c1092mo_excl 6 2 (c1092mo_seed 2 (`&3`, `&3`))] THEN
  MP_TAC(c1092mo_side ()) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: upper_point *)
let C1092NEEA_UPPER_POINT = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> %s" C1092AE_P C1092AE_HYP C1092MMPE_CTX
    (c1092mmpe_in 6 "&107 / &50" "&5 / &2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092NEEA_EXISTS_PROFILE) THEN ASM_REWRITE_TAC[c1092neea_profile] THEN
  MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC))
    [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aB:real = l`)) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `l:real`] C1092NEF_UPPER_POINT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[]);;

(* Lean: small_northwest *)
let C1092NEEA_SMALL_NORTHWEST = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s /\\ cC * cC + sC * sC = &1 /\\ &0 < aC /\\ aC = l /\\
      (!x y. linside cC sC uC vC aC x y <=> %s) /\\ c977cc_normal cC (--sC)
      ==> --sC < &7 / &50 /\\ &99 / &100 < cC" C1092AE_P C1092AE_HYP C1092MMPE_CTX
    (c1092mmpe_in 7 "&2 + x" "&2 + y")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l`)) THEN
  MP_TAC(SPEC_ALL C1092NEEA_EXISTS_PROFILE) THEN ASM_REWRITE_TAC[c1092neea_profile] THEN
  MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC))
    [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aB:real = l`)) THEN
  MATCH_MP_TAC (SPECL [`cC:real`; `sC:real`; `--vC - l`; `uC:real`; `l:real`;
                       `cB:real`; `sB:real`; `uB:real`; `vB:real`; `l:real`] C1092NEF_SMALL_CENTRAL) THEN
  REWRITE_TAC[ldisj; C1092MEA_INSIDE_CLOCKWISE] THEN ASM_REWRITE_TAC[C1092NEEA_NEG] THEN
  CONV_TAC C1092MO_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  let ne = c1092mo_use C1092MMPE_NORTHEAST_PAIR in
  ASM_REWRITE_TAC[CONJUNCT1 ne; c1092mo_seed 6 (`&47 / &20`, `&47 / &20`);
    c1092mo_use C1092MPC_NORTHWEST_CENTER; c1092mo_use C1092MO_NORTHWEST_LEFT;
    c1092mo_seed 7 (`&33 / &20`, `&47 / &20`);
    c1092mo_excl 7 4 (c1092mo_seed 4 (`&33 / &20`, `&33 / &20`));
    REWRITE_RULE[ldisj] (c1092mo_apart 7 6)] THEN
  MP_TAC(c1092mo_side ()) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;
