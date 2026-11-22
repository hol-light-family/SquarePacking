(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/TwoFifthsEntranceNorthwest.lean     *)
(* (N12Compact.C1092MMMPTwoFifthsEntrance).  The complete actual E/W         *)
(* entrance for the shared upper-third step.  Conventions of                 *)
(* CP_C1092_MMMP_TwoFifthsEntranceSoutheast.ml / ...Right.ml and the forward *)
(* toolkit c1092mo_* of CP_C1092_MMMP_Origins.ml (owners p i at mask         *)
(* EL i c1092wc_code, side l; WallContext p mmmp is C1092MMPE_CTX; near is   *)
(* C1092MSS_NEAR).  OpenSquares are 5-tuples with explicit invariants;       *)
(* clockwise (c,s,u,v,a) = (c,s,--v-a,u,a) (C1092MEA_INSIDE_CLOCKWISE);      *)
(* Normal is c977cc_normal; NortheastCore is c1092mtfen_core; NorthwestCore  *)
(* is c1092mtfnp_core; SoutheastActual c1092mtfes_actual; Southeast          *)
(* C1092TF_southeast; PositiveActual c1092mnas_pos.  C1092MMMMFirstPair.     *)
(* positive_support C1092MFP_POSITIVE_SUPPORT; C1092MMMMPairScalars.         *)
(* small_of_support C1092MPS_SMALL_OF_SUPPORT; southeast_caps                *)
(* C1092MTFF_SOUTHEAST_CAPS; the NorthwestGeometry lemmas C1092MTFNW_*;      *)
(* northwest_center / northwest_diagonal / left tip C1092MPC_*; northwest_   *)
(* left C1092MO_NORTHWEST_LEFT; northwest_pair C1092MMPE_NORTHWEST_PAIR;     *)
(* C1092MMMPLeftFar.point C1092MLF_POINT; northeast_core                     *)
(* C1092MTFEN_NORTHEAST_CORE.  Tag C1092MTFNP_.                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_TwoFifthsEntranceNorthwestGeometry.ml";;
needs "n12/geometry/CP_C1092_MMMP_TwoFifthsEntranceRight.ml";;
needs "n12/geometry/CP_C1092_MMMMFirstPair.ml";;
needs "n12/geometry/CP_C1092_MMMMPairScalars.ml";;

let C1092MTFNP_LIN = NLIN_TAC ~deg2:false [];;
let C1092MTFNP_FACT t tac = SUBGOAL_THEN t ASSUME_TAC THENL [tac; ALL_TAC];;
let C1092MTFNP_MUL_TAC =
  (MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC THEN RASM_ARITH_TAC;;
let C1092MTFNP_CLOSE_TAC =
  REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; REFL_TAC; RASM_ARITH_TAC];;
(* the four strict inequalities of a linside assumption *)
let C1092MTFNP_OPEN_TAC tm =
  MP_TAC (ASSUME tm) THEN REWRITE_TAC[linside] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN STRIP_TAC;;

(* Lean: negative_northwest_profile *)
let C1092MTFNP_NEGATIVE_NORTHWEST_PROFILE = prove
 (`forall cW sW uW vW aW cN sN uN vN aN.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     &1 < aW /\ aW = aN /\ c977cc_normal cW (--sW) /\
     c1092mtfen_core cN sN uN vN aN /\
     linside cW sW uW vW aW (&0) (&0) /\
     linside cW sW uW vW aW (--(&1 / &2)) (&0) /\
     linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
     ~linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\
     ldisj cW sW uW vW aW cN sN uN vN aN
     ==> --sW < &7 / &50 /\ &99 / &100 < cW /\ vW + aW < &25 / &33`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aW:real = aN`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mtfen_core] o
    check (fun th -> concl th = `c1092mtfen_core cN sN uN vN aW`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cW (--sW)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[ldisj] o check (fun th -> concl th =
    `ldisj cW sW uW vW aW cN sN uN vN aW`)) THEN
  C1092MTFNP_FACT `c977cc_normal cN sN`
   (REWRITE_TAC[c977cc_normal] THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_REWRITE_TAC[REAL_POW_2]]) THEN
  C1092MTFNP_OPEN_TAC `linside cW sW uW vW aW (&0) (&0)` THEN
  C1092MTFNP_OPEN_TAC `linside cW sW uW vW aW (--(&1 / &2)) (&0)` THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `--vW - aW`; `uW:real`; `aW:real`;
                `cN:real`; `sN:real`; `--vN - aW`; `uN:real`; `aW:real`] C1092MFP_POSITIVE_SUPPORT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[C1092MEA_INSIDE_CLOCKWISE; ldisj] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) THEN ASM_REWRITE_TAC[] THEN
    C1092MTFNP_CLOSE_TAC;
    DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cW (--sW)`)) THEN
  C1092MTFNP_FACT `&0 < cW` RASM_ARITH_TAC THEN
  C1092MTFNP_FACT `--vW - aW + aW <= &7 / &20 * (cW + --sW)`
   (REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20))` THEN
    REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C1092MTFNP_LIN) THEN
  MP_TAC(SPECL [`cW:real`; `--sW`; `cN:real`; `sN:real`; `aW:real`; `--vW - aW + aW`; `uW + aW`]
    C1092MPS_SMALL_OF_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  C1092MTFNP_FACT `&0 <= (cN - sN) * cW` C1092MTFNP_MUL_TAC THEN
  C1092MTFNP_FACT `&0 <= sN * (cW - --sW)` C1092MTFNP_MUL_TAC THEN
  C1092MTFNP_FACT `&0 <= cN * cW + sN * sW` C1092MTFNP_LIN THEN
  C1092MTFNP_FACT `(cN * cW + sN * sW) * (uW + aW) + (sN * cW - cN * sW) * (vW + aW)
                   <= cN + sN - aW` C1092MTFNP_LIN THEN
  C1092MTFNP_FACT `&0 < sN * (&4 * sN - &1 - cN)` C1092MTFNP_MUL_TAC THEN
  C1092MTFNP_FACT `&0 < (&1 + cN) * (&4 - &4 * cN - sN)` (NLIN_TAC []) THEN
  C1092MTFNP_FACT `&0 < &4 - &4 * cN - sN`
   (REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MTFNP_FACT `(&1 + cN) * (&4 - &4 * cN - sN) <= &0`
      (REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= x * --y`] THEN C1092MTFNP_MUL_TAC) THEN
    C1092MTFNP_LIN) THEN
  C1092MTFNP_FACT `&0 <= (cN * cW + sN * sW) * (uW + aW)` C1092MTFNP_MUL_TAC THEN
  C1092MTFNP_FACT `&0 <= (cN * --sW) * (vW + aW)`
   (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [C1092MTFNP_MUL_TAC; RASM_ARITH_TAC]) THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092MTFNP_FACT `&0 < (cW - &99 / &100) * (vW + aW)` C1092MTFNP_MUL_TAC THEN
  C1092MTFNP_FACT `&3 / &4 < cW * (vW + aW)` C1092MTFNP_LIN THEN
  C1092MTFNP_FACT `&0 < sN * (cW * (vW + aW) - &3 / &4)` C1092MTFNP_MUL_TAC THEN
  C1092MTFNP_LIN);;

(* Lean: NorthwestCore (structure) *)
let c1092mtfnp_core = new_definition
 `c1092mtfnp_core (cW:real) sW uW vW aW <=>
    c977cc_normal cW sW /\ &8 * sW < &7 * cW /\
    linside cW sW uW vW aW (&0) (&0) /\
    linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
    &23 / &25 < vW + aW /\
    aW - cW + (&2 / &5) * sW <= uW + aW`;;

(* (owners p 7).translated 2 2 at the literal mask, and its plain equivalence *)
let C1092MTFNP_T7 =
  match c1092mo_own 7 with
    [c; s; u; v; a] ->
      [c; s; mk_binop `(-):real->real->real` u
               (mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` c `&2`)
                                                (mk_binop `( * ):real->real->real` s `&2`));
       mk_binop `(-):real->real->real` v
               (mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` (mk_comb(`(--):real->real`, s)) `&2`)
                                                (mk_binop `( * ):real->real->real` c `&2`)); a]
  | _ -> failwith "C1092MTFNP_T7";;
let C1092MTFNP_EQ7 =
  let x = `x:real` and y = `y:real` in
  prove(list_mk_forall([x; y], mk_eq(list_mk_comb(`linside`, C1092MTFNP_T7 @ [x; y]),
          list_mk_comb(`linside`, c1092mo_own 7 @ [`&2 + x`; `&2 + y`]))),
        REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let C1092MTFNP_WV = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `l:real`]
and C1092MTFNP_EV = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `l:real`]
and C1092MTFNP_NV = [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `l:real`];;
let c1092mtfnp_in v x y = list_mk_comb(`linside`, v @ [parse_term x; parse_term y]);;
let c1092mtfnp_act v i =
  let x = `x:real` and y = `y:real` in
  list_mk_forall([x; y], mk_eq(list_mk_comb(`linside`, v @ [x; y]),
    list_mk_comb(`linside`, c1092mo_own i @ [`&2 + x`; `&2 + y`])));;
let C1092MTFNP_ACTW = c1092mtfnp_act C1092MTFNP_WV 7
and C1092MTFNP_ACTE = c1092mtfnp_act C1092MTFNP_EV 5
and C1092MTFNP_ACTN = c1092mtfnp_act C1092MTFNP_NV 6;;

(* add the fact tm, proved from th through the equivalence eq *)
let c1092mtfnp_cf eq tm th =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [REWRITE_TAC[eq] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    (fun g -> try ACCEPT_TAC th g with Failure _ ->
       failwith ("c1092mtfnp_cf: " ^ string_of_term (snd g) ^ " FROM " ^ string_of_term (concl th)));
    ALL_TAC];;
let c1092mtfnp_apart_tac v1 eq1 v2 eq2 i j =
  SUBGOAL_THEN (list_mk_comb(`ldisj`, v1 @ v2)) ASSUME_TAC THENL
   [REWRITE_TAC[ldisj; eq1; eq2] THEN REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC (c1092mo_apart i j);
    ALL_TAC];;

(* Lean: northwest_profile *)
let C1092MTFNP_NORTHWEST_PROFILE = prove
 (parse_term (Printf.sprintf "!%s cE sE uE vE aE cN sN uN vN aN. %s /\\
      cE * cE + sE * sE = &1 /\\ &0 < aE /\\ c1092mtfes_actual %s cE sE uE vE aE /\\
      C1092TF_southeast cE sE uE vE aE /\\ c1092mnas_pos %s cN sN uN vN aN
      ==> ?cW sW uW vW aW. cW * cW + sW * sW = &1 /\\ &0 < aW /\\ aW = l /\\
            (!x y. linside cW sW uW vW aW x y <=> %s) /\\ c1092mtfnp_core cW sW uW vW aW"
    C1092AE_P C1092MTFES_HYPS C1092AE_P C1092AE_P (c1092mmpe_in 7 "&2 + x" "&2 + y")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MMPE_V @ [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`])
    C1092MTFEN_NORTHEAST_CORE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE C1092MO_CODE_CONV o REWRITE_RULE[c1092mnas_pos] o
    check (fun th -> is_comb (concl th) && fst (strip_comb (concl th)) = `c1092mnas_pos`)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE C1092MO_CODE_CONV o REWRITE_RULE[c1092mtfes_actual] o
    check (fun th -> is_comb (concl th) && fst (strip_comb (concl th)) = `c1092mtfes_actual`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aN:real = l`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aE:real = l`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[C1092TF_southeast] o
    check (fun th -> is_comb (concl th) && fst (strip_comb (concl th)) = `C1092TF_southeast`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cE sE`)) THEN
  let near = CONV_RULE C1092MO_CODE_CONV (ASSUME (parse_term C1092MSS_NEAR)) in
  let nwc = c1092mo_use C1092MPC_NORTHWEST_CENTER and nwl = c1092mo_use C1092MO_NORTHWEST_LEFT
  and nwp = c1092mo_use C1092MMPE_NORTHWEST_PAIR and nwd = c1092mo_use C1092MPC_NORTHWEST_DIAGONAL
  and far = c1092mo_use C1092MLF_POINT
  and tip = CONV_RULE C1092MO_CODE_CONV (MP (SPECL C1092MMPE_V C1092MPC_LEFT_TIP) (ASSUME C1092MO_CTX)) in
  let actW = ASSUME C1092MTFNP_ACTW and actE = ASSUME C1092MTFNP_ACTE and actN = ASSUME C1092MTFNP_ACTN in
  MP_TAC(MP (SPECL C1092MTFNP_T7 CLF_CANONICAL_FRAME)
            (CONJ (c1092mo_punit 7 C1092MTFNP_T7) (c1092mo_pos ()))) THEN
  DISCH_THEN(X_CHOOSE_THEN `cW:real` (X_CHOOSE_THEN `sW:real` (X_CHOOSE_THEN `uW:real`
    (X_CHOOSE_THEN `vW:real` (X_CHOOSE_THEN `aW:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (find_term ((=) `lclosed`)) (concl th))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = l`)) THEN
  SUBGOAL_THEN C1092MTFNP_ACTW ASSUME_TAC THENL
   [REWRITE_TAC[GSYM C1092MTFNP_EQ7] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o check (fun th -> is_forall (concl th)));
    ALL_TAC] THEN
  ASSUME_TAC (c1092mo_side ()) THEN ASSUME_TAC (c1092mo_pos ()) THEN
  let wv = C1092MTFNP_WV and ev = C1092MTFNP_EV in
  c1092mtfnp_cf actW (c1092mtfnp_in wv "&0" "&0") nwc THEN
  c1092mtfnp_cf actW (c1092mtfnp_in wv "--(&1 / &2)" "&0") nwl THEN
  c1092mtfnp_cf actW (c1092mtfnp_in wv "--(&13 / &50)" "&0") (CONJUNCT2 nwp) THEN
  c1092mtfnp_cf actW (c1092mtfnp_in wv "&0" "&13 / &50") (CONJUNCT1 nwp) THEN
  c1092mtfnp_cf actW (c1092mtfnp_in wv "--(&1 / &2)" "&1 / &2") nwd THEN
  c1092mtfnp_cf actW (c1092mtfnp_in wv "--(&7 / &20)" "&7 / &20") (c1092mo_seed 7 (`&33 / &20`, `&47 / &20`)) THEN
  c1092mtfnp_cf actW (mk_neg (c1092mtfnp_in wv "--(&7 / &20)" "--(&7 / &20)"))
    (c1092mo_excl 7 4 (c1092mo_seed 4 (`&33 / &20`, `&33 / &20`))) THEN
  c1092mtfnp_cf actW (mk_neg (c1092mtfnp_in wv "&7 / &20" "&7 / &20"))
    (c1092mo_excl 7 6 (c1092mo_seed 6 (`&47 / &20`, `&47 / &20`))) THEN
  c1092mtfnp_cf actW (mk_neg (c1092mtfnp_in wv "--(&1)" "&39 / &100")) (c1092mo_excl 7 8 tip) THEN
  c1092mtfnp_cf actW (mk_neg (c1092mtfnp_in wv "--(&1)" "&2 / &5")) (c1092mo_excl 7 8 far) THEN
  c1092mtfnp_cf actE (c1092mtfnp_in ev "&7 / &20" "--(&7 / &20)") (c1092mo_seed 5 (`&47 / &20`, `&33 / &20`)) THEN
  c1092mtfnp_cf actE (mk_neg (c1092mtfnp_in ev "&0" "&0")) (c1092mo_excl 5 7 nwc) THEN
  c1092mtfnp_cf actE (mk_neg (c1092mtfnp_in ev "&1" "--(&13 / &50)")) (c1092mo_excl 5 10 near) THEN
  c1092mtfnp_apart_tac ev actE wv actW 5 7 THEN
  c1092mtfnp_apart_tac wv actW C1092MTFNP_NV actN 7 6 THEN
  MP_TAC(SPECL ev C1092MTFF_SOUTHEAST_CAPS) THEN
  ANTS_TAC THENL [C1092MTFNP_CLOSE_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL ev C1092MTFNW_SOUTHEAST_HEIGHT) THEN
  ANTS_TAC THENL [C1092MTFNP_CLOSE_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < sW` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `c977cc_normal cW (--sW)` ASSUME_TAC THENL
     [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
      UNDISCH_TAC `abs sW <= cW` THEN UNDISCH_TAC `sW <= &0` THEN
      UNDISCH_TAC `cW * cW + sW * sW = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL (wv @ C1092MTFNP_NV) C1092MTFNP_NEGATIVE_NORTHWEST_PROFILE) THEN
    ANTS_TAC THENL [C1092MTFNP_CLOSE_TAC; STRIP_TAC] THEN
    MP_TAC(SPECL (ev @ wv) C1092MTFNW_NEGATIVE_NORTHWEST_IMPOSSIBLE) THEN
    ANTS_TAC THENL [C1092MTFNP_CLOSE_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_normal cW sW` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs sW <= cW` THEN UNDISCH_TAC `&0 < sW` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL wv C1092MTFNW_POSITIVE_NORTHWEST_FACES) THEN
  ANTS_TAC THENL [C1092MTFNP_CLOSE_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL (ev @ wv) C1092MTFNW_POSITIVE_NORTHWEST_HEIGHT) THEN
  ANTS_TAC THENL [C1092MTFNP_CLOSE_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL wv C1092MTFNW_POSITIVE_NORTHWEST_LEFT_FACE) THEN
  ANTS_TAC THENL [C1092MTFNP_CLOSE_TAC; DISCH_TAC] THEN
  MAP_EVERY EXISTS_TAC wv THEN REWRITE_TAC[c1092mtfnp_core] THEN
  CONV_TAC C1092MO_CODE_CONV THEN C1092MTFNP_CLOSE_TAC);;
