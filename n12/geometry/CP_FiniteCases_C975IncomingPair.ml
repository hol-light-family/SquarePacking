(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C975IncomingPair.lean.            *)
(* The original C975 incoming branch.  owner p m is the 5-tuple (ooc .. m)  *)
(* (oos .. m) (oou .. m) (oov .. m) l; auxiliaries p m is ooaux .. m;        *)
(* natAuxOwners p 1 (ownerIndex p m) is auxown 1 (c1 (oidx ..)) .. l.        *)
(* Private helpers: close = LINSIDE_CLOSED, positive = C975IP_POSITIVE       *)
(* (squares A = cA .., B = cB ..; unit normals and positive sides explicit), *)
(* seed_point / aux_inside / foreign = oo_seed / oo_aux_point /              *)
(* C975IC_FOREIGN_TAC.  C849PositiveAbove.b_lower_face: C849PA_B_LOWER_FACE; *)
(* PositiveBLeftReduction.upper_left_marker_modes:                           *)
(* PBLR_UPPER_LEFT_MARKER_MODES; ClosedFrames.positive_frame /               *)
(* canonical_frame: CLF_POSITIVE_FRAME / CLF_CANONICAL_FRAME;                *)
(* C849ShallowAB.in_frame: C849SHAB_IN_FRAME; C849SteepAB.in_frame:          *)
(* C849SAB_IN_FRAME; C849Negative.impossible: C849N_IMPOSSIBLE;              *)
(* C1092MixedSpan.impossible: C1092MS_IMPOSSIBLE (Transform true true false  *)
(* pull = pullSwap (pullX q)); C975IncomingCut: C975IC_*.  Tag C975IP_.      *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C975IncomingCut.ml";;
needs "n12/geometry/C849Negative.ml";;
needs "n12/geometry/C849Positive.ml";;
needs "n12/geometry/C849PositiveAbove.ml";;
needs "n12/geometry/PositiveBLeftReduction.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/C849ShallowAB.ml";;
needs "n12/geometry/C849SteepAB.ml";;
needs "n12/geometry/CP_C1092_MixedSpan.ml";;

let C975IP_HIGH_SLOPE = prove
 (`forall c s. c * c + s * s = &1 /\ &50 / &63 < c /\ &0 <= s ==> s <= (&4 / &5) * c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  NLIN_TAC []);;

(* Lean: positive (private) *)
let C975IP_POSITIVE = prove
 (`forall cA sA uA vA aA cB sB uB vB aB.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &0 < cB /\ &0 <= sB /\ sB <= cB /\ aA = aB /\ &1 < aB /\
     lclosed cA sA uA vA aA (&2) (&113 / &50) /\ lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\ linside cA sA uA vA aA (&2) (&5 / &2) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&3) (&12 / &5) /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\ lclosed cB sB uB vB aB (&8 / &5) (&3) /\
     linside cB sB uB vB aB (&2) (&1543 / &500) /\
     ~linside cB sB uB vB aB (&113 / &50) (&3) /\ ~linside cB sB uB vB aB (&1) (&3) /\
     ldisj cA sA uA vA aA cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = aB`)) THEN
  SUBGOAL_THEN `~linside cB sB uB vB aB (&2) (&5 / &2)` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cA sA uA vA aB cB sB uB vB aB` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&2`; `&5 / &2`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C849PA_B_LOWER_FACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&3 * cB <= &7 * sB` ASSUME_TAC THENL
   [UNDISCH_TAC `lclosed cB sB uB vB aB (&33 / &20) (&47 / &20)` THEN
    UNDISCH_TAC `-- &2 * sB + (&5 / &2) * cB <= vB` THEN
    REWRITE_TAC[lclosed] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`] CLF_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cP:real` (X_CHOOSE_THEN `sP:real` (X_CHOOSE_THEN `uP:real`
    (X_CHOOSE_THEN `vP:real` (X_CHOOSE_THEN `aP:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aP:real = aB`)) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] PBLR_UPPER_LEFT_MARKER_MODES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ldisj cP sP uP vP aB cB sB uB vB aB` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cA sA uA vA aB cB sB uB vB aB` THEN ASM_REWRITE_TAC[ldisj]; ALL_TAC] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [SUBGOAL_THEN `uB + aB <= (&113 / &50) * cB + &3 * sB` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      UNDISCH_TAC `~linside cB sB uB vB aB (&113 / &50) (&3)` THEN REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`lclosed cB sB uB vB aB (&8 / &5) (&3)`;
        `lclosed cB sB uB vB aB (&33 / &20) (&47 / &20)`; `linside cB sB uB vB aB (&2) (&1543 / &500)`] THEN
      REWRITE_TAC[linside; lclosed] THEN RASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&50 / &63 < cB` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`] C975IP_HIGH_SLOPE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC C849SHAB_IN_FRAME THEN
    MAP_EVERY EXISTS_TAC [`cP:real`; `sP:real`; `uP:real`; `vP:real`; `aB:real`;
                          `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC C849SAB_IN_FRAME THEN
    MAP_EVERY EXISTS_TAC [`cP:real`; `sP:real`; `uP:real`; `vP:real`; `aB:real`;
                          `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Packing-level part.                                                        *)
(* ------------------------------------------------------------------------- *)

let C975IP_HAVE tm tac = SUBGOAL_THEN tm ASSUME_TAC THENL [tac; ALL_TAC];;
let C975IP_POS m x y ths =
  C975IP_HAVE (c975ic_own m x y) (FIRST [ASM_SIMP_TAC ths THEN NO_TAC; ASM_REWRITE_TAC C975IC_AUXPTS]);;
let C975IP_NEG m x y fors =
  C975IP_HAVE (mk_neg (c975ic_own m x y))
    (FIRST (map (fun (n, th) -> C975IC_FOREIGN_TAC n th) fors));;

let C975IP_SEED_TL = c975ic_seed 34816 (`&2`, `&1543 / &500`);;
let C975IP_SW = c975ic_seed 256 (`&33 / &20`, `&33 / &20`);;
let C975IP_L_MARKER = c975ic_seed 4096 (`&457 / &500`, `&2`);;
let C975IP_L_HIGH = c975ic_aux 4096 11;;
let C975IP_L_SEED = c975ic_seed 2 (`&19 / &25`, `&187 / &100`);;
let C975IP_E_P = c975ic_seed 192 (`&1`, `&1543 / &500`);;
let C975IP_E_Q = c975ic_seed 192 (`&457 / &500`, `&3`);;
let C975IP_E_CORNER = c975ic_seed 192 (`&1`, `&3`);;

(* frame of owner m: X_CHOOSE the canonical frame (c s u v a names given) *)
let C975IP_FRAME_TAC m names =
  let [c; s; u; v; a] = map (fun n -> mk_var(n, `:real`)) names in
  MP_TAC (SPECL (c975ic_owner m) CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OO_UNIT] THEN MP_TAC (SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN c (X_CHOOSE_THEN s (X_CHOOSE_THEN u (X_CHOOSE_THEN v
    (X_CHOOSE_THEN a STRIP_ASSUME_TAC)))));;

let C975IP_SIDE_TAC aparts =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         ASM_REWRITE_TAC[] THEN NO_TAC;
         ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LINSIDE_CLOSED THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         ASM_SIMP_TAC[OO_UNIT; OO_BOX] THEN NO_TAC;
         REWRITE_TAC[lcont] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM lcont] THEN ASM_SIMP_TAC[OO_BOX] THEN NO_TAC;
         REWRITE_TAC[ldisj] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM ldisj] THEN ASM_SIMP_TAC aparts THEN NO_TAC;
         MP_TAC (SPEC_ALL OO_SIDE) THEN MP_TAC (SPEC_ALL OO_SIDE_LE) THEN ASM_REWRITE_TAC[] THEN
         RASM_ARITH_TAC];;

(* Lean: incoming_forces_top_seven *)
let C975IP_INCOMING_FORCES_TOP_SEVEN = prove
 (c975ic_stmt [mk_conj(c975ic_mem 5 1024, c975ic_mem 16 1024)] (c975ic_mem 17 34816),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC (c975ic_mem 17 34816) THEN ASM_REWRITE_TAC[] THEN
  C975IC_COMPULSORY_TAC THEN
  MP_TAC (SPEC_ALL C975IC_TOP_LEFT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C975IP_POS 1024 `&2` `&113 / &50` [] THEN
  C975IP_POS 1024 `&113 / &50` `&2` [] THEN
  C975IP_POS 1024 `&47 / &20` `&47 / &20` [C975IC_NE_MARKER] THEN
  C975IP_POS 1024 `&2` `&5 / &2` [C975IC_INCOMING_HIGH] THEN
  C975IP_POS 34816 `&33 / &20` `&47 / &20` [C975IC_NW_MARKER] THEN
  C975IP_POS 34816 `&8 / &5` `&3` [] THEN
  C975IP_POS 34816 `&2` `&1543 / &500` [C975IP_SEED_TL] THEN
  C975IP_HAVE (mk_neg (c975ic_own 34816 `&113 / &50` `&3`)) (ASM_REWRITE_TAC C975IC_AUXPTS) THEN
  C975IP_NEG 1024 `&47 / &20` `&33 / &20` [512, C975IC_SE_MARKER] THEN
  C975IP_NEG 1024 `&33 / &20` `&47 / &20` [34816, C975IC_NW_MARKER] THEN
  C975IP_NEG 1024 `&3` `&12 / &5` [16384, C975IC_R_HIGH] THEN
  C975IP_NEG 34816 `&1` `&3` [192, C975IP_E_CORNER] THEN
  C975IP_NEG 34816 `&2` `&5 / &2` [1024, C975IC_INCOMING_HIGH] THEN
  C975IP_POS 4096 `&457 / &500` `&2` [C975IP_L_MARKER] THEN
  C975IP_POS 4096 `&1` `&12 / &5` [C975IP_L_HIGH] THEN
  C975IP_NEG 4096 `&19 / &25` `&187 / &100` [2, C975IP_L_SEED] THEN
  C975IP_NEG 4096 `&33 / &20` `&33 / &20` [256, C975IP_SW] THEN
  C975IP_POS 192 `&1` `&1543 / &500` [C975IP_E_P] THEN
  C975IP_POS 192 `&457 / &500` `&3` [C975IP_E_Q] THEN
  C975IP_FRAME_TAC 34816 ["cB"; "sB"; "uB"; "vB"; "aB"] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aB:real = l`)) THEN
  ASM_CASES_TAC `&0 <= sB` THENL
   [MATCH_MP_TAC (SPECL (c975ic_owner 1024 @ [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `l:real`])
                    C975IP_POSITIVE) THEN
    REPEAT CONJ_TAC THEN C975IP_SIDE_TAC [oo_apart C975D_F 1024 34816];
    C975IP_FRAME_TAC 4096 ["cL"; "sL"; "uL"; "vL"; "aL"] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aL:real = l`)) THEN
    MATCH_MP_TAC (SPECL ([`cB:real`; `sB:real`; `uB:real`; `vB:real`; `l:real`;
                          `cL:real`; `sL:real`; `uL:real`; `vL:real`; `l:real`] @ c975ic_owner 192)
                    C849N_IMPOSSIBLE) THEN
    REPEAT CONJ_TAC THEN C975IP_SIDE_TAC [oo_apart C975D_F 34816 4096; oo_apart C975D_F 34816 192]]);;

(* Lean: missing_ne_seven_forces_incoming *)
let C975IP_MISSING_NE_SEVEN_FORCES_INCOMING = prove
 (c975ic_stmt [mk_neg (c975ic_mem 17 1024)] (mk_conj(c975ic_mem 5 1024, c975ic_mem 16 1024)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C975IC_COMPULSORY_TAC THEN
  C975IC_BY_TAC (c975ic_mem 16 1024)
    [mk_disj(c975ic_mem 16 1024, c975ic_mem 17 1024); mk_neg (c975ic_mem 17 1024)] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC (c975ic_mem 5 1024) THEN ASM_REWRITE_TAC[] THEN
  C975IC_BY_TAC (c975ic_mem 7 1024)
    [mk_disj(c975ic_mem 5 1024, c975ic_mem 7 1024); mk_neg (c975ic_mem 5 1024)] THEN
  C975IC_CONTRA_TAC C1092MS_IMPOSSIBLE (c975ic_pull [`s:real`; `c:real`; `u:real`; `--v - a`; `a:real`]
                                         (c975ic_pullx (c975ic_owner 1024)))
    [] [16384, C975IC_R_HIGH; 16384, c975ic_aux 16384 9]);;

(* Lean: top_seven_forces_incoming *)
let C975IP_TOP_SEVEN_FORCES_INCOMING = prove
 (c975ic_stmt [c975ic_mem 17 34816] (mk_conj(c975ic_mem 5 1024, c975ic_mem 16 1024)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C975IP_MISSING_NE_SEVEN_FORCES_INCOMING THEN
  ASM_REWRITE_TAC[] THEN OO_EXCLUDE_ALL_TAC C975D_F 1024 THEN ASM_REWRITE_TAC[]);;

(* Lean: dichotomy *)
let C975IP_DICHOTOMY = prove
 (c975ic_stmt []
   (mk_disj(mk_conj(mk_conj(c975ic_mem 5 1024, c975ic_mem 16 1024), c975ic_mem 17 34816),
            list_mk_conj [c975ic_mem 17 1024; mk_eq(c975ic_gown 34816, `{4}`); mk_neg (c975ic_mem 7 34816)])),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC (c975ic_mem 17 1024) THENL
   [DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN OO_EXCLUDE_ALL_TAC C975D_F 34816 THEN
    MP_TAC (SPEC_ALL C975IC_TOP_G_OPTIONS) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC (SPEC_ALL C975IC_TOP_SEVEN_INCOMING) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC (SPEC_ALL C975IP_INCOMING_FORCES_TOP_SEVEN) THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC (mk_eq(c975ic_gown 34816, `{4,7}`)) THEN
      REWRITE_TAC[EXTENSION; C975E_G_COMBINED] THEN DISCH_THEN(MP_TAC o SPEC `7`) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]];
    DISJ1_TAC THEN
    MP_TAC (SPEC_ALL C975IP_MISSING_NE_SEVEN_FORCES_INCOMING) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC C975IP_INCOMING_FORCES_TOP_SEVEN THEN ASM_REWRITE_TAC[]]);;
