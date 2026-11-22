(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeRecipientWall.lean           *)
(* (namespace N12Compact.C1092MPPMNegativeRecipientWall; Lean header:        *)
(* "Source only, uncompiled").  NEGATIVE-MISSING-POSITIVE-ENDING Theorem 1:  *)
(* a negative recipient E strictly owning the origin (0,-1) forces the same  *)
(* negative boundary B beyond slope 1/4.  Squares E = cE sE uE vE aE and     *)
(* B = cB sB uB vB aB.  Input: c1092nrw_input; Normal: c977cc_normal;        *)
(* BoundaryFaces (MissingBoundaryShallow): c1092mbsg_boundary_faces;         *)
(* upper / lower: ABT_upper / ABT_lower; ownV: ABT_OWNV; strict_bounds of a  *)
(* point: ABT_STRICT_BOUNDS; signed_axes: C1092SPTS_SIGNED_AXES;             *)
(* upper_pos_pos: C1092TFSU_UPPER_POS_POS; lower_np: C1092WS_LOWER_NP;       *)
(* affine_endpoint_nonnegative: SCAP_AFFINE_ENDPOINT_NONNEG;                 *)
(* Scalars.upward_margin / boundary_margin: C1092NRWS_UPWARD_MARGIN /        *)
(* C1092NRWS_BOUNDARY_MARGIN.  Tag C1092NRW_.                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeRecipientWallScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingBoundaryShallowGeometry.ml";;
needs "n12/geometry/CP_C1092_MPPMSteepPositiveThreeSquareData.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;

(* Lean: Input (structure) *)
let c1092nrw_input = new_definition
 `c1092nrw_input cE sE uE vE aE cB sB uB vB aB <=>
    &1 < aE /\ aE = aB /\
    c977cc_normal cE (--sE) /\ c977cc_normal cB (--sB) /\ &0 < --sB /\
    linside cE sE uE vE aE (&0) (--(&1)) /\
    --(&13 / &50) * sE <= uE /\
    vE + aE <= --sE - (&14 / &25) * cE /\
    (&7 / &10 < cE /\ cE < &33 / &40 /\ &283 / &500 < --sE /\ --sE < &71 / &100 /\
     &139 / &100 < cE - sE) /\
    linside cB sB uB vB aB (&0) (--(&543) / &500) /\
    linside cB sB uB vB aB (--(&13) / &50) (--(&1)) /\
    ~linside cB sB uB vB aB (--(&1)) (--(&543) / &500) /\
    (forall x y. linside cB sB uB vB aB x y ==> --(&2) <= y) /\
    ldisj cB sB uB vB aB cE sE uE vE aE`;;

let C1092NRW_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

(* Lean: boundary_faces *)
let C1092NRW_BOUNDARY_FACES = prove
 (`forall cE sE uE vE aE cB sB uB vB aB.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092nrw_input cE sE uE vE aE cB sB uB vB aB
     ==> c1092mbsg_boundary_faces cB sB uB vB aB`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092nrw_input; c1092mbsg_boundary_faces] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `--sB`] C1092MBS_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~linside cB sB uB vB aB (&0) (--(&1))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `ldisj cB sB uB vB aB cE sE uE vE aE` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&0`; `--(&1)`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun t -> MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside cB sB uB vB aB (&0) (--(&543) / &500)`;
    `linside cB sB uB vB aB (--(&13) / &50) (--(&1))`] THEN
  SUBGOAL_THEN `vB + aB <= --cB` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092NRW_MISS_TAC `~linside cB sB uB vB aB (&0) (--(&1))`; ALL_TAC] THEN
  SUBGOAL_THEN `vB < sB - (&543 / &500) * cB` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--cB - (&543 / &500) * sB <= uB` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092NRW_MISS_TAC `~linside cB sB uB vB aB (--(&1)) (--(&543) / &500)`; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 + sB * (uB + aB) + cB * vB` ASSUME_TAC THENL
   [MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
    MAP_EVERY EXISTS_TAC [`aB:real`; `cB - sB`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`cB * (uB + aB - t) - sB * (vB + t)`; `sB * (uB + aB - t) + cB * (vB + t)`] o
     check (fun th -> is_forall(concl th) &&
                      length(fst(strip_forall(concl th))) = 2 &&
                      is_imp(snd(strip_forall(concl th))))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[linside] THEN
      SUBGOAL_THEN
       `cB * (cB * (uB + aB - t) - sB * (vB + t)) + sB * (sB * (uB + aB - t) + cB * (vB + t)) =
        uB + aB - t /\
        --sB * (cB * (uB + aB - t) - sB * (vB + t)) + cB * (sB * (uB + aB - t) + cB * (vB + t)) =
        vB + t` (fun th -> REWRITE_TAC[th]) THENL
       [CONJ_TAC THEN UNDISCH_TAC `cB * cB + sB * sB = &1` THEN CONV_TAC REAL_RING;
        RASM_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

let C1092NRW_CONE_TAC : tactic = fun (asl,w as g) ->
  let is_sep tm =
    try let l,_ = dest_binary "real_le" tm in
        fst(dest_const(fst(strip_comb l))) = "ABT_upper"
    with _ -> false in
  let sep = concl(snd(find (fun (_,th) -> is_sep(concl th)) asl)) in
  let args = snd(strip_comb(lhand sep)) in
  let nx = el 5 args and ny = el 6 args in
  let cone = snd(find (fun (_,th) -> is_forall(concl th) &&
                   can (find_term (fun t -> try fst(dest_const t) = "ABT_upper" with _ -> false))
                       (concl th)) asl) in
  (MP_TAC(SPECL [nx; ny] cone) THEN ANTS_TAC THENL
    [CONJ_TAC THENL [REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
     STRIP_TAC THEN RASM_ARITH_TAC]) g;;

(* Lean: sources (private) *)
let C1092NRW_SOURCES = prove
 (`forall cE sE uE vE aE cB sB uB vB aB.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092nrw_input cE sE uE vE aE cB sB uB vB aB
     ==> ABT_upper cB sB uB vB aB (--sE) cE <= vE \/
         ABT_upper cB sB uB vB aB (--sB) cB <= ABT_lower cE sE uE vE aE (--sB) cB`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092nrw_input] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aE:real = aB`)) THEN
  MP_TAC(SPECL [`cE:real`; `--sE`] C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`cB:real`; `--sB`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `forall nx ny. nx pow 2 + ny pow 2 = &1 /\
            ABT_upper cB sB uB vB aB nx ny <= ABT_lower cE sE uE vE aB nx ny
            ==> &0 < nx /\ &0 < ny`
   ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aB:real`;
                  `&0`; `--(&1)`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                  `--(&13) / &50`; `--(&1)`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                  `&0`; `--(&543) / &500`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
    UNDISCH_TAC `ABT_upper cB sB uB vB aB nx ny <= ABT_lower cE sE uE vE aB nx ny` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ABT_lower cE sE uE vE aB (--sE) cE = vE`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) THENL
   [MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aB:real`] ABT_OWNV) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aB:real`] C1092SPTS_SIGNED_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN (FIRST_ASSUM(fun th -> (DISJ1_TAC THEN ACCEPT_TAC th) ORELSE (DISJ2_TAC THEN ACCEPT_TAC th))
                       ORELSE C1092NRW_CONE_TAC));;

(* Lean: steep *)
let C1092NRW_STEEP = prove
 (`forall cE sE uE vE aE cB sB uB vB aB.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092nrw_input cE sE uE vE aE cB sB uB vB aB
     ==> cB < &4 * --sB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092NRW_SOURCES) THEN MP_TAC(SPEC_ALL C1092NRW_BOUNDARY_FACES) THEN
  ASM_REWRITE_TAC[c1092mbsg_boundary_faces] THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092nrw_input] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "c1092nrw_input"
                     with _ -> false)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aE:real = aB`)) THEN
  MP_TAC(SPECL [`cE:real`; `--sE`] C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`cB:real`; `--sB`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&2 * cE < &3 * --sE` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cE * cB /\ &0 < --sE * --sB /\ &0 < cB * (&3 * --sE - &2 * cE) /\
                &0 <= cE * (cB - &4 * --sB)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    (MATCH_MP_TAC REAL_LT_MUL ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cE * cB + --sE * --sB` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < --sE * cB - cE * --sB` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < cE * cB`; `&0 < cB * (&3 * --sE - &2 * cE)`;
                           `&0 <= cE * (cB - &4 * --sB)`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `vE < --cE` ASSUME_TAC THENL
   [UNDISCH_TAC `linside cE sE uE vE aB (&0) (--(&1))` THEN REWRITE_TAC[linside] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(&543 / &500) * cB < vB + aB` ASSUME_TAC THENL
   [UNDISCH_TAC `linside cB sB uB vB aB (&0) (--(&543) / &500)` THEN REWRITE_TAC[linside] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [(* recipient source *)
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `--sE`; `cE:real`;
                  `--sE * cB - cE * --sB`; `cE * cB + --sE * --sB`] C1092TFSU_UPPER_POS_POS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN RASM_ARITH_TAC;
      DISCH_TAC] THEN
    SUBGOAL_THEN
     `cB * ABT_upper cB sB uB vB aB (--sE) cE =
      (cE * cB + --sE * --sB) * (cB * (vB + aB) - --sB * (uB + aB)) + --sE * (uB + aB)`
     ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cB * cB + sB * sB = &1` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(cE * cB + --sE * --sB) * (--sB * (uB + aB) - cB * (vB + aB)) <=
      (cE * cB + --sE * --sB) * (&2 - aB * cB) /\
      --sE * (aB - cB + (&543 / &500) * --sB) <= --sE * (uB + aB)`
     STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`cE:real`; `--sE`; `cB:real`; `--sB`] C1092NRWS_UPWARD_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `&0 < (aB - &1) * (cB * (cE * cB + --sE * --sB) + --sE)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_ADD THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL; ALL_TAC] THEN
      RASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `cB * ABT_upper cB sB uB vB aB (--sE) cE <= cB * vE /\
                  cB * vE < cB * --cE` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL; MATCH_MP_TAC REAL_LT_LMUL] THEN
      RASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`cB * ABT_upper cB sB uB vB aB (--sE) cE =
       (cE * cB + --sE * --sB) * (cB * (vB + aB) - --sB * (uB + aB)) + --sE * (uB + aB)`;
      `(cE * cB + --sE * --sB) * (--sB * (uB + aB) - cB * (vB + aB)) <=
       (cE * cB + --sE * --sB) * (&2 - aB * cB)`;
      `--sE * (aB - cB + (&543 / &500) * --sB) <= --sE * (uB + aB)`;
      `&0 < (aB - &1) * (cB * (cE * cB + --sE * --sB) + --sE)`;
      `cB * ABT_upper cB sB uB vB aB (--sE) cE <= cB * vE`; `cB * vE < cB * --cE`] THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    (* boundary source *)
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] ABT_OWNV) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
      `ABT_upper cB sB uB vB aB (--sB) cB <= ABT_lower cE sE uE vE aB (--sB) cB`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aB:real`; `--sB`; `cB:real`;
                  `--(--sE * cB - cE * --sB)`; `cE * cB + --sE * --sB`] C1092WS_LOWER_NP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN RASM_ARITH_TAC;
      DISCH_TAC] THEN
    SUBGOAL_THEN
     `(--sE * cB - cE * --sB) * ((&13 / &50) * --sE) <= (--sE * cB - cE * --sB) * uE /\
      (cE * cB + --sE * --sB) * (vE + aB) <= (cE * cB + --sE * --sB) * (--sE - (&14 / &25) * cE)`
     STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`cE:real`; `--sE`; `cB:real`; `--sB`] C1092NRWS_BOUNDARY_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `&0 < (aB - &1) * ((cE * cB + --sE * --sB) + (--sE * cB - cE * --sB))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`ABT_lower cE sE uE vE aB (--sB) cB =
       --(--sE * cB - cE * --sB) * (uE + aB) + (cE * cB + --sE * --sB) * vE`;
      `(--sE * cB - cE * --sB) * ((&13 / &50) * --sE) <= (--sE * cB - cE * --sB) * uE`;
      `(cE * cB + --sE * --sB) * (vE + aB) <=
       (cE * cB + --sE * --sB) * (--sE - (&14 / &25) * cE)`;
      `&0 < (aB - &1) * ((cE * cB + --sE * --sB) + (--sE * cB - cE * --sB))`;
      `--(&543 / &500) * cB < vB + aB`;
      `vB + aB <= ABT_lower cE sE uE vE aB (--sB) cB`] THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC]);;
