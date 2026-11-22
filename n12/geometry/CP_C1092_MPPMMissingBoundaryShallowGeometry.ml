(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingBoundaryShallowGeometry.lean  *)
(* (N12Compact.C1092MPPMMissingBoundaryShallow).  Literal actual-square      *)
(* inputs, simultaneous boundary faces and complete separating-axis          *)
(* reduction for MISSING-BOUNDARY-SHALLOW-ANGLE, sections 1--3.  Square C is *)
(* cC sC uC vC aC, square B is cB sB uB vB aB; the structures Input and      *)
(* BoundaryFaces are c1092mbsg_input and c1092mbsg_boundary_faces.  upper / *)
(* lower are ABT_upper / ABT_lower; strict_bounds (of Normal) is             *)
(* C1092MBS_STRICT_BOUNDS; affine_endpoint_nonnegative is                    *)
(* SCAP_AFFINE_ENDPOINT_NONNEG.  Tag C1092MBSG_.                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingBoundaryShallowScalars.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* Lean: Input (structure) *)
let c1092mbsg_input = new_definition
 `c1092mbsg_input cC sC uC vC aC cB sB uB vB aB <=>
    &1 < aC /\ aC = aB /\
    c977cc_normal cC sC /\ &0 < sC /\
    c977cc_normal cB (--sB) /\ &0 < --sB /\
    linside cC sC uC vC aC (--(&1)) (--(&2) / &5) /\
    linside cC sC uC vC aC (--(&13) / &50) (&0) /\
    --cC - sC / &2 <= uC /\
    uC + aC <= &0 /\
    vC + aC <= sC /\
    linside cB sB uB vB aB (&0) (--(&543) / &500) /\
    linside cB sB uB vB aB (--(&13) / &50) (--(&1)) /\
    ~linside cB sB uB vB aB (&0) (--(&1)) /\
    ~linside cB sB uB vB aB (--(&1)) (--(&543) / &500) /\
    (forall x y. linside cB sB uB vB aB x y ==> --(&2) <= y) /\
    ldisj cC sC uC vC aC cB sB uB vB aB`;;

(* Lean: BoundaryFaces (structure) *)
let c1092mbsg_boundary_faces = new_definition
 `c1092mbsg_boundary_faces (cB:real) sB uB vB aB <=>
    vB + aB <= --cB /\
    --cB - (&543 / &500) * sB <= uB /\
    (--sB) * (uB + aB) - cB * (vB + aB) <= &2 - aB * cB`;;

let C1092MBSG_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

(* Lean: boundary_faces *)
let C1092MBSG_BOUNDARY_FACES = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092mbsg_input cC sC uC vC aC cB sB uB vB aB
     ==> c1092mbsg_boundary_faces cB sB uB vB aB`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mbsg_input; c1092mbsg_boundary_faces] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `--sB`] C1092MBS_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside cB sB uB vB aB (&0) (--(&543) / &500)`;
    `linside cB sB uB vB aB (--(&13) / &50) (--(&1))`] THEN
  SUBGOAL_THEN `vB + aB <= --cB` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MBSG_MISS_TAC `~linside cB sB uB vB aB (&0) (--(&1))`; ALL_TAC] THEN
  SUBGOAL_THEN `vB < sB - (&543 / &500) * cB` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--cB - (&543 / &500) * sB <= uB` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MBSG_MISS_TAC `~linside cB sB uB vB aB (--(&1)) (--(&543) / &500)`; ALL_TAC] THEN
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
        ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

(* Lean: cone *)
let C1092MBSG_CONE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092mbsg_input cC sC uC vC aC cB sB uB vB aB /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cB sB uB vB aB nx ny <= ABT_lower cC sC uC vC aC nx ny
     ==> &0 < ny /\ nx < (&30 / &37) * ny`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mbsg_input] THEN STRIP_TAC THEN
  ABT_ALL_SB_TAC
   [[`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`], (`--(&13) / &50`, `--(&1)`);
    [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`], (`--(&13) / &50`, `&0`);
    [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`], (`--(&1)`, `--(&2) / &5`)]
   [`nx:real`, `ny:real`] THEN
  ABT_ARITH_TAC);;

(* Lean: separators *)
let C1092MBSG_SEPARATORS = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092mbsg_input cC sC uC vC aC cB sB uB vB aB
     ==> ABT_upper cB sB uB vB aB (--sC) cC <= ABT_lower cC sC uC vC aC (--sC) cC \/
         ABT_upper cB sB uB vB aB (--cB) (--sB) <= ABT_lower cC sC uC vC aC (--cB) (--sB) \/
         ABT_upper cB sB uB vB aB (--sB) cB <= ABT_lower cC sC uC vC aC (--sB) cB`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mbsg_input] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`] C1092MBS_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cB:real`; `--sB`] C1092MBS_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = aB`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cC sC`)) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cC:real`; `sC:real`; `uC:real`; `vC:real`; `aB:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ldisj cC sC uC vC aB cB sB uB vB aB` THEN
    REWRITE_TAC[ldisj] THEN MESON_TAC[]; ALL_TAC] THEN
  ABT_ALL_SB_TAC
   [[`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`], (`--(&13) / &50`, `--(&1)`);
    [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aB:real`], (`--(&13) / &50`, `&0`);
    [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aB:real`], (`--(&1)`, `--(&2) / &5`)]
   [`cB:real`, `sB:real`; `--sB:real`, `cB:real`; `cC:real`, `sC:real`; `--sC:real`, `cC:real`] THEN
  REWRITE_TAC[OCWPVG_UPPER_NEG; OCWPVG_LOWER_NEG] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  ABT_ARITH_TAC);;
