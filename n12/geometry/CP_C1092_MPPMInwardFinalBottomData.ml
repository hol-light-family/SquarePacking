(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalBottomData.lean           *)
(* (N12Compact.C1092MPPMInwardFinal.BottomAngle; Lean header: "Source only, *)
(* uncompiled").  Literal actual-square inputs of INWARD-BOTTOM-ANGLE.       *)
(* Squares C = cC sC uC vC aC, B = cB sB uB vB aB.  Input is                  *)
(* c1092ifbd_input (its fields in Lean order; side, same, normal first),     *)
(* CentralFaces is c1092ifbd_faces.  Normal: c977cc_normal; lower / upper:  *)
(* ABT_lower / ABT_upper; strict_bounds: ABT_STRICT_BOUNDS;                  *)
(* faceSeparation_of_disjoint: CSAT_FACESEPARATION_OF_DISJOINT; separated,  *)
(* parallel_radius, transverse_radius, ownU, ownV: ABT_*; reverse:           *)
(* OCWPVG_UPPER_NEG / OCWPVG_LOWER_NEG; bottom_center: C1092SBS_BOTTOM_CENTER; *)
(* center_coordinates: LCENTRE_COORDS; affine_endpoint_nonnegative:          *)
(* C977WC_AFFINE_ENDPOINT; inside_iff_rotated_box: TSS_INSIDE_FACE;          *)
(* negative_height: C1092IFBS_NEGATIVE_HEIGHT.  Tag C1092IFBD_.              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalBottomScalars.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;
needs "n12/geometry/CP_C1092_ShallowBoundarySupport.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalSuccessor.ml";;
needs "n12/geometry/C977WallChains.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;

(* Lean: Input (structure) *)
let c1092ifbd_input = new_definition
 `c1092ifbd_input cC sC uC vC aC cB sB uB vB aB <=>
    &1 < aC /\ aC = aB /\ c977cc_normal cC (--sC) /\
    linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
    linside cC sC uC vC aC (&0) (--(&13 / &50)) /\
    linside cC sC uC vC aC (--(&13 / &50)) (&0) /\
    linside cC sC uC vC aC (--(&1 / &2)) (&0) /\
    linside cC sC uC vC aC (--(&1 / &100)) (--(&27 / &50)) /\
    ~linside cC sC uC vC aC (&0) (&0) /\
    ~linside cC sC uC vC aC (--(&1)) (--(&2 / &5)) /\
    linside cB sB uB vB aB (&0) (--(&543 / &500)) /\
    linside cB sB uB vB aB (--(&13 / &50)) (--(&1)) /\
    linside cB sB uB vB aB (--(&14 / &25)) (--(&1)) /\
    (forall x y. linside cB sB uB vB aB x y ==> --(&2) <= y) /\
    lcx cB sB uB vB aB <= &0 /\
    ldisj cC sC uC vC aC cB sB uB vB aB`;;

(* Lean: CentralFaces (structure) *)
let c1092ifbd_faces = new_definition
 `c1092ifbd_faces (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    s < &0 /\ v + a <= &0 /\ --c - (&2 / &5) * s <= u /\ u < --c / &2`;;

let C1092IFBD_HYP =
  "cC * cC + sC * sC = &1 /\\ &0 < aC /\\ cB * cB + sB * sB = &1 /\\ &0 < aB /\\ " ^
  "c1092ifbd_input cC sC uC vC aC cB sB uB vB aB";;
let C1092IFBD_VARS = "cC sC uC vC aC cB sB uB vB aB";;

let C1092IFBD_OPEN_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifbd_input] o
    check (can (term_match [] `c1092ifbd_input a b c d e f g h i j`) o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  C1092PRS_NORMAL_TAC;;

let C1092IFBD_PT_TAC tms =
  MAP_EVERY (fun t -> UNDISCH_TAC t THEN REWRITE_TAC[linside] THEN STRIP_TAC) tms;;

(* Lean: central_faces *)
let C1092IFBD_CENTRAL_FACES = prove
 (parse_term (Printf.sprintf "!%s. %s ==> c1092ifbd_faces cC sC uC vC aC" C1092IFBD_VARS C1092IFBD_HYP),
  C1092IFBD_OPEN_TAC THEN REWRITE_TAC[c1092ifbd_faces] THEN
  C1092IFBD_PT_TAC [`linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20))`;
                    `linside cC sC uC vC aC (&0) (--(&13 / &50))`;
                    `linside cC sC uC vC aC (--(&13 / &50)) (&0)`;
                    `linside cC sC uC vC aC (--(&1 / &2)) (&0)`] THEN
  SUBGOAL_THEN `sC < &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside cC sC uC vC aC (&0) (&0)` THEN REWRITE_TAC[linside] THEN
    SUBGOAL_THEN `sC = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID; REAL_ADD_LID;
                                REAL_NEG_0]) THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID; REAL_NEG_0] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `vC + aC <= &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside cC sC uC vC aC (&0) (&0)` THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--sC + (&2 / &5) * cC < &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (cC + sC) * (&41 * cC - sC)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC [SQ_NONNEG `--sC + (&2 / &5) * cC - &1`]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside cC sC uC vC aC (--(&1)) (--(&2 / &5))` THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC;
    RASM_ARITH_TAC]);;

(* Lean: cone *)
let C1092IFBD_CONE = prove
 (parse_term (Printf.sprintf
   "!%s nx ny. %s /\\ nx pow 2 + ny pow 2 = &1 /\\ ABT_upper cB sB uB vB aB nx ny <= ABT_lower cC sC uC vC aC nx ny ==> &0 < ny /\\ &0 < (&11 / &20) * nx + (&23 / &50) * ny"
   C1092IFBD_VARS C1092IFBD_HYP),
  C1092IFBD_OPEN_TAC THEN
  let sb sq (x, y) =
    MP_TAC(SPECL (sq @ [x; y; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC in
  let cs = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`]
  and bs = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`] in
  sb bs (`&0`, `--(&543 / &500)`) THEN sb cs (`&0`, `--(&13 / &50)`) THEN
  sb bs (`--(&14 / &25)`, `--(&1)`) THEN sb cs (`--(&1 / &100)`, `--(&27 / &50)`) THEN
  CONJ_TAC THEN RASM_ARITH_TAC);;

let C1092IFBD_CS = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let C1092IFBD_BS = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`];;

(* a separation upper B n <= lower C n, or (rev) its reverse upper C (-n) <= lower B (-n),
   gives the cone conditions at n *)
let C1092IFBD_DIR_TAC rev nx ny =
  (if rev then
     MP_TAC(SPECL (C1092IFBD_CS @ [nx; ny]) OCWPVG_UPPER_NEG) THEN
     MP_TAC(SPECL (C1092IFBD_BS @ [nx; ny]) OCWPVG_LOWER_NEG) THEN
     MP_TAC(SPECL (C1092IFBD_BS @ [nx; ny]) OCWPVG_UPPER_NEG) THEN
     MP_TAC(SPECL (C1092IFBD_CS @ [nx; ny]) OCWPVG_LOWER_NEG) THEN
     REWRITE_TAC[REAL_NEG_NEG] THEN REPEAT DISCH_TAC THEN
     SUBGOAL_THEN (mk_comb(mk_comb(`(<=):real->real->bool`,
                     list_mk_comb(`ABT_upper`, C1092IFBD_BS @ [nx; ny])),
                     list_mk_comb(`ABT_lower`, C1092IFBD_CS @ [nx; ny]))) ASSUME_TAC THENL
      [RASM_ARITH_TAC; ALL_TAC]
   else ALL_TAC) THEN
  MP_TAC(SPECL ([`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                 `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; nx; ny]) C1092IFBD_CONE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[c1092ifbd_input; c977cc_normal] THEN
    REWRITE_TAC[REAL_POW_2; REAL_NEG_MUL2] THEN RASM_ARITH_TAC;
    STRIP_TAC];;

(* Lean: separators *)
let C1092IFBD_SEPARATORS = prove
 (parse_term (Printf.sprintf
   "!%s. %s /\\ abs sB <= cB ==> ABT_upper cB sB uB vB aB (--sC) cC <= vC \\/ uB + aB <= ABT_lower cC sC uC vC aC cB sB \\/ vB + aB <= ABT_lower cC sC uC vC aC (--sB) cB"
   C1092IFBD_VARS C1092IFBD_HYP),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `--cB <= sB /\ sB <= cB` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `abs sB <= cB` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `abs sB <= cB`)) THEN
  SUBGOAL_THEN `&0 < cB` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> MP_TAC th THEN REWRITE_TAC[c1092ifbd_input] THEN STRIP_TAC THEN
    MP_TAC(MATCH_MP C977CC_NORMAL_BOUNDS (ASSUME `c977cc_normal cC (--sC)`)) THEN
    MP_TAC(ASSUME `c977cc_normal cC (--sC)`) THEN REWRITE_TAC[c977cc_normal] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL (C1092IFBD_BS @ C1092IFBD_CS) CSAT_FACESEPARATION_OF_DISJOINT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ldisj cC sC uC vC aC cB sB uB vB aB` THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
      REWRITE_TAC[ldisj] THEN MESON_TAC[];
      ALL_TAC]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `aC:real`; `cC:real`; `sC:real`; `aC:real`] ABT_PARALLEL_RADIUS) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `aC:real`; `cC:real`; `sC:real`; `aC:real`] ABT_TRANSVERSE_RADIUS) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `aC:real`; `cB:real`; `sB:real`; `aC:real`] ABT_PARALLEL_RADIUS) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `aC:real`; `cB:real`; `sB:real`; `aC:real`] ABT_TRANSVERSE_RADIUS) THEN
  MP_TAC(SPECL C1092IFBD_CS ABT_OWNV) THEN MP_TAC(SPECL C1092IFBD_BS ABT_OWNU) THEN
  MP_TAC(SPECL C1092IFBD_BS ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[C977CB_faceSep] o
    check (can (term_match [] `C977CB_faceSep a b c d e f g h i j`) o concl)) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   (map (fun (nx, ny, direct, back) ->
      MP_TAC(SPECL (C1092IFBD_BS @ C1092IFBD_CS @ [nx; ny]) ABT_SEPARATED) THEN
      ANTS_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL [direct; back])
    [`cB:real`, `sB:real`,
       (DISJ2_TAC THEN DISJ1_TAC THEN RASM_ARITH_TAC),
       (C1092IFBD_DIR_TAC true `--cB` `--sB` THEN RASM_ARITH_TAC);
     `--sB`, `cB:real`,
       (DISJ2_TAC THEN DISJ2_TAC THEN RASM_ARITH_TAC),
       (C1092IFBD_DIR_TAC true `sB:real` `--cB` THEN RASM_ARITH_TAC);
     `cC:real`, `sC:real`,
       (C1092IFBD_DIR_TAC false `cC:real` `sC:real` THEN RASM_ARITH_TAC),
       (C1092IFBD_DIR_TAC true `--cC` `--sC` THEN RASM_ARITH_TAC);
     `--sC`, `cC:real`,
       (DISJ1_TAC THEN RASM_ARITH_TAC),
       (C1092IFBD_DIR_TAC true `sC:real` `--cC` THEN RASM_ARITH_TAC)]));;

(* Lean: positive_wall *)
let C1092IFBD_POSITIVE_WALL = prove
 (parse_term (Printf.sprintf
   "!%s. %s /\\ c977cc_normal cB sB ==> --(&2) * cB + (aC / &2) * (&1 + cB * (cB + sB)) <= vB + aB"
   C1092IFBD_VARS C1092IFBD_HYP),
  C1092IFBD_OPEN_TAC THEN
  MP_TAC(SPECL C1092IFBD_BS C1092SBS_BOTTOM_CENTER) THEN
  ASM_REWRITE_TAC[c1092sbs_width0] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_ARITH `&7 / &10 <= x ==> abs x = x`] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL C1092IFBD_BS LCENTRE_COORDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `cB * (--(&2) + aC * (cB + sB) / &2) <= cB * lcy cB sB uB vB aC /\
    sB * lcx cB sB uB vB aC <= &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= x * --y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC];
    ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: negative_wall_height *)
let C1092IFBD_NEGATIVE_WALL_HEIGHT = prove
 (parse_term (Printf.sprintf
   "!%s. %s /\\ c977cc_normal cB (--sB) ==> --(&1) < vB + aB" C1092IFBD_VARS C1092IFBD_HYP),
  C1092IFBD_OPEN_TAC THEN
  SUBGOAL_THEN `&0 <= &2 + sB * (uB + aC) + cB * vB` ASSUME_TAC THENL
   [MATCH_MP_TAC C977WC_AFFINE_ENDPOINT THEN
    MAP_EVERY EXISTS_TAC [`aC:real`; `cB - sB`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`cB * (uB + aC - t) - sB * (vB + t)`; `sB * (uB + aC - t) + cB * (vB + t)`] o
      check (fun th -> is_forall (concl th))) THEN
    ASM_SIMP_TAC[TSS_INSIDE_FACE] THEN
    ANTS_TAC THENL [RASM_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  C1092IFBD_PT_TAC [`linside cB sB uB vB aC (&0) (--(&543 / &500))`] THEN
  SUBGOAL_THEN `&0 <= --sB * (uB + aC + (&543 / &500) * sB)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC C1092IFBS_NEGATIVE_HEIGHT THEN
  MAP_EVERY EXISTS_TAC [`cB:real`; `--sB`; `aC:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC);;
