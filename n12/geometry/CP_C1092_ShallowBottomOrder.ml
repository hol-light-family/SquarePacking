(* ========================================================================= *)
(* Port of Compact/Completion/C1092/ShallowBottomOrder.lean                  *)
(* (namespace N12Compact.C1092ShallowWallOrder).  The actual bottom-center   *)
(* envelope in the shallow-positive wall-order theorem.  Squares C, B are    *)
(* cC sC uC vC aC and cB sB uB vB aB.  Data C x: c1092sbo_data; cosH / sinH: *)
(* c1092sps_cosH / c1092sps_sinH; b: c1092scs_b; gap / margin:               *)
(* c1092sbm_gap / C1092SBM_MARGIN; bounds / brackets: C1092SCS_BOUNDS /      *)
(* C1092SCS_BRACKETS; bottom_center, width_bounds, bottom_face, FaceNormal,  *)
(* width0: C1092SBS_*, c1092sbs_*; negative_support:                         *)
(* C1092MCSUP_NEGATIVE_SUPPORT; upper / lower / supportRadius / pairRadius:  *)
(* ABT_upper / ABT_lower / tss_support_radius / C977CB_pairRadius.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_ShallowBottomMargin.ml";;
needs "n12/geometry/CP_C1092_ShallowBoundarySupport.ml";;
needs "n12/geometry/CP_C1092_MixedCornerSupports.ml";;
needs "n12/geometry/CongruentSAT.ml";;

(* Lean: Data (structure) *)
let c1092sbo_data = new_definition
 `c1092sbo_data (cC:real) (sC:real) (uC:real) (vC:real) (aC:real) (x:real) <=>
    &0 < x /\ x <= &1 / &4 /\ cC = c1092sps_cosH x /\ sC = c1092sps_sinH x /\
    c977cc_normal cC sC /\
    --cC - sC <= uC /\ uC + aC <= --sC / &2 /\
    (&14 / &25) * sC - cC <= vC /\ vC + aC <= sC /\
    linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
    linside cC sC uC vC aC (--(&1)) (--(&13 / &50))`;;

let C1092SBO_C = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let C1092SBO_B = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`];;

let C1092SBO_LIN =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (fun g -> if is_eq(snd g) then (REAL_ARITH_TAC ORELSE RASM_ARITH_TAC) g
            else NLIN_TAC ~deg2:false [] g));;
let C1092SBO_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092SBO_LIN; ALL_TAC];;

(* scalar facts of the shallow angle (bounds, brackets, half_cos_pos, half_sin_pos) *)
let C1092SBO_SCALARS = prove
 (`forall c s x. &0 < x /\ x <= &1 / &4 /\ c = c1092sps_cosH x /\ s = c1092sps_sinH x /\
           c977cc_normal c s
     ==> &0 < c /\ &0 < s /\ &7 / &17 <= c - s /\
         --c + s + &2 / &5 - s pow 2 - (&1 / &2) * c * s < &0 /\
         &1 - c - s + c * s - s pow 2 / &2 < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `c977cc_normal c s` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real` C1092SCS_BRACKETS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real` C1092SCS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_COS_POS) THEN
  ANTS_TAC THENL [C1092SBO_LIN; DISCH_TAC] THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_SIN_POS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[]);;

(* Lean: cone (local) *)
let C1092SBO_CONE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     linside cB sB uB vB aB (&0) (--(&543 / &500)) /\
     linside cB sB uB vB aB (--(&2 / &5)) (--(&1)) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cB sB uB vB aB nx ny <= ABT_lower cC sC uC vC aC nx ny
     ==> &0 < ny /\ nx < (&413 / &500) * ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (sq,(x,y)) ->
      MP_TAC(SPECL (sq @ [x; y; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC)
   [[`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`], (`&0`,`--(&543 / &500)`);
    [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`], (`--(&2 / &5)`,`--(&1)`);
    [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`], (`--(&7 / &20)`,`--(&7 / &20)`);
    [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`], (`--(&1)`,`--(&13 / &50)`)] THEN
  C1092SBO_LIN);;

(* Lean: central (local) *)
let C1092SBO_CENTRAL = prove
 (`forall cC sC uC vC aC cB sB uB vB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\
     c977cc_normal cC sC /\ &0 < cC /\ &0 < sC /\
     (forall x y. linside cB sB uB vB aC x y ==> --(&2) <= y) /\
     lcx cB sB uB vB aC < c1092scs_b aC cC sC (vC + aC)
     ==> ~(ABT_upper cB sB uB vB aC (--sC) cC <= ABT_lower cC sC uC vC aC (--sC) cC)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092SBO_C ABT_OWNV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`] C1092SBS_BOTTOM_CENTER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `cC:real`; `sC:real`]
    C1092SBS_WIDTH_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sC * c1092scs_b aC cC sC (vC + aC) =
                aC * (&3 / &2 + cC * (cC + sC) / &2) - (vC + aC) - &2 * cC` ASSUME_TAC THENL
   [REWRITE_TAC[c1092scs_b] THEN MATCH_MP_TAC REAL_DIV_LMUL THEN C1092SBO_LIN;
    ALL_TAC] THEN
  C1092SBO_PROD `&0 <= cC * (lcy cB sB uB vB aC - (--(&2) + aC * c1092sbs_width0 cB sB / &2))` THEN
  C1092SBO_PROD `&0 < sC * (c1092scs_b aC cC sC (vC + aC) - lcx cB sB uB vB aC)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ABT_upper]) THEN C1092SBO_LIN);;

(* Lean: northeast (local) *)
let C1092SBO_NORTHEAST = prove
 (`forall cC sC uC vC aC cB sB uB vB nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &1 < aC /\
     &0 < cC /\ &0 < sC /\ &7 / &17 <= cC - sC /\
     uC + aC <= --sC / &2 /\ vC + aC <= sC /\
     --cC + sC + &2 / &5 - sC pow 2 - (&1 / &2) * cC * sC < &0 /\
     &1 - cC - sC + cC * sC - sC pow 2 / &2 < &0 /\
     linside cB sB uB vB aC (&0) (--(&543 / &500)) /\
     linside cB sB uB vB aC (--(&2 / &5)) (--(&1)) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
     nx pow 2 + ny pow 2 = &1 /\ &0 <= nx
     ==> ~(ABT_upper cB sB uB vB aC nx ny <= ABT_lower cC sC uC vC aC nx ny)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092SBO_C @ C1092SBO_B @ [`nx:real`; `ny:real`]) C1092SBO_CONE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092SBO_PROD `&0 <= cC * nx` THEN C1092SBO_PROD `&0 < sC * ny` THEN
  C1092SBO_PROD `&0 < (cC - sC) * ny` THEN C1092SBO_PROD `&0 <= sC * (ny - nx)` THEN
  SUBGOAL_THEN `&0 < nx * cC + ny * sC /\ &0 < --nx * sC + ny * cC` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092SBO_LIN; ALL_TAC] THEN
  MP_TAC(SPECL (C1092SBO_C @ [`nx:real`; `ny:real`; `nx * cC + ny * sC`;
                              `--nx * sC + ny * cC`]) C1092WS_LOWER_NN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SBO_LIN; DISCH_TAC] THEN
  C1092SBO_PROD `&0 <= (nx * cC + ny * sC) * ((--sC / &2 - aC) - uC)` THEN
  C1092SBO_PROD `&0 <= (--nx * sC + ny * cC) * ((sC - aC) - vC)` THEN
  C1092SBO_PROD `&0 < (aC - &1) * ((nx * cC + ny * sC) + (--nx * sC + ny * cC))` THEN
  C1092SBO_PROD `&0 <= nx * --(--cC + sC + &2 / &5 - sC pow 2 - (&1 / &2) * cC * sC)` THEN
  C1092SBO_PROD `&0 < ny * --(&1 - cC - sC + cC * sC - sC pow 2 / &2)` THEN
  MP_TAC(SPECL (C1092SBO_B @ [`--(&2 / &5)`; `--(&1)`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092SBO_LIN);;

(* Lean: boundary (local) *)
let C1092SBO_BOUNDARY = prove
 (`forall cC sC uC vC aC cB sB uB vB x nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &1 < aC /\
     &0 < x /\ x <= &1 / &4 /\ c1092sps_cosH x = cC /\ c1092sps_sinH x = sC /\
     c977cc_normal cC sC /\
     &0 < cC /\ &0 < sC /\ &7 / &17 <= cC - sC /\
     --cC - sC <= uC /\ uC + aC <= --sC / &2 /\
     (&14 / &25) * sC - cC <= vC /\ vC + aC <= sC /\
     --cC + sC + &2 / &5 - sC pow 2 - (&1 / &2) * cC * sC < &0 /\
     &1 - cC - sC + cC * sC - sC pow 2 / &2 < &0 /\
     linside cB sB uB vB aC (&0) (--(&543 / &500)) /\
     linside cB sB uB vB aC (--(&2 / &5)) (--(&1)) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
     (forall x y. linside cB sB uB vB aC x y ==> --(&2) <= y) /\
     lcx cB sB uB vB aC < c1092scs_b aC cC sC (vC + aC) /\
     nx pow 2 + ny pow 2 = &1 /\ c1092sbs_FaceNormal cB sB nx ny
     ==> ~(ABT_upper cB sB uB vB aC nx ny <= ABT_lower cC sC uC vC aC nx ny)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= nx` THENL
   [MATCH_MP_TAC C1092SBO_NORTHEAST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL (C1092SBO_C @ C1092SBO_B @ [`nx:real`; `ny:real`]) C1092SBO_CONE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `--nx`; `ny:real`]
    C1092SBS_BOTTOM_FACE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_NEG_NEG] THEN C1092SBO_LIN;
    DISCH_THEN(LABEL_TAC "bf" o REWRITE_RULE[REAL_NEG_NEG])] THEN
  MP_TAC(SPECL [`aC:real`; `cC:real`; `sC:real`; `uC + aC`; `vC + aC`; `--nx`; `ny:real`;
                `x:real`] C1092SBM_MARGIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_NEG; ARITH] THEN
    REPEAT C1092SBO_LIN;
    STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < sC * --nx + cC * ny` ASSUME_TAC THENL
   [C1092SBO_PROD `&0 <= sC * --nx` THEN C1092SBO_PROD `&0 < cC * ny` THEN C1092SBO_LIN;
    ALL_TAC] THEN
  C1092SBO_PROD `&0 < --nx * (c1092scs_b aC cC sC (vC + aC) - lcx cB sB uB vB aC)` THEN
  UNDISCH_TAC `&0 <= c1092sbm_gap aC cC sC (uC + aC) (vC + aC) (--nx) ny` THEN
  REWRITE_TAC[c1092sbm_gap] THEN
  ASM_CASES_TAC `&0 <= sC * ny - cC * --nx` THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 <= d ==> max d (&0) = d`] THEN
    MP_TAC(SPECL (C1092SBO_C @ [`nx:real`; `ny:real`; `sC * ny - cC * --nx`;
                                `sC * --nx + cC * ny`]) C1092WS_LOWER_NN);
    ASM_SIMP_TAC[REAL_ARITH `~(&0 <= d) ==> max d (&0) = &0`] THEN
    MP_TAC(SPECL (C1092SBO_C @ [`nx:real`; `ny:real`; `sC * ny - cC * --nx`;
                                `sC * --nx + cC * ny`]) C1092WS_LOWER_NP)] THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT C1092SBO_LIN; ALL_TAC]) THEN
  UNDISCH_TAC `ABT_upper cB sB uB vB aC nx ny <= ABT_lower cC sC uC vC aC nx ny` THEN
  REMOVE_THEN "bf" MP_TAC THEN
  UNDISCH_TAC `&0 < --nx * (c1092scs_b aC cC sC (vC + aC) - lcx cB sB uB vB aC)` THEN
  REAL_ARITH_TAC);;

(* Lean: bottom_order *)
let C1092SBO_BOTTOM_ORDER = prove
 (`forall cC sC uC vC aC cB sB uB vB aB x.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aC /\ aC = aB /\ c1092sbo_data cC sC uC vC aC x /\
     linside cB sB uB vB aB (&0) (--(&543 / &500)) /\
     linside cB sB uB vB aB (--(&2 / &5)) (--(&1)) /\
     (forall x y. linside cB sB uB vB aB x y ==> --(&2) <= y) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> c1092scs_b aC cC sC (vC + aC) <= lcx cB sB uB vB aB`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092sbo_data] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> concl th = `cC = c1092sps_cosH x`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> concl th = `sC = c1092sps_sinH x`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `x:real`] C1092SBO_SCALARS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `aC <= cC + (&11 / &25) * sC` ASSUME_TAC THENL [C1092SBO_LIN; ALL_TAC] THEN
  MP_TAC(SPECL (C1092SBO_C @ C1092SBO_B) CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `aC:real`; `cB:real`; `sB:real`; `aC:real`] ABT_PARALLEL_RADIUS) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `aC:real`; `cB:real`; `sB:real`; `aC:real`] ABT_TRANSVERSE_RADIUS) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `aC:real`; `cC:real`; `sC:real`; `aC:real`] ABT_PARALLEL_RADIUS) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `aC:real`; `cC:real`; `sC:real`; `aC:real`] ABT_TRANSVERSE_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[C977CB_faceSep] o
    check (can (term_match [] `C977CB_faceSep a b c d e f g h i j`) o concl)) THEN
  let cone nx ny = SPECL (C1092SBO_C @ C1092SBO_B @ [nx; ny]) C1092SBO_CONE in
  let bnd nx ny = SPECL (C1092SBO_C @ [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `x:real`;
                         nx; ny]) C1092SBO_BOUNDARY in
  let use th = MP_TAC th THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[c1092sbs_FaceNormal; REAL_NEG_NEG] THEN
     REWRITE_TAC[REAL_POW_NEG; ARITH; REAL_POW_2] THEN C1092SBO_LIN; ALL_TAC] in
  let flip nx ny = SUBGOAL_THEN
    (mk_comb(mk_comb(`(<=):real->real->bool`,
      list_mk_comb(`ABT_upper`, C1092SBO_B @ [mk_comb(`(--):real->real`,nx);
                                              mk_comb(`(--):real->real`,ny)])),
      list_mk_comb(`ABT_lower`, C1092SBO_C @ [mk_comb(`(--):real->real`,nx);
                                              mk_comb(`(--):real->real`,ny)])))
    ASSUME_TAC THENL
    [REWRITE_TAC[C1092MCSUP_NEGATIVE_SUPPORT] THEN C1092SBO_LIN; ALL_TAC] in
  let neg t = mk_comb(`(--):real->real`, t) in
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   (map (fun (nx, ny, forward, backward) ->
      MP_TAC(SPECL (C1092SBO_C @ C1092SBO_B @ [nx; ny]) ABT_SEPARATED) THEN
      ANTS_TAC THENL [C1092SBO_LIN; ALL_TAC] THEN
      DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
       [flip nx ny THEN forward; backward])
    [`cC:real`, `sC:real`,
       (use (cone (neg `cC:real`) (neg `sC:real`)) THEN STRIP_TAC THEN C1092SBO_LIN),
       (use (cone `cC:real` `sC:real`) THEN STRIP_TAC THEN C1092SBO_LIN);
     `--sC`, `cC:real`,
       (use (cone (neg `--sC`) (neg `cC:real`)) THEN STRIP_TAC THEN C1092SBO_LIN),
       (MP_TAC(SPECL (C1092SBO_C @ [`cB:real`; `sB:real`; `uB:real`; `vB:real`])
          C1092SBO_CENTRAL) THEN ASM_REWRITE_TAC[]);
     `cB:real`, `sB:real`,
       (use (bnd (neg `cB:real`) (neg `sB:real`)) THEN ASM_REWRITE_TAC[]),
       (use (bnd `cB:real` `sB:real`) THEN ASM_REWRITE_TAC[]);
     `--sB`, `cB:real`,
       (use (bnd (neg `--sB`) (neg `cB:real`)) THEN ASM_REWRITE_TAC[]),
       (use (bnd `--sB` `cB:real`) THEN ASM_REWRITE_TAC[])]));;
