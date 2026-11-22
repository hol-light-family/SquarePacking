(* ========================================================================= *)
(* Port of Compact/Completion/C1092/ShallowLeftOrder.lean                    *)
(* (namespace N12Compact.C1092ShallowWallOrder).  The actual left comparison *)
(* and the shallow-positive wall order.  Squares C, B, L are cC sC uC vC aC, *)
(* cB sB uB vB aB, cL sL uL vL aL.  Data C x: c1092sbo_data; bottom_order:   *)
(* C1092SBO_BOTTOM_ORDER; b / ell / same_face_sum / brackets / small_left:   *)
(* c1092scs_b / c1092scs_ell / C1092SCS_*; ShallowLeftMargin.margin:         *)
(* C1092SLM_MARGIN; left_center / width_bounds / left_face / FaceNormal /    *)
(* width0: C1092SBS_*, c1092sbs_*; upper_nn / negative_support:              *)
(* C1092MCSUP_*; upper_np: C1092WS_UPPER_NP; upper / lower / supportRadius / *)
(* strict_bounds / ownV / separated / parallel_radius / transverse_radius:   *)
(* ABT_*, tss_support_radius; faceSeparation_of_disjoint:                    *)
(* CSAT_FACESEPARATION_OF_DISJOINT.  The local haves cone, central,          *)
(* northeast, boundary are separate lemmas.  Tag C1092SLO_.                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_ShallowBottomOrder.ml";;
needs "n12/geometry/CP_C1092_ShallowLeftMargin.ml";;

let C1092SLO_C = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let C1092SLO_L = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aC:real`];;

let C1092SLO_LIN = C1092SBO_LIN;;
let C1092SLO_PROD = C1092SBO_PROD;;

(* the four brackets of the shallow angle together with the C1092SBO scalars *)
let C1092SLO_SCALARS = prove
 (`forall c s x. &0 < x /\ x <= &1 / &4 /\ c = c1092sps_cosH x /\ s = c1092sps_sinH x /\
           c977cc_normal c s
     ==> &0 < c /\ &0 < s /\ &7 / &17 <= c - s /\
         &0 < c - s + (&11 / &25) * s pow 2 /\ &0 < c + s - &1 - (&11 / &25) * c * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `x:real`] C1092SBO_SCALARS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `c977cc_normal c s` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real` C1092SCS_BRACKETS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Lean: cone (local) *)
let C1092SLO_CONE = prove
 (`forall cC sC uC vC aC cL sL uL vL aL nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     linside cL sL uL vL aL (--(&543 / &500)) (&0) /\
     linside cL sL uL vL aL (--(&1)) (&0) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cC sC uC vC aC nx ny <= ABT_lower cL sL uL vL aL nx ny
     ==> &0 < ny /\ nx < (&175 / &368) * ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (sq,(x,y)) ->
      MP_TAC(SPECL (sq @ [x; y; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC)
   [[`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`], (`--(&543 / &500)`,`&0`);
    [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`], (`--(&1)`,`&0`);
    C1092SLO_C, (`--(&7 / &20)`,`--(&7 / &20)`);
    C1092SLO_C, (`--(&1)`,`--(&13 / &50)`)] THEN
  C1092SLO_LIN);;

(* Lean: central (local) *)
let C1092SLO_CENTRAL = prove
 (`forall cC sC uC vC aC cL sL uL vL.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\ &1 < aC /\
     c977cc_normal cC sC /\ &0 < cC /\ &0 < sC /\ vC + aC <= sC /\
     (forall u v. linside cL sL uL vL aC u v ==> --(&2) <= u) /\
     lcy cL sL uL vL aC <= --c1092scs_b aC cC sC (vC + aC)
     ==> ~(ABT_upper cC sC uC vC aC (--sC) cC <= ABT_lower cL sL uL vL aC (--sC) cC)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092SLO_C ABT_OWNV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`aC:real`; `cC:real`; `sC:real`; `vC + aC`] C1092SCS_SAME_FACE_SUM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL C1092SLO_L C1092SBS_LEFT_CENTER) THEN
  ANTS_TAC THENL [C1092SLO_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aC:real`; `cC:real`; `sC:real`]
    C1092SBS_WIDTH_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `cC * c1092scs_ell aC cC sC (vC + aC) =
                (vC + aC) - &2 * sC + (aC / &2) * (&1 + sC * (cC + sC))` ASSUME_TAC THENL
   [REWRITE_TAC[c1092scs_ell] THEN MATCH_MP_TAC REAL_DIV_LMUL THEN C1092SLO_LIN;
    ALL_TAC] THEN
  C1092SLO_PROD `&0 <= sC * (lcx cL sL uL vL aC - (--(&2) + aC * c1092sbs_width0 cL sL / &2))` THEN
  C1092SLO_PROD `&0 < cC * (c1092scs_ell aC cC sC (vC + aC) - lcy cL sL uL vL aC)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ABT_lower]) THEN C1092SLO_LIN);;

(* Lean: northeast (local) *)
let C1092SLO_NORTHEAST = prove
 (`forall cC sC uC vC aC cL sL uL vL nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\ &1 < aC /\
     &0 < cC /\ &0 < sC /\ &7 / &17 <= cC - sC /\
     --cC - sC <= uC /\ (&14 / &25) * sC - cC <= vC /\
     &0 < cC - sC + (&11 / &25) * sC pow 2 /\ &0 < cC + sC - &1 - (&11 / &25) * cC * sC /\
     linside cL sL uL vL aC (--(&543 / &500)) (&0) /\
     linside cL sL uL vL aC (--(&1)) (&0) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
     nx pow 2 + ny pow 2 = &1 /\ &0 <= nx
     ==> ~(ABT_upper cC sC uC vC aC nx ny <= ABT_lower cL sL uL vL aC nx ny)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092SLO_C @ C1092SLO_L @ [`nx:real`; `ny:real`]) C1092SLO_CONE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092SLO_PROD `&0 <= cC * nx` THEN C1092SLO_PROD `&0 < sC * ny` THEN
  C1092SLO_PROD `&0 < (cC - sC) * ny` THEN C1092SLO_PROD `&0 <= sC * (ny - nx)` THEN
  SUBGOAL_THEN `&0 < nx * cC + ny * sC /\ &0 < --nx * sC + ny * cC` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092SLO_LIN; ALL_TAC] THEN
  MP_TAC(SPECL (C1092SLO_C @ [`nx:real`; `ny:real`; `nx * cC + ny * sC`;
                              `--nx * sC + ny * cC`]) C1092MCSUP_UPPER_NN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SLO_LIN; DISCH_TAC] THEN
  C1092SLO_PROD `&0 <= (nx * cC + ny * sC) * ((uC + aC) - (aC - cC - sC))` THEN
  C1092SLO_PROD `&0 <= (--nx * sC + ny * cC) * ((vC + aC) - (aC + (&14 / &25) * sC - cC))` THEN
  C1092SLO_PROD `&0 < (aC - &1) * ((nx * cC + ny * sC) + (--nx * sC + ny * cC))` THEN
  C1092SLO_PROD `&0 <= nx * (cC - sC + (&11 / &25) * sC pow 2)` THEN
  C1092SLO_PROD `&0 < ny * (cC + sC - &1 - (&11 / &25) * cC * sC)` THEN
  SUBGOAL_THEN `nx * (cC * cC + sC * sC) = nx /\ ny * (cC * cC + sC * sC) = ny`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aC:real`; `--(&1)`; `&0`;
                `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092SLO_LIN);;

(* Lean: boundary (local), the western half (h = -nx > 0) *)
let C1092SLO_BOUNDARY_WEST = prove
 (`forall cC sC uC vC aC cL sL uL vL x h ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\ &1 < aC /\
     &0 < x /\ x <= &1 / &4 /\ c1092sps_cosH x = cC /\ c1092sps_sinH x = sC /\
     c977cc_normal cC sC /\
     &0 < cC /\ &0 < sC /\ &7 / &17 <= cC - sC /\
     --cC - sC <= uC /\ uC + aC <= --sC / &2 /\
     (&14 / &25) * sC - cC <= vC /\ vC + aC <= sC /\
     linside cL sL uL vL aC (--(&543 / &500)) (&0) /\
     linside cL sL uL vL aC (--(&1)) (&0) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
     (forall u v. linside cL sL uL vL aC u v ==> --(&2) <= u) /\
     lcy cL sL uL vL aC <= --c1092scs_b aC cC sC (vC + aC) /\
     &0 < h /\ ny pow 2 + h pow 2 = &1 /\ c1092sbs_FaceNormal cL sL (--h) ny
     ==> ~(ABT_upper cC sC uC vC aC (--h) ny <= ABT_lower cL sL uL vL aC (--h) ny)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092SLO_C @ C1092SLO_L @ [`--h`; `ny:real`]) C1092SLO_CONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_NEG; ARITH] THEN C1092SLO_LIN; STRIP_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aC:real`; `--(&1)`; `&0`;
                `--h`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_NEG; ARITH] THEN C1092SLO_LIN; STRIP_TAC] THEN
  C1092SLO_PROD `&0 <= sC * h` THEN C1092SLO_PROD `&0 < cC * ny` THEN
  ASM_CASES_TAC `ny <= h` THENL
   [(* small *)
    C1092SLO_PROD `&0 < (cC - sC) * h` THEN C1092SLO_PROD `&0 <= sC * (h - ny)` THEN
    MP_TAC(SPECL (C1092SLO_C @ [`--h`; `ny:real`; `sC * ny - cC * h`; `sC * h + cC * ny`])
      C1092WS_UPPER_NP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SLO_LIN; DISCH_TAC] THEN
    C1092SLO_PROD `&0 <= --(sC * ny - cC * h) * (--aC - sC / &2 - uC)` THEN
    C1092SLO_PROD `&0 <= (sC * h + cC * ny) * ((vC + aC) - (aC + (&14 / &25) * sC - cC))` THEN
    MP_TAC(SPECL [`aC:real`; `x:real`] C1092SCS_SMALL_LEFT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    C1092SLO_PROD `&0 <= (h - ny) * (aC * (cC + sC) - (&1 / &2) * cC * sC +
                                     (&14 / &25) * sC pow 2 - &1)` THEN
    C1092SLO_PROD `&0 < ny * ((aC * (cC + sC) - (&1 / &2) * cC * sC + (&14 / &25) * sC pow 2 - &1) +
                     (aC * (cC - sC) + (&14 / &25) * cC * sC - sC pow 2 / &2 - cC pow 2))` THEN
    C1092SLO_LIN;
    ALL_TAC] THEN
  (* not small *)
  SUBGOAL_THEN `c977cc_normal ny h` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal] THEN ASM_REWRITE_TAC[] THEN C1092SLO_LIN; ALL_TAC] THEN
  SUBGOAL_THEN
   `ABT_upper cC sC uC vC aC (--h) ny =
    --(cC * h - sC * ny) * (uC + aC) + (cC * ny + sC * h) * (vC + aC) +
    aC * max (cC * h - sC * ny) (&0)` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 <= cC * h - sC * ny` THENL
     [ASM_SIMP_TAC[REAL_ARITH `&0 <= d ==> max d (&0) = d`] THEN
      MP_TAC(SPECL (C1092SLO_C @ [`--h`; `ny:real`; `--(cC * h - sC * ny)`; `cC * ny + sC * h`])
        C1092WS_UPPER_NP);
      ASM_SIMP_TAC[REAL_ARITH `~(&0 <= d) ==> max d (&0) = &0`] THEN
      MP_TAC(SPECL (C1092SLO_C @ [`--h`; `ny:real`; `--(cC * h - sC * ny)`; `cC * ny + sC * h`])
        C1092MCSUP_UPPER_NN)] THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SLO_LIN; ALL_TAC]) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `--(cC * h - sC * ny) * (uC + aC) + (cC * ny + sC * h) * (vC + aC) +
    aC * max (cC * h - sC * ny) (&0) < h` ASSUME_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
      can (find_term ((=) `ABT_lower`)) (concl th) || can (find_term ((=) `ABT_upper`)) (concl th))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`aC:real`; `cC:real`; `sC:real`; `uC + aC`; `vC + aC`; `h:real`; `ny:real`;
                `x:real`] C1092SLM_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT C1092SLO_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL (C1092SLO_L @ [`h:real`; `ny:real`]) C1092SBS_LEFT_FACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SLO_LIN; DISCH_TAC] THEN
  C1092SLO_PROD `&0 <= ny * (--c1092scs_b aC cC sC (vC + aC) - lcy cL sL uL vL aC)` THEN
  UNDISCH_TAC `ABT_upper cC sC uC vC aC (--h) ny <= ABT_lower cL sL uL vL aC (--h) ny` THEN
  ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
    let c = concl th in
    can (find_term ((=) `c1092scs_b`)) c || can (find_term ((=) `ABT_lower`)) c)) THEN
  REAL_ARITH_TAC);;

(* Lean: boundary (local) *)
let C1092SLO_BOUNDARY = prove
 (`forall cC sC uC vC aC cL sL uL vL x nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\ &1 < aC /\
     &0 < x /\ x <= &1 / &4 /\ c1092sps_cosH x = cC /\ c1092sps_sinH x = sC /\
     c977cc_normal cC sC /\
     &0 < cC /\ &0 < sC /\ &7 / &17 <= cC - sC /\
     --cC - sC <= uC /\ uC + aC <= --sC / &2 /\
     (&14 / &25) * sC - cC <= vC /\ vC + aC <= sC /\
     &0 < cC - sC + (&11 / &25) * sC pow 2 /\ &0 < cC + sC - &1 - (&11 / &25) * cC * sC /\
     linside cL sL uL vL aC (--(&543 / &500)) (&0) /\
     linside cL sL uL vL aC (--(&1)) (&0) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
     (forall u v. linside cL sL uL vL aC u v ==> --(&2) <= u) /\
     lcy cL sL uL vL aC <= --c1092scs_b aC cC sC (vC + aC) /\
     nx pow 2 + ny pow 2 = &1 /\ c1092sbs_FaceNormal cL sL nx ny
     ==> ~(ABT_upper cC sC uC vC aC nx ny <= ABT_lower cL sL uL vL aC nx ny)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= nx` THENL
   [MATCH_MP_TAC C1092SLO_NORTHEAST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL (C1092SLO_C @ [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `x:real`;
                              `--nx`; `ny:real`]) C1092SLO_BOUNDARY_WEST) THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         UNDISCH_TAC `nx pow 2 + ny pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
         C1092SLO_LIN]);;

(* Lean: left_order *)
let C1092SLO_LEFT_ORDER = prove
 (`forall cC sC uC vC aC cL sL uL vL aL x.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     &1 < aC /\ aC = aL /\ c1092sbo_data cC sC uC vC aC x /\
     linside cL sL uL vL aL (--(&543 / &500)) (&0) /\
     linside cL sL uL vL aL (--(&1)) (&0) /\
     (forall u v. linside cL sL uL vL aL u v ==> --(&2) <= u) /\
     ldisj cC sC uC vC aC cL sL uL vL aL
     ==> --c1092scs_b aC cC sC (vC + aC) < lcy cL sL uL vL aL`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092sbo_data] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aL`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> concl th = `cC = c1092sps_cosH x`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> concl th = `sC = c1092sps_sinH x`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `x:real`] C1092SLO_SCALARS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092SLO_C @ C1092SLO_L) CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `aC:real`; `cL:real`; `sL:real`; `aC:real`] ABT_PARALLEL_RADIUS) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `aC:real`; `cL:real`; `sL:real`; `aC:real`] ABT_TRANSVERSE_RADIUS) THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `aC:real`; `cC:real`; `sC:real`; `aC:real`] ABT_PARALLEL_RADIUS) THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `aC:real`; `cC:real`; `sC:real`; `aC:real`] ABT_TRANSVERSE_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[C977CB_faceSep] o
    check (can (term_match [] `C977CB_faceSep a b c d e f g h i j`) o concl)) THEN
  let cone nx ny = SPECL (C1092SLO_C @ C1092SLO_L @ [nx; ny]) C1092SLO_CONE in
  let bnd nx ny = SPECL (C1092SLO_C @ [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `x:real`;
                         nx; ny]) C1092SLO_BOUNDARY in
  let use th = MP_TAC th THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[c1092sbs_FaceNormal; REAL_NEG_NEG] THEN
     REWRITE_TAC[REAL_POW_NEG; ARITH; REAL_POW_2] THEN C1092SLO_LIN; ALL_TAC] in
  let flip nx ny = SUBGOAL_THEN
    (mk_comb(mk_comb(`(<=):real->real->bool`,
      list_mk_comb(`ABT_upper`, C1092SLO_C @ [mk_comb(`(--):real->real`,nx);
                                              mk_comb(`(--):real->real`,ny)])),
      list_mk_comb(`ABT_lower`, C1092SLO_L @ [mk_comb(`(--):real->real`,nx);
                                              mk_comb(`(--):real->real`,ny)])))
    ASSUME_TAC THENL
    [REWRITE_TAC[C1092MCSUP_NEGATIVE_SUPPORT] THEN C1092SLO_LIN; ALL_TAC] in
  let neg t = mk_comb(`(--):real->real`, t) in
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   (map (fun (nx, ny, forward, backward) ->
      MP_TAC(SPECL (C1092SLO_C @ C1092SLO_L @ [nx; ny]) ABT_SEPARATED) THEN
      ANTS_TAC THENL [C1092SLO_LIN; ALL_TAC] THEN
      DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
       [forward; flip nx ny THEN backward])
    [`cC:real`, `sC:real`,
       (use (cone `cC:real` `sC:real`) THEN STRIP_TAC THEN C1092SLO_LIN),
       (use (cone (neg `cC:real`) (neg `sC:real`)) THEN STRIP_TAC THEN C1092SLO_LIN);
     `--sC`, `cC:real`,
       (MP_TAC(SPECL (C1092SLO_C @ [`cL:real`; `sL:real`; `uL:real`; `vL:real`])
          C1092SLO_CENTRAL) THEN ASM_REWRITE_TAC[]),
       (use (cone (neg `--sC`) (neg `cC:real`)) THEN STRIP_TAC THEN C1092SLO_LIN);
     `cL:real`, `sL:real`,
       (use (bnd `cL:real` `sL:real`) THEN ASM_REWRITE_TAC[]),
       (use (bnd (neg `cL:real`) (neg `sL:real`)) THEN ASM_REWRITE_TAC[]);
     `--sL`, `cL:real`,
       (use (bnd `--sL` `cL:real`) THEN ASM_REWRITE_TAC[]),
       (use (bnd (neg `--sL`) (neg `cL:real`)) THEN ASM_REWRITE_TAC[])]));;

(* Lean: order *)
let C1092SLO_ORDER = prove
 (`forall cC sC uC vC aC cB sB uB vB aB cL sL uL vL aL x.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     cL * cL + sL * sL = &1 /\ &0 < aL /\
     &1 < aC /\ aC = aB /\ aC = aL /\ c1092sbo_data cC sC uC vC aC x /\
     linside cB sB uB vB aB (&0) (--(&543 / &500)) /\
     linside cB sB uB vB aB (--(&2 / &5)) (--(&1)) /\
     (forall x y. linside cB sB uB vB aB x y ==> --(&2) <= y) /\
     linside cL sL uL vL aL (--(&543 / &500)) (&0) /\
     linside cL sL uL vL aL (--(&1)) (&0) /\
     (forall u v. linside cL sL uL vL aL u v ==> --(&2) <= u) /\
     ldisj cC sC uC vC aC cB sB uB vB aB /\
     ldisj cC sC uC vC aC cL sL uL vL aL
     ==> &0 < lcx cB sB uB vB aB + lcy cL sL uL vL aL`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092SLO_C @ [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `x:real`])
    C1092SBO_BOTTOM_ORDER) THEN
  MP_TAC(SPECL (C1092SLO_C @ [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `x:real`])
    C1092SLO_LEFT_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SLO_LIN; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SLO_LIN; DISCH_TAC] THEN
  ASM_REAL_ARITH_TAC);;
