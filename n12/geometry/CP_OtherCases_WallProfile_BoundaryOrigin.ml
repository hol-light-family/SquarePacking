(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/WallProfile/BoundaryOrigin.lean     *)
(* (N12Compact.Completion.OtherCases.WallProfile).  All-angle direct origin  *)
(* transfer between two actual congruent squares (Theorem7 of                *)
(* C1092-DIRECT-WALL-POINT).  Square B is cB sB uB vB aB, the corner square  *)
(* K is cK sK uK vK aK.  upper / lower are ABT_upper / ABT_lower; profile is *)
(* C1092WPS_profile; vertex, strict_closed_segment, vertical_owned,          *)
(* lower_wall_vertex, negative_frame, upper_neg, lower_neg are OCWPVG_*;     *)
(* negative_boundary_cap is OCWPBCG_NEGATIVE_BOUNDARY_CAP; corner_profile is *)
(* OCWPCP_CORNER_PROFILE.  Tag OCWPBO_.                                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_CornerProfile.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_BoundaryCapGeometry.ml";;

let OCWPBO_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC]) tms;;

let OCWPBO_POS_CANCEL = prove
 (`forall k y. &0 < k /\ &0 < k * y ==> &0 < y`,
  MESON_TAC[REAL_LT_MUL_EQ]);;

(* Lean: negative_transfer (private) *)
let OCWPBO_NEGATIVE_TRANSFER = prove
 (`forall cB sB uB vB aB cK sK uK vK aK t b ell.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     sB = --t /\ &0 < cB /\ &0 < t /\ &1 < aB /\ aB = aK /\
     (forall x y. linside cB sB uB vB aB x y ==> &0 <= y) /\
     &0 < b /\ b < &1 /\ &1 < ell /\ ell < &2 /\
     linside cB sB uB vB aB (&2) b /\ linside cB sB uB vB aB ell (&1) /\
     linside cK sK uK vK aK (&1) b /\ linside cK sK uK vK aK (&1) (&1) /\
     (forall c s. &0 <= c ==> &0 <= s ==> c pow 2 + s pow 2 = &1
            ==> aK * C1092WPS_profile c s <= ABT_upper cK sK uK vK aK c (--s)) /\
     ldisj cK sK uK vK aK cB sB uB vB aB
     ==> linside cB sB uB vB aB (&2) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aB:real = aK`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sB:real = --t`)) THEN
  REFUTE_THEN ASSUME_TAC THEN
  SUBGOAL_THEN `cB pow 2 + t pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `cB * cB + --t * --t = &1` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cB <= &1 /\ t <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `t:real`; SQ_NONNEG `cB:real`; SQ_NONNEG `cB - &1`;
                            SQ_NONNEG `t - &1`]; ALL_TAC] THEN
  MAP_EVERY (fun tm -> MP_TAC(ASSUME tm) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside cB (--t) uB vB aB (&2) b`; `linside cB (--t) uB vB aB ell (&1)`] THEN
  OCWPBO_PROD_TAC [`&0 < cB * (&2 - ell)`; `&0 < t * (&1 - b)`; `&0 < t * (&2 - ell)`] THEN
  SUBGOAL_THEN `vB + aB <= &2 * t + cB` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside cB (--t) uB vB aB (&2) (&1)` THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  (* the lower-left vertex of B *)
  SUBGOAL_THEN `cB * (cB * uB - --t * vB) + --t * (--t * uB + cB * vB) = uB /\
                --(--t) * (cB * uB - --t * vB) + cB * (--t * uB + cB * vB) = vB`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN UNDISCH_TAC `cB * cB + --t * --t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`; `uB:real`; `vB:real`]
    OCWPVG_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`] OCWPVG_LOWER_WALL_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `X = cB * uB - --t * vB` THEN ABBREV_TAC `Y = --t * uB + cB * vB` THEN
  SUBGOAL_THEN `aB * t <= Y` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `X < &1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < &1 - X ==> X < &1`) THEN
    MATCH_MP_TAC OCWPBO_POS_CANCEL THEN EXISTS_TAC `t:real` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    OCWPBO_PROD_TAC [`&0 <= cB * (Y - aB * t)`; `&0 < cB * t`] THEN
    OCWPBO_PROD_TAC [`&0 < (aB - &1) * (&1 + cB * t)`; `&0 <= (&1 - cB) * (&1 - t)`] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Y < &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OCWPBO_PROD_TAC [`&0 < cB * (&1 - X)`; `&0 <= t * (Y - &1)`;
                     `&0 < cB * (ell - &1)`; `&0 < t * (ell - &1)`] THEN
    UNDISCH_TAC `ldisj cK sK uK vK aB cB (--t) uB vB aB` THEN
    REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&1`; `&1`]) THEN
    ASM_REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aB:real`;
                `&1`; `b:real`; `&1`] OCWPVG_VERTICAL_OWNED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `Y < b` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < ell - X` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - X) / (ell - X) * (ell - X) = &1 - X` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (&1 - X) / (ell - X) /\ (&1 - X) / (ell - X) < &1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
    ABBREV_TAC `w = (&1 - X) / (ell - X)` THEN
    MP_TAC(SPECL [`cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`;
                  `X:real`; `Y:real`; `ell:real`; `&1`; `w:real`]
      OCWPVG_STRICT_CLOSED_SEGMENT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - w) * X + w * ell = &1` SUBST1_TAC THENL
     [UNDISCH_TAC `w * (ell - X) = &1 - X` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    OCWPBO_PROD_TAC [`&0 <= (&1 - w) * (Y - b)`; `&0 <= w * (&1 - b)`;
                     `&0 <= (&1 - w) * (&1 - Y)`] THEN
    FIRST_ASSUM(MP_TAC o SPEC `(&1 - w) * Y + w * &1` o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
      can (find_term ((=) `cK:real`)) (concl th))) THEN
    ANTS_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
    UNDISCH_TAC `ldisj cK sK uK vK aB cB (--t) uB vB aB` THEN
    REWRITE_TAC[ldisj] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  (* every separating direction from K to B is impossible *)
  SUBGOAL_THEN `forall nx ny. nx pow 2 + ny pow 2 = &1 /\
      ABT_upper cK sK uK vK aB nx ny <= ABT_lower cB (--t) uB vB aB nx ny ==> false`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aB:real`;
                  `&1`; `b:real`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
    MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aB:real`;
                  `&1`; `&1`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
    MP_TAC(SPECL [`cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`;
                  `&2`; `b:real`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
    MP_TAC(SPECL [`cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`;
                  `X:real`; `Y:real`; `nx:real`; `ny:real`] ABT_CLOSED_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 < nx` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `ny < &0` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      OCWPBO_PROD_TAC [`&0 < nx * (&1 - X)`; `&0 <= ny * (&1 - Y)`] THEN
      RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `nx pow 2 + (--ny) pow 2 = &1` ASSUME_TAC THENL
     [UNDISCH_TAC `nx pow 2 + ny pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `aB * C1092WPS_profile nx (--ny) <= ABT_upper cK sK uK vK aB nx ny`
    ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPECL [`nx:real`; `--ny`] o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `C1092WPS_profile`)) (concl th))) THEN
      REWRITE_TAC[REAL_NEG_NEG; IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `ABT_lower cB (--t) uB vB aB nx ny < aB * C1092WPS_profile nx (--ny)`
    ASSUME_TAC THENL
     [MP_TAC(SPECL [`cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`; `t:real`;
                    `nx:real`; `--ny`] OCWPBCG_NEGATIVE_BOUNDARY_CAP) THEN
      REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aB:real`;
                `cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `ABT_upper`)) (concl th) &&
      length(fst(strip_forall(concl th))) = 2 then
    let dirs = [`cK:real`, `sK:real`; `--sK:real`, `cK:real`;
                `cB:real`, `--t:real`; `-- --t:real`, `cB:real`] in
    let negs = map (fun (x,y) -> (mk_comb(`(--):real->real`,x),
                                 mk_comb(`(--):real->real`,y))) dirs in
    FIRST (map (fun (x,y) -> MATCH_MP_TAC th THEN MAP_EVERY EXISTS_TAC [x; y] THEN
      ASM_REWRITE_TAC[REAL_POW_2; OCWPVG_UPPER_NEG; OCWPVG_LOWER_NEG] THEN
      REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC) (dirs @ negs))
    else NO_TAC));;

(* Lean: boundary_origin_of_profile *)
let OCWPBO_BOUNDARY_ORIGIN_OF_PROFILE = prove
 (`forall cB sB uB vB aB cK sK uK vK aK b ell.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     &1 < aB /\ aB = aK /\
     (forall x y. linside cB sB uB vB aB x y ==> &0 <= y) /\
     &0 < b /\ b < &1 /\ &1 < ell /\ ell < &2 /\
     linside cB sB uB vB aB (&2) b /\ linside cB sB uB vB aB ell (&1) /\
     linside cK sK uK vK aK (&1) b /\ linside cK sK uK vK aK (&1) (&1) /\
     (forall c s. &0 <= c ==> &0 <= s ==> c pow 2 + s pow 2 = &1
            ==> aK * C1092WPS_profile c s <= ABT_upper cK sK uK vK aK c (--s)) /\
     ldisj cK sK uK vK aK cB sB uB vB aB
     ==> linside cB sB uB vB aB (&2) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] OCWPVG_NEGATIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cr:real` (X_CHOOSE_THEN `sr:real` (X_CHOOSE_THEN `ur:real`
    (X_CHOOSE_THEN `vr:real` (X_CHOOSE_THEN `ar:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ar:real = aB`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
     can (find_term ((=) `linside`)) (concl th) &&
     is_iff(snd(strip_forall(concl th))) then
     RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ldisj]) THEN
  ASM_CASES_TAC `sr = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MAP_EVERY (fun tm -> MP_TAC(ASSUME tm) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
     [`linside cr (&0) ur vr aB (&2) b`; `linside cr (&0) ur vr aB ell (&1)`] THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC;
    MATCH_MP_TAC OCWPBO_NEGATIVE_TRANSFER THEN
    MAP_EVERY EXISTS_TAC [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                          `--sr`; `b:real`; `ell:real`] THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: boundary_origin *)
let OCWPBO_BOUNDARY_ORIGIN = prove
 (`forall cB sB uB vB aB cK sK uK vK aK b ell.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     &1 < aB /\ aB = aK /\
     (forall x y. linside cB sB uB vB aB x y ==> &0 <= y) /\
     (forall x y. linside cK sK uK vK aK x y ==> &0 <= x /\ &0 <= y) /\
     &0 < b /\ b < &1 /\ &1 < ell /\ ell < &2 /\
     linside cB sB uB vB aB (&2) b /\ linside cB sB uB vB aB ell (&1) /\
     linside cK sK uK vK aK (&1) b /\ linside cK sK uK vK aK (&1) (&1) /\
     ~linside cK sK uK vK aK (&1) (&3 / &2) /\
     ldisj cK sK uK vK aK cB sB uB vB aB
     ==> linside cB sB uB vB aB (&2) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC OCWPBO_BOUNDARY_ORIGIN_OF_PROFILE THEN
  MAP_EVERY EXISTS_TAC [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                        `b:real`; `ell:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC OCWPCP_CORNER_PROFILE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
