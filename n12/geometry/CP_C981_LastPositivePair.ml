(* ========================================================================= *)
(* Port of Compact/Completion/C981/LastPositivePair.lean                      *)
(* (N12Compact.C981CompletionLastPositivePair).  The complete small-positive *)
(* central two-square ending for the last C981 cycles.  C has sC = r with   *)
(* c977cc_normal cC r; the Lean lets alpha, k, F, G, K, J, u, v are written *)
(* out.  inside_segment is CES_INSIDE_SEGMENT, affine_endpoint_nonnegative  *)
(* is SCAP_AFFINE_ENDPOINT_NONNEG, inside_iff_rotated_box is TSS_INSIDE_FACE,*)
(* short_projections is WFP_SHORT_PROJECTIONS.                               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_LastPositiveScalars.ml";;
needs "n12/geometry/CP_C981_NegativePair.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;
needs "n12/geometry/SectionCapacity.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let C981LPP_LIN = NLIN_TAC ~deg2:false [];;

let C981LPP_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C981LPP_LIN; ALL_TAC];;

let C981LPP_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C981LPP_LIN; ALL_TAC];;

let C981LPP_CONTRA = ONCE_REWRITE_TAC[GSYM REAL_NOT_LT; GSYM REAL_NOT_LE] THEN DISCH_TAC;;

let C981LPP_RING tm units = SUBGOAL_THEN tm ASSUME_TAC THENL
  [MAP_EVERY UNDISCH_TAC units THEN CONV_TAC REAL_RING; ALL_TAC];;

let C981LPP_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

(* contradiction with an omitted point (term ~linside ...) *)
let C981LPP_MISS_TAC t =
  UNDISCH_TAC t THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> false`) THEN
  REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C981LPP_LIN;;

let C981LPP_POS_OF_MUL = prove
 (`forall k x. &0 < k /\ &0 < k * x ==> &0 < x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= k * --x` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: neighbor_faces_any *)
let C981LPP_NEIGHBOR_FACES_ANY = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ c977cc_normal c s /\ &1 < a /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     linside c s u v a (&1) (&113 / &50) /\ linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&1) (&2) /\ ~linside c s u v a (&8 / &5) (&2) /\
     ~linside c s u v a (&1) (&3) /\ ~linside c s u v a (&8 / &5) (&3)
     ==> c + &2 * s <= u /\ &2 * c - (&8 / &5) * s <= v /\
         u + a <= (&8 / &5) * c + &3 * s /\ v + a <= &3 * c - s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  C981LPP_UNFOLD_TAC `linside c s u v a (&33 / &20) (&47 / &20)` THEN
  C981LPP_UNFOLD_TAC `linside c s u v a (&1) (&113 / &50)` THEN
  C981LPP_UNFOLD_TAC `linside c s u v a (&1) (&12 / &5)` THEN
  SUBGOAL_THEN `v + a <= &3 * c - s` ASSUME_TAC THENL
   [C981LPP_CONTRA THEN C981LPP_MISS_TAC `~linside c s u v a (&1) (&3)`; ALL_TAC] THEN
  SUBGOAL_THEN `c + &2 * s <= u` ASSUME_TAC THENL
   [C981LPP_CONTRA THEN C981LPP_MISS_TAC `~linside c s u v a (&1) (&2)`; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * c - (&8 / &5) * s <= v` ASSUME_TAC THENL
   [C981LPP_CONTRA THEN C981LPP_MISS_TAC `~linside c s u v a (&8 / &5) (&2)`; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= (&8 / &5) * c + &3 * s` ASSUME_TAC THENL
   [C981LPP_CONTRA THEN C981LPP_MISS_TAC `~linside c s u v a (&8 / &5) (&3)`; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: neighbor_faces *)
let C981LPP_NEIGHBOR_FACES = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ c977cc_normal c s /\ &1 < a /\ &1 / &2 <= s /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     linside c s u v a (&1) (&113 / &50) /\ linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&1) (&2) /\ ~linside c s u v a (&8 / &5) (&2) /\
     ~linside c s u v a (&1) (&3) /\ ~linside c s u v a (&8 / &5) (&3)
     ==> c + &2 * s <= u /\ &2 * c - (&8 / &5) * s <= v /\
         u + a <= (&8 / &5) * c + &3 * s /\ v + a <= &3 * c - s`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC_ALL C981LPP_NEIGHBOR_FACES_ANY) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* Lean: diagonal_support (private) *)
let C981LPP_DIAGONAL_SUPPORT = prove
 (`forall c s u v a r.
     c * c + s * s = &1 /\ &0 < a /\ s = r /\ c977cc_normal c r /\ &0 < c - r /\
     linside c s u v a (&2) (&2) /\
     u + a <= (&113 / &50) * c + &2 * r /\
     v + a <= (&113 / &50) * c - &2 * r /\
     (forall z. &0 <= z ==> z <= &13 / &50 ==> ~linside c s u v a (&2 + z) (&113 / &50 - z))
     ==> (c + r) * (u + a - &2 * (c + r)) + (c - r) * (v + a - &2 * (c - r)) <= &13 / &50`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = r`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  (* noLine *)
  SUBGOAL_THEN `forall x y. x + y = &213 / &50 ==> ~linside c r u v a x y` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
    SUBGOAL_THEN `y = &213 / &50 - x` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (c + r) * (x - &2)` ASSUME_TAC THENL [C981LPP_LIN; ALL_TAC] THEN
    MP_TAC(SPECL [`c + r:real`; `x - &2`] C981LPP_POS_OF_MUL) THEN
    ANTS_TAC THENL [CONJ_TAC THEN C981LPP_LIN; DISCH_TAC] THEN
    SUBGOAL_THEN `&0 < (c - r) * (&113 / &50 - x)` ASSUME_TAC THENL [C981LPP_LIN; ALL_TAC] THEN
    MP_TAC(SPECL [`c - r:real`; `&113 / &50 - x`] C981LPP_POS_OF_MUL) THEN
    ANTS_TAC THENL [CONJ_TAC THEN C981LPP_LIN; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x - &2` o
      check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 1)) THEN
    ANTS_TAC THENL [C981LPP_LIN; ALL_TAC] THEN ANTS_TAC THENL [C981LPP_LIN; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&2 + (x - &2) = x`;
                REAL_ARITH `&113 / &50 - (x - &2) = &213 / &50 - x`] THEN
    ASM_REWRITE_TAC[linside];
    ALL_TAC] THEN
  (* below *)
  SUBGOAL_THEN `forall x y. linside c r u v a x y ==> x + y <= &213 / &50` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN C981LPP_CONTRA THEN
    SUBGOAL_THEN `&0 < x + y - &4` ASSUME_TAC THENL [C981LPP_LIN; ALL_TAC] THEN
    SUBGOAL_THEN `(&13 / &50) / (x + y - &4) * (x + y - &4) = &13 / &50 /\
                  &0 < (&13 / &50) / (x + y - &4) /\ (&13 / &50) / (x + y - &4) < &1`
      MP_TAC THENL
     [ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LT_DIV; REAL_LT_LDIV_EQ] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT CONJ_TAC THEN
      TRY(MATCH_MP_TAC REAL_LT_DIV) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`(&13 / &50) / (x + y - &4)`,`t:real`) THEN GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`c:real`; `r:real`; `u:real`; `v:real`; `a:real`; `&2`; `&2`; `x:real`; `y:real`;
                  `t:real`] CES_INSIDE_SEGMENT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(&1 - t) * &2 + t * x`; `(&1 - t) * &2 + t * y`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `&213 / &50`)) (concl th) &&
        not (can (find_term ((=) `&13 / &50`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `t * (x + y - &4) = &13 / &50` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* limit *)
  SUBGOAL_THEN `&0 <= &213 / &50 - ((c + r) * (u + a) + (c - r) * (v + a))` ASSUME_TAC THENL
   [MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `&2 * c`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`c * (u + a - t) - r * (v + a - t)`;
                                  `r * (u + a - t) + c * (v + a - t)`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `&213 / &50`)) (concl th) &&
        can (find_term ((=) `linside`)) (concl th) &&
        not (can (find_term ((=) `&13 / &50`)) (concl th)))) THEN
    MP_TAC(SPECL [`c:real`; `r:real`; `u:real`; `v:real`; `a:real`;
                  `u + a - t`; `v + a - t`] TSS_INSIDE_FACE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN C981LPP_LIN;
    ALL_TAC] THEN
  C981LPP_LIN);;

(* Lean: impossible *)
let C981LPP_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB r.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     sC = r /\ c977cc_normal cC r /\ c977cc_normal cB sB /\
     &1 < aC /\ aC = aB /\ r < &8 / &25 /\ &1 / &2 <= sB /\
     linside cC sC uC vC aC (&2) (&2) /\
     linside cC sC uC vC aC (&69 / &50) (&2) /\
     linside cC sC uC vC aC (&2) (&3 / &2) /\
     linside cC sC uC vC aC (&33 / &20) (&33 / &20) /\
     ~linside cC sC uC vC aC (&33 / &20) (&47 / &20) /\
     ~linside cC sC uC vC aC (&47 / &20) (&33 / &20) /\
     (forall z. &0 <= z ==> z <= &13 / &50 ==>
          ~linside cC sC uC vC aC (&2 + z) (&113 / &50 - z)) /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&1) (&113 / &50) /\
     linside cB sB uB vB aB (&1) (&12 / &5) /\
     ~linside cB sB uB vB aB (&1) (&2) /\ ~linside cB sB uB vB aB (&8 / &5) (&2) /\
     ~linside cB sB uB vB aB (&1) (&3) /\ ~linside cB sB uB vB aB (&8 / &5) (&3) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`] C981LPP_NEIGHBOR_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `r:real`] C981LPS_SMALL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`] C981LPS_NEIGHBOR_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sC:real = r`)) THEN
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal; REAL_POW_2] th)) ns) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `&0 < cC /\ &0 < cB /\ &0 < sB` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN C981LPP_LIN; ALL_TAC] THEN
  C981LPP_UNFOLD_TAC `linside cC r uC vC aC (&2) (&2)` THEN
  C981LPP_UNFOLD_TAC `linside cC r uC vC aC (&69 / &50) (&2)` THEN
  C981LPP_UNFOLD_TAC `linside cC r uC vC aC (&2) (&3 / &2)` THEN
  C981LPP_UNFOLD_TAC `linside cC r uC vC aC (&33 / &20) (&33 / &20)` THEN
  SUBGOAL_THEN `vC + aC <= --(&33 / &20) * r + (&47 / &20) * cC` ASSUME_TAC THENL
   [C981LPP_CONTRA THEN C981LPP_MISS_TAC `~linside cC r uC vC aC (&33 / &20) (&47 / &20)`;
    ALL_TAC] THEN
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`cC:real`; `r:real`; `&7 / &10`; `&7 / &10`] WFP_SHORT_PROJECTIONS)) THEN
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`cC:real`; `r:real`; `&7 / &10`; `--(&7 / &10)`] WFP_SHORT_PROJECTIONS)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `uC + aC <= (&47 / &20) * cC + (&33 / &20) * r` ASSUME_TAC THENL
   [C981LPP_CONTRA THEN C981LPP_MISS_TAC `~linside cC r uC vC aC (&47 / &20) (&33 / &20)`;
    ALL_TAC] THEN
  C981LPP_PROD `&0 < cB * cC` THEN C981LPP_PROD `&0 <= sB * r` THEN
  C981LPP_PROD `&0 <= cC * (sB - &1 / &2)` THEN C981LPP_PROD `&0 <= r * (&1 - cB)` THEN
  C981LPP_FACT `&0 < sB * cC - cB * r` THEN
  (* the separation modes *)
  SUBGOAL_THEN `vC + aC <= ABT_lower cB sB uB vB aC (--r) cC \/
                ABT_upper cC r uC vC aC (--sB) cB <= vB` ASSUME_TAC THENL
   [(let sqC = [`cC:real`; `r:real`; `uC:real`; `vC:real`; `aC:real`]
    and sqB = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`] in
    ABT_SB_TAC sqC `&2` `&2` `cC:real` `r:real` THEN
    ABT_SB_TAC sqC `&2` `&2` `cB:real` `sB:real` THEN
    ABT_SB_TAC sqB `&33 / &20` `&47 / &20` `cC:real` `r:real` THEN
    ABT_SB_TAC sqB `&33 / &20` `&47 / &20` `cB:real` `sB:real` THEN
    ABT_SB_TAC sqB `&33 / &20` `&47 / &20` `--r:real` `cC:real` THEN
    ABT_SB_TAC sqB `&33 / &20` `&47 / &20` `--sB:real` `cB:real` THEN
    ABT_SB_TAC sqC `&33 / &20` `&33 / &20` `--r:real` `cC:real` THEN
    ABT_SB_TAC sqC `&33 / &20` `&33 / &20` `--sB:real` `cB:real` THEN
    ABT_SB_TAC sqB `&1` `&12 / &5` `cB:real` `sB:real` THEN
    ABT_OWN_TAC sqC THEN ABT_OWN_TAC sqB THEN
    MP_TAC(SPECL (sqC @ sqB) ABT_FOUR_AXES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
    (FIRST [MATCH_MP_TAC(TAUT `false ==> p`) THEN C981LPP_LIN;
            DISJ1_TAC THEN C981LPP_LIN;
            DISJ2_TAC THEN C981LPP_LIN;
            ALL_TAC]) THEN
    (* upper B (cB,sB) <= lower C (cB,sB) *)
    MATCH_MP_TAC(TAUT `false ==> p`) THEN
    SUBGOAL_THEN `ABT_lower cC r uC vC aC cB sB =
                  (cB * cC + sB * r) * uC + (sB * cC - cB * r) * vC` ASSUME_TAC THENL
     [REWRITE_TAC[C981SF_LOWER_IN_BANDS] THEN
      SUBGOAL_THEN `abs(cB * cC + sB * r) = cB * cC + sB * r /\
                    abs(--cB * r + sB * cC) = sB * cC - cB * r` (fun th -> REWRITE_TAC[th]) THENL
       [CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ x = y ==> abs x = y`) THEN
        CONJ_TAC THEN (C981LPP_LIN ORELSE REAL_ARITH_TAC);
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    C981LPP_PROD `&0 <= (cB * cC + sB * r) * (((&47 / &20) * cC + (&33 / &20) * r - &1) - uC)` THEN
    C981LPP_PROD `&0 < (sB * cC - cB * r) * ((--(&2) * r + (&3 / &2) * cC) - vC)` THEN
    C981LPP_RING
     `(cB * cC + sB * r) * ((&47 / &20) * cC + (&33 / &20) * r - &1) +
      (sB * cC - cB * r) * (--(&2) * r + (&3 / &2) * cC) -
      ((&33 / &20) * cB + (&47 / &20) * sB) =
      cB * (&7 / &10 - cC - (&7 / &20) * r * r + (&3 / &20) * cC * r) +
      sB * (--(&17 / &20) - r + (&3 / &20) * r * r + (&7 / &20) * cC * r)`
     [`cC * cC + r * r = &1`] THEN
    C981LPP_PROD `&0 <= r * (&1 - cC)` THEN
    C981LPP_PROD `&0 <= r * (&8 / &25 - r)` THEN
    C981LPP_PROD `&0 <= r * r` THEN
    C981LPP_FACT `&7 / &10 - cC - (&7 / &20) * r * r + (&3 / &20) * cC * r < &0` THEN
    C981LPP_FACT `--(&17 / &20) - r + (&3 / &20) * r * r + (&7 / &20) * cC * r < &0` THEN
    C981LPP_PROD `&0 < cB * --(&7 / &10 - cC - (&7 / &20) * r * r + (&3 / &20) * cC * r)` THEN
    C981LPP_PROD `&0 < sB * --(--(&17 / &20) - r + (&3 / &20) * r * r + (&7 / &20) * cC * r)` THEN
    C981LPP_LIN);
    ALL_TAC] THEN
  (* u, v *)
  C981LPP_FACT `(&31 / &50) * r < vC + aC - &2 * (cC - r)` THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [(* cv *)
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `--r:real`; `cC:real`]
      C981NPR_LOWER_PP) THEN
    ANTS_TAC THENL [CONJ_TAC THEN C981LPP_LIN; DISCH_TAC] THEN
    C981LPP_PROD `&0 <= (sB * cC - cB * r) * (((&8 / &5) * cB + &3 * sB - &1) - uB)` THEN
    C981LPP_PROD `&0 <= (cB * cC + sB * r) * ((&3 * cB - sB - &1) - vB)` THEN
    C981LPP_RING
     `(sB * cC - cB * r) * ((&8 / &5) * cB + &3 * sB - &1) +
      (cB * cC + sB * r) * (&3 * cB - sB - &1) - &2 * (cC - r) =
      --cC * (cB + sB - &1 - (&3 / &5) * cB * sB) +
      r * ((cB - sB - &1 / &4 + (&3 / &5) * sB * sB) + &13 / &20)`
     [`cB * cB + sB * sB = &1`] THEN
    C981LPP_PROD `&0 <= cC * ((cB + sB - &1 - (&3 / &5) * cB * sB) - &53 / &500)` THEN
    C981LPP_PROD `&0 <= r * (&917 / &1000 - ((cB - sB - &1 / &4 + (&3 / &5) * sB * sB) + &13 / &20))` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG]) THEN
    C981LPP_LIN;
    ALL_TAC] THEN
  (* bv *)
  SUBGOAL_THEN `ABT_upper cC r uC vC aC (--sB) cB =
                --(sB * cC - cB * r) * uC + (cB * cC + sB * r) * (vC + aC)` ASSUME_TAC THENL
   [REWRITE_TAC[C981SF_UPPER_IN_BANDS] THEN
    SUBGOAL_THEN `abs(--sB * cC + cB * r) = sB * cC - cB * r /\
                  abs(-- --sB * r + cB * cC) = cB * cC + sB * r`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH
        `(&0 <= y /\ (x = y \/ x = --y)) ==> abs x = y`) THEN
      (CONJ_TAC THENL [C981LPP_LIN; REAL_ARITH_TAC]);
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  C981LPP_RING
   `--(sB * cC - cB * r) * uC + (cB * cC + sB * r) * (vC + aC) =
    &2 * (cB - sB) + aC * (sB * cC - cB * r) -
    (sB * cC - cB * r) * (uC + aC - &2 * (cC + r)) +
    (cB * cC + sB * r) * (vC + aC - &2 * (cC - r))` [`cC * cC + r * r = &1`] THEN
  SUBGOAL_THEN `uC + aC <= (&113 / &50) * cC + &2 * r` ASSUME_TAC THENL
   [C981LPP_CONTRA THEN
    FIRST_ASSUM(MP_TAC o SPEC `&13 / &50` o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `&113 / &50`)) (concl th))) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[linside] THEN
    REPEAT CONJ_TAC THEN C981LPP_LIN;
    ALL_TAC] THEN
  SUBGOAL_THEN `uC + aC - &2 * (cC + r) <= (&13 / &50) * r \/
                vC + aC - &2 * (cC - r) <= (&13 / &50) * cC` ASSUME_TAC THENL
   [ASM_CASES_TAC `uC + aC - &2 * (cC + r) <= (&13 / &50) * r` THEN ASM_REWRITE_TAC[] THEN
    C981LPP_CONTRA THEN
    FIRST_ASSUM(MP_TAC o SPEC `&0` o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `&113 / &50`)) (concl th))) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[linside] THEN
    REPEAT CONJ_TAC THEN C981LPP_LIN;
    ALL_TAC] THEN
  C981LPP_PROD `&0 < (aC - &1) * (&1 + (sB * cC - cB * r))` THEN
  C981LPP_PROD `&0 <= (cB * cC + sB * r) * ((vC + aC - &2 * (cC - r)) - (&31 / &50) * r)` THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [C981LPP_PROD `&0 <= (sB * cC - cB * r) * ((&13 / &50) * r - (uC + aC - &2 * (cC + r)))` THEN
    MP_TAC(SPECL [`cC:real`; `r:real`; `cB:real`; `sB:real`] C981LPS_FIRST_IMPOSSIBLE) THEN
    MATCH_MP_TAC(TAUT `p ==> (p ==> false) ==> false`) THEN
    ASM_REWRITE_TAC[REAL_POW_2] THEN REPEAT CONJ_TAC THEN C981LPP_LIN;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `r:real`; `uC:real`; `vC:real`; `aC:real`; `r:real`]
    C981LPP_DIAGONAL_SUPPORT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN C981LPP_LIN;
    DISCH_TAC] THEN
  C981LPP_PROD `&0 <= (sB * cC - cB * r) *
     (&13 / &50 - ((cC + r) * (uC + aC - &2 * (cC + r)) + (cC - r) * (vC + aC - &2 * (cC - r))))` THEN
  C981LPP_PROD `&0 <= (cB + sB) * ((vC + aC - &2 * (cC - r)) - (&31 / &50) * r)` THEN
  C981LPP_RING
   `((sB * cC - cB * r) * (cC - r) + (cB * cC + sB * r) * (cC + r)) * (vC + aC - &2 * (cC - r)) =
    (cB + sB) * (vC + aC - &2 * (cC - r))` [`cC * cC + r * r = &1`] THEN
  C981LPP_FACT `&0 <= cB + sB + (sB * cC - cB * r) * (uC + aC - &2 * (cC + r)) -
                (cB * cC + sB * r) * (vC + aC - &2 * (cC - r)) - aC * (&1 + (sB * cC - cB * r))` THEN
  C981LPP_PROD `&0 <= (cC + r) * (cB + sB + (sB * cC - cB * r) * (uC + aC - &2 * (cC + r)) -
                (cB * cC + sB * r) * (vC + aC - &2 * (cC - r)) - aC * (&1 + (sB * cC - cB * r)))` THEN
  C981LPP_PROD `&0 < (cC + r) * ((aC - &1) * (&1 + (sB * cC - cB * r)))` THEN
  C981LPP_FACT `cC + r < (cC + r) * (cB * (&1 + r) + sB * (&13 / &50 + &1 - cC)) -
                (&22 / &25) * (cB + sB) * r` THEN
  SUBGOAL_THEN `&0 < cC + r` ASSUME_TAC THENL [C981LPP_LIN; ALL_TAC] THEN
  SUBGOAL_THEN
   `(cC + r) * (cB * (&1 + r - (&22 / &25) * r / (cC + r)) +
                sB * (&13 / &50 + (&1 - cC) - (&22 / &25) * r / (cC + r)) - &1) =
    (cC + r) * (cB * (&1 + r) + sB * (&13 / &50 + &1 - cC)) -
    (&22 / &25) * (cB + sB) * r - (cC + r)` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < cC + r` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC(SPECL [`cC + r:real`;
     `cB * (&1 + r - (&22 / &25) * r / (cC + r)) +
      sB * (&13 / &50 + (&1 - cC) - (&22 / &25) * r / (cC + r)) - &1`] C981LPP_POS_OF_MUL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C981LPP_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `r:real`; `cB:real`; `sB:real`] C981LPS_SECOND_IMPOSSIBLE) THEN
  MATCH_MP_TAC(TAUT `p ==> (p ==> false) ==> false`) THEN
  ASM_REWRITE_TAC[] THEN C981LPP_LIN);;
