(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/F4BottomMidpoint.lean         *)
(* (namespace N12Compact.Completion.OtherCases.C983.F4BottomMidpoint).      *)
(* C983-F4 ending, Section 3 (coordinates translated by (-2,-2)).            *)
(* Squares: B = cB sB uB vB aB, E = cE sE uE vE aE; the canonical frame q of *)
(* B is cq sq uq vq a.  upper / lower: ABT_upper / ABT_lower;                *)
(* strict_bounds: ABT_STRICT_BOUNDS; lower_in_bands: C981SF_LOWER_IN_BANDS;  *)
(* WallProfile.upper_neg / lower_neg: OCWPVG_UPPER_NEG / OCWPVG_LOWER_NEG;   *)
(* faceSeparation_of_disjoint: CSAT_FACESEPARATION_OF_DISJOINT; separated,  *)
(* parallel_radius, transverse_radius, ownV: ABT_SEPARATED, ABT_PARALLEL_   *)
(* RADIUS, ABT_TRANSVERSE_RADIUS, ABT_OWNV; short_projections:              *)
(* WFP_SHORT_PROJECTIONS; canonical_frame: CLF_CANONICAL_FRAME;              *)
(* vertical_segment: OO_VERTICAL_SEGMENT.  q.translated 0 (-1) is the tuple  *)
(* (c, s, u + s, v + c, a) (F4BM_TRANSLATE).                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/CongruentSAT.ml";;
needs "n12/geometry/C977ChainBridge.ml";;

(* Lean: SoutheastData (structure) *)
let f4bm_southeast_data = new_definition
 `f4bm_southeast_data (c:real) (s:real) (u:real) (v:real) (a:real) (t:real) <=>
    s = --t /\ &1 < a /\ &19 / &20 < c /\ &0 < t /\ t < &3 / &10 /\ v + a <= t /\
    linside c s u v a (&7 / &20) (--(&7 / &20)) /\
    linside c s u v a (&13 / &50) (&0) /\
    linside c s u v a (&1) (--(&13 / &50))`;;

let F4BM_ARITH_TAC = REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;;

(* expand the positive linside assumptions into atomic real relations *)
let F4BM_EXPAND_TAC =
  RULE_ASSUM_TAC(fun th -> if is_neg (concl th) then th else REWRITE_RULE[linside] th) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;

(* Lean: upper_right_point (private) *)
let F4BM_UPPER_RIGHT_POINT = prove
 (`forall c s u v a t. c * c + s * s = &1 /\ f4bm_southeast_data c s u v a t /\
     ~linside c s u v a (&0) (--(&1 / &2))
     ==> linside c s u v a (&1) (--(&1 / &2))`,
  REWRITE_TAC[f4bm_southeast_data] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL [NLIN_TAC [SQ_NONNEG `t:real`]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> not (is_eq (concl th))))) THEN
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: positive_bottom (private) *)
let F4BM_POSITIVE_BOTTOM = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     &27 / &50 * c < s /\
     linside c s u v a (&0) (&0) /\ linside c s u v a (&0) (&1 / &2) /\
     linside c s u v a (&4 / &5) (&0) /\
     ~linside c s u v a (&7 / &20) (&13 / &20) /\
     ~linside c s u v a (&0) (&37 / &50) /\
     ~linside c s u v a (--(&1 / &25)) (--(&6 / &25)) ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL [NLIN_TAC [SQ_NONNEG `s:real`]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&39 / &100`; `&89 / &100`] WFP_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC] THEN
  F4BM_EXPAND_TAC THEN
  SUBGOAL_THEN `u + a <= &7 / &20 * c + &13 / &20 * s` ASSUME_TAC THENL
   [UNDISCH_TAC `~linside c s u v a (&7 / &20) (&13 / &20)` THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= &37 / &50 * c` ASSUME_TAC THENL
   [UNDISCH_TAC `~linside c s u v a (&0) (&37 / &50)` THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `~linside c s u v a (--(&1 / &25)) (--(&6 / &25))` THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: negative_axis (private) *)
let F4BM_NEGATIVE_AXIS = prove
 (`forall c s u v a t d r. c * c + s * s = &1 /\ f4bm_southeast_data c s u v a t /\
     &0 < d /\ &0 <= r /\ r <= d /\ d pow 2 + r pow 2 = &1
     ==> ABT_lower c s u v a r d < --d / &2`,
  REWRITE_TAC[f4bm_southeast_data] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  F4BM_EXPAND_TAC THEN
  REWRITE_TAC[C981SF_LOWER_IN_BANDS] THEN
  SUBGOAL_THEN `c <= &1 /\ d <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `t:real`; SQ_NONNEG `r:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t * r /\ &0 < c * d` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(--r * --t + d * c) = t * r + c * d` SUBST1_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v < t - &1` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= c * r - t * d` THENL
   [SUBGOAL_THEN `abs(r * c + d * --t) = c * r - t * d` SUBST1_TAC THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (c * r - t * d) * (c * &13 / &50 - u)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (t * r + c * d) * (t - &1 - v)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&3 / &10 - t) * (&1 - &37 / &50 * (t + &3 / &10))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &13 / &50 + &37 / &50 * t pow 2 - t` ASSUME_TAC THENL
     [POP_ASSUM MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&13 / &50 + &37 / &50 * t pow 2 - t) * (d - r)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (c - &19 / &20) * (&1 - &37 / &50 * t) /\
                  &0 <= (&3 / &10 - t) * (&3 / &10 + t)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
      RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&13 / &50 + &37 / &50 * t pow 2 - t) + (&1 / &2 + c * (&37 / &50 * t - &1)) < &0`
      ASSUME_TAC THENL
     [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < d * --((&13 / &50 + &37 / &50 * t pow 2 - t) +
                              (&1 / &2 + c * (&37 / &50 * t - &1)))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `r * (c * c + --t * --t) = r` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
    NLIN_TAC ~deg2:false [];
    SUBGOAL_THEN `abs(r * c + d * --t) = --(c * r - t * d)` SUBST1_TAC THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(c * r - t * d) pow 2 + (t * r + c * d) pow 2 = &1` ASSUME_TAC THENL
     [UNDISCH_TAC `c * c + --t * --t = &1` THEN UNDISCH_TAC `d pow 2 + r pow 2 = &1` THEN
      CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= t * (&1 - d) /\ &0 <= c * r` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `--t <= c * r - t * d` ASSUME_TAC THENL
     [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (t + (c * r - t * d)) * (t - (c * r - t * d))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `c <= t * r + c * d` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < (c - (t * r + c * d)) * (c + (t * r + c * d))` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `&0 <= (t + (c * r - t * d)) * (t - (c * r - t * d))` THEN
      UNDISCH_TAC `(c * r - t * d) pow 2 + (t * r + c * d) pow 2 = &1` THEN
      UNDISCH_TAC `c * c + --t * --t = &1` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= --(c * r - t * d) * (u + a)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (t * r + c * d) * (t - &1 - v)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= ((t * r + c * d) - c) * (&1 - t) /\ &0 < (c - &19 / &20) * (&1 - t)`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
      RASM_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC ~deg2:false []]);;

(* q.translated 0 (-1) *)
let F4BM_TRANSLATE = prove
 (`forall c s u v a x y. linside c s (u + s) (v + c) a x y <=> linside c s u v a x (y - &1)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* the strict support bounds at a point, as an assumption *)
let F4BM_SB_TAC sq (x, y) (nx, ny) =
  MP_TAC(SPECL (sq @ [x; y; nx; ny]) ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_2; REAL_NEG_MUL2] THEN RASM_ARITH_TAC;
    STRIP_TAC];;

(* the local context of the proof of excluded: q the canonical frame of B,
   E = (cE, --t, uE, vE, a) *)
let f4bm_ctx = new_definition
 `f4bm_ctx cq sq uq vq cE uE vE a t <=>
    cq * cq + sq * sq = &1 /\ &0 < cq /\ abs sq <= cq /\
    cE * cE + --t * --t = &1 /\ f4bm_southeast_data cE (--t) uE vE a t /\
    linside cq sq uq vq a (&4 / &5) (-- &1) /\
    linside cq sq uq vq a (&0) (--(&1 / &2)) /\
    linside cq sq uq vq a (&0) (-- &1) /\
    ~linside cq sq uq vq a (&0) (--(&13 / &50)) /\
    ~linside cq sq uq vq a (--(&1 / &25)) (--(&31 / &25)) /\
    linside cE (--t) uE vE a (&1) (--(&1 / &2)) /\
    ldisj cq sq uq vq a cE (--t) uE vE a`;;

let F4BM_Q = [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `a:real`];;
let F4BM_E = [`cE:real`; `--t:real`; `uE:real`; `vE:real`; `a:real`];;

let F4BM_CTX_TAC =
  REWRITE_TAC[f4bm_ctx] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[f4bm_southeast_data] o
    check (fun th -> try fst(strip_comb(concl th)) = `f4bm_southeast_data` with _ -> false)) THEN
  SUBGOAL_THEN `&0 < a /\ cE <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [RASM_ARITH_TAC; NLIN_TAC [SQ_NONNEG `t:real`]]; ALL_TAC];;

(* Lean: cone (local) *)
let F4BM_CONE = prove
 (`forall cq sq uq vq cE uE vE a t nx ny.
     f4bm_ctx cq sq uq vq cE uE vE a t /\ nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cq sq uq vq a nx ny <= ABT_lower cE (--t) uE vE a nx ny ==> &0 < nx`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  REPEAT DISCH_TAC THEN UNDISCH_TAC `f4bm_ctx cq sq uq vq cE uE vE a t` THEN F4BM_CTX_TAC THEN
  F4BM_SB_TAC F4BM_Q (`&0`, `--(&1 / &2)`) (`nx:real`, `ny:real`) THEN
  F4BM_SB_TAC F4BM_E (`&1`, `--(&1 / &2)`) (`nx:real`, `ny:real`) THEN
  RASM_ARITH_TAC);;

(* Lean: reverse (local) *)
let F4BM_REVERSE = prove
 (`forall cq sq uq vq aq cE sE uE vE aE nx ny.
     ABT_upper cE sE uE vE aE nx ny <= ABT_lower cq sq uq vq aq nx ny
     ==> ABT_upper cq sq uq vq aq (--nx) (--ny) <= ABT_lower cE sE uE vE aE (--nx) (--ny)`,
  REWRITE_TAC[OCWPVG_UPPER_NEG; OCWPVG_LOWER_NEG] THEN REAL_ARITH_TAC);;

let F4BM_CONE_TAC nx ny =
  MP_TAC(SPECL [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `cE:real`; `uE:real`; `vE:real`;
                `a:real`; `t:real`; nx; ny] F4BM_CONE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[f4bm_ctx] o
      check (fun th -> try fst(strip_comb(concl th)) = `f4bm_ctx` with _ -> false)) THEN
    REWRITE_TAC[REAL_POW_2; REAL_NEG_MUL2] THEN RASM_ARITH_TAC;
    DISCH_TAC];;

(* backward separation along (nx0, ny0): reverse it, then the cone at the
   opposite normal *)
let F4BM_CONE_REV_TAC nx0 ny0 =
  let neg t = let t' = mk_comb(`(--):real->real`, t) in
              try rhs(concl(REWRITE_CONV[REAL_NEG_NEG] t')) with _ -> t' in
  MP_TAC(SPECL (F4BM_Q @ F4BM_E @ [nx0; ny0]) F4BM_REVERSE) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC] THEN
  F4BM_CONE_TAC (neg nx0) (neg ny0);;

(* Lean: noEU (local) *)
let F4BM_NO_EU = prove
 (`forall cq sq uq vq cE uE vE a t. f4bm_ctx cq sq uq vq cE uE vE a t
     ==> ~(ABT_upper cq sq uq vq a cE (--t) <= ABT_lower cE (--t) uE vE a cE (--t) \/
           ABT_upper cE (--t) uE vE a cE (--t) <= ABT_lower cq sq uq vq a cE (--t))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[DE_MORGAN_THM] THEN CONJ_TAC THEN DISCH_TAC THENL
   [UNDISCH_TAC `f4bm_ctx cq sq uq vq cE uE vE a t` THEN F4BM_CTX_TAC THEN
    F4BM_SB_TAC F4BM_Q (`&4 / &5`, `-- &1`) (`cE:real`, `--t`) THEN
    F4BM_SB_TAC F4BM_E (`&13 / &50`, `&0`) (`cE:real`, `--t`) THEN
    RASM_ARITH_TAC;
    F4BM_CONE_REV_TAC `cE:real` `--t` THEN
    UNDISCH_TAC `f4bm_ctx cq sq uq vq cE uE vE a t` THEN F4BM_CTX_TAC THEN RASM_ARITH_TAC]);;

(* Lean: noEV (local) *)
let F4BM_NO_EV = prove
 (`forall cq sq uq vq cE uE vE a t. f4bm_ctx cq sq uq vq cE uE vE a t
     ==> ~(ABT_upper cq sq uq vq a (-- --t) cE <= ABT_lower cE (--t) uE vE a (-- --t) cE \/
           ABT_upper cE (--t) uE vE a (-- --t) cE <= ABT_lower cq sq uq vq a (-- --t) cE)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[DE_MORGAN_THM] THEN CONJ_TAC THEN DISCH_TAC THENL
   [UNDISCH_TAC `f4bm_ctx cq sq uq vq cE uE vE a t` THEN F4BM_CTX_TAC THEN
    F4BM_SB_TAC F4BM_Q (`&0`, `--(&1 / &2)`) (`-- --t`, `cE:real`) THEN
    MP_TAC(SPECL F4BM_E ABT_OWNV) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    UNDISCH_TAC `ABT_upper cq sq uq vq a (-- --t) cE <= ABT_lower cE (--t) uE vE a (-- --t) cE` THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
    F4BM_CONE_REV_TAC `-- --t` `cE:real` THEN
    UNDISCH_TAC `f4bm_ctx cq sq uq vq cE uE vE a t` THEN F4BM_CTX_TAC THEN RASM_ARITH_TAC]);;

(* Lean: noWU (local) *)
let F4BM_NO_WU = prove
 (`forall cq sq uq vq cE uE vE a t. f4bm_ctx cq sq uq vq cE uE vE a t
     ==> ~(ABT_upper cq sq uq vq a cq sq <= ABT_lower cE (--t) uE vE a cq sq \/
           ABT_upper cE (--t) uE vE a cq sq <= ABT_lower cq sq uq vq a cq sq)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[DE_MORGAN_THM] THEN CONJ_TAC THEN DISCH_TAC THENL
   [ALL_TAC;
    F4BM_CONE_REV_TAC `cq:real` `sq:real` THEN
    UNDISCH_TAC `f4bm_ctx cq sq uq vq cE uE vE a t` THEN F4BM_CTX_TAC THEN RASM_ARITH_TAC] THEN
  UNDISCH_TAC `f4bm_ctx cq sq uq vq cE uE vE a t` THEN F4BM_CTX_TAC THEN
  F4BM_SB_TAC F4BM_Q (`&4 / &5`, `-- &1`) (`cq:real`, `sq:real`) THEN
  F4BM_SB_TAC F4BM_E (`&13 / &50`, `&0`) (`cq:real`, `sq:real`) THEN
  ASM_CASES_TAC `&0 <= sq` THENL [ALL_TAC; RASM_ARITH_TAC] THEN
  ASM_CASES_TAC `sq <= &27 / &50 * cq` THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `uq + sq`; `vq + cq`; `a:real`] F4BM_POSITIVE_BOTTOM) THEN
  REWRITE_TAC[F4BM_TRANSLATE] THEN
  REWRITE_TAC[REAL_ARITH `&0 - &1 = -- &1 /\ &1 / &2 - &1 = --(&1 / &2) /\
                          &13 / &20 - &1 = --(&7 / &20) /\ &37 / &50 - &1 = --(&13 / &50) /\
                          --(&6 / &25) - &1 = --(&31 / &25)`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~linside cq sq uq vq a (&7 / &20) (--(&7 / &20))` (fun th -> REWRITE_TAC[th]) THENL
   [DISCH_TAC THEN UNDISCH_TAC `ldisj cq sq uq vq a cE (--t) uE vE a` THEN
    REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&7 / &20`; `--(&7 / &20)`]) THEN
    ASM_REWRITE_TAC[];
    RASM_ARITH_TAC]);;

(* Lean: noWV (local) *)
let F4BM_NO_WV = prove
 (`forall cq sq uq vq cE uE vE a t. f4bm_ctx cq sq uq vq cE uE vE a t
     ==> ~(ABT_upper cq sq uq vq a (--sq) cq <= ABT_lower cE (--t) uE vE a (--sq) cq \/
           ABT_upper cE (--t) uE vE a (--sq) cq <= ABT_lower cq sq uq vq a (--sq) cq)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[DE_MORGAN_THM] THEN CONJ_TAC THEN DISCH_TAC THENL
   [ASM_CASES_TAC `&0 <= sq` THENL
     [F4BM_CONE_TAC `--sq` `cq:real` THEN RASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `f4bm_ctx cq sq uq vq cE uE vE a t` THEN F4BM_CTX_TAC THEN
    MP_TAC(SPECL [`cE:real`; `--t`; `uE:real`; `vE:real`; `a:real`; `t:real`; `cq:real`; `--sq`]
      F4BM_NEGATIVE_AXIS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_2; REAL_NEG_MUL2] THEN RASM_ARITH_TAC;
      DISCH_TAC] THEN
    F4BM_SB_TAC F4BM_Q (`&0`, `--(&1 / &2)`) (`--sq`, `cq:real`) THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL (F4BM_Q @ F4BM_E @ [`--sq`; `cq:real`]) F4BM_REVERSE) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC] THEN
  ASM_CASES_TAC `&0 <= sq` THENL
   [ALL_TAC; F4BM_CONE_TAC `sq:real` `--cq` THEN RASM_ARITH_TAC] THEN
  UNDISCH_TAC `f4bm_ctx cq sq uq vq cE uE vE a t` THEN F4BM_CTX_TAC THEN
  F4BM_SB_TAC F4BM_Q (`&4 / &5`, `-- &1`) (`sq:real`, `--cq`) THEN
  F4BM_SB_TAC F4BM_E (`&13 / &50`, `&0`) (`sq:real`, `--cq`) THEN
  RASM_ARITH_TAC);;

(* the four face separations of q and E are impossible *)
let F4BM_CORE = prove
 (`forall cq sq uq vq cE uE vE a t. f4bm_ctx cq sq uq vq cE uE vE a t ==> false`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY (fun th -> FIRST_ASSUM(fun c -> ASSUME_TAC(MATCH_MP (SPEC_ALL th) c)))
    [F4BM_NO_EU; F4BM_NO_EV; F4BM_NO_WU; F4BM_NO_WV] THEN
  UNDISCH_TAC `f4bm_ctx cq sq uq vq cE uE vE a t` THEN F4BM_CTX_TAC THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `a:real`; `cE:real`; `--t`; `a:real`] ABT_PARALLEL_RADIUS) THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `a:real`; `cE:real`; `--t`; `a:real`] ABT_TRANSVERSE_RADIUS) THEN
  MP_TAC(SPECL [`cE:real`; `--t`; `a:real`; `cq:real`; `sq:real`; `a:real`] ABT_PARALLEL_RADIUS) THEN
  MP_TAC(SPECL [`cE:real`; `--t`; `a:real`; `cq:real`; `sq:real`; `a:real`] ABT_TRANSVERSE_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL (F4BM_Q @ F4BM_E) CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[C977CB_faceSep] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   (map (fun (nx, ny) ->
      MP_TAC(SPECL (F4BM_Q @ F4BM_E @ [nx; ny]) ABT_SEPARATED) THEN
      ANTS_TAC THENL [RASM_ARITH_TAC; (ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE ASM_MESON_TAC[]])
    [`cq:real`, `sq:real`; `--sq`, `cq:real`; `cE:real`, `--t`; `-- --t`, `cE:real`]));;

(* Lean: excluded *)
let F4BM_EXCLUDED = prove
 (`forall cB sB uB vB aB cE sE uE vE aE t.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     aB = aE /\ f4bm_southeast_data cE sE uE vE aE t /\
     linside cB sB uB vB aB (&0) (--(&543 / &500)) /\
     linside cB sB uB vB aB (&4 / &5) (-- &1) /\
     ~linside cB sB uB vB aB (&0) (--(&13 / &50)) /\
     ~linside cB sB uB vB aB (--(&1 / &25)) (--(&31 / &25)) /\
     ldisj cB sB uB vB aB cE sE uE vE aE
     ==> ~linside cB sB uB vB aB (&0) (--(&1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aB:real = aE`)) THEN
  SUBGOAL_THEN `sE = --t` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[f4bm_southeast_data]; ALL_TAC] THEN
  SUBGOAL_THEN `linside cE (--t) uE vE aE (&1) (--(&1 / &2))` ASSUME_TAC THENL
   [MATCH_MP_TAC F4BM_UPPER_RIGHT_POINT THEN EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `ldisj cB sB uB vB aE cE (--t) uE vE aE` THEN
    REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&0`; `--(&1 / &2)`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linside cB sB uB vB aE (&0) (-- &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN
    MAP_EVERY EXISTS_TAC [`--(&543 / &500)`; `--(&1 / &2)`] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aE:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cq:real` (X_CHOOSE_THEN `sq:real` (X_CHOOSE_THEN `uq:real`
    (X_CHOOSE_THEN `vq:real` (X_CHOOSE_THEN `aq:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aq:real = aE`)) THEN
  MATCH_MP_TAC F4BM_CORE THEN
  MAP_EVERY EXISTS_TAC [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `cE:real`; `uE:real`;
                        `vE:real`; `aE:real`; `t:real`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  ASM_REWRITE_TAC[f4bm_ctx; ldisj]);;
