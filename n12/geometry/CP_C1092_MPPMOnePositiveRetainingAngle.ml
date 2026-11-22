(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMOnePositiveRetainingAngle.lean        *)
(* (N12Compact.C1092MPPMOnePositive).  ONE-POSITIVE-CONTINUOUS-ENDING Lemma *)
(* 3.1: the next retaining negative owner's slope is below one half.        *)
(* Squares C, E are c s u v a, cE sE uE vE aE (OpenSquare invariants        *)
(* explicit).  RetainingPairInput is c1092opra_input; upper / lower /       *)
(* strict_bounds / ownU are ABT_*; signed_axes C1092SPTS_SIGNED_AXES;       *)
(* lower_nn C1092WS_LOWER_NN; upper_pos_neg C1092TFSU_UPPER_POS_NEG;        *)
(* AllNonpositive.Core / faces c1092anc_core / C1092ANC_FACES.  The lets    *)
(* k, delta, Q, R are written out.  Tag C1092OPRA_.                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMOnePositiveMissingEnding.ml";;

let C1092OPRA_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092OPRA_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [C1092OPRA_LP_TAC; REAL_ARITH_TAC]; ALL_TAC];;

(* Lean: RetainingPairInput (structure) *)
let c1092opra_input = new_definition
 `c1092opra_input (c:real) (s:real) (u:real) (v:real) (a:real)
                  (cE:real) (sE:real) (uE:real) (vE:real) (aE:real) <=>
    c1092anc_core c s u v a /\ a = aE /\ &97 / &100 < c /\ &4 * --s < c /\
    v + a < &43 / &500 /\ c977cc_normal cE (--sE) /\
    linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
    linside cE sE uE vE aE (&13 / &50) (--(&1)) /\
    linside cE sE uE vE aE (&0) (--(&13 / &50)) /\
    ldisj c s u v a cE sE uE vE aE`;;

(* Lean: cone (local have of retaining_pair_axes) *)
let C1092OPRA_CONE = prove
 (`forall c s u v a cE sE uE vE aE nx ny.
     c * c + s * s = &1 /\ &0 < a /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     nx pow 2 + ny pow 2 = &1 /\
     linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&13 / &50) (--(&1)) /\
     ABT_upper c s u v a nx ny <= ABT_lower cE sE uE vE aE nx ny
     ==> &0 < nx /\ &0 < (&61 / &100) * nx - (&13 / &20) * ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (sq, (x, y)) ->
    MP_TAC(SPECL (sq @ [x; y; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC)
   [[`c:real`; `s:real`; `u:real`; `v:real`; `a:real`], (`--(&7 / &20)`, `--(&7 / &20)`);
    [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`], (`&7 / &20`, `--(&7 / &20)`);
    [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`], (`&13 / &50`, `--(&1)`)] THEN
  C1092OPRA_LP_TAC);;

let C1092OPRA_UNPACK_TAC =
  REWRITE_TAC[c1092opra_input; IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `a:real = aE`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092anc_core] o
    check (fun th -> can (term_match [] `c1092anc_core c s u v a`) (concl th))) THEN
  MAP_EVERY (fun tm ->
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
      check (fun th -> concl th = tm)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
      check (fun th -> concl th = tm)))
   [`c977cc_normal c (--s)`; `c977cc_normal cE (--sE)`];;

let C1092OPRA_CONE_TAC =
  FIRST_ASSUM(fun th ->
    let tm = concl th in
    if is_binary "real_le" tm &&
       (try fst(dest_const(fst(strip_comb(lhand tm)))) = "ABT_upper" with Failure _ -> false)
    then
      let args = snd(strip_comb(lhand tm)) in
      let nx = el 5 args and ny = el 6 args in
      MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                    `cE:real`; `sE:real`; `uE:real`; `vE:real`; `a:real`; nx; ny]
                   C1092OPRA_CONE) THEN
      ANTS_TAC THENL
      [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_2] THEN
       MAP_EVERY (fun t -> MP_TAC(ASSUME t))
         [`c * c + s * s = &1`; `cE * cE + sE * sE = &1`] THEN REAL_ARITH_TAC;
       STRIP_TAC THEN C1092OPRA_LP_TAC]
    else NO_TAC);;

(* Lean: retaining_pair_axes (private) *)
let C1092OPRA_RETAINING_PAIR_AXES = prove
 (`forall c s u v a cE sE uE vE aE.
     c * c + s * s = &1 /\ &0 < a /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092opra_input c s u v a cE sE uE vE aE
     ==> u + a <= ABT_lower cE sE uE vE aE c s \/ ABT_upper c s u v a cE sE <= uE`,
  REPEAT GEN_TAC THEN C1092OPRA_UNPACK_TAC THEN
  SUBGOAL_THEN `--s < &1 / &4` ASSUME_TAC THENL [C1092OPRA_LP_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `a:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `a:real`] C1092SPTS_SIGNED_AXES) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN C1092OPRA_CONE_TAC);;

(* Lean: steep_retaining_support (private) *)
let C1092OPRA_STEEP_RETAINING_SUPPORT = prove
 (`forall c s d t. c977cc_normal c s /\ &97 / &100 < c /\ &4 * s < c /\ c977cc_normal d t /\
             d <= &2 * t
     ==> (c * d + s * t) * (&13 / &50) * t + (c * t - s * d) * ((&13 / &50) * t - d) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun tm ->
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
      check (fun th -> concl th = tm)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
      check (fun th -> concl th = tm)))
   [`c977cc_normal c s`; `c977cc_normal d t`] THEN
  C1092OPRA_PROD `&0 <= d * (d - t)` THEN C1092OPRA_PROD `&0 < d * d` THEN
  C1092OPRA_PROD `&0 <= t * t` THEN
  SUBGOAL_THEN `&0 < d * d + (&13 / &50) * t * t - (&13 / &50) * d * t` ASSUME_TAC THENL
  [C1092OPRA_LP_TAC; ALL_TAC] THEN
  C1092OPRA_PROD `&0 < (c / &4 - s) * (d * d + (&13 / &50) * t * t - (&13 / &50) * d * t)` THEN
  C1092OPRA_PROD `&0 <= (t - d / &2) * ((&257 / &400) * d - (&13 / &40) * t)` THEN
  SUBGOAL_THEN `(&1 / &4) * d * d - (&161 / &200) * d * t + (&13 / &40) * t * t <=
                --(&57 / &800) * d * d` ASSUME_TAC THENL
  [C1092OPRA_LP_TAC; ALL_TAC] THEN
  C1092OPRA_PROD `&0 <= c * (--(&57 / &800) * d * d -
     ((&1 / &4) * d * d - (&161 / &200) * d * t + (&13 / &40) * t * t))` THEN
  C1092OPRA_PROD `&0 < c * (d * d)` THEN
  C1092OPRA_LP_TAC);;

(* Lean: retaining_successor_half_slope *)
let C1092OPRA_RETAINING_SUCCESSOR_HALF_SLOPE = prove
 (`forall c s u v a cE sE uE vE aE.
     c * c + s * s = &1 /\ &0 < a /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092opra_input c s u v a cE sE uE vE aE
     ==> &2 * --sE < cE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092OPRA_RETAINING_PAIR_AXES) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `c1092opra_input c s u v a cE sE uE vE aE`) (concl th))) THEN
  C1092OPRA_UNPACK_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092ANC_FACES) THEN
  ASM_REWRITE_TAC[c1092anc_faces] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MAP_EVERY (fun tm -> UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside cE sE uE vE a (&13 / &50) (--(&1))`;
    `linside cE sE uE vE a (&0) (--(&13 / &50))`] THEN
  (* k = c * cE + s * sE, delta = --c * sE + s * cE *)
  C1092OPRA_PROD `&0 < c * cE` THEN C1092OPRA_PROD `&0 < --s * --sE` THEN
  SUBGOAL_THEN `&0 < c * cE + s * sE` ASSUME_TAC THENL [C1092OPRA_LP_TAC; ALL_TAC] THEN
  C1092OPRA_PROD `&0 < (c - &97 / &100) * --sE` THEN
  C1092OPRA_PROD `&0 < (c + &4 * s) * --sE` THEN
  C1092OPRA_PROD `&0 <= --s * (--(&2) * sE - cE)` THEN
  SUBGOAL_THEN `(&97 / &200) * --sE < --c * sE + s * cE` ASSUME_TAC THENL
  [C1092OPRA_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < --c * sE + s * cE` ASSUME_TAC THENL [C1092OPRA_LP_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC o check (is_disj o concl)) THENL
  [MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `a:real`; `c:real`; `s:real`;
                 `c * cE + s * sE`; `--c * sE + s * cE`] C1092WS_LOWER_NN) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
   C1092OPRA_PROD `&0 < (c * cE + s * sE) * ((&13 / &50) * --sE - uE)` THEN
   C1092OPRA_PROD `&0 < (--c * sE + s * cE) * ((&13 / &50) * --sE - cE - vE)` THEN
   MP_TAC(SPECL [`c:real`; `--s`; `cE:real`; `--sE`] C1092OPRA_STEEP_RETAINING_SUPPORT) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
   C1092OPRA_LP_TAC;
   MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `cE:real`; `sE:real`;
                 `c * cE + s * sE`; `--(--c * sE + s * cE)`] C1092TFSU_UPPER_POS_NEG) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
   C1092OPRA_PROD `&0 <= (c * cE + s * sE) * (u + c)` THEN
   C1092OPRA_PROD `&0 < (--c * sE + s * cE) * (&43 / &500 - v - a)` THEN
   C1092OPRA_PROD `&0 < (a - &1) * ((c * cE + s * sE) + (--c * sE + s * cE))` THEN
   C1092OPRA_PROD `&0 <= (c * cE + s * sE) * (&1 - c)` THEN
   C1092OPRA_LP_TAC]);;

(* Lean: retaining_successor_bounds *)
let C1092OPRA_RETAINING_SUCCESSOR_BOUNDS = prove
 (`forall c s u v a cE sE uE vE aE.
     c * c + s * s = &1 /\ &0 < a /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092opra_input c s u v a cE sE uE vE aE
     ==> &89 / &100 < cE /\ --sE < &9 / &20`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092OPRA_RETAINING_SUCCESSOR_HALF_SLOPE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092opra_input] o check (fun th ->
    can (term_match [] `c1092opra_input c s u v a cE sE uE vE aE`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cE (--sE)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cE (--sE)`)) THEN
  C1092OPRA_PROD `&0 < (cE + &2 * sE) * (cE - &2 * sE)` THEN
  CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THENL
  [C1092OPRA_PROD `&0 <= (cE + &89 / &100) * (&89 / &100 - cE)` THEN C1092OPRA_LP_TAC;
   C1092OPRA_PROD `&0 <= (--sE - &9 / &20) * (--sE + &9 / &20)` THEN C1092OPRA_LP_TAC]);;
