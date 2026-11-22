(* ========================================================================= *)
(* Port of Compact/Completion/C981/LastRightFaces.lean                        *)
(* (N12Compact.C981CompletionLastRightFaces).  Actual support faces in the   *)
(* final C981 right-wall comparison.  Normal is c977cc_normal, Minor is      *)
(* c981lrs_minor, upper / lower are ABT_upper / ABT_lower, strict_bounds is  *)
(* ABT_STRICT_BOUNDS, faceSeparation_of_disjoint + separated + the radius    *)
(* identities are ABT_FOUR_AXES, ownU is ABT_OWNU, upper_in_bands /          *)
(* lower_in_bands are C981SF_*, cross_order is C981OS_CROSS_ORDER.           *)
(* B.translated dx dy is the explicit square (c, s, u - c*dx - s*dy,         *)
(* v + s*dx - c*dy, a).  Tag C981LRF_.                                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_LastRightScalars.ml";;
needs "n12/geometry/CP_C981_LastPositivePair.ml";;
needs "n12/geometry/CP_C981_CornerAdvance.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;
needs "n12/geometry/CP_C981_OppositeSupport.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* Lean: inside_translated_iff (S12), explicit form *)
let C981LRF_INSIDE_TRANSLATED = prove
 (`forall c s u v a dx dy x y.
     linside c s (u - c * dx - s * dy) (v + s * dx - c * dy) a x y <=>
     linside c s u v a (x + dx) (y + dy)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: faces *)
let C981LRF_FACES = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ c977cc_normal c s /\ &1 < a /\
     linside c s u v a (--(&7 / &20)) (&7 / &20) /\
     linside c s u v a (--(&1)) (&13 / &50) /\ linside c s u v a (--(&1)) (&2 / &5) /\
     ~linside c s u v a (--(&1)) (&0) /\ ~linside c s u v a (--(&2 / &5)) (&0) /\
     ~linside c s u v a (--(&1)) (&1) /\ ~linside c s u v a (--(&2 / &5)) (&1)
     ==> --c <= u /\ (&2 / &5) * s <= v /\
         u + a <= s - (&2 / &5) * c /\ v + a <= c + s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - c * --(&2) - s * --(&2)`;
                `v + s * --(&2) - c * --(&2)`; `a:real`] C981LPP_NEIGHBOR_FACES_ANY) THEN
  REWRITE_TAC[C981LRF_INSIDE_TRANSLATED] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: upper_wall *)
let C981LRF_UPPER_WALL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\
               (forall x y. linside c s u v a x y ==> y <= &2)
     ==> s * (u + a) + c * (v + a) <= &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - c * &0 - s * &1`; `v + s * &0 - c * &1`; `a:real`]
    C981CA_UPPER_WALL) THEN
  ASM_REWRITE_TAC[C981LRF_INSIDE_TRANSLATED] THEN ANTS_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_ARITH]);;

let C981LRF_SB sq x y nx ny =
  MP_TAC(SPECL (sq @ [x; y; nx; ny]) ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; STRIP_TAC];;

let C981LRF_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   NLIN_TAC ~deg2:false []; ALL_TAC];;

let C981LRF_BANDS_TAC =
  let al = `cB * cR + sB * sR` and bt = `cB * sR - sB * cR` in
  let up = SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `--sR`; `cR:real`] C981SF_UPPER_IN_BANDS
  and lo = SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `--sR`; `cR:real`] C981SF_LOWER_IN_BANDS in
  let e1 = REAL_ARITH `--sR * cB + cR * sB = --(cB * sR - sB * cR)`
  and e2 = REAL_ARITH `-- --sR * sB + cR * cB = cB * cR + sB * sR` in
  ASSUME_TAC(REWRITE_RULE[e1; e2] up) THEN ASSUME_TAC(REWRITE_RULE[e1; e2] lo) THEN
  C981LRF_PROD `&0 < cB * cR` THEN C981LRF_PROD `&0 <= sB * sR` THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`abs`, al), al)) (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC (mk_binop `(<=):real->real->bool` bt `&0`) THENL
   [SUBGOAL_THEN (mk_eq(mk_comb(`abs`, mk_comb(`(--):real->real`, bt)), mk_comb(`(--):real->real`, bt)))
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`; `cR:real`; `sR:real`] C981OS_CROSS_ORDER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; STRIP_TAC];
    SUBGOAL_THEN (mk_eq(mk_comb(`abs`, mk_comb(`(--):real->real`, bt)), bt))
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [ASM_REAL_ARITH_TAC; ALL_TAC]];;
let C981LRF_RING tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [UNDISCH_TAC `cB * cB + sB * sB = &1` THEN CONV_TAC REAL_RING; ALL_TAC];;

(* Lean: alternatives *)
let C981LRF_ALTERNATIVES = prove
 (`forall cB sB uB vB aB cR sR uR vR aR.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     c977cc_normal cB sB /\ &0 < cR /\ &0 <= sR /\ &1 < aB /\ aB = aR /\
     c981lrs_minor cB sB /\
     (--cB <= uB /\ (&2 / &5) * sB <= vB /\
      uB + aB <= sB - (&2 / &5) * cB /\ vB + aB <= cB + sB) /\
     linside cB sB uB vB aB (--(&1)) (&2 / &5) /\
     linside cR sR uR vR aR (--(&2 / &5)) (&1) /\ linside cR sR uR vR aR (&13 / &50) (&1) /\
     ldisj cB sB uB vB aB cR sR uR vR aR
     ==> uB + aB <= ABT_lower cR sR uR vR aR cB sB \/
         ABT_upper cB sB uB vB aB cR sR <= uR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aB:real = aR`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (can (term_match [] `c977cc_normal x y`) o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c981lrs_minor] o
    check (can (term_match [] `c981lrs_minor x y`) o concl)) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aB:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [(* B's U axis *)
    DISJ1_TAC THEN ASM_REAL_ARITH_TAC;
    DISJ1_TAC THEN
    C981LRF_SB [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] `--(&1)` `&2 / &5` `cB:real` `sB:real` THEN
    C981LRF_SB [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aB:real`] `&13 / &50` `&1` `cB:real` `sB:real` THEN
    ASM_REAL_ARITH_TAC;
    (* B's V axis: noBV *)
    C981LRF_SB [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] `--(&1)` `&2 / &5` `--sB` `cB:real` THEN
    C981LRF_SB [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aB:real`] `&13 / &50` `&1` `--sB` `cB:real` THEN
    ASM_REAL_ARITH_TAC;
    C981LRF_SB [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] `--(&1)` `&2 / &5` `--sB` `cB:real` THEN
    C981LRF_SB [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aB:real`] `--(&2 / &5)` `&1` `--sB` `cB:real` THEN
    ASM_REAL_ARITH_TAC;
    (* R's U axis *)
    DISJ2_TAC THEN ASM_REAL_ARITH_TAC;
    DISJ2_TAC THEN
    C981LRF_SB [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] `--(&1)` `&2 / &5` `cR:real` `sR:real` THEN
    C981LRF_SB [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aB:real`] `&13 / &50` `&1` `cR:real` `sR:real` THEN
    ASM_REAL_ARITH_TAC;
    (* R's V axis: noRV, forward *)
    C981LRF_BANDS_TAC THENL
     [C981LRF_SB [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aB:real`] `&13 / &50` `&1` `--sR` `cR:real` THEN
  C981LRF_PROD `&0 <= --(cB * sR - sB * cR) * (uB - --cB)` THEN
  C981LRF_PROD `&0 <= (cB * cR + sB * sR) * (vB - (&2 / &5) * sB)` THEN
  C981LRF_PROD `&0 < ((cB * cR + sB * sR) - (cB * sR - sB * cR)) * (aB - &1)` THEN
  C981LRF_PROD `&0 <= (&1 / &2 - sB) * (&1 / &2 + sB)` THEN
  C981LRF_PROD `&0 < cR * (cB + sB - &1 - (&3 / &5) * cB * sB)` THEN
  C981LRF_PROD `&0 <= sR * (&63 / &50 + sB - cB - (&3 / &5) * sB pow 2)` THEN
  C981LRF_RING `--(cB * sR - sB * cR) * (&1 - cB) + (cB * cR + sB * sR) * (&1 + (&2 / &5) * sB) -
     (cR - (&13 / &50) * sR) = cR * (cB + sB - &1 - (&3 / &5) * cB * sB) +
     sR * (&63 / &50 + sB - cB - (&3 / &5) * sB pow 2)` THEN
  ASM_REAL_ARITH_TAC;
      C981LRF_SB [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] `--(&1)` `&2 / &5` `--sR` `cR:real` THEN
  C981LRF_SB [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aB:real`] `&13 / &50` `&1` `--sR` `cR:real` THEN
  C981LRF_PROD `&0 < cR * ((&63 / &50) * sB - (&3 / &5) * cB)` THEN
  SUBGOAL_THEN `&0 < cB * ((&63 / &50) * sR - (&3 / &5) * cR)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&63 / &50) * sR - (&3 / &5) * cR` ASSUME_TAC THENL
   [MATCH_MP_TAC C981LPP_POS_OF_MUL THEN EXISTS_TAC `cB:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC];
    (* R's V axis: noRV, reverse *)
    C981LRF_BANDS_TAC THENL
     [C981LRF_SB [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] `--(&1)` `&2 / &5` `--sR` `cR:real` THEN
  C981LRF_SB [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aB:real`] `--(&2 / &5)` `&1` `--sR` `cR:real` THEN
  ASM_REAL_ARITH_TAC;
      C981LRF_SB [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aB:real`] `--(&2 / &5)` `&1` `--sR` `cR:real` THEN
  C981LRF_PROD `&0 <= (cB * sR - sB * cR) * (uB - --cB)` THEN
  C981LRF_PROD `&0 <= (cB * cR + sB * sR) * (cB + sB - aB - vB)` THEN
  C981LRF_PROD `&0 < ((cB * cR + sB * sR) + (cB * sR - sB * cR)) * (aB - &1)` THEN
  C981LRF_PROD `&0 <= (&1 - cB) * sB` THEN
  SUBGOAL_THEN `sB - cB - sB pow 2 < &0` ASSUME_TAC THENL
   [MP_TAC(SPEC `sB:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&3 / &5 + cB * sB - cB - sB <= &0` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cR * (sB - cB - sB pow 2) < &0` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `x * y < &0 <=> &0 < x * --y`] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sR * (&3 / &5 + cB * sB - cB - sB) <= &0` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= x * --y`] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C981LRF_RING `(cB * cR + sB * sR) * (cB + sB - &1) + (cB * sR - sB * cR) * (cB - &1) -
     (cR + (&2 / &5) * sR) = cR * (sB - cB - sB pow 2) + sR * (&3 / &5 + cB * sB - cB - sB)` THEN
  ASM_REAL_ARITH_TAC]]);;
