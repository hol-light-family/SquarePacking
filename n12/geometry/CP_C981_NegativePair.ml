(* ========================================================================= *)
(* Port of Compact/Completion/C981/NegativePair.lean                          *)
(* (N12Compact.C981CompletionNegativePair).  The retained negative/negative  *)
(* two-square ending.  C has sC = --r with c977cc_normal cC r; B has         *)
(* sB = --t with c977cc_normal cB t.  The Lean lets alpha, h, k, F, G, u, v,  *)
(* H, q are written out.  short_projections is WFP_SHORT_PROJECTIONS.        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_NegativePoint.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let C981NPR_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

let C981NPR_POS_OF_MUL = prove
 (`forall k x. &0 < k /\ &0 < k * x ==> &0 < x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= k * --x` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let C981NPR_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC];;

(* substitute the negative sines and add the normal bounds *)
let C981NPR_SETUP_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sB:real = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sC:real = --r`)) THEN
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal; REAL_POW_2] th)) ns) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]);;

(* Lean: lower_pp *)
let C981NPR_LOWER_PP = prove
 (`forall c s u v a x y. &0 <= x * c + y * s /\ &0 <= --x * s + y * c
     ==> ABT_lower c s u v a x y = (x * c + y * s) * u + (--x * s + y * c) * v`,
  MATCH_ACCEPT_TAC C981NP_LOWER_PP);;

(* Lean: central_cap *)
let C981NPR_CENTRAL_CAP = prove
 (`forall cC sC uC vC aC r.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ sC = --r /\ c977cc_normal cC r /\
     linside cC sC uC vC aC (&2) (&2) /\ linside cC sC uC vC aC (&2) (&3 / &2) /\
     ~linside cC sC uC vC aC (&47 / &20) (&33 / &20)
     ==> uC + aC <= (&47 / &20) * cC - (&33 / &20) * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sC:real = --r`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (can (term_match [] `c977cc_normal x y`) o concl)) THEN
  C981NPR_UNFOLD_TAC `linside cC (--r) uC vC aC (&2) (&2)` THEN
  C981NPR_UNFOLD_TAC `linside cC (--r) uC vC aC (&2) (&3 / &2)` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~linside cC (--r) uC vC aC (&47 / &20) (&33 / &20)` THEN
  REWRITE_TAC[linside] THEN ASM_REAL_ARITH_TAC);;

(* one separating-axis case of `alternatives`; C = (cC,sC,uC,vC), B = (cB,sB,uB,vB), *)
(* common side aB                                                                  *)
let C981NPR_CASE_TAC nx ny swap radius points =
  let sep = SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aB:real`;
                   `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; nx; ny]
                  ABT_SEPARATED in
  let sb ((c,s,u,v),(x,y)) =
    MP_TAC(SPECL [c; s; u; v; `aB:real`; x; y; nx; ny] ABT_STRICT_BOUNDS) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
     ASM_REAL_ARITH_TAC; STRIP_TAC] in
  MP_TAC sep THEN ANTS_TAC THENL
  [(if swap then MATCH_MP_TAC(REAL_ARITH `b + a <= x ==> a + b <= x:real`)
    else ALL_TAC) THEN
   MP_TAC radius THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY sb points THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC; RASM_ARITH_TAC];;

(* Lean: alternatives (private) *)
let C981NPR_ALTERNATIVES = prove
 (`forall cC sC uC vC aC cB sB uB vB aB r t.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     sC = --r /\ c977cc_normal cC r /\ sB = --t /\ c977cc_normal cB t /\
     &1 < aC /\ aC = aB /\
     uC + aC <= (&47 / &20) * cC - (&33 / &20) * r /\
     linside cC sC uC vC aC (&2) (&2) /\
     linside cC sC uC vC aC (&33 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&1) (&12 / &5) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> uB + aB <= ABT_lower cC sC uC vC aC cB (--t) \/
         vC + aC <= ABT_lower cB sB uB vB aB r cC \/
         ABT_upper cC sC uC vC aC t cB <= vB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `r = --sC /\ t = --sB` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
  [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = aB`)) THEN
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `&7 / &10`; `--(&7 / &10)`] WFP_SHORT_PROJECTIONS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aB:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aB:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aB:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[C977CB_faceSep]] THEN
  let qC = (`cC:real`,`sC:real`,`uC:real`,`vC:real`)
  and qB = (`cB:real`,`sB:real`,`uB:real`,`vB:real`) in
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
  [C981NPR_CASE_TAC `cC:real` `sC:real` false
     (SPECL [`cC:real`; `sC:real`; `aB:real`; `cB:real`; `sB:real`; `aB:real`]
       ABT_PARALLEL_RADIUS)
     [qC,(`&2`,`&2`); qB,(`&33 / &20`,`&47 / &20`)];
   C981NPR_CASE_TAC `--sC:real` `cC:real` false
     (SPECL [`cC:real`; `sC:real`; `aB:real`; `cB:real`; `sB:real`; `aB:real`]
       ABT_TRANSVERSE_RADIUS)
     [qC,(`&33 / &20`,`&33 / &20`); qB,(`&33 / &20`,`&47 / &20`)];
   C981NPR_CASE_TAC `cB:real` `sB:real` true
     (SPECL [`cB:real`; `sB:real`; `aB:real`; `cC:real`; `sC:real`; `aB:real`]
       ABT_PARALLEL_RADIUS)
     [qC,(`&2`,`&2`); qB,(`&1`,`&12 / &5`)];
   C981NPR_CASE_TAC `--sB:real` `cB:real` true
     (SPECL [`cB:real`; `sB:real`; `aB:real`; `cC:real`; `sC:real`; `aB:real`]
       ABT_TRANSVERSE_RADIUS)
     [qC,(`&33 / &20`,`&33 / &20`); qB,(`&33 / &20`,`&47 / &20`)]]);;

(* Lean: shallow_long_impossible (private) *)
let C981NPR_SHALLOW_LONG_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB r t.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     sC = --r /\ c977cc_normal cC r /\ sB = --t /\ c977cc_normal cB t /\
     &1 < aC /\ uC + aC <= (&47 / &20) * cC - (&33 / &20) * r /\
     linside cC sC uC vC aC (&2) (&3 / &2) /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     &0 <= cB * r - t * cC /\
     uB + aB <= ABT_lower cC sC uC vC aC cB (--t)
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  C981NPR_SETUP_TAC THEN
  C981NPR_UNFOLD_TAC `linside cC (--r) uC vC aC (&2) (&3 / &2)` THEN
  C981NPR_UNFOLD_TAC `linside cB (--t) uB vB aB (&33 / &20) (&47 / &20)` THEN
  SUBGOAL_THEN `r <= &5 / &7` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C981NPR_PROD `&0 < (r - &5 / &7) * (r + &5 / &7)` THEN
   C981NPR_PROD `&0 <= (cC - &7 / &10) * (cC + &7 / &10)` THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C981NPR_PROD `&0 < cB * cC` THEN
  C981NPR_PROD `&0 <= t * r` THEN
  C981NPR_PROD `&0 <= r * (cC - r)` THEN
  C981NPR_PROD `&0 <= r * r` THEN
  SUBGOAL_THEN `&0 < cB * cC + t * r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &17 / &20 - r - (&3 / &20) * r * r + (&7 / &20) * cC * r`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_lower cC (--r) uC vC aC cB (--t) =
                (cB * cC + t * r) * uC + (cB * r - t * cC) * vC` ASSUME_TAC THENL
  [C981NP_FORM_TAC; ALL_TAC] THEN
  C981NPR_PROD `&0 <= (cB * cC + t * r) * ((&47 / &20 * cC - &33 / &20 * r - &1) - uC)` THEN
  C981NPR_PROD `&0 <= (cB * r - t * cC) * ((&2 * r + &3 / &2 * cC) - vC)` THEN
  SUBGOAL_THEN
   `(cB * cC + t * r) * (&47 / &20 * cC - &33 / &20 * r - &1) +
    (cB * r - t * cC) * (&2 * r + &3 / &2 * cC) - (&33 / &20 * cB - &47 / &20 * t) =
    cB * (&7 / &10 - cC - (&7 / &20) * r * r - (&3 / &20) * cC * r) +
    t * (&17 / &20 - r - (&3 / &20) * r * r + (&7 / &20) * cC * r)` ASSUME_TAC THENL
  [UNDISCH_TAC `cC * cC + r * r = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `cB * (&7 / &10 - cC - (&7 / &20) * r * r - (&3 / &20) * cC * r) +
    t * (&17 / &20 - r - (&3 / &20) * r * r + (&7 / &20) * cC * r) <= &0`
  ASSUME_TAC THENL
  [MATCH_MP_TAC C981NP_NONPOS_OF_MUL THEN EXISTS_TAC `cC:real` THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `cC * (cB * (&7 / &10 - cC - (&7 / &20) * r * r - (&3 / &20) * cC * r) +
           t * (&17 / &20 - r - (&3 / &20) * r * r + (&7 / &20) * cC * r)) =
     cB * ((&7 / &10) * (cC + r) - &1) -
     (cB * r - t * cC) * (&17 / &20 - r - (&3 / &20) * r * r + (&7 / &20) * cC * r)`
   SUBST1_TAC THENL
   [UNDISCH_TAC `cC * cC + r * r = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   MATCH_MP_TAC(REAL_ARITH `a <= &0 /\ &0 <= b ==> a - b <= &0`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC C981NP_MUL_NONPOS THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: deep_long_impossible (private) *)
let C981NPR_DEEP_LONG_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB r t.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     sC = --r /\ c977cc_normal cC r /\ sB = --t /\ c977cc_normal cB t /\
     &1 < aC /\ aC = aB /\ uC + aC <= (&47 / &20) * cC - (&33 / &20) * r /\
     linside cC sC uC vC aC (&2) (&2) /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&1) (&12 / &5) /\
     ~linside cB sB uB vB aB (&1) (&3) /\
     ~linside cB sB uB vB aB (&457 / &500) (&2) /\
     cB * r - t * cC < &0 /\
     uB + aB <= ABT_lower cC sC uC vC aC cB (--t)
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  C981NPR_SETUP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  C981NPR_UNFOLD_TAC `linside cC (--r) uC vC aC (&2) (&2)` THEN
  C981NPR_UNFOLD_TAC `linside cB (--t) uB vB aC (&33 / &20) (&47 / &20)` THEN
  C981NPR_UNFOLD_TAC `linside cB (--t) uB vB aC (&1) (&12 / &5)` THEN
  C981NPR_PROD `&0 < cB * cC` THEN
  C981NPR_PROD `&0 <= t * r` THEN
  C981NPR_PROD `&0 <= cB * r` THEN
  SUBGOAL_THEN `&0 < cB * cC + t * r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_lower cC (--r) uC vC aC cB (--t) =
                (cB * cC + t * r) * uC - (t * cC - cB * r) * (vC + aC)` ASSUME_TAC THENL
  [C981NP_FORM_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_lower cC (--r) uC vC aC cB (--t) =
     &2 * (cB - t) + (cB * cC + t * r) * (uC + aC - &2 * (cC - r)) -
     (cB * cC + t * r) * aC - (t * cC - cB * r) * (vC + aC - &2 * (cC + r))`
  ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cC * cC + r * r = &1` THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  C981NPR_PROD `&0 < (cB * cC + t * r) * (aC - &1)` THEN
  SUBGOAL_THEN `&0 < &7 / &20 * (cB + t) -
                (cB * cC + t * r) * (&1 - (uC + aC - &2 * (cC - r))) -
                (t * cC - cB * r) * (vC + aC - &2 * (cC + r))` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  C981NPR_PROD `&0 <= (t * cC - cB * r) * (vC + aC - &2 * (cC + r))` THEN
  SUBGOAL_THEN `cB < &4 * t` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C981NPR_PROD `&0 <= r * (cB - &4 * t)` THEN
   SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
   [MATCH_MP_TAC C981NPR_POS_OF_MUL THEN EXISTS_TAC `cC:real` THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < cC - &4 * r` ASSUME_TAC THENL
   [MATCH_MP_TAC C981NPR_POS_OF_MUL THEN EXISTS_TAC `t:real` THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   C981NPR_PROD `&0 <= r * (&1 / &4 - r)` THEN
   SUBGOAL_THEN `&24 / &25 <= cC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C981NPR_PROD `&0 <= (&24 / &25 - cC) * (&24 / &25 + cC)` THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   C981NPR_PROD `&0 <= cB * (cC - &24 / &25)` THEN
   C981NPR_PROD `&0 <= (cB * cC + t * r) * (&1 - (uC + aC - &2 * (cC - r)) - &9 / &16)` THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&457 / &500 * t + &2 * cB <= vB` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   UNDISCH_TAC `~linside cB (--t) uB vB aC (&457 / &500) (&2)` THEN
   REWRITE_TAC[linside] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C981NPR_PROD `&0 <= (&1 - cB) * (&1 - cB)` THEN
  C981NPR_PROD `&0 < t * (t / &2 - &43 / &500)` THEN
  SUBGOAL_THEN `cB + &43 / &500 * t < &1` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cB - &3 * t <= uB` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   UNDISCH_TAC `~linside cB (--t) uB vB aC (&1) (&3)` THEN
   REWRITE_TAC[linside] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C981NPR_PROD `&0 <= (cC + r - &1) * (&13 / &20 - &7 / &20 * (cC + r))` THEN
  C981NPR_PROD `&0 <= (cB - t) * (cC - r)` THEN
  C981NPR_PROD `&0 <= (&1 - &7 / &20 * (cC + r)) *
                      (&2 * (cB * cC + t * r) - (cB + t) * (cC + r))` THEN
  C981NPR_PROD `&0 <= (cB + t) * ((cC + r) * (&1 - &7 / &20 * (cC + r)) - &13 / &20)` THEN
  C981NPR_PROD `&0 <= (cB * cC + t * r) * (&7 / &20 * (cC + r) - (uC + aC - &2 * (cC - r)))` THEN
  C981NPR_PROD `&0 < (&1 + cB * cC + t * r) * (aC - &1)` THEN
  RASM_ARITH_TAC);;

(* Lean: impossible *)
let C981NPR_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB r t.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     sC = --r /\ c977cc_normal cC r /\ sB = --t /\ c977cc_normal cB t /\
     &1 < aC /\ aC = aB /\
     linside cC sC uC vC aC (&2) (&2) /\
     linside cC sC uC vC aC (&2) (&3 / &2) /\
     linside cC sC uC vC aC (&33 / &20) (&33 / &20) /\
     ~linside cC sC uC vC aC (&47 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&1) (&12 / &5) /\
     ~linside cB sB uB vB aB (&8 / &5) (&3) /\
     ~linside cB sB uB vB aB (&1) (&3) /\
     ~linside cB sB uB vB aB (&457 / &500) (&2) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sB:real = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sC:real = --r`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = aB`)) THEN
  MP_TAC(SPECL [`cC:real`; `--r:real`; `uC:real`; `vC:real`; `aB:real`; `r:real`]
    C981NPR_CENTRAL_CAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--r:real`; `uC:real`; `vC:real`; `aB:real`;
                `cB:real`; `--t:real`; `uB:real`; `vB:real`; `aB:real`; `r:real`; `t:real`]
    C981NPR_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
  [ASM_CASES_TAC `&0 <= cB * r - t * cC` THENL
   [MP_TAC(SPECL [`cC:real`; `--r:real`; `uC:real`; `vC:real`; `aB:real`;
                  `cB:real`; `--t:real`; `uB:real`; `vB:real`; `aB:real`; `r:real`; `t:real`]
      C981NPR_SHALLOW_LONG_IMPOSSIBLE) THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`cC:real`; `--r:real`; `uC:real`; `vC:real`; `aB:real`;
                  `cB:real`; `--t:real`; `uB:real`; `vB:real`; `aB:real`; `r:real`; `t:real`]
      C981NPR_DEEP_LONG_IMPOSSIBLE) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
   UNDISCH_TAC `~linside cB (--t) uB vB aB (&8 / &5) (&3)` THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC C981NP_POINT THEN
   MAP_EVERY EXISTS_TAC [`cC:real`; `--r:real`; `uC:real`; `vC:real`; `aB:real`;
                         `r:real`; `t:real`] THEN
   ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   UNDISCH_TAC `~linside cB (--t) uB vB aB (&8 / &5) (&3)` THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC C981NP_POINT THEN
   MAP_EVERY EXISTS_TAC [`cC:real`; `--r:real`; `uC:real`; `vC:real`; `aB:real`;
                         `r:real`; `t:real`] THEN
   ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC]);;
