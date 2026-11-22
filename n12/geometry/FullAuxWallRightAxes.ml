(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallRightAxes.lean (Jatloe, N12-jatloe)   *)
(* (namespace N12Compact.FullAuxWallRightAxes).                              *)
(* Actual right-neighbour SAT reduction without an assumed crossing point;   *)
(* both signs of the right square's canonical frame are retained.            *)
(* Lean upper/lower are ABT_upper/ABT_lower; strict_bounds, ownU/ownV and    *)
(* the four separating axes are ABT_STRICT_BOUNDS, ABT_OWNU/ABT_OWNV and     *)
(* ABT_FOUR_AXES.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/CentralWallPairSupport.ml";;
needs "n12/geometry/FullAuxWallRightMargin.ml";;

let FAWRA_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let FAWRA_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let FAWRA_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let FAWRA_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

(* Support values with known coefficient signs (helpers). *)
let FAWRA_LOWER_NEG = prove
 (`forall c s u v a nx ny. nx * c + ny * s <= &0 /\ &0 <= --nx * s + ny * c
     ==> ABT_lower c s u v a nx ny =
         (nx * c + ny * s) * (u + a) + (--nx * s + ny * c) * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy] THEN
  ASM_SIMP_TAC[REAL_ARITH `x <= &0 ==> abs x = --x`; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  REAL_ARITH_TAC);;

let FAWRA_UPPER_POS = prove
 (`forall c s u v a nx ny. &0 <= nx * c + ny * s /\ &0 <= --nx * s + ny * c
     ==> ABT_upper c s u v a nx ny =
         (nx * c + ny * s) * (u + a) + (--nx * s + ny * c) * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ABT_upper; tss_support_radius; lcx; lcy] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  REAL_ARITH_TAC);;

(* Lean: positive_lower (private) *)
let FAWRA_POSITIVE_LOWER = prove
 (`forall cA sA uA vA aA cR sR.
     c977cc_normal cA sA /\ c977cc_normal cR sR /\ &1 < aA /\ &4 * sA <= cA /\
     &2 * (cA + sA) <= uA /\ linside cA sA uA vA aA (&113 / &50) (&2) /\
     vA + aA <= &3 * cA - (&12 / &5) * sA
     ==> ABT_lower cA sA uA vA aA (--sR) cR < (&12 / &5) * cR - &3 * sR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWRA_NORMAL_TAC THEN
  SUBGOAL_THEN `cA * cA + sA * sA = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_CASES_TAC `cA * sR <= sA * cR` THENL
  [FAWRA_PROD_TAC `cR:real` `cA - &4 * sA` THEN
   SUBGOAL_THEN `&4 * sR <= cR` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
   ABT_SB_TAC [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
     `&113 / &50` `&2` `--sR` `cR:real` THEN
   RASM_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cA * cR + sA * sR` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN RASM_ARITH_TAC;
   ALL_TAC] THEN
  FAWRA_USE FAWRA_LOWER_NEG
    [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `--sR`; `cR:real`] THEN
  FAWRA_USE FAWRM_CENTRAL_BOUNDS [`cA:real`; `sA:real`] THEN
  FAWRA_PROD_TAC `cA * sR - sA * cR` `(uA + aA) - (&2 * (cA + sA) + &1)` THEN
  FAWRA_PRODLT_TAC `cA * cR + sA * sR` `(&3 * cA - (&12 / &5) * sA - &1) - vA` THEN
  FAWRA_PROD_TAC `sA:real` `&1 - cA` THEN
  SUBGOAL_THEN
   `&0 <= cA - sA - &3 / &5 + sA pow 2 + (&2 / &5) * cA * sA /\
    &0 <= (cA - sA - &3 / &5 + sA pow 2 + (&2 / &5) * cA * sA) +
          (cA + sA - &1 + (&2 / &5) * sA pow 2 - cA * sA)` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC ~deg2:false [SQ_NONNEG `sA:real`]; ALL_TAC] THEN
  FAWRA_PROD_TAC `cR - sR` `cA - sA - &3 / &5 + sA pow 2 + (&2 / &5) * cA * sA` THEN
  FAWRA_PROD_TAC `sR:real`
    `(cA - sA - &3 / &5 + sA pow 2 + (&2 / &5) * cA * sA) +
     (cA + sA - &1 + (&2 / &5) * sA pow 2 - cA * sA)` THEN
  SUBGOAL_THEN
   `(&12 / &5) * cR - &3 * sR -
    (--(cA * sR - sA * cR) * (&2 * (cA + sA) + &1) +
     (cA * cR + sA * sR) * (&3 * cA - (&12 / &5) * sA - &1)) =
    cR * (cA - sA - &3 / &5 + sA pow 2 + (&2 / &5) * cA * sA) +
    sR * (cA + sA - &1 + (&2 / &5) * sA pow 2 - cA * sA)` ASSUME_TAC THENL
  [UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: negative_upper (private) *)
let FAWRA_NEGATIVE_UPPER = prove
 (`forall cA sA uA vA aA cR sR t.
     c977cc_normal cA sA /\ c977cc_normal cR t /\ sR = --t /\ &1 < aA /\
     &4 * sA <= cA /\ &2 * (cA + sA) <= uA /\
     linside cA sA uA vA aA (&5 / &2) (&3)
     ==> (&1543 / &500) * t + &2 * cR < ABT_upper cA sA uA vA aA t cR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWRA_NORMAL_TAC THEN
  FAWRA_USE FAWRM_CENTRAL_BOUNDS [`cA:real`; `sA:real`] THEN
  FAWRA_PROD_TAC `sA:real` `cR - t` THEN
  FAWRA_PRODLT_TAC `cR:real` `cA - sA` THEN
  SUBGOAL_THEN `&0 <= cA * t + sA * cR /\ &0 < cA * cR - sA * t` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    RASM_ARITH_TAC; RASM_ARITH_TAC]; ALL_TAC] THEN
  FAWRA_USE FAWRA_UPPER_POS
    [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `t:real`; `cR:real`] THEN
  UNDISCH_TAC `linside cA sA uA vA aA (&5 / &2) (&3)` THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  FAWRA_PROD_TAC `cA * t + sA * cR` `(uA + aA) - (&2 * (cA + sA) + &1)` THEN
  FAWRA_PRODLT_TAC `cA * cR - sA * t` `(vA + aA) - (&3 * cA - (&5 / &2) * sA)` THEN
  FAWRA_PROD_TAC `sA:real` `&1 - cA` THEN
  FAWRA_PROD_TAC `&1 / &4 - sA` `sA + &1 / &4` THEN
  SUBGOAL_THEN
   `&0 <= &1 - sA pow 2 - (&1 / &2) * cA * sA + sA /\
    &0 <= (&1 - sA pow 2 - (&1 / &2) * cA * sA + sA) +
          (cA - &543 / &500 + (&1 / &2) * sA pow 2 - cA * sA)` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWRA_PROD_TAC `cR - t` `&1 - sA pow 2 - (&1 / &2) * cA * sA + sA` THEN
  FAWRA_PROD_TAC `t:real`
    `(&1 - sA pow 2 - (&1 / &2) * cA * sA + sA) +
     (cA - &543 / &500 + (&1 / &2) * sA pow 2 - cA * sA)` THEN
  SUBGOAL_THEN
   `(cA * t + sA * cR) * (&2 * (cA + sA) + &1) +
    (cA * cR - sA * t) * (&3 * cA - (&5 / &2) * sA) -
    ((&1543 / &500) * t + &2 * cR) =
    cR * (&1 - sA pow 2 - (&1 / &2) * cA * sA + sA) +
    t * (cA - &543 / &500 + (&1 / &2) * sA pow 2 - cA * sA)` ASSUME_TAC THENL
  [UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: alternatives *)
let FAWRA_ALTERNATIVES = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     c977cc_normal cA sA /\ cR * cR + sR * sR = &1 /\ &0 < cR /\
     --cR <= sR /\ sR <= cR /\ &1 < aA /\ aA = aR /\ &4 * sA <= cA /\
     &2 * (cA + sA) <= uA /\ --(&47 / &20) * sA + (&33 / &20) * cA <= vA /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     linside cA sA uA vA aA (&5 / &2) (&3) /\
     vA + aA <= &3 * cA - (&12 / &5) * sA /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> uA + aA <= ABT_lower cR sR uR vR aR cA sA \/
         ABT_upper cA sA uA vA aA cR sR <= uR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWRA_NORMAL_TAC THEN
  SUBGOAL_THEN `cA * cA + sA * sA = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < aR /\ &0 < aA` STRIP_ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = aR`)) THEN
  let sqA = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aR:real`]
  and sqR = [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] in
  MP_TAC(SPECL sqA ABT_OWNU) THEN MP_TAC(SPECL sqA ABT_OWNV) THEN MP_TAC(SPECL sqR ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY (fun (sq,(x,y),(nx,ny)) -> ABT_SB_TAC sq x y nx ny)
   [sqR,(`&1543 / &500`,`&2`),(`cA:real`,`sA:real`);
    sqR,(`&3`,`&12 / &5`),(`--sA`,`cA:real`);
    sqR,(`&1543 / &500`,`&2`),(`--sR`,`cR:real`);
    sqR,(`&3`,`&12 / &5`),(`--sR`,`cR:real`);
    sqA,(`&47 / &20`,`&47 / &20`),(`--sR`,`cR:real`);
    sqA,(`&113 / &50`,`&2`),(`--sR`,`cR:real`);
    sqA,(`&113 / &50`,`&2`),(`cR:real`,`sR:real`)] THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (can (term_match [] `linside c s u v a x y`) o concl) ths)) THEN
  SUBGOAL_THEN
   `~(ABT_upper cA sA uA vA aR (--sR) cR <= ABT_lower cR sR uR vR aR (--sR) cR) /\
    ~(ABT_upper cR sR uR vR aR (--sR) cR <= ABT_lower cA sA uA vA aR (--sR) cR)`
  STRIP_ASSUME_TAC THENL
  [ASM_CASES_TAC `&0 <= sR` THENL
   [SUBGOAL_THEN `c977cc_normal cR sR` ASSUME_TAC THENL
    [REWRITE_TAC[c977cc_normal] THEN REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
     UNDISCH_TAC `cR * cR + sR * sR = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    FAWRA_USE FAWRA_POSITIVE_LOWER (sqA @ [`cR:real`; `sR:real`]) THEN
    CONJ_TAC THEN RASM_ARITH_TAC;
    SUBGOAL_THEN `c977cc_normal cR (--sR)` ASSUME_TAC THENL
    [REWRITE_TAC[c977cc_normal] THEN REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
     UNDISCH_TAC `cR * cR + sR * sR = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    FAWRA_USE FAWRA_NEGATIVE_UPPER (sqA @ [`cR:real`; `sR:real`; `--sR`]) THEN
    CONJ_TAC THEN RASM_ARITH_TAC];
   ALL_TAC] THEN
  MP_TAC(SPECL (sqA @ sqR) ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN RASM_ARITH_TAC);;
