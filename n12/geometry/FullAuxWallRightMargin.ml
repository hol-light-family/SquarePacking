(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallRightMargin.lean (Jatloe, N12-jatloe) *)
(* (namespace N12Compact.FullAuxWallRightMargin).                            *)
(* Quadratic support margin for the full positive right-wall square.         *)
(* The Lean local abbreviations A, B, M, ((&2 / &5) * s pow 2 - (&1 - c) * (&1 - s)) are written out in full.         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

let FAWRM_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let FAWRM_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let FAWRM_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let FAWRM_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

(* Lean: central_bounds *)
let FAWRM_CENTRAL_BOUNDS = prove
 (`forall c s. c977cc_normal c s /\ &4 * s <= c
     ==> &24 / &25 <= c /\ s <= &1 / &4 /\ &1 - c <= (&25 / &49) * s pow 2 /\
         --(&3 / &25) * s pow 2 <= (&2 / &5) * s pow 2 - (&1 - c) * (&1 - s) /\
         &11 / &100 <= c - s - &3 / &5 + s pow 2 + (&2 / &5) * c * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWRM_NORMAL_TAC THEN
  SUBGOAL_THEN `s <= &1 / &4` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  FAWRM_PROD_TAC `&1 / &4 - s` `&1 / &4 + s` THEN
  SUBGOAL_THEN `&24 / &25 <= c` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   FAWRM_PRODLT_TAC `&24 / &25 - c` `&24 / &25 + c` THEN NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  FAWRM_PROD_TAC `&1 - c` `c - &24 / &25` THEN
  NLIN_FACTS_TAC [] [`&1 - c <= (&25 / &49) * s pow 2`] THEN
  FAWRM_PROD_TAC `s:real` `&1 - c` THEN
  FAWRM_PROD_TAC `c:real` `s:real` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `s:real`]);;

(* Lean: positive_u_margin *)
let FAWRM_POSITIVE_U_MARGIN = prove
 (`forall c s r t. c977cc_normal c s /\ c977cc_normal r t /\ &4 * s <= c /\ t <= s
     ==> &0 <= r * (&1 + c * r + s * t - &2 * c) - (&457 / &500) * s * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FAWRM_USE FAWRM_CENTRAL_BOUNDS [`c:real`; `s:real`] THEN
  FAWRM_USE C977CSB_COSINE_ORDER [`c:real`; `s:real`; `r:real`; `t:real`] THEN
  FAWRM_NORMAL_TAC THEN
  FAWRM_PROD_TAC `r:real` `r - c` THEN
  FAWRM_PROD_TAC `r:real` `&1 - c` THEN
  FAWRM_PROD_TAC `r * (&1 - c)` `&1 - r` THEN
  FAWRM_PROD_TAC `s:real` `t:real` THEN
  FAWRM_PROD_TAC `s * t` `r - &457 / &500` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: negative_u_margin *)
let FAWRM_NEGATIVE_U_MARGIN = prove
 (`forall c s r t. c977cc_normal c s /\ c977cc_normal r t /\ &4 * s <= c
     ==> &0 <= r + (c * r - s * t) * (r + t) - &2 * c * r + (&457 / &500) * s * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWRM_NORMAL_TAC THEN
  FAWRM_PROD_TAC `t:real` `&1 + r - &2 * t` THEN
  SUBGOAL_THEN `t / &2 <= r + t - &1` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= (&1 + r) * (&2 * r + t - &2)` MP_TAC THENL
   [SUBGOAL_THEN `(&1 + r) * (&2 * r + t - &2) = t * (&1 + r - &2 * t)` SUBST1_TAC THENL
    [UNDISCH_TAC `r pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  FAWRM_PROD_TAC `r:real` `&1 - c` THEN
  FAWRM_PROD_TAC `c:real` `r:real` THEN
  FAWRM_PROD_TAC `c * r` `(r + t - &1) - t / &2` THEN
  FAWRM_PROD_TAC `s:real` `t:real` THEN
  FAWRM_PROD_TAC `s * t` `&3 / &5 - (r + t - &457 / &500)` THEN
  FAWRM_PROD_TAC `t:real` `c / &4 - s` THEN
  FAWRM_PROD_TAC `c:real` `t:real` THEN
  FAWRM_PROD_TAC `c * t` `r / &2 - &3 / &20` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: baseline_margin *)
let FAWRM_BASELINE_MARGIN = prove
 (`forall c s r t. c977cc_normal c s /\ c977cc_normal r t /\ &4 * s <= c /\ t <= s
     ==> (&2 / &5) * s pow 2 - (&1 - c) * (&1 - s) <=
      r pow 2 * (&2 + (&2 / &5) * s pow 2 - c * s) + r * t * (&1 - s pow 2 - (&2 / &5) * c * s) +
      r * ((c * r + s * t) - (c * t - s * r) + &1) + (&1543 / &500) * t pow 2 - &4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FAWRM_USE FAWRM_CENTRAL_BOUNDS [`c:real`; `s:real`] THEN
  FAWRM_USE C977CSB_COSINE_ORDER [`c:real`; `s:real`; `r:real`; `t:real`] THEN
  FAWRM_NORMAL_TAC THEN
  FAWRM_PROD_TAC `&1 / &4 - s` `&1 / &4 + s` THEN
  FAWRM_PROD_TAC `&1 - r` `r - &24 / &25` THEN
  NLIN_FACTS_TAC [] [`&1 - r <= (&25 / &49) * t pow 2`] THEN
  FAWRM_PROD_TAC `&1 - c` `&1 - s` THEN
  SUBGOAL_THEN `(&2 + c + s + (&2 / &5) * s pow 2 - c * s) <= &121 / &40` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWRM_PROD_TAC `s:real` `&1 - c` THEN
  FAWRM_PROD_TAC `s:real` `&1 / &4 - s` THEN
  SUBGOAL_THEN `(&1 - c + s - s pow 2 - (&2 / &5) * c * s) - ((&3 / &5) * s - (&1 / &2) * s pow 2) =
                (&1 / &2) * (&1 - c) pow 2 + (&2 / &5) * s * (&1 - c)` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `(&19 / &40) * s <= (&1 - c + s - s pow 2 - (&2 / &5) * c * s)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false [SQ_NONNEG `&1 - c`]; ALL_TAC] THEN
  FAWRM_PROD_TAC `r - &24 / &25` `(&1 - c + s - s pow 2 - (&2 / &5) * c * s)` THEN
  SUBGOAL_THEN `(&57 / &125) * s <= r * (&1 - c + s - s pow 2 - (&2 / &5) * c * s)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWRM_PROD_TAC `t:real` `r * (&1 - c + s - s pow 2 - (&2 / &5) * c * s) - (&57 / &125) * s` THEN
  FAWRM_PROD_TAC `t pow 2` `&121 / &40 - (&2 + c + s + (&2 / &5) * s pow 2 - c * s)` THEN
  FAWRM_PROD_TAC `t:real` `s - t` THEN
  SUBGOAL_THEN `(r pow 2 * (&2 + c + s + (&2 / &5) * s pow 2 - c * s) + r * t * (&1 - c + s - s pow 2 - (&2 / &5) * c * s) + r + (&1543 / &500) * t pow 2 - &4) - ((&2 / &5) * s pow 2 - (&1 - c) * (&1 - s)) = r * t * (&1 - c + s - s pow 2 - (&2 / &5) * c * s) + ((&1543 / &500) - (&2 + c + s + (&2 / &5) * s pow 2 - c * s)) * t pow 2 - (&1 - r)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `r pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `((&2 / &5) * s pow 2 - (&1 - c) * (&1 - s)) <= (r pow 2 * (&2 + c + s + (&2 / &5) * s pow 2 - c * s) + r * t * (&1 - c + s - s pow 2 - (&2 / &5) * c * s) + r + (&1543 / &500) * t pow 2 - &4)` MP_TAC THENL
  [NLIN_TAC ~deg2:false [SQ_NONNEG `t:real`]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Lean: margin *)
let FAWRM_MARGIN = prove
 (`forall c s r t. c977cc_normal c s /\ c977cc_normal r t /\ &4 * s <= c /\ t <= s
     ==> &0 <= r pow 2 * (&2 + (&2 / &5) * s pow 2 - c * s) + r * t * (&1 - s pow 2 - (&2 / &5) * c * s) +
      r * ((c * r + s * t) - (c * t - s * r) + &1) + (&1543 / &500) * t pow 2 - &4 +
      (&1 / &5) * r * (c * r + s * t) * s pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FAWRM_USE FAWRM_CENTRAL_BOUNDS [`c:real`; `s:real`] THEN
  FAWRM_USE FAWRM_BASELINE_MARGIN [`c:real`; `s:real`; `r:real`; `t:real`] THEN
  FAWRM_NORMAL_TAC THEN
  FAWRM_PROD_TAC `&1 / &4 - t` `&1 / &4 + t` THEN
  FAWRM_PROD_TAC `c - &24 / &25` `r pow 2` THEN
  FAWRM_PROD_TAC `r:real` `s:real` THEN
  FAWRM_PROD_TAC `r * s` `t:real` THEN
  SUBGOAL_THEN `&9 / &10 <= r * (c * r + s * t)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWRM_PROD_TAC `s pow 2` `r * (c * r + s * t) - &9 / &10` THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `s:real`]);;
