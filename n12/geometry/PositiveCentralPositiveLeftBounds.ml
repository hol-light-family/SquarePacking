(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveCentralPositiveLeftBounds.lean (Jatloe,  *)
(* N12-jatloe; namespace N12Compact.PositiveCentralPositiveLeftBounds).      *)
(* A continuous positive-left support margin in the missing-west sector.     *)
(* B is pceo_b; in reduced_margin 1/p is written ip = inv p.                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/PositiveCentralEscapeOrder.ml";;
needs "n12/geometry/PositiveCentralEscapeLeft.ml";;

let PCPLB_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PCPLB_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let PCPLB_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PCPLB_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

let PCPLB_NONNEG_OF_MUL = prove
 (`forall k y. &0 < k /\ &0 <= k * y ==> &0 <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: vertexDefect (definition) *)
let pcplb_vertexdefect = new_definition
 `pcplb_vertexdefect (c:real) (s:real) = (&1 - c) * (&1 - s) / c`;;

(* Lean: defect_bound (private) *)
let PCPLB_DEFECT_BOUND = prove
 (`forall c s. c977cc_normal c s /\ &4 / &5 <= c ==> &3 * (&1 - c) <= s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCPLB_NORMAL_TAC THEN
  PCPLB_PROD_TAC `&1 - c` `&10 * c - &8` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  PCPLB_PRODLT_TAC `&3 * (&1 - c) - s` `&3 * (&1 - c) + s` THEN NLIN_TAC ~deg2:false []);;

(* Lean: defect_order *)
let PCPLB_DEFECT_ORDER = prove
 (`forall p q C S. c977cc_normal p q /\ c977cc_normal C S /\ q <= S /\ &4 / &5 <= C /\ S <= &3 / &5
     ==> pcplb_vertexdefect p q <= pcplb_vertexdefect C S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCPLB_USE C977CSB_COSINE_ORDER [`C:real`; `S:real`; `p:real`; `q:real`] THEN
  PCPLB_USE PCPLB_DEFECT_BOUND [`p:real`; `q:real`] THEN
  PCPLB_USE PCPLB_DEFECT_BOUND [`C:real`; `S:real`] THEN
  PCPLB_NORMAL_TAC THEN
  PCPLB_PROD_TAC `&1 - p` `&1 - C` THEN
  PCPLB_PROD_TAC `p:real` `&1 - C` THEN
  SUBGOAL_THEN `p * C <= &1` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCPLB_PROD_TAC `&2 - p - C` `&1 - p * C` THEN
  PCPLB_PROD_TAC `q:real` `&3 / &5 - S` THEN
  PCPLB_PROD_TAC `S:real` `&3 / &5 - q` THEN
  SUBGOAL_THEN `&0 <= p * C * (p + C - &1) - (&1 - S) * (&1 - q)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCPLB_PROD_TAC `S - q` `p * C * (p + C - &1) - (&1 - S) * (&1 - q)` THEN
  SUBGOAL_THEN
   `(p * C * (p + C)) * (pcplb_vertexdefect C S - pcplb_vertexdefect p q) =
    (S - q) * (p * C * (p + C - &1) - (&1 - S) * (&1 - q))` ASSUME_TAC THENL
  [REWRITE_TAC[pcplb_vertexdefect] THEN
   UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN
   (SUBGOAL_THEN `~(p = &0) /\ ~(C = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC]) THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  PCPLB_PRODLT_TAC `p:real` `C:real` THEN
  PCPLB_PRODLT_TAC `p * C` `p + C` THEN
  SUBGOAL_THEN `&0 <= pcplb_vertexdefect C S - pcplb_vertexdefect p q` MP_TAC THENL
  [MATCH_MP_TAC PCPLB_NONNEG_OF_MUL THEN EXISTS_TAC `p * C * (p + C)` THEN
   CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: reduced_margin (private) *)
let PCPLB_REDUCED_MARGIN = prove
 (`forall p q l r. c977cc_normal p q /\ c977cc_normal l r /\ &9 / &10 <= p
     ==> &0 <= ((&1 - l) + r * (l - &2 + (pceo_b p q + q * r) / p) + l * (pcplb_vertexdefect p q + q * (&1 - p)) + r * q * (&1 - p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCPLB_USE C977CSB_DOT_LE_ONE [`p:real`; `q:real`; `l:real`; `r:real`] THEN
  PCPLB_NORMAL_TAC THEN
  ABBREV_TAC `ip = inv p` THEN
  SUBGOAL_THEN `p * ip = &1` ASSUME_TAC THENL
  [EXPAND_TAC "ip" THEN MATCH_MP_TAC REAL_MUL_RINV THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= ip /\ ip <= &10 / &9` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  PCPLB_PROD_TAC `p - &9 / &10` `p + &9 / &10` THEN
  SUBGOAL_THEN `q <= &1 / &2` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   PCPLB_PRODLT_TAC `q - &1 / &2` `q + &1 / &2` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&1 - p <= q` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= p + ip` ASSUME_TAC THENL [NLIN_TAC [SQ_NONNEG `p - &1`]; ALL_TAC] THEN
  PCPLB_PROD_TAC `q:real` `&1 / &10 - (&1 - p)` THEN
  PCPLB_PROD_TAC `q:real` `&1 - p` THEN
  SUBGOAL_THEN `&0 <= (&1 - q * (&1 - p)) /\ (&1 - q * (&1 - p)) <= &1` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCPLB_PROD_TAC `q:real` `p pow 2` THEN
  SUBGOAL_THEN `p * (q * (p + ip) - (&1 - p) * ip) = q * (p pow 2 + &1) - (&1 - p)` ASSUME_TAC THENL
  [UNDISCH_TAC `p * ip = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (q * (p + ip) - (&1 - p) * ip)` ASSUME_TAC THENL
  [MATCH_MP_TAC PCPLB_NONNEG_OF_MUL THEN EXISTS_TAC `p:real` THEN
   CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  PCPLB_PROD_TAC `q:real` `&19 / &9 - (p + ip)` THEN
  PCPLB_PROD_TAC `&1 - p` `ip:real` THEN
  SUBGOAL_THEN `(q * (p + ip) - (&1 - p) * ip) <= (&19 / &9) * q` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCPLB_PROD_TAC `(&1 - q * (&1 - p))` `&1 - (&1 - q * (&1 - p))` THEN
  PCPLB_PROD_TAC `(&19 / &9) * q - (q * (p + ip) - (&1 - p) * ip)` `(&19 / &9) * q + (q * (p + ip) - (&1 - p) * ip)` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `p - &1`] [`q pow 2 <= &2 * (&1 - p)`] THEN
  SUBGOAL_THEN `(&1 - q * (&1 - p)) pow 2 + (q * (p + ip) - (&1 - p) * ip) pow 2 - &1 <= &9 * (&1 - p)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `p * (&1 - q * (&1 - p)) + q * (q * (p + ip) - (&1 - p) * ip) - &1 = (&1 - p) * (p pow 2 + (p + ip) * (&1 - q))`
  ASSUME_TAC THENL
  [UNDISCH_TAC `p * ip = &1` THEN UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  PCPLB_PROD_TAC `(p + ip) - &2` `&1 - q` THEN
  SUBGOAL_THEN `&7 / &4 <= p pow 2 + (p + ip) * (&1 - q)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCPLB_PROD_TAC `&1 - p` `(p pow 2 + (p + ip) * (&1 - q)) - &7 / &4` THEN
  SUBGOAL_THEN `(&7 / &4) * (&1 - p) <= p * (&1 - q * (&1 - p)) + q * (q * (p + ip) - (&1 - p) * ip) - &1` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCPLB_PROD_TAC `&2 * (&2 / &7) * (&1 - p)` `(p * (&1 - q * (&1 - p)) + q * (q * (p + ip) - (&1 - p) * ip) - &1) - (&7 / &4) * (&1 - p)` THEN
  PCPLB_PROD_TAC `(&1 - p) pow 2` `&9 * (&1 - p) - ((&1 - q * (&1 - p)) pow 2 + (q * (p + ip) - (&1 - p) * ip) pow 2 - &1)` THEN
  PCPLB_PROD_TAC `(&1 - p) pow 2` `&1 - &9 * (&1 - p)` THEN
  SUBGOAL_THEN
   `((&2 / &7) - (&1 - p)) pow 2 - (((&2 / &7) * p - (&1 - p) * (&1 - q * (&1 - p))) pow 2 + ((&2 / &7) * q - (&1 - p) * (q * (p + ip) - (&1 - p) * ip)) pow 2) =
    &2 * (&2 / &7) * (&1 - p) * (p * (&1 - q * (&1 - p)) + q * (q * (p + ip) - (&1 - p) * ip) - &1) + (&1 - p) pow 2 * (&1 - (&1 - q * (&1 - p)) pow 2 - (q * (p + ip) - (&1 - p) * ip) pow 2)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `((&2 / &7) * p - (&1 - p) * (&1 - q * (&1 - p))) pow 2 + ((&2 / &7) * q - (&1 - p) * (q * (p + ip) - (&1 - p) * ip)) pow 2 <= ((&2 / &7) - (&1 - p)) pow 2`
  ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN
   `(l * ((&2 / &7) * p - (&1 - p) * (&1 - q * (&1 - p))) + r * ((&2 / &7) * q - (&1 - p) * (q * (p + ip) - (&1 - p) * ip))) pow 2 +
    (r * ((&2 / &7) * p - (&1 - p) * (&1 - q * (&1 - p))) - l * ((&2 / &7) * q - (&1 - p) * (q * (p + ip) - (&1 - p) * ip))) pow 2 =
    ((&2 / &7) * p - (&1 - p) * (&1 - q * (&1 - p))) pow 2 + ((&2 / &7) * q - (&1 - p) * (q * (p + ip) - (&1 - p) * ip)) pow 2` ASSUME_TAC THENL
  [UNDISCH_TAC `l pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ABBREV_TAC `XX = l * ((&2 / &7) * p - (&1 - p) * (&1 - q * (&1 - p))) + r * ((&2 / &7) * q - (&1 - p) * (q * (p + ip) - (&1 - p) * ip))` THEN
  ABBREV_TAC `YY = r * ((&2 / &7) * p - (&1 - p) * (&1 - q * (&1 - p))) - l * ((&2 / &7) * q - (&1 - p) * (q * (p + ip) - (&1 - p) * ip))` THEN
  ABBREV_TAC `NN = ((&2 / &7) * p - (&1 - p) * (&1 - q * (&1 - p))) pow 2 + ((&2 / &7) * q - (&1 - p) * (q * (p + ip) - (&1 - p) * ip)) pow 2` THEN
  SUBGOAL_THEN `XX <= (&2 / &7) - (&1 - p)` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   PCPLB_PRODLT_TAC `XX - ((&2 / &7) - (&1 - p))` `XX + ((&2 / &7) - (&1 - p))` THEN
   MP_TAC(SPEC `YY:real` REAL_LE_POW_2) THEN
   UNDISCH_TAC `XX pow 2 + YY pow 2 = NN` THEN
   UNDISCH_TAC `NN <= ((&2 / &7) - (&1 - p)) pow 2` THEN
   UNDISCH_TAC `&0 < (XX - ((&2 / &7) - (&1 - p))) * (XX + ((&2 / &7) - (&1 - p)))` THEN
   POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT DISCH_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCPLB_PROD_TAC `&1 - r - (&2 / &7)` `&1 - (p * l + q * r)` THEN
  SUBGOAL_THEN
   `p * ((&1 - l) + r * (l - &2 + (pceo_b p q + q * r) / p) + l * (pcplb_vertexdefect p q + q * (&1 - p)) + r * q * (&1 - p)) = (&1 - r) * (&1 - (p * l + q * r)) + (&1 - p) * (--(&1) + (&1 - q * (&1 - p)) * l + (q * (p + ip) - (&1 - p) * ip) * r)`
  ASSUME_TAC THENL
  [REWRITE_TAC[pceo_b; pcplb_vertexdefect; real_div] THEN ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `p * ip = &1` THEN UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC PCPLB_NONNEG_OF_MUL THEN EXISTS_TAC `p:real` THEN
  CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> try lhand(concl th) = `p * ((&1 - l) + r * (l - &2 + (pceo_b p q + q * r) / p) + l * (pcplb_vertexdefect p q + q * (&1 - p)) + r * q * (&1 - p))` with Failure _ -> false)) THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: own_axis_margin *)
let PCPLB_OWN_AXIS_MARGIN = prove
 (`forall p q C S l r. c977cc_normal p q /\ c977cc_normal C S /\ c977cc_normal l r /\
     q <= S /\ &9 / &10 <= p /\ &4 / &5 <= C /\ S <= &3 / &5
     ==> &0 <= (&1 - l) + r * (l - &2 + (pceo_b p q + q * r) / p) +
               l * (pcplb_vertexdefect C S + S * (&1 - p)) + r * S * (&1 - C)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCPLB_USE C977CSB_COSINE_ORDER [`C:real`; `S:real`; `p:real`; `q:real`] THEN
  PCPLB_USE PCPLB_REDUCED_MARGIN [`p:real`; `q:real`; `l:real`; `r:real`] THEN
  PCPLB_USE PCPLB_DEFECT_ORDER [`p:real`; `q:real`; `C:real`; `S:real`] THEN
  PCPLB_NORMAL_TAC THEN
  PCPLB_PROD_TAC `l:real` `pcplb_vertexdefect C S - pcplb_vertexdefect p q` THEN
  PCPLB_PROD_TAC `S - q` `&1 - p` THEN
  PCPLB_PROD_TAC `l:real` `(S - q) * (&1 - p)` THEN
  PCPLB_PROD_TAC `r:real` `(S - q) * (&1 - p)` THEN
  PCPLB_PROD_TAC `r:real` `S:real` THEN
  PCPLB_PROD_TAC `r * S` `p - C` THEN
  NLIN_TAC ~deg2:false []);;
