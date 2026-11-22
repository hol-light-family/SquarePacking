(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCrosspointBoundaryG01.lean            *)
(* (N12Compact.C1092MPPMCrosspointSupport).  The complete G01 inequality.   *)
(* Below the diagonal four polynomial pieces lie below the support          *)
(* expression; exact sine interpolation joins the zero, E-aligned,          *)
(* C-aligned and diagonal endpoints.  Above the diagonal: G01High.          *)
(* Normal is c977cc_normal; G00, G01, kC, deltaC, kE, deltaE, C0, E0, FE,   *)
(* Quarter are c1092mcs_*; the private Bool-indexed definitions sg,         *)
(* support, piece, qa, qb, ex, ey, ax, ay are c1092g01_* over HOL :bool.    *)
(* P, Q c1092mcbc_*; alignedBoundary c1092mcba_*; half / normal_half /      *)
(* half_order / steep_half / rho_bounds C1092MCBH_*; QuadraticArc           *)
(* c1092mpqa_value, C1092MPQA_NONNEGATIVE, C1092MPQR_CENTRAL_REMAINDER /    *)
(* MIDDLE_REMAINDER; steep_bounds C1092G10_STEEP_BOUNDS; Central.aligned_E  *)
(* C1092MCCE_ALIGNED_E; UnitCircleChord.cross_order CCUCC_CROSS_ORDER.      *)
(* Tag C1092G01_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryG01High.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryAligned.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryHalf.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointCentralEndpointE.ml";;

let C1092G01_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092G01_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [C1092G01_LP_TAC; REAL_ARITH_TAC]; ALL_TAC];;

let C1092G01_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

(* Lean: sg, support, piece, qa, qb, ex, ey, ax, ay (private definitions) *)
let c1092g01_sg = new_definition
 `c1092g01_sg (b:bool) = if b then &1 else -- &1`;;
let c1092g01_support = new_definition
 `c1092g01_support (e:bool) (d:real) (t:real) (h:real) (r:real) =
    if e then c1092mcs_kE d t h r * c1092mcs_E0 d t +
              c1092mcs_deltaE d t h r * (--d - (&2 / &5) * t)
    else c1092mcs_kE d t h r * c1092mcs_E0 d t - (d / &2) * c1092mcs_deltaE d t h r`;;
let c1092g01_piece = new_definition
 `c1092g01_piece (b:bool) (e:bool) (c:real) (s:real) (d:real) (t:real) (h:real) (r:real) =
    (c1092mcs_kC c s h r * (h + r) +
     h * (c1092mcs_kC c s h r + c1092g01_sg b * c1092mcs_deltaC c s h r) + s) / &2 -
    &2 * c1092mcs_kC c s h r - h * c1092mcs_C0 s - s * c1092g01_support e d t h r`;;
let c1092g01_qa = new_definition
 `c1092g01_qa (b:bool) (c:real) (s:real) = if b then c - s else c`;;
let c1092g01_qb = new_definition
 `c1092g01_qb (b:bool) (c:real) (s:real) = if b then c + s else s`;;
let c1092g01_ex = new_definition
 `c1092g01_ex (e:bool) (d:real) (t:real) =
    if e then c1092mcbc_P d t else &1 - t pow 2 - (&3 / &50) * d * t - d`;;
let c1092g01_ey = new_definition
 `c1092g01_ey (e:bool) (d:real) (t:real) =
    if e then --c1092mcbc_Q d t else d * t - (&3 / &50) * t pow 2 - t - &1 / &2`;;
let c1092g01_ax = new_definition
 `c1092g01_ax (e:bool) (c:real) (s:real) (d:real) (t:real) =
    &1 - &2 * c - (&543 / &500) * s - s * c1092g01_ex e d t`;;
let c1092g01_ay = new_definition
 `c1092g01_ay (e:bool) (s:real) (d:real) (t:real) = -- &2 * s - s * c1092g01_ey e d t`;;

(* Lean: support_form (private) *)
let C1092G01_SUPPORT_FORM = prove
 (`forall e d t h r. c977cc_normal d t
     ==> c1092g01_support e d t h r = c1092g01_ex e d t * h + c1092g01_ey e d t * r`,
  GEN_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
  BOOL_CASES_TAC `e:bool` THEN
  REWRITE_TAC[c1092g01_support; c1092g01_ex; c1092g01_ey; c1092mcs_kE; c1092mcs_deltaE;
              c1092mcs_E0; c1092mcbc_P; c1092mcbc_Q] THEN
  UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING);;

(* Lean: support_up (private) *)
let C1092G01_SUPPORT_UP = prove
 (`forall d t h r. &0 <= c1092mcs_deltaE d t h r
     ==> c1092g01_support true d t h r = c1092mcs_FE d t h r`,
  SIMP_TAC[c1092g01_support; c1092mcs_FE]);;

(* Lean: support_down (private) *)
let C1092G01_SUPPORT_DOWN = prove
 (`forall d t h r. c1092mcs_deltaE d t h r <= &0
     ==> c1092g01_support false d t h r = c1092mcs_FE d t h r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[c1092g01_support; c1092mcs_FE] THEN
  ASM_CASES_TAC `&0 <= c1092mcs_deltaE d t h r` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `c1092mcs_deltaE d t h r = &0` SUBST1_TAC THENL
  [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: support_above (private) *)
let C1092G01_SUPPORT_ABOVE = prove
 (`forall e d t h r. c977cc_normal d t ==> c1092mcs_FE d t h r <= c1092g01_support e d t h r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092G01_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= d / &2 + (&2 / &5) * t` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1092g01_support; c1092mcs_FE] THEN
  ASM_CASES_TAC `&0 <= c1092mcs_deltaE d t h r` THEN
  BOOL_CASES_TAC `e:bool` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THENL
  [C1092G01_PROD `&0 <= c1092mcs_deltaE d t h r * (d / &2 + (&2 / &5) * t)` THEN
   C1092G01_LP_TAC;
   C1092G01_PROD `&0 <= --c1092mcs_deltaE d t h r * (d / &2 + (&2 / &5) * t)` THEN
   C1092G01_LP_TAC]);;

let C1092G01_SG_ABS = prove
 (`forall b x. c1092g01_sg b * x <= abs x`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[c1092g01_sg] THEN REAL_ARITH_TAC);;

(* Lean: piece_below (private) *)
let C1092G01_PIECE_BELOW = prove
 (`forall b e c s d t h r. c977cc_normal c s /\ c977cc_normal d t /\ &0 <= h
     ==> c1092g01_piece b e c s d t h r <= c1092mcs_G01 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:bool`; `d:real`; `t:real`; `h:real`; `r:real`] C1092G01_SUPPORT_ABOVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`b:bool`; `c1092mcs_deltaC c s h r`] C1092G01_SG_ABS) THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN
  C1092G01_PROD `&0 <= h * (abs(c1092mcs_deltaC c s h r) -
                            c1092g01_sg b * c1092mcs_deltaC c s h r)` THEN
  C1092G01_PROD `&0 <= s * (c1092g01_support e d t h r - c1092mcs_FE d t h r)` THEN
  REWRITE_TAC[c1092g01_piece; c1092mcs_G01] THEN C1092G01_LP_TAC);;

(* Lean: piece_exact (private) *)
let C1092G01_PIECE_EXACT = prove
 (`forall b e c s d t h r.
     c1092g01_sg b * c1092mcs_deltaC c s h r = abs(c1092mcs_deltaC c s h r) /\
     c1092g01_support e d t h r = c1092mcs_FE d t h r
     ==> c1092g01_piece b e c s d t h r = c1092mcs_G01 c s d t h r`,
  SIMP_TAC[c1092g01_piece; c1092mcs_G01]);;

(* Lean: piece_form (private) *)
let C1092G01_PIECE_FORM = prove
 (`forall b e c s d t h r. c977cc_normal d t /\ c1092mcs_quarter h r
     ==> c1092g01_piece b e c s d t h r =
         c1092g01_qa b c s * h pow 2 + c1092g01_qb b c s * h * r + s +
         c1092g01_ax e c s d t * h + c1092g01_ay e s d t * r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mcs_quarter] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:bool`; `d:real`; `t:real`; `h:real`; `r:real`] C1092G01_SUPPORT_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[c1092g01_piece] THEN
  UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN
  BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[c1092g01_qa; c1092g01_qb; c1092g01_sg; c1092g01_ax; c1092g01_ay;
              c1092mcs_kC; c1092mcs_deltaC; c1092mcs_C0] THEN
  CONV_TAC REAL_RING);;

(* Lean: piece_half (private) *)
let C1092G01_PIECE_HALF = prove
 (`forall b e c s d t H R. c977cc_normal d t /\ c977cc_normal H R
     ==> c1092mpqa_value (c1092g01_qa b c s) (c1092g01_qb b c s) s
           (c1092g01_ax e c s d t) (c1092g01_ay e s d t) (c1092mcbh_half H R) =
         c1092g01_piece b e c s d t H R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`H:real`; `R:real`] C1092MCBH_NORMAL_HALF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:bool`; `e:bool`; `c:real`; `s:real`; `d:real`; `t:real`;
                `H:real`; `R:real`] C1092G01_PIECE_FORM) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[c1092mcs_quarter] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN ASM_REAL_ARITH_TAC;
   DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[c1092mpqa_value] THEN REAL_ARITH_TAC);;

let C1092G01_HALF_FACTS_TAC pts =
  MAP_EVERY (fun (x, y) ->
    MP_TAC(SPECL [x; y] C1092MCBH_NORMAL_HALF) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC) pts THEN
  STRIP_ASSUME_TAC C1092MCBH_RHO_BOUNDS;;

let C1092G01_HALF_ORDER_TAC (a, b) (c, d) =
  MP_TAC(SPECL [a; b; c; d] C1092MCBH_HALF_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC];;

(* Lean: low_arc (private) *)
let C1092G01_LOW_ARC = prove
 (`forall e c s d t h r H R C S.
     c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal h r /\
     c977cc_normal H R /\ c977cc_normal C S /\ R <= r /\ r <= S /\ S <= s /\
     &0 <= c1092g01_piece false e c s d t H R /\ &0 <= c1092g01_piece false e c s d t C S
     ==> &0 <= c1092mcs_G01 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092G01_HALF_FACTS_TAC [`c:real`,`s:real`; `H:real`,`R:real`; `h:real`,`r:real`;
                           `C:real`,`S:real`] THEN
  C1092G01_HALF_ORDER_TAC (`H:real`,`R:real`) (`c:real`,`s:real`) THEN
  C1092G01_HALF_ORDER_TAC (`h:real`,`r:real`) (`c:real`,`s:real`) THEN
  C1092G01_HALF_ORDER_TAC (`C:real`,`S:real`) (`c:real`,`s:real`) THEN
  C1092G01_HALF_ORDER_TAC (`H:real`,`R:real`) (`h:real`,`r:real`) THEN
  C1092G01_HALF_ORDER_TAC (`h:real`,`r:real`) (`C:real`,`S:real`) THEN
  MP_TAC(SPECL [`c1092mcbh_half c s`; `c1092mcbh_half H R`; `c1092mcbh_half h r`;
                `c1092mcbh_half C S`] C1092MPQR_CENTRAL_REMAINDER) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [C1092G01_LP_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c1092g01_qa false c s`; `c1092g01_qb false c s`; `s:real`;
                `c1092g01_ax e c s d t`; `c1092g01_ay e s d t`; `c1092mcbh_half H R`;
                `c1092mcbh_half h r`; `c1092mcbh_half C S`] C1092MPQA_NONNEGATIVE) THEN
  ASM_SIMP_TAC[C1092G01_PIECE_HALF] THEN REWRITE_TAC[c1092g01_qa; c1092g01_qb] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c1092g01_piece false e c s d t h r` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C1092G01_PIECE_BELOW THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN ASM_REAL_ARITH_TAC);;

(* Lean: middle_arc (private) *)
let C1092G01_MIDDLE_ARC = prove
 (`forall e c s d t h r H R C S.
     c977cc_normal c s /\ c977cc_normal d t /\ &3 / &5 <= s /\ c977cc_normal h r /\
     c977cc_normal H R /\ c977cc_normal C S /\ s <= R /\ R <= r /\ r <= S /\
     &0 <= c1092g01_piece true e c s d t H R /\ &0 <= c1092g01_piece true e c s d t C S
     ==> &0 <= c1092mcs_G01 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092G01_HALF_FACTS_TAC [`H:real`,`R:real`; `h:real`,`r:real`; `C:real`,`S:real`] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092G10_STEEP_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MCBH_STEEP_HALF) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  C1092G01_HALF_ORDER_TAC (`c:real`,`s:real`) (`H:real`,`R:real`) THEN
  C1092G01_HALF_ORDER_TAC (`H:real`,`R:real`) (`h:real`,`r:real`) THEN
  C1092G01_HALF_ORDER_TAC (`h:real`,`r:real`) (`C:real`,`S:real`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN
  MP_TAC(SPECL [`c - s`; `c + s`; `s:real`; `c1092mcbh_half H R`; `c1092mcbh_half h r`;
                `c1092mcbh_half C S`] C1092MPQR_MIDDLE_REMAINDER) THEN
  ANTS_TAC THENL [C1092G01_LP_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c1092g01_qa true c s`; `c1092g01_qb true c s`; `s:real`;
                `c1092g01_ax e c s d t`; `c1092g01_ay e s d t`; `c1092mcbh_half H R`;
                `c1092mcbh_half h r`; `c1092mcbh_half C S`] C1092MPQA_NONNEGATIVE) THEN
  SUBGOAL_THEN `c977cc_normal d t /\ c977cc_normal H R /\ c977cc_normal h r /\
                c977cc_normal C S` STRIP_ASSUME_TAC THENL
  [ASM_REWRITE_TAC[c977cc_normal]; ALL_TAC] THEN
  ASM_SIMP_TAC[C1092G01_PIECE_HALF] THEN REWRITE_TAC[c1092g01_qa; c1092g01_qb] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c1092g01_piece true e c s d t h r` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C1092G01_PIECE_BELOW THEN
  ASM_REWRITE_TAC[c977cc_normal] THEN ASM_REAL_ARITH_TAC);;

(* Lean: at_C (private) *)
let C1092G01_AT_C = prove
 (`forall b e c s d t. c977cc_normal c s /\
     c1092g01_support e d t c s = c1092mcs_FE d t c s
     ==> c1092g01_piece b e c s d t c s = c1092mcba_alignedBoundary c s d t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[c1092g01_piece; c1092mcba_alignedBoundary; c1092mcs_kC; c1092mcs_deltaC;
                  c1092mcs_C0] THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING);;

(* Lean: at_E (private) *)
let C1092G01_AT_E = prove
 (`forall b e c s d t. c977cc_normal d t /\
     c1092g01_sg b * c1092mcs_deltaC c s d t = abs(c1092mcs_deltaC c s d t)
     ==> c1092g01_piece b e c s d t d t = c1092mcs_G00 c s d t d t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c1092mcs_deltaE d t d t = &0 /\ c1092mcs_kE d t d t = &1` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[c1092mcs_deltaE; c1092mcs_kE] THEN
   UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `c1092g01_support e d t d t = c1092mcs_E0 d t` ASSUME_TAC THENL
  [BOOL_CASES_TAC `e:bool` THEN ASM_REWRITE_TAC[c1092g01_support] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[c1092g01_piece; c1092mcs_G00; REAL_ABS_0; c1092mcs_k; c1092mcs_kC] THEN
  REAL_ARITH_TAC);;

(* Lean: zero_endpoint (private) *)
let C1092G01_ZERO_ENDPOINT = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &3 / &5 <= s
     ==> &0 <= c1092g01_piece false false c s d t (&1) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092G10_STEEP_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092G01_NORMAL_TAC THEN
  C1092G01_PROD `&0 <= s * (&4 * s - &3 * c)` THEN
  SUBGOAL_THEN `c + s / &3 <= &1` ASSUME_TAC THENL
  [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
   NLIN_TAC [SQ_NONNEG `c + s / &3 - &1`]; ALL_TAC] THEN
  C1092G01_PROD `&0 <= d * (&1 - d)` THEN C1092G01_PROD `&0 <= d * t` THEN
  C1092G01_PROD `&0 <= s * (d * (&1 - d) + (&3 / &50) * d * t)` THEN
  SUBGOAL_THEN `c1092g01_piece false false c s d t (&1) (&0) =
                &1 - c - (&43 / &500) * s + s * (d * (&1 - d) + (&3 / &50) * d * t)`
    SUBST1_TAC THENL
  [REWRITE_TAC[c1092g01_piece; c1092g01_sg; c1092g01_support; c1092mcs_kC; c1092mcs_deltaC;
               c1092mcs_kE; c1092mcs_deltaE; c1092mcs_C0; c1092mcs_E0] THEN
   REAL_ARITH_TAC;
   C1092G01_LP_TAC]);;

(* the diagonal point sqrt 2 / 2 is normal *)
let C1092G01_DIAGONAL_NORMAL = prove
 (`c977cc_normal (sqrt(&2) / &2) (sqrt(&2) / &2)`,
  REWRITE_TAC[c977cc_normal; REAL_LE_REFL] THEN
  MP_TAC(SPEC `&2` SQRT_POW_2) THEN MP_TAC(SPEC `&2` SQRT_POS_LE) THEN
  REWRITE_TAC[REAL_POS] THEN REPEAT DISCH_TAC THEN CONJ_TAC THENL
  [ASM_REAL_ARITH_TAC;
   REWRITE_TAC[REAL_POW_DIV] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* Lean: G01_nonnegative *)
let C1092G01_G01_NONNEGATIVE = prove
 (`forall c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\
                 c1092mcs_quarter h r
                 ==> &0 <= c1092mcs_G01 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `h <= r` THENL
  [MATCH_MP_TAC C1092G01H_G01_HIGH_NONNEGATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcs_quarter] o
    check (fun th -> can (term_match [] `c1092mcs_quarter x y`) (concl th))) THEN
  SUBGOAL_THEN `c977cc_normal h r` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[c977cc_normal] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC C1092G01_DIAGONAL_NORMAL THEN
  ABBREV_TAC `v = sqrt(&2) / &2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `c1092mcs_quarter v v` ASSUME_TAC THENL
  [UNDISCH_TAC `c977cc_normal v v` THEN REWRITE_TAC[c977cc_normal; c1092mcs_quarter] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  C1092G01_NORMAL_TAC THEN
  SUBGOAL_THEN `r <= v` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092G01_PROD `&0 <= (h - r) * (h + r)` THEN
   C1092G01_PROD `&0 < (r - v) * (r + v)` THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092G01_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_normal (&1) (&0)` ASSUME_TAC THENL
  [REWRITE_TAC[c977cc_normal] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092G01_ZERO_ENDPOINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092G01_PROD `&0 <= (c - s) * v` THEN C1092G01_PROD `&0 <= (d - t) * v` THEN
  SUBGOAL_THEN `&0 <= c1092mcs_deltaC c s v v /\ &0 <= c1092mcs_deltaE d t v v`
    STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[c1092mcs_deltaC; c1092mcs_deltaE] THEN C1092G01_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c1092g01_piece true true c s d t v v` ASSUME_TAC THENL
  [SUBGOAL_THEN `c1092g01_piece true true c s d t v v = c1092mcs_G01 c s d t v v` SUBST1_TAC THENL
   [MATCH_MP_TAC C1092G01_PIECE_EXACT THEN ASM_SIMP_TAC[C1092G01_SUPPORT_UP] THEN
    REWRITE_TAC[c1092g01_sg] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC C1092G01H_G01_HIGH_NONNEGATIVE THEN
   ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092MCBA_ALIGNEDBOUNDARY_POSITIVE) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092MCCE_ALIGNED_E) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `t <= s` THENL
  [MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] CCUCC_CROSS_ORDER) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
   SUBGOAL_THEN `&0 <= c1092mcs_deltaE d t c s /\ c1092mcs_deltaC c s d t <= &0`
     STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092mcs_deltaE; c1092mcs_deltaC] THEN C1092G01_LP_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `c1092g01_sg false * c1092mcs_deltaC c s d t = abs(c1092mcs_deltaC c s d t)`
     ASSUME_TAC THENL
   [REWRITE_TAC[c1092g01_sg] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= c1092g01_piece false true c s d t c s /\ &0 <= c1092g01_piece true true c s d t c s /\
                 &0 <= c1092g01_piece false false c s d t d t /\ &0 <= c1092g01_piece false true c s d t d t`
     STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[C1092G01_AT_C; C1092G01_AT_E; C1092G01_SUPPORT_UP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   ASM_CASES_TAC `r <= t` THENL
   [MATCH_MP_TAC C1092G01_LOW_ARC THEN
    MAP_EVERY EXISTS_TAC [`false`; `&1`; `&0`; `d:real`; `t:real`] THEN ASM_REWRITE_TAC[];
    ASM_CASES_TAC `r <= s` THENL
    [MATCH_MP_TAC C1092G01_LOW_ARC THEN
     MAP_EVERY EXISTS_TAC [`true`; `d:real`; `t:real`; `c:real`; `s:real`] THEN
     ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC C1092G01_MIDDLE_ARC THEN
     MAP_EVERY EXISTS_TAC [`true`; `c:real`; `s:real`; `v:real`; `v:real`] THEN
     ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC]];
   SUBGOAL_THEN `s <= t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CCUCC_CROSS_ORDER) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
   SUBGOAL_THEN `c1092mcs_deltaE d t c s <= &0 /\ &0 <= c1092mcs_deltaC c s d t`
     STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092mcs_deltaE; c1092mcs_deltaC] THEN C1092G01_LP_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `c1092g01_sg true * c1092mcs_deltaC c s d t = abs(c1092mcs_deltaC c s d t)`
     ASSUME_TAC THENL
   [REWRITE_TAC[c1092g01_sg] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= c1092g01_piece false false c s d t c s /\ &0 <= c1092g01_piece true false c s d t c s /\
                 &0 <= c1092g01_piece true false c s d t d t /\ &0 <= c1092g01_piece true true c s d t d t`
     STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[C1092G01_AT_C; C1092G01_AT_E; C1092G01_SUPPORT_DOWN] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   ASM_CASES_TAC `r <= s` THENL
   [MATCH_MP_TAC C1092G01_LOW_ARC THEN
    MAP_EVERY EXISTS_TAC [`false`; `&1`; `&0`; `c:real`; `s:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ASM_CASES_TAC `r <= t` THENL
    [MATCH_MP_TAC C1092G01_MIDDLE_ARC THEN
     MAP_EVERY EXISTS_TAC [`false`; `c:real`; `s:real`; `d:real`; `t:real`] THEN
     ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
     MATCH_MP_TAC C1092G01_MIDDLE_ARC THEN
     MAP_EVERY EXISTS_TAC [`true`; `d:real`; `t:real`; `v:real`; `v:real`] THEN
     ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC]]]);;
