(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMAllNonpositiveCore.lean               *)
(* (N12Compact.C1092MPPMAllNonpositive), ALL-NEGATIVE-MIXED-FORWARD-ENDING   *)
(* section 2.  The square C is c s u v a, the bar square B is cB sB uB vB aB.*)
(* Normal is c977cc_normal; half / quarter_data are C1092WPS_*; vertex is    *)
(* OCWPVG_VERTEX; the clockwise turn of (c,s,u,v,a) is (c,s,--v-a,u,a) as   *)
(* in CP_C1092_MMMP_EndingAxes.                                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeForwardFaces.ml";;
needs "n12/geometry/CP_C1092_MMMP_EndingAxes.ml";;

let C1092ANC_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092ANC_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [MATCH_ACCEPT_TAC REAL_LE_POW_2; C1092ANC_LP_TAC]; ALL_TAC];;

(* from an excluded point ~linside c s u v a x y, the goal F *)
let C1092ANC_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN C1092ANC_LP_TAC;;

(* Lean: Core (structure) *)
let c1092anc_core = new_definition
 `c1092anc_core c s u v a <=>
    &1 < a /\ c977cc_normal c (--s) /\
    linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
    linside c s u v a (--(&1)) (--(&13 / &50)) /\
    linside c s u v a (--(&1)) (--(&2 / &5)) /\
    linside c s u v a (--(&13 / &50)) (&0) /\
    linside c s u v a (--(&1)) (--(&1 / &2)) /\
    ~linside c s u v a (--(&1)) (&0) /\
    ~linside c s u v a (--(&1)) (--(&1)) /\
    ~linside c s u v a (--(&7 / &20)) (&7 / &20)`;;

(* Lean: Faces (structure) *)
let c1092anc_faces = new_definition
 `c1092anc_faces c s u v a <=>
    --c <= u /\ s - c <= v /\ v + a <= (&7 / &20) * (c + s) /\ s < &0`;;

let C1092ANC_SETUP_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092anc_core] o
    check (fun th -> can (term_match [] `c1092anc_core c s u v a`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) || is_forall(concl th) then th
                           else REWRITE_RULE[linside] th);;

(* Lean: faces *)
let C1092ANC_FACES = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ c1092anc_core c s u v a
               ==> c1092anc_faces c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092ANC_SETUP_TAC THEN
  REWRITE_TAC[c1092anc_faces] THEN
  SUBGOAL_THEN `--c <= u` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092ANC_MISS_TAC `~linside c s u v a (--(&1)) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `s - c <= v` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092ANC_MISS_TAC `~linside c s u v a (--(&1)) (--(&1))`; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= (&7 / &20) * (c + s)` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092ANC_MISS_TAC `~linside c s u v a (--(&7 / &20)) (&7 / &20)`; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN C1092ANC_LP_TAC);;

(* Lean: narrow_angle *)
let C1092ANC_NARROW_ANGLE = prove
 (`forall c s. c977cc_normal c s /\ &1 < c + (&13 / &50) * s
         ==> &0 < s /\ &873 / &1000 < c /\ s < &61 / &125 /\ c < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&873 / &1000 < c` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `s < &61 / &125` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN NLIN_TAC []);;

(* Lean: above_bar *)
let C1092ANC_ABOVE_BAR = prove
 (`forall c s u v a cB sB uB vB aB X Y.
     c * c + s * s = &1 /\ &0 < a /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     lclosed c s u v a X Y /\ linside c s u v a (--(&13 / &50)) (&0) /\
     --(&14 / &25) <= X /\ X <= &0 /\
     (forall x. --(&14 / &25) <= x ==> x <= &0 ==> linside cB sB uB vB aB x (--(&1))) /\
     ldisj c s u v a cB sB uB vB aB
     ==> --(&1) < Y`,
  MATCH_ACCEPT_TAC C1092NFF_ABOVE_BAR);;

(* Lean: Cleared (structure, extends Faces) *)
let c1092anc_cleared = new_definition
 `c1092anc_cleared c s u v a <=>
    c1092anc_faces c s u v a /\
    u + a <= --(&13 / &50) * s /\ &873 / &1000 < c /\ --s < &61 / &125 /\ c < &1 /\
    --(&1) < s * (u + a) + c * v`;;

(* Lean: clearance *)
let C1092ANC_CLEARANCE = prove
 (`forall c s u v a cB sB uB vB aB.
     c * c + s * s = &1 /\ &0 < a /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092anc_core c s u v a /\ ~linside c s u v a (&0) (--(&13 / &50)) /\
     (forall x. --(&14 / &25) <= x ==> x <= &0 ==> linside cB sB uB vB aB x (--(&1))) /\
     ldisj c s u v a cB sB uB vB aB
     ==> c1092anc_cleared c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092ANC_FACES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[c1092anc_cleared] THEN
  MP_TAC(ASSUME `c1092anc_core c s u v a`) THEN REWRITE_TAC[c1092anc_core] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `linside c s u v a (--(&13 / &50)) (&0)` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092anc_faces] o
    check (fun th -> can (term_match [] `c1092anc_faces c s u v a`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) || is_forall(concl th) ||
                              concl th = `linside c s u v a (--(&13 / &50)) (&0)` then th
                           else REWRITE_RULE[linside] th) THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[linside] o
    check (fun th -> concl th = `linside c s u v a (--(&13 / &50)) (&0)`)) THEN
  SUBGOAL_THEN `u + a <= --(&13 / &50) * s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092ANC_MISS_TAC `~linside c s u v a (&0) (--(&13 / &50))`; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--s:real`] C1092ANC_NARROW_ANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092ANC_LP_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `--c + (&14 / &25) * s <= v` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   FIRST_ASSUM(MP_TAC o SPEC `--(&14 / &25)` o check (fun th -> is_forall(concl th) &&
     can (find_term ((=) `--(&14 / &25)`)) (concl th))) THEN
   MATCH_MP_TAC(TAUT `a /\ b /\ ~c ==> (a ==> b ==> c) ==> false`) THEN
   CONJ_TAC THENL [REAL_ARITH_TAC; CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]] THEN
   DISCH_TAC THEN UNDISCH_TAC `ldisj c s u v a cB sB uB vB aB` THEN REWRITE_TAC[ldisj] THEN
   DISCH_THEN(MP_TAC o SPECL [`--(&14 / &25)`; `--(&1)`]) THEN ASM_REWRITE_TAC[linside] THEN
   C1092ANC_LP_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `u + a:real`; `v:real`]
    OCWPVG_VERTEX) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  C1092ANC_PROD `&0 <= c * (u - --c)` THEN
  C1092ANC_PROD `&0 <= --s * (v - (--c + (&14 / &25) * s))` THEN
  C1092ANC_PROD `&0 < c * (a - &1)` THEN
  C1092ANC_PROD `&0 < (&1 + s) * (c - (&11 / &25) * (&1 - s))` THEN
  SUBGOAL_THEN `--(&14 / &25) < c * (u + a) - s * v` ASSUME_TAC THENL
  [C1092ANC_LP_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `c * (c * (u + a) - s * v) + s * (s * (u + a) + c * v) = u + a`
  ASSUME_TAC THENL
  [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092ANC_PROD `&0 <= --s * (--(&1) - (s * (u + a) + c * v))` THEN
  SUBGOAL_THEN `c * (c * (u + a) - s * v) <= &0` ASSUME_TAC THENL
  [C1092ANC_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * (u + a) - s * v <= &0` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092ANC_PROD `&0 < c * (c * (u + a) - s * v)` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `c * (u + a) - s * v`; `s * (u + a) + c * v`] C1092ANC_ABOVE_BAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; RASM_ARITH_TAC]);;

(* Lean: SuccessorFaces (structure), for E = clockwise D *)
let c1092anc_successorFaces = new_definition
 `c1092anc_successorFaces c s u v a <=>
    --c <= v /\ u + a <= c - s /\ u < --(&13 / &50) * s /\ --(&7 / &20) * (c + s) <= u`;;

(* Lean: successor_faces *)
let C1092ANC_SUCCESSOR_FACES = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ c1092anc_core c s u v a
               ==> c1092anc_successorFaces c s (--v - a) u a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092ANC_FACES) THEN
  ASM_REWRITE_TAC[c1092anc_faces] THEN STRIP_TAC THEN C1092ANC_SETUP_TAC THEN
  REWRITE_TAC[c1092anc_successorFaces] THEN C1092ANC_LP_TAC);;
