(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCenteredPositiveData.lean             *)
(* (N12Compact.C1092MPPMCenteredPositive).  The point-only southeast         *)
(* calculation of the centered positive chapters.  C = cC sC uC vC aC,       *)
(* E = cE sE uE vE aE.  Normal is c977cc_normal; norm_lt C1092NPP_NORM_LT;   *)
(* RigidCharts.swap (c,s,u,v,a) -> (c,--s,v,u,a), inside_swap               *)
(* C1092RC_INSIDE_SWAP; NortheastNegativeFaces C1092MNNF_*; MMMMNegative-    *)
(* Neighbor.impossible_faces C1092MNN_IMPOSSIBLE_FACES.  S12.Convex          *)
(* (inside_segment) is used only on a vertical segment and is replaced by    *)
(* the equivalent linear arithmetic.                                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveOverlapScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMNonpositivePredecessor.ml";;
needs "n12/geometry/CP_C1092_MMMP_NortheastNegativeFaces.ml";;
needs "n12/geometry/CP_C1092_MMMMNegativeNeighbor.ml";;
needs "n12/geometry/CP_C1092_RigidCharts.ml";;

let C1092MCPD_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092MCPD_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

(* the goal F from an excluded point ~linside q x y (unfolding) *)
let C1092MCPD_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN C1092MCPD_LP_TAC;;

(* Lean: Input (structure) *)
let c1092mcpd_input = new_definition
 `c1092mcpd_input cC sC uC vC aC cE sE uE vE aE <=>
    linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
    ~linside cC sC uC vC aC (--(&7 / &20)) (&7 / &20) /\
    linside cC sC uC vC aC (&0) (&0) /\
    linside cC sC uC vC aC (--(&1 / &2)) (&0) /\
    linside cC sC uC vC aC (&0) (--(&13 / &50)) /\
    linside cC sC uC vC aC (--(&1 / &100)) (--(&27 / &50)) /\
    linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
    linside cE sE uE vE aE (&13 / &50) (--(&1)) /\
    linside cE sE uE vE aE (&2 / &5) (--(&1)) /\
    linside cE sE uE vE aE (&1 / &2) (--(&1)) /\
    ~linside cE sE uE vE aE (&1) (--(&39 / &100)) /\
    ~linside cE sE uE vE aE (&0) (--(&543 / &500)) /\
    ~linside cE sE uE vE aE (&1) (--(&1)) /\
    ~linside cE sE uE vE aE (&1) (&0) /\
    ~linside cE sE uE vE aE (&1) (--(&2 / &5)) /\
    ldisj cC sC uC vC aC cE sE uE vE aE`;;

let C1092MCPD_SETUP_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcpd_input] o
    check (fun th -> can (term_match [] `c1092mcpd_input a b c d e f g h i j`) (concl th))) THEN
  C1092MCPD_NORMAL_TAC;;

let C1092MCPD_APART_TAC x y =
  UNDISCH_TAC `ldisj cC sC uC vC aC cE sE uE vE aE` THEN REWRITE_TAC[ldisj] THEN
  DISCH_THEN(MP_TAC o SPECL [x; y]) THEN ASM_REWRITE_TAC[linside] THEN C1092MCPD_LP_TAC;;

(* Lean: center_caps *)
let C1092MCPD_CENTER_CAPS = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aC /\ c977cc_normal cC sC /\ c1092mcpd_input cC sC uC vC aC cE sE uE vE aE
     ==> uC + aC <= (&7 / &20) * (cC - sC) /\ vC + aC <= (&7 / &20) * (cC + sC)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MCPD_SETUP_TAC THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th) THEN
  SUBGOAL_THEN `vC + aC <= (&7 / &20) * (cC + sC)` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092MCPD_MISS_TAC `~linside cC sC uC vC aC (--(&7 / &20)) (&7 / &20)`; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `vC < --(&7 / &20) * (cC + sC)` ASSUME_TAC THENL
  [C1092MCPD_LP_TAC; ALL_TAC] THEN
  C1092MCPD_APART_TAC `&7 / &20` `--(&7 / &20)`);;

(* Lean: lower_crosspoint *)
let C1092MCPD_LOWER_CROSSPOINT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c977cc_normal c s /\
               linside c s u v a (&0) (&0) /\ linside c s u v a (--(&1 / &2)) (&0) /\
               v + a <= (&7 / &20) * (c + s)
               ==> linside c s u v a (&0) (--(&1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MCPD_NORMAL_TAC THEN
  MP_TAC(SPECL [`&17 / &20`; `&7 / &20`; `c:real`; `s:real`; `&1`] C1092NPP_NORM_LT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th) THEN
  REWRITE_TAC[linside] THEN C1092MCPD_LP_TAC);;

(* Lean: successor_negative *)
let C1092MCPD_SUCCESSOR_NEGATIVE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aC /\ aC = aE /\ c977cc_normal cC sC /\ abs sE <= cE /\
     c1092mcpd_input cC sC uC vC aC cE sE uE vE aE
     ==> sE < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] C1092MCPD_CENTER_CAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  C1092MCPD_SETUP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092MCPD_LOWER_CROSSPOINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `linside cC sC uC vC aC (&0) (--(&39 / &100))` ASSUME_TAC THENL
  [UNDISCH_TAC `linside cC sC uC vC aC (&0) (&0)` THEN
   UNDISCH_TAC `linside cC sC uC vC aC (&0) (--(&1 / &2))` THEN
   REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN C1092MCPD_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sE <= cE` ASSUME_TAC THENL
  [UNDISCH_TAC `abs sE <= cE` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[C1092RC_INSIDE_SWAP; REAL_NEG_NEG]
    (SPECL [`cE:real`; `--sE:real`; `vE:real`; `uE:real`; `aC:real`] C1092MNNF_FACES)) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[c977cc_normal] THEN REPEAT CONJ_TAC THEN
   TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY RASM_ARITH_TAC THEN
   TRY(UNDISCH_TAC `cE * cE + sE * sE = &1` THEN REAL_ARITH_TAC) THEN
   DISCH_TAC THEN UNDISCH_TAC `ldisj cC sC uC vC aC cE sE uE vE aC` THEN
   REWRITE_TAC[ldisj] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[c1092mnnf_faces; REAL_NEG_NEG] THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[C1092RC_INSIDE_SWAP; REAL_NEG_NEG]
   (SPECL [`cC:real`; `--sC:real`; `vC:real`; `uC:real`; `aC:real`;
           `cE:real`; `--sE:real`; `vE:real`; `uE:real`; `aC:real`]
    C1092MNN_IMPOSSIBLE_FACES)) THEN
  MATCH_MP_TAC(TAUT `a ==> ~a ==> false`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(UNDISCH_TAC `cC * cC + sC * sC = &1` THEN REAL_ARITH_TAC) THEN
  TRY(UNDISCH_TAC `cE * cE + sE * sE = &1` THEN REAL_ARITH_TAC) THEN
  TRY RASM_ARITH_TAC THEN
  TRY(ASM_REWRITE_TAC[c977cc_normal] THEN RASM_ARITH_TAC) THEN
  UNDISCH_TAC `ldisj cC sC uC vC aC cE sE uE vE aC` THEN
  REWRITE_TAC[ldisj; C1092RC_INSIDE_SWAP] THEN MESON_TAC[]);;

(* Lean: SuccessorFaces (structure) *)
let c1092mcpd_successorFaces = new_definition
 `c1092mcpd_successorFaces (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    --(&13 / &50) * s <= u /\ u + a <= c - s /\
    --(&543 / &500) * c <= v /\ v + a <= --s`;;

(* Lean: successor_faces *)
let C1092MCPD_SUCCESSOR_FACES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aE /\ c977cc_normal cE (--sE) /\
     c1092mcpd_input cC sC uC vC aC cE sE uE vE aE
     ==> c1092mcpd_successorFaces cE sE uE vE aE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MCPD_SETUP_TAC THEN
  SUBGOAL_THEN `~linside cE sE uE vE aE (&0) (--(&13 / &50))` ASSUME_TAC THENL
  [DISCH_TAC THEN UNDISCH_TAC `ldisj cC sC uC vC aC cE sE uE vE aE` THEN
   REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&0`; `--(&13 / &50)`]) THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th) THEN
  REWRITE_TAC[c1092mcpd_successorFaces] THEN
  let miss x y = C1092MCPD_MISS_TAC (mk_neg(list_mk_comb(`linside cE sE uE vE aE`,[x;y]))) in
  let fact t x y = SUBGOAL_THEN t ASSUME_TAC THENL
    [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN miss x y; ALL_TAC] in
  SUBGOAL_THEN `--(&13 / &50) * sE <= uE` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   fact `vE + aE <= --(&13 / &50) * cE` `&0` `--(&13 / &50)` THEN
   fact `uE + aE <= cE - sE` `&1` `--(&1)` THEN
   fact `--(&543 / &500) * sE <= uE` `&0` `--(&543 / &500)` THEN
   C1092MCPD_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `vE + aE <= --sE` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   fact `uE + aE <= cE` `&1` `&0` THEN C1092MCPD_LP_TAC; ALL_TAC] THEN
  fact `uE + aE <= cE - sE` `&1` `--(&1)` THEN
  SUBGOAL_THEN `--(&543 / &500) * cE <= vE` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   fact `--(&543 / &500) * sE <= uE` `&0` `--(&543 / &500)` THEN
   C1092MCPD_LP_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;
