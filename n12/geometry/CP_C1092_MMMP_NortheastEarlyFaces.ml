(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/NortheastEarlyFaces.lean            *)
(* (N12Compact.C1092MMMPNortheastEarlyFaces).  The positive northeast faces  *)
(* before any top-origin deduction.  Normal: c977cc_normal;                  *)
(* short_projections: WFP_SP; MMMMFirstPair.positive_support:                *)
(* C1092MFP_POSITIVE_SUPPORT; MMMMPairScalars.small_of_support:              *)
(* C1092MPS_SMALL_OF_SUPPORT.                                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMMFirstPair.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let C1092NEF_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092NEF_EXPAND_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> not(is_neg(concl th)) &&
     can (find_term ((=) `linside`)) (concl th)))) THEN
  REWRITE_TAC[linside] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC);;

let C1092NEF_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C1092NEF_LIN_TAC;;

(* Lean: Data (structure) *)
let c1092nef_data = new_definition
 `c1092nef_data (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    --(&543 / &500) * c <= u /\ u + a <= s - (&2 / &5) * c /\
    (&2 / &5) * s <= v /\ v + a <= c + s`;;

(* Lean: faces *)
let C1092NEF_FACES = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c977cc_normal c s /\ &0 < s /\
     linside c s u v a (--(&7 / &20)) (&7 / &20) /\
     linside c s u v a (--(&1)) (&2 / &5) /\
     ~linside c s u v a (--(&2 / &5)) (&0) /\
     ~linside c s u v a (--(&2 / &5)) (&1) /\
     ~linside c s u v a (--(&543 / &500)) (&0) /\
     ~linside c s u v a (--(&1)) (&1)
     ==> c1092nef_data c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  C1092NEF_EXPAND_TAC THEN REWRITE_TAC[c1092nef_data] THEN
  SUBGOAL_THEN `(&2 / &5) * s <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092NEF_MISS_TAC `~linside c s u v a (--(&2 / &5)) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= s - (&2 / &5) * c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(&2 / &5) * s + c < v + a` ASSUME_TAC THENL
     [C1092NEF_LIN_TAC; ALL_TAC] THEN
    C1092NEF_MISS_TAC `~linside c s u v a (--(&2 / &5)) (&1)`; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= c + s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092NEF_MISS_TAC `~linside c s u v a (--(&1)) (&1)`; ALL_TAC] THEN
  SUBGOAL_THEN `--(&543 / &500) * c <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `v < (&543 / &500) * s /\ (&543 / &500) * s < v + a`
      STRIP_ASSUME_TAC THENL [CONJ_TAC THEN C1092NEF_LIN_TAC; ALL_TAC] THEN
    C1092NEF_MISS_TAC `~linside c s u v a (--(&543 / &500)) (&0)`; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: upper_point *)
let C1092NEF_UPPER_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c1092nef_data c s u v a
     ==> linside c s u v a (--(&1 / &2)) (&7 / &50)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092nef_data] THEN STRIP_TAC THEN
  MP_TAC(WFP_SP `&1 / &10` `&43 / &50`) THEN
  MP_TAC(WFP_SP `&293 / &500` `&7 / &50`) THEN
  MP_TAC(WFP_SP `&43 / &50` `&1 / &2`) THEN
  MP_TAC(WFP_SP `&7 / &50` `&1 / &10`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C1092NEF_LIN_TAC);;

(* Lean: small_central *)
let C1092NEF_SMALL_CENTRAL = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aC /\ aC = aB /\
     c977cc_normal cC (--sC) /\ c977cc_normal cB sB /\ &0 < sB /\
     linside cC sC uC vC aC (&0) (&0) /\
     linside cC sC uC vC aC (&0) (--(&1 / &2)) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     ~linside cC sC uC vC aC (&7 / &20) (--(&7 / &20)) /\
     linside cB sB uB vB aB (--(&7 / &20)) (&7 / &20) /\
     linside cB sB uB vB aB (--(&1)) (&2 / &5) /\
     c1092nef_data cB sB uB vB aB /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> --sC < &7 / &50 /\ &99 / &100 < cC`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092nef_data] o
    check (fun th -> can (term_match [] `c1092nef_data c s u v a`) (concl th))) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`]
    C1092MFP_POSITIVE_SUPPORT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092NEF_LIN_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `uC + aC <= (&7 / &20) * (cC + --sC) /\ &0 < uC + aC /\ &0 < vC + aC`
    STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < uC + aC /\ &0 < vC + aC` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `linside cC sC uC vC aC (&0) (&0)` THEN REWRITE_TAC[linside] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside cC sC uC vC aC (&7 / &20) (--(&7 / &20))` THEN
    UNDISCH_TAC `linside cC sC uC vC aC (&0) (&0)` THEN
    UNDISCH_TAC `linside cC sC uC vC aC (&0) (--(&1 / &2))` THEN
    REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN C1092NEF_LIN_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`; `cB:real`; `sB:real`; `aC:real`; `uC + aC`; `vC + aC`]
    C1092MPS_SMALL_OF_SUPPORT) THEN
  ASM_REWRITE_TAC[]);;
