(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardNonnegativeFaces.lean          *)
(* (namespace N12Compact.C1092MPPMInwardFinal.NonnegativeRecipient).         *)
(* Ordinary recipient face comparisons for one actual square E =            *)
(* (c, s, u, v, a).  Data is the predicate c1092minf_data; Normal is        *)
(* c977cc_normal; half / quarter_data: C1092WPS_half / C1092WPS_QUARTER_DATA.*)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalSignScalars.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;

(* Lean: Data (structure) *)
let c1092minf_data = new_definition
 `c1092minf_data c s u v a <=>
    &1 < a /\
    linside c s u v a (&7 / &20) (--(&7 / &20)) /\
    linside c s u v a (&13 / &50) (--(&1)) /\
    linside c s u v a (&2 / &5) (--(&1)) /\
    ~linside c s u v a (&0) (--(&13 / &50)) /\
    ~linside c s u v a (&1) (--(&2 / &5)) /\
    ~linside c s u v a (&0) (--(&543 / &500)) /\
    ~linside c s u v a (&1) (--(&1)) /\
    ~linside c s u v a (&1) (--(&543 / &500))`;;

let C1092MINF_LIN_TAC =
  REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NLIN_TAC ~deg2:false []);;

(* a missing point: the goal is refuted by showing the point is inside *)
let C1092MINF_MISSING_TAC (x,y) =
  FIRST_X_ASSUM(fun th ->
    if concl th = mk_neg(list_mk_comb(`linside c s u v a`,[x; y])) then
      MP_TAC th else NO_TAC) THEN
  REWRITE_TAC[linside] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[] THEN C1092MINF_LIN_TAC;;

(* Lean: faces *)
let C1092MINF_FACES = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ c1092minf_data c s u v a /\ c977cc_normal c s
     ==> u + a <= c - (&2 / &5) * s /\ v + a <= --(&13 / &50) * c /\ --c - s <= v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092minf_data] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> try fst(strip_comb(concl th)) = `linside` with _ -> false) ths)) THEN
  SUBGOAL_THEN `u + a <= c - (&2 / &5) * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MINF_MISSING_TAC (`&1`, `--(&2 / &5)`);
    ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= --(&13 / &50) * c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MINF_MISSING_TAC (`&0`, `--(&13 / &50)`);
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `u + a <= c - s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MINF_MISSING_TAC (`&1`, `--(&1)`);
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&543 / &500) * s <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MINF_MISSING_TAC (`&0`, `--(&543 / &500)`);
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < c + (&43 / &500) * s` ASSUME_TAC THENL
   [C1092MINF_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [C1092MINF_LIN_TAC; ALL_TAC] THEN
  SPEC_TAC(`C1092WPS_half c s`, `z:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `(&1 + z * z) * (c + (&43 / &500) * s - &1) = &2 * z * (&43 / &500 - z)`
    ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(&1 + z * z) * c = &1 - z * z`; `(&1 + z * z) * s = &2 * z`] THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 + z * z) * (c + (&43 / &500) * s - &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [NLIN_TAC []; C1092MINF_LIN_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `z < &43 / &500` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`&2 * z`; `z - &43 / &500`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [C1092MINF_LIN_TAC; DISCH_TAC] THEN C1092MINF_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s < &43 / &250` ASSUME_TAC THENL
   [MP_TAC(SPECL [`s:real`; `z * z`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [REWRITE_TAC[REAL_LE_SQUARE] THEN C1092MINF_LIN_TAC; DISCH_TAC] THEN
    C1092MINF_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c - (&543 / &500) * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MINF_MISSING_TAC (`&1`, `--(&543 / &500)`);
    ALL_TAC] THEN
  C1092MINF_LIN_TAC);;
