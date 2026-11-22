(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C972NorthwestForward.lean          *)
(* (namespace N12Compact.FiniteCases.C972).  The actual northwest square     *)
(* must own F5.  owners p i = owner of mask EL i c972o_masks, written with   *)
(* the literal mask (owners 0..11 = masks 1,2,12,48,192,256,512,1024,2048,   *)
(* 4096,8192,16384).  A Lean OpenSquare q is c s u v a with its unit normal  *)
(* and positive side explicit.  q.translated 2 2 = (c, s, u - (c 2 + s 2),   *)
(* v - (--s 2 + c 2), a) (C972NF_TRANSLATED); short_projections =            *)
(* WFP_SHORT_PROJECTIONS; ClosedFrames.canonical_frame = CLF_CANONICAL_FRAME;*)
(* NorthwestSharpPoint.upper_point_original = CCNWS_UPPER_POINT_ORIGINAL;    *)
(* C981CompletionUpperPoint.point = C981UP_POINT; inside_segment (vertical)  *)
(* = OO_VERTICAL_SEGMENT.  Tag C972NF_.                                      *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C972UpperReduction.ml";;
needs "n12/geometry/CP_C981_UpperPoint.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let c972nf_own = c972mc_own and c972nf_stmt = c972mc_stmt and c972nf_tuple = c972mc_tuple;;

(* Lean: upper_anchor_canonical (private) *)
let C972NF_UPPER_ANCHOR_CANONICAL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ abs s <= c /\
     linside c s u v a (&7 / &20) (&7 / &20) /\ linside c s u v a (&0) (&1) /\
     linside c s u v a (&2 / &5) (&1) /\ ~linside c s u v a (&1) (&1)
     ==> linside c s u v a (&1 / &10) (&3 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`c:real`; `s:real`; `&9 / &10`; `&2 / &5`] WFP_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC] THEN
  REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let C972NF_TRANSLATED = prove
 (`forall c s u v a tx ty x y.
     linside c s (u - (c * tx + s * ty)) (v - (--s * tx + c * ty)) a x y <=>
     linside c s u v a (tx + x) (ty + y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: northeast_upper_anchor *)
let C972NF_NORTHEAST_UPPER_ANCHOR = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&47 / &20) (&47 / &20) /\ linside c s u v a (&2) (&3) /\
     linside c s u v a (&12 / &5) (&3) /\ ~linside c s u v a (&3) (&3)
     ==> linside c s u v a (&21 / &10) (&13 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`; `a:real`]
            CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN STRIP_TAC THEN
  MP_TAC (SPECL [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] C972NF_UPPER_ANCHOR_CANONICAL) THEN
  ASM_REWRITE_TAC[C972NF_TRANSLATED] THEN CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN RASM_ARITH_TAC);;

(* Lean: northwest_forward *)
let C972NF_NORTHWEST_FORWARD = prove
 (c972nf_stmt [] (c972nf_own 2048 `&2` `&113 / &50`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C972CS_FIXED_TAC THEN
  MP_TAC(SPEC_ALL C972CS_NORTHWEST_PAIR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C972CS_NORTHEAST_F7) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972MC_REMAINING_ALTERNATIVE) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC (c972nf_own 2048 `&2` `&113 / &50`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C972CS_OWNER_TAC 2048 THEN C972CS_OWNER_TAC 1024 THEN
  SUBGOAL_THEN (c972nf_own 2048 `&21 / &10` `&13 / &5`) ASSUME_TAC THENL
   [MATCH_MP_TAC (SPECL (c972nf_tuple 2048) CCNWS_UPPER_POINT_ORIGINAL) THEN
    REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           DISCH_TAC THEN C972CS_CLASH_TAC;
           X_GEN_TAC `z:real` THEN REPEAT DISCH_TAC THEN
           MP_TAC(SPECL (C972MC_V5 @ [`z:real`]) C972MC_LEFT_BAR) THEN ASM_REWRITE_TAC[] THEN
           DISCH_TAC THEN C972CS_CLASH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN (c972nf_own 1024 `&21 / &10` `&13 / &5`) ASSUME_TAC THENL
   [MATCH_MP_TAC (SPECL (c972nf_tuple 1024) C972NF_NORTHEAST_UPPER_ANCHOR) THEN
    REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC THEN C972CS_CLASH_TAC; RASM_ARITH_TAC];
    ALL_TAC] THEN
  C972CS_CLASH_TAC);;

(* Lean: northwest_missing_origin *)
let C972NF_NORTHWEST_MISSING_ORIGIN = prove
 (c972nf_stmt [] (mk_neg (c972nf_own 2048 `&2` `&3`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C972CS_FIXED_TAC THEN
  MP_TAC(SPEC_ALL C972CS_NORTHEAST_G7) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972CS_RIGHT_REACH) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972NF_NORTHWEST_FORWARD) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C972CS_OWNER_TAC 1024 THEN
  SUBGOAL_THEN (mk_conj(c972nf_own 2048 `&2` `&12 / &5`, c972nf_own 2048 `&2` `&131 / &50`))
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN
    MAP_EVERY EXISTS_TAC [`&113 / &50`; `&3`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN (c972nf_own 1024 `&2` `&131 / &50`) ASSUME_TAC THENL
   [MATCH_MP_TAC (SPECL (c972nf_tuple 1024) C981UP_POINT) THEN
    REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC THEN C972CS_CLASH_TAC; RASM_ARITH_TAC];
    ALL_TAC] THEN
  C972CS_CLASH_TAC);;
