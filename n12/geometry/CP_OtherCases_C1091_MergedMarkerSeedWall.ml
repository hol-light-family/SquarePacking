(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1091/MergedMarkerSeedWall.lean     *)
(* (namespace N12Compact.Completion.OtherCases.C1091.MergedMarkerSeed).     *)
(* point_original: C1091MMS_POINT_ORIGINAL; C981CompletionWallAdvance.point:*)
(* C981WA_POINT; inside_segment: CES_INSIDE_SEGMENT.  Squares A K N L are   *)
(* the tuples cA sA uA vA aA etc.; their OpenSquare invariants are lsquare. *)
(* The family q : Fin 12 -> OpenSquare enters only through q 4, q 0, q 7,   *)
(* q 8, so original_owner_bar is the instance A = Q4, K = Q0, N = Q7, L = Q8 *)
(* written with those coordinates (c4 s4 u4 v4 a4 etc.).                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1091_MergedMarkerSeed.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;

(* Lean: WallInput (structure) *)
let c1091mmsw_wall_input = new_definition
 `c1091mmsw_wall_input cA sA uA vA aA cK sK uK vK aK cN sN uN vN aN cL sL uL vL aL <=>
    &1 < aA /\ &1 < aL /\ lcont cL sL uL vL aL /\
    linside cA sA uA vA aA (&457 / &500) (&1) /\
    linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
    linside cA sA uA vA aA (&1) (&87 / &50) /\
    linside cK sK uK vK aK (&1) (&1) /\
    linside cN sN uN vN aN (&87 / &50) (&2) /\
    linside cN sN uN vN aN (&33 / &20) (&47 / &20) /\
    linside cL sL uL vL aL (&457 / &500) (&2) /\
    linside cL sL uL vL aL (&1) (&113 / &50) /\
    linside cL sL uL vL aL (&1) (&12 / &5) /\
    ldisj cA sA uA vA aA cK sK uK vK aK /\
    ldisj cA sA uA vA aA cN sN uN vN aN /\
    ldisj cL sL uL vL aL cA sA uA vA aA /\
    ldisj cL sL uL vL aL cN sN uN vN aN`;;

(* Lean: seed_of_owners *)
let C1091MMSW_SEED_OF_OWNERS = prove
 (`forall cA sA uA vA aA cK sK uK vK aK cN sN uN vN aN cL sL uL vL aL.
     lsquare cA sA uA vA aA /\ lsquare cK sK uK vK aK /\
     lsquare cN sN uN vN aN /\ lsquare cL sL uL vL aL /\
     c1091mmsw_wall_input cA sA uA vA aA cK sK uK vK aK cN sN uN vN aN cL sL uL vL aL
     ==> linside cA sA uA vA aA (&19 / &25) (&187 / &100)`,
  REWRITE_TAC[lsquare; c1091mmsw_wall_input; ldisj] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC C1091MMS_POINT_ORIGINAL THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* Lean: wall_advance *)
let C1091MMSW_WALL_ADVANCE = prove
 (`forall cA sA uA vA aA cK sK uK vK aK cN sN uN vN aN cL sL uL vL aL.
     lsquare cA sA uA vA aA /\ lsquare cK sK uK vK aK /\
     lsquare cN sN uN vN aN /\ lsquare cL sL uL vL aL /\
     c1091mmsw_wall_input cA sA uA vA aA cK sK uK vK aK cN sN uN vN aN cL sL uL vL aL
     ==> linside cL sL uL vL aL (&1) (&14 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C1091MMSW_SEED_OF_OWNERS o
    CONJ (ASSUME `lsquare cA sA uA vA aA`) o CONJ (ASSUME `lsquare cK sK uK vK aK`) o
    CONJ (ASSUME `lsquare cN sN uN vN aN`) o CONJ (ASSUME `lsquare cL sL uL vL aL`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lsquare; c1091mmsw_wall_input; ldisj]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  MATCH_MP_TAC C981WA_POINT THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Lean: wall_bar *)
let C1091MMSW_WALL_BAR = prove
 (`forall cA sA uA vA aA cK sK uK vK aK cN sN uN vN aN cL sL uL vL aL y.
     lsquare cA sA uA vA aA /\ lsquare cK sK uK vK aK /\
     lsquare cN sN uN vN aN /\ lsquare cL sL uL vL aL /\
     c1091mmsw_wall_input cA sA uA vA aA cK sK uK vK aK cN sN uN vN aN cL sL uL vL aL /\
     &113 / &50 <= y /\ y <= &14 / &5
     ==> linside cL sL uL vL aL (&1) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1091MMSW_WALL_ADVANCE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `&1`; `&113 / &50`; `&1`; `&14 / &5`; `(&50 / &27) * (y - &113 / &50)`]
    CES_INSIDE_SEGMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `c1091mmsw_wall_input cA sA uA vA aA cK sK uK vK aK cN sN uN vN aN cL sL uL vL aL` THEN
    SIMP_TAC[c1091mmsw_wall_input] THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN REAL_ARITH_TAC]);;

(* Lean: original_owner_bar *)
let C1091MMSW_ORIGINAL_OWNER_BAR = prove
 (`forall c4 s4 u4 v4 a4 c0 s0 u0 v0 a0 c7 s7 u7 v7 a7 c8 s8 u8 v8 a8.
     lsquare c4 s4 u4 v4 a4 /\ lsquare c0 s0 u0 v0 a0 /\
     lsquare c7 s7 u7 v7 a7 /\ lsquare c8 s8 u8 v8 a8 /\
     c1091mmsw_wall_input c4 s4 u4 v4 a4 c0 s0 u0 v0 a0 c7 s7 u7 v7 a7 c8 s8 u8 v8 a8
     ==> linside c4 s4 u4 v4 a4 (&19 / &25) (&187 / &100) /\
         forall y. &113 / &50 <= y ==> y <= &14 / &5 ==> linside c8 s8 u8 v8 a8 (&1) y`,
  let vs = [`c4:real`; `s4:real`; `u4:real`; `v4:real`; `a4:real`;
            `c0:real`; `s0:real`; `u0:real`; `v0:real`; `a0:real`;
            `c7:real`; `s7:real`; `u7:real`; `v7:real`; `a7:real`;
            `c8:real`; `s8:real`; `u8:real`; `v8:real`; `a8:real`] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(SPECL vs C1091MMSW_SEED_OF_OWNERS) THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MP_TAC(SPECL (vs @ [`y:real`]) C1091MMSW_WALL_BAR) THEN
    ASM_REWRITE_TAC[]]);;
