(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1091/ResidualProduction.lean       *)
(* (namespace N12Compact.Completion.OtherCases.C1091.OriginalData).          *)
(* Authentic C1091 residual producer: from the six literal entrance points   *)
(* (ResidualEntrance) all fields of Residual.Input (c1091ri_input) are       *)
(* produced for the packing's owners, and the residual is impossible.        *)
(* owners p is the 5-tuple of functions c1091rp_owners:                      *)
(*   qc = \i. ooc c1 c2 a b l (EL i c1091od_masks), ..., qa = \i. l.         *)
(* Lean inline pulls (pullX (pullY ..), pullY, pullSwap (pullY ..)) are      *)
(* factored into the one-square lemmas C1091RP_RIGHT_WALL, C1091RP_SOUTH,    *)
(* C1091RP_EAST (same geometric content, applied to owners p 10 / p 5).      *)
(* Dependencies: DirectDomains (C1091DD_ thms), C1089 ContinuousBottom.          *)
(* reach_of_far (C1089CB_REACH_OF_FAR), ContinuousActual.southeast           *)
(* (C1089CA_SOUTHEAST), C981 Crosspoint.point (C981CP_POINT),                *)
(* WallUpperMissingReach.point (WUMR_POINT), WallLowerCenterBarrier.         *)
(* center_above (WLCB_CENTER_ABOVE), Residual.impossible (C1091RE_IMPOSSIBLE).*)
(* Tag C1091RP_ / c1091rp_.                                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1091_DirectDomains.ml";;
needs "n12/geometry/CP_OtherCases_C1091_ResidualEnding.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ContinuousActual.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ContinuousBottom.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;
needs "n12/geometry/WallUpperMissingReach.ml";;
needs "n12/geometry/WallLowerCenterBarrier.ml";;

(* Lean: ResidualEntrance (structure) *)
let c1091rp_entrance = new_definition
 `c1091rp_entrance (qc:num->real) (qs:num->real) (qu:num->real) (qv:num->real) (qa:num->real) <=>
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&1) (&1) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&1) (&87 / &50) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&2) (&87 / &50) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&113 / &50) (&2) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&3) (&113 / &50) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&8 / &5) (&3)`;;

let c1091rp_owners = map (fun f -> mk_abs(`i:num`, list_mk_comb(f,
    [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `EL i c1091od_masks`])))
  [`ooc`; `oos`; `oou`; `oov`] @ [`\i:num. (l:real)`];;

let C1091RP_EL_CONV = REWRITE_CONV[c1091od_masks] THENC ONCE_DEPTH_CONV EL_CONV;;

let C1091RP_UNIT_TAC =
  REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN RASM_ARITH_TAC;;

let C1091RP_LCY_PULLXY = prove
 (`forall c s u v a. c * c + s * s = &1
     ==> lcy (--c) (--s) ((u - &4 * s) - &4 * c) (--(&4 * c - v - a) - a - &4 * --s) a =
         &4 - lcy c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lcy] THEN CONV_TAC REAL_RING);;

(* right-centre sign and low point of owners p 10, through R = pullX (pullY q) *)
let C1091RP_RIGHT_WALL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&1543 / &500) (&2) /\ linside c s u v a (&3) (&8 / &5) /\
     ~linside c s u v a (&3) (&113 / &50) /\ ~linside c s u v a (&47 / &20) (&33 / &20)
     ==> lcy c s u v a <= &2 /\ linside c s u v a (&3) (&36 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let r = [`--c:real`; `--s:real`; `(u - &4 * s) - &4 * c:real`;
           `--(&4 * c - v - a) - a - &4 * --s:real`; `a:real`] in
  MP_TAC(SPECL r WLCB_CENTER_ABOVE) THEN MP_TAC(SPECL r WUMR_POINT) THEN
  SUBGOAL_THEN (list_mk_comb(`lcont`, r)) ASSUME_TAC THENL
   [MATCH_MP_TAC LCONT_PULLX THEN MATCH_MP_TAC LCONT_PULLY THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LINSIDE_PULLX; LINSIDE_PULLY;
              MATCH_MP C1091RP_LCY_PULLXY (ASSUME `c * c + s * s = &1`)] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [C1091RP_UNIT_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [C1091RP_UNIT_TAC; DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

(* Lean: (inline) south = C981CompletionCrosspoint.point (pullY (owners p 5)) *)
let C1091RP_SOUTH = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&2) (&87 / &50) /\ linside c s u v a (&113 / &50) (&2) /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     ~linside c s u v a (&47 / &20) (&47 / &20) /\ ~linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&3) (&8 / &5) /\ ~linside c s u v a (&3) (&3 / &2)
     ==> linside c s u v a (&2) (&3 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `--s:real`; `u - &4 * s:real`; `&4 * c - v - a:real`; `a:real`]
    C981CP_POINT) THEN
  REWRITE_TAC[LINSIDE_PULLY] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [C1091RP_UNIT_TAC; REWRITE_TAC[]]);;

(* Lean: (inline) east = C981CompletionCrosspoint.point (pullSwap (pullY (owners p 5))) *)
let C1091RP_EAST = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&113 / &50) (&2) /\ linside c s u v a (&2) (&87 / &50) /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     ~linside c s u v a (&33 / &20) (&33 / &20) /\ ~linside c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&12 / &5) (&1) /\ ~linside c s u v a (&5 / &2) (&1)
     ==> linside c s u v a (&5 / &2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`--s:real`; `c:real`; `u - &4 * s:real`; `--(&4 * c - v - a) - a:real`; `a:real`]
    C981CP_POINT) THEN
  REWRITE_TAC[LINSIDE_PULLSW; LINSIDE_PULLY] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [C1091RP_UNIT_TAC; REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Owner-level helpers (literal masks).                                      *)
(* ------------------------------------------------------------------------- *)

let C1091RP_F = `c1091od_family`;;
let c1091rp_own m =
  let mt = mk_small_numeral m in
  map (fun f -> list_mk_comb(f, [`c1:num->real`; `c2:num->real`; `a:num->real`;
                                 `b:num->real`; `l:real`; mt])) [`ooc`; `oos`; `oou`; `oov`]
  @ [`l:real`];;
let c1091rp_ins m (x, y) = list_mk_comb(`linside`, c1091rp_own m @ [x; y]);;

(* seed point of owners p i *)
let C1091RP_SEED_TAC i xy =
  MP_TAC(SPEC_ALL (c1091od_seed i xy)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC;;

(* foreign: a point of owner n (an assumption) is not in owner m *)
let C1091RP_FOREIGN_TAC m n (x, y) =
  SUBGOAL_THEN (mk_neg (c1091rp_ins m (x, y))) ASSUME_TAC THENL
   [MP_TAC(SPEC_ALL (oo_apart C1091RP_F m n)) THEN ASM_REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [x; y]) THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let C1091RP_USE_TAC th = MP_TAC(SPEC_ALL th) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC;;

(* the forall fields of an Input-like structure over c1091rp_owners *)
let C1091RP_FIELD_TAC =
  FIRST
   [GEN_TAC THEN DISCH_TAC THEN MP_TAC (SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    GEN_TAC THEN DISCH_TAC THEN MP_TAC (SPEC_ALL OO_SIDE_LE) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN NO_TAC;
    GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[OO_UNIT] THEN NO_TAC;
    ASM_SIMP_TAC[OO_BOX] THEN NO_TAC;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                   `i:num`; `j:num`] C1091OD_APART) THEN
    ASM_REWRITE_TAC[ldisj] THEN NO_TAC;
    CONV_TAC C1091RP_EL_CONV THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REWRITE_TAC[]) THEN NO_TAC];;

(* Lean: residual_input *)
let C1091RP_RESIDUAL_INPUT =
  let vars = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] in
  let ent = list_mk_comb(`c1091rp_entrance`, c1091rp_owners)
  and inp = list_mk_comb(`c1091ri_input`, c1091rp_owners) in
  let fr x y = (x, y) in
  prove
   (list_mk_forall(vars, mk_imp(mk_conj(
      `NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1091od_family`, ent), inp)),
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
      (STRIP_ASSUME_TAC o CONV_RULE C1091RP_EL_CONV o BETA_RULE o REWRITE_RULE[c1091rp_entrance])) THEN
    (* units, sides, boxes of the owners used below *)
    MAP_EVERY (fun m ->
      let mt = mk_small_numeral m in
      ASSUME_TAC(UNDISCH(SPECL (vars @ [mt]) OO_UNIT)) THEN
      ASSUME_TAC(UNDISCH(SPECL (vars @ [mt]) OO_BOX))) [512; 8192; 16384] THEN
    ASSUME_TAC(UNDISCH(SPECL vars OO_SIDE)) THEN
    C1091RP_USE_TAC C1091OD_MERGED_MARKERS THEN
    C1091RP_SEED_TAC 5 (fr `&47 / &20` `&33 / &20`) THEN
    C1091RP_SEED_TAC 6 (fr `&47 / &20` `&47 / &20`) THEN
    C1091RP_SEED_TAC 7 (fr `&33 / &20` `&47 / &20`) THEN
    C1091RP_SEED_TAC 8 (fr `&457 / &500` `&2`) THEN
    C1091RP_SEED_TAC 9 (fr `&2` `&457 / &500`) THEN
    C1091RP_SEED_TAC 10 (fr `&1543 / &500` `&2`) THEN
    C1091RP_SEED_TAC 11 (fr `&2` `&1543 / &500`) THEN
    C1091RP_SEED_TAC 0 (fr `&87 / &50` `&1`) THEN
    C1091RP_SEED_TAC 0 (fr `&187 / &100` `&19 / &25`) THEN
    C1091RP_SEED_TAC 1 (fr `&3` `&1`) THEN
    C1091RP_SEED_TAC 1 (fr `&1543 / &500` `&1`) THEN
    C1091RP_SEED_TAC 2 (fr `&3` `&3`) THEN
    C1091RP_USE_TAC C1091DD_LEFT_PAIR THEN
    C1091RP_USE_TAC C1091DD_BOTTOM_FAR THEN
    C1091RP_USE_TAC C1091DD_RIGHT_PAIR THEN
    C1091RP_USE_TAC C1091DD_TOP_PAIR THEN
    (* bottomReach *)
    C1091RP_FOREIGN_TAC 8192 1 (fr `&87 / &50` `&1`) THEN
    C1091RP_FOREIGN_TAC 8192 1 (fr `&187 / &100` `&19 / &25`) THEN
    C1091RP_FOREIGN_TAC 8192 512 (fr `&47 / &20` `&33 / &20`) THEN
    MP_TAC(SPECL (c1091rp_own 8192) C1089CB_REACH_OF_FAR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    (* rightSign, rightLow *)
    C1091RP_FOREIGN_TAC 16384 1024 (fr `&3` `&113 / &50`) THEN
    C1091RP_FOREIGN_TAC 16384 512 (fr `&47 / &20` `&33 / &20`) THEN
    MP_TAC(SPECL (c1091rp_own 16384) C1091RP_RIGHT_WALL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    (* centers *)
    MP_TAC(SPECL c1091rp_owners C1089CA_SOUTHEAST) THEN BETA_TAC THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN C1091RP_FIELD_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV C1091RP_EL_CONV) THEN STRIP_TAC THEN
    (* rightBar *)
    SUBGOAL_THEN (mk_forall(`y:real`, mk_imp(`&36 / &25 <= y /\ y <= &2`,
                    c1091rp_ins 16384 (fr `&3` `y:real`)))) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN
      MAP_EVERY EXISTS_TAC [`&36 / &25`; `&2`] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN (mk_conj(c1091rp_ins 16384 (fr `&3` `&8 / &5`),
                          c1091rp_ins 16384 (fr `&3` `&3 / &2`))) STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    (* south *)
    C1091RP_FOREIGN_TAC 512 1024 (fr `&47 / &20` `&47 / &20`) THEN
    C1091RP_FOREIGN_TAC 512 258 (fr `&33 / &20` `&33 / &20`) THEN
    C1091RP_FOREIGN_TAC 512 16384 (fr `&3` `&8 / &5`) THEN
    C1091RP_FOREIGN_TAC 512 16384 (fr `&3` `&3 / &2`) THEN
    MP_TAC(SPECL (c1091rp_own 512) C1091RP_SOUTH) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    (* east *)
    SUBGOAL_THEN (mk_conj(c1091rp_ins 8192 (fr `&12 / &5` `&1`),
                          c1091rp_ins 8192 (fr `&5 / &2` `&1`))) STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    C1091RP_FOREIGN_TAC 512 8192 (fr `&12 / &5` `&1`) THEN
    C1091RP_FOREIGN_TAC 512 8192 (fr `&5 / &2` `&1`) THEN
    MP_TAC(SPECL (c1091rp_own 512) C1091RP_EAST) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    (* northeastG9, northwestG *)
    C1091RP_USE_TAC C1091DD_NORTHEAST_OUTER THEN
    MP_TAC(SPEC_ALL C1091DD_NORTHWEST_COVER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[c1091ri_input] THEN BETA_TAC THEN REPEAT CONJ_TAC THEN C1091RP_FIELD_TAC);;

(* Lean: impossible_of_residual_entrance *)
let C1091RP_IMPOSSIBLE_OF_RESIDUAL_ENTRANCE =
  let vars = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] in
  let ent = list_mk_comb(`c1091rp_entrance`, c1091rp_owners) in
  prove
   (list_mk_forall(vars, mk_imp(mk_conj(
      `NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1091od_family`, ent), `false`)),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPEC_ALL C1091RP_RESIDUAL_INPUT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL c1091rp_owners C1091RE_IMPOSSIBLE) THEN ASM_REWRITE_TAC[] THEN
    BETA_TAC THEN ASM_SIMP_TAC[OO_UNIT]);;
