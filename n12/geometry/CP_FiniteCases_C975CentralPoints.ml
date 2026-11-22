(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C975CentralPoints.lean            *)
(* (namespace N12Compact.FiniteCases.C975Selection; Lean header: "Source     *)
(* only, uncompiled").  Central and wall producers after the C975 selection  *)
(* cuts.  owner p m is the 5-tuple (ooc .. m) .. l; q.translated 2 2 is      *)
(* (c, s, u - (c 2 + s 2), v - (--s 2 + c 2), a) (C975CP_TRANSLATED).        *)
(* F4PointTransfers.horizontal_original: OCF4PT_HORIZONTAL_ORIGINAL;         *)
(* C1090.ResidualCentralPoints.mixed_point / southeast_point / Parameters:   *)
(* C1090RCP_MIXED_POINT / C1090RCP_SOUTHEAST_POINT / c1090rcp_parameters;    *)
(* WallProfile.boundary_origin: OCWPBO_BOUNDARY_ORIGIN; C981CompletionWall-  *)
(* Advance.point: C981WA_POINT; SouthwestSupportPoint.point_of_neighbours:   *)
(* OCSWSPM_POINT_OF_NEIGHBOURS.  The local transfer of southeast_lower is    *)
(* C975CP_TRANSFER.  Tag C975CP_.                                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C975ResidualSelection.ml";;
needs "n12/geometry/CP_OtherCases_C1090_ResidualCentralPoints.ml";;
needs "n12/geometry/CP_OtherCases_F4PointTransfers.ml";;
needs "n12/geometry/CP_OtherCases_SouthwestSupportPoint_Main.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_BoundaryOrigin.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;

let C975CP_TRANSLATED = prove
 (`forall c s u v a tx ty x y.
     linside c s (u - (c * tx + s * ty)) (v - (--s * tx + c * ty)) a x y <=>
     linside c s u v a (tx + x) (ty + y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* an owner fact |- .. /\ lo <= x /\ x <= hi ==> P x at a literal point *)
let c975cp_inst th t =
  let th1 = SPEC t (SPECL C975IC_V5 th) in
  prove(c975ic_stmt [] (rand (concl th1)),
    REPEAT STRIP_TAC THEN MATCH_MP_TAC th1 THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let C975CP_WALL_TAC m =
  REPEAT GEN_TAC THEN
  DISCH_THEN (MP_TAC o MATCH_MP (REWRITE_RULE[lcont]
    (UNDISCH (SPECL (C975IC_V5 @ [mk_small_numeral m]) OO_BOX)))) THEN
  REAL_ARITH_TAC;;

let C975CP_APPLY_TAC th tp ths fors extra =
  let th' = CONV_RULE (REWRITE_CONV[C975CP_TRANSLATED; LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW] THENC
                       REAL_RAT_REDUCE_CONV) (SPECL tp th) in
  let th' = if is_neg (concl th') then NOT_ELIM th' else th' in
  (if rand (concl th') = `false`
   then SUBGOAL_THEN (lhand (concl th')) (fun h -> ACCEPT_TAC (MP th' h))
   else MATCH_MP_TAC th') THEN
  REPEAT CONJ_TAC THEN
  FIRST ([C975IC_SIDE_TAC ths fors;
          CONV_TAC (REWRITE_CONV[c1090rcp_parameters] THENC REAL_RAT_REDUCE_CONV) THEN NO_TAC] @ extra);;

let c975cp_tr22 q = c975rs_tr22 q;;

let C975CP_BOTTOM_52 = c975cp_inst C975SEL_BOTTOM_BAR `&5 / &2`;;

(* Lean: southeast_east *)
let C975CP_SOUTHEAST_EAST = prove
 (c975ic_stmt [] (c975ic_own 512 `&5 / &2` `&2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C975CP_APPLY_TAC OCF4PT_HORIZONTAL_ORIGINAL (c975ic_owner 512)
   [C975SS_SE_MARKER; C975RS_SOUTHEAST_G6_POINT; C975SS_SE_F8]
   [256, C975SS_SW_F4; 8192, C975CP_BOTTOM_52] []);;

(* Lean: northeast_mixed_sharp *)
let C975CP_NORTHEAST_MIXED_SHARP = prove
 (c975ic_stmt [c975ic_own 1024 `&2` `&113 / &50`] (c975ic_own 1024 `&121 / &50` `&54 / &25`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C975CP_APPLY_TAC C1090RCP_MIXED_POINT (c975cp_tr22 (c975ic_owner 1024))
   [C975SS_NE_MARKER; C975SEL_NORTHEAST_SELECTION]
   [34816, C975SS_NW_MARKER; 34816, C975TO_TOP_ORIGIN; 48, C975RS_CORNER; 16384, C975SS_RIGHT_F9] []);;

(* Lean: transfer (local in southeast_lower) *)
let C975CP_TRANSFER = prove
 (`forall c1 c2 a b l x y. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c975d_family /\
     c1090rcp_parameters x y /\
     linside (ooc c1 c2 a b l 1024) (oos c1 c2 a b l 1024) (oou c1 c2 a b l 1024) (oov c1 c2 a b l 1024) l (&2 + x) (&2 + y)
     ==> linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512) (oov c1 c2 a b l 512) l (&3) (&3 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C975CP_APPLY_TAC C1090RCP_SOUTHEAST_POINT (c975cp_tr22 (c975ic_owner 512) @ [`x:real`; `y:real`])
   [C975SS_SE_MARKER; C975RS_SOUTHEAST_G6_POINT; C975SS_SE_F8]
   [256, C975SS_SOUTHWEST_SOUTH;
    1024, ASSUME (c975ic_own 1024 `&2 + x` `&2 + y`)] []);;

(* Lean: southeast_lower *)
let C975CP_SOUTHEAST_LOWER = prove
 (c975ic_stmt [] (c975ic_own 512 `&3` `&3 / &2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC (c975ic_own 1024 `&2` `&113 / &50`) THENL
   [MP_TAC (SPEC_ALL C975CP_NORTHEAST_MIXED_SHARP) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC C975CP_TRANSFER THEN MAP_EVERY EXISTS_TAC [`&21 / &50`; `&4 / &25`];
    MP_TAC (SPEC_ALL C975RS_NORTHEAST_UPPER_SHARP) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC C975CP_TRANSFER THEN MAP_EVERY EXISTS_TAC [`&21 / &40`; `&1 / &8`]] THEN
  REWRITE_TAC[c1090rcp_parameters] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let C975CP_CORNER_MARKER = c975ss_seed_point 12 (`&3`, `&457 / &500`);;

(* Lean: bottom_origin *)
let C975CP_BOTTOM_ORIGIN = prove
 (c975ic_stmt [] (c975ic_own 8192 `&2` `&1`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C975CP_APPLY_TAC OCWPBO_BOUNDARY_ORIGIN
    (c975ic_pullx (c975ic_owner 8192) @ c975ic_pullx (c975ic_owner 12) @ [`&457 / &500`; `&8 / &5`])
   [C975SS_BOTTOM_MARKER; C975SS_BOTTOM_F6; C975CP_CORNER_MARKER; C975SS_SE_CORNER]
   [512, C975CP_SOUTHEAST_LOWER]
   [C975CP_WALL_TAC 8192; C975CP_WALL_TAC 12;
    REWRITE_TAC[ldisj; LINSIDE_PULLX] THEN
    MP_TAC (SPEC_ALL (oo_apart C975D_F 12 8192)) THEN ASM_REWRITE_TAC[ldisj] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[]]);;

(* Lean: left_reach *)
let C975CP_LEFT_REACH = prove
 (c975ic_stmt [] (c975ic_own 4096 `&1` `&14 / &5`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C975CP_APPLY_TAC C981WA_POINT (c975ic_owner 4096)
   [C975IP_L_MARKER; C975IP_L_HIGH]
   [2, C975SS_V2; 2, C975IP_L_SEED; 34816, C975SS_NW_MARKER] []);;

(* Lean: southwest_support *)
let C975CP_SOUTHWEST_SUPPORT = prove
 (c975ic_stmt [] (c975ic_own 256 `&127 / &100` `&49 / &25`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C975CP_APPLY_TAC OCSWSPM_POINT_OF_NEIGHBOURS (c975ic_owner 256 @ c975ic_owner 1 @ c975ic_owner 512)
   [C975SS_SW_MARKER; C975SS_SW_F4; C975SS_SW_G3; C975SS_SOUTHWEST_WEST; C975SS_SOUTHWEST_SOUTH;
    c975cp_inst C975SS_SINGLETON_HORIZONTAL `&3 / &2`; C975SS_H2;
    C975SS_SE_MARKER; C975RS_SOUTHEAST_G6_POINT]
   [34816, C975SS_NW_MARKER; 8192, C975CP_BOTTOM_ORIGIN;
    2, c975cp_inst C975SS_SINGLETON_VERTICAL `&8 / &5`; 2, C975SS_V2]
   (map (fun n -> MP_TAC (SPEC_ALL (oo_apart C975D_F 256 n)) THEN ASM_REWRITE_TAC[ldisj] THEN NO_TAC)
        [1; 512]));;
