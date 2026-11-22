(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/WallOrigins.lean              *)
(* (N12Compact.Completion.OtherCases.C1089.WallOrigins).  Actual-owner       *)
(* wall-origin applications in C1089-LAST-SECTOR-POINTS / -REDUCTION.        *)
(* The family q : Fin 12 -> OpenSquare enters only through the squares used  *)
(* by each theorem; square q i is ci si ui vi ai (with its OpenSquare        *)
(* invariants), InsideContainer is lcont, and only the used instances of    *)
(* the pairwise disjointness are assumed (ldisj).  pullX / pullY / pullSwap  *)
(* are the explicit squares of LINSIDE_PULLX / _PULLY / _PULLSW.             *)
(* boundary_origin is OCWPBO_BOUNDARY_ORIGIN; WallUpperMissingReach.point is *)
(* WUMR_POINT; OrdinaryMarkerHalfpoint.northeast/northwest_halfpoint are     *)
(* OCOMHM_*; inside_segment is CES_INSIDE_SEGMENT.  Tag OC1089WO_.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_BoundaryOrigin.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryMarkerHalfpoint_Main.ml";;
needs "n12/geometry/WallUpperMissingReach.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;

let oc1089wo_sq n =
  map (fun p -> mk_var(p ^ string_of_int n, `:real`)) ["c"; "s"; "u"; "v"; "a"];;

let oc1089wo_pull th tup =
  match tup with
    [c; s; u; v; a] ->
      let t = SPECL [c; s; u; v; a; `x:real`; `y:real`] th in
      let args = snd(strip_comb(lhs(concl t))) in
      [el 0 args; el 1 args; el 2 args; el 3 args; el 4 args]
  | _ -> failwith "oc1089wo_pull";;
let oc1089wo_px = oc1089wo_pull LINSIDE_PULLX;;
let oc1089wo_py = oc1089wo_pull LINSIDE_PULLY;;
let oc1089wo_psw = oc1089wo_pull LINSIDE_PULLSW;;

(* a wall goal  !x y. linside Q X Y ==> P  from the (unfolded) containments *)
let OC1089WO_WALL_TAC (asl,w as g) =
  (REPEAT GEN_TAC THEN
   DISCH_THEN(fun h ->
     EVERY (mapfilter (fun (_,th) -> MP_TAC(MATCH_MP th h)) asl)) THEN
   REAL_ARITH_TAC) g;;

let OC1089WO_GOAL_TAC =
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC; ASM_REAL_ARITH_TAC; OC1089WO_WALL_TAC;
         ASM_MESON_TAC[]];;

let OC1089WO_APPLY th args =
  MP_TAC(SPECL args th) THEN
  REWRITE_TAC[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW; ldisj; lcont] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN OC1089WO_GOAL_TAC; REWRITE_TAC[]];;

let OC1089WO_START_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ldisj; lcont]);;

(* Lean: bottom_origin *)
let OC1089WO_BOTTOM_ORIGIN = prove
 (`forall c9 s9 u9 v9 a9 c1 s1 u1 v1 a1 c10 s10 u10 v10 a10.
     c9 * c9 + s9 * s9 = &1 /\ &0 < a9 /\ c1 * c1 + s1 * s1 = &1 /\ &0 < a1 /\
     c10 * c10 + s10 * s10 = &1 /\ &0 < a10 /\
     &1 < a9 /\ a9 = a1 /\
     lcont c9 s9 u9 v9 a9 /\ lcont c1 s1 u1 v1 a1 /\
     ldisj c1 s1 u1 v1 a1 c10 s10 u10 v10 a10 /\ ldisj c1 s1 u1 v1 a1 c9 s9 u9 v9 a9 /\
     linside c9 s9 u9 v9 a9 (&2) (&457 / &500) /\ linside c9 s9 u9 v9 a9 (&12 / &5) (&1) /\
     linside c1 s1 u1 v1 a1 (&3) (&457 / &500) /\ linside c1 s1 u1 v1 a1 (&3) (&1) /\
     linside c10 s10 u10 v10 a10 (&3) (&36 / &25) /\ linside c10 s10 u10 v10 a10 (&3) (&8 / &5)
     ==> linside c9 s9 u9 v9 a9 (&2) (&1)`,
  OC1089WO_START_TAC THEN
  SUBGOAL_THEN `linside c10 s10 u10 v10 a10 (&3) (&3 / &2)` ASSUME_TAC THENL
   [MP_TAC(SPECL (oc1089wo_sq 10 @ [`&3`; `&36 / &25`; `&3`; `&8 / &5`; `&3 / &8`])
      CES_INSIDE_SEGMENT) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  OC1089WO_APPLY OCWPBO_BOUNDARY_ORIGIN
    (oc1089wo_px (oc1089wo_sq 9) @ oc1089wo_px (oc1089wo_sq 1) @ [`&457 / &500`; `&8 / &5`]));;

(* Lean: top_origin *)
let OC1089WO_TOP_ORIGIN = prove
 (`forall c11 s11 u11 v11 a11 c2 s2 u2 v2 a2 c6 s6 u6 v6 a6.
     c11 * c11 + s11 * s11 = &1 /\ &0 < a11 /\ c2 * c2 + s2 * s2 = &1 /\ &0 < a2 /\
     &1 < a11 /\ a11 = a2 /\
     lcont c11 s11 u11 v11 a11 /\ lcont c2 s2 u2 v2 a2 /\
     ldisj c2 s2 u2 v2 a2 c6 s6 u6 v6 a6 /\ ldisj c2 s2 u2 v2 a2 c11 s11 u11 v11 a11 /\
     linside c11 s11 u11 v11 a11 (&2) (&1543 / &500) /\
     linside c11 s11 u11 v11 a11 (&12 / &5) (&3) /\
     linside c2 s2 u2 v2 a2 (&3) (&1543 / &500) /\ linside c2 s2 u2 v2 a2 (&3) (&3) /\
     linside c6 s6 u6 v6 a6 (&3) (&5 / &2)
     ==> linside c11 s11 u11 v11 a11 (&2) (&3)`,
  OC1089WO_START_TAC THEN
  OC1089WO_APPLY OCWPBO_BOUNDARY_ORIGIN
    (oc1089wo_py (oc1089wo_px (oc1089wo_sq 11)) @ oc1089wo_py (oc1089wo_px (oc1089wo_sq 2)) @
     [`&457 / &500`; `&8 / &5`]));;

(* Lean: top_origin_of_ordinary *)
let OC1089WO_TOP_ORIGIN_OF_ORDINARY = prove
 (`forall c6 s6 u6 v6 a6 c5 s5 u5 v5 a5 c10 s10 u10 v10 a10 c2 s2 u2 v2 a2
    c11 s11 u11 v11 a11.
     c6 * c6 + s6 * s6 = &1 /\ &0 < a6 /\ c11 * c11 + s11 * s11 = &1 /\ &0 < a11 /\
     c2 * c2 + s2 * s2 = &1 /\ &0 < a2 /\
     &1 < a6 /\ &1 < a11 /\ a11 = a2 /\
     lcont c11 s11 u11 v11 a11 /\ lcont c2 s2 u2 v2 a2 /\
     ldisj c6 s6 u6 v6 a6 c5 s5 u5 v5 a5 /\ ldisj c6 s6 u6 v6 a6 c10 s10 u10 v10 a10 /\
     ldisj c6 s6 u6 v6 a6 c2 s2 u2 v2 a2 /\ ldisj c6 s6 u6 v6 a6 c11 s11 u11 v11 a11 /\
     ldisj c2 s2 u2 v2 a2 c6 s6 u6 v6 a6 /\ ldisj c2 s2 u2 v2 a2 c11 s11 u11 v11 a11 /\
     linside c6 s6 u6 v6 a6 (&47 / &20) (&47 / &20) /\
     linside c6 s6 u6 v6 a6 (&3) (&113 / &50) /\ linside c6 s6 u6 v6 a6 (&3) (&12 / &5) /\
     linside c5 s5 u5 v5 a5 (&113 / &50) (&2) /\
     linside c10 s10 u10 v10 a10 (&1543 / &500) (&2) /\
     linside c11 s11 u11 v11 a11 (&113 / &50) (&3) /\
     linside c11 s11 u11 v11 a11 (&2) (&1543 / &500) /\
     linside c11 s11 u11 v11 a11 (&12 / &5) (&3) /\
     linside c2 s2 u2 v2 a2 (&3) (&1543 / &500) /\ linside c2 s2 u2 v2 a2 (&3) (&3)
     ==> linside c11 s11 u11 v11 a11 (&2) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (oc1089wo_sq 6) OCOMHM_NORTHEAST_HALFPOINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
    REPEAT CONJ_TAC THEN ASM_MESON_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC OC1089WO_TOP_ORIGIN THEN
  MAP_EVERY EXISTS_TAC (oc1089wo_sq 2 @ oc1089wo_sq 6) THEN ASM_REWRITE_TAC[]);;

(* Lean: top_advance *)
let OC1089WO_TOP_ADVANCE = prove
 (`forall c11 s11 u11 v11 a11 c7 s7 u7 v7 a7 c6 s6 u6 v6 a6.
     c11 * c11 + s11 * s11 = &1 /\ &0 < a11 /\ &1 < a11 /\ lcont c11 s11 u11 v11 a11 /\
     ldisj c11 s11 u11 v11 a11 c7 s7 u7 v7 a7 /\ ldisj c11 s11 u11 v11 a11 c6 s6 u6 v6 a6 /\
     linside c11 s11 u11 v11 a11 (&2) (&1543 / &500) /\
     linside c11 s11 u11 v11 a11 (&12 / &5) (&3) /\
     linside c7 s7 u7 v7 a7 (&87 / &50) (&3) /\
     linside c6 s6 u6 v6 a6 (&47 / &20) (&47 / &20)
     ==> linside c11 s11 u11 v11 a11 (&64 / &25) (&3)`,
  OC1089WO_START_TAC THEN
  OC1089WO_APPLY WUMR_POINT (oc1089wo_psw (oc1089wo_py (oc1089wo_sq 11))));;

(* Lean: left_advance *)
let OC1089WO_LEFT_ADVANCE = prove
 (`forall c8 s8 u8 v8 a8 c4 s4 u4 v4 a4 c7 s7 u7 v7 a7.
     c8 * c8 + s8 * s8 = &1 /\ &0 < a8 /\ &1 < a8 /\ lcont c8 s8 u8 v8 a8 /\
     ldisj c8 s8 u8 v8 a8 c4 s4 u4 v4 a4 /\ ldisj c8 s8 u8 v8 a8 c7 s7 u7 v7 a7 /\
     linside c8 s8 u8 v8 a8 (&457 / &500) (&2) /\ linside c8 s8 u8 v8 a8 (&1) (&12 / &5) /\
     linside c4 s4 u4 v4 a4 (&1) (&87 / &50) /\
     linside c7 s7 u7 v7 a7 (&33 / &20) (&47 / &20)
     ==> linside c8 s8 u8 v8 a8 (&1) (&64 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC WUMR_POINT THEN
  ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  CONJ_TAC THEN ASM_MESON_TAC[]);;

(* Lean: right_low *)
let OC1089WO_RIGHT_LOW = prove
 (`forall c10 s10 u10 v10 a10 c6 s6 u6 v6 a6 c5 s5 u5 v5 a5.
     c10 * c10 + s10 * s10 = &1 /\ &0 < a10 /\ &1 < a10 /\ lcont c10 s10 u10 v10 a10 /\
     ldisj c10 s10 u10 v10 a10 c6 s6 u6 v6 a6 /\ ldisj c10 s10 u10 v10 a10 c5 s5 u5 v5 a5 /\
     linside c10 s10 u10 v10 a10 (&1543 / &500) (&2) /\
     linside c10 s10 u10 v10 a10 (&3) (&8 / &5) /\
     linside c6 s6 u6 v6 a6 (&3) (&113 / &50) /\
     linside c5 s5 u5 v5 a5 (&47 / &20) (&33 / &20)
     ==> linside c10 s10 u10 v10 a10 (&3) (&36 / &25)`,
  OC1089WO_START_TAC THEN
  OC1089WO_APPLY WUMR_POINT (oc1089wo_py (oc1089wo_px (oc1089wo_sq 10))));;

(* Lean: top_left_advance *)
let OC1089WO_TOP_LEFT_ADVANCE = prove
 (`forall c11 s11 u11 v11 a11 c6 s6 u6 v6 a6 c7 s7 u7 v7 a7.
     c11 * c11 + s11 * s11 = &1 /\ &0 < a11 /\ &1 < a11 /\ lcont c11 s11 u11 v11 a11 /\
     ldisj c11 s11 u11 v11 a11 c6 s6 u6 v6 a6 /\ ldisj c11 s11 u11 v11 a11 c7 s7 u7 v7 a7 /\
     linside c11 s11 u11 v11 a11 (&2) (&1543 / &500) /\
     linside c11 s11 u11 v11 a11 (&8 / &5) (&3) /\
     linside c6 s6 u6 v6 a6 (&113 / &50) (&3) /\
     linside c7 s7 u7 v7 a7 (&33 / &20) (&47 / &20)
     ==> linside c11 s11 u11 v11 a11 (&36 / &25) (&3)`,
  OC1089WO_START_TAC THEN
  OC1089WO_APPLY WUMR_POINT (oc1089wo_psw (oc1089wo_py (oc1089wo_px (oc1089wo_sq 11)))));;

(* Lean: top_origin_from_northwest *)
let OC1089WO_TOP_ORIGIN_FROM_NORTHWEST = prove
 (`forall c7 s7 u7 v7 a7 c4 s4 u4 v4 a4 c8 s8 u8 v8 a8 c11 s11 u11 v11 a11
    c3 s3 u3 v3 a3.
     c7 * c7 + s7 * s7 = &1 /\ &0 < a7 /\ c11 * c11 + s11 * s11 = &1 /\ &0 < a11 /\
     c3 * c3 + s3 * s3 = &1 /\ &0 < a3 /\
     &1 < a7 /\ &1 < a11 /\ a11 = a3 /\
     lcont c11 s11 u11 v11 a11 /\ lcont c3 s3 u3 v3 a3 /\
     ldisj c7 s7 u7 v7 a7 c4 s4 u4 v4 a4 /\ ldisj c7 s7 u7 v7 a7 c8 s8 u8 v8 a8 /\
     ldisj c7 s7 u7 v7 a7 c3 s3 u3 v3 a3 /\ ldisj c7 s7 u7 v7 a7 c11 s11 u11 v11 a11 /\
     ldisj c3 s3 u3 v3 a3 c7 s7 u7 v7 a7 /\ ldisj c3 s3 u3 v3 a3 c11 s11 u11 v11 a11 /\
     linside c7 s7 u7 v7 a7 (&33 / &20) (&47 / &20) /\
     linside c7 s7 u7 v7 a7 (&1) (&113 / &50) /\ linside c7 s7 u7 v7 a7 (&1) (&12 / &5) /\
     linside c4 s4 u4 v4 a4 (&87 / &50) (&2) /\
     linside c8 s8 u8 v8 a8 (&457 / &500) (&2) /\
     linside c11 s11 u11 v11 a11 (&87 / &50) (&3) /\
     linside c11 s11 u11 v11 a11 (&2) (&1543 / &500) /\
     linside c3 s3 u3 v3 a3 (&1) (&1543 / &500) /\ linside c3 s3 u3 v3 a3 (&1) (&3)
     ==> linside c11 s11 u11 v11 a11 (&2) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (oc1089wo_sq 7) OCOMHM_NORTHWEST_HALFPOINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
    REPEAT CONJ_TAC THEN ASM_MESON_TAC[]; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj; lcont]) THEN
  OC1089WO_APPLY OCWPBO_BOUNDARY_ORIGIN
    (oc1089wo_py (oc1089wo_sq 11) @ oc1089wo_py (oc1089wo_sq 3) @ [`&457 / &500`; `&87 / &50`]));;
