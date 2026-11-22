(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/C702.lean                          *)
(* (N12Compact.CommonCases.C702).  Complete original C702: the merged        *)
(* square's genuine upper auxiliary is forced first, then the actual SW and  *)
(* NW owners share one strict point.  The packing is NPACK c1 c2 a b l with  *)
(* family c702e_family; owner p m is the 5-tuple of C702OP_*.  The Lean      *)
(* charts pullY (pullX q) and Transform.pull <true,true,true> q are the      *)
(* explicit squares of LINSIDE_PULLX/_PULLY/_PULLSW.  Crosspoint.point,      *)
(* WallAdvance.point, SouthwestPoint.point, C702SouthPoint.point,            *)
(* C702NorthPoint.point_original are C981CP_POINT, C981WA_POINT,             *)
(* CCSWP_POINT, CCC7SP_POINT, CCC702P_POINT_ORIGINAL; ExcludesCase is        *)
(* excl_case (RowIdentity.ml), row 383.  Tag CCC702_.                        *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_C702OwnedPoints.ml";;
needs "n12/geometry/CP_CommonCases_C702SouthPoint.ml";;
needs "n12/geometry/CP_CommonCases_C702NorthPoint.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/CP_CommonCases_SouthwestPoint.ml";;
needs "n12/geometry/RowIdentity.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;

let ccc702_pull th tup =
  match tup with
    [c; s; u; v; a] ->
      let t = SPECL [c; s; u; v; a; `x:real`; `y:real`] th in
      let args = snd(strip_comb(lhs(concl t))) in
      [el 0 args; el 1 args; el 2 args; el 3 args; el 4 args]
  | _ -> failwith "ccc702_pull";;
let ccc702_pyx m = ccc702_pull LINSIDE_PULLY (ccc702_pull LINSIDE_PULLX (c702op_owner m));;
let ccc702_ptt m = ccc702_pull LINSIDE_PULLSW (ccc702_pyx m);;

let ccc702_apart_gen m n =
  REWRITE_RULE[ldisj] (MP (SPECL C702OP_VARS (oo_apart C702OP_F m n)) C702OP_H);;

(* ~ owner m at (x, y), from a point (x, y) of owner n in the assumptions *)
let CCC702_FOREIGN_TAC m n =
  MP_TAC(ccc702_apart_gen m n) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN NO_TAC ORELSE
    (W(fun (asl,w) -> let tm = rand w in
       let args = snd(strip_comb tm) in
       MP_TAC(SPECL [el 5 args; el 6 args] th) THEN ASM_REWRITE_TAC[])));;

let CCC702_WALL_TAC (asl,w as g) =
  (REPEAT GEN_TAC THEN
   DISCH_THEN(fun h -> EVERY (mapfilter (fun (_,th) -> MP_TAC(MATCH_MP th h)) asl)) THEN
   REAL_ARITH_TAC) g;;

let CCC702_APPLY lemma args =
  MP_TAC(SPECL args lemma) THEN
  REWRITE_TAC[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW; lcont] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC; ASM_REAL_ARITH_TAC; CCC702_WALL_TAC];;

let ccc702_use_apart m n =
  DISCH_THEN(fun th -> let args = snd(strip_comb(concl th)) in
    MP_TAC(SPECL [el 5 args; el 6 args] (ccc702_apart_gen m n)) THEN ASM_REWRITE_TAC[th]);;

let ccc702_seg_tac2 lemma m x0 y0 x1 y1 =
  MP_TAC(SPECL (c702op_owner m @ [x0; y0; x1; y1; `wn:real`]) lemma) THEN ASM_REWRITE_TAC[];;

let ccc702_seg_tac lemma m x0 y0 x1 y1 =
  MP_TAC(SPECL (c702op_owner m @ [x0; y0; x1; y1; `wt:real`]) lemma) THEN ASM_REWRITE_TAC[];;

let ccc702_foreign m n x y =
  SUBGOAL_THEN (mk_neg(c702op_lin m x y)) ASSUME_TAC THENL [CCC702_FOREIGN_TAC m n; ALL_TAC];;

(* Lean: family_impossible *)
let CCC702_FAMILY_IMPOSSIBLE = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c702e_family ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MP (SPECL C702OP_VARS C702OP_OWNED_POINTS) C702OP_H) THEN
  REWRITE_TAC[c702op_owned_points] THEN STRIP_TAC THEN
  MAP_EVERY (fun (m, p) -> ASSUME_TAC(c702op_seed m p))
   [256, (`&33 / &20`, `&33 / &20`); 1536, (`&47 / &20`, `&33 / &20`);
    1536, (`&47 / &20`, `&47 / &20`); 6144, (`&33 / &20`, `&47 / &20`);
    6144, (`&457 / &500`, `&2`); 32768, (`&2`, `&1543 / &500`); 192, (`&1`, `&3`);
    16, (`&213 / &100`, `&81 / &25`); 2, (`&19 / &25`, `&187 / &100`)] THEN
  MAP_EVERY (fun m -> ASSUME_TAC(c702op_unit m)) [256; 1536; 6144; 32768; 2] THEN
  ASSUME_TAC C702OP_SIDE THEN ASSUME_TAC C702OP_SIDE_POS THEN
  ASSUME_TAC(REWRITE_RULE[lcont] (MP (SPECL (C702OP_VARS @ [`32768`]) OO_BOX) (ASSUME C702OP_NP))) THEN
  (* the singleton bar points used below *)
  MAP_EVERY (fun (q, t) -> ASSUME_TAC(c702op_at (ASSUME q) t)) [] THEN
  FIRST_ASSUM(fun th -> if can (find_term ((=) `oou c1 c2 a b l 2`)) (concl th) &&
      is_forall(concl th) then
    MAP_EVERY (fun t -> ASSUME_TAC(c702op_at th t))
      [`&8 / &5`; `&3 / &2`; `&33 / &20`; `&87 / &50`] else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if can (find_term ((=) `oou c1 c2 a b l 1`)) (concl th) &&
      is_forall(concl th) then
    MAP_EVERY (fun t -> ASSUME_TAC(c702op_at th t))
      [`&8 / &5`; `&3 / &2`; `&33 / &20`] else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if can (find_term ((=) `oou c1 c2 a b l 32`)) (concl th) &&
      is_forall(concl th) then
    MAP_EVERY (fun t -> ASSUME_TAC(c702op_at th t)) [`&47 / &20`; `&113 / &50`] else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if can (find_term ((=) `oou c1 c2 a b l 16`)) (concl th) &&
      is_forall(concl th) then
    MAP_EVERY (fun t -> ASSUME_TAC(c702op_at th t)) [`&113 / &50`; `&47 / &20`] else NO_TAC) THEN
  ccc702_foreign 256 6144 `&33 / &20` `&47 / &20` THEN ccc702_foreign 256 1536 `&47 / &20` `&33 / &20` THEN
  ccc702_foreign 256 2 `&1` `&8 / &5` THEN ccc702_foreign 256 2 `&1` `&3 / &2` THEN
  ccc702_foreign 256 1 `&8 / &5` `&1` THEN ccc702_foreign 256 1 `&3 / &2` `&1` THEN
  SUBGOAL_THEN (c702op_lin 256 `&2` `&3 / &2`) ASSUME_TAC THENL
   [CCC702_APPLY C981CP_POINT (ccc702_pyx 256); ALL_TAC] THEN
  SUBGOAL_THEN (c702op_lin 256 `&3 / &2` `&2`) ASSUME_TAC THENL
   [CCC702_APPLY C981CP_POINT (ccc702_ptt 256); ALL_TAC] THEN
  ccc702_foreign 1536 32 `&3` `&47 / &20` THEN ccc702_foreign 1536 16 `&113 / &50` `&3` THEN
  ccc702_foreign 1536 16 `&47 / &20` `&3` THEN ccc702_foreign 1536 32 `&3` `&113 / &50` THEN
  SUBGOAL_THEN (c702op_lin 1536 `&41 / &20` `&41 / &20`) ASSUME_TAC THENL
   [CCC702_APPLY CCSWP_POINT (ccc702_pyx 1536); ALL_TAC] THEN
  ccc702_foreign 32768 16 `&113 / &50` `&3` THEN ccc702_foreign 32768 16 `&213 / &100` `&81 / &25` THEN
  ccc702_foreign 32768 6144 `&33 / &20` `&47 / &20` THEN
  SUBGOAL_THEN (c702op_lin 32768 `&6 / &5` `&3`) ASSUME_TAC THENL
   [CCC702_APPLY C981WA_POINT (ccc702_ptt 32768); ALL_TAC] THEN
  ccc702_foreign 256 2 `&1` `&33 / &20` THEN ccc702_foreign 256 1 `&33 / &20` `&1` THEN
  SUBGOAL_THEN (c702op_lin 256 `&13 / &10` `&193 / &100`) ASSUME_TAC THENL
   [MATCH_MP_TAC CCC7SP_POINT THEN ASM_REWRITE_TAC[] THEN

    X_GEN_TAC `wt:real` THEN REPEAT DISCH_TAC THEN
    ccc702_seg_tac CES_INSIDE_SEGMENT 1536 `&41 / &20` `&41 / &20` `&47 / &20` `&33 / &20` THEN
    ccc702_use_apart 256 1536; ALL_TAC] THEN
  ccc702_foreign 6144 256 `&3 / &2` `&2` THEN ccc702_foreign 6144 192 `&1` `&3` THEN
  SUBGOAL_THEN (c702op_lin 6144 `&13 / &10` `&193 / &100`) ASSUME_TAC THENL
   [MATCH_MP_TAC CCC702P_POINT_ORIGINAL THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `xt:real` THEN REPEAT DISCH_TAC THEN
      MP_TAC(SPECL (c702op_owner 32768 @ [`&6 / &5`; `&87 / &50`; `&3`; `xt:real`])
        OO_HORIZONTAL_SEGMENT) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
      ASM_REWRITE_TAC[] THEN ccc702_use_apart 6144 32768;
X_GEN_TAC `wn:real` THEN REPEAT DISCH_TAC THEN
      ccc702_seg_tac2 CES_INSIDE_SEGMENT 2 `&19 / &25` `&187 / &100` `&1` `&87 / &50` THEN
      REWRITE_TAC[REAL_MUL_RID] THEN ccc702_use_apart 6144 2]; ALL_TAC] THEN
  MP_TAC(SPECL [`&13 / &10`; `&193 / &100`] (ccc702_apart_gen 256 6144)) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: row_checked (private) / excludes *)
let CCC702_EXCLUDES = prove
 (`excl_case 702`,
  REWRITE_TAC[ri_excludes_case_iff 383 `c702e_family`; excl_fam] THEN
  MESON_TAC[CCC702_FAMILY_IMPOSSIBLE]);;
