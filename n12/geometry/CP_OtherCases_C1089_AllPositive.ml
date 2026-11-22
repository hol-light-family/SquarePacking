(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/AllPositive.lean              *)
(* (namespace N12Compact.Completion.OtherCases.C1089.AllPositive).  The      *)
(* all-positive C1089 sector, using the whole continuous MMMM ending on the  *)
(* actual Q6, Q5, Q7.  Conventions of WallCore.ml / SectorEntrances.ml       *)
(* (owners p i = owner at the literal mask EL i c1089sc_masks: 1 -> 12,      *)
(* 2 -> 48, 3 -> 192, 5 -> 512, 6 -> 1024, 7 -> 2048, 8 -> 4096, 9 -> 8192, *)
(* 10 -> 16384, 11 -> 32768).  q.translated 2 2 is (c, s, u - (c * &2 +      *)
(* s * &2), v - (--s * &2 + c * &2), a).  WallProfile.boundary_origin =      *)
(* OCWPBO_BOUNDARY_ORIGIN, CentralWallCenter.right_high / point =            *)
(* CWC_RIGHT_HIGH / CWC_POINT, C981CompletionCrosspoint.point = C981CP_POINT,*)
(* C1092MMMMEnding.Data / impossible = c1092mme_data / C1092MME_IMPOSSIBLE.  *)
(* (Lean header: "Source only, uncompiled".)  Tag C1089AP_.                  *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1089_SectorEntrances.ml";;
needs "n12/geometry/CP_C1092_MMMMEnding.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;
needs "n12/geometry/CentralWallCenter.ml";;
needs "n12/geometry/CP_OtherCases_C1089_WallOrigins.ml";;

let C1089AP_V = C1089WC_V;;
let c1089ap_own = c1089wc_own;;
let c1089ap_le = c1089se_le;;
let c1089ap_box m = MP (SPECL (C1089AP_V @ [mk_small_numeral m]) OO_BOX) (ASSUME C1089WC_NP);;
let c1089ap_ldisj m n = MP (SPECL C1089AP_V (oo_apart `c1089sc_family` m n)) (c1089wc_hh ());;

let C1089AP_SIDE_TAC =
  FIRST [(fun (asl, w as g) -> if is_comb w && fst (strip_comb w) = `ldisj` then
            (REWRITE_TAC[ldisj; LINSIDE_PULLSW; LINSIDE_PULLX; LINSIDE_PULLY] THEN
             CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
             REPEAT GEN_TAC THEN STRIP_TAC THEN C1089WC_CLASH_TAC) g
          else NO_TAC g);
         C1089WC_SIDE_TAC];;
let C1089AP_APPLY_TAC th =
  MP_TAC th THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN C1089AP_SIDE_TAC; CONV_TAC TAUT];;
let C1089AP_HAVE_TAC = C1089SE_HAVE_TAC;;

(* Lean: southeast_pair *)
let C1089AP_SOUTHEAST_PAIR = prove
 (c1089wc_stmt [] [c1089ap_le `&2` (c1089wc_lcy 16384); c1089ap_le `&2` (c1089wc_lcx 32768)]
    (mk_conj(c1089ap_own 512 `&3` `&87 / &50`, c1089ap_own 512 `&3` `&8 / &5`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1089WC_BASE_TAC [512] THEN
  C1089WC_USE_TAC C1089AP_V C1089WC_NORTHEAST_INWARD THEN
  C1089WC_USE_TAC C1089AP_V C1089WC_BOTTOM THEN
  FIRST_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) `&14 / &5`)) (concl th)
    then MAP_EVERY (fun x -> MP_TAC (SPEC x th) THEN CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
                             REWRITE_TAC[] THEN DISCH_TAC) [`&113 / &50`; `&239 / &100`]
    else NO_TAC) THEN
  C1089AP_HAVE_TAC (c1089ap_own 512 `&3` `&8 / &5`)
    (C1089SE_COVER_TAC C1089AC_SOUTHEAST_G_COVER) THEN
  ASSUME_TAC (c1089se_cover C1089AC_SOUTHEAST_F_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  C1089AP_APPLY_TAC (c1089wc_inst C1089SE_CLOCKWISE_PAIR (c1089wc_sw (c1089wc_py (c1089wc_tuple 512)))));;

(* Lean: northwest_pair *)
let C1089AP_NORTHWEST_PAIR = prove
 (c1089wc_stmt [] [c1089ap_le `&2` (c1089wc_lcy 4096); c1089ap_le `&2` (c1089wc_lcy 16384);
                   c1089ap_le `&2` (c1089wc_lcx 32768)]
    (mk_conj(c1089ap_own 2048 `&8 / &5` `&3`, c1089ap_own 2048 `&87 / &50` `&3`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1089WC_BASE_TAC [2048] THEN
  C1089WC_USE_TAC C1089AP_V C1089WC_NORTHEAST_INWARD THEN
  C1089SE_AT_TAC C1089WC_LEFT_HIGH `&113 / &50` THEN
  C1089SE_AT_TAC C1089WC_LEFT_HIGH `&239 / &100` THEN
  C1089AP_HAVE_TAC (c1089ap_own 2048 `&8 / &5` `&3`)
    (C1089SE_COVER_TAC C1089AC_NORTHWEST_F_COVER) THEN
  ASSUME_TAC (c1089se_cover C1089AC_NORTHWEST_G_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  C1089AP_APPLY_TAC (c1089wc_inst C1089SE_CLOCKWISE_PAIR (c1089wc_px (c1089wc_tuple 2048))));;

(* Lean: top_origin *)
let C1089AP_TOP_ORIGIN = prove
 (`forall cB sB uB vB aB cK sK uK vK aK.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     &1 < aB /\ aB = aK /\ lcont cB sB uB vB aB /\ lcont cK sK uK vK aK /\
     linside cB sB uB vB aB (&2) (&1543 / &500) /\ linside cB sB uB vB aB (&12 / &5) (&3) /\
     linside cK sK uK vK aK (&3) (&1543 / &500) /\ linside cK sK uK vK aK (&3) (&3) /\
     ~linside cK sK uK vK aK (&3) (&5 / &2) /\
     ldisj cK sK uK vK aK cB sB uB vB aB
     ==> linside cB sB uB vB aB (&2) (&3)`,
  OC1089WO_START_TAC THEN
  OC1089WO_APPLY OCWPBO_BOUNDARY_ORIGIN
    (oc1089wo_py (oc1089wo_px [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]) @
     oc1089wo_py (oc1089wo_px [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`]) @
     [`&457 / &500`; `&8 / &5`]));;

(* q.translated 2 2 *)
let C1089AP_TR_INSIDE = prove
 (`forall c s u v a x y.
     linside c s (u - (c * &2 + s * &2)) (v - (--s * &2 + c * &2)) a x y <=>
     linside c s u v a (&2 + x) (&2 + y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
let c1089ap_tr m =
  match c1089wc_tuple m with
    [c; s; u; v; a] ->
      [c; s; mk_binop `(-):real->real->real` u
               (mk_binop `(+):real->real->real` (mk_binop `(*):real->real->real` c `&2`)
                                                 (mk_binop `(*):real->real->real` s `&2`));
             mk_binop `(-):real->real->real` v
               (mk_binop `(+):real->real->real` (mk_binop `(*):real->real->real` (mk_comb(`(--):real->real`, s)) `&2`)
                                                 (mk_binop `(*):real->real->real` c `&2`)); a]
  | _ -> failwith "c1089ap_tr";;

(* Lean: impossible *)
let C1089AP_IMPOSSIBLE = prove
 (c1089wc_stmt [] [c1089ap_le `&2` (c1089wc_lcy 4096); c1089ap_le `&2` (c1089wc_lcy 16384);
                   c1089ap_le `&2` (c1089wc_lcx 32768)] `false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1089WC_BASE_TAC [512; 1024; 2048; 16384; 32768; 48] THEN
  MAP_EVERY (fun (i, p) -> ASSUME_TAC (MP (SPEC_ALL (c1089od_seed i p)) (c1089wc_hh ())))
    [2, (`&1543 / &500`, `&3`); 2, (`&3`, `&1543 / &500`)] THEN
  C1089WC_USE_TAC C1089AP_V C1089WC_NORTHEAST_INWARD THEN
  C1089WC_USE_TAC C1089AP_V C1089AP_SOUTHEAST_PAIR THEN
  C1089WC_USE_TAC C1089AP_V C1089AP_NORTHWEST_PAIR THEN
  C1089WC_USE_TAC C1089AP_V C1089WC_BOTTOM THEN
  FIRST_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) `&14 / &5`)) (concl th)
    then MP_TAC (SPEC `&239 / &100` th) THEN CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
         REWRITE_TAC[] THEN DISCH_TAC
    else NO_TAC) THEN
  C1089SE_AT_TAC C1089WC_LEFT_HIGH `&239 / &100` THEN
  (* rightPair, topF7 *)
  C1089AP_HAVE_TAC (mk_neg (c1089ap_own 16384 `&3` `&87 / &50`)) (DISCH_TAC THEN C1089WC_CLASH_TAC) THEN
  C1089WC_USE_TAC C1089AP_V C1089DD_RIGHT_HIGH_PAIR THEN
  C1089AP_HAVE_TAC (mk_neg (c1089ap_own 32768 `&8 / &5` `&3`)) (DISCH_TAC THEN C1089WC_CLASH_TAC) THEN
  C1089WC_USE_TAC C1089AP_V C1089DD_TOP_F7 THEN
  (* rHalf, tHalf *)
  C1089AP_HAVE_TAC (c1089ap_own 16384 `&3` `&5 / &2`)
    (C1089AP_APPLY_TAC (SPECL (c1089wc_tuple 16384) CWC_RIGHT_HIGH)) THEN
  ASSUME_TAC (MATCH_MP LCONT_PULLSW (c1089ap_box 32768)) THEN
  C1089AP_HAVE_TAC (c1089ap_own 32768 `&5 / &2` `&3`)
    (C1089AP_APPLY_TAC (c1089wc_inst CWC_RIGHT_HIGH (c1089wc_sw (c1089wc_tuple 32768)))) THEN
  (* rOrigin, tOrigin *)
  ASSUME_TAC (MATCH_MP LCONT_PULLSW (c1089ap_box 16384)) THEN
  ASSUME_TAC (MATCH_MP LCONT_PULLSW (c1089ap_box 48)) THEN
  C1089AP_HAVE_TAC (c1089ap_own 16384 `&3` `&2`)
    (C1089AP_APPLY_TAC (c1089wc_inst C1089AP_TOP_ORIGIN
       (c1089wc_sw (c1089wc_tuple 16384) @ c1089wc_sw (c1089wc_tuple 48)))) THEN
  C1089AP_HAVE_TAC (c1089ap_own 32768 `&2` `&3`)
    (C1089AP_APPLY_TAC (SPECL (c1089wc_tuple 32768 @ c1089wc_tuple 48) C1089AP_TOP_ORIGIN)) THEN
  (* center, halfY, halfX *)
  MAP_EVERY (fun (m, n) -> ASSUME_TAC (c1089ap_ldisj m n)) [1024, 16384; 1024, 32768] THEN
  C1089AP_HAVE_TAC (c1089ap_own 1024 `&2` `&2`)
    (C1089AP_APPLY_TAC (SPECL (c1089wc_tuple 1024 @ c1089wc_tuple 16384 @ c1089wc_tuple 32768)
                              CWC_POINT)) THEN
  C1089AP_HAVE_TAC (c1089ap_own 1024 `&2` `&5 / &2`)
    (C1089AP_APPLY_TAC (SPECL (c1089wc_tuple 1024) C981CP_POINT)) THEN
  C1089AP_HAVE_TAC (c1089ap_own 1024 `&5 / &2` `&2`)
    (C1089AP_APPLY_TAC (c1089wc_inst C981CP_POINT (c1089wc_sw (c1089wc_tuple 1024)))) THEN
  (* innerX, innerY *)
  C1089AP_HAVE_TAC (c1089ap_own 1024 `&239 / &100` `&2`)
    (MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&2`; `&5 / &2`] THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV) THEN
  C1089AP_HAVE_TAC (c1089ap_own 1024 `&2` `&239 / &100`)
    (MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&2`; `&5 / &2`] THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV) THEN
  (* the MMMM ending on N, E, W *)
  let n = c1089ap_tr 1024 and e = c1089ap_tr 512 and w = c1089ap_tr 2048 in
  MATCH_MP_TAC (SPECL (n @ e @ w) C1092MME_IMPOSSIBLE) THEN
  REWRITE_TAC[c1092mme_data; ldisj; C1089AP_TR_INSIDE] THEN
  CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         DISCH_TAC THEN C1089WC_CLASH_TAC;
         REPEAT GEN_TAC THEN STRIP_TAC THEN C1089WC_CLASH_TAC;
         RASM_ARITH_TAC]);;
