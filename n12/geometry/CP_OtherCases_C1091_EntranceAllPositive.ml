(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1091/EntranceAllPositive.lean      *)
(* (namespace N12Compact.Completion.OtherCases.C1091.EntranceAllPositive).   *)
(* C1091's closed (+++) wall sector: the actual Q6, Q5, Q7 enter the shared  *)
(* continuous MMMM ending.  Conventions of EntranceWalls.ml (owners p i =    *)
(* owner at the literal mask EL i c1091od_masks; 2 -> 48, 5 -> 512,          *)
(* 6 -> 1024, 7 -> 2048, 10 -> 16384, 11 -> 32768).  clockwise_pair /        *)
(* top_origin are the C1089 abbrevs C1089SE_CLOCKWISE_PAIR /                 *)
(* C1089AP_TOP_ORIGIN; EntranceDomains.* = C1091ED_*; CentralWallCenter.     *)
(* right_high / point = CWC_RIGHT_HIGH / CWC_POINT; C981CompletionCrosspoint.*)
(* point = C981CP_POINT; C1092MMMMEnding = c1092mme_data /                   *)
(* C1092MME_IMPOSSIBLE; q.translated 2 2 as in C1089 AllPositive.ml.         *)
(* (Lean header: "Source only".)  Tag C1091EAP_.                             *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1091_EntranceWalls.ml";;
needs "n12/geometry/CP_OtherCases_C1089_AllPositive.ml";;

(* Lean: clockwise_pair (abbrev of C1089.SectorEntrances.clockwise_pair) *)
let C1091EAP_CLOCKWISE_PAIR = C1089SE_CLOCKWISE_PAIR;;

let c1091eap_cover th = MP (SPEC_ALL th) (c1091ew_hh ());;
let C1091EAP_HAVE0_TAC tm tac = SUBGOAL_THEN tm ASSUME_TAC THENL [tac; ALL_TAC];;
let C1091EAP_CLOSE_TAC =
  FIRST [FIRST_ASSUM ACCEPT_TAC; C1091EW_CLASH_TAC;
         FIRST_ASSUM(fun th -> if is_neg (concl th) then
           FIRST_ASSUM(fun th2 -> CONTR_TAC (MP (NOT_ELIM th) th2)) else NO_TAC)];;
let C1091EAP_COVER_TAC th =
  MP_TAC (c1091eap_cover th) THEN STRIP_TAC THEN C1091EAP_CLOSE_TAC;;
let C1091EAP_AT_TAC th t = C1091EW_CHORDS_TAC th [t];;

let C1091EAP_V = C1091EW_V;;
let c1091eap_own = c1091ew_own;;
let c1091eap_le = c1091ew_le;;
let c1091eap_box m = MP (SPECL (C1091EAP_V @ [mk_small_numeral m]) OO_BOX) (ASSUME C1091EW_NP);;
let c1091eap_ldisj m n = MP (SPECL C1091EAP_V (oo_apart `c1091od_family` m n)) (c1091ew_hh ());;

let C1091EAP_SIDE_TAC =
  FIRST [(fun (asl, w as g) -> if is_comb w && fst (strip_comb w) = `ldisj` then
            (REWRITE_TAC[ldisj; LINSIDE_PULLSW; LINSIDE_PULLX; LINSIDE_PULLY] THEN
             CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
             REPEAT GEN_TAC THEN STRIP_TAC THEN C1091EW_CLASH_TAC) g
          else NO_TAC g);
         C1091EW_SIDE_TAC];;
let C1091EAP_APPLY_TAC th =
  MP_TAC th THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN C1091EAP_SIDE_TAC; CONV_TAC TAUT];;
let C1091EAP_HAVE_TAC = C1091EAP_HAVE0_TAC;;

(* Lean: southeast_pair *)
let C1091EAP_SOUTHEAST_PAIR = prove
 (c1091ew_stmt [] [c1091eap_le `&2` (c1091ew_lcy 16384); c1091eap_le `&2` (c1091ew_lcx 32768)]
    (mk_conj(c1091eap_own 512 `&3` `&87 / &50`, c1091eap_own 512 `&3` `&8 / &5`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1091EW_BASE_TAC [512] THEN
  C1091EW_USE_TAC C1091EAP_V C1091EW_NORTHEAST_INWARD THEN
  MP_TAC (MP (SPEC_ALL C1091ED_BOTTOM_BAR) (c1091ew_hh ())) THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) `&14 / &5`)) (concl th)
    then MAP_EVERY (fun x -> MP_TAC (SPEC x th) THEN CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
                             REWRITE_TAC[] THEN DISCH_TAC) [`&113 / &50`; `&239 / &100`]
    else NO_TAC) THEN
  C1091EAP_HAVE_TAC (c1091eap_own 512 `&3` `&8 / &5`)
    (C1091EAP_COVER_TAC C1091ED_SOUTHEAST_G) THEN
  ASSUME_TAC (c1091eap_cover C1091ED_SOUTHEAST_F) THEN
  ASM_REWRITE_TAC[] THEN
  C1091EAP_APPLY_TAC (c1089wc_inst C1091EAP_CLOCKWISE_PAIR (c1089wc_sw (c1089wc_py (c1091ew_tuple 512)))));;

(* Lean: northwest_pair *)
let C1091EAP_NORTHWEST_PAIR = prove
 (c1091ew_stmt [] [c1091eap_le `&2` (c1091ew_lcy 4096); c1091eap_le `&2` (c1091ew_lcy 16384);
                   c1091eap_le `&2` (c1091ew_lcx 32768)]
    (mk_conj(c1091eap_own 2048 `&8 / &5` `&3`, c1091eap_own 2048 `&87 / &50` `&3`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1091EW_BASE_TAC [2048] THEN
  C1091EW_USE_TAC C1091EAP_V C1091EW_NORTHEAST_INWARD THEN
  C1091EAP_AT_TAC C1091EW_LEFT_HIGH `&113 / &50` THEN
  C1091EAP_AT_TAC C1091EW_LEFT_HIGH `&239 / &100` THEN
  C1091EAP_HAVE_TAC (c1091eap_own 2048 `&8 / &5` `&3`)
    (C1091EAP_COVER_TAC C1091ED_NORTHWEST_F) THEN
  ASSUME_TAC (c1091eap_cover C1091ED_NORTHWEST_G) THEN
  ASM_REWRITE_TAC[] THEN
  C1091EAP_APPLY_TAC (c1089wc_inst C1091EAP_CLOCKWISE_PAIR (c1089wc_px (c1091ew_tuple 2048))));;

(* Lean: top_origin (abbrev of C1089.AllPositive.top_origin) *)
let C1091EAP_TOP_ORIGIN = C1089AP_TOP_ORIGIN;;

(* q.translated 2 2 *)
let C1091EAP_TR_INSIDE = C1089AP_TR_INSIDE;;
let c1091eap_tr m =
  match c1091ew_tuple m with
    [c; s; u; v; a] ->
      [c; s; mk_binop `(-):real->real->real` u
               (mk_binop `(+):real->real->real` (mk_binop `(*):real->real->real` c `&2`)
                                                 (mk_binop `(*):real->real->real` s `&2`));
             mk_binop `(-):real->real->real` v
               (mk_binop `(+):real->real->real` (mk_binop `(*):real->real->real` (mk_comb(`(--):real->real`, s)) `&2`)
                                                 (mk_binop `(*):real->real->real` c `&2`)); a]
  | _ -> failwith "c1091eap_tr";;

(* Lean: impossible *)
let C1091EAP_IMPOSSIBLE = prove
 (c1091ew_stmt [] [c1091eap_le `&2` (c1091ew_lcy 4096); c1091eap_le `&2` (c1091ew_lcy 16384);
                   c1091eap_le `&2` (c1091ew_lcx 32768)] `false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1091EW_BASE_TAC [512; 1024; 2048; 16384; 32768; 48] THEN
  MAP_EVERY (fun (i, p) -> ASSUME_TAC (MP (SPEC_ALL (c1091od_seed i p)) (c1091ew_hh ())))
    [2, (`&1543 / &500`, `&3`); 2, (`&3`, `&1543 / &500`)] THEN
  C1091EW_USE_TAC C1091EAP_V C1091EW_NORTHEAST_INWARD THEN
  C1091EW_USE_TAC C1091EAP_V C1091EAP_SOUTHEAST_PAIR THEN
  C1091EW_USE_TAC C1091EAP_V C1091EAP_NORTHWEST_PAIR THEN
  MP_TAC (MP (SPEC_ALL C1091ED_BOTTOM_BAR) (c1091ew_hh ())) THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) `&14 / &5`)) (concl th)
    then MP_TAC (SPEC `&239 / &100` th) THEN CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
         REWRITE_TAC[] THEN DISCH_TAC
    else NO_TAC) THEN
  C1091EAP_AT_TAC C1091EW_LEFT_HIGH `&239 / &100` THEN
  (* rightPair, topF7 *)
  C1091EAP_HAVE_TAC (mk_neg (c1091eap_own 16384 `&3` `&87 / &50`)) (DISCH_TAC THEN C1091EW_CLASH_TAC) THEN
  C1091EW_USE_TAC C1091EAP_V (REWRITE_RULE[GSYM CONJ_ASSOC] C1091ED_RIGHT_HIGH_PAIR) THEN
  C1091EAP_HAVE_TAC (mk_neg (c1091eap_own 32768 `&8 / &5` `&3`)) (DISCH_TAC THEN C1091EW_CLASH_TAC) THEN
  C1091EW_USE_TAC C1091EAP_V (REWRITE_RULE[GSYM CONJ_ASSOC] C1091ED_TOP_F7) THEN
  (* rHalf, tHalf *)
  C1091EAP_HAVE_TAC (c1091eap_own 16384 `&3` `&5 / &2`)
    (C1091EAP_APPLY_TAC (SPECL (c1091ew_tuple 16384) CWC_RIGHT_HIGH)) THEN
  ASSUME_TAC (MATCH_MP LCONT_PULLSW (c1091eap_box 32768)) THEN
  C1091EAP_HAVE_TAC (c1091eap_own 32768 `&5 / &2` `&3`)
    (C1091EAP_APPLY_TAC (c1089wc_inst CWC_RIGHT_HIGH (c1089wc_sw (c1091ew_tuple 32768)))) THEN
  (* rOrigin, tOrigin *)
  ASSUME_TAC (MATCH_MP LCONT_PULLSW (c1091eap_box 16384)) THEN
  ASSUME_TAC (MATCH_MP LCONT_PULLSW (c1091eap_box 48)) THEN
  C1091EAP_HAVE_TAC (c1091eap_own 16384 `&3` `&2`)
    (C1091EAP_APPLY_TAC (c1089wc_inst C1091EAP_TOP_ORIGIN
       (c1089wc_sw (c1091ew_tuple 16384) @ c1089wc_sw (c1091ew_tuple 48)))) THEN
  C1091EAP_HAVE_TAC (c1091eap_own 32768 `&2` `&3`)
    (C1091EAP_APPLY_TAC (SPECL (c1091ew_tuple 32768 @ c1091ew_tuple 48) C1091EAP_TOP_ORIGIN)) THEN
  (* center, halfY, halfX *)
  MAP_EVERY (fun (m, n) -> ASSUME_TAC (c1091eap_ldisj m n)) [1024, 16384; 1024, 32768] THEN
  C1091EAP_HAVE_TAC (c1091eap_own 1024 `&2` `&2`)
    (C1091EAP_APPLY_TAC (SPECL (c1091ew_tuple 1024 @ c1091ew_tuple 16384 @ c1091ew_tuple 32768)
                              CWC_POINT)) THEN
  C1091EAP_HAVE_TAC (c1091eap_own 1024 `&2` `&5 / &2`)
    (C1091EAP_APPLY_TAC (SPECL (c1091ew_tuple 1024) C981CP_POINT)) THEN
  C1091EAP_HAVE_TAC (c1091eap_own 1024 `&5 / &2` `&2`)
    (C1091EAP_APPLY_TAC (c1089wc_inst C981CP_POINT (c1089wc_sw (c1091ew_tuple 1024)))) THEN
  (* innerX, innerY *)
  C1091EAP_HAVE_TAC (c1091eap_own 1024 `&239 / &100` `&2`)
    (MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&2`; `&5 / &2`] THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV) THEN
  C1091EAP_HAVE_TAC (c1091eap_own 1024 `&2` `&239 / &100`)
    (MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&2`; `&5 / &2`] THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV) THEN
  (* the MMMM ending on N, E, W *)
  let n = c1091eap_tr 1024 and e = c1091eap_tr 512 and w = c1091eap_tr 2048 in
  MATCH_MP_TAC (SPECL (n @ e @ w) C1092MME_IMPOSSIBLE) THEN
  REWRITE_TAC[c1092mme_data; ldisj; C1091EAP_TR_INSIDE] THEN
  CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         DISCH_TAC THEN C1091EW_CLASH_TAC;
         REPEAT GEN_TAC THEN STRIP_TAC THEN C1091EW_CLASH_TAC;
         RASM_ARITH_TAC]);;
