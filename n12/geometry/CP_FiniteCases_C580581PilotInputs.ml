(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C580581PilotInputs.lean            *)
(* (N12Compact.FiniteCases.C580581PilotInputs).  Actual-family inputs for    *)
(* the bounded three-owner proposal, for both original bottom masks.         *)
(* Statements indexed by v : Fin 2 are OCaml arrays (family v = C580E_FAM,   *)
(* bottomMask v = C580E_BOTTOM).  Private seed_point / foreign / aux_inside  *)
(* are fc580ce_seed / fc580ce_excl / fc580ce_auxpt (C580581CentralEntrance   *)
(* port); C580581Entrance.inside = fc580ce_claim; compulsory =               *)
(* FC580P_COMPULSORY.  C981CompletionWallAdvance.point = C981WA_POINT,       *)
(* C981CompletionCrosspoint.point = C981CP_POINT, horizontal_segment =       *)
(* OO_HORIZONTAL_SEGMENT; pullX / pullY / pullSwap tuples are those of       *)
(* LCONT_PULLX / Y / SW.  Tag FC580PI_.                                      *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C580581CentralEntrance.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;


(* a lemma at the tuple of a (pulled) box; antecedent from the facts *)
let fc580pi_apply v lemma box m ths =
  let tuple = snd (strip_comb (concl box)) in
  let th = CONV_RULE (REWRITE_CONV[LINSIDE_PULLSW; LINSIDE_PULLY; LINSIDE_PULLX] THENC
                      ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) (SPECL tuple lemma) in
  let np = fc580ce_np v in
  let unit = MP (SPECL (FC580CE_VARS @ [mk_small_numeral m]) OO_UNIT) np in
  let side = MP (SPECL FC580CE_VARS OO_SIDE) np in
  let close = FIRST [FIRST (map ACCEPT_TAC (box :: ths));
                     MP_TAC unit THEN REAL_ARITH_TAC; MP_TAC side THEN REAL_ARITH_TAC] in
  MP th (TAC_PROOF(([], lhand (concl th)), REPEAT CONJ_TAC THEN close));;

let fc580pi_box_v v m = MP (SPECL (FC580CE_VARS @ [mk_small_numeral m]) OO_BOX) (fc580ce_np v);;

(* Lean: bottom_far *)
let FC580PI_BOTTOM_FAR = Array.init 2 (fun v ->
  let bm = C580E_BOTTOM.(v) in
  let markerB = fc580ce_seed v bm (`&2`, `&457 / &500`) in
  let highB = fc580ce_auxpt bm 6 (fc580ce_comp v 3) in
  let lowSW = fc580ce_seed v 1 (`&87 / &50`, `&1`) in
  let seedSW = fc580ce_seed v 1 (`&187 / &100`, `&19 / &25`) in
  let markerSE = fc580ce_seed v 512 (`&47 / &20`, `&33 / &20`) in
  let th = fc580pi_apply v C981WA_POINT (MATCH_MP LCONT_PULLSW (fc580pi_box_v v bm)) bm
    [markerB; highB; fc580ce_excl v bm 1 lowSW; fc580ce_excl v bm 1 seedSW;
     fc580ce_excl v bm 512 markerSE] in
  fc580ce_prove v (fc580ce_own bm `&14 / &5` `&1`) th);;

(* Lean: southeast_east *)
let FC580PI_SOUTHEAST_EAST = Array.init 2 (fun v ->
  let bm = C580E_BOTTOM.(v) in
  let markerA = fc580ce_seed v 512 (`&47 / &20`, `&33 / &20`) in
  let inwardA = fc580ce_auxpt 512 4 (fc580ce_comp v 5) in
  let elbowA = fc580ce_claim v 6 in
  let markerSW = fc580ce_seed v 2304 (`&33 / &20`, `&33 / &20`) in
  let markerNE = fc580ce_seed v 1024 (`&47 / &20`, `&47 / &20`) in
  let lowB = fc580ce_claim v 4 in
  let middleB = fc580ce_auxpt bm 6 (fc580ce_comp v 3) in
  let highB = fc580ce_hseg bm `&113 / &50` `&14 / &5` `&1` `&5 / &2` lowB
                (fc580ce_inst v FC580PI_BOTTOM_FAR.(v)) in
  let th = fc580pi_apply v C981CP_POINT
    (MATCH_MP LCONT_PULLSW (MATCH_MP LCONT_PULLY (fc580pi_box_v v 512))) 512
    [elbowA; inwardA; markerA; fc580ce_excl v 512 2304 markerSW; fc580ce_excl v 512 1024 markerNE;
     fc580ce_excl v 512 bm middleB; fc580ce_excl v 512 bm highB] in
  fc580ce_prove v (fc580ce_own 512 `&5 / &2` `&2`) th);;

(* Lean: southeast_missing_center *)
let FC580PI_SOUTHEAST_MISSING_CENTER = Array.init 2 (fun v ->
  fc580ce_prove v (mk_neg (fc580ce_own 512 `&2` `&2`))
    (fc580ce_excl v 512 2304 (fc580ce_inst v FC580CE_MERGED_CENTER.(v))));;

(* Lean: right_far *)
let FC580PI_RIGHT_FAR = Array.init 2 (fun v ->
  let markerR = fc580ce_seed v 16384 (`&1543 / &500`, `&2`) in
  let highR = fc580ce_claim v 7 in
  let lowO = fc580ce_seed v 8 (`&3`, `&87 / &50`) in
  let seedO = fc580ce_seed v 8 (`&81 / &25`, `&187 / &100`) in
  let markerN = fc580ce_seed v 1024 (`&47 / &20`, `&47 / &20`) in
  let th = fc580pi_apply v C981WA_POINT (MATCH_MP LCONT_PULLX (fc580pi_box_v v 16384)) 16384
    [markerR; highR; fc580ce_excl v 16384 8 lowO; fc580ce_excl v 16384 8 seedO;
     fc580ce_excl v 16384 1024 markerN] in
  fc580ce_prove v (fc580ce_own 16384 `&3` `&14 / &5`) th);;
