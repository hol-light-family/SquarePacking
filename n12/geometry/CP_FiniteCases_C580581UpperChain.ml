(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C580581UpperChain.lean             *)
(* (N12Compact.FiniteCases.C580581UpperChain).  Additional actual-owner      *)
(* consequences for the two original merged-left families; both paired      *)
(* upper corners are used as their full genuine squares.  Statements indexed *)
(* by v : Fin 2 are OCaml arrays of the two theorems (family v = C580E_FAM,  *)
(* shape |- !c1 c2 a b l. NPACK .. /\ IMAGE binarysum (FFP ..) = family v    *)
(* ==> linside (owner m) x y).  Private seed_point / foreign are             *)
(* fc580ce_seed / fc580ce_excl; C580581Entrance.inside = fc580ce_claim;      *)
(* compulsory = fc580ce_comp; auxiliary_exact = fc580ce_auxpt;               *)
(* C981CompletionWallAdvance.point = C981WA_POINT; horizontal_segment of     *)
(* pullSwap = OO_VERTICAL_SEGMENT (fc580ce_vseg); WallProfile.boundary_origin*)
(* = OCWPBO_BOUNDARY_ORIGIN at the pulled tuples (LCONT_PULLX / Y / SW);     *)
(* TopOnlyExtension.point_original = OCTOE_POINT_ORIGINAL;                   *)
(* C580581CentralEntrance.northeast_top / merged_inward = FC580CE_*;         *)
(* C580581PilotInputs.southeast_east = FC580PI_SOUTHEAST_EAST.  Tag FC580UC_.*)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C580581PilotInputs.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_BoundaryOrigin.ml";;
needs "n12/geometry/CP_OtherCases_TopOnlyExtension.ml";;

(* apply lemma at the tuple of the (pulled) box, normalising the pulls and   *)
(* ldisj; the premises come from the facts, the owner units / side, literal  *)
(* arithmetic, the boxes (wall facts) and the owners' disjointness facts.    *)
let fc580uc_tuple box = snd (strip_comb (concl box));;

let fc580uc_apply v lemma tuple ms facts aparts =
  let np = fc580ce_np v in
  let units = map (fun m -> MP (SPECL (FC580CE_VARS @ [mk_small_numeral m]) OO_UNIT) np) ms in
  let boxes = map (fun m -> REWRITE_RULE[lcont] (fc580pi_box_v v m)) ms in
  let side = MP (SPECL FC580CE_VARS OO_SIDE) np in
  let conv = REWRITE_CONV[ldisj; LINSIDE_PULLSW; LINSIDE_PULLY; LINSIDE_PULLX] THENC
             ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV in
  let th = CONV_RULE (LAND_CONV conv THENC RAND_CONV conv) (SPECL tuple lemma) in
  let dis = map (REWRITE_RULE[ldisj]) aparts in
  let wall = REPEAT GEN_TAC THEN
    DISCH_THEN(fun h -> MAP_EVERY (fun b -> try MP_TAC (MATCH_MP b h) with Failure _ -> ALL_TAC)
                          boxes) THEN REAL_ARITH_TAC in
  let close = FIRST [FIRST (map ACCEPT_TAC facts); REFL_TAC;
                     MAP_EVERY MP_TAC units THEN REAL_ARITH_TAC;
                     MP_TAC side THEN REAL_ARITH_TAC;
                     REPEAT GEN_TAC THEN REWRITE_TAC dis THEN NO_TAC;
                     wall] in
  MP th (TAC_PROOF(([], lhand (concl th)), REPEAT CONJ_TAC THEN close));;

(* Lean: seed_point, foreign (private): fc580ce_seed, fc580ce_excl *)

(* Lean: left_far *)
let FC580UC_LEFT_FAR = Array.init 2 (fun v ->
  let markerL = fc580ce_seed v 4096 (`&457 / &500`, `&2`) in
  let highL = fc580ce_claim v 5 in
  let lowK = fc580ce_seed v 2 (`&1`, `&87 / &50`) in
  let seedK = fc580ce_seed v 2 (`&19 / &25`, `&187 / &100`) in
  let markerM = fc580ce_seed v 2304 (`&33 / &20`, `&47 / &20`) in
  let th = fc580pi_apply v C981WA_POINT (fc580pi_box_v v 4096) 4096
    [markerL; highL; fc580ce_excl v 4096 2 lowK; fc580ce_excl v 4096 2 seedK;
     fc580ce_excl v 4096 2304 markerM] in
  fc580ce_prove v (fc580ce_own 4096 `&1` `&14 / &5`) th);;

(* Lean: top_origin *)
let FC580UC_TOP_ORIGIN = Array.init 2 (fun v ->
  let top = fc580ce_comp v 7 in
  let marker = fc580ce_seed v 32768 (`&2`, `&1543 / &500`) in
  let inner = fc580ce_auxpt 32768 3 top in
  let cornerMarker = fc580ce_seed v 192 (`&1`, `&1543 / &500`) in
  let cornerPoint = fc580ce_seed v 192 (`&1`, `&3`) in
  let wallHigh = fc580ce_claim v 5 in
  let wallMiddle = fc580ce_vseg 4096 `&1` `&12 / &5` `&14 / &5` `&5 / &2` wallHigh
                     (fc580ce_inst v FC580UC_LEFT_FAR.(v)) in
  let missing = fc580ce_excl v 192 4096 wallMiddle in
  let boxB = MATCH_MP LCONT_PULLY (fc580pi_box_v v 32768)
  and boxK = MATCH_MP LCONT_PULLY (fc580pi_box_v v 192) in
  let th = fc580uc_apply v
    OCWPBO_BOUNDARY_ORIGIN
    (fc580uc_tuple boxB @ fc580uc_tuple boxK @ [`&457 / &500`; `&8 / &5`]) [32768; 192]
    [marker; inner; cornerMarker; cornerPoint; missing] [fc580ce_apart v 192 32768] in
  fc580ce_prove v (fc580ce_own 32768 `&2` `&3`) th);;

(* Lean: northeast_extension *)
let FC580UC_NORTHEAST_EXTENSION = Array.init 2 (fun v ->
  let marker = fc580ce_seed v 1024 (`&47 / &20`, `&47 / &20`) in
  let top = CONJUNCT1 (fc580ce_inst v FC580CE_NORTHEAST_TOP.(v)) in
  let merged = fc580ce_inst v FC580CE_MERGED_INWARD.(v) in
  let origin = fc580ce_inst v FC580UC_TOP_ORIGIN.(v) in
  let east = fc580ce_inst v FC580PI_SOUTHEAST_EAST.(v) in
  let th = fc580ce_discharge v [1024] (SPECL (fc580ce_tuple 1024) OCTOE_POINT_ORIGINAL)
    [marker; top; fc580ce_excl v 1024 2304 merged; fc580ce_excl v 1024 32768 origin;
     fc580ce_excl v 1024 512 east] in
  fc580ce_prove v (fc580ce_own 1024 `&5 / &2` `&3`) th);;

(* Lean: right_origin *)
let FC580UC_RIGHT_ORIGIN = Array.init 2 (fun v ->
  let pull box = MATCH_MP LCONT_PULLSW (MATCH_MP LCONT_PULLY (MATCH_MP LCONT_PULLX box)) in
  let boxB = pull (fc580pi_box_v v 16384) and boxK = pull (fc580pi_box_v v 48) in
  let marker = fc580ce_seed v 16384 (`&1543 / &500`, `&2`) in
  let inner = fc580ce_claim v 7 in
  let cornerMarker = fc580ce_seed v 48 (`&1543 / &500`, `&3`) in
  let cornerPoint = fc580ce_seed v 48 (`&3`, `&3`) in
  let missing = fc580ce_excl v 48 1024 (fc580ce_inst v FC580UC_NORTHEAST_EXTENSION.(v)) in
  let th = fc580uc_apply v OCWPBO_BOUNDARY_ORIGIN
    (fc580uc_tuple boxB @ fc580uc_tuple boxK @ [`&457 / &500`; `&8 / &5`]) [16384; 48]
    [marker; inner; cornerMarker; cornerPoint; missing] [fc580ce_apart v 48 16384] in
  fc580ce_prove v (fc580ce_own 16384 `&3` `&2`) th);;
