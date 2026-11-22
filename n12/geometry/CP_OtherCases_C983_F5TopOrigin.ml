(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/F5TopOrigin.lean.             *)
(* Universal actual top origin (2, 3) of owners p 11 (owner 32768) in the    *)
(* merged-F5 branch (5 IN actual p 7).  Conventions of                       *)
(* CP_OtherCases_C983_F5Filters.ml (owners p 3 -> 48, 5 -> 512, 6 -> 1024,   *)
(* 7 -> 2304, 9 -> 8192, 10 -> 16384, 11 -> 32768).  top_origin_of_f3 =      *)
(* C983FO_TOP_ORIGIN_OF_F3; C981CompletionTopReach.origin_alternative =      *)
(* C981TR_ORIGIN_ALTERNATIVE on (owners p 11).translated 2 3 (through        *)
(* OCOBP_INSIDE_TRANSLATED); CommonCases.CentralPair.impossible =            *)
(* CCCPAIR_IMPOSSIBLE; horizontal_segment = OO_HORIZONTAL_SEGMENT;           *)
(* bottom_bar = C983AB_BOTTOM_BAR.  Tag C983F5T_.                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F5Crosspoint.ml";;
needs "n12/geometry/CP_OtherCases_C983_InwardAlternative.ml";;
needs "n12/geometry/CP_CommonCases_CentralPair.ml";;
needs "n12/geometry/CP_C981_TopReach.ml";;

(* Lean: top_cover_check (private) *)
let C983F5T_TOP_COVER_CHECK = prove
 (`forall s. MEM s (EL 11 c983e_original_components) ==> 3 IN s \/ 7 IN s`, c983f5_check []);;

(* Lean: top_outward_check (private) *)
let C983F5T_TOP_OUTWARD_CHECK = prove
 (`forall s. MEM s (EL 11 c983e_original_components) ==> 7 IN s ==> 17 IN s`, c983f5_check []);;

(* Lean: northeast_rightward_check (private) *)
let C983F5T_NORTHEAST_RIGHTWARD_CHECK = prove
 (`forall s. MEM s c983f5_northeast_components ==> ~(7 IN s) ==> ~(17 IN s) ==> s = {9, 19}`,
  c983f5_check [c983f5_northeast_components]);;

(* Lean: right_lower_check (private) *)
let C983F5T_RIGHT_LOWER_CHECK = prove
 (`forall s. MEM s c983f5_right_components ==> ~(9 IN s) ==> ~(19 IN s) ==> s = {8, 18}`,
  c983f5_check [c983f5_right_components]);;

(* Lean: southeast_inward_check (private) *)
let C983F5T_SOUTHEAST_INWARD_CHECK = prove
 (`forall s. MEM s c983f5_southeast_components ==> ~(8 IN s) ==> ~(18 IN s) ==> ~(9 IN s) ==> s = {4, 16}`,
  c983f5_check [c983f5_southeast_components]);;

(* the tuple of (owner m).translated x y *)
let c983f5t_tr m x y =
  let t = SPECL (c983ab_own m @ [x; y; `p:real`; `q:real`]) OCOBP_INSIDE_TRANSLATED in
  let args = snd (strip_comb (lhs (concl t))) in
  [el 0 args; el 1 args; el 2 args; el 3 args; el 4 args];;

let C983F5T_TR_CONV = REWRITE_CONV[OCOBP_INSIDE_TRANSLATED] THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV;;

(* membership j IN actual i from an exact equation actual i = {..} *)
let c983f5t_memo ex j i =
  EQT_ELIM ((REWRITE_CONV[ex; IN_INSERT; NOT_IN_EMPTY] THENC NUM_REDUCE_CONV) (c983f4f_mem j i));;

(* Lean: f5_top_origin *)
let C983F5T_F5_TOP_ORIGIN =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let f5 = c983f5_f5 () in
  let leftward = c983f4f_mem 3 11 in
  let goal = c983ab_in 32768 `&2` `&3` in
  let th1 = c983f5_use C983FO_TOP_ORIGIN_OF_F3 [ASSUME leftward] in
  let th2 =
    let orig11 = c983f4f_orig 11 in
    let topF7 = c983f5_res_left (MATCH_MP C983F5T_TOP_COVER_CHECK orig11) (ASSUME (mk_neg leftward)) in
    let topG7 = MP (MATCH_MP C983F5T_TOP_OUTWARD_CHECK orig11) topF7 in
    let nExact = c983f5_mps (MATCH_MP C983F5T_NORTHEAST_RIGHTWARD_CHECK (c983f5_northeast_components_th ()))
      [c983f4f_absent 11 6 topF7; c983f4f_absent 11 6 topG7] in
    let nF9 = c983f5t_memo nExact 9 6 and nG9 = c983f5t_memo nExact 19 6 in
    let rExact = c983f5_mps (MATCH_MP C983F5T_RIGHT_LOWER_CHECK (c983f5_right_components_th ()))
      [c983f4f_absent 6 10 nF9; c983f4f_absent 6 10 nG9] in
    let rF8 = c983f5t_memo rExact 8 10 and rG8 = c983f5t_memo rExact 18 10 in
    let eExact = c983f5_mps (MATCH_MP C983F5T_SOUTHEAST_INWARD_CHECK
                               (c983f5_use C983F5_F5_SOUTHEAST_COMPONENTS [f5]))
      [c983f4f_absent 10 5 rF8; c983f4f_absent 10 5 rG8; c983f4f_absent 6 5 nF9] in
    let eF4 = c983f5t_memo eExact 4 5 in
    let missingOrigin = ASSUME (mk_neg goal) in
    let topMarker = seed 11 `&2` `&1543 / &500` in
    let topAnchor = c983f4f_point topF7 in
    let spec = SPECL (c983f5t_tr 32768 `&2` `&3`) C981TR_ORIGIN_ALTERNATIVE in
    let wall = c983ia_wall 32768 (c983ia_ant spec c983ia_is_forall) in
    let topHigh = c983sa_apply C983F5T_TR_CONV spec
      [unit 32768; pos; side; wall; topMarker; topAnchor; missingOrigin] in
    let topLow = c983f4f_point topG7 in
    let lo = `&113 / &50 <= z` and hi = `z <= &14 / &5` in
    let barz = MP (SPECL (c983ab_own 32768 @ [`&113 / &50`; `&14 / &5`; `&3`; `z:real`]) OO_HORIZONTAL_SEGMENT)
      (end_itlist CONJ [topLow; topHigh; EQT_ELIM (REAL_RAT_REDUCE_CONV `&113 / &50 < &14 / &5`);
                        ASSUME lo; ASSUME hi]) in
    let topBar = GEN `z:real` (DISCH lo (DISCH hi (excl 1024 32768 barz))) in
    let eMarker = seed 5 `&47 / &20` `&33 / &20` in
    let eInward = c983f4f_point eF4 in
    let eElbow = c983f4f_point (c983f5_use C983F5_F5_SOUTHEAST_G6 [f5]) in
    let noSW = excl 512 2304 (seed 7 `&33 / &20` `&33 / &20`) in
    let bar = MP (SPECL C983E_VARS C983AB_BOTTOM_BAR) (c983f4f_hh ()) in
    let bl = let th = SPEC `&12 / &5` bar in
      MP (MP th (EQT_ELIM (REAL_RAT_REDUCE_CONV (lhand (concl th)))))
         (EQT_ELIM (REAL_RAT_REDUCE_CONV (lhand (rand (concl th))))) in
    let noLow = excl 512 8192 bl in
    let nMarker = seed 6 `&47 / &20` `&47 / &20` in
    let nOuter = c983f4f_point nF9 and nUpper = c983f4f_point nG9 in
    let noRight = excl 1024 16384 (seed 10 `&1543 / &500` `&2`) in
    let noCorner = excl 1024 48 (seed 3 `&3` `&3`) in
    let noCornerMarker = excl 1024 48 (seed 3 `&1543 / &500` `&3`) in
    let dj = MP (SPECL C983E_VARS (oo_apart C983E_F 512 1024)) (c983f4f_hh ()) in
    let cspec = SPECL (c983ab_own 512 @ c983ab_own 1024) CCCPAIR_IMPOSSIBLE in
    let dtm = find is_disj (conjuncts (lhand (concl cspec))) in
    let alt = DISJ2 (lhand dtm) (CONJ nOuter nUpper) in
    let f = c983sa_apply C983FO_CONV cspec
      [unit 512; unit 1024; side; eMarker; eInward; eElbow; noSW; noLow; nMarker; alt;
       noRight; noCorner; noCornerMarker; topBar; dj] in
    CCONTR goal f in
  let th = DISJ_CASES (SPEC leftward EXCLUDED_MIDDLE) th1 th2 in
  c983f4f_close (c983sa_stmt [c983f4f_mem 5 7] goal) th;;
