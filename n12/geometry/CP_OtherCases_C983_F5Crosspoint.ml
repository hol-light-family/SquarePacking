(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/F5Crosspoint.lean.            *)
(* The actual southeast horizontal crosspoint (5/2, 2) of owners p 5 (owner  *)
(* 512) throughout merged-F5 (5 IN actual p 7).  Conventions of             *)
(* CP_OtherCases_C983_F5Filters.ml / SharpApplications.ml (actual p i =     *)
(* c983e_actual c1 c2 a b l i, owners p i = owner at EL i c983ri_owner_code: *)
(* 5 -> 512, 6 -> 1024, 7 -> 2304, 9 -> 8192).  C981CompletionCrosspoint.   *)
(* point = C981CP_POINT applied to pullSwap (pullY (owners p 5)) through     *)
(* LINSIDE_PULLSW / LINSIDE_PULLY; F4PointTransfers.horizontal_original =    *)
(* OCF4PT_HORIZONTAL_ORIGINAL; bottom_bar = C983AB_BOTTOM_BAR.  Tag C983F5C_.*)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F5Filters.ml";;
needs "n12/geometry/CP_OtherCases_F4PointTransfers.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;

(* Lean: southeast_no_f4_check (private) *)
let C983F5C_SOUTHEAST_NO_F4_CHECK = prove
 (`forall s. MEM s c983f5_southeast_components ==> ~(4 IN s) ==> 8 IN s`,
  c983f5_check [c983f5_southeast_components]);;

let C983F5C_SWY_CONV = REWRITE_CONV[LINSIDE_PULLSW; LINSIDE_PULLY; REAL_NEG_MUL2] THENC
                       ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV;;

(* the tuple of pullSwap (pullY (owner m)) *)
let c983f5c_swy m =
  match c983fo_pull LINSIDE_PULLY m with
    [c; s; u; v; a] -> [s; c; u; mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, v)) a; a]
  | _ -> failwith "c983f5c_swy";;

(* Lean: f5_southeast_crosspoint *)
let C983F5C_F5_SOUTHEAST_CROSSPOINT =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let f5 = c983f5_f5 () in
  let marker = seed 5 `&47 / &20` `&33 / &20` in
  let elbow = c983f4f_point (c983f5_use C983F5_F5_SOUTHEAST_G6 [f5]) in
  let bar = MP (SPECL C983E_VARS C983AB_BOTTOM_BAR) (c983f4f_hh ()) in
  let barat x = let th = SPEC x bar in
    MP (MP th (EQT_ELIM (REAL_RAT_REDUCE_CONV (lhand (concl th)))))
       (EQT_ELIM (REAL_RAT_REDUCE_CONV (lhand (rand (concl th))))) in
  let bottomLow = barat `&12 / &5` and bottomHigh = barat `&5 / &2` in
  let noHigh = excl 512 8192 bottomHigh in
  let f4tm = c983f4f_mem 4 5 in
  (* F4 present: the crosspoint lemma in the pulled frame *)
  let th1 =
    let inward = c983f4f_point (ASSUME f4tm) in
    let noSW = excl 512 2304 (seed 7 `&33 / &20` `&33 / &20`) in
    let noNE = excl 512 1024 (seed 6 `&47 / &20` `&47 / &20`) in
    let noLow = excl 512 8192 bottomLow in
    let u = unit 512 in
    let facts = [u; ONCE_REWRITE_RULE[REAL_ADD_SYM] u; pos; side; elbow; inward; marker;
                 noSW; noNE; noLow; noHigh] in
    c983sa_apply C983F5C_SWY_CONV (SPECL (c983f5c_swy 512) C981CP_POINT) facts in
  (* F4 absent: F8 from the southeast components, then the horizontal transfer *)
  let th2 =
    let noF4 = ASSUME (mk_neg f4tm) in
    let comps = c983f5_use C983F5_F5_SOUTHEAST_COMPONENTS [f5] in
    let f8 = MP (MATCH_MP C983F5C_SOUTHEAST_NO_F4_CHECK comps) noF4 in
    let outer = c983f4f_point f8 in
    let missing = c983sa_missing 4 5 in
    c983sa_apply C983FO_CONV (SPECL (c983ab_own 512) OCF4PT_HORIZONTAL_ORIGINAL)
      [unit 512; pos; side; marker; elbow; outer; missing; noHigh] in
  let th = DISJ_CASES (SPEC f4tm EXCLUDED_MIDDLE) th1 th2 in
  c983f4f_close (c983sa_stmt [c983f4f_mem 5 7] (c983ab_in 512 `&5 / &2` `&2`)) th;;
