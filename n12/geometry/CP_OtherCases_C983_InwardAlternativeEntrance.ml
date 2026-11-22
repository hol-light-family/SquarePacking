(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/InwardAlternativeEntrance.lean*)
(* The actual-owner entrance when the merged F5 is absent.  Conventions of  *)
(* CP_OtherCases_C983_F5Filters.ml / SharpApplications.ml (owners p 1 -> 2,  *)
(* 7 -> 2304, 8 -> 4096).  MergedNearPoint.points_original =                 *)
(* CCMNP_POINTS_ORIGINAL (on pullX, LINSIDE_PULLX), InwardShortBarPoint.point *)
(* = OCISBP_POINT (on (owners p 5).translated 2 2, OCOBP_INSIDE_TRANSLATED),  *)
(* inward_outward_impossible = C983IOP_INWARD_OUTWARD_IMPOSSIBLE, left_aux = *)
(* C983AB_LEFT_AUX, bottom_bar = C983AB_BOTTOM_BAR.  Tag C983IAE_.           *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_SharpApplications.ml";;
needs "n12/geometry/CP_OtherCases_C983_F5Filters.ml";;
needs "n12/geometry/CP_OtherCases_InwardShortBarPoint.ml";;
needs "n12/geometry/CP_CommonCases_MergedNearPoint.ml";;

let C983IAE_TR_CONV = REWRITE_CONV[OCOBP_INSIDE_TRANSLATED] THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV;;

(* the tuple of (owner m).translated 2 2 *)
let c983iae_tr m =
  let t = SPECL (c983ab_own m @ [`&2`; `&2`; `p:real`; `q:real`]) OCOBP_INSIDE_TRANSLATED in
  let args = snd (strip_comb (lhs (concl t))) in
  [el 0 args; el 1 args; el 2 args; el 3 args; el 4 args];;

(* Lean: merged_near_when_no_inward *)
let c983iae_merged_near () =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let leftAux = MP (SPECL C983E_VARS C983AB_LEFT_AUX) (c983f4f_hh ()) in
  let facts = [unit 2304; side; seed 7 `&33 / &20` `&33 / &20`; seed 7 `&33 / &20` `&47 / &20`;
               c983sa_missing 4 7; c983sa_missing 5 7;
               excl 2304 2 (seed 1 `&1` `&87 / &50`); excl 2304 4096 (CONJUNCT1 leftAux);
               excl 2304 4096 (seed 8 `&457 / &500` `&2`)] in
  CONJUNCT1 (c983sa_apply C983FO_CONV (SPECL (c983fo_pull LINSIDE_PULLX 2304) CCMNP_POINTS_ORIGINAL) facts);;

let C983IAE_MERGED_NEAR_WHEN_NO_INWARD = c983f4f_close
  (c983sa_stmt [mk_neg (c983f4f_mem 4 7); mk_neg (c983f4f_mem 5 7)] (c983ab_in 2304 `&41 / &20` `&39 / &20`))
  (c983iae_merged_near ());;

(* Lean: southeast_inward_forces_merged_f5 *)
let c983iae_forces () =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let f4 = ASSUME (c983f4f_mem 4 5) in
  let noF5 = ASSUME (mk_neg (c983f4f_mem 5 7)) in
  let west = c983f5_use C983IAE_MERGED_NEAR_WHEN_NO_INWARD [c983f4f_absent 5 7 f4; noF5] in
  let bar =
    let b = MP (SPECL C983E_VARS C983AB_BOTTOM_BAR) (c983f4f_hh ()) in
    let lh = `&13 / &50 <= x /\ x <= &7 / &20` in
    let a = ASSUME lh in
    let lo = MP (REAL_ARITH `&13 / &50 <= x /\ x <= &7 / &20 ==> &113 / &50 <= &2 + x`) a
    and hi = MP (REAL_ARITH `&13 / &50 <= x /\ x <= &7 / &20 ==> &2 + x <= &14 / &5`) a in
    GEN `x:real` (DISCH lh (excl 512 8192 (MP (MP (SPEC `&2 + x` b) lo) hi))) in
  let facts = [unit 512; pos; side; seed 5 `&47 / &20` `&33 / &20`;
               c983sa_aux 16 5; c983sa_aux 4 5; c983sa_missing 8 5; bar] in
  let point = c983sa_apply C983IAE_TR_CONV (SPECL (c983iae_tr 512) OCISBP_POINT) facts in
  let ap = REWRITE_RULE[ldisj] (MP (SPECL C983E_VARS (oo_apart C983E_F 512 2304)) (c983f4f_hh ())) in
  let f = MP (NOT_ELIM (SPECL [`&41 / &20`; `&39 / &20`] ap)) (CONJ point west) in
  CCONTR (c983f4f_mem 5 7) f;;

let C983IAE_SOUTHEAST_INWARD_FORCES_MERGED_F5 = c983f4f_close
  (c983sa_stmt [c983f4f_mem 4 5; c983f4f_mem 16 5; mk_neg (c983f4f_mem 8 5)] (c983f4f_mem 5 7))
  (c983iae_forces ());;

(* Lean: southeast_no_f8_check (private) *)
let C983IAE_SOUTHEAST_NO_F8_CHECK = prove
 (`forall s. MEM s (EL 5 c983e_original_components) ==> ~(8 IN s) ==> 4 IN s /\ (16 IN s \/ 18 IN s)`,
  c983f5_check []);;

(* Lean: no_merged_f5_southeast_f8 *)
let c983iae_f8 () =
  let noF5 = ASSUME (mk_neg (c983f4f_mem 5 7)) in
  let noF8 = ASSUME (mk_neg (c983f4f_mem 8 5)) in
  let labels = MP (MATCH_MP C983IAE_SOUTHEAST_NO_F8_CHECK (c983f4f_orig 5)) noF8 in
  let g6 = ASSUME (c983f4f_mem 16 5) and ng6 = ASSUME (mk_neg (c983f4f_mem 16 5)) in
  let c1 = MP (NOT_ELIM noF5) (c983f5_use C983IAE_SOUTHEAST_INWARD_FORCES_MERGED_F5 [CONJUNCT1 labels; g6; noF8]) in
  let c2 = c983f5_use C983SA_SOUTHEAST_INWARD_OUTWARD_EXCLUSION
             [CONJUNCT1 labels; c983f5_res_left (CONJUNCT2 labels) ng6; ng6] in
  CCONTR (c983f4f_mem 8 5) (DISJ_CASES (SPEC (c983f4f_mem 16 5) EXCLUDED_MIDDLE) c1 c2);;

let C983IAE_NO_MERGED_F5_SOUTHEAST_F8 = c983f4f_close
  (c983sa_stmt [mk_neg (c983f4f_mem 5 7)] (c983f4f_mem 8 5)) (c983iae_f8 ());;

(* Lean: right_no_f8_check (private) *)
let C983IAE_RIGHT_NO_F8_CHECK = prove
 (`forall s. MEM s (EL 10 c983e_original_components) ==> ~(8 IN s) ==> 9 IN s /\ 19 IN s`,
  c983f5_check []);;

(* Lean: no_merged_f5_right *)
let c983iae_right () =
  let f8 = c983f5_use C983IAE_NO_MERGED_F5_SOUTHEAST_F8 [ASSUME (mk_neg (c983f4f_mem 5 7))] in
  MP (MATCH_MP C983IAE_RIGHT_NO_F8_CHECK (c983f4f_orig 10)) (c983f4f_absent 5 10 f8);;

let C983IAE_NO_MERGED_F5_RIGHT = c983f4f_close
  (c983sa_stmt [mk_neg (c983f4f_mem 5 7)] (mk_conj(c983f4f_mem 9 10, c983f4f_mem 19 10)))
  (c983iae_right ());;

(* Lean: northeast_no_right_check (private) *)
let C983IAE_NORTHEAST_NO_RIGHT_CHECK = prove
 (`forall s. MEM s (EL 6 c983e_original_components) ==> ~(9 IN s) ==> ~(19 IN s) ==> ~(13 IN s) ==>
       (5 IN s \/ 7 IN s) /\ (16 IN s \/ 17 IN s)`, c983f5_check []);;

(* Lean: top_f7_g7_check (private) *)
let C983IAE_TOP_F7_G7_CHECK = prove
 (`forall s. MEM s (EL 11 c983e_original_components) ==> 7 IN s ==> 17 IN s`, c983f5_check []);;

(* Lean: southeast_no_g6_check (private) *)
let C983IAE_SOUTHEAST_NO_G6_CHECK = prove
 (`forall s. MEM s (EL 5 c983e_original_components) ==> ~(16 IN s) ==> 18 IN s`, c983f5_check []);;

(* Lean: actual_inward_outward (private) *)
let c983iae_actual_io () =
  let np = ASSUME C983F4F_NP and hh = c983f4f_hh () in
  let unit m = MP (SPECL (C983E_VARS @ [mk_small_numeral m]) OO_UNIT) np in
  let side = MP (SPECL C983E_VARS OO_SIDE) np in
  let pos = MATCH_MP (REAL_ARITH `&1 < l ==> &0 < l`) side in
  let seed i x y = MP (SPECL C983E_VARS (c983e_seed_inside i (x, y))) hh in
  let apart m n = MP (SPECL C983E_VARS (oo_apart C983E_F m n)) hh in
  let bar = MP (SPECL C983E_VARS C983AB_BOTTOM_BAR) hh in
  let facts = [unit 1024; unit 512; unit 8192; unit 12; unit 16384; unit 2304; pos; side; REFL `l:real`;
               seed 6 `&47 / &20` `&47 / &20`; c983sa_aux 5 6; c983sa_aux 16 6; c983sa_missing 7 6;
               seed 5 `&47 / &20` `&33 / &20`; c983sa_aux 8 5; c983sa_aux 18 5;
               seed 7 `&33 / &20` `&47 / &20`; seed 10 `&1543 / &500` `&2`;
               seed 2 `&3` `&1`; seed 2 `&1543 / &500` `&1`; bar;
               apart 1024 512; apart 1024 2304; apart 512 16384; apart 512 12; apart 512 8192] in
  let own m = c983ab_own m in
  let spec = SPECL (own 1024 @ own 512 @ own 8192 @ own 12 @ own 16384 @ own 2304)
                   C983IOP_INWARD_OUTWARD_IMPOSSIBLE in
  let pa tm = try find (fun f -> aconv (concl f) tm) facts
              with Failure _ -> failwith ("c983iae_actual_io: " ^ string_of_term tm) in
  MP spec (end_itlist CONJ (map pa (conjuncts (lhand (concl spec)))));;

let C983IAE_ACTUAL_INWARD_OUTWARD = c983f4f_close
  (c983sa_stmt [c983f4f_mem 5 6; c983f4f_mem 16 6; mk_neg (c983f4f_mem 7 6);
                c983f4f_mem 8 5; c983f4f_mem 18 5] `false`)
  (c983iae_actual_io ());;

(* Lean: top_no_f7_check (private) *)
let C983IAE_TOP_NO_F7_CHECK = prove
 (`forall s. MEM s (EL 11 c983e_original_components) ==> ~(7 IN s) ==> 3 IN s /\ 14 IN s`,
  c983f5_check []);;

(* Lean: no_merged_f5_top *)
let c983iae_top () =
  let noF5 = ASSUME (mk_neg (c983f4f_mem 5 7)) in
  let topF7 = ASSUME (c983f4f_mem 7 11) in
  let topG7 = MP (MATCH_MP C983IAE_TOP_F7_G7_CHECK (c983f4f_orig 11)) topF7 in
  let noF7 = c983f4f_absent 11 6 topF7 and noG7 = c983f4f_absent 11 6 topG7 in
  let right = c983f5_use C983IAE_NO_MERGED_F5_RIGHT [noF5] in
  let cover = c983f5_mps (MATCH_MP C983IAE_NORTHEAST_NO_RIGHT_CHECK (c983f4f_orig 6))
    [c983f4f_absent 10 6 (CONJUNCT1 right); c983f4f_absent 10 6 (CONJUNCT2 right);
     c983f4f_absent 7 6 (c983f5_g3 ())] in
  let nF5 = c983f5_res_right (CONJUNCT1 cover) noF7 in
  let nG6 = c983f5_res_right (CONJUNCT2 cover) noG7 in
  let eG8 = MP (MATCH_MP C983IAE_SOUTHEAST_NO_G6_CHECK (c983f4f_orig 5)) (c983f4f_absent 6 5 nG6) in
  let f = c983f5_use C983IAE_ACTUAL_INWARD_OUTWARD
    [nF5; nG6; noF7; c983f5_use C983IAE_NO_MERGED_F5_SOUTHEAST_F8 [noF5]; eG8] in
  MP (MATCH_MP C983IAE_TOP_NO_F7_CHECK (c983f4f_orig 11)) (NOT_INTRO (DISCH (c983f4f_mem 7 11) f));;

let C983IAE_NO_MERGED_F5_TOP = c983f4f_close
  (c983sa_stmt [mk_neg (c983f4f_mem 5 7)] (mk_conj(c983f4f_mem 3 11, c983f4f_mem 14 11)))
  (c983iae_top ());;
