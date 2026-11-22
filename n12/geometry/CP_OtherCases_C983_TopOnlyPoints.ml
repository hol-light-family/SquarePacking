(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/TopOnlyPoints.lean.            *)
(* Original-owner point entrance for the F4 top-only ending and the         *)
(* elementary merged points.  Conventions of CP_OtherCases_C983_F4Filters.ml *)
(* / SharpApplications.ml: owners p 3 / 5 / 6 / 7 / 10 / 11 = owner          *)
(* 48 / 512 / 1024 / 2304 / 16384 / 32768, actual p i = c983e_actual .. i.   *)
(* MergedElementary.horizontal_original / two_inward_center_original =       *)
(* OCMEL_*, TopOnlyLeftPoint.point_original = OCTOLP_POINT_ORIGINAL,         *)
(* f4_northeast_f7 = C983F4CF_F4_NORTHEAST_F7, f4_northeast_g7 =             *)
(* C983F4CE_F4_NORTHEAST_G7, f4_top_origin = C983FO_F4_TOP_ORIGIN,           *)
(* f4_right_bar = C983FO_F4_RIGHT_BAR, f4_right = C983F4F_F4_RIGHT,          *)
(* northeast_upper_point = C983SA_NORTHEAST_UPPER_POINT,                     *)
(* northeast_top_extension / right_origin_of_upper_extension = C983WO_*,     *)
(* f4_southeast_crosspoint = C983F4CF_F4_SOUTHEAST_CROSSPOINT.  Tag C983TOP_.*)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F4CentralFinal.ml";;
needs "n12/geometry/CP_OtherCases_C983_WallOrigins.ml";;
needs "n12/geometry/CP_OtherCases_TopOnlyLeftPoint.ml";;
needs "n12/geometry/CP_OtherCases_MergedElementary.ml";;

let c983top_use th facts =
  MP (SPECL C983E_VARS th) (end_itlist CONJ ([ASSUME C983F4F_NP; ASSUME C983F4F_IMG] @ facts));;

let C983TOP_CONV = ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV;;

(* Lean: merged_horizontal_point *)
let C983TOP_MERGED_HORIZONTAL_POINT =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let th = c983sa_apply C983TOP_CONV (SPECL (c983ab_own 2304) OCMEL_HORIZONTAL_ORIGINAL)
    [unit 2304; pos; side; seed 7 `&33 / &20` `&33 / &20`; seed 7 `&33 / &20` `&47 / &20`;
     c983f4f_point (c983top_use C983F4F_MERGED_G3 []);
     excl 2304 512 (seed 5 `&47 / &20` `&33 / &20`); excl 2304 1024 (seed 6 `&47 / &20` `&47 / &20`)] in
  c983f4f_close (c983sa_stmt [] (c983ab_in 2304 `&3 / &2` `&2`)) th;;

(* Lean: two_inward_merged_center *)
let C983TOP_TWO_INWARD_MERGED_CENTER =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let th = c983sa_apply C983TOP_CONV (SPECL (c983ab_own 2304) OCMEL_TWO_INWARD_CENTER_ORIGINAL)
    [unit 2304; pos; side; seed 7 `&33 / &20` `&33 / &20`; seed 7 `&33 / &20` `&47 / &20`;
     c983f4f_point (c983top_use C983F4F_MERGED_G3 []);
     c983sa_aux 4 7; c983sa_aux 5 7] in
  c983f4f_close (c983sa_stmt [c983f4f_mem 4 7; c983f4f_mem 5 7] (c983ab_in 2304 `&2` `&2`)) th;;

let C983TOP_BAR = mk_forall(`y:real`, mk_imp(`&113 / &50 <= y`, mk_imp(`y <= &64 / &25`,
                    c983ab_in 16384 `&3` `y:real`)));;

(* Lean: northeast_left_point *)
let c983top_left g7 noF5 sharp top bar =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let barx =
    let lo = `&113 / &50 <= y` and hi = `y <= &64 / &25` in
    let pt = MP (MP (SPEC `y:real` bar) (ASSUME lo)) (ASSUME hi) in
    GEN `y:real` (DISCH lo (DISCH hi (excl 1024 16384 pt))) in
  c983sa_apply C983TOP_CONV (SPECL (c983ab_own 1024) OCTOLP_POINT_ORIGINAL)
    [unit 1024; pos; side; seed 6 `&47 / &20` `&47 / &20`; c983f4f_point g7; sharp;
     PROVE_HYP noF5 (c983sa_missing 5 6); excl 1024 32768 top; excl 1024 48 (seed 3 `&3` `&3`); barx];;

let C983TOP_NORTHEAST_LEFT_POINT = c983f4f_close
  (c983sa_stmt [c983f4f_mem 17 6; mk_neg (c983f4f_mem 5 6); c983ab_in 1024 `&101 / &40` `&17 / &8`;
                c983ab_in 32768 `&2` `&3`; C983TOP_BAR] (c983ab_in 1024 `&2` `&131 / &50`))
  (c983top_left (ASSUME (c983f4f_mem 17 6)) (ASSUME (mk_neg (c983f4f_mem 5 6)))
     (ASSUME (c983ab_in 1024 `&101 / &40` `&17 / &8`)) (ASSUME (c983ab_in 32768 `&2` `&3`))
     (ASSUME C983TOP_BAR));;

(* Lean: f4_top_only_points *)
let C983TOP_F4_TOP_ONLY_POINTS =
  let f4 = ASSUME (c983f4f_mem 4 7) and noF5 = ASSUME (mk_neg (c983f4f_mem 5 6)) in
  let f7 = c983top_use C983F4CF_F4_NORTHEAST_F7 [f4] in
  let g7 = c983top_use C983F4CE_F4_NORTHEAST_G7 [f4] in
  let top = c983top_use C983FO_F4_TOP_ORIGIN [f4] in
  let bar = c983top_use C983FO_F4_RIGHT_BAR [f4] in
  let sharp = c983top_use C983SA_NORTHEAST_UPPER_POINT [f7; noF5; top; bar] in
  let ext = c983top_use C983WO_NORTHEAST_TOP_EXTENSION
              [f7; noF5; top; c983top_use C983F4CF_F4_SOUTHEAST_CROSSPOINT [f4]] in
  let left = c983top_use C983TOP_NORTHEAST_LEFT_POINT [g7; noF5; sharp; top; bar] in
  let right = c983top_use C983WO_RIGHT_ORIGIN_OF_UPPER_EXTENSION
                [CONJUNCT2 (c983top_use C983F4F_F4_RIGHT [f4]); ext] in
  c983f4f_close
    (c983sa_stmt [c983f4f_mem 4 7; mk_neg (c983f4f_mem 5 6)]
       (list_mk_conj [c983ab_in 1024 `&101 / &40` `&17 / &8`; c983ab_in 1024 `&5 / &2` `&3`;
                      c983ab_in 1024 `&2` `&131 / &50`; c983ab_in 16384 `&3` `&2`]))
    (end_itlist CONJ [sharp; ext; left; right]);;
