(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/F5LowerRight.lean.            *)
(* The two-wall center theorem removes the pure lower right component for    *)
(* every merged F5 owner, and closes the merged G4 branch.  Conventions of   *)
(* CP_OtherCases_C983_F5Filters.ml / SharpApplications.ml (owners p 0 / 5 /  *)
(* 6 / 7 / 9 / 10 / 11 = owner 1 / 512 / 1024 / 2304 / 8192 / 16384 / 32768, *)
(* actual p i = c983e_actual c1 c2 a b l i).  CentralWallCenter.point =      *)
(* CWC_POINT, pullY = LINSIDE_PULLY, f5_merged_center =                      *)
(* C983MCF_F5_MERGED_CENTER, bottom_aux = C983AB_BOTTOM_AUX,                 *)
(* merged_g4_implies_f5 = C983MR_MERGED_G4_IMPLIES_F5.  Tag C983F5LR_.       *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_MergedCenterF5.ml";;
needs "n12/geometry/CP_OtherCases_C983_MergedReduction.ml";;
needs "n12/geometry/CentralWallCenter.ml";;

(* Lean: southeast_without_f8_check (private) *)
let C983F5LR_SOUTHEAST_WITHOUT_F8_CHECK = prove
 (`forall s. MEM s c983f5_southeast_components ==> ~(8 IN s) ==> 4 IN s`,
  c983f5_check [c983f5_southeast_components]);;

let C983F5LR_LOWER = mk_eq(c983f4f_act 10, `{8, 18}`);;

(* Lean: f5_right_not_lower *)
let c983f5lr_not_lower f5 =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let lower = ASSUME C983F5LR_LOWER in
  let memo j = EQT_ELIM ((REWRITE_CONV[lower; IN_INSERT; NOT_IN_EMPTY] THENC NUM_REDUCE_CONV) (c983f4f_mem j 10)) in
  let rNoF9 = EQT_ELIM ((REWRITE_CONV[lower; IN_INSERT; NOT_IN_EMPTY] THENC NUM_REDUCE_CONV)
                          (mk_neg (c983f4f_mem 9 10))) in
  let rF8 = memo 8 and rG8 = memo 18 in
  let eF4 = MP (MATCH_MP C983F5LR_SOUTHEAST_WITHOUT_F8_CHECK (c983f5_use C983F5_F5_SOUTHEAST_COMPONENTS [f5]))
               (c983f4f_absent 10 5 rF8) in
  let eG6 = c983f5_use C983F5_F5_SOUTHEAST_G6 [f5] in
  let rMissing = PROVE_HYP rNoF9 (c983sa_missing 9 10) in
  let singleton = seed 0 `&87 / &50` `&1` in
  let bHigh = CONJUNCT1 (MP (SPECL C983E_VARS C983AB_BOTTOM_AUX) (c983f4f_hh ())) in
  let pA = c983fo_pull LINSIDE_PULLY 512 and pR = c983fo_pull LINSIDE_PULLY 16384
  and pT = c983fo_pull LINSIDE_PULLY 8192 in
  let punit m t =
    let c = el 0 t and s = el 1 t in
    let tm = mk_eq(mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` c c)
                     (mk_binop `( * ):real->real->real` s s), `&1`) in
    MP (prove(mk_imp(concl (unit m), tm), CONV_TAC REAL_RING)) (unit m) in
  let disj m n t1 t2 =
    let tm = list_mk_comb(`ldisj`, t1 @ t2) in
    EQ_MP (SYM (REWRITE_CONV[ldisj; LINSIDE_PULLY] tm))
          (GEN `x:real` (GEN `y:real` (SPECL [`x:real`; `&4 - y`] (apart m n)))) in
  let point = c983sa_apply C983FO_CONV (SPECL (pA @ pR @ pT) CWC_POINT)
    [punit 512 pA; punit 16384 pR; punit 8192 pT; pos; side; REFL `l:real`;
     MATCH_MP LCONT_PULLY (box 16384); MATCH_MP LCONT_PULLY (box 8192);
     c983f4f_point eF4; c983f4f_point eG6; seed 5 `&47 / &20` `&33 / &20`;
     excl 512 1024 (seed 6 `&47 / &20` `&47 / &20`); excl 512 2304 (seed 7 `&33 / &20` `&33 / &20`);
     seed 10 `&1543 / &500` `&2`; c983f4f_point rG8; rMissing;
     seed 9 `&2` `&457 / &500`; bHigh; excl 8192 1 singleton;
     disj 512 16384 pA pR; disj 512 8192 pA pT] in
  let center = c983f5_use C983MCF_F5_MERGED_CENTER [f5] in
  let f = MP (NOT_ELIM (SPECL [`&2`; `&2`] (apart 512 2304))) (CONJ point center) in
  NOT_INTRO (DISCH C983F5LR_LOWER f);;
let C983F5LR_F5_RIGHT_NOT_LOWER = c983f4f_close (c983sa_stmt [c983f4f_mem 5 7] (mk_neg C983F5LR_LOWER))
  (c983f5lr_not_lower (c983f5_f5 ()));;

(* Lean: right_after_lower_check (private) *)
let C983F5LR_RIGHT_AFTER_LOWER_CHECK = prove
 (`forall s. MEM s c983f5_right_components ==> ~(s = {8, 18}) ==> 9 IN s`,
  c983f5_check [c983f5_right_components]);;

(* Lean: f5_right_f9 *)
let c983f5lr_right_f9 f5 =
  MP (MATCH_MP C983F5LR_RIGHT_AFTER_LOWER_CHECK (c983f5_use C983F5_F5_RIGHT_COMPONENTS [f5]))
     (c983f5lr_not_lower f5);;
let C983F5LR_F5_RIGHT_F9 = c983f4f_close (c983sa_stmt [c983f4f_mem 5 7] (c983f4f_mem 9 10))
  (c983f5lr_right_f9 (c983f5_f5 ()));;

(* Lean: f5_northeast_f7 *)
let c983f5lr_northeast_f7 f5 =
  c983f5_res_right (CONJUNCT1 (c983f5_use C983F5_F5_NORTHEAST_COVER [f5]))
    (c983f4f_absent 10 6 (c983f5lr_right_f9 f5));;
let C983F5LR_F5_NORTHEAST_F7 = c983f4f_close (c983sa_stmt [c983f4f_mem 5 7] (c983f4f_mem 7 6))
  (c983f5lr_northeast_f7 (c983f5_f5 ()));;

(* Lean: top_without_f7_check (private) *)
let C983F5LR_TOP_WITHOUT_F7_CHECK = prove
 (`forall s. MEM s (EL 11 c983e_original_components) ==> ~(7 IN s) ==> 3 IN s /\ 14 IN s`,
  c983f5_check []);;

(* Lean: f5_top_f3_g4 *)
let c983f5lr_top_f3_g4 f5 =
  MP (MATCH_MP C983F5LR_TOP_WITHOUT_F7_CHECK (c983f4f_orig 11))
     (c983f4f_absent 6 11 (c983f5lr_northeast_f7 f5));;
let C983F5LR_F5_TOP_F3_G4 = c983f4f_close
  (c983sa_stmt [c983f4f_mem 5 7] (mk_conj(c983f4f_mem 3 11, c983f4f_mem 14 11)))
  (c983f5lr_top_f3_g4 (c983f5_f5 ()));;

(* Lean: merged_no_g4 *)
let C983F5LR_MERGED_NO_G4 =
  let g4 = c983f4f_mem 14 7 in
  let f5 = c983f5_use C983MR_MERGED_G4_IMPLIES_F5 [ASSUME g4] in
  let foreign = CONJUNCT2 (c983f5lr_top_f3_g4 f5) in
  let f = MP (NOT_ELIM (c983f4f_absent 11 7 foreign)) (ASSUME g4) in
  c983f4f_close (c983sa_stmt [] (mk_neg g4)) (NOT_INTRO (DISCH g4 f));;
