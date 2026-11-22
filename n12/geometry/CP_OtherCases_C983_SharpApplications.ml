(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/SharpApplications.lean.       *)
(* The sharp single-square theorems instantiated with the original C983      *)
(* owners.  Conventions of CP_OtherCases_C983_F4Filters.ml / F4Origins.ml:   *)
(* owners p i = owner at mask EL i c983ri_owner_code (2 -> 12, 3 -> 48,      *)
(* 5 -> 512, 6 -> 1024, 7 -> 2304, 9 -> 8192, 10 -> 16384, 11 -> 32768),     *)
(* actual p i = c983e_actual c1 c2 a b l i, hf = the IMAGE hypothesis.       *)
(* Geometry: OutwardBarPoint.point_original = OCOBP_POINT_ORIGINAL,          *)
(* UpperBarPoint.point_original = OCUBP_POINT_ORIGINAL,                      *)
(* InwardTopPoint.point_original = OCITP_POINT_ORIGINAL,                     *)
(* C1092MixedSpan.impossible = C1092MS_IMPOSSIBLE,                           *)
(* C981CompletionOutwardAnchor.impossible = C981OA_IMPOSSIBLE;              *)
(* pullY / pullSwap (pullX q) via LINSIDE_PULLY / LINSIDE_PULLSW+PULLX.      *)
(* bottom_bar = C983AB_BOTTOM_BAR.  Tag C983SA_.                             *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F4Origins.ml";;
needs "n12/geometry/CP_OtherCases_OutwardBarPoint.ml";;
needs "n12/geometry/CP_OtherCases_UpperBarPoint.ml";;
needs "n12/geometry/CP_OtherCases_InwardTopPoint.ml";;
needs "n12/geometry/CP_C1092_MixedSpan.ml";;
needs "n12/geometry/CP_C981_OutwardAnchor.ml";;

(* Lean: missing_auxiliary *)
let C983SA_MISSING_AUXILIARY = prove
 (mk_forall(`c1:num->real`, list_mk_forall([`c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`; `j:num`],
   mk_imp(`j < 20 /\ ~(j IN c983e_actual c1 c2 a b l i)`,
     mk_neg(list_mk_comb(`linside`, c983e_own `i:num` @ [`EL j (AUXPTS 2)$1`; `EL j (AUXPTS 2)$2`]))))),
  SIMP_TAC[C983F4F_POINT_EXACT]);;

(* forward form at literal indices: |- ~linside (owners p i) x_j y_j  (hyp ~(j IN actual i)) *)
let c983sa_missing j i =
  let m = el i C983E_MASKS in
  let eq = SPECL (C983E_VARS @ [mk_small_numeral m]) (oo_aux_point j) in
  let nm = CONV_RULE C983F4F_ACT_CONV (ASSUME (mk_neg (c983f4f_mem j i))) in
  CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) (EQ_MP (SYM (AP_TERM `(~)` eq)) nm);;

let c983sa_aux j i = c983f4f_point (ASSUME (c983f4f_mem j i));;

(* discharge the antecedents of spec from facts, up to the conversion conv *)
let c983sa_apply conv spec facts =
  let nf = map (fun f -> CONV_RULE conv f) facts in
  let ants = conjuncts (lhand (concl spec)) in
  let pa tm =
    try find (fun f -> aconv (concl f) tm) facts with Failure _ ->
    let eq = conv tm in
    let r = rhs (concl eq) in
    if r = `true` then EQT_ELIM eq else
    try EQ_MP (SYM eq) (find (fun f -> aconv (concl f) r) nf)
    with Failure _ -> failwith ("c983sa_apply: " ^ string_of_term tm) in
  let th = MP spec (end_itlist CONJ (map pa ants)) in
  CONV_RULE conv th;;

let C983SA_SWX_CONV = REWRITE_CONV[LINSIDE_PULLSW; LINSIDE_PULLX; REAL_NEG_MUL2] THENC
                      ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV;;

(* the tuple of pullSwap (pullX (owner m)) *)
let c983sa_swx m =
  let px = c983fo_pull LINSIDE_PULLX m in
  let t = SPECL (px @ [`x:real`; `y:real`]) LINSIDE_PULLSW in
  let args = snd (strip_comb (lhs (concl t))) in
  [el 0 args; el 1 args; el 2 args; el 3 args; el 4 args];;

(* the bottom bar of owner 9 excluded from owner m:
   |- !z. &113 / &50 <= z ==> z <= &14 / &5 ==> ~linside (owner m) z (&1) *)
let c983sa_bar_excl m =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let bar = MP (SPECL C983E_VARS C983AB_BOTTOM_BAR) (c983f4f_hh ()) in
  let lo = `&113 / &50 <= z` and hi = `z <= &14 / &5` in
  let pt = MP (MP (SPEC `z:real` bar) (ASSUME lo)) (ASSUME hi) in
  GEN `z:real` (DISCH lo (DISCH hi (excl m 8192 pt)));;

let c983sa_stmt hyps concl =
  mk_forall(`c1:num->real`, list_mk_forall([`c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
    mk_imp(list_mk_conj ([C983F4F_NP; C983F4F_IMG] @ hyps), concl)));;

(* Lean: southeast_outward_point *)
let C983SA_SOUTHEAST_OUTWARD_POINT =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let hyps = [c983f4f_mem 8 5; c983f4f_mem 18 5; mk_neg (c983f4f_mem 16 5)] in
  let marker = seed 5 `&47 / &20` `&33 / &20` in
  let outward = c983sa_aux 8 5 and upper = c983sa_aux 18 5 in
  let missingG = c983sa_missing 16 5 in
  let right = seed 10 `&1543 / &500` `&2` in
  let corner = seed 2 `&3` `&1` and cornerMarker = seed 2 `&1543 / &500` `&1` in
  let facts = [unit 512; pos; side; marker; outward; upper; missingG;
               excl 512 16384 right; excl 512 12 corner; excl 512 12 cornerMarker;
               c983sa_bar_excl 512] in
  let th = c983sa_apply C983FO_CONV (SPECL (c983fo_pull LINSIDE_PULLY 512) OCOBP_POINT_ORIGINAL) facts in
  c983f4f_close (c983sa_stmt hyps (c983ab_in 512 `&101 / &40` `&17 / &8`)) th;;

(* Lean: northeast_upper_point *)
let C983SA_NORTHEAST_UPPER_POINT =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let top = c983ab_in 32768 `&2` `&3` in
  let bar = mk_forall(`y:real`, mk_imp(`&113 / &50 <= y`, mk_imp(`y <= &64 / &25`,
              c983ab_in 16384 `&3` `y:real`))) in
  let hyps = [c983f4f_mem 7 6; mk_neg (c983f4f_mem 5 6); top; bar] in
  let barx =
    let lo = `&113 / &50 <= y` and hi = `y <= &64 / &25` in
    let pt = MP (MP (SPEC `y:real` (ASSUME bar)) (ASSUME lo)) (ASSUME hi) in
    GEN `y:real` (DISCH lo (DISCH hi (excl 1024 16384 pt))) in
  let facts = [unit 1024; pos; side; seed 6 `&47 / &20` `&47 / &20`; c983sa_aux 7 6;
               c983sa_missing 5 6; excl 1024 32768 (ASSUME top);
               excl 1024 48 (seed 3 `&3` `&3`); barx] in
  let th = c983sa_apply C983FO_CONV (SPECL (c983ab_own 1024) OCUBP_POINT_ORIGINAL) facts in
  c983f4f_close (c983sa_stmt hyps (c983ab_in 1024 `&101 / &40` `&17 / &8`)) th;;

(* Lean: northeast_inward_top_point *)
let C983SA_NORTHEAST_INWARD_TOP_POINT =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let hyps = [c983f4f_mem 5 6; c983f4f_mem 16 6; c983f4f_mem 7 6; mk_neg (c983f4f_mem 17 6)] in
  let facts = [unit 1024; pos; side; seed 6 `&47 / &20` `&47 / &20`;
               c983sa_aux 5 6; c983sa_aux 16 6; c983sa_aux 7 6; c983sa_missing 17 6;
               excl 1024 2304 (seed 7 `&33 / &20` `&47 / &20`);
               excl 1024 512 (seed 5 `&47 / &20` `&33 / &20`)] in
  let th = c983sa_apply C983FO_CONV (SPECL (c983ab_own 1024) OCITP_POINT_ORIGINAL) facts in
  c983f4f_close (c983sa_stmt hyps (c983ab_in 1024 `&101 / &40` `&17 / &8`)) th;;

(* Lean: northeast_mixed_exclusion *)
let C983SA_NORTHEAST_MIXED_EXCLUSION =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let hyps = [c983f4f_mem 16 6; c983f4f_mem 7 6; mk_neg (c983f4f_mem 5 6); mk_neg (c983f4f_mem 17 6);
              c983f4f_mem 9 10; c983f4f_mem 19 10] in
  let facts = [ONCE_REWRITE_RULE[REAL_ADD_SYM] (unit 1024); pos; side;
               c983sa_aux 16 6; c983sa_aux 7 6; c983sa_missing 5 6; c983sa_missing 17 6;
               excl 1024 16384 (c983sa_aux 9 10); excl 1024 16384 (c983sa_aux 19 10)] in
  let th = c983sa_apply C983SA_SWX_CONV (SPECL (c983sa_swx 1024) C1092MS_IMPOSSIBLE) facts in
  c983f4f_close (c983sa_stmt hyps `false`) th;;

(* Lean: southeast_inward_outward_exclusion *)
let C983SA_SOUTHEAST_INWARD_OUTWARD_EXCLUSION =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let hyps = [c983f4f_mem 4 5; c983f4f_mem 18 5; mk_neg (c983f4f_mem 16 5)] in
  let bar =
    let b = c983sa_bar_excl 512 in
    let lh = `&113 / &50 <= z /\ z <= &14 / &5` in
    let a = ASSUME lh in
    GEN `z:real` (DISCH lh (MP (MP (SPEC `z:real` b) (CONJUNCT1 a)) (CONJUNCT2 a))) in
  let facts = [unit 512; pos; side; seed 5 `&47 / &20` `&33 / &20`;
               c983sa_aux 4 5; c983sa_aux 18 5;
               excl 512 12 (seed 2 `&3` `&1`); excl 512 16384 (seed 10 `&1543 / &500` `&2`);
               c983sa_missing 16 5; bar] in
  let th = c983sa_apply C983FO_CONV (SPECL (c983ab_own 512) C981OA_IMPOSSIBLE) facts in
  c983f4f_close (c983sa_stmt hyps `false`) th;;
