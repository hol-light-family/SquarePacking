(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/LeftOrigin.lean.               *)
(* The actual left origin from a top-wall advance and the original paired   *)
(* northwest corner.  Conventions of CP_OtherCases_C983_F4Filters.ml /       *)
(* WallOrigins.ml: owners p 4 / 6 / 7 / 8 / 11 = owner 192 / 1024 / 2304 /   *)
(* 4096 / 32768, actual p i = c983e_actual c1 c2 a b l i; pullX / pullY /    *)
(* pullSwap are the tuples of LINSIDE_PULLX / PULLY / PULLSW (c983wo_pulls), *)
(* container_pull* = LCONT_PULL*.  WallUpperMissingReach.point = WUMR_POINT, *)
(* WallProfile.boundary_origin = OCWPBO_BOUNDARY_ORIGIN (via c983wo_origin), *)
(* horizontal_segment / vertical_segment = OO_HORIZONTAL_SEGMENT /           *)
(* OO_VERTICAL_SEGMENT, left_aux / left_advance = C983AB_LEFT_AUX /          *)
(* C983AB_LEFT_ADVANCE, f5_final_central = C983F5RF_F5_FINAL_CENTRAL.        *)
(* Tag C983LO_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F5TopOnlyPoints.ml";;

let c983lo_use th facts =
  MP (SPECL C983E_VARS th) (end_itlist CONJ ([ASSUME C983F4F_NP; ASSUME C983F4F_IMG] @ facts));;

(* Lean: top_left_advance *)
let c983lo_advance f3 g7 =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let pths = [LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW] in
  let pT = c983wo_pulls pths 32768 in
  let boxT = itlist (fun th acc -> MATCH_MP th acc) (rev [LCONT_PULLX; LCONT_PULLY; LCONT_PULLSW]) (box 32768) in
  let unitT =
    let c = el 0 pT and s = el 1 pT in
    let tm = mk_eq(mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` c c)
                     (mk_binop `( * ):real->real->real` s s), `&1`) in
    MP (prove(mk_imp(concl (unit 32768), tm), CONV_TAC REAL_RING)) (unit 32768) in
  c983sa_apply C983WO_SWYX_CONV (SPECL pT WUMR_POINT)
    [unitT; pos; side; boxT; seed 11 `&2` `&1543 / &500`; c983f4f_point f3;
     excl 32768 1024 (c983f4f_point g7); excl 32768 2304 (seed 7 `&33 / &20` `&47 / &20`)];;

let C983LO_TOP_LEFT_ADVANCE = c983f4f_close
  (c983sa_stmt [c983f4f_mem 3 11; c983f4f_mem 17 6] (c983ab_in 32768 `&36 / &25` `&3`))
  (c983lo_advance (ASSUME (c983f4f_mem 3 11)) (ASSUME (c983f4f_mem 17 6)));;

(* Lean: left_origin_of_top_g7 *)
let c983lo_origin f3 g7 =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let anchor = c983f4f_point f3 in
  let topPoint =
    MP (SPECL (c983ab_own 32768 @ [`&36 / &25`; `&8 / &5`; `&3`; `&3 / &2`]) OO_HORIZONTAL_SEGMENT)
       (end_itlist CONJ [c983lo_advance f3 g7; anchor;
                         EQT_ELIM (REAL_RAT_REDUCE_CONV `&36 / &25 < &8 / &5`);
                         EQT_ELIM (REAL_RAT_REDUCE_CONV `&36 / &25 <= &3 / &2`);
                         EQT_ELIM (REAL_RAT_REDUCE_CONV `&3 / &2 <= &8 / &5`)]) in
  let conv = REWRITE_CONV[LINSIDE_PULLSW; LINSIDE_PULLY] THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV in
  c983wo_origin [LINSIDE_PULLY; LINSIDE_PULLSW] [LCONT_PULLY; LCONT_PULLSW] conv
    4096 192 `&457 / &500` `&8 / &5`
    [seed 8 `&457 / &500` `&2`; CONJUNCT2 (c983lo_use C983AB_LEFT_AUX []);
     seed 4 `&457 / &500` `&3`; seed 4 `&1` `&3`; excl 192 32768 topPoint] [`y:real`; `&4 - x`];;

let C983LO_LEFT_ORIGIN_OF_TOP_G7 = c983f4f_close
  (c983sa_stmt [c983f4f_mem 3 11; c983f4f_mem 17 6] (c983ab_in 4096 `&1` `&2`))
  (c983lo_origin (ASSUME (c983f4f_mem 3 11)) (ASSUME (c983f4f_mem 17 6)));;

let C983LO_LEFT_BAR = mk_forall(`y:real`, mk_imp(`&2 <= y`, mk_imp(`y <= &14 / &5`,
                        c983ab_in 4096 `&1` `y:real`)));;

(* Lean: left_full_bar_of_top_g7 *)
let c983lo_bar f3 g7 =
  let lower = `&2 <= y` and upper = `y <= &14 / &5` in
  let th = MP (SPECL (c983ab_own 4096 @ [`&1`; `&2`; `&14 / &5`; `y:real`]) OO_VERTICAL_SEGMENT)
              (end_itlist CONJ [c983lo_origin f3 g7; c983lo_use C983AB_LEFT_ADVANCE [];
                                EQT_ELIM (REAL_RAT_REDUCE_CONV `&2 < &14 / &5`);
                                ASSUME lower; ASSUME upper]) in
  GEN `y:real` (DISCH lower (DISCH upper th));;

let C983LO_LEFT_FULL_BAR_OF_TOP_G7 = c983f4f_close
  (c983sa_stmt [c983f4f_mem 3 11; c983f4f_mem 17 6] C983LO_LEFT_BAR)
  (c983lo_bar (ASSUME (c983f4f_mem 3 11)) (ASSUME (c983f4f_mem 17 6)));;

(* Lean: f5_left_full_bar *)
let C983LO_F5_LEFT_FULL_BAR =
  let final = c983lo_use C983F5RF_F5_FINAL_CENTRAL [c983f5_f5 ()] in
  let e6 = CONJUNCT1 (CONJUNCT2 final) and e11 = CONJUNCT2 (CONJUNCT2 (CONJUNCT2 final)) in
  let dec eq tm = EQT_ELIM ((REWRITE_CONV[eq; IN_INSERT; NOT_IN_EMPTY] THENC NUM_REDUCE_CONV) tm) in
  c983f4f_close (c983sa_stmt [c983f4f_mem 5 7] C983LO_LEFT_BAR)
    (c983lo_bar (dec e11 (c983f4f_mem 3 11)) (dec e6 (c983f4f_mem 17 6)));;
