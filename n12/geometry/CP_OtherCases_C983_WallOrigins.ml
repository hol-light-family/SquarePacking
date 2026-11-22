(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/WallOrigins.lean.             *)
(* Both genuine corner/right-wall transfers and their universal F5 join.     *)
(* Conventions of CP_OtherCases_C983_F4Filters.ml / SharpApplications.ml:    *)
(* owners p i = owner at mask EL i c983ri_owner_code (2 -> 12, 3 -> 48,      *)
(* 5 -> 512, 6 -> 1024, 7 -> 2304, 9 -> 8192, 10 -> 16384, 11 -> 32768),     *)
(* actual p i = c983e_actual c1 c2 a b l i.  WallProfile.boundary_origin =   *)
(* OCWPBO_BOUNDARY_ORIGIN, TopOnlyExtension.point_original =                 *)
(* OCTOE_POINT_ORIGINAL, bottom_bar = C983AB_BOTTOM_BAR, f5_top_origin =     *)
(* C983F5T_F5_TOP_ORIGIN, f5_southeast_crosspoint =                          *)
(* C983F5C_F5_SOUTHEAST_CROSSPOINT, f5_upper_of_right_g9 =                   *)
(* C983F5_F5_UPPER_OF_RIGHT_G9.  pullSwap (pullX q) and                      *)
(* pullSwap (pullY (pullX q)) are the tuples of LINSIDE_PULLX/PULLY/PULLSW;  *)
(* the container facts come from LCONT_PULLX/PULLY/PULLSW.  Tag C983WO_.     *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F5TopOrigin.ml";;
needs "n12/geometry/CP_OtherCases_TopOnlyExtension.ml";;

(* the container coordinates used by boundary_origin *)
let C983WO_BOX_Y = prove
 (`forall c s u v a. lcont c s u v a ==> forall x y. linside c s u v a x y ==> &0 <= y`,
  REWRITE_TAC[lcont] THEN MESON_TAC[]);;
let C983WO_BOX_XY = prove
 (`forall c s u v a. lcont c s u v a ==> forall x y. linside c s u v a x y ==> &0 <= x /\ &0 <= y`,
  REWRITE_TAC[lcont] THEN MESON_TAC[]);;

(* the tuple of the successive pulls (innermost first) of owner m *)
let c983wo_pulls pths m =
  itlist (fun pth cur ->
    let t = SPECL (cur @ [`x:real`; `y:real`]) pth in
    let args = snd (strip_comb (lhs (concl t))) in
    [el 0 args; el 1 args; el 2 args; el 3 args; el 4 args]) (rev pths) (c983ab_own m);;

let C983WO_SWX_CONV = REWRITE_CONV[LINSIDE_PULLSW; LINSIDE_PULLX] THENC
                      ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV;;
let C983WO_SWYX_CONV = REWRITE_CONV[LINSIDE_PULLSW; LINSIDE_PULLY; LINSIDE_PULLX] THENC
                       ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV;;

(* boundary_origin for B = pulls (owner mb), K = pulls (owner mk) *)
let c983wo_origin pths lconts conv mb mk b ell facts xy =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let pB = c983wo_pulls pths mb and pK = c983wo_pulls pths mk in
  let pbox m = itlist (fun th acc -> MATCH_MP th acc) (rev lconts) (box m) in
  let disj =
    let tm = list_mk_comb(`ldisj`, pK @ pB) in
    EQ_MP (SYM (REWRITE_CONV(ldisj :: pths) tm))
          (GEN `x:real` (GEN `y:real` (SPECL xy (apart mk mb)))) in
  let punit m t =
    let c = el 0 t and s = el 1 t in
    let tm = mk_eq(mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` c c)
                     (mk_binop `( * ):real->real->real` s s), `&1`) in
    MP (prove(mk_imp(concl (unit m), tm), CONV_TAC REAL_RING)) (unit m) in
  let facts = [punit mb pB; punit mk pK; pos; side; REFL `l:real`;
               MATCH_MP C983WO_BOX_Y (pbox mb); MATCH_MP C983WO_BOX_XY (pbox mk); disj] @ facts in
  c983sa_apply conv (SPECL (pB @ pK @ [b; ell]) OCWPBO_BOUNDARY_ORIGIN) facts;;

(* Lean: right_origin_of_lower_aux *)
let c983wo_lower f8 =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let bar = MP (SPECL C983E_VARS C983AB_BOTTOM_BAR) (c983f4f_hh ()) in
  let b52 = let th = SPEC `&5 / &2` bar in
    MP (MP th (EQT_ELIM (REAL_RAT_REDUCE_CONV (lhand (concl th)))))
       (EQT_ELIM (REAL_RAT_REDUCE_CONV (lhand (rand (concl th))))) in
  c983wo_origin [LINSIDE_PULLX; LINSIDE_PULLSW] [LCONT_PULLX; LCONT_PULLSW] C983WO_SWX_CONV
    16384 12 `&457 / &500` `&87 / &50`
    [seed 10 `&1543 / &500` `&2`; c983f4f_point f8; seed 2 `&1543 / &500` `&1`; seed 2 `&3` `&1`;
     excl 12 8192 b52] [`&4 - y`; `x:real`];;

let C983WO_RIGHT_ORIGIN_OF_LOWER_AUX = c983f4f_close
  (c983sa_stmt [c983f4f_mem 8 10] (c983ab_in 16384 `&3` `&2`))
  (c983wo_lower (ASSUME (c983f4f_mem 8 10)));;

(* Lean: northeast_top_extension *)
let c983wo_extension f7 noF5 top se =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let missingL = PROVE_HYP noF5 (c983sa_missing 5 6) in
  c983sa_apply (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) (SPECL (c983ab_own 1024) OCTOE_POINT_ORIGINAL)
    [unit 1024; pos; side; seed 6 `&47 / &20` `&47 / &20`; c983f4f_point f7; missingL;
     excl 1024 32768 top; excl 1024 512 se];;

let C983WO_NORTHEAST_TOP_EXTENSION = c983f4f_close
  (c983sa_stmt [c983f4f_mem 7 6; mk_neg (c983f4f_mem 5 6); c983ab_in 32768 `&2` `&3`;
                c983ab_in 512 `&5 / &2` `&2`] (c983ab_in 1024 `&5 / &2` `&3`))
  (c983wo_extension (ASSUME (c983f4f_mem 7 6)) (ASSUME (mk_neg (c983f4f_mem 5 6)))
     (ASSUME (c983ab_in 32768 `&2` `&3`)) (ASSUME (c983ab_in 512 `&5 / &2` `&2`)));;

(* Lean: right_origin_of_upper_extension *)
let c983wo_upper g9 ext =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  c983wo_origin [LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW] [LCONT_PULLX; LCONT_PULLY; LCONT_PULLSW]
    C983WO_SWYX_CONV 16384 48 `&457 / &500` `&8 / &5`
    [seed 10 `&1543 / &500` `&2`; c983f4f_point g9; seed 3 `&1543 / &500` `&3`; seed 3 `&3` `&3`;
     excl 48 1024 ext] [`&4 - y`; `&4 - x`];;

let C983WO_RIGHT_ORIGIN_OF_UPPER_EXTENSION = c983f4f_close
  (c983sa_stmt [c983f4f_mem 19 10; c983ab_in 1024 `&5 / &2` `&3`] (c983ab_in 16384 `&3` `&2`))
  (c983wo_upper (ASSUME (c983f4f_mem 19 10)) (ASSUME (c983ab_in 1024 `&5 / &2` `&3`)));;

(* Lean: right_origin_cover_check (private) *)
let C983WO_RIGHT_ORIGIN_COVER_CHECK = prove
 (`forall s. MEM s c983f5_right_components ==> 8 IN s \/ 19 IN s`,
  c983f5_check [c983f5_right_components]);;

(* Lean: f5_right_origin *)
let C983WO_F5_RIGHT_ORIGIN =
  let f5 = c983f5_f5 () in
  let d = MATCH_MP C983WO_RIGHT_ORIGIN_COVER_CHECK (c983f5_use C983F5_F5_RIGHT_COMPONENTS [f5]) in
  let lower = c983wo_lower (ASSUME (c983f4f_mem 8 10)) in
  let upper =
    let g9 = ASSUME (c983f4f_mem 19 10) in
    let exactUpper = c983f5_use C983F5_F5_UPPER_OF_RIGHT_G9 [f5; g9] in
    let f7 = c983f5t_memo (CONJUNCT1 exactUpper) 7 6 in
    let noF5 = c983f4f_absent 7 6 f5 in
    let ext = c983wo_extension f7 noF5 (c983f5_use C983F5T_F5_TOP_ORIGIN [f5])
                (c983f5_use C983F5C_F5_SOUTHEAST_CROSSPOINT [f5]) in
    c983wo_upper g9 ext in
  c983f4f_close (c983sa_stmt [c983f4f_mem 5 7] (c983ab_in 16384 `&3` `&2`))
    (DISJ_CASES d lower upper);;
