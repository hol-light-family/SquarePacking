(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C1090/AuxiliaryCover.lean          *)
(* (N12Compact.Completion.OtherCases.C1090.AuxiliaryCover; Lean header:      *)
(* "Source-only; these declarations have not been compiled").  Original     *)
(* C1090 auxiliary covers from the actual family, via the producers          *)
(* c1090ac_central_cover / c1090ac_wall_cover of AuxiliaryCoverTransport.ml  *)
(* (each checks the points / mask / ordinary conditions and re-proves the    *)
(* certificate at the transformed points).  owners p i is the owner tuple at *)
(* mask EL i c1090od_masks.  RelaxedOwnerDomain.reflectXG / halfTurnPerm are *)
(* RO_REFLECTXG / RO_HALFTURN; Equiv.refl is the identity list.  Tag C1090AV_.*)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1090_AuxiliaryCoverTransport.ml";;

let C1090AV_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let c1090av_owner i =
  map (fun f -> list_mk_comb(f, C1090AV_VARS @
    [mk_comb(mk_comb(`EL:num->num list->num`, mk_small_numeral i), `c1090od_masks`)]))
    [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;

(* the literal cover of owner i from a transported cover h (transform trf, source G points) *)
let c1090av_cover producer trf kind perm i js pts =
  let h = producer trf kind perm i in
  let own = c1090av_owner i in
  let body = list_mk_disj (map (fun (x, y) -> list_mk_comb(`linside`, own @ [x; y])) pts) in
  let eqs = map (fun j -> pull_point_eq trf own (c1090ac_pt 1 j)) js in
  prove(list_mk_forall(C1090AV_VARS,
          mk_imp(`NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1090od_family`, body)),
    REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP h) THEN
    REWRITE_TAC eqs THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN MESON_TAC[]);;

let c1090av_central = c1090av_cover c1090ac_central_cover;;
let c1090av_wall = c1090av_cover c1090ac_wall_cover;;

(* Lean: southwest_f_cover *)
let C1090AV_SOUTHWEST_F_COVER = c1090av_central (true, false, false) 0 C1090AC_SWAPGF 4 [0; 2; 3]
  [`&1`, `&87 / &50`; `&8 / &5`, `&1`; `&2`, `&87 / &50`];;
(* Lean: southwest_g_cover *)
let C1090AV_SOUTHWEST_G_COVER = c1090av_central (false, false, false) 1 (0--9) 4 [0; 2; 3]
  [`&1`, `&8 / &5`; `&87 / &50`, `&1`; `&87 / &50`, `&2`];;
(* Lean: southeast_f_cover *)
let C1090AV_SOUTHEAST_F_COVER = c1090av_central (true, true, false) 0 C1090AC_SWAPXGF 5 [0; 2; 3]
  [`&2`, `&87 / &50`; `&12 / &5`, `&1`; `&3`, `&87 / &50`];;
(* Lean: southeast_g_cover *)
let C1090AV_SOUTHEAST_G_COVER = c1090av_central (false, true, false) 1 RO_REFLECTXG 5 [0; 2; 3]
  [`&113 / &50`, `&1`; `&113 / &50`, `&2`; `&3`, `&8 / &5`];;
(* Lean: northeast_f_cover *)
let C1090AV_NORTHEAST_F_COVER = c1090av_central (true, true, true) 0 C1090AC_SWAPXYGF 6 [0; 2; 3]
  [`&2`, `&113 / &50`; `&12 / &5`, `&3`; `&3`, `&113 / &50`];;
(* Lean: northeast_g_cover *)
let C1090AV_NORTHEAST_G_COVER = c1090av_central (false, true, true) 1 RO_HALFTURN 6 [0; 2; 3]
  [`&113 / &50`, `&2`; `&113 / &50`, `&3`; `&3`, `&12 / &5`];;
(* Lean: northwest_f_cover *)
let C1090AV_NORTHWEST_F_COVER = c1090av_central (true, false, true) 0 C1090AC_SWAPYGF 7 [0; 2; 3]
  [`&1`, `&113 / &50`; `&8 / &5`, `&3`; `&2`, `&113 / &50`];;
(* Lean: northwest_g_cover *)
let C1090AV_NORTHWEST_G_COVER = c1090av_central (false, false, true) 1 C1090AC_REFLECTYG 7 [0; 2; 3]
  [`&1`, `&12 / &5`; `&87 / &50`, `&2`; `&87 / &50`, `&3`];;
(* Lean: bottom_f_cover *)
let C1090AV_BOTTOM_F_COVER = c1090av_wall (true, false, false) 0 C1090AC_SWAPGF 9 [0; 1; 3]
  [`&8 / &5`, `&1`; `&2`, `&87 / &50`; `&12 / &5`, `&1`];;
(* Lean: top_f_cover *)
let C1090AV_TOP_F_COVER = c1090av_wall (true, false, true) 0 C1090AC_SWAPYGF 11 [0; 1; 3]
  [`&8 / &5`, `&3`; `&2`, `&113 / &50`; `&12 / &5`, `&3`];;
(* Lean: right_g_cover *)
let C1090AV_RIGHT_G_COVER = c1090av_wall (false, true, false) 1 RO_REFLECTXG 10 [0; 1; 3]
  [`&113 / &50`, `&2`; `&3`, `&8 / &5`; `&3`, `&12 / &5`];;
