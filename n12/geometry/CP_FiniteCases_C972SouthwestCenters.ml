(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C972SouthwestCenters.lean          *)
(* (namespace N12Compact.FiniteCases.C972).  Conditional actual SW-center    *)
(* producers.  owners p i = owner of mask EL i c972o_masks, written with the *)
(* literal mask (owners 0..11 = masks 1,2,12,48,192,256,512,1024,2048,4096,  *)
(* 8192,16384).  A Lean OpenSquare A is cA sA uA vA aA with its unit normal *)
(* and positive side explicit; Normal = c977cc_normal.  A.translated dx dy   *)
(* is (c, s, u - (c dx + s dy), v - (--s dx + c dy), a) (FC972SNH_TRANSLATED)*)
(* pullSwap q = (s, c, u, --v - a, a) (LINSIDE_PULLSW, LCONT_PULLSW);        *)
(* turnFrame^3 (pullSwap q) = (c, --s, v, u, a) (C972SWC_Q_INSIDE).          *)
(* SouthwestNegativeCorner.point = SNC_POINT; fixed = C972CS_FIXED;          *)
(* singleton_horizontal / vertical = C972O_SINGLETON_*; one_corner_of_       *)
(* northeast_origin = C972NH_*, zero_corner_of_southeast_halfpoint =         *)
(* C972MC_*.  The private negative_center / positive_center are inlined     *)
(* (C972SWC_CENTER_TAC).  Tag C972SWC_.                                      *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C972NorthwestHalfpoint.ml";;
needs "n12/geometry/CP_FiniteCases_C972SoutheastNegativeHalfpoint.ml";;
needs "n12/geometry/SouthwestNegativeCorner.ml";;

(* Lean: turnFrame (turnFrame (turnFrame (pullSwap A))) inside (qc, qs, qi) *)
let C972SWC_Q_INSIDE = prove
 (`forall c s u v a x y. linside c (--s) v u a x y <=> linside c s u v a y x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let C972SWC_SHIFT = REAL_ARITH `forall x. &2 + (x + --(&2)) = x`;;

let C972SWC_A = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`];;
(* A.translated (-2) (-2) *)
let C972SWC_G = [`cA:real`; `sA:real`; `uA - (cA * --(&2) + sA * --(&2))`;
                 `vA - (--sA * --(&2) + cA * --(&2))`; `aA:real`];;
let C972SWC_ACTUAL =
  `forall x y. linside cA sA uA vA aA x y <=>
         linside (ooc c1 c2 a b l 256) (oos c1 c2 a b l 256) (oou c1 c2 a b l 256)
                 (oov c1 c2 a b l 256) l (&2 + x) (&2 + y)`;;
let c972swc_stmt hyp normal =
  list_mk_forall(C972MC_V5 @ C972SWC_A,
    mk_imp(list_mk_conj [C972MC_NP; C972MC_IMG; hyp; `cA * cA + sA * sA = &1`; `&0 < aA`;
                         normal; `aA:real = l`; C972SWC_ACTUAL],
           `linside cA sA uA vA aA (&0) (&0)`));;

let c972swc_swap t = match t with
    [c; s; u; v; a] -> [s; c; u; mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, v)) a; a]
  | _ -> failwith "c972swc_swap";;

(* actual G:  !x y. linside G x y <=> owner 256 x y *)
let C972SWC_ACTUAL_G = prove
 (mk_imp(C972SWC_ACTUAL,
    `forall x y. linside cA sA (uA - (cA * --(&2) + sA * --(&2))) (vA - (--sA * --(&2) + cA * --(&2))) aA x y <=>
           linside (ooc c1 c2 a b l 256) (oos c1 c2 a b l 256) (oou c1 c2 a b l 256)
                   (oov c1 c2 a b l 256) l x y`),
  DISCH_TAC THEN ASM_REWRITE_TAC[FC972SNH_TRANSLATED; C972SWC_SHIFT]);;

(* common part: instantiate SNC_POINT, rewrite to owner points, discharge, conclude *)
let C972SWC_CENTER_TAC sncth extra =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C972SWC_ACTUAL_G) THEN
  MP_TAC(SPEC_ALL C972CS_SOUTHWEST_WEST) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972CS_SOUTHWEST_SOUTH) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C972CS_FIXED_TAC THEN C972CS_OWNER_TAC 1 THEN C972CS_OWNER_TAC 2 THEN
  C972CS_SH `&28 / &25` THEN C972CS_SH `&87 / &50` THEN
  C972CS_SV `&28 / &25` THEN C972CS_SV `&87 / &50` THEN
  MAP_EVERY (fun (m, p) -> MP_TAC (c972mc_seed m p) THEN DISCH_TAC)
    [1, (`&1`, `&457 / &500`); 2, (`&457 / &500`, `&1`)] THEN
  extra THEN
  MP_TAC sncth THEN
  FIRST_X_ASSUM(fun th -> if is_forall (concl th) &&
      (match strip_comb (lhs (snd (strip_forall (concl th)))) with
         (_, args) -> length args = 7 && el 2 args = el 2 C972SWC_G | _ -> false)
    then REWRITE_TAC[ldisj; LINSIDE_PULLSW; C972SWC_Q_INSIDE; th] else NO_TAC) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
           REWRITE_TAC[REAL_NEG_NEG] THEN FIRST_ASSUM ACCEPT_TAC;
           MATCH_MP_TAC LCONT_PULLSW THEN FIRST_ASSUM ACCEPT_TAC;
           REWRITE_TAC (map (fun (m, n) -> c972mc_apart m n) [1, 256; 256, 2; 2, 256; 256, 1]) THEN NO_TAC;
           DISCH_TAC THEN C972CS_CLASH_TAC;
           RASM_ARITH_TAC];
    DISCH_TAC] THEN
  FIRST_ASSUM(fun th -> if concl th = C972SWC_ACTUAL then ONCE_REWRITE_TAC[th] else NO_TAC) THEN
  CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN FIRST_ASSUM ACCEPT_TAC;;

(* Lean: negative_center (private) + southwest_negative_center_of_northeast_origin *)
let C972SWC_SOUTHWEST_NEGATIVE_CENTER_OF_NORTHEAST_ORIGIN = prove
 (c972swc_stmt (c972mc_own 1024 `&2` `&3`) `c977cc_normal cA (--sA)`,
  C972SWC_CENTER_TAC
    (SPECL (c972mc_tuple 1 @ C972SWC_G @ c972mc_tuple 2 @ [`--sA:real`]) SNC_POINT)
    (MP_TAC(SPEC_ALL C972NH_ONE_CORNER_OF_NORTHEAST_ORIGIN) THEN ASM_REWRITE_TAC[] THEN
     DISCH_TAC));;

(* Lean: positive_center (private) + southwest_positive_center_of_southeast_halfpoint *)
let C972SWC_SOUTHWEST_POSITIVE_CENTER_OF_SOUTHEAST_HALFPOINT =
  let q = match C972SWC_G with
      [c; s; u; v; a] -> [c; mk_comb(`(--):real->real`, s); v; u; a]
    | _ -> failwith "q" in
  prove
   (c972swc_stmt (c972mc_own 512 `&3` `&3 / &2`) `c977cc_normal cA sA`,
    C972SWC_CENTER_TAC
      (SPECL (c972swc_swap (c972mc_tuple 2) @ q @ c972swc_swap (c972mc_tuple 1) @ [`sA:real`]) SNC_POINT)
      (MP_TAC(SPEC_ALL C972MC_ZERO_CORNER_OF_SOUTHEAST_HALFPOINT) THEN ASM_REWRITE_TAC[] THEN
       DISCH_TAC));;
