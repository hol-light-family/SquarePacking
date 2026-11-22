(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976/ActualEnding.lean              *)
(* (namespace N12Compact.Completion.OtherCases.C976.OriginalData).          *)
(* The actual C976 family supplies every field of its continuous ending.     *)
(* owners p i is the owner of mask EL i c976od_masks, written with the       *)
(* literal mask (owners 0..11 = masks 1,2,12,48,192,256,512,1024,6144,8192,  *)
(* 16384,32768); as a family q : Fin 12 -> OpenSquare (C976.Data =           *)
(* c976mlao_data) it is qc = \i. ooc c1 c2 a b l (EL i c976od_masks), ...,   *)
(* qa = \i. l (c976ae_owners).  C974976Central.top_origin / southeast_g6 /   *)
(* southeast_lower / bottom_origin / EndingInput = CC974O_TOP_ORIGIN /       *)
(* CC974C_SOUTHEAST_G6 / CC974O_SOUTHEAST_LOWER / CC974O_BOTTOM_ORIGIN /     *)
(* cc974c_ending; F4PointTransfers.horizontal_original =                     *)
(* OCF4PT_HORIZONTAL_ORIGINAL; C976.impossible = C976RE_IMPOSSIBLE.          *)
(* Tag C976AE_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C976_EarlyGeometry.ml";;
needs "n12/geometry/CP_OtherCases_C976_ResidualEnding.ml";;
needs "n12/geometry/CP_CommonCases_C974976Origins.ml";;
needs "n12/geometry/CP_OtherCases_F4PointTransfers.ml";;

let C976AE_P = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let c976ae_own m =
  map (fun f -> list_mk_comb(f, C976AE_P @ [mk_small_numeral m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let c976ae_in m x y = list_mk_comb(`linside`, c976ae_own m @ [x; y]);;
let c976ae_stmt concl = list_mk_forall(C976AE_P,
  mk_imp(`NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c976od_family`, concl));;

(* add the conclusion of a theorem  !c1 c2 a b l. NPACK .. /\ IMAGE .. ==> P  *)
let C976AE_HAVE th = MP_TAC(SPEC_ALL th) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC];;

let C976AE_LDISJ_TAC (asl, w as g) =
  let f, args = strip_comb w in
  if f <> `ldisj` then failwith "C976AE_LDISJ_TAC" else
  let m = dest_small_numeral (rand (el 0 args)) and n = dest_small_numeral (rand (el 5 args)) in
  (MP_TAC (SPEC_ALL (oo_apart `c976od_family` m n)) THEN ASM_REWRITE_TAC[]) g;;

let C976AE_SIDE_TAC =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; REFL_TAC; C976AE_LDISJ_TAC;
         DISCH_TAC THEN C976E_CLASH_TAC; RASM_ARITH_TAC];;

(* Lean: top_origin *)
let C976AE_TOP_ORIGIN = prove
 (c976ae_stmt (c976ae_in 32768 `&2` `&3`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C976EG_FIXED_TAC THEN
  C976EG_OWNER_TAC 6144 THEN C976EG_OWNER_TAC 32768 THEN C976EG_OWNER_TAC 192 THEN
  C976EG_SV `&87 / &50` THEN C976AE_HAVE C976EG_TOP_PAIR THEN
  MP_TAC(SPECL (c976ae_own 6144 @ c976ae_own 32768 @ c976ae_own 192) CC974O_TOP_ORIGIN) THEN
  ANTS_TAC THENL [C976AE_SIDE_TAC; SIMP_TAC[]]);;

(* Lean: ending_input *)
let C976AE_ENDING_INPUT = prove
 (c976ae_stmt (list_mk_comb(`cc974c_ending`, c976ae_own 512 @ c976ae_own 1024)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C976EG_FIXED_TAC THEN
  C976AE_HAVE C976EG_SELECTION_INPUT THEN C976AE_HAVE C976AE_TOP_ORIGIN THEN
  REWRITE_TAC[cc974c_ending] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST
   [DISCH_TAC THEN C976E_CLASH_TAC;
    X_GEN_TAC `y:real` THEN REPEAT DISCH_TAC THEN
    MP_TAC(SPEC_ALL C976EG_RIGHT_BAR) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    C976E_CLASH_TAC]);;

(* Lean: southeast_g6 *)
let C976AE_SOUTHEAST_G6 = prove
 (c976ae_stmt (c976ae_in 512 `&113 / &50` `&2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C976EG_FIXED_TAC THEN
  C976EG_OWNER_TAC 512 THEN C976EG_OWNER_TAC 1024 THEN C976AE_HAVE C976AE_ENDING_INPUT THEN
  MP_TAC(SPECL (c976ae_own 512 @ c976ae_own 1024) CC974C_SOUTHEAST_G6) THEN
  ANTS_TAC THENL [C976AE_SIDE_TAC; SIMP_TAC[]]);;

(* Lean: southeast_east *)
let C976AE_SOUTHEAST_EAST = prove
 (c976ae_stmt (c976ae_in 512 `&5 / &2` `&2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C976EG_FIXED_TAC THEN
  C976EG_OWNER_TAC 512 THEN C976AE_HAVE C976AE_SOUTHEAST_G6 THEN
  SUBGOAL_THEN (c976ae_in 8192 `&5 / &2` `&1`) ASSUME_TAC THENL
   [MP_TAC(SPEC_ALL C976EG_BOTTOM_REACH) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `&5 / &2` o CONJUNCT2) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL (c976ae_own 512) OCF4PT_HORIZONTAL_ORIGINAL) THEN
  ANTS_TAC THENL [C976AE_SIDE_TAC; SIMP_TAC[]]);;

(* Lean: southeast_lower *)
let C976AE_SOUTHEAST_LOWER = prove
 (c976ae_stmt (c976ae_in 512 `&3` `&3 / &2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C976EG_FIXED_TAC THEN
  C976EG_OWNER_TAC 512 THEN C976EG_OWNER_TAC 1024 THEN
  C976AE_HAVE C976AE_ENDING_INPUT THEN C976AE_HAVE C976AE_SOUTHEAST_G6 THEN
  MP_TAC(SPECL (c976ae_own 512 @ c976ae_own 1024) CC974O_SOUTHEAST_LOWER) THEN
  ANTS_TAC THENL [C976AE_SIDE_TAC; SIMP_TAC[]]);;

(* Lean: bottom_origin *)
let C976AE_BOTTOM_ORIGIN = prove
 (c976ae_stmt (c976ae_in 8192 `&2` `&1`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C976EG_FIXED_TAC THEN
  C976EG_OWNER_TAC 8192 THEN C976EG_OWNER_TAC 12 THEN C976EG_OWNER_TAC 512 THEN
  C976AE_HAVE C976AE_SOUTHEAST_LOWER THEN
  MP_TAC(SPECL (c976ae_own 8192 @ c976ae_own 12 @ c976ae_own 512) CC974O_BOTTOM_ORIGIN) THEN
  ANTS_TAC THENL [C976AE_SIDE_TAC; SIMP_TAC[]]);;

(* Lean: owners p, as the five coordinate functions *)
let c976ae_owners = map (fun f -> mk_abs(`i:num`, list_mk_comb(f, C976AE_P @ [`EL i c976od_masks`])))
  [`ooc`; `oos`; `oou`; `oov`] @ [`\i:num. (l:real)`];;
let C976AE_EL_CONV = REWRITE_CONV[c976od_masks] THENC ONCE_DEPTH_CONV EL_CONV;;

(* the OpenSquare unit normals of owners p *)
let C976AE_UNIT = prove
 (c976ae_stmt (subst (zip c976ae_owners C976AO_Q) C976AO_UNIT),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[OO_UNIT]);;

(* Lean: actual_data *)
let C976AE_ACTUAL_DATA = prove
 (c976ae_stmt (list_mk_comb(`c976mlao_data`, c976ae_owners)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C976EG_FIXED_TAC THEN
  C976EG_SH `&28 / &25` THEN C976EG_SH `&87 / &50` THEN
  C976EG_SV `&8 / &5` THEN C976EG_SV `&87 / &50` THEN
  C976AE_HAVE C976EG_SOUTHWEST_WEST THEN C976AE_HAVE C976EG_SOUTHWEST_SOUTH THEN
  C976AE_HAVE C976AE_SOUTHEAST_G6 THEN C976AE_HAVE C976EG_NORTHEAST_G7 THEN
  C976AE_HAVE C976AE_BOTTOM_ORIGIN THEN C976AE_HAVE C976EG_TOP_PAIR THEN
  C976AE_HAVE C976EG_NORTHEAST_F7 THEN C976AE_HAVE C976AE_SOUTHEAST_EAST THEN
  REWRITE_TAC[c976mlao_data; c976ao_data] THEN REPEAT CONJ_TAC THEN
  FIRST
   [GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    ASM_SIMP_TAC[C976OD_BOX] THEN NO_TAC;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (SPECL (C976AE_P @ [`i:num`; `j:num`]) C976OD_APART) THEN
    ASM_REWRITE_TAC[ldisj] THEN NO_TAC;
    CONV_TAC C976AE_EL_CONV THEN ASM_REWRITE_TAC[] THEN NO_TAC]);;

(* Lean: impossible *)
let C976AE_IMPOSSIBLE = prove
 (c976ae_stmt `false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C976AE_UNIT) THEN MP_TAC(SPEC_ALL C976AE_ACTUAL_DATA) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC (SPECL c976ae_owners C976RE_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]);;
