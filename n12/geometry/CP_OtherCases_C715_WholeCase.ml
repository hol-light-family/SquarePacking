(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C715/WholeCase.lean.               *)
(* Whole original C715 exclusion.  owners p i is the OriginalOwners 5-tuple  *)
(* at mask EL i c715ri_owner_code (side l); ExcludesFamily family is         *)
(* excl_fam c715ri_family, ExcludesCase 715 is excl_case 715 (RowIdentity),  *)
(* and C715WC_EXCLUDED_ROW : |- EXCLUDED_ROW 396 is the assembly form.       *)
(* (auxPoints 2)[j]! is EL j (AUXPTS 2); ExactMarkers q (maskSupport m) is   *)
(* the marker equivalence of OO_MARKERS (k IN bitset m).  Tag C715WC_.       *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C715_Entrance.ml";;
needs "n12/geometry/CP_OtherCases_C715_FourPointEnding.ml";;
needs "n12/geometry/C715Segment.ml";;

let C715WC_F = `c715ri_family`;;
let C715WC_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let C715WC_HYP = `NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c715ri_family`;;

let C715WC_LIST = oo_list_facts C715WC_F (rand (concl c715ri_owner_code));;
let C715WC_LENGTH =
  (REWRITE_CONV[c715ri_owner_code; LENGTH] THENC NUM_REDUCE_CONV) `LENGTH c715ri_owner_code`;;

let C715WC_MEMBER = prove
 (`forall i. i < 12 ==> EL i c715ri_owner_code IN c715ri_family`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_LIST_MEMBER THEN
  REWRITE_TAC[C715WC_LENGTH; c715ri_owner_code] THEN ASM_REWRITE_TAC[fst C715WC_LIST]);;

(* Lean: owners (definition: the owner at ownerCode i) -- the 5-tuple below *)
let c715wc_own i =
  let m = mk_comb(mk_comb(`EL:num->(num)list->num`, i), `c715ri_owner_code`) in
  map (fun f -> list_mk_comb(f, C715WC_VARS @ [m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;

(* Lean: owner_code *)
let C715WC_OWNER_CODE = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c715ri_family /\ i < 12
     ==> ownmask (c1 (oidx c1 c2 a b l (EL i c715ri_owner_code))) (c2 (oidx c1 c2 a b l (EL i c715ri_owner_code)))
                 (a (oidx c1 c2 a b l (EL i c715ri_owner_code))) (b (oidx c1 c2 a b l (EL i c715ri_owner_code))) l =
         EL i c715ri_owner_code`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL (C715WC_VARS @ [C715WC_F; `EL i c715ri_owner_code`]) OO_CODE) THEN
  ASM_SIMP_TAC[C715WC_MEMBER]);;

(* Lean: owners_side  (the side of every owner is the common side l) *)
let C715WC_OWNERS_SIDE = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l ==> &1 < l`,
  REWRITE_TAC[OO_SIDE]);;

(* Lean: owners_markers *)
let C715WC_OWNERS_MARKERS = prove
 (mk_forall(`c1:num->real`, list_mk_forall([`c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`],
   mk_imp(`NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c715ri_family /\ i < 12`,
     mk_forall(`k:num`, mk_imp(`k < 16`,
       mk_eq(list_mk_comb(`linside`, c715wc_own `i:num` @ [`marker k$1`; `marker k$2`]),
             `k IN bitset (EL i c715ri_owner_code)`)))))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC OO_MARKERS THEN
  EXISTS_TAC C715WC_F THEN ASM_SIMP_TAC[C715WC_MEMBER]);;

(* Lean: owners_apart *)
let C715WC_OWNERS_APART = prove
 (mk_forall(`c1:num->real`, list_mk_forall([`c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`; `j:num`],
   mk_imp(`NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c715ri_family /\ i < 12 /\ j < 12 /\
           ~(EL i c715ri_owner_code = EL j c715ri_owner_code)`,
     list_mk_comb(`ldisj`, c715wc_own `i:num` @ c715wc_own `j:num`)))),
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_APART THEN EXISTS_TAC C715WC_F THEN
  ASM_SIMP_TAC[C715WC_MEMBER]);;

(* Lean: auxiliary_inside *)
let C715WC_AUXILIARY_INSIDE = prove
 (mk_forall(`c1:num->real`, list_mk_forall([`c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`; `j:num`],
   mk_imp(`j < 20 /\ j IN ooaux c1 c2 a b l (EL i c715ri_owner_code)`,
     list_mk_comb(`linside`, c715wc_own `i:num` @ [`EL j (AUXPTS 2)$1`; `EL j (AUXPTS 2)$2`])))),
  MESON_TAC[OO_AUX_EXACT]);;

(* Lean: southeast_corner  (owners p 2 = owner 12, seed point (3,1)) *)
let C715WC_SOUTHEAST_CORNER =
  let th = oo_inst C715WC_F (oo_seed 12 (`&3`, `&1`)) in
  prove(mk_forall(`c1:num->real`, list_mk_forall([`c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
          mk_imp(C715WC_HYP, list_mk_comb(`linside`, c715wc_own `2` @ [`&3`; `&1`])))),
        REWRITE_TAC[c715ri_owner_code] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
        REWRITE_TAC[th]);;

(* the owner tuple at a literal mask *)
let c715wc_m m =
  map (fun f -> list_mk_comb(f, C715WC_VARS @ [mk_small_numeral m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;

(* owner m at marker k (bitset m decided) *)
let c715wc_marker m k (x, y) =
  let goal = mk_imp(C715WC_HYP, list_mk_comb(`linside`, c715wc_m m @ [x; y])) in
  prove(goal,
    STRIP_TAC THEN
    MP_TAC(SPECL (C715WC_VARS @ [C715WC_F; mk_small_numeral m]) OO_MARKERS) THEN
    ASM_REWRITE_TAC[in_fam m C715WC_F] THEN
    DISCH_THEN(MP_TAC o SPEC (mk_small_numeral k)) THEN
    REWRITE_TAC[ARITH; bitset_bits m; IN_SET_OF_LIST; MEM; MARKER_EXPLICIT; VECTOR_2] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

(* Lean: family_excluded *)
let C715WC_FAMILY_EXCLUDED =
  let ap m n = UNDISCH (SPEC_ALL (oo_apart C715WC_F m n)) in
  let np = CONJUNCT1 (ASSUME C715WC_HYP) in
  let un m = SPEC (mk_small_numeral m) (MATCH_MP OO_UNIT np) in
  let side = MATCH_MP OO_SIDE np in
  let mse = UNDISCH (c715wc_marker 512 9 (`&47 / &20`, `&33 / &20`)) in
  let rmk = UNDISCH (c715wc_marker 17408 14 (`&1543 / &500`, `&2`)) in
  let corner = REWRITE_RULE[c715ri_owner_code]
                 (UNDISCH (SPEC_ALL C715WC_SOUTHEAST_CORNER)) in
  let corner = CONV_RULE (ONCE_DEPTH_CONV EL_CONV) corner in
  let body = prove(mk_imp(C715WC_HYP, `false`), DISCH_TAC THEN
    MP_TAC(UNDISCH (SPECL C715WC_VARS C715E_ACTUAL_COVER)) THEN
    REWRITE_TAC[c715e_cover_property; c715e_actual_vector; MAP] THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN BETA_TAC THEN
    REWRITE_TAC(map (fun j -> GSYM (oo_aux_point j)) [5; 6; 9; 16; 18]) THEN
    CONV_TAC(REWR_CONV(TAUT `~p <=> p ==> false`)) THEN STRIP_TAC THENL
     [(* first branch: g6 in owner 6 (512), g8 in owner 10 (17408) *)
      MP_TAC(SPECL (c715wc_m 17408) OCC715FPE_FOUR_POINT_ENDING) THEN
      ASM_REWRITE_TAC[un 17408; side] THEN
      MP_TAC(REWRITE_RULE[ldisj] (ap 17408 512)) THEN
      MP_TAC(REWRITE_RULE[ldisj] (ap 17408 32)) THEN
      ASM_MESON_TAC[];
      (* second branch: lower_points_foreign_square for owners 6 and 10 *)
      MATCH_MP_TAC(SPECL (c715wc_m 512 @ c715wc_m 17408) C715S_LOWER_POINTS_FOREIGN_SQUARE) THEN
      ASM_REWRITE_TAC[un 512; side; mse; rmk; ap 512 17408] THEN
      MP_TAC(REWRITE_RULE[ldisj] (ap 512 8192)) THEN
      MP_TAC(REWRITE_RULE[ldisj] (ap 512 12)) THEN
      MP_TAC corner THEN ASM_MESON_TAC[]]) in
  prove(`excl_fam c715ri_family`,
    REWRITE_TAC[excl_fam] THEN MESON_TAC[body]);;

(* Lean: whole_case *)
let C715WC_WHOLE_CASE = MP C715RI_EXCLUDES_CASE C715WC_FAMILY_EXCLUDED;;

(* for the assembly: |- EXCLUDED_ROW 396 *)
let C715WC_EXCLUDED_ROW = ri_excluded_row 396 C715WC_WHOLE_CASE;;
