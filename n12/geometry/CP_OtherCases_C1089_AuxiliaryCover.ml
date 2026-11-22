(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C1089/AuxiliaryCover.lean          *)
(* (N12Compact.Completion.OtherCases.C1089.AuxiliaryCover; Lean header:      *)
(* "Source-only; these declarations have not been compiled").  Direct reuse *)
(* of the central-G and wall-G certificates single979_5_1 / single979_8_1    *)
(* (Cases_C979_EntryQueryChunks_Chunk11/17.ml) on the actual C1089 packing,  *)
(* following the C1090 port (CP_OtherCases_C1090_AuxiliaryCover{Transport,}.ml).*)
(* Conventions of OriginalData.ml: family / masks = c1089sc_family /         *)
(* c1089sc_masks; owners p i is the owner tuple at mask EL i c1089sc_masks.  *)
(* A Transform is the triple (sw, rx, ry); t.pull q is pull_params           *)
(* (gen_bridge.ml), whose inside is q's inside at the transformed point      *)
(* (pull_point_eq); Transform.applyRat is c1092ct_apx / c1092ct_apy.         *)
(* A Fin 10 permutation is the list of its values.                          *)
(* transported_cover / central_cover / wall_cover quantify over w, t, kind,  *)
(* perm, i with decidable side conditions (candidate, budget interval,       *)
(* cover, points, mask, ordinary); they are producers that check these       *)
(* conditions at literal data and return the theorem                         *)
(*   |- !c1 c2 a b l. NPACK .. /\ IMAGE .. = c1089sc_family                  *)
(*        ==> linside (t.pull (owners p i)) (aux 1 a) \/ .. (aux 1 b) \/ .. (aux 1 c)  *)
(* The certificate's refutations are re-proved by the kernel at the          *)
(* transformed points (dsb_transformed_actual); the host family case979      *)
(* (c979eqb_family) only supplies the checked budget equalities.             *)
(* RelaxedOwnerDomain.reflectXG / halfTurnPerm are RO_REFLECTXG /            *)
(* RO_HALFTURN; Equiv.refl is the identity list.  Tag C1089AC_.              *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_DirectSingleBudget.ml";;
needs "n12/geometry/CP_OtherCases_C1089_OriginalData.ml";;
needs "n12/geometry/Cases_C979_EntryQueryChunks_Chunk11.ml";;
needs "n12/geometry/Cases_C979_EntryQueryChunks_Chunk17.ml";;
needs "n12/geometry/ContextTransport.ml";;

let C1089AC_FAMILY_LIT = rhs (concl c1089sc_family);;

(* Lean: exemption_count (k = 0, 1) *)
let C1089AC_EXEMPTION_COUNT = map (fun k ->
  let th = card_exempt C1089AC_FAMILY_LIT k in
  REWRITE_RULE[GSYM c1089sc_family] th) [0; 1];;

(* Lean: mask_member (private) is C1089OD_MASK_MEMBER *)

let C1089AC_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;

(* the aux point (x, y) terms of EL j (AUXPTS k) *)
let c1089ac_pt k j =
  let th = (REWRITE_CONV[AUXPTS_EXPL.(k)] THENC ONCE_DEPTH_CONV EL_CONV)
             (mk_comb(mk_comb(`EL:num->(real^2)list->real^2`, mk_small_numeral j), mk_comb(`AUXPTS`, mk_small_numeral k))) in
  match dest_list (rand (rhs (concl th))) with [x; y] -> (x, y) | _ -> failwith "c1089ac_pt";;

(* Lean: transported_cover (producer at literal data) *)
let c1089ac_transported_cover w (ja, jb, jc) trf kind perm i =
  let m = el i C1089SC_MASKS in
  if mask_action trf w.dmask <> m then failwith "c1089ac: mask" else
  if rhs (concl (pklow_thm m kind)) <> `1` then failwith "c1089ac: ordinary" else
  if w.dlower > 1 || w.dupper < 2 then failwith "c1089ac: interval" else
  if exists (fun s -> not (mem ja s || mem jb s || mem jc s)) w.dallowed then failwith "c1089ac: cover" else
  let ta = dsb_transformed_actual `c979eqb_family` 1 kind w trf perm in
  let pkup = pkup_thm `c1089sc_family` m kind in
  let mt = mk_small_numeral m in
  let ix = list_mk_comb(`oidx`, C1089AC_VARS @ [mt]) in
  let sq = map (fun f -> mk_comb(f, ix)) [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`] in
  let aux = list_mk_comb(`auxown`, [mk_small_numeral kind] @ sq @ [`l:real`]) in
  let own = map (fun f -> list_mk_comb(f, C1089AC_VARS @ [mt])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`] in
  let ownel = map (fun f -> list_mk_comb(f, C1089AC_VARS @
                [mk_comb(mk_comb(`EL:num->num list->num`, mk_small_numeral i), `c1089sc_masks`)]))
                [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`] in
  let pulled = pull_params trf ownel in
  let pts = map (c1089ac_pt 1) [ja; jb; jc] in
  let body = list_mk_disj (map (fun (x, y) -> list_mk_comb(`linside`, pulled @ [x; y])) pts) in
  let eqs = map (pull_point_eq trf own) pts in
  let auxs = map (fun j -> SPECL (C1089AC_VARS @ [mt]) (oo_auxk_point kind (el j perm))) [ja; jb; jc] in
  let elm = (REWRITE_CONV[c1089sc_masks] THENC ONCE_DEPTH_CONV EL_CONV)
              (mk_comb(mk_comb(`EL:num->num list->num`, mk_small_numeral i), `c1089sc_masks`)) in
  prove(list_mk_forall(C1089AC_VARS,
          mk_imp(`NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1089sc_family`, body)),
    REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[elm] THEN
    SUBGOAL_THEN (let mt = rand (snd (strip_forall (concl ta))) in
                  mk_comb(mk_comb(rator (rator mt), aux), rand mt)) MP_TAC THENL
     [MATCH_MP_TAC ta THEN
      SUBGOAL_THEN (mk_eq(list_mk_comb(`ownmask`, sq @ [`l:real`]), mt)) ASSUME_TAC THENL
       [MATCH_MP_TAC OIDX_SPEC THEN EXISTS_TAC `c1089sc_family` THEN
        ASM_REWRITE_TAC[in_fam m `c1089sc_family`];
        ALL_TAC] THEN
      MP_TAC(SPECL (C1089AC_VARS @ [`c1089sc_family`; mk_small_numeral kind; ix]) PK_BUDGET) THEN
      ASM_REWRITE_TAC[OIDX_LT; ARITH; pklow_thm m kind; pkup] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC eqs THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC auxs THEN
    SPEC_TAC(aux, `s:num->bool`) THEN GEN_TAC THEN REWRITE_TAC[MEM] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH_EQ]);;

(* Lean: swapGF, swapXGF, swapYGF, swapXYGF, reflectYG (value lists) *)
let C1089AC_SWAPGF = [2;6;0;4;8;1;5;9;3;7];;
let C1089AC_SWAPXGF = [6;2;8;4;0;9;5;1;7;3];;
let C1089AC_SWAPYGF = [3;7;1;5;9;0;4;8;2;6];;
let C1089AC_SWAPXYGF = [7;3;9;5;1;8;4;0;6;2];;
let C1089AC_REFLECTYG = [1;0;4;3;2;7;6;5;9;8];;

(* the points theorems: for every j < 10, t.apply (aux 1 j) = aux k (perm j)  (a conjunction over j) *)
let c1089ac_points trf k perm =
  dsb_check_points trf 1 k perm;
  let mkb t = if t then `true` else `false` in
  let trft = let (s, x, y) = trf in mk_pair(mkb s, mk_pair(mkb x, mkb y)) in
  let one j =
    let (x, y) = c1089ac_pt 1 j and (x', y') = c1089ac_pt k (el j perm) in
    mk_conj(mk_eq(list_mk_icomb "c1092ct_apx" [trft; x; y], x'),
            mk_eq(list_mk_icomb "c1092ct_apy" [trft; x; y], y')) in
  prove(list_mk_conj (map one (0--9)),
    REWRITE_TAC[c1092ct_apx; c1092ct_apy; LET_DEF; LET_END_DEF] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: swapGF_points *)
let C1089AC_SWAPGF_POINTS = c1089ac_points (true, false, false) 0 C1089AC_SWAPGF;;
(* Lean: swapXGF_points *)
let C1089AC_SWAPXGF_POINTS = c1089ac_points (true, true, false) 0 C1089AC_SWAPXGF;;
(* Lean: swapYGF_points *)
let C1089AC_SWAPYGF_POINTS = c1089ac_points (true, false, true) 0 C1089AC_SWAPYGF;;
(* Lean: swapXYGF_points *)
let C1089AC_SWAPXYGF_POINTS = c1089ac_points (true, true, true) 0 C1089AC_SWAPXYGF;;
(* Lean: reflectYG_points *)
let C1089AC_REFLECTYG_POINTS = c1089ac_points (false, false, true) 1 C1089AC_REFLECTYG;;

(* Lean: central_cover (producer; points (1, 8/5), (87/50, 1), (87/50, 2) = G 0, 2, 3) *)
let c1089ac_central_cover trf kind perm i =
  c1089ac_transported_cover c979eqc11_single979_5_1 (0, 2, 3) trf kind perm i;;

(* Lean: wall_cover (producer; points (1, 8/5), (1, 12/5), (87/50, 2) = G 0, 1, 3) *)
let c1089ac_wall_cover trf kind perm i =
  c1089ac_transported_cover c979eqc17_single979_8_1 (0, 1, 3) trf kind perm i;;

let c1089ac_owner i =
  map (fun f -> list_mk_comb(f, C1089AC_VARS @
    [mk_comb(mk_comb(`EL:num->num list->num`, mk_small_numeral i), `c1089sc_masks`)]))
    [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;

(* the literal cover of owner i from a transported cover h (transform trf, source G points) *)
let c1089ac_cover producer trf kind perm i js pts =
  let h = producer trf kind perm i in
  let own = c1089ac_owner i in
  let body = list_mk_disj (map (fun (x, y) -> list_mk_comb(`linside`, own @ [x; y])) pts) in
  let eqs = map (fun j -> pull_point_eq trf own (c1089ac_pt 1 j)) js in
  prove(list_mk_forall(C1089AC_VARS,
          mk_imp(`NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1089sc_family`, body)),
    REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP h) THEN
    REWRITE_TAC eqs THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN MESON_TAC[]);;

let c1089ac_central = c1089ac_cover c1089ac_central_cover;;
let c1089ac_wall = c1089ac_cover c1089ac_wall_cover;;

(* Lean: southwest_f_cover *)
let C1089AC_SOUTHWEST_F_COVER = c1089ac_central (true, false, false) 0 C1089AC_SWAPGF 4 [0; 2; 3]
  [`&1`, `&87 / &50`; `&8 / &5`, `&1`; `&2`, `&87 / &50`];;
(* Lean: southwest_g_cover *)
let C1089AC_SOUTHWEST_G_COVER = c1089ac_central (false, false, false) 1 (0--9) 4 [0; 2; 3]
  [`&1`, `&8 / &5`; `&87 / &50`, `&1`; `&87 / &50`, `&2`];;
(* Lean: southeast_f_cover *)
let C1089AC_SOUTHEAST_F_COVER = c1089ac_central (true, true, false) 0 C1089AC_SWAPXGF 5 [0; 2; 3]
  [`&2`, `&87 / &50`; `&12 / &5`, `&1`; `&3`, `&87 / &50`];;
(* Lean: southeast_g_cover *)
let C1089AC_SOUTHEAST_G_COVER = c1089ac_central (false, true, false) 1 RO_REFLECTXG 5 [0; 2; 3]
  [`&113 / &50`, `&1`; `&113 / &50`, `&2`; `&3`, `&8 / &5`];;
(* Lean: northeast_f_cover *)
let C1089AC_NORTHEAST_F_COVER = c1089ac_central (true, true, true) 0 C1089AC_SWAPXYGF 6 [0; 2; 3]
  [`&2`, `&113 / &50`; `&12 / &5`, `&3`; `&3`, `&113 / &50`];;
(* Lean: northeast_g_cover *)
let C1089AC_NORTHEAST_G_COVER = c1089ac_central (false, true, true) 1 RO_HALFTURN 6 [0; 2; 3]
  [`&113 / &50`, `&2`; `&113 / &50`, `&3`; `&3`, `&12 / &5`];;
(* Lean: northwest_f_cover *)
let C1089AC_NORTHWEST_F_COVER = c1089ac_central (true, false, true) 0 C1089AC_SWAPYGF 7 [0; 2; 3]
  [`&1`, `&113 / &50`; `&8 / &5`, `&3`; `&2`, `&113 / &50`];;
(* Lean: northwest_g_cover *)
let C1089AC_NORTHWEST_G_COVER = c1089ac_central (false, false, true) 1 C1089AC_REFLECTYG 7 [0; 2; 3]
  [`&1`, `&12 / &5`; `&87 / &50`, `&2`; `&87 / &50`, `&3`];;
(* Lean: bottom_f_cover *)
let C1089AC_BOTTOM_F_COVER = c1089ac_wall (true, false, false) 0 C1089AC_SWAPGF 9 [0; 1; 3]
  [`&8 / &5`, `&1`; `&2`, `&87 / &50`; `&12 / &5`, `&1`];;
(* Lean: top_f_cover *)
let C1089AC_TOP_F_COVER = c1089ac_wall (true, false, true) 0 C1089AC_SWAPYGF 11 [0; 1; 3]
  [`&8 / &5`, `&3`; `&2`, `&113 / &50`; `&12 / &5`, `&3`];;
(* Lean: right_g_cover *)
let C1089AC_RIGHT_G_COVER = c1089ac_wall (false, true, false) 1 RO_REFLECTXG 10 [0; 1; 3]
  [`&113 / &50`, `&2`; `&3`, `&8 / &5`; `&3`, `&12 / &5`];;
(* Lean: left_g_cover *)
let C1089AC_LEFT_G_COVER = c1089ac_wall (false, false, false) 1 (0--9) 8 [0; 1; 3]
  [`&1`, `&8 / &5`; `&1`, `&12 / &5`; `&87 / &50`, `&2`];;
