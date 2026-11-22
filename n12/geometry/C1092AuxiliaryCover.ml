(* ========================================================================= *)
(* Phase 2: Compact/Bridge/C1092AuxiliaryCover.lean (Lean header: "not yet   *)
(* elaborated").  Original C1092 auxiliary covering consequences.            *)
(* Conventions of C1092WallCycle.ml / OwnerTransport.ml / ContextTransport.ml:*)
(* owners p i is the OriginalOwners 5-tuple at mask EL i c1092wc_code;       *)
(* natAuxOwners p k (ownerIndex p m) is auxown k (c1 (oidx .. m)) .. l;      *)
(* a Transform is (sw, rx, ry), g.apply x y is (c1092ct_apx g x y,           *)
(* c1092ct_apy g x y), ownerAction is c1092ws_owner_action.  The Lean        *)
(* DirectSingleDomains single979_5_1 / single979_8_1 are the dsd records of  *)
(* Cases_C979_EntryQueryChunks_Chunk11/17.ml; the private rebase (only the   *)
(* two budget equalities are re-checked for the new family) is the re-check  *)
(* sodt_checked `c1092wc_family` 1 w (which re-checks the budget equalities  *)
(* for c1092wc_family and reuses the same kernel-checked query refutations). *)
(* w.allowed is the literal allowed list.  Tag C1092AC_.                     *)
(* ========================================================================= *)

needs "n12/geometry/C1092WallSymmetry.ml";;
needs "n12/geometry/Cases_C979_EntryQueryChunks_Chunk11.ml";;
needs "n12/geometry/Cases_C979_EntryQueryChunks_Chunk17.ml";;

let C1092AC_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let c1092ac_owner i =
  let m = mk_comb(mk_comb(`EL:num->num list->num`, mk_small_numeral i), `c1092wc_code`) in
  map (fun f -> list_mk_comb(f, C1092AC_VARS @ [m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let c1092ac_in tl (x, y) = list_mk_comb(`linside`, tl @ [x; y]);;
let c1092ac_hyp = `NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family`;;
let c1092ac_stmt body = list_mk_forall(C1092AC_VARS, mk_imp(c1092ac_hyp, body));;

(* the domain theorem: MEM (natAuxOwners p 1 (ownerIndex p (ownerCode i))) w.allowed *)
let c1092ac_domain i w =
  let h = sodt_checked `c1092wc_family` 1 w in
  let al = rand (concl h) in
  let m = mk_comb(mk_comb(`EL:num->num list->num`, mk_small_numeral i), `c1092wc_code`) in
  let ix = list_mk_comb(`oidx`, C1092AC_VARS @ [m]) in
  let aux = list_mk_comb(`auxown 1`, map (fun f -> mk_comb(f, ix)) [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`] @ [`l:real`]) in
  prove(c1092ac_stmt (mk_comb(mk_comb(`MEM:(num->bool)->(num->bool)list->bool`, aux), al)),
    REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C1092WC_CODE_EL.(i)] THEN
    MATCH_MP_TAC HDOM_OWNER THEN EXISTS_TAC `c1092wc_family` THEN
    ASM_REWRITE_TAC[h; in_fam w.dmask `c1092wc_family`]);;

(* Lean: southwest_g_domain *)
let C1092AC_SOUTHWEST_G_DOMAIN = c1092ac_domain 4 c979eqc11_single979_5_1;;

(* Lean: left_g_domain *)
let C1092AC_LEFT_G_DOMAIN = c1092ac_domain 8 c979eqc17_single979_8_1;;

(* a cover by three auxiliary G points (kind 1) j0 j1 j2 of owner i *)
let c1092ac_cover i dom js pts =
  let tl = c1092ac_owner i in
  let body = list_mk_disj (map (c1092ac_in tl) pts) in
  let aux = lhand (rand (snd (strip_forall (concl dom)))) in
  let m = mk_small_numeral (dest_small_numeral (rhs (concl C1092WC_CODE_EL.(i)))) in
  prove(c1092ac_stmt body,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP dom) THEN
    REWRITE_TAC[C1092WC_CODE_EL.(i)] THEN
    REWRITE_TAC(map (fun j -> SPECL (C1092AC_VARS @ [m]) (oo_auxk_point 1 j)) js) THEN
    SPEC_TAC(subst [m, mk_comb(mk_comb(`EL:num->num list->num`, mk_small_numeral i), `c1092wc_code`)] aux,
             `s:num->bool`) THEN
    GEN_TAC THEN REWRITE_TAC[MEM] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH_EQ]);;

(* Lean: southwest_g_cover *)
let C1092AC_SOUTHWEST_G_COVER = c1092ac_cover 4 C1092AC_SOUTHWEST_G_DOMAIN [0; 2; 3]
  [`&1`, `&8 / &5`; `&87 / &50`, `&1`; `&87 / &50`, `&2`];;

(* Lean: left_g_cover *)
let C1092AC_LEFT_G_COVER = c1092ac_cover 8 C1092AC_LEFT_G_DOMAIN [0; 1; 3]
  [`&1`, `&8 / &5`; `&1`, `&12 / &5`; `&87 / &50`, `&2`];;

(* transport of a cover of owner i through an arbitrary container symmetry g *)
let c1092ac_transported i cover pts =
  let act = mk_comb(mk_comb(`c1092ws_owner_action`, `g:bool#bool#bool`), mk_small_numeral i) in
  let m = mk_comb(mk_comb(`EL:num->num list->num`, act), `c1092wc_code`) in
  let tl = map (fun f -> list_mk_comb(f, C1092AC_VARS @ [m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`] in
  let ap (x, y) = (list_mk_comb(`c1092ct_apx (g:bool#bool#bool)`, [x; y]), list_mk_comb(`c1092ct_apy (g:bool#bool#bool)`, [x; y])) in
  let body = list_mk_disj (map (fun p -> c1092ac_in tl (ap p)) pts) in
  let dv = [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`] in
  prove(mk_forall(`g:bool#bool#bool`, c1092ac_stmt body),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `exists d1 d2 e1 e2. c1092ot_pk g (c1,c2,a,b) = (d1,d2,e1,e2)` STRIP_ASSUME_TAC THENL
     [MESON_TAC[PAIR]; ALL_TAC] THEN
    MP_TAC(SPECL (dv @ [`l:real`]) cover) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[C1092OT_NPACK; C1092OT_FAMILY_TRANSPORT]; ALL_TAC] THEN
    MP_TAC(SPECL ([`g:bool#bool#bool`] @ C1092AC_VARS @ dv @ [mk_small_numeral i]) C1092OT_OWNERS_TRANSPORT) THEN
    ASM_REWRITE_TAC[ARITH] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP C1092CT_INSIDE_PULL th]));;

(* Lean: central_cover_transported *)
let C1092AC_CENTRAL_COVER_TRANSPORTED = c1092ac_transported 4 C1092AC_SOUTHWEST_G_COVER
  [`&1`, `&8 / &5`; `&87 / &50`, `&1`; `&87 / &50`, `&2`];;

(* Lean: wall_cover_transported *)
let C1092AC_WALL_COVER_TRANSPORTED = c1092ac_transported 8 C1092AC_LEFT_G_COVER
  [`&1`, `&8 / &5`; `&1`, `&12 / &5`; `&87 / &50`, `&2`];;

(* a concrete transported cover: owner i, transform g, points *)
let c1092ac_concrete th g i pts =
  let body = list_mk_disj (map (c1092ac_in (c1092ac_owner i)) pts) in
  prove(c1092ac_stmt body,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (SPEC g th)) THEN
    REWRITE_TAC[c1092ws_owner_action; c1092ct_apx; c1092ct_apy; LET_DEF; LET_END_DEF; FST; SND] THEN
    REWRITE_TAC C1092WS_LOOKUPS THEN REPEAT(CHANGED_TAC(REWRITE_TAC C1092WS_LOOKUPS)) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN MESON_TAC[]);;

(* Lean: northwest_f_cover *)
let C1092AC_NORTHWEST_F_COVER = c1092ac_concrete C1092AC_CENTRAL_COVER_TRANSPORTED `(true,false,true)` 7
  [`&1`, `&113 / &50`; `&8 / &5`, `&3`; `&2`, `&113 / &50`];;

(* Lean: northwest_g_cover *)
let C1092AC_NORTHWEST_G_COVER = c1092ac_concrete C1092AC_CENTRAL_COVER_TRANSPORTED `(false,false,true)` 7
  [`&1`, `&12 / &5`; `&87 / &50`, `&2`; `&87 / &50`, `&3`];;

(* Lean: northeast_f_cover *)
let C1092AC_NORTHEAST_F_COVER = c1092ac_concrete C1092AC_CENTRAL_COVER_TRANSPORTED `(true,true,true)` 6
  [`&2`, `&113 / &50`; `&12 / &5`, `&3`; `&3`, `&113 / &50`];;

(* Lean: northeast_g_cover *)
let C1092AC_NORTHEAST_G_COVER = c1092ac_concrete C1092AC_CENTRAL_COVER_TRANSPORTED `(false,true,true)` 6
  [`&113 / &50`, `&2`; `&113 / &50`, `&3`; `&3`, `&12 / &5`];;

(* Lean: top_f_cover *)
let C1092AC_TOP_F_COVER = c1092ac_concrete C1092AC_WALL_COVER_TRANSPORTED `(true,false,true)` 11
  [`&8 / &5`, `&3`; `&2`, `&113 / &50`; `&12 / &5`, `&3`];;

(* Lean: right_g_cover *)
let C1092AC_RIGHT_G_COVER = c1092ac_concrete C1092AC_WALL_COVER_TRANSPORTED `(false,true,false)` 10
  [`&113 / &50`, `&2`; `&3`, `&8 / &5`; `&3`, `&12 / &5`];;

(* Lean: southeast_g_cover *)
let C1092AC_SOUTHEAST_G_COVER = c1092ac_concrete C1092AC_CENTRAL_COVER_TRANSPORTED `(false,true,false)` 5
  [`&113 / &50`, `&1`; `&113 / &50`, `&2`; `&3`, `&8 / &5`];;
