(* ========================================================================= *)
(* Port of Compact/Bridge/C696CentralNormalForm.lean (namespace N12Compact.  *)
(* C696CentralNormalForm).  (Lean header: "Source only, uncompiled".)        *)
(* Center-first normalization of the original C696 packing.  Conventions of *)
(* C696CornerReach.ml / C696NextBottomWall.ml: owners p i is the owner of    *)
(* mask EL i c696ssp_owner_masks (5-tuple ooc .. l); frames A, O are         *)
(* cA sA uA vA aA etc. with unit normal and positive side (OpenSquare        *)
(* fields); Normal is c977cc_normal; shapes are aA = l etc.                  *)
(* Transforms (transport.ml, Phase 1): symmetry 0 = <false,true,true> is the *)
(* half-turn, whose pullPacking of (c1,c2,a,b,l) is the packing              *)
(* ((\i. 4 - c1 i), (\i. 4 - c2 i), a, b, l) (NPACK_RY then NPACK_RX);      *)
(* symmetry 1 = <true,false,false> is the diagonal reflection, pullPacking   *)
(* (c2, c1, b, a, l) (NPACK_SW).  Transform.apply is written out: (4-x,4-y)  *)
(* and (y, x).  The packing q of the existential statements keeps the side l *)
(* (stronger than Lean).  The private swapped frame is replaced by the frame *)
(* cA (--sA) vA uA aA (C696NBW_INSIDE_TRANSPOSE), which has the same Inside. *)
(* Data p A O is c696cnf_data (with the OpenSquare fields of A and O).       *)
(* ExcludesCase 696 is excl_case 696 (row 377, RowIdentity.ml).              *)
(* Tag C696CNF_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/C696PositiveBottomWest.ml";;
needs "n12/geometry/C696NextBottomWall.ml";;
needs "n12/geometry/RowIdentity.ml";;

(* Lean: symmetry, permutation *)
let c696cnf_symmetry = new_definition
 `c696cnf_symmetry : (bool#bool#bool)list = [(false,true,true); (true,false,false)]`;;
let c696cnf_permutation = new_definition
 `c696cnf_permutation : (num list)list =
    [[3;4;5;0;1;2;7;6;10;11;8;9]; [1;0;5;4;3;2;6;7;9;8;11;10]]`;;
let C696CNF_PERM = [[3;4;5;0;1;2;7;6;10;11;8;9]; [1;0;5;4;3;2;6;7;9;8;11;10]];;
let C696CNF_MASKS = [1; 2; 12; 16; 32; 192; 256; 1024; 4096; 8192; 16384; 32768];;

let C696CNF_OLD = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`];;
let C696CNF_PK = [| [`\i. &4 - (c1:num->real) i`; `\i. &4 - (c2:num->real) i`; `a:num->real`; `b:num->real`];
                    [`c2:num->real`; `c1:num->real`; `b:num->real`; `a:num->real`] |];;

(* owner of the packing pk (a list of four arrays, side l) at the mask term mt *)
let c696cnf_q pk mt = map (fun f -> list_mk_comb(f, pk @ [`l:real`; mt])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let c696cnf_in pk mt x y = list_mk_comb(`linside`, c696cnf_q pk mt @ [x; y]);;
let c696cnf_hyp pk = mk_conj(list_mk_comb(`NPACK`, pk @ [`l:real`]),
  mk_eq(mk_comb(`IMAGE binarysum`, list_mk_comb(`FFP`, pk @ [`l:real`])), `c696ssp_family`));;

(* the marker permutations of the generators *)
let c696cnf_gen th = rand (rator (rhs (snd (strip_forall (concl th)))));;
let C696CNF_PRX = c696cnf_gen OWNED_RX and C696CNF_PRY = c696cnf_gen OWNED_RY
and C696CNF_PSW = c696cnf_gen OWNED_SW;;
let c696cnf_image f s = mk_comb(mk_comb(`IMAGE:(num->num)->(num->bool)->num->bool`, f), s);;
(* the action on marker sets *)
let c696cnf_act k s =
  if k = 0 then c696cnf_image C696CNF_PRX (c696cnf_image C696CNF_PRY s) else c696cnf_image C696CNF_PSW s;;

(* the transformed packings: NPACK and FFP *)
let C696CNF_PK0 =
  let np = ASSUME `NPACK c1 c2 a b l` in
  let t1 = MATCH_MP NPACK_RY np in
  let t2 = MATCH_MP NPACK_RX (CONJUNCT1 t1) in
  let eq = TRANS (CONJUNCT2 t2) (AP_TERM (rator (rhs (concl (CONJUNCT2 t2)))) (CONJUNCT2 t1)) in
  GENL (C696CNF_OLD @ [`l:real`]) (DISCH `NPACK c1 c2 a b l` (CONJ (CONJUNCT1 t2) eq));;
let C696CNF_PKS = [| C696CNF_PK0; NPACK_SW |];;

(* owned of a moved square *)
let C696CNF_OWNED0 =
  let th1 = SPECL [`x:real`; `&4 - y`; `b:real`; `a:real`; `l:real`] OWNED_RX in
  let th2 = SPECL [`x:real`; `y:real`; `a:real`; `b:real`; `l:real`] OWNED_RY in
  GENL [`x:real`; `y:real`; `a:real`; `b:real`; `l:real`]
    (TRANS th1 (AP_TERM (rator (rhs (concl th1))) th2));;
let C696CNF_OWNEDS = [| C696CNF_OWNED0; OWNED_SW |];;

(* Lean: mask_symmetry (private):  |- binarysum (act k (bitset m0)) = m *)
let c696cnf_mask k m0 =
  let tm = mk_comb(`binarysum`, c696cnf_act k (mk_comb(`bitset`, mk_small_numeral m0))) in
  let th1 = (REWRITE_CONV[bitset_bits m0; GSYM SET_OF_LIST_MAP; MAP] THENC
             DEPTH_CONV BETA_CONV THENC DEPTH_CONV EL_CONV) tm in
  let l1 = dest_list (rand (rand (rhs (concl th1)))) in
  let m' = itlist (fun t acc -> acc + (1 lsl (dest_small_numeral t))) l1 0 in
  let eq = prove(mk_eq(rand (rhs (concl th1)), rand (lhand (concl (binarysum_bits m')))),
    REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM] THEN ARITH_TAC) in
  TRANS th1 (TRANS (AP_TERM `binarysum` eq) (binarysum_bits m'));;

(* Lean: family_symmetry (private) *)
let c696cnf_family_image k =
  let f = mk_abs(`m:num`, mk_comb(`binarysum`, c696cnf_act k `bitset m`)) in
  prove(mk_eq(mk_comb(mk_comb(`IMAGE:(num->num)->(num->bool)->num->bool`, f), `c696ssp_family`), `c696ssp_family`),
    REWRITE_TAC[c696ssp_family; IMAGE_CLAUSES] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC(map (c696cnf_mask k) C696CNF_MASKS) THEN CONV_TAC setlit_eq_dconv);;
let C696CNF_FAMILY_IMAGE = Array.init 2 c696cnf_family_image;;

let C696CNF_FFP_BITSET = prove
 (`forall c1 c2 a b l G. G IN FFP c1 c2 a b l ==> G = bitset (binarysum G)`,
  REWRITE_TAC[FFP; IN_IMAGE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM ownmask; OWNED_BITSET]);;

(* Lean: pulled_family  (k = 0, 1) *)
let c696cnf_pulled_family k =
  prove(list_mk_forall(C696CNF_OLD @ [`l:real`], mk_imp(C696SSP_HYP, c696cnf_hyp C696CNF_PK.(k))),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C696CNF_PKS.(k)) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM IMAGE_o] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM C696CNF_FAMILY_IMAGE.(k)] THEN
    FIRST_X_ASSUM(fun th -> if is_eq (concl th) && rhs (concl th) = `c696ssp_family`
                            then GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th] else NO_TAC) THEN
    REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ_ON THEN
    X_GEN_TAC `G:num->bool` THEN DISCH_TAC THEN REWRITE_TAC[o_THM; IMAGE_o] THEN
    REPEAT AP_TERM_TAC THEN MATCH_MP_TAC C696CNF_FFP_BITSET THEN ASM_MESON_TAC[]);;
let C696CNF_PULLED_FAMILY_K = Array.init 2 c696cnf_pulled_family;;
let C696CNF_PULLED_FAMILY = CONJ C696CNF_PULLED_FAMILY_K.(0) C696CNF_PULLED_FAMILY_K.(1);;

(* pulled_owner at a literal pair of masks *)
let c696cnf_owner_lit k (m, m0) =
  let pk = C696CNF_PK.(k) in
  let mt = mk_small_numeral m and m0t = mk_small_numeral m0 in
  let tm = list_mk_forall(C696CNF_OLD @ [`l:real`], mk_imp(C696SSP_HYP,
    mk_eq(list_mk_comb(`oidx`, pk @ [`l:real`; mt]), list_mk_comb(`oidx`, C696CNF_OLD @ [`l:real`; m0t])))) in
  prove(tm,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPEC_ALL C696CNF_PULLED_FAMILY_K.(k)) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC OWNMASK_INJ THEN
    MAP_EVERY EXISTS_TAC (pk @ [`l:real`]) THEN ASM_REWRITE_TAC[OIDX_LT] THEN
    MP_TAC(SPECL (pk @ [`l:real`; `c696ssp_family`; mt]) OIDX_SPEC) THEN
    ASM_REWRITE_TAC[in_fam m `c696ssp_family`] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ownmask] THEN ONCE_REWRITE_TAC[C696CNF_OWNEDS.(k)] THEN
    MP_TAC(SPECL (C696CNF_OLD @ [`l:real`; `c696ssp_family`; m0t]) OIDX_OWNED) THEN
    ASM_REWRITE_TAC[in_fam m0 `c696ssp_family`] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[c696cnf_mask k m0]);;

let c696cnf_el i lst = mk_comb(mk_comb(`EL:num->num list->num`, i), lst);;
let c696cnf_mt i = c696cnf_el i `c696ssp_owner_masks`;;
let c696cnf_pt k i =
  c696cnf_mt (c696cnf_el i (mk_comb(mk_comb(`EL:num->(num list)list->num list`, mk_small_numeral k),
                                    `c696cnf_permutation`)));;

(* Lean: pulled_owner  (k = 0, 1) *)
let c696cnf_pulled_owner k =
  let lits = map (fun i -> c696cnf_owner_lit k (el i C696CNF_MASKS, el (el i (el k C696CNF_PERM)) C696CNF_MASKS))
                 (0 -- 11) in
  prove(list_mk_forall(C696CNF_OLD @ [`l:real`], mk_imp(C696SSP_HYP,
      mk_forall(`i:num`, mk_imp(`i < 12`,
        mk_eq(list_mk_comb(`oidx`, C696CNF_PK.(k) @ [`l:real`; c696cnf_mt `i:num`]),
              list_mk_comb(`oidx`, C696CNF_OLD @ [`l:real`; c696cnf_pt k `i:num`])))))),
    REPEAT GEN_TAC THEN DISCH_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[c696ssp_owner_masks; c696cnf_permutation] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
    REPEAT CONJ_TAC THEN FIRST (map (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[]) lits));;
let C696CNF_PULLED_OWNER_K = Array.init 2 c696cnf_pulled_owner;;
let C696CNF_PULLED_OWNER = CONJ C696CNF_PULLED_OWNER_K.(0) C696CNF_PULLED_OWNER_K.(1);;

let C696CNF_HALFTURN_LINSIDE = prove
 (`forall a b c1 c2 l x y.
     linside a b (a * (&4 - c1) + b * (&4 - c2) - l / &2) (--b * (&4 - c1) + a * (&4 - c2) - l / &2) l x y <=>
     linside a b (a * c1 + b * c2 - l / &2) (--b * c1 + a * c2 - l / &2) l (&4 - x) (&4 - y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
let C696CNF_SWAP_LINSIDE = prove
 (`forall a b c1 c2 l x y.
     linside b a (b * c2 + a * c1 - l / &2) (--a * c2 + b * c1 - l / &2) l x y <=>
     linside a b (a * c1 + b * c2 - l / &2) (--b * c1 + a * c2 - l / &2) l y x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
let C696CNF_MOVE_LINSIDE = [| C696CNF_HALFTURN_LINSIDE; C696CNF_SWAP_LINSIDE |];;
let c696cnf_apply k x y = if k = 0 then (mk_binop `(-):real->real->real` `&4` x, mk_binop `(-):real->real->real` `&4` y)
                          else (y, x);;

(* Lean: pulled_inside  (k = 0, 1; Transform.apply written out) *)
let c696cnf_pulled_inside k =
  let x', y' = c696cnf_apply k `x:real` `y:real` in
  prove(list_mk_forall(C696CNF_OLD @ [`l:real`], mk_imp(C696SSP_HYP,
      list_mk_forall([`i:num`; `x:real`; `y:real`], mk_imp(`i < 12`,
        mk_eq(c696cnf_in C696CNF_PK.(k) (c696cnf_mt `i:num`) `x:real` `y:real`,
              c696cnf_in C696CNF_OLD (c696cnf_pt k `i:num`) x' y'))))),
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[ooc; oos; oou; oov] THEN
    MP_TAC(SPEC `i:num` (UNDISCH (SPEC_ALL C696CNF_PULLED_OWNER_K.(k)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SPEC_TAC(list_mk_comb(`oidx`, C696CNF_OLD @ [`l:real`; c696cnf_pt k `i:num`]), `j:num`) THEN
    GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [C696CNF_MOVE_LINSIDE.(k)] THEN REWRITE_TAC[]);;
let C696CNF_PULLED_INSIDE_K = Array.init 2 c696cnf_pulled_inside;;
let C696CNF_PULLED_INSIDE = CONJ C696CNF_PULLED_INSIDE_K.(0) C696CNF_PULLED_INSIDE_K.(1);;

(* Lean: pulled_side: the owners of both packings have side l (nothing to prove) *)

(* pulled_inside at a literal index i, with literal masks *)
let c696cnf_inside_at k i =
  let th = UNDISCH (SPEC_ALL C696CNF_PULLED_INSIDE_K.(k)) in
  let th1 = SPEC_ALL (SPEC (mk_small_numeral i) th) in
  let lt = EQT_ELIM (NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` (mk_small_numeral i) `12`)) in
  let th2 = CONV_RULE (REWRITE_CONV[c696ssp_owner_masks; c696cnf_permutation] THENC DEPTH_CONV EL_CONV)
              (MP th1 lt) in
  GENL (C696CNF_OLD @ [`l:real`]) (DISCH C696SSP_HYP (GENL [`x:real`; `y:real`] th2));;

let C696CNF_D = [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`];;

(* Lean: missing_center_cover *)
let C696CNF_MISSING_CENTER_COVER =
  let ia = c696cnf_inside_at 0 6 in
  prove
   (list_mk_forall(C696CNF_OLD @ [`l:real`], mk_imp(C696SSP_HYP,
      list_mk_exists(C696CNF_D, mk_conj(c696cnf_hyp C696CNF_D,
        mk_neg (c696cnf_in C696CNF_D `256` `&2` `&2`))))),
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    ASM_CASES_TAC (c696ck_oin 256 `&2` `&2`) THENL
     [MAP_EVERY EXISTS_TAC C696CNF_PK.(0) THEN
      MP_TAC(SPEC_ALL C696CNF_PULLED_FAMILY_K.(0)) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC_ALL ia) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
      MP_TAC(SPEC_ALL (oo_apart `c696ssp_family` 256 1024)) THEN ASM_REWRITE_TAC[ldisj] THEN
      DISCH_THEN(MP_TAC o SPECL [`&2`; `&2`]) THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC C696CNF_OLD THEN ASM_REWRITE_TAC[]]);;

(* Lean: nonnegative_central_cover (private) *)
let C696CNF_A = C696NBW_A;;
let c696cnf_frame_hyps d =
  [c696ow_unit C696CNF_A; c696ow_pos C696CNF_A; `c977cc_normal cA sA`; c696ow_shape C696CNF_A;
   list_mk_forall([`x:real`; `y:real`], mk_eq(c696ow_in C696CNF_A `x:real` `y:real`, c696cnf_in d `256` `x:real` `y:real`));
   mk_neg (c696cnf_in d `256` `&2` `&2`)];;
let C696CNF_NONNEGATIVE_CENTRAL_COVER =
  let ia = c696cnf_inside_at 1 6 in
  prove
   (list_mk_forall(C696CNF_OLD @ [`l:real`], mk_imp(mk_conj(C696SSP_HYP, mk_neg (c696ck_oin 256 `&2` `&2`)),
      list_mk_exists(C696CNF_D, mk_conj(c696cnf_hyp C696CNF_D,
        list_mk_exists(C696CNF_A, list_mk_conj (c696cnf_frame_hyps C696CNF_D)))))),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    C696NBW_CANONICAL_TAC 256 C696CNF_A THEN
    ASM_CASES_TAC `&0 <= sA` THENL
     [MAP_EVERY EXISTS_TAC C696CNF_OLD THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC C696CNF_A THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC C696PW_NORMAL_OF_CANONICAL THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC C696CNF_PK.(1) THEN
      MP_TAC(SPEC_ALL C696CNF_PULLED_FAMILY_K.(1)) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC_ALL ia) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`cA:real`; `--sA:real`; `vA:real`; `uA:real`; `aA:real`] THEN
      ASM_REWRITE_TAC[C696NBW_INSIDE_TRANSPOSE] THEN CONJ_TAC THENL
       [UNDISCH_TAC `cA * cA + sA * sA = &1` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC C696PBW_NEG_NORMAL THEN ASM_REWRITE_TAC[]]]);;

(* Lean: Data *)
let c696cnf_data = new_definition
 (let args = C696CNF_OLD @ [`l:real`] @ C696NBW_A @ C696NBW_O in
  mk_eq(list_mk_comb(mk_var("c696cnf_data", itlist (mk_fun_ty o type_of) args `:bool`), args),
   list_mk_conj
    [c696ow_unit C696NBW_A; c696ow_pos C696NBW_A; c696ow_unit C696NBW_O; c696ow_pos C696NBW_O;
     `c977cc_normal cA sA`; `&0 < sA`; c696ow_shape C696NBW_A; c696ow_equiv C696NBW_A 256;
     `&0 < cO`; `sO < &0`; `&1 / &5 < --sO`; `abs sO <= cO`; c696ow_shape C696NBW_O;
     c696ow_equiv C696NBW_O 1;
     mk_neg (c696ck_oin 256 `&2` `&2`); c696ck_oin 256 `&1` `&2`; c696ck_oin 2 `&1` `&1`;
     mk_neg (c696ck_oin 1 `&1` `&1`)]));;

(* cover on a packing with a nonnegative central frame (the body of Lean's cover) *)
let C696CNF_DATA_OF = prove
 (list_mk_forall(C696CNF_OLD @ [`l:real`], mk_imp(C696SSP_HYP,
    list_mk_forall(C696CNF_A, mk_imp(list_mk_conj
      [c696ow_unit C696CNF_A; c696ow_pos C696CNF_A; `c977cc_normal cA sA`; c696ow_shape C696CNF_A;
       c696ow_equiv C696CNF_A 256; mk_neg (c696ck_oin 256 `&2` `&2`)],
      list_mk_exists(C696NBW_O, list_mk_comb(`c696cnf_data`, C696CNF_OLD @ [`l:real`] @ C696CNF_A @ C696NBW_O)))))),
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (c696ck_oin 2 `&1` `&1`) ASSUME_TAC THENL
   [MP_TAC(SPEC_ALL C696CK_LEFT_CORNER) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL C696CNF_A) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN (mk_neg (c696ck_oin 1 `&1` `&1`)) ASSUME_TAC THENL
   [MP_TAC(SPEC_ALL (oo_apart `c696ssp_family` 1 2)) THEN ASM_REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&1`; `&1`]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sA` ASSUME_TAC THENL
   [REFUTE_THEN ASSUME_TAC THEN
    SUBGOAL_THEN `sA = &0` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `c977cc_normal cA sA` THEN REWRITE_TAC[c977cc_normal] THEN
      UNDISCH_TAC `~(&0 < sA)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC_ALL C696NC_CENTER_OF_NEGATIVE_FRAME) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`cA:real`; `&0`; `uA:real`; `vA:real`; `aA:real`; `&0`]) THEN
    ASM_REWRITE_TAC[REAL_NEG_0]; ALL_TAC] THEN
  C696NBW_CANONICAL_TAC 1 C696NBW_O THEN
  SUBGOAL_THEN `sO < &0` ASSUME_TAC THENL
   [MP_TAC(SPEC_ALL C696PBW_CANONICAL_SINE_NEGATIVE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL C696NBW_O) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN (c696ck_oin 256 `&1` `&2`) ASSUME_TAC THENL
   [REFUTE_THEN ASSUME_TAC THEN
    MP_TAC(SPEC_ALL C696NBW_MISSING_WEST) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_normal cO (--sO)` ASSUME_TAC THENL
   [MATCH_MP_TAC C696PBW_NEG_NORMAL THEN ASM_REWRITE_TAC[REAL_NOT_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &5 < --sO` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPEC_ALL C696NBW_EXCLUDES_OF_SMALL_BOTTOM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL (C696NBW_O @ [`--sO:real`])) THEN ASM_REWRITE_TAC[REAL_NEG_NEG]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC C696NBW_O THEN REWRITE_TAC[c696cnf_data] THEN ASM_REWRITE_TAC[]);;

(* Lean: cover *)
let C696CNF_Q = [`q1:num->real`; `q2:num->real`; `q3:num->real`; `q4:num->real`];;
let C696CNF_R = [`r1:num->real`; `r2:num->real`; `r3:num->real`; `r4:num->real`];;
let C696CNF_COVER = prove
 (list_mk_forall(C696CNF_OLD @ [`l:real`], mk_imp(C696SSP_HYP,
    list_mk_exists(C696CNF_D, mk_conj(c696cnf_hyp C696CNF_D,
      list_mk_exists(C696CNF_A @ C696NBW_O, list_mk_comb(`c696cnf_data`, C696CNF_D @ [`l:real`] @ C696CNF_A @ C696NBW_O)))))),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C696CNF_MISSING_CENTER_COVER) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC C696CNF_Q THEN STRIP_TAC THEN
  MP_TAC(SPECL (C696CNF_Q @ [`l:real`]) C696CNF_NONNEGATIVE_CENTRAL_COVER) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC C696CNF_R THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC C696CNF_R THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL (C696CNF_R @ [`l:real`]) C696CNF_DATA_OF) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL C696CNF_A) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* Lean: excludes_of_normal_form *)
let C696CNF_EXCLUDES_OF_NORMAL_FORM = prove
 (mk_imp(list_mk_forall(C696CNF_OLD @ [`l:real`], mk_imp(C696SSP_HYP,
     list_mk_forall(C696CNF_A @ C696NBW_O,
       mk_imp(list_mk_comb(`c696cnf_data`, C696CNF_OLD @ [`l:real`] @ C696CNF_A @ C696NBW_O), `false`)))),
   `excl_case 696`),
  DISCH_TAC THEN MATCH_MP_TAC (ri_excludes_case 377 `c696ssp_family`) THEN
  REWRITE_TAC[excl_fam] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL C696CNF_COVER) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_MESON_TAC[]);;
