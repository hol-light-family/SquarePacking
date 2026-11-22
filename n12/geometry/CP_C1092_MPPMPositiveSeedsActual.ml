(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMPositiveSeedsActual.lean             *)
(* (namespace N12Compact.C1092MPPMPositiveSeedsActual; Lean header:          *)
(* "Source-only, without compiler acceptance").  Literal original-owner      *)
(* applications of the MPPM ordinary halfpoint, positive missing-forward     *)
(* profile and positive crosspoint seeds.  Conventions of                    *)
(* CP_C1092_MPPMEntrance.ml: owners p i is the owner 5-tuple at mask         *)
(* EL i c1092wc_code (0 -> 3, 4 -> 256, 5 -> 512, 7 -> 2048, 8 -> 4096,      *)
(* 9 -> 8192; side l); WallContext p mppm is                                 *)
(* c1092wc_ctx c1 c2 a b l c1092mppe_mppm.  An OpenSquare C is cC sC uC vC aC *)
(* with its invariants cC * cC + sC * sC = &1 /\ &0 < aC as hypotheses;      *)
(* ActualFrame p C is c1092psa_frame; Normal = c977cc_normal;                *)
(* MissingPositiveFaces Inputs / Faces / profile = c1092mmpf_inputs /        *)
(* c1092mmpf_faces / C1092MMPF_PROFILE; PositiveCrosspointSeeds ForwardCore /*)
(* ForwardInputs = c1092pcs_forwardCore / c1092pcs_forwardInputs;            *)
(* MarkerHalfpoint.point = C1092MMH_POINT; boundary_origin =                 *)
(* OCWPBO_BOUNDARY_ORIGIN; canonical_frame = CLF_CANONICAL_FRAME.            *)
(* Points of the owners come from oo_seed (markers, corner points),          *)
(* owners_disjoint from oo_apart.  Tag C1092PSA_.                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMEntrance.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveCrosspointSeeds.ml";;
needs "n12/geometry/CP_C1092_MMMP_MarkerHalfpoint.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_BoundaryOrigin.ml";;

(* Lean: side_gt (private) *)
let C1092PSA_SIDE_GT = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l ==> &1 < l`, REWRITE_TAC[OO_SIDE]);;
(* Lean: side_same (private) *)
let C1092PSA_SIDE_SAME = prove (`forall l:real. l = l`, REWRITE_TAC[]);;
(* Lean: marker_point (private) *)
let C1092PSA_MARKER_POINT = prove
 (parse_term (Printf.sprintf "!%s i j. %s /\\ i < 12 /\\ j < 16 /\\ j IN bitset (EL i c1092wc_code) ==> linside %s (marker j$1) (marker j$2)"
    C1092AE_P C1092AE_HYP
    "(ooc c1 c2 a b l (EL i c1092wc_code)) (oos c1 c2 a b l (EL i c1092wc_code)) (oou c1 c2 a b l (EL i c1092wc_code)) (oov c1 c2 a b l (EL i c1092wc_code)) l"),
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ [`i:num`]) C1092WC_OWNERS_MARKERS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[]);;

(* S12 inside_translated_iff *)
let C1092PSA_INSIDE_TRANSLATED = prove
 (`forall c s u v a x y p q.
      linside c s (u - (c * x + s * y)) (v - (--s * x + c * y)) a p q <=>
      linside c s u v a (x + p) (y + q)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: ActualFrame (structure) *)
let c1092psa_frame = new_definition
 `c1092psa_frame (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real)
                 (cC:real) (sC:real) (uC:real) (vC:real) (aC:real) <=>
    aC = l /\
    forall x y. linside cC sC uC vC aC x y <=>
          linside (ooc c1 c2 a b l (EL 4 c1092wc_code)) (oos c1 c2 a b l (EL 4 c1092wc_code))
                  (oou c1 c2 a b l (EL 4 c1092wc_code)) (oov c1 c2 a b l (EL 4 c1092wc_code)) l
                  (&2 + x) (&2 + y)`;;

(* Lean: exists_canonical_frame *)
let C1092PSA_EXISTS_CANONICAL_FRAME = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l
     ==> exists cC sC uC vC aC. cC * cC + sC * sC = &1 /\ &0 < aC /\
           c1092psa_frame c1 c2 a b l cC sC uC vC aC /\ &0 < cC /\ abs sC <= cC`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ooc c1 c2 a b l (EL 4 c1092wc_code)`; `oos c1 c2 a b l (EL 4 c1092wc_code)`;
    `oou c1 c2 a b l (EL 4 c1092wc_code) - (ooc c1 c2 a b l (EL 4 c1092wc_code) * &2 + oos c1 c2 a b l (EL 4 c1092wc_code) * &2)`;
    `oov c1 c2 a b l (EL 4 c1092wc_code) - (--oos c1 c2 a b l (EL 4 c1092wc_code) * &2 + ooc c1 c2 a b l (EL 4 c1092wc_code) * &2)`;
    `l:real`] CLF_CANONICAL_FRAME) THEN
  ASM_SIMP_TAC[OO_UNIT; OO_SIDE; REAL_ARITH `&1 < l ==> &0 < l`] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  REWRITE_TAC[c1092psa_frame; C1092PSA_INSIDE_TRANSLATED] THEN MESON_TAC[]);;

(* ---- forward toolkit (literal masks) ---- *)
let C1092PSA_NP = `NPACK c1 c2 a b l`;;
let C1092PSA_IMG = `IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family`;;
let C1092PSA_CTX = parse_term C1092MPPE_CTX;;
let C1092PSA_CODE_CONV = REWRITE_CONV (Array.to_list C1092WC_CODE_EL);;
let C1092PSA_MASKS = [3;12;48;192;256;512;1024;2048;4096;8192;16384;32768];;
let C1092PSA_CV = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let c1092psa_own i =
  map (fun f -> list_mk_comb(f, C1092MPPE_V @ [mk_small_numeral (el i C1092PSA_MASKS)]))
    [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let c1092psa_hh () = CONJ (ASSUME C1092PSA_NP) (ASSUME C1092PSA_IMG);;
let c1092psa_side () = MP (SPECL C1092MPPE_V OO_SIDE) (ASSUME C1092PSA_NP);;
let c1092psa_pos () = MATCH_MP (REAL_ARITH `&1 < l ==> &0 < l`) (c1092psa_side ());;
let c1092psa_unit i = MP (SPECL (C1092MPPE_V @ [mk_small_numeral (el i C1092PSA_MASKS)]) OO_UNIT) (ASSUME C1092PSA_NP);;
let c1092psa_box i = MP (SPECL (C1092MPPE_V @ [mk_small_numeral (el i C1092PSA_MASKS)]) OO_BOX) (ASSUME C1092PSA_NP);;
let c1092psa_seed i (x, y) =
  MP (SPECL C1092MPPE_V (oo_inst `c1092wc_family` (oo_seed (el i C1092PSA_MASKS) (x, y)))) (c1092psa_hh ());;
let c1092psa_apart i j =
  REWRITE_RULE[ldisj] (MP (SPECL C1092MPPE_V
    (oo_apart `c1092wc_family` (el i C1092PSA_MASKS) (el j C1092PSA_MASKS))) (c1092psa_hh ()));;
let c1092psa_excl i j pt =
  let args = snd (strip_comb (concl pt)) in
  let d2 = SPECL [el 5 args; el 6 args] (c1092psa_apart i j) in
  let a = lhand (rand (concl d2)) in
  NOT_INTRO (DISCH a (MP (NOT_ELIM d2) (CONJ (ASSUME a) pt)));;
(* an EL-form hypothesis (string), assumed, and its literal-mask form *)
let c1092psa_hyp s = CONV_RULE C1092PSA_CODE_CONV (ASSUME (parse_term s));;
let c1092psa_wa () =
  CONV_RULE C1092PSA_CODE_CONV
    (MP (SPECL C1092MPPE_V C1092MPPE_WALL_AUXILIARIES) (CONJ (ASSUME C1092PSA_NP) (ASSUME C1092PSA_CTX)));;

let c1092psa_apply conv spec facts =
  let ants = conjuncts (lhand (concl spec)) in
  let pa tm =
    try find (fun f -> aconv (concl f) tm) facts with Failure _ ->
    let eq = conv tm in
    let r = rhs (concl eq) in
    if r = `true` then EQT_ELIM eq else
    try EQ_MP (SYM eq) (find (fun f -> aconv (concl f) r) facts)
    with Failure _ -> failwith ("c1092psa_apply: " ^ string_of_term tm) in
  CONV_RULE conv (MP spec (end_itlist CONJ (map pa ants)));;

(* hypothesis strings *)
let c1092psa_in = c1092mppe_in;;
let C1092PSA_P = c1092psa_in 4 "&1" "&87 / &50";;
let C1092PSA_G = c1092psa_in 4 "&1" "&8 / &5";;
let C1092PSA_MISSING = "~" ^ c1092psa_in 4 "&87 / &50" "&2";;
let C1092PSA_FAR = c1092psa_in 9 "&36 / &25" "&1";;
let C1092PSA_BOTTOMF = c1092psa_in 9 "&8 / &5" "&1";;
let C1092PSA_FORWARD = c1092psa_in 4 "&87 / &50" "&2";;
let C1092PSA_PREVIOUS = "~" ^ c1092psa_in 4 "&1" "&2";;
let C1092PSA_NEXT = c1092psa_in 5 "&2" "&3 / &2";;
let C1092PSA_SQ = "cC * cC + sC * sC = &1 /\\ &0 < aC";;
let C1092PSA_FRAME = "c1092psa_frame c1 c2 a b l cC sC uC vC aC";;
let c1092psa_stmt vars hyps concl =
  parse_term (Printf.sprintf "!%s. %s ==> %s" vars (String.concat " /\\ " hyps) concl);;
let c1092psa_close stmt th =
  prove(stmt, REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC (TRY_CONV C1092PSA_CODE_CONV) THEN ACCEPT_TAC th);;
let C1092PSA_VARS = "c1 c2 a b l";;
let C1092PSA_VARS_C = "c1 c2 a b l cC sC uC vC aC";;

(* the frame equivalence and the conversion C -> owners p 4 *)
let c1092psa_frame_conv () =
  let fr = CONJUNCTS (REWRITE_RULE[c1092psa_frame] (ASSUME (parse_term C1092PSA_FRAME))) in
  (hd fr, GEN_REWRITE_CONV ONCE_DEPTH_CONV [el 1 fr] THENC C1092PSA_CODE_CONV THENC
          ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV);;

(* Lean: missing_halfpoint *)
let c1092psa_missing_halfpoint () =
  let p = c1092psa_hyp C1092PSA_P and g = c1092psa_hyp C1092PSA_G
  and missingE = c1092psa_hyp C1092PSA_MISSING in
  let t = let th = SPECL (c1092psa_own 4 @ [`x:real`; `y:real`]) LINSIDE_PULLX in
    fst (chop_list 5 (snd (strip_comb (lhs (concl th))))) in
  let t2 = let th = SPECL (t @ [`&2`; `&2`; `x:real`; `y:real`]) C1092PSA_INSIDE_TRANSLATED in
    fst (chop_list 5 (snd (strip_comb (lhs (concl th))))) in
  let conv = REWRITE_CONV[C1092PSA_INSIDE_TRANSLATED] THENC REWRITE_CONV[LINSIDE_PULLX] THENC
             ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV in
  let unit = MP (prove(mk_imp(concl (c1092psa_unit 4),
                 mk_eq(mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` (hd t2) (hd t2))
                         (mk_binop `( * ):real->real->real` (el 1 t2) (el 1 t2)), `&1`)), CONV_TAC REAL_RING))
                (c1092psa_unit 4) in
  let wa = c1092psa_wa () in
  c1092psa_apply conv (SPECL (t2 @ [`&43 / &500`]) C1092MMH_POINT)
    [unit; c1092psa_pos (); c1092psa_side (); c1092psa_seed 4 (`&33 / &20`, `&33 / &20`); p; g; missingE;
     c1092psa_excl 4 8 (c1092psa_seed 8 (`&457 / &500`, `&2`));
     c1092psa_excl 4 0 (c1092psa_seed 0 (`&1`, `&1`));
     c1092psa_excl 4 9 (CONJUNCT1 (CONJUNCT2 wa))];;
let C1092PSA_MISSING_HALFPOINT = c1092psa_close
  (c1092psa_stmt C1092PSA_VARS [C1092AE_HYP; C1092MPPE_CTX; C1092PSA_P; C1092PSA_G; C1092PSA_MISSING]
     (c1092psa_in 4 "&1" "&3 / &2"))
  (c1092psa_missing_halfpoint ());;

let C1092PSA_BOX_Y = prove
 (`forall c s u v a. lcont c s u v a ==> forall x y. linside c s u v a x y ==> &0 <= y`,
  REWRITE_TAC[lcont] THEN MESON_TAC[]);;
let C1092PSA_BOX_XY = prove
 (`forall c s u v a. lcont c s u v a ==> forall x y. linside c s u v a x y ==> &0 <= x /\ &0 <= y`,
  REWRITE_TAC[lcont] THEN MESON_TAC[]);;

(* Lean: bottom_origin_of_halfpoint *)
let c1092psa_bottom_origin half =
  let bottomF = c1092psa_hyp C1092PSA_BOTTOMF in
  let boxy i = MATCH_MP C1092PSA_BOX_Y (c1092psa_box i) in
  let boxxy i = MATCH_MP C1092PSA_BOX_XY (c1092psa_box i) in
  let disj = REWRITE_RULE[GSYM ldisj] (c1092psa_apart 0 9) in
  c1092psa_apply (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
    (SPECL (c1092psa_own 9 @ c1092psa_own 0 @ [`&457 / &500`; `&8 / &5`]) OCWPBO_BOUNDARY_ORIGIN)
    [c1092psa_unit 9; c1092psa_unit 0; c1092psa_pos (); c1092psa_side (); REFL `l:real`;
     boxy 9; boxxy 0; c1092psa_seed 9 (`&2`, `&457 / &500`); bottomF;
     c1092psa_seed 0 (`&1`, `&457 / &500`); c1092psa_seed 0 (`&1`, `&1`);
     c1092psa_excl 0 4 half; disj];;
let C1092PSA_BOTTOM_ORIGIN_OF_HALFPOINT = c1092psa_close
  (c1092psa_stmt C1092PSA_VARS [C1092AE_HYP; C1092PSA_BOTTOMF; c1092psa_in 4 "&1" "&3 / &2"]
     (c1092psa_in 9 "&2" "&1"))
  (c1092psa_bottom_origin (c1092psa_hyp (c1092psa_in 4 "&1" "&3 / &2")));;

(* Lean: bottom_origin_of_missing *)
let C1092PSA_BOTTOM_ORIGIN_OF_MISSING = c1092psa_close
  (c1092psa_stmt C1092PSA_VARS [C1092AE_HYP; C1092MPPE_CTX; C1092PSA_BOTTOMF; C1092PSA_P; C1092PSA_G;
                                C1092PSA_MISSING] (c1092psa_in 9 "&2" "&1"))
  (c1092psa_bottom_origin (c1092psa_missing_halfpoint ()));;

(* prove a structure of C-point facts from owner facts through the frame *)
let c1092psa_through_frame defth facts =
  let _, conv = c1092psa_frame_conv () in
  let lhs_tm = lhs (concl (SPEC_ALL defth)) in
  let tm = list_mk_comb(fst (strip_comb lhs_tm), C1092PSA_CV) in
  let body = rhs (concl (REWRITE_CONV[defth] tm)) in
  let pf c =
    let e = conv c in
    let r = rhs (concl e) in
    try EQ_MP (SYM e) (find (fun f -> aconv (concl f) r) facts)
    with Failure _ -> failwith ("c1092psa_through_frame: " ^ string_of_term r) in
  EQ_MP (SYM (REWRITE_CONV[defth] tm)) (end_itlist CONJ (map pf (conjuncts body)));;

(* Lean: missing_inputs *)
let c1092psa_missing_inputs () =
  let half = c1092psa_missing_halfpoint () in
  let wa = c1092psa_wa () in
  c1092psa_through_frame c1092mmpf_inputs
    [c1092psa_seed 4 (`&33 / &20`, `&33 / &20`); c1092psa_hyp C1092PSA_P; c1092psa_hyp C1092PSA_G; half;
     c1092psa_excl 4 0 (c1092psa_seed 0 (`&1`, `&1`));
     c1092psa_excl 4 0 (c1092psa_seed 0 (`&457 / &500`, `&1`));
     c1092psa_excl 4 8 (c1092psa_seed 8 (`&457 / &500`, `&2`));
     c1092psa_hyp C1092PSA_MISSING;
     c1092psa_excl 4 9 (c1092psa_hyp C1092PSA_FAR);
     c1092psa_excl 4 9 (CONJUNCT1 (CONJUNCT2 wa))];;
let C1092PSA_MISSING_HYPS = [C1092AE_HYP; C1092MPPE_CTX; C1092PSA_P; C1092PSA_G; C1092PSA_MISSING;
                             C1092PSA_FAR; C1092PSA_SQ; C1092PSA_FRAME];;
let C1092PSA_MISSING_INPUTS = c1092psa_close
  (c1092psa_stmt C1092PSA_VARS_C C1092PSA_MISSING_HYPS "c1092mmpf_inputs cC sC uC vC aC")
  (c1092psa_missing_inputs ());;

let c1092psa_c_side () =
  let fs, _ = c1092psa_frame_conv () in
  MP (MP (REAL_ARITH `aC = l ==> &1 < l ==> &1 < aC`) fs) (c1092psa_side ());;
let C1092PSA_SQ_THS () = map ASSUME (conjuncts (parse_term C1092PSA_SQ));;

(* Lean: missing_profile *)
let C1092PSA_MISSING_PROFILE = c1092psa_close
  (c1092psa_stmt C1092PSA_VARS_C (C1092PSA_MISSING_HYPS @ ["c977cc_normal cC sC"])
     "c1092mmpf_faces cC sC uC vC aC")
  (c1092psa_apply ALL_CONV (SPECL C1092PSA_CV C1092MMPF_PROFILE)
     (C1092PSA_SQ_THS () @ [c1092psa_c_side (); ASSUME `c977cc_normal cC sC`; c1092psa_missing_inputs ()]));;

(* Lean: missing_crosspoint *)
let C1092PSA_MISSING_CROSSPOINT =
  let _, conv = c1092psa_frame_conv () in
  c1092psa_close
  (c1092psa_stmt C1092PSA_VARS_C (C1092PSA_MISSING_HYPS @ ["c977cc_normal cC sC"; "C1092WPS_half cC sC <= &1 / &3"])
     (c1092psa_in 4 "&3 / &2" "&2"))
  (CONV_RULE conv (c1092psa_apply ALL_CONV (SPECL C1092PSA_CV C1092PCS_CROSSPOINT_OF_MISSING)
     (C1092PSA_SQ_THS () @ [c1092psa_c_side (); ASSUME `c977cc_normal cC sC`; c1092psa_missing_inputs ();
                            ASSUME `C1092WPS_half cC sC <= &1 / &3`])));;

(* Lean: forward_core *)
let c1092psa_forward_core () =
  c1092psa_through_frame c1092pcs_forwardCore
    [c1092psa_seed 4 (`&33 / &20`, `&33 / &20`); c1092psa_hyp C1092PSA_P; c1092psa_hyp C1092PSA_G;
     c1092psa_hyp C1092PSA_FORWARD;
     c1092psa_excl 4 0 (c1092psa_seed 0 (`&1`, `&1`));
     c1092psa_hyp C1092PSA_PREVIOUS;
     c1092psa_excl 4 9 (c1092psa_hyp C1092PSA_BOTTOMF)];;
let C1092PSA_FORWARD_HYPS = [C1092AE_HYP; C1092PSA_BOTTOMF; C1092PSA_P; C1092PSA_G; C1092PSA_FORWARD;
                             C1092PSA_PREVIOUS];;
let C1092PSA_FORWARD_CORE = c1092psa_close
  (c1092psa_stmt C1092PSA_VARS_C (C1092PSA_FORWARD_HYPS @ [C1092PSA_SQ; C1092PSA_FRAME])
     "c1092pcs_forwardCore cC sC uC vC aC")
  (c1092psa_forward_core ());;

(* Lean: forward_inputs *)
let c1092psa_forward_inputs () =
  c1092psa_through_frame c1092pcs_forwardInputs
    [c1092psa_seed 4 (`&33 / &20`, `&33 / &20`); c1092psa_hyp C1092PSA_P; c1092psa_hyp C1092PSA_G;
     c1092psa_hyp C1092PSA_FORWARD;
     c1092psa_excl 4 0 (c1092psa_seed 0 (`&1`, `&1`));
     c1092psa_hyp C1092PSA_PREVIOUS;
     c1092psa_excl 4 9 (c1092psa_hyp C1092PSA_BOTTOMF);
     c1092psa_excl 4 9 (c1092psa_hyp C1092PSA_FAR);
     c1092psa_excl 4 7 (c1092psa_seed 7 (`&33 / &20`, `&47 / &20`))];;
let C1092PSA_FORWARD_INPUTS = c1092psa_close
  (c1092psa_stmt C1092PSA_VARS_C (C1092PSA_FORWARD_HYPS @ [C1092PSA_FAR; C1092PSA_SQ; C1092PSA_FRAME])
     "c1092pcs_forwardInputs cC sC uC vC aC")
  (c1092psa_forward_inputs ());;

(* Lean: forward_crosspoint *)
let C1092PSA_FORWARD_CROSSPOINT =
  let _, conv = c1092psa_frame_conv () in
  c1092psa_close
  (c1092psa_stmt C1092PSA_VARS_C (C1092PSA_FORWARD_HYPS @ [C1092PSA_FAR; C1092PSA_SQ; C1092PSA_FRAME;
                                                          "c977cc_normal cC sC"])
     (c1092psa_in 4 "&3 / &2" "&2"))
  (CONV_RULE conv (c1092psa_apply ALL_CONV (SPECL C1092PSA_CV C1092PCS_CROSSPOINT_OF_FORWARD)
     (C1092PSA_SQ_THS () @ [c1092psa_c_side (); ASSUME `c977cc_normal cC sC`; c1092psa_forward_inputs ()])));;

(* Lean: forward_halfpoint_and_origin *)
let C1092PSA_FORWARD_HALFPOINT_AND_ORIGIN =
  let _, conv = c1092psa_frame_conv () in
  let cfact tm th = let e = conv tm in
    if aconv (rhs (concl e)) (concl th) then EQ_MP (SYM e) th
    else failwith ("cfact: " ^ string_of_term (rhs (concl e))) in
  let cin x y = list_mk_comb(`linside`, C1092PSA_CV @ [x; y]) in
  let markN = c1092psa_excl 4 7 (c1092psa_seed 7 (`&33 / &20`, `&47 / &20`)) in
  let nx = c1092psa_excl 4 5 (c1092psa_hyp C1092PSA_NEXT) in
  let result = c1092psa_apply ALL_CONV (SPECL C1092PSA_CV C1092PCS_HALFPOINT_OF_NEXT_CROSSPOINT)
    (C1092PSA_SQ_THS () @ [c1092psa_c_side (); ASSUME `c977cc_normal cC sC`; ASSUME `&0 < sC`;
      c1092psa_forward_core (); cfact (mk_neg (cin `--(&7 / &20)` `&7 / &20`)) markN;
      ASSUME `C1092WPS_half cC sC <= &1 / &3`; cfact (mk_neg (cin `&0` `--(&1 / &2)`)) nx]) in
  let [r1; r2; r3] = CONJUNCTS result in
  let half = CONV_RULE conv r3 in
  c1092psa_close
  (c1092psa_stmt C1092PSA_VARS_C (C1092PSA_FORWARD_HYPS @ [C1092PSA_NEXT; C1092PSA_SQ; C1092PSA_FRAME;
     "c977cc_normal cC sC"; "&0 < sC"; "C1092WPS_half cC sC <= &1 / &3"])
     ("uC + aC <= --sC / &2 /\\ ~" ^ c1092psa_in 4 "&2" "&87 / &50" ^ " /\\ " ^
      c1092psa_in 4 "&1" "&3 / &2" ^ " /\\ " ^ c1092psa_in 9 "&2" "&1"))
  (end_itlist CONJ [r1; CONV_RULE conv r2; half; c1092psa_bottom_origin half]);;
