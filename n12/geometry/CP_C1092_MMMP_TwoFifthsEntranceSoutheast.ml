(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/TwoFifthsEntranceSoutheast.lean     *)
(* (N12Compact.C1092MMMPTwoFifthsEntrance).  Actual Q5 entrance for both     *)
(* truth values of G8.  Conventions of CP_C1092_MMMP_SoutheastSign.ml and    *)
(* the forward toolkit c1092mo_* of CP_C1092_MMMP_Origins.ml: owners p i is  *)
(* the owner 5-tuple at mask EL i c1092wc_code (side l); WallContext p mmmp  *)
(* is C1092MMPE_CTX; near is C1092MSS_NEAR.  SoutheastActual p E is          *)
(* c1092mtfes_actual (OpenSquare invariants of E as explicit conjuncts in    *)
(* the existential); C1092TwoFifths.Southeast is C1092TF_southeast.          *)
(* inverseChart C = clockwise^3 C is the tuple (c, s, v, --u - a, a).        *)
(* SoutheastSign.PositiveActual / exists_positive / inward_pair:             *)
(* c1092mss_positiveActual / C1092MSS_EXISTS_POSITIVE / C1092MSS_INWARD_PAIR;*)
(* InwardOuterArmHalfpoint.bottom_origin_of_near                             *)
(* C1092MIOA_BOTTOM_ORIGIN_OF_NEAR; BottomPair.pair C1092MBP_PAIR;           *)
(* PositiveInwardHalfangle.small_angle_of_bar C1092MPIH_SMALL_ANGLE_OF_BAR;  *)
(* northwest_center C1092MPC_NORTHWEST_CENTER; northeast_sharp               *)
(* C1092MTFEN_NORTHEAST_SHARP; OriginalOwners.horizontal_segment            *)
(* OO_HORIZONTAL_SEGMENT; translated CCIP_INSIDE_TRANSLATED; the floor       *)
(* lemmas C1092MTFF_*.  Tag C1092MTFES_.                                     *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_TwoFifthsEntranceFloor.ml";;
needs "n12/geometry/CP_C1092_MMMP_InwardOuterArmHalfpoint.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;
needs "n12/geometry/CP_C1092_MMMP_SoutheastSign.ml";;
needs "n12/geometry/CP_C1092_MMMP_PositiveInwardHalfangle.ml";;
needs "n12/geometry/CP_C1092_MMMP_PointCore.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsData.ml";;

(* Lean: SoutheastActual (structure) *)
let c1092mtfes_actual = new_definition
 `c1092mtfes_actual (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real)
                    (cE:real) (sE:real) (uE:real) (vE:real) (aE:real) <=>
    aE = l /\
    (forall x y. linside cE sE uE vE aE x y <=>
           linside (ooc c1 c2 a b l (EL 5 c1092wc_code)) (oos c1 c2 a b l (EL 5 c1092wc_code))
                   (oou c1 c2 a b l (EL 5 c1092wc_code)) (oov c1 c2 a b l (EL 5 c1092wc_code)) l
                   (&2 + x) (&2 + y)) /\
    c977cc_normal cE sE /\ &0 < sE`;;

(* Lean: inverse_inside (private; inverseChart C = clockwise (clockwise (clockwise C))) *)
let C1092MTFES_INVERSE_INSIDE = prove
 (`forall c s u v a x y. linside c s v (--u - a) a x y <=> linside c s u v a (--y) x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: inverse_actual (private) *)
let C1092MTFES_INVERSE_ACTUAL = prove
 (`forall c1 c2 a b l cC sC uC vC aC.
     c1092mss_positiveActual c1 c2 a b l cC sC uC vC aC
     ==> c1092mtfes_actual c1 c2 a b l cC sC vC (--uC - aC) aC`,
  REWRITE_TAC[c1092mss_positiveActual; c1092mtfes_actual; C1092MTFES_INVERSE_INSIDE] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `&2 - --x = &2 + x`]);;

(* o5 point facts through an explicit chart equation eq : !x y. linside T x y <=> o5 .. *)
let c1092mtfes_pt eq x y th =
  let e = CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) (SPECL [x; y] eq) in
  EQ_MP (SYM e) th;;
let c1092mtfes_npt eq x y th =
  let e = CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) (SPECL [x; y] eq) in
  EQ_MP (SYM (AP_TERM `(~)` e)) th;;

let C1092MTFES_HYPS = Printf.sprintf "%s /\\ %s /\\ %s" C1092AE_HYP C1092MMPE_CTX C1092MSS_NEAR;;

(* the bottom bar: o9 owns (2 + x, 1) for 0 <= x <= 2/5 *)
let C1092MTFES_BAR = prove
 (parse_term (Printf.sprintf "!%s. %s ==> !x. &0 <= x /\\ x <= &2 / &5 ==> %s"
    C1092AE_P C1092MTFES_HYPS (c1092mmpe_in 9 "&2 + x" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MMPE_V C1092MIOA_BOTTOM_ORIGIN_OF_NEAR) THEN
  MP_TAC(SPECL C1092MMPE_V C1092MBP_PAIR) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN DISCH_TAC THEN MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&2`; `&12 / &5`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`&0 <= x`; `x <= &2 / &5`] THEN REAL_ARITH_TAC);;

(* the literal-mask facts shared by both proofs *)
let c1092mtfes_facts () =
  let near = CONV_RULE C1092MO_CODE_CONV (ASSUME (parse_term C1092MSS_NEAR)) in
  let hyps3 = end_itlist CONJ [ASSUME C1092MO_NP; ASSUME C1092MO_IMG; ASSUME C1092MO_CTX;
                               ASSUME (parse_term C1092MSS_NEAR)] in
  let use3 th = CONV_RULE C1092MO_CODE_CONV (MP (SPECL C1092MMPE_V th) hyps3) in
  let inward = use3 C1092MSS_INWARD_PAIR in
  let bar = use3 C1092MTFES_BAR in
  let mark = c1092mo_seed 5 (`&47 / &20`, `&33 / &20`) in
  let nwc = c1092mo_use C1092MPC_NORTHWEST_CENTER in
  let sharp = c1092mo_use C1092MTFEN_NORTHEAST_SHARP in
  (near, inward, bar, mark, nwc, sharp);;

(* Lean: missing_outer_small (private) *)
let C1092MTFES_MISSING_OUTER_SMALL = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ ~%s /\\
      cC * cC + sC * sC = &1 /\\ &0 < aC /\\ c1092mss_positiveActual %s cC sC uC vC aC
      ==> sC < &21 / &100 /\\ &97 / &100 < cC"
    C1092AE_P C1092MTFES_HYPS (c1092mmpe_in 5 "&3" "&8 / &5") C1092AE_P),
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mss_positiveActual] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l`)) THEN
  let near, inward, bar, mark, nwc, sharp = c1092mtfes_facts () in
  let eqC = CONV_RULE C1092MO_CODE_CONV (ASSUME
    (parse_term ("!x y. linside cC sC uC vC l x y <=> " ^ c1092mmpe_in 5 "&2 + y" "&2 - x"))) in
  let missing = CONV_RULE C1092MO_CODE_CONV
    (ASSUME (mk_neg (parse_term (c1092mmpe_in 5 "&3" "&8 / &5")))) in
  let bar5 = GEN `y:real` (DISCH `&0 <= y /\ y <= &2 / &5`
    (c1092mo_excl 5 9 (UNDISCH (SPEC `y:real` bar)))) in
  let th = c1092mo_apply (c1092mo_conv [eqC])
    (SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `l:real`] C1092MPIH_SMALL_ANGLE_OF_BAR)
    [ASSUME `cC * cC + sC * sC = &1`; c1092mo_pos (); c1092mo_side ();
     ASSUME `c977cc_normal cC sC`; mark; CONJUNCT2 inward; CONJUNCT1 inward;
     c1092mo_excl 5 7 nwc; missing; bar5] in
  REWRITE_TAC[CONJUNCT2 th]);;

(* Lean: southeast_profile *)
let C1092MTFES_SOUTHEAST_PROFILE = prove
 (parse_term (Printf.sprintf "!%s. %s ==> ?cE sE uE vE aE. cE * cE + sE * sE = &1 /\\ &0 < aE /\\
      c1092mtfes_actual %s cE sE uE vE aE /\\ C1092TF_southeast cE sE uE vE aE"
    C1092AE_P C1092MTFES_HYPS C1092AE_P),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MMPE_V C1092MSS_EXISTS_POSITIVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cC:real` (X_CHOOSE_THEN `sC:real` (X_CHOOSE_THEN `uC:real`
    (X_CHOOSE_THEN `vC:real` (X_CHOOSE_THEN `aC:real` STRIP_ASSUME_TAC))))) THEN
  MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `vC:real`; `--uC - aC`; `aC:real`] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C1092MTFES_INVERSE_ACTUAL) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ASSUME `c1092mss_positiveActual c1 c2 a b l cC sC uC vC aC`) THEN
  REWRITE_TAC[c1092mss_positiveActual] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cC sC`)) THEN
  let near, inward, bar, mark, nwc, sharp = c1092mtfes_facts () in
  let eqC0 = ASSUME (parse_term ("!x y. linside cC sC uC vC l x y <=> " ^
                                 c1092mmpe_in 5 "&2 + y" "&2 - x")) in
  let eqE0 = MP (prove(mk_imp(concl eqC0, parse_term ("!x y. linside cC sC vC (--uC - l) l x y <=> " ^
                               c1092mmpe_in 5 "&2 + x" "&2 + y")),
    DISCH_TAC THEN ASM_REWRITE_TAC[C1092MTFES_INVERSE_INSIDE; REAL_ARITH `&2 - --x = &2 + x`])) eqC0 in
  let eqE = CONV_RULE C1092MO_CODE_CONV eqE0 in
  let pt = c1092mtfes_pt eqE and npt = c1092mtfes_npt eqE in
  let tE = [`cC:real`; `sC:real`; `vC:real`; `--uC - l`; `l:real`] in
  let tB, eqsB = c1092mo_layers 9 [c1092mo_tr `&2` `&2`] in
  let eqB = hd eqsB in
  let markE = pt `&7 / &20` `--(&7 / &20)` mark
  and innerE = pt `&0` `--(&13 / &50)` (CONJUNCT1 inward)
  and forwardE = pt `&13 / &50` `&0` (CONJUNCT2 inward)
  and originE = npt `&0` `&0` (c1092mo_excl 5 7 nwc)
  and nearE = npt `&1` `--(&13 / &50)` (c1092mo_excl 5 10 near)
  and sharpE = npt `&47 / &100` `&3 / &25` (c1092mo_excl 5 6 sharp) in
  let barB =
    let x = `x:real` in
    let e = CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV))
      (SPECL [x; `--(&1)`] eqB) in
    let pre = UNDISCH (SPEC x bar) in
    let pre' = EQ_MP (SYM e) pre in
    GEN x (DISCH `&0 <= x` (DISCH `x <= &2 / &5`
      (PROVE_HYP (CONJ (ASSUME `&0 <= x`) (ASSUME `x <= &2 / &5`)) pre'))) in
  let apartEB =
    let x = `x:real` and y = `y:real` in
    let a1 = SPECL [`&2 + x`; `&2 + y`] (c1092mo_apart 5 9) in
    let a2 = REWRITE_RULE[GSYM (SPECL [x; y] eqE); GSYM (SPECL [x; y] eqB)] a1 in
    let ld = REWRITE_CONV[ldisj] (list_mk_comb(`ldisj`, tE @ tB)) in
    EQ_MP (SYM ld) (GENL [x; y] a2) in
  let gen_facts = [ASSUME `cC * cC + sC * sC = &1`; c1092mo_pos (); c1092mo_side ();
                   markE; innerE; forwardE; originE; nearE; sharpE; barB; apartEB] in
  MAP_EVERY ASSUME_TAC gen_facts THEN
  MP_TAC(SPECL tE C1092MTFF_SOUTHEAST_CAPS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false []; STRIP_TAC] THEN
  REWRITE_TAC[C1092TF_southeast] THEN
  SUBGOAL_THEN `&1 < l /\ &0 < cC` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false []; ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC (parse_term (c1092mmpe_in 5 "&3" "&8 / &5")) THENL
   [(let outer = CONV_RULE C1092MO_CODE_CONV (ASSUME (parse_term (c1092mmpe_in 5 "&3" "&8 / &5"))) in
    let outerE = pt `&1` `--(&2 / &5)` outer in
    ASSUME_TAC outerE THEN
    MP_TAC(SPECL tE C1092MTFF_SOUTHEAST_OUTER_CAP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(SPECL (tE @ tB) C1092MTFF_SOUTHEAST_FLOOR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL tE C1092MTFF_SOUTHEAST_OUTER_SMALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);
    MP_TAC(SPECL (C1092MMPE_V @ [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `l:real`])
      C1092MTFES_MISSING_OUTER_SMALL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(SPECL (tE @ tB) C1092MTFF_SOUTHEAST_FLOOR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `sC < &21 / &100` THEN REAL_ARITH_TAC; DISCH_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`sC < &21 / &100`; `&97 / &100 < cC`] THEN REAL_ARITH_TAC]);;
