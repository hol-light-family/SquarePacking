(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/SoutheastSign.lean                  *)
(* (N12Compact.C1092MMMPSoutheastSign).  A genuine right F8 forces the       *)
(* southeast inward pair and its strictly positive canonical sign.           *)
(* Conventions of CP_C1092_MMMPEntrance.ml / CP_C1092_MMMP_BottomPair.ml     *)
(* (forward toolkit c1092mo_* of CP_C1092_MMMP_Origins.ml at literal masks): *)
(* owners p i is the owner 5-tuple at mask EL i c1092wc_code (side l);       *)
(* WallContext p mmmp is c1092wc_ctx c1 c2 a b l c1092mmpe_mmmp.             *)
(* BottomPair.pair C1092MBP_PAIR; southeast_f_cover C1092MMEN_SOUTHEAST_F_   *)
(* COVER; southeast_g_cover C1092AC_SOUTHEAST_G_COVER; MixedSpan.impossible  *)
(* C1092MS_IMPOSSIBLE; ShortBarNegative.impossible C1092SBN_IMPOSSIBLE;      *)
(* right_origin C1092MO_RIGHT_ORIGIN; northwest_center                       *)
(* C1092MPC_NORTHWEST_CENTER; local_wall_segment C1092WC_LOCAL_WALL_SEGMENT; *)
(* inside_segment C1092WC_INSIDE_SEGMENT; canonical_frame CLF_CANONICAL_FRAME.*)
(* The private chart q = (pullSwap (pullY q)).translated 2 2 is the explicit *)
(* tuple (--s, c, u - 2c - 2s, v - 2c + 2s, a) (C1092MSS_INSIDE_CHART).      *)
(* An OpenSquare C is cC sC uC vC aC with its invariants as hypotheses;      *)
(* PositiveActual p C is c1092mss_positiveActual.  Tag C1092MSS_.            *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_BottomPair.ml";;
needs "n12/geometry/CP_C1092_MMMP_ShortBarNegative.ml";;

let C1092MSS_NEAR = c1092mmpe_in 10 "&3" "&87 / &50";;

(* Lean: inward_pair *)
let C1092MSS_INWARD_PAIR = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> %s /\\ %s" C1092AE_P C1092AE_HYP C1092MMPE_CTX
    C1092MSS_NEAR (c1092mmpe_in 5 "&2" "&87 / &50") (c1092mmpe_in 5 "&113 / &50" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC C1092MO_CODE_CONV THEN
  let useh th = CONV_RULE C1092MO_CODE_CONV (MP (SPECL C1092MMPE_V th) (c1092mo_hh ())) in
  let near = CONV_RULE C1092MO_CODE_CONV (ASSUME (parse_term C1092MSS_NEAR)) in
  let bottom = c1092mo_use C1092MBP_PAIR in
  let fcov = useh C1092MMEN_SOUTHEAST_F_COVER and gcov = useh C1092AC_SOUTHEAST_G_COVER in
  let e1 = c1092mo_excl 5 9 (CONJUNCT1 bottom) and e2 = c1092mo_excl 5 9 (CONJUNCT2 bottom)
  and e3 = c1092mo_excl 5 10 near in
  let hf = c1092mo_in 5 `&2` `&87 / &50` and hh = c1092mo_in 5 `&3` `&8 / &5`
  and hm = mk_neg (c1092mo_in 5 `&113 / &50` `&2`) in
  let ms = itlist DISCH [hf; hh; hm]
    (c1092mo_apply (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
      (SPECL (c1092mo_own 5) C1092MS_IMPOSSIBLE)
      [c1092mo_unit 5; c1092mo_pos (); c1092mo_side (); ASSUME hf; ASSUME hh; ASSUME hm; e1; e2; e3]) in
  MP_TAC (end_itlist CONJ [fcov; gcov; e1; e2; e3; ms]) THEN CONV_TAC TAUT);;

(* Lean: chart (private), inside_chart (private) *)
let C1092MSS_INSIDE_CHART = prove
 (`forall c s u v a x y.
     linside (--s) c (u - &2 * c - &2 * s) (v - &2 * c + &2 * s) a x y <=>
     linside c s u v a (&2 + y) (&2 - x)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: center_chart (private) *)
let C1092MSS_CENTER_CHART = prove
 (`forall c s u v a. c * c + s * s = &1
     ==> lcy (--s) c (u - &2 * c - &2 * s) (v - &2 * c + &2 * s) a = lcx c s u v a - &2`,
  REWRITE_TAC[lcx; lcy] THEN CONV_TAC REAL_RING);;

let C1092MSS_CHART_UNIT = prove
 (`forall c s. c * c + s * s = &1 ==> --s * --s + c * c = &1`,
  CONV_TAC REAL_RING);;

(* Lean: PositiveActual (structure) *)
let c1092mss_positiveActual = new_definition
 `c1092mss_positiveActual (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real)
                          (cC:real) (sC:real) (uC:real) (vC:real) (aC:real) <=>
    aC = l /\
    (forall x y. linside cC sC uC vC aC x y <=>
           linside (ooc c1 c2 a b l (EL 5 c1092wc_code)) (oos c1 c2 a b l (EL 5 c1092wc_code))
                   (oou c1 c2 a b l (EL 5 c1092wc_code)) (oov c1 c2 a b l (EL 5 c1092wc_code)) l
                   (&2 + y) (&2 - x)) /\
    c977cc_normal cC sC /\ &0 < sC`;;

(* rightBar (local fact) *)
let C1092MSS_RIGHT_BAR = prove
 (`forall c s u v a x. linside c s u v a (&3) (&2) /\ linside c s u v a (&3) (&87 / &50) /\
     &0 <= x /\ x <= &13 / &50 ==> linside c s u v a (&3) (&2 - x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&3`; `&2`; `&3`; `&87 / &50`;
                `&50 / &13 * x`] C1092WC_INSIDE_SEGMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN REAL_ARITH_TAC);;

(* the wall tip of owner 9 (local_wall_segment at wall 1) *)
let C1092MSS_TIP = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P C1092MMPE_CTX (c1092mmpe_in 9 "&239 / &100" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MMPE_V @ [`c1092mmpe_mmmp`; `1`; `&161 / &100`]) C1092WC_LOCAL_WALL_SEGMENT) THEN
  ASM_REWRITE_TAC[c1092wc_pmx; c1092wc_pmy; c1092wc_by; c1092mmpe_mmmp; ARITH] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]);;

(* cut (local fact): the bottom wall frame centre *)
let C1092MSS_CUT = prove
 (parse_term (Printf.sprintf "!%s. %s ==> &2 <= lcx %s" C1092AE_P C1092MMPE_CTX (c1092ae_own C1092AE_P 9)),
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092wc_ctx] THEN DISCH_THEN(MP_TAC o SPEC `1`) THEN
  REWRITE_TAC[ARITH; c1092mmpe_mmmp; c1092wc_wfc; c1092wc_wfs; c1092wc_wfu; c1092wc_wfv;
              c1092wc_lfc; c1092wc_lfs; c1092wc_lfu; c1092wc_lfv] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[lcx; lcy] THEN REAL_ARITH_TAC);;

let c1092mss_chart [c; s; u; v; a] =
  [mk_comb(`(--):real->real`, s); c;
   list_mk_comb(`(-):real->real->real`,
     [list_mk_comb(`(-):real->real->real`, [u; mk_comb(`(*) (&2:real)`, c)]); mk_comb(`(*) (&2:real)`, s)]);
   list_mk_comb(`(+):real->real->real`,
     [list_mk_comb(`(-):real->real->real`, [v; mk_comb(`(*) (&2:real)`, c)]); mk_comb(`(*) (&2:real)`, s)]);
   a];;

(* Lean: exists_positive *)
let C1092MSS_EXISTS_POSITIVE = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> ?cC sC uC vC aC. cC * cC + sC * sC = &1 /\\ &0 < aC /\\
      c1092mss_positiveActual c1 c2 a b l cC sC uC vC aC" C1092AE_P C1092AE_HYP C1092MMPE_CTX C1092MSS_NEAR),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[c1092mss_positiveActual] THEN CONV_TAC C1092MO_CODE_CONV THEN
  let o5 = c1092mo_own 5 and o9 = c1092mo_own 9 in
  let k5 = c1092mss_chart o5 and k9 = c1092mss_chart o9 in
  let near = CONV_RULE C1092MO_CODE_CONV (ASSUME (parse_term C1092MSS_NEAR)) in
  let inward = CONV_RULE C1092MO_CODE_CONV (MP (SPECL C1092MMPE_V C1092MSS_INWARD_PAIR)
    (end_itlist CONJ [ASSUME C1092MO_NP; ASSUME C1092MO_IMG; ASSUME C1092MO_CTX; ASSUME (parse_term C1092MSS_NEAR)])) in
  let bottom = c1092mo_use C1092MBP_PAIR in
  let rorig = c1092mo_use C1092MO_RIGHT_ORIGIN in
  let nwc = c1092mo_use C1092MPC_NORTHWEST_CENTER in
  let tip = CONV_RULE C1092MO_CODE_CONV (UNDISCH (SPECL C1092MMPE_V C1092MSS_TIP)) in
  let cut = CONV_RULE C1092MO_CODE_CONV (UNDISCH (SPECL C1092MMPE_V C1092MSS_CUT)) in
  let mss_u5 = MATCH_MP C1092MSS_CHART_UNIT (c1092mo_unit 5)
  and mss_u9 = MATCH_MP C1092MSS_CHART_UNIT (c1092mo_unit 9) in
  let center9 = MATCH_MP (SPECL o9 C1092MSS_CENTER_CHART) (c1092mo_unit 9) in
  let box9 = REWRITE_RULE[lcont] (c1092mo_box 9) in
  let bar = GEN `x:real` (DISCH `&0 <= x` (DISCH `x <= &13 / &50`
    (c1092mo_excl 5 10 (MATCH_MP C1092MSS_RIGHT_BAR (end_itlist CONJ
       [rorig; near; ASSUME `&0 <= x`; ASSUME `x <= &13 / &50`]))))) in
  let disj59 = c1092mo_apart 5 9 in
  MP_TAC(SPECL k5 CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [REWRITE_TAC[mss_u5; c1092mo_pos ()]; ALL_TAC] THEN
  REWRITE_TAC[C1092MSS_INSIDE_CHART] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < s'` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `c977cc_normal c' (--s')` ASSUME_TAC THENL
     [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `abs s' <= c'` THEN UNDISCH_TAC `s' <= &0` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC (SPECL ([`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] @ k9) C1092SBN_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[C1092MSS_INSIDE_CHART; ldisj; mss_u9; center9; c1092mo_pos (); c1092mo_side ()] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[CONJUNCT1 inward; CONJUNCT2 inward; CONJUNCT2 bottom; tip;
                c1092mo_seed 5 (`&47 / &20`, `&33 / &20`); c1092mo_seed 9 (`&2`, `&457 / &500`);
                c1092mo_excl 5 7 nwc; c1092mo_excl 5 9 (CONJUNCT1 bottom); c1092mo_excl 5 10 near;
                c1092mo_side (); c1092mo_pos ()] THEN
    REPEAT CONJ_TAC THEN FIRST
     [ACCEPT_TAC bar;
      REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP box9) THEN REAL_ARITH_TAC;
      MP_TAC cut THEN REAL_ARITH_TAC;
      REPEAT GEN_TAC THEN REWRITE_TAC[disj59]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
  UNDISCH_TAC `abs s' <= c'` THEN UNDISCH_TAC `&0 < s'` THEN REAL_ARITH_TAC);;
