(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveLeftOwnVBounds.lean (Jatloe, N12-jatloe; *)
(* namespace N12Compact.PositiveLeftOwnVBounds).  The vertex margin for an   *)
(* incoming separator on the left square's own V face.  Normal is            *)
(* c977cc_normal; vertexDefect is pcplb_vertexdefect; F is pccm_f.           *)
(* The Lean auxiliaries X, E, D are used multiplied by p (PLOVB_XP, ..),     *)
(* which keeps every identity polynomial.                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/PositiveCentralCrossMargin.ml";;
needs "n12/geometry/PositiveCentralPositiveLeftBounds.ml";;
needs "n12/geometry/PositiveLeftOwnVEndpoint.ml";;

let PLOVB_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PLOVB_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;

let PLOVB_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_TAC];;

let PLOVB_NONNEG_OF_MUL = prove
 (`forall k y. &0 < k /\ &0 <= k * y ==> &0 <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* p times the Lean auxiliaries *)
let plovb_a = `&2 - p - &2 * q + p * q`;;
let plovb_xp = `p - (&1 - p) * (&1 - q) - p * q * (&1 - p)`;;
let plovb_ep = `--(&2) * p + q * (p + q - &457 / &500) +
                (p - (&1 - p) * (&1 - q) - p * q * (&1 - p))`;;
let plovb_dp c s =
  subst [c,`cc:real`; s,`ss:real`]
   `p * (cc + ss - (&2 - p - &2 * q + p * q) * cc * ss) +
    (--(&2) * p + q * (p + q - &457 / &500) +
     (p - (&1 - p) * (&1 - q) - p * q * (&1 - p))) * ss pow 2 -
    (p - (&1 - p) * (&1 - q) - p * q * (&1 - p))`;;

(* Lean: endpoint_bottom *)
let PLOVB_ENDPOINT_BOTTOM = prove
 (`forall p q l r. c977cc_normal p q /\ c977cc_normal l r /\ &9 / &10 <= p /\ r <= q
     ==> l pow 2 * (&1 - pcplb_vertexdefect p q - q * (&1 - p)) +
         l * r * (&2 - q * (&1 - p)) <= l + r * pccm_f p q l r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PLOVB_USE C977CSB_COSINE_ORDER [`p:real`; `q:real`; `l:real`; `r:real`] THEN
  PLOVB_USE C977CSB_DOT_LE_ONE [`p:real`; `q:real`; `l:real`; `r:real`] THEN
  PLOVB_USE C977CSB_ARC_CHORD [`p:real`; `q:real`; `l:real`; `r:real`; `&0`] THEN
  PLOVB_NORMAL_TAC THEN
  SUBGOAL_THEN `q <= &11 / &25` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   PLOVB_PROD_TAC `p - &9 / &10` `p + &9 / &10` THEN
   MP_TAC(SPECL [`q - &11 / &25`; `q + &11 / &25`] REAL_LT_MUL) THEN
   ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  (* the p-scaled facts *)
  PLOVB_PROD_TAC `&1 - p` `&1 - q` THEN PLOVB_PROD_TAC `q:real` `&1 - p` THEN
  PLOVB_PROD_TAC `p:real` `q * (&1 - p)` THEN
  SUBGOAL_THEN (mk_comb(mk_comb(`(<=):real->real->bool`,plovb_xp),`p:real`)) ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PLOVB_PROD_TAC `&2 - p` `&1 - q` THEN
  SUBGOAL_THEN (mk_comb(mk_comb(`(<=):real->real->bool`,`&0`),plovb_a)) ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN (mk_comb(mk_comb(`(<=):real->real->bool`,plovb_a),`&1`)) ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PLOVB_PROD_TAC `q:real` `&263 / &500 - (p + q - &457 / &500)` THEN
  SUBGOAL_THEN `q * (p + q - &457 / &500) <= (&3 / &10) * p` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN (mk_comb(mk_comb(`(<=):real->real->bool`,plovb_ep),`--(&7 / &10) * p`))
    ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  (* the endpoint (p,q) *)
  PLOVB_PROD_TAC `p pow 2` `q:real` THEN
  PLOVB_PROD_TAC `p pow 2 * q` `p + q - &1` THEN
  PLOVB_PROD_TAC `q:real` `(&543 / &500) * p - &457 / &500` THEN
  PLOVB_PROD_TAC `q pow 2`
    `p pow 2 * q * (p + q - &1) + q * ((&543 / &500) * p - &457 / &500) + &1 - p` THEN
  SUBGOAL_THEN
   (mk_eq(mk_comb(mk_comb(`( * ):real->real->real`,`&1 + p`),plovb_dp `p:real` `q:real`),
     `q pow 2 * (p pow 2 * q * (p + q - &1) + q * ((&543 / &500) * p - &457 / &500) + &1 - p)`))
   ASSUME_TAC THENL
  [UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN (mk_comb(mk_comb(`(<=):real->real->bool`,`&0`),plovb_dp `p:real` `q:real`))
    ASSUME_TAC THENL
  [MATCH_MP_TAC PLOVB_NONNEG_OF_MUL THEN EXISTS_TAC `&1 + p` THEN
   CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  (* the circle chord *)
  SUBGOAL_THEN `&0 <= q * l - q + r - r * p` ASSUME_TAC THENL
  [MATCH_MP_TAC PLOVB_NONNEG_OF_MUL THEN EXISTS_TAC `p:real` THEN
   CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `q * ((&1 - &0 * r) * (p * l + q * r)) - ((q - r) * p + r * (&1 - &0 * q)) =
                 p * (q * l - q + r - r * p)` ASSUME_TAC THENL
   [UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p * (l - p) <= q * (q - r)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  (* the correction, scaled by p *)
  PLOVB_PROD_TAC `q:real` `r:real` THEN
  PLOVB_PROD_TAC `q:real` `&1 - (&2 - p - &2 * q + p * q)` THEN
  SUBGOAL_THEN `(&2 - p - &2 * q + p * q) * q <= p / &2` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PLOVB_PROD_TAC `&2 - p - &2 * q + p * q` `q * r` THEN
  PLOVB_PROD_TAC `(&2 - p - &2 * q + p * q) * (q * r)` `q * (q - r) - p * (l - p)` THEN
  PLOVB_PROD_TAC `q * r` `q - r` THEN
  PLOVB_PROD_TAC `(q * r) * (q - r)`
   (mk_comb(mk_comb(`(-):real->real->real`,mk_comb(`(--):real->real`,plovb_ep)),
     `(&2 - p - &2 * q + p * q) * q`)) THEN
  (* the three-point combination *)
  PLOVB_PROD_TAC `q - r` (mk_comb(mk_comb(`(-):real->real->real`,`p:real`),plovb_xp)) THEN
  PLOVB_PROD_TAC `r:real` (plovb_dp `p:real` `q:real`) THEN
  PLOVB_PROD_TAC `p:real` `q * l - q + r - r * p` THEN
  SUBGOAL_THEN
   (mk_eq(list_mk_comb(`(-):real->real->real`,
      [list_mk_comb(`(-):real->real->real`,
        [mk_comb(mk_comb(`( * ):real->real->real`,`q:real`),plovb_dp `l:real` `r:real`);
         mk_comb(mk_comb(`( * ):real->real->real`,`q - r`),plovb_dp `&1` `&0`)]);
       mk_comb(mk_comb(`( * ):real->real->real`,`r:real`),plovb_dp `p:real` `q:real`)]),
     list_mk_comb(`(-):real->real->real`,
      [list_mk_comb(`(-):real->real->real`,
        [`p * (q * l - q + r - r * p)`;
         `(&2 - p - &2 * q + p * q) * q * r * p * (l - p)`]);
       mk_comb(mk_comb(`( * ):real->real->real`,plovb_ep),`q * r * (q - r)`)])))
   ASSUME_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN (mk_comb(mk_comb(`(<=):real->real->bool`,`&0`),
     mk_comb(mk_comb(`( * ):real->real->real`,`q:real`),plovb_dp `l:real` `r:real`)))
    ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN (mk_comb(mk_comb(`(<=):real->real->bool`,`&0`),plovb_dp `l:real` `r:real`))
    ASSUME_TAC THENL
  [ASM_CASES_TAC `q = &0` THENL
   [SUBGOAL_THEN `r = &0` SUBST_ALL_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `l = &1` SUBST_ALL_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `l <= &1 /\ &1 <= l ==> l = &1`) THEN
     CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
    NLIN_TAC ~deg2:false [];
    MATCH_MP_TAC PLOVB_NONNEG_OF_MUL THEN EXISTS_TAC `q:real` THEN
    CONJ_TAC THEN RASM_ARITH_TAC];
   ALL_TAC] THEN
  (* the gap identity *)
  SUBGOAL_THEN `max (q * l - p * r) (&0) = q * l - p * r` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `y <= x ==> max x y = x`) THEN
   PLOVB_PROD_TAC `l:real` `q - r` THEN PLOVB_PROD_TAC `r:real` `l - p` THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN
   (mk_eq(`p * ((l + r * pccm_f p q l r) -
                (l pow 2 * (&1 - pcplb_vertexdefect p q - q * (&1 - p)) +
                 l * r * (&2 - q * (&1 - p))))`, plovb_dp `l:real` `r:real`))
   ASSUME_TAC THENL
  [ASM_REWRITE_TAC[pccm_f; pcplb_vertexdefect] THEN
   UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN UNDISCH_TAC `l pow 2 + r pow 2 = &1` THEN
   SUBGOAL_THEN `~(p = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  MATCH_MP_TAC PLOVB_NONNEG_OF_MUL THEN EXISTS_TAC `p:real` THEN
  CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: vertex_margin *)
let PLOVB_VERTEX_MARGIN = prove
 (`forall p q C S l r.
     c977cc_normal p q /\ c977cc_normal C S /\ c977cc_normal l r /\
     q <= S /\ r <= S /\ &9 / &10 <= p /\ &4 / &5 <= C /\ S <= &3 / &5
     ==> l pow 2 * (&1 - pcplb_vertexdefect C S - S * (&1 - p)) +
         l * r * (&2 - S * (&1 - C)) <= l + r * pccm_f p q l r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PLOVB_NORMAL_TAC THEN
  PLOVB_PROD_TAC `l:real` `r:real` THEN
  ASM_CASES_TAC `q <= r` THENL
  [PLOVB_USE PLOVE_ENDPOINT_LEFT [`p:real`; `q:real`; `l:real`; `r:real`] THEN
   PLOVB_USE C977CSB_COSINE_ORDER [`C:real`; `S:real`; `l:real`; `r:real`] THEN
   PLOVB_USE PCPLB_DEFECT_ORDER [`l:real`; `r:real`; `C:real`; `S:real`] THEN
   PLOVB_PROD_TAC `l pow 2` `pcplb_vertexdefect C S - pcplb_vertexdefect l r` THEN
   PLOVB_PROD_TAC `S - r` `&1 - p` THEN
   PLOVB_PROD_TAC `l pow 2` `(S - r) * (&1 - p)` THEN
   PLOVB_PROD_TAC `S - r` `&1 - l` THEN
   PLOVB_PROD_TAC `l * r` `(S - r) * (&1 - l)` THEN
   PLOVB_PROD_TAC `l * r` `S:real` THEN
   PLOVB_PROD_TAC `(l * r) * S` `l - C` THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  PLOVB_USE PLOVB_ENDPOINT_BOTTOM [`p:real`; `q:real`; `l:real`; `r:real`] THEN
  PLOVB_USE C977CSB_COSINE_ORDER [`C:real`; `S:real`; `p:real`; `q:real`] THEN
  PLOVB_USE PCPLB_DEFECT_ORDER [`p:real`; `q:real`; `C:real`; `S:real`] THEN
  PLOVB_PROD_TAC `l pow 2` `pcplb_vertexdefect C S - pcplb_vertexdefect p q` THEN
  PLOVB_PROD_TAC `S - q` `&1 - p` THEN
  PLOVB_PROD_TAC `l pow 2` `(S - q) * (&1 - p)` THEN
  PLOVB_PROD_TAC `l * r` `(S - q) * (&1 - p)` THEN
  PLOVB_PROD_TAC `l * r` `S:real` THEN
  PLOVB_PROD_TAC `(l * r) * S` `p - C` THEN
  NLIN_TAC ~deg2:false []);;
