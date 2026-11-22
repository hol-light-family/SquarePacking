(* ========================================================================= *)
(* Phase 2: Compact/Bridge/C1092WallSymmetry/OwnerTransport.lean.            *)
(* Exact family and physical-square transport under the container           *)
(* symmetries.  Conventions of OwnerFacts.ml / C1092WallCycle.ml: a Lean     *)
(* Transform <swap, reflectX, reflectY> is (sw, rx, ry) : bool#bool#bool,    *)
(* owners p i is the OriginalOwners owner 5-tuple at mask EL i c1092wc_code. *)
(* Transform.pull g q on 5-tuples is c1092ot_pull g (pullX / pullY /        *)
(* pullSwap of SymmetryBase, applied in Lean's order X, Y, Swap).            *)
(* g.pullPacking p of the packing (c1,c2,a,b,l) is the packing               *)
(* c1092ot_pk g (c1,c2,a,b) = (d1,d2,e1,e2) with the same side l, whose      *)
(* squares are exactly the 5-tuples g.pull (p.square i):                     *)
(*   reflectX: (\i. &4 - c1 i, c2, \i. --a i, b),                            *)
(*   reflectY: (c1, \i. &4 - c2 i, a, \i. --b i),  swap: (c2, c1, b, a)      *)
(* (C1092OT_PK_SQUARE); C1092OT_NPACK: it is a normalized packing.           *)
(* The private exact_owner_transport / pull_owner_code are merged into       *)
(* C1092OT_PULL_OWNER_CODE.  Tag C1092OT_.                                   *)
(* ========================================================================= *)

needs "n12/geometry/OwnerFacts.ml";;

(* ------------------------------------------------------------------------- *)
(* Transform.pull on 5-tuples and the transformed packing.                   *)
(* ------------------------------------------------------------------------- *)

let c1092ot_px = define
 `c1092ot_px (c:real, s:real, u:real, v:real, a:real) = (--c, s, u - &4 * c, --v - a - &4 * s, a)`;;
let c1092ot_py = define
 `c1092ot_py (c:real, s:real, u:real, v:real, a:real) = (c, --s, u - &4 * s, &4 * c - v - a, a)`;;
let c1092ot_psw = define
 `c1092ot_psw (c:real, s:real, u:real, v:real, a:real) = (s, c, u, --v - a, a)`;;

(* Lean: S12.Transform.pull *)
let c1092ot_pull = define
 `c1092ot_pull (sw,rx,ry) (q:real#real#real#real#real) =
    (if sw then c1092ot_psw else I) ((if ry then c1092ot_py else I) ((if rx then c1092ot_px else I) q))`;;

let c1092ot_kx = define
 `c1092ot_kx (c1:num->real, c2:num->real, a:num->real, b:num->real) =
    ((\i. &4 - c1 i), c2, (\i. --a i), b)`;;
let c1092ot_ky = define
 `c1092ot_ky (c1:num->real, c2:num->real, a:num->real, b:num->real) =
    (c1, (\i. &4 - c2 i), a, (\i. --b i))`;;
let c1092ot_ksw = define
 `c1092ot_ksw (c1:num->real, c2:num->real, a:num->real, b:num->real) = (c2, c1, b, a)`;;

(* Lean: S12.Transform.pullPacking (the four coordinate arrays; side unchanged) *)
let c1092ot_pk = define
 `c1092ot_pk (sw,rx,ry) (P:(num->real)#(num->real)#(num->real)#(num->real)) =
    (if sw then c1092ot_ksw else I) ((if ry then c1092ot_ky else I) ((if rx then c1092ot_kx else I) P))`;;

(* the transformed packing's squares are the pulled squares *)
let C1092OT_PK_SQUARE = prove
 (`forall g c1 c2 a b l d1 d2 e1 e2 (i:num). c1092ot_pk g (c1,c2,a,b) = (d1,d2,e1,e2)
     ==> (e1 i, e2 i, e1 i * d1 i + e2 i * d2 i - l / &2, --e2 i * d1 i + e1 i * d2 i - l / &2, l) =
         c1092ot_pull g (a i, b i, a i * c1 i + b i * c2 i - l / &2, --b i * c1 i + a i * c2 i - l / &2, l)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  MAP_EVERY BOOL_CASES_TAC [`p1:bool`; `p1':bool`; `p2:bool`] THEN
  REWRITE_TAC[c1092ot_pk; c1092ot_pull; c1092ot_kx; c1092ot_ky; c1092ot_ksw; I_THM;
              c1092ot_px; c1092ot_py; c1092ot_psw; PAIR_EQ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT CONJ_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The packing-level generators in these coordinates.                        *)
(* ------------------------------------------------------------------------- *)

let C1092OT_OSQ_X = prove
 (`forall x y a b l. osq x y (--a) b l = osq x y b a l`,
  MESON_TAC[OSQ_ROT]);;
let C1092OT_OSQ_Y = prove
 (`forall x y a b l. osq x y a (--b) l = osq x y b a l`,
  REWRITE_TAC[osq; EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC);;
let C1092OT_OWALLS_X = prove
 (`forall x y a b l. owalls x y (--a) b l <=> owalls x y b a l`,
  REWRITE_TAC[owalls; REAL_ABS_NEG] THEN REAL_ARITH_TAC);;
let C1092OT_OWALLS_Y = prove
 (`forall x y a b l. owalls x y a (--b) l <=> owalls x y b a l`,
  REWRITE_TAC[owalls; REAL_ABS_NEG] THEN REAL_ARITH_TAC);;
let C1092OT_OWNED_X = prove
 (`forall x y a b l. owned x y (--a) b l = owned x y b a l`,
  REWRITE_TAC[owned; C1092OT_OSQ_X]);;
let C1092OT_OWNED_Y = prove
 (`forall x y a b l. owned x y a (--b) l = owned x y b a l`,
  REWRITE_TAC[owned; C1092OT_OSQ_Y]);;

let C1092OT_NPACK_X = prove
 (`forall X Y a b l. NPACK X Y (\i. --a i) b l <=> NPACK X Y b a l`,
  REWRITE_TAC[NPACK; C1092OT_OSQ_X; C1092OT_OWALLS_X;
              REAL_ARITH `--x * --x + y * y = y * y + x * x`]);;
let C1092OT_NPACK_Y = prove
 (`forall X Y a b l. NPACK X Y a (\i. --b i) l <=> NPACK X Y b a l`,
  REWRITE_TAC[NPACK; C1092OT_OSQ_Y; C1092OT_OWALLS_Y;
              REAL_ARITH `x * x + --y * --y = y * y + x * x`]);;
let C1092OT_FFP_X = prove
 (`forall X Y a b l. FFP X Y (\i. --a i) b l = FFP X Y b a l`,
  REWRITE_TAC[FFP; C1092OT_OWNED_X]);;
let C1092OT_FFP_Y = prove
 (`forall X Y a b l. FFP X Y a (\i. --b i) l = FFP X Y b a l`,
  REWRITE_TAC[FFP; C1092OT_OWNED_Y]);;

let C1092OT_GEN_X = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l
     ==> NPACK (\i. &4 - c1 i) c2 (\i. --a i) b l /\
         FFP (\i. &4 - c1 i) c2 (\i. --a i) b l =
         IMAGE (IMAGE (\k. EL k [2; 3; 0; 1; 6; 7; 4; 5; 9; 8; 11; 10; 14; 13; 12; 15]))
               (FFP c1 c2 a b l)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP NPACK_RX) THEN
  REWRITE_TAC[C1092OT_NPACK_X; C1092OT_FFP_X]);;
let C1092OT_GEN_Y = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l
     ==> NPACK c1 (\i. &4 - c2 i) a (\i. --b i) l /\
         FFP c1 (\i. &4 - c2 i) a (\i. --b i) l =
         IMAGE (IMAGE (\k. EL k [6; 7; 4; 5; 2; 3; 0; 1; 11; 10; 9; 8; 12; 15; 14; 13]))
               (FFP c1 c2 a b l)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP NPACK_RY) THEN
  REWRITE_TAC[C1092OT_NPACK_Y; C1092OT_FFP_Y]);;

let C1092OT_SCAL_X = prove
 (`forall x y a b l. owned (&4 - x) y (--a) b l =
     IMAGE (\k. EL k [2; 3; 0; 1; 6; 7; 4; 5; 9; 8; 11; 10; 14; 13; 12; 15]) (owned x y a b l)`,
  REWRITE_TAC[C1092OT_OWNED_X] THEN REWRITE_TAC[OWNED_RX]);;
let C1092OT_SCAL_Y = prove
 (`forall x y a b l. owned x (&4 - y) a (--b) l =
     IMAGE (\k. EL k [6; 7; 4; 5; 2; 3; 0; 1; 11; 10; 9; 8; 12; 15; 14; 13]) (owned x y a b l)`,
  REWRITE_TAC[C1092OT_OWNED_Y] THEN REWRITE_TAC[OWNED_RY]);;

let C1092OT_TRIPLES =
  [(`false`,`false`,`false`); (`false`,`false`,`true`); (`false`,`true`,`false`); (`false`,`true`,`true`);
   (`true`,`false`,`false`); (`true`,`false`,`true`); (`true`,`true`,`false`); (`true`,`true`,`true`)];;

(* packing chain for a literal g: |- NPACK c1 c2 a b l ==> NPACK D l /\ FFP D l = IMAGE .. (FFP c1 c2 a b l) *)
let c1092ot_chain (sw, rx, ry) =
  let gens = (if rx = `true` then [C1092OT_GEN_X] else []) @ (if ry = `true` then [C1092OT_GEN_Y] else []) @
             (if sw = `true` then [NPACK_SW] else []) in
  let np0 = ASSUME `NPACK c1 c2 a b l` in
  let step (np, eq) gen =
    let th = MATCH_MP gen np in
    (CONJUNCT1 th, TRANS (CONJUNCT2 th) (AP_TERM (rator (rhs (concl (CONJUNCT2 th)))) eq)) in
  let np, eq = rev_itlist (fun gen acc -> step acc gen) gens (np0, REFL `FFP c1 c2 a b l`) in
  DISCH_ALL (CONJ np eq);;

(* scalar owned chain at index k: |- owned (D at k) = IMAGE .. (owned (c1 k) (c2 k) (a k) (b k) l) *)
let c1092ot_scalar (sw, rx, ry) =
  let k = `k:num` in
  let st0 = map (fun f -> mk_comb(f, k)) [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`] in
  let apply (st, eq) (th, f) =
    let th1 = SPECL (st @ [`l:real`]) th in
    (f st, TRANS th1 (AP_TERM (rator (rhs (concl th1))) eq)) in
  let neg t = mk_comb(`(--):real->real`, t) and four t = mk_binop `(-):real->real->real` `&4` t in
  let steps = (if rx = `true` then [(C1092OT_SCAL_X, (function [x;y;p;q] -> [four x; y; neg p; q] | _ -> []))] else []) @
              (if ry = `true` then [(C1092OT_SCAL_Y, (function [x;y;p;q] -> [x; four y; p; neg q] | _ -> []))] else []) @
              (if sw = `true` then [(OWNED_SW, (function [x;y;p;q] -> [y; x; q; p] | _ -> []))] else []) in
  snd (rev_itlist (fun s acc -> apply acc s) steps
         (st0, REFL (list_mk_comb(`owned`, st0 @ [`l:real`]))));;

(* binarysum (IMAGE f1 (.. (IMAGE fn (bitset m)))) for literal lambdas and m *)
let c1092ot_mask_conv tm =
  let rec inner t = if is_comb t && is_comb (rator t) && fst (dest_const (fst (strip_comb t))) = "IMAGE"
                    then inner (rand t) else t in
  if not (is_comb tm && rator tm = `binarysum`) then failwith "c1092ot_mask_conv" else
  let bs = inner (rand tm) in
  if not (is_comb bs && rator bs = `bitset`) then failwith "c1092ot_mask_conv" else
  let m = dest_small_numeral (rand bs) in
  let th1 = (REWRITE_CONV[bitset_bits m; GSYM SET_OF_LIST_MAP; MAP] THENC DEPTH_CONV BETA_CONV THENC
             DEPTH_CONV EL_CONV) tm in
  let ns = map dest_small_numeral (dest_list (rand (rand (rhs (concl th1))))) in
  let m' = itlist (fun i acc -> acc + (1 lsl i)) (setify ns) 0 in
  let b = binarysum_bits m' in
  let eq = prove(mk_eq(rand (rhs (concl th1)), rand (lhand (concl b))),
    REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM] THEN ARITH_TAC) in
  TRANS th1 (TRANS (AP_TERM `binarysum` eq) b);;

let C1092OT_ACT_LT = prove
 (`forall g i. i < 12 ==> c1092ws_owner_action g i < 12`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  C1092WSF_ENUM_TAC `i:num` 12 THEN
  MAP_EVERY BOOL_CASES_TAC [`p1:bool`; `p1':bool`; `p2:bool`] THEN
  REWRITE_TAC([c1092ws_owner_action; LET_DEF; LET_END_DEF] @ C1092WSF_LOOKUPS) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let C1092OT_ACT_LT' = prove
 (`forall i. i < 12 ==> forall g. c1092ws_owner_action g i < 12`,
  MESON_TAC[C1092OT_ACT_LT]);;

let C1092OT_FFP_BITSET = prove
 (`forall c1 c2 a b l G. G IN FFP c1 c2 a b l ==> G = bitset (binarysum G)`,
  REWRITE_TAC[FFP; IN_IMAGE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM ownmask; OWNED_BITSET]);;

(* the literal triple g occurring in a goal as c1092ws_owner_action g *)
let c1092ot_goal_triple w =
  let t = find_term (fun t -> is_comb t && is_const (rator t) &&
                              fst (dest_const (rator t)) = "c1092ws_owner_action") w in
  let x, yz = dest_pair (rand t) in let y, z = dest_pair yz in (x, y, z);;

(* Lean: (Transform.pullPacking is a NormalizedPacking) *)
let C1092OT_NPACK = prove
 (`forall g c1 c2 a b l d1 d2 e1 e2. NPACK c1 c2 a b l /\ c1092ot_pk g (c1,c2,a,b) = (d1,d2,e1,e2)
     ==> NPACK d1 d2 e1 e2 l`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  MAP_EVERY BOOL_CASES_TAC [`p1:bool`; `p1':bool`; `p2:bool`] THEN
  REWRITE_TAC[c1092ot_pk; c1092ot_kx; c1092ot_ky; c1092ot_ksw; I_THM; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM))) THEN
  FIRST (map (fun t -> MP_TAC(c1092ot_chain t) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN NO_TAC)
             C1092OT_TRIPLES));;

(* Lean: exact_owner_transport + pull_owner_code (private) *)
let C1092OT_PULL_OWNER_CODE = prove
 (`forall g c1 c2 a b l d1 d2 e1 e2 i.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family /\
     c1092ot_pk g (c1,c2,a,b) = (d1,d2,e1,e2) /\ i < 12
     ==> ownmask (d1 (oidx c1 c2 a b l (EL (c1092ws_owner_action g i) c1092wc_code)))
                 (d2 (oidx c1 c2 a b l (EL (c1092ws_owner_action g i) c1092wc_code)))
                 (e1 (oidx c1 c2 a b l (EL (c1092ws_owner_action g i) c1092wc_code)))
                 (e2 (oidx c1 c2 a b l (EL (c1092ws_owner_action g i) c1092wc_code))) l =
         EL i c1092wc_code`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  MAP_EVERY BOOL_CASES_TAC [`p1:bool`; `p1':bool`; `p2:bool`] THEN
  REWRITE_TAC[c1092ot_pk; c1092ot_kx; c1092ot_ky; c1092ot_ksw; I_THM; PAIR_EQ] THEN
  DISCH_THEN(fun th -> let a, r = CONJ_PAIR th in let b, r = CONJ_PAIR r in let e, c = CONJ_PAIR r in
    ASSUME_TAC a THEN ASSUME_TAC b THEN ASSUME_TAC c THEN
    MP_TAC e) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C1092OT_ACT_LT' o check (fun th -> concl th = `i < 12`)) THEN
  (fun (asl, w as gl) ->
     let x, y, z = c1092ot_goal_triple w in
     let g = mk_pair(x, mk_pair(y, z)) in
     let mtm = mk_comb(mk_comb(`EL:num->num list->num`,
                 mk_comb(mk_comb(`c1092ws_owner_action`, g), `i:num`)), `c1092wc_code`) in
     (MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                    `c1092wc_family`; mtm] OIDX_OWNED) THEN
      ASM_SIMP_TAC[C1092WC_MEMBER] THEN
      SPEC_TAC(mk_comb(list_mk_comb(`oidx`, [`c1:num->real`; `c2:num->real`; `a:num->real`;
                                            `b:num->real`; `l:real`]), mtm), `k:num`)) gl) THEN
  GEN_TAC THEN REWRITE_TAC[ownmask] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  (fun (asl, w as g) ->
     let tr = c1092ot_goal_triple w in
     ((if tr = (`false`,`false`,`false`) then ALL_TAC else SUBST1_TAC (c1092ot_scalar tr)) THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `i < 12` THEN SPEC_TAC(`i:num`, `i:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      REWRITE_TAC([c1092ws_owner_action; LET_DEF; LET_END_DEF] @ C1092WSF_LOOKUPS) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC C1092WSF_LOOKUPS THEN
      CONV_TAC(ONCE_DEPTH_CONV c1092ot_mask_conv) THEN REWRITE_TAC[]) g));;

(* the goals of MAP_EVERY BOOL_CASES_TAC [p1; p1'; p2] for g = (p1,p1',p2), in order *)
let C1092OT_ORDER =
  [(`true`,`true`,`true`); (`true`,`true`,`false`); (`true`,`false`,`true`); (`true`,`false`,`false`);
   (`false`,`true`,`true`); (`false`,`true`,`false`); (`false`,`false`,`true`); (`false`,`false`,`false`)];;

(* the image of the family under the composite mask action of the chain for t *)
let c1092ot_family_image t =
  let ch = c1092ot_chain t in
  let rec perms e = if is_comb e && is_comb (rator e) && fst (dest_const (fst (strip_comb e))) = "IMAGE"
                    then rand (rand (rator e)) :: perms (rand e) else [] in
  let ps = perms (rhs (concl (CONJUNCT2 (UNDISCH ch)))) in
  let body = itlist (fun p acc -> mk_comb(mk_comb(`IMAGE:(num->num)->(num->bool)->num->bool`, p), acc))
               ps `bitset m` in
  let f = mk_abs(`m:num`, mk_comb(`binarysum`, body)) in
  let tm = mk_eq(mk_comb(mk_comb(`IMAGE:(num->num)->(num->bool)->num->bool`, f), `c1092wc_family`),
                 `c1092wc_family`) in
  prove(tm, REWRITE_TAC[c1092wc_family; IMAGE_CLAUSES] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
            CONV_TAC(ONCE_DEPTH_CONV c1092ot_mask_conv) THEN CONV_TAC setlit_eq_dconv);;

let c1092ot_family_tac t =
  if t = (`false`,`false`,`false`) then ASM_REWRITE_TAC[] else
  MP_TAC(c1092ot_chain t) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM (c1092ot_family_image t)] THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && rhs (concl th) = `c1092wc_family`
                          then GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th] else NO_TAC) THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ_ON THEN
  X_GEN_TAC `G:num->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[IMAGE_o] THEN
  REPEAT AP_TERM_TAC THEN MATCH_MP_TAC C1092OT_FFP_BITSET THEN ASM_MESON_TAC[];;

(* Lean: family_transport *)
let C1092OT_FAMILY_TRANSPORT = prove
 (`forall g c1 c2 a b l d1 d2 e1 e2.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family /\
     c1092ot_pk g (c1,c2,a,b) = (d1,d2,e1,e2)
     ==> IMAGE binarysum (FFP d1 d2 e1 e2 l) = c1092wc_family`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  MAP_EVERY BOOL_CASES_TAC [`p1:bool`; `p1':bool`; `p2:bool`] THEN
  REWRITE_TAC[c1092ot_pk; c1092ot_kx; c1092ot_ky; c1092ot_ksw; I_THM; PAIR_EQ] THEN
  DISCH_THEN(fun th -> let a, r = CONJ_PAIR th in let b, e = CONJ_PAIR r in
    ASSUME_TAC a THEN ASSUME_TAC b THEN MP_TAC e) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM)) THENL
  map c1092ot_family_tac C1092OT_ORDER);;

(* Lean: owners_transport  (equality of the physical 5-tuples) *)
let C1092OT_OWNERS_TRANSPORT = prove
 (`forall g c1 c2 a b l d1 d2 e1 e2 i.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family /\
     c1092ot_pk g (c1,c2,a,b) = (d1,d2,e1,e2) /\ i < 12
     ==> (ooc d1 d2 e1 e2 l (EL i c1092wc_code), oos d1 d2 e1 e2 l (EL i c1092wc_code),
          oou d1 d2 e1 e2 l (EL i c1092wc_code), oov d1 d2 e1 e2 l (EL i c1092wc_code), l) =
         c1092ot_pull g
          (ooc c1 c2 a b l (EL (c1092ws_owner_action g i) c1092wc_code),
           oos c1 c2 a b l (EL (c1092ws_owner_action g i) c1092wc_code),
           oou c1 c2 a b l (EL (c1092ws_owner_action g i) c1092wc_code),
           oov c1 c2 a b l (EL (c1092ws_owner_action g i) c1092wc_code), l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `oidx d1 d2 e1 e2 l (EL i c1092wc_code) =
                oidx c1 c2 a b l (EL (c1092ws_owner_action g i) c1092wc_code)` ASSUME_TAC THENL
   [MATCH_MP_TAC OWNMASK_INJ THEN
    MAP_EVERY EXISTS_TAC [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`] THEN
    REWRITE_TAC[OIDX_LT] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[C1092OT_NPACK]; ALL_TAC] THEN
    MP_TAC(SPECL [`g:bool#bool#bool`; `c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
                  `l:real`; `d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `i:num`]
      C1092OT_PULL_OWNER_CODE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`; `i:num`]
      C1092WC_OWNER_CODE) THEN
    ASM_MESON_TAC[C1092OT_NPACK; C1092OT_FAMILY_TRANSPORT];
    ALL_TAC] THEN
  REWRITE_TAC[ooc; oos; oou; oov] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C1092OT_PK_SQUARE THEN ASM_REWRITE_TAC[]);;

(* Lean: central_transport *)
let C1092OT_CENTRAL_TRANSPORT = prove
 (`forall g c1 c2 a b l d1 d2 e1 e2 k.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family /\
     c1092ot_pk g (c1,c2,a,b) = (d1,d2,e1,e2) /\ k < 4
     ==> (ooc d1 d2 e1 e2 l (EL (EL k c1092wc_central) c1092wc_code),
          oos d1 d2 e1 e2 l (EL (EL k c1092wc_central) c1092wc_code),
          oou d1 d2 e1 e2 l (EL (EL k c1092wc_central) c1092wc_code),
          oov d1 d2 e1 e2 l (EL (EL k c1092wc_central) c1092wc_code), l) =
         c1092ot_pull g
          (ooc c1 c2 a b l (EL (EL (c1092ws_central_action g k) c1092wc_central) c1092wc_code),
           oos c1 c2 a b l (EL (EL (c1092ws_central_action g k) c1092wc_central) c1092wc_code),
           oou c1 c2 a b l (EL (EL (c1092ws_central_action g k) c1092wc_central) c1092wc_code),
           oov c1 c2 a b l (EL (EL (c1092ws_central_action g k) c1092wc_central) c1092wc_code), l)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM C1092WS_OWNERACTION_CENTRAL] THEN
  MATCH_MP_TAC C1092OT_OWNERS_TRANSPORT THEN ASM_REWRITE_TAC[] THEN C1092WC_IDX_TAC);;

(* Lean: wall_transport *)
let C1092OT_WALL_TRANSPORT = prove
 (`forall g c1 c2 a b l d1 d2 e1 e2 k.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family /\
     c1092ot_pk g (c1,c2,a,b) = (d1,d2,e1,e2) /\ k < 4
     ==> (ooc d1 d2 e1 e2 l (EL (EL k c1092wc_wall) c1092wc_code),
          oos d1 d2 e1 e2 l (EL (EL k c1092wc_wall) c1092wc_code),
          oou d1 d2 e1 e2 l (EL (EL k c1092wc_wall) c1092wc_code),
          oov d1 d2 e1 e2 l (EL (EL k c1092wc_wall) c1092wc_code), l) =
         c1092ot_pull g
          (ooc c1 c2 a b l (EL (EL (c1092ws_wall_action g k) c1092wc_wall) c1092wc_code),
           oos c1 c2 a b l (EL (EL (c1092ws_wall_action g k) c1092wc_wall) c1092wc_code),
           oou c1 c2 a b l (EL (EL (c1092ws_wall_action g k) c1092wc_wall) c1092wc_code),
           oov c1 c2 a b l (EL (EL (c1092ws_wall_action g k) c1092wc_wall) c1092wc_code), l)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM C1092WS_OWNERACTION_WALL] THEN
  MATCH_MP_TAC C1092OT_OWNERS_TRANSPORT THEN ASM_REWRITE_TAC[] THEN C1092WC_IDX_TAC);;

(* Lean: corner_transport *)
let C1092OT_CORNER_TRANSPORT = prove
 (`forall g c1 c2 a b l d1 d2 e1 e2 k.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family /\
     c1092ot_pk g (c1,c2,a,b) = (d1,d2,e1,e2) /\ k < 4
     ==> (ooc d1 d2 e1 e2 l (EL (EL k c1092wc_corner) c1092wc_code),
          oos d1 d2 e1 e2 l (EL (EL k c1092wc_corner) c1092wc_code),
          oou d1 d2 e1 e2 l (EL (EL k c1092wc_corner) c1092wc_code),
          oov d1 d2 e1 e2 l (EL (EL k c1092wc_corner) c1092wc_code), l) =
         c1092ot_pull g
          (ooc c1 c2 a b l (EL (EL (c1092ws_central_action g k) c1092wc_corner) c1092wc_code),
           oos c1 c2 a b l (EL (EL (c1092ws_central_action g k) c1092wc_corner) c1092wc_code),
           oou c1 c2 a b l (EL (EL (c1092ws_central_action g k) c1092wc_corner) c1092wc_code),
           oov c1 c2 a b l (EL (EL (c1092ws_central_action g k) c1092wc_corner) c1092wc_code), l)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM C1092WS_OWNERACTION_CORNER] THEN
  MATCH_MP_TAC C1092OT_OWNERS_TRANSPORT THEN ASM_REWRITE_TAC[] THEN C1092WC_IDX_TAC);;
