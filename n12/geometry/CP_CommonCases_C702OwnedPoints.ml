(* ========================================================================= *)
(* Phase 2: Compact/Completion/CommonCases/C702OwnedPoints.lean              *)
(* (namespace N12Compact.CommonCases.C702).  The owned points of the C702    *)
(* owners.  owner p m is the 5-tuple (ooc .. m) (oos .. m) (oou .. m)        *)
(* (oov .. m) l; Lean structure OwnedPoints p is c702op_owned_points.        *)
(* The proof is forward: every fact is a theorem under the hypotheses        *)
(* NPACK c1 c2 a b l and IMAGE binarysum (FFP ..) = c702e_family.            *)
(* Singleton segments and pairs: MPSB_* (MergedPending/SingletonBars, the    *)
(* same seed + segment argument); base_pairs: C702E_BASE_PAIRS;              *)
(* SouthwestPoint.point: CCSWP_POINT; MergedNearPoint.points_original:       *)
(* CCMNP_POINTS_ORIGINAL; some_auxiliary: C702E_SOME_AUXILIARY;              *)
(* normalized_diameter_bound: DIA_NORMALIZED_DIAMETER_BOUND.                 *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_C702Entrance.ml";;
needs "n12/geometry/CP_CommonCases_SouthwestPoint.ml";;
needs "n12/geometry/CP_CommonCases_MergedNearPoint.ml";;
needs "n12/geometry/CP_OtherCases_MergedPending_SingletonBars.ml";;
needs "n12/certlib/Diameter.ml";;

(* Lean: seed_point *)
let C702OP_SEED_POINT m p = oo_inst `c702e_family` (oo_seed m p);;

(* Lean: OwnedPoints (structure) *)
let c702op_owned_points = new_definition
 `c702op_owned_points (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) <=>
    (forall x. &28 / &25 <= x /\ x <= &87 / &50 ==> linside (ooc c1 c2 a b l 1) (oos c1 c2 a b l 1) (oou c1 c2 a b l 1) (oov c1 c2 a b l 1) l x (&1)) /\
    (forall y. &28 / &25 <= y /\ y <= &87 / &50 ==> linside (ooc c1 c2 a b l 2) (oos c1 c2 a b l 2) (oou c1 c2 a b l 2) (oov c1 c2 a b l 2) l (&1) y) /\
    (forall x. &113 / &50 <= x /\ x <= &72 / &25 ==> linside (ooc c1 c2 a b l 16) (oos c1 c2 a b l 16) (oou c1 c2 a b l 16) (oov c1 c2 a b l 16) l x (&3)) /\
    (forall y. &113 / &50 <= y /\ y <= &72 / &25 ==> linside (ooc c1 c2 a b l 32) (oos c1 c2 a b l 32) (oou c1 c2 a b l 32) (oov c1 c2 a b l 32) l (&3) y) /\
    linside (ooc c1 c2 a b l 256) (oos c1 c2 a b l 256) (oou c1 c2 a b l 256) (oov c1 c2 a b l 256) l (&2) (&87 / &50) /\
    linside (ooc c1 c2 a b l 256) (oos c1 c2 a b l 256) (oou c1 c2 a b l 256) (oov c1 c2 a b l 256) l (&87 / &50) (&2) /\
    linside (ooc c1 c2 a b l 16384) (oos c1 c2 a b l 16384) (oou c1 c2 a b l 16384) (oov c1 c2 a b l 16384) l (&3) (&87 / &50) /\
    linside (ooc c1 c2 a b l 16384) (oos c1 c2 a b l 16384) (oou c1 c2 a b l 16384) (oov c1 c2 a b l 16384) l (&3) (&8 / &5) /\
    linside (ooc c1 c2 a b l 32768) (oos c1 c2 a b l 32768) (oou c1 c2 a b l 32768) (oov c1 c2 a b l 32768) l (&8 / &5) (&3) /\
    linside (ooc c1 c2 a b l 32768) (oos c1 c2 a b l 32768) (oou c1 c2 a b l 32768) (oov c1 c2 a b l 32768) l (&87 / &50) (&3) /\
    linside (ooc c1 c2 a b l 1536) (oos c1 c2 a b l 1536) (oou c1 c2 a b l 1536) (oov c1 c2 a b l 1536) l (&2) (&113 / &50) /\
    linside (ooc c1 c2 a b l 1536) (oos c1 c2 a b l 1536) (oou c1 c2 a b l 1536) (oov c1 c2 a b l 1536) l (&113 / &50) (&2) /\
    linside (ooc c1 c2 a b l 6144) (oos c1 c2 a b l 6144) (oou c1 c2 a b l 6144) (oov c1 c2 a b l 6144) l (&1) (&113 / &50)`;;
(* fields: bottomSingleton, leftSingleton, topSingleton, rightSingleton, southInward, southElbow, rightInward, rightOutward, topLeft, topElbow, mergedInward, mergedElbow, northInward *)

let C702OP_F = `c702e_family`;;
let C702OP_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let C702OP_NP = `NPACK c1 c2 a b l`;;
let C702OP_IMG = `IMAGE binarysum (FFP c1 c2 a b l) = c702e_family`;;
let C702OP_H = CONJ (ASSUME C702OP_NP) (ASSUME C702OP_IMG);;

let c702op_owner m =
  let mt = mk_small_numeral m in
  map (fun f -> list_mk_comb(f, C702OP_VARS @ [mt])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let c702op_lin m x y = list_mk_comb(`linside`, c702op_owner m @ [x; y]);;
(* mask and point of a fact  linside (owner m) x y *)
let c702op_parts th =
  let args = snd (strip_comb (concl th)) in
  (dest_small_numeral (rand (hd args)), el 5 args, el 6 args);;

let c702op_seed m p = MP (SPECL C702OP_VARS (C702OP_SEED_POINT m p)) C702OP_H;;
let c702op_bar th m =
  MP (SPECL (C702OP_VARS @ [C702OP_F]) th)
     (CONJ (ASSUME C702OP_NP) (CONJ (ASSUME C702OP_IMG) (in_fam m C702OP_F)));;
let c702op_at bar x = let th = SPEC x bar in MP th (REAL_ARITH (lhand (concl th)));;
let c702op_unit m = MP (SPECL (C702OP_VARS @ [mk_small_numeral m]) OO_UNIT) (ASSUME C702OP_NP);;
let C702OP_SIDE = MP (SPECL C702OP_VARS OO_SIDE) (ASSUME C702OP_NP);;
let C702OP_SIDE_LE = MP (SPECL C702OP_VARS OO_SIDE_LE) (ASSUME C702OP_NP);;
let C702OP_SIDE_POS = MP (REAL_ARITH `&1 < l ==> &0 < l`) C702OP_SIDE;;

(* ~(lin m x y /\ lin n x y) *)
let c702op_apart m n x y =
  let d = MP (SPECL C702OP_VARS (oo_apart C702OP_F m n)) C702OP_H in
  SPECL [x; y] (REWRITE_RULE[ldisj] d);;
(* Lean: foreign m n .. point : ~(owner m).Inside x y *)
let c702op_foreign m n thn =
  let (_, x, y) = c702op_parts thn in
  let lm = c702op_lin m x y in
  NOT_INTRO (DISCH lm (MP (NOT_ELIM (c702op_apart m n x y)) (CONJ (ASSUME lm) thn)));;

let c702op_mp th facts = MP th (EQT_ELIM (REWRITE_CONV facts (lhand (concl th))));;

(* the singleton bars and their endpoints *)
let C702OP_OSEG = c702op_bar MPSB_SINGLETON_BOTTOM 1;;
let C702OP_VSEG = c702op_bar MPSB_SINGLETON_LEFT 2;;
let C702OP_TRSEG = c702op_bar MPSB_SINGLETON_TOP 16;;
let C702OP_NRSEG = c702op_bar MPSB_SINGLETON_RIGHT 32;;
let C702OP_OHI = c702op_seed 1 (`&87 / &50`, `&1`);;
let C702OP_VHI = c702op_seed 2 (`&1`, `&87 / &50`);;
let C702OP_TRLO = c702op_seed 16 (`&113 / &50`, `&3`);;
let C702OP_NRLO = c702op_seed 32 (`&3`, `&113 / &50`);;

(* the base pairs and the auxiliary points they own *)
let C702OP_PAIRS =
  MP (SPECL (C702OP_VARS @ [C702OP_F]) MPSB_SINGLETON_PAIRS)
     (end_itlist CONJ ([ASSUME C702OP_NP; ASSUME C702OP_IMG] @
                       map (fun m -> in_fam m C702OP_F) [1; 2; 16; 32]));;
let C702OP_BASE =
  CONJUNCTS (REWRITE_RULE[INSERT_SUBSET; EMPTY_SUBSET]
    (MP (SPECL C702OP_VARS C702E_BASE_PAIRS)
        (CONJ (ASSUME C702OP_NP) (CONJ (ASSUME C702OP_IMG) C702OP_PAIRS))));;
let c702op_aux m j =
  let mt = mk_small_numeral m and jt = mk_small_numeral j in
  let mem = find (fun th -> lhand (concl th) = jt && rand (rand (concl th)) = mt) C702OP_BASE in
  EQ_MP (SYM (SPECL (C702OP_VARS @ [mt]) (oo_aux_point j))) mem;;

let C702OP_AINWARD = c702op_aux 256 4;;
let C702OP_AELBOW = c702op_aux 256 13;;
let C702OP_BOUTER = c702op_aux 8192 6;;
let C702OP_BELBOW = c702op_aux 8192 15;;
let C702OP_RINWARD = c702op_aux 16384 8;;
let C702OP_ROUTWARD = c702op_aux 16384 18;;
let C702OP_TLEFT = c702op_aux 32768 3;;
let C702OP_TELBOW = c702op_aux 32768 14;;
let C702OP_MARKA = c702op_seed 256 (`&33 / &20`, `&33 / &20`);;
let C702OP_MARKW0 = c702op_seed 1536 (`&47 / &20`, `&33 / &20`);;
let C702OP_MARKW1 = c702op_seed 1536 (`&47 / &20`, `&47 / &20`);;
let C702OP_MARKR = c702op_seed 16384 (`&1543 / &500`, `&2`);;

(* aNear: SouthwestPoint.point for owner 256 *)
let C702OP_ANEAR =
  c702op_mp (SPECL (c702op_owner 256) CCSWP_POINT)
    [c702op_unit 256; C702OP_SIDE; C702OP_MARKA; C702OP_AINWARD; C702OP_AELBOW;
     c702op_foreign 256 2 (c702op_at C702OP_VSEG `&33 / &20`);
     c702op_foreign 256 1 C702OP_OHI;
     c702op_foreign 256 1 (c702op_at C702OP_OSEG `&33 / &20`);
     c702op_foreign 256 2 C702OP_VHI];;

(* wInward, by contradiction with MergedNearPoint.points_original *)
let C702OP_WINWARD =
  let goal = c702op_lin 1536 `&2` `&113 / &50` in
  let missing = ASSUME (mk_neg goal) in
  let wnear = CONJUNCT1 (c702op_mp (SPECL (c702op_owner 1536) CCMNP_POINTS_ORIGINAL)
    [c702op_unit 1536; C702OP_SIDE; C702OP_MARKW0; C702OP_MARKW1;
     c702op_foreign 1536 256 C702OP_AINWARD; missing;
     c702op_foreign 1536 16384 C702OP_RINWARD; c702op_foreign 1536 32 C702OP_NRLO;
     c702op_foreign 1536 16384 C702OP_MARKR]) in
  let f = MP (NOT_ELIM (c702op_apart 256 1536 `&39 / &20` `&39 / &20`)) (CONJ C702OP_ANEAR wnear) in
  CCONTR goal f;;

(* the facts available to exclude an auxiliary point of owner m *)
let C702OP_KNOWN =
  [C702OP_OHI; C702OP_VHI; C702OP_TRLO; C702OP_NRLO;
   c702op_at C702OP_VSEG `&8 / &5`; c702op_at C702OP_OSEG `&8 / &5`;
   c702op_at C702OP_TRSEG `&12 / &5`; c702op_at C702OP_NRSEG `&12 / &5`;
   C702OP_AINWARD; C702OP_AELBOW; C702OP_BOUTER; C702OP_BELBOW; C702OP_RINWARD;
   C702OP_ROUTWARD; C702OP_TLEFT; C702OP_TELBOW; C702OP_MARKA; C702OP_MARKW0;
   C702OP_MARKW1; C702OP_MARKR; C702OP_WINWARD];;

let c702op_rat t = rat_of_term t;;
(* |- lin m x y = lin m x' y'  for rationally equal coordinates *)
let c702op_repoint th x' y' =
  let (_, x, y) = c702op_parts th in
  let eq a b = if a = b then REFL a else EQT_ELIM (REAL_RAT_REDUCE_CONV (mk_eq(a, b))) in
  EQ_MP (MK_COMB(AP_TERM (rator (rator (concl th))) (eq x x'), eq y y')) th;;

(* from  lin_k : linside (owner m) x y, derive the target (another linside of
   owner m): it is the target, or it clashes with a known point of another
   owner, or it is too far from a known point of owner m (diameter bound) *)
let c702op_resolve target known lin_k =
  let (m, x, y) = c702op_parts lin_k in
  let tth = ASSUME target in
  let (_, tx, ty) = c702op_parts tth in
  let same p q = c702op_rat p =/ c702op_rat q in
  if same x tx && same y ty then c702op_repoint lin_k tx ty else
  try
    let thn = find (fun th -> let (n, x', y') = c702op_parts th in n <> m && same x x' && same y y') known in
    let (n, x', y') = c702op_parts thn in
    CONTR target (MP (NOT_ELIM (c702op_apart m n x' y')) (CONJ (c702op_repoint lin_k x' y') thn))
  with Failure _ ->
    let far th = let (n, x', y') = c702op_parts th in
      n = m && (let dx = c702op_rat x -/ c702op_rat x' and dy = c702op_rat y -/ c702op_rat y' in
                dx */ dx +/ dy */ dy >=/ (Num.num_of_int 2000000 // Num.num_of_int 982081)) in
    let thm = find far known in
    let (_, x', y') = c702op_parts thm in
    let d = MP (SPECL (c702op_owner m @ [x; y; x'; y']) DIA_NORMALIZED_DIAMETER_BOUND)
               (end_itlist CONJ [c702op_unit m; C702OP_SIDE_POS; C702OP_SIDE_LE; lin_k; thm]) in
    CONTR target (EQ_MP (REAL_RAT_REDUCE_CONV (concl d)) d);;

(* Lean: some_auxiliary + fin_cases j: the target point of owner m of kind k *)
let c702op_some_aux m k target known =
  let mt = mk_small_numeral m and kt = mk_small_numeral k in
  let ex = MP (SPECL (C702OP_VARS @ [mt; kt]) C702E_SOME_AUXILIARY)
              (end_itlist CONJ [ASSUME C702OP_NP; ASSUME C702OP_IMG; in_fam m C702OP_F;
                                ARITH_RULE (mk_binop `(<):num->num->bool` kt `2`);
                                EQF_ELIM (AUXEX_CONV (mk_binop `(IN):num->(num->bool)->bool` mt
                                                       (mk_comb(`auxex`, kt))))]) in
  let jv = `j:num` in
  let body = ASSUME (snd (dest_exists (concl ex))) in
  let cases = MP (ARITH_RULE `j < 10 ==> j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/
                                         j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9`) (CONJUNCT1 body) in
  let one eq =
    let lk = SUBS [eq] (CONJUNCT2 body) in
    let lk = CONV_RULE (RATOR_CONV (RAND_CONV (REWRITE_CONV[AUXPTS_EXPL.(k)] THENC ONCE_DEPTH_CONV EL_CONV THENC
                                                REWRITE_CONV[VECTOR_2])) THENC
                        RAND_CONV (REWRITE_CONV[AUXPTS_EXPL.(k)] THENC ONCE_DEPTH_CONV EL_CONV THENC
                                   REWRITE_CONV[VECTOR_2])) lk in
    c702op_resolve target known lk in
  let rec go th = if is_disj (concl th) then
      let p, q = dest_disj (concl th) in DISJ_CASES th (one (ASSUME p)) (go (ASSUME q))
    else one th in
  CHOOSE (jv, ex) (go cases);;

let C702OP_WELBOW = c702op_some_aux 1536 1 (c702op_lin 1536 `&113 / &50` `&2`) C702OP_KNOWN;;
let C702OP_NINWARD = c702op_some_aux 6144 0 (c702op_lin 6144 `&1` `&113 / &50`) C702OP_KNOWN;;

(* Lean: owned_points *)
let C702OP_OWNED_POINTS = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c702e_family
     ==> c702op_owned_points c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c702op_owned_points] THEN
  REPEAT CONJ_TAC THEN
  FIRST (map ACCEPT_TAC [C702OP_OSEG; C702OP_VSEG; C702OP_TRSEG; C702OP_NRSEG;
                         C702OP_AINWARD; C702OP_AELBOW; C702OP_RINWARD; C702OP_ROUTWARD;
                         C702OP_TLEFT; C702OP_TELBOW; C702OP_WINWARD; C702OP_WELBOW;
                         C702OP_NINWARD]));;
