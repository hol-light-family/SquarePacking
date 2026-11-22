(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C580581TripleEntrance.lean         *)
(* (N12Compact.FiniteCases.C580581TripleEntrance).  Both original C580/C581  *)
(* families enter the same physical three-square problem as C983.  Every     *)
(* frame represents its actual original owner and all three pairwise         *)
(* disjointness statements are retained.  This is an entrance only.          *)
(* Statements indexed by v : Fin 2 are OCaml arrays of the two theorems      *)
(* (family v = C580E_FAM.(v), bottomMask v = C580E_BOTTOM.(v)); an           *)
(* OpenSquare E is a 5-tuple with explicit unit normal / positive side;      *)
(* (owner p m).translated 2 2 is the tuple                                   *)
(* (c, s, u - (c * &2 + s * &2), v - (--s * &2 + c * &2), a)                 *)
(* (OCTOE_INSIDE_TRANSLATED).  canonical_frame = CLF_CANONICAL_FRAME;        *)
(* InwardSign.positive_impossible = OCISG_POSITIVE_IMPOSSIBLE;               *)
(* UpperBarPoint / TopOnlyLeftPoint.point_original = OCUBP_ / OCTOLP_POINT_  *)
(* ORIGINAL; TopOnlyQuadrantProfile.frame / Data = OCTOQP_FRAME /            *)
(* octoqp_data; RightTripleData.right_frame / Input = OCRTD_RIGHT_FRAME /    *)
(* ocrtd_input; NegativeTripleFaces.faces = CCNTF_FACES.  The geometric      *)
(* steps are the generic lemmas C580TE_*_CORE, instantiated at the owners.   *)
(* Tag C580TE_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C580581UpperChain.ml";;
needs "n12/geometry/CP_OtherCases_InwardSign.ml";;
needs "n12/geometry/CP_OtherCases_UpperBarPoint.ml";;
needs "n12/geometry/CP_OtherCases_RightTripleData.ml";;

(* Lean: bottom_bar + foreign (private): the bottom owner B's bar excludes A *)
let C580TE_HBAR_AVOID = prove
 (`forall cA sA uA vA aA cB sB uB vB aB.
     linside cB sB uB vB aB (&113 / &50) (&1) /\ linside cB sB uB vB aB (&14 / &5) (&1) /\
     ldisj cA sA uA vA aA cB sB uB vB aB
     ==> forall x. &113 / &50 <= x /\ x <= &14 / &5 ==> ~linside cA sA uA vA aA x (&1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `&113 / &50`; `&14 / &5`; `&1`; `x:real`] OO_HORIZONTAL_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* Lean: right_bar + foreign (private): the right owner R's bar excludes Q *)
let C580TE_VBAR_AVOID = prove
 (`forall cQ sQ uQ vQ aQ cR sR uR vR aR.
     linside cR sR uR vR aR (&3) (&2) /\ linside cR sR uR vR aR (&3) (&14 / &5) /\
     ldisj cQ sQ uQ vQ aQ cR sR uR vR aR
     ==> forall y. &113 / &50 <= y ==> y <= &64 / &25 ==> ~linside cQ sQ uQ vQ aQ (&3) y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN
  X_GEN_TAC `y:real` THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                `&3`; `&2`; `&14 / &5`; `y:real`] OO_VERTICAL_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let C580TE_IFF_TAC =
  REPEAT GEN_TAC THEN FIRST_ASSUM(fun th ->
    if is_forall(concl th) && is_iff(snd(strip_forall(concl th))) then REWRITE_TAC[th]
    else NO_TAC) THEN REWRITE_TAC[REAL_ADD_SYM];;

(* Lean: southeast_negative_frame (generic part): A = owner 512, M = owner 2304 *)
let C580TE_SOUTHEAST_FRAME_CORE = prove
 (`forall cM sM uM vM aM cA sA uA vA aA.
     cM * cM + sM * sM = &1 /\ &0 < aM /\ cA * cA + sA * sA = &1 /\ &0 < aA /\
     &1 < aA /\ aM = aA /\
     linside cM sM uM vM aM (&33 / &20) (&33 / &20) /\
     linside cM sM uM vM aM (&2) (&2) /\
     linside cM sM uM vM aM (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     ~linside cA sA uA vA aA (&3) (&87 / &50) /\
     (forall x. &113 / &50 <= x /\ x <= &14 / &5 ==> ~linside cA sA uA vA aA x (&1)) /\
     ldisj cM sM uM vM aM cA sA uA vA aA
     ==> exists cE sE uE vE aE.
           cE * cE + sE * sE = &1 /\ &0 < aE /\
           &0 < cE /\ sE < &0 /\ --sE <= cE /\ aE = aA /\
           (forall x y. linside cE sE uE vE aE x y <=> linside cA sA uA vA aA (x + &2) (y + &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA - (cA * &2 + sA * &2)`; `vA - (--sA * &2 + cA * &2)`;
                `aA:real`] CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[OCTOE_INSIDE_TRANSLATED; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aE:real = aA`)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (find_term ((=) `lclosed`)) (concl th))) THEN
  SUBGOAL_THEN `sE < &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`cM:real`; `sM:real`; `uM - (cM * &2 + sM * &2)`; `vM - (--sM * &2 + cM * &2)`;
                  `aM:real`; `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aA:real`]
      OCISG_POSITIVE_IMPOSSIBLE) THEN
    MATCH_MP_TAC(TAUT `forall p. p ==> (p ==> false) ==> false`) THEN
    REWRITE_TAC[ldisj; OCTOE_INSIDE_TRANSLATED] THEN
    FIRST_ASSUM(fun th ->
      if is_forall(concl th) && is_iff(snd(strip_forall(concl th))) then REWRITE_TAC[th]
      else NO_TAC) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           UNDISCH_TAC `abs sE <= cE` THEN RASM_ARITH_TAC;
           RASM_ARITH_TAC;
           X_GEN_TAC `x:real` THEN DISCH_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
             RASM_ARITH_TAC;
           REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aA:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `abs sE <= cE` THEN RASM_ARITH_TAC; C580TE_IFF_TAC]);;

(* Lean: northeast_profile (generic part): Q = owner 1024 *)
let C580TE_NORTHEAST_PROFILE_CORE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     linside c s u v a (&12 / &5) (&3) /\ linside c s u v a (&113 / &50) (&3) /\
     linside c s u v a (&5 / &2) (&3) /\
     ~linside c s u v a (&2) (&113 / &50) /\ ~linside c s u v a (&2) (&3) /\
     ~linside c s u v a (&3) (&3) /\
     (forall y. &113 / &50 <= y ==> y <= &64 / &25 ==> ~linside c s u v a (&3) y)
     ==> exists cN sN uN vN aN.
           cN * cN + sN * sN = &1 /\ &0 < aN /\ aN = a /\
           (forall x y. linside cN sN uN vN aN x y <=> linside c s u v a (x + &2) (y + &2)) /\
           octoqp_data cN sN uN vN aN /\
           linside cN sN uN vN aN (&21 / &40) (&1 / &8) /\
           linside cN sN uN vN aN (&1 / &2) (&1) /\
           linside cN sN uN vN aN (&0) (&31 / &50)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] OCUBP_POINT_ORIGINAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] OCTOLP_POINT_ORIGINAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`;
                `a:real`] OCTOQP_FRAME) THEN
  REWRITE_TAC[OCTOE_INSIDE_TRANSLATED] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `y:real` THEN DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&2 + y` o check (fun th -> is_forall (concl th) &&
      not (is_iff (snd (strip_forall (concl th)))))) THEN
    REWRITE_TAC[IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN C580TE_IFF_TAC);;

(* ~linside X P from an unfolded disjointness assumption and an assumption   *)
(* linside Y P (Lean: foreign)                                               *)
let C580TE_EXCL_TAC (asl, w as g) =
  let p = dest_neg w in
  let x = rand (rator p) and y = rand p in
  let ths = map snd asl in
  let pts = filter (fun th -> let t = concl th in
    try fst (strip_comb t) = `linside` && rand (rator t) = x && rand t = y
    with Failure _ -> false) ths in
  let ds = filter (fun th -> let t = concl th in
    is_forall t && is_neg (snd (strip_forall t)) && is_conj (rand (snd (strip_forall t)))) ths in
  let one d q =
    let d' = SPECL [x; y] d in
    let th = try MP (MATCH_MP (TAUT `~(p /\ q) ==> q ==> ~p`) d') q
             with Failure _ -> MP (MATCH_MP (TAUT `~(q /\ p) ==> q ==> ~p`) d') q in
    if aconv (concl th) w then th else failwith "excl" in
  ACCEPT_TAC (tryfind (fun d -> tryfind (one d) pts) ds) g;;

(* Lean: entrance (generic part): A = owner 512, Q = owner 1024, R = owner   *)
(* 16384 (common side a), E / N the frames of southeast_negative_frame /     *)
(* northeast_profile                                                          *)
let C580TE_ENTRANCE_CORE = prove
 (`forall cE sE uE vE aE cN sN uN vN aN cA sA uA vA cQ sQ uQ vQ cR sR uR vR a.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ &0 < cE /\ sE < &0 /\ --sE <= cE /\ aE = a /\
     (forall x y. linside cE sE uE vE aE x y <=> linside cA sA uA vA a (x + &2) (y + &2)) /\
     cN * cN + sN * sN = &1 /\ &0 < aN /\ aN = a /\
     (forall x y. linside cN sN uN vN aN x y <=> linside cQ sQ uQ vQ a (x + &2) (y + &2)) /\
     octoqp_data cN sN uN vN aN /\
     linside cN sN uN vN aN (&21 / &40) (&1 / &8) /\
     linside cN sN uN vN aN (&1 / &2) (&1) /\
     linside cN sN uN vN aN (&0) (&31 / &50) /\
     cR * cR + sR * sR = &1 /\ &1 < a /\ lcont cR sR uR vR a /\
     linside cR sR uR vR a (&3) (&2) /\ linside cR sR uR vR a (&3) (&64 / &25) /\
     linside cA sA uA vA a (&47 / &20) (&33 / &20) /\
     linside cA sA uA vA a (&113 / &50) (&2) /\
     ~linside cA sA uA vA a (&2) (&2) /\
     (forall x. &113 / &50 <= x /\ x <= &14 / &5 ==> ~linside cA sA uA vA a x (&1)) /\
     ldisj cA sA uA vA a cQ sQ uQ vQ a /\ ldisj cA sA uA vA a cR sR uR vR a /\
     ldisj cQ sQ uQ vQ a cR sR uR vR a
     ==> exists cR' sR' uR' vR' aR'.
           cR' * cR' + sR' * sR' = &1 /\ &0 < aR' /\ aR' = a /\
           ocrtd_input cE sE uE vE aE cN sN uN vN aN cR' sR' uR' vR' aR' /\
           ldisj cE sE uE vE aE cN sN uN vN aN /\
           (forall x y. linside cR' sR' uR' vR' aR' x y <=> linside cR sR uR vR a (x + &2) (y + &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aE:real = a`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aN:real = a`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR - (cR * &2 + sR * &2)`; `vR - (--sR * &2 + cR * &2)`;
                `a:real`] OCRTD_RIGHT_FRAME) THEN
  REWRITE_TAC[OCTOE_INSIDE_TRANSLATED] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST [RASM_ARITH_TAC;
           REPEAT GEN_TAC THEN DISCH_TAC THEN
           UNDISCH_TAC `lcont cR sR uR vR a` THEN REWRITE_TAC[lcont] THEN
           DISCH_THEN(MP_TAC o SPECL [`&2 + x`; `&2 + y`]) THEN ASM_REWRITE_TAC[] THEN
           REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cR':real`; `sR':real`; `uR':real`; `vR':real`; `aR':real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aR':real = a`)) THEN
  (* the point facts of E, N, R' in owner coordinates *)
  let iffs = [`cE:real`; `cN:real`; `cR':real`] in
  let isiff c th = let t = concl th in is_forall t &&
    (let b = snd (strip_forall t) in is_iff b &&
       (try el 0 (snd (strip_comb (lhs b))) = c with Failure _ -> false)) in
  let IFFR c = FIRST_ASSUM(fun th -> if isiff c th then REWRITE_TAC[th] else NO_TAC) in
  let ALLIFF = MAP_EVERY IFFR iffs THEN REWRITE_TAC[REAL_ADD_SYM] in
  SUBGOAL_THEN `linside cQ sQ uQ vQ a (&101 / &40) (&17 / &8)` ASSUME_TAC THENL
   [UNDISCH_TAC `linside cN sN uN vN a (&21 / &40) (&1 / &8)` THEN IFFR `cN:real` THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ccntf_data cE sE uE vE a (--sE)` ASSUME_TAC THENL
   [MATCH_MP_TAC CCNTF_FACES THEN ASM_REWRITE_TAC[REAL_NEG_NEG] THEN
    IFFR `cE:real` THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST [RASM_ARITH_TAC;
           X_GEN_TAC `x:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
             RASM_ARITH_TAC;
           C580TE_EXCL_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`cR':real`; `sR':real`; `uR':real`; `vR':real`; `a:real`] THEN
  ASM_REWRITE_TAC[ocrtd_input; ldisj] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THEN
  FIRST [ALLIFF THEN NO_TAC;
         ALLIFF THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         REPEAT GEN_TAC THEN ALLIFF THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The actual families (v = 0, 1).                                           *)
(* ------------------------------------------------------------------------- *)

(* Lean: bottom_bar + foreign 512 (bottomMask v) (private) *)
let c580te_bottom_avoid v =
  let bm = C580E_BOTTOM.(v) in
  MP (SPECL (fc580ce_tuple 512 @ fc580ce_tuple bm) C580TE_HBAR_AVOID)
     (end_itlist CONJ [fc580ce_claim v 4; fc580ce_inst v FC580PI_BOTTOM_FAR.(v);
                       fc580ce_apart v 512 bm]);;

(* Lean: right_bar (private), at y = 64/25 *)
let c580te_right_upper v =
  fc580ce_vseg 16384 `&3` `&2` `&14 / &5` `&64 / &25`
    (fc580ce_inst v FC580UC_RIGHT_ORIGIN.(v)) (fc580ce_inst v FC580PI_RIGHT_FAR.(v));;

(* Lean: southeast_negative_frame *)
let C580TE_SOUTHEAST_NEGATIVE_FRAME = Array.init 2 (fun v ->
  let th = fc580ce_discharge v [2304; 512]
    (SPECL (fc580ce_tuple 2304 @ fc580ce_tuple 512) C580TE_SOUTHEAST_FRAME_CORE)
    [fc580ce_seed v 2304 (`&33 / &20`, `&33 / &20`);
     fc580ce_inst v FC580CE_MERGED_CENTER.(v);
     fc580ce_inst v FC580CE_MERGED_INWARD.(v);
     fc580ce_seed v 512 (`&47 / &20`, `&33 / &20`);
     fc580ce_auxpt 512 4 (fc580ce_comp v 5);
     fc580ce_claim v 6;
     fc580ce_excl v 512 8 (fc580ce_seed v 8 (`&3`, `&87 / &50`));
     c580te_bottom_avoid v;
     fc580ce_apart v 2304 512] in
  fc580ce_gen v th);;

(* Lean: northeast_profile *)
let C580TE_NORTHEAST_PROFILE = Array.init 2 (fun v ->
  let top = fc580ce_inst v FC580CE_NORTHEAST_TOP.(v) in
  let avoid = MP (SPECL (fc580ce_tuple 1024 @ fc580ce_tuple 16384) C580TE_VBAR_AVOID)
    (end_itlist CONJ [fc580ce_inst v FC580UC_RIGHT_ORIGIN.(v); fc580ce_inst v FC580PI_RIGHT_FAR.(v);
                      fc580ce_apart v 1024 16384]) in
  let th = fc580ce_discharge v [1024]
    (SPECL (fc580ce_tuple 1024) C580TE_NORTHEAST_PROFILE_CORE)
    [fc580ce_seed v 1024 (`&47 / &20`, `&47 / &20`); CONJUNCT1 top; CONJUNCT2 top;
     fc580ce_inst v FC580UC_NORTHEAST_EXTENSION.(v);
     fc580ce_excl v 1024 2304 (fc580ce_inst v FC580CE_MERGED_INWARD.(v));
     fc580ce_excl v 1024 32768 (fc580ce_inst v FC580UC_TOP_ORIGIN.(v));
     fc580ce_excl v 1024 48 (fc580ce_seed v 48 (`&3`, `&3`));
     avoid] in
  fc580ce_gen v th);;

(* Lean: entrance *)
let C580TE_ENTRANCE = Array.init 2 (fun v ->
  let rv n = mk_var(n, `:real`) in
  let sq x = map (fun p -> rv (p ^ x)) ["c"; "s"; "u"; "v"; "a"] in
  let own m = butlast (fc580ce_tuple m) in
  let lin q = list_mk_comb(`linside`, q @ [`x:real`; `y:real`]) in
  let iff q m = list_mk_forall([`x:real`; `y:real`],
    mk_iff(lin q, list_mk_comb(`linside`, fc580ce_tuple m @ [`x + &2`; `y + &2`]))) in
  let unit [c; s; _; _; a] = [mk_eq(mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` c c)
                                      (mk_binop `( * ):real->real->real` s s), `&1`);
                              mk_binop `(<):real->real->bool` `&0` a] in
  let e = sq "E" and n = sq "N" and r = sq "R" in
  let body = list_mk_exists(e @ n @ r, list_mk_conj(unit e @ unit n @ unit r @
    [list_mk_comb(`ocrtd_input`, e @ n @ r); list_mk_comb(`ldisj`, e @ n);
     iff e 512; iff n 1024; iff r 16384])) in
  let np = fc580ce_np v in
  let facts =
    [MP (SPECL (FC580CE_VARS @ [`16384`]) OO_UNIT) np; MP (SPECL FC580CE_VARS OO_SIDE) np;
     fc580pi_box_v v 16384; fc580ce_inst v FC580UC_RIGHT_ORIGIN.(v); c580te_right_upper v;
     fc580ce_seed v 512 (`&47 / &20`, `&33 / &20`); fc580ce_claim v 6;
     fc580ce_inst v FC580PI_SOUTHEAST_MISSING_CENTER.(v); c580te_bottom_avoid v;
     fc580ce_apart v 512 1024; fc580ce_apart v 512 16384; fc580ce_apart v 1024 16384] in
  prove(fc580ce_stmt v body,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(fc580ce_inst v C580TE_NORTHEAST_PROFILE.(v)) THEN
    MP_TAC(fc580ce_inst v C580TE_SOUTHEAST_NEGATIVE_FRAME.(v)) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC e THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC n THEN STRIP_TAC THEN
    MP_TAC(SPECL (e @ n @ own 512 @ own 1024 @ own 16384 @ [`l:real`]) C580TE_ENTRANCE_CORE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; FIRST (map ACCEPT_TAC facts)];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC r THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC (e @ n @ r) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC));;
