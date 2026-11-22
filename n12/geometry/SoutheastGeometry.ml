(* ========================================================================= *)
(* Port of Compact/Cases/C868/SoutheastGeometry.lean (N12Compact.C868,       *)
(* Jatloe).  The physical B512 (owner 512 = OriginalOwners tuple).            *)
(* CrossedElbow.impossible_original = OCCE_IMPOSSIBLE_ORIGINAL,              *)
(* ClosedFrames.canonical_frame = CLF_CANONICAL_FRAME,                        *)
(* C981CompletionOutwardAnchor.nonnegative_impossible =                       *)
(* C981OA_NONNEGATIVE_IMPOSSIBLE, CommonCases.OutwardPoint.point_original =   *)
(* CCOP_POINT_ORIGINAL, OutwardBarPoint.point_original = OCOBP_POINT_ORIGINAL;*)
(* pullY q = (c, --s, u - &4 * s, &4 * c - v - a, a) (LINSIDE_PULLY).         *)
(* Lean private southeast_size / southeast_marker / southeast_f8 /            *)
(* southeast_foreign are the Ownership facts OO_SIDE / c868_seed /            *)
(* C868AO_ADDITIONAL_INSIDE.(7) / c868_excl.  Tag C868SE_.                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ActualBars.ml";;
needs "n12/geometry/CP_OtherCases_CrossedElbow.ml";;
needs "n12/geometry/CP_OtherCases_OutwardBarPoint.ml";;
needs "n12/geometry/CP_CommonCases_OutwardPoint.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/CP_C981_OutwardAnchor.ml";;

(* small packing toolkit (also used by the UpperNegative* files) *)
let C868SE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    let cs = CONJUNCTS th in
    ASSUME_TAC (CONJ (el 0 cs) (el 1 cs)) THEN MAP_EVERY ASSUME_TAC (tl (tl cs)));;

let C868SE_FACTS_TAC facts =
  MAP_EVERY ASSUME_TAC facts THEN REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REWRITE_TAC[C868_SIDE]);;

let C868SE_IFF_TAC =
  ASSUM_LIST(fun ths -> REWRITE_TAC(filter (fun th ->
    let t = snd(strip_forall(concl th)) in is_forall(concl th) && is_iff t &&
      fst(strip_comb(lhand t)) = `linside`) ths));;

let c868se_app th hyps =
  let th1 = SPEC_ALL (SPECL C868OW_VARS th) in
  let avail = CONJUNCTS (ASSUME C868_H) @ hyps in
  let rec build t =
    try find (fun f -> aconv (concl f) t) avail with Failure _ ->
    if is_conj t then CONJ (build (lhand t)) (build (rand t))
    else failwith ("c868se_app: " ^ string_of_term t) in
  MP th1 (build (lhand (concl th1)));;

let C868SE_APP_TAC th =
  ASSUM_LIST(fun ths -> MAP_EVERY ASSUME_TAC (CONJUNCTS (c868se_app th ths)));;

let c868se_excl m n thn =
  let d = REWRITE_RULE[ldisj] (c868_apart_f m n) in
  let args = snd(strip_comb(concl thn)) in
  let d1 = SPECL [el 5 args; el 6 args] d in
  MP (MP (TAUT (mk_imp(concl d1, mk_imp(concl thn, mk_neg(lhand(rand(concl d1))))))) d1) thn;;

let c868se_lin m x y = list_mk_comb(`linside`, c868_own m @ [x; y]);;

(* Lean: southeast_avoids_bottom (private) *)
let C868SE_SOUTHEAST_AVOIDS_BOTTOM = prove
 (`forall c1 c2 a b l x.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     &113 / &50 <= x /\ x <= &14 / &5
     ==> ~linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512)
                  (oov c1 c2 a b l 512) l x (&1)`,
  C868SE_INTRO_TAC THEN
  ACCEPT_TAC(c868se_excl 512 8192 (c868se_app C868AB_BOTTOM_BAR
    [ASSUME `&113 / &50 <= x`; ASSUME `x <= &14 / &5`])));;

(* the same, as a fact under C868_H, curried and conjunctive forms *)
let C868SE_BAR =
  let x = `x:real` in
  let lo = ASSUME `&113 / &50 <= x` and hi = ASSUME `x <= &14 / &5` in
  GEN x (DISCH (concl lo) (DISCH (concl hi)
    (c868se_app C868SE_SOUTHEAST_AVOIDS_BOTTOM [lo; hi])));;
let C868SE_BAR_CONJ =
  let z = `z:real` in
  let h = `&113 / &50 <= z /\ z <= &14 / &5` in
  GEN z (DISCH h (MP (MP (SPEC z C868SE_BAR) (CONJUNCT1 (ASSUME h))) (CONJUNCT2 (ASSUME h))));;

(* Lean: southeast_right_crosspoint *)
let C868SE_SOUTHEAST_RIGHT_CROSSPOINT = prove
 (`forall c1 c2 a b l.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512)
             (oov c1 c2 a b l 512) l (&113 / &50) (&2)
     ==> linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512)
                 (oov c1 c2 a b l 512) l (&5 / &2) (&2)`,
  C868SE_INTRO_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL (c868_own 512 @ [`&4 / &5`]) OCCE_IMPOSSIBLE_ORIGINAL) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  C868SE_FACTS_TAC
   [c868_unit 512; C868_POS;
    c868_seed_f 512 (`&47 / &20`, `&33 / &20`);
    c868_mp C868AO_ADDITIONAL_INSIDE.(7);
    c868se_excl 512 256 (CONJUNCT2 (c868_mp C868AC_SOUTHWEST_CROSSPOINTS));
    MP (MP (SPEC `&14 / &5` C868SE_BAR) (REAL_ARITH `&113 / &50 <= &14 / &5`))
       (REAL_ARITH `&14 / &5 <= &14 / &5`)]);;

(* Lean: southeast_outward_frame *)
let C868SE_SOUTHEAST_OUTWARD_FRAME = prove
 (`forall c1 c2 a b l.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     ~linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512)
              (oov c1 c2 a b l 512) l (&113 / &50) (&2)
     ==> exists cB sB uB vB aB.
           cB * cB + sB * sB = &1 /\ &0 < aB /\
           &0 < cB /\ sB < &0 /\ --sB <= cB /\ aB = l /\
           (forall x y. linside cB sB uB vB aB x y <=>
                  linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512)
                          (oov c1 c2 a b l 512) l x y)`,
  C868SE_INTRO_TAC THEN
  MP_TAC (SPECL (c868_own 512) CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [C868SE_FACTS_TAC [c868_unit 512; C868_POS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cB:real` (X_CHOOSE_THEN `sB:real` (X_CHOOSE_THEN `uB:real`
    (X_CHOOSE_THEN `vB:real` (X_CHOOSE_THEN `aB:real` STRIP_ASSUME_TAC))))) THEN
  MAP_EVERY EXISTS_TAC [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP
    (REAL_ARITH `forall s c. abs s <= c ==> s <= c /\ --s <= c`) o
    check (fun th -> try rator(lhand(concl th)) = `abs:real->real` with Failure _ -> false)) THEN
  SUBGOAL_THEN `sB < &0` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   MATCH_MP_TAC (SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
     C981OA_NONNEGATIVE_IMPOSSIBLE) THEN
   C868SE_IFF_TAC THEN
   C868SE_FACTS_TAC
    [c868_seed_f 512 (`&47 / &20`, `&33 / &20`);
     c868_mp C868AC_SOUTHEAST_G8;
     c868_excl_f 512 12 (c868_seed_f 12 (`&3`, `&1`));
     c868_excl_f 512 16416 (c868_seed_f 16416 (`&1543 / &500`, `&2`));
     C868SE_BAR_CONJ];
   ALL_TAC] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* Lean: southeast_outward_points *)
let C868SE_SOUTHEAST_OUTWARD_POINTS = prove
 (`forall c1 c2 a b l.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     ~linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512)
              (oov c1 c2 a b l 512) l (&113 / &50) (&2)
     ==> linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512)
                 (oov c1 c2 a b l 512) l (&123 / &50) (&201 / &100) /\
         linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512)
                 (oov c1 c2 a b l 512) l (&101 / &40) (&17 / &8)`,
  C868SE_INTRO_TAC THEN
  let q = match c868_own 512 with
      [c; s; u; v; a] ->
        [c; mk_comb(`(--):real->real`, s); mk_binop `(-):real->real->real` u (mk_binop `(*):real->real->real` `&4` s);
         mk_binop `(-):real->real->real`
           (mk_binop `(-):real->real->real` (mk_binop `(*):real->real->real` `&4` c) v) a; a]
    | _ -> failwith "C868SE: owner" in
  let point th =
    MP_TAC (SPECL q th) THEN REWRITE_TAC[LINSIDE_PULLY; REAL_NEG_MUL2] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN
    C868SE_FACTS_TAC
     [c868_unit 512; C868_POS;
      c868_seed_f 512 (`&47 / &20`, `&33 / &20`);
      c868_mp C868AO_ADDITIONAL_INSIDE.(7);
      c868_mp C868AC_SOUTHEAST_G8;
      c868_excl_f 512 16416 (c868_seed_f 16416 (`&1543 / &500`, `&2`));
      c868_excl_f 512 12 (c868_seed_f 12 (`&3`, `&1`));
      c868_excl_f 512 12 (c868_seed_f 12 (`&1543 / &500`, `&1`));
      C868SE_BAR] in
  CONJ_TAC THENL [point CCOP_POINT_ORIGINAL; point OCOBP_POINT_ORIGINAL]);;
