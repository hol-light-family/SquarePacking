(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C580581Entrance.lean.             *)
(* The forced G owners of the original C580 (v = 0) / C581 (v = 1)           *)
(* families.  Lean  G p mask = natAuxOwners p 1 (ownerIndex p mask)  is      *)
(* c580e_G.  The private half domains are the theorems C580E_*G (one per v); *)
(* actual / separate / absent are used inside pk_forced_half.                *)
(* forced v i / inside v i (i : Fin 10) are stated as the conjunction over i. *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;
needs "n12/geometry/CP_FiniteCases_TransposeOwnerDomain.ml";;

(* Lean: bottomMask, family *)
let c580e_family0 = new_definition
 `c580e_family0 = {1,2,8,48,192,512,1024,2304,4096,8192,16384,32768}`;;
let c580e_family1 = new_definition
 `c580e_family1 = {1,2,8,48,192,512,1024,2304,4096,8196,16384,32768}`;;
let C580E_FAM = [| `c580e_family0`; `c580e_family1` |];;
let C580E_BOTTOM = [| 8192; 8196 |];;

(* Lean: swG, lowG, seG, mergedG, bottomG, leftG, southG, rightG, northG, topG (private) *)
let C580E_DOMS = Array.init 2 (fun v ->
  let f = C580E_FAM.(v) in
  [ro_single f 2; ro_single f 6;
   tod_transported f 8 6 (false, true, false) 1 1 RO_REFLECTXG;
   tod_transported f 2304 33 (true, false, false) 0 1 TOD_SWAPFG;
   (if v = 0 then ro_single f 68
    else pk_hdom_seedhull f 8196 1 5
           ([(nlin_rat "9/4", num 1); (nlin_rat "11/4", num 1); (nlin_rat "9/4", num 1)],
            (nlin_rat "113/50", num 1), nlin_rat "1/50", num 0));
   ro_single f 57; ro_single f 27; ro_single f 77; ro_single f 35; ro_single f 90]);;

(* Lean: G *)
let c580e_G = new_definition
 `c580e_G (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) (m:num) =
    auxown 1 (c1 (oidx c1 c2 a b l m)) (c2 (oidx c1 c2 a b l m))
             (a (oidx c1 c2 a b l m)) (b (oidx c1 c2 a b l m)) l`;;

(* Lean: claims *)
let c580e_claims v = [(1,2); (2,0); (8,8); (2304,3); (C580E_BOTTOM.(v),5); (4096,1);
                      (512,6); (16384,9); (1024,7); (32768,4)];;

let c580e_hyp v = mk_conj(`NPACK c1 c2 a b l`, mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, C580E_FAM.(v)));;
let c580e_all v body = list_mk_forall([`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
                                      mk_imp(c580e_hyp v, body));;
let c580e_gt m = list_mk_comb(`c580e_G`, [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
                                          `l:real`; mk_small_numeral m]);;

(* Lean: forced *)
let C580E_FORCED = Array.init 2 (fun v ->
  let ths = map (fun (m, j) -> pk_forced_half 1 C580E_FAM.(v) C580E_DOMS.(v) m (mk_numset [j])) (c580e_claims v) in
  prove(c580e_all v (list_mk_conj (map (fun (m, j) -> mk_eq(c580e_gt m, mk_numset [j])) (c580e_claims v))),
    REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[c580e_G] THEN ASM_SIMP_TAC ths));;

(* Lean: inside *)
let C580E_INSIDE = Array.init 2 (fun v ->
  let pt m j = list_mk_comb(`linside`,
     map (fun f -> list_mk_comb(f, [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                                    mk_small_numeral m])) [`ooc`; `oos`; `oou`; `oov`] @
     [`l:real`; mk_comb(mk_comb(`($):real^2->num->real`, mk_comb(mk_comb(`EL:num->(real^2)list->real^2`, mk_small_numeral j), `AUXPTS 1`)), `1`);
                mk_comb(mk_comb(`($):real^2->num->real`, mk_comb(mk_comb(`EL:num->(real^2)list->real^2`, mk_small_numeral j), `AUXPTS 1`)), `2`)]) in
  prove(c580e_all v (list_mk_conj (map (fun (m, j) -> pt m j) (c580e_claims v))),
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (SPEC_ALL C580E_FORCED.(v)) THEN ASM_REWRITE_TAC[c580e_G] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[OO_AUXK_EXACT; LEN_AUX.(1); ARITH] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV));;
