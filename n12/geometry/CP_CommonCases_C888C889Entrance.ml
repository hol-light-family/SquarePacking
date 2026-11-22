(* ========================================================================= *)
(* Phase 2: Compact/Completion/CommonCases/C888C889Entrance.lean             *)
(* (namespace N12Compact.CommonCases.C888C889).  Shared ownership entrance   *)
(* of the original C888 (b = false, family c888d_family_f, right mask 16384) *)
(* and C889 (b = true, c888d_family_t, right mask 16416).  A statement for   *)
(* the Lean parameter b is given as the two theorems _F and _T.              *)
(* auxiliaries p m is ooaux c1 c2 a b l m; owner p m the usual 5-tuple.     *)
(* The private list cuts are proved by literal evaluation (C888E_CUT).       *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_C888C889Domains.ml";;

(* ------------------------------------------------------------------------- *)
(* Literal list cuts (Lean: decide +kernel).                                 *)
(* ------------------------------------------------------------------------- *)

(* |- s = t <=> T/F for literal numeral sets *)
let c888e_seteq_conv tm =
  let l, r = dest_eq tm in
  let ls = numset_of l and rs = numset_of r in
  if ls = rs then EQT_INTRO (setlit_eq l r) else
  let e = mk_small_numeral (hd (filter (fun x -> not (mem x rs)) ls @ filter (fun x -> not (mem x ls)) rs)) in
  let th = AP_TERM (mk_comb(`(IN):num->(num->bool)->bool`, e)) (ASSUME tm) in
  let f = CONV_RULE (BINOP_CONV (REWRITE_CONV[IN_INSERT; NOT_IN_EMPTY; ARITH_EQ])) th in
  EQF_INTRO (NOT_INTRO (DISCH tm (EQ_MP (REWRITE_CONV[] (concl f)) f)));;

let C888E_DEC_CONV =
  REWRITE_CONV[DISJOINT_INSERT; DISJOINT_EMPTY; INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT;
               NOT_IN_EMPTY; ARITH_EQ; MEM] THENC
  DEPTH_CONV (fun t -> if is_eq t && type_of (lhs t) = `:num->bool` then c888e_seteq_conv t
                       else failwith "") THENC
  REWRITE_CONV[];;

(* !s. MEM s L ==> ... : case split over the literal list L (defs unfold it) *)
let C888E_CUT_TAC defs =
  REWRITE_TAC (defs @ [MEM]) THEN
  TRY(GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN CONV_TAC C888E_DEC_CONV);;

(* Lean: southChoices, northChoices (private) *)
let c888e_south_choices = new_definition
 `c888e_south_choices = [{4,16}; {4,18}; {8,16}; {8,18}; {4,5,16}; {4,8,16}; {4,8,18}; {4,9,16}; {5,8,16}; {8,9,16}]`;;
let c888e_north_choices = new_definition
 `c888e_north_choices = [{5,16}; {5,19}; {9,16}; {9,19}; {4,5,16}; {4,9,16}; {5,8,16}; {5,9,16}; {5,9,19}; {8,9,16}]`;;

(* Lean: Pattern *)
let c888e_pattern = new_definition
 `c888e_pattern (a:num->bool) (n:num->bool) <=>
    ({4,16} SUBSET a /\ MEM n [{5,19}; {9,19}; {5,9,19}]) \/
    ({5,16} SUBSET n /\ MEM a [{4,18}; {8,18}; {4,8,18}])`;;

(* Lean: singleton_sets (private) *)
let C888E_SINGLETON_SETS = CONJ
  (prove(`forall s. MEM s c888d_southwest_allowed ==> s = {2,12}`, C888E_CUT_TAC [c888d_southwest_allowed]))
  (prove(`forall s. MEM s c888d_singleton_allowed ==> s = {7,17}`, C888E_CUT_TAC [c888d_singleton_allowed]));;

(* Lean: bottom_filtered (private) *)
let C888E_BOTTOM_FILTERED = prove
 (`forall a. MEM a c888d_bottom_allowed ==> DISJOINT a {2,12} ==> MEM a [{6,15}; {4,6,15}]`,
  C888E_CUT_TAC [c888d_bottom_allowed]);;

(* Lean: south_filtered (private) *)
let C888E_SOUTH_FILTERED = prove
 (`forall a. MEM a c888d_south_allowed ==> DISJOINT a {6,15} ==> MEM a c888e_south_choices`,
  C888E_CUT_TAC [c888d_south_allowed; c888e_south_choices]);;

(* Lean: north_filtered (private) *)
let C888E_NORTH_FILTERED = prove
 (`forall n. MEM n c888d_north_allowed ==> DISJOINT n {7,17} ==> MEM n c888e_north_choices`,
  C888E_CUT_TAC [c888d_north_allowed; c888e_north_choices]);;

(* Lean: right_filtered (private) *)
let C888E_RIGHT_FILTERED = prove
 (`forall r. MEM r c888d_right_allowed ==> DISJOINT r {6,15} ==> DISJOINT r {7,17} ==>
       {8,18} SUBSET r \/ {9,19} SUBSET r`,
  C888E_CUT_TAC [c888d_right_allowed]);;

(* Lean: lower_south (private) *)
let C888E_LOWER_SOUTH = prove
 (`forall a. MEM a c888e_south_choices ==> DISJOINT a {8,18} ==> {4,16} SUBSET a`,
  C888E_CUT_TAC [c888e_south_choices]);;

(* Lean: lower_north (private) *)
let C888E_LOWER_NORTH = prove
 (`forall n. MEM n c888e_north_choices ==> ~(16 IN n) ==> DISJOINT n {8,18} ==>
       MEM n [{5,19}; {9,19}; {5,9,19}]`,
  C888E_CUT_TAC [c888e_north_choices]);;

(* Lean: upper_north (private) *)
let C888E_UPPER_NORTH = prove
 (`forall n. MEM n c888e_north_choices ==> DISJOINT n {9,19} ==> {5,16} SUBSET n`,
  C888E_CUT_TAC [c888e_north_choices]);;

(* Lean: upper_south (private) *)
let C888E_UPPER_SOUTH = prove
 (`forall a. MEM a c888e_south_choices ==> ~(16 IN a) ==> DISJOINT a {9,19} ==>
       MEM a [{4,18}; {8,18}; {4,8,18}]`,
  C888E_CUT_TAC [c888e_south_choices]);;

(* Lean: checked (local in entrance) *)
let C888E_BOTTOM_CHECKED = prove
 (`forall a. MEM a [{6,15}; {4,6,15}] ==> {6,15} SUBSET a`, C888E_CUT_TAC []);;

(* ------------------------------------------------------------------------- *)
(* Owner points.                                                             *)
(* ------------------------------------------------------------------------- *)

let c888e_fam b = assoc b C888D_FAMS;;

(* Lean: seed_point b (producer, like OriginalOwners.seed):
   |- !c1 c2 a b l. NPACK .. /\ IMAGE binarysum (FFP ..) = family b ==> linside (owner m) x y *)
let C888E_SEED_POINT b m p = oo_inst (c888e_fam b) (oo_seed m p);;

(* Lean: auxiliary_point *)
let C888E_AUXILIARY_POINT = prove
 (`forall c1 c2 a b l m owned j. owned SUBSET ooaux c1 c2 a b l m /\ j < 20 /\ j IN owned
     ==> linside (ooc c1 c2 a b l m) (oos c1 c2 a b l m) (oou c1 c2 a b l m) (oov c1 c2 a b l m) l
                 (EL j (AUXPTS 2)$1) (EL j (AUXPTS 2)$2)`,
  REWRITE_TAC[SUBSET] THEN MESON_TAC[OO_AUX_EXACT]);;

(* Lean: missing_auxiliary *)
let C888E_MISSING_AUXILIARY = prove
 (`forall c1 c2 a b l m owned j. ooaux c1 c2 a b l m = owned /\ j < 20 /\ ~(j IN owned)
     ==> ~linside (ooc c1 c2 a b l m) (oos c1 c2 a b l m) (oou c1 c2 a b l m) (oov c1 c2 a b l m) l
                  (EL j (AUXPTS 2)$1) (EL j (AUXPTS 2)$2)`,
  MESON_TAC[OO_AUX_EXACT]);;

(* ------------------------------------------------------------------------- *)
(* The entrance.                                                             *)
(* ------------------------------------------------------------------------- *)

let C888E_DISJ_MONO = prove
 (`forall s t u:num->bool. DISJOINT s t /\ u SUBSET t ==> DISJOINT s u`, SET_TAC[]);;
let C888E_DISJ_MISS = prove
 (`forall s t:num->bool x. DISJOINT s t /\ x IN s ==> ~(x IN t)`, SET_TAC[]);;

let C888E_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;

let c888e_entrance b =
  let fam = c888e_fam b in
  let np = `NPACK c1 c2 a b l` and img = mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam) in
  let h = CONJ (ASSUME np) (ASSUME img) in
  let aux m = list_mk_comb(`ooaux`, C888E_VARS @ [mk_small_numeral m]) in
  let dom m d = MATCH_MP OO_DOMAIN (CONJ d (CONJ (ASSUME np) (CONJ (ASSUME img) (in_fam m fam)))) in
  let disj m n =
    MP (SPECL (C888E_VARS @ [fam; mk_small_numeral m; mk_small_numeral n]) OO_AUX_DISJOINT)
       (end_itlist CONJ [ASSUME np; ASSUME img; in_fam m fam; in_fam n fam;
                         EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral m, mk_small_numeral n)))]) in
  let mono d s = MATCH_MP C888E_DISJ_MONO (CONJ d s) in
  let cut th x ths = List.fold_left MP (SPEC x th) ths in
  let rm = if b then 16416 else 16384 in
  let sw = cut (CONJUNCT1 C888E_SINGLETON_SETS) (aux 1) [dom 1 (assoc b C888D_SOUTHWEST_DOMAIN)] in
  let tr = cut (CONJUNCT2 C888E_SINGLETON_SETS) (aux 16) [dom 16 (assoc b C888D_SINGLETON_DOMAIN)] in
  let bottom_sw = REWRITE_RULE[sw] (disj 8192 1) in
  let bottom_options = cut C888E_BOTTOM_FILTERED (aux 8192)
                         [dom 8192 (assoc b C888D_BOTTOM_DOMAIN); bottom_sw] in
  let bottom = cut C888E_BOTTOM_CHECKED (aux 8192) [bottom_options] in
  let south = cut C888E_SOUTH_FILTERED (aux 512)
                [dom 512 (assoc b C888D_SOUTH_DOMAIN); mono (disj 512 8192) bottom] in
  let north = cut C888E_NORTH_FILTERED (aux 1024)
                [dom 1024 (assoc b C888D_NORTH_DOMAIN); REWRITE_RULE[tr] (disj 1024 16)] in
  let right_pair =
    if not b then
      cut C888E_RIGHT_FILTERED (aux 16384)
        [dom 16384 C888D_RIGHT_DOMAIN; mono (disj 16384 8192) bottom; REWRITE_RULE[tr] (disj 16384 16)]
    else
      let seed p = MP (SPECL C888E_VARS (C888E_SEED_POINT true 16416 p)) h in
      let lo = seed (`&3`, `&9 / &4`) and hi = seed (`&3`, `&11 / &4`) in
      let seg y = MATCH_MP OO_VERTICAL_SEGMENT
                    (CONJ lo (CONJ hi (REAL_ARITH (mk_conj(`&9 / &4 < &11 / &4`,
                       mk_conj(mk_binop `(<=):real->real->bool` `&9 / &4` y,
                               mk_binop `(<=):real->real->bool` y `&11 / &4`)))))) in
      let mem j th = EQ_MP (SPECL (C888E_VARS @ [`16416`]) (oo_aux_point j)) th in
      let f = mem 9 (seg `&113 / &50`) and g = mem 19 (seg `&12 / &5`) in
      let sub = EQ_MP (SYM (REWRITE_CONV[INSERT_SUBSET; EMPTY_SUBSET]
                              (mk_binop `(SUBSET):(num->bool)->(num->bool)->bool` `{9,19}` (aux 16416))))
                      (CONJ f g) in
      DISJ2 (mk_binop `(SUBSET):(num->bool)->(num->bool)->bool` `{8,18}` (aux 16416)) sub in
  let a_right = disj 512 rm and n_right = disj 1024 rm and central = disj 512 1024 in
  let goal = mk_conj(concl bottom, list_mk_comb(`c888e_pattern`, [aux 512; aux 1024])) in
  let pat = REWRITE_CONV[c888e_pattern] (rand goal) in
  let lower_case lower =
    let apair = cut C888E_LOWER_SOUTH (aux 512) [south; mono a_right lower] in
    let in16 = CONJUNCT2 (REWRITE_RULE[INSERT_SUBSET; EMPTY_SUBSET] apair) in
    let missing = MATCH_MP C888E_DISJ_MISS (CONJ central in16) in
    let nmem = cut C888E_LOWER_NORTH (aux 1024) [north; missing; mono n_right lower] in
    CONJ bottom (EQ_MP (SYM (pat)) (DISJ1 (CONJ apair nmem) (rand(rand(concl(pat)))))) in
  let upper_case upper =
    let npair = cut C888E_UPPER_NORTH (aux 1024) [north; mono n_right upper] in
    let in16 = CONJUNCT2 (REWRITE_RULE[INSERT_SUBSET; EMPTY_SUBSET] npair) in
    let missing = MATCH_MP C888E_DISJ_MISS (CONJ (ONCE_REWRITE_RULE[DISJOINT_SYM] central) in16) in
    let amem = cut C888E_UPPER_SOUTH (aux 512) [south; missing; mono a_right upper] in
    CONJ bottom (EQ_MP (SYM (pat)) (DISJ2 (lhand(rand(concl(pat)))) (CONJ npair amem))) in
  let p, q = dest_disj (concl right_pair) in
  let th = DISJ_CASES right_pair (lower_case (ASSUME p)) (upper_case (ASSUME q)) in
  if concl th <> goal then failwith "c888e_entrance" else
  GENL C888E_VARS (DISCH (mk_conj(np, img)) (PROVE_HYP (CONJUNCT1 (ASSUME (mk_conj(np, img))))
                     (PROVE_HYP (CONJUNCT2 (ASSUME (mk_conj(np, img)))) th)));;

(* Lean: entrance (b = false: C888) *)
let C888E_ENTRANCE_F = c888e_entrance false;;
(* Lean: entrance (b = true: C889) *)
let C888E_ENTRANCE_T = c888e_entrance true;;
