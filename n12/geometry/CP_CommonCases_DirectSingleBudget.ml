(* ========================================================================= *)
(* Phase 2: Compact/Completion/CommonCases/DirectSingleBudget.lean           *)
(* (N12Compact.CommonCases.DirectSingleBudget).  Reuse a direct single-cover *)
(* certificate (S12 DirectSingleDomain, the OCaml dsd record of              *)
(* SmallOwnerDomainThree.ml) on a contained cardinality interval.            *)
(*                                                                           *)
(* A Lean OpenSquare q with side, size, box, ExactMarkers q (maskSupport m)  *)
(* and AuxExact q (auxKind k) owned is the local square (c1, c2, a, b, l) of  *)
(* the Phase-1 local queries:  &1 < l, l <= 1001/1000, a*a+b*b = 1 (unit     *)
(* normal), owalls c1 c2 a b l, owned c1 c2 a b l = bitset m, and            *)
(* owned = auxown k c1 c2 a b l (owned SUBSET range 10 holds by definition). *)
(*   sound_of_budget    dsb_sound_of_budget host k w   (producer; checks      *)
(*                      w.Check host k, as Lean's hypothesis checked):        *)
(*     |- !c1 c2 a b l. LQ hyps /\ owned c1 c2 a b l = bitset w.mask /\       *)
(*          lower <= CARD (auxown k ..) /\ CARD (auxown k ..) <= upper        *)
(*          ==> MEM (auxown k c1 c2 a b l) [w.allowed]                       *)
(*   actual_of_budget   DSB_ACTUAL_OF_LOCAL / dsb_actual_of_budget host k w   *)
(*   actual_of_interval DSB_INTERVAL_OF_LOCAL / dsb_actual_of_interval        *)
(*                      host actual k w  (the low / high side conditions are  *)
(*                      hypotheses lo <= pklow m k, pkup fam m k <= hi)       *)
(*   pull_exact         dsb_check_points (the points hypothesis) plus the     *)
(*                      query transport inside dsb_transformed_actual: each   *)
(*                      exact query of w is re-proved by the kernel at the     *)
(*                      transformed points (as RelaxedOwnerDomain's port does *)
(*                      for ofTransformedCombined).                           *)
(*   transformed_actual dsb_transformed_actual host srck actk w trf perm:     *)
(*     |- !c1 c2 a b l i. NPACK c1 c2 a b l /\ i < 12 /\                      *)
(*          ownmask (c1 i) .. l = maskAction trf w.mask /\                    *)
(*          lower <= CARD (auxown actk (c1 i) ..) /\ CARD .. <= upper         *)
(*          ==> MEM (auxown actk (c1 i) (c2 i) (a i) (b i) l) [perm w.allowed] *)
(*     Lean's markers hypothesis ExactMarkers (t.pull (p.square i))           *)
(*     (maskSupport w.mask) is markerCode p i = maskAction t w.mask, and      *)
(*     pulledOwners perm O IN w.allowed  <=>  O IN map (image perm) w.allowed *)
(*     (perm a bijection of 0..9 given by its value list; trf = (swap,        *)
(*     reflectX, reflectY) as in PackingContext tr_q).                        *)
(* Tag DSB_ / dsb_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/SmallOwnerDomainThree.ml";;
needs "n12/geometry/RelaxedOwnerDomain.ml";;
needs "n12/geometry/cornerpair.ml";;

(* the packing version of a local single-domain statement *)
(* Lean: actual_of_budget (generic part) *)
let DSB_ACTUAL_OF_LOCAL = prove
 (`forall m k lo hi (al:(num->bool)list).
     (forall c1 c2 a b l. &1 < l /\ l <= &1001 / &1000 /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
          owned c1 c2 a b l = bitset m /\
          lo <= CARD (auxown k c1 c2 a b l) /\ CARD (auxown k c1 c2 a b l) <= hi
          ==> MEM (auxown k c1 c2 a b l) al)
     ==> forall c1 c2 a b l i. NPACK c1 c2 a b l /\ i < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = m /\
           lo <= CARD (auxown k (c1 i) (c2 i) (a i) (b i) l) /\
           CARD (auxown k (c1 i) (c2 i) (a i) (b i) l) <= hi
           ==> MEM (auxown k (c1 i) (c2 i) (a i) (b i) l) al`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`] NPACK_SQ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[GSYM OWNED_BITSET]);;

(* Lean: actual_of_interval (generic part) *)
let DSB_INTERVAL_OF_LOCAL = prove
 (`forall fam m k lo hi (al:(num->bool)list). k < 2 /\
     (forall c1 c2 a b l. &1 < l /\ l <= &1001 / &1000 /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
          owned c1 c2 a b l = bitset m /\
          lo <= CARD (auxown k c1 c2 a b l) /\ CARD (auxown k c1 c2 a b l) <= hi
          ==> MEM (auxown k c1 c2 a b l) al)
     ==> forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\ i < 12 /\
           ownmask (c1 i) (c2 i) (a i) (b i) l = m /\
           lo <= pklow m k /\ pkup fam m k <= hi
           ==> MEM (auxown k (c1 i) (c2 i) (a i) (b i) l) al`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o MATCH_MP DSB_ACTUAL_OF_LOCAL)) THEN
  MAP_EVERY X_GEN_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `fam:num->bool`; `k:num`; `i:num`] PK_BUDGET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LE_TRANS]);;

(* the local statement for mask m, kind k, interval lo..hi, allowed sets al *)
let dsb_local m k lo hi al alt =
  let sth = spec_theorem m k lo hi al in
  let ownp = mk_eq(`owned c1 c2 a b l`, set_tm (bits m)) in
  let (hl, hh) = bound_tms k lo hi in
  let hyps = LQ_HYPS @ [ownp; hl; hh] in
  let th = List.fold_left MP (SPECL SPEC5 sth) (map ASSUME hyps) in
  local_to_mem m (auxown_tm k) hyps th alt;;

(* Lean: DirectSingleDomain.Check host k (budget equalities, query mask / kind, every
   subset in the interval allowed or refuted by an exact query of the list) *)
let dsb_check host k w = ignore (dsd_actual host k w);;

(* Lean: sound_of_budget *)
let dsb_sound_of_budget host k w =
  dsb_check host k w;
  let al = map (List.sort compare) w.dallowed in
  dsb_local w.dmask k w.dlower w.dupper al (mk_list(map mk_numset w.dallowed, `:num->bool`));;

(* Lean: actual_of_budget *)
let dsb_actual_of_budget host k w = MATCH_MP DSB_ACTUAL_OF_LOCAL (dsb_sound_of_budget host k w);;

(* Lean: actual_of_interval  (actual family afam, a literal or a named constant) *)
let dsb_actual_of_interval host afam k w =
  let loc = dsb_sound_of_budget host k w in
  let kl = EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` (mk_small_numeral k) `2`)) in
  let th = MATCH_MP (ISPEC afam DSB_INTERVAL_OF_LOCAL) (CONJ kl loc) in
  th;;

(* Lean: pull_exact (its points hypothesis):  t.applyRat (aux srck j) = aux actk (perm j) *)
let dsb_check_points trf srck actk perm =
  if sort (<) perm <> 0--9 then failwith "dsb_check_points: not a permutation" else
  List.iter (fun j -> if not (qeq (tr_q trf (aux_q srck j)) (aux_q actk (el j perm))) then
     failwith (Printf.sprintf "dsb_check_points: point %d" j)) (0--9);;

(* Lean: transformed_actual *)
let dsb_transformed_actual host srck actk w trf perm =
  dsb_check host srck w;
  dsb_check_points trf srck actk perm;
  let tmask = mask_action trf w.dmask in
  let tp (x, y) = let (x1, y1) = tr_point trf (term_of_rat x, term_of_rat y) in
                  (rat_of_term x1, rat_of_term y1) in
  List.iter (fun n ->
      let (_, m, k, ow, uin, uout) = slq_data n in
      add_query (tmask, actk, List.sort compare (map (perm_of perm) ow), map tp uin, map tp uout))
    w.dqueries;
  let pa = map (fun s -> List.sort compare (map (perm_of perm) s)) w.dallowed in
  let loc = dsb_local tmask actk w.dlower w.dupper pa (mk_list(map mk_numset pa, `:num->bool`)) in
  MATCH_MP DSB_ACTUAL_OF_LOCAL loc;;
