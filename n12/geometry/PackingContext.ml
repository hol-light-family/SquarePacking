(* ========================================================================= *)
(* Phase 2, packing context: the Lean vocabulary that quantifies over a     *)
(* NormalizedPacking (Jatloe: S12/CoreExclusion ownerIndex, S12/AuxPacking  *)
(* nat_aux_budget, S12/CombinedPacking, S12/CertifiedDomain, S12/Seeds,     *)
(* S12/LocalQuery, Compact/Bridge/OwnerBudget).                             *)
(*                                                                           *)
(* Representation (see also n12/PROOF_STRUCTURE.md): *)
(*   p : NormalizedPacking          c1 c2 a b l  with  NPACK c1 c2 a b l     *)
(*   codedMarkerFamily p = family   IMAGE binarysum (FFP c1 c2 a b l) = fam  *)
(*   markerCode p i = mask          ownmask (c1 i) (c2 i) (a i) (b i) l = m  *)
(*   natAuxOwners p k i             auxown k (c1 i) (c2 i) (a i) (b i) l     *)
(*   natCombinedOwners p i          auxown 2 (c1 i) (c2 i) (a i) (b i) l     *)
(*   ownerIndex p mask              oidx c1 c2 a b l m                       *)
(*   owner p mask (OriginalOwners)  the 5-tuple (ooc .. m) (oos .. m)        *)
(*                                  (oou .. m) (oov .. m) l                  *)
(*   auxiliaries p mask             ooaux c1 c2 a b l m                      *)
(*   auxExempt k                    auxex k  (Lean's literal exempt0/1)      *)
(*   CertifiedDomain family (mask m, allowed al)    |- cdom fam m al         *)
(*   OwnerBudget.HalfDomain family m k (allowed al) |- hdom fam m k al       *)
(*   combinedOwners x y             combown x y                              *)
(* Literal finite sets are written {a, b, c} (as in Lean); lists of them as  *)
(* HOL lists.  Theorem producers (OCaml functions pk_.., oo_..) compute the   *)
(* Lean decide-facts and return kernel theorems.                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/fs_bridge.ml";;
needs "n12/geometry/cornerpair.ml";;

(* ------------------------------------------------------------------------- *)
(* Owner index (Lean: CoreExclusion.ownerIndex) and the owner square.        *)
(* ------------------------------------------------------------------------- *)

let oidx = new_definition
 `oidx (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) (m:num) =
    if exists i. i < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = m
    then (@i. i < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = m) else 0`;;

let ooc = new_definition
 `ooc (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) (m:num) =
    a (oidx c1 c2 a b l m)`;;
let oos = new_definition
 `oos (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) (m:num) =
    b (oidx c1 c2 a b l m)`;;
let oou = new_definition
 `oou (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) (m:num) =
    a (oidx c1 c2 a b l m) * c1 (oidx c1 c2 a b l m) +
    b (oidx c1 c2 a b l m) * c2 (oidx c1 c2 a b l m) - l / &2`;;
let oov = new_definition
 `oov (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) (m:num) =
    --b (oidx c1 c2 a b l m) * c1 (oidx c1 c2 a b l m) +
    a (oidx c1 c2 a b l m) * c2 (oidx c1 c2 a b l m) - l / &2`;;
let ooaux = new_definition
 `ooaux (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) (m:num) =
    auxown 2 (c1 (oidx c1 c2 a b l m)) (c2 (oidx c1 c2 a b l m))
             (a (oidx c1 c2 a b l m)) (b (oidx c1 c2 a b l m)) l`;;

(* Lean: ownerIndex is a Fin 12 *)
let OIDX_LT = prove
 (`forall c1 c2 a b l m. oidx c1 c2 a b l m < 12`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oidx] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN SIMP_TAC[]; ARITH_TAC]);;

(* Lean: ownerIndex_spec *)
let OIDX_SPEC = prove
 (`forall c1 c2 a b l fam m. IMAGE binarysum (FFP c1 c2 a b l) = fam /\ m IN fam
     ==> ownmask (c1 (oidx c1 c2 a b l m)) (c2 (oidx c1 c2 a b l m))
                 (a (oidx c1 c2 a b l m)) (b (oidx c1 c2 a b l m)) l = m`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[FFP; GSYM IMAGE_o] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[oidx; GSYM ownmask] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC[]]);;

let OWNED_BITSET = prove
 (`forall c1 c2 a b l. bitset (ownmask c1 c2 a b l) = owned c1 c2 a b l`,
  REWRITE_TAC[ownmask] THEN SIMP_TAC[BITSET_BINARYSUM; FINITE_OWNED]);;

(* Lean: markerCode_injective *)
let OWNMASK_INJ = prove
 (`forall c1 c2 a b l i j. NPACK c1 c2 a b l /\ i < 12 /\ j < 12 /\
       ownmask (c1 i) (c2 i) (a i) (b i) l = ownmask (c1 j) (c2 j) (a j) (b j) l
       ==> i = j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OWNED_INJ THEN
  MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] THEN
  ASM_REWRITE_TAC[GSYM OWNED_BITSET]);;

(* the owner of a member mask: index, marker set, square facts *)
let OIDX_OWNED = prove
 (`forall c1 c2 a b l fam m. IMAGE binarysum (FFP c1 c2 a b l) = fam /\ m IN fam
     ==> owned (c1 (oidx c1 c2 a b l m)) (c2 (oidx c1 c2 a b l m))
               (a (oidx c1 c2 a b l m)) (b (oidx c1 c2 a b l m)) l = bitset m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM OWNED_BITSET] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC OIDX_SPEC THEN ASM_MESON_TAC[]);;

let OIDX_INJ = prove
 (`forall c1 c2 a b l fam m n. IMAGE binarysum (FFP c1 c2 a b l) = fam /\ m IN fam /\ n IN fam /\
       oidx c1 c2 a b l m = oidx c1 c2 a b l n ==> m = n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `fam:num->bool`; `m:num`] OIDX_SPEC) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `fam:num->bool`; `n:num`] OIDX_SPEC) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* centred square <-> 5-tuple, at a vector and at a point *)
let PK_OSQ_LINSIDE = prove
 (`forall z c1 c2 a b l. z IN osq c1 c2 a b l <=>
      linside a b (a * c1 + b * c2 - l / &2) (--b * c1 + a * c2 - l / &2) l (z$1) (z$2)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM VEC2_ETA] THEN
  REWRITE_TAC[OSQ_LSQ]);;

let OO_OSQ = prove
 (`forall c1 c2 a b l m z.
     z IN osq (c1 (oidx c1 c2 a b l m)) (c2 (oidx c1 c2 a b l m))
              (a (oidx c1 c2 a b l m)) (b (oidx c1 c2 a b l m)) l <=>
     linside (ooc c1 c2 a b l m) (oos c1 c2 a b l m) (oou c1 c2 a b l m) (oov c1 c2 a b l m) l
             (z$1) (z$2)`,
  REWRITE_TAC[PK_OSQ_LINSIDE; ooc; oos; oou; oov]);;

let OO_OSQ_PT = prove
 (`forall c1 c2 a b l m x y.
     vector[x; y] IN osq (c1 (oidx c1 c2 a b l m)) (c2 (oidx c1 c2 a b l m))
              (a (oidx c1 c2 a b l m)) (b (oidx c1 c2 a b l m)) l <=>
     linside (ooc c1 c2 a b l m) (oos c1 c2 a b l m) (oou c1 c2 a b l m) (oov c1 c2 a b l m) l x y`,
  REWRITE_TAC[OO_OSQ; VECTOR_2]);;

(* ------------------------------------------------------------------------- *)
(* Exemptions and the individual budget (Lean: AuxPacking.nat_aux_budget).   *)
(* ------------------------------------------------------------------------- *)

let auxex = new_definition
 `auxex k = if k = 0 then
   {3,12,48,192,2304,1536,259,4099,8195,524,8204,16396,1072,16432,32816,2240,4288,32960,
    1792,2816,3328,6400,3584,17920,4355,8451,8716,16908,17456,33840,6336,35008,3840}
   else
   {3,12,48,192,768,3072,259,4099,8195,524,8204,16396,1072,16432,32816,2240,4288,32960,
    1792,2816,8960,3328,3584,35840,4355,8451,8716,16908,17456,33840,6336,35008,3840}`;;

(* Lean: RelaxedOwnerDomain.lower / upper, the exact budget interval *)
let pklow = new_definition `pklow m k = if m IN auxex k then 0 else 1`;;
let pkup = new_definition `pkup fam m k = CARD (fam INTER auxex k) - 2 + pklow m k`;;

let AUXEX_CONV tm =
  (REWRITE_CONV[auxex] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[IN_INSERT; NOT_IN_EMPTY] THENC
   NUM_REDUCE_CONV THENC REWRITE_CONV[]) tm;;

(* Lean: code_f_exempt / code_g_exempt on the 103 candidate masks *)
let AUXEX_PAIRIN = prove
 (`forall k m. k < 2 /\ MEM m CANDMASKS ==> (m IN auxex k <=> pairin (PKS k) (bitset m))`,
  let case_tac (asl, w) =
    let m = dest_small_numeral (lhand (lhs w)) and k = dest_small_numeral (rand (rand (lhs w))) in
    let lth = AUXEX_CONV (lhs w) in
    let rth = TRANS (AP_TERM (rator (rhs w)) (bitset_bits m)) (pk_is k (bits m)) in
    ACCEPT_TAC (TRANS lth (SYM rth)) (asl, w) in
  REWRITE_TAC[ARITH_RULE `k < 2 <=> k = 0 \/ k = 1`; CANDMASKS; MEM] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (DISJ_CASES_THEN SUBST1_TAC) (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)) THEN
  case_tac);;

let FINITE_LT12_P = prove
 (`forall P. FINITE {j:num | j < 12 /\ P j}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j:num | j < 12}` THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[]);;

(* Lean: nat_aux_budget *)
let PK_BUDGET = prove
 (`forall c1 c2 a b l fam k i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\
       k < 2 /\ i < 12
     ==> pklow (ownmask (c1 i) (c2 i) (a i) (b i) l) k <= CARD (auxown k (c1 i) (c2 i) (a i) (b i) l) /\
         CARD (auxown k (c1 i) (c2 i) (a i) (b i) l) <= pkup fam (ownmask (c1 i) (c2 i) (a i) (b i) l) k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pkup; pklow] THEN
  ABBREV_TAC `E = {j:num | ownmask ((c1:num->real) j) (c2 j) (a j) (b j) l IN auxex k}` THEN
  SUBGOAL_THEN `forall j. j < 12 ==> (pairin (PKS k) (owned ((c1:num->real) j) (c2 j) (a j) (b j) l) <=> j IN E)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REWRITE_TAC[GSYM OWNED_BITSET] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC AUXEX_PAIRIN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OWNMASK_IN_TABLE THEN ASM_MESON_TAC[NPACK_SQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\j. auxown k ((c1:num->real) j) (c2 j) (a j) (b j) l`; `E:num->bool`; `i:num`]
                BUDGET_INDIV) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[AUXOWN_SUBSET10; AUXOWN_DISJ] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                  `k:num`; `j:num`] SQUARE_NONEMPTY) THEN
    ASM_SIMP_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `fam INTER auxex k =
                IMAGE (\j. ownmask ((c1:num->real) j) (c2 j) (a j) (b j) l) {j:num | j < 12 /\ j IN E}`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && rhs(concl th) = `fam:num->bool`)) THEN
    EXPAND_TAC "E" THEN REWRITE_TAC[FFP; GSYM IMAGE_o] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; IN_ELIM_THM; o_THM; ownmask] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD (fam INTER auxex k) = CARD {j:num | j < 12 /\ j IN E}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN REWRITE_TAC[FINITE_LT12_P] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC OWNMASK_INJ THEN
    MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD {j:num | j < 12 /\ j IN E} + CARD {j:num | j < 12 /\ ~(j IN E)} = 12` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM (SPEC `12` CARD_NUMSEG_LT)] THEN
    MATCH_MP_TAC CARD_UNION_EQ THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ownmask ((c1:num->real) i) (c2 i) (a i) (b i) l IN auxex k <=> i IN E` SUBST1_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  ASM_CASES_TAC `(i:num) IN E` THEN ASM_REWRITE_TAC[LE_0] THENL
   [SUBGOAL_THEN `{j:num | j < 12 /\ ~(j IN E) /\ ~(j = i)} = {j:num | j < 12 /\ ~(j IN E)}` ASSUME_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `CARD (auxown k ((c1:num->real) i) (c2 i) (a i) (b i) l) +
                 CARD {j:num | j < 12 /\ ~(j IN E) /\ ~(j = i)} <= 10` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `CARD {j:num | j < 12 /\ j IN E} + CARD {j:num | j < 12 /\ ~(j IN E)} = 12` THEN
    ARITH_TAC;
    CONJ_TAC THENL
     [MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                    `k:num`; `i:num`] SQUARE_NONEMPTY) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `CARD {j:num | j < 12 /\ ~(j IN E)} = CARD {j:num | j < 12 /\ ~(j IN E) /\ ~(j = i)} + 1`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `{j:num | j < 12 /\ ~(j IN E)} = (i:num) INSERT {j:num | j < 12 /\ ~(j IN E) /\ ~(j = i)}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      SIMP_TAC[CARD_CLAUSES; FINITE_LT12_P] THEN REWRITE_TAC[IN_ELIM_THM; ADD1];
      ALL_TAC] THEN
    UNDISCH_TAC `CARD (auxown k ((c1:num->real) i) (c2 i) (a i) (b i) l) +
                 CARD {j:num | j < 12 /\ ~(j IN E) /\ ~(j = i)} <= 10` THEN
    UNDISCH_TAC `CARD {j:num | j < 12 /\ ~(j IN E)} = CARD {j:num | j < 12 /\ ~(j IN E) /\ ~(j = i)} + 1` THEN
    UNDISCH_TAC `CARD (fam INTER auxex k) = CARD {j:num | j < 12 /\ j IN E}` THEN
    UNDISCH_TAC `CARD {j:num | j < 12 /\ j IN E} + CARD {j:num | j < 12 /\ ~(j IN E)} = 12` THEN
    ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Combined owners (Lean: DomainSpecs.combinedOwners, CombinedPacking).      *)
(* ------------------------------------------------------------------------- *)

let combown = new_definition
 `combown (x:num->bool) y = x UNION IMAGE (\n. n + 10) y`;;

(* Lean: natCombinedOwners p i = combinedOwners (natAuxOwners p 0 i) (natAuxOwners p 1 i) *)
let AUXOWN2_COMBOWN = prove
 (`forall c1 c2 a b l. auxown 2 c1 c2 a b l = combown (auxown 0 c1 c2 a b l) (auxown 1 c1 c2 a b l)`,
  REWRITE_TAC[combown; AUXOWN2]);;

(* Lean: nat_combined_disjoint *)
let PK_COMBINED_DISJOINT = prove
 (`forall c1 c2 a b l i j. NPACK c1 c2 a b l /\ i < 12 /\ j < 12 /\ ~(i = j)
     ==> DISJOINT (auxown 2 (c1 i) (c2 i) (a i) (b i) l) (auxown 2 (c1 j) (c2 j) (a j) (b j) l)`,
  MESON_TAC[AUXOWN_DISJ]);;

(* Lean: nat_combined_exact (AuxExact (p.square i) 2 (natCombinedOwners p i)) *)
let PK_COMBINED_EXACT = prove
 (`forall c1 c2 a b l j. j < 20
     ==> (linside a b (a * c1 + b * c2 - l / &2) (--b * c1 + a * c2 - l / &2) l
                  (EL j (AUXPTS 2)$1) (EL j (AUXPTS 2)$2) <=> j IN auxown 2 c1 c2 a b l)`,
  SIMP_TAC[auxown; IN_ELIM_THM; LEN_AUX.(2); PK_OSQ_LINSIDE]);;

(* ------------------------------------------------------------------------- *)
(* Certified domains (Lean: S12.CertifiedDomain, OwnerBudget.HalfDomain).     *)
(* ------------------------------------------------------------------------- *)

let cdom = new_definition
 `cdom fam m (al:(num->bool)list) <=>
    forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\ i < 12 /\
       ownmask (c1 i) (c2 i) (a i) (b i) l = m
       ==> MEM (auxown 2 (c1 i) (c2 i) (a i) (b i) l) al`;;

let hdom = new_definition
 `hdom fam m k (al:(num->bool)list) <=>
    forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\ i < 12 /\
       ownmask (c1 i) (c2 i) (a i) (b i) l = m
       ==> MEM (auxown k (c1 i) (c2 i) (a i) (b i) l) al`;;

(* Lean: OriginalOwners.domain (d.sound at ownerIndex) *)
let CDOM_OWNER = prove
 (`forall fam m al c1 c2 a b l. cdom fam m al /\ NPACK c1 c2 a b l /\
       IMAGE binarysum (FFP c1 c2 a b l) = fam /\ m IN fam
       ==> MEM (ooaux c1 c2 a b l m) al`,
  REWRITE_TAC[cdom; ooaux] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[OIDX_LT] THEN MATCH_MP_TAC OIDX_SPEC THEN ASM_MESON_TAC[]);;

(* weakening of the allowed list (used for Lean's cached_domain) *)
let CDOM_MONO = prove
 (`forall fam m al al'. cdom fam m al /\ ALL (\s. MEM s al') al ==> cdom fam m al'`,
  REWRITE_TAC[cdom; GSYM ALL_MEM] THEN MESON_TAC[]);;

let HDOM_MONO = prove
 (`forall fam m k al al'. hdom fam m k al /\ ALL (\s. MEM s al') al ==> hdom fam m k al'`,
  REWRITE_TAC[hdom; GSYM ALL_MEM] THEN MESON_TAC[]);;

(* the per-square local statement gives a domain, through the budget *)
let PK_HDOM_OF_LOCAL = prove
 (`forall fam m k lo hi al. k < 2 /\ lo <= pklow m k /\ pkup fam m k <= hi /\
     (forall c1 c2 a b l. &1 < l /\ l <= &1001 / &1000 /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
          owned c1 c2 a b l = bitset m /\
          lo <= CARD (auxown k c1 c2 a b l) /\ CARD (auxown k c1 c2 a b l) <= hi
          ==> MEM (auxown k c1 c2 a b l) al)
     ==> hdom fam m k al`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[hdom] THEN
  MAP_EVERY X_GEN_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `fam:num->bool`; `k:num`; `i:num`] PK_BUDGET) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`] NPACK_SQ) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM OWNED_BITSET] THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[LE_TRANS];
    ASM_MESON_TAC[LE_TRANS]]);;

let PK_CDOM_OF_LOCAL = prove
 (`forall fam m lo0 hi0 lo1 hi1 al.
     lo0 <= pklow m 0 /\ pkup fam m 0 <= hi0 /\ lo1 <= pklow m 1 /\ pkup fam m 1 <= hi1 /\
     (forall c1 c2 a b l. &1 < l /\ l <= &1001 / &1000 /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
          owned c1 c2 a b l = bitset m /\
          lo0 <= CARD (auxown 0 c1 c2 a b l) /\ CARD (auxown 0 c1 c2 a b l) <= hi0 /\
          lo1 <= CARD (auxown 1 c1 c2 a b l) /\ CARD (auxown 1 c1 c2 a b l) <= hi1
          ==> MEM (auxown 2 c1 c2 a b l) al)
     ==> cdom fam m al`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[cdom] THEN
  MAP_EVERY X_GEN_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `fam:num->bool`; `0`; `i:num`] PK_BUDGET) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `fam:num->bool`; `1`; `i:num`] PK_BUDGET) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`] NPACK_SQ) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < 2 /\ 1 < 2`] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM OWNED_BITSET] THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[LE_TRANS]; ASM_MESON_TAC[LE_TRANS];
    ASM_MESON_TAC[LE_TRANS]; ASM_MESON_TAC[LE_TRANS]]);;

(* Lean: OwnerBudget.product / CertifiedDomain.ofProduct, as a theorem *)
let PK_PRODUCT = prove
 (`forall fam m al0 al1 al. hdom fam m 0 al0 /\ hdom fam m 1 al1 /\
     (forall x y. MEM x al0 /\ MEM y al1 ==> MEM (combown x y) al)
     ==> cdom fam m al`,
  REWRITE_TAC[hdom; cdom; AUXOWN2_COMBOWN] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* OCaml support: literal number sets.                                       *)
(* ------------------------------------------------------------------------- *)

(* the elements of a literal set  {a, b, ..}, {} or set_of_list [..] *)
let rec dest_numset tm =
  if is_comb tm && rator tm = `set_of_list:(num)list->num->bool` then
    map dest_small_numeral (dest_list (rand tm))
  else if tm = `{}:num->bool` then []
  else try map dest_small_numeral (dest_setenum tm)
       with Failure _ -> failwith ("dest_numset: " ^ string_of_term tm);;

let numset_of tm = setify (dest_numset tm);;

let mk_numset l =
  let l = setify l in
  if l = [] then `{}:num->bool` else mk_setenum(map mk_small_numeral l, `:num`);;

(* a named family (a constant defined by new_definition) unfolds to its literal *)
let fam_unfold tm =
  if is_const tm then
    (try find (fun th -> lhs (concl th) = tm) (definitions ()) with Failure _ -> REFL tm)
  else REFL tm;;
let fam_defs tm = if is_const tm then [fam_unfold tm] else [];;

(* |- t = set_of_list [sorted distinct elements] *)
let SETLIT_TBL = Hashtbl.create 1000;;
let setlit_conv tm =
  try Hashtbl.find SETLIT_TBL tm with Not_found ->
  let d = fam_unfold tm in
  let tm' = rhs (concl d) in
  let l = numset_of tm' in
  let goal = mk_eq(tm', set_tm l) in
  let th = TRANS d (prove(goal,
    REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY; IN_SET_OF_LIST; MEM] THEN
    TRY (X_GEN_TAC `x:num` THEN EQ_TAC THEN
         DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
         CONV_TAC(NUM_REDUCE_CONV THENC REWRITE_CONV[])))) in
  Hashtbl.add SETLIT_TBL tm th; th;;

(* |- s = t  for two literal sets with the same elements *)
let setlit_eq s t =
  if s = t then REFL s else TRANS (setlit_conv s) (SYM (setlit_conv t));;

(* |- m IN fam  (or |- ~(m IN fam)) for a literal family *)
let in_fam_conv m fam =
  let tm = mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral m), fam) in
  (RAND_CONV fam_unfold THENC
   REWRITE_CONV[IN_INSERT; NOT_IN_EMPTY; IN_SET_OF_LIST; MEM] THENC NUM_REDUCE_CONV THENC
   REWRITE_CONV[]) tm;;
let in_fam m fam = EQT_ELIM (in_fam_conv m fam);;

(* FILTER P [literal list], deciding each condition with cc (which must give
   T or F) before expanding the tail (REWRITE_CONV[FILTER] is exponential) *)
let rec filter_by_conv cc tm =
  if is_const (rand tm) then REWR_CONV (CONJUNCT1 FILTER) tm else
  let th1 = REWR_CONV (CONJUNCT2 FILTER) tm in
  let th2 = RATOR_CONV (RATOR_CONV (RAND_CONV (TRY_CONV BETA_CONV THENC cc))) (rhs (concl th1)) in
  let th3 = GEN_REWRITE_CONV I [COND_CLAUSES] (rhs (concl th2)) in
  let r = rhs (concl th3) in
  let th4 = if fst (strip_comb r) = `CONS:num->(num)list->(num)list` ||
               (is_const (fst (strip_comb r)) && fst (dest_const (fst (strip_comb r))) = "CONS")
            then RAND_CONV (filter_by_conv cc) r else filter_by_conv cc r in
  TRANS th1 (TRANS th2 (TRANS th3 th4));;

(* |- CARD (fam INTER auxex k) = n *)
let SOL_INTER = prove
 (`forall l s. set_of_list l INTER s = set_of_list (FILTER (\x:num. x IN s) l)`,
  REWRITE_TAC[EXTENSION; IN_INTER; IN_SET_OF_LIST; MEM_FILTER] THEN MESON_TAC[]);;

let card_exempt fam k =
  let tm = mk_comb(`CARD:(num->bool)->num`,
             mk_binop `(INTER):(num->bool)->(num->bool)->(num->bool)` fam (mk_comb(`auxex`, mk_small_numeral k))) in
  let th1 = (RAND_CONV (LAND_CONV setlit_conv) THENC RAND_CONV (REWR_CONV SOL_INTER) THENC
             RAND_CONV (RAND_CONV (filter_by_conv AUXEX_CONV))) tm in
  TRANS th1 (CARD_LIST_CONV (rhs(concl th1)));;

(* |- pklow m k = n  and  |- pkup fam m k = n *)
let pklow_thm m k =
  (REWRITE_CONV[pklow] THENC ONCE_DEPTH_CONV (fun t ->
     if is_binop `(IN):num->(num->bool)->bool` t then AUXEX_CONV t else failwith "") THENC
   REWRITE_CONV[]) (list_mk_comb(`pklow`, [mk_small_numeral m; mk_small_numeral k]));;
let pkup_thm fam m k =
  let tm = list_mk_comb(`pkup`, [fam; mk_small_numeral m; mk_small_numeral k]) in
  (REWRITE_CONV[pkup; card_exempt fam k; pklow_thm m k] THENC NUM_REDUCE_CONV) tm;;
let pk_num th = dest_small_numeral (rhs (concl th));;

(* |- a <= b for numerals after rewriting with eqs *)
let num_le_thm a b eqs =
  EQT_ELIM ((REWRITE_CONV eqs THENC NUM_REDUCE_CONV) (mk_binop `(<=):num->num->bool` a b));;

(* |- MEM s al  for a literal set s whose elements occur as an entry of al *)
let mem_lit s al =
  let ls = numset_of s in
  let t = try find (fun e -> numset_of e = ls) (dest_list al)
          with Failure _ -> failwith ("mem_lit: " ^ string_of_term s ^ " not allowed") in
  let memt = EQT_ELIM (REWRITE_CONV[MEM] (mk_comb(mk_comb(`MEM:(num->bool)->(num->bool)list->bool`, t), al))) in
  EQ_MP (SYM (AP_THM (AP_TERM `MEM:(num->bool)->(num->bool)list->bool` (setlit_eq s t)) al)) memt;;

(* |- ALL (\s. MEM s al') al *)
let all_mem_thm al al' =
  let tm = list_mk_comb(`ALL:((num->bool)->bool)->(num->bool)list->bool`,
             [mk_abs(`s:num->bool`, mk_comb(mk_comb(`MEM:(num->bool)->(num->bool)list->bool`, `s:num->bool`), al')); al]) in
  let els = dest_list al in
  if els = [] then EQT_ELIM (REWRITE_CONV[ALL] tm) else
  let eqth = (REWRITE_CONV[ALL] THENC DEPTH_CONV BETA_CONV) tm in
  let mems = map (fun s -> mem_lit s al') els in
  EQ_MP (SYM eqth) (end_itlist CONJ mems);;

(* weaken a domain theorem to a target list (Lean: cached_domain) *)
let cdom_cache th al' =
  let al = rand (concl th) in
  MATCH_MP CDOM_MONO (CONJ th (all_mem_thm al al'));;
let hdom_cache th al' =
  let al = rand (concl th) in
  MATCH_MP HDOM_MONO (CONJ th (all_mem_thm al al'));;

(* from  A |- x = s1 \/ ... \/ x = sn  (or A |- F) to  A |- MEM x al *)
let MEM_TM = `MEM:(num->bool)->(num->bool)list->bool`;;
let mem_of_eq th al =     (* th: |- x = s, s a literal occurring (as a set) in al *)
  EQ_MP (SYM (AP_THM (AP_TERM MEM_TM th) al)) (mem_lit (rhs (concl th)) al);;
let disj_to_mem x dth al =
  let memtm = mk_comb(mk_comb(MEM_TM, x), al) in
  let rec go th =
    if is_disj (concl th) then
      let p, q = dest_disj (concl th) in DISJ_CASES th (go (ASSUME p)) (go (ASSUME q))
    else if concl th = `false` then CONTR memtm th
    else mem_of_eq th al in
  go dth;;

(* ------------------------------------------------------------------------- *)
(* Producers: single and combined specs (Lean: SingleSpec / CombinedSpec     *)
(* .actual, HalfDomain.ofSpec, CertifiedDomain.ofCombined).                  *)
(* ------------------------------------------------------------------------- *)

let pk_single_row n =
  try find (fun (i,_,_,_,_,_) -> i = n) (SINGLE_SPECS @ !EXTRA_SINGLE)
  with Failure _ -> failwith (Printf.sprintf "no single spec %d" n);;
let pk_comb_row n =
  try find (fun (i,_,_,_,_) -> i = n) (COMBINED_SPECS @ !EXTRA_COMBINED)
  with Failure _ -> failwith (Printf.sprintf "no combined spec %d" n);;

let pk_single_thm n =
  try Hashtbl.find SPEC_TBL n with Not_found ->
    let (_,m0,k0,lo0,hi0,al0) = pk_single_row n in
    let th = spec_theorem m0 k0 lo0 hi0 al0 in Hashtbl.replace SPEC_TBL n th; th;;

let le_tm a b = mk_binop `(<=):num->num->bool` a b;;
let bound_tms k lo hi =
  (le_tm (mk_small_numeral lo) (card_tm (auxown_tm k)), le_tm (card_tm (auxown_tm k)) (mk_small_numeral hi));;
let bitset_tm m = mk_comb(`bitset`, mk_small_numeral m);;

(* local combined spec on scalar square variables:
   LQ_HYPS, owned = set_of_list (bits m), bounds |- disjunction over auxown 2 *)
(* local queries: Phase-1 table, plus transformed query data registered by
   later files (re-proved on first use by query_theorem) *)
let PK_XQ = Hashtbl.create 100;;
let pk_lq (m, k, owned) =
  try Hashtbl.find LQ_TABLE (m, k, owned) with Not_found ->
  try let (uin, uout) = Hashtbl.find PK_XQ (m, k, owned) in
      let th = query_theorem (-1, m, k, owned, uin, uout) in
      Hashtbl.add LQ_TABLE (m, k, owned) th; th
  with Not_found -> lq_thm (m, k, owned);;

let PK_COMB_TBL = Hashtbl.create 100;;
let pk_comb_local n =
  try Hashtbl.find PK_COMB_TBL n with Not_found ->
  let (_,m,f,g,allowed) = pk_comb_row n in
  let (_,mf,k0,lo0,hi0,_) = pk_single_row f and (_,mg,k1,lo1,hi1,_) = pk_single_row g in
  if mf <> m || mg <> m || k0 <> 0 || k1 <> 1 then failwith "pk_comb_local: bad spec" else
  let sqhyps = map ASSUME LQ_HYPS in
  let ownp = mk_eq(`owned c1 c2 a b l`, set_tm (bits m)) in
  let own = ASSUME ownp in
  let (l0, h0) = bound_tms 0 lo0 hi0 and (l1, h1) = bound_tms 1 lo1 hi1 in
  let run sth lo hi = List.fold_left MP (SPECL SPEC5 sth) (sqhyps @ [own; ASSUME lo; ASSUME hi]) in
  let d0 = run (pk_single_thm f) l0 h0 and d1 = run (pk_single_thm g) l1 h1 in
  let a2 = auxown_tm 2 in
  let goal = if allowed = [] then `false` else list_mk_disj (map (fun d -> mk_eq(a2, set_tm d)) allowed) in
  let qcase thx thy =
    let th = MATCH_MP AUXOWN2_LIST (CONJ thx thy) in
    let th = CONV_RULE (RAND_CONV (RAND_CONV (REWRITE_CONV[APPEND; MAP] THENC DEPTH_CONV BETA_CONV THENC
                                               NUM_REDUCE_CONV))) th in
    let s = map dest_small_numeral (dest_list (rand(rand(concl th)))) in
    if mem s allowed then
      let ds = disjuncts goal in
      let i = index (mk_eq(a2, set_tm s)) ds in
      let rec build ds j = match ds with
          [_] -> th
        | d::rest -> if j = 0 then DISJ1 th (list_mk_disj rest) else DISJ2 d (build rest (j-1))
        | [] -> failwith "build" in
      build ds i
    else
      let q = pk_lq (m, 2, s) in
      CONTR goal (List.fold_left MP (SPECL SPEC5 q) (sqhyps @ [own; th])) in
  let cases dth k =
    let rec go th = if is_disj (concl th) then
        let a, b = dest_disj (concl th) in DISJ_CASES th (k (ASSUME a)) (go (ASSUME b))
      else if concl th = `false` then CONTR goal th else k th in
    go dth in
  let th = cases d0 (fun thx -> cases d1 (fun thy -> qcase thx thy)) in
  let res = (m, (lo0, hi0, lo1, hi1), LQ_HYPS @ [ownp; l0; h0; l1; h1], th) in
  Hashtbl.add PK_COMB_TBL n res; res;;

(* discharge the local hypotheses (given as a list, in order) from a conjunction *)
let disch_conj hyps th =
  let c = list_mk_conj hyps in
  let cs = CONJUNCTS (ASSUME c) in
  DISCH c (List.fold_left (fun th h -> PROVE_HYP h th) th cs);;

(* the local statement with  owned = bitset m, MEM conclusion *)
let local_to_mem m x hyps th al =
  let ownp = mk_eq(`owned c1 c2 a b l`, set_tm (bits m)) in
  let ownb = mk_eq(`owned c1 c2 a b l`, bitset_tm m) in
  let bb = bitset_bits m in
  let memth = disj_to_mem x th al in
  let memth = PROVE_HYP (TRANS (ASSUME ownb) bb) memth in
  let hyps' = map (fun h -> if h = ownp then ownb else h) hyps in
  GENL SPEC5 (disch_conj hyps' memth);;

(* Lean: CertifiedDomain.ofCombined / RelaxedOwnerDomain.ofCombined.
   |- cdom fam m al  for combined spec n; al defaults to the spec's list. *)
let pk_combined_x fam n al_opt =
  let (m, (lo0, hi0, lo1, hi1), hyps, th) = pk_comb_local n in
  let (_,_,_,_,allowed) = pk_comb_row n in
  let al = match al_opt with Some al -> al
           | None -> mk_list(map mk_numset allowed, `:num->bool`) in
  let loc = local_to_mem m (auxown_tm 2) hyps th al in
  let mt = mk_small_numeral m in
  let lw0 = pklow_thm m 0 and lw1 = pklow_thm m 1 in
  let up0 = pkup_thm fam m 0 and up1 = pkup_thm fam m 1 in
  let b1 = num_le_thm (mk_small_numeral lo0) (lhs(concl lw0)) [lw0]
  and b2 = num_le_thm (lhs(concl up0)) (mk_small_numeral hi0) [up0]
  and b3 = num_le_thm (mk_small_numeral lo1) (lhs(concl lw1)) [lw1]
  and b4 = num_le_thm (lhs(concl up1)) (mk_small_numeral hi1) [up1] in
  let th = SPECL [fam; mt; mk_small_numeral lo0; mk_small_numeral hi0; mk_small_numeral lo1;
                  mk_small_numeral hi1; al] PK_CDOM_OF_LOCAL in
  MP th (end_itlist CONJ [b1; b2; b3; b4; loc]);;
let pk_combined fam n = pk_combined_x fam n None;;

(* hdom from a local single statement  hyps |- disjunction over auxown k *)
let pk_hdom_local fam m k lo hi hyps th al =
  let loc = local_to_mem m (auxown_tm k) hyps th al in
  let lw = pklow_thm m k and up = pkup_thm fam m k in
  let b1 = num_le_thm (mk_small_numeral lo) (lhs(concl lw)) [lw]
  and b2 = num_le_thm (lhs(concl up)) (mk_small_numeral hi) [up] in
  let kl = EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` (mk_small_numeral k) `2`)) in
  let th = SPECL [fam; mk_small_numeral m; mk_small_numeral k; mk_small_numeral lo; mk_small_numeral hi; al]
             PK_HDOM_OF_LOCAL in
  MP th (end_itlist CONJ [kl; b1; b2; loc]);;

let single_local n =
  let (_,m,k,lo,hi,allowed) = pk_single_row n in
  let sth = pk_single_thm n in
  let ownp = mk_eq(`owned c1 c2 a b l`, set_tm (bits m)) in
  let (hl, hh) = bound_tms k lo hi in
  let hyps = LQ_HYPS @ [ownp; hl; hh] in
  let th = List.fold_left MP (SPECL SPEC5 sth) (map ASSUME hyps) in
  (m, k, lo, hi, allowed, hyps, th);;

(* Lean: HalfDomain.ofSpec / RelaxedOwnerDomain.ofSingle:  |- hdom fam m k al *)
let pk_single_x fam n al_opt =
  let (m, k, lo, hi, allowed, hyps, th) = single_local n in
  let al = match al_opt with Some al -> al | None -> mk_list(map mk_numset allowed, `:num->bool`) in
  pk_hdom_local fam m k lo hi hyps th al;;
let pk_single fam n = pk_single_x fam n None;;

(* a budget-only half domain: every subset in the exact budget interval
   (Lean: HalfDomain.singleton / empty, RelaxedOwnerDomain.ofSmallBudget) *)
let rec subsets_upto n l =
  if n = 0 then [[]] else match l with
    [] -> [[]]
  | h::t -> subsets_upto n t @ map (fun s -> h :: s) (subsets_upto (n-1) t);;

let pk_budget_hdom fam m k al_lists =
  let lo = pk_num (pklow_thm m k) and hi = pk_num (pkup_thm fam m k) in
  let al_lists = map (fun s -> List.sort compare s) al_lists in
  let th = spec_theorem m k lo hi al_lists in
  let ownp = mk_eq(`owned c1 c2 a b l`, set_tm (bits m)) in
  let (hl, hh) = bound_tms k lo hi in
  let hyps = LQ_HYPS @ [ownp; hl; hh] in
  let th = List.fold_left MP (SPECL SPEC5 th) (map ASSUME hyps) in
  pk_hdom_local fam m k lo hi hyps th (mk_list(map mk_numset al_lists, `:num->bool`));;

(* Lean: OwnerBudget.HalfDomain.singleton  (allowed [{0}; ...; {9}]) *)
let pk_hdom_singleton fam m k =
  if pk_num (pkup_thm fam m k) <> 1 || pk_num (pklow_thm m k) <> 1 then failwith "pk_hdom_singleton: budget" else
  pk_budget_hdom fam m k (map (fun j -> [j]) (0--9));;
(* Lean: OwnerBudget.HalfDomain.empty  (allowed [{}]) *)
let pk_hdom_empty fam m k =
  if pk_num (pkup_thm fam m k) <> 0 then failwith "pk_hdom_empty: budget" else
  pk_budget_hdom fam m k [[]];;

(* Lean: OwnerBudget.product: |- cdom fam m [combown x y | x in al0, y in al1] *)
let pk_product th0 th1 =
  let al0 = rand (concl th0) and al1 = rand (concl th1) in
  let comb x y = setify (numset_of x @ map (fun j -> j + 10) (numset_of y)) in
  let al = mk_list(List.concat (map (fun x -> map (fun y -> mk_numset (comb x y)) (dest_list al1)) (dest_list al0)),
                   `:num->bool`) in
  let case_tac (asl, w) =
    let ct = lhand w in
    let x = lhand ct and y = rand ct in
    let eq = (REWRITE_CONV[combown] THENC
              LAND_CONV setlit_conv THENC RAND_CONV (RAND_CONV setlit_conv) THENC
              REWRITE_CONV[GSYM SET_OF_LIST_MAP; GSYM SET_OF_LIST_APPEND; MAP; APPEND] THENC
              DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV) ct in
    let target = mk_numset (comb x y) in
    let eq2 = TRANS eq (TRANS (setlit_conv (rhs (concl eq))) (SYM (setlit_conv target))) in
    let memt = EQT_ELIM (REWRITE_CONV[MEM] (mk_comb(mk_comb(MEM_TM, target), al))) in
    ACCEPT_TAC (EQ_MP (SYM (AP_THM (AP_TERM MEM_TM eq2) al)) memt) (asl, w) in
  let subst_or_contr th = SUBST1_TAC th ORELSE CONTR_TAC th in
  let side = prove(mk_forall(`x:num->bool`, mk_forall(`y:num->bool`,
     mk_imp(mk_conj(mk_comb(mk_comb(MEM_TM, `x:num->bool`), al0), mk_comb(mk_comb(MEM_TM, `y:num->bool`), al1)),
            mk_comb(mk_comb(MEM_TM, `combown x y`), al)))),
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[MEM]) (MP_TAC o REWRITE_RULE[MEM])) THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN subst_or_contr) THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN subst_or_contr) THEN case_tac) in
  MATCH_MP PK_PRODUCT (end_itlist CONJ [th0; th1; side]);;

(* ------------------------------------------------------------------------- *)
(* Literal set decisions and FILTER evaluation.                              *)
(* ------------------------------------------------------------------------- *)

(* |- (s = t) <=> T  or  |- (s = t) <=> F  for literal sets *)
let setlit_eq_conv tm =
  let s, t = dest_eq tm in
  let ls = numset_of s and lt = numset_of t in
  if ls = lt then EQT_INTRO (setlit_eq s t) else
  let ne = set_neq ls lt in
  let f = MP (NOT_ELIM ne) (TRANS (SYM (setlit_conv s)) (TRANS (ASSUME tm) (setlit_conv t))) in
  EQF_INTRO (NOT_INTRO (DISCH tm f));;

let is_numset t = try ignore (dest_numset t); true with Failure _ -> false;;

let setlit_eq_dconv t =
  if is_eq t && type_of (lhs t) = `:num->bool` && is_numset (lhs t) && is_numset (rhs t)
  then setlit_eq_conv t else failwith "setlit_eq_dconv";;

(* FILTER P [literal list], with pc deciding the (beta-reduced) instances of P *)
let filter_eval_conv pc tm =
  filter_by_conv (ONCE_DEPTH_CONV pc THENC REWRITE_CONV[]) tm;;

(* ------------------------------------------------------------------------- *)
(* Packing-level facts used by the owner vocabulary (Lean: OriginalOwners).  *)
(* ------------------------------------------------------------------------- *)

(* Lean: OriginalOwners.auxiliary_exact *)
let OO_AUX_EXACT = prove
 (`forall c1 c2 a b l m j. j < 20
     ==> (linside (ooc c1 c2 a b l m) (oos c1 c2 a b l m) (oou c1 c2 a b l m) (oov c1 c2 a b l m) l
                  (EL j (AUXPTS 2)$1) (EL j (AUXPTS 2)$2) <=> j IN ooaux c1 c2 a b l m)`,
  REWRITE_TAC[ooaux; ooc; oos; oou; oov] THEN SIMP_TAC[PK_COMBINED_EXACT]);;

(* Lean: OriginalOwners.auxiliary_disjoint *)
let OO_AUX_DISJOINT = prove
 (`forall c1 c2 a b l fam m n. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\
       m IN fam /\ n IN fam /\ ~(m = n)
       ==> DISJOINT (ooaux c1 c2 a b l m) (ooaux c1 c2 a b l n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ooaux] THEN MATCH_MP_TAC PK_COMBINED_DISJOINT THEN
  ASM_REWRITE_TAC[OIDX_LT] THEN ASM_MESON_TAC[OIDX_INJ]);;

(* the point form of auxiliary_exact at a literal index:
   |- !c1 c2 a b l m. linside (ooc ..) .. l x_j y_j <=> j IN ooaux c1 c2 a b l m *)
let OO_AUX_TBL = Hashtbl.create 20;;
let oo_aux_point j =
  try Hashtbl.find OO_AUX_TBL j with Not_found ->
  let lt = EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` (mk_small_numeral j) `20`)) in
  let th = MP (SPEC (mk_small_numeral j) (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`;
                 `b:num->real`; `l:real`; `m:num`] OO_AUX_EXACT)) lt in
  let th = CONV_RULE (LAND_CONV (REWRITE_CONV[AUXPTS_EXPL.(2)] THENC ONCE_DEPTH_CONV EL_CONV THENC
                                 REWRITE_CONV[VECTOR_2])) th in
  let th = GENL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `m:num`] th in
  Hashtbl.add OO_AUX_TBL j th; th;;

let aux2_point j =
  let th = rand(concl(SPEC_ALL (oo_aux_point j))) in ignore th;
  let lin = lhand(concl(SPEC_ALL (oo_aux_point j))) in
  let args = snd(strip_comb lin) in (rat_of_term (el 5 args), rat_of_term (el 6 args));;

(* ------------------------------------------------------------------------- *)
(* Seeds (Lean: S12.Seeds.seedPoints, seed_points_sound), including the      *)
(* corner extras (Lean: CornerForcing.corner_pair_forces).                   *)
(* ------------------------------------------------------------------------- *)

let PK_CORNER_POS = prove
 (`forall c1 c2 a b l bb. &1 < l /\ &0 <= a /\ &0 <= b /\
     (a + b) * l / &2 <= c1 /\ (a + b) * l / &2 <= c2 /\ bb <= &1 /\
     vector[&1; bb] IN osq c1 c2 a b l /\ vector[bb; &1] IN osq c1 c2 a b l
     ==> vector[&1; &1] IN osq c1 c2 a b l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_OSQ_BANDS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= a * (c1 - (a + b) * l / &2) /\ &0 <= b * (c2 - (a + b) * l / &2) /\
                &0 < (l - &1) * (&1 + (a + b) * (a + b)) /\ &0 <= (a + b - &1) * (a + b - &1) /\
                &0 <= a * (&1 - bb) /\ &0 <= b * (&1 - bb)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN MP_TAC(SPEC `a + b:real` REAL_LE_SQUARE) THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LE_SQUARE];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC]);;

let PK_CORNER = prove
 (`forall c1 c2 a b l bb. &1 < l /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\ bb <= &1 /\
     vector[&1; bb] IN osq c1 c2 a b l /\ vector[bb; &1] IN osq c1 c2 a b l
     ==> vector[&1; &1] IN osq c1 c2 a b l`,
  let CASE_TAC (ea,eb) (a',b') =
    SUBGOAL_THEN (mk_conj(mk_eq(`abs a`,ea), mk_eq(`abs b`,eb)))
     (CONJUNCTS_THEN (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`c1:real`; `c2:real`; a'; b'; `l:real`; `bb:real`] PK_CORNER_POS) THEN
    REWRITE_TAC[OSQ_ROT; OSQ_NEG; OSQ_ROT3] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC in
  REPEAT GEN_TAC THEN REWRITE_TAC[owalls] THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= a` THEN ASM_CASES_TAC `&0 <= b` THENL
   [CASE_TAC (`a:real`,`b:real`) (`a:real`,`b:real`);
    CASE_TAC (`a:real`,`--b`) (`--b`,`a:real`);
    CASE_TAC (`--a`,`b:real`) (`b:real`,`--a`);
    CASE_TAC (`--a`,`--b`) (`--a`,`--b`)]);;

let PK_CORNER0 =
  let hyps = [`&1 < l`; `a * a + b * b = &1`; `owalls c1 c2 a b l`;
              `vector[&1; &457 / &500] IN osq c1 c2 a b l`;
              `vector[&457 / &500; &1] IN osq c1 c2 a b l`] in
  prove(list_mk_forall(SPEC5, mk_imp(list_mk_conj hyps, `vector[&1; &1] IN osq c1 c2 a b l`)),
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PK_CORNER THEN EXISTS_TAC `&457 / &500` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let CORNER_EXPL = D4_FORMS PK_CORNER0;;

(* all seed theorems for a square given by parameter terms sp *)
let pk_try_use sp sqhyps facts th =
  let th = SPECL sp th in
  let hs = conjuncts(lhand(concl th)) in
  let prove_h h =
    try find (fun f -> aconv (concl f) h) (facts @ sqhyps)
    with Failure _ ->
      let rels = filter (fun f -> is_real_rel (concl f)) sqhyps in
      if is_real_rel h then
        MP (REAL_ARITH (mk_imp(list_mk_conj (map concl rels), h))) (end_itlist CONJ rels)
      else failwith "no" in
  try CONJUNCTS (MP th (end_itlist CONJ (map prove_h hs))) with Failure _ -> [];;

let pk_seeds sp sqhyps facts clist =
  seeds_at sp sqhyps facts clist @ List.concat (map (pk_try_use sp sqhyps facts) CORNER_EXPL);;

(* Lean's seedPoints (maskSupport m), computed on rationals *)
let marker_q k = let (x, y) = marker_xy k in (rat_of_term x, rat_of_term y);;
let tr_q (sw, rx, ry) (x, y) =
  let (u, v) = if sw then (y, x) else (x, y) in
  ((if rx then num 4 -/ u else u), (if ry then num 4 -/ v else v));;
let ALL_TRF = [(false,false,false); (false,false,true); (false,true,false); (false,true,true);
               (true,false,false); (true,false,true); (true,true,false); (true,true,true)];;
let qeq (x, y) (x', y') = x =/ x' && y =/ y';;
let marker_action t i = let p = tr_q t (marker_q i) in find (fun k -> qeq (marker_q k) p) (0--15);;
let BASE_SINGLETON = [(nlin_rat "28/25", num 1); (nlin_rat "87/50", num 1); (nlin_rat "187/100", nlin_rat "19/25")];;
let seed_points m =
  let g = bits m in
  map marker_q g @
  List.concat (map (fun t ->
    (if g = [marker_action t 0] then map (tr_q t) BASE_SINGLETON else []) @
    (if mem (marker_action t 0) g && mem (marker_action t 1) g then [tr_q t (num 1, num 1)] else []) @
    (if mem (marker_action t 1) g && mem (marker_action t 12) g
     then [tr_q t (num 1, nlin_rat "5/4"); tr_q t (num 1, nlin_rat "7/4")] else [])) ALL_TRF);;

(* the hypothesis  NPACK .. /\ IMAGE binarysum (FFP ..) = fam /\ m IN fam  and the owner's facts *)
let oo_hyp m =
  mk_conj(`NPACK c1 c2 a b l`, mk_conj(`IMAGE binarysum (FFP c1 c2 a b l) = fam`,
    mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral m), `fam:num->bool`)));;
let OO_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `fam:num->bool`];;
let oo_iv m = list_mk_comb(`oidx`, [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                                    mk_small_numeral m]);;
let oo_ctx m =
  let hyp = oo_hyp m in
  let h = ASSUME hyp in
  let hnp = CONJUNCT1 h and hrow = CONJUNCT1 (CONJUNCT2 h) and hin = CONJUNCT2 (CONJUNCT2 h) in
  let iv = oo_iv m in
  let lt = SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                  mk_small_numeral m] OIDX_LT in
  let own = TRANS (MATCH_MP OIDX_OWNED (CONJ hrow hin)) (bitset_bits m) in
  let sqth = CONJUNCTS (MATCH_MP NPACK_SQ (CONJ hnp lt)) in
  (hyp, iv, lt, own, sqth);;

(* osq membership at the owner -> linside of the owner 5-tuple *)
let oo_lin m th =
  let pt = lhand (concl th) in
  let [x; y] = dest_list (rand pt) in
  EQ_MP (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                mk_small_numeral m; x; y] OO_OSQ_PT) th;;

let OO_SEED_TBL = Hashtbl.create 100;;
(* all seed points of the owner of m:  [(point, hyp |- linside (owner m) x y)] *)
let oo_seed_all m =
  try Hashtbl.find OO_SEED_TBL m with Not_found ->
  let (hyp, iv, lt, own, sqth) = oo_ctx m in
  let ths = pk_seeds (sq_params iv) sqth (marker_facts own) (bits m) in
  let lins = map (fun th -> let th' = oo_lin m th in
                   let args = snd(strip_comb(concl th')) in
                   ((rat_of_term (el 5 args), rat_of_term (el 6 args)), th')) ths in
  let res = (hyp, lins) in Hashtbl.add OO_SEED_TBL m res; res;;

(* Lean: OriginalOwners.seed at a literal point (x, y) of seedPoints (maskSupport m):
   |- !c1 c2 a b l fam. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\ m IN fam
        ==> linside (ooc c1 c2 a b l m) (oos ..) (oou ..) (oov ..) l x y *)
let oo_seed m (x, y) =
  let p = (rat_of_term x, rat_of_term y) in
  let (hyp, lins) = oo_seed_all m in
  let th = try snd (find (fun (q, _) -> qeq p q) lins)
           with Failure _ -> failwith (Printf.sprintf "oo_seed %d: point (%s, %s) not in seedPoints" m
                                         (string_of_term x) (string_of_term y)) in
  GENL OO_VARS (DISCH hyp th);;

(* every Lean seed point of m is derivable (a check, returns the points) *)
let oo_seed_check m =
  let (_, lins) = oo_seed_all m in
  let pts = seed_points m in
  List.iter (fun p -> if not (exists (fun (q, _) -> qeq p q) lins) then
     failwith (Printf.sprintf "oo_seed_check %d: missing seedPoints entry (%s, %s)" m
                 (string_of_num (fst p)) (string_of_num (snd p)))) pts;
  pts;;

(* Lean: OriginalOwners.known_point, a point of queryInsidePoints mask 2 owned:
   |- !c1 c2 a b l fam. NPACK .. /\ IMAGE .. = fam /\ m IN fam /\ ooaux c1 c2 a b l m = owned
        ==> linside (owner m) x y *)
let oo_known m owned (x, y) =
  let p = (rat_of_term x, rat_of_term y) in
  let eqtm = mk_eq(list_mk_comb(`ooaux`, [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
                                          `l:real`; mk_small_numeral m]), owned) in
  let hyp = oo_hyp m in
  let hyp2 = mk_conj(`NPACK c1 c2 a b l`, mk_conj(`IMAGE binarysum (FFP c1 c2 a b l) = fam`,
               mk_conj(rand(rand hyp), eqtm))) in
  let h2 = ASSUME hyp2 in
  let h1 = CONJ (CONJUNCT1 h2) (CONJ (CONJUNCT1 (CONJUNCT2 h2)) (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 h2)))) in
  let (_, lins) = oo_seed_all m in
  let th =
    try PROVE_HYP h1 (snd (find (fun (q, _) -> qeq p q) lins)) with Failure _ ->
    let j = try find (fun j -> qeq (aux2_point j) p && mem j (numset_of owned)) (0--19)
            with Failure _ -> failwith "oo_known: point not in queryInsidePoints" in
    let ath = SPEC (mk_small_numeral m) (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`;
                 `b:num->real`; `l:real`] (oo_aux_point j)) in
    let eq = CONJUNCT2 (CONJUNCT2 (CONJUNCT2 h2)) in
    let inj = EQT_ELIM ((RAND_CONV (REWR_CONV eq) THENC RAND_CONV setlit_conv THENC
                         REWRITE_CONV[IN_SET_OF_LIST; MEM] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[])
                        (rand (concl ath))) in
    EQ_MP (SYM ath) inj in
  GENL OO_VARS (DISCH hyp2 th);;

(* ------------------------------------------------------------------------- *)
(* Lean: S12.CertifiedDomain.certified_domain_forced.                         *)
(*   pk_forced fam [ |- cdom fam m_j al_j ] m value                           *)
(*   |- !c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP ..) = fam     *)
(*        ==> ooaux c1 c2 a b l m = value                                     *)
(* ------------------------------------------------------------------------- *)

let ooaux_tm m = list_mk_comb(`ooaux`, [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
                                       `l:real`; mk_small_numeral m]);;
let cdom_mask th = dest_small_numeral (rand (rator (concl th)));;
let cdom_fam th = rand (rator (rator (concl th)));;

let pk_forced fam doms m value =
  let hyp = mk_conj(`NPACK c1 c2 a b l`, mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam)) in
  let h = ASSUME hyp in
  let hnp = CONJUNCT1 h and hrow = CONJUNCT2 h in
  let goal = mk_eq(ooaux_tm m, value) in
  let lv = numset_of value in
  let masks = map cdom_mask doms in
  if length (setify masks) <> length masks then failwith "pk_forced: repeated masks" else
  let mems = map (fun d ->
      let mj = cdom_mask d in
      let inj = in_fam mj fam in
      let th = MATCH_MP CDOM_OWNER (CONJ d (CONJ hnp (CONJ hrow inj))) in
      CONV_RULE (REWRITE_CONV[MEM]) th) doms in
  let da = Array.of_list (List.combine masks mems) in
  let n = Array.length da in
  let DTBL = Hashtbl.create 50 in
  let disj mi mj =
    try Hashtbl.find DTBL (mi, mj) with Not_found ->
    let ne = EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral mi, mk_small_numeral mj))) in
    let th = MATCH_MP OO_AUX_DISJOINT (end_itlist CONJ [hnp; hrow; in_fam mi fam; in_fam mj fam; ne]) in
    Hashtbl.add DTBL (mi, mj) th; th in
  let rec dfs j chosen =
    if j = n then failwith "pk_forced: feasible assignment" else
    let (mj, dj) = da.(j) in
    let rec cases th =
      if is_disj (concl th) then
        let p, q = dest_disj (concl th) in DISJ_CASES th (pick (ASSUME p)) (cases (ASSUME q))
      else if concl th = `false` then CONTR goal th
      else pick th
    and pick eqj =
      let s = rhs (concl eqj) in
      let ls = numset_of s in
      let rec conflict ch = match ch with
          [] -> None
        | (mt, eqt, lt) :: rest ->
            if exists (fun x -> mem x ls) lt then
              let d = disj mt mj in
              let d1 = SUBS [eqt; eqj] d in
              Some (CONV_RULE (LAND_CONV setlit_conv THENC RAND_CONV setlit_conv THENC disjoint_conv) d1)
            else conflict rest in
      match conflict chosen with
        Some f -> CONTR goal f
      | None ->
          if mj = m && ls = lv then TRANS eqj (setlit_eq s value)
          else dfs (j + 1) ((mj, eqj, ls) :: chosen) in
    cases dj in
  let th = dfs 0 [] in
  GENL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] (DISCH hyp th);;

(* ------------------------------------------------------------------------- *)
(* Lean: S12.CertifiedDomain.remove (drop one owner set refuted by a local   *)
(* query of kind 2):  pk_remove (|- cdom fam m al) owned  |- cdom fam m al'  *)
(* ------------------------------------------------------------------------- *)

let CDOM_REMOVE = prove
 (`forall fam m al S. cdom fam m al /\
     (forall c1 c2 a b l. &1 < l /\ l <= &1001 / &1000 /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
          owned c1 c2 a b l = bitset m /\ auxown 2 c1 c2 a b l = S ==> false)
     ==> cdom fam m (FILTER (\x. ~(x = S)) al)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cdom; MEM_FILTER] THEN BETA_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`] NPACK_SQ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(c1:num->real) i`; `(c2:num->real) i`; `(a:num->real) i`;
                                  `(b:num->real) i`; `l:real`] o
                  check (fun th -> is_forall (concl th) && length(fst(strip_forall(concl th))) = 5)) THEN
    ASM_REWRITE_TAC[GSYM OWNED_BITSET];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let pk_remove th owned =
  let m = cdom_mask th in
  let ls = numset_of owned in
  let q = pk_lq (m, 2, ls) in
  let ownb = mk_eq(`owned c1 c2 a b l`, bitset_tm m) in
  let auxp = mk_eq(auxown_tm 2, owned) in
  let hyps = LQ_HYPS @ [ownb; auxp] in
  let own = TRANS (ASSUME ownb) (bitset_bits m) in
  let aux = TRANS (ASSUME auxp) (setlit_conv owned) in
  let f = List.fold_left MP (SPECL SPEC5 q) (map ASSUME LQ_HYPS @ [own; aux]) in
  let loc = GENL SPEC5 (disch_conj hyps f) in
  let al = rand (concl th) in
  let r = MATCH_MP CDOM_REMOVE (CONJ th loc) in
  CONV_RULE (RAND_CONV (filter_eval_conv setlit_eq_dconv)) r;;

(* ------------------------------------------------------------------------- *)
(* Single-kind owner sets  natAuxOwners p k (ownerIndex p mask).             *)
(* ------------------------------------------------------------------------- *)

let ooauxk_tm k m =
  let iv = oo_iv m in
  list_mk_comb(`auxown`, [mk_small_numeral k; mk_comb(`c1:num->real`, iv); mk_comb(`c2:num->real`, iv);
                          mk_comb(`a:num->real`, iv); mk_comb(`b:num->real`, iv); `l:real`]);;

(* Lean: HalfDomain.sound at ownerIndex *)
let HDOM_OWNER = prove
 (`forall fam m k al c1 c2 a b l. hdom fam m k al /\ NPACK c1 c2 a b l /\
       IMAGE binarysum (FFP c1 c2 a b l) = fam /\ m IN fam
       ==> MEM (auxown k (c1 (oidx c1 c2 a b l m)) (c2 (oidx c1 c2 a b l m))
                         (a (oidx c1 c2 a b l m)) (b (oidx c1 c2 a b l m)) l) al`,
  REWRITE_TAC[hdom] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[OIDX_LT] THEN MATCH_MP_TAC OIDX_SPEC THEN ASM_MESON_TAC[]);;

(* Lean: nat_aux_exact at ownerIndex *)
let OO_AUXK_EXACT = prove
 (`forall c1 c2 a b l m k j. j < LENGTH (AUXPTS k)
     ==> (linside (ooc c1 c2 a b l m) (oos c1 c2 a b l m) (oou c1 c2 a b l m) (oov c1 c2 a b l m) l
                  (EL j (AUXPTS k)$1) (EL j (AUXPTS k)$2) <=>
          j IN auxown k (c1 (oidx c1 c2 a b l m)) (c2 (oidx c1 c2 a b l m))
                        (a (oidx c1 c2 a b l m)) (b (oidx c1 c2 a b l m)) l)`,
  SIMP_TAC[auxown; IN_ELIM_THM; OO_OSQ]);;

(* Lean: nat_aux_disjoint at two owner indices *)
let OO_AUXK_DISJOINT = prove
 (`forall c1 c2 a b l fam k m n. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\
       m IN fam /\ n IN fam /\ ~(m = n)
       ==> DISJOINT (auxown k (c1 (oidx c1 c2 a b l m)) (c2 (oidx c1 c2 a b l m))
                              (a (oidx c1 c2 a b l m)) (b (oidx c1 c2 a b l m)) l)
                    (auxown k (c1 (oidx c1 c2 a b l n)) (c2 (oidx c1 c2 a b l n))
                              (a (oidx c1 c2 a b l n)) (b (oidx c1 c2 a b l n)) l)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC AUXOWN_DISJ THEN
  ASM_REWRITE_TAC[OIDX_LT] THEN ASM_MESON_TAC[OIDX_INJ]);;

(* |- !c1 c2 a b l m. linside (owner m) x_j y_j <=> j IN auxown k (owner index m ..) *)
let OO_AUXK_TBL = Hashtbl.create 40;;
let oo_auxk_point k j =
  try Hashtbl.find OO_AUXK_TBL (k, j) with Not_found ->
  let vars = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `m:num`] in
  let lt = EQT_ELIM ((REWRITE_CONV[LEN_AUX.(k)] THENC NUM_REDUCE_CONV)
             (mk_binop `(<):num->num->bool` (mk_small_numeral j)
                (mk_comb(`LENGTH:(real^2)list->num`, mk_comb(`AUXPTS`, mk_small_numeral k))))) in
  let th = MP (SPECL (vars @ [mk_small_numeral k; mk_small_numeral j]) OO_AUXK_EXACT) lt in
  let th = CONV_RULE (LAND_CONV (REWRITE_CONV[AUXPTS_EXPL.(k)] THENC ONCE_DEPTH_CONV EL_CONV THENC
                                 REWRITE_CONV[VECTOR_2])) th in
  let th = GENL vars th in Hashtbl.add OO_AUXK_TBL (k, j) th; th;;

(* Lean: certified_domain_forced for one kind k < 2 (forced owners over half domains):
   pk_forced_half k fam [ |- hdom fam m_j k al_j ] m value
   |- !c1 c2 a b l. NPACK .. /\ IMAGE binarysum (FFP ..) = fam ==> auxown k (owner index m ..) = value *)
let pk_forced_half k fam doms m value =
  let hyp = mk_conj(`NPACK c1 c2 a b l`, mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam)) in
  let h = ASSUME hyp in
  let hnp = CONJUNCT1 h and hrow = CONJUNCT2 h in
  let goal = mk_eq(ooauxk_tm k m, value) in
  let lv = numset_of value in
  let hmask th = dest_small_numeral (rand (rator (rator (concl th)))) in
  let masks = map hmask doms in
  if length (setify masks) <> length masks then failwith "pk_forced_half: repeated masks" else
  let mems = map (fun d ->
      let inj = in_fam (hmask d) fam in
      CONV_RULE (REWRITE_CONV[MEM]) (MATCH_MP HDOM_OWNER (CONJ d (CONJ hnp (CONJ hrow inj))))) doms in
  let da = Array.of_list (List.combine masks mems) in
  let n = Array.length da in
  let disj mi mj =
    let ne = EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral mi, mk_small_numeral mj))) in
    MATCH_MP (SPEC (mk_small_numeral k) (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`;
               `b:num->real`; `l:real`; fam] OO_AUXK_DISJOINT))
      (end_itlist CONJ [hnp; hrow; in_fam mi fam; in_fam mj fam; ne]) in
  let rec dfs j chosen =
    if j = n then failwith "pk_forced_half: feasible assignment" else
    let (mj, dj) = da.(j) in
    let rec cases th =
      if is_disj (concl th) then
        let p, q = dest_disj (concl th) in DISJ_CASES th (pick (ASSUME p)) (cases (ASSUME q))
      else if concl th = `false` then CONTR goal th
      else pick th
    and pick eqj =
      let s = rhs (concl eqj) in
      let ls = numset_of s in
      let rec conflict ch = match ch with
          [] -> None
        | (mt, eqt, lt) :: rest ->
            if exists (fun x -> mem x ls) lt then
              let d1 = SUBS [eqt; eqj] (disj mt mj) in
              Some (CONV_RULE (LAND_CONV setlit_conv THENC RAND_CONV setlit_conv THENC disjoint_conv) d1)
            else conflict rest in
      match conflict chosen with
        Some f -> CONTR goal f
      | None ->
          if mj = m && ls = lv then TRANS eqj (setlit_eq s value)
          else dfs (j + 1) ((mj, eqj, ls) :: chosen) in
    cases dj in
  GENL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] (DISCH hyp (dfs 0 []));;

(* ------------------------------------------------------------------------- *)
(* Four-point certificates (Lean: S12.FourPointDatum.sound): a square of     *)
(* side > 1 containing A and B contains P or E (|P - E| <= 1); re-proved by  *)
(* the Phase-1 linear refutation over the faces of P and E.                  *)
(*   pk_four_point (A, B, P, E)  (points as pairs of real literal terms)     *)
(*   |- !c1 c2 a b l. &1 < l /\ a * a + b * b = &1 /\ A IN osq .. /\ B IN osq .. *)
(*        ==> P IN osq .. \/ E IN osq ..                                      *)
(*   oo_four_point (A, B, P, E): the same for the owner of any mask           *)
(* ------------------------------------------------------------------------- *)

let pk_four_point ((ax, ay), (bx, by), (px, py), (ex, ey)) =
  let pt x y = mk_comb(`vector:(real)list->real^2`, mk_list([x; y], `:real`)) in
  let mo p = mk_comb(mk_comb(`(IN):real^2->(real^2->bool)->bool`, p), `osq c1 c2 a b l`) in
  let ma = mo (pt ax ay) and mb = mo (pt bx by) and mp = mo (pt px py) and me = mo (pt ex ey) in
  let sqhyps = map ASSUME [`&1 < l`; `a * a + b * b = &1`] in
  let f = lin_refute sqhyps [ASSUME ma; ASSUME mb] [ASSUME (mk_neg mp); ASSUME (mk_neg me)] in
  let g = mk_disj(mp, me) in
  let th = DISJ_CASES (SPEC mp EXCLUDED_MIDDLE) (DISJ1 (ASSUME mp) me)
             (DISJ_CASES (SPEC me EXCLUDED_MIDDLE) (DISJ2 mp (ASSUME me)) (CONTR g f)) in
  GENL SPEC5 (disch_conj [`&1 < l`; `a * a + b * b = &1`; ma; mb] th);;

let oo_four_point pts =
  let th = pk_four_point pts in
  let vars = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `m:num`] in
  let iv = `oidx c1 c2 a b l m` in
  let th1 = SPECL (sq_params iv) th in
  let sq = MATCH_MP NPACK_SQ (CONJ (ASSUME `NPACK c1 c2 a b l`) (SPEC_ALL OIDX_LT)) in
  let [l1; _; ab; _] = CONJUNCTS sq in
  let conv = REWRITE_CONV[OO_OSQ_PT] in
  let th2 = CONV_RULE (LAND_CONV conv THENC RAND_CONV conv) th1 in
  let ant = lhand (concl th2) in
  let [_; _; la; lb] = conjuncts ant in
  let hyp = mk_conj(`NPACK c1 c2 a b l`, mk_conj(la, lb)) in
  let h = ASSUME hyp in
  let r = MP th2 (end_itlist CONJ [l1; ab; CONJUNCT1 (CONJUNCT2 h); CONJUNCT2 (CONJUNCT2 h)]) in
  GENL vars (DISCH hyp (PROVE_HYP (CONJUNCT1 h) r));;
