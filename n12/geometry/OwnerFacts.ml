(* ========================================================================= *)
(* Phase 2: Compact/Bridge/C1092WallSymmetry/OwnerFacts.lean.                *)
(* Finite exact-owner identities of the C1092 family (namespace FiniteFacts). *)
(* Transform.markerAction g j (S12/TransformFacts) is c1092wsf_marker_action *)
(* g j with the S12 marker permutations permX / permY / permSwap as HOL      *)
(* lists (Marker = Fin 16: j < 16);  maskSupport m is bitset m;  the Lean    *)
(* candidateMasks list is the Phase-1 CANDMASKS (same list);  ownerCode i   *)
(* is EL i c1092wc_code and ownerAction is c1092ws_owner_action (Actions.ml). *)
(* ========================================================================= *)

needs "n12/geometry/Actions.ml";;

(* |- !k. k < n <=> k = n-1 \/ ... \/ k = 0, by the LT recursion (no arithmetic case explosion) *)
let C1092WSF_LT_CASES =
  let tbl = Hashtbl.create 20 in
  fun n ->
    try Hashtbl.find tbl n with Not_found ->
    let k = `k:num` in
    let rec go m =
      if m = 0 then SPEC k (CONJUNCT1 LT) else
      let th1 = AP_TERM (mk_comb(`(<):num->num->bool`, k)) (num_CONV (mk_small_numeral m)) in
      let th2 = SPECL [k; mk_small_numeral (m - 1)] (CONJUNCT2 LT) in
      let th3 = TRANS th1 th2 in
      CONV_RULE (RAND_CONV (RAND_CONV (K (go (m - 1))))) th3 in
    let th = GEN k (REWRITE_RULE[] (go n)) in
    Hashtbl.add tbl n th; th;;

(* case split on a bounded index v < n (an assumption) *)
let C1092WSF_ENUM_TAC v n =
  let lt = mk_binop `(<):num->num->bool` v (mk_small_numeral n) in
  FIRST_ASSUM(fun th -> if concl th = lt then MP_TAC(EQ_MP (SPEC v (C1092WSF_LT_CASES n)) th) else NO_TAC) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC);;

(* Lean: S12.permX, S12.permY, S12.permSwap *)
let c1092wsf_permX = new_definition
 `c1092wsf_permX = [2;3;0;1;6;7;4;5;9;8;11;10;14;13;12;15]`;;
let c1092wsf_permY = new_definition
 `c1092wsf_permY = [6;7;4;5;2;3;0;1;11;10;9;8;12;15;14;13]`;;
let c1092wsf_permSwap = new_definition
 `c1092wsf_permSwap = [1;0;7;6;5;4;3;2;8;11;10;9;13;12;15;14]`;;

(* Lean: S12.Transform.markerAction *)
let c1092wsf_marker_action = new_definition
 `c1092wsf_marker_action (g:bool#bool#bool) (i:num) =
    let j = if FST g then EL i c1092wsf_permSwap else i in
    let k = if SND (SND g) then EL j c1092wsf_permY else j in
    if FST (SND g) then EL k c1092wsf_permX else k`;;

let C1092WSF_LOOKUPS =
  List.concat (map (fun th -> Array.to_list (el_lookups th))
    [c1092wsf_permX; c1092wsf_permY; c1092wsf_permSwap]) @ C1092WS_LOOKUPS;;

let C1092WSF_BITSETS =
  map bitset_bits [3;12;48;192;256;512;1024;2048;4096;8192;16384;32768];;

(* one evaluation conversion (rewrite net built once) *)
let C1092WSF_EVAL_CONV =
  let rw = REWRITE_CONV([c1092ws_owner_action; c1092wsf_marker_action; LET_DEF; LET_END_DEF] @
                        C1092WSF_LOOKUPS @ C1092WSF_BITSETS @ [IN_SET_OF_LIST; MEM]) in
  rw THENC NUM_REDUCE_CONV THENC REWRITE_CONV[];;

(* Lean: FiniteFacts.owner_marker_transport *)
let C1092WSF_OWNER_MARKER_TRANSPORT = prove
 (`forall a b c i j. i < 12 /\ j < 16
     ==> (c1092wsf_marker_action (a,b,c) j IN bitset (EL (c1092ws_owner_action (a,b,c) i) c1092wc_code) <=>
          j IN bitset (EL i c1092wc_code))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  C1092WSF_ENUM_TAC `i:num` 12 THEN C1092WSF_ENUM_TAC `j:num` 16 THEN
  MAP_EVERY BOOL_CASES_TAC [`a:bool`; `b:bool`; `c:bool`] THEN
  CONV_TAC C1092WSF_EVAL_CONV);;

(* Lean: FiniteFacts.owner_code_candidate *)
let C1092WSF_OWNER_CODE_CANDIDATE = prove
 (`forall i. i < 12 ==> MEM (EL i c1092wc_code) CANDMASKS`,
  GEN_TAC THEN DISCH_TAC THEN C1092WSF_ENUM_TAC `i:num` 12 THEN
  REWRITE_TAC C1092WC_LISTS THEN REWRITE_TAC[CANDMASKS; MEM] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: FiniteFacts.family_enumerated *)
let C1092WSF_FAMILY_ENUMERATED = prove
 (`forall m. m IN c1092wc_family ==> exists i. i < 12 /\ EL i c1092wc_code = m`,
  REWRITE_TAC[c1092wc_family; IN_INSERT; NOT_IN_EMPTY] THEN GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  FIRST (map (fun k -> EXISTS_TAC (mk_small_numeral k) THEN REWRITE_TAC C1092WC_LISTS THEN
                       CONV_TAC NUM_REDUCE_CONV THEN NO_TAC) (0--11)));;
