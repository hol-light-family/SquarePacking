(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/MergedPending/NegativeUpperFaces    *)
(* (namespace N12Compact.MergedPending.NegativeUpperFaces).  Exact faces of *)
(* the negative upper-merged frame in coordinates centred at (2,2).         *)
(* Normal / normal_bounds: c977cc_normal / C977CC_NORMAL_BOUNDS.            *)
(* A square H is c s u v a with c * c + s * s = &1 and &0 < a.              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

(* Lean: Input (structure) *)
let ocmpnuf_input = new_definition
 `ocmpnuf_input (c:real) s u v a <=>
    c977cc_normal c (--s) /\ &1 < a /\
    linside c s u v a (--(&7 / &20)) (&7 / &20) /\
    linside c s u v a (&7 / &20) (&7 / &20) /\
    ~linside c s u v a (--(&13 / &50)) (&0) /\
    ~linside c s u v a (--(&13 / &50)) (&1) /\
    ~linside c s u v a (&0) (&543 / &500)`;;

let OCMPNUF_SETUP_TAC =
  REPEAT GEN_TAC THEN REWRITE_TAC[ocmpnuf_input] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th ->
    is_conj(concl th) && not(can (find_term ((=) `linside`)) (concl th)))));;

(* linear arithmetic keeping only the omitted points whose x-coordinate is in keep *)
let OCMPNUF_LIN_TAC_KEEP keep =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_neg t && can (find_term ((=) `linside`)) t &&
       not (mem (rand(rator(rand t))) keep) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

(* Lean: lower_v *)
let OCMPNUF_LOWER_V = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ ocmpnuf_input c s u v a
               ==> &13 / &50 * s <= v`,
  OCMPNUF_SETUP_TAC THEN (OCMPNUF_LIN_TAC_KEEP [`--(&13 / &50)`]));;

(* Lean: lower_u *)
let OCMPNUF_LOWER_U = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ ocmpnuf_input c s u v a
               ==> --(&13 / &50) * c + s <= u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL OCMPNUF_LOWER_V) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `ocmpnuf_input c s u v a` THEN OCMPNUF_SETUP_TAC THEN (OCMPNUF_LIN_TAC_KEEP [`--(&13 / &50)`]));;

(* Lean: tilt *)
let OCMPNUF_TILT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ ocmpnuf_input c s u v a
               ==> &9 * c < --(&65) * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL OCMPNUF_LOWER_U) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `ocmpnuf_input c s u v a` THEN OCMPNUF_SETUP_TAC THEN (OCMPNUF_LIN_TAC_KEEP []));;

(* Lean: top_marker_faces *)
let OCMPNUF_TOP_MARKER_FACES = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ ocmpnuf_input c s u v a
               ==> &543 / &500 * s <= u \/ v + a <= &543 / &500 * c`,
  OCMPNUF_SETUP_TAC THEN (OCMPNUF_LIN_TAC_KEEP [`&0`]));;

(* Lean: top_lower_tilt *)
let OCMPNUF_TOP_LOWER_TILT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ ocmpnuf_input c s u v a /\
               &543 / &500 * s <= u
               ==> &175 * c < --(&368) * s`,
  OCMPNUF_SETUP_TAC THEN (OCMPNUF_LIN_TAC_KEEP []));;

(* Lean: sharp_point *)
let OCMPNUF_SHARP_POINT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ ocmpnuf_input c s u v a /\
               &543 / &500 * s <= u /\
               &9 * c <= --(&35) * s /\
               &525 * c - &961 * s <= &1000
               ==> linside c s u v a (&21 / &40) (&1 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL OCMPNUF_LOWER_V) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `ocmpnuf_input c s u v a` THEN OCMPNUF_SETUP_TAC THEN (OCMPNUF_LIN_TAC_KEEP []));;
