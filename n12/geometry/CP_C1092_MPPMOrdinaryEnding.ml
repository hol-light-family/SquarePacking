(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMOrdinaryEnding.lean                  *)
(* (N12Compact.C1092MPPMOrdinaryCycle; Lean header: "Source only, without    *)
(* compiler or replay acceptance").  The complete ordinary windmill ending.  *)
(* Conventions of CP_C1092_MPPMOrdinaryCycleData.ml: Frames p d is           *)
(* c1092mocd_frames c1 c2 a b l cc cs cu cv ca, Positive d i is `&0 < cs i`, *)
(* Retains p i is c1092mocd_retains c1 c2 a b l i; d.rotated hf i is the     *)
(* family (\j. cc (c1092mar_addSector i j)) .. over the packing              *)
(* (d1,d2,e1,e2) = pk (EL i rotation) p (C1092MOCD_FRAMES_ROTATED).          *)
(* FourCycle.classify C1092MFCS_CLASSIFY; AllNonpositive.impossible          *)
(* C1092ANPA_IMPOSSIBLE; ActualPositiveCycle.impossible C1092MAAP_IMPOSSIBLE.*)
(* Tag C1092MOEN_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMOrdinaryCycleData.ml";;
needs "n12/geometry/CP_C1092_MPPMFourCycleStates.ml";;
needs "n12/geometry/CP_C1092_MPPMAllNonpositiveActual.ml";;
needs "n12/geometry/CP_C1092_MPPMActualAllPositive.ml";;

let C1092MOEN_CORE = Printf.sprintf "%s /\\ %s" C1092MOCD_HYPS C1092MOCD_FR;;

(* a signed-cycle rule of OrdinaryCycleData at the literal sector i *)
let c1092moen_inst th i =
  CONV_RULE(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MOD_CONV ORELSEC NUM_LT_CONV))
    (PURE_REWRITE_RULE[c1092mar_addSector] (SPECL (C1092MOCD_V @ C1092MOCD_F4 @ [mk_small_numeral i]) th));;
let c1092moen_use th i =
  MP_TAC(c1092moen_inst th i) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC];;
let c1092moen_ret i = Printf.sprintf "c1092mocd_retains c1 c2 a b l %d" i;;
let c1092moen_case i = ASM_CASES_TAC (parse_term (c1092moen_ret i));;

(* Lean: one_positive *)
let C1092MOEN_ONE_POSITIVE = prove
 (parse_term (Printf.sprintf "forall %s cc cs cu cv ca. %s /\\ &0 < cs 0 /\\ ~(&0 < cs 1) /\\ ~(&0 < cs 2) /\\
      ~(&0 < cs 3) ==> false" C1092AE_P C1092MOEN_CORE),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092moen_use C1092MOCD_SIGNED_EDGE 3 THEN
  c1092moen_case 1 THEN c1092moen_case 2 THENL
   [c1092moen_use C1092MOCD_THREE_RETAINING 1;
    c1092moen_use C1092MOCD_MISSING_BEFORE_POSITIVE 3;
    c1092moen_use C1092MOCD_MISSING_BEFORE_RETAINING 2;
    c1092moen_use C1092MOCD_ADJACENT_MISSING 1]);;

(* Lean: sandwich *)
let C1092MOEN_SANDWICH = prove
 (parse_term (Printf.sprintf "forall %s cc cs cu cv ca. %s /\\ &0 < cs 0 /\\ ~(&0 < cs 1) /\\ &0 < cs 2 ==> false"
    C1092AE_P C1092MOEN_CORE),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092moen_use C1092MOCD_SIGNED_EDGE 1 THEN
  c1092moen_use C1092MOCD_POSITIVE_SANDWICH 1);;

(* Lean: adjacent_positive *)
let C1092MOEN_ADJACENT_POSITIVE = prove
 (parse_term (Printf.sprintf "forall %s cc cs cu cv ca. %s /\\ &0 < cs 0 /\\ &0 < cs 1 /\\ ~(&0 < cs 2) /\\
      ~(&0 < cs 3) ==> false" C1092AE_P C1092MOEN_CORE),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092moen_use C1092MOCD_SIGNED_EDGE 3 THEN
  c1092moen_case 2 THENL
   [c1092moen_use C1092MOCD_POSITIVE_BEFORE_RETAINING 2;
    c1092moen_use C1092MOCD_MISSING_BEFORE_POSITIVE 3]);;

let C1092MOEN_ZERO = prove
 (`forall i. i < 4 ==> c1092mar_addSector i 0 = i`,
  SIMP_TAC[c1092mar_addSector; ADD_CLAUSES; MOD_LT]);;

(* apply a literal-sector ending to the rotated frames at sector i *)
let c1092moen_rot_tac th =
  FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mfcs_onePositive; c1092mfcs_sandwich; c1092mfcs_adjacentPositive]) THEN
  c1092mapc_choose_tac (c1092mapc_el `i:num`) C1092MOCD_V4 C1092MOCD_D THEN
  c1092mapc_facts_tac C1092MOCD_V4 C1092MOCD_D `i:num` THEN
  MP_TAC(SPECL (C1092MOCD_V @ C1092MOCD_F4 @ [`i:num`] @ C1092MOCD_D) C1092MOCD_FRAMES_ROTATED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC (SPECL (C1092MANH_D5 @
    map (fun f -> mk_abs(`j:num`, mk_comb(f, `c1092mar_addSector i j`))) C1092MOCD_F4) th) THEN
  ASM_SIMP_TAC[C1092MOEN_ZERO];;

(* Lean: impossible_of_frames *)
let C1092MOEN_IMPOSSIBLE_OF_FRAMES = prove
 (parse_term (Printf.sprintf "forall %s cc cs cu cv ca. %s ==> false" C1092AE_P C1092MOEN_CORE),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\i:num. &0 < cs i` C1092MFCS_CLASSIFY) THEN BETA_TAC THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [(* all nonpositive *)
    MATCH_MP_TAC (SPECL (C1092MOCD_V @ C1092MOCD_F4) C1092ANPA_IMPOSSIBLE) THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[c1092mfcs_allNonpositive]) THEN BETA_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mocd_frames] o check (c1092mpapo_head `c1092mocd_frames`)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (SPECL (C1092MOCD_V @ C1092MOCD_F4) C1092MOCD_FRAMES_NONPOSITIVE_NORMAL) THEN
    ASM_SIMP_TAC[];
    (* all positive *)
    MATCH_MP_TAC (SPECL C1092MOCD_V C1092MAAP_IMPOSSIBLE) THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[c1092mfcs_allPositive]) THEN BETA_TAC THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[c1092mapc_positiveFrames] THEN
    MAP_EVERY X_GEN_TAC (`i:num` :: C1092MOCD_D) THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC (c1092macr_at `i:num`) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mocd_frames] o check (c1092mpapo_head `c1092mocd_frames`)) THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC (SPECL (C1092MOCD_V @ C1092MOCD_F4) C1092MOCD_FRAMES_POSITIVE_NORMAL) THEN
    ASM_SIMP_TAC[];
    c1092moen_rot_tac C1092MOEN_ONE_POSITIVE;
    c1092moen_rot_tac C1092MOEN_SANDWICH;
    c1092moen_rot_tac C1092MOEN_ADJACENT_POSITIVE]);;

(* Lean: impossible *)
let C1092MOEN_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "forall %s. %s ==> false" C1092AE_P C1092MOCD_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C1092MOCD_FRAMES_EXISTS o check (fun th -> concl th = `NPACK c1 c2 a b l`)) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC C1092MOCD_F4 THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MOCD_V @ C1092MOCD_F4) C1092MOEN_IMPOSSIBLE_OF_FRAMES) THEN
  ASM_REWRITE_TAC[]);;
