(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMPositiveSector.lean                  *)
(* (N12Compact.C1092MPPMPositiveSector; Lean header: "makes no compiler-     *)
(* acceptance claim").  Preferred original-owner joins for the positive      *)
(* ordinary MPPM sector.  Conventions of CP_C1092_MPPMPositiveSeedsActual.ml *)
(* (ActualFrame p C is c1092psa_frame; Faces is c1092mmpf_faces; Normal is   *)
(* c977cc_normal; C1092WallProfileScalars.half is C1092WPS_half) and         *)
(* CP_C1092_MPPMOmissions.ml (Missing is c1092mom_missing).  The joined      *)
(* producers are the C1092PSA_ theorems, ordinary_walls C1092MOM_ORDINARY_   *)
(* WALLS and bottom_far_no_omission C1092OWA_BOTTOM_FAR_NO_OMISSION.         *)
(* Tag C1092MPS_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMPositiveSeedsActual.ml";;
needs "n12/geometry/CP_C1092_MPPMOrdinaryWallAdvance.ml";;

let C1092MPS_EMPTY = "(!k. k < 4 ==> ~c1092mom_missing c1 c2 a b l k)";;
let C1092MPS_SUCC = c1092psa_in 5 "&113 / &50" "&1";;
let c1092mps_stmt hyps concl =
  c1092psa_stmt C1092PSA_VARS_C ([C1092AE_HYP; C1092MPPE_CTX; C1092MPS_EMPTY] @ hyps) concl;;
let C1092MPS_TAC ths =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MOM_ORDINARY_WALLS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  TRY(MP_TAC(SPEC_ALL C1092OWA_BOTTOM_FAR_NO_OMISSION) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
  let one = FIRST (map (fun th -> MP_TAC(SPEC_ALL th) THEN ASM_REWRITE_TAC[] THEN NO_TAC) ths) in
  (one ORELSE (REPEAT CONJ_TAC THEN one));;

(* Lean: missing_points_and_faces *)
let C1092MPS_MISSING_POINTS_AND_FACES = prove
 (c1092mps_stmt [C1092PSA_P; C1092PSA_G; C1092MPS_SUCC; C1092PSA_MISSING; C1092PSA_SQ; C1092PSA_FRAME;
                 "c977cc_normal cC sC"]
    (c1092psa_in 4 "&1" "&3 / &2" ^ " /\\ " ^ c1092psa_in 9 "&2" "&1" ^
     " /\\ c1092mmpf_faces cC sC uC vC aC"),
  C1092MPS_TAC [C1092PSA_MISSING_HALFPOINT; C1092PSA_BOTTOM_ORIGIN_OF_MISSING; C1092PSA_MISSING_PROFILE]);;

(* Lean: missing_crosspoint_of_ceiling *)
let C1092MPS_MISSING_CROSSPOINT_OF_CEILING = prove
 (c1092mps_stmt [C1092PSA_P; C1092PSA_G; C1092MPS_SUCC; C1092PSA_MISSING; C1092PSA_SQ; C1092PSA_FRAME;
                 "c977cc_normal cC sC"; "C1092WPS_half cC sC <= &1 / &3"]
    (c1092psa_in 4 "&3 / &2" "&2"),
  C1092MPS_TAC [C1092PSA_MISSING_CROSSPOINT]);;

(* Lean: forward_crosspoint_of_previous_exclusion *)
let C1092MPS_FORWARD_CROSSPOINT_OF_PREVIOUS_EXCLUSION = prove
 (c1092mps_stmt [C1092PSA_P; C1092PSA_G; C1092MPS_SUCC; C1092PSA_FORWARD; C1092PSA_PREVIOUS;
                 C1092PSA_SQ; C1092PSA_FRAME; "c977cc_normal cC sC"]
    (c1092psa_in 4 "&3 / &2" "&2"),
  C1092MPS_TAC [C1092PSA_FORWARD_CROSSPOINT]);;

(* Lean: retaining_points_of_next_crosspoint *)
let C1092MPS_RETAINING_POINTS_OF_NEXT_CROSSPOINT = prove
 (c1092mps_stmt [C1092PSA_P; C1092PSA_G; C1092PSA_FORWARD; C1092PSA_PREVIOUS; C1092PSA_NEXT;
                 C1092PSA_SQ; C1092PSA_FRAME; "c977cc_normal cC sC"; "&0 < sC";
                 "C1092WPS_half cC sC <= &1 / &3"]
    ("uC + aC <= --sC / &2 /\\ ~" ^ c1092psa_in 4 "&2" "&87 / &50" ^ " /\\ " ^
     c1092psa_in 4 "&1" "&3 / &2" ^ " /\\ " ^ c1092psa_in 9 "&2" "&1"),
  C1092MPS_TAC [C1092PSA_FORWARD_HALFPOINT_AND_ORIGIN]);;
