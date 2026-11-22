(* ========================================================================= *)
(* Phase 2: Compact/Cases/C981.lean (namespace N12Compact.Case981).          *)
(* Original-model C981 completion boundary: the routing lists, the           *)
(* obligation structure and its soundness (completion of every slot closes   *)
(* ExcludesCase 981 = excl_case 981).  Obligations is a conjunction of its   *)
(* fields; i : Fin 117 is i < 117; RepresentativeExcluded i is               *)
(* c981vd_excludes_vector (EL i c981vd_representative_vectors).              *)
(* This is a conditional reduction (no case closer).                         *)
(* ========================================================================= *)

needs "n12/geometry/VectorData.ml";;

(* Lean: remainingIndices *)
let c981c_remaining_indices = new_definition
 `c981c_remaining_indices =
   [0;1;2;3;4;7;8;19;20;21;24;26;28;29;30;34;37;39;41;43;44;45;46;47;
    49;50;51;52;53;56;59;67;68;69;71;72;73;75;76;77;78;79;93;96;103;104;
    105;107;108;109;111;112;113;114;115]`;;

(* Lean: flatPairWall *)
let c981c_flat_pair_wall = new_definition
 `c981c_flat_pair_wall =
   [44;45;46;47;49;52;56;67;68;72;73;75;76;77;78;79;93;96;109;111;112;113;114;115]`;;

(* Lean: terminalStrip, stripBorder, kernelWithoutRefinement, angleRefinement, centerSplit *)
let c981c_terminal_strip = new_definition `c981c_terminal_strip = [108]`;;
let c981c_strip_border = new_definition `c981c_strip_border = [7]`;;
let c981c_kernel_without_refinement = new_definition `c981c_kernel_without_refinement = [8; 69]`;;
let c981c_angle_refinement = new_definition
 `c981c_angle_refinement =
   [0;1;2;3;4;19;20;21;24;26;28;29;30;34;37;39;41;43;53;59;71;103;104;105;107]`;;
let c981c_center_split = new_definition `c981c_center_split = [50; 51]`;;

(* Lean: remaining_count *)
let C981C_REMAINING_COUNT = prove
 (`LENGTH c981c_remaining_indices = 55`,
  REWRITE_TAC[c981c_remaining_indices; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: routes_cover *)
let C981C_ROUTES_COVER = prove
 (`forall i. i < 117 /\ MEM i c981c_remaining_indices ==>
       MEM i c981c_flat_pair_wall \/ MEM i c981c_terminal_strip \/ MEM i c981c_strip_border \/
       MEM i c981c_kernel_without_refinement \/ MEM i c981c_angle_refinement \/
       MEM i c981c_center_split`,
  GEN_TAC THEN REWRITE_TAC[c981c_remaining_indices; MEM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[c981c_flat_pair_wall; c981c_terminal_strip; c981c_strip_border;
                  c981c_kernel_without_refinement; c981c_angle_refinement; c981c_center_split; MEM] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* Lean: RepresentativeExcluded *)
let c981c_representative_excluded = new_definition
 `c981c_representative_excluded i <=>
    c981vd_excludes_vector (EL i c981vd_representative_vectors)`;;

(* Lean: CatalogueCoverage *)
let c981c_catalogue_coverage = new_definition
 `c981c_catalogue_coverage <=>
    forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc981ri_family
      ==> exists d1 d2 da db dl. NPACK d1 d2 da db dl /\
                           IMAGE binarysum (FFP d1 d2 da db dl) = ccc981ri_family /\
                           exists i. i < 117 /\
                               c981ow_vector d1 d2 da db dl = EL i c981vd_representative_vectors`;;

(* Lean: Obligations (structure; the conjunction of its fields
   coverage, formerlyConnected, flat, strip, border, kernel, refined, split) *)
let c981c_obligations = new_definition
 `c981c_obligations <=>
    c981c_catalogue_coverage /\
    (forall i. i < 117 /\ ~MEM i c981c_remaining_indices ==> c981c_representative_excluded i) /\
    (forall i. i < 117 /\ MEM i c981c_flat_pair_wall ==> c981c_representative_excluded i) /\
    (forall i. i < 117 /\ MEM i c981c_terminal_strip ==> c981c_representative_excluded i) /\
    (forall i. i < 117 /\ MEM i c981c_strip_border ==> c981c_representative_excluded i) /\
    (forall i. i < 117 /\ MEM i c981c_kernel_without_refinement ==> c981c_representative_excluded i) /\
    (forall i. i < 117 /\ MEM i c981c_angle_refinement ==> c981c_representative_excluded i) /\
    (forall i. i < 117 /\ MEM i c981c_center_split ==> c981c_representative_excluded i)`;;

(* Lean: Obligations.all *)
let C981C_OBLIGATIONS_ALL = prove
 (`c981c_obligations ==> forall i. i < 117 ==> c981c_representative_excluded i`,
  REWRITE_TAC[c981c_obligations] THEN STRIP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `MEM (i:num) c981c_remaining_indices` THENL
   [MP_TAC(SPEC `i:num` C981C_ROUTES_COVER) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* Lean: catalogue_indexed *)
let C981C_CATALOGUE_INDEXED = prove
 (`c981vd_representative_vectors =
   list_of_seq (\i. EL i c981vd_representative_vectors) 117`,
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM (CONJUNCT1 C981VD_REPRESENTATIVE_VECTORS_LENGTH)] THEN
  REWRITE_TAC[LIST_OF_SEQ_EQ_SELF]);;

(* Lean: excluded_of_obligations *)
let C981C_EXCLUDED_OF_OBLIGATIONS = prove
 (`c981c_obligations ==> excl_case 981`,
  DISCH_TAC THEN REWRITE_TAC[CCC981RI_EXCLUDES_CASE_IFF; excl_fam] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C981C_OBLIGATIONS_ALL) THEN
  UNDISCH_TAC `c981c_obligations` THEN REWRITE_TAC[c981c_obligations; c981c_catalogue_coverage] THEN
  DISCH_THEN(MP_TAC o SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
  ASM_REWRITE_TAC[c981c_representative_excluded; c981vd_excludes_vector] THEN
  DISCH_THEN(MP_TAC o SPECL [`d1:num->real`; `d2:num->real`; `da:num->real`; `db:num->real`; `dl:real`]) THEN
  ASM_REWRITE_TAC[]);;
