(* ========================================================================= *)
(* Port of Compact/Cases/C1092Compact.lean (N12Compact.C1092Compact; Lean    *)
(* header: "All new source still awaits compiler acceptance").  The retained *)
(* C1092 obligation with all four actual whole-packing branches supplied.    *)
(* BranchEnding k = c1092wsy_ending k, FourBranchEndings = c1092wsy_four,    *)
(* excludes_original C1092WSY_EXCLUDES_ORIGINAL; branch endings              *)
(* C1092MPPMW_WINDMILL (MPPM.windmill), C1092MTFE_BRANCH_ENDING             *)
(* (MMMPTwoFifthsEntrance.branch_ending), C1092MM_ADJACENT_PAIR              *)
(* (MMMM.adjacentPair), C1092OP_OPPOSITE_PAIR (OppositePair.oppositePair).   *)
(* The Lean structure Pending (three fields with closed defaults) is the     *)
(* predicate c1092cc_pending.  RowIdentity: ri_lookup / ri_excludes_case.    *)
(* Tag C1092CC_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/C1092WallSymmetry.ml";;
needs "n12/geometry/CP_C1092_OppositePair.ml";;
needs "n12/geometry/CP_C1092_MMMM.ml";;
needs "n12/geometry/CP_C1092_MMMP_TwoFifthsEntrance.ml";;
needs "n12/geometry/CP_C1092_MPPM.ml";;
needs "n12/geometry/RowIdentity.ml";;

(* Lean: Pending (structure) *)
let c1092cc_pending = new_definition
 `c1092cc_pending <=> c1092wsy_ending 0 /\ c1092wsy_ending 1 /\ c1092wsy_ending 2`;;

(* Lean: all_branches *)
let C1092CC_ALL_BRANCHES = prove
 (`c1092cc_pending ==> c1092wsy_four`,
  REWRITE_TAC[c1092cc_pending; c1092wsy_four] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[C1092OP_OPPOSITE_PAIR]);;

(* Lean: pending_closed *)
let C1092CC_PENDING_CLOSED = prove
 (`c1092cc_pending`,
  REWRITE_TAC[c1092cc_pending; C1092MPPMW_WINDMILL; C1092MTFE_BRANCH_ENDING; C1092MM_ADJACENT_PAIR]);;

(* Lean: row_checked (private) *)
let C1092CC_ROW_CHECKED = ri_lookup 576 `c1092wc_family`;;

(* Lean: excludes_case *)
let C1092CC_EXCLUDES_CASE = prove
 (`c1092cc_pending ==> excl_case 1092`,
  DISCH_TAC THEN MATCH_MP_TAC (ri_excludes_case 576 `c1092wc_family`) THEN
  PURE_REWRITE_TAC[excl_fam] THEN MATCH_MP_TAC C1092WSY_EXCLUDES_ORIGINAL THEN
  MATCH_MP_TAC C1092CC_ALL_BRANCHES THEN ASM_REWRITE_TAC[]);;

(* Lean: excludes_case_complete *)
let C1092CC_EXCLUDES_CASE_COMPLETE = MP C1092CC_EXCLUDES_CASE C1092CC_PENDING_CLOSED;;

(* the assembly form (retained row 576 has id 1092) *)
let C1092CC_EXCLUDED_ROW = ri_excluded_row 576 C1092CC_EXCLUDES_CASE_COMPLETE;;
