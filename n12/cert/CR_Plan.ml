(* ========================================================================= *)
(* Certificate layer, part 3 (F2): complement split, blocked-target plans    *)
(* and pair stages.                                                          *)
(* Lean: Compact/Core/BlockedTarget.lean (Hint, Hint.Check, Hint.sound,      *)
(*       Independent, source_sound, Check, sound),                           *)
(*       Compact/Bridge/IndexedBlockedTarget.lean (Plan, Plan.Check,         *)
(*       Plan.sound, TargetsIn, Stage, Stage.Check, Stage.BlockOverlap,      *)
(*       Stage.step_sound), Cases/C713/Assembly.lean (PairTransition).       *)
(* ========================================================================= *)

needs "n12/cert/CR_Farkas.ml";;

(* Lean: BlockedTarget.Hint  (impossible: EmptyContext.Witness inputs terms) *)
let cbhint_INDUCT,cbhint_RECURSION = define_type
  "cbhint = BhDirect crhint | BhBlock (crhint list) | BhImpossible (num list) ((int#num) list)";;

(* Lean: BlockedTarget.Hint.Check (violation rows = opposite target :: inputs) *)
let cr_bhint_check = define
 `(cr_bhint_check (BhDirect h) inputs block t <=> cr_hint_check h inputs t) /\
  (cr_bhint_check (BhBlock hs) inputs block t <=>
     cr_hints_check (CONS (cr_opposite t) inputs) block hs) /\
  (cr_bhint_check (BhImpossible ins terms) inputs block t <=>
     cr_empty_check (CONS (cr_opposite t) inputs) ins terms)`;;

(* Lean: BlockedTarget.Hint.Independent *)
let cr_bhint_indep = define
 `(cr_bhint_indep (BhDirect h) <=> true) /\
  (cr_bhint_indep (BhBlock hs) <=> false) /\
  (cr_bhint_indep (BhImpossible ins terms) <=> true)`;;

let CR_VIOLATION_HOLDS = prove
 (`forall inputs t px py.
     (forall r. MEM r inputs ==> cr_holds r px py) /\ ~cr_holds t px py
     ==> forall r. MEM r (CONS (cr_opposite t) inputs) ==> cr_holds r px py`,
  REWRITE_TAC[MEM] THEN MESON_TAC[CR_OPPOSITE_HOLDS]);;

(* Lean: BlockedTarget.Hint.sound *)
let CR_BHINT_SOUND = prove
 (`forall h inputs block t px py.
     cr_bhint_check h inputs block t /\ (forall r. MEM r inputs ==> cr_holds r px py) /\
     ~(forall r. MEM r block ==> cr_holds r px py)
     ==> cr_holds t px py`,
  MATCH_MP_TAC cbhint_INDUCT THEN REWRITE_TAC[cr_bhint_check] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[CR_HINT_SOUND];
    ASM_MESON_TAC[CR_HINTS_SOUND; CR_VIOLATION_HOLDS];
    ASM_MESON_TAC[CR_EMPTY_SOUND; CR_VIOLATION_HOLDS; CR_ROWAT_HOLDS]]);;

(* Lean: BlockedTarget.Hint.source_sound *)
let CR_BHINT_SOURCE_SOUND = prove
 (`forall h inputs block t px py.
     cr_bhint_check h inputs block t /\ cr_bhint_indep h /\
     (forall r. MEM r inputs ==> cr_holds r px py)
     ==> cr_holds t px py`,
  MATCH_MP_TAC cbhint_INDUCT THEN REWRITE_TAC[cr_bhint_check; cr_bhint_indep] THEN
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[CR_HINT_SOUND];
    ASM_MESON_TAC[CR_EMPTY_SOUND; CR_VIOLATION_HOLDS; CR_ROWAT_HOLDS]]);;

(* Lean: BlockedTarget.Check *)
let cr_bt_check = define
 `(cr_bt_check inputs block [] [] <=> true) /\
  (cr_bt_check inputs block [] (CONS (h:cbhint) hs) <=> false) /\
  (cr_bt_check inputs block (CONS t ts) [] <=> false) /\
  (cr_bt_check inputs block (CONS t ts) (CONS h hs) <=>
     cr_bhint_check h inputs block t /\ cr_bt_check inputs block ts hs)`;;

(* Lean: BlockedTarget.sound *)
let CR_BT_SOUND = prove
 (`forall inputs block targets hints px py.
     cr_bt_check inputs block targets hints /\ (forall r. MEM r inputs ==> cr_holds r px py) /\
     ~(forall r. MEM r block ==> cr_holds r px py)
     ==> forall t. MEM t targets ==> cr_holds t px py`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[cr_bt_check] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[CR_BHINT_SOUND]);;

(* Lean: BlockedTarget.source_sound *)
let CR_BT_SOURCE_SOUND = prove
 (`forall inputs block targets hints px py.
     cr_bt_check inputs block targets hints /\ ALL cr_bhint_indep hints /\
     (forall r. MEM r inputs ==> cr_holds r px py)
     ==> forall t. MEM t targets ==> cr_holds t px py`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[cr_bt_check; ALL] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[CR_BHINT_SOURCE_SOUND]);;

(* ------------------------------------------------------------------------- *)
(* Plans (Lean: IndexedBlockedTarget.Plan; the materialized inputs, blocked  *)
(* and outputs lists are not stored: they are the rows of the source pose,  *)
(* the block rows and the rows of the target pose).                          *)
(* ------------------------------------------------------------------------- *)

let cplan_INDUCT,cplan_RECURSION = define_type
  "cplan = CPlan cpose ((crow list)option) (cpose option) (cbhint list)";;

let cpl_source = define `cpl_source (CPlan s b t h) = s`;;
let cpl_block = define `cpl_block (CPlan s b t h) = b`;;
let cpl_target = define `cpl_target (CPlan s b t h) = t`;;
let cpl_hints = define `cpl_hints (CPlan s b t h) = h`;;
(* Lean: Plan.header *)
let cpl_header = new_definition `cpl_header p = (cpl_source p, cpl_block p)`;;

(* block.getD [] ; block = none ; block = some [] *)
let cr_blk_rows = define `(cr_blk_rows NONE = []) /\ (cr_blk_rows (SOME (l:crow list)) = l)`;;
let cr_blk_none = define `(cr_blk_none NONE <=> true) /\ (cr_blk_none (SOME (l:crow list)) <=> false)`;;
let cr_blk_empty = define
 `(cr_blk_empty NONE <=> false) /\ (cr_blk_empty (SOME (l:crow list)) <=> NULL l)`;;

(* Lean: Plan.Check *)
let cr_plan_check = define
 `(cr_plan_check (CPlan src blk NONE hs) <=> cr_blk_empty blk) /\
  (cr_plan_check (CPlan src blk (SOME tgt) hs) <=>
     cp_angle src = cp_angle tgt /\
     cr_bt_check (cp_rows src) (cr_blk_rows blk) (cp_rows tgt) hs /\
     (cr_blk_none blk ==> ALL cr_bhint_indep hs))`;;

let CR_NULL_EQ = prove
 (`forall l:A list. NULL l <=> l = []`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; NOT_CONS_NIL]);;

let CR_PLAN_CHECK_LEAN = prove
 (`forall src blk t hs. cr_plan_check (CPlan src blk t hs) <=>
     (t = NONE /\ blk = SOME []) \/
     (exists tgt. t = SOME tgt /\ cp_angle src = cp_angle tgt /\
            cr_bt_check (cp_rows src) (cr_blk_rows blk) (cp_rows tgt) hs /\
            (blk = NONE ==> ALL cr_bhint_indep hs))`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `t:cpose option` (cases "option")) THEN
  STRUCT_CASES_TAC(ISPEC `blk:(crow list)option` (cases "option")) THEN
  REWRITE_TAC[cr_plan_check; cr_blk_empty; cr_blk_none; cr_blk_rows;
              distinctness "option"; injectivity "option"; UNWIND_THM1] THEN
  REWRITE_TAC[CR_NULL_EQ]);;


(* Lean: IndexedBlockedTarget.Plan.sound *)
let CR_PLAN_SOUND = prove
 (`forall p c s u v a.
     cr_plan_check p /\ oriented_realizes (cr_leaf (cpl_source p)) c s u v a /\
     (forall blk. cpl_block p = SOME blk ==>
            ~(forall r. MEM r blk ==> cr_holds r (lcx c s u v a) (lcy c s u v a)))
     ==> exists t. cpl_target p = SOME t /\ oriented_realizes (cr_leaf t) c s u v a`,
  MATCH_MP_TAC cplan_INDUCT THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `a2:cpose option` (cases "option")) THEN
  STRUCT_CASES_TAC(ISPEC `a1:(crow list)option` (cases "option")) THEN
  REWRITE_TAC[cr_plan_check; cpl_source; cpl_block; cpl_target; cr_blk_empty; cr_blk_none;
              cr_blk_rows; distinctness "option"; injectivity "option"; UNWIND_THM1] THEN
  REPEAT GEN_TAC THENL
   [REWRITE_TAC[CR_NULL_EQ] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `[]:crow list`) THEN ASM_REWRITE_TAC[MEM];
    STRIP_TAC THEN MATCH_MP_TAC CR_TRANSFER THEN
    ASM_MESON_TAC[CR_BT_SOURCE_SOUND; CR_REALIZES_ROWS];
    STRIP_TAC THEN MATCH_MP_TAC CR_TRANSFER THEN
    ASM_MESON_TAC[CR_BT_SOUND; CR_REALIZES_ROWS]]);;

(* ------------------------------------------------------------------------- *)
(* Stages                                                                    *)
(* ------------------------------------------------------------------------- *)

(* Lean: C713Assembly.PairTransition (and the CK_DirectPruning analogues);   *)
(* the OpenSquare invariants are explicit hypotheses.                        *)
let cr_pair_transition = new_definition
 `cr_pair_transition (Sd:pose_leaf list) (Nd:pose_leaf list) (Td:pose_leaf list) <=>
    forall cq sq uq vq aq ct st ut vt aT.
      cq * cq + sq * sq = &1 /\ &0 < aq /\ ct * ct + st * st = &1 /\ &0 < aT /\
      oriented_pose_covered Sd cq sq uq vq aq /\
      oriented_pose_covered Nd ct st ut vt aT /\
      ldisj cq sq uq vq aq ct st ut vt aT
      ==> oriented_pose_covered Td cq sq uq vq aq`;;

(* Lean: IndexedBlockedTarget.Stage.BlockOverlap  (headers = plans.map header) *)
let cr_block_overlap = new_definition
 `cr_block_overlap (headers:(cpose#(crow list)option)list) (Nd:pose_leaf list) <=>
    forall src blk. MEM (src, SOME blk) headers ==>
      forall cq sq uq vq aq ct st ut vt aT.
        cq * cq + sq * sq = &1 /\ &0 < aq /\ ct * ct + st * st = &1 /\ &0 < aT /\
        oriented_realizes (cr_leaf src) cq sq uq vq aq /\
        oriented_pose_covered Nd ct st ut vt aT /\
        (forall r. MEM r blk ==> cr_holds r (lcx cq sq uq vq aq) (lcy cq sq uq vq aq))
        ==> exists x y. linside cq sq uq vq aq x y /\ linside ct st ut vt aT x y`;;

(* Lean: Stage.Check  (plans.map source = sources, TargetsIn, all plans checked) *)
let cr_stage_ok = new_definition
 `cr_stage_ok (Sd:cpose list) (Td:cpose list) plans <=>
    MAP cpl_source plans = Sd /\
    (forall p t. MEM p plans /\ cpl_target p = SOME t ==> MEM t Td) /\
    (forall p. MEM p plans ==> cr_plan_check p)`;;

(* Lean: Stage.step_sound *)
let CR_STAGE_SOUND = prove
 (`forall Sd Nd Td plans.
     cr_stage_ok Sd Td plans /\ cr_block_overlap (MAP cpl_header plans) Nd
     ==> cr_pair_transition (MAP cr_leaf Sd) Nd (MAP cr_leaf Td)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cr_stage_ok; cr_block_overlap; cr_pair_transition] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `oriented_pose_covered (MAP cr_leaf Sd) cq sq uq vq aq` THEN
  REWRITE_TAC[oriented_pose_covered; MEM_MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:pose_leaf` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `src:cpose` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `exists p. MEM p plans /\ cpl_source p = src` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `MEM (src:cpose) Sd` THEN EXPAND_TAC "Sd" THEN
    REWRITE_TAC[MEM_MAP] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`p:cplan`; `cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`]
    CR_PLAN_SOUND) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN X_GEN_TAC `blk:crow list` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`src:cpose`; `blk:crow list`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `p:cplan` THEN
      ASM_REWRITE_TAC[cpl_header; PAIR_EQ]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`;
                                `ct:real`; `st:real`; `ut:real`; `vt:real`; `aT:real`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ldisj]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:cpose` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `cr_leaf t` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `t:cpose` THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Assembly helpers for stage theorems (used by CR_HistStages.ml).           *)
(* ------------------------------------------------------------------------- *)

let cr_plan_ok = new_definition
 `cr_plan_ok (Td:cpose list) p <=>
    cr_plan_check p /\ (forall t. cpl_target p = SOME t ==> MEM t Td)`;;

let CR_ALL_NIL = prove (`forall P:A->bool. ALL P []`, REWRITE_TAC[ALL]);;
let CR_ALL_CONS = prove
 (`forall P (h:A) t. P h /\ ALL P t ==> ALL P (CONS h t)`, REWRITE_TAC[ALL]);;
let CR_MEM_HEAD = prove (`forall (x:A) t. MEM x (CONS x t)`, REWRITE_TAC[MEM]);;
let CR_MEM_TAIL = prove
 (`forall (x:A) h t. MEM x t ==> MEM x (CONS h t)`, SIMP_TAC[MEM]);;

let CR_TGT_NONE = prove
 (`forall Td src blk hs. forall t. cpl_target (CPlan src blk NONE hs) = SOME t ==> MEM t Td`,
  REWRITE_TAC[cpl_target; distinctness "option"]);;

let CR_TGT_SOME = prove
 (`forall Td src blk tgt hs. MEM tgt Td ==>
     forall t. cpl_target (CPlan src blk (SOME tgt) hs) = SOME t ==> MEM t Td`,
  REWRITE_TAC[cpl_target; injectivity "option"] THEN MESON_TAC[]);;

let CR_PLAN_OK_INTRO = prove
 (`forall Td p. cr_plan_check p /\ (forall t. cpl_target p = SOME t ==> MEM t Td) ==> cr_plan_ok Td p`,
  REWRITE_TAC[cr_plan_ok]);;

let CR_STAGE_OK_INTRO = prove
 (`forall Sd Td plans. MAP cpl_source plans = Sd /\ ALL (cr_plan_ok Td) plans
     ==> cr_stage_ok Sd Td plans`,
  REWRITE_TAC[cr_stage_ok; GSYM ALL_MEM; cr_plan_ok] THEN MESON_TAC[]);;

(* The stage theorem with the header list and the pose lists abstracted.    *)
let CR_STAGE_THM = prove
 (`forall Sd Nd Td plans hdrs.
     cr_stage_ok Sd Td plans /\ MAP cpl_header plans = hdrs
     ==> cr_block_overlap hdrs Nd
     ==> cr_pair_transition (MAP cr_leaf Sd) Nd (MAP cr_leaf Td)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_MESON_TAC[CR_STAGE_SOUND]);;

(* ------------------------------------------------------------------------- *)
(* For the overlap provers (design §4.2): pairwise overlap obligations.      *)
(* Lean: IndexedCommonGroups.PairOverlaps (header realizes = pose realizes + *)
(* block rows hold at the centre).                                           *)
(* ------------------------------------------------------------------------- *)

let cr_pair_overlaps = new_definition
 `cr_pair_overlaps src (blk:crow list) n <=>
    forall cq sq uq vq aq ct st ut vt aT.
      cq * cq + sq * sq = &1 /\ &0 < aq /\ ct * ct + st * st = &1 /\ &0 < aT /\
      pose_realizes (cr_leaf src) cq sq uq vq aq /\
      (forall r. MEM r blk ==> cr_holds r (lcx cq sq uq vq aq) (lcy cq sq uq vq aq)) /\
      pose_realizes (cr_leaf n) ct st ut vt aT
      ==> exists x y. linside cq sq uq vq aq x y /\ linside ct st ut vt aT x y`;;

let CR_BLOCK_OVERLAP_OF_PAIRS = prove
 (`forall hdrs Nd.
     (forall src blk n. MEM (src, SOME blk) hdrs /\ MEM n Nd ==> cr_pair_overlaps src blk n)
     ==> cr_block_overlap hdrs (MAP cr_leaf Nd)`,
  REWRITE_TAC[cr_block_overlap; cr_pair_overlaps; oriented_pose_covered; MEM_MAP;
              oriented_realizes] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`src:cpose`; `blk:crow list`; `x:cpose`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* F2, first-failing-row split (Lean: PairPruning.outsidePieces, on rows    *)
(* instead of dictionary indices; complement = cr_opposite).                 *)
(* ------------------------------------------------------------------------- *)

let cr_outside_pieces = define
 `(cr_outside_pieces [] (inputs:crow list) = []) /\
  (cr_outside_pieces (CONS r rest) inputs =
     CONS (CONS (cr_opposite r) inputs) (cr_outside_pieces rest (CONS r inputs)))`;;

(* Lean: PairPruning.outsidePieces_sound *)
let CR_OUTSIDE_PIECES_SOUND = prove
 (`forall block inputs px py.
     (forall r. MEM r inputs ==> cr_holds r px py) /\ ~(forall r. MEM r block ==> cr_holds r px py)
     ==> exists piece. MEM piece (cr_outside_pieces block inputs) /\
                 forall r. MEM r piece ==> cr_holds r px py`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; cr_outside_pieces] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `cr_holds h px py` THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (h:crow) inputs`; `px:real`; `py:real`]) THEN
    ANTS_TAC THENL [REWRITE_TAC[MEM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN MESON_TAC[];
    EXISTS_TAC `CONS (cr_opposite h) inputs` THEN REWRITE_TAC[MEM] THEN
    ASM_MESON_TAC[CR_OPPOSITE_HOLDS]]);;

(* ------------------------------------------------------------------------- *)
(* Relaxation links (Lean: Bridge/RelaxationTable.lean, used by C898).      *)
(* ------------------------------------------------------------------------- *)

(* Lean: RelaxationTable.Entry.Check *)
let cr_relax_check = new_definition
 `cr_relax_check src tgt hints <=>
    cp_angle src = cp_angle tgt /\ cr_hints_check (cp_rows src) (cp_rows tgt) hints`;;

(* Lean: RelaxationTable.Entry.sound *)
let CR_RELAX_SOUND = prove
 (`forall src tgt hints c s u v a.
     cr_relax_check src tgt hints /\ oriented_realizes (cr_leaf src) c s u v a
     ==> oriented_realizes (cr_leaf tgt) c s u v a`,
  REWRITE_TAC[cr_relax_check] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CR_TRANSFER THEN
  EXISTS_TAC `src:cpose` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CR_HINTS_SOUND THEN
  MAP_EVERY EXISTS_TAC [`cp_rows src`; `hints:crhint list`] THEN
  ASM_MESON_TAC[CR_REALIZES_ROWS]);;

(* Lean: RelaxationTable.cover_sound  (links = (source, target, hints) triples) *)
let CR_RELAX_COVER_SOUND = prove
 (`forall Sd Td links c s u v a.
     (forall src. MEM src Sd ==> exists l. MEM l links /\ FST l = src /\ MEM (FST (SND l)) Td) /\
     (forall l. MEM l links ==> cr_relax_check (FST l) (FST (SND l)) (SND (SND l))) /\
     oriented_pose_covered (MAP cr_leaf Sd) c s u v a
     ==> oriented_pose_covered (MAP cr_leaf Td) c s u v a`,
  REWRITE_TAC[oriented_pose_covered; MEM_MAP] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:cpose`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:cpose#cpose#crhint list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `cr_leaf (FST (SND (l:cpose#cpose#crhint list)))` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; MATCH_MP_TAC CR_RELAX_SOUND] THEN
  ASM_MESON_TAC[]);;
