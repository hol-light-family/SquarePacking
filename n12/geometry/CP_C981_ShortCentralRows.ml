(* ========================================================================= *)
(* Port of Compact/Completion/C981/ShortCentralRows.lean                     *)
(* (namespace N12Compact.C981CompletionShortCentralRows).  Original rows 93  *)
(* and 98 ("Source candidate").  q : Fin 12 -> OpenSquare is the five        *)
(* functions qc qs qu qv qa (unit normals explicit); insidePoints /          *)
(* outsidePoints are c981scr_insidePoints / c981scr_outsidePoints; the       *)
(* geometry toolkit and the excludes producer are those of                   *)
(* CP_C981_OutwardRows.ml (the c981or_ functions).  pullSwap is LINSIDE_PULLSW / *)
(* LCONT_PULLSW; swapFrame A is (cA, --sA, vA, uA, aA)                       *)
(* (C981SCR_INSIDE_SWAPFRAME); ClosedFrames.canonical_frame =                *)
(* CLF_CANONICAL_FRAME; CentralWallCenter.point / right_high = CWC_POINT /   *)
(* CWC_RIGHT_HIGH; C981CompletionCrosspoint.point = C981CP_POINT;            *)
(* C981CompletionWallAdvance.point = C981WA_POINT;                           *)
(* C981CompletionShortCentralPair.impossible = C981SCP_IMPOSSIBLE;           *)
(* inside_segment = OO_VERTICAL_SEGMENT.  Tag C981SCR_.                      *)
(* ========================================================================= *)

needs "n12/geometry/CP_C981_OutwardRows.ml";;
needs "n12/geometry/CP_C981_ShortCentralPair.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/CentralWallCenter.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: insidePoints *)
let c981scr_insidePoints = new_definition
 `c981scr_insidePoints : ((real#real)list)list =
    [[(&187 / &100, &19 / &25)]; [(&19 / &25, &187 / &100)]; [(&3, &1)]; []; [(&1, &3)];
     [(&47 / &20, &33 / &20); (&3, &8 / &5)];
     [(&47 / &20, &47 / &20); (&2, &113 / &50); (&113 / &50, &2)];
     [(&33 / &20, &47 / &20); (&8 / &5, &3)];
     [(&457 / &500, &2); (&1, &12 / &5); (&1, &113 / &50)];
     [(&2, &457 / &500); (&12 / &5, &1); (&113 / &50, &1)];
     [(&1543 / &500, &2); (&3, &12 / &5)];
     [(&2, &1543 / &500); (&12 / &5, &3)]]`;;

(* Lean: outsidePoints *)
let c981scr_outsidePoints = new_definition
 `c981scr_outsidePoints : ((real#real)list)list =
    [[]; []; []; []; []; []; []; []; [(&1, &87 / &50)]; [(&87 / &50, &1)];
     [(&3, &87 / &50)]; [(&87 / &50, &3)]]`;;

(* Lean: wall_segment (private) *)
let C981SCR_WALL_SEGMENT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&457 / &500) (&2) /\ linside c s u v a (&1) (&12 / &5) /\
     linside c s u v a (&1) (&113 / &50) /\
     ~linside c s u v a (&1) (&87 / &50) /\
     ~linside c s u v a (&19 / &25) (&187 / &100) /\
     ~linside c s u v a (&33 / &20) (&47 / &20)
     ==> forall z. &113 / &50 <= z /\ z <= &273 / &100 ==> linside c s u v a (&1) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C981WA_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&113 / &50`; `&14 / &5`] THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: swapFrame, swapFrame_c, swapFrame_s, swapFrame_side, inside_swapFrame (private) *)
let C981SCR_INSIDE_SWAPFRAME = prove
 (`forall c s u v a x y. linside c (--s) v u a x y <=> linside c s u v a y x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let C981SCR_HSAME = `forall i j. i < 12 /\ j < 12 ==> (qa:num->real) i = qa j`;;

let c981scr_same i j =
  MP (SPECL [mk_small_numeral i; mk_small_numeral j] (ASSUME C981SCR_HSAME))
     (CONJ (c981or_lt i) (c981or_lt j));;

(* Lean: geometry *)
let C981SCR_GEOMETRY = prove
 (list_mk_forall([`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`],
   mk_imp(list_mk_conj [C981OR_HUNIT; C981OR_HSIDE; C981SCR_HSAME; C981OR_HBOX;
                        c981or_hpts false `c981scr_insidePoints`;
                        c981or_hpts true `c981scr_outsidePoints`; C981OR_HAPART], `false`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let pin = c981or_pt false `c981scr_insidePoints` c981scr_insidePoints
  and pout = c981or_pt true `c981scr_outsidePoints` c981scr_outsidePoints in
  let fr = c981or_foreign in
  let sw i = let [c; s; u; v; a] = c981or_q i in
    [s; c; u; mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, v)) a; a] in
  let unitsw i = MATCH_MP (REAL_ARITH `x + y = &1 ==> y + x = &1`) (c981or_unit i) in
  let cMarker = pin 6 (`&47 / &20`, `&47 / &20`) and cNorth = pin 6 (`&2`, `&113 / &50`)
  and cEast = pin 6 (`&113 / &50`, `&2`) and seMarker = pin 5 (`&47 / &20`, `&33 / &20`)
  and nwMarker = pin 7 (`&33 / &20`, `&47 / &20`) and rMarker = pin 10 (`&1543 / &500`, `&2`)
  and rHigh = pin 10 (`&3`, `&12 / &5`) and rMissing = pout 10 (`&3`, `&87 / &50`)
  and tMarker = pin 11 (`&2`, `&1543 / &500`) and tHigh = pin 11 (`&12 / &5`, `&3`)
  and tMissing = pout 11 (`&87 / &50`, `&3`) in
  let center = c981or_apply CWC_POINT (c981or_q 6 @ c981or_q 10 @ c981or_q 11)
    [c981or_unit 6; c981or_unit 10; c981or_unit 11; c981or_side 6; c981or_side 10; c981or_side 11;
     c981scr_same 6 10; c981scr_same 6 11; c981or_box 10; c981or_box 11;
     cNorth; cEast; cMarker; fr 6 5 seMarker; fr 6 7 nwMarker;
     rMarker; rHigh; rMissing; tMarker; tHigh; tMissing;
     REWRITE_RULE[GSYM ldisj] (c981or_apart 6 10); REWRITE_RULE[GSYM ldisj] (c981or_apart 6 11)] in
  let rFar = c981or_apply CWC_RIGHT_HIGH (c981or_q 10)
    [c981or_unit 10; c981or_side 10; c981or_box 10; rMarker; rHigh; rMissing; fr 10 6 cEast] in
  let tFar = c981or_apply CWC_RIGHT_HIGH (sw 11)
    [unitsw 11; c981or_side 11; c981or_box 11; tMarker; tHigh; tMissing; fr 11 6 cNorth] in
  let north = c981or_apply C981CP_POINT (c981or_q 6)
    [c981or_unit 6; c981or_side 6; cNorth; cEast; cMarker; fr 6 5 seMarker; fr 6 7 nwMarker;
     fr 6 10 rHigh; fr 6 10 rFar] in
  let east = c981or_apply C981CP_POINT (sw 6)
    [unitsw 6; c981or_side 6; cNorth; cEast; cMarker; fr 6 5 seMarker; fr 6 7 nwMarker;
     fr 6 11 tHigh; fr 6 11 tFar] in
  let leftSegment = c981or_apply C981SCR_WALL_SEGMENT (c981or_q 8)
    [c981or_unit 8; c981or_side 8; c981or_box 8;
     pin 8 (`&457 / &500`, `&2`); pin 8 (`&1`, `&12 / &5`); pin 8 (`&1`, `&113 / &50`);
     pout 8 (`&1`, `&87 / &50`); fr 8 1 (pin 1 (`&19 / &25`, `&187 / &100`)); fr 8 7 nwMarker] in
  let bottomSegment = c981or_apply C981SCR_WALL_SEGMENT (sw 9)
    [unitsw 9; c981or_side 9; c981or_box 9;
     pin 9 (`&2`, `&457 / &500`); pin 9 (`&12 / &5`, `&1`); pin 9 (`&113 / &50`, `&1`);
     pout 9 (`&87 / &50`, `&1`); fr 9 0 (pin 0 (`&187 / &100`, `&19 / &25`)); fr 9 5 seMarker] in
  let seg_excl i j segth =
    (* !z. lo <= z /\ z <= hi ==> ~linside (q i) at the segment point of (q j) *)
    let z = `z:real` in
    let inst = UNDISCH (SPEC z segth) in
    GEN z (DISCH (lhand(concl(SPEC z segth))) (fr i j inst)) in
  let facts = [center; north; east; cMarker; cEast; cNorth; seMarker; nwMarker; rMarker; tMarker;
               fr 6 7 nwMarker; fr 6 5 seMarker;
               pin 5 (`&3`, `&8 / &5`); fr 5 2 (pin 2 (`&3`, `&1`)); fr 5 10 rMarker; fr 5 6 cEast;
               fr 5 9 (pin 9 (`&12 / &5`, `&1`)); seg_excl 5 9 bottomSegment;
               pin 7 (`&8 / &5`, `&3`); fr 7 4 (pin 4 (`&1`, `&3`)); fr 7 11 tMarker; fr 7 6 cNorth;
               fr 7 8 (pin 8 (`&1`, `&12 / &5`)); seg_excl 7 8 leftSegment;
               c981or_apart 6 5; c981or_apart 6 7;
               c981or_side 6; c981scr_same 6 5; c981scr_same 6 7;
               c981or_unit 5; c981or_unit 7; unitsw 7; c981or_unit 6] in
  let close =
    REWRITE_TAC[ldisj; C981SCR_INSIDE_SWAPFRAME; LINSIDE_PULLSW] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST [FIRST (map ACCEPT_TAC facts);
           REPEAT GEN_TAC THEN FIRST (map MATCH_ACCEPT_TAC facts);
           MP_TAC (c981or_side 6) THEN MP_TAC (c981scr_same 6 5) THEN MP_TAC (c981scr_same 6 7) THEN
           REWRITE_TAC[REAL_ABS_NEG] THEN ASM_REAL_ARITH_TAC] in
  MP_TAC(SPECL (c981or_q 6) CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [REWRITE_TAC[c981or_unit 6] THEN MP_TAC (c981or_side 6) THEN REAL_ARITH_TAC;
                  ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cA:real` (X_CHOOSE_THEN `sA:real` (X_CHOOSE_THEN `uA:real`
    (X_CHOOSE_THEN `vA:real` (X_CHOOSE_THEN `aA:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA = (qa:num->real) 6`)) THEN
  ASM_CASES_TAC `sA <= &0` THENL
   [MATCH_MP_TAC(SPECL ([`cA:real`; `sA:real`; `uA:real`; `vA:real`; `(qa:num->real) 6`] @ c981or_q 5)
      C981SCP_IMPOSSIBLE) THEN close;
    MATCH_MP_TAC(SPECL ([`cA:real`; `--sA`; `vA:real`; `uA:real`; `(qa:num->real) 6`] @ sw 7)
      C981SCP_IMPOSSIBLE) THEN close]);;

(* Lean: Check, excludes *)
let c981scr_inside_list =
  [0, [(`&187 / &100`, `&19 / &25`)]; 1, [(`&19 / &25`, `&187 / &100`)]; 2, [(`&3`, `&1`)];
   4, [(`&1`, `&3`)]; 5, [(`&47 / &20`, `&33 / &20`); (`&3`, `&8 / &5`)];
   6, [(`&47 / &20`, `&47 / &20`); (`&2`, `&113 / &50`); (`&113 / &50`, `&2`)];
   7, [(`&33 / &20`, `&47 / &20`); (`&8 / &5`, `&3`)];
   8, [(`&457 / &500`, `&2`); (`&1`, `&12 / &5`); (`&1`, `&113 / &50`)];
   9, [(`&2`, `&457 / &500`); (`&12 / &5`, `&1`); (`&113 / &50`, `&1`)];
   10, [(`&1543 / &500`, `&2`); (`&3`, `&12 / &5`)];
   11, [(`&2`, `&1543 / &500`); (`&12 / &5`, `&3`)]];;
let c981scr_outside_list =
  [8, [(`&1`, `&87 / &50`)]; 9, [(`&87 / &50`, `&1`)];
   10, [(`&3`, `&87 / &50`)]; 11, [(`&87 / &50`, `&3`)]];;

let c981scr_excludes vtm =
  c981or_excludes_with C981SCR_GEOMETRY
    c981scr_inside_list c981scr_insidePoints c981scr_outside_list c981scr_outsidePoints
    [REPEAT GEN_TAC THEN DISCH_TAC THEN REFL_TAC] vtm;;

(* Lean: coveredIds *)
let c981scr_coveredIds = new_definition
 `c981scr_coveredIds = [93; 98]`;;

(* Lean: checked *)
let C981SCR_CHECKED = map (fun i -> c981br_rep_excluded i c981scr_excludes) [93; 98];;

(* Lean: covered_excluded *)
let C981SCR_COVERED_EXCLUDED =
  REWRITE_RULE[GSYM c981scr_coveredIds] (c981br_covered [93; 98] C981SCR_CHECKED);;
