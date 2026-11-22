(* ========================================================================= *)
(* Port of Compact/Geometry/ABTransverse.lean (N12Compact.ABTransverse).     *)
(* Two compulsory triangles rule out both longitudinal separating axes of A *)
(* and B; the remaining alternatives are transverse face inequalities.      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CongruentSAT.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;

(* Lean: upper *)
let ABT_upper = new_definition
 `ABT_upper (c:real) s u v a nx ny =
    nx * lcx c s u v a + ny * lcy c s u v a + tss_support_radius c s a nx ny`;;

(* Lean: lower *)
let ABT_lower = new_definition
 `ABT_lower (c:real) s u v a nx ny =
    nx * lcx c s u v a + ny * lcy c s u v a - tss_support_radius c s a nx ny`;;

(* Lean: closed_bounds *)
let ABT_CLOSED_BOUNDS = prove
 (`forall c s u v a x y nx ny.
     c * c + s * s = &1 /\ &0 < a /\ lclosed c s u v a x y
     ==> ABT_lower c s u v a nx ny <= nx * x + ny * y /\
         nx * x + ny * y <= ABT_upper c s u v a nx ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `x:real`; `y:real`;
                `nx:real`; `ny:real`] TSS_CLOSED_SUPPORT) THEN
  ASM_REWRITE_TAC[ABT_upper; ABT_lower] THEN REAL_ARITH_TAC);;

(* Lean: strict_bounds *)
let ABT_STRICT_BOUNDS = prove
 (`forall c s u v a x y nx ny.
     c * c + s * s = &1 /\ &0 < a /\ nx pow 2 + ny pow 2 = &1 /\ linside c s u v a x y
     ==> ABT_lower c s u v a nx ny < nx * x + ny * y /\
         nx * x + ny * y < ABT_upper c s u v a nx ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `abs(nx * (x - lcx c s u v a) + ny * (y - lcy c s u v a)) <
    tss_support_radius c s a nx ny`
  MP_TAC THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `linside c s u v a x y` THEN
    REWRITE_TAC[linside; tss_support_radius] THEN
    SPEC_TAC(`lcx c s u v a`,`X:real`) THEN SPEC_TAC(`lcy c s u v a`,`Y:real`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN
     `abs(c * (x - X) + s * (y - Y)) < a / &2 /\
      abs(--s * (x - X) + c * (y - Y)) < a / &2`
    MP_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `nx * (x - X) + ny * (y - Y) =
      (nx * c + ny * s) * (c * (x - X) + s * (y - Y)) +
      (--nx * s + ny * c) * (--s * (x - X) + c * (y - Y))` SUBST1_TAC THENL
     [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `(nx * c + ny * s) pow 2 + (--nx * s + ny * c) pow 2 = &1` MP_TAC THENL
     [UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `nx pow 2 + ny pow 2 = &1` THEN
      CONV_TAC REAL_RING; ALL_TAC] THEN
    SPEC_TAC(`c * (x - X) + s * (y - Y)`,`U:real`) THEN
    SPEC_TAC(`--s * (x - X) + c * (y - Y)`,`V:real`) THEN
    SPEC_TAC(`nx * c + ny * s`,`A:real`) THEN
    SPEC_TAC(`--nx * s + ny * c`,`B:real`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `abs A * abs U + abs B * abs V` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_ABS_TRIANGLE]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < abs A \/ &0 < abs B` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_ABS_NZ] THEN
      ASM_CASES_TAC `A = &0` THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `(A:real) pow 2 + B pow 2 = &1` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= abs A /\ &0 <= abs B` MP_TAC THENL
     [REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
    UNDISCH_TAC `abs U < a / &2 /\ abs V < a / &2` THEN
    SPEC_TAC(`abs A`,`p:real`) THEN SPEC_TAC(`abs B`,`q:real`) THEN
    SPEC_TAC(`abs U`,`m:real`) THEN SPEC_TAC(`abs V`,`k:real`) THEN
    REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN NLIN_TAC [];
    REWRITE_TAC[ABT_upper; ABT_lower] THEN REAL_ARITH_TAC]);;

(* Lean: ownU *)
let ABT_OWNU = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a
     ==> ABT_lower c s u v a c s = u /\ ABT_upper c s u v a c s = u + a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[ABT_upper; ABT_lower; tss_support_radius;
    REAL_ARITH `--c * s + s * c = &0`] THEN
  REAL_ARITH_TAC);;

(* Lean: ownV *)
let ABT_OWNV = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a
     ==> ABT_lower c s u v a (--s) c = v /\ ABT_upper c s u v a (--s) c = v + a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[ABT_upper; ABT_lower; tss_support_radius;
    REAL_ARITH `--s * c + c * s = &0`;
    REAL_ARITH `-- --s * s + c * c = c * c + s * s`] THEN
  REAL_ARITH_TAC);;

(* Lean: separated *)
let ABT_SEPARATED = prove
 (`forall cq sq uq vq aq cr sr ur vr ar nx ny.
     tss_support_radius cq sq aq nx ny + tss_support_radius cr sr ar nx ny <=
       abs(nx * (lcx cr sr ur vr ar - lcx cq sq uq vq aq) +
           ny * (lcy cr sr ur vr ar - lcy cq sq uq vq aq))
     ==> ABT_upper cq sq uq vq aq nx ny <= ABT_lower cr sr ur vr ar nx ny \/
         ABT_upper cr sr ur vr ar nx ny <= ABT_lower cq sq uq vq aq nx ny`,
  REWRITE_TAC[ABT_upper; ABT_lower] THEN REAL_ARITH_TAC);;

(* Lean: parallel_radius *)
let ABT_PARALLEL_RADIUS = prove
 (`forall cq sq aq cr sr ar. cq * cq + sq * sq = &1
     ==> tss_support_radius cq sq aq cq sq + tss_support_radius cr sr ar cq sq =
         C977CB_pairRadius cq sq aq cr sr ar`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[tss_support_radius; C977CB_pairRadius;
    REAL_ARITH `--cq * sq + sq * cq = &0`;
    REAL_ARITH `abs(--cq * sr + sq * cr) = abs(cq * sr - sq * cr)`] THEN
  REAL_ARITH_TAC);;

(* Lean: transverse_radius *)
let ABT_TRANSVERSE_RADIUS = prove
 (`forall cq sq aq cr sr ar. cq * cq + sq * sq = &1
     ==> tss_support_radius cq sq aq (--sq) cq + tss_support_radius cr sr ar (--sq) cq =
         C977CB_pairRadius cq sq aq cr sr ar`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[tss_support_radius; C977CB_pairRadius;
    REAL_ARITH `--sq * cq + cq * sq = &0`;
    REAL_ARITH `abs(--sq * cr + cq * sr) = abs(cq * sr - sq * cr)`;
    REAL_ARITH `abs(-- --sq * sr + cq * cr) = abs(cq * cr + sq * sr)`;
    REAL_ARITH `-- --sq * sq + cq * cq = cq * cq + sq * sq`] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: alternatives *)
let ABT_ALTERNATIVES = prove
 (`forall cA sA uA vA aA cB sB uB vB aB.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &0 < cA /\ &0 <= sA /\ &0 < cB /\ &0 < sB /\
     aA = aB /\
     lclosed cA sA uA vA aA (&2) (&113 / &50) /\
     lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     lclosed cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&2) (&1543 / &500) /\
     ldisj cA sA uA vA aA cB sB uB vB aB
     ==> ABT_upper cA sA uA vA aA (--sB) cB <= vB \/
         vA + aA <= ABT_lower cB sB uB vB aB (--sA) cA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = aB`)) THEN
  SUBGOAL_THEN `cA pow 2 + sA pow 2 = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `lclosed cB sB uB vB aB (&2) (&1543 / &500)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LINSIDE_CLOSED]; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[C977CB_faceSep] THEN
  STRIP_TAC THENL
   [(* A's longitudinal axis *)
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ABT_SEPARATED o
      REWRITE_RULE[GSYM(MP (SPECL [`cA:real`; `sA:real`; `aB:real`; `cB:real`; `sB:real`; `aB:real`] ABT_PARALLEL_RADIUS) (ASSUME `cA * cA + sA * sA = &1`))]) THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
      `&47 / &20`; `&47 / &20`; `cA:real`; `sA:real`] ABT_CLOSED_BOUNDS) THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
      `&33 / &20`; `&47 / &20`; `cA:real`; `sA:real`] ABT_CLOSED_BOUNDS) THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
      `&2`; `&113 / &50`; `cA:real`; `sA:real`] ABT_CLOSED_BOUNDS) THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
      `&2`; `&1543 / &500`; `cA:real`; `sA:real`] ABT_STRICT_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
    (* A's transverse axis *)
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ABT_SEPARATED o
      REWRITE_RULE[GSYM(MP (SPECL [`cA:real`; `sA:real`; `aB:real`; `cB:real`; `sB:real`; `aB:real`] ABT_TRANSVERSE_RADIUS) (ASSUME `cA * cA + sA * sA = &1`))]) THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
      `&113 / &50`; `&2`; `--sA`; `cA:real`] ABT_CLOSED_BOUNDS) THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
      `&2`; `&1543 / &500`; `--sA`; `cA:real`] ABT_CLOSED_BOUNDS) THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`] ABT_OWNV) THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
    (* B's longitudinal axis *)
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ABT_SEPARATED o
      REWRITE_RULE[GSYM(ONCE_REWRITE_RULE[REAL_ADD_SYM] (MP (SPECL [`cB:real`; `sB:real`; `aB:real`; `cA:real`; `sA:real`; `aB:real`] ABT_PARALLEL_RADIUS) (ASSUME `cB * cB + sB * sB = &1`)))]) THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
      `&47 / &20`; `&47 / &20`; `cB:real`; `sB:real`] ABT_CLOSED_BOUNDS) THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
      `&33 / &20`; `&47 / &20`; `cB:real`; `sB:real`] ABT_CLOSED_BOUNDS) THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
      `&2`; `&113 / &50`; `cB:real`; `sB:real`] ABT_CLOSED_BOUNDS) THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
      `&2`; `&1543 / &500`; `cB:real`; `sB:real`] ABT_CLOSED_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
    (* B's transverse axis *)
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ABT_SEPARATED o
      REWRITE_RULE[GSYM(ONCE_REWRITE_RULE[REAL_ADD_SYM] (MP (SPECL [`cB:real`; `sB:real`; `aB:real`; `cA:real`; `sA:real`; `aB:real`] ABT_TRANSVERSE_RADIUS) (ASSUME `cB * cB + sB * sB = &1`)))]) THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
      `&113 / &50`; `&2`; `--sB`; `cB:real`] ABT_CLOSED_BOUNDS) THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
      `&2`; `&1543 / &500`; `--sB`; `cB:real`] ABT_CLOSED_BOUNDS) THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] ABT_OWNV) THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Helpers shared by the files importing ABTransverse (no Lean counterpart). *)
(* ------------------------------------------------------------------------- *)

(* the four separated alternatives of two disjoint congruent squares *)
let ABT_FOUR_AXES = prove
 (`forall cq sq uq vq aq cr sr ur vr ar.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ cr * cr + sr * sr = &1 /\ &0 < ar /\
     aq = ar /\ ldisj cq sq uq vq aq cr sr ur vr ar
     ==> (ABT_upper cq sq uq vq aq cq sq <= ABT_lower cr sr ur vr ar cq sq \/
          ABT_upper cr sr ur vr ar cq sq <= ABT_lower cq sq uq vq aq cq sq) \/
         (ABT_upper cq sq uq vq aq (--sq) cq <= ABT_lower cr sr ur vr ar (--sq) cq \/
          ABT_upper cr sr ur vr ar (--sq) cq <= ABT_lower cq sq uq vq aq (--sq) cq) \/
         (ABT_upper cq sq uq vq aq cr sr <= ABT_lower cr sr ur vr ar cr sr \/
          ABT_upper cr sr ur vr ar cr sr <= ABT_lower cq sq uq vq aq cr sr) \/
         (ABT_upper cq sq uq vq aq (--sr) cr <= ABT_lower cr sr ur vr ar (--sr) cr \/
          ABT_upper cr sr ur vr ar (--sr) cr <= ABT_lower cq sq uq vq aq (--sr) cr)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`;
                `cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`]
    CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[C977CB_faceSep] THEN
  let rad name q r swap =
    let th = MP (SPECL [mk_var("c"^q,`:real`); mk_var("s"^q,`:real`); mk_var("a"^q,`:real`);
                        mk_var("c"^r,`:real`); mk_var("s"^r,`:real`); mk_var("a"^r,`:real`)] name)
                (ASSUME (subst [mk_var("c"^q,`:real`),`c:real`; mk_var("s"^q,`:real`),`s:real`]
                         `c * c + s * s = &1`)) in
    GSYM(if swap then ONCE_REWRITE_RULE[REAL_ADD_SYM] th else th) in
  let fin r = FIRST_X_ASSUM(MP_TAC o MATCH_MP ABT_SEPARATED o REWRITE_RULE[r]) THEN
              MESON_TAC[] in
  REPEAT STRIP_TAC THENL
   [fin (rad ABT_PARALLEL_RADIUS "q" "r" false);
    fin (rad ABT_TRANSVERSE_RADIUS "q" "r" false);
    fin (rad ABT_PARALLEL_RADIUS "r" "q" true);
    fin (rad ABT_TRANSVERSE_RADIUS "r" "q" true)]);;

(* REAL_ARITH with the (conjunctions of) real-relation assumptions *)
let ABT_ARITH_TAC (asl,w as g) =
  let hs = filter (fun th -> let t = concl th in
                     is_real_rel t || (is_neg t && is_real_rel (rand t)))
                  (flat (map (CONJUNCTS o snd) asl)) in
  (if hs = [] then REAL_ARITH_TAC else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

let ABT_BOUNDS_TAC th sq x y nx ny =
  MP_TAC(SPECL (sq @ [x; y; nx; ny]) th) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN ABT_ARITH_TAC;
    STRIP_TAC];;

(* strict / closed bounds of square sq = [c;s;u;v;a] at (x,y) in direction (nx,ny) *)
let ABT_SB_TAC = ABT_BOUNDS_TAC ABT_STRICT_BOUNDS;;
let ABT_CB_TAC = ABT_BOUNDS_TAC ABT_CLOSED_BOUNDS;;

(* strict bounds for every listed (square, point) in every listed direction *)
let ABT_ALL_SB_TAC sqpts dirs =
  MAP_EVERY (fun (sq,(x,y)) ->
    MAP_EVERY (fun (nx,ny) -> ABT_SB_TAC sq x y nx ny) dirs) sqpts;;

let ABT_ALL_CB_TAC sqpts dirs =
  MAP_EVERY (fun (sq,(x,y)) ->
    MAP_EVERY (fun (nx,ny) -> ABT_CB_TAC sq x y nx ny) dirs) sqpts;;

(* ownU / ownV of square sq as assumptions *)
let ABT_OWN_TAC sq =
  MP_TAC(SPECL sq ABT_OWNU) THEN MP_TAC(SPECL sq ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC;;

(* Standard proof of a two-square SAT reduction: squares named q and r      *)
(* (variables cq sq uq vq aq, ...), hypothesis aq = ar; pts lists the       *)
(* owned points (name, (x,y)); all four face directions are used.           *)
let ABT_PAIR_TAC q r pts =
  let rv n = mk_var(n,`:real`) in
  let sq x a = [rv("c"^x); rv("s"^x); rv("u"^x); rv("v"^x); rv("a"^a)] in
  let qs = sq q q and rs = sq r q in
  let dirs = [rv("c"^q), rv("s"^q); mk_comb(`(--)`, rv("s"^q)), rv("c"^q);
              rv("c"^r), rv("s"^r); mk_comb(`(--)`, rv("s"^r)), rv("c"^r)] in
  MP_TAC(SPECL (sq q q @ sq r r) ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> concl th = mk_eq(rv("a"^q), rv("a"^r)))) THEN
  ABT_ALL_SB_TAC (map (fun (who,pt) -> (if who = q then qs else rs), pt) pts) dirs THEN
  ABT_OWN_TAC qs THEN ABT_OWN_TAC rs THEN ABT_ARITH_TAC;;
