(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/ThreeCentral/TwoSquares.lean        *)
(* (namespace N12Compact.Completion.OtherCases.ThreeCentral).  A square     *)
(* with an inward auxiliary pair cannot be disjoint from the square holding *)
(* the other three central markers.  upper / lower: ABT_upper / ABT_lower;  *)
(* strict_bounds: ABT_STRICT_BOUNDS (ABT_SB_TAC); the SAT reduction         *)
(* (faceSeparation_of_disjoint, separated, parallel/transverse_radius):     *)
(* ABT_FOUR_AXES; C868CentralSupport.positive_support:                      *)
(* C868CS_POSITIVE_SUPPORT; steep_support: OC3CSS_STEEP_SUPPORT;            *)
(* canonical_frame: CLF_CANONICAL_FRAME; Normal: c977cc_normal.             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_ThreeCentral_SteepSupport.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: radius_even (private) *)
let OC3CTS_RADIUS_EVEN = prove
 (`forall c s a nx ny. tss_support_radius c s a (--nx) (--ny) = tss_support_radius c s a nx ny`,
  REWRITE_TAC[tss_support_radius] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `--nx * c + --ny * s = --(nx * c + ny * s)`;
              REAL_ARITH `-- --nx * s + --ny * c = --(--nx * s + ny * c)`; REAL_ABS_NEG]);;

(* Lean: upper_neg (private) *)
let OC3CTS_UPPER_NEG = prove
 (`forall c s u v a nx ny.
      ABT_upper c s u v a (--nx) (--ny) = --ABT_lower c s u v a nx ny`,
  REWRITE_TAC[ABT_upper; ABT_lower; OC3CTS_RADIUS_EVEN] THEN REAL_ARITH_TAC);;

(* Lean: lower_neg (private) *)
let OC3CTS_LOWER_NEG = prove
 (`forall c s u v a nx ny.
      ABT_lower c s u v a (--nx) (--ny) = --ABT_upper c s u v a nx ny`,
  REWRITE_TAC[ABT_upper; ABT_lower; OC3CTS_RADIUS_EVEN] THEN REAL_ARITH_TAC);;

(* Lean: separator_cone (private) and the no_forward step of             *)
(* positive_impossible: no separator from A towards H                     *)
let OC3CTS_NO_FORWARD = prove
 (`forall cA sA uA vA cH sH uH vH a x y.
      cA * cA + sA * sA = &1 /\ cH * cH + sH * sH = &1 /\ &0 < a /\
      c977cc_normal cA sA /\ &1 < a /\
      linside cA sA uA vA a (&33 / &20) (&33 / &20) /\
      linside cA sA uA vA a (&2) (&87 / &50) /\
      linside cA sA uA vA a (&87 / &50) (&2) /\
      ~linside cA sA uA vA a (&8 / &5) (&1) /\
      ~linside cA sA uA vA a (&1) (&8 / &5) /\
      linside cH sH uH vH a (&47 / &20) (&33 / &20) /\
      linside cH sH uH vH a (&33 / &20) (&47 / &20) /\
      x pow 2 + y pow 2 = &1 /\
      ABT_upper cA sA uA vA a x y <= ABT_lower cH sH uH vH a x y
      ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABT_SB_TAC [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `a:real`]
    `&2` `&87 / &50` `x:real` `y:real` THEN
  ABT_SB_TAC [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `a:real`]
    `&87 / &50` `&2` `x:real` `y:real` THEN
  ABT_SB_TAC [`cH:real`; `sH:real`; `uH:real`; `vH:real`; `a:real`]
    `&47 / &20` `&33 / &20` `x:real` `y:real` THEN
  ABT_SB_TAC [`cH:real`; `sH:real`; `uH:real`; `vH:real`; `a:real`]
    `&33 / &20` `&47 / &20` `x:real` `y:real` THEN
  SUBGOAL_THEN `&0 < x /\ &0 < y` STRIP_ASSUME_TAC THENL
   [ABT_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `y <= x` THENL
   [MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `a:real`;
                  `x:real`; `y:real`] C868CS_POSITIVE_SUPPORT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[c977cc_normal] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    ABT_ARITH_TAC;
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `a:real`;
                  `x:real`; `y:real`] OC3CSS_STEEP_SUPPORT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    ABT_ARITH_TAC]);;

(* Lean: no_axis step of positive_impossible: neither order separates *)
let OC3CTS_NO_AXIS = prove
 (`forall cA sA uA vA cH sH uH vH a.
      cA * cA + sA * sA = &1 /\ cH * cH + sH * sH = &1 /\ &0 < a /\
      c977cc_normal cA sA /\ &1 < a /\
      linside cA sA uA vA a (&33 / &20) (&33 / &20) /\
      linside cA sA uA vA a (&2) (&87 / &50) /\
      linside cA sA uA vA a (&87 / &50) (&2) /\
      ~linside cA sA uA vA a (&8 / &5) (&1) /\
      ~linside cA sA uA vA a (&1) (&8 / &5) /\
      linside cH sH uH vH a (&47 / &20) (&33 / &20) /\
      linside cH sH uH vH a (&33 / &20) (&47 / &20)
      ==> forall x y. x pow 2 + y pow 2 = &1
                ==> ~(ABT_upper cA sA uA vA a x y <= ABT_lower cH sH uH vH a x y) /\
                    ~(ABT_upper cH sH uH vH a x y <= ABT_lower cA sA uA vA a x y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`;
                  `cH:real`; `sH:real`; `uH:real`; `vH:real`; `a:real`;
                  `x:real`; `y:real`] OC3CTS_NO_FORWARD);
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`;
                  `cH:real`; `sH:real`; `uH:real`; `vH:real`; `a:real`;
                  `--x`; `--y`] OC3CTS_NO_FORWARD) THEN
    REWRITE_TAC[OC3CTS_UPPER_NEG; OC3CTS_LOWER_NEG; REAL_LE_NEG2;
                REAL_POW_NEG; ARITH]] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: positive_impossible (private) *)
let OC3CTS_POSITIVE_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cH sH uH vH aH.
      cA * cA + sA * sA = &1 /\ &0 < aA /\ cH * cH + sH * sH = &1 /\ &0 < aH /\
      c977cc_normal cA sA /\ &1 < aA /\ aA = aH /\
      linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
      linside cA sA uA vA aA (&2) (&87 / &50) /\
      linside cA sA uA vA aA (&87 / &50) (&2) /\
      ~linside cA sA uA vA aA (&8 / &5) (&1) /\
      ~linside cA sA uA vA aA (&1) (&8 / &5) /\
      linside cH sH uH vH aH (&47 / &20) (&33 / &20) /\
      linside cH sH uH vH aH (&47 / &20) (&47 / &20) /\
      linside cH sH uH vH aH (&33 / &20) (&47 / &20) /\
      ldisj cA sA uA vA aA cH sH uH vH aH
      ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cH:real`; `sH:real`; `uH:real`; `vH:real`; `aH:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = aH`)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`;
                `cH:real`; `sH:real`; `uH:real`; `vH:real`; `aH:real`] OC3CTS_NO_AXIS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MAP_EVERY (fun (x,y) ->
      FIRST_ASSUM(MP_TAC o SPECL [x; y] o check (is_forall o concl)) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_POW_2] THEN ABT_ARITH_TAC; ALL_TAC])
    [`cA:real`,`sA:real`; `--sA`,`cA:real`; `cH:real`,`sH:real`; `--sH`,`cH:real`] THEN
  CONV_TAC TAUT);;

(* Lean: impossible *)
let OC3CTS_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cH sH uH vH aH.
      cA * cA + sA * sA = &1 /\ &0 < aA /\ cH * cH + sH * sH = &1 /\ &0 < aH /\
      &1 < aA /\ aA = aH /\
      linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
      linside cA sA uA vA aA (&2) (&87 / &50) /\
      linside cA sA uA vA aA (&87 / &50) (&2) /\
      ~linside cA sA uA vA aA (&8 / &5) (&1) /\
      ~linside cA sA uA vA aA (&1) (&8 / &5) /\
      linside cH sH uH vH aH (&47 / &20) (&33 / &20) /\
      linside cH sH uH vH aH (&47 / &20) (&47 / &20) /\
      linside cH sH uH vH aH (&33 / &20) (&47 / &20) /\
      ldisj cA sA uA vA aA cH sH uH vH aH
      ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  PURE_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = aA`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && can (find_term ((=) `linside`)) (concl th) &&
       length(fst(strip_forall(concl th))) = 2 && is_eq(snd(strip_forall(concl th)))
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MATCH_MP_TAC OC3CTS_POSITIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `aA:real`;
                          `cH:real`; `sH:real`; `uH:real`; `vH:real`; `aH:real`] THEN
    ASM_REWRITE_TAC[ldisj; c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    (* b = (c1, --s1, v1, u1): b.Inside x y <=> a.Inside y x;  J = pullSwap H *)
    MATCH_MP_TAC OC3CTS_POSITIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`c1:real`; `--s1`; `v1:real`; `u1:real`; `aA:real`;
                          `sH:real`; `cH:real`; `uH:real`; `--vH - aH`; `aH:real`] THEN
    SUBGOAL_THEN `forall x y. linside c1 (--s1) v1 u1 aA x y <=> linside c1 s1 u1 v1 aA y x`
      (fun th -> REWRITE_TAC[th; LINSIDE_PULLSW; ldisj]) THENL
     [REWRITE_TAC[linside] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    REPEAT GEN_TAC THEN FIRST_X_ASSUM(MATCH_ACCEPT_TAC o check (is_forall o concl))]);;
