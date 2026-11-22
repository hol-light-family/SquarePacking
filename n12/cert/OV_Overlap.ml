(* ========================================================================= *)
(* W-F345: block overlaps of the historical pair stages (n12/docs/cert_design.md *)
(* §4.2, §9).  Tag OV_ / ov_.                                                *)
(*                                                                           *)
(* Lean: Compact/Core/VertexSupport.lean (Basis.Cone, Basis.sound,           *)
(*       PairCheck), Compact/Core/CommonPoint.lean (axis, inside_sound),     *)
(*       Compact/Core/RawSupportFan.lean (PairCheck, pair_sound),            *)
(*       Compact/Bridge/IndexedCommonGroups.lean (PairOverlaps, pointGroup,  *)
(*       fallbackGroup, block_overlap_headers), Compact/Bridge/              *)
(*       IndexedCommonPoint.lean, Compact/Core/ReferenceAxis.lean            *)
(*       (directions, overlap), Compact/Core/EmptyContext.lean.              *)
(*                                                                           *)
(* Only the checks are ported (design §1.3): Lean's fans, keys, direction    *)
(* arrays, rectangle partitions and kernel matrices are replaced by          *)
(*  - F3  support entries: for a context (row list) and an angle, four       *)
(*        nonnegative row combinations whose (x,y) parts are positive        *)
(*        multiples k of the four integer face normals of the angle;         *)
(*  - F5  common points: P = (X/W, Y/W) is in the inner reference square of  *)
(*        the context's own angle around every centre of the context;        *)
(*  - F4  8-axis SAT with the support bounds of both contexts                *)
(*        (p3 AOC_AXISOVERLAPFORMS_SOUND);                                   *)
(*  - an emptiness witness (cr_empty_check) for an infeasible context.       *)
(* Every check is an executable HOL function evaluated by CR_EVAL_CONV.     *)
(* ========================================================================= *)

needs "n12/cert/CR_Eval.ml";;

(* ------------------------------------------------------------------------- *)
(* Integer references of the 192 angles (Lean HistoricalPoseFanRecipe.       *)
(* reference: (c*d, s*d, d, inner.num, inner.den)).                         *)
(* ------------------------------------------------------------------------- *)

let ovref_INDUCT,ovref_RECURSION = define_type "ovref = OvRef int int int int int";;
let ovr_c = define `ovr_c (OvRef C S D N M) = C`;;
let ovr_s = define `ovr_s (OvRef C S D N M) = S`;;
let ovr_d = define `ovr_d (OvRef C S D N M) = D`;;
let ovr_n = define `ovr_n (OvRef C S D N M) = N`;;
let ovr_m = define `ovr_m (OvRef C S D N M) = M`;;

let ov_ref_ok = new_definition
 `ov_ref_ok a r <=>
    &0 < ovr_d r /\ &0 < ovr_m r /\
    ae_c (s12_angles a) = real_of_int (ovr_c r) / real_of_int (ovr_d r) /\
    ae_s (s12_angles a) = real_of_int (ovr_s r) / real_of_int (ovr_d r) /\
    ae_inner (s12_angles a) = real_of_int (ovr_n r) / real_of_int (ovr_m r)`;;

(* the 192 integer references, n12/data/cert/ov_refs.txt (untrusted, checked below) *)
let ov_ref_tms =
  Array.of_list (List.map (fun l -> match cr_split ' ' l with
      [_; c; s; d; n; m] -> list_mk_comb (`OvRef`, map cr_int_tm [c; s; d; n; m])
    | _ -> failwith "ov_refs") (cr_read_lines "n12/data/cert/ov_refs.txt"));;

let ov_refs = new_definition
  (mk_eq (`ov_refs:ovref list`, mk_list (Array.to_list ov_ref_tms, `:ovref`)));;
let ov_ref = new_definition `ov_ref a = EL a ov_refs`;;

let OV_REF_LIT_OK =
  let conv = REWRITE_CONV[ov_ref_ok; ovr_c; ovr_s; ovr_d; ovr_n; ovr_m; s12_angles] THENC
             NUM_REDUCE_CONV THENC REWRITE_CONV[AD64_EL; AD128_EL] THENC
             REWRITE_CONV[ae_c; ae_s; ae_inner; int_of_num_th; int_neg_th; int_lt] THENC
             REAL_RAT_REDUCE_CONV in
  Array.mapi (fun i r ->
    EQT_ELIM (conv (list_mk_comb (`ov_ref_ok`, [mk_small_numeral i; r])))) ov_ref_tms;;

let ov_refs_ok = define
 `(ov_refs_ok k [] <=> true) /\
  (ov_refs_ok k (CONS r rs) <=> ov_ref_ok k r /\ ov_refs_ok (k + 1) rs)`;;

let OV_REFS_OK_EL = prove
 (`forall l k i. ov_refs_ok k l /\ i < LENGTH l ==> ov_ref_ok (k + i) (EL i l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ov_refs_ok; LENGTH; LT] THEN
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; ADD_CLAUSES] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k + 1`; `i:num`]) THEN
  ASM_REWRITE_TAC[ARITH_RULE `(k + 1) + i = SUC (k + i)`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let OV_REFS_ALL_OK =
  let lem = prove
   (`forall k k' r rs. ov_ref_ok k r /\ ov_refs_ok k' rs /\ k + 1 = k' ==> ov_refs_ok k (CONS r rs)`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC[ov_refs_ok]) in
  let n = Array.length ov_ref_tms in
  let rec go i =
    if i = n then EQT_ELIM (INST [mk_small_numeral n, `k:num`] (SPEC_ALL (CONJUNCT1 ov_refs_ok)))
    else
      let th = go (i + 1) in
      let k = mk_small_numeral i and k' = mk_small_numeral (i + 1) in
      let eq = NUM_ADD_CONV (mk_binop `(+):num->num->num` k `1`) in
      MP (ISPECL [k; k'; ov_ref_tms.(i); rand (concl th)] lem)
         (CONJ OV_REF_LIT_OK.(i) (CONJ th eq)) in
  let th = go 0 in
  EQ_MP (AP_TERM `ov_refs_ok 0` (SYM ov_refs)) th;;

let OV_REF_OK = prove
 (`forall a. a < 192 ==> ov_ref_ok a (ov_ref a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ov_ref] THEN
  MP_TAC(SPECL [`ov_refs`; `0`; `a:num`] OV_REFS_OK_EL) THEN
  REWRITE_TAC[ADD_CLAUSES; OV_REFS_ALL_OK] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[ov_refs; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Support entries (F3).                                                     *)
(* OvSup k e s for direction (nx,ny): every centre p of the context          *)
(* satisfies k*(nx*px+ny*py) + e >= 0 (> 0 if s), with k > 0.                *)
(* OvAng a r s0 s1 s2 s3: angle a with reference r and the supports for the  *)
(* four face normals (C,S), (-C,-S), (-S,C), (S,-C) of r.                    *)
(* ------------------------------------------------------------------------- *)

let ovsup_INDUCT,ovsup_RECURSION = define_type "ovsup = OvSup int int bool";;
let ovs_k = define `ovs_k (OvSup k e s) = k`;;
let ovs_e = define `ovs_e (OvSup k e s) = e`;;
let ovs_s = define `ovs_s (OvSup k e s) = s`;;

let ovang_INDUCT,ovang_RECURSION = define_type "ovang = OvAng num ovref ovsup ovsup ovsup ovsup";;
let ova_angle = define `ova_angle (OvAng a r s0 s1 s2 s3) = a`;;
let ova_ref = define `ova_ref (OvAng a r s0 s1 s2 s3) = r`;;
let ova_s0 = define `ova_s0 (OvAng a r s0 s1 s2 s3) = s0`;;
let ova_s1 = define `ova_s1 (OvAng a r s0 s1 s2 s3) = s1`;;
let ova_s2 = define `ova_s2 (OvAng a r s0 s1 s2 s3) = s2`;;
let ova_s3 = define `ova_s3 (OvAng a r s0 s1 s2 s3) = s3`;;

let ov_sup_holds = new_definition
 `ov_sup_holds sp nx ny px py <=>
    &0 < ovs_k sp /\ cr_holds (CRow (ovs_k sp * nx) (ovs_k sp * ny) (ovs_e sp) (ovs_s sp)) px py`;;

(* semantic validity of one table entry for a context (row list) *)
let ov_ang_sem = new_definition
 `ov_ang_sem rws e <=>
    ova_angle e < 192 /\ ov_ref (ova_angle e) = ova_ref e /\
    forall px py. (forall r. MEM r rws ==> cr_holds r px py) ==>
      ov_sup_holds (ova_s0 e) (ovr_c (ova_ref e)) (ovr_s (ova_ref e)) px py /\
      ov_sup_holds (ova_s1 e) (--ovr_c (ova_ref e)) (--ovr_s (ova_ref e)) px py /\
      ov_sup_holds (ova_s2 e) (--ovr_s (ova_ref e)) (ovr_c (ova_ref e)) px py /\
      ov_sup_holds (ova_s3 e) (ovr_s (ova_ref e)) (--ovr_c (ova_ref e)) px py`;;


(* ------------------------------------------------------------------------- *)
(* Level-1 checker: a support entry from a row combination (F1/F3).          *)
(* ------------------------------------------------------------------------- *)

let OV_IF_POS0 = prove
 (`forall s x. (if s then &0 < x else &0 <= x) <=> &0 <= x /\ (s ==> &0 < x)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;
let OV_LMUL_LT = prove
 (`forall k a b. &0 < k /\ k * a < k * b ==> a < b`,
  MESON_TAC[REAL_LT_LMUL_EQ]);;
let OV_INT_RULES0 = [int_le; int_lt; int_eq; int_add_th; int_mul_th; int_of_num_th;
                     int_sub_th; int_neg_th; int_abs_th];;

(* rounding: from k*L + c >= 0 (> if s0) and c/k <= e/k' to k'*L + e >= 0 *)
let OV_ROUND = prove
 (`forall k k' c e s0 s L.
     &0 < k /\ &0 < k' /\ (if s0 then &0 < k * L + c else &0 <= k * L + c) /\
     c * k' <= e * k /\ (s ==> s0 \/ c * k' < e * k)
     ==> (if s then &0 < k' * L + e else &0 <= k' * L + e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OV_IF_POS0] THEN STRIP_TAC THEN
  SUBGOAL_THEN `k * (k' * L + e) = k' * (k * L + c) + (e * k - c * k')` ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= k' * (k * L + c) /\ (s0 ==> &0 < k' * (k * L + c))` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LT_MUL]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ISPEC `k:real` REAL_LE_LCANCEL_IMP) THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN MATCH_MP_TAC OV_LMUL_LT THEN EXISTS_TAC `k:real` THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> not (is_var (concl th)) && not (is_neg (concl th))))) THEN
    ASM_CASES_TAC `s0:bool` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* Lean: VertexSupport.Basis.sound (a cone combination of context rows), with the
   bound relaxed to the rounded entry sp *)
let ov_sup_check = new_definition
 `ov_sup_check rws sp (nx:int) (ny:int) (cert:int#(int#num)list) <=>
    &0 < FST cert /\ &0 < ovs_k sp /\ cr_nonneg (SND cert) /\
    (let r = cr_sum rws (SND cert) in
     cr_x r = FST cert * nx /\ cr_y r = FST cert * ny /\
     cr_c r * ovs_k sp <= ovs_e sp * FST cert /\
     (ovs_s sp ==> cr_s r \/ cr_c r * ovs_k sp < ovs_e sp * FST cert))`;;

let OV_SUP_CHECK_SOUND = prove
 (`forall rws sp nx ny cert px py.
     ov_sup_check rws sp nx ny cert /\ (forall r. MEM r rws ==> cr_holds r px py)
     ==> ov_sup_holds sp nx ny px py`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ov_sup_check; ov_sup_holds; LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`rws:crow list`; `SND (cert:int#(int#num)list)`; `px:real`; `py:real`] CR_SUM_SOUND) THEN
  ASM_SIMP_TAC[CR_ROWAT_HOLDS] THEN
  REWRITE_TAC[cr_holds; cr_eval; cr_x; cr_y; cr_c; cr_s] THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE OV_INT_RULES0) THEN REWRITE_TAC OV_INT_RULES0 THEN
  REWRITE_TAC[REAL_ARITH `(k * nx) * px + (k * ny) * py + c = k * (nx * px + ny * py) + c`] THEN
  DISCH_TAC THEN MATCH_MP_TAC OV_ROUND THEN
  MAP_EVERY EXISTS_TAC [`real_of_int (FST (cert:int#(int#num)list))`;
    `real_of_int (cr_c (cr_sum rws (SND (cert:int#(int#num)list))))`;
    `cr_s (cr_sum rws (SND (cert:int#(int#num)list)))`] THEN
  ASM_REWRITE_TAC[]);;

let ov_ang_check = define
 `ov_ang_check rws (OvAng a r s0 s1 s2 s3)
     (cs:(int#(int#num)list)#(int#(int#num)list)#(int#(int#num)list)#(int#(int#num)list)) <=>
    a < 192 /\ ov_ref a = r /\
    ov_sup_check rws s0 (ovr_c r) (ovr_s r) (FST cs) /\
    ov_sup_check rws s1 (--ovr_c r) (--ovr_s r) (FST (SND cs)) /\
    ov_sup_check rws s2 (--ovr_s r) (ovr_c r) (FST (SND (SND cs))) /\
    ov_sup_check rws s3 (ovr_s r) (--ovr_c r) (SND (SND (SND cs)))`;;

let OV_ANG_CHECK_SOUND = prove
 (`forall rws e cs. ov_ang_check rws e cs ==> ov_ang_sem rws e`,
  GEN_TAC THEN MATCH_MP_TAC ovang_INDUCT THEN
  REWRITE_TAC[ov_ang_check; ov_ang_sem; ova_angle; ova_ref; ova_s0; ova_s1; ova_s2; ova_s3] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OV_SUP_CHECK_SOUND THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Real-arithmetic cores.                                                    *)
(* ------------------------------------------------------------------------- *)

let OV_DIV_NEG = prove
 (`forall x y. x < &0 /\ &0 < y ==> x / y < &0`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`--x:real`; `y:real`] REAL_LT_DIV) THEN
  ASM_REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN ASM_REAL_ARITH_TAC);;

let OV_IF_POS = prove
 (`forall s x. (if s then &0 < x else &0 <= x) <=> &0 <= x /\ (s ==> &0 < x)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: CommonPoint.axis (one face of the inner reference square) *)
let OV_PT_CORE = prove
 (`forall k e s nx ny px py X Y W M D Nn.
     &0 < k /\ &0 < W /\ &0 < M /\ &0 < D /\
     (if s then &0 < (k * nx) * px + (k * ny) * py + e
      else &0 <= (k * nx) * px + (k * ny) * py + e) /\
     (&2 * M * (k * (nx * X + ny * Y) + e * W) < k * D * Nn * W \/
      s /\ &2 * M * (k * (nx * X + ny * Y) + e * W) <= k * D * Nn * W)
     ==> (nx / D) * (X / W - px) + (ny / D) * (Y / W - py) < (&1 * Nn / M) / &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OV_IF_POS] THEN
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &2 * M * W` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&2 * M * W) * ((k * nx) * px + (k * ny) * py + e) /\ (s ==> &0 < (&2 * M * W) * ((k * nx) * px + (k * ny) * py + e))` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * M * (nx * X + ny * Y - W * (nx * px + ny * py)) < D * Nn * W`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OV_LMUL_LT THEN EXISTS_TAC `k:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `s:bool` THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> not (is_var (concl th)) && not (is_neg (concl th))))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((nx / D) * (X / W - px) + (ny / D) * (Y / W - py)) - (&1 * Nn / M) / &2 =
    (&2 * M * (nx * X + ny * Y - W * (nx * px + ny * py)) - D * Nn * W) / (&2 * M * D * W)`
  ASSUME_TAC THENL
   [MAP_EVERY (fun t -> SUBGOAL_THEN (mk_neg(mk_eq(t,`&0`))) MP_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC]) [`M:real`; `D:real`; `W:real`] THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a - b < &0 ==> a < b`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OV_DIV_NEG THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC);;

(* Lean: ReferenceSquare.ratRadius for an integer reference and direction *)
let OV_RADIUS = prove
 (`forall C S D N M nx ny dn. &0 < D /\ &0 < M /\ &0 < dn ==>
     rs_rat_radius (RefSq (C / D) (S / D) (&1 * N / M)) (nx / dn) (ny / dn) =
     N * (abs(nx * C + ny * S) + abs(--nx * S + ny * C)) / (&2 * M * D * dn)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rs_rat_radius; rs_c; rs_s; rs_side] THEN
  SUBGOAL_THEN `&0 < dn * D` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `nx / dn * C / D + ny / dn * S / D = (nx * C + ny * S) / (dn * D) /\
                --(nx / dn) * S / D + ny / dn * C / D = (--nx * S + ny * C) / (dn * D)`
   (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_comb o concl))) THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_DIV] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_comb o concl))) THEN CONV_TAC REAL_FIELD);;

(* Lean: VertexSupport.PairCheck + ReferenceAxis gap (one axis of the SAT test) *)
let OV_AXIS_CORE = prove
 (`forall kA eA sA kB eB sB nx ny dn px py rx ry CA SA DA NA MA CB SB DB NB MB.
     &0 < kA /\ &0 < kB /\ &0 < dn /\ &0 < DA /\ &0 < MA /\ &0 < DB /\ &0 < MB /\
     (if sA then &0 < (kA * nx) * px + (kA * ny) * py + eA
      else &0 <= (kA * nx) * px + (kA * ny) * py + eA) /\
     (if sB then &0 < (kB * --nx) * rx + (kB * --ny) * ry + eB
      else &0 <= (kB * --nx) * rx + (kB * --ny) * ry + eB) /\
     (&2 * MA * DA * MB * DB * (eA * kB + eB * kA) <
      kA * kB * (NA * (abs(nx * CA + ny * SA) + abs(--nx * SA + ny * CA)) * MB * DB +
                 NB * (abs(nx * CB + ny * SB) + abs(--nx * SB + ny * CB)) * MA * DA) \/
      &2 * MA * DA * MB * DB * (eA * kB + eB * kA) <=
      kA * kB * (NA * (abs(nx * CA + ny * SA) + abs(--nx * SA + ny * CA)) * MB * DB +
                 NB * (abs(nx * CB + ny * SB) + abs(--nx * SB + ny * CB)) * MA * DA) /\
      (sA \/ sB))
     ==> (nx / dn) * (rx - px) + (ny / dn) * (ry - py) <
         rs_rat_radius (RefSq (CA / DA) (SA / DA) (&1 * NA / MA)) (nx / dn) (ny / dn) +
         rs_rat_radius (RefSq (CB / DB) (SB / DB) (&1 * NB / MB)) (nx / dn) (ny / dn)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OV_IF_POS; IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  ASM_SIMP_TAC[OV_RADIUS] THEN
  ABBREV_TAC `GA = abs(nx * CA + ny * SA) + abs(--nx * SA + ny * CA)` THEN
  ABBREV_TAC `GB = abs(nx * CB + ny * SB) + abs(--nx * SB + ny * CB)` THEN
  SUBGOAL_THEN `&0 < &2 * MA * DA * MB * DB` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&2 * MA * DA * MB * DB) * kB /\ &0 < (&2 * MA * DA * MB * DB) * kA`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= ((&2 * MA * DA * MB * DB) * kB) * ((kA * nx) * px + (kA * ny) * py + eA) /\
    (sA ==> &0 < ((&2 * MA * DA * MB * DB) * kB) * ((kA * nx) * px + (kA * ny) * py + eA)) /\
    &0 <= ((&2 * MA * DA * MB * DB) * kA) * ((kB * --nx) * rx + (kB * --ny) * ry + eB) /\
    (sB ==> &0 < ((&2 * MA * DA * MB * DB) * kA) * ((kB * --nx) * rx + (kB * --ny) * ry + eB))`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * MA * DA * MB * DB) * (nx * (rx - px) + ny * (ry - py)) <
                NA * GA * MB * DB + NB * GB * MA * DA` ASSUME_TAC THENL
   [MATCH_MP_TAC OV_LMUL_LT THEN EXISTS_TAC `kA * kB:real` THEN
    ASM_SIMP_TAC[REAL_LT_MUL] THEN
    ASM_CASES_TAC `sA:bool` THEN ASM_CASES_TAC `sB:bool` THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> not (is_var (concl th)) && not (is_neg (concl th))))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((nx / dn) * (rx - px) + (ny / dn) * (ry - py)) -
    (NA * GA / (&2 * MA * DA * dn) + NB * GB / (&2 * MB * DB * dn)) =
    ((&2 * MA * DA * MB * DB) * (nx * (rx - px) + ny * (ry - py)) -
     (NA * GA * MB * DB + NB * GB * MA * DA)) / ((&2 * MA * DA * MB * DB) * dn)`
  ASSUME_TAC THENL
   [MAP_EVERY (fun t -> SUBGOAL_THEN (mk_neg(mk_eq(t,`&0`))) MP_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC]) [`MA:real`; `DA:real`; `MB:real`; `DB:real`; `dn:real`] THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a - b < &0 ==> a < b`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OV_DIV_NEG THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Level-2 checkers: common points (F5) and 8-axis SAT (F4).                 *)
(* ------------------------------------------------------------------------- *)

(* Lean: CommonPoint.axis (integer test, P = (X/W, Y/W)) *)
let ov_pt_sup = new_definition
 `ov_pt_sup r sp (nx:int) (ny:int) (X:int) (Y:int) (W:int) <=>
    let k = ovs_k sp in
    let lhs = &2 * ovr_m r * (k * (nx * X + ny * Y) + ovs_e sp * W) in
    let rhs = k * ovr_d r * ovr_n r * W in
    lhs < rhs \/ (ovs_s sp /\ lhs <= rhs)`;;

(* Lean: IndexedCommonPoint.PointCheck (the 4 own faces) *)
let ov_pt_ok = new_definition
 `ov_pt_ok e X Y W <=>
    &0 < W /\
    ov_pt_sup (ova_ref e) (ova_s0 e) (ovr_c (ova_ref e)) (ovr_s (ova_ref e)) X Y W /\
    ov_pt_sup (ova_ref e) (ova_s1 e) (--ovr_c (ova_ref e)) (--ovr_s (ova_ref e)) X Y W /\
    ov_pt_sup (ova_ref e) (ova_s2 e) (--ovr_s (ova_ref e)) (ovr_c (ova_ref e)) X Y W /\
    ov_pt_sup (ova_ref e) (ova_s3 e) (ovr_s (ova_ref e)) (--ovr_c (ova_ref e)) X Y W`;;

let ov_g = new_definition
 `ov_g (nx:int) (ny:int) r = abs(nx * ovr_c r + ny * ovr_s r) + abs(--nx * ovr_s r + ny * ovr_c r)`;;

(* Lean: VertexSupport.PairCheck (one axis; supports of both contexts) *)
let ov_axis_ok = new_definition
 `ov_axis_ok ra rb (nx:int) (ny:int) sa sb <=>
    let kA = ovs_k sa in let kB = ovs_k sb in
    let lhs = &2 * ovr_m ra * ovr_d ra * ovr_m rb * ovr_d rb * (ovs_e sa * kB + ovs_e sb * kA) in
    let rhs = kA * kB * (ovr_n ra * ov_g nx ny ra * ovr_m rb * ovr_d rb +
                         ovr_n rb * ov_g nx ny rb * ovr_m ra * ovr_d ra) in
    lhs < rhs \/ (lhs <= rhs /\ (ovs_s sa \/ ovs_s sb))`;;

(* the four axes of angle X: ex = source entry for X, ey = neighbour entry for X *)
let ov_axes = new_definition
 `ov_axes ra rb ex ey <=>
    ov_axis_ok ra rb (ovr_c (ova_ref ex)) (ovr_s (ova_ref ex)) (ova_s0 ex) (ova_s1 ey) /\
    ov_axis_ok ra rb (--ovr_c (ova_ref ex)) (--ovr_s (ova_ref ex)) (ova_s1 ex) (ova_s0 ey) /\
    ov_axis_ok ra rb (--ovr_s (ova_ref ex)) (ovr_c (ova_ref ex)) (ova_s2 ex) (ova_s3 ey) /\
    ov_axis_ok ra rb (ovr_s (ova_ref ex)) (--ovr_c (ova_ref ex)) (ova_s3 ex) (ova_s2 ey)`;;

(* ------------------------------------------------------------------------- *)
(* Soundness of the level-2 checks.                                          *)
(* ------------------------------------------------------------------------- *)

let OV_INT_RULES = [int_le; int_lt; int_eq; int_add_th; int_mul_th; int_of_num_th;
                    int_sub_th; int_neg_th; int_abs_th];;

let OV_HOLDS_REAL = prove
 (`forall k nx ny e s px py.
     cr_holds (CRow (k * nx) (k * ny) e s) px py <=>
     (if s then &0 < (real_of_int k * real_of_int nx) * px + (real_of_int k * real_of_int ny) * py + real_of_int e
      else &0 <= (real_of_int k * real_of_int nx) * px + (real_of_int k * real_of_int ny) * py + real_of_int e)`,
  REWRITE_TAC[cr_holds; cr_eval; cr_x; cr_y; cr_c; cr_s; int_mul_th]);;

let OV_ENTRY_FACTS = prove
 (`forall rws e. ov_ang_sem rws e ==>
     ova_angle e < 192 /\ ov_ref_ok (ova_angle e) (ova_ref e) /\ ae_check (s12_angles (ova_angle e))`,
  REWRITE_TAC[ov_ang_sem] THEN MESON_TAC[OV_REF_OK; S12_ANGLES_CHECKED]);;

let OV_PT_DIR = prove
 (`forall sp nx ny X Y W px py C S D N M.
     &0 < real_of_int D /\ &0 < real_of_int M /\ &0 < real_of_int W /\
     ov_sup_holds sp nx ny px py /\ ov_pt_sup (OvRef C S D N M) sp nx ny X Y W
     ==> (real_of_int nx / real_of_int D) * (real_of_int X / real_of_int W - px) +
         (real_of_int ny / real_of_int D) * (real_of_int Y / real_of_int W - py) <
         (&1 * real_of_int N / real_of_int M) / &2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ov_sup_holds; ov_pt_sup; LET_DEF; LET_END_DEF; OV_HOLDS_REAL;
              ovr_c; ovr_s; ovr_d; ovr_n; ovr_m] THEN
  REWRITE_TAC OV_INT_RULES THEN STRIP_TAC THEN MATCH_MP_TAC OV_PT_CORE THEN
  MAP_EVERY EXISTS_TAC [`real_of_int(ovs_k sp)`; `real_of_int(ovs_e sp)`; `ovs_s sp`] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: CommonPoint.inside_sound *)
let OV_PT_ENTRY0 = prove
 (`forall C S D N M s0 s1 s2 s3 X Y W px py.
     &0 < real_of_int D /\ &0 < real_of_int M /\ &0 < real_of_int W /\
     ov_sup_holds s0 C S px py /\ ov_sup_holds s1 (--C) (--S) px py /\
     ov_sup_holds s2 (--S) C px py /\ ov_sup_holds s3 S (--C) px py /\
     ov_pt_sup (OvRef C S D N M) s0 C S X Y W /\
     ov_pt_sup (OvRef C S D N M) s1 (--C) (--S) X Y W /\
     ov_pt_sup (OvRef C S D N M) s2 (--S) C X Y W /\
     ov_pt_sup (OvRef C S D N M) s3 S (--C) X Y W
     ==> psub (real_of_int X / real_of_int W, real_of_int Y / real_of_int W) (px,py) IN
         sqset (real_of_int C / real_of_int D) (real_of_int S / real_of_int D)
               (--(&1 * real_of_int N / real_of_int M) / &2)
               (--(&1 * real_of_int N / real_of_int M) / &2)
               (&1 * real_of_int N / real_of_int M)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (sp, nx, ny) ->
    MP_TAC(SPECL [sp; nx; ny; `X:int`; `Y:int`; `W:int`; `px:real`; `py:real`;
                  `C:int`; `S:int`; `D:int`; `N:int`; `M:int`] OV_PT_DIR) THEN
    ASM_REWRITE_TAC[])
   [`s0:ovsup`, `C:int`, `S:int`; `s1:ovsup`, `--C:int`, `--S:int`;
    `s2:ovsup`, `--S:int`, `C:int`; `s3:ovsup`, `S:int`, `--C:int`] THEN
  REWRITE_TAC[IN_SQSET; psub; linside; FST; SND; int_neg_th] THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN REAL_ARITH_TAC);;

let OV_PT_ENTRY = prove
 (`forall rws e X Y W px py.
     ov_ang_sem rws e /\ (forall r. MEM r rws ==> cr_holds r px py) /\ ov_pt_ok e X Y W
     ==> psub (real_of_int X / real_of_int W, real_of_int Y / real_of_int W) (px,py) IN
         rs_sqset (ae_reference (s12_angles (ova_angle e)) (&1))`,
  GEN_TAC THEN MATCH_MP_TAC ovang_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `r:ovref`; `s0:ovsup`; `s1:ovsup`; `s2:ovsup`; `s3:ovsup`] THEN
  SPEC_TAC(`r:ovref`,`r:ovref`) THEN MATCH_MP_TAC ovref_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`C:int`; `S:int`; `D:int`; `N:int`; `M:int`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP OV_ENTRY_FACTS) THEN
  UNDISCH_TAC `ov_ang_sem rws (OvAng a (OvRef C S D N M) s0 s1 s2 s3)` THEN
  REWRITE_TAC[ov_ang_sem; ova_angle; ova_ref; ova_s0; ova_s1; ova_s2; ova_s3;
              ovr_c; ovr_s; ovr_d; ovr_n; ovr_m] THEN
  DISCH_THEN(MP_TAC o SPECL [`px:real`; `py:real`] o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ova_angle; ova_ref; ov_ref_ok; ovr_c; ovr_s; ovr_d; ovr_n; ovr_m]) THEN
  UNDISCH_TAC `ov_pt_ok (OvAng a (OvRef C S D N M) s0 s1 s2 s3) X Y W` THEN
  REWRITE_TAC[ov_pt_ok; ova_angle; ova_ref; ova_s0; ova_s1; ova_s2; ova_s3;
              ovr_c; ovr_s; ovr_d; ovr_n; ovr_m] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ova_angle; ae_reference; rs_sqset; rs_c; rs_s; rs_side] THEN
  MATCH_MP_TAC OV_PT_ENTRY0 THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`s0:ovsup`; `s1:ovsup`; `s2:ovsup`; `s3:ovsup`] THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[int_lt; int_of_num_th]) THEN ASM_REWRITE_TAC[]);;

let OV_PT_ENTRY_A = prove
 (`forall rws e X Y W px py a.
     ov_ang_sem rws e /\ ova_angle e = a /\ (forall r. MEM r rws ==> cr_holds r px py) /\
     ov_pt_ok e X Y W
     ==> psub (real_of_int X / real_of_int W, real_of_int Y / real_of_int W) (px,py) IN
         rs_sqset (ae_reference (s12_angles a) (&1))`,
  MESON_TAC[OV_PT_ENTRY]);;

(* one axis from two support entries *)
let OV_AXIS_ENTRY = prove
 (`forall ra rb nx ny sa sb px py rx ry a b dn.
     ov_ref_ok a ra /\ ov_ref_ok b rb /\ ov_axis_ok ra rb nx ny sa sb /\
     ov_sup_holds sa nx ny px py /\ ov_sup_holds sb (--nx) (--ny) rx ry /\ &0 < dn
     ==> (real_of_int nx / dn) * (rx - px) + (real_of_int ny / dn) * (ry - py) <
         rs_rat_radius (ae_reference (s12_angles a) (&1)) (real_of_int nx / dn) (real_of_int ny / dn) +
         rs_rat_radius (ae_reference (s12_angles b) (&1)) (real_of_int nx / dn) (real_of_int ny / dn)`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`ra:ovref`,`ra:ovref`) THEN MATCH_MP_TAC ovref_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`CA:int`; `SA:int`; `DA:int`; `NA:int`; `MA:int`] THEN
  SPEC_TAC(`rb:ovref`,`rb:ovref`) THEN MATCH_MP_TAC ovref_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`CB:int`; `SB:int`; `DB:int`; `NB:int`; `MB:int`] THEN
  REWRITE_TAC[ov_ref_ok; ovr_c; ovr_s; ovr_d; ovr_n; ovr_m] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ae_reference] THEN
  MATCH_MP_TAC OV_AXIS_CORE THEN
  MAP_EVERY EXISTS_TAC [`real_of_int(ovs_k sa)`; `real_of_int(ovs_e sa)`; `ovs_s sa`;
                        `real_of_int(ovs_k sb)`; `real_of_int(ovs_e sb)`; `ovs_s sb`] THEN
  UNDISCH_TAC `ov_axis_ok (OvRef CA SA DA NA MA) (OvRef CB SB DB NB MB) nx ny sa sb` THEN
  UNDISCH_TAC `ov_sup_holds sa nx ny px py` THEN UNDISCH_TAC `ov_sup_holds sb (--nx) (--ny) rx ry` THEN
  REWRITE_TAC[ov_axis_ok; ov_sup_holds; ov_g; LET_DEF; LET_END_DEF; OV_HOLDS_REAL;
              ovr_c; ovr_s; ovr_d; ovr_n; ovr_m] THEN
  RULE_ASSUM_TAC(REWRITE_RULE OV_INT_RULES) THEN REWRITE_TAC OV_INT_RULES THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let OV_AXES_SOUND = prove
 (`forall ra rb ex ey px py rx ry a b rowsA rowsB.
     ov_ref_ok a ra /\ ov_ref_ok b rb /\ ov_ang_sem rowsA ex /\ ov_ang_sem rowsB ey /\
     ova_angle ex = ova_angle ey /\
     (forall r. MEM r rowsA ==> cr_holds r px py) /\ (forall r. MEM r rowsB ==> cr_holds r rx ry) /\
     ov_axes ra rb ex ey
     ==> forall ux uy. MEM (ux,uy) [(ae_c (s12_angles (ova_angle ex)), ae_s (s12_angles (ova_angle ex)));
                             (--ae_c (s12_angles (ova_angle ex)), --ae_s (s12_angles (ova_angle ex)));
                             (--ae_s (s12_angles (ova_angle ex)), ae_c (s12_angles (ova_angle ex)));
                             (ae_s (s12_angles (ova_angle ex)), --ae_c (s12_angles (ova_angle ex)))]
         ==> ux * (rx - px) + uy * (ry - py) <
             rs_rat_radius (ae_reference (s12_angles a) (&1)) ux uy +
             rs_rat_radius (ae_reference (s12_angles b) (&1)) ux uy`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ova_ref ey = ova_ref ex` ASSUME_TAC THENL
   [ASM_MESON_TAC[ov_ang_sem]; ALL_TAC] THEN
  UNDISCH_TAC `ova_angle ex = ova_angle ey` THEN DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(MATCH_MP OV_ENTRY_FACTS (ASSUME `ov_ang_sem rowsA ex`)) THEN STRIP_TAC THEN
  UNDISCH_TAC `ov_ang_sem rowsB ey` THEN REWRITE_TAC[ov_ang_sem] THEN
  DISCH_THEN(MP_TAC o SPECL [`rx:real`; `ry:real`] o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `ov_ang_sem rowsA ex` THEN REWRITE_TAC[ov_ang_sem] THEN
  DISCH_THEN(MP_TAC o SPECL [`px:real`; `py:real`] o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `ov_axes ra rb ex ey` THEN ASM_REWRITE_TAC[ov_axes] THEN STRIP_TAC THEN
  UNDISCH_TAC `ov_ref_ok (ova_angle ex) (ova_ref ex)` THEN
  REWRITE_TAC[ov_ref_ok] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MEM; PAIR_EQ] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (CONJUNCTS_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG; GSYM int_neg_th] THEN REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC OV_AXIS_ENTRY THEN
  MAP_EVERY EXISTS_TAC [`ra:ovref`; `rb:ovref`] THEN ASM_REWRITE_TAC[INT_NEG_NEG] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[int_lt; int_of_num_th]) THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> match snd(strip_comb(concl th)) with
      [_; _; _; _; sa; sb] -> EXISTS_TAC sa THEN EXISTS_TAC sb THEN ASM_REWRITE_TAC[INT_NEG_NEG] THEN NO_TAC
    | _ -> failwith "no"));;

(* reduction of a pair obligation to the inner reference squares *)
let OV_PAIR_FROM_REF = prove
 (`forall src blk n.
     (forall px py rx ry.
        (forall r. MEM r (APPEND (cp_rows src) blk) ==> cr_holds r px py) /\
        (forall r. MEM r (cp_rows n) ==> cr_holds r rx ry)
        ==> exists P. psub P (px,py) IN rs_sqset (ae_reference (s12_angles (cp_angle src)) (&1)) /\
                psub P (rx,ry) IN rs_sqset (ae_reference (s12_angles (cp_angle n)) (&1)))
     ==> cr_pair_overlaps src blk n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[cr_pair_overlaps; pose_realizes] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`lcx cq sq uq vq aq`; `lcy cq sq uq vq aq`;
                                `lcx ct st ut vt aT`; `lcy ct st ut vt aT`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MEM_APPEND] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CR_CENTRE_HOLDS]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real#real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`FST(P:real#real)`; `SND(P:real#real)`] THEN
  REWRITE_TAC[GSYM IN_SQSET] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[cr_leaf; pl_angle_th]) THEN ASM_MESON_TAC[]);;

(* Lean: IndexedCommonGroups.pointGroup / IndexedCommonPoint.point_sound *)
let OV_PAIR_PT = prove
 (`forall src blk n eA eB X Y W.
     ov_ang_sem (APPEND (cp_rows src) blk) eA /\ ova_angle eA = cp_angle src /\
     ov_ang_sem (cp_rows n) eB /\ ova_angle eB = cp_angle n /\
     ov_pt_ok eA X Y W /\ ov_pt_ok eB X Y W
     ==> cr_pair_overlaps src blk n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC OV_PAIR_FROM_REF THEN
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `(real_of_int X / real_of_int W, real_of_int Y / real_of_int W)` THEN
  CONJ_TAC THEN MATCH_MP_TAC OV_PT_ENTRY_A THEN ASM_MESON_TAC[]);;

(* Lean: IndexedCommonGroups.fallbackGroup / RawSupportFan.pair_sound *)
let OV_PAIR_AX = prove
 (`forall src blk n e1 e2 e3 e4.
     ov_ang_sem (APPEND (cp_rows src) blk) e1 /\ ova_angle e1 = cp_angle src /\
     ov_ang_sem (APPEND (cp_rows src) blk) e2 /\ ova_angle e2 = cp_angle n /\
     ov_ang_sem (cp_rows n) e3 /\ ova_angle e3 = cp_angle src /\
     ov_ang_sem (cp_rows n) e4 /\ ova_angle e4 = cp_angle n /\
     ov_axes (ova_ref e1) (ova_ref e4) e1 e3 /\ ov_axes (ova_ref e1) (ova_ref e4) e2 e4
     ==> cr_pair_overlaps src blk n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC OV_PAIR_FROM_REF THEN
  MAP_EVERY X_GEN_TAC [`px:real`; `py:real`; `rx:real`; `ry:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `a = cp_angle src` THEN ABBREV_TAC `b = cp_angle n` THEN
  ABBREV_TAC `rowsA = APPEND (cp_rows src) blk` THEN ABBREV_TAC `rowsB = cp_rows n` THEN
  SUBGOAL_THEN `ov_ref_ok a (ova_ref e1) /\ ov_ref_ok b (ova_ref e4) /\
                ae_check (s12_angles a) /\ ae_check (s12_angles b)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OV_ENTRY_FACTS]; ALL_TAC] THEN
  REWRITE_TAC[GSYM overlaps_at] THEN MATCH_MP_TAC AOC_AXISOVERLAPFORMS_SOUND THEN
  ASM_SIMP_TAC[AR_REFERENCE_CHECKED; REAL_LT_01] THEN
  REWRITE_TAC[axis_overlap_forms; pair_axes; MAP; lflat; APPEND; MEM] THEN
  REWRITE_TAC[FST; SND; REAL_NEG_NEG] THEN GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[AOC_AXISGAPFORM_HOLDS] THEN
  MP_TAC(SPECL [`ova_ref e1`; `ova_ref e4`; `e1:ovang`; `e3:ovang`; `px:real`; `py:real`;
                `rx:real`; `ry:real`; `a:num`; `b:num`; `rowsA:crow list`; `rowsB:crow list`]
               OV_AXES_SOUND) THEN
  MP_TAC(SPECL [`ova_ref e1`; `ova_ref e4`; `e2:ovang`; `e4:ovang`; `px:real`; `py:real`;
                `rx:real`; `ry:real`; `a:num`; `b:num`; `rowsA:crow list`; `rowsB:crow list`]
               OV_AXES_SOUND) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[MEM; PAIR_EQ] THEN
  REWRITE_TAC[ae_reference; rs_c; rs_s] THEN MESON_TAC[]);;

(* the per-header obligation from the per-pair theorems (structural) *)
let OV_ALL_MEM = prove
 (`forall P (l:A list). ALL P l ==> forall x. MEM x l ==> P x`,
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[]);;

(* Lean: EmptyContext.Witness.sound for a source context *)
let OV_EMPTY_SOUND = prove
 (`forall src blk ins terms n.
     cr_empty_check (APPEND (cp_rows src) blk) ins terms ==> cr_pair_overlaps src blk n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[cr_pair_overlaps; pose_realizes] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `false ==> p`) THEN MATCH_MP_TAC CR_EMPTY_SOUND THEN
  MAP_EVERY EXISTS_TAC [`APPEND (cp_rows src) blk`; `ins:num list`; `terms:(int#num)list`;
                        `lcx cq sq uq vq aq`; `lcy cq sq uq vq aq`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CR_ROWAT_HOLDS THEN
  REWRITE_TAC[MEM_APPEND] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CR_CENTRE_HOLDS]) THEN ASM_MESON_TAC[]);;

let ov_hdr_ok = new_definition
 `ov_hdr_ok Nd (h:cpose#(crow list)option) <=>
    forall blk. SND h = SOME blk ==> forall n. MEM n Nd ==> cr_pair_overlaps (FST h) blk n`;;

let OV_HDR_NONE = prove
 (`forall Nd src. ov_hdr_ok Nd (src, NONE)`,
  REWRITE_TAC[ov_hdr_ok; distinctness "option"]);;

let OV_HDR_SOME = prove
 (`forall Nd src blk. (forall n. MEM n Nd ==> cr_pair_overlaps src blk n) ==> ov_hdr_ok Nd (src, SOME blk)`,
  REWRITE_TAC[ov_hdr_ok; injectivity "option"] THEN MESON_TAC[]);;

(* Lean: IndexedCommonGroups.block_overlap_headers *)
let OV_BLOCK_OVERLAP = prove
 (`forall hdrs Nd. ALL (ov_hdr_ok Nd) hdrs ==> cr_block_overlap hdrs (MAP cr_leaf Nd)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CR_BLOCK_OVERLAP_OF_PAIRS THEN
  UNDISCH_TAC `ALL (ov_hdr_ok Nd) hdrs` THEN REWRITE_TAC[GSYM ALL_MEM; ov_hdr_ok] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `(src:cpose, SOME (blk:crow list))`) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* the checker equations for CR_EVAL_CONV *)
let OV_REF_EQS = Array.to_list (Array.mapi (fun i r ->
   let th = (REWRITE_CONV[ov_ref; ov_refs] THENC EL_CONV) (mk_comb (`ov_ref`, mk_small_numeral i)) in
   if rhs (concl th) <> r then failwith "OV_REF_EQS" else th) ov_ref_tms);;

let () =
  cr_extra_thms := !cr_extra_thms @ OV_REF_EQS @
   [ovr_c; ovr_s; ovr_d; ovr_n; ovr_m; ovs_k; ovs_e; ovs_s;
    ova_angle; ova_ref; ova_s0; ova_s1; ova_s2; ova_s3;
    ov_sup_check; ov_ang_check; ov_pt_sup; ov_pt_ok; ov_g; ov_axis_ok; ov_axes;
    injectivity "ovref"; injectivity "ovsup"; injectivity "ovang"];
  cr_cs_reset ();;
