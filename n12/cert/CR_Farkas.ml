(* ========================================================================= *)
(* Certificate layer, part 2 (F1): 2-D integer Farkas combinations with     *)
(* strictness tracked.                                                       *)
(* Lean: Compact/Core/IntegerSupport.lean (TwoRow, TwoRow.Check.sound),      *)
(*       Compact/Core/SparseInteger.lean (zero, sum, sum_sound, Certificate, *)
(*       Certificate.Check.sound, refutes),                                  *)
(*       Compact/Core/PairSupport.lean (cramer),                             *)
(*       Compact/Core/RowSupport.lean (one, certificate, Check, sound),      *)
(*       Compact/Core/RelaxationHints.lean (rowAt, single/constant, Hint,    *)
(*       Hint.Check, Hint.sound, Check, sound),                              *)
(*       Compact/Core/EmptyContext.lean (Witness.Check, Witness.sound).      *)
(* The checking functions are executable HOL functions on integer literals;  *)
(* they are evaluated by CR_EVAL_CONV (CR_Eval.ml).                          *)
(* ========================================================================= *)

needs "n12/cert/CR_Row.ml";;

(* Lean: SparseInteger.zero *)
let cr_zero = new_definition `cr_zero = CRow (&0) (&0) (&0) false`;;
(* Lean: RowSupport.one *)
let cr_one = new_definition `cr_one = CRow (&0) (&0) (&1) true`;;

let CR_ZERO_HOLDS = prove
 (`forall px py. cr_holds cr_zero px py`,
  REWRITE_TAC[cr_zero; cr_holds; cr_eval; cr_x; cr_y; cr_c; cr_s; int_of_num_th] THEN
  REAL_ARITH_TAC);;

let CR_ONE_HOLDS = prove
 (`forall px py. cr_holds cr_one px py`,
  REWRITE_TAC[cr_one; cr_holds; cr_eval; cr_x; cr_y; cr_c; cr_s; int_of_num_th] THEN
  REAL_ARITH_TAC);;

(* Lean: RelaxationHints.rowAt  (rws[index]?.getD zero) *)
let cr_rowat = new_definition
 `cr_rowat (rws:crow list) i = if i < LENGTH rws then EL i rws else cr_zero`;;

let CR_ROWAT_HOLDS = prove
 (`forall rws i px py. (forall r. MEM r rws ==> cr_holds r px py) ==> cr_holds (cr_rowat rws i) px py`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cr_rowat] THEN COND_CASES_TAC THEN
  ASM_MESON_TAC[MEM_EL; CR_ZERO_HOLDS]);;

let CR_ROWAT_MEM = prove
 (`forall rws i. i < LENGTH rws ==> MEM (cr_rowat rws i) rws`,
  SIMP_TAC[cr_rowat; MEM_EL]);;

(* ------------------------------------------------------------------------- *)
(* TwoRow                                                                    *)
(* ------------------------------------------------------------------------- *)

(* Lean: TwoRow.Check  (w = ⟨left, right, scale⟩) *)
let cr_tworow_check = new_definition
 `cr_tworow_check (wl:int) (wr:int) (sc:int) a b t <=>
    &0 <= wl /\ &0 <= wr /\ &0 < sc /\
    wl * cr_x a + wr * cr_x b = sc * cr_x t /\
    wl * cr_y a + wr * cr_y b = sc * cr_y t /\
    wl * cr_c a + wr * cr_c b = sc * cr_c t /\
    (cr_s t ==> (&0 < wl /\ cr_s a) \/ (&0 < wr /\ cr_s b))`;;

let CR_SIGN_LEMMA = prove
 (`forall wl wr sc ea eb et.
     &0 <= wl /\ &0 <= wr /\ &0 < sc /\ wl * ea + wr * eb = sc * et /\
     &0 <= ea /\ &0 <= eb
     ==> &0 <= et /\ ((&0 < wl /\ &0 < ea) \/ (&0 < wr /\ &0 < eb) ==> &0 < et)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= wl * ea /\ &0 <= wr * eb` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  MP_TAC(SPECL [`&0`; `et:real`; `sc:real`] REAL_LE_LMUL_EQ) THEN
  MP_TAC(SPECL [`&0`; `et:real`; `sc:real`] REAL_LT_LMUL_EQ) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th))) THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(SPECL [`wl:real`; `ea:real`] REAL_LT_MUL);
    MP_TAC(SPECL [`wr:real`; `eb:real`] REAL_LT_MUL)] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CR_EVAL_IDENTITY = prove
 (`forall wl wr sc ax ay ac bx by bc tx ty tc px py:real.
     wl * ax + wr * bx = sc * tx /\ wl * ay + wr * by = sc * ty /\ wl * ac + wr * bc = sc * tc
     ==> wl * (ax * px + ay * py + ac) + wr * (bx * px + by * py + bc) =
         sc * (tx * px + ty * py + tc)`,
  CONV_TAC REAL_RING);;

let INT_REAL_RULES = [int_le; int_lt; int_eq; int_add_th; int_mul_th; int_of_num_th;
                      int_sub_th; int_neg_th];;

(* Lean: TwoRow.Check.sound *)
let CR_TWOROW_SOUND = prove
 (`forall wl wr sc a b t px py.
     cr_tworow_check wl wr sc a b t /\ cr_holds a px py /\ cr_holds b px py
     ==> cr_holds t px py`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cr_tworow_check] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`real_of_int wl`; `real_of_int wr`; `real_of_int sc`;
                `cr_eval a px py`; `cr_eval b px py`; `cr_eval t px py`] CR_SIGN_LEMMA) THEN
  RULE_ASSUM_TAC(REWRITE_RULE INT_REAL_RULES) THEN
  ASM_SIMP_TAC[CR_HOLDS_NONNEG] THEN ANTS_TAC THENL
   [REWRITE_TAC[cr_eval] THEN MATCH_MP_TAC CR_EVAL_IDENTITY THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[cr_holds] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME `cr_s t`))) THEN
  STRIP_TAC THEN ASM_SIMP_TAC[CR_HOLDS_POS]);;

(* ------------------------------------------------------------------------- *)
(* Sparse sums and certificates                                              *)
(* ------------------------------------------------------------------------- *)

(* Lean: SparseInteger.sum (rws : Fin n -> Row is the list rws, read by rowAt) *)
let cr_sum = define
 `(cr_sum rws [] = cr_zero) /\
  (cr_sum rws (CONS (t:int#num) ts) =
     let tl = cr_sum rws ts in
     let r = cr_rowat rws (SND t) in
     CRow (FST t * cr_x r + cr_x tl) (FST t * cr_y r + cr_y tl) (FST t * cr_c r + cr_c tl)
          ((&0 < FST t /\ cr_s r) \/ cr_s tl))`;;

(* Lean: SparseInteger.Nonnegative *)
let cr_nonneg = new_definition `cr_nonneg (terms:(int#num)list) <=> ALL (\t. &0 <= FST t) terms`;;

(* Lean: SparseInteger.sum_sound (only the cited rws need to hold) *)
let CR_SUM_SOUND = prove
 (`forall rws terms px py.
     cr_nonneg terms /\ (forall t. MEM t terms ==> cr_holds (cr_rowat rws (SND t)) px py)
     ==> cr_holds (cr_sum rws terms) px py`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[cr_sum; CR_ZERO_HOLDS; cr_nonneg; ALL; MEM] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
  MATCH_MP_TAC CR_TWOROW_SOUND THEN
  MAP_EVERY EXISTS_TAC [`FST (h:int#num)`; `&1:int`; `&1:int`;
                        `cr_rowat rws (SND (h:int#num))`; `cr_sum rws t`] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[cr_tworow_check; cr_x; cr_y; cr_c; cr_s] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INT_MUL_LID; INT_POS; INT_LT_01] THEN CONV_TAC TAUT;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[cr_nonneg] THEN ASM_MESON_TAC[]]);;

(* Lean: Certificate.Check  (terms, scale) *)
let cr_cert_check = new_definition
 `cr_cert_check terms (scale:int) rws t <=>
    cr_nonneg terms /\ cr_tworow_check (&1) (&0) scale (cr_sum rws terms) cr_zero t`;;

(* Lean: Certificate.Check.sound *)
let CR_CERT_SOUND = prove
 (`forall terms scale rws t px py.
     cr_cert_check terms scale rws t /\
     (forall x. MEM x terms ==> cr_holds (cr_rowat rws (SND x)) px py)
     ==> cr_holds t px py`,
  REWRITE_TAC[cr_cert_check] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CR_TWOROW_SOUND THEN
  MAP_EVERY EXISTS_TAC [`&1:int`; `&0:int`; `scale:int`; `cr_sum rws terms`; `cr_zero`] THEN
  ASM_SIMP_TAC[CR_ZERO_HOLDS; CR_SUM_SOUND]);;

let CR_CERT_SOUND_ALL = prove
 (`forall terms scale rws t px py.
     cr_cert_check terms scale rws t /\ (forall r. MEM r rws ==> cr_holds r px py)
     ==> cr_holds t px py`,
  MESON_TAC[CR_CERT_SOUND; CR_ROWAT_HOLDS]);;

(* Lean: SparseInteger.refutes *)
let CR_REFUTES = prove
 (`forall terms scale rws px py.
     cr_cert_check terms scale rws (CRow (&0) (&0) (&0) true) /\
     (forall x. MEM x terms ==> cr_holds (cr_rowat rws (SND x)) px py) ==> false`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`terms:(int#num)list`; `scale:int`; `rws:crow list`;
                `CRow (&0) (&0) (&0) true`; `px:real`; `py:real`] CR_CERT_SOUND) THEN
  ASM_REWRITE_TAC[cr_holds; cr_eval; cr_x; cr_y; cr_c; cr_s; int_of_num_th] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Two-row support (RowSupport), single and constant hints                   *)
(* ------------------------------------------------------------------------- *)

(* Lean: PairSupport.cramer  (result (left, right, scale)) *)
let cr_cramer = new_definition
 `cr_cramer a b (x:int) (y:int) =
    let det = cr_x a * cr_y b - cr_y a * cr_x b in
    let sg = if &0 <= det then &1 else -- &1 in
    (sg * (x * cr_y b - y * cr_x b), sg * (cr_x a * y - cr_y a * x), sg * det)`;;

(* Lean: RowSupport.Check  (certificate a b target on sourceRows = [a; b; one]) *)
let cr_rs_check = new_definition
 `cr_rs_check a b t <=>
    let w = cr_cramer a b (cr_x t) (cr_y t) in
    cr_cert_check
      [(FST w, 0); (FST (SND w), 1);
       (SND (SND w) * cr_c t - FST w * cr_c a - FST (SND w) * cr_c b, 2)]
      (SND (SND w)) [a; b; cr_one] t`;;

let CR_MEM3_HOLDS = prove
 (`forall a b px py. cr_holds a px py /\ cr_holds b px py
     ==> forall r. MEM r [a; b; cr_one] ==> cr_holds r px py`,
  REWRITE_TAC[MEM] THEN MESON_TAC[CR_ONE_HOLDS]);;

(* Lean: RowSupport.sound *)
let CR_RS_SOUND = prove
 (`forall a b t px py. cr_rs_check a b t /\ cr_holds a px py /\ cr_holds b px py
     ==> cr_holds t px py`,
  REWRITE_TAC[cr_rs_check; LET_DEF; LET_END_DEF] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CR_CERT_SOUND_ALL THEN
  MAP_EVERY EXISTS_TAC [`[(FST (cr_cramer a b (cr_x t) (cr_y t)),0);
      (FST (SND (cr_cramer a b (cr_x t) (cr_y t))),1);
      (SND (SND (cr_cramer a b (cr_x t) (cr_y t))) * cr_c t -
       FST (cr_cramer a b (cr_x t) (cr_y t)) * cr_c a -
       FST (SND (cr_cramer a b (cr_x t) (cr_y t))) * cr_c b,2)]`;
    `SND (SND (cr_cramer a b (cr_x t) (cr_y t)))`; `[a; b; cr_one]`] THEN
  ASM_SIMP_TAC[CR_MEM3_HOLDS]);;

(* Lean: RelaxationHints.singleCertificate / SingleCheck *)
let cr_single_check = new_definition
 `cr_single_check src t <=>
    let pivot = if cr_x src = &0 then cr_y src else cr_x src in
    let comp = if cr_x src = &0 then cr_y t else cr_x t in
    let scale = abs pivot in
    let w = if pivot < &0 then --comp else comp in
    cr_cert_check [(w, 0); (scale * cr_c t - w * cr_c src, 1)] scale [src; cr_one] t`;;

(* Lean: RelaxationHints.single_sound *)
let CR_SINGLE_SOUND = prove
 (`forall src t px py. cr_single_check src t /\ cr_holds src px py ==> cr_holds t px py`,
  REWRITE_TAC[cr_single_check; LET_DEF; LET_END_DEF] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CR_CERT_SOUND_ALL THEN
  FIRST_ASSUM(fun th -> MAP_EVERY EXISTS_TAC
    (let l = snd(strip_comb(concl th)) in [el 0 l; el 1 l; el 2 l])) THEN
  ASM_REWRITE_TAC[MEM] THEN ASM_MESON_TAC[CR_ONE_HOLDS]);;

(* Lean: RelaxationHints.constantCertificate / ConstantCheck *)
let cr_const_check = new_definition
 `cr_const_check t <=> cr_cert_check [(cr_c t, 0)] (&1) [cr_one] t`;;

(* Lean: RelaxationHints.constant_sound *)
let CR_CONST_SOUND = prove
 (`forall t px py. cr_const_check t ==> cr_holds t px py`,
  REWRITE_TAC[cr_const_check] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CR_CERT_SOUND_ALL THEN
  MAP_EVERY EXISTS_TAC [`[(cr_c t, 0)]`; `&1:int`; `[cr_one]`] THEN
  ASM_REWRITE_TAC[MEM] THEN MESON_TAC[CR_ONE_HOLDS]);;

(* Lean: RelaxationHints.Hint *)
let crhint_INDUCT,crhint_RECURSION = define_type
  "crhint = RhConst | RhCopy num | RhSingle num | RhPair num num";;

(* Lean: RelaxationHints.Hint.Check *)
let cr_hint_check = define
 `(cr_hint_check RhConst srcs t <=> cr_const_check t) /\
  (cr_hint_check (RhCopy i) srcs t <=> i < LENGTH srcs /\ cr_rowat srcs i = t) /\
  (cr_hint_check (RhSingle i) srcs t <=> i < LENGTH srcs /\ cr_single_check (cr_rowat srcs i) t) /\
  (cr_hint_check (RhPair i j) srcs t <=>
     i < LENGTH srcs /\ j < LENGTH srcs /\ cr_rs_check (cr_rowat srcs i) (cr_rowat srcs j) t)`;;

(* Lean: RelaxationHints.Hint.sound *)
let CR_HINT_SOUND = prove
 (`forall h srcs t px py. cr_hint_check h srcs t /\ (forall r. MEM r srcs ==> cr_holds r px py)
     ==> cr_holds t px py`,
  MATCH_MP_TAC crhint_INDUCT THEN REWRITE_TAC[cr_hint_check] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[CR_CONST_SOUND];
    ASM_MESON_TAC[CR_ROWAT_MEM];
    ASM_MESON_TAC[CR_SINGLE_SOUND; CR_ROWAT_MEM];
    ASM_MESON_TAC[CR_RS_SOUND; CR_ROWAT_MEM]]);;

(* Lean: RelaxationHints.Check (one hint per target, in order) *)
let cr_hints_check = define
 `(cr_hints_check srcs [] [] <=> true) /\
  (cr_hints_check srcs [] (CONS (h:crhint) hs) <=> false) /\
  (cr_hints_check srcs (CONS t ts) [] <=> false) /\
  (cr_hints_check srcs (CONS t ts) (CONS h hs) <=>
     cr_hint_check h srcs t /\ cr_hints_check srcs ts hs)`;;

(* Lean: RelaxationHints.sound *)
let CR_HINTS_SOUND = prove
 (`forall srcs targets hints px py.
     cr_hints_check srcs targets hints /\ (forall r. MEM r srcs ==> cr_holds r px py)
     ==> forall t. MEM t targets ==> cr_holds t px py`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[cr_hints_check] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[CR_HINT_SOUND]);;

(* ------------------------------------------------------------------------- *)
(* Empty contexts                                                            *)
(* ------------------------------------------------------------------------- *)

(* Lean: EmptyContext.Witness.Check  (rws : Fin n -> Row as a list, inputs, terms) *)
let cr_empty_check = new_definition
 `cr_empty_check rws (inputs:num list) terms <=>
    cr_nonneg terms /\ ALL (\t:int#num. MEM (SND t) inputs) terms /\
    (let s = cr_sum rws terms in
     cr_x s = &0 /\ cr_y s = &0 /\ (cr_c s < &0 \/ (cr_c s <= &0 /\ cr_s s)))`;;

(* Lean: EmptyContext.Witness.sound *)
let CR_EMPTY_SOUND = prove
 (`forall rws inputs terms px py.
     cr_empty_check rws inputs terms /\
     (forall i. MEM i inputs ==> cr_holds (cr_rowat rws i) px py) ==> false`,
  REWRITE_TAC[cr_empty_check; LET_DEF; LET_END_DEF; GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`rws:crow list`; `terms:(int#num)list`; `px:real`; `py:real`] CR_SUM_SOUND) THEN
  (ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE INT_REAL_RULES) THEN
  REWRITE_TAC[cr_holds; cr_eval] THEN ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;
