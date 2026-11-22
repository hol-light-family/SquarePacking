(* ========================================================================= *)
(* Port of Compact/Geometry/C849NegativePositiveMargins.lean                 *)
(* (namespace N12Compact.C849NegativePositiveMargins).                       *)
(* Positive-left-frame support margins for negative B: two-angle polynomial  *)
(* inequalities via half-angle substitutions and Bernstein certificates.     *)
(* The certificate identities are checked by REAL_RING.                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: margin0 (def) *)
let C849NPM_MARGIN0_DEF = new_definition
 `c849npm_margin0 (c:real) (t:real) (C:real) (S:real) =
    C pow 2 * (&2 - c - (&7 / &20) * t pow 2 - (&3 / &20) * c * t) +
    C * S * ((&63 / &100) + t - (&7 / &20) * c * t - (&3 / &20) * c pow 2) +
    (&19 / &25) * S pow 2 - C - S`;;

(* Lean: margin1 (def) *)
let C849NPM_MARGIN1_DEF = new_definition
 `c849npm_margin1 (c:real) (t:real) (C:real) (S:real) =
    C pow 2 * ((&113 / &50) - (&61 / &100) * t pow 2 - (&13 / &20) * c * t - c) +
    C * S * ((&113 / &100) - (&61 / &100) * c * t - (&13 / &20) * c pow 2 + t) +
    (&19 / &25) * S pow 2 - C - S`;;

(* Lean: margin2 (def) *)
let C849NPM_MARGIN2_DEF = new_definition
 `c849npm_margin2 (c:real) (t:real) (C:real) (S:real) =
    C pow 2 * (&2 + (&13 / &50) * t pow 2 + (&1 / &2) * c * t - c - t) +
    C * S * ((&63 / &100) + (&13 / &50) * c * t + (&1 / &2) * c pow 2 + t - c) +
    (&19 / &25) * S pow 2 - C - S`;;

(* Lean: certificate0 (private def) *)
let C849NPM_CERTIFICATE0_DEF = new_definition
 `c849npm_certificate0 (x:real) (y:real) =
    (&449280000 * (&12 * y) * (&5 - &12 * y) pow 3 + &1160640000 * (&12 * y) pow 2 * (&5
    - &12 * y) pow 2 + &1195440000 * (&12 * y) pow 3 * (&5 - &12 * y) + &421580000 *
    (&12 * y) pow 4) * (&3 - &10 * x) pow 4 + (&93312000 * (&5 - &12 * y) pow 4 +
    &1833408000 * (&12 * y) * (&5 - &12 * y) pow 3 + &4159152000 * (&12 * y) pow 2 * (&5
    - &12 * y) pow 2 + &4137828000 * (&12 * y) pow 3 * (&5 - &12 * y) + &1471584500 *
    (&12 * y) pow 4) * (&10 * x) * (&3 - &10 * x) pow 3 + (&223948800 * (&5 - &12 * y)
    pow 4 + &2614809600 * (&12 * y) * (&5 - &12 * y) pow 3 + &5266080000 * (&12 * y) pow
    2 * (&5 - &12 * y) pow 2 + &5139086400 * (&12 * y) pow 3 * (&5 - &12 * y) +
    &1884367200 * (&12 * y) pow 4) * (&10 * x) pow 2 * (&3 - &10 * x) pow 2 +
    (&159563520 * (&5 - &12 * y) pow 4 + &1429937280 * (&12 * y) * (&5 - &12 * y) pow 3
    + &2460834720 * (&12 * y) pow 2 * (&5 - &12 * y) pow 2 + &2440666680 * (&12 * y) pow
    3 * (&5 - &12 * y) + &982515095 * (&12 * y) pow 4) * (&10 * x) pow 3 * (&3 - &10 *
    x) + (&12130560 * (&5 - &12 * y) pow 4 + &135710208 * (&12 * y) * (&5 - &12 * y) pow
    3 + &107722944 * (&12 * y) pow 2 * (&5 - &12 * y) pow 2 + &198130704 * (&12 * y) pow
    3 * (&5 - &12 * y) + &140096783 * (&12 * y) pow 4) * (&10 * x) pow 4`;;

(* Lean: certificate1 (private def) *)
let C849NPM_CERTIFICATE1_DEF = new_definition
 `c849npm_certificate1 (x:real) (y:real) =
    (&11511631872 * (&5 - &12 * y) pow 4 + &54737952768 * (&12 * y) * (&5 - &12 * y) pow
    3 + &55561001472 * (&12 * y) pow 2 * (&5 - &12 * y) pow 2 + &48474544128 * (&12 * y)
    pow 3 * (&5 - &12 * y) + &24605833552 * (&12 * y) pow 4) * (&7 - &20 * x) pow 4 +
    (&51495284736 * (&5 - &12 * y) pow 4 + &223264733184 * (&12 * y) * (&5 - &12 * y)
    pow 3 + &198639438336 * (&12 * y) pow 2 * (&5 - &12 * y) pow 2 + &161719592064 *
    (&12 * y) pow 3 * (&5 - &12 * y) + &88223712176 * (&12 * y) pow 4) * (&20 * x - &6)
    * (&7 - &20 * x) pow 3 + (&84391538688 * (&5 - &12 * y) pow 4 + &335824745472 * (&12
    * y) * (&5 - &12 * y) pow 3 + &252239781888 * (&12 * y) pow 2 * (&5 - &12 * y) pow 2
    + &186769010112 * (&12 * y) pow 3 * (&5 - &12 * y) + &115194565008 * (&12 * y) pow
    4) * (&20 * x - &6) pow 2 * (&7 - &20 * x) pow 2 + (&60260557824 * (&5 - &12 * y)
    pow 4 + &220429472256 * (&12 * y) * (&5 - &12 * y) pow 3 + &130195914624 * (&12 * y)
    pow 2 * (&5 - &12 * y) pow 2 + &81873847776 * (&12 * y) pow 3 * (&5 - &12 * y) +
    &64048650084 * (&12 * y) pow 4) * (&20 * x - &6) pow 3 * (&7 - &20 * x) +
    (&15850328832 * (&5 - &12 * y) pow 4 + &53122583808 * (&12 * y) * (&5 - &12 * y) pow
    3 + &21022484832 * (&12 * y) pow 2 * (&5 - &12 * y) pow 2 + &8343335568 * (&12 * y)
    pow 3 * (&5 - &12 * y) + &12470785087 * (&12 * y) pow 4) * (&20 * x - &6) pow 4`;;

(* Lean: certificate2 (private def) *)
let C849NPM_CERTIFICATE2_DEF = new_definition
 `c849npm_certificate2 (x:real) (y:real) =
    (&779341824 * (&12 * y) * (&5 - &12 * y) pow 5 + &3702620160 * (&12 * y) pow 2 * (&5
    - &12 * y) pow 4 + &7192800000 * (&12 * y) pow 3 * (&5 - &12 * y) pow 3 +
    &7091297280 * (&12 * y) pow 4 * (&5 - &12 * y) pow 2 + &3517966080 * (&12 * y) pow 5
    * (&5 - &12 * y) + &696190464 * (&12 * y) pow 6) * (&5 - &12 * x) pow 4 +
    (&447897600 * (&5 - &12 * y) pow 6 + &4864167936 * (&12 * y) * (&5 - &12 * y) pow 5
    + &16670499840 * (&12 * y) pow 2 * (&5 - &12 * y) pow 4 + &27864518400 * (&12 * y)
    pow 3 * (&5 - &12 * y) pow 3 + &25248071520 * (&12 * y) pow 4 * (&5 - &12 * y) pow 2
    + &11951133120 * (&12 * y) pow 5 * (&5 - &12 * y) + &2313350496 * (&12 * y) pow 6) *
    (&12 * x) * (&5 - &12 * x) pow 3 + (&776355840 * (&5 - &12 * y) pow 6 + &6783035904
    * (&12 * y) * (&5 - &12 * y) pow 5 + &20768348160 * (&12 * y) pow 2 * (&5 - &12 * y)
    pow 4 + &32375484000 * (&12 * y) pow 3 * (&5 - &12 * y) pow 3 + &28313484480 * (&12
    * y) pow 4 * (&5 - &12 * y) pow 2 + &13316865120 * (&12 * y) pow 5 * (&5 - &12 * y)
    + &2617196544 * (&12 * y) pow 6) * (&12 * x) pow 2 * (&5 - &12 * x) pow 2 +
    (&442298880 * (&5 - &12 * y) pow 6 + &3394711296 * (&12 * y) * (&5 - &12 * y) pow 5
    + &9274357440 * (&12 * y) pow 2 * (&5 - &12 * y) pow 4 + &13327822800 * (&12 * y)
    pow 3 * (&5 - &12 * y) pow 3 + &11359084770 * (&12 * y) pow 4 * (&5 - &12 * y) pow 2
    + &5512367700 * (&12 * y) pow 5 * (&5 - &12 * y) + &1159160706 * (&12 * y) pow 6) *
    (&12 * x) pow 3 * (&5 - &12 * x) + (&49040640 * (&5 - &12 * y) pow 6 + &277191504 *
    (&12 * y) * (&5 - &12 * y) pow 5 + &365988960 * (&12 * y) pow 2 * (&5 - &12 * y) pow
    4 + &104229075 * (&12 * y) pow 3 * (&5 - &12 * y) pow 3 + &65283905 * (&12 * y) pow
    4 * (&5 - &12 * y) pow 2 + &190122745 * (&12 * y) pow 5 * (&5 - &12 * y) + &91229819
    * (&12 * y) pow 6) * (&12 * x) pow 4`;;

(* Positivity of a sum of products of powers of nonnegative linear factors. *)
let C849NPM_POS_TAC =
  REPEAT(FIRST [MATCH_ACCEPT_TAC REAL_POS;
                MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC;
                MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC;
                MATCH_MP_TAC REAL_POW_LE]) THEN
  ASM_REAL_ARITH_TAC;;

let C849NPM_SIGN = prove
 (`forall m P. &0 < P /\ &0 <= --m * P ==> m <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN NLIN_TAC []);;

let C849NPM_DEN_TAC =
  REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN TRY(MATCH_MP_TAC REAL_POW_LT) THEN
  (REAL_ARITH_TAC ORELSE
   (MATCH_MP_TAC(REAL_ARITH `forall z. &0 <= z ==> &0 < &1 + z`) THEN REWRITE_TAC[REAL_LE_POW_2]));;

(* Lean: half_angle (private) *)
let C849NPM_HALF_ANGLE = prove
 (`forall p q. &0 < p /\ &0 <= q /\ p pow 2 + q pow 2 = &1 /\ q <= p
         ==> &0 <= q / (&1 + p) /\ q / (&1 + p) <= &5 / &12 /\
             p * (&1 + (q / (&1 + p)) pow 2) = &1 - (q / (&1 + p)) pow 2 /\
             q * (&1 + (q / (&1 + p)) pow 2) = &2 * (q / (&1 + p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + p` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `q - &5 / &7`] [`&0 <= (p - q) * (p + q)`; `q <= &5 / &7`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN UNDISCH_TAC `&0 < &1 + p` THEN
    CONV_TAC REAL_FIELD;
    UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN UNDISCH_TAC `&0 < &1 + p` THEN
    CONV_TAC REAL_FIELD]);;

(* Lean: check0 (private) *)
let C849NPM_CHECK0 = prove
 (`forall c t C S x y. &0 <= x /\ x <= &3 / &10 /\ &0 <= y /\ y <= &5 / &12 /\
     c * (&1 + x pow 2) = &1 - x pow 2 /\ t * (&1 + x pow 2) = &2 * x /\
     C * (&1 + y pow 2) = &1 - y pow 2 /\ S * (&1 + y pow 2) = &2 * y
     ==> c849npm_margin0 c t C S <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(--(c849npm_margin0 c t C S)) * (&1 + x pow 2) pow 2 * (&1 + y pow 2) pow 2 *
    &52488000000000 = c849npm_certificate0 x y` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`c * (&1 + x pow 2) = &1 - x pow 2`; `t * (&1 + x pow 2) = &2 * x`;
      `C * (&1 + y pow 2) = &1 - y pow 2`; `S * (&1 + y pow 2) = &2 * y`] THEN
    REWRITE_TAC[C849NPM_MARGIN0_DEF; C849NPM_CERTIFICATE0_DEF] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC C849NPM_SIGN THEN
  EXISTS_TAC `(&1 + x pow 2) pow 2 * (&1 + y pow 2) pow 2 * &52488000000000` THEN
  CONJ_TAC THENL [C849NPM_DEN_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[C849NPM_CERTIFICATE0_DEF] THEN C849NPM_POS_TAC);;

(* Lean: check1 (private) *)
let C849NPM_CHECK1 = prove
 (`forall c t C S x y. &3 / &10 <= x /\ x <= &7 / &20 /\ &0 <= y /\ y <= &5 / &12 /\
     c * (&1 + x pow 2) = &1 - x pow 2 /\ t * (&1 + x pow 2) = &2 * x /\
     C * (&1 + y pow 2) = &1 - y pow 2 /\ S * (&1 + y pow 2) = &2 * y
     ==> c849npm_margin1 c t C S <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(--(c849npm_margin1 c t C S)) * (&1 + x pow 2) pow 2 * (&1 + y pow 2) pow 2 *
    &103680000000000 = c849npm_certificate1 x y` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`c * (&1 + x pow 2) = &1 - x pow 2`; `t * (&1 + x pow 2) = &2 * x`;
      `C * (&1 + y pow 2) = &1 - y pow 2`; `S * (&1 + y pow 2) = &2 * y`] THEN
    REWRITE_TAC[C849NPM_MARGIN1_DEF; C849NPM_CERTIFICATE1_DEF] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC C849NPM_SIGN THEN
  EXISTS_TAC `(&1 + x pow 2) pow 2 * (&1 + y pow 2) pow 2 * &103680000000000` THEN
  CONJ_TAC THENL [C849NPM_DEN_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[C849NPM_CERTIFICATE1_DEF] THEN C849NPM_POS_TAC);;

(* Lean: check2 (private) *)
let C849NPM_CHECK2 = prove
 (`forall c t C S x y. &0 <= x /\ x <= &5 / &12 /\ &0 <= y /\ y <= &5 / &12 /\
     c * (&1 + x pow 2) = &1 - x pow 2 /\ t * (&1 + x pow 2) = &2 * x /\
     C * (&1 + y pow 2) = &1 - y pow 2 /\ S * (&1 + y pow 2) = &2 * y
     ==> c849npm_margin2 c t C S <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(--(c849npm_margin2 c t C S)) * (&1 + x pow 2) pow 2 * (&1 + y pow 2) pow 2 *
    &10497600000000000 = c849npm_certificate2 x y` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`c * (&1 + x pow 2) = &1 - x pow 2`; `t * (&1 + x pow 2) = &2 * x`;
      `C * (&1 + y pow 2) = &1 - y pow 2`; `S * (&1 + y pow 2) = &2 * y`] THEN
    REWRITE_TAC[C849NPM_MARGIN2_DEF; C849NPM_CERTIFICATE2_DEF] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC C849NPM_SIGN THEN
  EXISTS_TAC `(&1 + x pow 2) pow 2 * (&1 + y pow 2) pow 2 * &10497600000000000` THEN
  CONJ_TAC THENL [C849NPM_DEN_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[C849NPM_CERTIFICATE2_DEF] THEN C849NPM_POS_TAC);;

(* Lean: upperU *)
let C849NPM_UPPERU = prove
 (`forall c t C S. &0 < c /\ &0 <= t /\ c pow 2 + t pow 2 = &1 /\ t <= c /\
             &0 < C /\ &0 <= S /\ C pow 2 + S pow 2 = &1 /\ S <= C /\ &50 / &63 <= c
             ==> c849npm_margin0 c t C S <= &0 \/ c849npm_margin1 c t C S <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] C849NPM_HALF_ANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`C:real`; `S:real`] C849NPM_HALF_ANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `x = t / (&1 + c)` THEN ABBREV_TAC `y = S / (&1 + C)` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `x:real`; SQ_NONNEG `x - &7 / &20`]
   [`&0 <= (c - &50 / &63) * (&1 + x pow 2)`; `x <= &7 / &20`] THEN
  ASM_CASES_TAC `x <= &3 / &10` THENL
   [DISJ1_TAC THEN MATCH_MP_TAC C849NPM_CHECK0 THEN
    MAP_EVERY EXISTS_TAC [`x:real`; `y:real`] THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN MATCH_MP_TAC C849NPM_CHECK1 THEN
    MAP_EVERY EXISTS_TAC [`x:real`; `y:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* Lean: upperV *)
let C849NPM_UPPERV = prove
 (`forall c t C S. &0 < c /\ &0 <= t /\ c pow 2 + t pow 2 = &1 /\ t <= c /\
             &0 < C /\ &0 <= S /\ C pow 2 + S pow 2 = &1 /\ S <= C
             ==> c849npm_margin2 c t C S <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] C849NPM_HALF_ANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`C:real`; `S:real`] C849NPM_HALF_ANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC C849NPM_CHECK2 THEN
  MAP_EVERY EXISTS_TAC [`t / (&1 + c)`; `S / (&1 + C)`] THEN ASM_REWRITE_TAC[]);;
