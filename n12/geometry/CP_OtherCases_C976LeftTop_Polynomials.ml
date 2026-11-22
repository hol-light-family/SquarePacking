(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976LeftTop/Polynomials.lean         *)
(* (N12Compact.Completion.OtherCases.C976LeftTop.Polynomials).  The two      *)
(* bivariate quartics of C976-LEFT-TOP-ANGLE section 7 and their Bernstein   *)
(* certificates.  value is ccbq_value; positive is CCBQ_POSITIVE.            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_BernsteinQuartic.ml";;

(* Lean: Phi (definition) *)
let c976ltp_Phi = new_definition
 `c976ltp_Phi (r:real) (w:real) =
    &4 * (w - &1) * (&650 * r pow 4 * w pow 3 - &4181 * r pow 4 * w pow 2 - &3531 * r pow 4 *
    w - &5762 * r pow 3 * w pow 3 + &762 * r pow 3 * w pow 2 + &5086 * r pow 3 * w + &3362
    * r pow 3 + &1100 * r pow 2 * w pow 3 + &4800 * r pow 2 * w pow 2 + &2600 * r pow 2 *
    w - &1100 * r pow 2 - &2062 * r * w pow 3 + &2262 * r * w pow 2 - &814 * r * w - &338
    * r - &650 * w pow 3 + &481 * w pow 2 - &169 * w)`;;

(* Lean: Plo (definition) *)
let c976ltp_Plo = new_definition
 `c976ltp_Plo (r:real) (w:real) =
    &2 * (w - &1) * (&2626 * r pow 4 * w pow 3 - &2140 * r pow 4 * w pow 2 - &3492 * r pow 4 *
    w - &1326 * r pow 4 - &11875 * r pow 3 * w pow 3 - &123 * r pow 3 * w pow 2 + &9227 *
    r pow 3 * w + &7075 * r pow 3 + &3500 * r pow 2 * w pow 3 + &15700 * r pow 2 * w pow 2
    + &8700 * r pow 2 * w - &3500 * r pow 2 - &4475 * r * w pow 3 + &2877 * r * w pow 2 -
    &2573 * r * w - &325 * r - &1326 * w pow 3 + &840 * w pow 2 - &408 * w + &26)`;;

(* Lean: hiCertificate (definition) *)
let c976ltp_hiCertificate = new_definition
 `c976ltp_hiCertificate (u:real) (v:real) =
    ccbq_value u
     (ccbq_value v (&576425601 / &2500000) (&61343959377 / &275000000) (&549771560687 / &2552343750) (&11662883977037 / &56151562500) (&18539000153896 / &92650078125))
     (ccbq_value v (&3234097557 / &13040000) (&260894951 / &1100000) (&15056227652929 / &66565125000) (&1193807392403 / &5547093750) (&617327770586386 / &3020392546875))
     (ccbq_value v (&50925234847 / &212552000) (&23642049567373 / &105213240000) (&136528744328231 / &651006922500) (&465048107173409 / &2387025382500) (&10644535395409252 / &59078878216875))
     (ccbq_value v (&266411996457 / &1385839040) (&3591848363311 / &20787585600) (&24104253924679 / &157206116100) (&9274698666875 / &69170691084) (&4932058421246332 / &42799365108225))
     (ccbq_value v (&1077874742655 / &11294588176) (&1105819449107 / &15530058742) (&108659091293749 / &2306213723187) (&594100361054744 / &25368350955057) (&271661855034224 / &837155581516881))`;;

(* Lean: loCertificate (definition) *)
let c976ltp_loCertificate = new_definition
 `c976ltp_loCertificate (u:real) (v:real) =
    ccbq_value u
     (ccbq_value v (&68351412 / &390625) (&4620997149 / &19531250) (&60362514731 / &244140625) (&11691483495219 / &48828125000) (&138809174244633 / &610351562500))
     (ccbq_value v (&1279692893 / &5093750) (&38618050889 / &127343750) (&3792499475861 / &12734375000) (&86529024218359 / &318359375000) (&7711611015318373 / &31835937500000))
     (ccbq_value v (&16453209689 / &49816875) (&181879023877 / &498168750) (&125410860360259 / &373626562500) (&353607363000067 / &1245421875000) (&23904304319516043 / &103785156250000))
     (ccbq_value v (&43101011766 / &108268675) (&2208517500383 / &5413433750) (&140778777316973 / &406007531250) (&3548515512650273 / &13533584375000) (&60484811879859163 / &338339609375000))
     (ccbq_value v (&312461268540 / &705911761) (&7410813902292 / &17647794025) (&28183130714259 / &88238970125) (&2156292523401063 / &11029871265625) (&17028128160128427 / &220597425312500))`;;

(* Lean: hi_identity *)
let C976LTP_HI_IDENTITY = prove
 (`forall r w. c976ltp_Phi r w =
         c976ltp_hiCertificate ((&4075 * r - &652) / &673) ((&132 * w - &33) / &7)`,
  REWRITE_TAC[c976ltp_Phi; c976ltp_hiCertificate; ccbq_value] THEN CONV_TAC REAL_RING);;

(* Lean: lo_identity *)
let C976LTP_LO_IDENTITY = prove
 (`forall r w. c976ltp_Plo r w =
         c976ltp_loCertificate ((&4075 * r - &652) / &673) ((&50 / &13) * w)`,
  REWRITE_TAC[c976ltp_Plo; c976ltp_loCertificate; ccbq_value] THEN CONV_TAC REAL_RING);;

(* all 25 coefficients positive: nested CCBQ_POSITIVE *)
let C976LTP_CERT_TAC =
  MATCH_MP_TAC CCBQ_POSITIVE THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC CCBQ_POSITIVE THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;;

(* Lean: hi_positive *)
let C976LTP_HI_POSITIVE = prove
 (`forall r w. &4 / &25 <= r /\ r <= &53 / &163 /\ &1 / &4 <= w /\ w <= &10 / &33
         ==> &0 < c976ltp_Phi r w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C976LTP_HI_IDENTITY; c976ltp_hiCertificate] THEN
  SUBGOAL_THEN `&0 <= (&4075 * r - &652) / &673 /\ (&4075 * r - &652) / &673 <= &1 /\
                &0 <= (&132 * w - &33) / &7 /\ (&132 * w - &33) / &7 <= &1` STRIP_ASSUME_TAC
  THENL [REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C976LTP_CERT_TAC);;

(* Lean: lo_positive *)
let C976LTP_LO_POSITIVE = prove
 (`forall r w. &4 / &25 <= r /\ r <= &53 / &163 /\ &0 <= w /\ w <= &13 / &50
         ==> &0 < c976ltp_Plo r w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C976LTP_LO_IDENTITY; c976ltp_loCertificate] THEN
  SUBGOAL_THEN `&0 <= (&4075 * r - &652) / &673 /\ (&4075 * r - &652) / &673 <= &1 /\
                &0 <= (&50 / &13) * w /\ (&50 / &13) * w <= &1` STRIP_ASSUME_TAC
  THENL [REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C976LTP_CERT_TAC);;
