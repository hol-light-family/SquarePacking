(* ========================================================================= *)
(* Phase 2: Compact/Assembly/RowIdentity.lean, with the contract vocabulary  *)
(* of Completion/Contracts.lean.                                             *)
(*                                                                           *)
(*   Lean S12Completion.ExcludesFamily family   excl_fam fam                 *)
(*     (= !c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP ..) = fam ==> F) *)
(*   Lean S12Completion.ExcludesCase id         excl_case id                 *)
(*   Lean coverRows (577 rows, ids and groups)  ROWS (Phase 1, same order:   *)
(*     row i's groups = set_of_list (EL i ROWS)), COVER_IDS (originalId)    *)
(*   Lean expectedIds                           EXPECTED_IDS                 *)
(*   Lean retainedRows = rows with id in expectedIds = rows EL i ROWS with   *)
(*     MEM i RI_RETAINED_INDEX (RI_RETAINED_INDEX_EQ; = Phase 1 RETAINED_IDX) *)
(*   Lean rowAt i                               EL i ROWS                    *)
(* COVER_IDS / EXPECTED_IDS are copied from source/S12/CoverData.lean; the   *)
(* groups of all 577 rows were checked equal to Phase 1's ROWS.              *)
(* For the final assembly: ri_excluded_row i (|- excl_case id) gives         *)
(* |- EXCLUDED_ROW i (step6.ml) for the retained row i with that id.          *)
(* ========================================================================= *)

needs "n12/geometry/PackingContext.ml";;

(* Lean: S12Completion.ExcludesFamily *)
let excl_fam = new_definition
 `excl_fam fam <=> forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam ==> false`;;

(* Lean: CoverRow.originalId of coverRows, expectedIds *)
let COVER_IDS = new_definition `COVER_IDS = [999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;999999;0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31;32;33;34;35;36;37;38;39;40;41;42;43;44;45;46;47;48;49;50;51;52;53;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;94;98;107;108;109;113;128;129;130;131;135;139;146;147;151;155;159;164;173;174;175;187;188;189;193;197;201;205;209;219;220;221;234;235;236;240;244;248;252;257;261;265;272;273;277;289;290;291;295;299;303;307;312;316;320;325;342;351;383;387;401;999999;999999;999999;999999;999999;999999;999999;999999;999999;402;403;404;405;406;407;408;409;410;411;412;413;414;415;416;417;418;419;420;421;422;423;424;425;426;427;428;429;430;431;432;433;434;435;436;437;438;439;440;441;442;443;444;445;446;447;448;449;450;451;452;453;454;455;456;457;458;459;463;467;474;475;484;485;489;493;498;502;506;510;518;519;523;527;532;533;534;535;536;537;538;539;540;541;542;543;544;545;546;547;548;549;550;551;552;553;554;555;556;557;558;559;560;561;562;563;564;565;566;567;568;569;570;571;572;573;574;575;576;577;578;579;580;581;582;583;584;585;586;587;588;589;590;594;598;605;606;615;616;620;624;629;633;637;641;645;654;655;659;663;668;669;670;671;672;673;674;675;676;677;678;679;680;681;682;683;684;685;686;687;688;689;690;691;692;693;694;695;696;697;698;699;700;701;702;703;704;705;706;707;708;709;710;711;712;713;714;715;716;717;722;725;729;737;738;742;746;751;755;760;769;770;771;783;784;785;789;793;797;801;804;813;814;818;823;827;832;836;840;841;842;843;844;845;846;847;848;849;850;851;852;853;854;855;856;857;858;859;860;861;862;863;864;865;866;867;868;869;870;871;872;873;874;875;876;877;878;879;880;881;882;883;884;885;886;887;888;889;890;891;892;893;894;895;896;897;898;902;906;913;914;923;924;928;932;937;942;948;949;957;958;962;966;971;972;973;974;975;976;977;978;979;980;981;982;983;984;985;986;987;988;989;990;991;992;993;994;995;996;997;998;999;1000;1001;1002;1003;1004;1005;1015;1025;1046;1056;1057;1058;1059;1060;1061;1062;1063;1064;1065;1066;1067;1068;1069;1070;1071;1072;1073;1074;1075;1076;1077;1078;1079;1080;1081;1082;1083;1084;1085;1086;1087;1088;1089;1090;1091;1092]`;;
let EXPECTED_IDS = new_definition `EXPECTED_IDS = [28;48;71;78;80;84;405;424;445;454;537;556;565;567;569;570;573;574;575;576;577;580;581;585;589;590;669;670;673;674;675;678;680;683;684;690;691;694;696;697;698;699;700;701;702;705;709;711;713;715;716;717;841;842;846;847;848;849;850;851;852;853;862;864;867;868;882;886;887;888;889;890;893;896;898;972;973;974;975;976;977;978;979;981;982;983;985;990;992;993;994;995;997;998;999;1001;1002;1063;1064;1069;1070;1072;1073;1074;1075;1077;1078;1081;1083;1084;1085;1086;1087;1089;1090;1091;1092]`;;
let RI_RETAINED_INDEX = new_definition `RI_RETAINED_INDEX = [67;87;110;117;119;123;202;221;242;251;278;297;306;308;310;311;314;315;316;317;318;321;322;326;330;331;350;351;354;355;356;359;361;364;365;371;372;375;377;378;379;380;381;382;383;386;390;392;394;396;397;398;428;429;433;434;435;436;437;438;439;440;449;451;454;455;469;473;474;475;476;477;480;483;485;503;504;505;506;507;508;509;510;512;513;514;516;521;523;524;525;526;528;529;530;532;533;547;548;553;554;556;557;558;559;561;562;565;567;568;569;570;571;573;574;575;576]`;;

(* Lean: S12Completion.ExcludesCase *)
let excl_case = new_definition
 `excl_case id <=> forall i. i < 577 /\ MEM (EL i COVER_IDS) EXPECTED_IDS /\ EL i COVER_IDS = id
                       ==> excl_fam (set_of_list (EL i ROWS))`;;

let EXCL_FAM_ALT = prove
 (`forall fam. excl_fam fam <=> ~(exists c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam)`,
  REWRITE_TAC[excl_fam; NOT_EXISTS_THM] THEN MESON_TAC[]);;

let ID_LOOKUP = el_lookups COVER_IDS;;
let LENGTH_COVER_IDS = (REWRITE_CONV[COVER_IDS; LENGTH] THENC NUM_REDUCE_CONV) `LENGTH COVER_IDS`;;

(* Lean: rowAt_mem *)
let RI_ROWAT_MEM = prove
 (`forall i. i < 577 ==> MEM (EL i ROWS) ROWS`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEM_EL THEN ASM_REWRITE_TAC[LENGTH_ROWS]);;

(* the retained indices are exactly the rows with an expected id *)
let RI_RETAINED_INDEX_EQ =
  let tm = `FILTER (\j. MEM (EL j COVER_IDS) EXPECTED_IDS) (rangelist 0 577)` in
  let r = RANGE_EXPL 577 in
  let cc t = (REWRITE_CONV[ID_LOOKUP.(dest_small_numeral (lhand (lhand t)))] THENC
              REWRITE_CONV[EXPECTED_IDS; MEM] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[]) t in
  let th = (RAND_CONV (K r) THENC filter_by_conv cc) tm in
  TRANS th (SYM RI_RETAINED_INDEX);;

let RI_RETAINED = prove
 (`forall j. MEM j RI_RETAINED_INDEX <=> j < 577 /\ MEM (EL j COVER_IDS) EXPECTED_IDS`,
  REWRITE_TAC[GSYM RI_RETAINED_INDEX_EQ; MEM_FILTER; MEM_RANGELIST; LE_0; ADD_CLAUSES] THEN
  MESON_TAC[]);;

let MAP_DISTINCT_INJ = prove
 (`forall (f:num->num) l. PAIRWISE (\x y. ~(x = y)) (MAP f l)
     ==> forall i j. MEM i l /\ MEM j l /\ f i = f j ==> i = j`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; PAIRWISE; MEM; GSYM ALL_MEM; MEM_MAP] THEN
  BETA_TAC THEN ASM_MESON_TAC[]);;

let RI_RET_MAP = prove
 (`MAP (\i. EL i COVER_IDS) RI_RETAINED_INDEX = EXPECTED_IDS`,
  REWRITE_TAC[RI_RETAINED_INDEX; MAP] THEN BETA_TAC THEN
  REWRITE_TAC(Array.to_list ID_LOOKUP) THEN REWRITE_TAC[EXPECTED_IDS]);;

let RI_EXPECTED_DISTINCT = prove
 (`PAIRWISE (\x y:num. ~(x = y)) EXPECTED_IDS`,
  REWRITE_TAC[EXPECTED_IDS; PAIRWISE; ALL] THEN CONV_TAC(DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV) THEN
  REWRITE_TAC[]);;

(* Lean: retained_id_injective (as indices of the original table) *)
let RI_RETAINED_ID_INJECTIVE = prove
 (`forall i j. i < 577 /\ j < 577 /\ MEM (EL i COVER_IDS) EXPECTED_IDS /\ MEM (EL j COVER_IDS) EXPECTED_IDS /\
         EL i COVER_IDS = EL j COVER_IDS ==> i = j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\i. EL i COVER_IDS`; `RI_RETAINED_INDEX`] MAP_DISTINCT_INJ) THEN
  REWRITE_TAC[RI_RET_MAP; RI_EXPECTED_DISTINCT] THEN BETA_TAC THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[RI_RETAINED]);;

(* Lean: family_at *)
let RI_FAMILY_AT = prove
 (`forall i id fam. i < 577 /\ EL i COVER_IDS = id /\ set_of_list (EL i ROWS) = fam
     ==> forall j. j < 577 /\ MEM (EL j COVER_IDS) EXPECTED_IDS /\ EL j COVER_IDS = id
             ==> set_of_list (EL j ROWS) = fam`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `j:num = i` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC RI_RETAINED_ID_INJECTIVE THEN ASM_MESON_TAC[]);;

(* the Lean "lookup" decide:  |- i < 577 /\ EL i COVER_IDS = id /\ set_of_list (EL i ROWS) = fam *)
let ri_lookup i fam =
  let it = mk_small_numeral i in
  let lt = EQT_ELIM (NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` it `577`)) in
  let idth = ID_LOOKUP.(i) in
  let rth = AP_TERM `set_of_list:(num)list->num->bool` ROW_LOOKUP.(i) in
  let fth = TRANS rth (setlit_eq (rhs (concl rth)) fam) in
  end_itlist CONJ [lt; idth; fth];;

(* family_at at a literal row:  |- !j. j < 577 /\ MEM (EL j COVER_IDS) EXPECTED_IDS /\ EL j COVER_IDS = id
                                       ==> set_of_list (EL j ROWS) = fam *)
let ri_family_at i fam = MATCH_MP RI_FAMILY_AT (ri_lookup i fam);;

(* excludes_case from a family exclusion:  |- excl_fam fam ==> excl_case id  (row i has id and fam) *)
let ri_excludes_case i fam =
  let fa = ri_family_at i fam in
  let id = rand (concl ID_LOOKUP.(i)) in
  prove(mk_imp(mk_comb(`excl_fam`, fam), mk_comb(`excl_case`, id)),
    DISCH_TAC THEN REWRITE_TAC[excl_case] THEN REPEAT STRIP_TAC THEN
    MP_TAC (SPEC `i:num` fa) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

(* for the assembly:  |- excl_case id  ==>  |- EXCLUDED_ROW i  (i the retained row with that id) *)
let ri_excluded_row i th =
  let id = rand (concl th) in
  let idth = ID_LOOKUP.(i) in
  if rand (concl idth) <> id then failwith "ri_excluded_row: id mismatch" else
  let lt = EQT_ELIM (NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` (mk_small_numeral i) `577`)) in
  let memth = EQT_ELIM ((REWRITE_CONV[idth; EXPECTED_IDS; MEM] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[])
     (mk_comb(mk_comb(`MEM:num->(num)list->bool`, lhs (concl idth)), `EXPECTED_IDS`))) in
  let ef = MP (SPEC (mk_small_numeral i) (REWRITE_RULE[excl_case] th)) (end_itlist CONJ [lt; memth; idth]) in
  let ef = REWRITE_RULE[ROW_LOOKUP.(i); EXCL_FAM_ALT] ef in
  EQ_MP (ALPHA (concl ef) (EXCLUDED_ROW i)) ef;;

(* Lean (per-case RowIdentity files): family_retained and excludes_case_iff.
   RI_EXCLUDES_CASE_IFF: a retained row with id and family fam makes the case contract
   equivalent to the family exclusion. *)
let RI_EXCLUDES_CASE_IFF = prove
 (`forall i id fam. i < 577 /\ MEM (EL i COVER_IDS) EXPECTED_IDS /\ EL i COVER_IDS = id /\
              set_of_list (EL i ROWS) = fam
     ==> (excl_case id <=> excl_fam fam)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[excl_case] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`i:num`; `id:num`; `fam:num->bool`] RI_FAMILY_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i':num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* |- i < 577 /\ MEM (EL i COVER_IDS) EXPECTED_IDS /\ EL i COVER_IDS = id /\ set_of_list (EL i ROWS) = fam *)
let ri_retained_lookup i fam =
  let lk = ri_lookup i fam in
  let lt, rest = CONJ_PAIR lk in
  let idth, fth = CONJ_PAIR rest in
  let memth = EQT_ELIM ((REWRITE_CONV[idth; EXPECTED_IDS; MEM] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[])
     (mk_comb(mk_comb(`MEM:num->(num)list->bool`, lhs (concl idth)), `EXPECTED_IDS`))) in
  end_itlist CONJ [lt; memth; idth; fth];;

(* Lean family_retained:  |- ?i. i < 577 /\ MEM (EL i COVER_IDS) EXPECTED_IDS /\ EL i COVER_IDS = id /\
                                 set_of_list (EL i ROWS) = fam *)
let ri_family_retained i fam =
  let th = ri_retained_lookup i fam in
  EXISTS (mk_exists(`i:num`, subst [`i:num`, mk_small_numeral i] (concl th)), mk_small_numeral i) th;;

(* Lean excludes_case_iff:  |- excl_case id <=> excl_fam fam *)
let ri_excludes_case_iff i fam = MATCH_MP RI_EXCLUDES_CASE_IFF (ri_retained_lookup i fam);;
