structure poregexTheory :> poregexTheory =
struct
  val _ = if !Globals.print_thy_loads then TextIO.print "Loading poregexTheory ... " else ()
  open Type Term Thm
  infixr -->

  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  (* Parents and ML dependencies *)
  local open indexedListsTheory patternMatchesTheory
  in end;
  val _ = Theory.link_parents
          ("poregex",
          Arbnum.fromString "1501061068",
          Arbnum.fromString "922018")
          [("indexedLists",
           Arbnum.fromString "1492712812",
           Arbnum.fromString "523551"),
           ("patternMatches",
           Arbnum.fromString "1492712832",
           Arbnum.fromString "748185")];
  val _ = Theory.incorporate_types "poregex" [("Reg", 1)];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "fun"), ID("list", "list"), ID("pair", "prod"),
   ID("min", "bool"), ID("poregex", "Reg"), ID("num", "num"),
   ID("ind_type", "recspace"), ID("bool", "!"), ID("arithmetic", "+"),
   ID("pair", ","), ID("bool", "/\\"), ID("num", "0"), ID("min", "="),
   ID("min", "==>"), ID("bool", "?"), ID("list", "APPEND"),
   ID("bool", "ARB"), ID("poregex", "Alt"), ID("arithmetic", "BIT1"),
   ID("ind_type", "BOTTOM"), ID("bool", "COND"), ID("list", "CONS"),
   ID("ind_type", "CONSTR"), ID("bool", "DATATYPE"),
   ID("pred_set", "EMPTY"), ID("list", "EVERY"), ID("list", "EXISTS"),
   ID("poregex", "Eps"), ID("ind_type", "FCONS"), ID("list", "FLAT"),
   ID("pair", "FST"), ID("pred_set", "GSPEC"), ID("list", "HD"),
   ID("bool", "IN"), ID("pred_set", "INSERT"), ID("list", "LIST_TO_SET"),
   ID("list", "MAP"), ID("list", "NIL"), ID("arithmetic", "NUMERAL"),
   ID("poregex", "Reg_CASE"), ID("poregex", "Reg_size"),
   ID("poregex", "Rep"), ID("pair", "SND"), ID("num", "SUC"),
   ID("poregex", "Seq"), ID("poregex", "Sym"), ID("list", "TL"),
   ID("bool", "TYPE_DEFINITION"), ID("pair", "UNCURRY"),
   ID("pred_set", "UNION"), ID("arithmetic", "ZERO"), ID("bool", "\\/"),
   ID("poregex", "accept"), ID("poregex", "language_of"),
   ID("poregex", "parts"), ID("poregex", "split"), ID("bool", "~")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYV "'a", TYOP [1, 0], TYOP [2, 1, 1], TYOP [1, 2], TYOP [0, 1, 3],
   TYOP [1, 1], TYOP [1, 5], TYOP [0, 1, 6], TYOP [3], TYOP [0, 1, 8],
   TYOP [4, 0], TYOP [0, 10, 9], TYOP [0, 0, 10], TYOP [0, 10, 10],
   TYOP [0, 10, 13], TYOP [5], TYOP [0, 10, 15], TYOP [0, 0, 15],
   TYOP [0, 17, 16], TYV "'b", TYOP [0, 10, 19], TYOP [0, 20, 19],
   TYOP [0, 10, 20], TYOP [0, 22, 21], TYOP [0, 22, 23], TYOP [0, 0, 19],
   TYOP [0, 25, 24], TYOP [0, 19, 26], TYOP [0, 10, 27], TYOP [6, 0],
   TYOP [0, 29, 8], TYOP [0, 10, 8], TYOP [0, 13, 8], TYOP [0, 14, 32],
   TYOP [0, 14, 33], TYOP [0, 12, 34], TYOP [0, 10, 35], TYOP [0, 19, 19],
   TYOP [0, 19, 37], TYOP [0, 10, 38], TYOP [0, 10, 39], TYOP [0, 10, 37],
   TYOP [0, 10, 29], TYOP [0, 0, 8], TYOP [0, 43, 8], TYOP [0, 19, 8],
   TYOP [0, 45, 8], TYOP [0, 31, 8], TYOP [0, 25, 8], TYOP [0, 48, 8],
   TYOP [0, 17, 8], TYOP [0, 50, 8], TYOP [0, 20, 8], TYOP [0, 52, 8],
   TYOP [0, 47, 8], TYOP [0, 41, 8], TYOP [0, 55, 8], TYOP [0, 22, 8],
   TYOP [0, 57, 8], TYOP [0, 40, 8], TYOP [0, 59, 8], TYOP [0, 11, 8],
   TYOP [0, 61, 8], TYOP [0, 30, 8], TYOP [0, 63, 8], TYOP [0, 9, 8],
   TYOP [0, 5, 8], TYOP [0, 66, 8], TYOP [0, 2, 8], TYOP [0, 68, 8],
   TYOP [0, 15, 15], TYOP [0, 15, 70], TYOP [2, 1, 8], TYOP [0, 8, 72],
   TYOP [0, 1, 73], TYOP [0, 1, 2], TYOP [0, 1, 75], TYOP [0, 8, 8],
   TYOP [0, 8, 77], TYOP [0, 0, 43], TYOP [0, 19, 45], TYOP [0, 10, 31],
   TYOP [0, 9, 65], TYOP [0, 1, 9], TYOP [0, 5, 66], TYOP [0, 6, 8],
   TYOP [0, 6, 85], TYOP [0, 3, 8], TYOP [0, 3, 87], TYOP [0, 15, 8],
   TYOP [0, 15, 89], TYOP [0, 29, 30], TYOP [0, 42, 8], TYOP [0, 92, 8],
   TYOP [0, 1, 1], TYOP [0, 1, 94], TYOP [0, 6, 6], TYOP [0, 6, 96],
   TYOP [0, 8, 97], TYOP [0, 0, 94], TYOP [0, 5, 5], TYOP [0, 1, 100],
   TYOP [0, 5, 96], TYOP [0, 3, 3], TYOP [0, 2, 103], TYOP [0, 15, 29],
   TYOP [0, 105, 29], TYOP [0, 0, 106], TYOP [0, 15, 107], TYOP [0, 9, 66],
   TYOP [0, 66, 85], TYOP [0, 68, 87], TYOP [0, 105, 105],
   TYOP [0, 29, 112], TYOP [0, 5, 1], TYOP [1, 6], TYOP [0, 115, 6],
   TYOP [0, 2, 1], TYOP [0, 1, 72], TYOP [0, 118, 9], TYOP [0, 2, 72],
   TYOP [0, 120, 9], TYOP [0, 1, 65], TYOP [0, 5, 67], TYOP [0, 2, 69],
   TYOP [0, 9, 9], TYOP [0, 1, 125], TYOP [0, 5, 9], TYOP [0, 6, 66],
   TYOP [0, 3, 68], TYOP [0, 6, 115], TYOP [0, 5, 6], TYOP [0, 131, 130],
   TYOP [0, 2, 2], TYOP [0, 133, 103], TYOP [0, 30, 92], TYOP [0, 1, 118],
   TYOP [0, 136, 120], TYOP [0, 9, 125]]
  end
  val _ = Theory.incorporate_consts "poregex" tyvector
     [("split", 4), ("parts", 7), ("language_of", 11), ("accept", 11),
      ("Sym", 12), ("Seq", 14), ("Rep", 13), ("Reg_size", 18),
      ("Reg_CASE", 28), ("Eps", 10), ("Alt", 14)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("'Reg'", 30), TMV("M", 10), TMV("M'", 10), TMV("P", 31),
   TMV("P", 11), TMV("R", 10), TMV("R0", 10), TMV("RR", 10),
   TMV("Reg", 36), TMV("a", 0), TMV("a", 10), TMV("a", 29), TMV("a'", 0),
   TMV("a'", 10), TMV("a0", 10), TMV("a0", 29), TMV("a0'", 10),
   TMV("a0'", 29), TMV("a1", 10), TMV("a1", 29), TMV("a1'", 10),
   TMV("b", 10), TMV("c", 0), TMV("cs", 1), TMV("e", 1), TMV("f", 10),
   TMV("f", 25), TMV("f", 17), TMV("f'", 25), TMV("f0", 19), TMV("f1", 25),
   TMV("f1", 22), TMV("f1'", 22), TMV("f2", 22), TMV("f2", 40),
   TMV("f2'", 22), TMV("f3", 20), TMV("f3", 40), TMV("f3'", 20),
   TMV("f4", 41), TMV("fn", 20), TMV("fstPrt", 1), TMV("h", 0),
   TMV("n", 15), TMV("p", 10), TMV("part", 1), TMV("partition", 5),
   TMV("q", 10), TMV("r", 10), TMV("rep", 42), TMV("s", 10),
   TMV("sndPrt", 1), TMV("t", 1), TMV("u", 1), TMV("v", 19), TMV("v", 10),
   TMV("v'", 19), TMV("v1", 1), TMV("words", 5), TMV("x", 1), TMV("x", 5),
   TMV("x", 2), TMC(7, 44), TMC(7, 46), TMC(7, 47), TMC(7, 49), TMC(7, 51),
   TMC(7, 53), TMC(7, 54), TMC(7, 56), TMC(7, 58), TMC(7, 60), TMC(7, 62),
   TMC(7, 64), TMC(7, 65), TMC(7, 67), TMC(7, 69), TMC(7, 63), TMC(8, 71),
   TMC(9, 74), TMC(9, 76), TMC(10, 78), TMC(11, 15), TMC(12, 79),
   TMC(12, 80), TMC(12, 81), TMC(12, 78), TMC(12, 82), TMC(12, 83),
   TMC(12, 84), TMC(12, 86), TMC(12, 88), TMC(12, 90), TMC(12, 91),
   TMC(13, 78), TMC(14, 44), TMC(14, 47), TMC(14, 53), TMC(14, 93),
   TMC(14, 67), TMC(14, 63), TMC(15, 95), TMC(16, 0), TMC(17, 14),
   TMC(18, 70), TMC(19, 29), TMC(20, 98), TMC(21, 99), TMC(21, 101),
   TMC(21, 102), TMC(21, 104), TMC(22, 108), TMC(23, 77), TMC(24, 9),
   TMC(25, 109), TMC(26, 110), TMC(26, 111), TMC(27, 10), TMC(28, 113),
   TMC(29, 114), TMC(29, 116), TMC(30, 117), TMC(31, 119), TMC(31, 121),
   TMC(32, 114), TMC(33, 122), TMC(33, 123), TMC(33, 124), TMC(34, 126),
   TMC(35, 127), TMC(35, 128), TMC(35, 129), TMC(36, 132), TMC(36, 134),
   TMC(37, 1), TMC(37, 5), TMC(37, 6), TMC(37, 3), TMC(38, 70),
   TMC(39, 28), TMC(40, 18), TMC(41, 13), TMC(42, 117), TMC(43, 70),
   TMC(44, 14), TMC(45, 12), TMC(46, 100), TMC(47, 135), TMC(48, 137),
   TMC(49, 138), TMC(50, 15), TMC(51, 78), TMC(52, 11), TMC(53, 11),
   TMC(54, 7), TMC(55, 4), TMC(56, 77)]
  end
  structure ThmBind = struct
    val DT = Thm.disk_thm
    val read = Term.read_raw tmvector
  end
  fun op Reg_TY_DEF x = x
    val op Reg_TY_DEF =
    ThmBind.DT(((("poregex",0),
                [("bool",[14,25,26,52,131,132,137])]),["DISK_THM"]),
               [ThmBind.read"%98%49%147%17%73%0%94%77%17%94%151%93$0@%111%82@%102@%43%105|@3%151%95%9%93$1@%9%111%143%82@2$0@%43%105|@|$0@2|@2%151%100%15%100%19%81%93$2@%15%19%111%143%143%82@3%102@%118$1@%118$0@%43%105|@3||$1@$0@3%81$3$1@2$3$0@3|@|@2%151%100%15%100%19%81%93$2@%15%19%111%143%143%143%82@4%102@%118$1@%118$0@%43%105|@3||$1@$0@3%81$3$1@2$3$0@3|@|@2%100%11%81%93$1@%11%111%143%143%143%143%82@5%102@%118$0@%43%105|@2|$0@3$2$0@2|@6$1$0@2|@2$0$1@2|@|@$0@|@"])
  fun op Reg_case_def x = x
    val op Reg_case_def =
    ThmBind.DT(((("poregex",12),
                [("bool",[14,25,26,30,52,62,131,132,137,180]),
                 ("ind_type",[33,34]),
                 ("poregex",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%81%63%54%65%26%70%31%70%33%67%36%84%139%117@$4@$3@$2@$1@$0@2$4@|@|@|@|@|@2%81%62%9%63%54%65%26%70%31%70%33%67%36%84%139%145$5@2$4@$3@$2@$1@$0@2$3$5@2|@|@|@|@|@|@2%81%64%14%64%18%63%54%65%26%70%31%70%33%67%36%84%139%103$6@$5@2$4@$3@$2@$1@$0@2$2$6@$5@2|@|@|@|@|@|@|@2%81%64%14%64%18%63%54%65%26%70%31%70%33%67%36%84%139%144$6@$5@2$4@$3@$2@$1@$0@2$1$6@$5@2|@|@|@|@|@|@|@2%64%10%63%54%65%26%70%31%70%33%67%36%84%139%141$5@2$4@$3@$2@$1@$0@2$0$5@2|@|@|@|@|@|@5"])
  fun op Reg_size_def x = x
    val op Reg_size_def =
    ThmBind.DT(((("poregex",13),
                [("bool",[14,25,26,30,52,62,131,132,137,180]),
                 ("ind_type",[33,34]),
                 ("poregex",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%81%66%27%92%140$0@%117@2%82@|@2%81%66%27%62%9%92%140$1@%145$0@3%78%138%104%150@3$1$0@3|@|@2%81%66%27%64%14%64%18%92%140$2@%103$1@$0@3%78%138%104%150@3%78%140$2@$1@2%140$2@$0@4|@|@|@2%81%66%27%64%14%64%18%92%140$2@%144$1@$0@3%78%138%104%150@3%78%140$2@$1@2%140$2@$0@4|@|@|@2%66%27%64%10%92%140$1@%141$0@3%78%138%104%150@3%140$1@$0@3|@|@5"])
  fun op language_of_def x = x
    val op language_of_def =
    ThmBind.DT(((("poregex",21),
                [("bool",[14,25,26,30,52,62,131,132,137,180]),
                 ("ind_type",[33,34]),
                 ("poregex",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%81%87%153%117@2%128%134@%113@3%81%62%22%87%153%145$0@3%128%107$0@%134@2%113@2|@2%81%64%10%64%21%87%153%103$1@$0@3%149%153$1@2%153$0@3|@|@2%81%64%25%64%50%87%153%144$1@$0@3%123%148%41%51%79%101$1@$0@2%81%125$1@%153$3@3%125$0@%153$2@4||@3|@|@2%64%48%87%153%141$0@3%122%59%79$0@%99%58%81%156%89$0@%135@3%81%114%24%125$0@%153$3@2|@$0@2%88%119$0@2$1@3|@2|@2|@5"])
  fun op split_def x = x
    val op split_def =
    ThmBind.DT(((("poregex",22),[("list",[13])]),["DISK_THM"]),
               [ThmBind.read"%81%91%155%134@2%110%80%134@%134@2%137@3%62%22%74%23%91%155%107$1@$0@3%110%80%134@%107$1@$0@3%133%61%80%107$2@%121$0@3%142$0@2|@%155$0@4|@|@2"])
  fun op parts_def x = x
    val op parts_def =
    ThmBind.DT(((("poregex",23),[("list",[13])]),["DISK_THM"]),
               [ThmBind.read"%81%90%154%134@2%109%135@%136@3%62%22%74%23%90%154%107$1@$0@3%106%88$0@%134@2%109%108%107$1@%134@2%135@2%136@2%120%132%60%109%108%107$2@%134@2$0@2%109%108%107$2@%124$0@3%146$0@3%136@2|@%154$0@5|@|@2"])
  fun op datatype_Reg x = x
    val op datatype_Reg =
    ThmBind.DT(((("poregex",14),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%112%8%117@%145@%103@%144@%141@2"])
  fun op Reg_11 x = x
    val op Reg_11 =
    ThmBind.DT(((("poregex",15),
                [("bool",[14,25,26,30,50,52,55,62,131,132,137,180]),
                 ("ind_type",[33,34]),
                 ("poregex",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%81%62%9%62%12%86%85%145$1@2%145$0@3%83$1@$0@2|@|@2%81%64%14%64%18%64%16%64%20%86%85%103$3@$2@2%103$1@$0@3%81%85$3@$1@2%85$2@$0@3|@|@|@|@2%81%64%14%64%18%64%16%64%20%86%85%144$3@$2@2%144$1@$0@3%81%85$3@$1@2%85$2@$0@3|@|@|@|@2%64%10%64%13%86%85%141$1@2%141$0@3%85$1@$0@2|@|@4"])
  fun op Reg_distinct x = x
    val op Reg_distinct =
    ThmBind.DT(((("poregex",16),
                [("bool",
                 [14,25,26,30,35,46,50,52,53,55,62,131,132,137,180]),
                 ("ind_type",[33,34]),
                 ("poregex",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%81%62%9%156%85%117@%145$0@3|@2%81%64%18%64%14%156%85%117@%103$0@$1@3|@|@2%81%64%18%64%14%156%85%117@%144$0@$1@3|@|@2%81%64%10%156%85%117@%141$0@3|@2%81%64%18%64%14%62%9%156%85%145$0@2%103$1@$2@3|@|@|@2%81%64%18%64%14%62%9%156%85%145$0@2%144$1@$2@3|@|@|@2%81%64%13%62%9%156%85%145$0@2%141$1@3|@|@2%81%64%20%64%18%64%16%64%14%156%85%103$0@$2@2%144$1@$3@3|@|@|@|@2%81%64%18%64%14%64%10%156%85%103$1@$2@2%141$0@3|@|@|@2%64%18%64%14%64%10%156%85%144$1@$2@2%141$0@3|@|@|@10"])
  fun op Reg_case_cong x = x
    val op Reg_case_cong =
    ThmBind.DT(((("poregex",17),
                [("bool",[14,25,26,52,131,132,137,180]),
                 ("poregex",[1,2,3,4,5,6,7,8,9,10,11,12])]),["DISK_THM"]),
               [ThmBind.read"%64%1%64%2%63%54%65%26%70%31%70%33%67%36%94%81%85$6@$5@2%81%94%85$5@%117@2%84$4@%56@3%81%62%9%94%85$6@%145$0@3%84$4$0@2%28$0@3|@2%81%64%14%64%18%94%85$7@%103$1@$0@3%84$4$1@$0@2%32$1@$0@3|@|@2%81%64%14%64%18%94%85$7@%144$1@$0@3%84$3$1@$0@2%35$1@$0@3|@|@2%64%10%94%85$6@%141$0@3%84$1$0@2%38$0@3|@7%84%139$6@$4@$3@$2@$1@$0@2%139$5@%56@%28@%32@%35@%38@3|@|@|@|@|@|@|@"])
  fun op Reg_nchotomy x = x
    val op Reg_nchotomy =
    ThmBind.DT(((("poregex",18),
                [("bool",[14,25,26,52,131,132,137,180]),
                 ("poregex",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%64%7%151%85$0@%117@2%151%95%9%85$1@%145$0@2|@2%151%96%5%96%6%85$2@%103$1@$0@2|@|@2%151%96%5%96%6%85$2@%144$1@$0@2|@|@2%96%5%85$1@%141$0@2|@5|@"])
  fun op Reg_Axiom x = x
    val op Reg_Axiom =
    ThmBind.DT(((("poregex",19),
                [("bool",[14,25,26,30,52,62,131,132,137,180]),
                 ("ind_type",[33,34]),
                 ("poregex",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%63%29%65%30%71%34%71%37%69%39%97%40%81%84$0%117@2$5@2%81%62%9%84$1%145$0@3$5$0@2|@2%81%64%14%64%18%84$2%103$1@$0@3$5$1@$0@$2$1@2$2$0@3|@|@2%81%64%14%64%18%84$2%144$1@$0@3$4$1@$0@$2$1@2$2$0@3|@|@2%64%10%84$1%141$0@3$2$0@$1$0@3|@5|@|@|@|@|@|@"])
  fun op Reg_induction x = x
    val op Reg_induction =
    ThmBind.DT(((("poregex",20),
                [("bool",[14,25,26,52,131,132,137]),
                 ("poregex",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%68%3%94%81$0%117@2%81%62%9$1%145$0@2|@2%81%64%5%64%6%94%81$2$1@2$2$0@3$2%103$1@$0@3|@|@2%81%64%5%64%6%94%81$2$1@2$2$0@3$2%144$1@$0@3|@|@2%64%5%94$1$0@2$1%141$0@3|@6%64%5$1$0@|@2|@"])
  fun op accept_ind x = x
    val op accept_ind =
    ThmBind.DT(((("poregex",26),
                [("arithmetic",[24,25,26,27,41,46,59,73,95,179,186]),
                 ("bool",
                 [14,25,26,27,35,50,51,52,53,57,62,92,95,103,104,106,123,
                  131,132,137,180]),("list",[46]),("numeral",[3,7,8]),
                 ("pair",[5,7,8,9,16,25]),
                 ("poregex",[1,2,3,4,5,6,7,8,9,10,11,13]),
                 ("prim_rec",[42]),("relation",[107,119,121]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%72%4%94%81%74%53$1%117@$0@|@2%81%62%22%74%53$2%145$1@2$0@|@|@2%81%64%44%64%47%74%53%94%81$3$2@$0@2$3$1@$0@3$3%103$2@$1@2$0@2|@|@|@2%81%64%44%64%47%74%53%94%81%76%61%94%127$0@%131%155$1@4$4$3@%121$0@3|@2%76%61%94%127$0@%131%155$1@4$4$2@%142$0@3|@3$3%144$2@$1@2$0@2|@|@|@2%81%64%48%94$1$0@%134@2$1%141$0@2%134@2|@2%64%48%62%42%74%52%94%75%46%74%45%94%81%126$1@%130%154%107$3@$2@5%125$0@%129$1@4$5$4@$0@2|@|@2$3%141$2@2%107$1@$0@3|@|@|@7%64%55%74%57$2$1@$0@|@|@2|@"])
  fun op accept_def x = x
    val op accept_def =
    ThmBind.DT(((("poregex",27),
                [("arithmetic",[24,25,26,27,41,46,59,73,95,179,186]),
                 ("bool",
                 [15,25,35,50,51,52,53,57,62,92,95,103,104,106,123]),
                 ("combin",[19]),("list",[6,155,156]),("numeral",[3,7,8]),
                 ("pair",[7,8,9,16,25,49]),("poregex",[12,13,24,25]),
                 ("prim_rec",[42]),("relation",[119,121,127,132]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%81%74%53%86%152%117@$0@2%88$0@%134@2|@2%81%74%53%62%22%86%152%145$0@2$1@2%88$1@%107$0@%134@3|@|@2%81%74%53%64%47%64%44%86%152%103$0@$1@2$2@2%151%152$0@$2@2%152$1@$2@3|@|@|@2%81%74%53%64%47%64%44%86%152%144$0@$1@2$2@2%116%61%81%152$1@%121$0@3%152$2@%142$0@3|@%155$2@3|@|@|@2%81%64%48%86%152%141$0@2%134@2%152$0@%134@2|@2%74%52%64%48%62%42%86%152%141$1@2%107$0@$2@3%115%46%114%45%152$3@$0@|@$0@|@%154%107$0@$2@4|@|@|@6"])
  fun op LANGUAGE_ACCEPTED_THM x = x
    val op LANGUAGE_ACCEPTED_THM =
    ThmBind.DT(((("poregex",28),
                [("arithmetic",[24,25,26,27,41,46,59,73,95,179,186]),
                 ("bool",
                 [14,15,25,26,27,35,50,51,52,53,55,57,62,92,95,103,104,106,
                  123,131,132,137]),("combin",[19]),
                 ("list",[6,48,155,156]),("numeral",[3,7,8]),
                 ("pair",[7,8,9,16,25,49]),
                 ("poregex",[1,2,3,4,5,6,7,8,9,10,11,12,13,21,24,25]),
                 ("pred_set",[18,41,88]),("prim_rec",[42]),
                 ("relation",[119,121,127,132]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM", "cheat"]),
               [ThmBind.read"%64%5%74%59%94%125$0@%153$1@3%152$1@$0@2|@|@"])

  val _ = DB.bindl "poregex"
  [("Reg_TY_DEF",Reg_TY_DEF,DB.Def), ("Reg_case_def",Reg_case_def,DB.Def),
   ("Reg_size_def",Reg_size_def,DB.Def),
   ("language_of_def",language_of_def,DB.Def),
   ("split_def",split_def,DB.Def), ("parts_def",parts_def,DB.Def),
   ("datatype_Reg",datatype_Reg,DB.Thm), ("Reg_11",Reg_11,DB.Thm),
   ("Reg_distinct",Reg_distinct,DB.Thm),
   ("Reg_case_cong",Reg_case_cong,DB.Thm),
   ("Reg_nchotomy",Reg_nchotomy,DB.Thm), ("Reg_Axiom",Reg_Axiom,DB.Thm),
   ("Reg_induction",Reg_induction,DB.Thm),
   ("accept_ind",accept_ind,DB.Thm), ("accept_def",accept_def,DB.Thm),
   ("LANGUAGE_ACCEPTED_THM",LANGUAGE_ACCEPTED_THM,DB.Thm)]

  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "poregex",
    thydataty = "compute",
    read = ThmBind.read,
    data =
        "poregex.language_of_def poregex.parts_def poregex.accept_def poregex.split_def"
  }
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "poregex",
    thydataty = "TypeGrammarDeltas",
    read = ThmBind.read,
    data = "NTY7.poregex,3.Reg"
  }
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "poregex",
    thydataty = "TermGrammarDeltas",
    read = ThmBind.read,
    data =
        "OO3.Eps4.%117OO3.Sym4.%145OO3.Alt4.%103OO3.Seq4.%144OO3.Rep4.%141OO8.Reg_CASE4.%139OO8.Reg_size4.%140OO4.case4.%139OO11.language_of4.%153OO5.split4.%155OO5.parts4.%154OO6.accept4.%152"
  }
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val poregex_grammars = merge_grammars ["indexedLists", "patternMatches"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="poregex"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val poregex_grammars = 
    Portable.## (addtyUDs,addtmUDs) poregex_grammars
  val _ = Parse.grammarDB_insert("poregex",poregex_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end


  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG Reg_Axiom,
           case_def=Reg_case_def,
           case_cong=Reg_case_cong,
           induction=ORIG Reg_induction,
           nchotomy=Reg_nchotomy,
           size=SOME(Parse.Term`(poregex$Reg_size) :('a -> num$num) -> 'a poregex$Reg -> num$num`,
                     ORIG Reg_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME Reg_11,
           distinct=SOME Reg_distinct,
           fields=let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}
    val U = mk_vartype
in
[] end,
           accessors=[],
           updates=[],
           recognizers=[],
           destructors=[]}
        val tyinfo0 = tyinfo0
        val () = computeLib.write_datatype_info tyinfo0
      in
        tyinfo0
      end
    ];

val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "poregex"
end
