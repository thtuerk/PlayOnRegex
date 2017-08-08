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
  local open basis_emitTheory
  in end;
  val _ = Theory.link_parents
          ("poregex",
          Arbnum.fromString "1502202819",
          Arbnum.fromString "659553")
          [("basis_emit",
           Arbnum.fromString "1492712999",
           Arbnum.fromString "229888")];
  val _ = Theory.incorporate_types "poregex" [("Reg", 1)];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "fun"), ID("list", "list"), ID("pair", "prod"),
   ID("min", "bool"), ID("poregex", "Reg"), ID("num", "num"),
   ID("ind_type", "recspace"), ID("bool", "!"), ID("arithmetic", "+"),
   ID("pair", ","), ID("bool", "/\\"), ID("num", "0"), ID("min", "="),
   ID("min", "==>"), ID("bool", "?"), ID("min", "@"), ID("list", "APPEND"),
   ID("bool", "ARB"), ID("poregex", "Alt"), ID("arithmetic", "BIT1"),
   ID("ind_type", "BOTTOM"), ID("bool", "COND"), ID("list", "CONS"),
   ID("ind_type", "CONSTR"), ID("bool", "DATATYPE"),
   ID("pred_set", "EMPTY"), ID("list", "EVERY"), ID("list", "EXISTS"),
   ID("poregex", "Eps"), ID("ind_type", "FCONS"), ID("list", "FILTER"),
   ID("list", "FLAT"), ID("pair", "FST"), ID("pred_set", "GSPEC"),
   ID("list", "HD"), ID("combin", "I"), ID("bool", "IN"),
   ID("pred_set", "INSERT"), ID("list", "LIST_TO_SET"), ID("list", "MAP"),
   ID("list", "NIL"), ID("arithmetic", "NUMERAL"),
   ID("poregex", "Reg_CASE"), ID("poregex", "Reg_size"),
   ID("poregex", "Rep"), ID("list", "SET_TO_LIST"), ID("pair", "SND"),
   ID("num", "SUC"), ID("poregex", "Seq"), ID("poregex", "Sym"),
   ID("list", "TL"), ID("bool", "TYPE_DEFINITION"), ID("pair", "UNCURRY"),
   ID("pred_set", "UNION"), ID("relation", "WF"), ID("relation", "WFREC"),
   ID("arithmetic", "ZERO"), ID("bool", "\\/"), ID("poregex", "accept"),
   ID("poregex", "language_of"), ID("list", "list_CASE"),
   ID("poregex", "parts"), ID("poregex", "parts'"), ID("poregex", "split"),
   ID("bool", "~")]
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
   TYOP [0, 29, 8], TYOP [0, 10, 8], TYOP [0, 1, 9], TYOP [0, 13, 8],
   TYOP [0, 14, 33], TYOP [0, 14, 34], TYOP [0, 12, 35], TYOP [0, 10, 36],
   TYOP [0, 19, 19], TYOP [0, 19, 38], TYOP [0, 10, 39], TYOP [0, 10, 40],
   TYOP [0, 10, 38], TYOP [0, 10, 29], TYOP [0, 0, 8], TYOP [0, 44, 8],
   TYOP [0, 19, 8], TYOP [0, 46, 8], TYOP [0, 31, 8], TYOP [0, 25, 8],
   TYOP [0, 49, 8], TYOP [0, 17, 8], TYOP [0, 51, 8], TYOP [0, 20, 8],
   TYOP [0, 53, 8], TYOP [0, 48, 8], TYOP [0, 42, 8], TYOP [0, 56, 8],
   TYOP [0, 22, 8], TYOP [0, 58, 8], TYOP [0, 41, 8], TYOP [0, 60, 8],
   TYOP [0, 11, 8], TYOP [0, 62, 8], TYOP [0, 9, 8], TYOP [0, 64, 8],
   TYOP [0, 30, 8], TYOP [0, 66, 8], TYOP [0, 5, 8], TYOP [0, 68, 8],
   TYOP [0, 2, 8], TYOP [0, 70, 8], TYOP [0, 15, 15], TYOP [0, 15, 72],
   TYOP [2, 1, 8], TYOP [0, 8, 74], TYOP [0, 1, 75], TYOP [0, 1, 2],
   TYOP [0, 1, 77], TYOP [2, 5, 8], TYOP [0, 8, 79], TYOP [0, 5, 80],
   TYOP [0, 8, 8], TYOP [0, 8, 82], TYOP [0, 0, 44], TYOP [0, 19, 46],
   TYOP [0, 10, 31], TYOP [0, 9, 64], TYOP [0, 7, 8], TYOP [0, 7, 88],
   TYOP [0, 5, 68], TYOP [0, 6, 8], TYOP [0, 6, 91], TYOP [0, 3, 8],
   TYOP [0, 3, 93], TYOP [0, 15, 8], TYOP [0, 15, 95], TYOP [0, 29, 30],
   TYOP [0, 43, 8], TYOP [0, 98, 8], TYOP [0, 93, 8], TYOP [0, 32, 8],
   TYOP [0, 101, 32], TYOP [0, 1, 1], TYOP [0, 1, 103], TYOP [0, 5, 5],
   TYOP [0, 5, 105], TYOP [0, 3, 3], TYOP [0, 3, 107], TYOP [0, 6, 6],
   TYOP [0, 6, 109], TYOP [0, 8, 110], TYOP [0, 0, 103], TYOP [0, 1, 105],
   TYOP [0, 5, 109], TYOP [0, 2, 107], TYOP [0, 15, 29], TYOP [0, 116, 29],
   TYOP [0, 0, 117], TYOP [0, 15, 118], TYOP [0, 9, 68], TYOP [0, 68, 91],
   TYOP [0, 70, 93], TYOP [0, 116, 116], TYOP [0, 29, 123],
   TYOP [0, 9, 105], TYOP [0, 5, 1], TYOP [1, 6], TYOP [0, 127, 6],
   TYOP [0, 2, 1], TYOP [0, 1, 74], TYOP [0, 130, 9], TYOP [0, 5, 79],
   TYOP [0, 132, 68], TYOP [0, 2, 74], TYOP [0, 134, 9], TYOP [0, 1, 64],
   TYOP [0, 5, 69], TYOP [0, 2, 71], TYOP [0, 9, 9], TYOP [0, 1, 139],
   TYOP [0, 5, 9], TYOP [0, 6, 68], TYOP [0, 3, 70], TYOP [0, 6, 127],
   TYOP [0, 5, 6], TYOP [0, 145, 144], TYOP [0, 2, 2], TYOP [0, 147, 107],
   TYOP [0, 68, 6], TYOP [0, 30, 98], TYOP [0, 1, 130], TYOP [0, 151, 134],
   TYOP [0, 9, 139], TYOP [0, 7, 7], TYOP [0, 154, 7], TYOP [0, 32, 155],
   TYOP [0, 0, 7], TYOP [0, 157, 6], TYOP [0, 6, 158], TYOP [0, 1, 159]]
  end
  val _ = Theory.incorporate_consts "poregex" tyvector
     [("split", 4), ("parts'", 7), ("parts", 7), ("language_of", 11),
      ("accept", 11), ("Sym", 12), ("Seq", 14), ("Rep", 13),
      ("Reg_size", 18), ("Reg_CASE", 28), ("Eps", 10), ("Alt", 14)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("'Reg'", 30), TMV("A", 1), TMV("B", 1), TMV("C", 3), TMV("D", 3),
   TMV("M", 10), TMV("M'", 10), TMV("P", 31), TMV("P", 11), TMV("P", 9),
   TMV("R", 10), TMV("R", 32), TMV("R0", 10), TMV("RR", 10),
   TMV("Reg", 37), TMV("a", 0), TMV("a", 10), TMV("a", 1), TMV("a", 29),
   TMV("a'", 0), TMV("a'", 10), TMV("a0", 10), TMV("a0", 29),
   TMV("a0'", 10), TMV("a0'", 29), TMV("a1", 10), TMV("a1", 29),
   TMV("a1'", 10), TMV("b", 10), TMV("c", 0), TMV("cs", 1), TMV("e", 1),
   TMV("e", 5), TMV("f", 10), TMV("f", 25), TMV("f", 17), TMV("f'", 25),
   TMV("f0", 19), TMV("f1", 25), TMV("f1", 22), TMV("f1'", 22),
   TMV("f2", 22), TMV("f2", 41), TMV("f2'", 22), TMV("f3", 20),
   TMV("f3", 41), TMV("f3'", 20), TMV("f4", 42), TMV("fn", 20),
   TMV("fstPrt", 1), TMV("h", 0), TMV("l", 1), TMV("l1", 1), TMV("l1'", 5),
   TMV("l2", 1), TMV("l2'", 5), TMV("ll", 5), TMV("n", 15), TMV("p", 10),
   TMV("part", 1), TMV("partit", 5), TMV("partition", 5), TMV("parts'", 7),
   TMV("q", 10), TMV("r", 10), TMV("rep", 43), TMV("s", 10),
   TMV("sndPrt", 1), TMV("t", 1), TMV("u", 1), TMV("v", 0), TMV("v", 19),
   TMV("v", 10), TMV("v", 1), TMV("v'", 19), TMV("v1", 1), TMV("v2", 0),
   TMV("v3", 1), TMV("words", 5), TMV("x", 0), TMV("x", 1), TMV("x", 5),
   TMV("x", 2), TMV("y", 1), TMC(7, 45), TMC(7, 47), TMC(7, 48),
   TMC(7, 50), TMC(7, 52), TMC(7, 54), TMC(7, 55), TMC(7, 57), TMC(7, 59),
   TMC(7, 61), TMC(7, 63), TMC(7, 65), TMC(7, 67), TMC(7, 64), TMC(7, 69),
   TMC(7, 71), TMC(7, 66), TMC(8, 73), TMC(9, 76), TMC(9, 78), TMC(9, 81),
   TMC(10, 83), TMC(11, 15), TMC(12, 84), TMC(12, 85), TMC(12, 86),
   TMC(12, 83), TMC(12, 87), TMC(12, 89), TMC(12, 32), TMC(12, 90),
   TMC(12, 92), TMC(12, 94), TMC(12, 96), TMC(12, 97), TMC(13, 83),
   TMC(14, 45), TMC(14, 48), TMC(14, 54), TMC(14, 99), TMC(14, 69),
   TMC(14, 100), TMC(14, 66), TMC(15, 102), TMC(16, 104), TMC(16, 106),
   TMC(16, 108), TMC(17, 0), TMC(18, 14), TMC(19, 72), TMC(20, 29),
   TMC(21, 111), TMC(22, 112), TMC(22, 113), TMC(22, 114), TMC(22, 115),
   TMC(23, 119), TMC(24, 82), TMC(25, 9), TMC(26, 120), TMC(27, 121),
   TMC(27, 122), TMC(28, 10), TMC(29, 124), TMC(30, 125), TMC(31, 126),
   TMC(31, 128), TMC(32, 129), TMC(33, 131), TMC(33, 133), TMC(33, 135),
   TMC(34, 126), TMC(35, 109), TMC(36, 136), TMC(36, 137), TMC(36, 138),
   TMC(37, 140), TMC(38, 141), TMC(38, 142), TMC(38, 143), TMC(39, 146),
   TMC(39, 148), TMC(40, 1), TMC(40, 5), TMC(40, 6), TMC(40, 3),
   TMC(41, 72), TMC(42, 28), TMC(43, 18), TMC(44, 13), TMC(45, 149),
   TMC(46, 129), TMC(47, 72), TMC(48, 14), TMC(49, 12), TMC(50, 105),
   TMC(51, 150), TMC(52, 152), TMC(53, 153), TMC(54, 101), TMC(55, 156),
   TMC(56, 15), TMC(57, 83), TMC(58, 11), TMC(59, 11), TMC(60, 160),
   TMC(61, 7), TMC(62, 7), TMC(63, 4), TMC(64, 82)]
  end
  structure ThmBind = struct
    val DT = Thm.disk_thm
    val read = Term.read_raw tmvector
  end
  fun op Reg_TY_DEF x = x
    val op Reg_TY_DEF =
    ThmBind.DT(((("poregex",0),
                [("bool",[14,25,26,52,131,132,137])]),["DISK_THM"]),
               [ThmBind.read"%123%65%180%24%96%0%119%100%24%119%186%118$0@%140%106@%131@%57%134|@3%186%120%15%118$1@%15%140%176%106@2$0@%57%134|@|$0@2|@2%186%126%22%126%26%105%118$2@%22%26%140%176%176%106@3%131@%147$1@%147$0@%57%134|@3||$1@$0@3%105$3$1@2$3$0@3|@|@2%186%126%22%126%26%105%118$2@%22%26%140%176%176%176%106@4%131@%147$1@%147$0@%57%134|@3||$1@$0@3%105$3$1@2$3$0@3|@|@2%126%18%105%118$1@%18%140%176%176%176%176%106@5%131@%147$0@%57%134|@2|$0@3$2$0@2|@6$1$0@2|@2$0$1@2|@|@$0@|@"])
  fun op Reg_case_def x = x
    val op Reg_case_def =
    ThmBind.DT(((("poregex",12),
                [("bool",[14,25,26,30,52,62,131,132,137,180]),
                 ("ind_type",[33,34]),
                 ("poregex",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%105%85%71%87%34%92%39%92%41%89%44%108%171%146@$4@$3@$2@$1@$0@2$4@|@|@|@|@|@2%105%84%15%85%71%87%34%92%39%92%41%89%44%108%171%178$5@2$4@$3@$2@$1@$0@2$3$5@2|@|@|@|@|@|@2%105%86%21%86%25%85%71%87%34%92%39%92%41%89%44%108%171%132$6@$5@2$4@$3@$2@$1@$0@2$2$6@$5@2|@|@|@|@|@|@|@2%105%86%21%86%25%85%71%87%34%92%39%92%41%89%44%108%171%177$6@$5@2$4@$3@$2@$1@$0@2$1$6@$5@2|@|@|@|@|@|@|@2%86%16%85%71%87%34%92%39%92%41%89%44%108%171%173$5@2$4@$3@$2@$1@$0@2$0$5@2|@|@|@|@|@|@5"])
  fun op Reg_size_def x = x
    val op Reg_size_def =
    ThmBind.DT(((("poregex",13),
                [("bool",[14,25,26,30,52,62,131,132,137,180]),
                 ("ind_type",[33,34]),
                 ("poregex",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%105%88%35%117%172$0@%146@2%106@|@2%105%88%35%84%15%117%172$1@%178$0@3%101%170%133%185@3$1$0@3|@|@2%105%88%35%86%21%86%25%117%172$2@%132$1@$0@3%101%170%133%185@3%101%172$2@$1@2%172$2@$0@4|@|@|@2%105%88%35%86%21%86%25%117%172$2@%177$1@$0@3%101%170%133%185@3%101%172$2@$1@2%172$2@$0@4|@|@|@2%88%35%86%16%117%172$1@%173$0@3%101%170%133%185@3%172$1@$0@3|@|@5"])
  fun op language_of_def x = x
    val op language_of_def =
    ThmBind.DT(((("poregex",21),
                [("bool",[14,25,26,30,52,62,131,132,137,180]),
                 ("ind_type",[33,34]),
                 ("poregex",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%105%111%188%146@2%160%166@%142@3%105%84%29%111%188%178$0@3%160%136$0@%166@2%142@2|@2%105%86%16%86%28%111%188%132$1@$0@3%182%188$1@2%188$0@3|@|@2%105%86%33%86%66%111%188%177$1@$0@3%154%181%49%67%102%128$1@$0@2%105%157$1@%188$3@3%157$0@%188$2@4||@3|@|@2%86%64%111%188%173$0@3%152%80%102$0@%124%78%105%193%114$0@%167@3%105%143%31%157$0@%188$3@2|@$0@2%113%149$0@2$1@3|@2|@2|@5"])
  fun op split_def x = x
    val op split_def =
    ThmBind.DT(((("poregex",22),[("list",[13])]),["DISK_THM"]),
               [ThmBind.read"%105%116%192%166@2%139%103%166@%166@2%169@3%84%29%97%30%116%192%136$1@$0@3%139%103%166@%136$1@$0@3%165%82%103%136$2@%151$0@3%175$0@2|@%192$0@4|@|@2"])
  fun op parts_def x = x
    val op parts_def =
    ThmBind.DT(((("poregex",24),[("list",[13])]),["DISK_THM"]),
               [ThmBind.read"%105%115%190%166@2%138%167@%168@3%84%29%97%30%115%190%136$1@$0@3%135%113$0@%166@2%138%137%136$1@%166@2%167@2%168@2%150%164%81%138%137%136$2@%166@2$0@2%138%137%136$2@%155$0@3%179$0@3%168@2|@%190$0@5|@|@2"])
  fun op parts'_primitive_def x = x
    val op parts'_primitive_def =
    ThmBind.DT(((("poregex",34),[]),[]),
               [ThmBind.read"%112%191@%184%127%11%183$0@|@2%62%17%189$0@%156%138%167@%168@3%76%77%156%174%153%60%104$0@%105%114%148%83%193%113%166@$0@2|@$0@2$0@2%113%149$0@2%136$2@$1@4|@3||@||@2"])
  fun op accept_ind x = x
    val op accept_ind =
    ThmBind.DT(((("poregex",45),
                [("arithmetic",[24,25,26,27,41,46,59,73,95,179,186]),
                 ("bool",
                 [14,25,26,27,35,50,51,52,53,57,62,92,95,103,104,106,123,
                  131,132,137,180]),("list",[46]),("numeral",[3,7,8]),
                 ("pair",[5,7,8,9,16,25]),
                 ("poregex",[1,2,3,4,5,6,7,8,9,10,11,13]),
                 ("prim_rec",[42]),("relation",[107,119,121]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%94%8%119%105%97%69$1%146@$0@|@2%105%84%29%97%69$2%178$1@2$0@|@|@2%105%86%58%86%63%97%69%119%105$3$2@$0@2$3$1@$0@3$3%132$2@$1@2$0@2|@|@|@2%105%86%58%86%63%97%69%119%105%99%82%119%159$0@%163%192$1@4$4$3@%151$0@3|@2%99%82%119%159$0@%163%192$1@4$4$2@%175$0@3|@3$3%177$2@$1@2$0@2|@|@|@2%105%86%64%119$1$0@%166@2$1%173$0@2%166@2|@2%86%64%84%50%97%68%119%98%61%97%59%119%105%158$1@%162%190%136$3@$2@5%157$0@%161$1@4$5$4@$0@2|@|@2$3%173$2@2%136$1@$0@3|@|@|@7%86%72%97%75$2$1@$0@|@|@2|@"])
  fun op PARTS_MEM_APPEND_THM2 x = x
    val op PARTS_MEM_APPEND_THM2 =
    ThmBind.DT(((("poregex",38),
                [("bool",[25,26,27,35,50,51,52,53,55,57,104,123]),
                 ("list",[82,85,106]),("poregex",[33])]),["DISK_THM"]),
               [ThmBind.read"%97%52%97%54%98%53%98%55%119%158$1@%162%190$3@4%119%158$0@%162%190$2@4%158%129$1@$0@2%162%190%128$3@$2@6|@|@|@|@"])
  fun op PARTS_MEM_APPEND_THM1 x = x
    val op PARTS_MEM_APPEND_THM1 =
    ThmBind.DT(((("poregex",31),
                [("bool",[25,26,27,35,50,51,52,53,55,57,104,123]),
                 ("list",[82,85,106]),("poregex",[25])]),["DISK_THM"]),
               [ThmBind.read"%97%52%97%54%98%53%98%55%119%158$1@%162%190$3@4%119%158$0@%162%190$2@4%158%129$1@$0@2%162%190%128$3@$2@6|@|@|@|@"])
  fun op PARTS_MEM_HEAD_THM x = x
    val op PARTS_MEM_HEAD_THM =
    ThmBind.DT(((("poregex",30),
                [("bool",[25,26,27,35,50,51,55]),
                 ("list",[20,21,48,49,122]),
                 ("poregex",[25])]),["DISK_THM"]),
               [ThmBind.read"%84%50%97%68%98%32%110%158$0@%162%190$1@4%158%137%136$2@%166@2$0@2%162%190%136$2@$1@5|@|@|@"])
  fun op PARTS_SINGEl_THM x = x
    val op PARTS_SINGEl_THM =
    ThmBind.DT(((("poregex",29),
                [("bool",[25,26,27,35,51,55,57,63,104,128]),
                 ("list",[20,21,23,25]),("poregex",[24]),
                 ("pred_set",[18,88])]),["DISK_THM"]),
               [ThmBind.read"%98%32%84%79%110%114$1@%137%136$0@%166@2%167@3%158$1@%162%190%136$0@%166@5|@|@"])
  fun op PARTS_EMPTY_THM2 x = x
    val op PARTS_EMPTY_THM2 =
    ThmBind.DT(((("poregex",28),
                [("bool",[25,35,50,52,53,55,57,104,123]),("list",[21,122]),
                 ("poregex",[25])]),["DISK_THM"]),
               [ThmBind.read"%97%31%119%158%167@%162%190$0@4%113$0@%166@2|@"])
  fun op PARTS_NON_EMPTY_THM x = x
    val op PARTS_NON_EMPTY_THM =
    ThmBind.DT(((("poregex",27),
                [("bool",[25,26,27,35,52,53,57,62,92,94,100,104,123,144]),
                 ("poregex",[26])]),["DISK_THM"]),
               [ThmBind.read"%97%31%98%81%119%193%114$0@%167@3%119%158$0@%162%190$1@4%193%113$1@%166@4|@|@"])
  fun op PARTS_EMPTY_THM x = x
    val op PARTS_EMPTY_THM =
    ThmBind.DT(((("poregex",26),
                [("bool",[25,26,27,35,51,55]),("list",[25]),
                 ("poregex",[24]),("pred_set",[18,88])]),["DISK_THM"]),
               [ThmBind.read"%98%32%110%114$0@%167@2%158$0@%162%190%166@4|@"])
  fun op datatype_Reg x = x
    val op datatype_Reg =
    ThmBind.DT(((("poregex",14),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%141%14%146@%178@%132@%177@%173@2"])
  fun op Reg_11 x = x
    val op Reg_11 =
    ThmBind.DT(((("poregex",15),
                [("bool",[14,25,26,30,50,52,55,62,131,132,137,180]),
                 ("ind_type",[33,34]),
                 ("poregex",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%105%84%15%84%19%110%109%178$1@2%178$0@3%107$1@$0@2|@|@2%105%86%21%86%25%86%23%86%27%110%109%132$3@$2@2%132$1@$0@3%105%109$3@$1@2%109$2@$0@3|@|@|@|@2%105%86%21%86%25%86%23%86%27%110%109%177$3@$2@2%177$1@$0@3%105%109$3@$1@2%109$2@$0@3|@|@|@|@2%86%16%86%20%110%109%173$1@2%173$0@3%109$1@$0@2|@|@4"])
  fun op Reg_distinct x = x
    val op Reg_distinct =
    ThmBind.DT(((("poregex",16),
                [("bool",
                 [14,25,26,30,35,46,50,52,53,55,62,131,132,137,180]),
                 ("ind_type",[33,34]),
                 ("poregex",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%105%84%15%193%109%146@%178$0@3|@2%105%86%25%86%21%193%109%146@%132$0@$1@3|@|@2%105%86%25%86%21%193%109%146@%177$0@$1@3|@|@2%105%86%16%193%109%146@%173$0@3|@2%105%86%25%86%21%84%15%193%109%178$0@2%132$1@$2@3|@|@|@2%105%86%25%86%21%84%15%193%109%178$0@2%177$1@$2@3|@|@|@2%105%86%20%84%15%193%109%178$0@2%173$1@3|@|@2%105%86%27%86%25%86%23%86%21%193%109%132$0@$2@2%177$1@$3@3|@|@|@|@2%105%86%25%86%21%86%16%193%109%132$1@$2@2%173$0@3|@|@|@2%86%25%86%21%86%16%193%109%177$1@$2@2%173$0@3|@|@|@10"])
  fun op Reg_case_cong x = x
    val op Reg_case_cong =
    ThmBind.DT(((("poregex",17),
                [("bool",[14,25,26,52,131,132,137,180]),
                 ("poregex",[1,2,3,4,5,6,7,8,9,10,11,12])]),["DISK_THM"]),
               [ThmBind.read"%86%5%86%6%85%71%87%34%92%39%92%41%89%44%119%105%109$6@$5@2%105%119%109$5@%146@2%108$4@%74@3%105%84%15%119%109$6@%178$0@3%108$4$0@2%36$0@3|@2%105%86%21%86%25%119%109$7@%132$1@$0@3%108$4$1@$0@2%40$1@$0@3|@|@2%105%86%21%86%25%119%109$7@%177$1@$0@3%108$3$1@$0@2%43$1@$0@3|@|@2%86%16%119%109$6@%173$0@3%108$1$0@2%46$0@3|@7%108%171$6@$4@$3@$2@$1@$0@2%171$5@%74@%36@%40@%43@%46@3|@|@|@|@|@|@|@"])
  fun op Reg_nchotomy x = x
    val op Reg_nchotomy =
    ThmBind.DT(((("poregex",18),
                [("bool",[14,25,26,52,131,132,137,180]),
                 ("poregex",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%86%13%186%109$0@%146@2%186%120%15%109$1@%178$0@2|@2%186%121%10%121%12%109$2@%132$1@$0@2|@|@2%186%121%10%121%12%109$2@%177$1@$0@2|@|@2%121%10%109$1@%173$0@2|@5|@"])
  fun op Reg_Axiom x = x
    val op Reg_Axiom =
    ThmBind.DT(((("poregex",19),
                [("bool",[14,25,26,30,52,62,131,132,137,180]),
                 ("ind_type",[33,34]),
                 ("poregex",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%85%37%87%38%93%42%93%45%91%47%122%48%105%108$0%146@2$5@2%105%84%15%108$1%178$0@3$5$0@2|@2%105%86%21%86%25%108$2%132$1@$0@3$5$1@$0@$2$1@2$2$0@3|@|@2%105%86%21%86%25%108$2%177$1@$0@3$4$1@$0@$2$1@2$2$0@3|@|@2%86%16%108$1%173$0@3$2$0@$1$0@3|@5|@|@|@|@|@|@"])
  fun op Reg_induction x = x
    val op Reg_induction =
    ThmBind.DT(((("poregex",20),
                [("bool",[14,25,26,52,131,132,137]),
                 ("poregex",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%90%7%119%105$0%146@2%105%84%15$1%178$0@2|@2%105%86%10%86%12%119%105$2$1@2$2$0@3$2%132$1@$0@3|@|@2%105%86%10%86%12%119%105$2$1@2$2$0@3$2%177$1@$0@3|@|@2%86%10%119$1$0@2$1%173$0@3|@6%86%10$1$0@|@2|@"])
  fun op SPLIT_APPEND_THM x = x
    val op SPLIT_APPEND_THM =
    ThmBind.DT(((("poregex",23),
                [("bool",[2,14,15,25,26,50,52,53,55,57,62,139]),
                 ("list",[20,23,43,46,48,58,106]),("pair",[4,8,9]),
                 ("poregex",[22]),("sat",[1,3,7,17,18])]),["DISK_THM"]),
               [ThmBind.read"%97%1%97%2%125%3%125%4%116%192%128$3@$2@3%130%130$1@%139%103$3@$2@2%169@3$0@2|@|@|@|@"])
  fun op parts_SPEC x = x
    val op parts_SPEC =
    ThmBind.DT(((("poregex",33),
                [("bool",
                 [5,14,25,26,27,29,35,36,50,51,52,53,54,55,57,62,63,70,74,
                  91,95,99,104,107,108,123,128,142,177]),
                 ("list",
                 [17,18,20,21,25,43,46,48,49,72,84,91,102,103,122,414]),
                 ("poregex",[24]),("pred_set",[18,88]),
                 ("sat",[1,3,5,6,7,11,12,13,15,17,18])]),["DISK_THM"]),
               [ThmBind.read"%97%51%98%56%110%158$0@%162%190$1@4%105%193%157%166@%161$0@4%113%149$0@2$1@3|@|@"])
  fun op parts'_ind x = x
    val op parts'_ind =
    ThmBind.DT(((("poregex",35),
                [("bool",[25,27,52,53,62]),("list",[46]),
                 ("relation",[107,113]),
                 ("sat",[1,3,5,6,7,11,15])]),["DISK_THM"]),
               [ThmBind.read"%95%9%119%105$0%166@2%84%70%97%75$2%136$1@$0@2|@|@3%97%73$1$0@|@2|@"])
  fun op parts'_def x = x
    val op parts'_def =
    ThmBind.DT(((("poregex",36),
                [("bool",[15]),("combin",[19]),("list",[6]),
                 ("poregex",[34]),("relation",[113,132])]),["DISK_THM"]),
               [ThmBind.read"%105%115%191%166@2%138%167@%168@3%115%191%136%70@%75@3%174%153%60%104$0@%105%114%148%83%193%113%166@$0@2|@$0@2$0@2%113%149$0@2%136%70@%75@4|@4"])
  fun op PARTS_FLAT_MEM_THM x = x
    val op PARTS_FLAT_MEM_THM =
    ThmBind.DT(((("poregex",37),
                [("bool",
                 [5,14,25,26,27,29,50,51,52,53,55,57,62,63,100,104,107,108,
                  128,144]),("list",[20,21,26,43,83,106]),
                 ("poregex",[33])]),["DISK_THM"]),
               [ThmBind.read"%98%61%97%51%119%113%149$1@2$0@2%158%148%83%193%113%166@$0@2|@$1@2%162%190$0@4|@|@"])
  fun op accept_def x = x
    val op accept_def =
    ThmBind.DT(((("poregex",46),
                [("arithmetic",[24,25,26,27,41,46,59,73,95,179,186]),
                 ("bool",
                 [15,25,35,50,51,52,53,57,62,92,95,103,104,106,123]),
                 ("combin",[19]),("list",[6,155,156]),("numeral",[3,7,8]),
                 ("pair",[7,8,9,16,25,49]),("poregex",[12,13,43,44]),
                 ("prim_rec",[42]),("relation",[119,121,127,132]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%105%97%69%110%187%146@$0@2%113$0@%166@2|@2%105%97%69%84%29%110%187%178$0@2$1@2%113$1@%136$0@%166@3|@|@2%105%97%69%86%63%86%58%110%187%132$0@$1@2$2@2%186%187$0@$2@2%187$1@$2@3|@|@|@2%105%97%69%86%63%86%58%110%187%177$0@$1@2$2@2%145%82%105%187$1@%151$0@3%187$2@%175$0@3|@%192$2@3|@|@|@2%105%86%64%110%187%173$0@2%166@2%187$0@%166@2|@2%97%68%86%64%84%50%110%187%173$1@2%136$0@$2@3%144%61%143%59%187$3@$0@|@$0@|@%190%136$0@$2@4|@|@|@6"])

  val _ = DB.bindl "poregex"
  [("Reg_TY_DEF",Reg_TY_DEF,DB.Def), ("Reg_case_def",Reg_case_def,DB.Def),
   ("Reg_size_def",Reg_size_def,DB.Def),
   ("language_of_def",language_of_def,DB.Def),
   ("split_def",split_def,DB.Def), ("parts_def",parts_def,DB.Def),
   ("parts'_primitive_def",parts'_primitive_def,DB.Def),
   ("accept_ind",accept_ind,DB.Thm),
   ("PARTS_MEM_APPEND_THM2",PARTS_MEM_APPEND_THM2,DB.Thm),
   ("PARTS_MEM_APPEND_THM1",PARTS_MEM_APPEND_THM1,DB.Thm),
   ("PARTS_MEM_HEAD_THM",PARTS_MEM_HEAD_THM,DB.Thm),
   ("PARTS_SINGEl_THM",PARTS_SINGEl_THM,DB.Thm),
   ("PARTS_EMPTY_THM2",PARTS_EMPTY_THM2,DB.Thm),
   ("PARTS_NON_EMPTY_THM",PARTS_NON_EMPTY_THM,DB.Thm),
   ("PARTS_EMPTY_THM",PARTS_EMPTY_THM,DB.Thm),
   ("datatype_Reg",datatype_Reg,DB.Thm), ("Reg_11",Reg_11,DB.Thm),
   ("Reg_distinct",Reg_distinct,DB.Thm),
   ("Reg_case_cong",Reg_case_cong,DB.Thm),
   ("Reg_nchotomy",Reg_nchotomy,DB.Thm), ("Reg_Axiom",Reg_Axiom,DB.Thm),
   ("Reg_induction",Reg_induction,DB.Thm),
   ("SPLIT_APPEND_THM",SPLIT_APPEND_THM,DB.Thm),
   ("parts_SPEC",parts_SPEC,DB.Thm), ("parts'_ind",parts'_ind,DB.Thm),
   ("parts'_def",parts'_def,DB.Thm),
   ("PARTS_FLAT_MEM_THM",PARTS_FLAT_MEM_THM,DB.Thm),
   ("accept_def",accept_def,DB.Thm)]

  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "poregex",
    thydataty = "compute",
    read = ThmBind.read,
    data =
        "poregex.split_def poregex.parts_def poregex.accept_def poregex.parts'_def poregex.language_of_def"
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
        "OO3.Eps4.%146OO3.Sym4.%178OO3.Alt4.%132OO3.Seq4.%177OO3.Rep4.%173OO8.Reg_CASE4.%171OO8.Reg_size4.%172OO4.case4.%171OO11.language_of4.%188OO5.split4.%192OO5.parts4.%190OO6.parts'4.%191OO6.accept4.%187"
  }
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val poregex_grammars = merge_grammars ["basis_emit"]
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


  val _ = 
     let open Parse
         fun doit (r,(b,s,ty)) = 
           let val c = Term.mk_thy_const r
           in ConstMapML.prim_insert(c,(b,"poregex",s,ty))
           end
         fun typ s = Feedback.trace ("Vartype Format Complaint", 0)
                      (#1 (parse_from_grammars min_grammars))
                      [QUOTE (":"^s)]
     in
       List.app doit [
         ({Name = "Eps", Thy = "poregex", Ty = typ "'a poregex$Reg"},
          (true, "Eps", typ "'a poregex$Reg")),
         ({Name = "Sym", Thy = "poregex", Ty = typ "'a -> 'a poregex$Reg"},
          (true, "Sym", typ "'a -> 'a poregex$Reg")),
         ({Name = "Alt", Thy = "poregex",
           Ty = typ "'a poregex$Reg -> 'a poregex$Reg -> 'a poregex$Reg"},
          (true, "Alt",
           typ "'a poregex$Reg -> 'a poregex$Reg -> 'a poregex$Reg")),
         ({Name = "Seq", Thy = "poregex",
           Ty = typ "'a poregex$Reg -> 'a poregex$Reg -> 'a poregex$Reg"},
          (true, "Seq",
           typ "'a poregex$Reg -> 'a poregex$Reg -> 'a poregex$Reg")),
         ({Name = "Rep", Thy = "poregex",
           Ty = typ "'a poregex$Reg -> 'a poregex$Reg"},
          (true, "Rep", typ "'a poregex$Reg -> 'a poregex$Reg")),
         ({Name = "split", Thy = "poregex",
           Ty =
             typ
             "'a list$list -> ('a list$list, 'a list$list) pair$prod list$list"},
          (false, "split",
           typ
           "'a list$list -> ('a list$list, 'a list$list) pair$prod list$list")),
         ({Name = "parts", Thy = "poregex",
           Ty = typ "''a list$list -> ''a list$list list$list list$list"},
          (false, "parts",
           typ "''a list$list -> ''a list$list list$list list$list")),
         ({Name = "accept", Thy = "poregex",
           Ty = typ "''a poregex$Reg -> ''a list$list -> bool"},
          (false, "accept",
           typ "''a poregex$Reg -> ''a list$list -> bool"))
       ]
     end


val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "poregex"
end
