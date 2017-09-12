structure scratchTheory :> scratchTheory =
struct
  val _ = if !Globals.print_thy_loads then TextIO.print "Loading scratchTheory ... " else ()
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
          ("scratch",
          Arbnum.fromString "1492712681",
          Arbnum.fromString "976717")
          [("basis_emit",
           Arbnum.fromString "1492712999",
           Arbnum.fromString "229888")];
  val _ = Theory.incorporate_types "scratch" [("MReg", 1)];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "fun"), ID("scratch", "MReg"), ID("min", "bool"),
   ID("num", "num"), ID("ind_type", "recspace"), ID("pair", "prod"),
   ID("bool", "!"), ID("arithmetic", "+"), ID("pair", ","),
   ID("bool", "/\\"), ID("num", "0"), ID("min", "="), ID("min", "==>"),
   ID("bool", "?"), ID("min", "@"), ID("bool", "ARB"),
   ID("arithmetic", "BIT1"), ID("ind_type", "BOTTOM"),
   ID("ind_type", "CONSTR"), ID("bool", "DATATYPE"), ID("bool", "F"),
   ID("ind_type", "FCONS"), ID("combin", "I"), ID("scratch", "MARK_REG"),
   ID("scratch", "MAlt"), ID("scratch", "MEps"),
   ID("scratch", "MReg_CASE"), ID("scratch", "MReg_size"),
   ID("scratch", "MRep"), ID("scratch", "MSeq"), ID("scratch", "MSym"),
   ID("arithmetic", "NUMERAL"), ID("num", "SUC"), ID("bool", "T"),
   ID("bool", "TYPE_DEFINITION"), ID("relation", "WF"),
   ID("relation", "WFREC"), ID("arithmetic", "ZERO"), ID("bool", "\\/"),
   ID("basicSize", "bool_size"), ID("scratch", "empty"),
   ID("scratch", "final"), ID("scratch", "shift"), ID("bool", "~")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYV "'a", TYOP [1, 0], TYOP [0, 0, 1], TYOP [0, 1, 2], TYOP [2],
   TYOP [0, 4, 3], TYOP [0, 1, 4], TYOP [0, 4, 2], TYOP [0, 1, 1],
   TYOP [0, 1, 8], TYOP [3], TYOP [0, 1, 10], TYOP [0, 0, 10],
   TYOP [0, 12, 11], TYV "'b", TYOP [0, 1, 14], TYOP [0, 15, 14],
   TYOP [0, 1, 15], TYOP [0, 17, 16], TYOP [0, 17, 18], TYOP [0, 0, 14],
   TYOP [0, 4, 20], TYOP [0, 21, 19], TYOP [0, 14, 22], TYOP [0, 1, 23],
   TYOP [0, 14, 1], TYOP [5, 4, 0], TYOP [4, 26], TYOP [0, 27, 4],
   TYOP [0, 8, 4], TYOP [0, 9, 29], TYOP [0, 9, 30], TYOP [0, 7, 31],
   TYOP [0, 1, 32], TYOP [0, 14, 4], TYOP [0, 14, 34], TYOP [0, 14, 14],
   TYOP [0, 14, 36], TYOP [0, 1, 37], TYOP [0, 1, 38], TYOP [0, 1, 36],
   TYOP [0, 1, 27], TYOP [0, 0, 4], TYOP [0, 42, 4], TYOP [0, 34, 4],
   TYOP [0, 6, 4], TYOP [0, 4, 4], TYOP [0, 46, 4], TYOP [0, 12, 4],
   TYOP [0, 48, 4], TYOP [0, 44, 4], TYOP [0, 15, 4], TYOP [0, 51, 4],
   TYOP [0, 45, 4], TYOP [0, 40, 4], TYOP [0, 54, 4], TYOP [0, 17, 4],
   TYOP [0, 56, 4], TYOP [0, 39, 4], TYOP [0, 58, 4], TYOP [0, 21, 4],
   TYOP [0, 60, 4], TYOP [0, 28, 4], TYOP [0, 62, 4], TYOP [0, 10, 10],
   TYOP [0, 10, 64], TYOP [0, 0, 26], TYOP [0, 4, 66], TYOP [0, 4, 46],
   TYOP [0, 0, 42], TYOP [0, 1, 6], TYOP [0, 25, 4], TYOP [0, 25, 71],
   TYOP [0, 10, 4], TYOP [0, 10, 73], TYOP [0, 27, 28], TYOP [0, 41, 4],
   TYOP [0, 76, 4], TYOP [0, 35, 4], TYOP [0, 78, 35], TYOP [0, 10, 27],
   TYOP [0, 80, 27], TYOP [0, 26, 81], TYOP [0, 10, 82], TYOP [0, 80, 80],
   TYOP [0, 27, 84], TYOP [0, 28, 76], TYOP [0, 25, 25], TYOP [0, 87, 25],
   TYOP [0, 35, 88], TYOP [0, 4, 10]]
  end
  val _ = Theory.incorporate_consts "scratch" tyvector
     [("shift", 5), ("final", 6), ("empty", 6), ("MSym", 7), ("MSeq", 9),
      ("MRep", 8), ("MReg_size", 13), ("MReg_CASE", 24), ("MEps", 1),
      ("MAlt", 9), ("MARK_REG", 25)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("'MReg'", 28), TMV("Eps", 14), TMV("M", 1), TMV("M'", 1),
   TMV("M0", 1), TMV("MARK_REG", 25), TMV("MM", 1), TMV("MReg", 33),
   TMV("P", 34), TMV("P", 6), TMV("R", 35), TMV("a", 0), TMV("a", 1),
   TMV("a", 27), TMV("a'", 1), TMV("a0", 1), TMV("a0", 4), TMV("a0", 27),
   TMV("a0'", 1), TMV("a0'", 4), TMV("a0'", 27), TMV("a1", 0),
   TMV("a1", 1), TMV("a1", 27), TMV("a1'", 0), TMV("a1'", 1), TMV("b", 4),
   TMV("c", 0), TMV("f", 12), TMV("f", 21), TMV("f'", 21), TMV("f0", 14),
   TMV("f1", 17), TMV("f1", 21), TMV("f1'", 17), TMV("f2", 17),
   TMV("f2", 39), TMV("f2'", 17), TMV("f3", 15), TMV("f3", 39),
   TMV("f3'", 15), TMV("f4", 40), TMV("fn", 15), TMV("m", 4), TMV("n", 10),
   TMV("p", 1), TMV("q", 1), TMV("r", 1), TMV("rep", 41), TMV("v", 14),
   TMV("v'", 14), TMV("v0", 0), TMV("v0", 4), TMV("v1", 0), TMV("v2", 1),
   TMV("v2", 4), TMV("x", 0), TMC(6, 43), TMC(6, 44), TMC(6, 45),
   TMC(6, 47), TMC(6, 49), TMC(6, 50), TMC(6, 52), TMC(6, 53), TMC(6, 55),
   TMC(6, 57), TMC(6, 59), TMC(6, 61), TMC(6, 63), TMC(6, 62), TMC(7, 65),
   TMC(8, 67), TMC(9, 68), TMC(10, 10), TMC(11, 69), TMC(11, 35),
   TMC(11, 70), TMC(11, 68), TMC(11, 72), TMC(11, 74), TMC(11, 75),
   TMC(12, 68), TMC(13, 43), TMC(13, 45), TMC(13, 47), TMC(13, 52),
   TMC(13, 77), TMC(13, 62), TMC(14, 79), TMC(15, 0), TMC(15, 4),
   TMC(16, 64), TMC(17, 27), TMC(18, 83), TMC(19, 46), TMC(20, 4),
   TMC(21, 85), TMC(22, 8), TMC(23, 25), TMC(24, 9), TMC(25, 1),
   TMC(26, 24), TMC(27, 13), TMC(28, 8), TMC(29, 9), TMC(30, 7),
   TMC(31, 64), TMC(32, 64), TMC(33, 4), TMC(34, 86), TMC(35, 78),
   TMC(36, 89), TMC(37, 10), TMC(38, 68), TMC(39, 90), TMC(40, 6),
   TMC(41, 6), TMC(42, 5), TMC(43, 46)]
  end
  structure ThmBind = struct
    val DT = Thm.disk_thm
    val read = Term.read_raw tmvector
  end
  fun op MReg_TY_DEF x = x
    val op MReg_TY_DEF =
    ThmBind.DT(((("scratch",0),
                [("bool",[14,25,26,52,131,132,137])]),["DISK_THM"]),
               [ThmBind.read"%87%48%110%20%69%0%82%70%20%82%114%81$0@%94%74@%72%91@%90@2%44%93|@3%114%85%16%83%21%81$2@%16%21%94%108%74@2%72$1@$0@2%44%93|@||$1@$0@2|@|@2%114%88%17%88%23%73%81$2@%17%23%94%108%108%74@3%72%91@%90@2%97$1@%97$0@%44%93|@3||$1@$0@3%73$3$1@2$3$0@3|@|@2%114%88%17%88%23%73%81$2@%17%23%94%108%108%108%74@4%72%91@%90@2%97$1@%97$0@%44%93|@3||$1@$0@3%73$3$1@2$3$0@3|@|@2%88%13%73%81$1@%13%94%108%108%108%108%74@5%72%91@%90@2%97$0@%44%93|@2|$0@3$2$0@2|@6$1$0@2|@2$0$1@2|@|@$0@|@"])
  fun op MReg_case_def x = x
    val op MReg_case_def =
    ThmBind.DT(((("scratch",12),
                [("bool",[14,25,26,30,52,62,131,132,137,180]),
                 ("ind_type",[33,34]),("pair",[8,9]),
                 ("scratch",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%73%58%49%68%29%66%32%66%35%63%38%76%102%101@$4@$3@$2@$1@$0@2$4@|@|@|@|@|@2%73%60%16%57%21%58%49%68%29%66%32%66%35%63%38%76%102%106$6@$5@2$4@$3@$2@$1@$0@2$3$6@$5@2|@|@|@|@|@|@|@2%73%59%15%59%22%58%49%68%29%66%32%66%35%63%38%76%102%100$6@$5@2$4@$3@$2@$1@$0@2$2$6@$5@2|@|@|@|@|@|@|@2%73%59%15%59%22%58%49%68%29%66%32%66%35%63%38%76%102%105$6@$5@2$4@$3@$2@$1@$0@2$1$6@$5@2|@|@|@|@|@|@|@2%59%12%58%49%68%29%66%32%66%35%63%38%76%102%104$5@2$4@$3@$2@$1@$0@2$0$5@2|@|@|@|@|@|@5"])
  fun op MReg_size_def x = x
    val op MReg_size_def =
    ThmBind.DT(((("scratch",13),
                [("bool",[14,25,26,30,52,62,131,132,137,180]),
                 ("ind_type",[33,34]),("pair",[8,9]),
                 ("scratch",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%73%61%28%80%103$0@%101@2%74@|@2%73%61%28%60%16%57%21%80%103$2@%106$1@$0@3%71%107%92%113@3%71%115$1@2$2$0@4|@|@|@2%73%61%28%59%15%59%22%80%103$2@%100$1@$0@3%71%107%92%113@3%71%103$2@$1@2%103$2@$0@4|@|@|@2%73%61%28%59%15%59%22%80%103$2@%105$1@$0@3%71%107%92%113@3%71%103$2@$1@2%103$2@$0@4|@|@|@2%61%28%59%12%80%103$1@%104$0@3%71%107%92%113@3%103$1@$0@3|@|@5"])
  fun op MARK_REG_primitive_def x = x
    val op MARK_REG_primitive_def =
    ThmBind.DT(((("scratch",21),[]),[]),
               [ThmBind.read"%79%99@%112%89%10%111$0@|@2%5%1%98%101@||@2"])
  fun op empty_def x = x
    val op empty_def =
    ThmBind.DT(((("scratch",24),
                [("bool",[14,25,26,30,52,62,131,132,137,180]),
                 ("ind_type",[33,34]),("pair",[8,9]),
                 ("scratch",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%73%78%116%101@2%109@2%73%60%52%57%53%78%116%106$1@$0@3%96@|@|@2%73%59%45%59%46%78%116%100$1@$0@3%114%116$1@2%116$0@3|@|@2%73%59%45%59%46%78%116%105$1@$0@3%73%116$1@2%116$0@3|@|@2%59%54%78%116%104$0@3%109@|@5"])
  fun op final_def x = x
    val op final_def =
    ThmBind.DT(((("scratch",25),
                [("bool",[14,25,26,30,52,62,131,132,137,180]),
                 ("ind_type",[33,34]),("pair",[8,9]),
                 ("scratch",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%73%78%117%101@2%96@2%73%60%26%57%51%78%117%106$1@$0@3$1@|@|@2%73%59%45%59%46%78%117%100$1@$0@3%114%117$1@2%117$0@3|@|@2%73%59%45%59%46%78%117%105$1@$0@3%114%73%117$1@2%116$0@3%117$0@3|@|@2%59%47%78%117%104$0@3%117$0@2|@5"])
  fun op shift_def x = x
    val op shift_def =
    ThmBind.DT(((("scratch",26),
                [("bool",[14,25,26,30,52,62,131,132,137,180]),
                 ("ind_type",[33,34]),("pair",[8,9]),
                 ("scratch",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%73%60%52%57%53%77%118$1@%101@$0@2%101@|@|@2%73%60%43%60%55%57%56%57%27%77%118$3@%106$2@$1@2$0@2%106%73$3@%75$1@$0@3$1@2|@|@|@|@2%73%60%43%59%45%59%46%57%27%77%118$3@%100$2@$1@2$0@2%100%118$3@$2@$0@2%118$3@$1@$0@3|@|@|@|@2%73%60%43%59%45%59%46%57%27%77%118$3@%105$2@$1@2$0@2%105%118$3@$2@$0@2%118%114%73$3@%116$2@3%117$2@3$1@$0@3|@|@|@|@2%60%43%59%47%57%27%77%118$2@%104$1@2$0@2%104%118%114$2@%117$1@3$1@$0@3|@|@|@5"])
  fun op datatype_MReg x = x
    val op datatype_MReg =
    ThmBind.DT(((("scratch",14),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%95%7%101@%106@%100@%105@%104@2"])
  fun op MReg_11 x = x
    val op MReg_11 =
    ThmBind.DT(((("scratch",15),
                [("bool",[14,25,26,30,50,52,55,62,131,132,137,180]),
                 ("ind_type",[33,34]),("pair",[8,9]),
                 ("scratch",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%73%60%16%57%21%60%19%57%24%78%77%106$3@$2@2%106$1@$0@3%73%78$3@$1@2%75$2@$0@3|@|@|@|@2%73%59%15%59%22%59%18%59%25%78%77%100$3@$2@2%100$1@$0@3%73%77$3@$1@2%77$2@$0@3|@|@|@|@2%73%59%15%59%22%59%18%59%25%78%77%105$3@$2@2%105$1@$0@3%73%77$3@$1@2%77$2@$0@3|@|@|@|@2%59%12%59%14%78%77%104$1@2%104$0@3%77$1@$0@2|@|@4"])
  fun op MReg_distinct x = x
    val op MReg_distinct =
    ThmBind.DT(((("scratch",16),
                [("bool",
                 [14,25,26,30,35,46,50,52,53,55,62,131,132,137,180]),
                 ("ind_type",[33,34]),("pair",[8,9]),
                 ("scratch",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%73%57%21%60%16%119%77%101@%106$0@$1@3|@|@2%73%59%22%59%15%119%77%101@%100$0@$1@3|@|@2%73%59%22%59%15%119%77%101@%105$0@$1@3|@|@2%73%59%12%119%77%101@%104$0@3|@2%73%59%25%57%21%59%18%60%16%119%77%106$0@$2@2%100$1@$3@3|@|@|@|@2%73%59%25%57%21%59%18%60%16%119%77%106$0@$2@2%105$1@$3@3|@|@|@|@2%73%57%21%60%16%59%12%119%77%106$1@$2@2%104$0@3|@|@|@2%73%59%25%59%22%59%18%59%15%119%77%100$0@$2@2%105$1@$3@3|@|@|@|@2%73%59%22%59%15%59%12%119%77%100$1@$2@2%104$0@3|@|@|@2%59%22%59%15%59%12%119%77%105$1@$2@2%104$0@3|@|@|@10"])
  fun op MReg_case_cong x = x
    val op MReg_case_cong =
    ThmBind.DT(((("scratch",17),
                [("bool",[14,25,26,52,131,132,137,180]),
                 ("scratch",[1,2,3,4,5,6,7,8,9,10,11,12])]),["DISK_THM"]),
               [ThmBind.read"%59%2%59%3%58%49%68%29%66%32%66%35%63%38%82%73%77$6@$5@2%73%82%77$5@%101@2%76$4@%50@3%73%60%16%57%21%82%77$7@%106$1@$0@3%76$5$1@$0@2%30$1@$0@3|@|@2%73%59%15%59%22%82%77$7@%100$1@$0@3%76$4$1@$0@2%34$1@$0@3|@|@2%73%59%15%59%22%82%77$7@%105$1@$0@3%76$3$1@$0@2%37$1@$0@3|@|@2%59%12%82%77$6@%104$0@3%76$1$0@2%40$0@3|@7%76%102$6@$4@$3@$2@$1@$0@2%102$5@%50@%30@%34@%37@%40@3|@|@|@|@|@|@|@"])
  fun op MReg_nchotomy x = x
    val op MReg_nchotomy =
    ThmBind.DT(((("scratch",18),
                [("bool",[14,25,26,52,131,132,137,180]),
                 ("scratch",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%59%6%114%77$0@%101@2%114%85%26%83%11%77$2@%106$1@$0@2|@|@2%114%84%2%84%4%77$2@%100$1@$0@2|@|@2%114%84%2%84%4%77$2@%105$1@$0@2|@|@2%84%2%77$1@%104$0@2|@5|@"])
  fun op MReg_Axiom x = x
    val op MReg_Axiom =
    ThmBind.DT(((("scratch",19),
                [("bool",[14,25,26,30,52,62,131,132,137,180]),
                 ("ind_type",[33,34]),("pair",[8,9]),
                 ("scratch",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%58%31%68%33%67%36%67%39%65%41%86%42%73%76$0%101@2$5@2%73%60%16%57%21%76$2%106$1@$0@3$6$1@$0@2|@|@2%73%59%15%59%22%76$2%100$1@$0@3$5$1@$0@$2$1@2$2$0@3|@|@2%73%59%15%59%22%76$2%105$1@$0@3$4$1@$0@$2$1@2$2$0@3|@|@2%59%12%76$1%104$0@3$2$0@$1$0@3|@5|@|@|@|@|@|@"])
  fun op MReg_induction x = x
    val op MReg_induction =
    ThmBind.DT(((("scratch",20),
                [("bool",[14,25,26,52,131,132,137]),
                 ("scratch",[1,2,3,4,5,6,7,8,9,10,11])]),["DISK_THM"]),
               [ThmBind.read"%64%9%82%73$0%101@2%73%60%26%57%11$2%106$1@$0@2|@|@2%73%59%2%59%4%82%73$2$1@2$2$0@3$2%100$1@$0@3|@|@2%73%59%2%59%4%82%73$2$1@2$2$0@3$2%105$1@$0@3|@|@2%59%2%82$1$0@2$1%104$0@3|@6%59%2$1$0@|@2|@"])
  fun op MARK_REG_ind x = x
    val op MARK_REG_ind =
    ThmBind.DT(((("scratch",22),
                [("bool",[25,27,52,53,62]),("relation",[107,113]),
                 ("sat",[1,3,5,6,7,11,15])]),["DISK_THM"]),
               [ThmBind.read"%62%8%82%58%1$1$0@|@2%58%49$1$0@|@2|@"])
  fun op MARK_REG_def x = x
    val op MARK_REG_def =
    ThmBind.DT(((("scratch",23),
                [("bool",[15]),("combin",[19]),("relation",[113,132]),
                 ("scratch",[21])]),["DISK_THM"]),
               [ThmBind.read"%77%99%1@2%101@"])

  val _ = DB.bindl "scratch"
  [("MReg_TY_DEF",MReg_TY_DEF,DB.Def),
   ("MReg_case_def",MReg_case_def,DB.Def),
   ("MReg_size_def",MReg_size_def,DB.Def),
   ("MARK_REG_primitive_def",MARK_REG_primitive_def,DB.Def),
   ("empty_def",empty_def,DB.Def), ("final_def",final_def,DB.Def),
   ("shift_def",shift_def,DB.Def), ("datatype_MReg",datatype_MReg,DB.Thm),
   ("MReg_11",MReg_11,DB.Thm), ("MReg_distinct",MReg_distinct,DB.Thm),
   ("MReg_case_cong",MReg_case_cong,DB.Thm),
   ("MReg_nchotomy",MReg_nchotomy,DB.Thm),
   ("MReg_Axiom",MReg_Axiom,DB.Thm),
   ("MReg_induction",MReg_induction,DB.Thm),
   ("MARK_REG_ind",MARK_REG_ind,DB.Thm),
   ("MARK_REG_def",MARK_REG_def,DB.Thm)]

  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "scratch",
    thydataty = "compute",
    read = ThmBind.read,
    data =
        "scratch.MARK_REG_def scratch.shift_def scratch.empty_def scratch.final_def"
  }
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "scratch",
    thydataty = "TypeGrammarDeltas",
    read = ThmBind.read,
    data = "NTY7.scratch,4.MReg"
  }
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "scratch",
    thydataty = "TermGrammarDeltas",
    read = ThmBind.read,
    data =
        "OO4.MEps4.%101OO4.MSym4.%106OO4.MAlt4.%100OO4.MSeq4.%105OO4.MRep4.%104OO9.MReg_CASE4.%102OO9.MReg_size4.%103OO4.case4.%102OO8.MARK_REG3.%99OO5.empty4.%116OO5.final4.%117OO5.shift4.%118"
  }
  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG MReg_Axiom,
           case_def=MReg_case_def,
           case_cong=MReg_case_cong,
           induction=ORIG MReg_induction,
           nchotomy=MReg_nchotomy,
           size=SOME(Parse.Term`(scratch$MReg_size) :('a -> num$num) -> 'a scratch$MReg -> num$num`,
                     ORIG MReg_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME MReg_11,
           distinct=SOME MReg_distinct,
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
val _ = Theory.load_complete "scratch"
end
