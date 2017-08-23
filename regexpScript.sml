open HolKernel Parse boolLib bossLib
open pred_setSyntax pred_setLib listTheory rich_listTheory listTheory pred_setTheory arithmeticTheory
open EmitML basis_emitTheory

val _ = new_theory "regexp"

(* =========================== *)
(*    DEFINITION OF REGEX    *)
(* =========================== *)

val Regex = Datatype `Reg = Eps
                          | Sym 'a
                          | Alt Reg Reg
                          | Seq Reg Reg
                          | Rep Reg`;

(* =========================== *)
(*    REGEX Semantics          *)
(* =========================== *)

val LANGUAGE_OF_def = Define
  `(language_of Eps = {[]}) /\
   (language_of (Sym c) = {[c]}) /\
   (language_of (Alt a b) = (language_of a) UNION (language_of b) ) /\
   (language_of (Seq f s) =
     {fstPrt ++ sndPrt | (fstPrt IN language_of f) /\
                         (sndPrt IN language_of s) } ) /\
   (language_of (Rep r) =
     {x| ?words. (EVERY (\e. e IN language_of r) words) /\
                 ((FLAT words)=x)})`;

EVAL ``[1;3] IN (language_of (Seq (Alt (Sym 1) (Sym 2)) (Sym 3)))``;
EVAL ``language_of (Rep (Alt (Sym 1) (Sym 2)))``;


val SanityRep = prove(
  ``[1;2;1;1] IN language_of (Rep (Alt (Sym 1) (Sym 2)))``,
  Ho_Rewrite.REWRITE_TAC [LANGUAGE_OF_def,IN_GSPEC_IFF]>>
  Q.EXISTS_TAC `[[1];[2];[1];[1]]` >>
  SIMP_TAC list_ss []
);

val SanitySeq1 = prove(
  ``[1;2] IN language_of (Seq (Sym 1)(Sym 2))``,
  Ho_Rewrite.REWRITE_TAC [LANGUAGE_OF_def,IN_GSPEC_IFF]>>
  REWRITE_TAC [
    SET_SPEC_CONV
      ``[1; 2] IN {fstPrt ++ sndPrt | fstPrt IN {[1]} /\ sndPrt IN {[2]}}``
  ]>>
  SIMP_TAC list_ss []
);

(* TT: Not needed below 
val AND_FOLD_FALSE_thm = prove(
  ``!a. ~(FOLDL $/\ F a)``,
  Induct >> ASM_SIMP_TAC std_ss [FOLDL]
);
*)

val SanityRepNullable = prove(
  ``([] IN language_of (Rep (Alt (Sym 1) (Sym 2))))``,
  Ho_Rewrite.REWRITE_TAC [LANGUAGE_OF_def,IN_GSPEC_IFF, NOT_EXISTS_THM]>>
  Q.EXISTS_TAC `[]`>>
  SIMP_TAC list_ss []
);

val SanityRepNullable = prove(
  ``!R. ([] IN language_of (Rep R))``,
  Induct>>
  Ho_Rewrite.REWRITE_TAC [LANGUAGE_OF_def,IN_GSPEC_IFF]>>
  TRY STRIP_TAC>>
  Q.EXISTS_TAC `[]`>>
  SIMP_TAC (list_ss) []
);

(* =========================== *)
(* Executable model of regex *)
(* =========================== *)

val SPLIT_def = Define
  `(split []    = [([],[])]) /\
   (split (c::cs) = ([],c::cs)::(MAP (\x. (c::(FST x), SND x)) (split cs)))`;

val MEM_SPLIT_APPEND_THM = store_thm(
  "SPLIT_APPEND_THM",
  ``!A B. MEM (A,B) (split (A++B))``,

Induct >| [
  Cases >> SIMP_TAC list_ss [SPLIT_def],
  ASM_SIMP_TAC (list_ss++QI_ss) [SPLIT_def, MEM_MAP]
]);



val SPLIT_APPEND_THM =  store_thm(
  "SPLIT_APPEND_THM",
  ``!l l1 l2. (MEM (l1, l2) (split l)) <=> (l1 ++ l2 = l)``,
  SIMP_TAC std_ss [boolTheory.EQ_IMP_THM, FORALL_AND_THM] >>
  (Tactical.REVERSE CONJ_TAC) >-(
    Induct >- (
      Cases >> SIMP_TAC list_ss [SPLIT_def]
    )>>
    ASM_SIMP_TAC (list_ss++QI_ss) [SPLIT_def, MEM_MAP]
  )>>
  Induct>-(
     ASM_SIMP_TAC (list_ss) [SPLIT_def]
  )>>

  ASM_SIMP_TAC (list_ss) [SPLIT_def, MEM_MAP]>>
  REPEAT STRIP_TAC>>
  FULL_SIMP_TAC list_ss []
);

EVAL ``split []``;
EVAL ``split [x]``;
EVAL ``split [x;y;z]``;


(* It was pritty hard to work with this definition,
   maybe i should redefine this  *)
(* TT: HD, TL etc. are in my opinion usually best to avoid.
       This however really depends on the situation and needs
       judgement. Here I would just use the pattern compilation. *)
val PARTS_def = Define
  `(parts []     = [[]]) /\
   (parts (c::cs) =
     if cs = []
     then [[[c]]]
     else FLAT (MAP (\x. [[c]::x; (c::(HD x))::(TL x)]) (parts cs)))
   `;


val PARTS_SPEC = store_thm ("PARTS_SPEC",
  ``!(l:'a list) ll. MEM ll (parts l) <=> (~(MEM [] ll) /\ (FLAT ll = l))``,
Induct >- (
  SIMP_TAC list_ss [PARTS_def, FLAT_EQ_NIL, EVERY_MEM] >>
  Cases_on `ll` >| [
    SIMP_TAC list_ss [],

    SIMP_TAC list_ss [] >> METIS_TAC[]
  ]
) >>
CONV_TAC (RENAME_VARS_CONV ["c"]) >>
REPEAT GEN_TAC >>
ASM_SIMP_TAC (list_ss++boolSimps.LIFT_COND_ss) [PARTS_def,
  MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
Cases_on `ll` >> SIMP_TAC list_ss [] >>
rename1 `cl ++ FLAT ll' = [c:'a]` >>
Cases_on `cl` >> SIMP_TAC list_ss [] >>
SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [] >>
rename1 `(cl' = ([]:'a list)) /\ (c' = (c:'a))` >>
Cases_on `l` >> SIMP_TAC list_ss [] >> REPEAT STRIP_TAC >> (
  REPEAT BasicProvers.VAR_EQ_TAC >> FULL_SIMP_TAC list_ss [PARTS_def]
) >>
rename1 `FLAT _ = (c2:'a)::cs` >>
EQ_TAC >> STRIP_TAC >> REPEAT BasicProvers.VAR_EQ_TAC >| [
  ASM_SIMP_TAC list_ss [],

  rename1 `FLAT ll' = (_:'a)::_` >>
  Cases_on `ll'` >> FULL_SIMP_TAC list_ss [],

  Q.EXISTS_TAC `if ((cl':'a list) = []) then ll' else cl'::ll'` >>
  Cases_on `cl' = []` >> FULL_SIMP_TAC list_ss []
]);


EVAL ``parts [x;y;z]``;
EVAL ``parts [1;2]``;
EVAL ``parts [1]``;
EVAL ``parts []``;
EVAL ``parts [x;y;z;w]``;


val PARTS_EMPTY_THM = store_thm(
  "PARTS_EMPTY_THM",
  ``!e. (e =[]) = (MEM (e) (parts ([])))``,
    ASM_SIMP_TAC list_ss [PARTS_def]
);

val PARTS_EMPTY_THM2 = store_thm(
  "PARTS_EMPTY_THM2",
  ``!e. (MEM [] (parts e )) ==> (e=[])``,
     SIMP_TAC list_ss [PARTS_SPEC]
);

val PARTS_NON_EMPTY_THM = store_thm(
  "PARTS_NON_EMPTY_THM",
  ``!e x . x<>[] ==>
           (MEM x (parts e )) ==>
           (e<>[])``,
     ASM_SIMP_TAC list_ss [PARTS_EMPTY_THM]
);


val PARTS_SINGEL_THM = store_thm(
  "PARTS_SINGEL_THM",
  ``!e x. (e =[[x]]) = (MEM (e) (parts [x]))``,

    ASM_SIMP_TAC list_ss [PARTS_def]
);

val PARTS_MEM_HEAD_THM = store_thm(
  "PARTS_MEM_HEAD_THM",
  ``!h t e. (MEM e (parts t)) =
            (MEM ([h]::e) (parts (h::t)))``,
  SIMP_TAC list_ss [PARTS_SPEC]
);

val PARTS_MEM_APPEND_THM1 = store_thm(
  "PARTS_MEM_APPEND_THM1",

  ``!l1 l2 l1' l2'. (MEM l1' (parts l1))  ==>
            (MEM l2' (parts l2))  ==>
            (MEM (l1' ++ l2') (parts (l1 ++ l2)))``,

  SIMP_TAC list_ss [PARTS_SPEC]
);

val ACCEPT_def = Define
  `(accept Eps       u = (u=[]))/\
   (accept (Sym c)   u = (u=[c]))/\
   (accept (Alt p q) u = (accept p u \/ accept q u))/\
   (accept (Seq p q) u =
     (EXISTS
       (\x. accept p (FST x) /\ accept q (SND x))
       (split u)
     )
   )/\
   (accept (Rep r)   u =
        EXISTS (\partition. EVERY (\part. accept r part) partition) (parts u)
   )`;

EVAL ``accept (Sym e) [e]``;
EVAL ``accept (Sym e) []``;
EVAL ``accept (Rep (Alt (Sym 1) (Sym 2))) [6;1;2;1;1]``;
EVAL ``accept (Rep (Alt (Sym 1) (Sym 2))) [1;2;1;1]``;
EVAL ``accept (Rep (Alt (Sym 1) (Eps))) []``;
EVAL ``accept (Rep (Sym 1)) []``;
EVAL ``accept (Seq (Sym 1)(Sym 2)) [1;2]``;




(* ============================================================ *)
(*  Equaivalance of semantics and executable model         *)
(* ============================================================= *)

val FLAT_EQ_FLAT_WITHOUT_EMPTY_thm = prove(
``!words. (FLAT words) =(FLAT (FILTER (\y. []<>y) words))``,
Induct_on `words`>>
(
  ASM_SIMP_TAC (list_ss++boolSimps.LIFT_COND_ss) []
));

(*

unesesary lemman in this current version of the proof
But it could be usefull for something else

val FLAT_SINGLETON_thm = prove(
``!l x. (FLAT l = [x]) ==> MEM [x] l ``,
  Induct>>
  ASM_SIMP_TAC list_ss [FLAT]>>
  REPEAT STRIP_TAC>>
  Cases_on `h=[x]`>|
  [
    DISJ1_TAC>>
    METIS_TAC []
  ,
    DISJ2_TAC>>
    Cases_on `h`>>
    REV_FULL_SIMP_TAC list_ss []
  ]
);

*)

val LANGUAGE_ACCEPTED_THM = store_thm(
  "LANGUAGE_ACCEPTED_THM",
  ``!R x. x IN language_of R = accept R x``,
  (* TT: Better make structure very clear *)
  Induct_on `R` >> (
    (* Solve simple cases *)
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss) [ EXISTS_MEM,
                                                         LANGUAGE_OF_def,
                                                         ACCEPT_def]>>
    REWRITE_TAC [boolTheory.EQ_IMP_THM] >>
    REPEAT STRIP_TAC
  ) >|
  [ 
    (* Seq lang to accept  *)
    Q.EXISTS_TAC `(fstPrt,sndPrt)`>>
    ASM_SIMP_TAC list_ss [SPLIT_APPEND_THM]
  ,
    (* Seq accept to lang  *)

    (* TT: The following looks rather complicated. Perhaps use just a case split and renaming 
    Q.EXISTS_TAC `FST x'`>>
    Q.EXISTS_TAC `SND x'`>>
    `?l1 l2. x'=(l1,l2)`
      Q.EXISTS_TAC `FST x'`>>
      Q.EXISTS_TAC `SND x'`>>
      SIMP_TAC list_ss [])>>
    *)
    Cases_on `x'` >> rename1 `FST (l1, l2)` >>
    Q.EXISTS_TAC `l1` >> Q.EXISTS_TAC `l2` >>
    FULL_SIMP_TAC list_ss [SPLIT_APPEND_THM]
  ,
    (* Rep lang to accept *)
    Q.EXISTS_TAC `FILTER ($<>[]) words`>>
    FULL_SIMP_TAC list_ss [ MEM_FILTER,
                            EVERY_MEM,
                            PARTS_SPEC,
                            GSYM FLAT_EQ_FLAT_WITHOUT_EMPTY_thm ]
  , 
    (* Rep accept to lang *)
    Q.EXISTS_TAC `partition'`>>
    FULL_SIMP_TAC list_ss [ MEM_FILTER,
                            EVERY_MEM,
                            PARTS_SPEC,
                            GSYM FLAT_EQ_FLAT_WITHOUT_EMPTY_thm ]
  ]
);


 (* ======================================= *)
(*            Marked Regex               *)
 (* ======================================= *)

val MReg = Datatype `MReg = MEps
                          | MSym bool 'a
                          | MAlt MReg MReg
                          | MSeq MReg MReg
                          | MRep MReg`;

val  MARK_REG_DEF = Define 
  `(MARK_REG Eps = MEps) /\
   (MARK_REG (Sym x) = MSym F x)/\
   (MARK_REG (Alt p q) = MAlt (MARK_REG p) (MARK_REG q) )/\
   (MARK_REG (Seq p q) = MSeq (MARK_REG p) (MARK_REG q) )/\
   (MARK_REG (Rep r) = MRep (MARK_REG r) )`;

val EMPTY_M_DEF = Define 
  `
   (empty MEps = T) /\
   (empty (MSym _ _) = F) /\
   (empty (MAlt p q) = empty p \/ empty q) /\
   (empty (MSeq p q) = empty p /\ empty q) /\
   (empty (MRep _  ) = T )
  `;


EVAL ``empty MEps``;
EVAL ``empty (MAlt MEps (MSym T 2))``;
EVAL ``empty (MSeq MEps (MSym T 2))``;
EVAL ``empty (MAlt (MSym T 2) MEps)``;
EVAL ``empty (MAlt (MRep(MSym T 2)) MEps)``;
EVAL ``empty (MAlt (MRep(MSym T 2)) (MRep(MSym T 2)))``;

val FINAL_M_DEF = Define 
  `(final MEps = F) /\
   (final (MSym b _) = b) /\
   (final (MAlt p q) = final p\/final q) /\
   (final (MSeq p q) = final p/\empty q \/ final q ) /\
   (final (MRep  r ) = final r )`;

EVAL ``final MEps``;
EVAL ``final (MAlt MEps (MSym T 2))``;
EVAL ``final (MSeq MEps (MSym T 2))``;
EVAL ``final (MSeq (MSym T 2) MEps)``;
EVAL ``final (MSeq (MSym T 2) MEps)``;
EVAL ``final (MSeq (MSym T 2) (MSym F 2))``;
EVAL ``final (MAlt (MRep(MSym T 2)) MEps)``;
EVAL ``final (MSeq (MRep(MSym T 2)) (MRep(MSym F 2)))``;



val SHIFT_M_DEF = Define
  `(shift _ MEps _ =  MEps )/\
   (shift m (MSym _ x) c = MSym (m /\ (x=c) ) x )/\
   (shift m (MAlt p q) c = MAlt (shift m p c) (shift m q c))/\
   (shift m (MSeq p q) c =
     MSeq (shift m p c)
	  (shift (m /\ empty p \/ final p) q c))/\
   (shift m (MRep r)    c =
     MRep (shift (m \/ final r) r c) )`;



val ACCEPT_M_DEF = Define 
  `( acceptM r []      = empty r ) /\
   ( acceptM r (c::cs) = final (FOLDL (shift F) (shift T r c) cs))`;


(*
val FOLDL_SHIFT_MREP = store_thm (
"FOLDL_SHIFT_MREP",
``!r h1 t1 h2 t2.
  ( final(FOLDL (shift F) (shift T r h1) t1) ) /\ ( final(FOLDL (shift F) (shift T r h2) t2) ) =
  ( final(FOLDL (shift F) (shift T (MRep r) h1) (t1++h2::t2)) )
``,

Ho_Rewrite.REWRITE_TAC [boolTheory.EQ_IMP_THM, FORALL_AND_THM] >>
STRIP_TAC>|
Induct_on `t1`
REPEAT STRIP_TAC

ASM_SIMP_TAC list_ss [MARK_REG_DEF, ACCEPT_M_DEF, EMPTY_M_DEF, LANGUAGE_OF_def, SHIFT_M_DEF, FINAL_M_DEF]


);
*)

val MARKED_M_DEF = Define
  `(marked MEps = F ) /\
   (marked (MSym v x) = v) /\
   (marked (MAlt p q) = (marked p) \/ (marked q )) /\
   (marked (MSeq p q) = (marked p) \/ (marked q )) /\
   (marked (MRep r)   = marked r )`;

val MSYM_STAYS_UNMARKED_THM = store_thm(
  "MSYM_STAYS_UNMaRKED_THM",
  ``!l a. FOLDL (shift F) (MSym F a) l = MSym F a``,
  Induct>>
    ASM_SIMP_TAC list_ss [SHIFT_M_DEF] 
);

val MSYM_BECOMES_UNMARKED_THM = store_thm(
  "MSYM_BECOMES_UNMaRKED_THM",
  ``!t h b. FOLDL (shift F) (MSym b a) (h::t) = MSym F a``,
  Induct>>
    ASM_SIMP_TAC list_ss [SHIFT_M_DEF, MSYM_STAYS_UNMARKED_THM] 
);

val UNMARKED_NOT_FINAL_THM = store_thm(
  "UNMARKED_NOT_FINAL_THM",
  ``!R. ~marked R ==> (final R ==> F)``,
  Induct>>
    ASM_SIMP_TAC list_ss [MARKED_M_DEF,MSYM_STAYS_UNMARKED_THM, FINAL_M_DEF]
);

val STAYS_UNMARKED_THM = store_thm(
  "MSYM_STAYS_UNMaRKED_THM",
  ``!R l. (~marked R) ==> ((FOLDL (shift F) (R) l) = R)``,
  Induct>>
    Induct>>
      REPEAT STRIP_TAC>>  
      REPEAT ( 
        Q.PAT_X_ASSUM `!l. _` (fn x => MP_TAC ( Q.SPEC `[h]` x))
      )>> 
      MP_TAC (Q.SPEC `R` UNMARKED_NOT_FINAL_THM)>>
      FULL_SIMP_TAC list_ss [MARKED_M_DEF, SHIFT_M_DEF, FOLDL, MSYM_STAYS_UNMARKED_THM]
);

val ex_regex_def = Define 
`exmpl_reg = 
   MSeq 
     (MRep (MSeq 
         (MSeq
           (MRep (MAlt 
             (MSym F 1) 
             (MSym F 2)
           ))
           (MSym F 3)
         ) 
         (MSeq
           (MRep (MAlt 
             (MSym F 1) 
             (MSym F 2)
           ))
           (MSym F 3)
         ) 
     )) 
     ((MRep (MAlt 
        (MSym F 1) 
        (MSym F 2)
      )))`;

EVAL ``shift T exmpl_reg 3``;
EVAL ``shift T exmpl_reg 1``;
EVAL ``shift T exmpl_reg 1``;




EVAL ``acceptM ((MRep (MAlt 
        (MSym F 1) 
        (MSym F 2)
      ))) []``;

EVAL ``acceptM exmpl_reg [1;3;2;1;2;3;1]``;

EVAL ``acceptM ((MRep (MAlt 
        (MSym F 1) 
        (MSym F 2)
      ))) [1;2;1;1;1;1;1]``;

EVAL ``acceptM ((MRep (MSeq 
        (MSym F 1) 
        (MSym F 2)
      ))) [1;2;1;2]``;


val EPS_REPITED_SHIFT = store_thm (
"EPS_REPITED_SHIFT",
``!t. FOLDL(shift F) MEps t = MEps``,
  Induct_on `t`>>
  ASM_SIMP_TAC list_ss [MARK_REG_DEF, ACCEPT_M_DEF, EMPTY_M_DEF, LANGUAGE_OF_def, SHIFT_M_DEF, FINAL_M_DEF]);

val EPS_ACCEPTS_EMPTY = prove(
``!e. acceptM MEps e = (e=[]) ``,
  STRIP_TAC>>
  Cases_on `e` >>
  ASM_SIMP_TAC list_ss [MARK_REG_DEF, ACCEPT_M_DEF, EMPTY_M_DEF, LANGUAGE_OF_def, SHIFT_M_DEF, FINAL_M_DEF, EPS_REPITED_SHIFT]
);

val REP_NULLABLE = prove(
``!r. acceptM (MRep r) []``,
  ASM_SIMP_TAC list_ss [MARK_REG_DEF, ACCEPT_M_DEF, EMPTY_M_DEF, FINAL_M_DEF]
);

val ACCEPT_REP_REPLICATE1 = prove(
`` !n v . acceptM (MRep (MSym F v)) (REPLICATE n v) ``,
REPEAT STRIP_TAC>>
Cases_on `n`>>
    FULL_SIMP_TAC list_ss [REPLICATE, ACCEPT_M_DEF, EMPTY_M_DEF, FINAL_M_DEF, SHIFT_M_DEF]>>
Induct_on `n'`>>
    FULL_SIMP_TAC list_ss [REPLICATE, ACCEPT_M_DEF, EMPTY_M_DEF, FINAL_M_DEF, SHIFT_M_DEF]
);


(*val ACCEPT_REP_APPEND_THM = store_thm(
  "ACCEPT_REP_APPEND_THM",
  `` !w1 w2 R . (acceptM R w1 /\ acceptM R w2) = (acceptM (MRep R) (w1++w2)) ``,
  Induct_on `w1++w2` 
);*)

val ACCEPT_SEQ_APPEND_THM = store_thm(
  "ACCEPT_SEQ_APPEND_THM",
  `` !h t R1 R2. (final (FOLDL (shift F) (shift T (MSeq R1 R2) h) (t))) ==>
                    (?t1 h2 t2. (t = t1++h2::t2) /\ 
                    (final( FOLDL (shift F) (shift T R1 h) t1)) /\   
                    (final( FOLDL (shift F) (shift T R2 h2) t2)) \/
                    (empty(R1) ) /\   
                    (final( FOLDL (shift F) (shift T R2 h) t)))
  ``,
  cheat

(*
Ho_Rewrite.REWRITE_TAC [boolTheory.EQ_IMP_THM, FORALL_AND_THM] >>
REPEAT STRIP_TAC

  Induct_on `t` >>
   REV_FULL_SIMP_TAC list_ss [FINAL_FOLDL_SHIFT_ALT_THM , FINAL_M_DEF, MARK_REG_DEF, EPS_ACCEPTS_EMPTY, LANGUAGE_OF_def, ACCEPT_M_DEF, EMPTY_M_DEF, SHIFT_M_DEF, MSYM_STAYS_UNMARKED_THM]>>
   
   REPEAT STRIP_TAC *)
);

val ACCEPT_REP_APPEND_THM = store_thm(
  "ACCEPT_REP_APPEND_THM",
  `` !h t R.  (final (FOLDL (shift F) (shift T (MRep R) h) (t))) =
                    ?t1 h2 t2. (t = t1++h2::t2) /\ 
                   (final( FOLDL (shift F) (shift T R h) t1)) /\   
                    (final( FOLDL (shift F) (shift T R h2) t2)) ``,
  cheat
);

val ACCEPT_REP_APPEND2_THM = store_thm(
  "ACCEPT_REP_APPEND2_THM",
  `` !h t R. (final (FOLDL (shift F) (shift T (MRep R) h) (t))) =
                    ?t1 h2 t2. (t = t1++h2::t2) /\ 
                    (final( FOLDL (shift F) (shift T R h) t1)) /\   
                    (final( FOLDL (shift F) (shift T (MRep R) h2) t2)) ``,

  cheat
);

(* probably need a lema like this aswell *)
val ACCEPT_REP_FLAT_THM = store_thm(
  "ACCEPT_REP_FLAT_THM",
  `` !h t R. (final (FOLDL (shift F) (shift T (MRep R) h) (FLAT t))) =
             (final (FOLDL (shift F) (shift T R h) (FLAT (HD t)))) /\
             (EVERY (\x. (final (FOLDL (shift F) (shift T R (HD x)) (TL x))))  TL t)``,
  cheat
);

(*
val ACCEPT_REP_FLAT_THM = prove(
`` !l R. (EVERY (acceptM R) l) = (acceptM (MRep R) (FLAT l)) ``,

Ho_Rewrite.REWRITE_TAC [boolTheory.EQ_IMP_THM, FORALL_AND_THM] >>
STRIP_TAC>|
[
  Induct>>
  
   REPEAT STRIP_TAC>>
   REV_FULL_SIMP_TAC list_ss [FINAL_FOLDL_SHIFT_ALT_THM , FINAL_M_DEF, MARK_REG_DEF, EPS_ACCEPTS_EMPTY, LANGUAGE_OF_def, ACCEPT_M_DEF, EMPTY_M_DEF, SHIFT_M_DEF, MSYM_STAYS_UNMARKED_THM]>>
   `acceptM (MRep R) (FLAT l)` by METIS_TAC []>>
   Q.PAT_X_ASSUM `!R._` (fn x=> ALL_TAC)>>
   Induct_on `h`
,


]

REPEAT STRIP_TAC>>
Cases_on `n`>>
    FULL_SIMP_TAC list_ss [REPLICATE, ACCEPT_M_DEF, EMPTY_M_DEF, FINAL_M_DEF, SHIFT_M_DEF]>>
Induct_on `n'`>>
    FULL_SIMP_TAC list_ss [REPLICATE, ACCEPT_M_DEF, EMPTY_M_DEF, FINAL_M_DEF, SHIFT_M_DEF]
);
 *)

val EMPTY_STRING_IN_NULLABLE_REG = store_thm (
  "EMPTY_STRING_IN_NULLABLE_REG",
  ``!r. [] IN language_of r = empty (MARK_REG r)``,
  Induct>>
    ASM_SIMP_TAC (list_ss ++pred_setSimps.PRED_SET_ss) [MARK_REG_DEF, LANGUAGE_OF_def, EMPTY_M_DEF]>>
  Q.EXISTS_TAC `[]`>>
  ASM_SIMP_TAC (list_ss) []
);

val FOLDL_SHIFT_ALT_THM = store_thm (
"FOLDL_SHIFT_ALT_THM",
``!l R R'. FOLDL (shift F) (MAlt R R') l = MAlt (FOLDL (shift F) R l) (FOLDL (shift F) R' l)``,
Induct>>
   ASM_SIMP_TAC list_ss [ SHIFT_M_DEF, FINAL_M_DEF, MARK_REG_DEF, EPS_ACCEPTS_EMPTY, LANGUAGE_OF_def, ACCEPT_M_DEF, EMPTY_M_DEF, SHIFT_M_DEF, MSYM_STAYS_UNMARKED_THM]
);

val FINAL_FOLDL_SHIFT_ALT_THM = store_thm (
"FINAL_FOLDL_SHIFT_ALT_THM",
``!l R R'. final (FOLDL (shift F) (MAlt R R') l) = final (FOLDL (shift F) R l) \/ final (FOLDL (shift F) R' l)``,
   ASM_SIMP_TAC list_ss [FINAL_M_DEF, FOLDL_SHIFT_ALT_THM]
);

(* val FOLDL_SHIFT_SEQ_THM = store_thm (
"FOLDL_SHIFT_SEQ_THM",
``! (FOLDL (shift F) (MSeq R R') l) ==>
               ? l1 l2. (l=l1++l2) /\	    
               MSeq (FOLDL (shift F) R l) ( FOLDL2 () (R,R') l)``
DB.find "FOLDL"
Induct_on `l1++l2`>>
   ASM_SIMP_TAC list_ss [ SHIFT_M_DEF, FINAL_M_DEF, MARK_REG_DEF, EPS_ACCEPTS_EMPTY, LANGUAGE_OF_def, ACCEPT_M_DEF, EMPTY_M_DEF, SHIFT_M_DEF, MSYM_STAYS_UNMARKED_THM]>-
   
SIMP_TAC list_ss [SHIFT_M_DEF]
REWRITE_TAC [FOLDL, SHIFT_M_DEF]
);

val FINAL_FOLDL_SHIFT_SEQ_THM = store_thm (
"FINAR_FOLDL_SHIFT_SEQ_THM",
``!h t h1 t1 h2 t2 R R'. final ( FOLDL (shift F) (shift T (MSeq R R')h) (t)) ==>
               ? l1 l2. h::t = h1::t1++h2::t2 /\	    
               final ( FOLDL (shift F) R l) /\ (empty R') \/
               final ( FOLDL (shift F) R' l2) ``
Induct_on `l1++l2`>>
   ASM_SIMP_TAC list_ss [ SHIFT_M_DEF, FINAL_M_DEF, MARK_REG_DEF, EPS_ACCEPTS_EMPTY, LANGUAGE_OF_def, ACCEPT_M_DEF, EMPTY_M_DEF, SHIFT_M_DEF, MSYM_STAYS_UNMARKED_THM]>-
   
SIMP_TAC list_ss [SHIFT_M_DEF]
REWRITE_TAC [FOLDL, SHIFT_M_DEF]
);

``!l R R'. acceptM  (MSeq R R') l ==>
               ? l1 l2. (l = l1++l2) /\		    
               (acceptM R l1) /\
               (acceptM R' l2) ``

Induct>>
Cases_on `l`>>
   ASM_SIMP_TAC list_ss [ SHIFT_M_DEF, FINAL_M_DEF, MARK_REG_DEF, EPS_ACCEPTS_EMPTY, LANGUAGE_OF_def, ACCEPT_M_DEF, EMPTY_M_DEF, SHIFT_M_DEF, MSYM_STAYS_UNMARKED_THM]>-
   
   
   FULL_SIMP_TAC list_ss [ SHIFT_M_DEF, FINAL_M_DEF, MARK_REG_DEF, EPS_ACCEPTS_EMPTY, LANGUAGE_OF_def, ACCEPT_M_DEF, EMPTY_M_DEF, SHIFT_M_DEF, MSYM_STAYS_UNMARKED_THM]>-
Induct_on `t`>>
REPEAT STRIP_TAC >|
[
  Q.EXISTS_TAC `[h]`>>
  Q.EXISTS_TAC `[]`>>
  Cases_on `final R`
,
]
EVAL ``T /\ (F \/ T)``
*)
val all_defs = [FINAL_M_DEF, MARK_REG_DEF, EPS_ACCEPTS_EMPTY, LANGUAGE_OF_def, ACCEPT_M_DEF, EMPTY_M_DEF, SHIFT_M_DEF];

val ACCEPT_M_LANGUAGE_THM = strore_thm (
"ACCEPT_M_LANGUAGE_THM ",
``!r w. acceptM (MARK_REG r) w <=> w IN (language_of r)``,

`!t h r.
  final (FOLDL (shift F) (shift T (MARK_REG r) h) t) ⇔
  h::t IN language_of r ` suffices_by (
   REPEAT STRIP_TAC >>
   Cases_on `w`>>
    ASM_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss)[FINAL_M_DEF, MARK_REG_DEF, EPS_ACCEPTS_EMPTY, LANGUAGE_OF_def, ACCEPT_M_DEF, EMPTY_M_DEF, SHIFT_M_DEF, EMPTY_STRING_IN_NULLABLE_REG])  >>


(*Ho_Rewrite.REWRITE_TAC [boolTheory.EQ_IMP_THM, FORALL_AND_THM] >>
STRIP_TAC>>
*)
Induct_on `r`>>
  REPEAT GEN_TAC>|
[

  ASM_SIMP_TAC list_ss [FINAL_M_DEF, MARK_REG_DEF, EPS_ACCEPTS_EMPTY, LANGUAGE_OF_def, ACCEPT_M_DEF, EMPTY_M_DEF, SHIFT_M_DEF]>>
  SIMP_TAC std_ss [EPS_REPITED_SHIFT,FINAL_M_DEF]
,
  ASM_SIMP_TAC list_ss all_defs >>
  Cases_on `a=h`>>
  ASM_SIMP_TAC list_ss all_defs >>
  Cases_on `t`>>
  ASM_SIMP_TAC list_ss [MSYM_STAYS_UNMARKED_THM,FINAL_M_DEF, MARK_REG_DEF, EPS_ACCEPTS_EMPTY, LANGUAGE_OF_def, ACCEPT_M_DEF, EMPTY_M_DEF, SHIFT_M_DEF]>>
   
  , 
   FULL_SIMP_TAC list_ss [FINAL_FOLDL_SHIFT_ALT_THM , FINAL_M_DEF, MARK_REG_DEF, EPS_ACCEPTS_EMPTY, LANGUAGE_OF_def, ACCEPT_M_DEF, EMPTY_M_DEF, SHIFT_M_DEF, MSYM_STAYS_UNMARKED_THM]
  ,
   cheat
   (* I do not understand why this rewrite is failing now *)
   
   (*FULL_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss) [ACCEPT_SEQ_APPEND_THM,MARK_REG_DEF, LANGUAGE_OF_def]

   Ho_Rewrite.REWRITE_TAC [boolTheory.EQ_IMP_THM, FORALL_AND_THM] >>
   REPEAT STRIP_TAC >|
   [
     Q.EXISTS_TAC `h::t1`>>
     Q.EXISTS_TAC `h2::t2`>>
     ASM_SIMP_TAC list_ss []
   ,
     cheat
   (*  Q.EXISTS_TAC `TL fstPrt`>>
     Q.EXISTS_TAC `HD sndPrt`>>
     Q.EXISTS_TAC `TL sndPrt`>>
   FULL_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss) [ACCEPT_SEQ_APPEND_THM , FINAL_M_DEF, MARK_REG_DEF, EPS_ACCEPTS_EMPTY, LANGUAGE_OF_def, ACCEPT_M_DEF, EMPTY_M_DEF, SHIFT_M_DEF, MSYM_STAYS_UNMARKED_THM]
     *)*)
    
   ,


   FULL_SIMP_TAC (list_ss ++ pred_setSimps.PRED_SET_ss) [ACCEPT_REP_FLAT_THM,MARK_REG_DEF, LANGUAGE_OF_def]
cheat
ACCEPT_REP_FLAT_THM

 (* ======================================= *)
(*            Code generation            *)
 (* ======================================= *)


emitML (!Globals.emitMLDir) ("poregex", [
                         MLSIG "Type 'a list = 'a listML.list",
                         OPEN ["list"],
                         DATATYPE `Reg = Eps
                                       | Sym 'a
                                       | Alt Reg Reg
                                       | Seq Reg Reg
                                       | Rep Reg`,
                         DEFN SPLIT_def,
                         DEFN PARTS_def,
                         DEFN ACCEPT_def
                           ]);
val _ = export_theory();
