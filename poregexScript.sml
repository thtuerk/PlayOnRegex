open HolKernel Parse boolLib bossLib
open pred_setSyntax pred_setLib listTheory rich_listTheory listTheory pred_setTheory
open EmitML basis_emitTheory
                    
val _ = new_theory "poregex"

(* =========================== *)
(*    DEFINITION OF REGEX    *)
(* =========================== *)

val Regex = Datatype `Reg = Eps
                          | Sym 'a
                          | Alt Reg Reg
                          | Seq Reg Reg
                          | Rep Reg`;

(* =========================== *)
(*    REGEX Semantix         *)
(* =========================== *)

val LANGUAGE_OF_def = Define 
  `(language_of Eps = {[]}) /\
   (language_of (Sym c) = {[c]}) /\
   (language_of (Alt a b) = (language_of a) UNION (language_of b) ) /\
   (language_of (Seq f s) = 
     {fstPrt ++ sndPrt | (fstPrt IN language_of f) /\ 
                         (sndPrt IN language_of s) } ) /\
   (language_of (Rep r) = 
     {x| ?words. (words <> []) /\ 
                 (EVERY (\e. e IN language_of r) words) /\
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
  `` [1;2] IN language_of (Seq (Sym 1)(Sym 2))``,
  Ho_Rewrite.REWRITE_TAC [LANGUAGE_OF_def,IN_GSPEC_IFF]>>
  REWRITE_TAC [ SET_SPEC_CONV 
    ``[1; 2] IN {fstPrt ++ sndPrt | fstPrt IN {[1]} /\ sndPrt IN {[2]}}`` 
  ]>>
  Q.EXISTS_TAC `[1]` >>
  Q.EXISTS_TAC `[2]` >>
  SIMP_TAC list_ss []
);

val AND_FOLD_FALSE_thm = prove(
  ``!a. ~(FOLDL $/\ F a)``,
  Induct >> ASM_SIMP_TAC std_ss [FOLDL]
);

val SanityRepNotNullable = prove(
  ``~([] IN language_of (Rep (Alt (Sym 1) (Sym 2))))``,

  Ho_Rewrite.REWRITE_TAC [LANGUAGE_OF_def,IN_GSPEC_IFF, NOT_EXISTS_THM]>>
  Induct >> ASM_SIMP_TAC list_ss [AND_FOLD_FALSE_thm]
);

val SanityRepNullable = prove(
  ``([] IN language_of (Rep (Alt (Eps) (Sym 2))))``,

  Ho_Rewrite.REWRITE_TAC [LANGUAGE_OF_def,IN_GSPEC_IFF]>>
  Q.EXISTS_TAC `[[]]` >>
  SIMP_TAC list_ss []
);

(* =========================== *)
(* Executable model of regex *)
(* =========================== *)

val SPLIT_def = Define 
  `(split []    = [([],[])]) /\
   (split (c::cs) = ([],c::cs)::(MAP (\x. (c::(FST x), SND x)) (split cs)))`;


val SPLIT_APPEND_THM = store_thm( 
  "SPLIT_APPEND_THM",
  ``!A B. ? C D. (split (A++B)) = ( C++[(A,B)] ++ D)``
,
 Induct >-
 (
   GEN_TAC >> Q.EXISTS_TAC `[]`>>
   Cases_on `B` >| 
   [
     Q.EXISTS_TAC `[]`
   ,
     Q.EXISTS_TAC `(MAP (\x. (h::(FST x), SND x)) (split t))`
   ]>>
   SIMP_TAC list_ss [ SPLIT_def]
 )>>
 REPEAT GEN_TAC>>
 SIMP_TAC list_ss [ SPLIT_def] >>
 Q.PAT_X_ASSUM `!B._` (fn x=> (MP_TAC (Q.SPEC `B` x)))>>
 STRIP_TAC>>
 Q.PAT_X_ASSUM `_` (fn x=> (REWRITE_TAC [x]))>>
 SIMP_TAC list_ss [MAP_APPEND]>>
 Q.EXISTS_TAC `([],h::(A ++ B))::(MAP (λx. (h::FST x,SND x)) C)`>>
 Q.EXISTS_TAC `(MAP (\x. (h::FST x,SND x)) D)`>>
 SIMP_TAC list_ss []
);
 
EVAL ``split []``;
EVAL ``split [x]``;
EVAL ``split [x;y;z]``;


(* It was pritty hard to work with this definition, 
   maybe i should redefine this  *)
val PARTS_def = Define
  `(parts []     = [[]]) /\
   (parts (c::cs) = 
     if cs = [] 
     then [[[c]]] 
     else FLAT (MAP (\x. [[c]::x; (c::(HD x))::(TL x)]) (parts cs)))
   `;


val PARTS_SPEC = store_thm ("parts_SPEC",
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


val PARTS2_def = Define
  `(parts' []     = [[]]) /\
   (parts' l = 
     (SET_TO_LIST 
       {partit| ((FILTER ($<> []) partit )=partit) /\ (FLAT partit = l )}))`;


EVAL ``parts [x;y;z]``;
EVAL ``parts [1;2]``;
EVAL ``parts [1]``;
EVAL ``parts []``;
EVAL ``parts [x;y;z;w]``;

val PARTS_EMPTY_THM = store_thm(
  "PARTS_EMPTY_THM",
  ``!e. (e =[]) = (MEM (e) (parts ([])))``,

    ASM_SIMP_TAC list_ss [PARTS_def, FLAT, MEM, FILTER]
);

val PARTS_NON_EMPTY_THM = store_thm(
  "PARTS_NON_EMPTY_THM",
  ``!e x . x<>[] ==> 
           (MEM x (parts e )) ==> 
           (e<>[])``,
     ASM_SIMP_TAC list_ss [PARTS_EMPTY_THM]    
);

val PARTS_EMPTY_THM2 = store_thm(
  "PARTS_EMPTY_THM2",
  ``!e. (MEM [] (parts e )) ==> (e=[])``,
SIMP_TAC list_ss [PARTS_SPEC])


val PARTS_SINGEL_THM = store_thm(
  "PARTS_SINGEl_THM",
  ``!e x. (e =[[x]]) = (MEM (e) (parts [x]))``,

    ASM_SIMP_TAC list_ss [PARTS_def, FLAT, MEM, FILTER]

);

val PARTS_MEM_HEAD_THM = store_thm(
  "PARTS_MEM_HEAD_THM",
  ``!h t e. (MEM e (parts t)) =
            (MEM ([h]::e) (parts (h::t)))``,
  SIMP_TAC list_ss [PARTS_SPEC]);


val PARTS_MEM_APPEND_THM1 = store_thm(
  "PARTS_MEM_APPEND_THM1",

  ``!l1 l2 l1' l2'. (MEM l1' (parts l1))  ==>
            (MEM l2' (parts l2))  ==>
            (MEM (l1' ++ l2') (parts (l1 ++ l2)))``,
  
SIMP_TAC list_ss [PARTS_SPEC]);


val PARTS_MEM_APPEND_THM2 = store_thm(
  "PARTS_MEM_APPEND_THM2",

  ``!l1 l2 l1' l2'. (MEM l1' (parts l1))  ==>
            (MEM l2' (parts l2))  ==>
            (MEM (l1' ++ l2') (parts (l1 ++ l2)))``,

SIMP_TAC list_ss [PARTS_SPEC]);


val PARTS_FLAT_MEM_THM = store_thm(
  "PARTS_FLAT_MEM_THM",
  
  ``!partition l. ((FLAT partition) = l) ==> 
                  ((MEM (FILTER ($<>[] ) partition)) ( parts l))``,

SIMP_TAC list_ss [PARTS_SPEC, MEM_FILTER] >>
Induct >- SIMP_TAC list_ss [] >>
ASM_SIMP_TAC (list_ss++boolSimps.LIFT_COND_ss) []);


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
   (accept (Rep r)   []    =  accept r [])/\ 
   (accept (Rep r)   (h::t) = 
        EXISTS (\partition. EVERY (\part. accept r part) partition) (parts (h::t))
   )`;

EVAL ``accept (Sym e) [e]``;
EVAL ``accept (Sym e) []``;
EVAL ``accept (Rep (Alt (Sym 1) (Sym 2))) [1;2;1;1;3]``;
EVAL ``accept (Rep (Alt (Sym 1) (Sym 2))) [1;2;1;1]``;
EVAL ``accept (Rep (Alt (Sym 1) (Eps))) []``;
EVAL ``accept (Rep (Sym 1)) []``;





(* ============================================================ *)
(*  Equaivalance of semantics and executable model         *)
(* ============================================================= *)

EVAL ``accept (Seq (Sym 1)(Sym 2)) [1;2]``;



val LANGUAGE_ACCEPTED_THM = store_thm(
  "LANGUAGE_ACCEPTED_THM", 
  ``!R x. x IN language_of R ==> accept R x``,
  
  Induct_on `R` >> 
    (* Solve simple cases *)
    REPEAT STRIP_TAC >> 
    FULL_SIMP_TAC list_ss [LANGUAGE_OF_def, ACCEPT_def] >|
  [
    FULL_SIMP_TAC std_ss [SET_SPEC_CONV ``x IN
      {fstPrt ++ sndPrt |
       fstPrt IN language_of R /\ sndPrt IN language_of R'}``]>>
    MP_TAC (Q.SPECL [`fstPrt`,`sndPrt`] SPLIT_APPEND_THM)>>
    STRIP_TAC>>
    ASM_SIMP_TAC std_ss [EXISTS_DEF, EXISTS_APPEND]
  ,                  
    FULL_SIMP_TAC bool_ss [IN_GSPEC_IFF]>>
    Cases_on `x` >> ASM_REWRITE_TAC [ACCEPT_def] >- 
    (
      Cases_on `words=[]::t`>>
      Cases_on `words`>>
      FULL_SIMP_TAC list_ss [FLAT,EVERY_DEF]
    )>>
    REWRITE_TAC [ EXISTS_MEM]>>
    Q.EXISTS_TAC `FILTER ($<>[]) words`>>
    STRIP_TAC >|
    [ 
      ASM_SIMP_TAC list_ss [PARTS_FLAT_MEM_THM]
    ,
      SIMP_TAC std_ss []
      LANGUAGE_OF_def 
      Q.SPECL [`\e.true`, `\(x:'a list).x=x`, `(words:'a list list)`] EVERY_FILTER_IMP 
      REWRITE_TAC [EVERY_FILTER_IMP]
      Q.PAT_X_ASSUM `EVERY (_) words` (fn x => MP_TAC x)>>
      SIMP_TAC std_ss [EVERY_MEM]>>
      REPEAT STRIP_TAC>>
      ASM_SIMP_TAC std_ss[]
    ]
  ]
);

(*
``!x n e. accept (Rep (Sym e)) (REPLICATE (n+1) e)``
  `!n. (n + 1 ) = ( SUC n )` by DECIDE_TAC >> 
  Q.PAT_X_ASSUM `_` (fn x => REWRITE_TAC [x, REPLICATE ])
  

  Induct_on `n`>> SIMP_TAC list_ss [ REPLICATE ] >|
  [
    ASM_REWRITE_TAC [REPLICATE, ACCEPT_def, PARTS_def]>>
    SIMP_TAC list_ss [EVERY_DEF, EXISTS_DEF]
  ,
    ONCE_REWRITE_TAC [ACCEPT_def]
    ONCE_REWRITE_TAC [PARTS_def]
    GEN_TAC
    IF_CASES_TAC 
    ASM_SIMP_TAC list_ss [NOT_CONS_NIL, ACCEPT_def]
    
    REWRITE_TAC [GSYM ACCEPT_def] 
    REWRITE_TAC [GSYM PARTS_def]
    DB.match [] ``e::t<>[]``
    ASM_SIMP_TAC list_ss []
    REPLICATE 
    SIMP_TAC std_ss []
  *)

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
