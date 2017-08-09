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

val AND_FOLD_FALSE_thm = prove(
  ``!a. ~(FOLDL $/\ F a)``,
  Induct >> ASM_SIMP_TAC std_ss [FOLDL]
);

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

val SPLIT_APPEND_THM = store_thm(
  "SPLIT_APPEND_THM",
  ``!A B. MEM (A,B) (split (A++B))``,

Induct >| [
  Cases >> SIMP_TAC list_ss [SPLIT_def],
  ASM_SIMP_TAC (list_ss++QI_ss) [SPLIT_def, MEM_MAP]
]);

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
  "PARTS_SINGEl_THM",
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
  ``!R x. x IN language_of R ==> accept R x``,
  Induct_on `R` >>
    (* Solve simple cases *)
    REPEAT STRIP_TAC >>
    FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss) [
      EXISTS_MEM,
      LANGUAGE_OF_def, 
      ACCEPT_def]>|
  [
    Q.EXISTS_TAC `(fstPrt,sndPrt)`>>
    ASM_SIMP_TAC list_ss [SPLIT_APPEND_THM]
  ,
    Q.EXISTS_TAC `FILTER ($<>[]) words`>>
    FULL_SIMP_TAC list_ss [MEM_FILTER, 
                           EVERY_MEM, 
                           PARTS_SPEC, 
                           GSYM FLAT_EQ_FLAT_WITHOUT_EMPTY_thm ]
  ]
);


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
