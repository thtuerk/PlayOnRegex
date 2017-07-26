open HolKernel Parse boolLib bossLib
open pred_setSyntax listTheory rich_listTheory pred_setTheory
		    
val _ = new_theory "poregex"

val Regex = Datatype `Reg = Eps
                          | Sym 'a
                          | Alt Reg Reg
                          | Seq Reg Reg
                          | Rep Reg`;

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


val SPLIT_def = Define 
  `(split []    = [([],[])]) /\
   (split (c::cs) = ([],c::cs)::(MAP (\x. (c::(FST x), SND x)) (split cs)))`;

EVAL ``split []``;
EVAL ``split [x]``;
EVAL ``split [x;y;z]``;

val PARTS_def = Define
  `(parts []     = [[]]) /\
   (parts (c::cs) = 
     if cs = [] 
     then [[[c]]] 
     else FLAT (MAP (\x. [[c]::x; (c::(HD x))::(TL x)]) (parts cs)))
   `;


EVAL ``parts [x;y;z]``;
EVAL ``parts [1;2]``;
EVAL ``parts [1]``;
EVAL ``parts []``;
EVAL ``parts [x;y;z;w]``;

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

(*REWRITE_TAC [ACCEPT_def, PARTS_def]
REWRITE_TAC [EXISTS_DEF]
SIMP_TAC std_ss []
EVERY_DEF
*)
EVAL ``accept (Seq (Sym 1)(Sym 2)) [1;1]``;

val LANGUAGE_ACCEPTED_THM = store_thm(
  "LANGUAGE_ACCEPTED_THM", 
  ``!R x. x IN language_of R ==> accept R x``,
  
  Induct_on `R` >> 
    SIMP_TAC list_ss [LANGUAGE_OF_def, ACCEPT_def] >|
  [
    REPEAT STRIP_TAC >> 
    FULL_SIMP_TAC bool_ss []
  ,
    cheat
  (* do not know how to deal with append in comprehension *)
  (* if only sohehow i could rewrite 
            x ∈ {fstPrt ++ sndPrt |
                 fstPrt ∈ language_of R ∧ sndPrt ∈ language_of R'} 
   to
            (x = firstPrt ++ sndPrt) ∧
            fstPrt ∈ language_of R   ∧
            sndPrt ∈ language_of R'} 
  *)
  ,
   cheat
    (*GEN_TAC>>
    FULL_SIMP_TAC bool_ss [IN_GSPEC_IFF]>>
    REPEAT STRIP_TAC >> 
    Cases_on `x` >> ASM_REWRITE_TAC [ACCEPT_def] >- (
      Cases_on `words=[]::t`>|
      [ 
        FULL_SIMP_TAC list_ss [FLAT,EVERY_DEF]
      ,
        Cases_on `words` >> FULL_SIMP_TAC list_ss []
      ];
    )>>
    Induct_on `words`>>
    METIS_TAC [FLAT]
    REPEAT STRIP_TAC >> 
    GEN_TAC
    REWRITE_TAC [PARTS_def]
    STRIP_TAC
    `words <> []` by ASM_SIMP_TAC list_ss []*)
    (* to be continued *)
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
val _ = export_theory()
