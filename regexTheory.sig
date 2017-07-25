signature regexTheory =
sig
  type thm = Thm.thm

  val regex_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [indexedLists] Parent theory of "regex"

   [patternMatches] Parent theory of "regex"


*)
end
