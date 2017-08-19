structure poregexML :> poregexML =
struct
  nonfix accept parts split Rep Seq Alt Sym Eps * / div mod + - ^ @ <> >
         < >= <= := o before;

  open listML

  datatype 'a Reg
       = Eps
       | Sym of 'a
       | Alt of 'a Reg * 'a Reg
       | Seq of 'a Reg * 'a Reg
       | Rep of 'a Reg
  fun split [] = [([],[])]
    | split (c::cs) =
        ([],c::cs)::
        MAP (fn x => (c::pairML.FST x,pairML.SND x)) (split cs)

  fun parts [] = [[]]
    | parts (c::cs) =
        (if cs = [] then
           [[[c]]]
         else FLAT (MAP (fn x => [[c]::x,(c::HD x)::TL x]) (parts cs)))

  fun accept Eps u = (u = [])
    | accept (Sym(c)) u = (u = [c])
    | accept (Alt(p,q)) u = accept p u orelse accept q u
    | accept (Seq(p,q)) u =
        EXISTS (fn x =>
          accept p (pairML.FST x) andalso accept q (pairML.SND x))
          (split u)
    | accept (Rep(r)) u =
        EXISTS (fn partition =>
          EVERY (fn part => accept r part) partition) (parts u)

end
