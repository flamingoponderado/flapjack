import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompileCodeInfo
namespace Flapjack.Test.StackRawCallCompileCodeInfoParity
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall

example {width : Nat} [NeZero width] (code : List (Nat × HolProg width)) :
    sptDomain (sptFromAList (compile code)) = sptDomain (sptFromAList code) :=
  domainFromAListCompile code

example {width : Nat} [NeZero width] (code : List (Nat × HolProg width)) (key : Nat) (rest : Spt Nat)
    (distinct : (code.map Prod.fst).Nodup) :
    sptLookup key (collectInfo code rest) =
      match sptAListLookup key code with
      | none => sptLookup key rest
      | some body => sptLookup key (collectInfo [(key, body)] rest) :=
  by
    have law := lookupCollectInfo code key rest distinct
    cases found : sptAListLookup key code <;> simpa only [found] using law

example {width : Nat} [NeZero width] (code : List (Nat × HolProg width))
    (distinct : (code.map Prod.fst).Nodup) :
    stateOk (collectInfo code .ln) (sptFromAList code) := stateOkCollectInfo code distinct

example  (code : List (Nat × HolProg 1)) :
    sptDomain (sptFromAList (compile code)) = sptDomain (sptFromAList code) :=
  domainFromAListCompile code

example  (code : List (Nat × HolProg 1)) (key : Nat) (rest : Spt Nat)
    (distinct : (code.map Prod.fst).Nodup) :
    sptLookup key (collectInfo code rest) =
      match sptAListLookup key code with
      | none => sptLookup key rest
      | some body => sptLookup key (collectInfo [(key, body)] rest) :=
  by
    have law := lookupCollectInfo code key rest distinct
    cases found : sptAListLookup key code <;> simpa only [found] using law

example  (code : List (Nat × HolProg 1))
    (distinct : (code.map Prod.fst).Nodup) :
    stateOk (collectInfo code .ln) (sptFromAList code) := stateOkCollectInfo code distinct

example  (code : List (Nat × HolProg 8)) :
    sptDomain (sptFromAList (compile code)) = sptDomain (sptFromAList code) :=
  domainFromAListCompile code

example  (code : List (Nat × HolProg 8)) (key : Nat) (rest : Spt Nat)
    (distinct : (code.map Prod.fst).Nodup) :
    sptLookup key (collectInfo code rest) =
      match sptAListLookup key code with
      | none => sptLookup key rest
      | some body => sptLookup key (collectInfo [(key, body)] rest) :=
  by
    have law := lookupCollectInfo code key rest distinct
    cases found : sptAListLookup key code <;> simpa only [found] using law

example  (code : List (Nat × HolProg 8))
    (distinct : (code.map Prod.fst).Nodup) :
    stateOk (collectInfo code .ln) (sptFromAList code) := stateOkCollectInfo code distinct

example  (code : List (Nat × HolProg 64)) :
    sptDomain (sptFromAList (compile code)) = sptDomain (sptFromAList code) :=
  domainFromAListCompile code

example  (code : List (Nat × HolProg 64)) (key : Nat) (rest : Spt Nat)
    (distinct : (code.map Prod.fst).Nodup) :
    sptLookup key (collectInfo code rest) =
      match sptAListLookup key code with
      | none => sptLookup key rest
      | some body => sptLookup key (collectInfo [(key, body)] rest) :=
  by
    have law := lookupCollectInfo code key rest distinct
    cases found : sptAListLookup key code <;> simpa only [found] using law

example  (code : List (Nat × HolProg 64))
    (distinct : (code.map Prod.fst).Nodup) :
    stateOk (collectInfo code .ln) (sptFromAList code) := stateOkCollectInfo code distinct

example  (code : List (Nat × HolProg 80)) :
    sptDomain (sptFromAList (compile code)) = sptDomain (sptFromAList code) :=
  domainFromAListCompile code

example  (code : List (Nat × HolProg 80)) (key : Nat) (rest : Spt Nat)
    (distinct : (code.map Prod.fst).Nodup) :
    sptLookup key (collectInfo code rest) =
      match sptAListLookup key code with
      | none => sptLookup key rest
      | some body => sptLookup key (collectInfo [(key, body)] rest) :=
  by
    have law := lookupCollectInfo code key rest distinct
    cases found : sptAListLookup key code <;> simpa only [found] using law

example  (code : List (Nat × HolProg 80))
    (distinct : (code.map Prod.fst).Nodup) :
    stateOk (collectInfo code .ln) (sptFromAList code) := stateOkCollectInfo code distinct

example : stateOk (width := 64)
    (collectInfo ([(3, .seq (.stackAlloc 0) .skip), (5, .stackAlloc 4)] : List (Nat × HolProg 64)) .ln)
    (sptFromAList [(3, .seq (.stackAlloc 0) .skip), (5, .stackAlloc 4)]) :=
  stateOkCollectInfo _ (by decide)
#guard (compile ([(3, .skip), (5, .skip), (3, .stackAlloc 0)] : List (Nat × HolProg 64))).map Prod.fst = [3, 5, 3]
#guard sptLookup 77 (collectInfo ([] : List (Nat × HolProg 64)) (sptInsert 3 99 .ln)) = none
#guard sptLookup 3 (collectInfo ([(3, .stackAlloc 4)] : List (Nat × HolProg 64)) (sptInsert 3 99 .ln)) = some 99
#guard sptLookup 3 (collectInfo ([(3, .seq (.stackAlloc 0) .skip)] : List (Nat × HolProg 64)) (sptInsert 3 99 .ln)) = some 0
#guard sptLookup 6 (collectInfo ([(3, .stackAlloc 4), (6, .seq (.stackAlloc (2^70)) .skip)] : List (Nat × HolProg 64)) (sptInsert 3 99 .ln)) = some (2^70)

example : stateOk (width := 80)
    (collectInfo ([(3, .seq (.stackAlloc 0) .skip), (5, .stackAlloc 4)] : List (Nat × HolProg 80)) .ln)
    (sptFromAList [(3, .seq (.stackAlloc 0) .skip), (5, .stackAlloc 4)]) :=
  stateOkCollectInfo _ (by decide)
#guard (compile ([(3, .skip), (5, .skip), (3, .stackAlloc 0)] : List (Nat × HolProg 80))).map Prod.fst = [3, 5, 3]
#guard sptLookup 77 (collectInfo ([] : List (Nat × HolProg 80)) (sptInsert 3 99 .ln)) = none
#guard sptLookup 3 (collectInfo ([(3, .stackAlloc 4)] : List (Nat × HolProg 80)) (sptInsert 3 99 .ln)) = some 99
#guard sptLookup 3 (collectInfo ([(3, .seq (.stackAlloc 0) .skip)] : List (Nat × HolProg 80)) (sptInsert 3 99 .ln)) = some 0
#guard sptLookup 6 (collectInfo ([(3, .stackAlloc 4), (6, .seq (.stackAlloc (2^70)) .skip)] : List (Nat × HolProg 80)) (sptInsert 3 99 .ln)) = some (2^70)

end Flapjack.Test.StackRawCallCompileCodeInfoParity
