import Flapjack.Compiler.Backend.WordCse.ProductionProgram

namespace Flapjack.Test.WordCseProductionProgramParity
open Flapjack RiscV Compiler.Backend.WordCse
private abbrev StateObservation := List (Option Nat) × List (Option Nat) × List (Option Nat) ×
    List (Option Nat) × List (Option Nat) × Nat × Nat × Nat × Nat × Nat
private structure Fixture where
  label : String
  original : WordLangProgHOL (BitVec 64)
  expected : WordLangProgHOL (BitVec 64)
  state : StateObservation
private def regKeys : List Nat := [3,5,7,9,11,13]
private def instKeys : List (List Nat) :=
  [instToNumList (.arith (.binop .add 0 9 (.reg 5)) : Compiler.Encoders.Asm.HolInst 64),
   instToNumList (.arith (.binop .add 0 5 (.reg 5)) : Compiler.Encoders.Asm.HolInst 64),
   opCurrHeapToNumList .add 9]
private def loadKeys : List (List Nat) := [loadToNumList .load 9 (0 : BitVec 64)]
private def nativeState (data : Knowledge) : StateObservation :=
  (regKeys.map (fun k => sptLookup k data.toCanonical),
   regKeys.map (fun k => sptLookup k data.toLatest),
   [WordStore.currHeap,WordStore.heapLength].map (fun k => data.getsMem.lookup k),
   instKeys.map (fun k => Misc.BalancedMap.lookup listCmp k data.instrsMem),
   loadKeys.map (fun k => Misc.BalancedMap.lookup listCmp k data.loadsMem),
   sptSize data.toCanonical,sptSize data.toLatest,data.getsMem.length,
   Misc.BalancedMap.size data.instrsMem,Misc.BalancedMap.size data.loadsMem)
private def actualState (data : WordCseKnowledge) : StateObservation :=
  (regKeys.map (fun k => data.toCanonical[k]?),
   regKeys.map (fun k => data.toLatest[k]?),
   [WordStore.currHeap,WordStore.heapLength].map
     (fun k => data.getsMem[wordCseStoreCode (k : WordStore (BitVec 64))]?),
   instKeys.map (fun k => data.instrsMem[k]?),loadKeys.map (fun k => data.loadsMem[k]?),
   data.toCanonical.size,data.toLatest.size,data.getsMem.size,data.instrsMem.size,data.loadsMem.size)
-- Complete source programs/expected programs are independently checked by
-- original EVAL equalitiesT; these state tuples come from original numeric rows.
private def fixtures : List Fixture := [
  ⟨"seq",(.seq (.inst (.arith (.binop .add 7 9 (.reg 5)))) (.inst (.arith (.binop .add 11 9 (.reg 5))))),(.seq (.inst (.arith (.binop .add 7 9 (.reg 5)))) (.move 0 [(11,7)])),([none, some 5, some 7, some 9, some 7, none],[none, none, some 11, none, none, none],[none, none],[some 7, none, none],[none],4,1,0,1,0)⟩,
  ⟨"must",(.mustTerminate (.seq (.inst (.arith (.binop .add 7 9 (.reg 5)))) (.inst (.arith (.binop .add 11 9 (.reg 5)))))),(.mustTerminate (.seq (.inst (.arith (.binop .add 7 9 (.reg 5)))) (.move 0 [(11,7)]))),([none, some 5, some 7, some 9, some 7, none],[none, none, some 11, none, none, none],[none, none],[some 7, none, none],[none],4,1,0,1,0)⟩,
  ⟨"if_same",(.seq (.ite .less 3 (.reg 5) (.inst (.arith (.binop .add 7 9 (.reg 5)))) (.inst (.arith (.binop .add 7 9 (.reg 5))))) (.inst (.arith (.binop .add 11 9 (.reg 5))))),(.seq (.ite .less 3 (.reg 5) (.inst (.arith (.binop .add 7 9 (.reg 5)))) (.inst (.arith (.binop .add 7 9 (.reg 5))))) (.move 0 [(11,7)])),([none, some 5, some 7, some 9, some 7, none],[none, none, some 11, none, none, none],[none, none],[some 7, none, none],[none],4,1,0,1,0)⟩,
  ⟨"if_different",(.seq (.ite .less 3 (.reg 5) (.inst (.arith (.binop .add 7 9 (.reg 5)))) (.inst (.arith (.binop .sub 7 9 (.reg 5))))) (.inst (.arith (.binop .add 11 9 (.reg 5))))),(.seq (.ite .less 3 (.reg 5) (.inst (.arith (.binop .add 7 9 (.reg 5)))) (.inst (.arith (.binop .sub 7 9 (.reg 5))))) (.inst (.arith (.binop .add 11 9 (.reg 5))))),([none, some 5, some 7, some 9, some 11, none],[none, none, none, none, some 11, none],[none, none],[some 11, none, none],[none],4,1,0,1,0)⟩,
  ⟨"loop",(.seq (.loop (sptFromAList [(9,())]) (.seq (.inst (.arith (.binop .add 7 9 (.reg 5)))) (.inst (.arith (.binop .add 11 9 (.reg 5))))) (sptFromAList [(11,())])) (.inst (.arith (.binop .add 13 9 (.reg 5))))),(.seq (.loop (sptFromAList [(9,())]) (.seq (.inst (.arith (.binop .add 7 9 (.reg 5)))) (.move 0 [(11,7)])) (sptFromAList [(11,())])) (.inst (.arith (.binop .add 13 9 (.reg 5))))),([none, some 5, none, some 9, none, some 13],[none, none, none, none, none, some 13],[none, none],[some 13, none, none],[none],3,1,0,1,0)⟩,
  ⟨"move",(.seq (.move 0 [(9,5)]) (.seq (.inst (.arith (.binop .add 7 9 (.reg 5)))) (.inst (.arith (.binop .add 11 9 (.reg 5)))))),(.seq (.move 0 [(9,5)]) (.seq (.inst (.arith (.binop .add 7 9 (.reg 5)))) (.move 0 [(11,7)]))),([none, some 5, some 7, some 5, some 7, none],[none, some 9, some 11, none, none, none],[none, none],[none, some 7, none],[none],4,2,0,1,0)⟩,
  ⟨"memory",(.seq (.inst (.mem .load 7 (.addr 9 0))) (.inst (.mem .load 11 (.addr 9 0)))),(.seq (.inst (.mem .load 7 (.addr 9 0))) (.move 0 [(11,7)])),([none, none, some 7, some 9, some 7, none],[none, none, some 11, none, none, none],[none, none],[none, none, none],[some 7],3,1,0,0,1)⟩,
  ⟨"heap",(.seq (.opCurrHeap .add 7 9) (.opCurrHeap .add 11 9)),(.seq (.opCurrHeap .add 7 9) (.move 0 [(11,7)])),([none, none, some 7, some 9, some 7, none],[none, none, some 11, none, none, none],[none, none],[none, none, some 7],[none],3,1,0,1,0)⟩,
  ⟨"assign",(.seq (.assign 7 (.load (.op .add [.var 9,.const 0]))) (.assign 7 (.load (.op .add [.var 9,.const 0])))),(.seq (.assign 7 (.load (.op .add [.var 9,.const 0]))) (.assign 7 (.load (.op .add [.var 9,.const 0])))),([none, none, none, none, none, none],[none, none, none, none, none, none],[none, none],[none, none, none],[none],0,0,0,0,0)⟩,
  ⟨"get_set",(.seq (.get 9 .heapLength) (.seq (.get 11 .heapLength) (.seq (.set .currHeap (.var 3)) (.get 13 .heapLength)))),(.seq (.get 9 .heapLength) (.seq (.move 1 [(11,9)]) (.seq (.set .currHeap (.var 3)) (.get 13 .heapLength)))),([none, none, none, none, none, some 13],[none, none, none, none, none, some 13],[none, some 13],[none, none, none],[none],1,1,1,0,0)⟩,
  ⟨"call_0_0",(.call (none) (some 9) [9,5] (none)),(.call (none) (some 9) [9,5] (none)),([none, none, none, none, none, none],[none, none, none, none, none, none],[none, none],[none, none, none],[none],0,0,0,0,0)⟩,
  ⟨"call_0_1",(.call (none) (some 9) [9,5] (some (5,(.seq (.inst (.arith (.binop .add 7 9 (.reg 5)))) (.inst (.arith (.binop .add 11 9 (.reg 5))))),3,4))),(.call (none) (some 9) [9,5] (some (5,(.seq (.inst (.arith (.binop .add 7 9 (.reg 5)))) (.inst (.arith (.binop .add 11 9 (.reg 5))))),3,4))),([none, none, none, none, none, none],[none, none, none, none, none, none],[none, none],[none, none, none],[none],0,0,0,0,0)⟩,
  ⟨"call_1_0",(.call (some ([7],(sptFromAList [(9,())],sptFromAList [(11,())]),(.seq (.inst (.arith (.binop .add 7 9 (.reg 5)))) (.inst (.arith (.binop .add 11 9 (.reg 5))))),1,2)) (some 9) [9,5] (none)),(.call (some ([7],(sptFromAList [(9,())],sptFromAList [(11,())]),(.seq (.inst (.arith (.binop .add 7 9 (.reg 5)))) (.inst (.arith (.binop .add 11 9 (.reg 5))))),1,2)) (some 9) [9,5] (none)),([none, none, none, none, none, none],[none, none, none, none, none, none],[none, none],[none, none, none],[none],0,0,0,0,0)⟩,
  ⟨"call_1_1",(.call (some ([7],(sptFromAList [(9,())],sptFromAList [(11,())]),(.seq (.inst (.arith (.binop .add 7 9 (.reg 5)))) (.inst (.arith (.binop .add 11 9 (.reg 5))))),1,2)) (some 9) [9,5] (some (5,(.seq (.inst (.arith (.binop .add 7 9 (.reg 5)))) (.inst (.arith (.binop .add 11 9 (.reg 5))))),3,4))),(.call (some ([7],(sptFromAList [(9,())],sptFromAList [(11,())]),(.seq (.inst (.arith (.binop .add 7 9 (.reg 5)))) (.inst (.arith (.binop .add 11 9 (.reg 5))))),1,2)) (some 9) [9,5] (some (5,(.seq (.inst (.arith (.binop .add 7 9 (.reg 5)))) (.inst (.arith (.binop .add 11 9 (.reg 5))))),3,4))),([none, none, none, none, none, none],[none, none, none, none, none, none],[none, none],[none, none, none],[none],0,0,0,0,0)⟩,
  ⟨"flat_controls",(.seq .skip (.seq (.store (.var 9) 5) (.seq (.raise 9) (.seq (.return 5 [9,7]) (.seq .tick (.seq (.alloc 7 (sptFromAList [(9,())],sptFromAList [(11,())])) (.seq (.install 3 5 7 9 (sptFromAList [(9,())],sptFromAList [(11,())])) (.seq (.codeBufferWrite 3 5) (.seq (.dataBufferWrite 7 9) (.seq (.ffi (Flapjack.Basis.Pure.MlString.ofString "x") 3 5 7 9 (sptFromAList [(9,())],sptFromAList [(11,())])) (.seq (.storeConsts 3 5 7 9 [(true,1),(false,2)]) (.seq (.shareInst .load 7 (.var 9)) (.seq (.shareInst .store 5 (.var 9)) (.seq (.break 1) (.continue 2))))))))))))))),(.seq .skip (.seq (.store (.var 9) 5) (.seq (.raise 9) (.seq (.return 5 [9,7]) (.seq .tick (.seq (.alloc 7 (sptFromAList [(9,())],sptFromAList [(11,())])) (.seq (.install 3 5 7 9 (sptFromAList [(9,())],sptFromAList [(11,())])) (.seq (.codeBufferWrite 3 5) (.seq (.dataBufferWrite 7 9) (.seq (.ffi (Flapjack.Basis.Pure.MlString.ofString "x") 3 5 7 9 (sptFromAList [(9,())],sptFromAList [(11,())])) (.seq (.storeConsts 3 5 7 9 [(true,1),(false,2)]) (.seq (.shareInst .load 7 (.var 9)) (.seq (.shareInst .store 5 (.var 9)) (.seq (.break 1) (.continue 2))))))))))))))),([none, none, none, none, none, none],[none, none, none, none, none, none],[none, none],[none, none, none],[none],0,0,0,0,0)⟩ ]
private def nativeCheck (fixture : Fixture) : Bool :=
  let output := wordCse emptyData fixture.original
  nativeState output.1 == fixture.state
example : fixtures.all nativeCheck = true := by decide +kernel

/-- Original cardinalities equal the number of present observations in each
field, so these fixture key lists cover every stored entry, not only a sample. -/
private def stateCoverage (state : StateObservation) : Bool :=
  let (canonical,latest,stores,instructions,loads,cs,ls,ss,is,ms) := state
  (canonical.filter Option.isSome).length == cs &&
    (latest.filter Option.isSome).length == ls &&
    (stores.filter Option.isSome).length == ss &&
    (instructions.filter Option.isSome).length == is &&
    (loads.filter Option.isSome).length == ms
example : fixtures.all (fun fixture => stateCoverage fixture.state) = true := by decide +kernel

-- Rejection remains visible for native instruction carriers outside the
-- existing partial codec; the wrapper theorem does not assume them away.
example : wordLangProgFromHOL (.inst .skip : WordLangProgHOL (BitVec 64)) = none := rfl
example : wordLangProgFromHOL (wordCommonSubexpElim (.inst .skip : WordLangProgHOL (BitVec 64))) = none := by
  simp [wordCommonSubexpElim,wordCse,Compiler.Backend.WordCse.wordCseInst,Compiler.Encoders.Asm.HolInst.ofWordLangInst,
    wordLangProgFromHOL,wordLangInstFromHOL,Compiler.Encoders.Asm.HolInst.toWordLangInst]

def runChecks : IO Bool := do
  for fixture in fixtures do
    match wordLangProgFromHOL fixture.original, wordLangProgFromHOL fixture.expected with
    | some original, some expected =>
      let output := wordCseProg wordCseEmpty original
      if actualState output.2 != fixture.state || reprStr output.1 != reprStr expected then
        IO.eprintln s!"FAIL executed whole CSE program {fixture.label}: {repr (actualState output.2)}"
        return false
      if reprStr (wordCseProp original) != reprStr expected then
        IO.eprintln s!"FAIL executed CSE wrapper {fixture.label}"
        return false
    | _,_ =>
      IO.eprintln s!"FAIL unexpected whole CSE fixture codec rejection {fixture.label}"
      return false
  IO.println "PASS executed whole CSE: 15 original/kernel/runtime full-program/state cases, Seq/If/Loop/MustTerminate, both Call continuations, all flat controls; state cardinalities and explicit instruction codec rejection"
  return true
end Flapjack.Test.WordCseProductionProgramParity
