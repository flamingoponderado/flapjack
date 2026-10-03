import Flapjack.Compiler.Backend.WordAlloc.ProductionHeuristicInstructions
import Flapjack.Compiler.Backend.WordAlloc.ProductionHeuristicCounterJoin
import Flapjack.Compiler.Backend.WordAlloc.ProductionHeuristicSelfCall
import Flapjack.Compiler.Backend.WordAlloc.ProductionHeuristicCondition
import Flapjack.Compiler.Backend.WordAlloc.ProductionHeuristicCachePreservation
import Flapjack.Compiler.Backend.WordAlloc.HeuProg

namespace Flapjack.WordAlloc
open RiscV

/-! Complete actual heuristic producer correspondence on the accepted source
encoder. The native original getHeu is already reviewed; these untagged
implementation theorems connect the accelerator to it, derive its redundant
cache invariant, and retain both source branch and return-call behavior. -/

abbrev heuristicStateToNative (state : WordHeuristicCountMap × WordHeuristicCallSet) :
    Spt HeuData × NumSet :=
  (heuristicCountMapToNative state.1, stackNamesTree state.2.names)

theorem heuristicProgram_production {width : Nat} [NeZero width]
    (functionName : Nat) (program : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native)
    (counts : WordHeuristicCountMap) (calls : WordHeuristicCallSet)
    (valid : StackCacheRep calls.names calls.seen) :
    heuristicStateToNative (wordHeuristicFast functionName program (counts, calls)) =
      getHeu functionName native (heuristicStateToNative (counts, calls)) := by
  cases program
  case move priority moves =>
    simp only [wordLangProgToHOL, Option.some.injEq] at encoded
    subst native
    simp only [wordHeuristicFast, getHeu, heuristicStateToNative,
      heuristicMoves_production]
  case inst instruction =>
    cases hi : wordLangInstToHOL instruction <;> simp [wordLangProgToHOL, hi] at encoded
    subst native
    simp only [wordHeuristicFast, getHeu, heuristicStateToNative,
      heuristicInst_production _ _ hi]
  case mustTerminate body =>
    cases hb : wordLangProgToHOL body <;> simp [wordLangProgToHOL, hb] at encoded
    subst native
    simpa only [wordHeuristicFast, getHeu] using
      heuristicProgram_production functionName body _ hb counts calls valid
  case loop names body exits =>
    cases hb : wordLangProgToHOL body <;> simp [wordLangProgToHOL, hb] at encoded
    subst native
    simpa only [wordHeuristicFast, getHeu] using
      heuristicProgram_production functionName body _ hb counts calls valid
  case seq first second =>
    cases hf : wordLangProgToHOL first <;> cases hs : wordLangProgToHOL second <;>
      simp [wordLangProgToHOL, hf, hs] at encoded
    subst native
    have firstResult := heuristicProgram_production functionName first _ hf counts calls valid
    have secondResult := heuristicProgram_production functionName second _ hs
      (wordHeuristicFast functionName first (counts, calls)).1
      (wordHeuristicFast functionName first (counts, calls)).2
      (heuristicCache_preserved functionName first counts calls valid)
    simpa only [wordHeuristicFast, getHeu, Prod.eta, firstResult] using secondResult
  case ite compare condition right yes no =>
    cases hy : wordLangProgToHOL yes <;> cases hn : wordLangProgToHOL no <;>
      simp [wordLangProgToHOL, hy, hn] at encoded
    subst native
    have yr := heuristicProgram_production functionName yes _ hy counts calls valid
    have nr := heuristicProgram_production functionName no _ hn counts calls valid
    have merged := (callCache_merge (wordHeuristicFast functionName yes (counts, calls)).2
      (wordHeuristicFast functionName no (counts, calls)).2.names
      (heuristicCache_preserved functionName yes counts calls valid)).1
    cases right with
    | imm value =>
        simp only [wordHeuristicFast, getHeu, ← yr, ← nr, heuristicStateToNative,
          heuristicCountMap_addRhsReg, heuristicCountMap_maxAll, merged]
    | reg source =>
        simp only [wordHeuristicFast, getHeu, ← yr, ← nr, heuristicStateToNative, merged]
        rw [heuristicCondition_reads_commute]
        simp only [heuristicCountMap_addRhsReg, heuristicCountMap_maxAll]
  case set store expression =>
    simp only [wordLangProgToHOL, Option.some.injEq] at encoded
    subst native
    cases expression <;> simp [wordHeuristicFast, getHeu, wordExpToHOL,
      heuristicStateToNative, heuristicCountMap_addRhsMem]
  case shareInst operator name address =>
    simp only [wordLangProgToHOL, Option.some.injEq] at encoded
    subst native
    cases operator <;> simp only [wordHeuristicFast, getHeu, heuristicStateToNative,
      heuristicCountMap_addLhsMem, heuristicCountMap_addRhsMem]
  case call returns target arguments handler =>
    let incoming := match target with
      | some name => if name = functionName then calls.addCall counts else calls
      | none => calls
    have incomingValid : StackCacheRep incoming.names incoming.seen := by
      cases target with
      | none => exact valid
      | some name =>
          by_cases same : name = functionName
          · simpa only [incoming, same, if_true, WordHeuristicCallSet.addCall] using
              (callCache_merge calls counts.keys valid).2
          · simpa only [incoming, same, if_false] using valid
    cases hReturns : returns with
    | none =>
        cases hHandler : handler with
        | none =>
            simp [wordLangProgToHOL, hReturns, hHandler] at encoded
            subst native
            cases target with
            | none => simp only [wordHeuristicFast, getHeu, heuristicStateToNative]
            | some name =>
                by_cases same : name = functionName <;>
                  simp only [wordHeuristicFast, getHeu, heuristicStateToNative, same,
                    if_true, if_false, (callCache_addCall calls counts valid).1]
        | some exception =>
            rcases exception with ⟨name, body, label1, label2⟩
            cases hb : wordLangProgToHOL body <;>
              simp [wordLangProgToHOL, hReturns, hHandler, hb] at encoded
            subst native
            cases target with
            | none => simp only [wordHeuristicFast, getHeu, heuristicStateToNative]
            | some name =>
                by_cases same : name = functionName <;>
                  simp only [wordHeuristicFast, getHeu, heuristicStateToNative, same,
                    if_true, if_false, (callCache_addCall calls counts valid).1]
    | some returning =>
        rcases returning with ⟨values, sets, body, label1, label2⟩
        cases hb : wordLangProgToHOL body with
        | none => simp [wordLangProgToHOL, hReturns, hb] at encoded
        | some nativeBody =>
            have br := heuristicProgram_production functionName body nativeBody hb
              counts incoming incomingValid
            cases hHandler : handler with
            | none =>
                simp [wordLangProgToHOL, hReturns, hHandler, hb] at encoded
                subst native
                cases target with
                | none =>
                    simp only [incoming] at br
                    simp only [wordHeuristicFast, getHeu, ← br, heuristicStateToNative]
                | some name =>
                    by_cases same : name = functionName
                    · simp only [incoming, same, if_true] at br
                      simp only [wordHeuristicFast, getHeu, same, if_true,
                        ← (callCache_addCall calls counts valid).1, ← br, heuristicStateToNative]
                    · simp only [incoming, same, if_false] at br
                      simp only [wordHeuristicFast, getHeu, same, if_false, ← br,
                        heuristicStateToNative]
            | some exception =>
                rcases exception with ⟨name, exceptionBody, handler1, handler2⟩
                cases hh : wordLangProgToHOL exceptionBody <;>
                  simp [wordLangProgToHOL, hReturns, hHandler, hb, hh] at encoded
                subst native
                have hr := heuristicProgram_production functionName exceptionBody _ hh
                  counts incoming incomingValid
                have merged := (callCache_merge
                  (wordHeuristicFast functionName body (counts, incoming)).2
                  (wordHeuristicFast functionName exceptionBody (counts, incoming)).2.names
                  (heuristicCache_preserved functionName body counts incoming incomingValid)).1
                cases target with
                | none =>
                    simp only [incoming] at br hr merged
                    simp only [wordHeuristicFast, getHeu, ← br, ← hr, heuristicStateToNative,
                      heuristicCountMap_maxAll, merged]
                | some destination =>
                    by_cases same : destination = functionName
                    · simp only [incoming, same, if_true] at br hr merged
                      simp only [wordHeuristicFast, getHeu, same, if_true,
                        ← (callCache_addCall calls counts valid).1, ← br, ← hr,
                        heuristicStateToNative, heuristicCountMap_maxAll, merged]
                    · simp only [incoming, same, if_false] at br hr merged
                      simp only [wordHeuristicFast, getHeu, same, if_false,
                        ← br, ← hr, heuristicStateToNative, heuristicCountMap_maxAll, merged]
  all_goals try
    simp only [wordLangProgToHOL, Option.some.injEq] at encoded
    subst native
    simp [wordHeuristicFast, getHeu, heuristicStateToNative,
      heuristicCountMap_addLhsMem, heuristicCountMap_addLhsReg,
      heuristicCountMap_addRhsReg]
termination_by sizeOf program
decreasing_by
  all_goals
    simp_wf
    subst program
    try rw [hReturns]
    try rw [hHandler]
    try simp
    all_goals omega

/-- The actual empty initializer supplies the proved input cache invariant;
no encoder-output or native-analysis-result premise is introduced. -/
theorem heuristicProgram_initial {width : Nat} [NeZero width]
    (functionName : Nat) (program : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native) :
    heuristicStateToNative (wordHeuristicFast functionName program ({}, {})) =
      getHeu functionName native (.ln, .ln) := by
  simpa only [heuristicStateToNative, heuristicCountMap_initial,
    stackNamesTree, List.map_nil, sptFromAList] using
    heuristicProgram_production functionName program native encoded {} {} callCache_initial

end Flapjack.WordAlloc
