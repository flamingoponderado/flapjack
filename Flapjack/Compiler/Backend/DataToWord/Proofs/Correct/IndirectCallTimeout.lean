import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.IndirectCallSetup

/-! Timeout outcomes of indirect returning calls. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A timeout in an indirect callee propagates through the non-tail caller,
including its independent clock clamps. -/
theorem returningCall64_indirect_callee_timeout {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (lastName : Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (values : List DataSem.Value) (args : List (WordLocW 64)) (body : DataLang.Prog) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some args)
    (pointer : DataSem.getVar lastName source.locals = some (.codePtr callee))
    (lookup : sptLookup callee source.code = some (values.length, body))
    (sizeEq : size = sptLookup callee source.stackFrameSizes)
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup) (positive : source.clock ≠ 0)
    (calleeTimeout : timesOut64 conf callee 2 body
      (DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source)))
      (WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
        (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
          none (WordSemStateFiniteExact.decClock target)))) :
    timesOut64 conf secn label (.call (some (returns, live)) none (names ++ [lastName]) none) source target := by
  obtain ⟨sourceLast, targetLast, sourceBody, wordBody, ffi, bound⟩ := calleeTimeout
  subst size
  obtain ⟨sourceAll, wordAll, sourceCode, wordCode, wordCut, notEmpty, mappedDistinct, entered⟩ :=
    indirectCall64_setup conf secn label l1 l2 source target locs related callee names returns lastName live saved values args body
      sourceRun wordRun pointer lookup cut distinct none
  have targetPositive : target.clock ≠ 0 := by simpa [related.2.1] using positive
  let sourceEntry := DataSem.callEnv values (sptLookup callee source.stackFrameSizes) (DataSem.pushEnv saved false (DataSem.decClock source))
  let targetEntry := WordSemStateFiniteExact.callEnv (.loc secn label :: args) (sptLookup callee source.stackFrameSizes)
    (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
      none (WordSemStateFiniteExact.decClock target))
  let sourceFinal := (DataSem.fixClock sourceEntry ((), sourceLast)).2
  let targetFinal := (WordSemStateFiniteExact.fixClock targetEntry ((), targetLast)).2
  have wordFix : WordSemStateFiniteExact.fixClock targetEntry
      (WordSemStateFiniteExact.evaluate (compileControl64 conf callee 2 body).1 targetEntry) = (some .timeOut, targetFinal) := by
    change WordSemStateFiniteExact.evaluate (compileControl64 conf callee 2 body).1 targetEntry = (some .timeOut, targetLast) at wordBody
    rw [wordBody]
    rfl
  simp only [adjustSets] at wordCut
  dsimp [targetEntry] at wordFix
  refine ⟨sourceFinal, targetFinal, ?_, ?_, ffi, bound⟩
  · simp [DataSem.evaluate, sourceAll, sourceCode, distinct, cut, positive, sourceBody, DataSem.fixClock, sourceFinal, sourceEntry]
  · have compiled : (compileControl64 conf secn label (.call (some (returns, live)) none (names ++ [lastName]) none)).1 =
        .call (some (returns.map adjustVar, adjustSets live, .skip, secn, label)) none ((names ++ [lastName]).map adjustVar) none := rfl
    rw [compiled]
    simp only [List.map_append, List.map_cons, List.map_nil] at wordAll
    simp only [List.cons_append] at wordCode
    simp only [WordSemStateFiniteExact.evaluate, wordAll, wordSemBadDestArgs, wordSemAddRetLoc, wordCode,
      adjustSets, notEmpty, mappedDistinct, wordCut, targetPositive, List.map_append, List.map_cons, List.map_nil]
    rw [wordFix]
    simp

/-- A resolved non-tail indirect call with zero clock times out before entering
the callee, while preserving the FFI and target stack-maximum bound. -/
theorem returningCall64_indirect_zero_timeout {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (lastName : Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (values : List DataSem.Value) (args : List (WordLocW 64)) (body : DataLang.Prog) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some args)
    (pointer : DataSem.getVar lastName source.locals = some (.codePtr callee))
    (lookup : sptLookup callee source.code = some (values.length, body))
    (_sizeEq : size = sptLookup callee source.stackFrameSizes)
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup) (zero : source.clock = 0) :
    timesOut64 conf secn label (.call (some (returns, live)) none (names ++ [lastName]) none) source target := by
  obtain ⟨sourceAll, wordAll, sourceCode, wordCode, wordCut, notEmpty, mappedDistinct, entered⟩ :=
    indirectCall64_setup conf secn label l1 l2 source target locs related callee names returns lastName live saved values args body
      sourceRun wordRun pointer lookup cut distinct none
  have targetZero : target.clock = 0 := by simpa [related.2.1] using zero
  let sourceEntry := DataSem.callEnv values (sptLookup callee source.stackFrameSizes) (DataSem.pushEnv saved false (DataSem.decClock source))
  let targetEntry := WordSemStateFiniteExact.callEnv (.loc secn label :: args) (sptLookup callee source.stackFrameSizes)
    (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
      none (WordSemStateFiniteExact.decClock target))
  let sourceFinal := { sourceEntry with stack := [], locals := .ln }
  let targetFinal := WordSemStateFiniteExact.flushState true { target with stack := [], stackMax := targetEntry.stackMax }
  have bound : BackendProps.optionLe targetFinal.stackMax sourceFinal.stackMax := entered.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [adjustSets] at wordCut
  refine ⟨sourceFinal, targetFinal, ?_, ?_, ?_, bound⟩
  · simp [DataSem.evaluate, sourceAll, sourceCode, distinct, cut, zero, sourceFinal, sourceEntry]
  · have compiled : (compileControl64 conf secn label (.call (some (returns, live)) none (names ++ [lastName]) none)).1 =
        .call (some (returns.map adjustVar, adjustSets live, .skip, secn, label)) none ((names ++ [lastName]).map adjustVar) none := rfl
    rw [compiled]
    simp only [List.map_append, List.map_cons, List.map_nil] at wordAll
    simp only [List.cons_append] at wordCode
    simp only [WordSemStateFiniteExact.evaluate, wordAll, wordSemBadDestArgs, wordSemAddRetLoc, wordCode,
      adjustSets, notEmpty, mappedDistinct, wordCut, targetZero, List.map_append, List.map_cons, List.map_nil]
    simp [targetFinal, targetEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
      WordSemStateFiniteExact.decClock, WordSemStateFiniteExact.flushState, targetZero]
  · exact related.1

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
