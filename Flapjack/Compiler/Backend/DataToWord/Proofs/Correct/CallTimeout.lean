import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ReturningCall

/-! Timeout outcomes of returning direct calls. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- Word-side guards and code lookup for a successful source call setup. -/
theorem returningCall64_direct_setup {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (values : List DataSem.Value) (args : List (WordLocW 64)) (body : DataLang.Prog) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some args)
    (found : DataSem.findCode (some callee) values source.code source.stackFrameSizes = some (values, body, size))
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup) :
    wordSemFindCode (some callee) (.loc secn label :: args) target.code target.stackSize =
        some (.loc secn label :: args, (compileControl64 conf callee 2 body).1, size) ∧
    wordSemCutEnvs (adjustSets live) target.locals =
        some (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live)) ∧
    ¬ sptDomainEmpty (.ls () : NumSet) ∧ (returns.map adjustVar).Nodup := by
  obtain ⟨ws, wr, len⟩ := stateRel64_getVars conf l1 l2 source target none locs related names values sourceRun
  rw [wordRun] at wr
  have eq : args = ws := Option.some.inj wr
  subst ws
  refine ⟨stateRel64_findCode_direct conf l1 l2 source target locs related secn label callee values args body size len found,
    stateRel64_cutEnvs conf l1 l2 source target locs related live saved cut, ?_, ?_⟩
  · intro empty
    apply empty 0
    exact (sptMem_iff_lookup 0 (.ls ())).mpr ⟨(), rfl⟩
  · apply List.Nodup.map_on ?_ distinct
    intro x _ y _ eq
    simp only [adjustVar] at eq
    omega

/-- A timeout in a direct callee propagates through the non-tail caller,
including its independent clock clamps. -/
theorem returningCall64_direct_callee_timeout {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (values : List DataSem.Value) (args : List (WordLocW 64)) (body : DataLang.Prog) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some args)
    (found : DataSem.findCode (some callee) values source.code source.stackFrameSizes = some (values, body, size))
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup) (positive : source.clock ≠ 0)
    (calleeTimeout : timesOut64 conf callee 2 body
      (DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source)))
      (WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
        (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
          none (WordSemStateFiniteExact.decClock target)))) :
    timesOut64 conf secn label (.call (some (returns, live)) (some callee) names none) source target := by
  obtain ⟨sourceLast, targetLast, sourceBody, wordBody, ffi, bound⟩ := calleeTimeout
  obtain ⟨wordCode, wordCut, notEmpty, mappedDistinct⟩ :=
    returningCall64_direct_setup conf secn label l1 l2 source target locs related callee names returns live saved values args body size
      sourceRun wordRun found cut distinct
  have targetPositive : target.clock ≠ 0 := by simpa [related.2.1] using positive
  let sourceEntry := DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source))
  let targetEntry := WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
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
  · simp [DataSem.evaluate, sourceRun, found, distinct, cut, positive, sourceBody, DataSem.fixClock, sourceFinal, sourceEntry]
  · have compiled : (compileControl64 conf secn label (.call (some (returns, live)) (some callee) names none)).1 =
        .call (some (returns.map adjustVar, adjustSets live, .skip, secn, label)) (some callee) (names.map adjustVar) none := rfl
    rw [compiled]
    simp only [WordSemStateFiniteExact.evaluate, wordRun, wordSemBadDestArgs, wordSemAddRetLoc, wordCode,
      adjustSets, notEmpty, mappedDistinct, wordCut, targetPositive]
    rw [wordFix]
    simp

/-- A resolved non-tail direct call with zero clock times out before entering
the callee, while preserving the FFI and target stack-maximum bound. -/
theorem returningCall64_direct_zero_timeout {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (values : List DataSem.Value) (args : List (WordLocW 64)) (body : DataLang.Prog) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some args)
    (found : DataSem.findCode (some callee) values source.code source.stackFrameSizes = some (values, body, size))
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup) (zero : source.clock = 0) :
    timesOut64 conf secn label (.call (some (returns, live)) (some callee) names none) source target := by
  obtain ⟨wordCode, wordCut, notEmpty, mappedDistinct⟩ :=
    returningCall64_direct_setup conf secn label l1 l2 source target locs related callee names returns live saved values args body size
      sourceRun wordRun found cut distinct
  have targetZero : target.clock = 0 := by simpa [related.2.1] using zero
  let sourceEntry := DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source))
  let targetEntry := WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
    (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
      none (WordSemStateFiniteExact.decClock target))
  let sourceFinal := { sourceEntry with stack := [], locals := .ln }
  let targetFinal := WordSemStateFiniteExact.flushState true { target with stack := [], stackMax := targetEntry.stackMax }
  have entered := stateRel64_pushCall conf l1 l2 secn label source target locs related names values args size
    sourceRun wordRun live saved cut none
  have bound : BackendProps.optionLe targetFinal.stackMax sourceFinal.stackMax := entered.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [adjustSets] at wordCut
  refine ⟨sourceFinal, targetFinal, ?_, ?_, ?_, bound⟩
  · simp [DataSem.evaluate, sourceRun, found, distinct, cut, zero, sourceFinal, sourceEntry]
  · have compiled : (compileControl64 conf secn label (.call (some (returns, live)) (some callee) names none)).1 =
        .call (some (returns.map adjustVar, adjustSets live, .skip, secn, label)) (some callee) (names.map adjustVar) none := rfl
    rw [compiled]
    simp only [WordSemStateFiniteExact.evaluate, wordRun, wordSemBadDestArgs, wordSemAddRetLoc, wordCode,
      adjustSets, notEmpty, mappedDistinct, wordCut, targetZero]
    simp [targetFinal, targetEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
      WordSemStateFiniteExact.decClock, WordSemStateFiniteExact.flushState, targetZero]
  · exact related.1

/-- A callee timeout also propagates when the caller installed an exception
handler; the handler is not executed for timeout results. -/
theorem returningCall64_direct_handler_callee_timeout {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (values : List DataSem.Value) (args : List (WordLocW 64)) (body handlerBody : DataLang.Prog)
    (handlerName : Nat) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some args)
    (found : DataSem.findCode (some callee) values source.code source.stackFrameSizes = some (values, body, size))
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup) (positive : source.clock ≠ 0)
    (calleeTimeout : timesOut64 conf callee 2 body
      (DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source)))
      (WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
        (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
          (some (adjustVar handlerName, (compileControl64 conf secn (label + 2) handlerBody).1, secn, label + 1))
          (WordSemStateFiniteExact.decClock target)))) :
    timesOut64 conf secn label (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody))) source target := by
  obtain ⟨sourceLast, targetLast, sourceBody, wordBody, ffi, bound⟩ := calleeTimeout
  obtain ⟨wordCode, wordCut, notEmpty, mappedDistinct⟩ :=
    returningCall64_direct_setup conf secn label l1 l2 source target locs related callee names returns live saved values args body size
      sourceRun wordRun found cut distinct
  have targetPositive : target.clock ≠ 0 := by simpa [related.2.1] using positive
  let sourceEntry := DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source))
  let targetEntry := WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
    (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
      (some (adjustVar handlerName, (compileControl64 conf secn (label + 2) handlerBody).1, secn, label + 1))
      (WordSemStateFiniteExact.decClock target))
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
  · simp [DataSem.evaluate, sourceRun, found, distinct, cut, positive, sourceBody, DataSem.fixClock, sourceFinal, sourceEntry]
  · have compiled : (compileControl64 conf secn label
        (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody)))).1 =
        .call (some (returns.map adjustVar, adjustSets live, .skip, secn, label)) (some callee) (names.map adjustVar)
          (some (adjustVar handlerName, (compileControl64 conf secn (label + 2) handlerBody).1, secn, label + 1)) := by
      conv_lhs => unfold compileControl64
      simp only [compileControl?]
      rw [compileControl64_checked conf secn (label + 2) handlerBody]
      rfl
    rw [compiled]
    simp only [WordSemStateFiniteExact.evaluate, wordRun, wordSemBadDestArgs, wordSemAddRetLoc, wordCode,
      adjustSets, notEmpty, mappedDistinct, wordCut, targetPositive]
    rw [wordFix]
    simp

/-- The same pre-entry timeout bound holds with an installed handler. -/
theorem returningCall64_direct_handler_zero_timeout {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (callee : Nat) (names returns : List Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (values : List DataSem.Value) (args : List (WordLocW 64)) (body handlerBody : DataLang.Prog) (handlerName : Nat) (size : Option Nat)
    (sourceRun : DataSem.getVars names source.locals = some values)
    (wordRun : WordSemStateFiniteExact.getVars (names.map adjustVar) target = some args)
    (found : DataSem.findCode (some callee) values source.code source.stackFrameSizes = some (values, body, size))
    (cut : DataSem.cutEnv live source.locals = some saved) (distinct : returns.Nodup) (zero : source.clock = 0) :
    timesOut64 conf secn label (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody))) source target := by
  obtain ⟨wordCode, wordCut, notEmpty, mappedDistinct⟩ :=
    returningCall64_direct_setup conf secn label l1 l2 source target locs related callee names returns live saved values args body size
      sourceRun wordRun found cut distinct
  have targetZero : target.clock = 0 := by simpa [related.2.1] using zero
  let sourceEntry := DataSem.callEnv values size (DataSem.pushEnv saved true (DataSem.decClock source))
  let targetEntry := WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
    (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
      (some (adjustVar handlerName, (compileControl64 conf secn (label + 2) handlerBody).1, secn, label + 1))
      (WordSemStateFiniteExact.decClock target))
  let sourceFinal := { sourceEntry with stack := [], locals := .ln }
  let targetFinal := WordSemStateFiniteExact.flushState true { target with stack := [], stackMax := targetEntry.stackMax }
  have entered := stateRel64_pushCall conf l1 l2 secn label source target locs related names values args size
    sourceRun wordRun live saved cut
      (some (adjustVar handlerName, (compileControl64 conf secn (label + 2) handlerBody).1, secn, label + 1))
  have bound : BackendProps.optionLe targetFinal.stackMax sourceFinal.stackMax := entered.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [adjustSets] at wordCut
  refine ⟨sourceFinal, targetFinal, ?_, ?_, ?_, bound⟩
  · simp [DataSem.evaluate, sourceRun, found, distinct, cut, zero, sourceFinal, sourceEntry]
  · have compiled : (compileControl64 conf secn label
        (.call (some (returns, live)) (some callee) names (some (handlerName, handlerBody)))).1 =
        .call (some (returns.map adjustVar, adjustSets live, .skip, secn, label)) (some callee) (names.map adjustVar)
          (some (adjustVar handlerName, (compileControl64 conf secn (label + 2) handlerBody).1, secn, label + 1)) := by
      conv_lhs => unfold compileControl64
      simp only [compileControl?]
      rw [compileControl64_checked conf secn (label + 2) handlerBody]
      rfl
    rw [compiled]
    simp only [WordSemStateFiniteExact.evaluate, wordRun, wordSemBadDestArgs, wordSemAddRetLoc, wordCode,
      adjustSets, notEmpty, mappedDistinct, wordCut, targetZero]
    simp [targetFinal, targetEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
      WordSemStateFiniteExact.decClock, WordSemStateFiniteExact.flushState, targetZero]
  · exact related.1

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
