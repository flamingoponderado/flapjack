import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ReturningCall
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.IndirectCallSetup

/-! Normal returns from indirect non-tail calls. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- If an indirect callee returns normally and the source caller can restore its
frame, both calls continue in related states. The callee return premise is a
case of the recursive simulation, not a claim about arbitrary code. -/
theorem returningCall64_indirect {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
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
    (returnValues : List DataSem.Value) (wordValues : List (WordLocW 64))
    (sourceLast : DataSem.State C F) (targetLast : WordSemStateFiniteExact 64 C F)
    (sourceBody : DataSem.evaluate body (DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source))) =
      (some (.val returnValues), sourceLast))
    (wordBody : WordSemStateFiniteExact.evaluate (compileControl64 conf callee 2 body).1
      (WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
        (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
          none (WordSemStateFiniteExact.decClock target))) = (some (.result (.loc secn label) wordValues), targetLast))
    (sameValues : returnValues.length = wordValues.length)
    (after : stateRel64 conf secn label sourceLast targetLast (some (returnValues.zip wordValues)) ((l1, l2) :: locs))
    (arity : returnValues.length = returns.length)
    (sourcePopped : DataSem.State C F)
    (pop : DataSem.popEnv (DataSem.fixClock
      (DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source))) ((), sourceLast)).2 = some sourcePopped) :
    continues64 conf secn label l1 l2 (.call (some (returns, live)) none (names ++ [lastName]) none) source target locs := by
  let sourceEntry := DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source))
  let targetEntry := WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
    (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
      none (WordSemStateFiniteExact.decClock target))
  let k := min sourceEntry.clock sourceLast.clock
  let sourceClamped := { sourceLast with clock := k }
  let targetClamped := { targetLast with clock := k, termdep := targetEntry.termdep }
  subst size
  obtain ⟨sourceAll, wordAll, sourceCode, wordCode, wordCut, notEmpty, mappedDistinct, entryRelated⟩ :=
    indirectCall64_setup conf secn label l1 l2 source target locs related callee names returns lastName live saved values args body
      sourceRun wordRun pointer lookup cut distinct none
  have entryClock : targetEntry.clock = sourceEntry.clock := entryRelated.2.1
  have afterClock : targetLast.clock = sourceLast.clock := after.2.1
  have clampRel : stateRel64 conf secn label sourceClamped targetClamped (some (returnValues.zip wordValues)) ((l1, l2) :: locs) :=
    stateRel64_withClock conf secn label sourceLast targetLast (some (returnValues.zip wordValues)) ((l1, l2) :: locs) k after
  have sourcePop : DataSem.popEnv sourceClamped = some sourcePopped := by
    simpa [DataSem.fixClock, sourceClamped, k] using pop
  obtain ⟨targetPopped, r1, r2, remaining, targetPop, locEq, afterPop⟩ :=
    stateRel64_popEnv_setVars conf secn label sourceClamped sourcePopped targetClamped returns returnValues wordValues
      arity.symm sameValues ((l1, l2) :: locs) clampRel sourcePop
  simp only [List.cons.injEq, Prod.mk.injEq] at locEq
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := locEq
  have targetFix : WordSemStateFiniteExact.fixClock targetEntry
      (WordSemStateFiniteExact.evaluate (compileControl64 conf callee 2 body).1 targetEntry) =
        (some (.result (.loc secn label) wordValues), targetClamped) := by
    have minEq : (if sourceEntry.clock < sourceLast.clock then sourceEntry.clock else sourceLast.clock) = k := by
      dsimp [k]
      split <;> omega
    change WordSemStateFiniteExact.evaluate (compileControl64 conf callee 2 body).1 targetEntry =
      (some (.result (.loc secn label) wordValues), targetLast) at wordBody
    rw [wordBody]
    simp only [WordSemStateFiniteExact.fixClock, entryClock, afterClock, minEq, targetClamped]
  have domain := evaluate_fixClock_popEnv_domain (compileControl64 conf callee 2 body).1 target
    (sptInter target.locals (.ls ())) (sptInter target.locals (adjustSet live)) (.loc secn label :: args) (sptLookup callee source.stackFrameSizes) none
    (.loc secn label) wordValues targetClamped targetPopped targetFix targetPop
  have targetPositive : target.clock ≠ 0 := by simpa [related.2.1] using positive
  simp only [sourceClamped, k, sourceEntry] at sourcePop
  simp only [adjustSets] at wordCut
  dsimp [targetEntry] at targetFix
  refine ⟨DataSem.setVars returns returnValues sourcePopped,
    WordSemStateFiniteExact.setVars (returns.map adjustVar) wordValues targetPopped, ?_, ?_, afterPop⟩
  · simp [DataSem.evaluate, sourceAll, sourceCode, distinct, cut, positive, sourceBody,
      DataSem.fixClock, sourcePop, arity]
  · have compiled : (compileControl64 conf secn label (.call (some (returns, live)) none (names ++ [lastName]) none)).1 =
        .call (some (returns.map adjustVar, adjustSets live, .skip, secn, label)) none ((names ++ [lastName]).map adjustVar) none := rfl
    rw [compiled]
    simp only [List.map_append, List.map_cons, List.map_nil] at wordAll
    simp only [List.cons_append] at wordCode
    simp only [WordSemStateFiniteExact.evaluate, wordAll, wordSemBadDestArgs, wordSemAddRetLoc, wordCode,
      adjustSets, notEmpty, mappedDistinct, wordCut, targetPositive, List.length_map, List.map_append, List.map_cons, List.map_nil]
    rw [targetFix]
    simp only [← sameValues, arity, ne_eq, not_true_eq_false, false_or]
    rw [targetPop]
    simp [domain]

/-- Source safety supplies the return-count and frame-pop conditions for the
returning case of an indirect callee simulation. -/
theorem returningCall64_indirect_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
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
    (safe : (DataSem.evaluate (.call (some (returns, live)) none (names ++ [lastName]) none) source).1 ≠ some (.err (.abort .typeError)))
    (calleeReturns : returns64 conf callee 2 secn label body
      (DataSem.callEnv values size (DataSem.pushEnv saved false (DataSem.decClock source)))
      (WordSemStateFiniteExact.callEnv (.loc secn label :: args) size
        (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live))
          none (WordSemStateFiniteExact.decClock target))) ((l1, l2) :: locs)) :
    continues64 conf secn label l1 l2 (.call (some (returns, live)) none (names ++ [lastName]) none) source target locs := by
  subst size
  obtain ⟨sourceAll, _, sourceCode, _, _, _, _, _⟩ :=
    indirectCall64_setup conf secn label l1 l2 source target locs related callee names returns lastName live saved values args body
      sourceRun wordRun pointer lookup cut distinct none
  obtain ⟨ret, retWords, sourceLast, targetLast, sameValues, sourceBody, wordBody, after⟩ := calleeReturns
  have arity : ret.length = returns.length := by
    by_contra bad
    simp [DataSem.evaluate, sourceAll, sourceCode, distinct, cut, positive, sourceBody, DataSem.fixClock, bad] at safe
  cases pop : DataSem.popEnv (DataSem.fixClock
      (DataSem.callEnv values (sptLookup callee source.stackFrameSizes) (DataSem.pushEnv saved false (DataSem.decClock source))) ((), sourceLast)).2 with
  | none =>
    simp only [DataSem.fixClock] at pop
    simp [DataSem.evaluate, sourceAll, sourceCode, distinct, cut, positive, sourceBody, DataSem.fixClock, arity, pop] at safe
  | some sourcePopped =>
    exact returningCall64_indirect conf secn label l1 l2 source target locs related callee names returns lastName live saved values args body _
      sourceRun wordRun pointer lookup rfl cut distinct positive ret retWords sourceLast targetLast sourceBody wordBody sameValues after arity sourcePopped pop

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
