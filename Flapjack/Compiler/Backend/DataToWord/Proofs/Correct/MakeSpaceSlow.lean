import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.MakeSpace

/-! The generated allocation branch before the collector runs. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- If the allocation check selects collection, executing the compiled
program reaches the actual slow path with register 1 holding the available
byte count. This includes the optional diagnostic FFIs and makes no
assumption about the allocator's result. -/
theorem makeSpace64_slow_transition {C F : Type} (conf : Config)
    (secn label : Nat) (target : WordSemStateFiniteExact 64 C F)
    (amount : Nat) (live : NumSet) (nextFree trigger : BitVec 64)
    (nextStore : target.store.lookup .nextFree = some (.word nextFree))
    (triggerStore : target.store.lookup .triggerGC = some (.word trigger))
    (slow : Compiler.Encoders.Asm.wordCmpHOL .lower (trigger - nextFree)
      (makeSpaceRequest64 amount) = true) :
    WordSemStateFiniteExact.evaluate
      (compileControl64 conf secn label (.makeSpace amount live)).1 target =
    WordSemStateFiniteExact.evaluate
      (wordListSeq [silentFfi conf 3 (adjustSets live),
        .assign 1 (.const (makeSpaceRequest64 amount)), .alloc 1 (adjustSets live),
        silentFfi conf 3 (adjustSets live)])
      (WordSemStateFiniteExact.setVar 1 (.word (trigger - nextFree)) target) := by
  let target1 := WordSemStateFiniteExact.setVar 1 (.word (trigger - nextFree)) target
  have first : WordSemStateFiniteExact.evaluate
      (.assign 1 (.op .sub [.lookup .triggerGC, .lookup .nextFree])) target = (none, target1) := by
    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
      WordSemStateFiniteExact.getStore, triggerStore, nextStore, wordOpHOL, wordOp, theWords, target1]
  have read : WordSemStateFiniteExact.getVar 1 target1 = some (.word (trigger - nextFree)) := by
    simp [target1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
  have fix : WordSemStateFiniteExact.fixClock target ((none : Option (WordSemResult 64)), target1) =
      (none, target1) := by
    simp [WordSemStateFiniteExact.fixClock, target1, WordSemStateFiniteExact.setVar]
  simp only [compileControl64, compileControl?, Option.getD_some]
  simp only [show 64 / 8 = 8 by decide]
  change WordSemStateFiniteExact.evaluate (.seq
    (.assign 1 (.op .sub [.lookup .triggerGC, .lookup .nextFree]))
    (.ite .lower 1 (.imm (makeSpaceRequest64 amount))
      (wordListSeq [silentFfi conf 3 (adjustSets live),
        .assign 1 (.const (makeSpaceRequest64 amount)), .alloc 1 (adjustSets live),
        silentFfi conf 3 (adjustSets live)]) .skip)) target = _
  simp only [WordSemStateFiniteExact.evaluate, first, fix,
    WordSemStateFiniteExact.getVarImm, wordSemWordCmp, read, slow]
  rfl

/-- With diagnostic FFIs disabled, the slow path installs the precise request
word and invokes the real allocator. The enclosing sequence restores the
clock and termination depth according to the word semantics. -/
theorem makeSpace64_slow_noFfi {C F : Type} (conf : Config)
    (secn label : Nat) (target : WordSemStateFiniteExact 64 C F)
    (amount : Nat) (live : NumSet) (nextFree trigger : BitVec 64)
    (nextStore : target.store.lookup .nextFree = some (.word nextFree))
    (triggerStore : target.store.lookup .triggerGC = some (.word trigger))
    (slow : Compiler.Encoders.Asm.wordCmpHOL .lower (trigger - nextFree)
      (makeSpaceRequest64 amount) = true) (noFfi : conf.callEmptyFfi = false) :
    WordSemStateFiniteExact.evaluate
      (compileControl64 conf secn label (.makeSpace amount live)).1 target =
    let allocated := WordSemStateFiniteExact.setVar 1 (.word (makeSpaceRequest64 amount))
      (WordSemStateFiniteExact.setVar 1 (.word (trigger - nextFree)) target)
    WordSemStateFiniteExact.fixClock allocated
      (WordSemStateFiniteExact.evaluate (.alloc 1 (adjustSets live)) allocated) := by
  rw [makeSpace64_slow_transition conf secn label target amount live nextFree trigger
    nextStore triggerStore slow]
  simp only [silentFfi, noFfi, Bool.false_eq_true, ↓reduceIte, wordListSeq]
  let t1 := WordSemStateFiniteExact.setVar 1 (.word (trigger - nextFree)) target
  let t2 := WordSemStateFiniteExact.setVar 1 (.word (makeSpaceRequest64 amount)) t1
  have fix1 : WordSemStateFiniteExact.fixClock t1 ((none : Option (WordSemResult 64)), t1) =
      (none, t1) := by simp [WordSemStateFiniteExact.fixClock]
  have assign : WordSemStateFiniteExact.evaluate
      (.assign 1 (.const (makeSpaceRequest64 amount))) t1 = (none, t2) := by
    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, t2]
  have fix2 : WordSemStateFiniteExact.fixClock t1 ((none : Option (WordSemResult 64)), t2) =
      (none, t2) := by
    simp [WordSemStateFiniteExact.fixClock, t2, WordSemStateFiniteExact.setVar]
  change WordSemStateFiniteExact.evaluate (.seq .skip
    (.seq (.assign 1 (.const (makeSpaceRequest64 amount)))
      (.seq (.alloc 1 (adjustSets live)) .skip))) t1 = _
  simp only [WordSemStateFiniteExact.evaluate, fix1, assign, fix2]
  generalize h : WordSemStateFiniteExact.fixClock t2
    (WordSemStateFiniteExact.evaluate (.alloc 1 (adjustSets live)) t2) = result
  rcases result with ⟨result, state⟩
  simp only [WordSemStateFiniteExact.evaluate] at h
  have h' := h
  dsimp only [t2, t1] at h'
  simp only [h, h']
  cases result <;> rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
