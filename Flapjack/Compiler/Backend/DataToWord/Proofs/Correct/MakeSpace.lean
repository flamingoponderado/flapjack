import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Constant
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MakeSpace
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Scratch

/-! Allocation checks that do not require a collection. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- If the generated allocation check takes its no-collection branch, and
the requested byte count fits the target word, it simulates the source cut.
The collection and overflowing-count cases remain separate obligations. -/
theorem makeSpace64_fast {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (amount : Nat) (live : NumSet) (saved : Spt DataSem.Value)
    (cut : DataSem.cutEnv live source.locals = some saved) (amountBound : amount * 8 < 2 ^ 64)
    (fast : ∃ nextFree trigger, target.store.lookup .nextFree = some (.word nextFree) ∧
      target.store.lookup .triggerGC = some (.word trigger) ∧
      Compiler.Encoders.Asm.wordCmpHOL .lower (trigger - nextFree) (BitVec.ofNat 64 (amount * 8)) = false) :
    continues64 conf secn label l1 l2 (.makeSpace amount live) source target locs := by
  obtain ⟨nextFree, trigger, available, nextStore, triggerStore, difference, sourceBound, noWrap, reserve⟩ :=
    stateRel64_spaceAvailable conf l1 l2 source target locs related
  have availableBound : available * 8 < 2 ^ 64 := by omega
  have amountNat : (BitVec.ofNat 64 (amount * 8)).toNat = amount * 8 := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt amountBound
  have availableNat : (8 * BitVec.ofNat 64 available : BitVec 64).toNat = available * 8 := by
    change (BitVec.ofNat 64 8 * BitVec.ofNat 64 available).toNat = available * 8
    rw [← BitVec.ofNat_mul]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * available < 2 ^ 64)]
    omega
  obtain ⟨nextFree', trigger', nextStore', triggerStore', check⟩ := fast
  have nextEq : nextFree' = nextFree := WordLocW.word.inj (Option.some.inj (nextStore'.symm.trans nextStore))
  have triggerEq : trigger' = trigger := WordLocW.word.inj (Option.some.inj (triggerStore'.symm.trans triggerStore))
  subst nextFree'
  subst trigger'
  rw [difference] at check
  have compare : Compiler.Encoders.Asm.wordCmpHOL .lower (8 * BitVec.ofNat 64 available)
      (BitVec.ofNat 64 (amount * 8)) = false := check
  have enoughAvailable : amount ≤ available := by
    simp only [Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, availableNat, amountNat,
      decide_eq_false_iff_not] at check
    omega
  let target1 := WordSemStateFiniteExact.setVar 1 (.word (8 * BitVec.ofNat 64 available)) target
  have reserved := reserve amount enoughAvailable
  have cutRel := stateRel64_sourceCut conf l1 l2 { source with space := amount } target locs reserved live saved cut
  have added : stateRel64 conf l1 l2 (DataSem.addSpace { source with locals := saved } amount) target none locs := by
    simpa [DataSem.addSpace, stateRel64] using cutRel
  have resultRel : stateRel64 conf l1 l2 (DataSem.addSpace { source with locals := saved } amount) target1 none locs :=
    stateRel64_setScratch1 conf l1 l2 _ target locs added _
  refine ⟨DataSem.addSpace { source with locals := saved } amount, target1, ?_, ?_, resultRel⟩
  · simp [DataSem.evaluate, cut]
  · have first : WordSemStateFiniteExact.evaluate
        (.assign 1 (.op .sub [.lookup .triggerGC, .lookup .nextFree])) target = (none, target1) := by
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore,
        triggerStore, nextStore, wordOpHOL, wordOp, theWords, difference, target1]
    have read : WordSemStateFiniteExact.getVar 1 target1 = some (.word (8 * BitVec.ofNat 64 available)) := by
      simp [target1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
    have check : WordSemStateFiniteExact.evaluate
        (.ite .lower 1 (.imm (BitVec.ofNat 64 (amount * 8)))
          (wordListSeq [silentFfi conf 3 (adjustSets live), .assign 1 (.const (BitVec.ofNat 64 (amount * 8))),
            .alloc 1 (adjustSets live), silentFfi conf 3 (adjustSets live)]) .skip) target1 = (none, target1) := by
      simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, wordSemWordCmp, read, compare]
    have fix : WordSemStateFiniteExact.fixClock target ((none : Option (WordSemResult 64)), target1) = (none, target1) := by
      simp [WordSemStateFiniteExact.fixClock, target1, WordSemStateFiniteExact.setVar]
    simp only [compileControl64, compileControl?, Option.getD_some]
    simp only [show 64 / 8 = 8 by decide, amountNat, ↓reduceIte]
    change WordSemStateFiniteExact.evaluate (.seq
      (.assign 1 (.op .sub [.lookup .triggerGC, .lookup .nextFree]))
      (.ite .lower 1 (.imm (BitVec.ofNat 64 (amount * 8)))
        (wordListSeq [silentFfi conf 3 (adjustSets live), .assign 1 (.const (BitVec.ofNat 64 (amount * 8))),
          .alloc 1 (adjustSets live), silentFfi conf 3 (adjustSets live)]) .skip)) target = _
    simp only [WordSemStateFiniteExact.evaluate, first, fix, check]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
