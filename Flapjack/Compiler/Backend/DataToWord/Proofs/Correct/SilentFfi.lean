import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.MakeSpaceSlow
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Scratch
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.TargetCut

/-! Execution of the allocation diagnostic in the word semantics. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack

/-- Flapjack simulation infrastructure: the enabled diagnostic reads no bytes,
leaves memory and the FFI unchanged, and retains the actual cut environment.
Its scratch assignments and floating-point register reset are explicit. -/
theorem silentFfi64_enabled {C F : Type} (conf : Config)
    (target : WordSemStateFiniteExact 64 C F) (names : WordLangCutsetsHOL)
    (nextFree currHeap heapLength : BitVec 64)
    (enabled : conf.callEmptyFfi = true)
    (nextStore : target.store.lookup .nextFree = some (.word nextFree))
    (heapStore : target.store.lookup .currHeap = some (.word currHeap))
    (lengthStore : target.store.lookup .heapLength = some (.word heapLength))
    (env : Spt (WordLocW 64))
    (cut : wordSemCutEnv names
      (WordSemStateFiniteExact.setVar 9 (.word heapLength)
        (WordSemStateFiniteExact.setVar 7 (.word (nextFree - currHeap))
          (WordSemStateFiniteExact.setVar 3 (.word 0) target))).locals = some env) :
    WordSemStateFiniteExact.evaluate (silentFfi conf 3 names) target =
      (none, { (WordSemStateFiniteExact.setVar 9 (.word heapLength)
        (WordSemStateFiniteExact.setVar 7 (.word (nextFree - currHeap))
          (WordSemStateFiniteExact.setVar 3 (.word 0) target))) with
          locals := env, fpRegs := HolFiniteMapExact.empty }) := by
  simp [silentFfi, enabled, wordListSeq, WordSemStateFiniteExact.evaluate,
    WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore,
    WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
    WordSemStateFiniteExact.fixClock, nextStore, heapStore, lengthStore,
    wordOpHOL, wordOp, theWords, sptLookup_sptInsert_same, sptLookup_sptInsert_ne,
    readBytearrayWordHOL, callFFIHOL, writeBytearrayExact] at cut ⊢
  rw [cut]

/-- A successful source cut supplies the diagnostic's word cut, including
all three scratch writes. This relates the generated instruction sequence to
actual source liveness without assuming a successful target cut. -/
theorem silentFfi64_enabled_sourceCut {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : Gc.stateRel64 conf l1 l2 source target none locs)
    (live : NumSet) (saved : Spt DataSem.Value)
    (sourceCut : DataSem.cutEnv live source.locals = some saved)
    (nextFree currHeap heapLength : BitVec 64)
    (enabled : conf.callEmptyFfi = true)
    (nextStore : target.store.lookup .nextFree = some (.word nextFree))
    (heapStore : target.store.lookup .currHeap = some (.word currHeap))
    (lengthStore : target.store.lookup .heapLength = some (.word heapLength)) :
    let prepared := WordSemStateFiniteExact.setVar 9 (.word heapLength)
      (WordSemStateFiniteExact.setVar 7 (.word (nextFree - currHeap))
        (WordSemStateFiniteExact.setVar 3 (.word 0) target))
    WordSemStateFiniteExact.evaluate (silentFfi conf 3 (adjustSets live)) target =
      (none, { prepared with
        locals := sptUnion (sptInter prepared.locals (adjustSet live))
          (sptInter prepared.locals (.ls ())), fpRegs := HolFiniteMapExact.empty }) := by
  let t3 := WordSemStateFiniteExact.setVar 3 (.word 0) target
  let t7 := WordSemStateFiniteExact.setVar 7 (.word (nextFree - currHeap)) t3
  let t9 := WordSemStateFiniteExact.setVar 9 (.word heapLength) t7
  have r3 : Gc.stateRel64 conf l1 l2 source t3 none locs := by
    apply Gc.stateRel64_setScratch conf l1 l2 source target locs related 3 _ (by decide)
    intro n
    simp [adjustVar]
  have r7 : Gc.stateRel64 conf l1 l2 source t7 none locs := by
    apply Gc.stateRel64_setScratch conf l1 l2 source t3 locs r3 7 _ (by decide)
    intro n
    simp [adjustVar]; omega
  have r9 : Gc.stateRel64 conf l1 l2 source t9 none locs := by
    apply Gc.stateRel64_setScratch conf l1 l2 source t7 locs r7 9 _ (by decide)
    intro n
    simp [adjustVar]; omega
  have wordCut := Gc.stateRel64_cutEnvs conf l1 l2 source t9 locs r9 live saved sourceCut
  have cut : wordSemCutEnv (adjustSets live) t9.locals =
      some (sptUnion (sptInter t9.locals (adjustSet live)) (sptInter t9.locals (.ls ()))) := by
    simp [wordSemCutEnv, wordCut]
  exact silentFfi64_enabled conf target (adjustSets live) nextFree currHeap heapLength
    enabled nextStore heapStore lengthStore _ cut

/-- Executing the enabled diagnostic preserves the candidate relation to the
source state with its locals cut to the live set. -/
theorem silentFfi64_enabled_related {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : Gc.stateRel64 conf l1 l2 source target none locs)
    (live : NumSet) (saved : Spt DataSem.Value)
    (sourceCut : DataSem.cutEnv live source.locals = some saved)
    (nextFree currHeap heapLength : BitVec 64)
    (enabled : conf.callEmptyFfi = true)
    (nextStore : target.store.lookup .nextFree = some (.word nextFree))
    (heapStore : target.store.lookup .currHeap = some (.word currHeap))
    (lengthStore : target.store.lookup .heapLength = some (.word heapLength)) :
    ∃ targetNext, WordSemStateFiniteExact.evaluate (silentFfi conf 3 (adjustSets live)) target =
      (none, targetNext) ∧ Gc.stateRel64 conf l1 l2 { source with locals := saved } targetNext none locs := by
  let t3 := WordSemStateFiniteExact.setVar 3 (.word 0) target
  let t7 := WordSemStateFiniteExact.setVar 7 (.word (nextFree - currHeap)) t3
  let t9 := WordSemStateFiniteExact.setVar 9 (.word heapLength) t7
  have r3 : Gc.stateRel64 conf l1 l2 source t3 none locs := by
    apply Gc.stateRel64_setScratch conf l1 l2 source target locs related 3 _ (by decide)
    intro n
    simp [adjustVar]
  have r7 : Gc.stateRel64 conf l1 l2 source t7 none locs := by
    apply Gc.stateRel64_setScratch conf l1 l2 source t3 locs r3 7 _ (by decide)
    intro n
    simp [adjustVar]; omega
  have r9 : Gc.stateRel64 conf l1 l2 source t9 none locs := by
    apply Gc.stateRel64_setScratch conf l1 l2 source t7 locs r7 9 _ (by decide)
    intro n
    simp [adjustVar]; omega
  let cutTarget := { t9 with locals := (sptUnion (sptInter t9.locals (adjustSet live))
    (sptInter t9.locals (.ls ()))) }
  refine ⟨{ cutTarget with fpRegs := HolFiniteMapExact.empty }, ?_, ?_⟩
  · exact silentFfi64_enabled_sourceCut conf l1 l2 source target locs related live saved sourceCut
      nextFree currHeap heapLength enabled nextStore heapStore lengthStore
  · exact Gc.stateRel64_withFpRegs conf l1 l2 { source with locals := saved } cutTarget none locs _
      (Gc.stateRel64_cutBoth conf l1 l2 source t9 locs r9 live saved sourceCut)

/-- Both diagnostic configurations return normally and relate the resulting
word state to the source state with its live locals retained. -/
theorem silentFfi64_related {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : Gc.stateRel64 conf l1 l2 source target none locs)
    (live : NumSet) (saved : Spt DataSem.Value)
    (sourceCut : DataSem.cutEnv live source.locals = some saved)
    (nextFree currHeap heapLength : BitVec 64)
    (nextStore : target.store.lookup .nextFree = some (.word nextFree))
    (heapStore : target.store.lookup .currHeap = some (.word currHeap))
    (lengthStore : target.store.lookup .heapLength = some (.word heapLength)) :
    ∃ targetNext, WordSemStateFiniteExact.evaluate (silentFfi conf 3 (adjustSets live)) target =
      (none, targetNext) ∧ Gc.stateRel64 conf l1 l2 { source with locals := saved } targetNext none locs := by
  cases enabled : conf.callEmptyFfi with
  | false =>
    refine ⟨target, ?_, Gc.stateRel64_sourceCut conf l1 l2 source target locs related live saved sourceCut⟩
    simp [silentFfi, enabled, WordSemStateFiniteExact.evaluate]
  | true =>
    exact silentFfi64_enabled_related conf l1 l2 source target locs related live saved sourceCut
      nextFree currHeap heapLength enabled nextStore heapStore lengthStore

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
