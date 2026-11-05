import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MakeSpace
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CombinedStore

/-! Reserving source space after a successful word-level allocation check. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Flapjack infrastructure: when the word machine reports sufficient space
for the encoded request, the candidate state relation supports the same
source-word reservation. -/
theorem stateRel64_hasSpace {C F : Type} (conf : Config) (l1 l2 requested : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (enough : WordSemStateFiniteExact.hasSpace (.word (gcAllocSize requested)) target = some true) :
    stateRel64 conf l1 l2 { source with space := requested } target none locs := by
  obtain ⟨nextFree, trigger, available, nextStore, triggerStore, difference, _, bound, reserve⟩ :=
    stateRel64_spaceAvailable conf l1 l2 source target locs related
  have fits : (gcAllocSize requested : BitVec 64) ≤ 8 * BitVec.ofNat 64 available := by
    simp only [WordSemStateFiniteExact.hasSpace, WordSemStateFiniteExact.getStore, nextStore,
      triggerStore, difference, Option.some.injEq, decide_eq_true_eq] at enough
    exact BitVec.le_def.mpr enough
  apply reserve requested
  apply gcAllocSize_le_imp (width := 64) requested available
  · simpa [wordSemBytesInWord] using fits
  · simpa [Nat.mul_comm] using bound
  · exact related.2.2.2.2.2.2.1

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
