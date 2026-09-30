import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Compiler.Backend.StackRemove

namespace Flapjack.PanGlobalsInitGlobalsMemory

open Flapjack
open Flapjack.Compiler.Backend.StackRemove (addresses)

/-- Exact `mem_stores_addrs_IS_SOME` (pan_globalsProofScript.sml:2079-2086).
HOL's address-set inclusion is predicate implication. Domain membership is
decided classically inside the evaluator application, with no added theorem
premise. The imported address recursion and store recursion use the same
`n2w (dimindex DIV 8)` stride. No address distinctness, alignment, or
non-wrapping assumption is needed, including at dimensions below eight. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "mem_stores_addrs_IS_SOME"
  (words_as_type_indexed_bitvec)]
theorem memStoresAddrsIsSomeHOL {width : Nat} [NeZero width]
    (address : BitVec width) (values : List (HolWordLab width))
    (domain : BitVec width → Prop) (memory : BitVec width → HolWordLab width) :
    (∀ current, addresses address values.length current → domain current) →
    ∃ updated, @panMemStoresHOL width _ address values domain
      (fun current => Classical.propDecidable (domain current)) memory = some updated := by
  classical
  induction values generalizing address memory with
  | nil =>
      intro _
      exact ⟨memory, rfl⟩
  | cons value values ih =>
      intro hcoverage
      have hhead : domain address := hcoverage address (Or.inl rfl)
      have htail : ∀ current,
          addresses (address + panBytesInWord width) values.length current → domain current := by
        intro current hcurrent
        exact hcoverage current (Or.inr hcurrent)
      obtain ⟨updated, hupdated⟩ := ih (address + panBytesInWord width)
        (fun current => if current = address then value else memory current) htail
      exact ⟨updated, by
        simpa only [panMemStoresHOL, panMemStoreHOL, if_pos hhead] using hupdated⟩

end Flapjack.PanGlobalsInitGlobalsMemory
