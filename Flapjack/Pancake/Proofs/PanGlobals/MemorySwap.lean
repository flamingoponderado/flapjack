import Flapjack.Pancake.Semantics.PanSemStateEval

namespace Flapjack.PanGlobalsMemorySwap
open Flapjack

/-- HOL257-264: store success depends on the address domain, so any initial
memory admits a successful replacement result. No coverage premise is added. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "mem_stores_memory_swap"
  (words_as_type_indexed_bitvec)]
theorem memStoresMemorySwapHOL {width : Nat} [NeZero width]
    (address : BitVec width) (values : List (HolWordLab width))
    (domain : BitVec width → Prop)
    (memory replacement result : BitVec width → HolWordLab width) :
    letI : DecidablePred domain := fun a => Classical.propDecidable (domain a)
    panMemStoresHOL address values domain memory = some result →
      ∃ updated, panMemStoresHOL address values domain replacement = some updated := by
  classical
  induction values generalizing address memory replacement result with
  | nil => intro _; exact ⟨replacement, rfl⟩
  | cons value values ih =>
    intro heval
    by_cases hd : domain address
    · simp only [panMemStoresHOL, panMemStoreHOL, if_pos hd] at heval
      obtain ⟨updated, hu⟩ := ih (address + panBytesInWord width)
        (fun a => if a = address then value else memory a)
        (fun a => if a = address then value else replacement a) result heval
      exact ⟨updated, by
        simpa only [panMemStoresHOL, panMemStoreHOL, if_pos hd] using hu⟩
    · simp [panMemStoresHOL, panMemStoreHOL, hd] at heval

end Flapjack.PanGlobalsMemorySwap
