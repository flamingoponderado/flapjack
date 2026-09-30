import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsMemory

namespace Flapjack.PanGlobalsMemoryLookup
open Flapjack
open Flapjack.Compiler.Backend.StackRemove (addresses)

/-- HOL310-321: a successful store list leaves addresses outside its original
address set unchanged, including when its word addresses wrap. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "mem_stores_lookup"
  (words_as_type_indexed_bitvec)]
theorem memStoresLookupHOL {width : Nat} [NeZero width]
    (address : BitVec width) (values : List (HolWordLab width))
    (domain : BitVec width → Prop)
    (memory result : BitVec width → HolWordLab width) (query : BitVec width) :
    letI : DecidablePred domain := fun a => Classical.propDecidable (domain a)
    panMemStoresHOL address values domain memory = some result ∧
      ¬ addresses address values.length query →
    result query = memory query := by
  classical
  induction values generalizing address memory result with
  | nil =>
    intro ⟨heval, _⟩
    have h := Option.some.inj heval
    subst result
    rfl
  | cons value values ih =>
    intro ⟨heval, hout⟩
    have hhead : query ≠ address := fun heq => hout (Or.inl heq)
    have htail : ¬ addresses (address + panBytesInWord width) values.length query :=
      fun h => hout (Or.inr h)
    by_cases hd : domain address
    · simp only [panMemStoresHOL, panMemStoreHOL, if_pos hd] at heval
      have h := ih (address + panBytesInWord width)
        (fun a => if a = address then value else memory a) result ⟨heval, htail⟩
      simpa only [if_neg hhead] using h
    · simp [panMemStoresHOL, panMemStoreHOL, hd] at heval

end Flapjack.PanGlobalsMemoryLookup
