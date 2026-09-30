import Flapjack.Pancake.Semantics.PanSemStateEval

namespace Flapjack.PanGlobalsMemStoresAppend

/-- Exact source concatenation equation, with all address arithmetic modular. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "mem_stores_append"
  (words_as_type_indexed_bitvec)]
theorem memStoresAppend {width : Nat} [NeZero width]
    (address : BitVec width) (values : List (HolWordLab width))
    (domain : BitVec width → Prop) [DecidablePred domain]
    (memory : BitVec width → HolWordLab width) (suffix : List (HolWordLab width)) :
    panMemStoresHOL address (values ++ suffix) domain memory =
      match panMemStoresHOL address values domain memory with
      | none => none
      | some updated => panMemStoresHOL
          (address + panBytesInWord width * BitVec.ofNat width values.length) suffix domain updated := by
  induction values generalizing address memory with
  | nil => simp [panMemStoresHOL]
  | cons value values ih =>
    simp only [List.cons_append, panMemStoresHOL]
    split
    · rename_i updated heq
      rw [ih]
      simp only [List.length_cons]
      congr 1
      funext finalMemory
      rw [BitVec.ofNat_add, BitVec.mul_add]
      simp only [BitVec.mul_one]
      rw [BitVec.add_comm (panBytesInWord width * BitVec.ofNat width values.length)
        (panBytesInWord width), BitVec.add_assoc]
    · rfl

end Flapjack.PanGlobalsMemStoresAppend
