import Flapjack.Compiler.Backend.StackNames
import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Compiler.Backend.StackProps.RegisterNames

namespace Flapjack.Compiler.Backend.StackNames

open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackProps

/-- Flapjack list infrastructure: distinct mapped outputs are injective on the
original list. This factors HOL's ALL_DISTINCT_GENLIST reasoning; no HOL
original is claimed for the helper. -/
theorem mappedNodupNe {α β : Type} (f : α → β) (xs : List α)
    (h : (xs.map f).Nodup) (a b : α) (ha : a ∈ xs) (hb : b ∈ xs)
    (hne : a ≠ b) : f a ≠ f b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp ha with rfl | hat
    · rcases List.mem_cons.mp hb with rfl | hbt
      · exact False.elim (hne rfl)
      · intro heq
        exact h.1 (heq ▸ List.mem_map.mpr ⟨b, hbt, rfl⟩)
    · rcases List.mem_cons.mp hb with rfl | hbt
      · intro heq
        exact h.1 (heq ▸ List.mem_map.mpr ⟨a, hat, rfl⟩)
      · exact ih h.2 hat hbt

/-- HOL names_ok_imp: the renamed register satisfies the assembler's original
bound and avoided-register conditions. No bijection premise is added. The exact sparse tree is passed to
the existing lookup-function helper through its tree lookup, matching HOL
tlookup without assuming a representation exception. -/
@[hol "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "names_ok_imp"
  (words_as_type_indexed_bitvec)]
theorem namesOkImp {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (h : namesOkHOL (fun key => Flapjack.sptLookup key names) config.regCount config.avoidRegs) :
    ∀ register, regName register config → asmRegOkExact (findName (fun key => Flapjack.sptLookup key names) register) config = true := by
  intro register hr
  have hm : findName (fun key => Flapjack.sptLookup key names) register ∈
      (List.range (config.regCount - config.avoidRegs.length)).map (findName (fun key => Flapjack.sptLookup key names)) :=
    List.mem_map.mpr ⟨register, List.mem_range.mpr hr, rfl⟩
  have hall := h.2
  simp only [List.all_eq_true] at hall
  exact hall _ hm

/-- HOL names_ok_imp2: distinct logical registers below the source name bound
remain distinct under renaming. The sole source antecedent is retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "names_ok_imp2"
  (words_as_type_indexed_bitvec)]
theorem namesOkImp2 {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (register other : Nat)
    (h : namesOkHOL (fun key => Flapjack.sptLookup key names) config.regCount config.avoidRegs ∧ register ≠ other ∧
      regName register config ∧ regName other config) :
    findName (fun key => Flapjack.sptLookup key names) register ≠ findName (fun key => Flapjack.sptLookup key names) other := by
  exact mappedNodupNe _ _ h.1.1 _ _ (List.mem_range.mpr h.2.2.1)
    (List.mem_range.mpr h.2.2.2) h.2.1

end Flapjack.Compiler.Backend.StackNames
