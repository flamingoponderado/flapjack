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
bound and avoided-register conditions. No bijection premise is added. The canonical finite-support map is passed to
the existing lookup-function helper through its lookup field, matching HOL
tlookup without assuming support of an arbitrary function map. -/
@[hol "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "names_ok_imp"
  (fmap_as_finite_support_relation := [names]) (words_as_type_indexed_bitvec)]
theorem namesOkImp {width : Nat} [NeZero width]
    (names : Flapjack.HolFiniteMapExact Nat Nat) (config : AsmConfigExact width)
    (h : namesOkHOL names.lookup config.regCount config.avoidRegs) :
    ∀ register, regName register config → asmRegOkExact (findName names.lookup register) config = true := by
  intro register hr
  have hm : findName names.lookup register ∈
      (List.range (config.regCount - config.avoidRegs.length)).map (findName names.lookup) :=
    List.mem_map.mpr ⟨register, List.mem_range.mpr hr, rfl⟩
  have hall := h.2
  simp only [List.all_eq_true] at hall
  exact hall _ hm

/-- HOL names_ok_imp2: distinct logical registers below the source name bound
remain distinct under renaming. The sole source antecedent is retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_namesProofScript.sml" "names_ok_imp2"
  (fmap_as_finite_support_relation := [names]) (words_as_type_indexed_bitvec)]
theorem namesOkImp2 {width : Nat} [NeZero width]
    (names : Flapjack.HolFiniteMapExact Nat Nat) (config : AsmConfigExact width)
    (register other : Nat)
    (h : namesOkHOL names.lookup config.regCount config.avoidRegs ∧ register ≠ other ∧
      regName register config ∧ regName other config) :
    findName names.lookup register ≠ findName names.lookup other := by
  exact mappedNodupNe _ _ h.1.1 _ _ (List.mem_range.mpr h.2.2.1)
    (List.mem_range.mpr h.2.2.2) h.2.1

end Flapjack.Compiler.Backend.StackNames
