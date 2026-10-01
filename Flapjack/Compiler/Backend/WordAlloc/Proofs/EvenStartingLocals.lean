import Flapjack.Compiler.Backend.RegAlloc
import Flapjack.Misc.Sptree
import Flapjack.Pancake.WordLang

namespace Flapjack.Compiler.Backend.WordAlloc.Proofs

/-- Every actual local-tree key is physical. HOL uses its domain, rather than
an initial consecutive-key sequence; word and location payloads are ignored.
The sole carrier translation is the positive type-indexed word dimension. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "even_starting_locals_def" (words_as_type_indexed_bitvec)]
def evenStartingLocals {width : Nat} [NeZero width]
    (locals : Spt (WordLocW width)) : Prop :=
  ∀ key, sptDomain locals key → Flapjack.isPhyVar key = true

/-- Flapjack domain infrastructure for the native predicate; no separately
named HOL theorem is claimed for this derived empty-tree fact. -/
@[simp] theorem evenStartingLocals_empty {width : Nat} [NeZero width] :
    evenStartingLocals (.ln : Spt (WordLocW width)) := by
  intro key member
  simp [sptDomain] at member

/-- Flapjack domain infrastructure: insertion contributes its actual key,
including overwrites, and preserves all other physical-key obligations.
There is no separately named HOL original for this derived equivalence. -/
@[simp] theorem evenStartingLocals_insert {width : Nat} [NeZero width]
    (key : Nat) (value : WordLocW width) (locals : Spt (WordLocW width)) :
    evenStartingLocals (sptInsert key value locals) ↔
      Flapjack.isPhyVar key = true ∧ evenStartingLocals locals := by
  change (∀ other, sptMem other (sptInsert key value locals) →
    Flapjack.isPhyVar other = true) ↔ _
  simp only [sptMem_sptInsert]
  constructor
  · intro all
    exact ⟨all key (Or.inl rfl), fun other member => all other (Or.inr member)⟩
  · rintro ⟨physical, all⟩ other (same | member)
    · simpa [same] using physical
    · exact all other member

end Flapjack.Compiler.Backend.WordAlloc.Proofs
