import Flapjack.FfiHOL
import Flapjack.Misc.ListEl

namespace Flapjack

private instance : Nonempty HolFfiName := ⟨.sharedMem .mappedRead⟩

/-- Flapjack infrastructure naming the literal predicate in HOL's optional
selection. Every EL use is guarded by the original prefix/suffix bounds. -/
def mmioIndexBoundary (names : List HolFfiName) (index : Nat) : Prop :=
  index ≤ names.length ∧
    (∀ j, j < index → ∃ name, holEl j names = .extCall name) ∧
    (∀ j, index ≤ j → j < names.length →
      ∃ operation, holEl j names = .sharedMem operation)

/-- Distinct boundaries would classify the same in-range name as both an
external call and shared memory. Thus HOL's optional choice is unambiguous. -/
theorem mmioIndexBoundary_unique {names : List HolFfiName} {left right : Nat}
    (hl : mmioIndexBoundary names left) (hr : mmioIndexBoundary names right) :
    left = right := by
  rcases hl with ⟨hll, hlpre, hlsuf⟩
  rcases hr with ⟨hrl, hrpre, hrsuf⟩
  have impossible (a b : Nat) (hab : a < b) (hb : b ≤ names.length)
      (beforeBoundary : ∀ j, j < b → ∃ name, holEl j names = .extCall name)
      (afterBoundary : ∀ j, a ≤ j → j < names.length →
        ∃ operation, holEl j names = .sharedMem operation) : False := by
    obtain ⟨name, hn⟩ := beforeBoundary a hab
    obtain ⟨operation, ho⟩ := afterBoundary a (Nat.le_refl a) (by omega)
    rw [hn] at ho
    cases ho
  by_cases h : left < right
  · exact False.elim (impossible left right h hrl hrpre hlsuf)
  by_cases h' : right < left
  · exact False.elim (impossible right left h' hll hlpre hrsuf)
  omega

/-- Literal optional selection from HOL: Some of a boundary satisfying the
whole prefix/suffix predicate, or None if none exists. The uniqueness theorem
above makes the witness independent of the assistants' choice operators. -/
@[hol "cakeml/compiler/backend/semantics/targetSemScript.sml" "mmio_pcs_min_index_def"]
noncomputable def mmioPcsMinIndex (names : List HolFfiName) : Option Nat := by
  classical
  exact if h : ∃ index, mmioIndexBoundary names index then
    some (Classical.choose h) else none

/-- Flapjack infrastructure eliminating optional choice using a genuine
boundary witness and the unconditional uniqueness proof. -/
theorem mmioPcsMinIndex_eq_some {names : List HolFfiName} {index : Nat}
    (h : mmioIndexBoundary names index) : mmioPcsMinIndex names = some index := by
  classical
  have existsBoundary : ∃ i, mmioIndexBoundary names i := ⟨index, h⟩
  simp only [mmioPcsMinIndex, dif_pos existsBoundary]
  exact congrArg some (mmioIndexBoundary_unique (Classical.choose_spec existsBoundary) h)

/-- Flapjack infrastructure: failure means the entire source predicate has
no witness, including lists with an external call after shared memory. -/
theorem mmioPcsMinIndex_eq_none {names : List HolFfiName}
    (h : ¬ ∃ index, mmioIndexBoundary names index) : mmioPcsMinIndex names = none := by
  classical
  simp only [mmioPcsMinIndex, dif_neg h]

end Flapjack
